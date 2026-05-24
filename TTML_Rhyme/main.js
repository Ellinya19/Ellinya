// ═══════════════════════════════════════════════════════════
//  TTML RHYME — main.js
//  Handles: audio loading, TTML parsing, game state, scoring
// ═══════════════════════════════════════════════════════════

const Game = (() => {
  // ── State ────────────────────────────────────────────────
  let audioBuffer = null;
  let audioContext = null;
  let audioSource = null;
  let audioDuration = 0;
  let audioStartTime = 0;      // AudioContext time when playback started
  let audioOffsetTime = 0;     // Offset in seconds into the track
  let isPlaying = false;

  let words = [];              // Parsed words: {text, begin, end, type}
  let activeWords = new Map(); // id → DOM element
  let score = 0;
  let missCount = 0;
  let combo = 0;
  let gameRunning = false;
  let gameStarted = false;
  let scheduleTimer = null;
  let wordIdCounter = 0;
  let wordColor = '#ffffff';

  // ── Constants ────────────────────────────────────────────
  const GHOST_LEAD = 2.0;      // Ghost appears N seconds before main word
  const WORD_LINGER = 3.0;     // Word stays on screen N seconds before auto-miss
  const TIMING_WINDOWS = [
    { label: 'PERFECT', maxDelta: 0.15, color: 'rainbow' },
    { label: 'GREAT',   maxDelta: 0.35, color: '#7ef2ff' },
    { label: 'GOOD',    maxDelta: 0.55, color: '#7eff9c' },
    { label: 'OK',      maxDelta: 0.75, color: '#ffe97e' },
    { label: 'LATE',    maxDelta: 1.00, color: '#ff9f7e' },
    { label: 'BAD',     maxDelta: Infinity, color: '#ff6e6e' },
  ];

  // ── Callbacks (set by UI) ─────────────────────────────────
  let onScoreUpdate = () => {};
  let onMiss = () => {};
  let onGameEnd = () => {};
  let onCountdown = () => {};
  let onWaiting = () => {};
  let onWordHit = () => {};

  function setCallbacks(cb) {
    onScoreUpdate = cb.onScoreUpdate || onScoreUpdate;
    onMiss = cb.onMiss || onMiss;
    onGameEnd = cb.onGameEnd || onGameEnd;
    onCountdown = cb.onCountdown || onCountdown;
    onWaiting = cb.onWaiting || onWaiting;
    onWordHit = cb.onWordHit || onWordHit;
  }

  // ── TTML Parsing ─────────────────────────────────────────
  function parseTime(t) {
    if (!t) return null;
    const m = t.match(/(\d+):(\d+):(\d+(?:\.\d+)?)/);
    if (m) return parseFloat(m[1]) * 3600 + parseFloat(m[2]) * 60 + parseFloat(m[3]);
    const s = t.match(/^(\d+(?:\.\d+)?)s?$/);
    return s ? parseFloat(s[1]) : null;
  }

  function parseTTML(xmlText) {
    const parser = new DOMParser();
    const doc = parser.parseFromString(xmlText, 'application/xml');
    const ns = 'http://www.w3.org/ns/ttml';
    const ttmNS = 'http://www.w3.org/ns/ttml#metadata';

    let pEls = Array.from(doc.getElementsByTagNameNS(ns, 'p'));
    if (!pEls.length) pEls = Array.from(doc.querySelectorAll('p'));

    const rawWords = [];

    pEls.forEach(p => {
      const agent = p.getAttributeNS(ttmNS, 'agent')
        || p.getAttribute('ttm:agent')
        || 'v1';

      const children = Array.from(p.children);
      children.forEach(child => {
        const tagName = child.localName || child.nodeName.split(':').pop();
        if (tagName !== 'span') return;

        const role = child.getAttributeNS
          ? child.getAttributeNS(ttmNS, 'role')
          : child.getAttribute('ttm:role');

        // Determine type
        let type;
        if (role === 'x-bg') {
          type = 'backing';
        } else if (agent === 'v2') {
          type = 'additional';
        } else {
          type = 'main';
        }

        // If it's x-bg, look for inner spans
        if (role === 'x-bg') {
          const innerSpans = Array.from(child.children).filter(el =>
            (el.localName || el.nodeName.split(':').pop()) === 'span'
          );
          if (innerSpans.length) {
            innerSpans.forEach(inner => {
              const begin = parseTime(inner.getAttribute('begin'));
              const end = parseTime(inner.getAttribute('end'));
              const text = inner.textContent.trim();
              if (text && begin !== null) {
                rawWords.push({ text, begin, end, type });
              }
            });
          } else {
            const begin = parseTime(child.getAttribute('begin'));
            const end = parseTime(child.getAttribute('end'));
            const text = child.textContent.trim();
            if (text && begin !== null) {
              rawWords.push({ text, begin, end, type });
            }
          }
          return;
        }

        // Regular span — collect with space-flag for backslash-merge
        const begin = parseTime(child.getAttribute('begin'));
        const end = parseTime(child.getAttribute('end'));
        const rawText = child.textContent.trim();
        if (rawText && begin !== null) {
          // Detect if this span is glued to previous span in same <p> (no space between)
          let noSpaceBefore = false;
          const siblings = Array.from(child.parentNode.childNodes);
          const myIdx = siblings.indexOf(child);
          if (myIdx > 0) {
            const prev = siblings[myIdx - 1];
            // Text node with no space = spans are glued (backslash-join in source)
            if (prev.nodeType === 3 && prev.textContent.trim() === '') noSpaceBefore = true;
          }
          // Strip trailing hyphen, then remove special chars except ? and !
          const text = rawText.replace(/-+$/, '').replace(/[^\p{L}\p{N}\s?!]/gu, '').trim();
          if (text.length > 0) {
            rawWords.push({ text, begin, end, type, noSpaceBefore, pEl: p });
          }
        }
      });
    });

    // Sort by begin time
    rawWords.sort((a, b) => a.begin - b.begin);

    // Merge backslash-split spans: spans with noSpaceBefore=true glue onto previous word
    // Only merge within same <p> element to avoid cross-line merges after sort
    const merged = [];
    for (const w of rawWords) {
      if (w.noSpaceBefore && merged.length > 0) {
        const prev = merged[merged.length - 1];
        if (prev.type === w.type && prev.pEl === w.pEl) {
          prev.text = prev.text + w.text;
          prev.end = w.end;
          continue;
        }
      }
      const { pEl: _p, ...rest } = w;
      merged.push(rest);
    }

    // Remove ellipsis tokens (... or . . .)
    const noEllipsis = merged.filter(w => !/^\.{1,3}$/.test(w.text.trim()));

    // Conflict resolution: if backing/additional is within 300ms of a main word, drop it
    const CONFLICT_THRESHOLD = 0.3;
    const mainWords = noEllipsis.filter(w => w.type === 'main');
    const filtered = noEllipsis.filter(w => {
      if (w.type === 'main') return true;
      // Check if conflicts with any main word
      const conflicts = mainWords.some(m => Math.abs(m.begin - w.begin) < CONFLICT_THRESHOLD);
      return !conflicts;
    });

    // Shift all word timings 200ms earlier to compensate audio latency
    const TTML_OFFSET = 0.2;
    filtered.forEach(w => {
      w.begin = Math.max(0, w.begin - TTML_OFFSET);
      if (w.end !== null) w.end = Math.max(0, w.end - TTML_OFFSET);
    });

    return filtered;
  }

  // ── Audio Loading ─────────────────────────────────────────
  async function loadAudio(file) {
    if (!audioContext) audioContext = new (window.AudioContext || window.webkitAudioContext)();
    const arrayBuffer = await file.arrayBuffer();
    audioBuffer = await audioContext.decodeAudioData(arrayBuffer);
    audioDuration = audioBuffer.duration;
    return audioDuration;
  }

  // ── Validation ────────────────────────────────────────────
  function validateFiles(audioDur, ttmlWords) {
    if (!ttmlWords.length) return { ok: false, msg: 'No words found in TTML file.' };
    const lastWord = ttmlWords[ttmlWords.length - 1];
    const ttmlEnd = lastWord.end || lastWord.begin;
    if (ttmlEnd > audioDur + 0.5) {
      return {
        ok: false,
        msg: `TTML duration (${ttmlEnd.toFixed(1)}s) exceeds audio duration (${audioDur.toFixed(1)}s). Please check your files.`
      };
    }
    return { ok: true };
  }

  // ── Current audio time (accurate) ────────────────────────
  function getCurrentTime() {
    if (!isPlaying || !audioContext) return audioOffsetTime;
    return audioOffsetTime + (audioContext.currentTime - audioStartTime);
  }

  // ── Start Game ────────────────────────────────────────────
  async function startGame(ttmlWords, color) {
    if (!audioBuffer || !audioContext) return;
    wordColor = color || '#ffffff';
    words = ttmlWords;
    score = 0;
    missCount = 0;
    combo = 0;
    wordIdCounter = 0;
    gameRunning = true;
    gameStarted = false;
    activeWords.clear();

    // Resume AudioContext if suspended
    if (audioContext.state === 'suspended') await audioContext.resume();

    const firstWordTime = words[0]?.begin ?? 0;

    if (firstWordTime < 3) {
      // Countdown 3 → 2 → 1 → START
      await doCountdown(3);
      beginPlayback(0);
    } else {
      // Start music immediately, show "waiting" message
      beginPlayback(0);
      onWaiting(firstWordTime);

      // Schedule countdown: start 3s before the ghost of the first word
      // Ghost appears 2s before the word, so countdown ends at (firstWordTime - 2)
      // Countdown duration = 3s, so countdown starts at (firstWordTime - 2 - 3) = (firstWordTime - 5)
      const countdownAt = firstWordTime - GHOST_LEAD - 3;
      if (countdownAt > 0) {
        setTimeout(() => {
          doCountdown(3);
        }, countdownAt * 1000);
      } else {
        // Not enough time, start countdown immediately
        doCountdown(3);
      }
    }
  }

  function beginPlayback(offset) {
    audioOffsetTime = offset;
    if (audioSource) {
      try { audioSource.stop(); } catch (e) {}
    }
    audioSource = audioContext.createBufferSource();
    audioSource.buffer = audioBuffer;
    audioSource.connect(audioContext.destination);
    audioSource.start(0, offset);
    audioStartTime = audioContext.currentTime;
    isPlaying = true;
    gameStarted = true;

    audioSource.onended = () => {
      if (isPlaying) {
        isPlaying = false;
        setTimeout(() => endGame(), 1000);
      }
    };

    scheduleWords();
  }

  // ── Countdown ─────────────────────────────────────────────
  function doCountdown(n) {
    return new Promise(resolve => {
      let count = n;
      const tick = () => {
        onCountdown(count);
        if (count <= 0) { resolve(); return; }
        count--;
        setTimeout(tick, 1000);
      };
      tick();
    });
  }

  // ── Word Scheduling ───────────────────────────────────────
  function scheduleWords() {
    if (!gameRunning) return;

    const now = getCurrentTime();
    const LOOKAHEAD = 0.5; // seconds to look ahead

    words.forEach((word, idx) => {
      if (word._scheduled) return;

      const ghostTime = word.begin - GHOST_LEAD;
      const mainTime = word.begin;

      // Schedule ghost appearance
      if (ghostTime <= now + LOOKAHEAD) {
        word._scheduled = true;
        const ghostDelay = Math.max(0, (ghostTime - now) * 1000) + 100;
        const mainDelay = Math.max(0, (mainTime - now) * 1000);

        setTimeout(() => {
          if (!gameRunning) return;
          spawnGhostWord(word, idx);
        }, ghostDelay);

        setTimeout(() => {
          if (!gameRunning) return;
          spawnMainWord(word, idx);
        }, mainDelay);
      }
    });

    scheduleTimer = setTimeout(scheduleWords, 200);
  }

  // ── Ghost Word ────────────────────────────────────────────
  function spawnGhostWord(word, idx) {
    const container = document.getElementById('game-field');
    if (!container) return;

    const id = `ghost-${idx}`;
    const el = document.createElement('div');
    el.className = 'game-word ghost-word';
    el.id = id;
    el.textContent = word.text;

    // Random position (avoid edges)
    const px = 8 + Math.random() * 84;
    const py = 10 + Math.random() * 80;
    el.style.left = `${px}%`;
    el.style.top = `${py}%`;
    el.style.color = wordColor;
    el.style.borderColor = wordColor;
    el.style.setProperty('--word-color', wordColor);

    word._px = px;
    word._py = py;

    // Ghost is clickable — scored same as main word
    el.dataset.wordBegin = String(word.begin);
    el.dataset.spawnTime = String(getCurrentTime());
    el.addEventListener('click', () => handleGhostClick(el, word, idx));
    el.addEventListener('touchstart', (e) => {
      e.preventDefault();
      handleGhostClick(el, word, idx);
    }, { passive: false });

    container.appendChild(el);
    activeWords.set(id, { el, word, isGhost: true });

    // Animate: grow from large to word-size over GHOST_LEAD seconds
    // Ghost starts big and shrinks to normal
    el.style.setProperty('--ghost-duration', `${GHOST_LEAD}s`);
    requestAnimationFrame(() => {
      el.classList.add('ghost-animate');
    });
  }

  // ── Ghost Click Handler ───────────────────────────────────
  function handleGhostClick(el, word, idx) {
    const ghostId = `ghost-${idx}`;
    if (!activeWords.has(ghostId)) return;

    activeWords.delete(ghostId);
    word._ghostClicked = true;

    const wordBegin = parseFloat(el.dataset.wordBegin);
    const now = getCurrentTime();
    const delta = Math.abs(now - wordBegin);

    let timing = TIMING_WINDOWS[TIMING_WINDOWS.length - 1];
    for (const w of TIMING_WINDOWS) {
      if (delta <= w.maxDelta) { timing = w; break; }
    }

    score++;
    combo++;
    onScoreUpdate({ score, combo, missCount });
    onWordHit({ label: timing.label, color: timing.color, x: el.style.left, y: el.style.top });

    el.classList.remove('ghost-word', 'ghost-animate');
    el.classList.add('hit-flash');
    el.style.animation = 'none';
    requestAnimationFrame(() => { el.style.animation = ''; el.classList.add('hit-flash'); });
    setTimeout(() => el.remove(), 300);
  }

  // ── Main Word ─────────────────────────────────────────────
  function spawnMainWord(word, idx) {
    const container = document.getElementById('game-field');
    if (!container) return;

    // If ghost was already clicked, skip spawning main word
    if (word._ghostClicked) {
      word._ghostClicked = false;
      return;
    }

    // Remove ghost (not yet clicked)
    const ghostEl = document.getElementById(`ghost-${idx}`);
    if (ghostEl) {
      activeWords.delete(`ghost-${idx}`);
      ghostEl.remove();
    }

    const id = `word-${wordIdCounter++}`;
    const el = document.createElement('div');
    el.className = 'game-word main-word';
    el.id = id;
    el.textContent = word.text;
    el.style.left = `${word._px ?? (8 + Math.random() * 84)}%`;
    el.style.top = `${word._py ?? (10 + Math.random() * 80)}%`;
    el.style.color = wordColor;
    el.style.borderColor = wordColor;
    el.style.setProperty('--word-color', wordColor);
    el.dataset.spawnTime = String(getCurrentTime());
    el.dataset.wordBegin = String(word.begin);

    // Click handler
    el.addEventListener('click', () => handleWordClick(el, word));
    el.addEventListener('touchstart', (e) => {
      e.preventDefault();
      handleWordClick(el, word);
    }, { passive: false });

    container.appendChild(el);
    activeWords.set(id, { el, word });

    // Auto-miss after WORD_LINGER seconds
    setTimeout(() => {
      if (activeWords.has(id)) {
        handleMiss(id, word);
      }
    }, WORD_LINGER * 1000);
  }

  // ── Click Handler ─────────────────────────────────────────
  function handleWordClick(el, word) {
    const id = el.id;
    if (!activeWords.has(id)) return;

    activeWords.delete(id);

    const spawnTime = parseFloat(el.dataset.spawnTime);
    const wordBegin = parseFloat(el.dataset.wordBegin);
    const now = getCurrentTime();
    const delta = Math.abs(now - wordBegin);

    // Find timing window
    let window = TIMING_WINDOWS[TIMING_WINDOWS.length - 1];
    for (const w of TIMING_WINDOWS) {
      if (delta <= w.maxDelta) { window = w; break; }
    }

    score++;
    combo++;
    onScoreUpdate({ score, combo, missCount });
    onWordHit({ label: window.label, color: window.color, x: el.style.left, y: el.style.top });

    el.classList.add('hit-flash');
    setTimeout(() => el.remove(), 300);
  }

  // ── Miss Handler ──────────────────────────────────────────
  function handleMiss(id, word) {
    const entry = activeWords.get(id);
    if (!entry) return;

    activeWords.delete(id);
    combo = 0;
    missCount++;

    const { el } = entry;
    onMiss({ word: word.text, x: el.style.left, y: el.style.top });
    onScoreUpdate({ score, combo, missCount });

    el.classList.add('miss-flash');
    setTimeout(() => el.remove(), 500);
  }

  // ── End Game ──────────────────────────────────────────────
  function endGame() {
    gameRunning = false;
    isPlaying = false;
    clearTimeout(scheduleTimer);
    try { audioSource?.stop(); } catch (e) {}

    // Clear remaining active words
    activeWords.forEach(({ el }) => el.remove());
    activeWords.clear();

    onGameEnd({ score, missCount, total: words.length });
  }

  function stopGame() {
    endGame();
  }

  // ── Word color setter ─────────────────────────────────────
  function setWordColor(c) {
    wordColor = c;
  }

  // ── Expose API ────────────────────────────────────────────
  return {
    loadAudio,
    parseTTML,
    validateFiles,
    startGame,
    stopGame,
    setCallbacks,
    setWordColor,
    getCurrentTime: () => getCurrentTime(),
    getScore: () => ({ score, combo, missCount }),
  };
})();
