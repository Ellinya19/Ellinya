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
  let usedPositions = [];      // [{px, py, expire}] – anti-overlap grid
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
  const WORD_LINGER = 2.1;     // Word stays on screen N seconds before auto-miss
  const SWIPE_MIN_GAP = 2.0;   // Min gap to next word (seconds) to become swipe
  const SWIPE_MAX_GAP = 5.0;   // Max gap to next word (seconds) to become swipe
  const SWIPE_PX_PER_SEC = 60; // Pixels per second of gap for swipe distance
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
      const lineId = Array.from(doc.getElementsByTagNameNS(ns, 'p').length ? doc.getElementsByTagNameNS(ns, 'p') : doc.querySelectorAll('p')).indexOf(w.pEl);
      const { pEl: _p, ...rest } = w;
      rest.lineId = lineId >= 0 ? lineId : merged.length;
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

    // Mark swipe words: gap to next word is 2–5 seconds
    for (let i = 0; i < filtered.length - 1; i++) {
      const gap = filtered[i + 1].begin - filtered[i].begin;
      filtered[i]._isSwipe = gap >= SWIPE_MIN_GAP && gap <= SWIPE_MAX_GAP;
    }
    filtered[filtered.length - 1]._isSwipe = false;

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
    if (isPaused) return audioOffsetTime + (pausedAt - audioStartTime);
    return audioOffsetTime + (audioContext.currentTime - audioStartTime);
  }

  // ── Start Game ────────────────────────────────────────────
  async function startGame(ttmlWords, color) {
    if (!audioBuffer || !audioContext) return;
    wordColor = color || '#ffffff';
    words = ttmlWords;
    words.forEach(w => {
      w._scheduled = false;
      w._px = undefined;
      w._py = undefined;
      w._swipePreTx = undefined;
      w._swipePreTy = undefined;
      w._swipeUseArc = undefined;
      w._swipeSweepDir = undefined;
      w._ghostClicked = false;
      w._ghostLineSvg = null;
      w._ghostDotEl = null;
    });
    score = 0;
    missCount = 0;
    combo = 0;
    wordIdCounter = 0;
    lastHitIdx = -1;
    isPaused = false;
    gameRunning = true;
    gameStarted = false;
    activeWords.clear();
    usedPositions = [];

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
  // ── Arc trail helper ─────────────────────────────────────
  // Returns SVG path "d" for a half-arc between (x1,y1) and (x2,y2)
  // sweepDir: 1 = clockwise arc, -1 = counter-clockwise
  // ── Arc geometry (shared by draw + drag) ─────────────────
  // SVG "A rx ry 0 large-arc-flag sweep-flag x2 y2"
  // sweepDir=1 → sweep-flag=1 (clockwise in SVG coords)
  // The center of that arc lies on the SAME side determined here.
  function getArcGeometry(ox, oy, tx, ty, sweepDir) {
    const dx = tx - ox, dy = ty - oy;
    const dist = Math.sqrt(dx * dx + dy * dy);
    const r = dist * 0.75;
    const mx = (ox + tx) / 2, my = (oy + ty) / 2;
    // Perpendicular unit vector (rotated 90° CCW from ox→tx)
    const pdx = -dy / dist, pdy = dx / dist;
    const h = Math.sqrt(Math.max(0, r * r - (dist / 2) * (dist / 2)));
    // SVG sweep-flag=1 means clockwise → center is to the LEFT of the chord
    // (SVG Y-axis points down, so "left of OX→TX" = sign = +1 on pdx)
    // sweep-flag=0 (CCW) → center to the RIGHT → sign = -1
    const sign = sweepDir === 1 ? 1 : -1;
    const cx = mx + sign * h * pdx;
    const cy = my + sign * h * pdy;
    const startA = Math.atan2(oy - cy, ox - cx);
    let sweep = Math.atan2(ty - cy, tx - cx) - startA;
    if (sweepDir === 1) { if (sweep < 0) sweep += 2 * Math.PI; }
    else               { if (sweep > 0) sweep -= 2 * Math.PI; }
    return { cx, cy, r, startA, sweep };
  }

  function arcPathD(x1, y1, x2, y2, sweepDir) {
    const dx = x2 - x1, dy = y2 - y1;
    const dist = Math.sqrt(dx * dx + dy * dy);
    const r = dist * 0.75;
    return `M ${x1} ${y1} A ${r} ${r} 0 0 ${sweepDir === 1 ? 1 : 0} ${x2} ${y2}`;
  }

  // ── Arc drag projection ───────────────────────────────────
  // Samples 128 points on the SAME arc as arcPathD, returns nearest {x, y, t}
  function projectOntoArc(mouseX, mouseY, ox, oy, tx, ty, sweepDir) {
    const { cx, cy, r, startA, sweep } = getArcGeometry(ox, oy, tx, ty, sweepDir);
    const N = 128;
    let best = null, bestD2 = Infinity;
    for (let i = 0; i <= N; i++) {
      const t = i / N;
      const angle = startA + sweep * t;
      const px = cx + r * Math.cos(angle);
      const py = cy + r * Math.sin(angle);
      const d2 = (mouseX - px) ** 2 + (mouseY - py) ** 2;
      if (d2 < bestD2) { bestD2 = d2; best = { x: px, y: py, t }; }
    }
    return best;
  }

  // ── Position resolver ─────────────────────────────────────
  // Pure random placement with anti-overlap check.
  function resolveWordPosition(word, idx, container) {
    const now2 = getCurrentTime();
    usedPositions = usedPositions.filter(p => p.expire > now2);

    let px, py, tries = 0;
    do {
      px = 8 + Math.random() * 84;
      py = 10 + Math.random() * 80;
      tries++;
    } while (
      tries < 30 &&
      usedPositions.some(p => Math.abs(p.px - px) < 18 && Math.abs(p.py - py) < 18)
    );

    usedPositions.push({ px, py, expire: now2 + GHOST_LEAD + WORD_LINGER + 0.5 });
    return { px, py };
  }

  function spawnGhostWord(word, idx) {
    const container = document.getElementById('game-field');
    if (!container) return;

    const id = `ghost-${idx}`;
    const el = document.createElement('div');
    el.className = 'game-word ghost-word';
    el.id = id;
    el.textContent = word.text;

    // Position: line-group aware
    const { px, py } = resolveWordPosition(word, idx, container);
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

    // If swipe word: pre-calculate target and draw ghost trail (line or arc)
    if (word._isSwipe) {
      const cw = container.offsetWidth  || window.innerWidth;
      const ch = container.offsetHeight || window.innerHeight;
      const BOX = 110;
      const MARGIN = BOX / 2 + 10;
      const ox = (px / 100) * cw;
      const oy = (py / 100) * ch;
      const minDist = SWIPE_PX_PER_SEC * SWIPE_MIN_GAP;
      const maxDist = SWIPE_PX_PER_SEC * SWIPE_MAX_GAP;
      const dist = minDist + Math.random() * (maxDist - minDist);
      let angle, tx, ty, tries3 = 0;
      do {
        angle = Math.random() * 2 * Math.PI;
        tx = ox + Math.cos(angle) * dist;
        ty = oy + Math.sin(angle) * dist;
        tries3++;
      } while (
        tries3 < 40 &&
        (tx < MARGIN || tx > cw - MARGIN || ty < MARGIN || ty > ch - MARGIN)
      );
      tx = Math.max(MARGIN, Math.min(cw - MARGIN, tx));
      ty = Math.max(MARGIN, Math.min(ch - MARGIN, ty));

      // Randomly decide straight or arc (50/50)
      const useArc = Math.random() < 0.5;
      const sweepDir = Math.random() < 0.5 ? 1 : -1;

      // Store for setupSwipeWord to reuse
      word._swipePreTx = tx;
      word._swipePreTy = ty;
      word._swipePreOx = ox;
      word._swipePreOy = oy;
      word._swipePreCw = cw;
      word._swipePreCh = ch;
      word._swipeUseArc = useArc;
      word._swipeSweepDir = sweepDir;

      // Ghost trail SVG
      const gSvg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
      gSvg.classList.add('ghost-swipe-trail');
      gSvg.style.left = '0';
      gSvg.style.top = '0';
      gSvg.style.width = `${cw}px`;
      gSvg.style.height = `${ch}px`;
      gSvg.style.setProperty('--ghost-line-duration', `${GHOST_LEAD}s`);

      if (useArc) {
        const gPath = document.createElementNS('http://www.w3.org/2000/svg', 'path');
        gPath.setAttribute('d', arcPathD(ox, oy, tx, ty, sweepDir));
        gPath.setAttribute('stroke', wordColor);
        gPath.setAttribute('stroke-width', '3');
        gPath.setAttribute('stroke-dasharray', '8 6');
        gPath.setAttribute('opacity', '0.3');
        gPath.setAttribute('fill', 'none');
        gSvg.appendChild(gPath);
      } else {
        const gLine = document.createElementNS('http://www.w3.org/2000/svg', 'line');
        gLine.setAttribute('x1', ox);
        gLine.setAttribute('y1', oy);
        gLine.setAttribute('x2', tx);
        gLine.setAttribute('y2', ty);
        gLine.setAttribute('stroke', wordColor);
        gLine.setAttribute('stroke-width', '3');
        gLine.setAttribute('stroke-dasharray', '8 6');
        gLine.setAttribute('opacity', '0.3');
        gSvg.appendChild(gLine);
      }
      container.appendChild(gSvg);
      word._ghostLineSvg = gSvg;

      // Ghost target dot
      const gDot = document.createElement('div');
      gDot.className = 'swipe-target-dot';
      gDot.style.left = `${tx}px`;
      gDot.style.top = `${ty}px`;
      gDot.style.borderColor = wordColor;
      gDot.style.opacity = '0';
      gDot.style.animation = 'none';
      gDot.style.transition = `opacity ${GHOST_LEAD}s linear`;
      container.appendChild(gDot);
      word._ghostDotEl = gDot;
      requestAnimationFrame(() => { gDot.style.opacity = '0.4'; });
    }

    // Animate: grow from large to word-size over GHOST_LEAD seconds
    el.style.setProperty('--ghost-duration', `${GHOST_LEAD}s`);
    requestAnimationFrame(() => {
      el.classList.add('ghost-animate');
    });
  }

  // ── Ghost Click Handler ───────────────────────────────────
  function handleGhostClick(el, word, idx) {
    const ghostId = `ghost-${idx}`;
    if (!activeWords.has(ghostId)) return;

    // Sequential enforcement: miss any skipped word before this ghost
    if (idx > 0 && idx > lastHitIdx + 1) {
      for (const [wid, entry] of activeWords) {
        const entryIdx = parseInt(entry.el.dataset.wordIdx ?? '-1', 10);
        if (entryIdx >= 0 && entryIdx < idx && entryIdx > lastHitIdx && wid !== ghostId) {
          handleMiss(wid, entry.word);
          break;
        }
      }
    }

    if (!activeWords.has(ghostId)) return;
    activeWords.delete(ghostId);
    word._ghostClicked = true;
    if (word._ghostLineSvg) { word._ghostLineSvg.remove(); word._ghostLineSvg = null; }
    if (word._ghostDotEl)  { word._ghostDotEl.remove();  word._ghostDotEl  = null; }

    const wordBegin = parseFloat(el.dataset.wordBegin);
    const now = getCurrentTime();
    const delta = Math.abs(now - wordBegin);

    let timing = TIMING_WINDOWS[TIMING_WINDOWS.length - 1];
    for (const w of TIMING_WINDOWS) {
      if (delta <= w.maxDelta) { timing = w; break; }
    }

    lastHitIdx = Math.max(lastHitIdx, idx);
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

    // Ghost snap-out: let it finish at scale(1) then flash out as main word appears
    const ghostEl = document.getElementById(`ghost-${idx}`);
    if (ghostEl) {
      activeWords.delete(`ghost-${idx}`);
      ghostEl.classList.remove('ghost-animate');
      ghostEl.classList.add('ghost-snap');
      setTimeout(() => ghostEl.remove(), 90);
    }
    // Remove ghost line & ghost dot (real ones will be added by setupSwipeWord)
    if (word._ghostLineSvg) { word._ghostLineSvg.remove(); word._ghostLineSvg = null; }
    if (word._ghostDotEl)  { word._ghostDotEl.remove();  word._ghostDotEl  = null; }

    const id = `word-${wordIdCounter++}`;
    const el = document.createElement('div');
    el.id = id;
    el.textContent = word.text;

    const pxRaw = word._px ?? (8 + Math.random() * 84);
    const pyRaw = word._py ?? (10 + Math.random() * 80);
    el.style.left = `${pxRaw}%`;
    el.style.top = `${pyRaw}%`;
    el.style.color = wordColor;
    el.style.borderColor = wordColor;
    el.style.setProperty('--word-color', wordColor);
    el.dataset.spawnTime = String(getCurrentTime());
    el.dataset.wordBegin = String(word.begin);
    el.dataset.wordIdx = String(idx);

    if (word._isSwipe) {
      el.className = 'game-word main-word swipe-word';
      setupSwipeWord(el, word, id, pxRaw, pyRaw, container);
    } else {
      el.className = 'game-word main-word';
      el.addEventListener('click', () => handleWordClick(el, word));
      el.addEventListener('touchstart', (e) => {
        e.preventDefault();
        handleWordClick(el, word);
      }, { passive: false });
    }

    container.appendChild(el);
    activeWords.set(id, { el, word });

    // Auto-miss after WORD_LINGER seconds
    setTimeout(() => {
      if (activeWords.has(id)) {
        handleMiss(id, word);
      }
    }, WORD_LINGER * 1000);
  }

  // ── Swipe Setup ───────────────────────────────────────────
  function setupSwipeWord(el, word, id, pxRaw, pyRaw, container) {
    const cw = container.offsetWidth  || window.innerWidth;
    const ch = container.offsetHeight || window.innerHeight;
    const BOX = 110; // must match CSS .game-word width/height

    // Origin in px
    const ox = (pxRaw / 100) * cw;
    const oy = (pyRaw / 100) * ch;

    // Reuse pre-calculated target from ghost phase (same direction as ghost line)
    const MARGIN = BOX / 2 + 10;
    let tx, ty;
    if (word._swipePreTx !== undefined) {
      tx = word._swipePreTx;
      ty = word._swipePreTy;
    } else {
      const minDist = SWIPE_PX_PER_SEC * SWIPE_MIN_GAP;
      const maxDist = SWIPE_PX_PER_SEC * SWIPE_MAX_GAP;
      const dist = minDist + Math.random() * (maxDist - minDist);
      let angle, tries2 = 0;
      do {
        angle = Math.random() * 2 * Math.PI;
        tx = ox + Math.cos(angle) * dist;
        ty = oy + Math.sin(angle) * dist;
        tries2++;
      } while (
        tries2 < 40 &&
        (tx < MARGIN || tx > cw - MARGIN || ty < MARGIN || ty > ch - MARGIN)
      );
      tx = Math.max(MARGIN, Math.min(cw - MARGIN, tx));
      ty = Math.max(MARGIN, Math.min(ch - MARGIN, ty));
    }

    // Draw dashed trail SVG (line or arc)
    const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svg.classList.add('swipe-trail');
    svg.style.left = '0';
    svg.style.top = '0';
    svg.style.width = `${cw}px`;
    svg.style.height = `${ch}px`;
    if (word._swipeUseArc) {
      const arcPath = document.createElementNS('http://www.w3.org/2000/svg', 'path');
      arcPath.setAttribute('d', arcPathD(ox, oy, tx, ty, word._swipeSweepDir ?? 1));
      arcPath.setAttribute('stroke', wordColor);
      arcPath.setAttribute('stroke-width', '3');
      arcPath.setAttribute('stroke-dasharray', '8 6');
      arcPath.setAttribute('opacity', '0.45');
      arcPath.setAttribute('fill', 'none');
      svg.appendChild(arcPath);
    } else {
      const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
      line.setAttribute('x1', ox);
      line.setAttribute('y1', oy);
      line.setAttribute('x2', tx);
      line.setAttribute('y2', ty);
      line.setAttribute('stroke', wordColor);
      line.setAttribute('stroke-width', '3');
      line.setAttribute('stroke-dasharray', '8 6');
      line.setAttribute('opacity', '0.45');
      svg.appendChild(line);
    }
    container.appendChild(svg);

    // Target dot
    const dot = document.createElement('div');
    dot.className = 'swipe-target-dot';
    dot.style.left = `${tx}px`;
    dot.style.top = `${ty}px`;
    dot.style.borderColor = wordColor;
    container.appendChild(dot);

    // Store refs for cleanup
    el._swipeTrailSvg = svg;
    el._swipeTargetDot = dot;
    el._swipeTx = tx;
    el._swipeTy = ty;
    el._swipeOx = ox;
    el._swipeOy = oy;
    el._swipeDone = false;

    // ── Drag logic ──
    let dragging = false;
    let startX, startY;

    function getEventXY(e) {
      if (e.touches) return { x: e.touches[0].clientX, y: e.touches[0].clientY };
      return { x: e.clientX, y: e.clientY };
    }

    function onDragStart(e) {
      if (el._swipeDone || !activeWords.has(id)) return;
      e.preventDefault();
      dragging = true;
      const { x, y } = getEventXY(e);
      const rect = container.getBoundingClientRect();
      startX = x - rect.left;
      startY = y - rect.top;
    }

    let currentArcT = 0; // track arc progress, only allow forward movement

    function onDragMove(e) {
      if (!dragging || el._swipeDone) return;
      e.preventDefault();
      const { x, y } = getEventXY(e);
      const rect = container.getBoundingClientRect();
      const cx2 = x - rect.left;
      const cy2 = y - rect.top;

      if (word._swipeUseArc) {
        const sweepDir = word._swipeSweepDir ?? 1;
        const { cx: cxArc, cy: cyArc, r, startA, sweep } = getArcGeometry(ox, oy, tx, ty, sweepDir);

        // Project mouse onto arc; only allow forward movement
        const proj = projectOntoArc(cx2, cy2, ox, oy, tx, ty, sweepDir);

        // Lock: if mouse is too far from the arc (>80px), don't advance
        const distToArc = Math.sqrt((cx2 - proj.x) ** 2 + (cy2 - proj.y) ** 2);
        if (distToArc > 80) return; // word stays at currentArcT position

        const clampedT = Math.max(currentArcT, proj.t);
        currentArcT = clampedT;

        // Re-sample clamped point using SAME geometry
        const angle = startA + sweep * clampedT;
        const clampedX = cxArc + r * Math.cos(angle);
        const clampedY = cyArc + r * Math.sin(angle);

        el.style.left = `${(clampedX / cw) * 100}%`;
        el.style.top  = `${(clampedY / ch) * 100}%`;
        if (clampedT >= 0.93) {
          el._swipeDone = true;
          dragging = false;
          cleanupSwipeListeners();
          handleSwipeComplete(el, word, id, container);
        }
      } else {
        // Project onto straight line (ox→tx, oy→ty)
        const dx = tx - ox, dy = ty - oy;
        const len = Math.sqrt(dx * dx + dy * dy);
        const ux = dx / len, uy = dy / len;
        const dot2 = (cx2 - ox) * ux + (cy2 - oy) * uy;
        const clamped = Math.max(0, Math.min(len, dot2));
        el.style.left = `${((ox + ux * clamped) / cw) * 100}%`;
        el.style.top  = `${((oy + uy * clamped) / ch) * 100}%`;
        if (clamped >= len - 28) {
          el._swipeDone = true;
          dragging = false;
          cleanupSwipeListeners();
          handleSwipeComplete(el, word, id, container);
        }
      }
    }

    function onDragEnd(e) {
      dragging = false;
    }

    function cleanupSwipeListeners() {
      el.removeEventListener('mousedown', onDragStart);
      el.removeEventListener('touchstart', onDragStart);
      window.removeEventListener('mousemove', onDragMove);
      window.removeEventListener('touchmove', onDragMove);
      window.removeEventListener('mouseup', onDragEnd);
      window.removeEventListener('touchend', onDragEnd);
    }

    el.addEventListener('mousedown', onDragStart);
    el.addEventListener('touchstart', onDragStart, { passive: false });
    window.addEventListener('mousemove', onDragMove, { passive: false });
    window.addEventListener('touchmove', onDragMove, { passive: false });
    window.addEventListener('mouseup', onDragEnd);
    window.addEventListener('touchend', onDragEnd);

    el._cleanupSwipe = cleanupSwipeListeners;
  }

  // ── Swipe Complete ────────────────────────────────────────
  function handleSwipeComplete(el, word, id, container) {
    if (!activeWords.has(id)) return;
    activeWords.delete(id);

    // Remove trail & dot
    el._swipeTrailSvg?.remove();
    el._swipeTargetDot?.remove();
    if (el._cleanupSwipe) el._cleanupSwipe();

    const completedIdx = parseInt(el.dataset.wordIdx ?? '-1', 10);
    const wordEnd = word.end ?? (word.begin + 0.5);
    const now = getCurrentTime();
    // Delta: absolute distance from wordEnd — closer = better rating
    // Kéo đúng lúc wordEnd → delta ≈ 0 → PERFECT
    const delta = Math.abs(now - wordEnd);

    let timing = TIMING_WINDOWS[TIMING_WINDOWS.length - 1];
    for (const w of TIMING_WINDOWS) {
      if (delta <= w.maxDelta) { timing = w; break; }
    }

    lastHitIdx = Math.max(lastHitIdx, completedIdx);
    score++;
    combo++;
    onScoreUpdate({ score, combo, missCount });
    onWordHit({ label: timing.label, color: timing.color, x: el.style.left, y: el.style.top });

    el.classList.add('hit-flash');
    setTimeout(() => el.remove(), 300);
  }

  // ── Click Handler ─────────────────────────────────────────
  function handleWordClick(el, word) {
    const id = el.id;
    if (!activeWords.has(id)) return;

    const clickedIdx = parseInt(el.dataset.wordIdx ?? '-1', 10);

    // Sequential enforcement: if a word before this one is still active, miss it first
    if (clickedIdx > 0 && clickedIdx > lastHitIdx + 1) {
      // Find any active word with idx between lastHitIdx+1 and clickedIdx-1
      for (const [wid, entry] of activeWords) {
        const entryIdx = parseInt(entry.el.dataset.wordIdx ?? '-1', 10);
        if (entryIdx >= 0 && entryIdx < clickedIdx && entryIdx > lastHitIdx && wid !== id) {
          handleMiss(wid, entry.word);
          break;
        }
      }
    }

    if (!activeWords.has(id)) return; // may have been removed by miss cascade
    activeWords.delete(id);

    const wordBegin = parseFloat(el.dataset.wordBegin);
    const now = getCurrentTime();
    const delta = Math.abs(now - wordBegin);

    let window = TIMING_WINDOWS[TIMING_WINDOWS.length - 1];
    for (const w of TIMING_WINDOWS) {
      if (delta <= w.maxDelta) { window = w; break; }
    }

    lastHitIdx = Math.max(lastHitIdx, clickedIdx);
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

    el._swipeTrailSvg?.remove();
    el._swipeTargetDot?.remove();
    if (el._cleanupSwipe) el._cleanupSwipe();
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

  function pauseGame() {
    if (!isPlaying || isPaused) return;
    isPaused = true;
    pausedAt = audioContext.currentTime;
    audioContext.suspend();
    clearTimeout(scheduleTimer);
  }

  function resumeGame() {
    if (!isPaused) return;
    isPaused = false;
    // Recalculate audioStartTime to account for paused duration
    const pausedDuration = audioContext.currentTime - pausedAt;
    audioStartTime += pausedDuration;
    audioContext.resume();
    scheduleWords();
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
    pauseGame,
    resumeGame,
    setCallbacks,
    setWordColor,
    getCurrentTime: () => getCurrentTime(),
    getScore: () => ({ score, combo, missCount }),
  };
})();