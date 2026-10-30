/* DRAM refresh simulator
   Part 1: deterministic model (no DOM). Part 2: UI. */

/* ===== Model ===== */
const SPEC = { thr: 85, normalMs: 64, hotMs: 32, cmds: 8192 };   // Micron 1Gb DDR3 datasheet
const ROWS = 4, COLS = 8, N = ROWS * COLS, PER_ROW = SPEC.cmds / ROWS, STRIDE = PER_ROW / COLS;
const DT = 0.5, END = 1000;                                      // ms of simulated time
const reqWindow = T => T > SPEC.thr ? SPEC.hotMs : SPEC.normalMs;
const retention = (T, i) => 96 * Math.pow(2, (85 - T) / 10) * (0.8 + 0.5 * ((i * 13) % 32) / 31);
const bitOf = i => (i * 5 + (i >> 3)) % 2;

function makePanel(adaptive, T) {
  return {
    adaptive, t: 0, windowMs: adaptive ? reqWindow(T) : SPEC.normalMs, cmd: 0, total: 0, next: 0,
    errors: 0, missed: false, missedMs: 0, charge: Array(N).fill(1), lost: Array(N).fill(false),
    last: Array(N).fill(0), action: 'Ready. Press Start.'
  };
}

function step(p, T) {
  const t1 = p.t + DT, req = reqWindow(T);
  if (p.adaptive && req !== p.windowMs) {          // controller switches schedule and catches up
    p.windowMs = req; p.cmd = 0; p.next = p.t; p.total += ROWS;
    for (let i = 0; i < N; i++) { p.charge[i] = 1; p.last[i] = p.t; }
    p.action = `Temperature crossed ${SPEC.thr} °C: switched to the ${req} ms schedule.`;
  } else if (p.t > 0 || p.cmd > 0) {
    p.action = (!p.adaptive && req < p.windowMs)
      ? `Still on the ${p.windowMs} ms schedule, but the device now requires ${req} ms.`
      : `Command ${p.cmd.toLocaleString('en-US')} of 8,192: refreshing a slice of row ${Math.floor(p.cmd / PER_ROW)}.`;
  }
  for (let i = 0; i < N; i++) {
    if (p.lost[i]) continue;
    p.charge[i] *= Math.pow(0.5, DT / retention(T, i));
    if (p.charge[i] < 0.5) { p.lost[i] = true; p.errors++; }
  }
  const ivl = p.windowMs / SPEC.cmds;
  while (p.next < t1 - 1e-9) {
    const w = p.cmd % PER_ROW;
    if (w % STRIDE === 0) {
      const i = Math.floor(p.cmd / PER_ROW) * COLS + w / STRIDE;
      p.charge[i] = 1; p.last[i] = p.next;           // a lost bit is rewritten wrong, never recovered
    }
    p.cmd = (p.cmd + 1) % SPEC.cmds; p.total++; p.next += ivl;
  }
  p.t = t1;
  p.missed = p.last.some(l => p.t - l > req + 1e-9);
  if (p.missed) p.missedMs += DT;
}

/* ===== UI ===== */
const $ = (s, r = document) => r.querySelector(s);
const SPEEDS = [0.25, 0.5, 1, 2, 4], BASE_RATE = 25;          // simulated ms per real second at 1×
const S = { T: 60, speed: 2, running: false, started: false, last: 0, acc: 0, p: null, el: null };

const INFO = {
  fixed: ['Fixed interval', 'Always 64 ms, even above 85 °C.'],
  adaptive: ['Temperature-adaptive', '64 ms normally → 32 ms above 85 °C.']
};

function buildPanel(k) {
  const s = document.createElement('section');
  s.className = 'proc dp'; s.dataset.k = k; s.setAttribute('aria-labelledby', k + '-h');
  let grid = `<div class="ctrlbox">Memory controller<small>REFRESH →</small></div>`;
  for (let r = 0; r < ROWS; r++) {
    grid += `<span class="arr" data-r="${r}" aria-hidden="true">➜</span>`;
    for (let c = 0; c < COLS; c++) grid += `<div class="cell" data-i="${r * COLS + c}"><i></i><b></b></div>`;
  }
  s.innerHTML = `
    <header class="proc-head"><div><h2 id="${k}-h">${INFO[k][0]}</h2><p>${INFO[k][1]}</p></div></header>
    <div class="proc-main">
      <dl class="counters">
        <div><dt>Temperature</dt><dd data-f="temp"></dd></div>
        <div><dt>Full refresh window</dt><dd data-f="win"></dd></div>
        <div><dt>Command interval · tREFI</dt><dd data-f="ivl"></dd></div>
        <div><dt>Refresh commands</dt><dd data-f="total"></dd></div>
        <div><dt>Refresh requirement</dt><dd class="st" data-f="st"></dd></div>
        <div><dt>Modeled errors</dt><dd data-f="err"></dd></div>
      </dl>
      <div class="mem" role="img" aria-label="Sample of 32 memory cells in 4 rows">${grid}</div>
      <div class="bar"><div class="progress"><span data-f="seq"></span></div><span data-f="seqt"></span></div>
      <p class="explain" data-f="act"></p>
      <p class="why-note" data-f="why"></p>
    </div>`;
  return s;
}

function render() {
  const T = S.T;
  $('#simtime').textContent = S.p.fixed.t.toFixed(1) + ' ms';
  for (const k of ['fixed', 'adaptive']) {
    const p = S.p[k], el = S.el[k], f = n => $(`[data-f="${n}"]`, el);
    f('temp').textContent = T + ' °C';
    $('#scenario-note').textContent = T <= SPEC.thr ? 'Same temperature range, same schedule. Try 90 °C to see the difference.' : 'Above 85 °C: adaptive refresh runs twice as often. Fixed refresh stays unchanged.';
    f('win').textContent = p.windowMs + ' ms';
    f('ivl').textContent = '≈ ' + (p.windowMs * 1000 / SPEC.cmds).toFixed(1) + ' µs';
    f('total').textContent = p.total.toLocaleString('en-US');
    const st = f('st'); st.textContent = p.missed ? 'Refresh requirement missed' : 'Within requirements';
    st.className = 'st ' + (p.missed ? 'bad' : 'ok');
    f('err').textContent = p.errors;
    f('act').textContent = p.action;
    f('seq').style.width = (p.cmd / SPEC.cmds * 100) + '%';
    f('seqt').textContent = `Command ${p.cmd.toLocaleString('en-US')} of 8,192 in this pass`;
    f('why').textContent = p.adaptive
      ? `Active schedule: ${p.windowMs} ms. Reason: ${T > SPEC.thr ? `TC is above ${SPEC.thr} °C, so the datasheet requires 32 ms` : `TC is at or below ${SPEC.thr} °C, so 64 ms is enough`}.`
      : `Active schedule: ${p.windowMs} ms (never changes). The device requires ${reqWindow(T)} ms at this temperature.`;
    const row = Math.floor(p.cmd / PER_ROW);
    el.querySelectorAll('.arr').forEach(a => a.classList.toggle('on', S.started && +a.dataset.r === row));
    el.querySelectorAll('.cell').forEach(c => {
      const i = +c.dataset.i, lost = p.lost[i];
      c.className = 'cell' + (lost ? ' lost' : p.charge[i] < 0.7 ? ' low' : '') + (S.started && Math.floor(i / COLS) === row ? ' on' : '');
      c.style.setProperty('--c', p.charge[i].toFixed(3));
      $('b', c).textContent = lost ? 1 - bitOf(i) : bitOf(i);
      c.title = lost ? 'Modeled bit error' : `Charge ${Math.round(p.charge[i] * 100)}%`;
    });
  }
  renderResults();
}

function renderResults() {
  const a = S.p.fixed, b = S.p.adaptive;
  $('#res-pending').hidden = S.started; $('#res-body').hidden = !S.started;
  if (!S.started) return;
  const card = (n, p) => `<div><span>${n}</span><strong>${p.errors} bit error${p.errors === 1 ? '' : 's'}</strong><small>${p.missedMs.toFixed(1)} ms outside requirements</small></div>`;
  $('#res-cards').innerHTML = card('Fixed interval', a) + card('Temperature-adaptive', b);
  let t;
  if (a.errors) t = 'The fixed schedule let weak cells fall below the model’s retention threshold, and later refreshes cannot undo that. The adaptive schedule refreshed in time.';
  else if (a.missedMs) t = 'The fixed schedule missed the specified requirement, but in this model no bit was lost yet. Missing a deadline removes the guarantee; it does not prove an error. Try a hotter setting.';
  else t = 'At or below 85 °C both schedules meet the 64 ms requirement. Raise the temperature past 85 °C to see them diverge.';
  $('#res-text').textContent = t;
}

function frame(ts) {
  if (S.running) {
    S.acc += Math.min(ts - S.last, 100) / 1000 * BASE_RATE * SPEEDS[S.speed];
    for (let n = 0; S.acc >= DT && n < 400; n++, S.acc -= DT) {
      step(S.p.fixed, S.T); step(S.p.adaptive, S.T);
      if (S.p.fixed.t >= END) { S.running = false; S.acc = 0; break; }
    }
    buttons(); render();
  }
  S.last = ts; requestAnimationFrame(frame);
}

function buttons() {
  const done = S.p.fixed.t >= END;
  $('#start').disabled = S.started && !done;
  $('#start').textContent = done ? 'Replay' : 'Start';
  $('#pause').disabled = !S.started || done;
  $('#pause').textContent = S.started && !S.running && !done ? 'Resume' : 'Pause';
}

function reset() {
  S.p = { fixed: makePanel(false, S.T), adaptive: makePanel(true, S.T) };
  S.running = false; S.started = false; S.acc = 0;
  buttons(); render();
}

document.addEventListener('DOMContentLoaded', () => {
  S.el = { fixed: buildPanel('fixed'), adaptive: buildPanel('adaptive') };
  $('#panels').append(S.el.fixed, S.el.adaptive);
  $('#temp').addEventListener('input', e => { S.T = +e.target.value; $('#temp-out').textContent = S.T + ' °C'; if (!S.started) reset(); else render(); });
  $('#speed').addEventListener('input', e => {
    S.speed = +e.target.value; const t = SPEEDS[S.speed] + '×';
    $('#speed-out').textContent = t; e.target.setAttribute('aria-valuetext', t);
  });
  $('#start').addEventListener('click', () => {
    if (S.p.fixed.t >= END) reset();
    S.started = true; S.running = true; buttons(); render();
  });
  $('#pause').addEventListener('click', () => { S.running = !S.running; buttons(); });
  $('#reset').addEventListener('click', reset);
  function preset(T) { S.T = T; $('#temp').value = T; $('#temp-out').textContent = T + ' °C'; reset(); S.started = true; S.running = true; buttons(); render(); }
  $('#try-hot').addEventListener('click', () => preset(90));
  $('#try-normal').addEventListener('click', () => preset(60));
  reset(); requestAnimationFrame(frame);
});
