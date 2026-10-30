/* CISC vs RISC simulator
   Part 1: execution engine (instruction sets, programs, timing)
   Part 2: user interface (panels, animation, comparison) */

/* ===== Execution engine (pure logic, no DOM) ===== */
const COST = {
  fetch: { CISC: 2, RISC: 1 }, // fetch & decode, per instruction
  read: 3,                      // one data read from memory
  write: 3,                     // one data write to memory
  alu: 1,                       // add, subtract, increment, decrement
  mul: 4,                       // multiply
  imm: 1,                       // put a constant into a register
  branch: 1                     // decide whether to jump
};

const OPSYM = { ADD: '+', SUB: '−', MUL: '×' };
const OPVERB = { ADD: 'Add', SUB: 'Subtract', MUL: 'Multiply' };
const REGS = ['R0', 'R1', 'R2', 'R3'];

const M = name => ({ t: 'mem', name });
const MX = idx => ({ t: 'memx', base: 'X', idx });
const R = n => ({ t: 'reg', r: 'R' + n });
const I = v => ({ t: 'imm', v });
const ins = (op, args, note, extra) => Object.assign({ op, args, note }, extra || {});

function fmtOperand(o) {
  if (o.t === 'mem') return o.name;
  if (o.t === 'memx') return `${o.base}[${o.idx}]`;
  if (o.t === 'reg') return o.r;
  return '#' + o.v;
}
function fmtIns(i) {
  return i.op.padEnd(5, ' ') + ' ' + i.args.map(fmtOperand).join(', ') + (i.target ? ', ' + i.target : '');
}

function opResult(op, a, b) {
  if (op === 'ADD') return a + b;
  if (op === 'SUB') return a - b;
  if (op === 'MUL') return a * b;
  throw new Error('bad op ' + op);
}
const fmtNum = v => (v === null || v === undefined) ? '—' : (v < 0 ? '−' + Math.abs(v) : String(v));

/* Programs for each task. n = list length. */
function buildPrograms(task, n) {
  if (task === 'add' || task === 'sub' || task === 'mul') {
    const op = { add: 'ADD', sub: 'SUB', mul: 'MUL' }[task];
    const s = OPSYM[op];
    return {
      CISC: [ins(op, [M('RES'), M('A'), M('B')], `RES ← A ${s} B`)],
      RISC: [
        ins('LOAD', [R(0), M('A')], 'R0 ← A'),
        ins('LOAD', [R(1), M('B')], 'R1 ← B'),
        ins(op, [R(2), R(0), R(1)], `R2 ← R0 ${s} R1`),
        ins('STORE', [R(2), M('RES')], 'RES ← R2')
      ]
    };
  }
  if (task === 'combo') {
    return {
      CISC: [
        ins('ADD', [R(0), M('A'), M('B')], 'R0 ← A + B'),
        ins('MUL', [M('RES'), R(0), M('D')], 'RES ← R0 × D')
      ],
      RISC: [
        ins('LOAD', [R(0), M('A')], 'R0 ← A'),
        ins('LOAD', [R(1), M('B')], 'R1 ← B'),
        ins('ADD', [R(2), R(0), R(1)], 'R2 ← R0 + R1'),
        ins('LOAD', [R(3), M('D')], 'R3 ← D'),
        ins('MUL', [R(2), R(2), R(3)], 'R2 ← R2 × R3'),
        ins('STORE', [R(2), M('RES')], 'RES ← R2')
      ]
    };
  }
  if (task === 'list') {
    return {
      CISC: [
        ins('MOV', [R(0), I(0)], 'sum ← 0'),
        ins('MOV', [R(1), I(0)], 'index ← 0'),
        ins('MOV', [R(2), I(n)], 'count ← ' + n),
        ins('ADD', [R(0), R(0), MX('R1')], 'sum ← sum + X[index]', { label: 'loop' }),
        ins('INC', [R(1)], 'index ← index + 1'),
        ins('DJNZ', [R(2)], 'count − 1; repeat if not 0', { target: 'loop' }),
        ins('MOV', [M('RES'), R(0)], 'RES ← sum')
      ],
      RISC: [
        ins('LI', [R(0), I(0)], 'sum ← 0'),
        ins('LI', [R(1), I(0)], 'index ← 0'),
        ins('LI', [R(2), I(n)], 'count ← ' + n),
        ins('LOAD', [R(3), MX('R1')], 'R3 ← X[index]', { label: 'loop' }),
        ins('ADD', [R(0), R(0), R(3)], 'sum ← sum + R3'),
        ins('ADDI', [R(1), R(1), I(1)], 'index ← index + 1'),
        ins('ADDI', [R(2), R(2), I(-1)], 'count ← count − 1'),
        ins('BNEZ', [R(2)], 'repeat if count ≠ 0', { target: 'loop' }),
        ins('STORE', [R(0), M('RES')], 'RES ← sum')
      ]
    };
  }
  throw new Error('unknown task ' + task);
}

function initialMemory(task, v) {
  const mem = {}, order = [];
  const put = (k, val) => { mem[k] = val; order.push(k); };
  if (task === 'list') v.list.forEach((x, i) => put(`X[${i}]`, x));
  else {
    put('A', v.A); put('B', v.B);
    if (task === 'combo') put('D', v.D);
  }
  put('RES', null);
  return { mem, order };
}

function expectedResult(task, v) {
  switch (task) {
    case 'add': return v.A + v.B;
    case 'sub': return v.A - v.B;
    case 'mul': return v.A * v.B;
    case 'combo': return (v.A + v.B) * v.D;
    case 'list': return v.list.reduce((s, x) => s + x, 0);
  }
}

const clone = s => ({ mem: Object.assign({}, s.mem), reg: Object.assign({}, s.reg), alu: Object.assign({}, s.alu) });

/* Run a program and record every internal action with a state snapshot. */
function buildTrace(isa, program, memInit) {
  const st = {
    mem: Object.assign({}, memInit),
    reg: { R0: null, R1: null, R2: null, R3: null },
    alu: { a: null, b: null, op: null, out: null }
  };
  const initial = clone(st);
  const labels = {};
  program.forEach((p, i) => { if (p.label) labels[p.label] = i; });
  const actions = [];
  let pc = 0, executed = 0;

  const addr = o => {
    if (o.t === 'mem') return o.name;
    const i = st.reg[o.idx];
    const key = `${o.base}[${i}]`;
    if (!(key in st.mem)) throw new Error('address out of range ' + key);
    return key;
  };
  const isMem = o => o.t === 'mem' || o.t === 'memx';

  while (pc < program.length) {
    if (executed > 400) throw new Error('runaway program');
    const p = program[pc];
    const start = actions.length;
    let next = pc + 1;
    const emit = (a, mutate) => {
      if (mutate) mutate(st);
      a.pc = pc; a.instr = executed; a.after = clone(st);
      a.moves = a.moves || [];
      a.highlight = a.highlight || [];
      actions.push(a);
    };
    const text = fmtIns(p).replace(/\s+/g, ' ');

    // 1. Fetch & decode
    emit({
      kind: 'fetch', cycles: COST.fetch[isa], step: 'Fetch & decode',
      text: isa === 'CISC'
        ? `Fetch and decode “${text}”. CISC instructions vary in length and may trigger several internal steps, so decoding takes ${COST.fetch.CISC} cycles in this model.`
        : `Fetch and decode “${text}”. RISC instructions have one fixed format, so decoding takes ${COST.fetch.RISC} cycle in this model.`,
      highlight: ['ctrl']
    }, s => { s.alu = { a: null, b: null, op: null, out: null }; });

    const op = p.op, a = p.args;

    if (isa === 'CISC' && OPSYM[op]) {
      const [dst, s1, s2] = a;
      const slots = ['a', 'b'];
      const regMoves = [];
      [s1, s2].forEach((src, k) => {
        const slot = slots[k];
        if (isMem(src)) {
          const key = addr(src);
          const val = st.mem[key];
          const how = src.t === 'memx' ? ` (address X + ${src.idx} = ${key})` : '';
          emit({
            kind: 'read', cycles: COST.read, step: `Read ${key}`,
            text: `Read ${key}${how} from memory: value ${fmtNum(val)} goes straight into the ALU's input ${k + 1}. No separate LOAD instruction is needed.`,
            moves: [[{ from: 'mem:' + key, to: 'alu:' + slot, value: val }]]
          }, s => { s.alu[slot] = val; });
        } else if (src.t === 'reg') {
          regMoves.push({ from: 'reg:' + src.r, to: 'alu:' + slot, value: st.reg[src.r] });
        }
      });
      const va = s1.t === 'reg' ? st.reg[s1.r] : st.alu.a;
      const vb = s2.t === 'reg' ? st.reg[s2.r] : st.alu.b;
      const res = opResult(op, va, vb);
      const phases = [];
      if (regMoves.length) phases.push(regMoves);
      phases.push([]); // compute
      if (dst.t === 'reg') phases.push([{ from: 'alu:out', to: 'reg:' + dst.r, value: res }]);
      emit({
        kind: op === 'MUL' ? 'mul' : 'alu', cycles: op === 'MUL' ? COST.mul : COST.alu, step: OPVERB[op],
        text: `${OPVERB[op]}: ${fmtNum(va)} ${OPSYM[op]} ${fmtNum(vb)} = ${fmtNum(res)}` +
          (dst.t === 'reg' ? `. The result is placed in register ${dst.r}.` : '. The result waits at the ALU output.'),
        moves: phases, highlight: ['alu']
      }, s => {
        s.alu = { a: va, b: vb, op: OPSYM[op], out: res };
        if (dst.t === 'reg') s.reg[dst.r] = res;
      });
      if (isMem(dst)) {
        const key = addr(dst);
        emit({
          kind: 'write', cycles: COST.write, step: `Write ${key}`,
          text: `Write the result ${fmtNum(res)} from the ALU back to memory location ${key}, still inside the same instruction.`,
          moves: [[{ from: 'alu:out', to: 'mem:' + key, value: res }]]
        }, s => { s.mem[key] = res; });
      }
    } else if (isa === 'CISC' && op === 'MOV') {
      const [dst, src] = a;
      if (src.t === 'imm' && dst.t === 'reg') {
        emit({
          kind: 'imm', cycles: COST.imm, step: `Set ${dst.r}`,
          text: `Put the constant ${fmtNum(src.v)} (part of the instruction itself) into register ${dst.r}. No memory access.`,
          moves: [[{ from: 'ctrl', to: 'reg:' + dst.r, value: src.v }]]
        }, s => { s.reg[dst.r] = src.v; });
      } else if (src.t === 'reg' && isMem(dst)) {
        const key = addr(dst), val = st.reg[src.r];
        emit({
          kind: 'write', cycles: COST.write, step: `Write ${key}`,
          text: `Copy register ${src.r} (${fmtNum(val)}) into memory location ${key}.`,
          moves: [[{ from: 'reg:' + src.r, to: 'mem:' + key, value: val }]]
        }, s => { s.mem[key] = val; });
      } else throw new Error('MOV form not used in this model');
    } else if (isa === 'CISC' && op === 'INC') {
      const r = a[0].r, v = st.reg[r];
      emit({
        kind: 'alu', cycles: COST.alu, step: 'Add 1',
        text: `Increment ${r}: ${fmtNum(v)} + 1 = ${fmtNum(v + 1)}.`,
        moves: [[{ from: 'reg:' + r, to: 'alu:a', value: v }, { from: 'ctrl', to: 'alu:b', value: 1 }], [], [{ from: 'alu:out', to: 'reg:' + r, value: v + 1 }]],
        highlight: ['alu']
      }, s => { s.alu = { a: v, b: 1, op: '+', out: v + 1 }; s.reg[r] = v + 1; });
    } else if (isa === 'CISC' && op === 'DJNZ') {
      const r = a[0].r, v = st.reg[r], nv = v - 1;
      emit({
        kind: 'alu', cycles: COST.alu, step: 'Subtract 1',
        text: `Decrement the loop counter ${r}: ${fmtNum(v)} − 1 = ${fmtNum(nv)}.`,
        moves: [[{ from: 'reg:' + r, to: 'alu:a', value: v }, { from: 'ctrl', to: 'alu:b', value: 1 }], [], [{ from: 'alu:out', to: 'reg:' + r, value: nv }]],
        highlight: ['alu']
      }, s => { s.alu = { a: v, b: 1, op: '−', out: nv }; s.reg[r] = nv; });
      const jump = nv !== 0;
      if (jump) next = labels[p.target];
      emit({
        kind: 'branch', cycles: COST.branch, step: jump ? 'Jump back' : 'Continue',
        text: jump
          ? `${r} is ${fmtNum(nv)}, not zero, so jump back to “${p.target}” for another pass. Same instruction, second internal step.`
          : `${r} is now 0, so the loop is finished. Continue with the next instruction.`,
        highlight: ['reg:' + r, 'ctrl']
      });
    } else if (isa === 'RISC' && op === 'LI') {
      const r = a[0].r, v = a[1].v;
      emit({
        kind: 'imm', cycles: COST.imm, step: `Set ${r}`,
        text: `Put the constant ${fmtNum(v)} (part of the instruction itself) into register ${r}. No memory access.`,
        moves: [[{ from: 'ctrl', to: 'reg:' + r, value: v }]]
      }, s => { s.reg[r] = v; });
    } else if (isa === 'RISC' && op === 'LOAD') {
      const r = a[0].r, key = addr(a[1]), v = st.mem[key];
      const how = a[1].t === 'memx' ? ` (address X + ${a[1].idx} = ${key})` : '';
      emit({
        kind: 'read', cycles: COST.read, step: `Read ${key}`,
        text: `LOAD reads ${key}${how} from memory and copies its value ${fmtNum(v)} into register ${r}. In RISC, only LOAD can read memory.`,
        moves: [[{ from: 'mem:' + key, to: 'reg:' + r, value: v }]]
      }, s => { s.reg[r] = v; });
    } else if (isa === 'RISC' && op === 'STORE') {
      const r = a[0].r, key = addr(a[1]), v = st.reg[r];
      emit({
        kind: 'write', cycles: COST.write, step: `Write ${key}`,
        text: `STORE copies register ${r} (${fmtNum(v)}) into memory location ${key}. In RISC, only STORE can write memory.`,
        moves: [[{ from: 'reg:' + r, to: 'mem:' + key, value: v }]]
      }, s => { s.mem[key] = v; });
    } else if (isa === 'RISC' && OPSYM[op]) {
      const [d, x, y] = a.map(o => o.r);
      const va = st.reg[x], vb = st.reg[y], res = opResult(op, va, vb);
      emit({
        kind: op === 'MUL' ? 'mul' : 'alu', cycles: op === 'MUL' ? COST.mul : COST.alu, step: OPVERB[op],
        text: `${OPVERB[op]} registers: ${x} (${fmtNum(va)}) ${OPSYM[op]} ${y} (${fmtNum(vb)}) = ${fmtNum(res)}, saved in ${d}. RISC arithmetic only uses registers.`,
        moves: [[{ from: 'reg:' + x, to: 'alu:a', value: va }, { from: 'reg:' + y, to: 'alu:b', value: vb }], [], [{ from: 'alu:out', to: 'reg:' + d, value: res }]],
        highlight: ['alu']
      }, s => { s.alu = { a: va, b: vb, op: OPSYM[op], out: res }; s.reg[d] = res; });
    } else if (isa === 'RISC' && op === 'ADDI') {
      const d = a[0].r, x = a[1].r, c = a[2].v, va = st.reg[x], res = va + c;
      emit({
        kind: 'alu', cycles: COST.alu, step: c < 0 ? 'Subtract 1' : 'Add 1',
        text: `Add the constant ${fmtNum(c)} to ${x}: ${fmtNum(va)} + ${c < 0 ? '(' + fmtNum(c) + ')' : fmtNum(c)} = ${fmtNum(res)}, saved in ${d}.`,
        moves: [[{ from: 'reg:' + x, to: 'alu:a', value: va }, { from: 'ctrl', to: 'alu:b', value: c }], [], [{ from: 'alu:out', to: 'reg:' + d, value: res }]],
        highlight: ['alu']
      }, s => { s.alu = { a: va, b: c, op: '+', out: res }; s.reg[d] = res; });
    } else if (isa === 'RISC' && op === 'BNEZ') {
      const r = a[0].r, v = st.reg[r], jump = v !== 0;
      if (jump) next = labels[p.target];
      emit({
        kind: 'branch', cycles: COST.branch, step: jump ? 'Jump back' : 'Continue',
        text: jump
          ? `${r} is ${fmtNum(v)}, not zero, so jump back to “${p.target}”. Counting down and branching took two separate RISC instructions.`
          : `${r} is 0, so the loop is finished. Continue with the next instruction.`,
        highlight: ['reg:' + r, 'ctrl']
      });
    } else {
      throw new Error(`Unsupported instruction ${op} for ${isa}`);
    }

    const group = actions.slice(start);
    group.forEach((x, i) => { x.sub = i; x.subCount = group.length; x.last = i === group.length - 1; x.instrCycles = group.reduce((t, g) => t + g.cycles, 0); });
    executed++;
    pc = next;
  }
  return { isa, program, initial, actions };
}

/* Counters derived from recorded events, up to and including action index i. */
function countersAt(trace, i) {
  const c = { instructions: 0, reads: 0, writes: 0, cycles: 0, byKind: { fetch: 0, memory: 0, arith: 0, branch: 0 } };
  for (let k = 0; k <= i && k < trace.actions.length; k++) {
    const a = trace.actions[k];
    if (a.last) c.instructions++;
    if (a.kind === 'read') c.reads++;
    if (a.kind === 'write') c.writes++;
    c.cycles += a.cycles;
    if (a.kind === 'fetch') c.byKind.fetch += a.cycles;
    else if (a.kind === 'read' || a.kind === 'write') c.byKind.memory += a.cycles;
    else if (a.kind === 'branch') c.byKind.branch += a.cycles;
    else c.byKind.arith += a.cycles;
  }
  return c;
}

function stateAt(trace, i) { return i < 0 ? trace.initial : trace.actions[i].after; }


/* ===== User interface ===== */
const SPEEDS = [0.25, 0.5, 1, 1.5, 2, 3, 4];
const reduceMQ = window.matchMedia('(prefers-reduced-motion: reduce)');
const wait = ms => new Promise(r => setTimeout(r, ms));
const $ = (s, r = document) => r.querySelector(s);
const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
const plural = (n, w) => `${n} ${w}${n === 1 ? '' : 's'}`;
const LIM = 999, MAXLIST = 8;

const TASKS = {
  add:   { fields: ['A', 'B'], expr: 'A + B', examples: [{ A: '7', B: '5' }, { A: '-8', B: '3' }, { A: '0', B: '-6' }] },
  sub:   { fields: ['A', 'B'], expr: 'A − B', examples: [{ A: '7', B: '12' }, { A: '-4', B: '-9' }, { A: '0', B: '0' }] },
  mul:   { fields: ['A', 'B'], expr: 'A × B', examples: [{ A: '-6', B: '4' }, { A: '12', B: '0' }, { A: '-3', B: '-7' }] },
  combo: { fields: ['A', 'B', 'D'], expr: '(A + B) × D', examples: [{ A: '3', B: '-5', D: '4' }, { A: '6', B: '2', D: '-3' }, { A: '0', B: '7', D: '0' }] },
  list:  { fields: ['list'], expr: 'X[0] + X[1] + …', examples: [{ list: '4, -2, 0, 9' }, { list: '10, 20, 30' }, { list: '-5, 0, 5, -1, 3, 8' }] }
};

const ISA_INFO = {
  CISC: {
    name: 'Complex instruction set',
    sub: 'Arithmetic instructions can read and write memory directly.',
    ref: `<dl>
      <dt>MOV d, s</dt><dd>Copy s into d. Either may be a register or memory; s may be a constant.</dd>
      <dt>ADD d, s1, s2</dt><dd>d ← s1 + s2. Any operand may be a memory location.</dd>
      <dt>SUB d, s1, s2</dt><dd>d ← s1 − s2, same operand rules.</dd>
      <dt>MUL d, s1, s2</dt><dd>d ← s1 × s2, same operand rules.</dd>
      <dt>INC r</dt><dd>r ← r + 1.</dd>
      <dt>DJNZ r, label</dt><dd>r ← r − 1, then jump to label if r ≠ 0.</dd>
    </dl>
    <p>Operands: <code>A</code> is a memory location, <code>X[R1]</code> is memory at X plus the value of R1, <code>R0</code> is a register, <code>#5</code> is a constant.</p>`
  },
  RISC: {
    name: 'Reduced instruction set',
    sub: 'Only LOAD and STORE touch memory; arithmetic uses registers.',
    ref: `<dl>
      <dt>LI r, #c</dt><dd>r ← constant c.</dd>
      <dt>LOAD r, addr</dt><dd>r ← memory[addr].</dd>
      <dt>STORE r, addr</dt><dd>memory[addr] ← r.</dd>
      <dt>ADD d, a, b</dt><dd>d ← a + b. Registers only.</dd>
      <dt>SUB d, a, b</dt><dd>d ← a − b. Registers only.</dd>
      <dt>MUL d, a, b</dt><dd>d ← a × b. Registers only.</dd>
      <dt>ADDI d, a, #c</dt><dd>d ← a + constant c.</dd>
      <dt>BNEZ r, label</dt><dd>Jump to label if r ≠ 0.</dd>
    </dl>
    <p>Operands: <code>A</code> is a memory location, <code>X[R1]</code> is memory at X plus the value of R1, <code>R0</code> is a register, <code>#5</code> is a constant.</p>`
  }
};

/* ---------- geometry for the diagram ---------- */
const G = {
  memX: 14, memW: 148, memTop: 82, memH: 26,
  regX: 214, regW: 120, regTop: 92, regH: 30,
  ctrl: { x: 14, y: 8, w: 170, h: 46 },
  aluA: { x: 396, y: 70, w: 58, h: 26 }, aluB: { x: 486, y: 70, w: 58, h: 26 }, aluOut: { x: 432, y: 204, w: 76, h: 26 }
};
const kindOf = key => key.split(':')[0];

function curve(p1, p2) {
  const dist = Math.hypot(p2.x - p1.x, p2.y - p1.y);
  const k = Math.max(40, Math.min(120, dist * 0.4));
  return `M${p1.x},${p1.y} C${p1.x + p1.nx * k},${p1.y + p1.ny * k} ${p2.x + p2.nx * k},${p2.y + p2.ny * k} ${p2.x},${p2.y}`;
}

class Runner {
  constructor(isa, app) {
    this.isa = isa; this.app = app;
    this.gen = 0; this.status = 'invalid'; this.idx = -1; this.busy = false; this.looping = false; this.trace = null;
    this.build();
  }

  build() {
    const i = this.isa, info = ISA_INFO[i], id = i.toLowerCase();
    const s = document.createElement('section');
    s.className = 'proc'; s.dataset.isa = i; s.setAttribute('aria-labelledby', id + '-h');
    s.innerHTML = `
      <header class="proc-head">
        <div><h2 id="${id}-h"><span class="tag">${i}</span> ${info.name}</h2><p>${info.sub}</p></div>
        <button class="run" type="button">Run ${i}</button>
      </header>
      <div class="proc-main">
        <div class="playbar">
          <button class="btn pause" type="button">Pause</button>
          <button class="btn step" type="button">Next step</button>
          <div class="progress" role="progressbar" aria-label="${i} progress" aria-valuemin="0" aria-valuemax="100" aria-valuenow="0"><span></span></div>
          <span class="progress-text"></span>
        </div>
        <dl class="counters">
          <div><dt>Instructions</dt><dd data-c="instructions">0</dd></div>
          <div><dt>Memory reads</dt><dd data-c="reads">0</dd></div>
          <div><dt>Memory writes</dt><dd data-c="writes">0</dd></div>
          <div><dt>Cycles (simulated)</dt><dd data-c="cycles">0</dd></div>
        </dl>
        <div class="diagram"></div>
        <p class="diagram-note"></p>
        <div class="now">
          <p class="explain" aria-live="polite"></p>
          <details class="why-step"><summary>Internal actions</summary>
            <p class="micro-sum"></p>
            <ol class="micro" aria-label="Internal actions of the current instruction"></ol>
          </details>
        </div>
        <div class="program">
          <h3>Program <small>teaching pseudocode</small></h3>
          <ol class="listing" aria-label="${i} program"></ol>
          <details class="isa"><summary>${i} instruction set</summary>${info.ref}</details>
        </div>
        <p class="result"></p>
      </div>`;
    this.root = s;
    this.runBtn = $('.run', s); this.pauseBtn = $('.pause', s); this.stepBtn = $('.step', s);
    this.bar = $('.progress span', s); this.barWrap = $('.progress', s); this.progText = $('.progress-text', s);
    this.listing = $('.listing', s); this.diagram = $('.diagram', s);
    this.diagNote = $('.diagram-note', s); this.microSum = $('.micro-sum', s); this.micro = $('.micro', s); this.explain = $('.explain', s); this.result = $('.result', s);
    this.runBtn.addEventListener('click', () => this.run());
    this.pauseBtn.addEventListener('click', () => this.togglePause());
    this.stepBtn.addEventListener('click', () => this.step());
  }

  /* ---------- lifecycle ---------- */
  load(trace, memOrder, expected) {
    this.gen++; this.looping = false; this.busy = false;
    this.trace = trace; this.memOrder = memOrder; this.expected = expected;
    this.status = 'idle'; this.idx = -1;
    this.buildListing(); this.buildSvg();
    this.markUnusedRegisters(); this.setDiagNote();
    this.renderState(-1); this.renderIdle(); this.updateButtons();
  }
  /* Registers the program never touches are drawn dashed and labelled, so it is clear they sit idle. */
  markUnusedRegisters() {
    const used = new Set();
    this.trace.program.forEach(p => p.args.forEach(o => { if (o.t === 'reg') used.add(o.r); if (o.t === 'memx') used.add(o.idx); }));
    REGS.forEach(r => {
      const g = this.el('reg:' + r);
      g.classList.toggle('unused', !used.has(r));
    });
    if (!used.size) {
      const NS = 'http://www.w3.org/2000/svg', y = G.regTop + 4 * G.regH + 20;
      ['No programmer-visible registers', 'used here. Internal CPU', 'storage is omitted.'].forEach((line, k) => {
        const t = document.createElementNS(NS, 'text');
        t.setAttribute('class', 'note'); t.setAttribute('x', G.regX); t.setAttribute('y', y + k * 14); t.textContent = line;
        this.svg.insertBefore(t, this.flows);
      });
    }
  }
  setDiagNote() {
    const fict = this.isa === 'CISC' && this.trace.program.some(p => p.args.filter(o => o.t === 'mem' || o.t === 'memx').length >= 2);
    this.diagNote.textContent = fict ? 'Fictional teaching instruction: one instruction takes its operands from memory and writes the result back to memory.' : '';
    this.diagNote.hidden = !fict;
  }
  reload() { if (this.trace) this.load(this.trace, this.memOrder, this.expected); }
  invalidate() {
    this.gen++; this.looping = false; this.busy = false; this.trace = null; this.status = 'invalid'; this.idx = -1;
    this.listing.innerHTML = ''; this.diagram.innerHTML = ''; this.diagNote.hidden = true;
    this.microSum.textContent = ''; this.micro.innerHTML = '';
    this.explain.textContent = 'Fix the inputs above to load this program.';
    this.result.textContent = '';
    this.setCounters({ instructions: 0, reads: 0, writes: 0, cycles: 0 });
    this.setProgress(0, 'Waiting for valid inputs');
    this.updateButtons();
  }

  run(quiet) {
    if (!this.trace || this.status === 'running' || this.status === 'paused') return;
    if (this.status === 'done') this.reload();
    this.status = 'running'; this.updateButtons(); if (!quiet) this.reveal(); this.loop();
  }
  /* Bring the diagram and current-step box into view so the animation is visible. */
  reveal() {
    const d = this.root.querySelector('.playbar'), now = this.root.querySelector('.now');
    if (!d || !now) return;
    const bar = document.querySelector('.toolbar');
    const barH = bar ? bar.getBoundingClientRect().height + 16 : 16;
    const top = d.getBoundingClientRect().top, bottom = now.getBoundingClientRect().bottom;
    if (top >= barH && bottom <= window.innerHeight) return;
    const room = window.innerHeight - barH;
    const target = window.scrollY + top - barH - Math.max(0, (room - (bottom - top)) / 2);
    window.scrollTo({ top: Math.max(0, target), behavior: reduceMQ.matches ? 'auto' : 'smooth' });
  }
  togglePause() {
    if (this.status === 'running') { this.status = 'paused'; this.updateButtons(); }
    else if (this.status === 'paused') { this.status = 'running'; this.updateButtons(); this.loop(); }
  }
  async step() {
    if (!this.trace || this.busy) return;
    if (this.status === 'idle') { this.status = 'paused'; this.reveal(); }
    if (this.status !== 'paused') return;
    const g = this.gen;
    await this.playNext(g);
    if (g === this.gen && this.idx === this.trace.actions.length - 1) this.finish();
  }
  async loop() {
    if (this.looping) return;
    this.looping = true;
    const g = this.gen;
    while (this.gen === g && this.status === 'running' && this.idx < this.trace.actions.length - 1) {
      await this.playNext(g);
    }
    if (this.gen !== g) return;
    this.looping = false;
    if (this.idx === this.trace.actions.length - 1 && this.status !== 'done') this.finish();
  }
  async playNext(g) {
    this.busy = true; this.updateButtons();
    const i = this.idx + 1, a = this.trace.actions[i];
    this.renderPre(a);
    await this.animate(a, g);
    if (g !== this.gen) return;
    this.idx = i;
    this.renderState(i); this.renderPost(a);
    this.busy = false; this.updateButtons();
  }
  finish() {
    this.status = 'done';
    const t = this.trace, last = t.actions.length - 1, c = countersAt(t, last);
    const res = stateAt(t, last).mem.RES;
    const ok = res === this.expected;
    this.listing.querySelectorAll('li').forEach(li => { li.classList.remove('active'); li.removeAttribute('aria-current'); $('.ptr', li).textContent = ''; });
    this.setCtrlText('finished');
    this.microSum.textContent = '';
    this.micro.innerHTML = '';
    this.explain.textContent = `Complete: ${plural(c.instructions, 'instruction')} · ${c.cycles} simulated cycles.`;
    this.result.innerHTML = `Result in RES: <strong>${fmtNum(res)}</strong> ` +
      (ok ? `<span class="ok">✓ correct</span>` : `<span class="bad">✗ expected ${fmtNum(this.expected)}</span>`);
    this.setProgress(100, `Finished: ${plural(c.instructions, 'instruction')}, ${c.cycles} cycles`);
    this.updateButtons();
    this.app.onFinish(this.isa);
  }

  updateButtons() {
    const st = this.status, active = st === 'running' || st === 'paused';
    this.runBtn.disabled = !this.trace || active;
    this.runBtn.textContent = st === 'done' ? `Replay ${this.isa}` : active ? 'Running…' : `Run ${this.isa}`;
    this.pauseBtn.disabled = !active;
    this.pauseBtn.textContent = st === 'paused' ? 'Resume' : 'Pause';
    this.stepBtn.disabled = !this.trace || this.busy || !(st === 'idle' || st === 'paused');
    if (this.app.syncShared) this.app.syncShared();
  }

  /* ---------- static structure ---------- */
  buildListing() {
    const prog = this.trace.program;
    this.listing.innerHTML = prog.map((p, k) =>
      `<li data-pc="${k}"><span class="ptr" aria-hidden="true"></span><span class="lbl">${p.label ? p.label + ':' : ''}</span><code>${esc(fmtIns(p))}</code><span class="cmt">${esc(p.note)}</span></li>`
    ).join('');
  }

  buildSvg() {
    const i = this.isa, order = this.memOrder;
    const memRows = order.map((k, n) => {
      const y = G.memTop + n * G.memH;
      return `<g class="memc" data-k="mem:${esc(k)}"><rect x="${G.memX}" y="${y}" width="${G.memW}" height="${G.memH}"/>
        <text class="nm" x="${G.memX + 10}" y="${y + 17}">${esc(k)}</text>
        <text class="v" x="${G.memX + G.memW - 10}" y="${y + 18}" text-anchor="end">—</text></g>`;
    }).join('');
    const regRows = REGS.map((r, n) => {
      const y = G.regTop + n * G.regH;
      return `<g class="regc" data-k="reg:${r}"><rect x="${G.regX}" y="${y}" width="${G.regW}" height="${G.regH}" rx="4"/>
        <text class="nm" x="${G.regX + 10}" y="${y + 19}">${r}</text>
        <text class="v" x="${G.regX + G.regW - 10}" y="${y + 20}" text-anchor="end">—</text></g>`;
    }).join('');
    const box = (b, k) => `<g class="alub" data-k="${k}"><rect class="alubox" x="${b.x}" y="${b.y}" width="${b.w}" height="${b.h}" rx="4"/>
      <text class="v" x="${b.x + b.w / 2}" y="${b.y + 18}" text-anchor="middle">—</text></g>`;
    const marker = c => `<marker id="${i}-ah-${c}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="11" markerHeight="11" markerUnits="userSpaceOnUse" orient="auto"><path class="${c}" d="M0,0 L10,5 L0,10 z"/></marker>`;
    const c = G.ctrl;
    this.diagram.innerHTML = `
<svg viewBox="0 0 560 324" role="img" aria-labelledby="${i}-svgt">
  <title id="${i}-svgt">${i} data path: control unit at the top left, memory below it, registers in the middle, ALU on the right. Values are also described in the current step text.</title>
  <defs>${['mem', 'reg', 'alu', 'ctrl'].map(marker).join('')}</defs>
  <text class="ttl" x="${G.memX}" y="${G.memTop - 8}" style="fill:var(--mem)">Memory</text>
  ${memRows}
  <g data-k="ctrl"><rect class="ctrlbox" x="${c.x}" y="${c.y}" width="${c.w}" height="${c.h}" rx="6"/>
    <text class="small" x="${c.x + 10}" y="${c.y + 17}">Control unit</text>
    <text class="v ctrltext" x="${c.x + 10}" y="${c.y + 36}" style="font-size:12px">idle</text></g>
  <text class="ttl" x="${G.regX}" y="84" style="fill:var(--reg)">Registers</text>
  ${regRows}
  <line class="wire" x1="425" y1="96" x2="425" y2="104"/><line class="wire" x1="515" y1="96" x2="515" y2="104"/><line class="wire" x1="470" y1="190" x2="470" y2="204"/>
  <g data-k="alu"><polygon class="alubody" points="392,104 458,104 470,122 482,104 548,104 516,190 424,190"/>
    <text class="aluop" x="470" y="160" text-anchor="middle"> </text>
    <text class="alulbl" x="470" y="182" text-anchor="middle">ALU</text></g>
  ${box(G.aluA, 'alu:a')}${box(G.aluB, 'alu:b')}${box(G.aluOut, 'alu:out')}
  <text class="small" x="392" y="88" text-anchor="end">in 1</text>
  <text class="small" x="483" y="88" text-anchor="end">in 2</text>
  <text class="small" x="428" y="222" text-anchor="end">out</text>
  <g class="flows"></g>
</svg>`;
    this.svg = $('svg', this.diagram);
    this.flows = $('.flows', this.svg);
    this.memPos = {};
    order.forEach((k, n) => { this.memPos[k] = G.memTop + n * G.memH + G.memH / 2; });
  }

  el(key) { return this.svg && this.svg.querySelector(`[data-k="${CSS.escape(key)}"]`); }

  setVal(key, v, changed) {
    const g = this.el(key); if (!g) return;
    const t = $('.v', g), s = g.classList.contains('unused') ? 'not used' : fmtNum(v);
    t.textContent = s;
    t.style.fontSize = s.length > 7 ? '11px' : '';
    g.classList.toggle('changed', !!changed);
  }
  setCtrlText(s) { const t = this.svg && $('.ctrltext', this.svg); if (t) t.textContent = s; }

  /* ---------- rendering ---------- */
  renderState(i) {
    const st = stateAt(this.trace, i), prev = i >= 0 ? stateAt(this.trace, i - 1) : st;
    this.memOrder.forEach(k => this.setVal('mem:' + k, st.mem[k], st.mem[k] !== prev.mem[k]));
    REGS.forEach(r => this.setVal('reg:' + r, st.reg[r], st.reg[r] !== prev.reg[r]));
    this.setVal('alu:a', st.alu.a); this.setVal('alu:b', st.alu.b); this.setVal('alu:out', st.alu.out);
    $('.aluop', this.svg).textContent = st.alu.op || ' ';
    if (i >= 0) {
      const c = countersAt(this.trace, i);
      this.setCounters(c);
      this.setProgress(Math.round((i + 1) / this.trace.actions.length * 100));
    } else this.setCounters({ instructions: 0, reads: 0, writes: 0, cycles: 0 });
  }
  setCounters(c) { ['instructions', 'reads', 'writes', 'cycles'].forEach(k => { $(`[data-c="${k}"]`, this.root).textContent = c[k]; }); }
  setProgress(pct, text) {
    this.bar.style.width = pct + '%';
    this.barWrap.setAttribute('aria-valuenow', pct);
    if (text !== undefined) this.progText.textContent = text;
  }

  renderIdle() {
    const p = this.trace.program;
    this.listing.querySelectorAll('li').forEach(li => { li.classList.remove('active'); li.removeAttribute('aria-current'); $('.ptr', li).textContent = ''; });
    this.setCtrlText('idle');
    this.microSum.textContent = 'Each instruction is carried out as a short sequence of internal actions. They will appear here.';
    this.micro.innerHTML = '';
    this.explain.textContent = `Press Run or Next step to follow the data.`;
    this.result.innerHTML = 'Result in RES: <strong>—</strong> (not computed yet)';
    this.setProgress(0, 'Not started');
  }

  renderPre(a) {
    const t = this.trace, p = t.program[a.pc];
    this.listing.querySelectorAll('li').forEach(li => {
      const on = +li.dataset.pc === a.pc;
      li.classList.toggle('active', on);
      $('.ptr', li).textContent = on ? '▶' : '';
      if (on) li.setAttribute('aria-current', 'step'); else li.removeAttribute('aria-current');
    });
    this.setCtrlText(fmtIns(p).replace(/\s+/g, ' '));
    const group = t.actions.filter(x => x.instr === a.instr);
    const totalInstr = t.actions[t.actions.length - 1].instr + 1;
    this.microSum.innerHTML = `Instruction ${a.instr + 1} of ${totalInstr}: <code>${esc(fmtIns(p).replace(/\s+/g, ' '))}</code> runs as ${plural(group.length, 'internal action')} costing ${a.instrCycles} cycles.`;
    this.micro.innerHTML = group.map((x, k) =>
      `<li class="${k < a.sub ? 'done' : k === a.sub ? 'cur' : ''}">${esc(x.step)} <span class="mono">(${x.cycles})</span></li>`).join('');
    this.explain.innerHTML = `${esc(a.text)} <span class="cyc">+${plural(a.cycles, 'cycle')}</span>`;
    this.progText.textContent = `Instruction ${a.instr + 1} of ${totalInstr}, internal action ${a.sub + 1} of ${a.subCount}`;
  }
  renderPost(a) {
    const items = this.micro.querySelectorAll('li');
    if (items[a.sub]) items[a.sub].className = 'done';
  }

  /* ---------- animation ---------- */
  anchor(key, other) {
    const ok = other ? kindOf(other) : '';
    if (key === 'ctrl') return { x: G.ctrl.x + G.ctrl.w, y: G.ctrl.y + 23, nx: 1, ny: 0 };
    if (key === 'alu:a') return { x: G.aluA.x + G.aluA.w / 2, y: G.aluA.y, nx: 0, ny: -1 };
    if (key === 'alu:b') return { x: G.aluB.x + G.aluB.w / 2, y: G.aluB.y, nx: 0, ny: -1 };
    if (key === 'alu:out') return { x: G.aluOut.x + G.aluOut.w / 2, y: G.aluOut.y + G.aluOut.h, nx: 0, ny: 1 };
    if (key.startsWith('mem:')) return { x: G.memX + G.memW, y: this.memPos[key.slice(4)], nx: 1, ny: 0 };
    if (key.startsWith('reg:')) {
      const y = G.regTop + REGS.indexOf(key.slice(4)) * G.regH + G.regH / 2;
      return ok === 'mem' ? { x: G.regX, y, nx: -1, ny: 0 } : { x: G.regX + G.regW, y, nx: 1, ny: 0 };
    }
  }

  async flow(m, g) {
    const NS = 'http://www.w3.org/2000/svg';
    const cls = kindOf(m.from);
    const d = curve(this.anchor(m.from, m.to), this.anchor(m.to, m.from));
    const path = document.createElementNS(NS, 'path'); path.setAttribute('class', 'flow ' + cls); path.setAttribute('d', d);
    const tok = document.createElementNS(NS, 'g'); tok.setAttribute('class', 'token ' + cls);
    const label = fmtNum(m.value), w = 14 + label.length * 8;
    tok.innerHTML = `<rect x="${-w / 2}" y="-12" width="${w}" height="24" rx="12"/><text x="0" y="4.5" text-anchor="middle">${esc(label)}</text>`;
    this.flows.append(path, tok);
    const L = path.getTotalLength();
    const dur = 800 / this.app.speed();
    const place = f => { const pt = path.getPointAtLength(L * f); tok.setAttribute('transform', `translate(${pt.x},${pt.y})`); };
    const done = () => { path.style.strokeDasharray = ''; path.style.strokeDashoffset = ''; path.setAttribute('marker-end', `url(#${this.isa}-ah-${cls})`); place(1); };
    if (reduceMQ.matches) { done(); await wait(dur); return; }
    path.style.strokeDasharray = L; path.style.strokeDashoffset = L;
    place(0);
    await new Promise(resolve => {
      const t0 = performance.now();
      const frame = now => {
        if (g !== this.gen) return resolve();
        const f = Math.min(1, (now - t0) / dur), e = f < .5 ? 2 * f * f : 1 - Math.pow(-2 * f + 2, 2) / 2;
        path.style.strokeDashoffset = L * (1 - e); place(e);
        if (f < 1) requestAnimationFrame(frame); else { done(); resolve(); }
      };
      requestAnimationFrame(frame);
    });
  }

  async animate(a, g) {
    const sp = () => this.app.speed();
    this.flows.innerHTML = '';
    this.svg.querySelectorAll('.changed').forEach(n => n.classList.remove('changed'));
    const keys = new Set(a.highlight);
    a.moves.flat().forEach(m => { keys.add(m.from); keys.add(m.to); });
    const lit = [...keys].map(k => this.el(k)).filter(Boolean);
    lit.forEach(n => n.classList.add('hl'));
    if (a.kind === 'fetch') { this.setVal('alu:a', null); this.setVal('alu:b', null); this.setVal('alu:out', null); $('.aluop', this.svg).textContent = ' '; }
    if (!a.moves.length) await wait(750 / sp());
    for (const phase of a.moves) {
      if (g !== this.gen) return;
      if (!phase.length) {           // ALU computes
        const alu = this.el('alu');
        $('.aluop', this.svg).textContent = a.after.alu.op;
        alu.classList.add('computing', 'hl');
        await wait(550 / sp());
        if (g !== this.gen) return;
        alu.classList.remove('computing');
        this.setVal('alu:out', a.after.alu.out, true);
        await wait(200 / sp());
        continue;
      }
      await Promise.all(phase.map(m => this.flow(m, g)));
      if (g !== this.gen) return;
      phase.forEach(m => this.setVal(m.to, m.value, true));
      await wait(150 / sp());
    }
    if (g !== this.gen) return;
    await wait(300 / sp());
    if (g !== this.gen) return;
    this.flows.querySelectorAll('.token').forEach(t => t.remove());
    this.flows.querySelectorAll('.flow').forEach(p => p.style.opacity = '.35');
    this.svg.querySelectorAll('.hl').forEach(n => n.classList.remove('hl'));
  }
}

/* ---------- application ---------- */
const app = {
  task: 'add',
  raw: Object.fromEntries(Object.keys(TASKS).map(k => [k, Object.assign({}, TASKS[k].examples[0])])),
  exIndex: Object.fromEntries(Object.keys(TASKS).map(k => [k, 0])),
  finished: { CISC: false, RISC: false },
  traces: null, values: null,
  speed() { return SPEEDS[+$('#speed').value] || 1; },

  init() {
    this.runners = { CISC: new Runner('CISC', this), RISC: new Runner('RISC', this) };
    $('#panels').append(this.runners.CISC.root, this.runners.RISC.root);
    $('#cost-rows').innerHTML = [
      ['Fetch &amp; decode (every instruction)', COST.fetch.CISC, COST.fetch.RISC],
      ['Read one value from memory', COST.read, COST.read],
      ['Write one value to memory', COST.write, COST.write],
      ['Add, subtract, increment, decrement', COST.alu, COST.alu],
      ['Multiply', COST.mul, COST.mul],
      ['Put a constant into a register', COST.imm, COST.imm],
      ['Decide whether to jump (branch)', COST.branch, COST.branch]
    ].map(r => `<tr><td>${r[0]}</td><td class="num">${plural(r[1], 'cycle')}</td><td class="num">${plural(r[2], 'cycle')}</td></tr>`).join('');
    document.querySelectorAll('input[name="task"]').forEach(r => r.addEventListener('change', () => { this.task = r.value; this.renderInputs(); this.rebuild(); }));
    $('#example').addEventListener('click', () => {
      const t = this.task, ex = TASKS[t].examples;
      this.exIndex[t] = (this.exIndex[t] + 1) % ex.length;
      this.raw[t] = Object.assign({}, ex[this.exIndex[t]]);
      this.renderInputs(); this.rebuild();
    });
    const sp = $('#speed');
    sp.addEventListener('input', () => { const v = SPEEDS[+sp.value] + '×'; $('#speed-out').textContent = v; sp.setAttribute('aria-valuetext', v); });
    $('#reset').addEventListener('click', () => this.resetAll());
    $('#run-both').addEventListener('click', () => this.runBoth());
    $('#pause-both').addEventListener('click', () => this.pauseBoth());
    document.querySelectorAll('input[name="p1"],input[name="p2"]').forEach(r => r.addEventListener('change', () => { if (this.finished.CISC && this.finished.RISC) this.renderCompare(); }));
    this.renderInputs(); this.rebuild();
  },

  renderInputs() {
    const t = this.task, box = $('#inputs');
    if (t === 'list') {
      box.innerHTML = `<div class="field wide"><label for="in-list">Numbers (comma-separated)</label>
        <input id="in-list" type="text" inputmode="text" autocomplete="off" spellcheck="false" value="${esc(this.raw.list.list)}" aria-describedby="limits"></div>`;
      $('#limits').textContent = `1 to ${MAXLIST} whole numbers, each from −${LIM} to ${LIM}. Example: 4, -2, 0, 9`;
    } else {
      box.innerHTML = TASKS[t].fields.map(f => `<div class="field"><label for="in-${f}">${f}</label>
        <input id="in-${f}" type="number" step="1" min="-${LIM}" max="${LIM}" value="${esc(this.raw[t][f])}" aria-describedby="limits"></div>`).join('');
      $('#limits').textContent = `Whole numbers: −${LIM} to ${LIM}.`;
    }
    TASKS[t].fields.forEach(f => {
      $('#in-' + f).addEventListener('input', e => { this.raw[t][f] = e.target.value; this.rebuild(); });
    });
  },

  validate() {
    const t = this.task, raw = this.raw[t], errors = [], values = {};
    const parse = s => {
      const v = String(s).trim().replace(/[−–]/g, '-');
      if (!/^[-+]?\d+$/.test(v)) return { err: 'is not a whole number' };
      const n = parseInt(v, 10);
      if (Math.abs(n) > LIM) return { err: `must be between −${LIM} and ${LIM}` };
      return { n: n === 0 ? 0 : n };
    };
    if (t === 'list') {
      const s = String(raw.list).trim();
      if (!s) errors.push(['list', 'Enter at least one number.']);
      else {
        const parts = s.split(',').map(x => x.trim());
        if (parts[parts.length - 1] === '' && parts.length > 1) parts.pop();
        if (parts.some(x => x === '')) errors.push(['list', 'There is an empty entry between two commas.']);
        else if (parts.length > MAXLIST) errors.push(['list', `Use at most ${MAXLIST} numbers (you entered ${parts.length}).`]);
        else {
          const list = [];
          parts.forEach((p, k) => { const r = parse(p); if (r.err) errors.push(['list', `Item ${k + 1} (“${p}”) ${r.err}.`]); else list.push(r.n); });
          values.list = list;
        }
      }
    } else {
      TASKS[t].fields.forEach(f => {
        if (String(raw[f]).trim() === '') { errors.push([f, `${f} is empty. Enter a whole number from −${LIM} to ${LIM}.`]); return; }
        const r = parse(raw[f]);
        if (r.err) errors.push([f, `${f} ${r.err}.`]); else values[f] = r.n;
      });
    }
    return { ok: !errors.length, errors, values };
  },

  rebuild() {
    const t = this.task, v = this.validate();
    TASKS[t].fields.forEach(f => { const inp = $('#in-' + f); if (inp) inp.setAttribute('aria-invalid', v.errors.some(e => e[0] === f) ? 'true' : 'false'); });
    $('#errors').innerHTML = v.errors.map(e => `<p class="err">${esc(e[1])}</p>`).join('');
    this.finished = { CISC: false, RISC: false };
    this.hideCompare();
    if (!v.ok) {
      this.traces = null;
      $('#statement').textContent = 'Fix the inputs to load both programs. Both processors reset whenever the inputs change.';
      this.runners.CISC.invalidate(); this.runners.RISC.invalidate();
      return;
    }
    this.values = v.values;
    const n = t === 'list' ? v.values.list.length : 0;
    const progs = buildPrograms(t, n);
    const { mem, order } = initialMemory(t, v.values);
    const expected = expectedResult(t, v.values);
    this.expected = expected;
    this.traces = { CISC: buildTrace('CISC', progs.CISC, mem), RISC: buildTrace('RISC', progs.RISC, mem) };
    this.runners.CISC.load(this.traces.CISC, order, expected);
    this.runners.RISC.load(this.traces.RISC, order, expected);
    let given;
    if (t === 'list') given = `X = [${v.values.list.map(fmtNum).join(', ')}]`;
    else given = TASKS[t].fields.map(f => `${f} = ${fmtNum(v.values[f])}`).join(', ');
    $('#statement').innerHTML = `<code>RES = ${TASKS[t].expr}</code> <span class="statement-answer">Expected result: <strong class="mono">${fmtNum(expected)}</strong></span>`;
  },

  /* Start both processors from the beginning at the same moment so they can be watched side by side. */
  runBoth() {
    if (!this.traces) return;
    const rs = [this.runners.CISC, this.runners.RISC];
    if (rs.some(r => r.status === 'running' || r.status === 'paused')) return;
    rs.forEach(r => r.reload());
    rs.forEach(r => r.run(true));
    this.runners.CISC.reveal();
  },
  pauseBoth() {
    const rs = [this.runners.CISC, this.runners.RISC];
    if (rs.some(r => r.status === 'running')) rs.forEach(r => { if (r.status === 'running') r.togglePause(); });
    else rs.forEach(r => { if (r.status === 'paused') r.togglePause(); });
  },
  syncShared() {
    if (!this.runners || !this.runners.RISC) return;
    const rs = [this.runners.CISC, this.runners.RISC];
    const active = rs.some(r => r.status === 'running' || r.status === 'paused');
    const anyRunning = rs.some(r => r.status === 'running');
    const rb = $('#run-both'), pb = $('#pause-both');
    rb.disabled = !this.traces || active;
    rb.textContent = rs.every(r => r.status === 'done') ? 'Replay both together' : 'Run both together';
    pb.disabled = !active;
    pb.textContent = active && !anyRunning ? 'Resume both' : 'Pause both';
  },
  resetAll() {
    this.finished = { CISC: false, RISC: false };
    this.hideCompare();
    if (this.traces) { this.runners.CISC.reload(); this.runners.RISC.reload(); }
  },

  onFinish(isa) {
    this.finished[isa] = true;
    if (this.finished.CISC && this.finished.RISC) this.renderCompare();
  },

  hideCompare() { $('#cmp-body').hidden = true; $('#cmp-pending').hidden = false; },

  renderCompare() {
    const tc = this.traces.CISC, tr = this.traces.RISC;
    const c = countersAt(tc, tc.actions.length - 1), r = countersAt(tr, tr.actions.length - 1);
    const rc = stateAt(tc, tc.actions.length - 1).mem.RES, rr = stateAt(tr, tr.actions.length - 1).mem.RES;
    const mark = v => v === this.expected ? ' ✓' : ' ✗';
    const rows = [
      ['Final result (RES)', fmtNum(rc) + mark(rc), fmtNum(rr) + mark(rr)],
      ['Program length (lines)', tc.program.length, tr.program.length],
      ['Instructions executed', c.instructions, r.instructions],
      ['Memory reads', c.reads, r.reads],
      ['Memory writes', c.writes, r.writes],
      ['Simulated clock cycles', c.cycles, r.cycles]
    ];
    const same = rc === rr && rc === this.expected;
    $('#cmp-takeaways').innerHTML = [
      [same ? 'Same result' : 'Results differ', same ? fmtNum(rc) : fmtNum(rc) + ' vs ' + fmtNum(rr), same ? 'both correct' : 'check the simulator'],
      ['Instructions', c.instructions + ' vs ' + r.instructions, 'CISC vs RISC'],
      ['Simulated cycles', c.cycles + ' vs ' + r.cycles, 'CISC vs RISC, under these assumptions']
    ].map(x => `<div><span>${x[0]}</span><strong>${x[1]}</strong><small>${x[2]}</small></div>`).join('');
    $('#cmp-rows').innerHTML = rows.map(x => `<tr><th scope="row">${x[0]}</th><td>${x[1]}</td><td>${x[2]}</td></tr>`).join('');
    $('#cmp-why').innerHTML = this.explainDiff(c, r, rc, rr).map(p => `<p>${p}</p>`).join('');
    this.renderFeedback(c, r);
    $('#cmp-pending').hidden = true; $('#cmp-body').hidden = false;
  },

  explainDiff(c, r, rc, rr) {
    const out = [], t = this.task;
    out.push(rc === rr && rc === this.expected
      ? `Both processors stored the same correct answer, ${fmtNum(rc)}, in RES.`
      : `The results differ from the expected ${fmtNum(this.expected)}; this indicates a simulator error.`);
    if (t === 'list') {
      const n = this.values.list.length;
      out.push(`CISC executed ${c.instructions} instructions and RISC ${r.instructions}. With ${plural(n, 'item')}, the loop runs ${plural(n, 'time')}. Each CISC pass is 3 instructions (an ADD that reads the item straight from memory, INC, and DJNZ, which counts down and branches together). Each RISC pass is 5 (LOAD, ADD, two ADDIs, BNEZ). Lines in the program are not the same as instructions executed: loop lines run once per pass.`);
    } else {
      out.push(`CISC executed ${plural(c.instructions, 'instruction')} and RISC ${r.instructions}. CISC arithmetic can name memory locations directly, so one instruction reads its operands, computes, and writes the result. RISC must LOAD each value into a register first and STORE the answer afterwards, so the same work is spread across more, simpler instructions.`);
    }
    if (c.reads === r.reads && c.writes === r.writes) {
      out.push(`Memory traffic was identical: ${plural(c.reads, 'read')} and ${plural(c.writes, 'write')} each. The data has to travel between memory and the processor either way. The difference is whether a separate instruction moves it (RISC) or it happens inside a larger instruction (CISC).`);
    } else {
      out.push(`Memory traffic differed: CISC made ${plural(c.reads, 'read')} and ${plural(c.writes, 'write')}, RISC ${plural(r.reads, 'read')} and ${plural(r.writes, 'write')}.`);
    }
    const k = [['fetch & decode', 'fetch'], ['memory', 'memory'], ['arithmetic and constants', 'arith'], ['branching', 'branch']];
    const split = k.map(([lbl, key]) => `${lbl} ${c.byKind[key]} vs ${r.byKind[key]}`).join(', ');
    out.push(`Where the cycles went (CISC vs RISC): ${split}.`);
    const differing = k.filter(([, key]) => c.byKind[key] !== r.byKind[key]).map(([lbl]) => lbl);
    const onlyFetch = differing.length === 1 && differing[0] === 'fetch & decode';
    const d = Math.abs(c.cycles - r.cycles);
    let v;
    if (c.cycles === r.cycles) {
      v = `It was a tie: both used ${c.cycles} cycles. In this model, the cycles CISC saved by running fewer instructions were exactly cancelled by its slower decoding.`;
    } else if (c.cycles < r.cycles) {
      v = `CISC used ${d} fewer cycle${d === 1 ? '' : 's'}. ` + (onlyFetch
        ? `All of the gap is in fetch & decode: CISC's ${plural(c.instructions, 'instruction')}, at ${COST.fetch.CISC} decode cycles apiece, took ${c.byKind.fetch} cycles, less than RISC's ${r.instructions} instructions at ${COST.fetch.RISC} cycle apiece (${r.byKind.fetch} cycles).`
        : `The gap comes from ${differing.join(' and ')}.`);
    } else {
      v = `RISC used ${d} fewer cycles even though it executed more instructions. ` + (onlyFetch
        ? `All of the gap is in fetch & decode: CISC paid ${COST.fetch.CISC} cycles to decode each of its ${c.instructions} instructions (${c.byKind.fetch} total), more than RISC's ${r.instructions} instructions at ${COST.fetch.RISC} cycle each (${r.byKind.fetch} total). More instructions did not mean more time here.`
        : `The gap comes from ${differing.join(' and ')}.`);
    }
    out.push(v);
    out.push(`This outcome depends on the timing assumptions (see the panel at the bottom) and on this particular program. Real processors overlap instructions (pipelining), use caches, and run at different clock rates, so neither approach is always faster.${t === 'list' ? ' Try a longer or shorter list and compare.' : ' Try the “Sum a list” task to see a case where the outcome flips.'}`);
    return out;
  },

  renderFeedback(c, r) {
    const p1 = $('input[name="p1"]:checked'), p2 = $('input[name="p2"]:checked'), box = $('#cmp-feedback');
    if (!p1 && !p2) { box.hidden = true; return; }
    const more = c.instructions > r.instructions ? 'CISC' : r.instructions > c.instructions ? 'RISC' : 'same';
    const lines = [];
    if (p1) {
      const right = p1.value === more;
      const truth = more === 'same' ? 'they executed the same number' : `${more} executed more (${Math.max(c.instructions, r.instructions)} vs ${Math.min(c.instructions, r.instructions)})`;
      lines.push(`<strong>Instructions:</strong> you predicted ${p1.value === 'same' ? 'the same number' : p1.value}. ${right ? '<span class="ok">✓ Correct</span>' : '<span class="bad">✗ Not this time</span>'}: ${truth}.`);
    }
    if (p2) {
      let truth, actual;
      if (more === 'same') { actual = null; truth = 'Both ran the same number of instructions, so this question has no single answer here.'; }
      else {
        const mc = more === 'CISC' ? c.cycles : r.cycles, oc = more === 'CISC' ? r.cycles : c.cycles;
        actual = mc > oc ? 'yes' : 'no';
        truth = mc > oc ? `${more} also used more cycles (${mc} vs ${oc}).` : mc === oc ? `${more} used the same number of cycles (${mc}).` : `${more} used fewer cycles (${mc} vs ${oc}) despite running more instructions.`;
      }
      let verdict;
      if (p2.value === 'unsure') verdict = 'You weren’t sure, which is reasonable: it depends on the task and the cycle costs.';
      else verdict = (actual && p2.value === actual) ? '<span class="ok">✓ Correct</span> for this task.' : '<span class="bad">✗ Not for this task.</span>';
      lines.push(`<strong>Cycles:</strong> ${verdict} ${truth} Instruction count alone doesn't decide the time.`);
    }
    box.innerHTML = lines.map(l => `<p>${l}</p>`).join('');
    box.hidden = false;
  }
};

document.addEventListener('DOMContentLoaded', () => app.init());
