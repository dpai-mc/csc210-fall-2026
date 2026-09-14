/* ============================================================
   CSC210 — Shared Boolean Logic Kernel
   ============================================================
   Pure computation. No DOM, no navigation, no network.

   Per Course Standards Section 8, this file must never touch
   the DOM. That is what keeps the Section 5 no-cross-SPA-links
   boundary structural instead of a matter of discipline: a
   module that cannot reach the document cannot become a
   navigator. Widgets consume this and do their own rendering.

   Public API — window.CSCLogic:
     gates          per-gate truth functions + metadata
     tokenize(s)    string  -> token array          (exposed for testing)
     parse(s)       string  -> AST
     evaluate(ast, env)     -> 0 | 1
     variables(ast)         -> sorted array of variable names
     truthTable(s)  string  -> { vars, rows }
     equivalent(a, b)       -> boolean
     simplifyCheck(orig, student) -> { ok, reason, ... }

   Combinational primitives (added Week 3) — bit arrays are
   LSB-first, i.e. index 0 is the least significant bit:
     halfAdder(a, b)              -> { sum, carry }
     fullAdder(a, b, cin)         -> { sum, cout, stage1, stage2 }
     ripple(aBits, bBits, cin)    -> { sum, cout, stages }
     decode(selBits)              -> one-hot array of length 2^n
     decoderCost(n)               -> { outputs, andGates, andInputs, notGates }
     bitsToInt(bits) / intToBits(value, width)

   Notation accepted (Standards Section 8 requires all of these):
     NOT   A'   !A   ~A   NOT A      (postfix prime OR prefix)
     AND   AB   A*B  A.B  A&B  A AND B
     OR    A+B  A|B  A OR B
     XOR   A^B  A XOR B
     Grouping with ( ).  Constants 0 and 1.
     Variables: single letters A-Z (case-insensitive, folded upper).

   Precedence, tightest first:  ' (postfix)  >  NOT  >  AND  >  XOR  >  OR
   ============================================================ */

(function (root) {
  'use strict';

  /* ---------- Gate definitions ---------- */

  var gates = {
    AND:  { arity: 2, fn: function (a, b) { return a & b; },
            label: 'AND',  rule: 'Output is 1 only when ALL inputs are 1' },
    OR:   { arity: 2, fn: function (a, b) { return a | b; },
            label: 'OR',   rule: 'Output is 1 when AT LEAST ONE input is 1' },
    NOT:  { arity: 1, fn: function (a) { return a ? 0 : 1; },
            label: 'NOT',  rule: 'Output is the INVERSE of the input' },
    NAND: { arity: 2, fn: function (a, b) { return (a & b) ? 0 : 1; },
            label: 'NAND', rule: 'Output is 0 only when ALL inputs are 1' },
    NOR:  { arity: 2, fn: function (a, b) { return (a | b) ? 0 : 1; },
            label: 'NOR',  rule: 'Output is 1 only when ALL inputs are 0' },
    XOR:  { arity: 2, fn: function (a, b) { return a ^ b; },
            label: 'XOR',  rule: 'Output is 1 when an ODD number of inputs are 1' },
    XNOR: { arity: 2, fn: function (a, b) { return (a ^ b) ? 0 : 1; },
            label: 'XNOR', rule: 'Output is 1 when the inputs are the SAME' }
  };

  /* ---------- n-input gates ----------
     Real hardware gates (and Logisim's) take more than two inputs. Most
     generalise by folding the base operation across every input; XOR and
     XNOR are the exceptions and generalise by PARITY, not by "exactly one".

     Note the fold happens on the base op and the inversion is applied ONCE
     at the end: a 3-input NAND is NOT(A·B·C), which is NOT the same as
     NAND(NAND(A,B),C). Getting this wrong is a classic source of silent
     wrong answers, so it is written out explicitly rather than chained. */

  var MAX_INPUTS = { NOT: 1 };   // everything else accepts 2..n

  function gateEval(name, inputs) {
    if (!gates[name]) throw new Error('Unknown gate: ' + name);
    if (!inputs || !inputs.length) throw new Error('No inputs given');
    var bits = inputs.map(function (b) { return b ? 1 : 0; });

    if (name === 'NOT') {
      if (bits.length !== 1) throw new Error('NOT takes exactly one input');
      return bits[0] ? 0 : 1;
    }

    var allOnes = bits.every(function (b) { return b === 1; });
    var anyOne  = bits.some(function (b) { return b === 1; });
    var oddOnes = bits.reduce(function (acc, b) { return acc ^ b; }, 0) === 1;

    switch (name) {
      case 'AND':  return allOnes ? 1 : 0;
      case 'NAND': return allOnes ? 0 : 1;
      case 'OR':   return anyOne  ? 1 : 0;
      case 'NOR':  return anyOne  ? 0 : 1;
      case 'XOR':  return oddOnes ? 1 : 0;   // odd number of 1s
      case 'XNOR': return oddOnes ? 0 : 1;   // even number of 1s
    }
    throw new Error('Unhandled gate: ' + name);
  }

  function maxInputs(name) { return MAX_INPUTS[name] || Infinity; }

  /* Plain-English behaviour rule for a given input count. The two-input
     phrasings students first meet are a special case of these. */
  function gateRule(name, n) {
    if (name === 'NOT') return 'Output is the INVERSE of the input';
    if (n === 2) return gates[name].rule;
    switch (name) {
      case 'AND':  return 'Output is 1 only when ALL ' + n + ' inputs are 1';
      case 'NAND': return 'Output is 0 only when ALL ' + n + ' inputs are 1';
      case 'OR':   return 'Output is 1 when AT LEAST ONE of the ' + n + ' inputs is 1';
      case 'NOR':  return 'Output is 1 only when ALL ' + n + ' inputs are 0';
      case 'XOR':  return 'Output is 1 when an ODD number of inputs are 1';
      case 'XNOR': return 'Output is 1 when an EVEN number of inputs are 1';
    }
    return '';
  }

  /* Full truth table for a single gate. Returns array of rows;
     each row is [in...,out]. n defaults to the gate's natural arity. */
  function gateTable(name, n) {
    var g = gates[name];
    if (!g) throw new Error('Unknown gate: ' + name);
    n = n || g.arity;
    if (n > maxInputs(name)) throw new Error(name + ' cannot take ' + n + ' inputs');
    var rows = [], i, j, ins;
    for (i = 0; i < (1 << n); i++) {
      ins = [];
      for (j = n - 1; j >= 0; j--) ins.push((i >> j) & 1);
      rows.push(ins.concat([gateEval(name, ins)]));
    }
    return rows;
  }

  /* ---------- Tokenizer ---------- */

  var WORD_OPS = { NOT: 'NOT', AND: 'AND', OR: 'OR', XOR: 'XOR',
                   NAND: 'NAND', NOR: 'NOR', XNOR: 'XNOR' };

  function tokenize(src) {
    var s = String(src).toUpperCase();
    var out = [], i = 0, ch, m;

    while (i < s.length) {
      ch = s[i];

      if (ch === ' ' || ch === '\t' || ch === '\n') { i++; continue; }

      // Multi-letter word operators must be checked before bare variables,
      // otherwise "NOT" tokenizes as N.O.T (three variables ANDed).
      m = /^(XNOR|NAND|XOR|NOR|NOT|AND|OR)\b/.exec(s.slice(i));
      if (m) { out.push({ t: WORD_OPS[m[1]] }); i += m[1].length; continue; }

      if (ch >= 'A' && ch <= 'Z') { out.push({ t: 'VAR', v: ch }); i++; continue; }
      if (ch === '0' || ch === '1') { out.push({ t: 'CONST', v: +ch }); i++; continue; }

      if (ch === "'" || ch === '’') { out.push({ t: 'PRIME' }); i++; continue; }
      if (ch === '!' || ch === '~' || ch === '¬') { out.push({ t: 'NOT' }); i++; continue; }
      if (ch === '*' || ch === '.' || ch === '&' || ch === '·') { out.push({ t: 'AND' }); i++; continue; }
      if (ch === '+' || ch === '|' || ch === '∨') { out.push({ t: 'OR' }); i++; continue; }
      if (ch === '^' || ch === '⊕') { out.push({ t: 'XOR' }); i++; continue; }
      if (ch === '(') { out.push({ t: '(' }); i++; continue; }
      if (ch === ')') { out.push({ t: ')' }); i++; continue; }

      throw new Error('Unexpected character "' + s[i] + '" at position ' + i);
    }
    return out;
  }

  /* ---------- Parser (recursive descent) ----------
     expr   := xorExpr ( OR xorExpr )*
     xorExpr:= andExpr ( XOR andExpr )*
     andExpr:= unary ( AND? unary )*        <- juxtaposition is implicit AND
     unary  := NOT unary | postfix
     postfix:= primary PRIME*
     primary:= VAR | CONST | '(' expr ')'
  */

  function parse(src) {
    var toks = tokenize(src), pos = 0;

    function peek() { return toks[pos]; }
    function eat(t) { if (toks[pos] && toks[pos].t === t) { return toks[pos++]; } return null; }

    function expr() {
      var node = xorExpr();
      while (eat('OR')) node = { op: 'OR', a: node, b: xorExpr() };
      return node;
    }

    function xorExpr() {
      var node = andExpr();
      while (eat('XOR')) node = { op: 'XOR', a: node, b: andExpr() };
      return node;
    }

    function andExpr() {
      var node = unary(), t;
      for (;;) {
        if (eat('AND')) { node = { op: 'AND', a: node, b: unary() }; continue; }
        if (eat('NAND')) { node = { op: 'NOT', a: { op: 'AND', a: node, b: unary() } }; continue; }
        if (eat('NOR'))  { node = { op: 'NOT', a: { op: 'OR',  a: node, b: unary() } }; continue; }
        if (eat('XNOR')) { node = { op: 'NOT', a: { op: 'XOR', a: node, b: unary() } }; continue; }
        // Implicit AND: another operand starts right here with no operator.
        t = peek();
        if (t && (t.t === 'VAR' || t.t === 'CONST' || t.t === '(' || t.t === 'NOT')) {
          node = { op: 'AND', a: node, b: unary() };
          continue;
        }
        return node;
      }
    }

    function unary() {
      if (eat('NOT')) return { op: 'NOT', a: unary() };
      return postfix();
    }

    function postfix() {
      var node = primary();
      while (eat('PRIME')) node = { op: 'NOT', a: node };
      return node;
    }

    function primary() {
      var t = peek(), node;
      if (!t) throw new Error('Unexpected end of expression');
      if (t.t === 'VAR')   { pos++; return { op: 'VAR', name: t.v }; }
      if (t.t === 'CONST') { pos++; return { op: 'CONST', value: t.v }; }
      if (t.t === '(') {
        pos++;
        node = expr();
        if (!eat(')')) throw new Error('Missing closing parenthesis');
        return node;
      }
      throw new Error('Unexpected token "' + t.t + '"');
    }

    var ast = expr();
    if (pos < toks.length) {
      throw new Error('Unexpected token "' + toks[pos].t + '" after end of expression');
    }
    return ast;
  }

  /* ---------- Evaluation ---------- */

  function evaluate(ast, env) {
    switch (ast.op) {
      case 'CONST': return ast.value ? 1 : 0;
      case 'VAR':
        if (!(ast.name in env)) throw new Error('Variable ' + ast.name + ' has no value');
        return env[ast.name] ? 1 : 0;
      case 'NOT': return evaluate(ast.a, env) ? 0 : 1;
      case 'AND': return (evaluate(ast.a, env) & evaluate(ast.b, env)) ? 1 : 0;
      case 'OR':  return (evaluate(ast.a, env) | evaluate(ast.b, env)) ? 1 : 0;
      case 'XOR': return (evaluate(ast.a, env) ^ evaluate(ast.b, env)) ? 1 : 0;
      default: throw new Error('Unknown node type: ' + ast.op);
    }
  }

  function variables(ast, acc) {
    acc = acc || {};
    if (ast.op === 'VAR') acc[ast.name] = true;
    else { if (ast.a) variables(ast.a, acc); if (ast.b) variables(ast.b, acc); }
    return Object.keys(acc).sort();
  }

  /* ---------- Truth tables ---------- */

  /* truthTable('AB + C') ->
       { vars: ['A','B','C'],
         rows: [ { inputs:[0,0,0], out:0 }, ... ] }
     Optional varsOverride forces a variable set/order, which matters when
     comparing two expressions that don't mention the same variables. */
  function truthTable(src, varsOverride) {
    var ast = (typeof src === 'string') ? parse(src) : src;
    var vars = varsOverride || variables(ast);
    var rows = [], i, j, env, inputs;

    for (i = 0; i < (1 << vars.length); i++) {
      env = {}; inputs = [];
      for (j = 0; j < vars.length; j++) {
        var bit = (i >> (vars.length - 1 - j)) & 1;
        env[vars[j]] = bit;
        inputs.push(bit);
      }
      rows.push({ inputs: inputs, out: evaluate(ast, env) });
    }
    return { vars: vars, rows: rows };
  }

  /* ---------- Equivalence ----------
     Two expressions are equivalent iff their truth tables agree over the
     UNION of their variables. Comparing over each expression's own variable
     set is the classic bug here: A and A+BB' would look different. */
  function equivalent(exprA, exprB) {
    var astA = (typeof exprA === 'string') ? parse(exprA) : exprA;
    var astB = (typeof exprB === 'string') ? parse(exprB) : exprB;

    var merged = {}, k;
    variables(astA).forEach(function (v) { merged[v] = true; });
    variables(astB).forEach(function (v) { merged[v] = true; });
    var vars = Object.keys(merged).sort();

    var ta = truthTable(astA, vars), tb = truthTable(astB, vars);
    for (k = 0; k < ta.rows.length; k++) {
      if (ta.rows[k].out !== tb.rows[k].out) return false;
    }
    return true;
  }

  /* Count literal occurrences — a rough proxy for "is this actually
     simpler?" so the widget can tell a student that A+A is equivalent
     but not a simplification. */
  function literalCount(ast) {
    if (ast.op === 'VAR' || ast.op === 'CONST') return 1;
    return (ast.a ? literalCount(ast.a) : 0) + (ast.b ? literalCount(ast.b) : 0);
  }

  /* simplifyCheck('AB + AB\'', 'A') ->
       { ok:true, equivalent:true, simpler:true, origLiterals:4, studentLiterals:1 }
     On a parse failure returns { ok:false, reason:'parse-error', message:... }
     so widgets can show the message without try/catch at the call site. */
  function simplifyCheck(original, student) {
    var astO, astS;
    try { astO = parse(original); }
    catch (e) { return { ok: false, reason: 'parse-error-original', message: e.message }; }
    try { astS = parse(student); }
    catch (e) { return { ok: false, reason: 'parse-error-student', message: e.message }; }

    var eq = equivalent(astO, astS);
    var lo = literalCount(astO), ls = literalCount(astS);

    return {
      ok: eq,
      equivalent: eq,
      simpler: eq && ls < lo,
      origLiterals: lo,
      studentLiterals: ls,
      reason: eq ? (ls < lo ? 'simplified' : 'equivalent-not-simpler') : 'not-equivalent'
    };
  }

  /* ============================================================
     Combinational-circuit primitives — added for Week 3
     ============================================================
     Still pure computation: no DOM, no events, no network. These
     exist because Week 3's ripple-carry widget, Week 6's ALU and
     Week 8's RAM addressing all need the same two operations, and
     Section 8 of the Course Standards exists to stop that logic
     being written three times.

     Bit-array convention, and it is worth stating once because
     getting it backwards is the classic ripple-carry bug:

         index 0 is the LEAST significant bit.

     So the 8-bit value 00000011 (decimal 3) is [1,1,0,0,0,0,0,0].
     Carries propagate from index 0 upward, which is the order a
     stepped display should reveal them in.
     ============================================================ */

  /* halfAdder(a, b) -> { sum, carry }
     sum = a XOR b, carry = a AND b. */
  function halfAdder(a, b) {
    a = a ? 1 : 0; b = b ? 1 : 0;
    return { sum: a ^ b, carry: a & b };
  }

  /* fullAdder(a, b, cin) -> { sum, cout, stage1, stage2 }
     Two half adders and an OR. stage1/stage2 are exposed so a
     widget can highlight the construction one half-adder at a
     time without recomputing anything. */
  function fullAdder(a, b, cin) {
    a = a ? 1 : 0; b = b ? 1 : 0; cin = cin ? 1 : 0;
    var h1 = halfAdder(a, b);
    var h2 = halfAdder(h1.sum, cin);
    return {
      sum: h2.sum,
      cout: h1.carry | h2.carry,
      stage1: h1,
      stage2: h2
    };
  }

  /* ripple(aBits, bBits, cin) -> { sum, cout, stages }

     aBits/bBits are arrays of 0|1, index 0 = LSB. Widths may differ;
     the shorter is zero-extended. Returns the sum as a bit array of
     the same convention, the final carry-out, and per-stage detail:

       stages[i] = { i, a, b, cin, sum, cout }

     The per-stage array is the reason this lives here rather than in
     a widget: stepped propagation needs each stage's carry-in as well
     as its result, and reconstructing that from the final answer is
     both awkward and easy to get subtly wrong. */
  function ripple(aBits, bBits, cin) {
    var n = Math.max(aBits.length, bBits.length);
    var c = cin ? 1 : 0;
    var sum = [], stages = [], i, a, b, fa;

    for (i = 0; i < n; i++) {
      a = aBits[i] ? 1 : 0;
      b = bBits[i] ? 1 : 0;
      fa = fullAdder(a, b, c);
      stages.push({ i: i, a: a, b: b, cin: c, sum: fa.sum, cout: fa.cout });
      sum.push(fa.sum);
      c = fa.cout;
    }
    return { sum: sum, cout: c, stages: stages };
  }

  /* decode(selBits) -> array of length 2^n, exactly one entry = 1.

     selBits index 0 = LSB, matching ripple(). So [1,0] is sel=01,
     which raises out1 — the pin ordering the Week 3 spec fixes as
     part of the component interface (sel 00 -> out0 ... 11 -> out3).

     Deliberately computed as an AND of input polarities rather than
     as an array index, because that is the construction the SPA prose
     describes: each output is one AND gate fed by the combination of
     true and inverted inputs that selects it. A lookup would give the
     right answer while demonstrating nothing. */
  function decode(selBits) {
    var n = selBits.length;
    var outs = [], i, j, match, bit, want;

    for (i = 0; i < (1 << n); i++) {
      match = 1;
      for (j = 0; j < n; j++) {
        bit  = selBits[j] ? 1 : 0;          // actual input bit j
        want = (i >> j) & 1;                // what output i requires
        if (bit !== want) { match = 0; break; }
      }
      outs.push(match);
    }
    return outs;
  }

  /* Gate count for an n-input decoder, for the widget's live readout.
     n AND gates of n inputs each, plus n inverters. */
  function decoderCost(n) {
    return { outputs: 1 << n, andGates: 1 << n, andInputs: n, notGates: n };
  }

  /* bitsToInt / intToBits — LSB-first, to keep the convention in one
     place rather than re-derived in each widget. */
  function bitsToInt(bits) {
    var v = 0, i;
    for (i = 0; i < bits.length; i++) { if (bits[i]) v += (1 << i); }
    return v;
  }

  function intToBits(value, width) {
    var bits = [], i;
    for (i = 0; i < width; i++) { bits.push((value >> i) & 1); }
    return bits;
  }


  /* ============================================================
     WEEK 4 — Sequential primitives
     ============================================================
     Added 2026-09-06. Week 4's two widgets need latch and flip-flop
     behaviour, and Standards Section 8 requires that live here rather than
     inside a widget.

     There is a specific reason beyond the standing rule. The Fall 2025
     Week 4 page rolled its own settle loop inside the widget:

         qn = (s_not && q)  ? 0 : 1;   // top gate, ALWAYS evaluated first
         q  = (r_not && qn) ? 0 : 1;   // bottom gate, always second

     That evaluation order is not a property of the circuit -- it is an
     artefact of writing one line above the other. Because of it, releasing
     the forbidden state ALWAYS resolved to q = 1, and students were taught
     that leaving the forbidden state gives Set. It does not; it gives
     whichever physical gate is faster, which is not knowable.

     srSettle() below updates both gates SIMULTANEOUSLY from the previous
     values, which is order-independent and therefore honest. On the
     forbidden release it does not converge, and it reports that rather
     than returning a number. logic.test.js asserts the non-convergence,
     so a future "fix" that makes it settle cleanly fails the suite instead
     of shipping.
     ============================================================ */

  var SETTLE_LIMIT = 12;

  function nand2(a, b) { return (a && b) ? 0 : 1; }

  /* One simultaneous update of the two cross-coupled NAND gates.
     q  = NAND(nS, nq)   nq = NAND(nR, q)
     Both computed from the PREVIOUS state, then assigned together. */
  function srStep(nS, nR, q, nq) {
    return { q: nand2(nS, nq), nq: nand2(nR, q) };
  }

  /* Iterate to a fixed point. Returns every intermediate state so a widget
     can render gate-delay stepping without re-deriving the semantics.
       steps    - [{q, nq}, ...] one entry per gate delay, first entry is
                  the state AFTER the first update
       settled  - true if a fixed point was reached within SETTLE_LIMIT
       q / nq   - the settled values; MEANINGLESS when settled is false,
                  and callers must not display them in that case
       state    - 'hold' | 'set' | 'reset' | 'forbidden' | 'race' */
  function srSettle(nS, nR, q, nq) {
    var steps = [], i, next, settled = false;
    for (i = 0; i < SETTLE_LIMIT; i++) {
      next = srStep(nS, nR, q, nq);
      steps.push({ q: next.q, nq: next.nq });
      if (next.q === q && next.nq === nq) { settled = true; break; }
      q = next.q; nq = next.nq;
    }
    var state;
    if (!settled)                     { state = 'race'; }
    else if (nS === 0 && nR === 0)    { state = 'forbidden'; }
    else if (nS === 0)                { state = 'set'; }
    else if (nR === 0)                { state = 'reset'; }
    else                              { state = 'hold'; }
    return { steps: steps, settled: settled, q: q, nq: nq, state: state };
  }

  /* Convenience wrapper: settle and report. Same contract as srSettle --
     when settled is false, q and nq carry no meaning. */
  function srLatch(nS, nR, q, nq) {
    if (nq === undefined) { nq = q ? 0 : 1; }
    return srSettle(nS, nR, q, nq);
  }

  /* MEM_1BIT -- the course's 1-bit memory cell, four NAND gates.
       A = NAND(In, Set)      B = NAND(A, Set)
       A and B drive the cross-coupled pair as nS and nR.
     Set = 1 -> A = In', B = In, so exactly one side goes low.
     Set = 0 -> A = B = 1, the latch holds.
     The forbidden state needs A = B = 0, which needs In' = In. Impossible,
     which is the whole point of the front two gates. */
  function memCell(In, Set, q) {
    var A = nand2(In, Set);
    var B = nand2(A, Set);
    var r = srSettle(A, B, q, q ? 0 : 1);
    return { q: r.q, nq: r.nq, nS: A, nR: B, transparent: Set === 1 };
  }

  /* Named for the textbook circuit this is, so outside references match.
     Identical behaviour; MEM_1BIT is the course's name for it. */
  function dLatch(d, en, q) { return memCell(d, en, q); }

  /* Edge-triggered D flip-flop. Captures only on a 0 -> 1 clock transition
     and holds through every other transition and through steady states.
     Taught in Week 4, not built -- the datapath uses memCell instead, and
     the machine's only edge-triggered element is the J-K in the clock. */
  function dFlipFlop(d, clkPrev, clkNow, q) {
    var rising = (clkPrev === 0 && clkNow === 1);
    var out = rising ? (d ? 1 : 0) : (q ? 1 : 0);
    return { q: out, nq: out ? 0 : 1, captured: rising };
  }

  /* Walk a device across a time series and return its output at each step.
     Used by Week 4's timing widget to draw three devices on one axis.
       device  - 'srlatch' | 'memcell' | 'dlatch' | 'dflipflop'
       dSeq    - data input per step
       ctlSeq  - enable (memcell/dlatch) or clock (dflipflop) per step;
                 ignored by 'srlatch', which has no control input at all
       q0      - starting output
     The S-R latch is driven nS = !d, nR = d, so it is always either setting
     or resetting and never holding. That is not a quirk of the harness --
     it is the point. A raw latch has no way to be told "not yet", so its
     output tracks the input continuously. */
  function trace(device, dSeq, ctlSeq, q0) {
    var q = q0 ? 1 : 0, out = [], i, d, c;
    for (i = 0; i < dSeq.length; i++) {
      d = dSeq[i] ? 1 : 0;
      c = (ctlSeq && ctlSeq[i]) ? 1 : 0;
      if (device === 'srlatch') {
        q = srSettle(d ? 0 : 1, d ? 1 : 0, q, q ? 0 : 1).q;
      } else if (device === 'memcell' || device === 'dlatch') {
        q = memCell(d, c, q).q;
      } else if (device === 'dflipflop') {
        q = dFlipFlop(d, (i === 0 ? c : ((ctlSeq[i - 1]) ? 1 : 0)), c, q).q;
      } else {
        throw new Error('trace: unknown device ' + device);
      }
      out.push(q);
    }
    return out;
  }

  /* ============================================================
     WEEK 5A — Word-width storage and bus primitives
     ============================================================
     Added 2026-09-14. Week 5's first three widgets need the byte-wide
     versions of the Week 4 cell, plus something Week 4 had no need for:
     a model of what happens when more than one device is connected to
     the same wire.

     BIT ORDER. Everything in this section uses MSB-FIRST arrays, so
     [1,0,1,0,1,0,1,0] reads as the byte 10101010 in the order a student
     sees it on a Logisim probe and in the SPA. This is the OPPOSITE of
     bitsToInt/intToBits above, which are LSB-first because Week 3's
     adder chains from the LSB. Do not mix them; use wordToInt/intToWord
     below for anything in this section.

     THE CONTRACT THAT MATTERS. busResolve() reports a contested bus as
     'conflict' and never as a byte -- including when the two drivers
     happen to agree, because two output stages fighting is a hardware
     fault whether or not they want the same answer. logic.test.js
     asserts that, so a later "fix" that resolves it cleanly fails the
     suite instead of shipping. This is the same contract as srSettle's
     non-convergence, and it exists for the same reason: the Fall 2025
     Week 4 widget quietly picked a winner in an undefined situation and
     taught a year of students something false.
     ============================================================ */

  function wordToInt(bits) {
    var n = 0, i;
    for (i = 0; i < bits.length; i++) { n = (n << 1) | (bits[i] ? 1 : 0); }
    return n >>> 0;
  }

  function intToWord(value, width) {
    var bits = [], i;
    for (i = width - 1; i >= 0; i--) { bits.push((value >> i) & 1); }
    return bits;
  }

  /* MEM_8BIT -- n instances of memCell sharing ONE set line.
     The shared line is the whole content of the circuit: it is what makes
     this a byte captured at one moment rather than n bits that happen to
     be near each other. */
  function memWord(inBits, set, qBits) {
    var q = [], i;
    for (i = 0; i < inBits.length; i++) {
      q.push(memCell(inBits[i] ? 1 : 0, set ? 1 : 0, (qBits && qBits[i]) ? 1 : 0).q);
    }
    return { q: q, transparent: set === 1 || set === true };
  }

  /* ENABLE_8BIT -- the output stage, in each of the three arrangements
     Week 5 discusses.

       'and'    eight AND gates. ALWAYS driving: at e = 0 it asserts
                00000000, which is a value, which is why it cannot share
                a wire.
       'buffer' controlled buffers only. At e = 0 it stops driving.
       'both'   AND then buffers -- what students actually build.

     'buffer' and 'both' are behaviourally IDENTICAL and the test suite
     asserts it. That is the paper analysis in Week 5 section 5.3b, and it
     is deliberately all this kernel models. The reason students build the
     redundant stages anyway is that Logisim Classic 2.7.1 is unstable
     without them (Dave, 2026-09-14) -- a property of the simulator, not of
     the circuit. A kernel that reproduced a simulator's quirk would be
     teaching the quirk as if it were the electronics. */
  function enableWord(inBits, e, mode) {
    var on = (e === 1 || e === true);
    var i, bits;
    mode = mode || 'both';
    if (mode === 'and') {
      bits = [];
      for (i = 0; i < inBits.length; i++) { bits.push(on ? (inBits[i] ? 1 : 0) : 0); }
      return { bits: bits, driving: true, mode: mode };
    }
    if (mode !== 'buffer' && mode !== 'both') {
      throw new Error('enableWord: unknown mode ' + mode);
    }
    if (!on) { return { bits: null, driving: false, mode: mode }; }
    bits = [];
    for (i = 0; i < inBits.length; i++) { bits.push(inBits[i] ? 1 : 0); }
    return { bits: bits, driving: true, mode: mode };
  }

  /* What a shared wire carries, given everything connected to it.
       drivers - [{ bits: [...] | null, driving: bool }, ...]
     Returns one of:
       { state: 'float' }                  nothing is driving
       { state: 'driven', bits: [...] }    exactly one device is driving
       { state: 'conflict', count: n }     more than one is driving

     Two drivers asserting the SAME byte is still a conflict. On real
     hardware that is two output stages connected together, one pulling
     high and one pulling low on any bit where they later disagree, and
     the fact that they agree right now is not a property anything can
     rely on. Reporting it as success would teach students that bus
     discipline is about agreement rather than about exclusivity. */
  function busResolve(drivers) {
    var active = [], i;
    for (i = 0; i < drivers.length; i++) {
      if (drivers[i] && drivers[i].driving) { active.push(drivers[i]); }
    }
    if (active.length === 0) { return { state: 'float' }; }
    if (active.length > 1)   { return { state: 'conflict', count: active.length }; }
    return { state: 'driven', bits: active[0].bits.slice() };
  }

  /* REGISTER_8BIT -- the full five-pin component.

       qBits  current stored byte (MSB-first)
       ctrl   { i: [...], s: 0|1, e: 0|1, mode: 'and'|'buffer'|'both' }

     Returns { q, reg, o, driving }:
       q        the new stored byte
       reg      the monitor output -- ALWAYS the stored byte, regardless
                of e. This is the pin the CPU Design Reference was missing
                and Week 13 cannot debug without.
       o        the bus port -- the byte when driving, null when not
       driving  whether o is asserting anything at all

     reg and o are the week's whole subject expressed as two pins: holding
     a value and putting it where others can see it are different acts. */
  function register8(qBits, ctrl) {
    var m = memWord(ctrl.i, ctrl.s, qBits);
    var out = enableWord(m.q, ctrl.e, ctrl.mode || 'both');
    return {
      q: m.q,
      reg: m.q.slice(),
      o: out.bits,
      driving: out.driving,
      /* 'bits' is 'o' under the name busResolve() expects, so a register
         can be handed straight to a bus without the caller repackaging
         it. That is the right shape: a register IS a bus driver, and the
         two pins that decide whether it is driving are its own. */
      bits: out.bits
    };
  }

  /* ============================================================
     WEEK 5B — MIPS instruction data and codecs (CSCLogic.mips)
     ============================================================
     Added 2026-09-14, approved as Open Decision #2.

     WHY THIS IS IN THE SHARED KERNEL. Standards Section 8's test is
     whether two or more files need it, and three do this week alone:
     the instruction-formats SPA's widget, that SPA's self-check, and
     assignment5.html, which renders the same five reference tables so a
     student can do Part C without leaving the page. Weeks 6, 7 and 8 add
     instructions to these same tables and the Midterm bank is generated
     against them.

     ONE opcode table, ONE place to correct it. The Fall 2025 alternative
     -- a reference sheet and a formatter each carrying their own copy --
     is exactly what this section of the standards exists to prevent.

     BIT ORDER here is MSB-first strings throughout, because that is how
     an instruction is written down, read out of a listing, and typed into
     a decoder.
     ============================================================ */

  /* ---- bit-string helpers ---- */

  function toBin(value, width) {
    var v = value < 0 ? (value + Math.pow(2, width)) : value;
    var s = (v >>> 0).toString(2);
    while (s.length < width) { s = '0' + s; }
    return s.slice(-width);
  }

  function fromBin(str)       { return parseInt(str, 2); }

  function fromBinSigned(str) {
    var v = parseInt(str, 2);
    return (str.charAt(0) === '1') ? v - Math.pow(2, str.length) : v;
  }

  /* ---- the register file ---- */

  var MIPS_REGS = [
    { n: 0,  name: '$zero', group: 'constant',  usage: 'Constant 0. Writes are discarded.' },
    { n: 1,  name: '$at',   group: 'assembler', usage: 'Reserved for the assembler.' },
    { n: 2,  name: '$v0',   group: 'return',    usage: 'Return value; syscall service number.' },
    { n: 3,  name: '$v1',   group: 'return',    usage: 'Return value (second word).' },
    { n: 4,  name: '$a0',   group: 'argument',  usage: 'Argument 1; syscall argument.' },
    { n: 5,  name: '$a1',   group: 'argument',  usage: 'Argument 2.' },
    { n: 6,  name: '$a2',   group: 'argument',  usage: 'Argument 3.' },
    { n: 7,  name: '$a3',   group: 'argument',  usage: 'Argument 4.' },
    { n: 8,  name: '$t0',   group: 'temporary', usage: 'Temporary. Not preserved across a call.' },
    { n: 9,  name: '$t1',   group: 'temporary', usage: 'Temporary.' },
    { n: 10, name: '$t2',   group: 'temporary', usage: 'Temporary.' },
    { n: 11, name: '$t3',   group: 'temporary', usage: 'Temporary.' },
    { n: 12, name: '$t4',   group: 'temporary', usage: 'Temporary.' },
    { n: 13, name: '$t5',   group: 'temporary', usage: 'Temporary.' },
    { n: 14, name: '$t6',   group: 'temporary', usage: 'Temporary.' },
    { n: 15, name: '$t7',   group: 'temporary', usage: 'Temporary.' },
    { n: 16, name: '$s0',   group: 'saved',     usage: 'Saved. Preserved across a call.' },
    { n: 17, name: '$s1',   group: 'saved',     usage: 'Saved.' },
    { n: 18, name: '$s2',   group: 'saved',     usage: 'Saved.' },
    { n: 19, name: '$s3',   group: 'saved',     usage: 'Saved.' },
    { n: 20, name: '$s4',   group: 'saved',     usage: 'Saved.' },
    { n: 21, name: '$s5',   group: 'saved',     usage: 'Saved.' },
    { n: 22, name: '$s6',   group: 'saved',     usage: 'Saved.' },
    { n: 23, name: '$s7',   group: 'saved',     usage: 'Saved.' },
    { n: 24, name: '$t8',   group: 'temporary', usage: 'Temporary.' },
    { n: 25, name: '$t9',   group: 'temporary', usage: 'Temporary.' },
    { n: 26, name: '$k0',   group: 'kernel',    usage: 'Reserved for the OS kernel.' },
    { n: 27, name: '$k1',   group: 'kernel',    usage: 'Reserved for the OS kernel.' },
    { n: 28, name: '$gp',   group: 'pointer',   usage: 'Global pointer.' },
    { n: 29, name: '$sp',   group: 'pointer',   usage: 'Stack pointer.' },
    { n: 30, name: '$fp',   group: 'pointer',   usage: 'Frame pointer.' },
    { n: 31, name: '$ra',   group: 'pointer',   usage: 'Return address.' }
  ];

  /* ---- the instruction tables ----
     form  tells encode/decode how the operands map onto the fields:
       r3    rd, rs, rt            add sub and or xor slt
       rsh   rd, rt, shamt         sll srl
       rjr   rs                    jr
       i3    rt, rs, imm           addi andi ori
       imem  rt, imm(rs)           lw sw
       ibr   rs, rt, imm           beq bne
       jt    target                j jal
     week  is the week the instruction enters the course's working subset.
           Week 5 teaches 5; anything later appears in the reference table
           marked with its week, so its absence is a signpost rather than
           an omission.
     sext  true if the 16-bit immediate is sign-extended, false if it is
           zero-extended. Standards Section 2: addi and andi sit in the
           same format with the same field and are treated differently,
           which is exactly the kind of pair that must be labelled. */

  var MIPS_R = [
    { m: 'add', funct: '100000', form: 'r3',  week: 5, syntax: 'add $rd, $rs, $rt',   desc: 'rd = rs + rt' },
    { m: 'sub', funct: '100010', form: 'r3',  week: 5, syntax: 'sub $rd, $rs, $rt',   desc: 'rd = rs - rt' },
    { m: 'and', funct: '100100', form: 'r3',  week: 5, syntax: 'and $rd, $rs, $rt',   desc: 'rd = rs AND rt, bitwise' },
    { m: 'or',  funct: '100101', form: 'r3',  week: 5, syntax: 'or $rd, $rs, $rt',    desc: 'rd = rs OR rt, bitwise' },
    { m: 'xor', funct: '100110', form: 'r3',  week: 5, syntax: 'xor $rd, $rs, $rt',   desc: 'rd = rs XOR rt, bitwise' },
    { m: 'slt', funct: '101010', form: 'r3',  week: 5, syntax: 'slt $rd, $rs, $rt',   desc: 'rd = 1 if rs < rt, else 0' },
    { m: 'sll', funct: '000000', form: 'rsh', week: 6, syntax: 'sll $rd, $rt, shamt', desc: 'rd = rt shifted left by shamt' },
    { m: 'srl', funct: '000010', form: 'rsh', week: 6, syntax: 'srl $rd, $rt, shamt', desc: 'rd = rt shifted right by shamt' },
    { m: 'jr',  funct: '001000', form: 'rjr', week: 7, syntax: 'jr $rs',              desc: 'jump to the address held in rs' }
  ];

  var MIPS_I = [
    { m: 'addi', opcode: '001000', form: 'i3',   week: 5, sext: true,  syntax: 'addi $rt, $rs, imm',  desc: 'rt = rs + imm, immediate SIGN-extended' },
    { m: 'andi', opcode: '001100', form: 'i3',   week: 5, sext: false, syntax: 'andi $rt, $rs, imm',  desc: 'rt = rs AND imm, immediate ZERO-extended' },
    { m: 'ori',  opcode: '001101', form: 'i3',   week: 5, sext: false, syntax: 'ori $rt, $rs, imm',   desc: 'rt = rs OR imm, immediate ZERO-extended' },
    { m: 'lw',   opcode: '100011', form: 'imem', week: 5, sext: true,  syntax: 'lw $rt, imm($rs)',    desc: 'load the word at rs + imm into rt' },
    { m: 'sw',   opcode: '101011', form: 'imem', week: 5, sext: true,  syntax: 'sw $rt, imm($rs)',    desc: 'store rt into memory at rs + imm' },
    { m: 'beq',  opcode: '000100', form: 'ibr',  week: 5, sext: true,  syntax: 'beq $rs, $rt, offset', desc: 'branch if rs equals rt (semantics: Week 7)' },
    { m: 'bne',  opcode: '000101', form: 'ibr',  week: 5, sext: true,  syntax: 'bne $rs, $rt, offset', desc: 'branch if rs does not equal rt (semantics: Week 7)' }
  ];

  var MIPS_J = [
    { m: 'j',   opcode: '000010', form: 'jt', week: 5, syntax: 'j target',   desc: 'jump to target' },
    { m: 'jal', opcode: '000011', form: 'jt', week: 5, syntax: 'jal target', desc: 'jump to target, return address into $ra' }
  ];

  var MIPS_SYSCALLS = [
    { service: 'print integer',  code: 1,  args: '$a0 = the integer to print' },
    { service: 'print string',   code: 4,  args: '$a0 = address of a null-terminated string' },
    { service: 'read integer',   code: 5,  args: 'returns the integer in $v0' },
    { service: 'read string',    code: 8,  args: '$a0 = buffer address, $a1 = length' },
    { service: 'allocate memory', code: 9, args: '$a0 = bytes wanted; address returned in $v0' },
    { service: 'exit',           code: 10, args: 'ends the program' }
  ];

  /* ---- lookup ---- */

  function regByName(token) {
    var t = String(token).trim(), i;
    if (t.charAt(0) !== '$') { return null; }
    for (i = 0; i < MIPS_REGS.length; i++) {
      if (MIPS_REGS[i].name === t) { return MIPS_REGS[i]; }
    }
    /* $8 and $t0 are the same register and both are legal to write. */
    if (/^\$\d+$/.test(t)) {
      var n = parseInt(t.slice(1), 10);
      if (n >= 0 && n < 32) { return MIPS_REGS[n]; }
    }
    return null;
  }

  function regByNumber(n) { return MIPS_REGS[n] || null; }

  function findOp(m) {
    var i;
    for (i = 0; i < MIPS_R.length; i++) { if (MIPS_R[i].m === m) { return { type: 'R', op: MIPS_R[i] }; } }
    for (i = 0; i < MIPS_I.length; i++) { if (MIPS_I[i].m === m) { return { type: 'I', op: MIPS_I[i] }; } }
    for (i = 0; i < MIPS_J.length; i++) { if (MIPS_J[i].m === m) { return { type: 'J', op: MIPS_J[i] }; } }
    return null;
  }

  function fail(msg) { return { ok: false, error: msg }; }

  function fld(name, width, bits, label) {
    return { name: name, width: width, bits: bits, label: label };
  }

  /* ---- encode ----
     Assembly text in, 32 bits out, with every field exposed separately so
     a widget can highlight the boundaries rather than showing an
     undifferentiated run of digits. That mapping is the thing students
     actually get wrong. */
  function mipsEncode(text) {
    var src = String(text).replace(/#.*$/, '').trim();
    if (!src) { return fail('Nothing to encode.'); }

    var sp = src.indexOf(' ');
    var mnemonic = (sp === -1 ? src : src.slice(0, sp)).toLowerCase();
    var rest = (sp === -1 ? '' : src.slice(sp + 1)).trim();

    var found = findOp(mnemonic);
    if (!found) { return fail('Unknown instruction "' + mnemonic + '".'); }
    var op = found.op, fields = [], parts, rd, rs, rt, imm, m;

    function needReg(tok, which) {
      var r = regByName(tok);
      if (!r) { throw new Error('"' + String(tok).trim() + '" is not a register name (' + which + ').'); }
      return r;
    }
    function needInt(tok, lo, hi, which) {
      var v = parseInt(String(tok).trim(), 10);
      if (isNaN(v)) { throw new Error('"' + String(tok).trim() + '" is not a number (' + which + ').'); }
      if (v < lo || v > hi) { throw new Error(which + ' ' + v + ' does not fit; the range is ' + lo + ' to ' + hi + '.'); }
      return v;
    }

    try {
      if (found.type === 'R') {
        if (op.form === 'r3') {
          parts = rest.split(',');
          if (parts.length !== 3) { return fail(op.syntax + ' takes three registers.'); }
          rd = needReg(parts[0], 'rd'); rs = needReg(parts[1], 'rs'); rt = needReg(parts[2], 'rt');
          fields = [
            fld('opcode', 6, '000000', 'R-type: always 000000'),
            fld('rs', 5, toBin(rs.n, 5), rs.name + ' = ' + rs.n),
            fld('rt', 5, toBin(rt.n, 5), rt.name + ' = ' + rt.n),
            fld('rd', 5, toBin(rd.n, 5), rd.name + ' = ' + rd.n),
            fld('shamt', 5, '00000', 'unused by this instruction'),
            fld('funct', 6, op.funct, mnemonic)
          ];
        } else if (op.form === 'rsh') {
          parts = rest.split(',');
          if (parts.length !== 3) { return fail(op.syntax + ' takes two registers and a shift amount.'); }
          rd = needReg(parts[0], 'rd'); rt = needReg(parts[1], 'rt');
          imm = needInt(parts[2], 0, 31, 'shift amount');
          fields = [
            fld('opcode', 6, '000000', 'R-type: always 000000'),
            fld('rs', 5, '00000', 'unused by a shift'),
            fld('rt', 5, toBin(rt.n, 5), rt.name + ' = ' + rt.n),
            fld('rd', 5, toBin(rd.n, 5), rd.name + ' = ' + rd.n),
            fld('shamt', 5, toBin(imm, 5), 'shift by ' + imm),
            fld('funct', 6, op.funct, mnemonic)
          ];
        } else {
          rs = needReg(rest, 'rs');
          fields = [
            fld('opcode', 6, '000000', 'R-type: always 000000'),
            fld('rs', 5, toBin(rs.n, 5), rs.name + ' = ' + rs.n),
            fld('rt', 5, '00000', 'unused'),
            fld('rd', 5, '00000', 'unused'),
            fld('shamt', 5, '00000', 'unused'),
            fld('funct', 6, op.funct, mnemonic)
          ];
        }
      } else if (found.type === 'I') {
        if (op.form === 'imem') {
          m = rest.match(/^([^,]+),\s*(-?\d+)\s*\(\s*(\$[A-Za-z0-9]+)\s*\)$/);
          if (!m) { return fail(op.syntax + ' — write the offset and base as imm($rs).'); }
          rt = needReg(m[1], 'rt'); rs = needReg(m[3], 'rs');
          imm = needInt(m[2], -32768, 65535, 'offset');
        } else {
          parts = rest.split(',');
          if (parts.length !== 3) { return fail(op.syntax + ' takes two registers and a number.'); }
          if (op.form === 'i3') {
            rt = needReg(parts[0], 'rt'); rs = needReg(parts[1], 'rs');
          } else {
            rs = needReg(parts[0], 'rs'); rt = needReg(parts[1], 'rt');
          }
          imm = needInt(parts[2], -32768, 65535, 'immediate');
        }
        fields = [
          fld('opcode', 6, op.opcode, mnemonic),
          fld('rs', 5, toBin(rs.n, 5), rs.name + ' = ' + rs.n),
          fld('rt', 5, toBin(rt.n, 5), rt.name + ' = ' + rt.n),
          fld('immediate', 16, toBin(imm, 16),
              imm + (imm < 0 ? ' — 16-bit two’s complement' : '') +
              (op.sext ? ' (sign-extended)' : ' (zero-extended)'))
        ];
      } else {
        imm = needInt(rest, 0, 67108863, 'target');
        fields = [
          fld('opcode', 6, op.opcode, mnemonic),
          fld('address', 26, toBin(imm, 26), 'target ' + imm)
        ];
      }
    } catch (e) {
      return fail(e.message);
    }

    var bits = '', i;
    for (i = 0; i < fields.length; i++) { bits += fields[i].bits; }
    if (bits.length !== 32) { return fail('Internal error: assembled ' + bits.length + ' bits, not 32.'); }
    return { ok: true, mnemonic: mnemonic, format: found.type, fields: fields, bits: bits };
  }

  /* ---- decode ----
     Read the opcode FIRST, then decide where the field boundaries are.
     That order is the algorithm, and it is what Assignment 5 Part C
     tests: you cannot split the bits until you know the format, and you
     cannot know the format until you have read the first six bits. */
  function mipsDecode(input) {
    var bits = String(input).replace(/[^01]/g, '');
    if (bits.length !== 32) {
      return fail('Need exactly 32 binary digits; got ' + bits.length + '.');
    }
    var opcode = bits.slice(0, 6), i, op = null, type, fields, text;

    if (opcode === '000000') {
      var funct = bits.slice(26, 32);
      for (i = 0; i < MIPS_R.length; i++) { if (MIPS_R[i].funct === funct) { op = MIPS_R[i]; } }
      if (!op) { return fail('Opcode 000000 means R-type, but funct ' + funct + ' is not in the table.'); }
      type = 'R';
      var rs = fromBin(bits.slice(6, 11)),
          rt = fromBin(bits.slice(11, 16)),
          rd = fromBin(bits.slice(16, 21)),
          sh = fromBin(bits.slice(21, 26));
      fields = [
        fld('opcode', 6, opcode, 'R-type'),
        fld('rs', 5, bits.slice(6, 11), regByNumber(rs).name + ' = ' + rs),
        fld('rt', 5, bits.slice(11, 16), regByNumber(rt).name + ' = ' + rt),
        fld('rd', 5, bits.slice(16, 21), regByNumber(rd).name + ' = ' + rd),
        fld('shamt', 5, bits.slice(21, 26), String(sh)),
        fld('funct', 6, funct, op.m)
      ];
      if (op.form === 'r3')       { text = op.m + ' ' + regByNumber(rd).name + ', ' + regByNumber(rs).name + ', ' + regByNumber(rt).name; }
      else if (op.form === 'rsh') { text = op.m + ' ' + regByNumber(rd).name + ', ' + regByNumber(rt).name + ', ' + sh; }
      else                        { text = op.m + ' ' + regByNumber(rs).name; }
      return { ok: true, mnemonic: op.m, format: type, fields: fields, text: text };
    }

    for (i = 0; i < MIPS_J.length; i++) { if (MIPS_J[i].opcode === opcode) { op = MIPS_J[i]; } }
    if (op) {
      var target = fromBin(bits.slice(6, 32));
      fields = [
        fld('opcode', 6, opcode, op.m),
        fld('address', 26, bits.slice(6, 32), String(target))
      ];
      return { ok: true, mnemonic: op.m, format: 'J', fields: fields, text: op.m + ' ' + target };
    }

    for (i = 0; i < MIPS_I.length; i++) { if (MIPS_I[i].opcode === opcode) { op = MIPS_I[i]; } }
    if (!op) { return fail('Opcode ' + opcode + ' is not in the Week 5 instruction table.'); }

    var irs = fromBin(bits.slice(6, 11)),
        irt = fromBin(bits.slice(11, 16)),
        immBits = bits.slice(16, 32),
        immVal = op.sext ? fromBinSigned(immBits) : fromBin(immBits);
    fields = [
      fld('opcode', 6, opcode, op.m),
      fld('rs', 5, bits.slice(6, 11), regByNumber(irs).name + ' = ' + irs),
      fld('rt', 5, bits.slice(11, 16), regByNumber(irt).name + ' = ' + irt),
      fld('immediate', 16, immBits, immVal + (op.sext ? ' (sign-extended)' : ' (zero-extended)'))
    ];
    if (op.form === 'imem')     { text = op.m + ' ' + regByNumber(irt).name + ', ' + immVal + '(' + regByNumber(irs).name + ')'; }
    else if (op.form === 'ibr') { text = op.m + ' ' + regByNumber(irs).name + ', ' + regByNumber(irt).name + ', ' + immVal; }
    else                        { text = op.m + ' ' + regByNumber(irt).name + ', ' + regByNumber(irs).name + ', ' + immVal; }
    return { ok: true, mnemonic: op.m, format: 'I', fields: fields, text: text };
  }

  /* ---------- Export ---------- */

  root.CSCLogic = {
    gates: gates,
    gateEval: gateEval,
    gateRule: gateRule,
    maxInputs: maxInputs,
    gateTable: gateTable,
    tokenize: tokenize,
    parse: parse,
    evaluate: evaluate,
    variables: variables,
    truthTable: truthTable,
    equivalent: equivalent,
    literalCount: literalCount,
    simplifyCheck: simplifyCheck,

    /* Week 3 additions — combinational circuit primitives */
    halfAdder: halfAdder,
    fullAdder: fullAdder,
    ripple: ripple,
    decode: decode,
    decoderCost: decoderCost,
    bitsToInt: bitsToInt,
    intToBits: intToBits,

    /* Week 4 additions -- sequential primitives */
    srStep: srStep,
    srSettle: srSettle,
    srLatch: srLatch,
    memCell: memCell,
    dLatch: dLatch,
    dFlipFlop: dFlipFlop,
    trace: trace,

    /* Week 5A additions -- word-width storage and bus primitives.
       NOTE the bit order: these are MSB-first, unlike bitsToInt/intToBits. */
    wordToInt: wordToInt,
    intToWord: intToWord,
    memWord: memWord,
    enableWord: enableWord,
    busResolve: busResolve,
    register8: register8,

    /* Week 5B additions -- the MIPS namespace. One opcode table for the
       whole course; SPAs and assignment pages render their reference
       tables from here rather than carrying their own copies. */
    mips: {
      regs: MIPS_REGS,
      r: MIPS_R,
      i: MIPS_I,
      j: MIPS_J,
      syscalls: MIPS_SYSCALLS,
      regByName: regByName,
      regByNumber: regByNumber,
      toBin: toBin,
      fromBin: fromBin,
      fromBinSigned: fromBinSigned,
      encode: mipsEncode,
      decode: mipsDecode
    }
  };

})(typeof window !== 'undefined' ? window : this);
