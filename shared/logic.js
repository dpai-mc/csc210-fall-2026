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
     WEEK 7 -- Control-flow address arithmetic and the assembler
     (CSCLogic.flow)
     ============================================================
     Added 2026-09-18.

     WHY THIS IS IN THE SHARED KERNEL. Standards Section 8's test is
     whether two or more files need it. Five do: the Branch Bench, the
     Jump Field Calculator and the What-The-Assembler-Emits widget on
     02-deciding.html and 03-repeating-and-jumping.html, the loop bench's
     PC display, and assignment7.html's Part C answer key.

     NAMING. Every helper here is flow-prefixed or lives inside the
     exported object. `target` was ALREADY a function name at this scope
     before this block was written, and Week 6 lost 42 test assertions to
     a silent shadow of exactly that kind (alu's evaluate() over Week 2's
     CSCLogic.evaluate). Check the file before adding a bare name.

     LOAD-BEARING ASSERTION, in the same category as srSettle's
     non-convergence and busResolve's contested bus:

       flowBranchOffset returns the offset in INSTRUCTIONS, never in
       bytes, and `fits` is computed against the word range -32768 to
       32767. A byte answer is wrong in a way that still looks plausible
       -- it is the same confusion that produced the Fall 2025 page's
       "can branch +/-32KB", which is off by a factor of four. week07-
       spa.test.js asserts the word semantics and the boundary cases, so
       a "fix" to bytes fails the suite instead of shipping.
     ============================================================ */

  /* The reach of a conditional branch. The INSTRUCTION figures are the
     ones the encoding produces; the byte figures are derived, and are
     given second everywhere in the course for that reason.

     maxBytes is 131068, not 131072: the largest offset is +32767
     instructions, and 32767 * 4 = 131068. The asymmetry is two's
     complement's, not a rounding error. */
  var FLOW_REACH = {
    minWords: -32768,
    maxWords: 32767,
    minBytes: -131072,
    maxBytes: 131068
  };

  function flowToBin(value, width) {
    var v = value < 0 ? value + Math.pow(2, width) : value;
    var s = (v >>> 0).toString(2);
    while (s.length < width) { s = '0' + s; }
    return s.slice(-width);
  }

  /* flowBranchOffset(pcBranch, targetAddr)

     The number the assembler puts in a beq/bne immediate field:

         words = (targetAddr - (pcBranch + 4)) / 4

     PC + 4 because the machine has already advanced past the branch by
     the time the branch is acted on. Divided by 4 because every MIPS
     instruction is four bytes and four-byte aligned, so the low two bits
     of a byte offset would always be zero -- storing them would spend
     two bits of a sixteen-bit field to carry no information, and
     counting instructions instead buys four times the reach for free.

     Returns { words, bits, fits, bytes, aligned }. `aligned` is false
     if either address is not a multiple of 4, which is a student error
     rather than a representable offset. */
  function flowBranchOffset(pcBranch, targetAddr) {
    var pc = pcBranch >>> 0, t = targetAddr >>> 0;
    var aligned = (pc % 4 === 0) && (t % 4 === 0);
    var bytes = t - (pc + 4);
    var words = bytes / 4;
    var fits = aligned &&
               Number.isInteger(words) &&
               words >= FLOW_REACH.minWords &&
               words <= FLOW_REACH.maxWords;
    return {
      words: words,
      bytes: bytes,
      aligned: aligned,
      fits: fits,
      bits: fits ? flowToBin(words, 16) : null
    };
  }

  /* The inverse: where a branch lands, given its own address and the
     offset in INSTRUCTIONS. */
  function flowBranchTarget(pcBranch, offsetWords) {
    return ((pcBranch >>> 0) + 4 + (offsetWords * 4)) >>> 0;
  }

  /* flowJumpField(targetAddr, pcJump)

     A J-type instruction carries 26 bits of WORD address. The low two
     bits are dropped because instructions are aligned; the top four are
     dropped because they are taken from the PC at run time. That is
     what limits a jump to a 256 MB region rather than the whole 4 GB
     address space.

     pcJump is optional. Given it, `fits` also checks that the target is
     inside the jump's own region -- which is the failure students never
     see, because every program they write lives in one region. */
  function flowJumpField(targetAddr, pcJump) {
    var t = targetAddr >>> 0;
    var aligned = (t % 4 === 0);
    var field = (t >>> 2) & 0x03FFFFFF;
    var sameRegion = true;
    if (pcJump !== undefined && pcJump !== null) {
      sameRegion = ((t & 0xF0000000) >>> 0) === ((((pcJump >>> 0) + 4) & 0xF0000000) >>> 0);
    }
    return {
      field: field >>> 0,
      bits: flowToBin(field, 26),
      aligned: aligned,
      sameRegion: sameRegion,
      fits: aligned && sameRegion
    };
  }

  /* flowJumpTarget(pcJump, field)

         PC = ((PC + 4) & 0xF0000000) | (field << 2)

     The shift is part of the formula, not a footnote to it. The Fall
     2025 page wrote the concatenation without the shift and put the
     shift in a separate box further down the page. */
  function flowJumpTarget(pcJump, field) {
    var hi = (((pcJump >>> 0) + 4) & 0xF0000000) >>> 0;
    return (hi | ((field << 2) >>> 0)) >>> 0;
  }

  /* ---- what the assembler actually emits ----

     MIPS has exactly two register-comparison branches: beq and bne.
     Everything below is a PSEUDO-INSTRUCTION -- convenient to write,
     and expanded by the assembler into real instructions before
     anything reaches the machine.

     The four comparison branches expand through `slt`, and slt's answer
     is the comparator leg's AL output -- the circuit students chained
     together in Week 6. `if (a < b)` in a high-level language is an slt
     in assembly is a wire coming out of an XOR cascade. That is the
     whole stack in one example, and it is why this table is content
     rather than a reference appendix.

     `$at` is the assembler's reserved scratch register. Week 5's
     register table already describes it as "reserved for the
     assembler"; this is what it is reserved FOR.

     `alu` names the ALU output that answers the expansion, for the
     widget's third panel. */
  var FLOW_PSEUDO = {
    blt:  { args: ['rs', 'rt', 'label'], alu: 'AL',
            expands: [['slt', '$at', 'rs', 'rt'], ['bne', '$at', '$zero', 'label']],
            why: 'a is less than b exactly when slt says so, and slt is the comparator’s AL flag with the operands in this order.' },
    bgt:  { args: ['rs', 'rt', 'label'], alu: 'AL',
            expands: [['slt', '$at', 'rt', 'rs'], ['bne', '$at', '$zero', 'label']],
            why: '"a greater than b" is "b less than a" -- the same slt with the operands swapped. No new hardware.' },
    ble:  { args: ['rs', 'rt', 'label'], alu: 'AL',
            expands: [['slt', '$at', 'rt', 'rs'], ['beq', '$at', '$zero', 'label']],
            why: '"a at most b" is "not (b less than a)". Same slt as bgt; the branch is inverted instead.' },
    bge:  { args: ['rs', 'rt', 'label'], alu: 'AL',
            expands: [['slt', '$at', 'rs', 'rt'], ['beq', '$at', '$zero', 'label']],
            why: '"a at least b" is "not (a less than b)". Same slt as blt, branch inverted.' },
    beqz: { args: ['rs', 'label'], alu: 'EQ',
            expands: [['beq', 'rs', '$zero', 'label']],
            why: 'one real instruction. $zero always reads 0, so comparing against it is a zero test.' },
    bnez: { args: ['rs', 'label'], alu: 'EQ',
            expands: [['bne', 'rs', '$zero', 'label']],
            why: 'as beqz, inverted.' },
    move: { args: ['rd', 'rs'], alu: 'ADD leg',
            expands: [['add', 'rd', 'rs', '$zero']],
            why: 'adding $zero changes nothing, so the sum is a copy. Week 6 taught this form directly.' },
    li:   { args: ['rd', 'imm'], alu: 'ADD leg',
            expands: [['addi', 'rd', '$zero', 'imm']],
            why: 'add the immediate to nothing. Only works while the value fits a 16-bit signed field -- a larger one expands to lui plus ori instead.',
            wide: [['lui', '$at', 'imm-upper'], ['ori', 'rd', '$at', 'imm-lower']] },
    la:   { args: ['rd', 'label'], alu: 'OR leg',
            expands: [['lui', '$at', 'label-upper'], ['ori', 'rd', '$at', 'label-lower']],
            why: 'an address is 32 bits and an immediate field is 16, so it takes two instructions: load the top half, or in the bottom half.' }
  };

  /* flowExpand('blt $t0, $t1, loop') -> the real instructions.

     Deliberately a small hand parser rather than a regex table: the
     widget shows the operands moving from the pseudo-instruction into
     the expansion, so the mapping has to be explicit and inspectable.
     Returns { ok, mnemonic, real: [...], why, alu } or { ok: false }. */
  function flowExpand(text) {
    var src = String(text).replace(/#.*$/, '').trim();
    if (!src) { return { ok: false, error: 'Nothing to expand.' }; }

    var sp = src.indexOf(' ');
    var m = (sp === -1 ? src : src.slice(0, sp)).toLowerCase();
    var entry = FLOW_PSEUDO[m];
    if (!entry) {
      return { ok: false, error: '"' + m + '" is not a pseudo-instruction. It is either a real MIPS instruction already, or not an instruction at all.' };
    }

    var rest = (sp === -1) ? '' : src.slice(sp + 1);
    var ops = rest.split(',').map(function (x) { return x.trim(); }).filter(function (x) { return x.length; });
    if (ops.length !== entry.args.length) {
      return { ok: false, error: m + ' takes ' + entry.args.length + ' operands (' + entry.args.join(', ') + '); got ' + ops.length + '.' };
    }

    var bind = {};
    entry.args.forEach(function (name, i) { bind[name] = ops[i]; });

    var wide = false;
    if (m === 'li') {
      var v = parseInt(bind.imm, 10);
      wide = !isNaN(v) && (v < -32768 || v > 65535);
    }
    var pattern = wide ? entry.wide : entry.expands;

    var real = pattern.map(function (parts) {
      var mn = parts[0];
      var rest2 = parts.slice(1).map(function (tok) {
        if (bind[tok] !== undefined) { return bind[tok]; }
        if (tok === 'imm-upper')   { return 'upper 16 bits of ' + bind.imm; }
        if (tok === 'imm-lower')   { return 'lower 16 bits of ' + bind.imm; }
        if (tok === 'label-upper') { return 'upper 16 bits of ' + bind.label; }
        if (tok === 'label-lower') { return 'lower 16 bits of ' + bind.label; }
        return tok;
      });
      /* lw/sw-style operands never appear here, so a plain comma join
         is the whole formatting rule. */
      return mn + ' ' + rest2.join(', ');
    });

    return {
      ok: true,
      mnemonic: m,
      real: real,
      why: entry.why,
      alu: entry.alu,
      usesAt: real.some(function (r) { return r.indexOf('$at') !== -1; }),
      wide: wide
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
     WEEK 6 -- The ALU operation legs (CSCLogic.alu)
     ============================================================
     Added 2026-09-18.

     WHY THIS IS IN THE SHARED KERNEL. Standards Section 8's test is
     whether two or more files need it. Seven do: four widgets on
     01-seven-ways.html, the cascade widget on 02-larger-equal-zero.html,
     two widgets on 03-saying-it-in-mips.html, and assignment6.html's
     Part C verification table.

     BIT ORDER. MSB-first arrays, matching wordToInt/intToWord and the
     rest of the Week 5 word section -- [1,0,1,0,1,0,1,0] reads as the
     byte 10101010, the order a student sees on a Logisim probe. The
     LSB-first boundary to ripple() lives inside aluAdd() and NOWHERE
     else.

     WHAT THIS MODELS, AND WHAT IT DOES NOT. These are the seven
     operation LEGS, built and tested individually as Checkpoint 2a.
     There is no decoder and no output-selection stage here, because
     Week 6 does not build them -- they are Checkpoint 2b, Week 7.
     evaluate() below reaches ahead only far enough to answer "which leg
     would be selected", because that question is the whole point of the
     ALU Bench widget.

     TWO LOAD-BEARING ASSERTIONS, in the same category as srSettle's
     non-convergence and busResolve's contested bus:

       1. evaluate() with opcode 7 returns out: null, NEVER 0. Decoder
          output 7 connects to nothing (Dave, 2026-09-18), so no leg is
          enabled and nothing drives the output. A floating output is not
          a zero output. Week 6 teaches that difference; the day this
          returns 0 the teaching becomes false.

       2. cmp8() takes no opcode and computes al/eq unconditionally. The
          comparator is ALWAYS live -- it is where two of the machine's
          three status flags come from, and Weeks 7 and 10 build
          branching on them. A future refactor that gates it behind
          opcode 110 breaks the flag model of the whole CPU.

     week06-spa.test.js asserts both, so a "fix" to either fails the
     suite instead of shipping.

     THE ALU OUTPUT IS NOT A BUS. Week 5's section 5.3 teaches that a
     shared wire needs devices that can stop driving rather than drive a
     0. The seven legs share an output and that is NOT the same
     situation: unselected legs drive 0, the results are ORed, and 0 is
     the identity for OR. Do not route these through busResolve(); it
     would report a conflict that the hardware does not have.
     ============================================================ */

  /* The operation table. cinRole/coutRole are what the shared carry
     pins MEAN for each operation -- three operations use them and they
     mean something different in each, which is the interface-design
     point the ALU Bench makes by relabelling them live. */
  var ALU_OPS = [
    { code: 0, bits: '000', name: 'ADD',         uses: ['a','b','cin'], cinRole: 'carry in',  coutRole: 'carry out' },
    { code: 1, bits: '001', name: 'SHIFT RIGHT', uses: ['a','cin'],     cinRole: 'shift in',  coutRole: 'shift out' },
    { code: 2, bits: '010', name: 'SHIFT LEFT',  uses: ['a','cin'],     cinRole: 'shift in',  coutRole: 'shift out' },
    { code: 3, bits: '011', name: 'NOT',         uses: ['a'],           cinRole: null,        coutRole: null },
    { code: 4, bits: '100', name: 'AND',         uses: ['a','b'],       cinRole: null,        coutRole: null },
    { code: 5, bits: '101', name: 'OR',          uses: ['a','b'],       cinRole: null,        coutRole: null },
    { code: 6, bits: '110', name: 'XOR',         uses: ['a','b'],       cinRole: null,        coutRole: null },
    { code: 7, bits: '111', name: null,          uses: [],              cinRole: null,        coutRole: null }
  ];

  function aluWord(bits) {
    var out = [], i;
    for (i = 0; i < 8; i++) { out.push(bits && bits[i] ? 1 : 0); }
    return out;
  }

  /* ---- the bitwise legs ----
     Eight gates in parallel. Bit i of the output depends on bit i of the
     inputs and on nothing else, which is why these settle all at once
     and the adder does not. That independence is the section 6.3
     teaching point and it is visible right here in the loop bound. */

  function and8(a, b) {
    var x = aluWord(a), y = aluWord(b), o = [], i;
    for (i = 0; i < 8; i++) { o.push(x[i] & y[i]); }
    return o;
  }

  function or8(a, b) {
    var x = aluWord(a), y = aluWord(b), o = [], i;
    for (i = 0; i < 8; i++) { o.push(x[i] | y[i]); }
    return o;
  }

  function xor8(a, b) {
    var x = aluWord(a), y = aluWord(b), o = [], i;
    for (i = 0; i < 8; i++) { o.push(x[i] ^ y[i]); }
    return o;
  }

  function not8(a) {
    var x = aluWord(a), o = [], i;
    for (i = 0; i < 8; i++) { o.push(x[i] ? 0 : 1); }
    return o;
  }

  /* ---- the adder leg ----
     One instance of the Week 3 ADDER_8BIT. Nothing is built here and
     nothing should be reimplemented here: this wraps ripple(), which is
     the circuit students already own. The ONLY thing this function adds
     is the bit-order conversion, and it is the only place in the alu
     namespace that touches LSB-first order. */
  function aluAdd(a, b, cin) {
    var x = aluWord(a), y = aluWord(b), i;
    var al = [], bl = [];
    for (i = 7; i >= 0; i--) { al.push(x[i]); bl.push(y[i]); }
    var r = ripple(al, bl, cin ? 1 : 0);
    var out = [];
    for (i = 7; i >= 0; i--) { out.push(r.sum[i]); }
    return { out: out, cout: r.cout };
  }

  /* Signed vs unsigned overflow, kept as two separate answers because
     Standards Section 2 says they are two separate concepts and a single
     "overflow" flag is exactly the conflation it forbids.

       unsigned  the carry out of the MSB. 255 + 1 does not fit.
       signed    the two's-complement result contradicts what the
                 operand signs predict. 127 + 1 fits in eight bits and
                 is still wrong.

     The adder hardware cannot tell which one the program meant; it
     produces both indications and the software decides which matters. */
  function addFlags(a, b, cin) {
    var x = aluWord(a), y = aluWord(b);
    var r = aluAdd(x, y, cin);
    var sa = x[0], sb = y[0], so = r.out[0];
    return {
      out: r.out,
      cout: r.cout,
      unsignedOverflow: r.cout,
      signedOverflow: (sa === sb && so !== sa) ? 1 : 0
    };
  }

  /* ---- the shift legs ----
     A shift is a re-indexing. shin fills the vacated end, shout catches
     the departing bit, and the two are the ALU's shared cin/cout pins
     doing a second job -- named shin/shout at leg level because this
     circuit is not adding and should not borrow the adder's vocabulary.

       SHIFT_LEFT   bit i -> bit i+1;  shin fills bit 0,  shout <- bit 7
       SHIFT_RIGHT  bit i -> bit i-1;  shin fills bit 7,  shout <- bit 0

     Confirmed by Dave 2026-09-18 against the built circuit. */
  function shiftLeft(a, shin) {
    var x = aluWord(a), o = [], i;
    for (i = 1; i < 8; i++) { o.push(x[i]); }
    o.push(shin ? 1 : 0);
    return { out: o, shout: x[0] };
  }

  function shiftRight(a, shin) {
    var x = aluWord(a), o = [], i;
    o.push(shin ? 1 : 0);
    for (i = 0; i < 7; i++) { o.push(x[i]); }
    return { out: o, shout: x[7] };
  }

  /* ---- the comparator ----

     cmp1 is XOR_CMP_1BIT: one XOR gate and three answers.

       o = a XOR b                     the bitwise result
       e = NOT(a XOR b) AND pe         equal here AND equal everywhere above
       l = pl OR (a AND (a XOR b) AND pe)

     The pe term in l is the part students do not guess. Without it, a
     lower bit could claim "a is larger" after a higher bit had already
     settled the question the other way. The pl term carries a decision
     already made further up, unchanged, to the bottom of the chain.

     Written as the gate expressions rather than as a numeric comparison,
     for the same reason decode() is written as an AND of polarities: a
     shortcut would give the right answer while demonstrating nothing,
     and this kernel drives a widget whose job is to show the gates. */
  function cmp1(a, b, pl, pe) {
    a = a ? 1 : 0; b = b ? 1 : 0; pl = pl ? 1 : 0; pe = pe ? 1 : 0;
    var x = a ^ b;
    return {
      o: x,
      e: (x ? 0 : 1) & pe,
      l: pl | (a & x & pe)
    };
  }

  /* cmp8 -- eight instances of cmp1 chained MSB -> LSB.

     THE DIRECTION IS THE TEACHING POINT. The adder chains LSB -> MSB
     because a carry propagates upward. The comparator chains the other
     way because the most significant bit where two numbers differ
     decides which is larger and nothing below it matters. Same
     construction pattern, opposite direction, and the reason is in the
     arithmetic rather than in the wiring.

     Bit 7's instance is seeded pl = 0, pe = 1 -- nothing above it is
     larger, and everything above it (there is nothing) is equal.

     stages[0] is BIT 7, not bit 0. The array is in cascade order because
     that is the order the widget steps through and the order the
     chaining is built in. week06-spa.test.js asserts it. */
  function cmp8(a, b) {
    var x = aluWord(a), y = aluWord(b);
    var pl = 0, pe = 1;
    var xorBits = [], stages = [], i, s;

    for (i = 0; i < 8; i++) {
      s = cmp1(x[i], y[i], pl, pe);
      stages.push({ i: 7 - i, a: x[i], b: y[i], pl: pl, pe: pe, o: s.o, l: s.l, e: s.e });
      xorBits.push(s.o);
      pl = s.l;
      pe = s.e;
    }
    return { xor: xorBits, al: pl, eq: pe, stages: stages };
  }

  /* IS_ZERO -- an eight-input OR, inverted. It watches the ALU's final
     output, after selection, so it reports on whichever operation was
     chosen. It belongs to no leg. */
  function isZero(word) {
    var x = aluWord(word), i;
    for (i = 0; i < 8; i++) { if (x[i]) { return 0; } }
    return 1;
  }

  /* MIPS_LEG -- which ALU leg each Week 6 instruction drives.

     THIS IS THE WEEK'S SLO2 CONTENT AS DATA. It lives in the shared
     kernel rather than in a page because two files render it: the
     instruction cards and the Instruction-to-Leg widget on
     03-saying-it-in-mips.html, and assignment6.html's Part C table.
     Two copies free to drift apart is exactly the Fall 2025 failure
     Standards Section 8 exists to prevent.

       opcode  the 3-bit ALU opcode, or null where no single leg answers
       via     a short phrase naming the route, shown as a badge
       from    'output'  the answer is the 8-bit ALU result
               'flag'    the answer is a status flag, NOT the 8-bit output
       note    one sentence, where the mapping is not one-to-one

     sub, nor, slt and slti are the four that teach something. The other
     six are one instruction, one leg, and they are the baseline that
     makes those four visible as departures. */
  var MIPS_LEG = {
    add:  { opcode: 0, via: 'ADD',            from: 'output' },
    addi: { opcode: 0, via: 'ADD',            from: 'output',
            note: 'The immediate is sign-extended before it reaches the ALU. The leg is the same one add uses.' },
    sub:  { opcode: 0, via: 'NOT then ADD',   from: 'output',
            note: 'No subtract leg exists. B goes through NOT_8BIT and the adder runs with carry-in 1.' },
    and:  { opcode: 4, via: 'AND',            from: 'output' },
    andi: { opcode: 4, via: 'AND',            from: 'output',
            note: 'The immediate is ZERO-extended, not sign-extended. There is no such thing as a signed bit mask.' },
    or:   { opcode: 5, via: 'OR',             from: 'output' },
    ori:  { opcode: 5, via: 'OR',             from: 'output',
            note: 'Zero-extended immediate, same as andi.' },
    nor:  { opcode: 5, via: 'OR then NOT',    from: 'output',
            note: 'The only Week 6 instruction with no leg of its own. Two ALU operations, or one extra inverter.' },
    xor:  { opcode: 6, via: 'XOR',            from: 'output' },
    slt:  { opcode: 6, via: 'comparator AL',  from: 'flag',
            note: 'The answer is a status flag, not the 8-bit result. The comparator already computed it.' },
    slti: { opcode: 6, via: 'comparator AL',  from: 'flag',
            note: 'Same flag, with a sign-extended immediate standing in for the second register.' }
  };

  /* aluEvaluate(opcode, a, b, cin)  -- exported as CSCLogic.alu.evaluate.
     NOT named evaluate(): CSCLogic already has a Boolean-expression
     evaluate() from Week 2, and a second one at the same scope silently
     shadowed it. Caught 2026-09-18 when 42 of logic.test.js's Boolean
     assertions failed on a change that touched no Boolean code.

     COMPUTES ALL SEVEN LEGS ON EVERY CALL, ON PURPOSE. A switch on
     opcode would be faster and would demonstrate nothing. The machine
     genuinely performs all seven operations on every input and discards
     six of them, and the ALU Bench widget exists to show exactly that,
     so the kernel must actually do it. Do not "optimise" this into a
     dispatch.

     Returns:
       legs      every leg's live result, keyed by operation name
       selected  the ALU_OPS entry for this opcode
       out       the 8-bit result reaching the output, or NULL for 111
       cout      the shared carry/shift out bit, or null where unused
       al, eq    from the comparator -- always live, never gated
       z         isZero of the OUTPUT, or null when nothing drives it

     out is null rather than 0 for opcode 111. Load-bearing. */
  function aluEvaluate(opcode, a, b, cin) {
    var x = aluWord(a), y = aluWord(b), c = cin ? 1 : 0;
    var code = (opcode | 0) & 7;

    var add = addFlags(x, y, c);
    var shr = shiftRight(x, c);
    var shl = shiftLeft(x, c);
    var cmp = cmp8(x, y);

    var legs = {
      ADD:           { out: add.out, cout: add.cout,
                       unsignedOverflow: add.unsignedOverflow,
                       signedOverflow: add.signedOverflow },
      'SHIFT RIGHT': { out: shr.out, cout: shr.shout },
      'SHIFT LEFT':  { out: shl.out, cout: shl.shout },
      NOT:           { out: not8(x),    cout: null },
      AND:           { out: and8(x, y), cout: null },
      OR:            { out: or8(x, y),  cout: null },
      XOR:           { out: cmp.xor,    cout: null }
    };

    var sel = ALU_OPS[code];
    var chosen = sel.name ? legs[sel.name] : null;

    return {
      legs: legs,
      selected: sel,
      out: chosen ? chosen.out.slice() : null,
      cout: chosen ? chosen.cout : null,
      al: cmp.al,
      eq: cmp.eq,
      z: chosen ? isZero(chosen.out) : null,
      cmp: cmp
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
    { m: 'nor', funct: '100111', form: 'r3',  week: 6, syntax: 'nor $rd, $rs, $rt',   desc: 'rd = NOT (rs OR rt), bitwise' },
    { m: 'sll', funct: '000000', form: 'rsh', week: 7, syntax: 'sll $rd, $rt, shamt', desc: 'rd = rt shifted left by shamt' },
    { m: 'srl', funct: '000010', form: 'rsh', week: 7, syntax: 'srl $rd, $rt, shamt', desc: 'rd = rt shifted right by shamt' },
    { m: 'jr',  funct: '001000', form: 'rjr', week: 7, syntax: 'jr $rs',              desc: 'jump to the address held in rs' }
  ];

  var MIPS_I = [
    { m: 'addi', opcode: '001000', form: 'i3',   week: 5, sext: true,  syntax: 'addi $rt, $rs, imm',  desc: 'rt = rs + imm, immediate SIGN-extended' },
    { m: 'andi', opcode: '001100', form: 'i3',   week: 5, sext: false, syntax: 'andi $rt, $rs, imm',  desc: 'rt = rs AND imm, immediate ZERO-extended' },
    { m: 'ori',  opcode: '001101', form: 'i3',   week: 5, sext: false, syntax: 'ori $rt, $rs, imm',   desc: 'rt = rs OR imm, immediate ZERO-extended' },
    { m: 'slti', opcode: '001010', form: 'i3',   week: 6, sext: true,  syntax: 'slti $rt, $rs, imm', desc: 'rt = 1 if rs < imm, else 0; immediate SIGN-extended' },
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

    /* Week 6 additions -- the ALU operation legs. Checkpoint 2a only:
       no decoder and no output-selection stage, which are Week 7. */
    alu: {
      OPS: ALU_OPS,
      MIPS_LEG: MIPS_LEG,
      and8: and8,
      or8: or8,
      xor8: xor8,
      not8: not8,
      add: aluAdd,
      addFlags: addFlags,
      shiftLeft: shiftLeft,
      shiftRight: shiftRight,
      cmp1: cmp1,
      cmp8: cmp8,
      isZero: isZero,
      evaluate: aluEvaluate
    },

    /* Week 7 additions -- control-flow address arithmetic and the
       assembler's pseudo-instruction expansions. */
    flow: {
      REACH: FLOW_REACH,
      PSEUDO: FLOW_PSEUDO,
      branchOffset: flowBranchOffset,
      branchTarget: flowBranchTarget,
      jumpField: flowJumpField,
      jumpTarget: flowJumpTarget,
      expand: flowExpand
    },

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
