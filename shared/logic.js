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
    simplifyCheck: simplifyCheck
  };

})(typeof window !== 'undefined' ? window : this);
