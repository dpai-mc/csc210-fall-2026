/* ============================================================
   CSC210 — Regression tests for shared/logic.js
   ============================================================
   Run:  node shared/logic.test.js      (from the repo root)
   Exits non-zero on any failure.

   Every expression in docs/CSC210-Week2-Spec.md that has a
   stated answer or truth table is asserted here. If a future
   spec edit changes an answer, this catches the drift.
   ============================================================ */

var root = {};
var fs = require('fs');
var path = require('path');
eval(fs.readFileSync(path.join(__dirname, 'logic.js'), 'utf8').replace(/typeof window !== 'undefined' \? window : this/, 'root'));
var L=root.CSCLogic, pass=0, fail=0;
function eq(a,b,label,expect){
  if(expect===undefined) expect=true;
  var r; try{ r=L.equivalent(a,b);}catch(e){ console.log('ERR  '+label+': '+e.message); fail++; return;}
  if(r===expect){pass++; console.log('ok   '+label);}
  else{fail++; console.log('FAIL '+label+'  got '+r+' want '+expect);}
}
function tt(s,expected,label){
  var r; try{ r=L.truthTable(s);}catch(e){console.log('ERR  '+label+': '+e.message);fail++;return;}
  var got=r.rows.map(function(x){return x.out;}).join('');
  if(got===expected){pass++;console.log('ok   '+label+'  ['+got+']');}
  else{fail++;console.log('FAIL '+label+'  got ['+got+'] want ['+expected+']');}
}

console.log('--- THE CORRECTED SPEC ITEM (Widget2 ex4 / Problem 7c) ---');
tt("A'B' + A'B + AB","1101","LHS A'B'+A'B+AB");
eq("A'B' + A'B + AB","A' + B","  == A' + B  (corrected)");
eq("A'B' + A'B + AB","A + B'","  == A + B'  (old spec, must be false)",false);

console.log('\n--- Widget 2 pre-loaded exercises ---');
eq("AB + AB'","A","ex1  AB+AB' = A");
eq("(A + B)(A + B')","A","ex2  (A+B)(A+B') = A");
eq("(AB)'","A' + B'","ex3  (AB)' = A'+B'  [De Morgan]");
eq("A'B' + A'B + AB","A' + B","ex4  (corrected)");

console.log('\n--- Assignment Part B Q5 simplifications ---');
eq("A + AB","A","5a  A+AB = A");
eq("(A + B)(A + B')","A","5b");
eq("A(B + A'B)","AB","5c  A(B+A'B) = AB");
eq("(A + B + C)(A' + B)","B + A'C","5d  = B + A'C");

console.log('\n--- Q6 De Morgan complements ---');
eq("(AB + C)'","(A' + B')C'","6a");
eq("(A + BC)'","A'(B' + C')","6b");
eq("(A'B + AB')'","(A + B')(A' + B)","6c");

console.log('\n--- Q7 equivalence proofs ---');
eq("AB + AB'","A","7a");
eq("(A + B)(A' + B)","B","7b");
eq("A'B' + A'B + AB","A' + B","7c  (corrected)");

console.log('\n--- Q15 sum-of-products from truth table 01011101 ---');
tt("A'B'C + A'BC + AB'C' + AB'C + ABC","01011101","Q15 SOP");
eq("A'B'C + A'BC + AB'C' + AB'C + ABC","C + AB'","Q16 simplifies to C + AB'");

console.log('\n--- Circuit 4 BOOLEAN_EXPR: F = (A AND B) OR (NOT C) ---');
tt("AB + C'","10101011","spec truth table col F");

console.log('\n--- Circuit 5 DEMORGAN_CHECK ---');
eq("(AB)'","A' + B'","law 1 sides equal");
eq("(A+B)'","A'B'","law 2 sides equal");
tt("(AB)' ^ (A' + B')","0000","XOR harness reads 0 for all inputs");

console.log('\n--- NAND universality derivations (Part C) ---');
eq("(AA)'","A'","Q10 NAND(A,A) = NOT A");
eq("((AB)'(AB)')'","AB","Q11 NAND(NAND(AB),NAND(AB)) = AND");
eq("((AA)'(BB)')'","A + B","Q12 NAND(NOT A,NOT B) = OR");
eq("(((AA)'(BB)')'((AA)'(BB)')')'","(A+B)'","Q13 NOR from NAND");

console.log('\n--- Notation equivalence (Standards 8 requirement) ---');
eq("AB + AB'","A*B + A*!B","prime/juxtaposition == star/bang");
eq("A'B'","!A & !B","A'B' == !A & !B");
eq("A NAND B","(AB)'","word NAND == (AB)'");
eq("A XNOR B","(A^B)'","word XNOR");
eq("NOT A OR B","A' + B","word NOT/OR");
eq("A'","NOT A","postfix == prefix");

console.log('\n--- Gate tables ---');
['AND','OR','NOT','NAND','NOR','XOR','XNOR'].forEach(function(g){
  var t=L.gateTable(g), outs=t.map(function(r){return r[r.length-1];}).join('');
  var want={AND:'0001',OR:'0111',NOT:'10',NAND:'1110',NOR:'1000',XOR:'0110',XNOR:'1001'}[g];
  if(outs===want){pass++;console.log('ok   '+g+' ['+outs+']');}else{fail++;console.log('FAIL '+g+' got '+outs+' want '+want);}
});

console.log('\n--- simplifyCheck behavior ---');
var r1=L.simplifyCheck("AB + AB'","A");
console.log((r1.ok&&r1.simpler?'ok  ':'FAIL')+' correct simplification -> '+r1.reason); r1.ok&&r1.simpler?pass++:fail++;
var r2=L.simplifyCheck("AB + AB'","A + B'");
console.log((!r2.ok&&r2.reason==='not-equivalent'?'ok  ':'FAIL')+' wrong answer -> '+r2.reason); (!r2.ok)?pass++:fail++;
var r3=L.simplifyCheck("A","A + AA");
console.log((r3.equivalent&&!r3.simpler?'ok  ':'FAIL')+' equivalent but not simpler -> '+r3.reason); (r3.equivalent&&!r3.simpler)?pass++:fail++;
var r4=L.simplifyCheck("AB","A B )(");
console.log((!r4.ok&&r4.reason.indexOf('parse-error')===0?'ok  ':'FAIL')+' malformed input -> '+r4.reason); (!r4.ok)?pass++:fail++;

console.log('\n--- precedence sanity ---');
tt("A + BC","00011111","A+BC (AND binds tighter than OR)");
eq("A + BC","A + (BC)","explicit parens agree");
eq("(A+B)C","AC + BC","distributive");
eq("A''","A","double prime = identity");
eq("A'''","A'","triple prime");

/* ============================================================
   WEEK 3 — combinational primitives
   ============================================================ */

function ok(cond,label){ if(cond){pass++;console.log('ok   '+label);} else {fail++;console.log('FAIL '+label);} }

console.log('\n--- Week 3: half adder (spec Deliverable 2, Circuit 1) ---');
[[0,0,0,0],[0,1,1,0],[1,0,1,0],[1,1,0,1]].forEach(function(r){
  var h=L.halfAdder(r[0],r[1]);
  ok(h.sum===r[2]&&h.carry===r[3],'HALF_ADDER a='+r[0]+' b='+r[1]+' -> sum '+r[2]+' carry '+r[3]);
});
// The half adder is XOR and AND side by side — assert that against the parser,
// so the two halves of the kernel cannot drift apart.
ok([[0,0],[0,1],[1,0],[1,1]].every(function(p){
  var h=L.halfAdder(p[0],p[1]);
  return h.sum===L.evaluate(L.parse("A^B"),{A:p[0],B:p[1]}) &&
         h.carry===L.evaluate(L.parse("AB"),{A:p[0],B:p[1]});
}),'half adder agrees with parsed A^B / AB');

console.log('\n--- Week 3: full adder (spec Deliverable 2, Circuit 2 — all 8 rows) ---');
// cin, a, b, sum, cout — transcribed from the spec table
[[0,0,0,0,0],[0,0,1,1,0],[0,1,0,1,0],[0,1,1,0,1],
 [1,0,0,1,0],[1,0,1,0,1],[1,1,0,0,1],[1,1,1,1,1]].forEach(function(r){
  var f=L.fullAdder(r[1],r[2],r[0]);
  ok(f.sum===r[3]&&f.cout===r[4],'FULL_ADDER cin='+r[0]+' a='+r[1]+' b='+r[2]+' -> sum '+r[3]+' cout '+r[4]);
});
ok([0,1].every(function(c){return [0,1].every(function(a){return [0,1].every(function(b){
    var f=L.fullAdder(a,b,c);
    return f.sum===L.evaluate(L.parse("A^B^C"),{A:a,B:b,C:c}) &&
           f.cout===L.evaluate(L.parse("AB + C(A^B)"),{A:a,B:b,C:c});
  });});}),'full adder agrees with parsed A^B^C / AB+C(A^B)');

console.log('\n--- Week 3: ripple() exhaustive, all 65,536 8-bit pairs ---');
var bad=0, worstCarries=0;
for(var a=0;a<256;a++){
  for(var b=0;b<256;b++){
    var r=L.ripple(L.intToBits(a,8),L.intToBits(b,8),0);
    if(L.bitsToInt(r.sum)+(r.cout<<8) !== a+b) bad++;
    if(r.stages.length!==8) bad++;
  }
}
ok(bad===0,'ripple matches integer addition for all 65,536 pairs (mismatches: '+bad+')');

// cin is honoured
ok((function(){var r=L.ripple(L.intToBits(5,8),L.intToBits(9,8),1);
   return L.bitsToInt(r.sum)===15 && r.cout===0;})(),'ripple honours cin=1  (5+9+1=15)');

console.log('\n--- Week 3: the three SPA presets (spec §3.4) ---');
function preset(a,b,label){
  var r=L.ripple(L.intToBits(a,8),L.intToBits(b,8),0);
  var carried=r.stages.filter(function(s){return s.cout===1;}).length;
  return {sum:L.bitsToInt(r.sum),cout:r.cout,carried:carried,label:label};
}
var p1=preset(0xFF,0x01,'worst case');
ok(p1.sum===0&&p1.cout===1&&p1.carried===8,'preset 11111111+00000001 -> sum 0, cout 1, carry through all 8 stages');
var p2=preset(0x81,0x81,'Part A Q5');
ok(p2.sum===2&&p2.cout===1,'preset 10000001+10000001 -> sum 00000010, cout 1  (unsigned 129+129=258)');
// Standards Section 2: this same pair is ALSO signed overflow. Assert both readings
// so nobody "fixes" the labelling by quietly changing the example.
ok((function(){var s=function(x){return x>=128?x-256:x;};
   return s(0x81)+s(0x81) === -254 && (s(0x81)+s(0x81) < -128);
  })(),'and IS signed overflow too: -127 + -127 = -254, outside [-128,127]');
var p3=preset(0x4D,0x26,'plain');
ok(p3.sum===115&&p3.cout===0&&p3.carried===2,'preset 01001101+00100110 -> 115, no cout, 2 stages carry');

console.log('\n--- Week 3: decode() (spec Deliverable 2, Circuits 4-6) ---');
[2,3,4].forEach(function(n){
  var allOk=true;
  for(var v=0; v<(1<<n); v++){
    var outs=L.decode(L.intToBits(v,n));
    var hot=outs.reduce(function(s,x){return s+x;},0);
    if(outs.length!==(1<<n) || hot!==1 || outs[v]!==1) allOk=false;
  }
  ok(allOk,'DECODER_'+n+'TO'+(1<<n)+': every input raises exactly one output, and it is out'+'[value]');
});
// Pin ordering is part of the component interface (spec: sel 00 -> out0).
ok(L.decode([0,0])[0]===1,'sel=00 raises out0');
ok(L.decode([1,0])[1]===1,'sel=01 raises out1   (LSB-first: [1,0] is 01)');
ok(L.decode([0,1])[2]===1,'sel=10 raises out2');
ok(L.decode([1,1])[3]===1,'sel=11 raises out3');

console.log('\n--- Week 3: decoderCost() (the SPA prose claims) ---');
ok(L.decoderCost(2).andGates===4  && L.decoderCost(2).andInputs===2,'2x4  = 4 AND gates of 2 inputs');
ok(L.decoderCost(3).andGates===8  && L.decoderCost(3).andInputs===3,'3x8  = 8 AND gates of 3 inputs');
ok(L.decoderCost(4).andGates===16 && L.decoderCost(4).andInputs===4,'4x16 = 16 AND gates of 4 inputs');
ok(L.decoderCost(16).andGates===65536,'16-bit address would need 65,536 AND gates (the SPA prose figure)');

console.log('\n--- Week 3: bit-array convention ---');
ok(L.intToBits(3,8).join('')==='11000000','intToBits is LSB-first: 3 -> 11000000');
ok(L.bitsToInt(L.intToBits(200,8))===200,'bitsToInt round-trips');


console.log('\n--- Week 4: srSettle() -- the S-R latch, exhaustively ---');
/* Four input combinations x both prior states = 8 cases. Written out
   rather than generated, so the expected values are a statement of the
   circuit's behaviour rather than a re-derivation of the code. */
ok(L.srSettle(1,1,1,0).settled && L.srSettle(1,1,1,0).q===1, 'hold from q=1 keeps q=1');
ok(L.srSettle(1,1,0,1).settled && L.srSettle(1,1,0,1).q===0, 'hold from q=0 keeps q=0');
ok(L.srSettle(0,1,0,1).settled && L.srSettle(0,1,0,1).q===1, 'set from q=0 -> q=1');
ok(L.srSettle(0,1,1,0).settled && L.srSettle(0,1,1,0).q===1, 'set from q=1 stays 1');
ok(L.srSettle(1,0,1,0).settled && L.srSettle(1,0,1,0).q===0, 'reset from q=1 -> q=0');
ok(L.srSettle(1,0,0,1).settled && L.srSettle(1,0,0,1).q===0, 'reset from q=0 stays 0');
ok(L.srSettle(0,0,1,0).settled && L.srSettle(0,0,1,0).q===1 && L.srSettle(0,0,1,0).nq===1,
   'forbidden drives BOTH outputs to 1 (from q=1)');
ok(L.srSettle(0,0,0,1).settled && L.srSettle(0,0,0,1).q===1 && L.srSettle(0,0,0,1).nq===1,
   'forbidden drives BOTH outputs to 1 (from q=0)');

ok(L.srSettle(1,1,1,0).state==='hold',      'state names: hold');
ok(L.srSettle(0,1,0,1).state==='set',       'state names: set');
ok(L.srSettle(1,0,1,0).state==='reset',     'state names: reset');
ok(L.srSettle(0,0,1,0).state==='forbidden', 'state names: forbidden');

console.log('\n--- Week 4: THE RACE MUST NOT RESOLVE ---');
/* Releasing the forbidden state -- both inputs back to 1 from q=nq=1 --
   has no defined outcome. Which gate wins depends on which is physically
   faster, and that is not knowable.

   The Fall 2025 widget resolved it to q=1 every time, because its settle
   loop evaluated the top gate first on every pass. Students were taught
   that leaving the forbidden state gives Set. It does not.

   These three assertions exist so that a future edit which "fixes" the
   oscillation by picking a winner FAILS THE SUITE instead of shipping.
   If you are here because one of them is failing: the bug is in the
   change you just made to srSettle, not in the test. */
var race = L.srSettle(1,1,1,1);
ok(race.settled === false, 'forbidden RELEASE does not converge');
ok(race.state === 'race',  'forbidden release is reported as a race, not a state');
ok(race.steps.length >= 4, 'the race oscillates rather than stopping after one pass');
ok(L.srSettle(1,1,1,1).settled === L.srSettle(1,1,1,1).settled, 'race result is deterministic in its non-determinism');

console.log('\n--- Week 4: memCell() / MEM_1BIT, exhaustively ---');
/* Four (In, Set) combinations x both prior states = 8 cases. */
ok(L.memCell(0,0,0).q===0, 'Set=0 In=0 from q=0 holds 0');
ok(L.memCell(1,0,0).q===0, 'Set=0 In=1 from q=0 HOLDS 0 -- In is ignored while Set is low');
ok(L.memCell(0,0,1).q===1, 'Set=0 In=0 from q=1 HOLDS 1 -- In is ignored while Set is low');
ok(L.memCell(1,0,1).q===1, 'Set=0 In=1 from q=1 holds 1');
ok(L.memCell(0,1,0).q===0, 'Set=1 In=0 from q=0 -> 0');
ok(L.memCell(0,1,1).q===0, 'Set=1 In=0 from q=1 -> 0  (transparent)');
ok(L.memCell(1,1,0).q===1, 'Set=1 In=1 from q=0 -> 1  (transparent)');
ok(L.memCell(1,1,1).q===1, 'Set=1 In=1 from q=1 -> 1');

/* The four-gate construction's whole justification: the forbidden state
   is unreachable because A and B can never both be 0. */
var f = true, ii, ss;
for (ii=0; ii<2; ii++) for (ss=0; ss<2; ss++) {
  var c = L.memCell(ii, ss, 0);
  if (c.nS === 0 && c.nR === 0) f = false;
}
ok(f, 'MEM_1BIT can NEVER drive both latch inputs low -- forbidden state unreachable by construction');
ok(L.memCell(1,1,0).transparent === true,  'transparent while Set = 1');
ok(L.memCell(1,0,0).transparent === false, 'not transparent while Set = 0');

console.log('\n--- Week 4: dFlipFlop() -- all 16 transitions ---');
/* 2 clock transitions x 2 d values x 2 prior states, plus the two steady
   states. The property that matters: q changes ONLY on 0 -> 1. */
ok(L.dFlipFlop(1,0,1,0).q===1 && L.dFlipFlop(1,0,1,0).captured, 'rising edge with d=1 captures 1');
ok(L.dFlipFlop(0,0,1,1).q===0 && L.dFlipFlop(0,0,1,1).captured, 'rising edge with d=0 captures 0');
ok(L.dFlipFlop(1,1,0,0).q===0 && !L.dFlipFlop(1,1,0,0).captured, 'FALLING edge ignores d');
ok(L.dFlipFlop(1,1,1,0).q===0 && !L.dFlipFlop(1,1,1,0).captured, 'clock steady high ignores d');
ok(L.dFlipFlop(1,0,0,0).q===0 && !L.dFlipFlop(1,0,0,0).captured, 'clock steady low ignores d');
var held = true, d2, cp, cn, q2;
for (d2=0;d2<2;d2++) for (cp=0;cp<2;cp++) for (cn=0;cn<2;cn++) for (q2=0;q2<2;q2++) {
  var r2 = L.dFlipFlop(d2,cp,cn,q2);
  var rising2 = (cp===0 && cn===1);
  if (!rising2 && r2.q !== q2) held = false;
  if (rising2 && r2.q !== d2) held = false;
}
ok(held, 'exhaustive: q takes d on a rising edge and is unchanged on every other transition');

console.log('\n--- Week 4: trace() -- the three timing-widget presets ---');
/* Expected outputs written by hand from the circuit behaviour, so a
   regression in the kernel is caught against intent rather than itself. */
var dS  = [0,1,1,0,0,1,1,0];
var enS = [0,0,1,1,0,0,1,1];
ok(L.trace('memcell', dS, enS, 0).join('') === '00100010',
   'memcell across a full window: follows d while Set is high (steps 2,6), holds it after Set drops');
ok(L.trace('memcell', [0,1,1,0], [0,1,0,0], 0).join('') === '0111',
   'memcell: captures 1 when Set goes high at step 1, then HOLDS through d falling');
ok(L.trace('dflipflop', [0,1,1,0], [0,1,0,0], 0).join('') === '0111',
   'flip-flop: captures 1 on the rising edge at step 1, then holds');
ok(L.trace('dflipflop', [0,1,0,1], [0,0,0,1], 0).join('') === '0001',
   'flip-flop: ignores d entirely between edges, captures at the one rising edge');
ok(L.trace('memcell', [0,1,0,1], [1,1,1,1], 0).join('') === '0101',
   'memcell with Set held high FOLLOWS d -- this is transparency, and it is the point of Week 4 4.5');
ok(L.trace('srlatch', [0,1,0,1], null, 0).join('') === '0101',
   'raw S-R latch tracks d continuously -- it has no way to be told "not yet"');

console.log('\n--- Week 4: the machine does not use a flip-flop in its datapath ---');
ok(typeof L.memCell === 'function' && typeof L.dFlipFlop === 'function',
   'both are exported: memCell is what the datapath uses, dFlipFlop is taught not built');


/* ============================================================
   WEEK 5A — word-width storage and bus primitives
   ============================================================ */

function W(str) { return str.split('').map(Number); }
function S(bits) { return bits === null ? 'float' : bits.join(''); }

console.log('\n--- Week 5: memWord() -- eight cells, one set line ---');
ok(S(L.memWord(W('10101010'), 1, W('00000000')).q) === '10101010',
   'set high: the whole byte is captured');
ok(S(L.memWord(W('11111111'), 0, W('10101010')).q) === '10101010',
   'set low: the stored byte is held and the input is ignored');
ok(S(L.memWord(W('00000000'), 1, W('11111111')).q) === '00000000',
   'set high with all zeros: zeros are a value like any other');

/* Exhaustive at width 3: 8 input patterns x 2 set values x 8 prior
   states. Cheap, and it covers the whole state space of the shared
   control line, which is the thing the circuit exists to have. */
(function () {
  var good = true, i, s, p;
  for (i = 0; i < 8; i++) for (s = 0; s < 2; s++) for (p = 0; p < 8; p++) {
    var inB = L.intToWord(i, 3), pr = L.intToWord(p, 3);
    var got = L.memWord(inB, s, pr).q.join('');
    var want = (s === 1 ? inB : pr).join('');
    if (got !== want) { good = false; }
  }
  ok(good, 'exhaustive at width 3: q follows i when s = 1 and holds otherwise, all 128 cases');
})();

console.log('\n--- Week 5: enableWord() -- three output stages ---');
ok(S(L.enableWord(W('10101010'), 1, 'and').bits) === '10101010', 'AND mode, e = 1: passes the byte');
ok(S(L.enableWord(W('10101010'), 0, 'and').bits) === '00000000', 'AND mode, e = 0: asserts eight zeros');
ok(L.enableWord(W('10101010'), 0, 'and').driving === true,
   'AND mode is ALWAYS driving -- which is exactly why it cannot share a wire');

ok(L.enableWord(W('10101010'), 1, 'buffer').driving === true, 'buffer mode, e = 1: driving');
ok(L.enableWord(W('10101010'), 0, 'buffer').driving === false, 'buffer mode, e = 0: NOT driving');
ok(L.enableWord(W('10101010'), 0, 'buffer').bits === null,
   'buffer mode, e = 0: there is no value, not a value of zero');

/* Section 5.3b's paper analysis, asserted rather than claimed in prose:
   adding the AND stage in front of the buffers changes nothing an
   observer downstream can detect.

   What this test does NOT model, deliberately: students build all nine
   buffers because Logisim Classic 2.7.1 is unstable with eight (Dave,
   2026-09-14). That is a property of the simulator, not of the
   electronics, and a kernel that reproduced it would be teaching the
   quirk as if it were the circuit. */
(function () {
  var same = true, i, e;
  for (i = 0; i < 256; i++) for (e = 0; e < 2; e++) {
    var w = L.intToWord(i, 8);
    var b = L.enableWord(w, e, 'buffer'), t = L.enableWord(w, e, 'both');
    if (b.driving !== t.driving || S(b.bits) !== S(t.bits)) { same = false; }
  }
  ok(same, "exhaustive: 'buffer' and 'both' are indistinguishable -- the AND stage never determines the output");
})();

console.log('\n--- Week 5: busResolve() -- and the contract that must not be relaxed ---');
ok(L.busResolve([]).state === 'float', 'nothing connected: the bus floats');
ok(L.busResolve([{ bits: W('11001100'), driving: false }]).state === 'float',
   'one device present but not driving: still floats');
ok(L.busResolve([{ bits: W('11001100'), driving: true },
                 { bits: W('00000000'), driving: false }]).state === 'driven',
   'exactly one driver: the bus carries that byte');
ok(S(L.busResolve([{ bits: W('11001100'), driving: true }]).bits) === '11001100',
   'and it carries the right byte');

ok(L.busResolve([{ bits: W('11001100'), driving: true },
                 { bits: W('00110011'), driving: true }]).state === 'conflict',
   'TWO drivers disagreeing: conflict');

/* The assertion most likely to be "fixed" by someone later, and the one
   that must not be. Two output stages wired together is a hardware fault
   whether or not they currently want the same answer; reporting agreement
   as success would teach that bus discipline is about agreeing rather
   than about being the only one talking. */
ok(L.busResolve([{ bits: W('11001100'), driving: true },
                 { bits: W('11001100'), driving: true }]).state === 'conflict',
   'two drivers AGREEING: still conflict -- this assertion is load-bearing, do not relax it');

ok(L.busResolve([{ bits: W('11001100'), driving: true },
                 { bits: W('11001100'), driving: true }]).bits === undefined,
   'a conflicted bus carries no byte at all -- the caller cannot accidentally display one');

console.log('\n--- Week 5: register8() -- the five-step verification from the spec ---');
(function () {
  var q = W('00000000'), r;

  r = L.register8(q, { i: W('00000000'), s: 0, e: 0 });
  ok(r.driving === false && r.o === null, 'step 1: s = 0, e = 0 -- o is floating');
  ok(r.reg.length === 8, 'step 1: reg is readable anyway -- that is what it is for');

  q = r.q;
  r = L.register8(q, { i: W('11001100'), s: 1, e: 0 });
  ok(S(r.reg) === '11001100', 'step 2: raising s writes the byte, and reg shows it');
  ok(r.o === null, 'step 2: o is STILL floating -- writing and speaking are different acts');
  q = r.q;

  r = L.register8(q, { i: W('00000000'), s: 0, e: 0 });
  ok(S(r.reg) === '11001100', 'step 3: s low, input changed -- the stored byte does not move');
  q = r.q;

  r = L.register8(q, { i: W('00000000'), s: 0, e: 1 });
  ok(S(r.o) === '11001100' && r.driving === true, 'step 4: raising e puts the stored byte on the bus');
  ok(S(r.reg) === '11001100', 'step 4: reg is unchanged by reading');
  q = r.q;

  r = L.register8(q, { i: W('00000000'), s: 0, e: 0 });
  ok(r.o === null && S(r.reg) === '11001100', 'step 5: dropping e stops the driving; the byte stays stored');
})();

/* The bus scenario the whole of section 5.3 is built on. */
console.log('\n--- Week 5: two registers, one bus ---');
(function () {
  var r1 = L.register8(W('10101010'), { i: W('10101010'), s: 0, e: 1 });
  var r2 = L.register8(W('01010101'), { i: W('00000000'), s: 0, e: 0 });
  ok(L.busResolve([r1, r2]).state === 'driven', 'one enabled, one silent: the bus is clean');
  ok(S(L.busResolve([r1, r2]).bits) === '10101010', 'and it carries R1');

  var r2on = L.register8(W('01010101'), { i: W('00000000'), s: 0, e: 1 });
  ok(L.busResolve([r1, r2on]).state === 'conflict', 'both enabled: conflict, and neither register wins');

  var r1and = L.register8(W('10101010'), { i: W('10101010'), s: 0, e: 1, mode: 'and' });
  var r2and = L.register8(W('01010101'), { i: W('00000000'), s: 0, e: 0, mode: 'and' });
  ok(L.busResolve([r1and, r2and]).state === 'conflict',
     "AND-only output stages: even the SILENT register is driving, so the bus is contested. This is the argument of 5.3.");
})();

/* ============================================================
   WEEK 5B — CSCLogic.mips
   ============================================================ */

var M = L.mips;

function enc(text, wantBits, label) {
  var r = M.encode(text);
  if (!r.ok) { fail++; console.log('FAIL ' + label + '  -> ' + r.error); return; }
  var got = r.bits;
  if (got === wantBits.replace(/\s+/g, '')) { pass++; console.log('ok   ' + label); }
  else { fail++; console.log('FAIL ' + label + '\n       got  ' + got + '\n       want ' + wantBits.replace(/\s+/g, '')); }
}
function dec(bits, wantText, label) {
  var r = M.decode(bits);
  if (!r.ok) { fail++; console.log('FAIL ' + label + '  -> ' + r.error); return; }
  if (r.text === wantText) { pass++; console.log('ok   ' + label); }
  else { fail++; console.log('FAIL ' + label + '  got "' + r.text + '" want "' + wantText + '"'); }
}

console.log('\n--- Week 5: the register file ---');
ok(M.regs.length === 32, 'thirty-two registers');
ok(M.regByName('$zero').n === 0 && M.regByName('$ra').n === 31, '$zero is 0 and $ra is 31');
ok(M.regByName('$t0').n === 8 && M.regByName('$s0').n === 16, '$t0 is 8 and $s0 is 16');
ok(M.regByName('$t8').n === 24, '$t8 is 24 -- NOT 18, which is the predictable wrong answer');
ok(M.regByName('$8') === M.regByName('$t0'), '$8 and $t0 are the same register');
ok(M.regByName('t0') === null && M.regByName('$zz') === null, 'bad register names are rejected, not guessed');

console.log('\n--- Week 5: encoding (expected bits written out by hand) ---');
/* Every expectation below was derived from the field tables by hand, so a
   regression is caught against intent rather than against the encoder
   agreeing with itself. */
enc('add $s1, $t2, $t3', '000000 01010 01011 10001 00000 100000', 'add $s1, $t2, $t3   (self-check B.1)');
enc('sub $s0, $t8, $t9', '000000 11000 11001 10000 00000 100010', 'sub $s0, $t8, $t9   (Assignment C.1)');
enc('and $t0, $t1, $t2', '000000 01001 01010 01000 00000 100100', 'and $t0, $t1, $t2');
enc('or  $t0, $t1, $t2', '000000 01001 01010 01000 00000 100101', 'or  $t0, $t1, $t2');
enc('xor $t0, $t1, $t2', '000000 01001 01010 01000 00000 100110', 'xor $t0, $t1, $t2');
enc('slt $t0, $t1, $t2', '000000 01001 01010 01000 00000 101010', 'slt $t0, $t1, $t2');

enc('addi $t0, $s3, 256', '001000 10011 01000 0000000100000000', 'addi $t0, $s3, 256   (self-check B.2)');
enc('addi $v0, $a1, -50', '001000 00101 00010 1111111111001110', 'addi $v0, $a1, -50   (Assignment C.3, NEGATIVE)');
enc('lw $t1, 64($sp)',    '100011 11101 01001 0000000001000000', 'lw $t1, 64($sp)      (Assignment C.2)');
enc('sw $t0, 16($sp)',    '101011 11101 01000 0000000000010000', 'sw $t0, 16($sp)');
enc('andi $t0, $s3, 256', '001100 10011 01000 0000000100000000', 'andi $t0, $s3, 256');
enc('ori  $t0, $s3, 256', '001101 10011 01000 0000000100000000', 'ori  $t0, $s3, 256');
enc('beq $t0, $t1, 4',    '000100 01000 01001 0000000000000100', 'beq $t0, $t1, 4');
enc('bne $t0, $t1, -4',   '000101 01000 01001 1111111111111100', 'bne $t0, $t1, -4');
enc('j 8192',             '000010 00000000000010000000000000',   'j 8192               (Assignment C.4)');
enc('jal 262148',         '000011 00000001000000000000000100',   'jal 262148');

console.log('\n--- Week 5: the negative immediate, checked as a value ---');
(function () {
  var r = M.encode('addi $v0, $a1, -50');
  var immField = r.fields[3];
  ok(immField.name === 'immediate' && immField.bits.length === 16, 'the immediate field is 16 bits wide');
  ok(M.fromBinSigned(immField.bits) === -50, '-50 round-trips as 16-bit two’s complement');
  ok(M.fromBin(immField.bits) === 65486, 'and read as UNSIGNED the same bits are 65486 -- the Week 1 point, in a new place');
})();

console.log('\n--- Week 5: decoding (Assignment Part C and self-check B) ---');
dec('000000 01001 01010 11000 00000 100101', 'or $t8, $t1, $t2',  'C.5  R-type -> or $t8, $t1, $t2');
dec('101011 11101 01000 0000000000010000', 'sw $t0, 16($sp)',     'C.6  I-type -> sw $t0, 16($sp)');
/* The legacy version of this problem reads
     000011 000001000000000000000100
   which is 30 bits, not 32 -- the address field was written 24 digits
   wide instead of 26. Padded to width it decodes as jal 262148, which is
   plainly what was intended. Assignment 5 ships the corrected 32-bit
   form; see the spec's Deliverable 9. */
dec('000011 00000001000000000000000100', 'jal 262148',             'C.7  J-type -> jal 262148  (legacy form was 30 bits)');
ok(M.decode('000011000001000000000000000100').ok === false,
   'and the uncorrected 30-bit legacy string is REJECTED rather than silently padded');
dec('000000 10001 10010 01000 00000 100010', 'sub $t0, $s1, $s2', 'B.3  R-type -> sub $t0, $s1, $s2');

console.log('\n--- Week 5: decode reads the OPCODE first, then splits ---');
ok(M.decode('00000001001010101100000000100101').format === 'R', 'opcode 000000 means R-type, and funct decides which');
ok(M.decode('10001111101010010000000001000000').format === 'I', 'a non-zero, non-jump opcode means I-type');
ok(M.decode('00001000000000000010000000000000').format === 'J', 'opcode 000010 means J-type');

console.log('\n--- Week 5: round-trip across the whole Week 5 subset ---');
/* encode(decode(x)) === x catches a whole class of field-offset bugs at
   once -- a boundary that is wrong in both directions agrees with itself
   on every individual test above and fails here. */
(function () {
  var cases = [
    'add $s1, $t2, $t3', 'sub $s0, $t8, $t9', 'and $t0, $t1, $t2',
    'or $t0, $t1, $t2', 'xor $t0, $t1, $t2', 'slt $t0, $t1, $t2',
    'addi $t0, $s3, 256', 'addi $v0, $a1, -50', 'andi $t0, $s3, 256',
    'ori $t0, $s3, 256', 'lw $t1, 64($sp)', 'sw $t0, 16($sp)',
    'beq $t0, $t1, 4', 'bne $t0, $t1, -4', 'j 8192', 'jal 262148',
    'sll $t0, $t1, 4', 'srl $t0, $t1, 4', 'jr $ra'
  ];
  var bad = [];
  cases.forEach(function (src) {
    var e1 = M.encode(src);
    if (!e1.ok) { bad.push(src + ' (encode: ' + e1.error + ')'); return; }
    var d = M.decode(e1.bits);
    if (!d.ok) { bad.push(src + ' (decode: ' + d.error + ')'); return; }
    var e2 = M.encode(d.text);
    if (!e2.ok || e2.bits !== e1.bits) { bad.push(src + ' -> ' + d.text); }
  });
  ok(bad.length === 0, 'encode(decode(x)) === x for all ' + cases.length + ' instructions' +
     (bad.length ? '  [' + bad.join('; ') + ']' : ''));
})();

console.log('\n--- Week 5: field widths always sum to 32 ---');
(function () {
  var good = true, srcs = ['add $t0, $t1, $t2', 'addi $t0, $t1, 5', 'lw $t0, 4($t1)', 'j 100', 'sll $t0, $t1, 2', 'jr $ra'];
  srcs.forEach(function (s) {
    var r = M.encode(s), total = 0;
    if (!r.ok) { good = false; return; }
    r.fields.forEach(function (f) { total += f.width; if (f.bits.length !== f.width) { good = false; } });
    if (total !== 32 || r.bits.length !== 32) { good = false; }
  });
  ok(good, 'every field is as wide as it says, and every instruction is exactly 32 bits');
})();

console.log('\n--- Week 5: sign-extension vs zero-extension are distinguished (Standards 2) ---');
(function () {
  var addi = null, andi = null, ori = null, i;
  for (i = 0; i < M.i.length; i++) {
    if (M.i[i].m === 'addi') { addi = M.i[i]; }
    if (M.i[i].m === 'andi') { andi = M.i[i]; }
    if (M.i[i].m === 'ori')  { ori  = M.i[i]; }
  }
  ok(addi.sext === true,  'addi SIGN-extends its immediate');
  ok(andi.sext === false, 'andi ZERO-extends its immediate');
  ok(ori.sext === false,  'ori ZERO-extends its immediate');
  ok(/SIGN-extended/.test(addi.desc) && /ZERO-extended/.test(andi.desc),
     'and the reference table says so in words -- the pair is labelled wherever both appear');
})();

console.log('\n--- Week 5: the instruction subset boundary is data, not prose ---');
(function () {
  var w5 = M.r.concat(M.i, M.j).filter(function (o) { return o.week === 5; });
  var later = M.r.concat(M.i, M.j).filter(function (o) { return o.week > 5; });
  ok(w5.length === 15, 'fifteen instructions in the Week 5 subset');
  ok(later.map(function (o) { return o.m; }).sort().join(',') === 'jr,sll,srl',
     'sll, srl and jr are in the tables but marked for later weeks -- a signpost, not an omission');
})();

console.log('\n--- Week 5: errors are reported, never guessed ---');
ok(M.encode('frobnicate $t0, $t1, $t2').ok === false, 'an unknown mnemonic fails');
ok(M.encode('add $t0, $t1').ok === false, 'a missing operand fails');
ok(M.encode('add $t0, $t1, $zz').ok === false, 'a bad register name fails');
ok(M.encode('addi $t0, $t1, 99999').ok === false, 'an immediate that does not fit in 16 bits fails');
ok(M.decode('0101').ok === false, 'fewer than 32 bits fails');
ok(M.decode('11111111111111111111111111111111').ok === false, 'an opcode not in the table fails rather than inventing one');

console.log('\n============================');
console.log('PASS '+pass+'   FAIL '+fail);
process.exit(fail?1:0);
