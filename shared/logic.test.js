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

console.log('\n============================');
console.log('PASS '+pass+'   FAIL '+fail);
process.exit(fail?1:0);
