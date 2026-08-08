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

console.log('\n============================');
console.log('PASS '+pass+'   FAIL '+fail);
process.exit(fail?1:0);
