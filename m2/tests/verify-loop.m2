-- test the in-session round trip: build a document, call
-- verifyWithLean, check the parsed report comes back.
loadPackage("M2Lean", FileName => "m2/M2Lean.m2", Reload => true)

R = QQ[x,y];
I = ideal(x+y, x-y);
D = newM2LeanDocument "verify-loop";
membershipClaim(D, "mem1", x^3 + y^3, I);
rep = verifyWithLean D;
assert(rep =!= null);
assert(#(rep#"results") == 1);
assert((first rep#"results")#"status" == "accepted");
assert((first rep#"results")#"assurance" == "proved");
<< "VERIFY-LOOP TEST PASSED" << endl;
