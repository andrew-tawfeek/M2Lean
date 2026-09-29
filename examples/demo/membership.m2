-- Run from the repository root; scripts/demo.sh creates build/demo first.
loadPackage("M2Lean", FileName => "m2/M2Lean.m2")

R = QQ[x,y];
I = ideal(x+y, x-y);
f = x^3 + y^3;
<< "Question: is x^3 + y^3 in the ideal (x+y, x-y)?" << endl;
<< "Macaulay2 discovers cofactors witnessing f = sum(c_i * g_i)." << endl;
D = newM2LeanDocument "membership-demo";
membershipClaim(D, "membership", f, I);
writeM2LeanDocument(D, "build/demo/membership.json");
rep = verifyWithLean D;
assert(rep =!= null);
assert((first rep#"results")#"status" == "accepted");
assert((first rep#"results")#"assurance" == "proved");
