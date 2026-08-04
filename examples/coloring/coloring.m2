-- Graph 3-colorability as a Nullstellensatz infeasibility case study.
--
-- A proper k-colouring of a graph G is the same as a common zero of the
-- "colouring ideal" (De Loera-Lee-Malkin-Margulies; Bayer): take one
-- variable x_v per vertex, encode "the colour of v is a k-th root of
-- unity" by x_v^k - 1, and "adjacent vertices differ" by the edge
-- polynomial (x_u^k - x_v^k)/(x_u - x_v).  For k = 3 the edge polynomial
-- is x_u^2 + x_u x_v + x_v^2.  Then
--
--    G is k-colourable  <=>  V(colouringIdeal(G,k)) is nonempty
--                       <=>  1 is NOT in colouringIdeal(G,k).
--
-- So a Nullstellensatz certificate 1 = sum c_i g_i is a *proof of
-- non-colourability*.  This is the infeasibility counterpart to Alon's
-- Combinatorial Nullstellensatz (which certifies colourings *exist*, and
-- is already in mathlib): here the certificate proves none exists.
--
-- Macaulay2 finds the certificate (a real Groebner computation whose
-- size grows with the graph); Lean re-checks it in the kernel and, via
-- the membership soundness theorem plus the coloring-to-common-zero
-- encoding lemma, turns it into `¬ G.Colorable 3` for the honest mathlib
-- `SimpleGraph.Colorable` predicate (M2Lean.Examples.Coloring).
--
-- We export two graphs of increasing hardness.  The certificate byte
-- counts (below) make the finding-hard / checking-easy asymmetry visible:
-- a bigger, harder graph needs a bigger witness, but every witness is
-- checked by the same direct polynomial arithmetic.
loadPackage("M2Lean", FileName => "m2/M2Lean.m2", Reload => true)

-- colouringDocument(name, n, edges, file): build the 3-colouring ideal of
-- the graph on vertices 0..n-1 with the given (0-based) edge list,
-- certify 1 in I, and write the document.
colouringDocument = (name, n, edges, file) -> (
    R := QQ[x_1..x_n];
    v := gens R;
    vertexGens := for i from 0 to n-1 list v#i^3 - 1;
    edgeGens := for e in edges list (v#(e#0))^2 + (v#(e#0))*(v#(e#1)) + (v#(e#1))^2;
    U := ideal(vertexGens | edgeGens);
    assert(U == 1);   -- discovery: the graph has no proper 3-colouring
    D := newM2LeanDocument name;
    unitIdealClaim(D, "not3col", U);
    writeM2LeanDocument(D, file);
    << "wrote " << file << "  (n=" << n << ", edges=" << #edges
       << ", gens=" << (n + #edges) << ", bytes=" << (#get file) << ")" << endl;
    )

-- The Grotzsch graph: the Mycielskian of the 5-cycle.  11 vertices,
-- 20 edges, TRIANGLE-FREE, and chromatic number 4 -- the smallest
-- triangle-free graph that is not 3-colourable.  There is no clique
-- forcing the fourth colour, so the obstruction is genuinely global:
-- the algebraic certificate earns its keep.
--   vertices 0..4  = the 5-cycle C5
--   vertices 5..9  = the Mycielski "shadow" of vertex (i-5)
--   vertex   10     = the apex, joined to every shadow
grotzsch = {
    {0,1},{1,2},{2,3},{3,4},{4,0},              -- C5
    {5,1},{5,4},{6,0},{6,2},{7,1},{7,3},         -- shadow_i ~ neighbours of i
    {8,2},{8,4},{9,3},{9,0},
    {10,5},{10,6},{10,7},{10,8},{10,9}};         -- apex ~ shadows
colouringDocument("grotzsch-not-3-colourable", 11, grotzsch,
    "examples/coloring/grotzsch.json");

-- The odd wheel W5 = C5 + hub (6 vertices, 10 edges), also not
-- 3-colourable; a smaller instance for the growth comparison.
w5 = {{0,1},{1,2},{2,3},{3,4},{4,0},{5,0},{5,1},{5,2},{5,3},{5,4}};
colouringDocument("wheel5-not-3-colourable", 6, w5,
    "examples/coloring/wheel5.json");
