# Local M2Lean demonstration

From PowerShell in the M2Lean checkout:

```powershell
.\scripts\demo.ps1
```

From the parent `Macaulay2` workspace, use `.\M2Lean\scripts\demo.ps1`.
The launcher uses Debian WSL; select another installed distribution with
`-Distribution NAME`. From Linux or a WSL terminal, use:

```sh
bash scripts/demo.sh
```

Prerequisites are `M2`, `lake` (via elan), `python3`, `rsync`, and `git`.
The repository pins the Lean version and dependencies. The first build needs
those dependencies installed or downloaded; rehearse once before presenting.
Subsequent runs reuse the native Linux build at `$HOME/m2lean-lean` (override
with `M2LEAN_BUILD_ROOT`). No service or external publication is involved.

## Presentation walkthrough

1. Open [`examples/demo/membership.m2`](../examples/demo/membership.m2).
   In `QQ[x,y]`, ask whether `x^3 + y^3` belongs to `(x+y, x-y)`.
   Macaulay2 finds cofactors and exports a certificate; `verifyWithLean D`
   invokes the Lean verifier in the same session.
2. Inspect `build/demo/membership.json` and `accepted-report.json`.
   The evidence is an explicit identity `f = sum(c_i * g_i)` that Lean can
   check without trusting Macaulay2's discovery procedure.
3. Inspect `build/demo/tampered.json` and `rejected-report.json`.
   The runner replaces the cofactors with zero polynomials. The document
   remains structurally valid, but the mathematical check must fail.
4. Open [`TacticDemo.lean`](../lean/M2Lean/Examples/TacticDemo.lean).
   Its last line proves the same membership goal with `by macaulay2`.
   The runner elaborates this file afresh, invoking live Macaulay2 and
   applying the membership soundness theorem to kernel-checked evidence.
   Successful Lean elaboration is silent; the runner then prints `DEMO PASSED`.

The runtime report's `proved` label means the checker has a soundness theorem;
the JSON report itself is not a Lean proof object. Step 4 demonstrates the
concrete kernel-checked proof. See [the trust model](trust-model.md).

All demonstration outputs go into the ignored `build/demo/` directory and
are replaced on each run. The shipped certificate fixtures are unchanged.
For a larger follow-up, verify the existing twisted-cubic certificate:

```sh
"${M2LEAN_BUILD_ROOT:-$HOME/m2lean-lean}/.lake/build/bin/m2lean-check" \
  examples/flagship/flagship.json
```
