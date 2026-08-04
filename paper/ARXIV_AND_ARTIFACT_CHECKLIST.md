# M2Lean release, artifact, and arXiv status ledger

Audited after the public v0.2.0 artifact release on 2026-08-03
(America/Los_Angeles). This file distinguishes completed repository and
archive work from the remaining author-controlled and upstream actions.

Status labels:

- `[x]` **Complete** — implemented and evidenced in the tree or by the test
  history named below.
- `[ ]` **Local pending** — can be completed without changing an external
  service.
- `[ ]` **External** — requires a public service or upstream/community action.
- `[ ]` **Human gate** — requires the author's decision, identity check, or
  review of a hosted preview.
- `[ ]` **Research-deferred** — intentionally outside the 0.2.0 artifact.

## Current released state

- Public repository: <https://github.com/andrew-tawfeek/M2Lean>.
- Preserved pre-edit paper: annotated tag
  `paper-pre-arxiv-tightening-2026-08-03` at `54dc80f`.
- Artifact release: [`v0.2.0`](https://github.com/andrew-tawfeek/M2Lean/releases/tag/v0.2.0).
- Evaluated commit: `49f18427957e3a7960971d43c14ea4ce6991e472`.
- Annotated tag object: `b14fe2261b9eca1a816b9590ee6edda3d091feb2`.
- Root tree: `8354556bb3be6e767b97774ca17f501efd6fbefd`.
- Final tag CI: [run 30874626074](https://github.com/andrew-tawfeek/M2Lean/actions/runs/30874626074),
  including the normal release gate, no-cache clean-room build, benchmark
  capture, validation, and artifact upload.
- Software Heritage snapshot:
  `swh:1:snp:3287142ae38071a07632f96b5887f3284112e764`; annotated release:
  `swh:1:rel:b14fe2261b9eca1a816b9590ee6edda3d091feb2`.
- The qualified [Software Heritage permalink](https://archive.softwareheritage.org/swh:1:dir:8354556bb3be6e767b97774ca17f501efd6fbefd;origin=https://github.com/andrew-tawfeek/M2Lean;visit=swh:1:snp:3287142ae38071a07632f96b5887f3284112e764;anchor=swh:1:rel:b14fe2261b9eca1a816b9590ee6edda3d091feb2)
  resolves through the snapshot, annotated release, commit, and root tree.
- `reproducibility/manifest.json` retains `null` for `releaseCommit`,
  `archive`, and `paperBenchmarkRecord` by design; the external release record
  supplies the post-tag identity without introducing self-reference.
- Official arXiv upload and submission: **not performed**.

## Artifact release gates

- [x] **Complete — public access.** The repository, release page, tag, and all
  four release assets were fetched without authentication. Downloaded asset
  bytes and SHA-256 digests matched the local release evidence.
- [x] **Complete — immutable release identity.** The annotated `v0.2.0` tag
  selects commit `49f18427957e3a7960971d43c14ea4ce6991e472`, tag object
  `b14fe2261b9eca1a816b9590ee6edda3d091feb2`, and root tree
  `8354556bb3be6e767b97774ca17f501efd6fbefd`.
- [x] **Complete — permanent source archive.** Software Heritage captured the
  exact annotated release and source tree. Ordinary Git ingestion does not
  preserve GitHub release assets; the external release record instead binds
  the benchmark, deterministic source archive, and checksum file to the tag.
- [x] **Complete — citation, release, and licensing files.** Evidence:
  `CITATION.cff`, `CHANGELOG.md`, `docs/releases/v0.2.0.md`, `LICENSE`,
  `LICENSES.md`, and `paper/LICENSE.md`. `CITATION.cff` passed the CFF 1.2
  schema validator. Post-release metadata records the exact commit, release,
  and Software Heritage identifiers; no DOI or arXiv identifier is claimed.
- [x] **Complete — reproducibility manifest and generated-file ledger.**
  `reproducibility/manifest.json` records Debian/container digests,
  Macaulay2 1.24.11, Lean 4.32.0, Lake, the exact mathlib commit, commands,
  expected outcomes, and generated artifact hashes;
  `scripts/check-generated.py` cross-checks the complete discovered set, JSON
  manifest, standard-tool ledger, and raw file digests without requiring Git;
  `sha256sum -c reproducibility/generated.sha256` also passed for all 15
  listed JSON/Data.lean artifacts.
- [x] **Complete — recorded-environment byte-replay pipeline implemented.** Evidence:
  `.github/workflows/ci.yml`, `scripts/regenerate-all.sh`,
  `scripts/check-generated.sh`, `scripts/schema-check.py`,
  `scripts/test-all.sh`, and `scripts/audit.sh`. The order is shipped-artifact
  verification, verifier build, regeneration of all 11 JSON documents and all
  four `*Data.lean` files, a second exact SHA-256-ledger check, schema
  prefilter, 21 integrity regressions, semantic/adversarial verification,
  theorem build, then axiom audit. CI pins Debian's linux/amd64 image digest.
- [x] **Complete — integrated replay after the root-Lake migration.**
  `bash scripts/test-all.sh` completed with exit 0 and final line
  `ALL REPRODUCIBILITY CHECKS PASSED`: 15 documents passed the schema and
  verifier, 20 invalid fixtures were rejected in their expected diagnostic
  classes, the full Lean build completed, and the axiom audit passed.
- [x] **Complete — empty-cache tag gate.** The tag workflow's
  `clean-release-evidence` job passed without restored project build state;
  the extracted deterministic source archive also passed `test-all.sh`.
- [x] **Complete — paper benchmark and external identity record.** The public
  `paper-v0.2.0.json` names the exact tagged commit, records
  `git_dirty: false`, an empty status, and an empty tracked diff, and passes
  `reproducibility/benchmark.schema.json`. The schema-validated
  `m2lean-v0.2.0-release-record.json` binds it to the tag, source archive, and
  checksum file. Their SHA-256 digests are respectively
  `8663cb9be104eb702099b5b4e27785ce5b1228f759979b2db99fd88e574f04f8`
  and `dd92995ae01c5fa486ecb9201cc66a43507cff8b0da52c59fb4cb504b4ece885`.
- [x] **Complete — stale 0.1.0 and trust-language cleanup.** Current public
  documentation and Macaulay2 messages use protocol 0.2.0; remaining 0.1.0
  mentions in ADR 0005, the changelog, and release notes are intentional
  compatibility history. `docs/trust-model.md` and `docs/architecture.md`
  distinguish runtime acceptance, formalized soundness, and a
  kernel-instantiated theorem, including current GRevLex soundness.

## Protocol and verifier hardening

- [x] **Complete — canonical membership elements.** The consumer rejects a
  noncanonical `IdealMembership.element`; evidence:
  `lean/M2Lean/Protocol/Ast.lean` and
  `protocol/fixtures/invalid/noncanonical-membership-element.json`.
- [x] **Complete — identifier uniqueness.** Duplicate object IDs, duplicate
  claim IDs, and object/claim collisions are rejected. Evidence: the three
  `structure-*-id.json` fixtures and validation in `Protocol/Ast.lean`.
- [x] **Complete — provenance policy.** Required/optional field types are
  validated, exact input provenance is echoed as `inputProvenance`, and all
  values remain informational; `deterministic: false` does not downgrade an
  independently verified claim. Evidence: `protocol/SPEC.md`, ADR 0006,
  `lean/M2Lean/Verify.lean`, `lean/Main.lean`, and
  `protocol/fixtures/valid/provenance-nondeterministic.json`.
- [x] **Complete — targeted negative fixtures.** The 20 invalid documents
  cover version mismatch, duplicate/colliding IDs, rational signs and
  denominators, membership canonicality, composite characteristics, monomial
  order, provenance shape, corrupted graded homogeneity, and earlier corrupt
  evidence cases. Evidence: `protocol/fixtures/invalid/`.
- [x] **Complete — diagnostic-class assertions.** `scripts/run-checks.sh`
  distinguishes parse, structural, and verification rejection by exit code
  and output marker; it no longer accepts any nonzero exit as sufficient.
- [x] **Complete — single regeneration/test entry points.** Evidence:
  `scripts/regenerate-all.sh`, `scripts/test-all.sh`, and matching commands in
  `README.md`/`CONTRIBUTING.md`.
- [x] **Complete — stale Lake manifest prevention.** `scripts/lean-build.sh`
  copies the checked-in root manifest on every invocation and discards cached
  dependency checkouts that are corrupt, dirty, or at the wrong revision.

## Theorems, examples, and assurance scope

- [x] **Complete — Jacobian dependency ledger.** All nine membership checks
  are promoted through `checkMembership_sound` in `collision_certified`; the
  final noninjectivity proof still evaluates the supplied points directly and
  documents the membership path as parallel. Evidence:
  `lean/M2Lean/Examples/Jacobian.lean`, `README.md`, and the paper case study.
- [x] **Complete — explicit Jacobian formulations.** `Jacobian.lean` defines
  `HasPolynomialInverse`, `PolynomialJacobianConjecture`, and the rational-
  point injectivity formulation, then proves the displayed map refutes both
  dimension-three statements. Claims remain limited to the definitions over
  `ℚ` that the file actually proves.
- [x] **Complete — graph scope made exact.** Vanishing lemmas are generic over
  `Fin n`, while the kernel-instantiated graph theorem remains the concrete
  six-vertex wheel. The K4 and Grötzsch documents are reported as runtime
  checks, not graph-generic theorems. Evidence: `Coloring.lean`, `README.md`,
  and the paper.
- [x] **Complete — homological scope made exact.** Documentation states that
  complex claims establish composition zero; graded runtime checking also
  covers dimensions, twists, and homogeneity. Exactness, minimality, cokernel
  identification, and Betti tables are not claimed.
- [x] **Complete — assurance alternatives chosen.** GRevLex Gröbner and
  non-membership are `proved`; Lex and graded-complex paths remain explicitly
  `checked`. Evidence: `Certificates/Checkers.lean`, `Groebner/Sound.lean`,
  `docs/trust-model.md`, and `protocol/SPEC.md`.
- [x] **Complete — practical warning cleanup.** Deprecated calls and unused-
  argument sites identified in the earlier build were revised, and the
  post-migration integrated Lean build completed without the earlier warning
  set.
- [ ] **Research-deferred — broaden formal scope.** Future work includes a
  graph-generic certificate theorem, exactness/minimality certificate
  families, the Lex order bridge, and graded-complex soundness. These are not
  blockers for the accurately scoped 0.2.0 paper.

## Evaluation

- [x] **Complete — machine-readable benchmark harness.** `scripts/bench.sh`
  delegates to `scripts/benchmark.py`, times all five generation scripts
  (including `examples/polynomial/polynomial.m2`), checker documents, and four
  Lean theorem files, and emits JSON conforming to
  `reproducibility/benchmark.schema.json`.
- [x] **Complete — memory, phases, failures, and raw samples.** The harness
  records every command, stdout/stderr, exit/timeout status, wall time, and
  `wait4` peak RSS. Generation, complete verifier-process, and Lean
  elaboration phases are separate. Process startup, parsing, and checker
  execution within one verifier invocation remain combined and should not be
  described as separately measured.
- [x] **Complete — comparison claims scoped.** The paper discusses current
  Lean polynomial automation and the Shen--Guo--Liu--Zhi certificate work as
  feature/architecture context and makes no cross-system performance claim.
- [ ] **Research-deferred — scaling benchmark families.** Vary variable and
  generator counts, basis/S-pair size, coefficient bits, density, timeouts,
  and failures before making research-scale performance or scaling claims.

## Macaulay2 distribution

- [x] **Complete — clone and installed workflows documented and tested.**
  Evidence: `docs/macaulay2-usage.md`; direct-load smoke command
  `M2 --script m2/tests/smoke.m2`; isolated `installPackage` followed by a
  fresh `loadPackage "M2Lean"` passed on Macaulay2 1.24.11 and 1.26.06.
- [x] **Complete — package metadata, help, examples, and tests.** Version,
  date, author/contact, homepage, exports, documentation nodes, examples, and
  embedded `TEST` blocks are in `m2/M2Lean.m2`; `check "M2Lean"` and
  documentation-checked isolated installation passed.
- [x] **Complete — supported version and M2-only smoke test.** The tested
  versions are explicitly Macaulay2 1.24.11 and 1.26.06; evidence:
  `docs/macaulay2-usage.md`, `reproducibility/macaulay2-compatibility.md`,
  and `m2/tests/smoke.m2`.
- [ ] **External — Macaulay2 package review/distribution.** Submit only after
  the public repository and protocol 0.2.0 tag are stable; those prerequisites
  are now met. Upstream review and distribution are not arXiv blockers because
  installation from the archived source is documented and tested.

## Lean distribution and upstreaming

- [x] **Complete — pinned Lake dependency layout and documentation.** The
  repository root is a Lake package with `srcDir = "lean"`; `README.md` and
  `docs/lean-usage.md` give a tag/commit-pinned dependency and minimal imports.
  The public-tag clean build remains part of the release gate above.
- [ ] **External — Reservoir release.** The public `v0.2.0` tag builds cleanly.
  Revisit publication after the repository has at least two organic GitHub
  stars and satisfies the registry's remaining eligibility checks; no
  Reservoir publication is claimed now.
- [ ] **External/research-deferred — upstreaming.** Discuss `degRevLex` and
  nonduplicative Buchberger components with mathlib maintainers and the 2026
  Lean Gröbner authors; submit small independent PRs, not the whole bridge.
  This is not an artifact or arXiv blocker.

## arXiv preparation and human gates

- [x] **Complete — final local build and visual QA.** The post-release
  `paper/m2lean.pdf` and matching `paper/m2lean.bbl` build to 23 letter-sized
  pages with no TeX/BibTeX warnings, unresolved references, or overfull or
  underfull boxes. All pages were rendered with Poppler and visually inspected.
  The PDF SHA-256 is
  `bfef86da061b91c3ef465713e08d8f77e4b887e20552bb138098fc347ee39ad7`.
- [x] **Complete — clean arXiv source bundle.** The ignored local bundle
  `dist/m2lean-arxiv-source-v1.tar.gz` contains exactly `m2lean.tex`, the
  matching `m2lean.bbl`, `references.bib`, and `LICENSE.md`. A clean extraction
  builds without BibTeX or warnings, and all 23 rendered pages are pixel-identical
  to the audited repository PDF. Bundle SHA-256:
  `13128d8fbeedb26e6ca8d0282f34e92d599c12ac32b52cfb1fdfeb360e06be58`.
- [ ] **Human gate — identity and metadata.** Confirm author spelling, public
  email, ORCID (if supplied), title, abstract, PDF metadata, references, and
  hyperlinks in the arXiv preview.
- [ ] **Human gate — category and endorsement.** Choose the primary category
  (candidate: `math.AC`) and any cross-list (candidate: `cs.LO`), and arrange
  endorsement if arXiv requires it.
- [x] **Complete — license/disclosure text prepared.** `paper/LICENSE.md` and
  `LICENSES.md` state CC BY 4.0 for the paper; the manuscript contains an
  AI-assistance disclosure.
- [ ] **Human gate — select the actual arXiv license and confirm policy.** The
  author must deliberately select the matching license in arXiv and confirm
  the disclosure against the intended venue's current policy.
- [ ] **Human gate — inspect arXiv's generated preview.** Check every page,
  especially the trust-boundary figure, listings, bibliography, and appendix
  page breaks. Do not submit until the hosted rendering matches the audited
  local PDF.
- [ ] **External/post-assignment — propagate the arXiv identifier.** After
  assignment, update `README.md`, `CITATION.cff`, archive metadata,
  `paper/references.bib`, and future paper revisions.

## Remaining actions in priority order

1. Confirm the author-facing arXiv metadata: spelling, public email, optional
   ORCID, title, abstract, and any comments or journal-reference field.
2. Choose the primary category (candidate: `math.AC`), any cross-list
   (candidate: `cs.LO`), and obtain endorsement if arXiv requests it.
3. Select CC BY 4.0 in arXiv to match `paper/LICENSE.md`, and confirm that the
   disclosure text meets the policy of any later journal or conference venue.
4. Upload the prepared source bundle, inspect arXiv's generated PDF and links
   page by page, and stop before the final submission action until the preview
   matches the audited local PDF.
5. After the author deliberately submits and an identifier is assigned,
   propagate that identifier through `README.md`, `CITATION.cff`, archive
   metadata, and `paper/references.bib`.
6. Independently of arXiv, request Macaulay2 package review, revisit Reservoir
   after its eligibility threshold is met, discuss the reusable Gröbner/order
   components with mathlib maintainers, and optionally create a DOI-bearing
   Zenodo deposit through the author's account.
