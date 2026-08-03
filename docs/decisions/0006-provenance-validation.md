# ADR 0006: Provenance is validated metadata, not evidence

- Status: accepted
- Date: 2026-08-03

## Context

Protocol 0.2.0 requires producer identity and version fields and permits
additional provenance fields. Earlier implementation and documentation could
be read as either ignoring the entire object or treating producer
determinism as part of mathematical assurance.

## Decision

The consumer validates the provenance object's structure:

- `producer` and `producerVersion` are required strings;
- optional package, algorithm, options, and deterministic fields must have
  their specified types;
- the accepted input provenance is echoed exactly as `inputProvenance` in the
  verification report.

Provenance remains informational. No provenance value is an assumption of a
certificate checker, and `deterministic: false` does not downgrade an
otherwise independently established assurance level.

## Consequences

Malformed provenance is a structural protocol error, while honest
nondeterminism is allowed and recorded. Reproducibility tooling may compare or
display provenance, but mathematical acceptance depends only on the validated
objects, claims, evidence, and their executable or formal checks. This is a
clarification and implementation alignment within protocol 0.2.0, not a
protocol version bump.
