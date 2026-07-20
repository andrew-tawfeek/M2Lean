# ADR 0004: Development encoding is canonical JSON; meaning is encoding-independent

- Status: accepted
- Date: 2026-07-20

## Decision

Version 0 uses a single JSON encoding with canonical forms strict
enough that structural equality of encodings coincides with equality
of the encoded mathematical objects (sorted terms, reduced fractions,
no zero terms, positional variables). Consumers reject non-canonical
input; nothing is silently repaired. The specification defines
semantics independently of field names so a future compact binary
encoding can represent the same abstract documents.

## Rationale

JSON is trivially producible from M2's `hashTable`/string layer and
parseable with Lean core's `Lean.Data.Json` (no extra dependency).
Canonicality pushes normalization to the producer, keeping the
trusted checker code small: equality testing becomes structural.
Decimal-string integers avoid JSON number-precision traps.

## Consequences

Certificates are verbose (acceptable at v0 scale; see risk
"certificate explosion" in README §12). Producers carry a
normalization burden — in practice free, since M2 keeps polynomials
sorted in the ring's order already.
