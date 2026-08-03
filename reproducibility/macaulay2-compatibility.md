# Macaulay2 compatibility record

The primary M2Lean 0.2.0 reproducibility environment uses Macaulay2 1.24.11.
The current official Macaulay2 1.26.06 packages were tested separately on
2026-08-03 to check that the producer package remains installable and usable.

## Isolated environment

- Debian 13 (`trixie`), `linux/amd64`
- base image:
  `debian@sha256:d63a99144861e4e460196ed93d07777490cbeab53ca660c434f2a589a6c50ea3`
- official source definition:
  `https://www.macaulay2.com/Repositories/Debian/trixie/macaulay2.sources`
- source-definition SHA-256:
  `99918b31f1ca22e6135a375b44c6f0ae7ab2920926449991de4a0e74da096250`
- packages, installed through APT after signature verification:
  `macaulay2=1.26.06+ds-1~bpo13+1` and
  `macaulay2-common=1.26.06+ds-1~bpo13+1`

The downloaded package hashes matched the SHA-256 values in APT's signed
`Packages` index:

| package | SHA-256 |
|---|---|
| `macaulay2` | `3b15469f083cc70375a4de273b8bc1cbd57ee46103b4bc8f3d66f9a0fc66608e` |
| `macaulay2-common` | `fb59f5034733391632fce05ba80662cbc3268fad081772131b3b9042af1a7f42` |

The repository was mounted read-only. The tested `m2/M2Lean.m2` had SHA-256
`8bab585f8b17058f772223cc4af5c4fd07df1a8aa64d4cc304e1f509d24d1056`;
the host file, read-only mount, and writable test copy agreed.

## Checks

The following all passed:

1. direct `loadPackage` with package metadata and membership assertions;
2. `M2 --script m2/tests/smoke.m2`, ending `ALL SMOKE TESTS PASSED`;
3. `check "M2Lean"`, including check levels 0 and 1;
4. `installPackage` into an isolated prefix with documentation/example
   capture and no generated `*.errors` files; and
5. a new Macaulay2 process loading the installed package and constructing a
   membership certificate.

The isolated installation used:

```macaulay2
installPackage(
    "M2Lean",
    FileName => "m2/M2Lean.m2",
    InstallPrefix => "/tmp/m2lean-readonly",
    MakeHTML => false,
    MakeInfo => false,
    Verbose => true
)
```

One initial disposable installation attempt reported that example output
ended prematurely. The message did not recur in three clean repetitions
(from a writable copy, from the read-only repository mount, and in a combined
load/check/install process), so it is not recorded as a reproducible 1.26.06
incompatibility.
