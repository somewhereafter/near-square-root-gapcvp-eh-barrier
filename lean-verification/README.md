# Lean verification boundary

This directory begins the machine-checking work requested by Version 2 of the
paper. It intentionally distinguishes what is verified from what remains the
central conditional assumption.

## Verified here

- `ParameterLedger.lean` checks the exact rational identity in Equation (9.10)
  and the algebraic rearrangement used in Corollary 5.3.
- `ScalarCommonAtom.lean` proves the `1 x 1` scalar specialization of the
  rectangular common-atom statement from Mira's already-formalized scalar
  Frobenius-Hankel theorem.

## Not yet verified

The matrix-valued rectangular common-atom lemma in Theorem 7.1 is not proved
here. In particular, the protected finite-window realization step that must
produce one common atom set for every matrix entry remains the critical gap.
The complexity-class implications in Part I also depend on cited published
theorems and are audited at the citation level rather than re-proved inside
Lean.

## Build

```powershell
lake update
lake exe cache get
lake build
```

The dependency is pinned to Mira's audited formalization commit
`44a92a158bff7e95cbc2ac11c5717c18cb83d535`.

The repository's `Lean verification` GitHub workflow performs this build on a
remote runner so verification does not consume the author's desktop memory.
