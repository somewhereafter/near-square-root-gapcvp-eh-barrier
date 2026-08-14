# Lean verification boundary

This directory targets the new matrix-valued rectangular common-atom lemma in
Theorem 7.1 of Version 2. Mira's already-formalized scalar theorem is a
dependency, not the verification target.

## Current proof boundary

- `RectangularCommonAtom.lean` attempts the genuinely matrix-valued spectral
  half: from a finite monogenic realization with a jointly nondegenerate
  matrix-valued functional satisfying the entrywise Frobenius law, it produces
  one common atom set and nonzero coefficient matrices with entries in
  `{0,1}`.
- It also attempts to derive reducedness of the realization algebra from the
  matrix-valued Frobenius law and joint nondegeneracy.

## Not yet verified

These claims count as verified only after the remote Lean build is green. The
protected finite-window realization implication is still the critical
remaining half: the finite rectangular block-Hankel rank hypothesis and guard
columns must construct the jointly reachable/observable monogenic realization
used by the verified spectral theorem. Completing that bridge completes the
new lemma. The complexity-class implications in Part I depend on cited
published theorems and are audited at the citation level rather than re-proved
inside Lean.

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
