# Lean verification boundary

This directory targets the new matrix-valued rectangular common-atom lemma in
Theorem 7.1 of Version 2. Mira's already-formalized scalar theorem is a
dependency, not the verification target.

## Verified theorem

- `RectangularCommonAtomFromWindow.lean` proves
  `rectangularCommonAtom_from_window`, the complete rectangular common-atom
  theorem from the finite block-Hankel hypotheses.  Under
  `max Q (2*t-2) + 2*t <= L`, rank `t`, and the protected Frobenius identities,
  it produces at most `t` common atoms and nonzero coefficient matrices whose
  entries lie in `{0,1}`, recovering every requested moment through degree
  `Q`.
- `FiniteWindowRealization.lean` constructs the protected plateau state shift
  from the rectangular rank window.
- `MonogenicMatrixRealization.lean` packages that shift into the generated
  finite algebra and transfers the entrywise Frobenius law.
- `MatrixPairingQuotient.lean` removes the joint pairing radical.
- `RectangularCommonAtom.lean` proves the matrix-valued spectral theorem and
  the resulting common-atom decomposition.

## Verification status

The complete theorem and all of its supporting modules pass the repository's
remote `Lean verification` workflow.  There is no remaining unverified half of
the rectangular common-atom lemma.  The complexity-class implications in Part
I depend on cited published theorems and are audited at the citation level
rather than re-proved inside Lean.

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
