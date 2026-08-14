import CVPFormalization.Algebra.ScalarAtomization

namespace BarrierVerification

open CVPFormalization.Algebra

/-- Machine-checked scalar specialization of the new paper's rectangular
common-atom assumption.

Mira's existing scalar Frobenius-Hankel theorem already proves the desired
atomization when the matrix dimensions are `1 x 1`.  Taking the atom cap to be
`t + 1` converts its strict bound into the paper's `at most t` conclusion.

This theorem deliberately does not claim the matrix-valued extension.  That
extension, including the protected finite-window realization step, remains the
load-bearing unverified statement in Theorem 7.1. -/
theorem scalarCommonAtomOfRankLtSucc
    {F Ω : Type*}
    [Field F] [Field Ω] [Algebra F Ω]
    [CharP F 2] [IsAlgClosed Ω]
    (moment : ℕ → F)
    (Q t : ℕ)
    (hwindow : 2 * (t + 1) ≤ Q)
    (hfrobenius : ∀ e < t + 1,
      moment (2 * e) = moment e ^ 2)
    (hrank : LowRank.RankLT
      (LowRank.hankel moment (t + 1) (Q + 1)) (t + 1)) :
    ∃ atomization : UnitAtomization F Ω moment Q (t + 1),
      atomization.atomCount ≤ t := by
  obtain ⟨atomization⟩ :=
    scalar_frobenius_hankel_atomization
      moment Q (t + 1) (by omega) hwindow hfrobenius hrank
  exact ⟨atomization, Nat.le_of_lt_succ atomization.atomCount_lt⟩

end BarrierVerification
