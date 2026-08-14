import BarrierVerification.FiniteWindowRealization
import BarrierVerification.MonogenicMatrixRealization

namespace BarrierVerification

open scoped BigOperators

/-- The complete rectangular common-atom theorem from the protected finite
block-Hankel window. -/
theorem rectangularCommonAtom_from_window
    {K : Type*} [Field K] [IsAlgClosed K] [CharP K 2]
    {m : ℕ}
    (moment : ℕ → Matrix (Fin m) (Fin m) K)
    (k L Q t : ℕ)
    (htk : t < k)
    (hguard : max Q (2 * t - 2) + 2 * t ≤ L)
    (hrank : (rectangularBlockHankel moment k L).rank = t)
    (hfrob : ∀ e, e < k → moment (2 * e) = (moment e).map (· ^ 2)) :
    ∃ u : ℕ, ∃ atoms : Fin u → K,
      ∃ coefficients : Fin u → Matrix (Fin m) (Fin m) K,
        u ≤ t ∧ Function.Injective atoms ∧
        (∀ i, coefficients i ≠ 0) ∧
        (∀ i row col, coefficients i row col = 0 ∨
          coefficients i row col = 1) ∧
        ∀ e, e ≤ Q → moment e = ∑ i,
          (atoms i ^ e) • coefficients i := by
  classical
  let C := max Q (2 * t - 2)
  have hk : 0 < k := by omega
  have hCL : C + 2 * t ≤ L := by simpa [C] using hguard
  have hrankSpanEq : Module.finrank K
      (blockColumnSpan (K := K) (momentBlockColumn moment k) L) = t := by
    rw [← rectangularBlockHankel_rank_eq_finrank_span]
    exact hrank
  have hrankSpan : Module.finrank K
      (blockColumnSpan (K := K) (momentBlockColumn moment k) L) ≤ t :=
    hrankSpanEq.le
  by_cases hzero : blockColumnSpan (K := K)
      (momentBlockColumn moment k) C = ⊥
  · refine ⟨0, Fin.elim0, Fin.elim0, Nat.zero_le _, ?_, ?_, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · intro e he
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact moment_eq_zero_of_blockColumnSpan_eq_bot moment k C e hk
        (he.trans (le_max_left Q (2 * t - 2))) hzero
  · obtain ⟨h, hC, hLt, hplateau, hfinW, hpower⟩ :=
      exists_plateau_state_shift moment k C t L htk hCL hzero hrankSpan
    let phi := blockSynthesis (K := K) (momentBlockColumn moment k) h
    let psi := shiftedBlockSynthesis (K := K) (momentBlockColumn moment k) h
    let hker : LinearMap.ker phi ≤ LinearMap.ker psi :=
      ker_blockSynthesis_le_ker_shifted moment k h t L htk (by omega) hrankSpan
    let W := LinearMap.range phi
    let shift : Module.End K W :=
      blockShiftOnPlateau (momentBlockColumn moment k) h hker hplateau
    let input : (Fin m → K) →ₗ[K] W :=
      (momentBlockColumn moment k 0).codRestrict W (by
        intro x
        refine ⟨singleBlockCoeff h 0 (Nat.zero_le h) x, ?_⟩
        exact blockSynthesis_singleBlockCoeff
          (momentBlockColumn moment k) h 0 (Nat.zero_le h) x)
    let output : W →ₗ[K] (Fin m → K) :=
      (LinearMap.pi fun i : Fin m =>
        LinearMap.proj (⟨⟨0, hk⟩, i⟩ : Fin k × Fin m)).comp W.subtype
    let lambda : Algebra.adjoin K {shift} →ₗ[K]
        Matrix (Fin m) (Fin m) K :=
      stateMatrixFunctional input output shift
    have hmoment : ∀ e, e ≤ C →
        lambda (generatedShift shift ^ e) = moment e := by
      intro e he
      ext i j
      have hstate := hpower e he (Pi.single j (1 : K))
      have hentry := congrArg (fun w => output w i) hstate
      simpa [lambda, stateMatrixFunctional, input, output, shift, W,
        phi, psi, hker, generatedShift, Matrix.mulVec_single_one] using hentry
    have hfinGenerated : Module.finrank K (Algebra.adjoin K {shift}) ≤ t :=
      (finrank_generatedShift_le shift).trans hfinW
    exact matrixCommonAtomOfGeneratedFunctional shift moment lambda htk
      (le_max_left Q (2 * t - 2)) (by dsimp [C]; omega)
      hfinGenerated hmoment hfrob

end BarrierVerification
