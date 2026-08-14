import BarrierVerification.MatrixPairingQuotient

namespace BarrierVerification

open Set

/-- Reverse-ordered shifted windows.  For `n > 0` these are the windows
starting at shifts `n, n - 1, ..., 1`.  The reverse order makes the
delayed-pivot argument an ordinary `Fin.cons` induction. -/
def reverseWindowFamily
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (q : ℕ → V) (k n : ℕ) : Fin n → (Fin k → V) :=
  fun i a => q (n - i.1 + a.1)

/-- The delayed-pivot lemma used to make the finite Hankel shift
well-defined.  If the first `k` terms vanish but `q k` does not, then any
`n ≤ k` consecutive positive-shift windows are linearly independent. -/
theorem reverseWindowFamily_linearIndependent
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (q : ℕ → V) (k n : ℕ)
    (hqzero : ∀ j, j < k → q j = 0)
    (hqk : q k ≠ 0)
    (hnk : n ≤ k) :
    LinearIndependent K (reverseWindowFamily q k n) := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
      have hnle : n ≤ k := by omega
      have hli : LinearIndependent K (reverseWindowFamily q k n) := ih hnle
      let pivotRow : Fin k := ⟨k - (n + 1), by omega⟩
      let newest : Fin k → V := fun a => q (n + 1 + a.1)
      let evaluate : (Fin k → V) →ₗ[K] V := LinearMap.proj pivotRow
      have htail_zero (i : Fin n) :
          evaluate (reverseWindowFamily q k n i) = 0 := by
        change q (n - i.1 + (k - (n + 1))) = 0
        apply hqzero
        omega
      have hspan_le :
          Submodule.span K (range (reverseWindowFamily q k n)) ≤
            LinearMap.ker evaluate := by
        apply Submodule.span_le.2
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        exact LinearMap.mem_ker.2 (htail_zero i)
      have hnewest_eval : evaluate newest = q k := by
        change q (n + 1 + (k - (n + 1))) = q k
        congr 1
        omega
      have hnewest_not_mem :
          newest ∉ Submodule.span K (range (reverseWindowFamily q k n)) := by
        intro hmem
        have hzero : evaluate newest = 0 :=
          LinearMap.mem_ker.1 (hspan_le hmem)
        apply hqk
        rw [hnewest_eval] at hzero
        exact hzero
      have hcons : LinearIndependent K
          (Fin.cons newest (reverseWindowFamily q k n) :
            Fin (n + 1) → (Fin k → V)) :=
        hli.finCons hnewest_not_mem
      have hfamily :
          reverseWindowFamily q k (n + 1) =
            (Fin.cons newest (reverseWindowFamily q k n) :
              Fin (n + 1) → (Fin k → V)) := by
        funext i a
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [reverseWindowFamily, newest]
        · simp [reverseWindowFamily, newest]
      rw [hfamily]
      exact hcons

end BarrierVerification
