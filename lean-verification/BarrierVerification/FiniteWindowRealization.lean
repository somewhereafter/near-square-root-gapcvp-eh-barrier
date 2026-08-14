import BarrierVerification.MatrixPairingQuotient

namespace BarrierVerification

open Set

/-- Vectors obtainable from one displayed block column up to index `h`. -/
def blockColumnSet
    {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (G : ℕ → X →ₗ[K] Y) (h : ℕ) : Set Y :=
  {y | ∃ b, b ≤ h ∧ y ∈ LinearMap.range (G b)}

/-- Span of the first `h + 1` displayed block columns. -/
def blockColumnSpan
    {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (G : ℕ → X →ₗ[K] Y) (h : ℕ) : Submodule K Y :=
  Submodule.span K (blockColumnSet (K := K) G h)

theorem blockColumnSpan_mono
    {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (G : ℕ → X →ₗ[K] Y) {h h' : ℕ} (hh' : h ≤ h') :
    blockColumnSpan (K := K) G h ≤ blockColumnSpan (K := K) G h' := by
  apply Submodule.span_mono
  intro y hy
  obtain ⟨b, hb, hy⟩ := hy
  exact ⟨b, hb.trans hh', hy⟩

/-- A nonzero monotone column-span chain of dimension at most `t` must
plateau within the next `t` inclusions. -/
theorem exists_blockColumnSpan_plateau
    {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (G : ℕ → X →ₗ[K] Y) (C t : ℕ)
    (hnonzero : blockColumnSpan (K := K) G C ≠ ⊥)
    (hrank : Module.finrank K (blockColumnSpan (K := K) G (C + t)) ≤ t) :
    ∃ h, C ≤ h ∧ h < C + t ∧
      blockColumnSpan (K := K) G h =
        blockColumnSpan (K := K) G (h + 1) := by
  classical
  by_contra hex
  have hstrict (i : ℕ) (hi : i < t) :
      blockColumnSpan (K := K) G (C + i) <
        blockColumnSpan (K := K) G (C + (i + 1)) := by
    have hle : blockColumnSpan (K := K) G (C + i) ≤
        blockColumnSpan (K := K) G (C + (i + 1)) := by
      apply blockColumnSpan_mono (K := K)
      omega
    apply lt_of_le_of_ne hle
    intro heq
    apply hex
    exact ⟨C + i, by omega, by omega, by simpa [Nat.add_assoc] using heq⟩
  have hgrowth : ∀ i, i ≤ t →
      Module.finrank K (blockColumnSpan (K := K) G C) + i ≤
        Module.finrank K (blockColumnSpan (K := K) G (C + i)) := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        have hit : i < t := by omega
        have hdim :
            Module.finrank K (blockColumnSpan (K := K) G (C + i)) <
              Module.finrank K
                (blockColumnSpan (K := K) G (C + (i + 1))) :=
          Submodule.finrank_lt_finrank_of_lt (hstrict i hit)
        have hprev := ih (by omega)
        omega
  have hpositive :
      1 ≤ Module.finrank K (blockColumnSpan (K := K) G C) :=
    Submodule.one_le_finrank_iff.2 hnonzero
  have hlarge := hgrowth t le_rfl
  have : t + 1 ≤
      Module.finrank K (blockColumnSpan (K := K) G (C + t)) := by
    omega
  omega

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
