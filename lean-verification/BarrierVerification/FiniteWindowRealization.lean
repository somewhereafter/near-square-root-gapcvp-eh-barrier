import BarrierVerification.MatrixPairingQuotient

namespace BarrierVerification

open Set

/-- The protected rectangular block-Hankel matrix of matrix moments. -/
def rectangularBlockHankel
    {K : Type*} {m : ℕ}
    (moment : ℕ → Matrix (Fin m) (Fin m) K) (k L : ℕ) :
    Matrix (Fin k × Fin m) (Fin (L + 1) × Fin m) K :=
  fun ai bj => moment (ai.1.1 + bj.1.1) ai.2 bj.2

/-- One block column, acting on its `m` scalar coefficients. -/
def momentBlockColumn
    {K : Type*} [Field K] {m : ℕ}
    (moment : ℕ → Matrix (Fin m) (Fin m) K) (k b : ℕ) :
    (Fin m → K) →ₗ[K] (Fin k × Fin m → K) :=
  LinearMap.pi fun ai =>
    (LinearMap.proj ai.2).comp (moment (ai.1.1 + b)).mulVecLin

@[simp]
theorem momentBlockColumn_apply
    {K : Type*} [Field K] {m : ℕ}
    (moment : ℕ → Matrix (Fin m) (Fin m) K)
    (k b : ℕ) (x : Fin m → K) (a : Fin k) (i : Fin m) :
    momentBlockColumn moment k b x (a, i) =
      (moment (a.1 + b)).mulVec x i :=
  rfl

/-- Moment-vector sequence produced by a finite linear relation among block
columns. -/
def relationMoment
    {K : Type*} [Field K] {m h : ℕ}
    (moment : ℕ → Matrix (Fin m) (Fin m) K)
    (x : Fin (h + 1) → (Fin m → K)) (j : ℕ) : Fin m → K :=
  ∑ b : Fin (h + 1), (moment (b.1 + j)).mulVec (x b)

/-- A shifted window of `relationMoment` is the corresponding sum of shifted
block columns. -/
theorem relationMoment_window_eq
    {K : Type*} [Field K] {m h : ℕ}
    (moment : ℕ → Matrix (Fin m) (Fin m) K)
    (x : Fin (h + 1) → (Fin m → K)) (k s : ℕ) :
    (fun ai : Fin k × Fin m => relationMoment moment x (s + ai.1.1) ai.2) =
      ∑ b, momentBlockColumn moment k (b.1 + s) (x b) := by
  funext ai
  simp only [relationMoment, Finset.sum_apply, momentBlockColumn_apply]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [show b.1 + (s + ai.1.1) = ai.1.1 + (b.1 + s) by omega]

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

/-- Synthesis of an arbitrary linear combination of the first `h + 1`
block columns. -/
def blockSynthesis
    {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (G : ℕ → X →ₗ[K] Y) (h : ℕ) :
    (Fin (h + 1) → X) →ₗ[K] Y :=
  ∑ b : Fin (h + 1), (G b.1).comp (LinearMap.proj b)

@[simp]
theorem blockSynthesis_apply
    {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (G : ℕ → X →ₗ[K] Y) (h : ℕ) (x : Fin (h + 1) → X) :
    blockSynthesis (K := K) G h x = ∑ b, G b.1 (x b) := by
  simp [blockSynthesis]

/-- The explicit synthesis map has exactly the abstract block-column span as
its range. -/
theorem range_blockSynthesis
    {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (G : ℕ → X →ₗ[K] Y) (h : ℕ) :
    LinearMap.range (blockSynthesis (K := K) G h) =
      blockColumnSpan (K := K) G h := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [blockSynthesis_apply (K := K)]
    apply Submodule.sum_mem
    intro b _hb
    apply Submodule.subset_span
    exact ⟨b.1, by omega, ⟨x b, rfl⟩⟩
  · apply Submodule.span_le.2
    intro y hy
    obtain ⟨b, hb, x, rfl⟩ := hy
    let ib : Fin (h + 1) := ⟨b, by omega⟩
    refine ⟨Pi.single ib x, ?_⟩
    rw [blockSynthesis_apply (K := K)]
    rw [Fintype.sum_eq_single ib]
    simp [ib]

/-- Flattening the coefficient blocks turns block synthesis into ordinary
matrix-vector multiplication by the rectangular block-Hankel matrix. -/
theorem blockSynthesis_comp_curry_eq_mulVecLin
    {K : Type*} [Field K] {m : ℕ}
    (moment : ℕ → Matrix (Fin m) (Fin m) K) (k h : ℕ) :
    (blockSynthesis (K := K) (momentBlockColumn moment k) h).comp
        (LinearEquiv.curry K K (Fin (h + 1)) (Fin m)).toLinearMap =
      (rectangularBlockHankel moment k h).mulVecLin := by
  apply LinearMap.ext
  intro x
  funext ai
  simp [blockSynthesis_apply, rectangularBlockHankel, Matrix.mulVec,
    Fintype.sum_prod_type, add_comm]

/-- The abstract column-span dimension is exactly the matrix rank appearing
in the paper statement. -/
theorem rectangularBlockHankel_rank_eq_finrank_span
    {K : Type*} [Field K] {m : ℕ}
    (moment : ℕ → Matrix (Fin m) (Fin m) K) (k h : ℕ) :
    (rectangularBlockHankel moment k h).rank =
      Module.finrank K
        (blockColumnSpan (K := K) (momentBlockColumn moment k) h) := by
  rw [Matrix.rank, ← blockSynthesis_comp_curry_eq_mulVecLin]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  rw [range_blockSynthesis (K := K)]

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
    LinearIndependent K (reverseWindowFamily (K := K) q k n) := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
      have hnle : n ≤ k := by omega
      have hli : LinearIndependent K
          (reverseWindowFamily (K := K) q k n) := ih hnle
      let pivotRow : Fin k := ⟨k - (n + 1), by omega⟩
      let newest : Fin k → V := fun a => q (n + 1 + a.1)
      let evaluate : (Fin k → V) →ₗ[K] V := LinearMap.proj pivotRow
      have htail_zero (i : Fin n) :
          evaluate (reverseWindowFamily (K := K) q k n i) = 0 := by
        change q (n - i.1 + (k - (n + 1))) = 0
        apply hqzero
        omega
      have hspan_le :
          Submodule.span K
              (range (reverseWindowFamily (K := K) q k n)) ≤
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
          newest ∉ Submodule.span K
            (range (reverseWindowFamily (K := K) q k n)) := by
        intro hmem
        have hzero : evaluate newest = 0 :=
          LinearMap.mem_ker.1 (hspan_le hmem)
        apply hqk
        rw [hnewest_eval] at hzero
        exact hzero
      have hcons : LinearIndependent K
          (Fin.cons newest (reverseWindowFamily (K := K) q k n) :
            Fin (n + 1) → (Fin k → V)) :=
        hli.finCons hnewest_not_mem
      have hfamily :
          reverseWindowFamily (K := K) q k (n + 1) =
            (Fin.cons newest (reverseWindowFamily (K := K) q k n) :
              Fin (n + 1) → (Fin k → V)) := by
        funext i a
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [reverseWindowFamily, newest]
        · simp [reverseWindowFamily, newest]
      rw [hfamily]
      exact hcons

/-- Uncurried form of `reverseWindowFamily`, matching the row type of the
rectangular block-Hankel matrix. -/
def reverseFlatWindowFamily
    {K : Type*} [Field K] {m : ℕ}
    (q : ℕ → (Fin m → K)) (k n : ℕ) :
    Fin n → (Fin k × Fin m → K) :=
  fun i a => q (n - i.1 + a.1.1) a.2

/-- The delayed-pivot lemma in an uncurried row-coordinate presentation. -/
theorem reverseFlatWindowFamily_linearIndependent
    {K : Type*} [Field K] {m : ℕ}
    (q : ℕ → (Fin m → K)) (k n : ℕ)
    (hqzero : ∀ j, j < k → q j = 0)
    (hqk : q k ≠ 0)
    (hnk : n ≤ k) :
    LinearIndependent K (reverseFlatWindowFamily (K := K) q k n) := by
  apply LinearIndependent.of_comp
    (LinearEquiv.curry K K (Fin k) (Fin m)).toLinearMap
  simpa [reverseFlatWindowFamily, reverseWindowFamily, Function.comp_def] using
    (reverseWindowFamily_linearIndependent
      (K := K) q k n hqzero hqk hnk)

/-- Any relation among the first `h + 1` block columns remains a relation
after shifting every column once, provided the protected right tail contains
`t + 1` further shifts and the entire column space has dimension at most
`t < k`. -/
theorem shifted_blockColumn_relation
    {K : Type*} [Field K] {m : ℕ}
    (moment : ℕ → Matrix (Fin m) (Fin m) K)
    (k h t L : ℕ)
    (htk : t < k)
    (hguard : h + t + 1 ≤ L)
    (hrank : Module.finrank K
      (blockColumnSpan (K := K) (momentBlockColumn moment k) L) ≤ t)
    (x : Fin (h + 1) → (Fin m → K))
    (hrel : ∑ b, momentBlockColumn moment k b.1 (x b) = 0) :
    ∑ b, momentBlockColumn moment k (b.1 + 1) (x b) = 0 := by
  classical
  let q : ℕ → (Fin m → K) := relationMoment moment x
  let W : Submodule K (Fin k × Fin m → K) :=
    blockColumnSpan (K := K) (momentBlockColumn moment k) L
  have hwindow_zero :
      (fun ai : Fin k × Fin m => q ai.1.1 ai.2) = 0 := by
    rw [show (fun ai : Fin k × Fin m => q ai.1.1 ai.2) =
        (fun ai => relationMoment moment x (0 + ai.1.1) ai.2) by
          funext ai
          simp [q]]
    rw [relationMoment_window_eq]
    simpa using hrel
  have hqzero : ∀ j, j < k → q j = 0 := by
    intro j hj
    funext i
    have h := congrFun hwindow_zero (⟨⟨j, hj⟩, i⟩)
    simpa using h
  by_contra hshift
  have hqk : q k ≠ 0 := by
    intro hqkzero
    apply hshift
    rw [← relationMoment_window_eq moment x k 1]
    funext ai
    change q (1 + ai.1.1) ai.2 = 0
    by_cases hlt : 1 + ai.1.1 < k
    · rw [hqzero _ hlt]
      rfl
    · have heq : 1 + ai.1.1 = k := by omega
      rw [heq, hqkzero]
      rfl
  have hfam_li : LinearIndependent K
      (reverseFlatWindowFamily (K := K) q k (t + 1)) :=
    reverseFlatWindowFamily_linearIndependent
      (K := K) q k (t + 1) hqzero hqk (by omega)
  have hfam_mem (i : Fin (t + 1)) :
      reverseFlatWindowFamily (K := K) q k (t + 1) i ∈ W := by
    let s := t + 1 - i.1
    have heq := relationMoment_window_eq moment x k s
    change (fun ai : Fin k × Fin m => q (s + ai.1.1) ai.2) ∈ W
    rw [show (fun ai : Fin k × Fin m => q (s + ai.1.1) ai.2) =
        (fun ai => relationMoment moment x (s + ai.1.1) ai.2) by
          funext ai
          rfl]
    rw [heq]
    apply Submodule.sum_mem
    intro b _hb
    apply Submodule.subset_span
    exact ⟨b.1 + s, by dsimp [s]; omega, ⟨x b, rfl⟩⟩
  let lifted : Fin (t + 1) → W := fun i =>
    ⟨reverseFlatWindowFamily (K := K) q k (t + 1) i, hfam_mem i⟩
  have hlifted : LinearIndependent K lifted := by
    apply LinearIndependent.of_comp W.subtype
    simpa [lifted, Function.comp_def] using hfam_li
  have hcard := hlifted.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  dsimp [W] at hcard
  omega

/-- Synthesis after shifting each displayed block column once. -/
def shiftedBlockSynthesis
    {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (G : ℕ → X →ₗ[K] Y) (h : ℕ) :
    (Fin (h + 1) → X) →ₗ[K] Y :=
  ∑ b : Fin (h + 1), (G (b.1 + 1)).comp (LinearMap.proj b)

@[simp]
theorem shiftedBlockSynthesis_apply
    {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (G : ℕ → X →ₗ[K] Y) (h : ℕ) (x : Fin (h + 1) → X) :
    shiftedBlockSynthesis (K := K) G h x =
      ∑ b, G (b.1 + 1) (x b) := by
  simp [shiftedBlockSynthesis]

/-- The protected-tail argument is exactly the kernel inclusion required to
descend the formal shift to the synthesized state space. -/
theorem ker_blockSynthesis_le_ker_shifted
    {K : Type*} [Field K] {m : ℕ}
    (moment : ℕ → Matrix (Fin m) (Fin m) K)
    (k h t L : ℕ)
    (htk : t < k)
    (hguard : h + t + 1 ≤ L)
    (hrank : Module.finrank K
      (blockColumnSpan (K := K) (momentBlockColumn moment k) L) ≤ t) :
    LinearMap.ker
        (blockSynthesis (K := K) (momentBlockColumn moment k) h) ≤
      LinearMap.ker
        (shiftedBlockSynthesis (K := K) (momentBlockColumn moment k) h) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [blockSynthesis_apply (K := K)] at hx
  rw [shiftedBlockSynthesis_apply (K := K)]
  exact shifted_blockColumn_relation moment k h t L htk hguard hrank x hx

/-- The canonical endomorphism on a realized range when a second map has no
new relations and no new output directions. -/
noncomputable def inducedShiftOnRange
    {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (phi psi : X →ₗ[K] Y)
    (hker : LinearMap.ker phi ≤ LinearMap.ker psi)
    (hrange : LinearMap.range psi ≤ LinearMap.range phi) :
    LinearMap.range phi →ₗ[K] LinearMap.range phi := by
  let psiRange : X →ₗ[K] LinearMap.range phi :=
    psi.codRestrict (LinearMap.range phi) fun x => hrange ⟨x, rfl⟩
  have hkerRange : LinearMap.ker phi ≤ LinearMap.ker psiRange := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply Subtype.ext
    change psi x = 0
    exact LinearMap.mem_ker.1 (hker (LinearMap.mem_ker.2 hx))
  exact (LinearMap.ker phi).liftQ psiRange hkerRange |>.comp
    phi.quotKerEquivRange.symm.toLinearMap

/-- `inducedShiftOnRange` sends the state represented by `x` to the state
represented by `psi x`. -/
theorem inducedShiftOnRange_apply
    {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    (phi psi : X →ₗ[K] Y)
    (hker : LinearMap.ker phi ≤ LinearMap.ker psi)
    (hrange : LinearMap.range psi ≤ LinearMap.range phi)
    (x : X) :
    inducedShiftOnRange phi psi hker hrange
        ⟨phi x, ⟨x, rfl⟩⟩ =
      ⟨psi x, hrange ⟨x, rfl⟩⟩ := by
  simp [inducedShiftOnRange, LinearMap.quotKerEquivRange_symm_apply_image]

end BarrierVerification
