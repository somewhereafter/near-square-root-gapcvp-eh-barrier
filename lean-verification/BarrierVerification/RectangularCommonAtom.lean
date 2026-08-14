import CVPFormalization.Algebra.FiniteReducedSplit

namespace BarrierVerification

open scoped BigOperators
open CVPFormalization.Algebra

/-- The common spectrum produced from a matrix-valued moment functional. -/
structure MatrixCommonSpectrum
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    {m n : ℕ}
    (lambda : A →ₗ[K] Matrix (Fin m) (Fin n) K)
    (generator : A) where
  atomCount : ℕ
  atomCount_eq_finrank : atomCount = Module.finrank K A
  atoms : Fin atomCount → K
  atoms_injective : Function.Injective atoms
  coefficients : Fin atomCount → Matrix (Fin m) (Fin n) K
  coefficients_ne_zero : ∀ i, coefficients i ≠ 0
  coefficient_entry_binary : ∀ i row col,
    coefficients i row col = 0 ∨ coefficients i row col = 1
  power_eq : ∀ e,
    lambda (generator ^ e) =
      ∑ i, (atoms i ^ e) • coefficients i

/-- Iteration of the entrywise Frobenius law along powers of two. -/
private theorem mapTwoPowEntry
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {m n : ℕ}
    (lambda : A →ₗ[K] Matrix (Fin m) (Fin n) K)
    (mapSq : ∀ x row col,
      lambda (x ^ 2) row col = lambda x row col ^ 2)
    (x : A) (row : Fin m) (col : Fin n) (q : ℕ) :
    lambda (x ^ (2 ^ q)) row col =
      lambda x row col ^ (2 ^ q) := by
  induction q with
  | zero => simp
  | succ q ih =>
      calc
        lambda (x ^ (2 ^ (q + 1))) row col =
            lambda ((x ^ (2 ^ q)) ^ 2) row col := by
              simp [pow_succ, pow_mul]
        _ = lambda (x ^ (2 ^ q)) row col ^ 2 := mapSq _ row col
        _ = (lambda x row col ^ (2 ^ q)) ^ 2 := by rw [ih]
        _ = lambda x row col ^ (2 ^ (q + 1)) := by
              simp [pow_succ, pow_mul]

/-- A jointly nondegenerate matrix-valued functional satisfying entrywise
Frobenius compatibility forces the realization algebra to be reduced. -/
theorem isReducedOfMatrixMapSqOfJointNondegenerate
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {m n : ℕ}
    (lambda : A →ₗ[K] Matrix (Fin m) (Fin n) K)
    (mapSq : ∀ x row col,
      lambda (x ^ 2) row col = lambda x row col ^ 2)
    (jointNondegenerate : ∀ a,
      (∀ b, lambda (a * b) = 0) → a = 0) :
    IsReduced A := by
  constructor
  intro a ha
  apply jointNondegenerate a
  intro b
  ext row col
  have hab : IsNilpotent (a * b) :=
    (Commute.all a b).isNilpotent_mul_right ha
  obtain ⟨q, hq⟩ := hab
  have hqle : q ≤ 2 ^ q := by
    exact le_trans (by omega)
      (Nat.mul_le_pow (by decide : (2 : ℕ) ≠ 1) q)
  have habpow : (a * b) ^ (2 ^ q) = 0 :=
    pow_eq_zero_of_le hqle hq
  have hpow : (lambda (a * b) row col) ^ (2 ^ q) = 0 := by
    rw [← mapTwoPowEntry lambda mapSq (a * b) row col q,
      habpow, map_zero]
    rfl
  by_contra hne
  exact (pow_ne_zero _ hne) hpow

/-- Matrix-valued common-atom theorem after the finite-window realization has
been constructed.

This is the genuinely new spectral half of Theorem 7.1. The remaining task is
to derive the realization and its joint nondegeneracy from the protected
rectangular block-Hankel window. -/
theorem matrixCommonAtomOfRealization
    {K A : Type*} [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [Module.Finite K A]
    {m n Q t : ℕ}
    (moment : ℕ → Matrix (Fin m) (Fin n) K)
    (lambda : A →ₗ[K] Matrix (Fin m) (Fin n) K)
    (generator : A)
    (mapSq : ∀ x row col,
      lambda (x ^ 2) row col = lambda x row col ^ 2)
    (jointNondegenerate : ∀ a,
      (∀ b, lambda (a * b) = 0) → a = 0)
    (generates : Algebra.adjoin K {generator} = ⊤)
    (finrank_le : Module.finrank K A ≤ t)
    (moment_eq : ∀ e, e ≤ Q → lambda (generator ^ e) = moment e) :
    ∃ spectrum : MatrixCommonSpectrum K A lambda generator,
      spectrum.atomCount ≤ t ∧
      ∀ e, e ≤ Q →
        moment e = ∑ i,
          (spectrum.atoms i ^ e) • spectrum.coefficients i := by
  classical
  letI : IsReduced A :=
    isReducedOfMatrixMapSqOfJointNondegenerate lambda mapSq jointNondegenerate
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  let I := MaximalSpectrum A
  letI : Fintype I := Fintype.ofFinite I
  let split : A ≃ₐ[K] (I → K) := finiteReducedAlgEquivPi K A
  let count := Fintype.card I
  let indexEquiv : Fin count ≃ I := (Fintype.equivFin I).symm
  let atoms : Fin count → K := fun i => split generator (indexEquiv i)
  have hcount : count = Module.finrank K A := by
    dsimp [count]
    have h := split.toLinearEquiv.finrank_eq
    simpa using h.symm
  let coordinate (i : I) : A →ₐ[K] K :=
    (Pi.evalAlgHom K (fun _ : I => K) i).comp split.toAlgHom
  have hatoms_injective : Function.Injective atoms := by
    intro i j hij
    have hcoordinate_on_generator :
        Set.EqOn (coordinate (indexEquiv i))
          (coordinate (indexEquiv j)) {generator} := by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      simpa [coordinate, atoms] using hij
    have hcoordinate_on_adjoin :
        Set.EqOn (coordinate (indexEquiv i))
          (coordinate (indexEquiv j)) (Algebra.adjoin K {generator}) :=
      (AlgHom.eqOn_adjoin_iff).2 hcoordinate_on_generator
    have hcoordinate :
        coordinate (indexEquiv i) = coordinate (indexEquiv j) := by
      ext x
      apply hcoordinate_on_adjoin
      rw [generates]
      exact Algebra.mem_top
    by_contra hne
    have hindex_ne : indexEquiv i ≠ indexEquiv j := by
      intro h
      exact hne (indexEquiv.injective h)
    have htest := AlgHom.congr_fun hcoordinate
      (split.symm (Pi.single (indexEquiv i) 1))
    have : (1 : K) = 0 := by
      simp [coordinate, hindex_ne] at htest
    exact one_ne_zero this
  let primitiveIdempotent (i : I) : A :=
    split.symm (Pi.single i 1)
  have hidempotent (i : I) :
      primitiveIdempotent i ^ 2 = primitiveIdempotent i := by
    apply split.injective
    ext j
    by_cases hji : j = i
    · subst j
      simp [primitiveIdempotent]
    · simp [primitiveIdempotent, hji]
  have hprimitive_ne_zero (i : I) : primitiveIdempotent i ≠ 0 := by
    intro hzero
    have h := congrArg split hzero
    have hi := congrFun h i
    simp [primitiveIdempotent] at hi
  have hmul_primitive (i : I) (b : A) :
      primitiveIdempotent i * b =
        (split b i) • primitiveIdempotent i := by
    apply split.injective
    ext j
    by_cases hji : j = i
    · subst j
      simp [primitiveIdempotent, Algebra.smul_def]
    · simp [primitiveIdempotent, hji, Algebra.smul_def]
  let coefficients : Fin count → Matrix (Fin m) (Fin n) K :=
    fun i => lambda (primitiveIdempotent (indexEquiv i))
  have hcoeff_ne_zero (i : Fin count) : coefficients i ≠ 0 := by
    intro hzero
    have hzero' :
        lambda (primitiveIdempotent (indexEquiv i)) = 0 := by
      simpa [coefficients] using hzero
    apply hprimitive_ne_zero (indexEquiv i)
    apply jointNondegenerate
    intro b
    rw [hmul_primitive, map_smul, hzero', smul_zero]
  have hcoeff_binary (i : Fin count) (row : Fin m) (col : Fin n) :
      coefficients i row col = 0 ∨ coefficients i row col = 1 := by
    have hfix : coefficients i row col = coefficients i row col ^ 2 := by
      calc
        coefficients i row col =
            lambda (primitiveIdempotent (indexEquiv i) ^ 2) row col := by
              rw [hidempotent]
        _ = coefficients i row col ^ 2 := mapSq _ row col
    have hmul : coefficients i row col *
        (coefficients i row col - 1) = 0 := by
      calc
        coefficients i row col * (coefficients i row col - 1) =
            coefficients i row col ^ 2 - coefficients i row col := by ring
        _ = 0 := sub_eq_zero.mpr hfix.symm
    rcases mul_eq_zero.mp hmul with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (sub_eq_zero.mp hone)
  have hdecompose (x : A) :
      x = ∑ i : I, (split x i) • primitiveIdempotent i := by
    apply split.injective
    have hsplit_sum :
        split (∑ i : I, (split x i) • primitiveIdempotent i) =
          ∑ i : I, (split x i) • Pi.single i (1 : K) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [primitiveIdempotent, map_smul]
    rw [hsplit_sum]
    exact pi_eq_sum_univ' (split x)
  have hpower (e : ℕ) :
      lambda (generator ^ e) =
        ∑ i : I,
          (split generator i) ^ e • lambda (primitiveIdempotent i) := by
    calc
      lambda (generator ^ e) =
          lambda (∑ i : I,
            (split (generator ^ e) i) • primitiveIdempotent i) := by
              rw [← hdecompose (generator ^ e)]
      _ = ∑ i : I,
          (split (generator ^ e) i) • lambda (primitiveIdempotent i) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro i _hi
              rw [map_smul]
      _ = ∑ i : I,
          (split generator i) ^ e • lambda (primitiveIdempotent i) := by
              apply Finset.sum_congr rfl
              intro i _hi
              simp [map_pow]
  let spectrum : MatrixCommonSpectrum K A lambda generator := {
    atomCount := count
    atomCount_eq_finrank := hcount
    atoms := atoms
    atoms_injective := hatoms_injective
    coefficients := coefficients
    coefficients_ne_zero := hcoeff_ne_zero
    coefficient_entry_binary := hcoeff_binary
    power_eq := fun e => by
      calc
        lambda (generator ^ e) =
            ∑ i : I,
              (split generator i) ^ e • lambda (primitiveIdempotent i) :=
          hpower e
        _ = ∑ i : Fin count, atoms i ^ e • coefficients i := by
          symm
          exact Equiv.sum_comp indexEquiv
            (fun i : I =>
              (split generator i) ^ e • lambda (primitiveIdempotent i))
  }
  refine ⟨spectrum, ?_, ?_⟩
  · rw [spectrum.atomCount_eq_finrank]
    exact finrank_le
  · intro e he
    rw [← moment_eq e he]
    exact spectrum.power_eq e

end BarrierVerification
