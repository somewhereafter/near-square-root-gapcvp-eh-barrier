import BarrierVerification.RectangularCommonAtom

namespace BarrierVerification

/-- The joint radical of a matrix-valued multiplication pairing. -/
def matrixPairingRadical
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {m n : ℕ}
    (lambda : A →ₗ[K] Matrix (Fin m) (Fin n) K) : Ideal A where
  carrier := {a | ∀ b, lambda (a * b) = 0}
  zero_mem' := by
    intro b
    simp
  add_mem' := by
    intro a b ha hb c
    rw [add_mul, map_add, ha c, hb c, add_zero]
  smul_mem' := by
    intro r a ha b
    change lambda ((r * a) * b) = 0
    simpa [mul_assoc, mul_comm, mul_left_comm] using ha (r * b)

@[simp]
theorem mem_matrixPairingRadical
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {m n : ℕ}
    (lambda : A →ₗ[K] Matrix (Fin m) (Fin n) K) (a : A) :
    a ∈ matrixPairingRadical lambda ↔ ∀ b, lambda (a * b) = 0 :=
  Iff.rfl

/-- The matrix functional induced on its joint pairing-radical quotient. -/
noncomputable def matrixQuotientFunctional
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {m n : ℕ}
    (lambda : A →ₗ[K] Matrix (Fin m) (Fin n) K) :
    (A ⧸ matrixPairingRadical lambda) →ₗ[K]
      Matrix (Fin m) (Fin n) K where
  __ := QuotientAddGroup.lift (matrixPairingRadical lambda).toAddSubgroup
    lambda.toAddMonoidHom (by
      intro a ha
      simpa using ha 1)
  map_smul' := by
    rintro r ⟨x⟩
    exact lambda.map_smul r x

@[simp]
theorem matrixQuotientFunctional_mk
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {m n : ℕ}
    (lambda : A →ₗ[K] Matrix (Fin m) (Fin n) K) (a : A) :
    matrixQuotientFunctional lambda
        (Ideal.Quotient.mk (matrixPairingRadical lambda) a) =
      lambda a :=
  rfl

/-- Quotienting by the joint radical makes the matrix multiplication pairing
nondegenerate by construction. -/
theorem matrixQuotientFunctional_jointNondegenerate
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {m n : ℕ}
    (lambda : A →ₗ[K] Matrix (Fin m) (Fin n) K) :
    ∀ a : A ⧸ matrixPairingRadical lambda,
      (∀ b, matrixQuotientFunctional lambda (a * b) = 0) → a = 0 := by
  intro a ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply (Ideal.Quotient.eq_zero_iff_mem).2
  intro b
  have h := ha (Ideal.Quotient.mk (matrixPairingRadical lambda) b)
  rw [← map_mul (Ideal.Quotient.mk (matrixPairingRadical lambda)),
    matrixQuotientFunctional_mk] at h
  exact h

/-- An entrywise square identity descends to the joint pairing quotient. -/
theorem matrixQuotientFunctional_mapSq
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {m n : ℕ}
    (lambda : A →ₗ[K] Matrix (Fin m) (Fin n) K)
    (mapSq : ∀ x row col,
      lambda (x ^ 2) row col = lambda x row col ^ 2) :
    ∀ x : A ⧸ matrixPairingRadical lambda, ∀ row col,
      matrixQuotientFunctional lambda (x ^ 2) row col =
        matrixQuotientFunctional lambda x row col ^ 2 := by
  intro x row col
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  calc
    matrixQuotientFunctional lambda
          (Ideal.Quotient.mk (matrixPairingRadical lambda) x ^ 2) row col =
        matrixQuotientFunctional lambda
          (Ideal.Quotient.mk (matrixPairingRadical lambda) (x ^ 2)) row col := by
            rw [← map_pow (Ideal.Quotient.mk (matrixPairingRadical lambda))]
    _ = lambda (x ^ 2) row col := by
          rw [matrixQuotientFunctional_mk]
    _ = lambda x row col ^ 2 := mapSq x row col
    _ = matrixQuotientFunctional lambda
          (Ideal.Quotient.mk (matrixPairingRadical lambda) x) row col ^ 2 := by
          rw [matrixQuotientFunctional_mk]

end BarrierVerification
