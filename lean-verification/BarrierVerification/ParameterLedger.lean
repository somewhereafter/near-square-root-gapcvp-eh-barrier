import Mathlib

namespace BarrierVerification

/-- Equation (9.10) in Version 2 of the paper.

This checks the exact rational identity behind the claim that the conditional
compiler has protocol-deficit constant `5 + 3 / (nu - 1)`, independently of
the axis parameter `r`. -/
theorem protocolDeficitIdentity
    (r nu : ℚ)
    (hnu : nu - 1 ≠ 0)
    (hden : r + 3 * nu - 1 ≠ 0) :
    ((r + 3 * nu - 1) / (nu - 1)) *
        (1 - 2 * ((r - 2 * nu + 1) / (2 * (r + 3 * nu - 1)))) =
      5 + 3 / (nu - 1) := by
  field_simp [hnu, hden]
  ring

/-- The fixed-exponent AMETH ceiling is exactly the reciprocal of the
protocol-deficit exponent.  This is the algebraic rearrangement used in
Corollary 5.3; the complexity-theoretic implication itself remains a cited
paper theorem, not something Lean can derive from algebra alone. -/
theorem amethCeilingRearrangement
    (K c : ℚ)
    (hK : 0 < K)
    (hc : c < 1 / 2)
    (h : 1 ≤ K * (1 - 2 * c)) :
    1 / (1 - 2 * c) ≤ K := by
  have hpos : 0 < 1 - 2 * c := by linarith
  exact (div_le_iff₀ hpos).2 (by simpa [mul_comm] using h)

end BarrierVerification
