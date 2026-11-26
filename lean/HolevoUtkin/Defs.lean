/-
Basic definitions for the Holevo–Utkin problem in dimension 3.
-/
import Mathlib

open Real

noncomputable section

namespace HolevoUtkin

/-- Coordinates of the unit zero-sum vector of `ℝ³` at angle `φ`:
`x_j(φ) = √(2/3) · cos(φ + 2πj/3)`, `j = 0, 1, 2`. -/
def x (j : Fin 3) (φ : ℝ) : ℝ :=
  Real.sqrt (2 / 3) * Real.cos (φ + 2 * π * (j.val : ℝ) / 3)

/-- `M_α(φ) = ∑_j |x_j(φ)|^(2α)`. -/
def M (α φ : ℝ) : ℝ :=
  ∑ j : Fin 3, |x j φ| ^ (2 * α)

/-- `Φ_α(φ) = -M_α'(φ) / sin 6φ` (meaningful for `0 < φ < π/6`). -/
def Φ (α φ : ℝ) : ℝ :=
  -deriv (M α) φ / Real.sin (6 * φ)

/-- Closed-form value of `Φ_α` at the endpoint `φ = 0`. -/
def Φ₀ (α : ℝ) : ℝ :=
  α / 9 * (2 * (2 / 3 : ℝ) ^ (α - 1) - (α - 2 / 3) * (6 : ℝ) ^ (2 - α))

/-- Closed-form value of `Φ_α` at the endpoint `φ = π/6`. -/
def Φ₁ (α : ℝ) : ℝ :=
  α * (α - 2) / 18 * (2 : ℝ) ^ (3 - α)

/-- The sharp constant of Theorem 2. -/
def Csharp (α : ℝ) : ℝ :=
  if (α - 3) * (α - 4) * (α - 5) < 0 then Φ₀ α else Φ₁ α

end HolevoUtkin
