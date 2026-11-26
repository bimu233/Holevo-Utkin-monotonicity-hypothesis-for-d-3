/-
Formal statements for the note `../README.md`
("A proof of the Holevo–Utkin monotonicity hypothesis for d = 3").

Every `sorry` below is to be replaced by a proof in the companion files;
this file fixes *what* is proved, so that it can be checked against the
paper independently of the proofs.
-/
import Mathlib

open Real Set Filter Topology

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

/-! ### Theorem 3 (monotonicity of `M_α` for every exponent) -/

theorem M_strictAntiOn_of_two_lt {α : ℝ} (hα : 2 < α) :
    StrictAntiOn (M α) (Icc 0 (π / 6)) := sorry

theorem M_strictMonoOn_of_one_lt_of_lt_two {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    StrictMonoOn (M α) (Icc 0 (π / 6)) := sorry

theorem M_strictAntiOn_of_pos_of_lt_one {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    StrictAntiOn (M α) (Icc 0 (π / 6)) := sorry

/-- Extreme values (`φ = 0` and `φ = π/6`). -/
theorem M_zero (α : ℝ) (hα : 0 < α) :
    M α 0 = (3 : ℝ) ^ (-α) * ((2 : ℝ) ^ α + (2 : ℝ) ^ (1 - α)) := sorry

theorem M_pi_div_six (α : ℝ) (hα : 0 < α) :
    M α (π / 6) = (2 : ℝ) ^ (1 - α) := sorry

/-! ### Theorem 2 (hypothesis (H) of Holevo–Utkin, with the sharp constant) -/

/-- Hypothesis (H): `-M_α'(φ)/sin 6φ ≥ C(α) > 0` on `(0, π/6)` for every `α > 2`. -/
theorem hypothesis_H {α : ℝ} (hα : 2 < α) :
    ∃ C > 0, ∀ φ ∈ Ioo 0 (π / 6), C ≤ Φ α φ := sorry

/-- Limits of `Φ_α` at the two endpoints. -/
theorem tendsto_Φ_zero {α : ℝ} (hα : 2 < α) :
    Tendsto (Φ α) (𝓝[>] 0) (𝓝 (Φ₀ α)) := sorry

theorem tendsto_Φ_pi_div_six {α : ℝ} (hα : 2 < α) :
    Tendsto (Φ α) (𝓝[<] (π / 6)) (𝓝 (Φ₁ α)) := sorry

/-- Direction of monotonicity of `Φ_α` on `(0, π/6)`. -/
theorem Φ_strictMonoOn {α : ℝ} (hα : 2 < α) (hs : (α - 3) * (α - 4) * (α - 5) < 0) :
    StrictMonoOn (Φ α) (Ioo 0 (π / 6)) := sorry

theorem Φ_strictAntiOn {α : ℝ} (hα : 2 < α) (hs : 0 < (α - 3) * (α - 4) * (α - 5)) :
    StrictAntiOn (Φ α) (Ioo 0 (π / 6)) := sorry

/-- The constant cases `α = 3, 4, 5`. -/
theorem Φ_three {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) : Φ 3 φ = 1 / 6 := sorry
theorem Φ_four  {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) : Φ 4 φ = 2 / 9 := sorry
theorem Φ_five  {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) : Φ 5 φ = 5 / 24 := sorry

/-- Sharpness: `Csharp α` is exactly the infimum of `Φ_α` over `(0, π/6)`. -/
theorem isGLB_Φ {α : ℝ} (hα : 2 < α) :
    IsGLB (Φ α '' Ioo 0 (π / 6)) (Csharp α) := sorry

theorem Csharp_pos {α : ℝ} (hα : 2 < α) : 0 < Csharp α := sorry

end HolevoUtkin
