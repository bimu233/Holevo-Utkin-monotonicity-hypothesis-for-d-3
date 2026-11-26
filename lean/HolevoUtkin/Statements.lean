/-
Main statements of the note `../../paper/holevo_utkin_d3.pdf`
("A proof of the Holevo–Utkin monotonicity hypothesis in dimension three").

This file only *restates* the results, using the definitions in `HolevoUtkin/Defs.lean`
(`x`, `M`, `Φ`, `Φ₀`, `Φ₁`, `Csharp`); every proof is a reference to the development in
`DividedDiff.lean`, `Cubic.lean`, `Identity.lean` and `Sharp.lean`.
-/
import HolevoUtkin.Sharp

open Real Set Filter Topology

namespace HolevoUtkin.Main

open HolevoUtkin

/-! ### Theorem 2 of the paper (monotonicity of `M_α` for every exponent) -/

theorem M_strictAntiOn_of_two_lt {α : ℝ} (hα : 2 < α) :
    StrictAntiOn (M α) (Icc 0 (π / 6)) :=
  HolevoUtkin.M_strictAntiOn_of_two_lt hα

theorem M_strictMonoOn_of_one_lt_of_lt_two {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    StrictMonoOn (M α) (Icc 0 (π / 6)) :=
  HolevoUtkin.M_strictMonoOn_of_one_lt_of_lt_two h1 h2

theorem M_strictAntiOn_of_pos_of_lt_one {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    StrictAntiOn (M α) (Icc 0 (π / 6)) :=
  HolevoUtkin.M_strictAntiOn_of_pos_of_lt_one h0 h1

/-- Extreme values (`φ = 0` and `φ = π/6`). -/
theorem M_zero (α : ℝ) (hα : 0 < α) :
    M α 0 = (3 : ℝ) ^ (-α) * ((2 : ℝ) ^ α + (2 : ℝ) ^ (1 - α)) :=
  HolevoUtkin.M_zero α hα

theorem M_pi_div_six (α : ℝ) (hα : 0 < α) :
    M α (π / 6) = (2 : ℝ) ^ (1 - α) :=
  HolevoUtkin.M_pi_div_six α hα

/-! ### Theorem 1 of the paper (the identity), for `M_α` -/

theorem Φ_eq_divided_difference (α : ℝ) {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) :
    Φ α φ = α / 18 * dd (fun t => t ^ (α - 1)) {x 0 φ ^ 2, x 1 φ ^ 2, x 2 φ ^ 2} := by
  rw [HolevoUtkin.Φ_eq α hφ, G, x_zero_sq, x_one_sq, x_two_sq, Ys]
  congr 2
  funext t
  exact powF_zero _ _

/-! ### Theorem 3 of the paper (hypothesis (H) of Holevo–Utkin, with the sharp constant) -/

/-- Hypothesis (H): `-M_α'(φ)/sin 6φ ≥ C(α) > 0` on `(0, π/6)` for every `α > 2`. -/
theorem hypothesis_H {α : ℝ} (hα : 2 < α) :
    ∃ C > 0, ∀ φ ∈ Ioo 0 (π / 6), C ≤ Φ α φ :=
  HolevoUtkin.hypothesis_H hα

/-- Limits of `Φ_α` at the two endpoints. -/
theorem tendsto_Φ_zero {α : ℝ} (hα : 2 < α) :
    Tendsto (Φ α) (𝓝[>] 0) (𝓝 (Φ₀ α)) :=
  HolevoUtkin.tendsto_Φ_zero hα

theorem tendsto_Φ_pi_div_six {α : ℝ} (hα : 2 < α) :
    Tendsto (Φ α) (𝓝[<] (π / 6)) (𝓝 (Φ₁ α)) :=
  HolevoUtkin.tendsto_Φ_pi_div_six hα

/-- Direction of monotonicity of `Φ_α` on `(0, π/6)`. -/
theorem Φ_strictMonoOn {α : ℝ} (hα : 2 < α) (hs : (α - 3) * (α - 4) * (α - 5) < 0) :
    StrictMonoOn (Φ α) (Ioo 0 (π / 6)) :=
  HolevoUtkin.Φ_strictMonoOn hα hs

theorem Φ_strictAntiOn {α : ℝ} (hα : 2 < α) (hs : 0 < (α - 3) * (α - 4) * (α - 5)) :
    StrictAntiOn (Φ α) (Ioo 0 (π / 6)) :=
  HolevoUtkin.Φ_strictAntiOn hα hs

/-- The constant cases `α = 3, 4, 5`. -/
theorem Φ_three {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) : Φ 3 φ = 1 / 6 := HolevoUtkin.Φ_three hφ
theorem Φ_four  {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) : Φ 4 φ = 2 / 9 := HolevoUtkin.Φ_four hφ
theorem Φ_five  {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) : Φ 5 φ = 5 / 24 := HolevoUtkin.Φ_five hφ

/-- Sharpness: `Csharp α` is exactly the infimum of `Φ_α` over `(0, π/6)`. -/
theorem isGLB_Φ {α : ℝ} (hα : 2 < α) :
    IsGLB (Φ α '' Ioo 0 (π / 6)) (Csharp α) :=
  HolevoUtkin.isGLB_Φ hα

theorem Csharp_pos {α : ℝ} (hα : 2 < α) : 0 < Csharp α := HolevoUtkin.Csharp_pos hα

end HolevoUtkin.Main

/-! ### Axiom check: only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. -/
#print axioms HolevoUtkin.Main.hypothesis_H
#print axioms HolevoUtkin.Main.isGLB_Φ
#print axioms HolevoUtkin.Main.Φ_eq_divided_difference
#print axioms HolevoUtkin.Main.M_strictAntiOn_of_two_lt
#print axioms HolevoUtkin.Main.M_strictMonoOn_of_one_lt_of_lt_two
#print axioms HolevoUtkin.Main.M_strictAntiOn_of_pos_of_lt_one
#print axioms HolevoUtkin.Main.tendsto_Φ_zero
#print axioms HolevoUtkin.Main.tendsto_Φ_pi_div_six
#print axioms HolevoUtkin.Main.Φ_five
