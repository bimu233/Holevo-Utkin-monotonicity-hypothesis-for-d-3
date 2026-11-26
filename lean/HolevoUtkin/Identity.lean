/-
Theorem 1 (the divided-difference identity) and Theorem 3 (monotonicity of `M_α`).
-/
import HolevoUtkin.Cubic
import HolevoUtkin.DividedDiff

open Real Set Polynomial

noncomputable section

namespace HolevoUtkin

/-- `G α φ = f_α[y₁, y₂, y₃]` with `f_α(t) = t^(α-1)`. -/
def G (α φ : ℝ) : ℝ := dd (powF (α - 1) 0) (Ys φ)

lemma roots_ne {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) :
    Y1 φ ≠ Y2 φ ∧ Y1 φ ≠ Y3 φ ∧ Y2 φ ≠ Y3 φ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := roots_bounds hφ
  exact ⟨ne_of_gt (by linarith), ne_of_gt (by linarith), ne_of_gt (by linarith)⟩

lemma G_eq_three {α φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) :
    G α φ = Y1 φ ^ (α - 1) / ((Y1 φ - Y2 φ) * (Y1 φ - Y3 φ))
      + Y2 φ ^ (α - 1) / ((Y2 φ - Y1 φ) * (Y2 φ - Y3 φ))
      + Y3 φ ^ (α - 1) / ((Y3 φ - Y1 φ) * (Y3 φ - Y2 φ)) := by
  obtain ⟨n12, n13, n23⟩ := roots_ne hφ
  rw [G, Ys, dd_three _ n12 n13 n23]
  simp only [powF_zero]

/-! ### Theorem 1 -/

theorem hasDerivAt_M (α : ℝ) {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) :
    HasDerivAt (M α) (-sin (6 * φ) / 18 * α * G α φ) φ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := roots_bounds hφ
  obtain ⟨n12, n13, n23⟩ := roots_ne hφ
  rw [M_eq_fun]
  have d1 := (hasDerivAt_Y1 φ).rpow_const (p := α) (Or.inl (ne_of_gt (by linarith)))
  have d2 := (hasDerivAt_Y2 φ).rpow_const (p := α) (Or.inl (ne_of_gt (by linarith)))
  have d3 := (hasDerivAt_Y3 φ).rpow_const (p := α) (Or.inl (ne_of_gt (by linarith)))
  refine ((d1.add d2).add d3).congr_deriv ?_
  have p1 : (Y1 φ - Y2 φ) * (Y1 φ - Y3 φ) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr n12) (sub_ne_zero.mpr n13)
  have p2 : (Y2 φ - Y1 φ) * (Y2 φ - Y3 φ) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr n12.symm) (sub_ne_zero.mpr n23)
  have p3 : (Y3 φ - Y1 φ) * (Y3 φ - Y2 φ) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr n13.symm) (sub_ne_zero.mpr n23.symm)
  have e1 : dY1 φ = -sin (6 * φ) / 18 / ((Y1 φ - Y2 φ) * (Y1 φ - Y3 φ)) := by
    rw [eq_div_iff p1]; exact key1 φ
  have e2 : dY2 φ = -sin (6 * φ) / 18 / ((Y2 φ - Y1 φ) * (Y2 φ - Y3 φ)) := by
    rw [eq_div_iff p2]; exact key2 φ
  have e3 : dY3 φ = -sin (6 * φ) / 18 / ((Y3 φ - Y1 φ) * (Y3 φ - Y2 φ)) := by
    rw [eq_div_iff p3]; exact key3 φ
  rw [G_eq_three hφ, e1, e2, e3]
  ring

/-- **Theorem 1.** `-M_α'(φ)/sin 6φ = (α/18) f_α[y₁, y₂, y₃]` on `(0, π/6)`. -/
theorem Φ_eq (α : ℝ) {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) : Φ α φ = α / 18 * G α φ := by
  have hs := sin_six_pos hφ
  rw [Φ, (hasDerivAt_M α hφ).deriv]
  field_simp

/-! ### Sign of `G` -/

lemma descPochhammer_two_eval (p : ℝ) : (descPochhammer ℝ 2).eval p = p * (p - 1) := by
  simp [descPochhammer_succ_right]

lemma powF_two (p t : ℝ) : powF p 2 t = p * (p - 1) * t ^ (p - 2) := by
  simp only [powF, descPochhammer_two_eval, Nat.cast_ofNat]

lemma G_pos {α φ : ℝ} (hα : 0 < (α - 1) * (α - 2)) (hφ : φ ∈ Ioo 0 (π / 6)) :
    0 < G α φ := by
  refine dd_pos 2 (powF (α - 1)) (powF_hasDerivAt_on _ 2 le_rfl) ?_ (Ys φ) (Ys_card hφ)
    (Ys_mem hφ)
  intro t ht
  rw [powF_two]
  have : (α - 1) * (α - 1 - 1) = (α - 1) * (α - 2) := by ring
  rw [this]
  exact mul_pos hα (Real.rpow_pos_of_pos ht.1 _)

lemma G_neg {α φ : ℝ} (hα : (α - 1) * (α - 2) < 0) (hφ : φ ∈ Ioo 0 (π / 6)) :
    G α φ < 0 := by
  refine dd_neg 2 (powF (α - 1)) (powF_hasDerivAt_on _ 2 le_rfl) ?_ (Ys φ) (Ys_card hφ)
    (Ys_mem hφ)
  intro t ht
  rw [powF_two]
  have : (α - 1) * (α - 1 - 1) = (α - 1) * (α - 2) := by ring
  rw [this]
  exact mul_neg_of_neg_of_pos hα (Real.rpow_pos_of_pos ht.1 _)

/-! ### Theorem 3 -/

lemma continuous_M {α : ℝ} (hα : 0 < α) : Continuous (M α) := by
  rw [M_eq_fun]
  have h : ∀ {f : ℝ → ℝ}, Continuous f → Continuous fun φ => f φ ^ α := fun hf =>
    hf.rpow_const fun _ => Or.inr hα.le
  exact ((h continuous_Y1).add (h continuous_Y2)).add (h continuous_Y3)

lemma deriv_M {α φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) :
    deriv (M α) φ = -sin (6 * φ) / 18 * α * G α φ :=
  (hasDerivAt_M α hφ).deriv

theorem M_strictAntiOn_of_two_lt {α : ℝ} (hα : 2 < α) :
    StrictAntiOn (M α) (Icc 0 (π / 6)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_M (by linarith)).continuousOn ?_
  intro φ hφ
  rw [interior_Icc] at hφ
  rw [deriv_M hφ]
  have hs := sin_six_pos hφ
  have hG := G_pos (α := α) (by nlinarith) hφ
  have : 0 < sin (6 * φ) / 18 * α * G α φ := by positivity
  linarith [show -sin (6 * φ) / 18 * α * G α φ = -(sin (6 * φ) / 18 * α * G α φ) by ring]

theorem M_strictAntiOn_of_pos_of_lt_one {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    StrictAntiOn (M α) (Icc 0 (π / 6)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_M h0).continuousOn ?_
  intro φ hφ
  rw [interior_Icc] at hφ
  rw [deriv_M hφ]
  have hs := sin_six_pos hφ
  have hG := G_pos (α := α) (by nlinarith) hφ
  have : 0 < sin (6 * φ) / 18 * α * G α φ := by positivity
  linarith [show -sin (6 * φ) / 18 * α * G α φ = -(sin (6 * φ) / 18 * α * G α φ) by ring]

theorem M_strictMonoOn_of_one_lt_of_lt_two {α : ℝ} (h1 : 1 < α) (h2 : α < 2) :
    StrictMonoOn (M α) (Icc 0 (π / 6)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_M (by linarith)).continuousOn ?_
  intro φ hφ
  rw [interior_Icc] at hφ
  rw [deriv_M hφ]
  have hs := sin_six_pos hφ
  have hG := G_neg (α := α) (by nlinarith) hφ
  have : 0 < sin (6 * φ) / 18 * α * (-G α φ) := by
    have : 0 < -G α φ := by linarith
    have : 0 < α := by linarith
    positivity
  linarith [show -sin (6 * φ) / 18 * α * G α φ = sin (6 * φ) / 18 * α * (-G α φ) by ring]

/-! ### Extreme values -/

theorem M_zero (α : ℝ) (_hα : 0 < α) :
    M α 0 = (3 : ℝ) ^ (-α) * ((2 : ℝ) ^ α + (2 : ℝ) ^ (1 - α)) := by
  rw [M_eq, Y1_zero, Y2_zero, Y3_zero]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ α := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ α := by positivity
  rw [Real.div_rpow (by norm_num) (by norm_num), Real.div_rpow (by norm_num) (by norm_num),
    Real.one_rpow, show (6 : ℝ) = 2 * 3 by norm_num, Real.mul_rpow (by norm_num) (by norm_num),
    Real.rpow_neg (by norm_num), Real.rpow_sub (by norm_num), Real.rpow_one]
  field_simp
  ring

theorem M_pi_div_six (α : ℝ) (hα : 0 < α) :
    M α (π / 6) = (2 : ℝ) ^ (1 - α) := by
  rw [M_eq, Y1_pi6, Y2_pi6, Y3_pi6, Real.zero_rpow hα.ne', Real.div_rpow (by norm_num)
    (by norm_num), Real.one_rpow, Real.rpow_sub (by norm_num), Real.rpow_one]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ α := by positivity
  field_simp
  ring

end HolevoUtkin
