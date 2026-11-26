/-
The three squares `y_j = x_j²` as roots of the cubic `t (t - 1/2)² = e(φ)`.
-/
import HolevoUtkin.Defs

open Real Set

noncomputable section

namespace HolevoUtkin

/-- `y₁ = x₀²`. -/
def Y1 (φ : ℝ) : ℝ := (1 + cos (2 * φ)) / 3
/-- `y₂ = x₁²`. -/
def Y2 (φ : ℝ) : ℝ := (2 - cos (2 * φ) + √3 * sin (2 * φ)) / 6
/-- `y₃ = x₂²`. -/
def Y3 (φ : ℝ) : ℝ := (2 - cos (2 * φ) - √3 * sin (2 * φ)) / 6
/-- `e(φ) = y₁ y₂ y₃ = (1 + cos 6φ)/108`. -/
def E (φ : ℝ) : ℝ := (1 + cos (6 * φ)) / 108

/-- The node set `{y₁, y₂, y₃}`. -/
def Ys (φ : ℝ) : Finset ℝ := {Y1 φ, Y2 φ, Y3 φ}

lemma sqrt3_sq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma cos_two_pi_div_three : cos (2 * π / 3) = -1 / 2 := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; ring

lemma sin_two_pi_div_three : sin (2 * π / 3) = √3 / 2 := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]

/-! ### The squares of the coordinates -/

lemma x_zero_sq (φ : ℝ) : x 0 φ ^ 2 = Y1 φ := by
  simp only [x, Fin.val_zero, Nat.cast_zero, mul_zero, zero_div, add_zero, mul_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 / 3 by norm_num), Real.cos_sq φ, Y1]
  ring

lemma x_one_sq (φ : ℝ) : x 1 φ ^ 2 = Y2 φ := by
  have h : cos (2 * (φ + 2 * π * 1 / 3)) = -(cos (2 * φ)) / 2 + √3 / 2 * sin (2 * φ) := by
    rw [show 2 * (φ + 2 * π * 1 / 3) = (2 * φ + π / 3) + π by ring, Real.cos_add_pi,
      Real.cos_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
    ring
  simp only [x, Fin.val_one, Nat.cast_one, mul_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 / 3 by norm_num), Real.cos_sq, h, Y2]
  ring

lemma x_two_sq (φ : ℝ) : x 2 φ ^ 2 = Y3 φ := by
  have h : cos (2 * (φ + 2 * π * 2 / 3)) = -(cos (2 * φ)) / 2 - √3 / 2 * sin (2 * φ) := by
    rw [show 2 * (φ + 2 * π * 2 / 3) = ((2 * φ - π / 3) + π) + 2 * π by ring,
      Real.cos_add_two_pi, Real.cos_add_pi, Real.cos_sub, Real.cos_pi_div_three,
      Real.sin_pi_div_three]
    ring
  have h2 : ((2 : Fin 3).val : ℝ) = 2 := by norm_num
  simp only [x, h2, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 / 3 by norm_num), Real.cos_sq, h,
    Y3]
  ring

lemma abs_rpow_two_mul (t α : ℝ) : |t| ^ (2 * α) = (t ^ 2) ^ α := by
  rw [Real.rpow_mul (abs_nonneg t), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, sq_abs]

lemma M_eq (α φ : ℝ) : M α φ = Y1 φ ^ α + Y2 φ ^ α + Y3 φ ^ α := by
  simp only [M, Fin.sum_univ_three, abs_rpow_two_mul, x_zero_sq, x_one_sq, x_two_sq]

lemma M_eq_fun (α : ℝ) : M α = fun φ => Y1 φ ^ α + Y2 φ ^ α + Y3 φ ^ α :=
  funext (M_eq α)

/-! ### Vieta relations -/

lemma vieta1 (φ : ℝ) : Y1 φ + Y2 φ + Y3 φ = 1 := by
  simp only [Y1, Y2, Y3]; ring

lemma vieta2 (φ : ℝ) : Y1 φ * Y2 φ + Y1 φ * Y3 φ + Y2 φ * Y3 φ = 1 / 4 := by
  have hs := Real.sin_sq_add_cos_sq (2 * φ)
  have hr := sqrt3_sq
  simp only [Y1, Y2, Y3]
  set c := cos (2 * φ); set s := sin (2 * φ); set r := (√3 : ℝ)
  linear_combination (-r ^ 2 / 36) * hs + (c ^ 2 / 36 - 1 / 36) * hr

lemma cos_six_mul (φ : ℝ) : cos (6 * φ) = 4 * cos (2 * φ) ^ 3 - 3 * cos (2 * φ) := by
  rw [show 6 * φ = 3 * (2 * φ) by ring, Real.cos_three_mul]

lemma sin_six_mul (φ : ℝ) : sin (6 * φ) = 3 * sin (2 * φ) - 4 * sin (2 * φ) ^ 3 := by
  rw [show 6 * φ = 3 * (2 * φ) by ring, Real.sin_three_mul]

lemma vieta3 (φ : ℝ) : Y1 φ * Y2 φ * Y3 φ = E φ := by
  have hs := Real.sin_sq_add_cos_sq (2 * φ)
  have hr := sqrt3_sq
  simp only [Y1, Y2, Y3, E, cos_six_mul]
  set c := cos (2 * φ); set s := sin (2 * φ); set r := (√3 : ℝ)
  linear_combination (-c * r ^ 2 / 108 - r ^ 2 / 108) * hs
    + (c ^ 3 / 108 + c ^ 2 / 108 - c / 108 - 1 / 108) * hr

/-- Each `y_j` is a root of `h(t) - e = t³ - t² + t/4 - e`. -/
lemma root_of_vieta {a b c e : ℝ} (h1 : a + b + c = 1) (h2 : a * b + a * c + b * c = 1 / 4)
    (h3 : a * b * c = e) : a ^ 3 - a ^ 2 + a / 4 = e := by
  linear_combination a ^ 2 * h1 - a * h2 + h3

/-- For a root `z` of `h = e` and roots `a, b, c` of `h = e'`:
`(z - a)(z - b)(z - c) = e - e'`. -/
lemma cross_prod {z a b c e e' : ℝ} (hz : z ^ 3 - z ^ 2 + z / 4 = e)
    (h1 : a + b + c = 1) (h2 : a * b + a * c + b * c = 1 / 4) (h3 : a * b * c = e') :
    (z - a) * (z - b) * (z - c) = e - e' := by
  linear_combination hz - z ^ 2 * h1 + z * h2 - h3

lemma Y1_root (φ : ℝ) : Y1 φ ^ 3 - Y1 φ ^ 2 + Y1 φ / 4 = E φ :=
  root_of_vieta (vieta1 φ) (vieta2 φ) (vieta3 φ)

lemma Y2_root (φ : ℝ) : Y2 φ ^ 3 - Y2 φ ^ 2 + Y2 φ / 4 = E φ :=
  root_of_vieta (a := Y2 φ) (b := Y1 φ) (c := Y3 φ) (by linarith [vieta1 φ])
    (by linarith [vieta2 φ]) (by rw [← vieta3 φ]; ring)

lemma Y3_root (φ : ℝ) : Y3 φ ^ 3 - Y3 φ ^ 2 + Y3 φ / 4 = E φ :=
  root_of_vieta (a := Y3 φ) (b := Y1 φ) (c := Y2 φ) (by linarith [vieta1 φ])
    (by linarith [vieta2 φ]) (by rw [← vieta3 φ]; ring)

/-! ### Derivatives -/

lemma hasDerivAt_cos2 (φ : ℝ) :
    HasDerivAt (fun φ => cos (2 * φ)) (-(2 * sin (2 * φ))) φ := by
  have := ((hasDerivAt_id φ).const_mul 2).cos
  simp only [id, mul_one] at this
  convert this using 1; ring

lemma hasDerivAt_sin2 (φ : ℝ) :
    HasDerivAt (fun φ => sin (2 * φ)) (2 * cos (2 * φ)) φ := by
  have := ((hasDerivAt_id φ).const_mul 2).sin
  simp only [id, mul_one] at this
  convert this using 1; ring

/-- `y₁' = -2 sin 2φ / 3`. -/
def dY1 (φ : ℝ) : ℝ := -2 * sin (2 * φ) / 3
/-- `y₂' = (sin 2φ + √3 cos 2φ)/3`. -/
def dY2 (φ : ℝ) : ℝ := (sin (2 * φ) + √3 * cos (2 * φ)) / 3
/-- `y₃' = (sin 2φ - √3 cos 2φ)/3`. -/
def dY3 (φ : ℝ) : ℝ := (sin (2 * φ) - √3 * cos (2 * φ)) / 3

lemma hasDerivAt_Y1 (φ : ℝ) : HasDerivAt Y1 (dY1 φ) φ := by
  have h := ((hasDerivAt_cos2 φ).const_add 1).div_const 3
  exact h.congr_deriv (by unfold dY1; ring)

lemma hasDerivAt_Y2 (φ : ℝ) : HasDerivAt Y2 (dY2 φ) φ := by
  have h := (((hasDerivAt_cos2 φ).const_sub 2).add
    ((hasDerivAt_sin2 φ).const_mul √3)).div_const 6
  exact h.congr_deriv (by unfold dY2; ring)

lemma hasDerivAt_Y3 (φ : ℝ) : HasDerivAt Y3 (dY3 φ) φ := by
  have h := (((hasDerivAt_cos2 φ).const_sub 2).sub
    ((hasDerivAt_sin2 φ).const_mul √3)).div_const 6
  exact h.congr_deriv (by unfold dY3; ring)

/-- The key identities `y_j' · ∏_{i ≠ j} (y_j - y_i) = -sin 6φ / 18`. -/
lemma key1 (φ : ℝ) : dY1 φ * ((Y1 φ - Y2 φ) * (Y1 φ - Y3 φ)) = -sin (6 * φ) / 18 := by
  have hs := Real.sin_sq_add_cos_sq (2 * φ)
  have hr := sqrt3_sq
  simp only [dY1, Y1, Y2, Y3, sin_six_mul]
  set c := cos (2 * φ); set s := sin (2 * φ); set r := (√3 : ℝ)
  linear_combination (r ^ 2 * s / 54 - 2 * s / 9) * hs + (-c ^ 2 * s / 54 + s / 54) * hr

lemma key2 (φ : ℝ) : dY2 φ * ((Y2 φ - Y1 φ) * (Y2 φ - Y3 φ)) = -sin (6 * φ) / 18 := by
  have hs := Real.sin_sq_add_cos_sq (2 * φ)
  have hr := sqrt3_sq
  simp only [dY2, Y1, Y2, Y3, sin_six_mul]
  set c := cos (2 * φ); set s := sin (2 * φ); set r := (√3 : ℝ)
  linear_combination (c * r ^ 3 / 54 - c * r / 18 + r ^ 2 * s / 54 - 2 * s / 9) * hs
    + (-c ^ 3 * r / 54 - 2 * c ^ 2 * s / 27 + c * r / 54 + s / 54) * hr

lemma key3 (φ : ℝ) : dY3 φ * ((Y3 φ - Y1 φ) * (Y3 φ - Y2 φ)) = -sin (6 * φ) / 18 := by
  have hs := Real.sin_sq_add_cos_sq (2 * φ)
  have hr := sqrt3_sq
  simp only [dY3, Y1, Y2, Y3, sin_six_mul]
  set c := cos (2 * φ); set s := sin (2 * φ); set r := (√3 : ℝ)
  linear_combination (-c * r ^ 3 / 54 + c * r / 18 + r ^ 2 * s / 54 - 2 * s / 9) * hs
    + (c ^ 3 * r / 54 - 2 * c ^ 2 * s / 27 - c * r / 54 + s / 54) * hr

/-! ### Angle forms and location of the roots -/

lemma Y2_angle (φ : ℝ) : Y2 φ = (1 + cos (2 * π / 3 - 2 * φ)) / 3 := by
  rw [Real.cos_sub, cos_two_pi_div_three, sin_two_pi_div_three, Y2]; ring

lemma Y3_angle (φ : ℝ) : Y3 φ = (1 + cos (2 * φ + 2 * π / 3)) / 3 := by
  rw [Real.cos_add, cos_two_pi_div_three, sin_two_pi_div_three, Y3]; ring

lemma cos_bounds_of_mem {a b θ : ℝ} (ha : 0 ≤ a) (hb : b ≤ π) (hθ : θ ∈ Ioo a b) :
    cos b < cos θ ∧ cos θ < cos a := by
  constructor
  · exact Real.strictAntiOn_cos ⟨by linarith [hθ.1], by linarith [hθ.2]⟩ ⟨by linarith [hθ.1, hθ.2], hb⟩ hθ.2
  · exact Real.strictAntiOn_cos ⟨ha, by linarith [hθ.1, hθ.2]⟩ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩ hθ.1

lemma cos_two_pi_div_three' : cos (2 * π / 3) = -1 / 2 := cos_two_pi_div_three

lemma roots_bounds {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) :
    0 < Y3 φ ∧ Y3 φ < 1 / 6 ∧ 1 / 6 < Y2 φ ∧ Y2 φ < 1 / 2 ∧ 1 / 2 < Y1 φ ∧ Y1 φ < 2 / 3 := by
  have hpi := Real.pi_pos
  obtain ⟨h1, h2⟩ := cos_bounds_of_mem (a := 0) (b := π / 3) (θ := 2 * φ) le_rfl (by linarith)
    ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  obtain ⟨h3, h4⟩ := cos_bounds_of_mem (a := π / 3) (b := 2 * π / 3) (θ := 2 * π / 3 - 2 * φ)
    (by linarith) (by linarith) ⟨by linarith [hφ.2], by linarith [hφ.1]⟩
  obtain ⟨h5, h6⟩ := cos_bounds_of_mem (a := 2 * π / 3) (b := π) (θ := 2 * φ + 2 * π / 3)
    (by linarith) le_rfl ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
  rw [Real.cos_zero] at h2
  rw [Real.cos_pi_div_three] at h1 h4
  rw [cos_two_pi_div_three] at h3 h6
  rw [Real.cos_pi] at h5
  rw [Y3_angle, Y2_angle, Y1]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

lemma Y1_zero : Y1 0 = 2 / 3 := by simp [Y1]; norm_num
lemma Y2_zero : Y2 0 = 1 / 6 := by simp [Y2]; norm_num
lemma Y3_zero : Y3 0 = 1 / 6 := by simp [Y3]; norm_num

lemma Y1_pi6 : Y1 (π / 6) = 1 / 2 := by
  rw [Y1, show 2 * (π / 6) = π / 3 by ring, Real.cos_pi_div_three]; norm_num
lemma Y2_pi6 : Y2 (π / 6) = 1 / 2 := by
  rw [Y2, show 2 * (π / 6) = π / 3 by ring, Real.cos_pi_div_three, Real.sin_pi_div_three]
  have := sqrt3_sq
  nlinarith
lemma Y3_pi6 : Y3 (π / 6) = 0 := by
  rw [Y3, show 2 * (π / 6) = π / 3 by ring, Real.cos_pi_div_three, Real.sin_pi_div_three]
  have := sqrt3_sq
  nlinarith

lemma continuous_Y1 : Continuous Y1 := by unfold Y1; fun_prop
lemma continuous_Y2 : Continuous Y2 := by unfold Y2; fun_prop
lemma continuous_Y3 : Continuous Y3 := by unfold Y3; fun_prop

/-! ### `e(φ)` -/

lemma E_strictAntiOn : StrictAntiOn E (Icc 0 (π / 6)) := by
  intro a ha b hb hab
  have hpi := Real.pi_pos
  have := Real.strictAntiOn_cos (a := 6 * a) (b := 6 * b)
    ⟨by linarith [ha.1], by linarith [ha.2]⟩ ⟨by linarith [hb.1], by linarith [hb.2]⟩
    (by linarith)
  simp only [E]
  linarith

lemma sin_six_pos {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) : 0 < sin (6 * φ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ.1]) (by linarith [hφ.2])

/-- On `(0, π/6)` the three roots are distinct, positive and `< 2/3`. -/
lemma Ys_card {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) : (Ys φ).card = 3 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := roots_bounds hφ
  rw [Ys, Finset.card_insert_of_notMem, Finset.card_pair]
  · exact ne_of_gt (by linarith)
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_gt (by linarith), ne_of_gt (by linarith)⟩

lemma Ys_mem {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) : ∀ z ∈ Ys φ, z ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := roots_bounds hφ
  intro z hz
  simp only [Ys, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl <;> constructor <;> linarith

end HolevoUtkin
