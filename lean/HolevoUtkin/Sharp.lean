/-
Theorem 2: hypothesis (H) with the sharp constant.
-/
import HolevoUtkin.Identity

open Real Set Filter Topology Polynomial

noncomputable section

namespace HolevoUtkin

/-! ### Six nodes: `G(φ) - G(ψ) = (e(φ) - e(ψ)) · f[Y(φ) ∪ Y(ψ)]` -/

lemma prod_Ys {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) (z : ℝ) :
    ∏ w ∈ Ys φ, (z - w) = (z - Y1 φ) * (z - Y2 φ) * (z - Y3 φ) := by
  obtain ⟨n12, n13, n23⟩ := roots_ne hφ
  have h1 : Y1 φ ∉ ({Y2 φ, Y3 φ} : Finset ℝ) := by simp [n12, n13]
  rw [Ys, Finset.prod_insert h1, Finset.prod_pair n23]
  ring

lemma root_of_mem {φ z : ℝ} (hz : z ∈ Ys φ) : z ^ 3 - z ^ 2 + z / 4 = E φ := by
  simp only [Ys, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  exacts [Y1_root φ, Y2_root φ, Y3_root φ]

lemma cross_Ys {φ ψ : ℝ} (hψ : ψ ∈ Ioo 0 (π / 6)) {z : ℝ} (hz : z ∈ Ys φ) :
    ∏ w ∈ Ys ψ, (z - w) = E φ - E ψ := by
  rw [prod_Ys hψ]
  exact cross_prod (root_of_mem hz) (vieta1 ψ) (vieta2 ψ) (vieta3 ψ)

lemma Ys_disjoint {φ ψ : ℝ} (h : E φ ≠ E ψ) : Disjoint (Ys φ) (Ys ψ) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  exact h ((root_of_mem hz).symm.trans (root_of_mem hz'))

lemma G_sub {α φ ψ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) (hψ : ψ ∈ Ioo 0 (π / 6)) (hE : E φ ≠ E ψ) :
    G α φ - G α ψ = (E φ - E ψ) * dd (powF (α - 1) 0) (Ys φ ∪ Ys ψ) := by
  have hU := dd_union (powF (α - 1) 0) (Ys_disjoint hE) (c := E φ - E ψ) (d := E ψ - E φ)
    (fun z hz => cross_Ys hψ hz) (fun z hz => cross_Ys hφ hz)
  rw [hU]
  have hne : E φ - E ψ ≠ 0 := sub_ne_zero.mpr hE
  have hne' : E ψ - E φ ≠ 0 := sub_ne_zero.mpr hE.symm
  simp only [G]
  field_simp
  ring

lemma union_card {φ ψ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) (hψ : ψ ∈ Ioo 0 (π / 6))
    (hE : E φ ≠ E ψ) : (Ys φ ∪ Ys ψ).card = 5 + 1 := by
  rw [Finset.card_union_of_disjoint (Ys_disjoint hE), Ys_card hφ, Ys_card hψ]

lemma union_mem {φ ψ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) (hψ : ψ ∈ Ioo 0 (π / 6)) :
    ∀ z ∈ Ys φ ∪ Ys ψ, z ∈ Ioo (0 : ℝ) 1 := by
  intro z hz
  rcases Finset.mem_union.mp hz with h | h
  exacts [Ys_mem hφ z h, Ys_mem hψ z h]

lemma descPochhammer_five_eval (p : ℝ) :
    (descPochhammer ℝ 5).eval p = p * (p - 1) * (p - 2) * (p - 3) * (p - 4) := by
  simp [descPochhammer_succ_right]

lemma powF_five (α t : ℝ) :
    powF (α - 1) 5 t = (α - 1) * (α - 2) * ((α - 3) * (α - 4) * (α - 5)) * t ^ (α - 1 - 5) := by
  simp only [powF, descPochhammer_five_eval, Nat.cast_ofNat]
  congr 1
  ring

/-- Sign of the fifth-order divided difference. -/
lemma dd6_sign {α φ ψ : ℝ} (hα : 2 < α) (hφ : φ ∈ Ioo 0 (π / 6)) (hψ : ψ ∈ Ioo 0 (π / 6))
    (hE : E φ ≠ E ψ) :
    (0 < (α - 3) * (α - 4) * (α - 5) → 0 < dd (powF (α - 1) 0) (Ys φ ∪ Ys ψ)) ∧
    ((α - 3) * (α - 4) * (α - 5) < 0 → dd (powF (α - 1) 0) (Ys φ ∪ Ys ψ) < 0) ∧
    ((α - 3) * (α - 4) * (α - 5) = 0 → dd (powF (α - 1) 0) (Ys φ ∪ Ys ψ) = 0) := by
  have h12 : 0 < (α - 1) * (α - 2) := by nlinarith
  have hF := powF_hasDerivAt_on (α - 1) 5 (L := 0) (R := 1) le_rfl
  have hc := union_card hφ hψ hE
  have hm := union_mem hφ hψ
  refine ⟨fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
  · refine dd_pos 5 _ hF (fun t ht => ?_) _ hc hm
    rw [powF_five]
    exact mul_pos (mul_pos h12 hs) (Real.rpow_pos_of_pos ht.1 _)
  · refine dd_neg 5 _ hF (fun t ht => ?_) _ hc hm
    rw [powF_five]
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h12 hs) (Real.rpow_pos_of_pos ht.1 _)
  · refine dd_zero 5 _ hF (fun t ht => ?_) _ hc hm
    rw [powF_five, hs]
    ring

/-! ### Monotonicity of `Φ_α` -/

lemma Φ_sub {α a b : ℝ} (ha : a ∈ Ioo 0 (π / 6)) (hb : b ∈ Ioo 0 (π / 6)) (hab : a < b) :
    Φ α a - Φ α b = α / 18 * ((E a - E b) * dd (powF (α - 1) 0) (Ys a ∪ Ys b)) := by
  have hE : E b < E a := E_strictAntiOn (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb) hab
  rw [Φ_eq α ha, Φ_eq α hb, ← G_sub ha hb hE.ne']
  ring

theorem Φ_strictAntiOn {α : ℝ} (hα : 2 < α) (hs : 0 < (α - 3) * (α - 4) * (α - 5)) :
    StrictAntiOn (Φ α) (Ioo 0 (π / 6)) := by
  intro a ha b hb hab
  have hE : E b < E a := E_strictAntiOn (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb) hab
  have hd := (dd6_sign hα ha hb hE.ne').1 hs
  have h := Φ_sub (α := α) ha hb hab
  have : 0 < α / 18 * ((E a - E b) * dd (powF (α - 1) 0) (Ys a ∪ Ys b)) :=
    mul_pos (by linarith) (mul_pos (by linarith) hd)
  linarith

theorem Φ_strictMonoOn {α : ℝ} (hα : 2 < α) (hs : (α - 3) * (α - 4) * (α - 5) < 0) :
    StrictMonoOn (Φ α) (Ioo 0 (π / 6)) := by
  intro a ha b hb hab
  have hE : E b < E a := E_strictAntiOn (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb) hab
  have hd := (dd6_sign hα ha hb hE.ne').2.1 hs
  have h := Φ_sub (α := α) ha hb hab
  have : α / 18 * ((E a - E b) * dd (powF (α - 1) 0) (Ys a ∪ Ys b)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (mul_neg_of_pos_of_neg (by linarith) hd)
  linarith

theorem Φ_antitoneOn {α : ℝ} (hα : 2 < α) (hs : 0 ≤ (α - 3) * (α - 4) * (α - 5)) :
    AntitoneOn (Φ α) (Ioo 0 (π / 6)) := by
  rcases hs.lt_or_eq with hs | hs
  · exact (Φ_strictAntiOn hα hs).antitoneOn
  · intro a ha b hb hab
    rcases hab.lt_or_eq with hab | rfl
    · have hE : E b < E a :=
        E_strictAntiOn (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb) hab
      have hd := (dd6_sign hα ha hb hE.ne').2.2 hs.symm
      have h := Φ_sub (α := α) ha hb hab
      rw [hd, mul_zero, mul_zero] at h
      linarith
    · exact le_rfl

/-! ### Slopes and the limits at the endpoints -/

/-- `slope (t ↦ t^(α-1)) a b`. -/
def sl (α a b : ℝ) : ℝ := (b ^ (α - 1) - a ^ (α - 1)) / (b - a)

/-- `f_α'(x) = (α-1) x^(α-2)`. -/
def fd (α x : ℝ) : ℝ := (α - 1) * x ^ (α - 2)

lemma slope_bounds {α a b : ℝ} (hα : 2 < α) (ha : 0 ≤ a) (hab : a < b) :
    fd α a < sl α a b ∧ sl α a b < fd α b := by
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ => x ^ (α - 1)) (fd α) hab
    (Real.continuous_rpow_const (by linarith)).continuousOn
    (fun x hx => by
      have := Real.hasDerivAt_rpow_const (p := α - 1)
        (Or.inl (ne_of_gt (lt_of_le_of_lt ha hx.1)))
      rw [show α - 1 - 1 = α - 2 by ring] at this
      exact this)
  rw [sl, ← h]
  constructor
  · exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow ha hξ.1 (by linarith)) (by linarith)
  · exact mul_lt_mul_of_pos_left
      (Real.rpow_lt_rpow (by linarith [hξ.1]) hξ.2 (by linarith)) (by linarith)

lemma G_slopes {α φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) :
    G α φ = (sl α (Y2 φ) (Y1 φ) - sl α (Y3 φ) (Y2 φ)) / (Y1 φ - Y3 φ) := by
  obtain ⟨n12, n13, n23⟩ := roots_ne hφ
  have d12 : Y1 φ - Y2 φ ≠ 0 := sub_ne_zero.mpr n12
  have d13 : Y1 φ - Y3 φ ≠ 0 := sub_ne_zero.mpr n13
  have d23 : Y2 φ - Y3 φ ≠ 0 := sub_ne_zero.mpr n23
  have d21 : Y2 φ - Y1 φ ≠ 0 := sub_ne_zero.mpr n12.symm
  have d31 : Y3 φ - Y1 φ ≠ 0 := sub_ne_zero.mpr n13.symm
  have d32 : Y3 φ - Y2 φ ≠ 0 := sub_ne_zero.mpr n23.symm
  rw [G_eq_three hφ, sl, sl]
  field_simp
  ring

lemma tendsto_of_continuous {Y : ℝ → ℝ} (hY : Continuous Y) (l : Filter ℝ) (a : ℝ)
    (hl : l ≤ 𝓝 a) : Tendsto Y l (𝓝 (Y a)) :=
  (hY.tendsto a).mono_left hl

lemma one_sixth_rpow (α : ℝ) : ((1 : ℝ) / 6) ^ (α - 2) = (6 : ℝ) ^ (2 - α) := by
  rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
  congr 1; ring

lemma one_half_rpow (α : ℝ) : ((1 : ℝ) / 2) ^ (α - 2) = (2 : ℝ) ^ (2 - α) := by
  rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
  congr 1; ring

lemma Φ₀_eq {α : ℝ} :
    α / 18 * ((sl α (1 / 6) (2 / 3) - fd α (1 / 6)) / (2 / 3 - 1 / 6)) = Φ₀ α := by
  have k2 : ((1 : ℝ) / 6) ^ (α - 1) = 1 / 6 * (6 : ℝ) ^ (2 - α) := by
    rw [show α - 1 = (α - 2) + 1 by ring, Real.rpow_add_one (by norm_num), one_sixth_rpow]
    ring
  simp only [sl, fd, Φ₀]
  rw [k2, one_sixth_rpow]
  ring

lemma Φ₁_eq {α : ℝ} (hα : 2 < α) :
    α / 18 * ((fd α (1 / 2) - sl α 0 (1 / 2)) / (1 / 2 - 0)) = Φ₁ α := by
  have k2 : ((1 : ℝ) / 2) ^ (α - 1) = 1 / 2 * (2 : ℝ) ^ (2 - α) := by
    rw [show α - 1 = (α - 2) + 1 by ring, Real.rpow_add_one (by norm_num), one_half_rpow]
    ring
  have k3 : (2 : ℝ) ^ (3 - α) = (2 : ℝ) ^ (2 - α) * 2 := by
    rw [show 3 - α = (2 - α) + 1 by ring, Real.rpow_add_one (by norm_num)]
  have k0 : (0 : ℝ) ^ (α - 1) = 0 := Real.zero_rpow (by linarith)
  simp only [sl, fd, Φ₁]
  rw [k2, k0, one_half_rpow, k3]
  ring

theorem tendsto_Φ_zero {α : ℝ} (hα : 2 < α) : Tendsto (Φ α) (𝓝[>] 0) (𝓝 (Φ₀ α)) := by
  have hpi : 0 < π / 6 := by positivity
  have hev : ∀ᶠ φ in 𝓝[>] (0 : ℝ), φ ∈ Ioo 0 (π / 6) := Ioo_mem_nhdsGT hpi
  have t1 := tendsto_of_continuous continuous_Y1 (𝓝[>] 0) 0 nhdsWithin_le_nhds
  have t2 := tendsto_of_continuous continuous_Y2 (𝓝[>] 0) 0 nhdsWithin_le_nhds
  have t3 := tendsto_of_continuous continuous_Y3 (𝓝[>] 0) 0 nhdsWithin_le_nhds
  rw [Y1_zero] at t1
  rw [Y2_zero] at t2
  rw [Y3_zero] at t3
  have hf : Continuous fun x : ℝ => x ^ (α - 1) := Real.continuous_rpow_const (by linarith)
  have hfd : Continuous (fd α) := continuous_const.mul (Real.continuous_rpow_const (by linarith))
  have tA : Tendsto (fun φ => sl α (Y2 φ) (Y1 φ)) (𝓝[>] 0) (𝓝 (sl α (1 / 6) (2 / 3))) :=
    (((hf.tendsto _).comp t1).sub ((hf.tendsto _).comp t2)).div (t1.sub t2) (by norm_num)
  have tB : Tendsto (fun φ => sl α (Y3 φ) (Y2 φ)) (𝓝[>] 0) (𝓝 (fd α (1 / 6))) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ((hfd.tendsto _).comp t3)
      ((hfd.tendsto _).comp t2) ?_ ?_
    · filter_upwards [hev] with φ hφ
      obtain ⟨h1, h2, h3, -, -, -⟩ := roots_bounds hφ
      exact (slope_bounds hα h1.le (by linarith)).1.le
    · filter_upwards [hev] with φ hφ
      obtain ⟨h1, h2, h3, -, -, -⟩ := roots_bounds hφ
      exact (slope_bounds hα h1.le (by linarith)).2.le
  have tG := ((tA.sub tB).div (t1.sub t3) (by norm_num)).const_mul (α / 18)
  rw [Φ₀_eq] at tG
  refine tG.congr' ?_
  filter_upwards [hev] with φ hφ
  rw [Φ_eq α hφ, G_slopes hφ]
  rfl

theorem tendsto_Φ_pi_div_six {α : ℝ} (hα : 2 < α) :
    Tendsto (Φ α) (𝓝[<] (π / 6)) (𝓝 (Φ₁ α)) := by
  have hpi : 0 < π / 6 := by positivity
  have hev : ∀ᶠ φ in 𝓝[<] (π / 6), φ ∈ Ioo 0 (π / 6) := Ioo_mem_nhdsLT hpi
  have t1 := tendsto_of_continuous continuous_Y1 (𝓝[<] (π / 6)) (π / 6) nhdsWithin_le_nhds
  have t2 := tendsto_of_continuous continuous_Y2 (𝓝[<] (π / 6)) (π / 6) nhdsWithin_le_nhds
  have t3 := tendsto_of_continuous continuous_Y3 (𝓝[<] (π / 6)) (π / 6) nhdsWithin_le_nhds
  rw [Y1_pi6] at t1
  rw [Y2_pi6] at t2
  rw [Y3_pi6] at t3
  have hf : Continuous fun x : ℝ => x ^ (α - 1) := Real.continuous_rpow_const (by linarith)
  have hfd : Continuous (fd α) := continuous_const.mul (Real.continuous_rpow_const (by linarith))
  have tA : Tendsto (fun φ => sl α (Y2 φ) (Y1 φ)) (𝓝[<] (π / 6)) (𝓝 (fd α (1 / 2))) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ((hfd.tendsto _).comp t2)
      ((hfd.tendsto _).comp t1) ?_ ?_
    · filter_upwards [hev] with φ hφ
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := roots_bounds hφ
      exact (slope_bounds hα (by linarith) (by linarith)).1.le
    · filter_upwards [hev] with φ hφ
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := roots_bounds hφ
      exact (slope_bounds hα (by linarith) (by linarith)).2.le
  have tB : Tendsto (fun φ => sl α (Y3 φ) (Y2 φ)) (𝓝[<] (π / 6)) (𝓝 (sl α 0 (1 / 2))) :=
    (((hf.tendsto _).comp t2).sub ((hf.tendsto _).comp t3)).div (t2.sub t3) (by norm_num)
  have tG := ((tA.sub tB).div (t1.sub t3) (by norm_num)).const_mul (α / 18)
  rw [Φ₁_eq hα] at tG
  refine tG.congr' ?_
  filter_upwards [hev] with φ hφ
  rw [Φ_eq α hφ, G_slopes hφ]
  rfl

/-! ### Sharp constant -/

lemma Φ₀_pos {α : ℝ} (hα : 2 < α) : 0 < Φ₀ α := by
  rw [← Φ₀_eq]
  have := (slope_bounds hα (a := 1 / 6) (b := 2 / 3) (by norm_num) (by norm_num)).1
  have : 0 < (sl α (1 / 6) (2 / 3) - fd α (1 / 6)) / (2 / 3 - 1 / 6) :=
    div_pos (by linarith) (by norm_num)
  exact mul_pos (by linarith) this

lemma Φ₁_pos {α : ℝ} (hα : 2 < α) : 0 < Φ₁ α := by
  unfold Φ₁
  have : 0 < α * (α - 2) := by nlinarith
  positivity

theorem Csharp_pos {α : ℝ} (hα : 2 < α) : 0 < Csharp α := by
  unfold Csharp
  split_ifs
  exacts [Φ₀_pos hα, Φ₁_pos hα]

theorem isGLB_Φ {α : ℝ} (hα : 2 < α) : IsGLB (Φ α '' Ioo 0 (π / 6)) (Csharp α) := by
  have hpi : 0 < π / 6 := by positivity
  unfold Csharp
  split_ifs with hs
  · -- `Φ` increasing, infimum at `0⁺`
    have hmono := Φ_strictMonoOn hα hs
    have hlim := tendsto_Φ_zero hα
    refine ⟨?_, ?_⟩
    · rintro _ ⟨φ, hφ, rfl⟩
      refine le_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsGT hφ.1] with ψ hψ
      exact (hmono ⟨hψ.1, hψ.2.trans hφ.2⟩ hφ hψ.2).le
    · intro b hb
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsGT hpi] with ψ hψ
      exact hb ⟨ψ, hψ, rfl⟩
  · -- `Φ` decreasing (or constant), infimum at `π/6⁻`
    have hanti := Φ_antitoneOn hα (not_lt.mp hs)
    have hlim := tendsto_Φ_pi_div_six hα
    refine ⟨?_, ?_⟩
    · rintro _ ⟨φ, hφ, rfl⟩
      refine le_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT hφ.2] with ψ hψ
      exact hanti hφ ⟨hφ.1.trans hψ.1, hψ.2⟩ hψ.1.le
    · intro b hb
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT hpi] with ψ hψ
      exact hb ⟨ψ, hψ, rfl⟩

/-- **Hypothesis (H)** of Holevo–Utkin. -/
theorem hypothesis_H {α : ℝ} (hα : 2 < α) :
    ∃ C > 0, ∀ φ ∈ Ioo 0 (π / 6), C ≤ Φ α φ :=
  ⟨Csharp α, Csharp_pos hα, fun φ hφ => (isGLB_Φ hα).1 ⟨φ, hφ, rfl⟩⟩

/-! ### The constant cases `α = 3, 4, 5` -/

lemma G_eq_pow {α φ : ℝ} (n : ℕ) (hn : α - 1 = n) (hφ : φ ∈ Ioo 0 (π / 6)) :
    G α φ = Y1 φ ^ n / ((Y1 φ - Y2 φ) * (Y1 φ - Y3 φ))
      + Y2 φ ^ n / ((Y2 φ - Y1 φ) * (Y2 φ - Y3 φ))
      + Y3 φ ^ n / ((Y3 φ - Y1 φ) * (Y3 φ - Y2 φ)) := by
  rw [G_eq_three hφ, hn, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]

theorem Φ_three {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) : Φ 3 φ = 1 / 6 := by
  obtain ⟨n12, n13, n23⟩ := roots_ne hφ
  have d12 := sub_ne_zero.mpr n12; have d13 := sub_ne_zero.mpr n13
  have d23 := sub_ne_zero.mpr n23
  have h : G 3 φ = 1 := by
    rw [G_eq_pow 2 (by norm_num) hφ]
    have d21 : Y2 φ - Y1 φ ≠ 0 := sub_ne_zero.mpr n12.symm
    have d31 : Y3 φ - Y1 φ ≠ 0 := sub_ne_zero.mpr n13.symm
    have d32 : Y3 φ - Y2 φ ≠ 0 := sub_ne_zero.mpr n23.symm
    field_simp
    ring
  rw [Φ_eq 3 hφ, h]; norm_num

theorem Φ_four {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) : Φ 4 φ = 2 / 9 := by
  obtain ⟨n12, n13, n23⟩ := roots_ne hφ
  have d12 := sub_ne_zero.mpr n12; have d13 := sub_ne_zero.mpr n13
  have d23 := sub_ne_zero.mpr n23
  have h : G 4 φ = Y1 φ + Y2 φ + Y3 φ := by
    rw [G_eq_pow 3 (by norm_num) hφ]
    have d21 : Y2 φ - Y1 φ ≠ 0 := sub_ne_zero.mpr n12.symm
    have d31 : Y3 φ - Y1 φ ≠ 0 := sub_ne_zero.mpr n13.symm
    have d32 : Y3 φ - Y2 φ ≠ 0 := sub_ne_zero.mpr n23.symm
    field_simp
    ring
  rw [Φ_eq 4 hφ, h, vieta1]; norm_num

theorem Φ_five {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 6)) : Φ 5 φ = 5 / 24 := by
  obtain ⟨n12, n13, n23⟩ := roots_ne hφ
  have d12 := sub_ne_zero.mpr n12; have d13 := sub_ne_zero.mpr n13
  have d23 := sub_ne_zero.mpr n23
  have h : G 5 φ = (Y1 φ + Y2 φ + Y3 φ) ^ 2
      - (Y1 φ * Y2 φ + Y1 φ * Y3 φ + Y2 φ * Y3 φ) := by
    rw [G_eq_pow 4 (by norm_num) hφ]
    have d21 : Y2 φ - Y1 φ ≠ 0 := sub_ne_zero.mpr n12.symm
    have d31 : Y3 φ - Y1 φ ≠ 0 := sub_ne_zero.mpr n13.symm
    have d32 : Y3 φ - Y2 φ ≠ 0 := sub_ne_zero.mpr n23.symm
    field_simp
    ring
  rw [Φ_eq 5 hφ, h, vieta1, vieta2]; norm_num

end HolevoUtkin
