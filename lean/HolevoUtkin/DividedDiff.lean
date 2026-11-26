/-
Divided differences over a finite set of nodes, Lagrange interpolation,
the generalized Rolle theorem, and the mean value theorem for divided differences.
-/
import Mathlib

open Polynomial Set

noncomputable section

namespace HolevoUtkin

/-- Divided difference of `f` at the nodes of the finite set `S`
(Lagrange form): `∑_{z ∈ S} f z / ∏_{w ∈ S, w ≠ z} (z - w)`. -/
def dd (f : ℝ → ℝ) (S : Finset ℝ) : ℝ :=
  ∑ z ∈ S, f z / ∏ w ∈ S.erase z, (z - w)

/-! ### Three nodes -/

lemma dd_three (f : ℝ → ℝ) {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    dd f {a, b, c} =
      f a / ((a - b) * (a - c)) + f b / ((b - a) * (b - c)) + f c / ((c - a) * (c - b)) := by
  have h1 : a ∉ ({b, c} : Finset ℝ) := by simp [hab, hac]
  have h2 : b ∉ ({c} : Finset ℝ) := by simp [hbc]
  have ea : ({a, b, c} : Finset ℝ).erase a = {b, c} := Finset.erase_insert h1
  have eb : ({a, b, c} : Finset ℝ).erase b = {a, c} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, h | h | h⟩
      · exact Or.inl h
      · exact absurd h hx
      · exact Or.inr h
    · rintro (h | h)
      · exact ⟨h ▸ hab, Or.inl h⟩
      · exact ⟨h ▸ hbc.symm, Or.inr (Or.inr h)⟩
  have ec : ({a, b, c} : Finset ℝ).erase c = {a, b} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, h | h | h⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hx
    · rintro (h | h)
      · exact ⟨h ▸ hac, Or.inl h⟩
      · exact ⟨h ▸ hbc, Or.inr (Or.inl h)⟩
  unfold dd
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton, ea, eb, ec,
    Finset.prod_pair hbc, Finset.prod_pair hac, Finset.prod_pair hab]
  ring

/-! ### Union of two node sets -/

lemma dd_union (f : ℝ → ℝ) {Y Y' : Finset ℝ} (hd : Disjoint Y Y') {c d : ℝ}
    (hY : ∀ z ∈ Y, ∏ w ∈ Y', (z - w) = c) (hY' : ∀ z ∈ Y', ∏ w ∈ Y, (z - w) = d) :
    dd f (Y ∪ Y') = dd f Y / c + dd f Y' / d := by
  unfold dd
  rw [Finset.sum_union hd, Finset.sum_div, Finset.sum_div]
  congr 1
  · refine Finset.sum_congr rfl fun z hz => ?_
    have hz' : z ∉ Y' := Finset.disjoint_left.mp hd hz
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hz',
      Finset.prod_union (hd.mono_left (Finset.erase_subset z Y)), hY z hz, div_div]
  · refine Finset.sum_congr rfl fun z hz => ?_
    have hz' : z ∉ Y := Finset.disjoint_right.mp hd hz
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hz',
      Finset.prod_union (hd.mono_right (Finset.erase_subset z Y')), hY' z hz, div_div,
      mul_comm d]

/-! ### Generalized Rolle theorem -/

/-- If `G 0` vanishes at `n+1` increasing points of `(L, R)` and `G (k+1)` is the
derivative of `G k` there for `k < n`, then `G n` vanishes somewhere in `(L, R)`. -/
theorem rolle_fin : ∀ (n : ℕ) (G : ℕ → ℝ → ℝ) {L R : ℝ},
    (∀ k < n, ∀ x ∈ Ioo L R, HasDerivAt (G k) (G (k + 1) x) x) →
    ∀ z : Fin (n + 1) → ℝ, StrictMono z → (∀ i, z i ∈ Ioo L R) → (∀ i, G 0 (z i) = 0) →
    ∃ ξ ∈ Ioo L R, G n ξ = 0
  | 0, _, _, _, _, z, _, hzI, hz0 => ⟨z 0, hzI 0, hz0 0⟩
  | n + 1, G, L, R, hG, z, hz, hzI, hz0 => by
    have step : ∀ i : Fin (n + 1), ∃ w ∈ Ioo (z i.castSucc) (z i.succ), G 1 w = 0 := by
      intro i
      have hlt : z i.castSucc < z i.succ := hz (Fin.castSucc_lt_succ)
      have hsub : Icc (z i.castSucc) (z i.succ) ⊆ Ioo L R := fun x hx =>
        ⟨lt_of_lt_of_le (hzI _).1 hx.1, lt_of_le_of_lt hx.2 (hzI _).2⟩
      obtain ⟨w, hw, hw0⟩ := exists_hasDerivAt_eq_zero hlt
        (fun x hx => (hG 0 (Nat.succ_pos n) x (hsub hx)).continuousAt.continuousWithinAt)
        (by rw [hz0, hz0])
        (fun x hx => hG 0 (Nat.succ_pos n) x (hsub (Ioo_subset_Icc_self hx)))
      exact ⟨w, hw, hw0⟩
    choose w hw hw0 using step
    have hwmono : StrictMono w := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      calc w i.castSucc < z i.castSucc.succ := (hw _).2
        _ = z i.succ.castSucc := by rw [Fin.succ_castSucc]
        _ < w i.succ := (hw _).1
    have hwI : ∀ i, w i ∈ Ioo L R := fun i =>
      ⟨lt_trans (hzI _).1 (hw i).1, lt_trans (hw i).2 (hzI _).2⟩
    exact rolle_fin n (fun k => G (k + 1)) (fun k hk x hx => hG (k + 1) (by omega) x hx)
      w hwmono hwI hw0

theorem rolle_finset (n : ℕ) (G : ℕ → ℝ → ℝ) {L R : ℝ}
    (hG : ∀ k < n, ∀ x ∈ Ioo L R, HasDerivAt (G k) (G (k + 1) x) x)
    (S : Finset ℝ) (hS : S.card = n + 1) (hSI : ∀ z ∈ S, z ∈ Ioo L R)
    (hS0 : ∀ z ∈ S, G 0 z = 0) :
    ∃ ξ ∈ Ioo L R, G n ξ = 0 :=
  rolle_fin n G hG (fun i => S.orderEmbOfFin hS i) (S.orderEmbOfFin hS).strictMono
    (fun i => hSI _ (S.orderEmbOfFin_mem hS i)) (fun i => hS0 _ (S.orderEmbOfFin_mem hS i))

/-! ### Lagrange interpolation -/

/-- The Lagrange interpolation polynomial of `f` at the nodes `S`. -/
def lagr (f : ℝ → ℝ) (S : Finset ℝ) : ℝ[X] :=
  ∑ z ∈ S, C (f z / ∏ w ∈ S.erase z, (z - w)) * ∏ w ∈ S.erase z, (X - C w)

lemma prod_erase_sub_ne_zero (S : Finset ℝ) (z : ℝ) : ∏ w ∈ S.erase z, (z - w) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hw => sub_ne_zero.mpr (Finset.ne_of_mem_erase hw).symm

lemma lagr_eval (f : ℝ → ℝ) (S : Finset ℝ) {z₀ : ℝ} (hz₀ : z₀ ∈ S) :
    (lagr f S).eval z₀ = f z₀ := by
  unfold lagr
  rw [eval_finsetSum, Finset.sum_eq_single z₀]
  · rw [eval_mul, eval_C, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    exact div_mul_cancel₀ _ (prod_erase_sub_ne_zero S z₀)
  · intro z _ hne
    rw [eval_mul, eval_prod]
    apply mul_eq_zero_of_right
    exact Finset.prod_eq_zero (i := z₀) (Finset.mem_erase.mpr ⟨hne.symm, hz₀⟩) (by simp)
  · intro h
    exact absurd hz₀ h

lemma monic_prod_erase (S : Finset ℝ) (z : ℝ) : (∏ w ∈ S.erase z, (X - C w)).Monic :=
  monic_prod_of_monic _ _ fun w _ => monic_X_sub_C w

lemma natDegree_prod_erase (S : Finset ℝ) (z : ℝ) {n : ℕ} (hS : S.card = n + 1)
    (hz : z ∈ S) : (∏ w ∈ S.erase z, (X - C w)).natDegree = n := by
  rw [natDegree_prod_of_monic _ _ fun w _ => monic_X_sub_C w]
  simp [Finset.card_erase_of_mem hz, hS]

lemma lagr_natDegree (f : ℝ → ℝ) (S : Finset ℝ) {n : ℕ} (hS : S.card = n + 1) :
    (lagr f S).natDegree ≤ n := by
  unfold lagr
  apply natDegree_sum_le_of_forall_le
  intro z hz
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_prod_erase S z hS hz]

lemma lagr_coeff (f : ℝ → ℝ) (S : Finset ℝ) {n : ℕ} (hS : S.card = n + 1) :
    (lagr f S).coeff n = dd f S := by
  unfold lagr dd
  rw [finsetSum_coeff]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [coeff_C_mul]
  have hm := monic_prod_erase S z
  have hd := natDegree_prod_erase S z hS hz
  rw [← hd, hm.coeff_natDegree, mul_one]

lemma eval_iterate_derivative_of_natDegree_le {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n)
    (x : ℝ) : (derivative^[n] p).eval x = n.factorial * p.coeff n := by
  have hdeg : (derivative^[n] p).natDegree = 0 := by
    have := natDegree_iterate_derivative p n
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg, eval_C, coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, nsmul_eq_mul]

/-! ### Mean value theorem for divided differences -/

/-- If `F (k+1)` is the derivative of `F k` on `(L, R)` for `k < n`, and `S ⊆ (L, R)`
has `n + 1` elements, then `F n ξ = n! · dd (F 0) S` for some `ξ ∈ (L, R)`. -/
theorem dd_mvt (n : ℕ) (F : ℕ → ℝ → ℝ) {L R : ℝ}
    (hF : ∀ k < n, ∀ x ∈ Ioo L R, HasDerivAt (F k) (F (k + 1) x) x)
    (S : Finset ℝ) (hS : S.card = n + 1) (hSI : ∀ z ∈ S, z ∈ Ioo L R) :
    ∃ ξ ∈ Ioo L R, F n ξ = n.factorial * dd (F 0) S := by
  set Q := lagr (F 0) S with hQ
  let G : ℕ → ℝ → ℝ := fun k x => F k x - (derivative^[k] Q).eval x
  have hG : ∀ k < n, ∀ x ∈ Ioo L R, HasDerivAt (G k) (G (k + 1) x) x := by
    intro k hk x hx
    have h1 := hF k hk x hx
    have h2 := Polynomial.hasDerivAt (derivative^[k] Q) x
    simp only [G]
    rw [Function.iterate_succ_apply']
    exact h1.sub h2
  have hS0 : ∀ z ∈ S, G 0 z = 0 := by
    intro z hz
    simp only [G, Function.iterate_zero, id_eq, hQ, lagr_eval _ _ hz, sub_self]
  obtain ⟨ξ, hξ, h0⟩ := rolle_finset n G hG S hS hSI hS0
  refine ⟨ξ, hξ, ?_⟩
  have h := eval_iterate_derivative_of_natDegree_le (lagr_natDegree (F 0) S hS) ξ
  rw [lagr_coeff (F 0) S hS] at h
  simp only [G] at h0
  rw [← hQ] at h
  linarith

theorem dd_pos (n : ℕ) (F : ℕ → ℝ → ℝ) {L R : ℝ}
    (hF : ∀ k < n, ∀ x ∈ Ioo L R, HasDerivAt (F k) (F (k + 1) x) x)
    (hpos : ∀ x ∈ Ioo L R, 0 < F n x)
    (S : Finset ℝ) (hS : S.card = n + 1) (hSI : ∀ z ∈ S, z ∈ Ioo L R) :
    0 < dd (F 0) S := by
  obtain ⟨ξ, hξ, h⟩ := dd_mvt n F hF S hS hSI
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have := hpos ξ hξ
  rw [h] at this
  exact pos_of_mul_pos_right this hf.le

theorem dd_neg (n : ℕ) (F : ℕ → ℝ → ℝ) {L R : ℝ}
    (hF : ∀ k < n, ∀ x ∈ Ioo L R, HasDerivAt (F k) (F (k + 1) x) x)
    (hneg : ∀ x ∈ Ioo L R, F n x < 0)
    (S : Finset ℝ) (hS : S.card = n + 1) (hSI : ∀ z ∈ S, z ∈ Ioo L R) :
    dd (F 0) S < 0 := by
  obtain ⟨ξ, hξ, h⟩ := dd_mvt n F hF S hS hSI
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have := hneg ξ hξ
  rw [h] at this
  by_contra hc
  push Not at hc
  linarith [mul_nonneg hf.le hc]

theorem dd_zero (n : ℕ) (F : ℕ → ℝ → ℝ) {L R : ℝ}
    (hF : ∀ k < n, ∀ x ∈ Ioo L R, HasDerivAt (F k) (F (k + 1) x) x)
    (hzero : ∀ x ∈ Ioo L R, F n x = 0)
    (S : Finset ℝ) (hS : S.card = n + 1) (hSI : ∀ z ∈ S, z ∈ Ioo L R) :
    dd (F 0) S = 0 := by
  obtain ⟨ξ, hξ, h⟩ := dd_mvt n F hF S hS hSI
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [hzero ξ hξ] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hf

/-! ### The power family `t ↦ (p)_k t^(p-k)` -/

/-- `powF p k t = p (p-1) ⋯ (p-k+1) · t^(p-k)`, the `k`-th derivative of `t ↦ t^p`. -/
def powF (p : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (descPochhammer ℝ k).eval p * t ^ (p - k)

lemma powF_zero (p t : ℝ) : powF p 0 t = t ^ p := by
  simp [powF]

lemma powF_hasDerivAt (p : ℝ) (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (powF p k) (powF p (k + 1) t) t := by
  have h := (Real.hasDerivAt_rpow_const (p := p - k) (Or.inl ht)).const_mul
    ((descPochhammer ℝ k).eval p)
  unfold powF
  convert h using 1
  rw [descPochhammer_succ_right, eval_mul]
  simp only [eval_sub, eval_X, eval_natCast, Nat.cast_add, Nat.cast_one]
  rw [show p - (k + 1 : ℝ) = p - k - 1 by ring]
  ring

lemma powF_hasDerivAt_on (p : ℝ) (n : ℕ) {L R : ℝ} (hL : 0 ≤ L) :
    ∀ k < n, ∀ x ∈ Ioo L R, HasDerivAt (powF p k) (powF p (k + 1) x) x :=
  fun k _ _ hx => powF_hasDerivAt p k (ne_of_gt (lt_of_le_of_lt hL hx.1))

end HolevoUtkin
