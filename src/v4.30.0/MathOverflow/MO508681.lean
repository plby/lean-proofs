/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-

This is a Lean formalization of a solution to MathOverflow question
508681:

https://mathoverflow.net/questions/508681/a-two-player-stochastic-game-fight-or-draw

The original question was asked by Nate River.

The solution here is by ChatGPT-5.4 Pro (from OpenAI).


The proof was formalized by Aristotle (from Harmonic).


The proof is verified by Lean.

-/


/-
Formalization of the optimal strategy and game value for the game described.

We define the constants `r` and `c`, and the functions `w`, `D`, and `g` as in the text.
We define the Bellman operator `C_r`.
We prove that `w` satisfies the Bellman equation (Lemma 3).
We prove that the Bellman equation has a unique uniformly bounded solution (Lemma 2).
We define `W_star` as the constant sequence of functions equal to `w` and prove it is the
unique uniformly bounded solution.
We define `game_value` as the integral of `w` over [0, 1] and prove it equals `3 - 2 * sqrt 2`.
-/

import Mathlib

namespace MO508681

/-
Definitions of constants r and c from the text.
-/
noncomputable def r : Real := Real.sqrt 2 - 1

noncomputable def c : Real := 2 * r - 1

/-
Definitions of functions w, D, and g from the text.
-/
noncomputable def w (x : Real) : Real :=
  if x < r then c else 2 * x - 1

noncomputable def D (k : Nat) (x : Real) : Real :=
  if x < r then 2 * (x ^ (k + 1) / r ^ k) - 1 else 2 * x - 1

noncomputable def g (x : Real) : Real :=
  if x < r then -1 else (2 * x - 1 - r) / (1 - r)

/-
Definition of the operator C_r from the text.
-/
noncomputable def C_r (f : Real → Real) (x : Real) : Real :=
  x * ((1 - r) * g x + r * f x) + ∫ u in x..1, ((1 - r) * g u + r * f u)

/-
Lemma 3: The function w satisfies the Bellman equation
w(x) = max(D_k(x), C_r w(x)) for all k and x in [0,1].
-/

lemma integral_affine (a b A B : ℝ) :
    (∫ u in a..b, A * u + B) = A * ((b ^ 2 - a ^ 2) / 2) + B * (b - a) := by
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    simp [smul_eq_mul]
    ring
  · exact (Continuous.mul continuous_const continuous_id).intervalIntegrable a b
  · exact continuous_const.intervalIntegrable a b

lemma C_r_w_left (x : ℝ) (hxr : x < r) :
    C_r w x = c := by
  have hr_le_one : r ≤ 1 := by
    unfold r
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have h1r : 1 - r ≠ 0 := by
    unfold r
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  let F : ℝ → ℝ := fun u => (1 - r) * g u + r * w u
  have hsplit : (∫ u in x..1, F u) = (∫ u in x..r, F u) + (∫ u in r..1, F u) := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · apply_rules [Continuous.intervalIntegrable]
      unfold F w g
      apply_rules [Continuous.if, Continuous.add, Continuous.mul, continuous_const, continuous_id]
      · erw [frontier_Iio]
        norm_num
        grind
      · erw [frontier_Iio]
        norm_num
        unfold c
        ring
    · apply_rules [Continuous.intervalIntegrable]
      unfold F w g
      apply_rules [Continuous.if, Continuous.add, Continuous.mul, continuous_const, continuous_id]
      · erw [frontier_Iio]
        norm_num
        grind
      · erw [frontier_Iio]
        norm_num
        unfold c
        ring
  have hleft : (∫ u in x..r, F u) = ∫ u in x..r, ((1 - r) * (-1) + r * c) := by
    apply intervalIntegral.integral_congr_ae
    have hae : ∀ᵐ u : ℝ, u ≠ r := by simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [hae] with u hur hu
    have huI : u ∈ Set.Ioc x r := by simpa [Set.uIoc_of_le (le_of_lt hxr)] using hu
    have hult : u < r := lt_of_le_of_ne huI.2 hur
    unfold F w g
    simp [hult]
  have hright : (∫ u in r..1, F u) = ∫ u in r..1, ((2 * (1 + r)) * u + (-1 - 2 * r)) := by
    apply intervalIntegral.integral_congr_ae
    have hae : ∀ᵐ u : ℝ, u ≠ r := by simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [hae] with u hur hu
    have huI : u ∈ Set.Ioc r 1 := by simpa [Set.uIoc_of_le hr_le_one] using hu
    have hnot : ¬ u < r := not_lt_of_ge huI.1.le
    unfold F w g
    simp [hnot]
    field_simp [h1r]
    ring
  unfold C_r
  rw [show (fun u => (1 - r) * g u + r * w u) = F by rfl]
  rw [hsplit, hleft, hright]
  rw [intervalIntegral.integral_const, integral_affine]
  simp only [mul_neg, mul_one, neg_sub, smul_eq_mul, one_pow]
  rw [w, g, c, if_pos hxr, if_pos hxr, r]
  ring_nf
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

lemma C_r_w_right_le (x : ℝ) (hrx : r ≤ x) (hx1 : x ≤ 1) :
    C_r w x ≤ 2 * x - 1 := by
  have h1r : 1 - r ≠ 0 := by
    unfold r
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  let F : ℝ → ℝ := fun u => (1 - r) * g u + r * w u
  have hF : (∫ u in x..1, F u) = ∫ u in x..1, ((2 * (1 + r)) * u + (-1 - 2 * r)) := by
    apply intervalIntegral.integral_congr_ae
    have hae : ∀ᵐ u : ℝ, u ≠ r := by simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [hae] with u hur hu
    have huI : u ∈ Set.Ioc x 1 := by simpa [Set.uIoc_of_le hx1] using hu
    have hnot : ¬ u < r := not_lt_of_ge (le_trans hrx huI.1.le)
    unfold F w g
    simp [hnot]
    field_simp [h1r]
    ring
  unfold C_r
  rw [show (fun u => (1 - r) * g u + r * w u) = F by rfl, hF]
  rw [integral_affine]
  rw [w, g, c, if_neg (not_lt_of_ge hrx), if_neg (not_lt_of_ge hrx), r]
  field_simp [show 1 - (Real.sqrt 2 - 1) ≠ 0 by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]]
  ring_nf
  have hfac :
      2 * x - 1 - (1 + x ^ 2 * Real.sqrt 2 - Real.sqrt 2) =
        Real.sqrt 2 * (1 - x) * (x - (Real.sqrt 2 - 1)) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hnonneg : 0 ≤ Real.sqrt 2 * (1 - x) * (x - (Real.sqrt 2 - 1)) := by
    have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h1x : 0 ≤ 1 - x := by linarith
    have hxr2 : 0 ≤ x - (Real.sqrt 2 - 1) := by simpa [r] using sub_nonneg.mpr hrx
    exact mul_nonneg (mul_nonneg hs h1x) hxr2
  linarith

lemma D_le_c_left (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hxr : x < r) :
    D k x ≤ c := by
  have hr_pos : 0 < r := by
    unfold r
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hx_le_r : x ≤ r := le_of_lt hxr
  have hpow : x ^ k ≤ r ^ k := pow_le_pow_left₀ hx0 hx_le_r k
  have hrpow_pos : 0 < r ^ k := pow_pos hr_pos k
  have hdiv : x ^ k / r ^ k ≤ 1 := div_le_one_of_le₀ hpow hrpow_pos.le
  have hmul : x * (x ^ k / r ^ k) ≤ r := by
    have h1 := mul_le_mul_of_nonneg_left hdiv hx0
    linarith
  rw [D, c, if_pos hxr]
  have hxpow : x ^ (k + 1) = x * x ^ k := by
    rw [pow_succ']
  rw [hxpow]
  have hrpow_ne : r ^ k ≠ 0 := ne_of_gt hrpow_pos
  field_simp [hrpow_ne]
  nlinarith

lemma intervalIntegrable_g_any (a b : ℝ) : IntervalIntegrable g MeasureTheory.volume a b := by
  apply_rules [Monotone.intervalIntegrable]
  intro x y hxy
  unfold g
  by_cases hxlt : x < r
  · by_cases hylt : y < r
    · simp only [hxlt, hylt, if_true]
      norm_num
    · simp only [hxlt, hylt, if_true, if_false]
      have hy_ge_r : r ≤ y := le_of_not_gt hylt
      have hden : 0 < 1 - r := by
        unfold r
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      have hnum : -(1 - r) ≤ 2 * y - 1 - r := by nlinarith
      have hdiv := div_le_div_of_nonneg_right hnum hden.le
      have hleft : -(1 - r) / (1 - r) = -1 := by field_simp [ne_of_gt hden]
      linarith
  · by_cases hylt : y < r
    · have hx_ge_r : r ≤ x := le_of_not_gt hxlt
      exact False.elim (not_lt_of_ge (le_trans hx_ge_r hxy) hylt)
    · simp only [hxlt, hylt, if_false]
      exact div_le_div_of_nonneg_right (by linarith) (by
        unfold r
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)])

theorem lemma_candidate (k : Nat) (x : Real) (hx : 0 ≤ x ∧ x ≤ 1) :
  w x = max (D k x) (C_r w x) := by
  by_cases hxr : x < r
  · have hC := C_r_w_left x hxr
    have hD := D_le_c_left k x hx.1 hxr
    rw [show w x = c by simp [w, hxr], hC]
    exact (max_eq_right hD).symm
  · have hrx : r ≤ x := le_of_not_gt hxr
    have hC := C_r_w_right_le x hrx hx.2
    rw [show w x = 2 * x - 1 by simp [w, hxr], show D k x = 2 * x - 1 by simp [D, hxr]]
    exact (max_eq_left hC).symm

/-
Definitions of is_solution and is_uniformly_bounded from Lemma 2.
-/
def is_solution (W : ℕ → ℝ → ℝ) : Prop :=
  ∀ k x, 0 ≤ x ∧ x ≤ 1 → W k x = max (D k x) (C_r (W (k + 1)) x)

def is_uniformly_bounded (W : ℕ → ℝ → ℝ) : Prop :=
  ∃ M, ∀ k x, 0 ≤ x ∧ x ≤ 1 → |W k x| ≤ M

/-
Lemma: The operator C_r satisfies a contraction property: if |f - h| <= delta, then
|C_r f - C_r h| <= r * delta.
-/
theorem C_r_contraction (f h : ℝ → ℝ) (δ : ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hh : IntervalIntegrable h MeasureTheory.volume 0 1)
    (h_diff : ∀ x, 0 ≤ x ∧ x ≤ 1 → |f x - h x| ≤ δ) :
    ∀ x, 0 ≤ x ∧ x ≤ 1 → |C_r f x - C_r h x| ≤ r * δ := by
  intro x hx
  have hr_nonneg : 0 ≤ r := by
    unfold r
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hf_x : IntervalIntegrable f MeasureTheory.volume x 1 := by
    apply_rules [hf.mono_set, Set.Icc_subset_Icc]
    · simp_all only [and_imp, zero_le_one, inf_of_le_left]
    · simp_all only [and_imp, sup_of_le_right, zero_le_one, Std.le_refl]
  have hh_x : IntervalIntegrable h MeasureTheory.volume x 1 := by
    apply_rules [hh.mono_set, Set.Icc_subset_Icc]
    · simp_all only [and_imp, zero_le_one, inf_of_le_left]
    · simp_all only [and_imp, sup_of_le_right, zero_le_one, Std.le_refl]
  have hg_x : IntervalIntegrable g MeasureTheory.volume x 1 := intervalIntegrable_g_any x 1
  have hif : IntervalIntegrable (fun u => (1 - r) * g u + r * f u) MeasureTheory.volume x 1 :=
    (hg_x.const_mul _).add (hf_x.const_mul _)
  have hih : IntervalIntegrable (fun u => (1 - r) * g u + r * h u) MeasureTheory.volume x 1 :=
    (hg_x.const_mul _).add (hh_x.const_mul _)
  have h_def : C_r f x - C_r h x = r * x * (f x - h x) + r * ∫ u in x..1, (f u - h u) := by
    calc
      C_r f x - C_r h x
          = x * (((1 - r) * g x + r * f x) - ((1 - r) * g x + r * h x)) +
              ((∫ u in x..1, (1 - r) * g u + r * f u) -
                ∫ u in x..1, (1 - r) * g u + r * h u) := by
                unfold C_r
                ring
      _ = x * (((1 - r) * g x + r * f x) - ((1 - r) * g x + r * h x)) +
              ∫ u in x..1, ((1 - r) * g u + r * f u) - ((1 - r) * g u + r * h u) := by
                rw [intervalIntegral.integral_sub hif hih]
      _ = r * x * (f x - h x) + ∫ u in x..1, r * (f u - h u) := by
                congr 1
                · ring
                · apply intervalIntegral.integral_congr
                  intro u hu
                  ring
      _ = r * x * (f x - h x) + r * ∫ u in x..1, (f u - h u) := by
                rw [intervalIntegral.integral_const_mul]
  have hδ_nonneg : 0 ≤ δ := by
    have h0 := h_diff 0 ⟨by norm_num, by norm_num⟩
    exact le_trans (abs_nonneg _) h0
  have h_integral_bound : |∫ u in x..1, (f u - h u)| ≤ δ * (1 - x) := by
    rw [intervalIntegral.integral_of_le hx.2]
    calc
      |∫ u in Set.Ioc x 1, f u - h u| ≤
          ∫ u in Set.Ioc x 1, ‖f u - h u‖ := by
        exact MeasureTheory.norm_integral_le_integral_norm (_ : ℝ → ℝ)
      _ ≤ ∫ _u in Set.Ioc x 1, δ := by
        exact
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (Continuous.integrableOn_Ioc (by continuity))
            (Filter.eventually_of_mem (MeasureTheory.ae_restrict_mem measurableSet_Ioc) fun u hu =>
              h_diff u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      _ = δ * (1 - x) := by
        simp [mul_comm, hx.2]
  rw [h_def]
  rw [abs_le]
  have hA := abs_le.mp (h_diff x hx)
  have hI := abs_le.mp h_integral_bound
  have hrx_nonneg : 0 ≤ r * x := mul_nonneg hr_nonneg hx.1
  constructor
  · have hAlo : -(r * x * δ) ≤ r * x * (f x - h x) := by
      nlinarith [mul_le_mul_of_nonneg_left hA.1 hrx_nonneg]
    have hIlo : -(r * (δ * (1 - x))) ≤ r * ∫ u in x..1, (f u - h u) := by
      nlinarith [mul_le_mul_of_nonneg_left hI.1 hr_nonneg]
    nlinarith
  · have hAhi : r * x * (f x - h x) ≤ r * x * δ := by
      nlinarith [mul_le_mul_of_nonneg_left hA.2 hrx_nonneg]
    have hIhi : r * ∫ u in x..1, (f u - h u) ≤ r * (δ * (1 - x)) := by
      nlinarith [mul_le_mul_of_nonneg_left hI.2 hr_nonneg]
    nlinarith

/-
Lemma: If the difference between W1 and W2 at step k+1 is bounded by D_val,
then at step k it is bounded by r * D_val.
-/
theorem lemma_uniqueness_step (W1 W2 : ℕ → ℝ → ℝ) (k : ℕ) (D_val : ℝ)
    (h1 : is_solution W1) (h2 : is_solution W2)
    (hW1_int : IntervalIntegrable (W1 (k + 1)) MeasureTheory.volume 0 1)
    (hW2_int : IntervalIntegrable (W2 (k + 1)) MeasureTheory.volume 0 1)
    (h_bound : ∀ x, 0 ≤ x ∧ x ≤ 1 → |W1 (k + 1) x - W2 (k + 1) x| ≤ D_val) :
    ∀ x, 0 ≤ x ∧ x ≤ 1 → |W1 k x - W2 k x| ≤ r * D_val := by
  intro x hx
  have h_diff :
      abs (W1 k x - W2 k x) ≤
        abs (C_r (W1 (k + 1)) x - C_r (W2 (k + 1)) x) := by
    rw [h1 k x hx, h2 k x hx]
    cases max_cases (D k x) (C_r (W1 (k + 1)) x)
    all_goals
      cases max_cases (D k x) (C_r (W2 (k + 1)) x)
    all_goals
      cases abs_cases (C_r (W1 (k + 1)) x - C_r (W2 (k + 1)) x)
    all_goals
      cases
        abs_cases
          (Max.max (D k x) (C_r (W1 (k + 1)) x) -
            Max.max (D k x) (C_r (W2 (k + 1)) x))
    all_goals
      linarith
  generalize_proofs at *
  exact h_diff.trans (C_r_contraction _ _ _ hW1_int hW2_int h_bound x hx) |>.trans <| by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show r = Real.sqrt 2 - 1 from rfl]

/-
Lemma 2: The Bellman equation has at most one uniformly bounded solution (assuming integrability).
-/
theorem lemma_uniqueness (W1 W2 : ℕ → ℝ → ℝ) (h1 : is_solution W1) (h2 : is_solution W2)
    (hb1 : is_uniformly_bounded W1) (hb2 : is_uniformly_bounded W2)
    (hW1_int : ∀ k, IntervalIntegrable (W1 k) MeasureTheory.volume 0 1)
    (hW2_int : ∀ k, IntervalIntegrable (W2 k) MeasureTheory.volume 0 1) :
    ∀ k x, 0 ≤ x ∧ x ≤ 1 → W1 k x = W2 k x := by
  -- By induction, `|W1_k(x) - W2_k(x)| ≤ r^m D` for all `x ∈ [0,1]`.
  have h_induction :
      ∀ k m : ℕ, ∀ x : ℝ,
        0 ≤ x ∧ x ≤ 1 →
          abs (W1 k x - W2 k x) ≤ r ^ m * (hb1.choose + hb2.choose) := by
    intro k m x hx
    induction m generalizing k x with
    | zero =>
        simpa using
          le_trans (abs_sub _ _) (add_le_add (hb1.choose_spec k x hx) (hb2.choose_spec k x hx))
    | succ m ih =>
        exact
          le_trans
            (lemma_uniqueness_step W1 W2 k (r ^ m * (hb1.choose + hb2.choose)) h1 h2
              (hW1_int _) (hW2_int _) (fun x hx => ih _ _ hx) x hx)
            (by rw [pow_succ', mul_assoc])
  -- Since `r < 1`, `r^m → 0` as `m → ∞`.
  have h_r_pow_zero :
      Filter.Tendsto (fun m => r ^ m * (hb1.choose + hb2.choose)) Filter.atTop (nhds 0) := by
    have hr_nonneg : 0 ≤ r := by
      exact sub_nonneg.2 <| Real.le_sqrt_of_sq_le <| by norm_num
    have hr_lt_one : r < 1 := by
      rw [r]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two]
    simpa using
      Filter.Tendsto.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt_one)
        tendsto_const_nhds
  exact fun k x hx => by
    simpa [sub_eq_zero] using
      le_antisymm
        (le_of_tendsto_of_tendsto' tendsto_const_nhds h_r_pow_zero fun m =>
          h_induction k m x hx)
        (abs_nonneg _)

/-
The function w is uniformly bounded.
-/
theorem w_is_uniformly_bounded : is_uniformly_bounded (fun _ => w) := by
  -- Choose M = 1, which bounds `w x` on [0,1].
  use 1
  intro k x hx
  by_cases hx_lt : x < r
  · change |if x < r then c else 2 * x - 1| ≤ 1
    rw [if_pos hx_lt, c, r]
    exact abs_le.mpr
      ⟨by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two],
       by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two]⟩
  · change |if x < r then c else 2 * x - 1| ≤ 1
    rw [if_neg hx_lt]
    exact abs_le.mpr ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩

/-
Theorem: W_star (defined as w for all k) is the unique uniformly bounded solution to the
Bellman equation.
-/
noncomputable def W_star (_ : ℕ) (x : ℝ) : ℝ := w x

theorem unique_solution :
    is_solution W_star ∧ is_uniformly_bounded W_star ∧
    ∀ W, is_solution W → is_uniformly_bounded W →
    (∀ k, IntervalIntegrable (W k) MeasureTheory.volume 0 1) →
    ∀ k x, 0 ≤ x ∧ x ≤ 1 → W k x = W_star k x := by
  unfold W_star
  use fun k x hx => lemma_candidate k x hx
  refine ⟨?_, ?_⟩
  · exact w_is_uniformly_bounded
  · intro W hW hW' hW'' k x hx
    apply
      lemma_uniqueness W (fun _ => w) hW (fun k x hx => lemma_candidate k x hx) hW'
        w_is_uniformly_bounded hW'' ?_ k x hx
    intro k
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le]
    · exact
        MeasureTheory.Integrable.mono'
          (g := fun _x => 2 + |c| + 1)
          (by norm_num +zetaDelta at *)
          (by
            exact Measurable.aestronglyMeasurable (by
              exact
                Measurable.ite measurableSet_Iio measurable_const
                  (measurable_id'.const_mul _ |> Measurable.sub <| measurable_const)))
          (by
            norm_num [w]
            exact Filter.eventually_inf_principal.mpr
              (Filter.Eventually.of_forall fun x hx => abs_le.mpr
                ⟨by
                  split_ifs
                  all_goals
                    cases abs_cases c
                  all_goals
                    linarith [hx.1, hx.2],
                 by
                  split_ifs
                  all_goals
                    cases abs_cases c
                  all_goals
                    linarith [hx.1, hx.2]⟩))
    · norm_num

/-
The value of the game is 3 - 2*sqrt(2).
-/
noncomputable def game_value : ℝ := ∫ x in 0..1, w x

theorem game_value_eq : game_value = 3 - 2 * Real.sqrt 2 := by
  -- Split the integral of `w` over `[0,1]` at `r`.
  have h_integral :
      ∫ x in (0 : ℝ)..1, w x =
        (∫ x in (0 : ℝ)..r, w x) + (∫ x in (r : ℝ)..1, w x) := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · apply_rules [Continuous.intervalIntegrable]
      unfold w
      apply_rules [Continuous.if, continuous_const]
      · erw [frontier_Iio]
        norm_num [r]
        ring_nf
        unfold c r
        ring
      · continuity
    · apply_rules [Continuous.intervalIntegrable]
      unfold w
      apply_rules [Continuous.if, continuous_const]
      · erw [frontier_Iio]
        norm_num [r]
        ring_nf
        unfold c r
        ring
      · continuity
  -- Evaluate the integrals over the intervals $[0,r]$ and $[r,1]$.
  have h_eval :
      (∫ x in (0 : ℝ)..r, w x) + (∫ x in (r : ℝ)..1, w x) =
        (∫ x in (0 : ℝ)..r, c) + (∫ x in (r : ℝ)..1, (2 * x - 1)) := by
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [intervalIntegral.integral_of_le, intervalIntegral.integral_of_le]
      · rw [MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => if_pos hx.2
      · exact sub_nonneg.2 <| Real.le_sqrt_of_sq_le <| by norm_num
      · exact sub_nonneg.2 <| Real.le_sqrt_of_sq_le <| by norm_num
    · refine intervalIntegral.integral_congr fun x hx => ?_
      exact if_neg (by
        rw [Set.uIcc_of_le (show r ≤ 1 by
          rw [show r = Real.sqrt 2 - 1 by rfl]
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two])] at hx
        exact hx.1.not_gt)
  convert h_integral.trans h_eval using 1
  · norm_num [mul_comm]
    ring_nf
    unfold c r
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two]

#print axioms game_value_eq
-- 'MO508681.game_value_eq' depends on axioms: [propext, Classical.choice, Quot.sound]

end MO508681
