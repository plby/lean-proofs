/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.Phase

/-!
# The Kusmin--Landau first derivative estimate

This file proves the first-derivative exponential-sum estimate used as
Lemma 8.4 of Granville--Ramaré, *Explicit bounds on exponential sums and the
scarcity of squarefree binomial coefficients*.  The proof is split into a
finite telescoping identity and a calculus wrapper.  The convention is
`expPhase x = exp (2 * π * i * x)`.
-/

namespace Erdos175

open scoped BigOperators
open Set Finset

noncomputable section

/-- The standard real additive character `e(x) = exp(2πix)`. -/
def expPhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma expPhase_eq_e (x : ℝ) : expPhase x = e x := by
  unfold expPhase e
  congr 1
  push_cast
  ring

lemma star_expPhase (x : ℝ) : (starRingEnd ℂ) (expPhase x) = expPhase (-x) := by
  simpa only [expPhase_eq_e] using conj_e x

@[simp] lemma norm_expPhase (x : ℝ) : ‖expPhase x‖ = 1 := by
  unfold expPhase
  convert Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x) using 1

@[simp] lemma expPhase_ne_zero (x : ℝ) : expPhase x ≠ 0 := by
  exact Complex.exp_ne_zero _

lemma expPhase_add (x y : ℝ) : expPhase (x + y) = expPhase x * expPhase y := by
  rw [expPhase, expPhase, expPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma expPhase_sub (x y : ℝ) : expPhase (x - y) = expPhase x / expPhase y := by
  rw [sub_eq_add_neg, expPhase_add]
  rw [show expPhase (-y) = (expPhase y)⁻¹ by
    unfold expPhase
    rw [show ((2 * Real.pi * -y : ℝ) : ℂ) * Complex.I =
        -(((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_neg]]
  rfl

/-- The reciprocal chord which occurs in the Kusmin--Landau telescoping
argument. -/
def chordInv (x : ℝ) : ℂ :=
  (1 - expPhase x)⁻¹

/-- On the upper semicircle, the reciprocal chord has constant real part.
This identity is the geometric reason that the variation term in the
Kusmin--Landau proof telescopes without loss. -/
lemma chordInv_eq_half_add_cot_mul_I {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) :
    chordInv x =
      (1 / 2 : ℂ) +
        (((Real.cos (Real.pi * x) / Real.sin (Real.pi * x)) / 2 : ℝ) : ℂ) * Complex.I := by
  unfold chordInv expPhase
  rw [show (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) =
      (((2 * (Real.pi * x) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_ofReal_mul_I, Real.cos_two_mul, Real.sin_two_mul]
  apply Complex.ext <;>
    simp only [Complex.inv_re, Complex.inv_im, Complex.normSq_apply,
      Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  · norm_num
    have hu := Real.sin_sq_add_cos_sq (Real.pi * x)
    have hc : 1 - Real.cos (Real.pi * x) ^ 2 = Real.sin (Real.pi * x) ^ 2 := by
      nlinarith
    rw [show 1 - (2 * Real.cos (Real.pi * x) ^ 2 - 1) =
        2 * Real.sin (Real.pi * x) ^ 2 by nlinarith]
    field_simp [hs]
    linear_combination -hu
  · norm_num
    have hu := Real.sin_sq_add_cos_sq (Real.pi * x)
    have hc : 1 - Real.cos (Real.pi * x) ^ 2 = Real.sin (Real.pi * x) ^ 2 := by
      nlinarith
    rw [show 1 - (2 * Real.cos (Real.pi * x) ^ 2 - 1) =
        2 * Real.sin (Real.pi * x) ^ 2 by nlinarith]
    field_simp [hs]
    linear_combination -Real.cos (Real.pi * x) * hu

/-- The real cotangent factor occurring in `chordInv`.  It is named
separately so that no complex cotangent API is needed below. -/
def cotPi (x : ℝ) : ℝ :=
  Real.cos (Real.pi * x) / Real.sin (Real.pi * x)

lemma sin_pi_mul_pos {x : ℝ} (hx : 0 < x) (hxhalf : x ≤ 1 / 2) :
    0 < Real.sin (Real.pi * x) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

lemma two_mul_le_sin_pi_mul {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    2 * x ≤ Real.sin (Real.pi * x) := by
  have h := Real.mul_le_sin (x := Real.pi * x) (by positivity)
    (by nlinarith [Real.pi_pos] : Real.pi * x ≤ Real.pi / 2)
  convert h using 1 <;> field_simp [Real.pi_ne_zero]

lemma cotPi_antitoneOn : AntitoneOn cotPi (Ioc 0 (1 / 2 : ℝ)) := by
  intro x hx y hy hxy
  have hsx : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx.1 hx.2
  have hsy : 0 < Real.sin (Real.pi * y) := sin_pi_mul_pos hy.1 hy.2
  rw [cotPi, cotPi, div_le_div_iff₀ hsy hsx]
  have hsin : 0 ≤ Real.sin (Real.pi * y - Real.pi * x) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · rw [show Real.pi * y - Real.pi * x = Real.pi * (y - x) by ring]
      exact mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hxy)
    · rw [show Real.pi * y - Real.pi * x = Real.pi * (y - x) by ring]
      have hyx : y - x ≤ 1 := by linarith [hx.1, hy.2]
      calc
        Real.pi * (y - x) ≤ Real.pi * 1 :=
          mul_le_mul_of_nonneg_left hyx Real.pi_pos.le
        _ = Real.pi := mul_one _
  rw [Real.sin_sub] at hsin
  nlinarith

lemma chordInv_sub_norm {x y : ℝ}
    (hx : x ∈ Ioc 0 (1 / 2 : ℝ)) (hy : y ∈ Ioc 0 (1 / 2 : ℝ)) (hxy : x ≤ y) :
    ‖chordInv y - chordInv x‖ = (cotPi x - cotPi y) / 2 := by
  rw [chordInv_eq_half_add_cot_mul_I (sin_pi_mul_pos hx.1 hx.2).ne',
    chordInv_eq_half_add_cot_mul_I (sin_pi_mul_pos hy.1 hy.2).ne']
  have hcot : cotPi y ≤ cotPi x := cotPi_antitoneOn hx hy hxy
  let cx : ℝ := Real.cos (Real.pi * x) / Real.sin (Real.pi * x)
  let cy : ℝ := Real.cos (Real.pi * y) / Real.sin (Real.pi * y)
  simp only [cotPi]
  change ‖(1 / 2 : ℂ) + ((cy / 2 : ℝ) : ℂ) * Complex.I -
      ((1 / 2 : ℂ) + ((cx / 2 : ℝ) : ℂ) * Complex.I)‖ = (cx - cy) / 2
  rw [show (1 / 2 : ℂ) + ((cy / 2 : ℝ) : ℂ) * Complex.I -
        ((1 / 2 : ℂ) + ((cx / 2 : ℝ) : ℂ) * Complex.I) =
      ((((cy - cx) / 2 : ℝ) : ℂ) * Complex.I) by push_cast; ring]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    abs_of_nonpos]
  · ring
  · dsimp [cotPi, cx, cy] at hcot
    linarith

lemma chordInv_sub_norm_of_ge {x y : ℝ}
    (hx : x ∈ Ioc 0 (1 / 2 : ℝ)) (hy : y ∈ Ioc 0 (1 / 2 : ℝ)) (hyx : y ≤ x) :
    ‖chordInv y - chordInv x‖ = (cotPi y - cotPi x) / 2 := by
  rw [← norm_neg, neg_sub]
  exact chordInv_sub_norm hy hx hyx

lemma chordInv_norm_le {m x : ℝ} (hm : 0 < m) (hmx : m ≤ x) (hxhalf : x ≤ 1 / 2) :
    ‖chordInv x‖ ≤ 1 / (4 * m) := by
  have hx : 0 < x := hm.trans_le hmx
  have hs : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx hxhalf
  have hsin : 2 * x ≤ Real.sin (Real.pi * x) :=
    two_mul_le_sin_pi_mul hx.le hxhalf
  unfold chordInv
  rw [norm_inv, ← norm_neg, neg_sub]
  have hnorm : ‖expPhase x - 1‖ = 2 * Real.sin (Real.pi * x) := by
    unfold expPhase
    rw [show (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) =
        Complex.I * (((2 * Real.pi * x : ℝ) : ℂ)) by ring,
      Complex.norm_exp_I_mul_ofReal_sub_one]
    norm_num
    rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
    rw [abs_of_pos hs]
  rw [hnorm]
  have hden : 4 * m ≤ 2 * Real.sin (Real.pi * x) := by nlinarith
  simpa [one_div] using (one_div_le_one_div_of_le (by positivity) hden)

lemma norm_one_sub_chordInv_eq {x : ℝ} (hx : 0 < x) (hxhalf : x ≤ 1 / 2) :
    ‖1 - chordInv x‖ = ‖chordInv x‖ := by
  rw [chordInv_eq_half_add_cot_mul_I (sin_pi_mul_pos hx hxhalf).ne']
  let c : ℝ := Real.cos (Real.pi * x) / Real.sin (Real.pi * x)
  change ‖1 - ((1 / 2 : ℂ) + ((c / 2 : ℝ) : ℂ) * Complex.I)‖ =
    ‖(1 / 2 : ℂ) + ((c / 2 : ℝ) : ℂ) * Complex.I‖
  rw [show 1 - ((1 / 2 : ℂ) + ((c / 2 : ℝ) : ℂ) * Complex.I) =
      (1 / 2 : ℂ) + ((-c / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

lemma cotPi_nonneg {x : ℝ} (hx : 0 < x) (hxhalf : x ≤ 1 / 2) : 0 ≤ cotPi x := by
  have hsin : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx hxhalf
  have hcos : 0 ≤ Real.cos (Real.pi * x) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  exact div_nonneg hcos hsin.le

lemma cotPi_le_inv_two_mul {m x : ℝ}
    (hm : 0 < m) (hmx : m ≤ x) (hxhalf : x ≤ 1 / 2) :
    cotPi x ≤ 1 / (2 * m) := by
  have hx : 0 < x := hm.trans_le hmx
  have hsin : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx hxhalf
  have hsin_lower : 2 * m ≤ Real.sin (Real.pi * x) := by
    have := two_mul_le_sin_pi_mul hx.le hxhalf
    linarith
  calc
    cotPi x ≤ 1 / Real.sin (Real.pi * x) := by
      rw [cotPi, div_le_div_iff₀ hsin hsin]
      nlinarith [Real.cos_le_one (Real.pi * x)]
    _ ≤ 1 / (2 * m) := one_div_le_one_div_of_le (by positivity) hsin_lower

/-- A finite summation-by-parts identity tailored to the reciprocal-chord
proof. -/
lemma phase_telescoping_identity (A z : ℕ → ℂ) (N : ℕ)
    (hstep : ∀ n ≤ N, z n = A n * (z n - z (n + 1))) :
    ∑ n ∈ range (N + 2), z n =
      A 0 * z 0 + (1 - A N) * z (N + 1) +
        ∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1) := by
  induction N with
  | zero =>
      norm_num [sum_range_succ]
      linear_combination hstep 0 le_rfl
  | succ N ih =>
      have ih' := ih (fun n hn ↦ hstep n (hn.trans (Nat.le_succ N)))
      rw [show N + 1 + 2 = (N + 2) + 1 by omega, sum_range_succ, ih',
        sum_range_succ]
      linear_combination hstep (N + 1) le_rfl

lemma sum_range_adjacent_sub (c : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, (c n - c (n + 1)) = c 0 - c N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih]
      ring

lemma sum_range_adjacent_sub_rev (c : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, (c (n + 1) - c n) = c N - c 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih]
      ring

/-- Discrete Kusmin--Landau estimate for forward differences monotone in
either direction.  The constant `1 / m` is a convenient rational weakening
of the classical `cot (π m / 2)` bound. -/
theorem kusminLandau_discrete_of_monotone_or_antitone
    (u : ℕ → ℝ) {m : ℝ} (hm : 0 < m) (N : ℕ)
    (hbounds : ∀ n ≤ N, m ≤ u (n + 1) - u n ∧ u (n + 1) - u n ≤ 1 / 2)
    (hmonotone :
      (∀ n < N, u (n + 1) - u n ≤ u (n + 2) - u (n + 1)) ∨
      (∀ n < N, u (n + 2) - u (n + 1) ≤ u (n + 1) - u n)) :
    ‖∑ n ∈ range (N + 2), expPhase (u n)‖ ≤ 1 / m := by
  let d : ℕ → ℝ := fun n ↦ u (n + 1) - u n
  let A : ℕ → ℂ := fun n ↦ chordInv (d n)
  let z : ℕ → ℂ := fun n ↦ expPhase (u n)
  have hd (n : ℕ) (hn : n ≤ N) : m ≤ d n ∧ d n ≤ 1 / 2 := hbounds n hn
  have hdpos (n : ℕ) (hn : n ≤ N) : 0 < d n := hm.trans_le (hd n hn).1
  have hden (n : ℕ) (hn : n ≤ N) : 1 - expPhase (d n) ≠ 0 := by
    intro he
    have hzero : chordInv (d n) = 0 := by simp [chordInv, he]
    have hform := chordInv_eq_half_add_cot_mul_I
      (sin_pi_mul_pos (hdpos n hn) (hd n hn).2).ne'
    rw [hzero] at hform
    let c : ℝ := Real.cos (Real.pi * d n) / Real.sin (Real.pi * d n)
    change (0 : ℂ) = (1 / 2 : ℂ) + ((c / 2 : ℝ) : ℂ) * Complex.I at hform
    have hre : (0 : ℝ) = 1 / 2 := by
      calc
        (0 : ℝ) = (0 : ℂ).re := rfl
        _ = ((1 / 2 : ℂ) + ((c / 2 : ℝ) : ℂ) * Complex.I).re :=
          congrArg Complex.re hform
        _ = 1 / 2 := by norm_num [Complex.mul_re]
    norm_num at hre
  have hz_mul (n : ℕ) : z (n + 1) = z n * expPhase (d n) := by
    dsimp [z, d]
    rw [← expPhase_add]
    congr 1
    ring
  have hphase (n : ℕ) (hn : n ≤ N) : z n = A n * (z n - z (n + 1)) := by
    rw [hz_mul]
    dsimp [A]
    unfold chordInv
    field_simp [hden n hn]
  have hid := phase_telescoping_identity A z N hphase
  change ‖∑ n ∈ range (N + 2), z n‖ ≤ 1 / m
  rw [hid]
  have hA0 : ‖A 0‖ ≤ 1 / (4 * m) := by
    exact chordInv_norm_le hm (hd 0 (Nat.zero_le N)).1 (hd 0 (Nat.zero_le N)).2
  have hAN : ‖1 - A N‖ ≤ 1 / (4 * m) := by
    rw [norm_one_sub_chordInv_eq (hdpos N le_rfl) (hd N le_rfl).2]
    exact chordInv_norm_le hm (hd N le_rfl).1 (hd N le_rfl).2
  have hsumNorm :
      ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ ≤ 1 / (4 * m) := by
    rcases hmonotone with hmono | hanti
    · have htel :
          ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ ≤
            (cotPi (d 0) - cotPi (d N)) / 2 := by
        calc
          _ ≤ ∑ n ∈ range N, ‖(A (n + 1) - A n) * z (n + 1)‖ :=
            norm_sum_le _ _
          _ = ∑ n ∈ range N, (cotPi (d n) - cotPi (d (n + 1))) / 2 := by
            apply sum_congr rfl
            intro n hn
            have hnlt : n < N := mem_range.mp hn
            rw [norm_mul, show ‖z (n + 1)‖ = 1 by simp [z], mul_one]
            exact chordInv_sub_norm
              ⟨hdpos n (by omega), (hd n (by omega)).2⟩
              ⟨hdpos (n + 1) (by omega), (hd (n + 1) (by omega)).2⟩
              (hmono n hnlt)
          _ = (cotPi (d 0) - cotPi (d N)) / 2 := by
            rw [← sum_div, sum_range_adjacent_sub]
      have hnonneg : 0 ≤ cotPi (d N) := cotPi_nonneg (hdpos N le_rfl) (hd N le_rfl).2
      have hupper : cotPi (d 0) ≤ 1 / (2 * m) :=
        cotPi_le_inv_two_mul hm (hd 0 (Nat.zero_le N)).1 (hd 0 (Nat.zero_le N)).2
      refine htel.trans ?_
      calc
        (cotPi (d 0) - cotPi (d N)) / 2 ≤ cotPi (d 0) / 2 := by linarith
        _ ≤ (1 / (2 * m)) / 2 := by gcongr
        _ = 1 / (4 * m) := by field_simp; norm_num
    · have htel :
          ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ ≤
            (cotPi (d N) - cotPi (d 0)) / 2 := by
        calc
          _ ≤ ∑ n ∈ range N, ‖(A (n + 1) - A n) * z (n + 1)‖ :=
            norm_sum_le _ _
          _ = ∑ n ∈ range N, (cotPi (d (n + 1)) - cotPi (d n)) / 2 := by
            apply sum_congr rfl
            intro n hn
            have hnlt : n < N := mem_range.mp hn
            rw [norm_mul, show ‖z (n + 1)‖ = 1 by simp [z], mul_one]
            exact chordInv_sub_norm_of_ge
              ⟨hdpos n (by omega), (hd n (by omega)).2⟩
              ⟨hdpos (n + 1) (by omega), (hd (n + 1) (by omega)).2⟩
              (hanti n hnlt)
          _ = (cotPi (d N) - cotPi (d 0)) / 2 := by
            rw [← sum_div]
            exact congrArg (fun t : ℝ ↦ t / 2)
              (sum_range_adjacent_sub_rev (fun n ↦ cotPi (d n)) N)
      have hnonneg : 0 ≤ cotPi (d 0) :=
        cotPi_nonneg (hdpos 0 (Nat.zero_le N)) (hd 0 (Nat.zero_le N)).2
      have hupper : cotPi (d N) ≤ 1 / (2 * m) :=
        cotPi_le_inv_two_mul hm (hd N le_rfl).1 (hd N le_rfl).2
      refine htel.trans ?_
      calc
        (cotPi (d N) - cotPi (d 0)) / 2 ≤ cotPi (d N) / 2 := by linarith
        _ ≤ (1 / (2 * m)) / 2 := by gcongr
        _ = 1 / (4 * m) := by field_simp; norm_num
  have htri :
      ‖A 0 * z 0 + (1 - A N) * z (N + 1) +
          ∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ ≤
        ‖A 0‖ + ‖1 - A N‖ +
          ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ := by
    calc
      _ ≤ ‖A 0 * z 0 + (1 - A N) * z (N + 1)‖ +
          ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ := norm_add_le _ _
      _ ≤ (‖A 0 * z 0‖ + ‖(1 - A N) * z (N + 1)‖) +
          ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ := by
            gcongr
            exact norm_add_le _ _
      _ = ‖A 0‖ + ‖1 - A N‖ +
          ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ := by
            simp [z]
  calc
    _ ≤ ‖A 0‖ + ‖1 - A N‖ +
        ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ := htri
    _ ≤ 1 / (4 * m) + 1 / (4 * m) + 1 / (4 * m) := by
      gcongr
    _ ≤ 1 / m := by
      have hq : 0 ≤ 1 / (4 * m) := by positivity
      have heq : 1 / m = 4 * (1 / (4 * m)) := by field_simp
      rw [heq]
      linarith

/-- Increasing-forward-difference form of `kusminLandau_discrete_of_monotone_or_antitone`. -/
theorem kusminLandau_discrete (u : ℕ → ℝ) {m : ℝ} (hm : 0 < m) (N : ℕ)
    (hbounds : ∀ n ≤ N, m ≤ u (n + 1) - u n ∧ u (n + 1) - u n ≤ 1 / 2)
    (hmono : ∀ n < N, u (n + 1) - u n ≤ u (n + 2) - u (n + 1)) :
    ‖∑ n ∈ range (N + 2), expPhase (u n)‖ ≤ 1 / m :=
  kusminLandau_discrete_of_monotone_or_antitone u hm N hbounds (Or.inl hmono)

/-- Decreasing-forward-difference form, used by reciprocal phases after the
last Weyl differencing step. -/
theorem kusminLandau_discrete_antitone (u : ℕ → ℝ) {m : ℝ} (hm : 0 < m) (N : ℕ)
    (hbounds : ∀ n ≤ N, m ≤ u (n + 1) - u n ∧ u (n + 1) - u n ≤ 1 / 2)
    (hanti : ∀ n < N, u (n + 2) - u (n + 1) ≤ u (n + 1) - u n) :
    ‖∑ n ∈ range (N + 2), expPhase (u n)‖ ≤ 1 / m :=
  kusminLandau_discrete_of_monotone_or_antitone u hm N hbounds (Or.inr hanti)

/-- First-derivative Kusmin--Landau estimate on a real interval.  This is the
calculus-facing form of Granville--Ramaré Lemma 8.4 (with the harmlessly
weaker rational constant `1 / m`). -/
theorem kusminLandau_of_deriv_monotone_or_antitone
    (f : ℝ → ℝ) (a : ℝ) {m : ℝ} (hm : 0 < m) (N : ℕ)
    (hdiff : DifferentiableOn ℝ f (Icc a (a + (N + 1 : ℕ))))
    (hderiv_bounds : ∀ x ∈ Icc a (a + (N + 1 : ℕ)),
      m ≤ deriv f x ∧ deriv f x ≤ 1 / 2)
    (hderiv_monotone :
      MonotoneOn (deriv f) (Icc a (a + (N + 1 : ℕ))) ∨
      AntitoneOn (deriv f) (Icc a (a + (N + 1 : ℕ)))) :
    ‖∑ n ∈ range (N + 2), expPhase (f (a + n))‖ ≤ 1 / m := by
  let u : ℕ → ℝ := fun n ↦ f (a + n)
  have hmean (n : ℕ) (hn : n ≤ N) :
      ∃ c ∈ Ioo (a + (n : ℝ)) (a + (n + 1 : ℕ)),
        u (n + 1) - u n = deriv f c := by
    let x : ℝ := a + n
    let y : ℝ := a + (n + 1 : ℕ)
    have hxy : x < y := by dsimp [x, y]; norm_num
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
    have hsubcc : Icc x y ⊆ Icc a (a + (N + 1 : ℕ)) := by
      intro t ht
      dsimp [x, y] at ht
      constructor
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        exact (le_add_of_nonneg_right hn0).trans ht.1
      · norm_num at ht ⊢
        linarith
    have hsuboo : Ioo x y ⊆ Icc a (a + (N + 1 : ℕ)) :=
      Ioo_subset_Icc_self.trans hsubcc
    obtain ⟨c, hc, hcder⟩ := exists_deriv_eq_slope f hxy
      (hdiff.continuousOn.mono hsubcc) (hdiff.mono hsuboo)
    refine ⟨c, hc, ?_⟩
    dsimp [u, x, y] at hcder ⊢
    have hunit : a + (n + 1 : ℕ) - (a + (n : ℝ)) = 1 := by norm_num
    rw [hunit, div_one] at hcder
    simpa using hcder.symm
  have hbounds : ∀ n ≤ N,
      m ≤ u (n + 1) - u n ∧ u (n + 1) - u n ≤ 1 / 2 := by
    intro n hn
    obtain ⟨c, hc, heq⟩ := hmean n hn
    have hcwhole : c ∈ Icc a (a + (N + 1 : ℕ)) := by
      constructor
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        linarith [hc.1]
      · have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
        norm_num at hc ⊢
        linarith [hc.2]
    simpa [heq] using hderiv_bounds c hcwhole
  apply kusminLandau_discrete_of_monotone_or_antitone u hm N hbounds
  rcases hderiv_monotone with hinc | hdec
  · left
    intro n hn
    obtain ⟨c, hc, hcEq⟩ := hmean n (by omega)
    obtain ⟨d, hd, hdEq⟩ := hmean (n + 1) (by omega)
    have hcwhole : c ∈ Icc a (a + (N + 1 : ℕ)) := by
      constructor
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        linarith [hc.1]
      · have hnR : (n : ℝ) < N := by exact_mod_cast hn
        norm_num at hc ⊢
        linarith [hc.2]
    have hdwhole : d ∈ Icc a (a + (N + 1 : ℕ)) := by
      constructor
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        norm_num at hd
        linarith [hd.1]
      · have hnR : (n : ℝ) < N := by exact_mod_cast hn
        norm_num at hd ⊢
        have hn2 : (n : ℝ) + 2 ≤ (N : ℝ) + 1 := by
          have hs : (n : ℝ) + 1 ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
          linarith
        calc
          d ≤ a + ((n : ℝ) + 1 + 1) := hd.2.le
          _ = a + ((n : ℝ) + 2) := by ring
          _ ≤ a + ((N : ℝ) + 1) := add_le_add_right hn2 a
    rw [hcEq, hdEq]
    exact hinc hcwhole hdwhole (le_of_lt (hc.2.trans hd.1))
  · right
    intro n hn
    obtain ⟨c, hc, hcEq⟩ := hmean n (by omega)
    obtain ⟨d, hd, hdEq⟩ := hmean (n + 1) (by omega)
    have hcwhole : c ∈ Icc a (a + (N + 1 : ℕ)) := by
      constructor
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        linarith [hc.1]
      · have hnR : (n : ℝ) < N := by exact_mod_cast hn
        norm_num at hc ⊢
        linarith [hc.2]
    have hdwhole : d ∈ Icc a (a + (N + 1 : ℕ)) := by
      constructor
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        norm_num at hd
        linarith [hd.1]
      · have hnR : (n : ℝ) < N := by exact_mod_cast hn
        norm_num at hd ⊢
        have hn2 : (n : ℝ) + 2 ≤ (N : ℝ) + 1 := by
          have hs : (n : ℝ) + 1 ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
          linarith
        calc
          d ≤ a + ((n : ℝ) + 1 + 1) := hd.2.le
          _ = a + ((n : ℝ) + 2) := by ring
          _ ≤ a + ((N : ℝ) + 1) := add_le_add_right hn2 a
    rw [hcEq, hdEq]
    exact hdec hcwhole hdwhole (le_of_lt (hc.2.trans hd.1))

/-! ### The once-differenced reciprocal phase -/

/-- A forward difference with positive increment `r`. -/
def onceDiff (f : ℝ → ℝ) (r t : ℝ) : ℝ :=
  f (t + r) - f t

/-- The mean value theorem expresses a forward difference using a derivative
at an intermediate point. -/
lemma onceDiff_eq_mul_deriv (f f' : ℝ → ℝ) {t r : ℝ} (hr : 0 < r)
    (hf : ∀ u ∈ Icc t (t + r), HasDerivAt f (f' u) u) :
    ∃ ξ ∈ Ioo t (t + r), onceDiff f r t = r * f' ξ := by
  have hcont : ContinuousOn f (Icc t (t + r)) :=
    fun u hu ↦ (hf u hu).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξSlope⟩ := exists_hasDerivAt_eq_slope f f'
    (by linarith : t < t + r) hcont (fun u hu ↦ hf u (Ioo_subset_Icc_self hu))
  refine ⟨ξ, hξ, ?_⟩
  have hr0 : t + r - t = r := by ring
  rw [hr0] at hξSlope
  have hEq := (eq_div_iff (ne_of_gt hr)).mp hξSlope
  dsimp [onceDiff]
  nlinarith

/-- Differentiating a forward difference commutes with taking the forward
difference. -/
lemma hasDerivAt_onceDiff (f f' : ℝ → ℝ) (r t : ℝ)
    (h0 : HasDerivAt f (f' t) t)
    (hr : HasDerivAt f (f' (t + r)) (t + r)) :
    HasDerivAt (onceDiff f r) (onceDiff f' r t) t := by
  have hshift : HasDerivAt (fun u : ℝ ↦ f (u + r)) (f' (t + r)) t := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      hr.comp t ((hasDerivAt_id t).add_const r)
  change HasDerivAt ((fun u : ℝ ↦ f (u + r)) - f) (f' (t + r) - f' t) t
  exact hshift.sub h0

/-- The once-differenced reciprocal phase `x/(t+r) - x/t`. -/
def onceDiffReciprocal (x r t : ℝ) : ℝ :=
  onceDiff (reciprocalPhase x) r t

/-! ### The twice-differenced reciprocal phase -/

/-- The mixed forward difference with positive increments `r` and `s`. -/
def twiceDiff (f : ℝ → ℝ) (r s t : ℝ) : ℝ :=
  (f (t + r + s) - f (t + r)) - (f (t + s) - f t)

/-- Two applications of the mean value theorem express a mixed difference in
terms of a second derivative at an intermediate point. -/
lemma twiceDiff_eq_mul_secondDeriv
    (f f' f'' : ℝ → ℝ) {t r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hf : ∀ u ∈ Icc t (t + r + s), HasDerivAt f (f' u) u)
    (hf' : ∀ u ∈ Icc t (t + r + s), HasDerivAt f' (f'' u) u) :
    ∃ ξ ∈ Ioo t (t + r + s), twiceDiff f r s t = r * s * f'' ξ := by
  let h : ℝ → ℝ := fun u ↦ f (u + s) - f u
  let h' : ℝ → ℝ := fun u ↦ f' (u + s) - f' u
  have hh : ∀ u ∈ Icc t (t + r), HasDerivAt h (h' u) u := by
    intro u hu
    have hu0 : u ∈ Icc t (t + r + s) := by
      exact ⟨hu.1, hu.2.trans (by linarith)⟩
    have hus : u + s ∈ Icc t (t + r + s) := by
      exact ⟨hu.1.trans (by linarith), by linarith [hu.2]⟩
    have hshift : HasDerivAt (fun v : ℝ ↦ f (v + s)) (f' (u + s)) u :=
      by simpa only [Function.comp_def, id_eq, mul_one] using
        (hf (u + s) hus).comp u ((hasDerivAt_id u).add_const s)
    change HasDerivAt ((fun v : ℝ ↦ f (v + s)) - f) (f' (u + s) - f' u) u
    exact hshift.sub (hf u hu0)
  have hcont : ContinuousOn h (Icc t (t + r)) :=
    fun u hu ↦ (hh u hu).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcSlope⟩ := exists_hasDerivAt_eq_slope h h'
    (by linarith : t < t + r) hcont (fun u hu ↦ hh u (Ioo_subset_Icc_self hu))
  have hc0 : c ∈ Icc t (t + r + s) := by
    exact ⟨hc.1.le, hc.2.le.trans (by linarith)⟩
  have hcs : c + s ∈ Icc t (t + r + s) := by
    exact ⟨hc.1.le.trans (by linarith), by linarith [hc.2]⟩
  have hprimeDeriv : ∀ u ∈ Icc c (c + s), HasDerivAt f' (f'' u) u := by
    intro u hu
    apply hf' u
    exact ⟨hc.1.le.trans hu.1, hu.2.trans (by linarith [hc.2])⟩
  have hprimeCont : ContinuousOn f' (Icc c (c + s)) :=
    fun u hu ↦ (hprimeDeriv u hu).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξSlope⟩ := exists_hasDerivAt_eq_slope f' f''
    (by linarith : c < c + s) hprimeCont
    (fun u hu ↦ hprimeDeriv u (Ioo_subset_Icc_self hu))
  refine ⟨ξ, ?_, ?_⟩
  · exact ⟨hc.1.trans hξ.1, hξ.2.trans (by linarith [hc.2])⟩
  · dsimp [h, h'] at hcSlope
    rw [show t + r + s = (t + r) + s by ring] at hcSlope
    dsimp [twiceDiff]
    have hr0 : t + r - t = r := by ring
    have hs0 : c + s - c = s := by ring
    rw [hr0] at hcSlope
    rw [hs0] at hξSlope
    have hcEq := (eq_div_iff (ne_of_gt hr)).mp hcSlope
    have hξEq := (eq_div_iff (ne_of_gt hs)).mp hξSlope
    nlinarith

/-- Differentiating a mixed difference commutes with taking the mixed
difference. -/
lemma hasDerivAt_twiceDiff (f f' : ℝ → ℝ) (r s t : ℝ)
    (h0 : HasDerivAt f (f' t) t)
    (hr : HasDerivAt f (f' (t + r)) (t + r))
    (hs : HasDerivAt f (f' (t + s)) (t + s))
    (hrs : HasDerivAt f (f' (t + r + s)) (t + r + s)) :
    HasDerivAt (twiceDiff f r s) (twiceDiff f' r s t) t := by
  have shift (c : ℝ) (hc : HasDerivAt f (f' (t + c)) (t + c)) :
      HasDerivAt (fun u : ℝ ↦ f (u + c)) (f' (t + c)) t := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      hc.comp t ((hasDerivAt_id t).add_const c)
  have hrs' : HasDerivAt (fun u : ℝ ↦ f (u + r + s)) (f' (t + r + s)) t := by
    have h := shift (r + s) (by simpa [add_assoc] using hrs)
    convert h using 1
    · ext u
      congr 1
      ring
    · congr 1
      ring
  have hr' := shift r hr
  have hs' := shift s hs
  change HasDerivAt
    (((fun u : ℝ ↦ f (u + r + s)) - (fun u : ℝ ↦ f (u + r))) -
      ((fun u : ℝ ↦ f (u + s)) - f))
    ((f' (t + r + s) - f' (t + r)) - (f' (t + s) - f' t)) t
  exact (hrs'.sub hr').sub (hs'.sub h0)

/-- The twice-differenced reciprocal phase used after the last van der
Corput step. -/
def twiceDiffReciprocal (x r s t : ℝ) : ℝ :=
  twiceDiff (reciprocalPhase x) r s t

private lemma hasDerivAt_reciprocalSquare (x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ x / u ^ 2) (-2 * x / t ^ 3) t := by
  have h := (hasDerivAt_const (x := t) x).div ((hasDerivAt_id t).pow 2)
    (pow_ne_zero 2 ht)
  apply h.congr_deriv
  simp only [Pi.pow_apply, id_eq]
  field_simp [ht]
  ring

private lemma hasDerivAt_reciprocalSquare_deriv (x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ -2 * x / u ^ 3) (6 * x / t ^ 4) t := by
  have h := (hasDerivAt_const (x := t) (-2 * x)).div ((hasDerivAt_id t).pow 3)
    (pow_ne_zero 3 ht)
  apply h.congr_deriv
  simp only [Pi.pow_apply, id_eq]
  field_simp [ht]
  ring

private lemma hasDerivAt_reciprocalSquare_deriv2 (x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ 6 * x / u ^ 4) (-24 * x / t ^ 5) t := by
  have h := (hasDerivAt_const (x := t) (6 * x)).div ((hasDerivAt_id t).pow 4)
    (pow_ne_zero 4 ht)
  apply h.congr_deriv
  simp only [Pi.pow_apply, id_eq]
  field_simp [ht]
  ring

private lemma hasDerivAt_onceDiffReciprocal
    (x r t : ℝ) (ht : 0 < t) (hr : 0 < r) :
    HasDerivAt (onceDiffReciprocal x r)
      (-onceDiff (fun u : ℝ ↦ x / u ^ 2) r t) t := by
  have h0 := hasDerivAt_reciprocalPhase x (ne_of_gt ht)
  have hR := hasDerivAt_reciprocalPhase x (ne_of_gt (by linarith : 0 < t + r))
  have h := hasDerivAt_onceDiff (reciprocalPhase x)
    (fun u : ℝ ↦ -x / u ^ 2) r t h0 hR
  change HasDerivAt (onceDiff (reciprocalPhase x) r)
    (-onceDiff (fun u : ℝ ↦ x / u ^ 2) r t) t
  apply h.congr_deriv
  simp only [onceDiff]
  ring

private lemma neg_onceDiff_reciprocalSquare_eq
    {x r t : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ∃ ξ ∈ Ioo t (t + r),
      -onceDiff (fun u : ℝ ↦ x / u ^ 2) r t = 2 * x * r / ξ ^ 3 := by
  obtain ⟨ξ, hξ, hξEq⟩ := onceDiff_eq_mul_deriv
    (fun u : ℝ ↦ x / u ^ 2) (fun u : ℝ ↦ -2 * x / u ^ 3) hr
    (fun u hu ↦ hasDerivAt_reciprocalSquare x (ne_of_gt (ht.trans_le hu.1)))
  refine ⟨ξ, hξ, ?_⟩
  rw [hξEq]
  ring

private lemma antitoneOn_neg_onceDiff_reciprocalSquare
    {x r a A : ℝ} (hx : 0 < x) (hr : 0 < r) (ha : 0 < a) :
    AntitoneOn (-onceDiff (fun u : ℝ ↦ x / u ^ 2) r) (Icc a A) := by
  let q : ℝ → ℝ := fun u ↦ x / u ^ 2
  let q' : ℝ → ℝ := fun u ↦ -2 * x / u ^ 3
  let D : ℝ → ℝ := -onceDiff q r
  have hd : ∀ t ∈ Icc a A, HasDerivAt D (-onceDiff q' r t) t := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have h0 := hasDerivAt_reciprocalSquare x (ne_of_gt ht0)
    have hR := hasDerivAt_reciprocalSquare x
      (ne_of_gt (by linarith : 0 < t + r))
    exact (hasDerivAt_onceDiff q q' r t h0 hR).neg
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a A)
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hd t (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    have htI : t ∈ Icc a A := interior_subset ht
    have ht0 : 0 < t := ha.trans_le htI.1
    obtain ⟨ξ, hξ, hξEq⟩ := onceDiff_eq_mul_deriv q'
      (fun u : ℝ ↦ 6 * x / u ^ 4) hr
      (fun u hu ↦ hasDerivAt_reciprocalSquare_deriv x
        (ne_of_gt (ht0.trans_le hu.1)))
    rw [hξEq]
    have hξ0 : 0 < ξ := ht0.trans hξ.1
    have hlast : 0 < 6 * x / ξ ^ 4 := by positivity
    exact neg_nonpos.mpr (mul_nonneg hr.le hlast.le)

/-- The concrete first-derivative estimate for a once-differenced reciprocal
phase.  Its derivative lies between `2*x*r/B^3` and `2*x*r/a^3`; the last
hypothesis is the latter endpoint written in the convenient form used in the
one-step van der Corput argument. -/
theorem kusminLandau_onceDiffReciprocal
    (x r a B : ℝ) (N : ℕ)
    (hx : 0 < x) (hr : 0 < r) (ha : 0 < a)
    (hendpoint : a + (N + 1 : ℕ) + r ≤ B)
    (hupper : 4 * x * r / a ^ 3 ≤ 1) :
    ‖∑ n ∈ range (N + 2), expPhase (onceDiffReciprocal x r (a + n))‖ ≤
      B ^ 3 / (2 * x * r) := by
  let F : ℝ → ℝ := onceDiffReciprocal x r
  let D : ℝ → ℝ := -onceDiff (fun u : ℝ ↦ x / u ^ 2) r
  let m : ℝ := 2 * x * r / B ^ 3
  have hC : 0 < 2 * x * r := by positivity
  have hN0 : (0 : ℝ) ≤ (N + 1 : ℕ) := by positivity
  have hB : 0 < B := by nlinarith [hendpoint]
  have hm : 0 < m := by
    dsimp [m]
    exact div_pos hC (pow_pos hB 3)
  have hhalf : 2 * x * r / a ^ 3 ≤ 1 / 2 := by
    rw [show 2 * x * r / a ^ 3 = (4 * x * r / a ^ 3) / 2 by ring]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [hupper]
  have hF : ∀ t ∈ Icc a (a + (N + 1 : ℕ)), HasDerivAt F (D t) t := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    change HasDerivAt F (-onceDiff (fun u : ℝ ↦ x / u ^ 2) r t) t
    simpa only [F] using hasDerivAt_onceDiffReciprocal x r t ht0 hr
  have hbounds : ∀ t ∈ Icc a (a + (N + 1 : ℕ)),
      m ≤ deriv F t ∧ deriv F t ≤ 1 / 2 := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    obtain ⟨ξ, hξ, hξEq⟩ := neg_onceDiff_reciprocalSquare_eq
      (x := x) (r := r) (t := t) ht0 hr
    have haξ : a < ξ := ht.1.trans_lt hξ.1
    have htB : t + r ≤ B := by linarith [ht.2, hendpoint]
    have hξB : ξ < B := hξ.2.trans_le htB
    have hξ0 : 0 < ξ := ha.trans haξ
    have ha3 : 0 < a ^ 3 := pow_pos ha 3
    have hξ3 : 0 < ξ ^ 3 := pow_pos hξ0 3
    have hB3 : 0 < B ^ 3 := pow_pos hB 3
    have haξ3 : a ^ 3 ≤ ξ ^ 3 := by
      gcongr
    have hξB3 : ξ ^ 3 ≤ B ^ 3 := by
      gcongr
    rw [(hF t ht).deriv]
    change m ≤ -onceDiff (fun u : ℝ ↦ x / u ^ 2) r t ∧
      -onceDiff (fun u : ℝ ↦ x / u ^ 2) r t ≤ 1 / 2
    rw [hξEq]
    constructor
    · dsimp [m]
      apply (div_le_div_iff₀ hB3 hξ3).2
      exact mul_le_mul_of_nonneg_left hξB3 hC.le
    · exact (div_le_div_of_nonneg_left hC.le ha3 haξ3).trans hhalf
  have hantiD : AntitoneOn D (Icc a (a + (N + 1 : ℕ))) := by
    simpa only [D] using
      (antitoneOn_neg_onceDiff_reciprocalSquare
        (A := a + (N + 1 : ℕ)) hx hr ha)
  have hanti : AntitoneOn (deriv F) (Icc a (a + (N + 1 : ℕ))) := by
    intro p hp q hq hpq
    rw [(hF p hp).deriv, (hF q hq).deriv]
    exact hantiD hp hq hpq
  have hKL := kusminLandau_of_deriv_monotone_or_antitone F a hm N
    (fun t ht ↦ (hF t ht).differentiableAt.differentiableWithinAt)
    hbounds (Or.inr hanti)
  calc
    ‖∑ n ∈ range (N + 2), expPhase (onceDiffReciprocal x r (a + n))‖ ≤ 1 / m := by
      simpa only [F] using hKL
    _ = B ^ 3 / (2 * x * r) := by
      dsimp [m]
      field_simp [ne_of_gt hC, ne_of_gt hB]

private lemma hasDerivAt_neg_twiceDiffReciprocal
    (x r s t : ℝ) (ht : 0 < t) (hr : 0 < r) (hs : 0 < s) :
    HasDerivAt (fun u : ℝ ↦ -twiceDiffReciprocal x r s u)
      (twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s t) t := by
  have h0 := hasDerivAt_reciprocalPhase x (ne_of_gt ht)
  have hR := hasDerivAt_reciprocalPhase x (ne_of_gt (by linarith : 0 < t + r))
  have hS := hasDerivAt_reciprocalPhase x (ne_of_gt (by linarith : 0 < t + s))
  have hRS := hasDerivAt_reciprocalPhase x
    (ne_of_gt (by linarith : 0 < t + r + s))
  have h := (hasDerivAt_twiceDiff (reciprocalPhase x)
    (fun u : ℝ ↦ -x / u ^ 2) r s t h0 hR hS hRS).neg
  change HasDerivAt (-(twiceDiff (reciprocalPhase x) r s))
    (twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s t) t
  apply h.congr_deriv
  simp only [twiceDiff]
  ring

private lemma twiceDiff_reciprocalSquare_eq
    {x r s t : ℝ} (ht : 0 < t) (hr : 0 < r) (hs : 0 < s) :
    ∃ ξ ∈ Ioo t (t + r + s),
      twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s t = 6 * x * r * s / ξ ^ 4 := by
  obtain ⟨ξ, hξ, hξEq⟩ := twiceDiff_eq_mul_secondDeriv
    (fun u : ℝ ↦ x / u ^ 2) (fun u : ℝ ↦ -2 * x / u ^ 3)
    (fun u : ℝ ↦ 6 * x / u ^ 4) hr hs
    (fun u hu ↦ hasDerivAt_reciprocalSquare x (ne_of_gt (ht.trans_le hu.1)))
    (fun u hu ↦ hasDerivAt_reciprocalSquare_deriv x (ne_of_gt (ht.trans_le hu.1)))
  refine ⟨ξ, hξ, ?_⟩
  rw [hξEq]
  ring

private lemma antitoneOn_twiceDiff_reciprocalSquare
    {x r s a A : ℝ} (hx : 0 < x) (hr : 0 < r) (hs : 0 < s) (ha : 0 < a) :
    AntitoneOn (twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s) (Icc a A) := by
  let q : ℝ → ℝ := fun u ↦ x / u ^ 2
  let q' : ℝ → ℝ := fun u ↦ -2 * x / u ^ 3
  have hd : ∀ t ∈ Icc a A, HasDerivAt (twiceDiff q r s) (twiceDiff q' r s t) t := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    apply hasDerivAt_twiceDiff q q' r s t
    · exact hasDerivAt_reciprocalSquare x (ne_of_gt ht0)
    · exact hasDerivAt_reciprocalSquare x (ne_of_gt (by linarith : 0 < t + r))
    · exact hasDerivAt_reciprocalSquare x (ne_of_gt (by linarith : 0 < t + s))
    · exact hasDerivAt_reciprocalSquare x
        (ne_of_gt (by linarith : 0 < t + r + s))
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a A)
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hd t (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    have htI : t ∈ Icc a A := interior_subset ht
    have ht0 : 0 < t := ha.trans_le htI.1
    obtain ⟨ξ, hξ, hξEq⟩ := twiceDiff_eq_mul_secondDeriv q'
      (fun u : ℝ ↦ 6 * x / u ^ 4) (fun u : ℝ ↦ -24 * x / u ^ 5) hr hs
      (fun u hu ↦ hasDerivAt_reciprocalSquare_deriv x
        (ne_of_gt (ht0.trans_le hu.1)))
      (fun u hu ↦ hasDerivAt_reciprocalSquare_deriv2 x
        (ne_of_gt (ht0.trans_le hu.1)))
    rw [hξEq]
    have hξ0 : 0 < ξ := ht0.trans hξ.1
    have hlast : -24 * x / ξ ^ 5 < 0 := by
      exact div_neg_of_neg_of_pos (by nlinarith [hx]) (pow_pos hξ0 5)
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hr.le hs.le) hlast.le

/-- The concrete first-derivative estimate for the twice-differenced
reciprocal phase.  This is the terminal Kusmin--Landau estimate needed in the
two-step van der Corput argument of Granville--Ramaré, Proposition 8.2. -/
theorem kusminLandau_twiceDiffReciprocal
    (x r s a B : ℝ) (N : ℕ)
    (hx : 0 < x) (hr : 0 < r) (hs : 0 < s) (ha : 0 < a)
    (hendpoint : a + (N + 1 : ℕ) + r + s ≤ B)
    (hhalf : 6 * x * r * s / a ^ 4 ≤ 1 / 2) :
    ‖∑ n ∈ range (N + 2),
        expPhase (-twiceDiffReciprocal x r s (a + n))‖ ≤
      B ^ 4 / (6 * x * r * s) := by
  let F : ℝ → ℝ := fun t ↦ -twiceDiffReciprocal x r s t
  let D : ℝ → ℝ := twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s
  let m : ℝ := 6 * x * r * s / B ^ 4
  have hC : 0 < 6 * x * r * s := by positivity
  have hN0 : (0 : ℝ) ≤ (N + 1 : ℕ) := by positivity
  have hB : 0 < B := by nlinarith [hendpoint]
  have hm : 0 < m := by
    dsimp [m]
    exact div_pos hC (pow_pos hB 4)
  have hF : ∀ t ∈ Icc a (a + (N + 1 : ℕ)), HasDerivAt F (D t) t := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    simpa only [F, D] using hasDerivAt_neg_twiceDiffReciprocal x r s t ht0 hr hs
  have hbounds : ∀ t ∈ Icc a (a + (N + 1 : ℕ)),
      m ≤ deriv F t ∧ deriv F t ≤ 1 / 2 := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    obtain ⟨ξ, hξ, hξEq⟩ := twiceDiff_reciprocalSquare_eq
      (x := x) (r := r) (s := s) (t := t) ht0 hr hs
    have haξ : a < ξ := ht.1.trans_lt hξ.1
    have htB : t + r + s ≤ B := by linarith [ht.2, hendpoint]
    have hξB : ξ < B := hξ.2.trans_le htB
    have hξ0 : 0 < ξ := ha.trans haξ
    have ha4 : 0 < a ^ 4 := pow_pos ha 4
    have hξ4 : 0 < ξ ^ 4 := pow_pos hξ0 4
    have hB4 : 0 < B ^ 4 := pow_pos hB 4
    have haξ4 : a ^ 4 ≤ ξ ^ 4 := by gcongr
    have hξB4 : ξ ^ 4 ≤ B ^ 4 := by gcongr
    rw [(hF t ht).deriv]
    change m ≤ twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s t ∧
      twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s t ≤ 1 / 2
    rw [hξEq]
    constructor
    · dsimp [m]
      apply (div_le_div_iff₀ hB4 hξ4).2
      exact mul_le_mul_of_nonneg_left hξB4 hC.le
    · exact (div_le_div_of_nonneg_left hC.le ha4 haξ4).trans hhalf
  have hantiD : AntitoneOn D (Icc a (a + (N + 1 : ℕ))) := by
    simpa only [D] using
      (antitoneOn_twiceDiff_reciprocalSquare
        (A := a + (N + 1 : ℕ)) hx hr hs ha)
  have hanti : AntitoneOn (deriv F) (Icc a (a + (N + 1 : ℕ))) := by
    intro p hp q hq hpq
    rw [(hF p hp).deriv, (hF q hq).deriv]
    exact hantiD hp hq hpq
  have hKL := kusminLandau_of_deriv_monotone_or_antitone F a hm N
    (fun t ht ↦ (hF t ht).differentiableAt.differentiableWithinAt)
    hbounds (Or.inr hanti)
  calc
    ‖∑ n ∈ range (N + 2),
        expPhase (-twiceDiffReciprocal x r s (a + n))‖ ≤ 1 / m := by
      simpa only [F] using hKL
    _ = B ^ 4 / (6 * x * r * s) := by
      dsimp [m]
      field_simp [ne_of_gt hC, ne_of_gt hB]

/-- Direct first-derivative estimate for the negative reciprocal phase.  The
minus sign makes the derivative positive; its decrease is exactly the
antitone branch of the calculus-facing Kusmin--Landau theorem. -/
theorem kusminLandau_neg_reciprocalPhase
    (x a B : ℝ) (N : ℕ) (hx : 0 < x) (ha : 0 < a)
    (hendpoint : a + (N + 1 : ℕ) ≤ B)
    (hhalf : x / a ^ 2 ≤ 1 / 2) :
    ‖∑ n ∈ range (N + 2), expPhase (-reciprocalPhase x (a + n))‖ ≤ B ^ 2 / x := by
  let F : ℝ → ℝ := -(reciprocalPhase x)
  let D : ℝ → ℝ := fun t ↦ x / t ^ 2
  let m : ℝ := x / B ^ 2
  have hN0 : (0 : ℝ) ≤ (N + 1 : ℕ) := by positivity
  have hB : 0 < B := by nlinarith [hendpoint]
  have hm : 0 < m := by
    dsimp [m]
    exact div_pos hx (pow_pos hB 2)
  have hF : ∀ t ∈ Icc a (a + (N + 1 : ℕ)), HasDerivAt F (D t) t := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have h := (hasDerivAt_reciprocalPhase x (ne_of_gt ht0)).neg
    change HasDerivAt (-(reciprocalPhase x)) (x / t ^ 2) t
    exact h.congr_deriv (by ring)
  have hbounds : ∀ t ∈ Icc a (a + (N + 1 : ℕ)),
      m ≤ deriv F t ∧ deriv F t ≤ 1 / 2 := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have htB : t ≤ B := by linarith [ht.2, hendpoint]
    have ht2 : 0 < t ^ 2 := pow_pos ht0 2
    have ha2 : 0 < a ^ 2 := pow_pos ha 2
    have hB2 : 0 < B ^ 2 := pow_pos hB 2
    have hat2 : a ^ 2 ≤ t ^ 2 := by
      gcongr
      exact ht.1
    have htB2 : t ^ 2 ≤ B ^ 2 := by gcongr
    rw [(hF t ht).deriv]
    constructor
    · dsimp [m, D]
      apply (div_le_div_iff₀ hB2 ht2).2
      exact mul_le_mul_of_nonneg_left htB2 hx.le
    · dsimp [D]
      exact (div_le_div_of_nonneg_left hx.le ha2 hat2).trans hhalf
  have hantiD : AntitoneOn D (Icc a (a + (N + 1 : ℕ))) := by
    have hD : ∀ t ∈ Icc a (a + (N + 1 : ℕ)),
        HasDerivAt D (-2 * x / t ^ 3) t := by
      intro t ht
      exact hasDerivAt_reciprocalSquare x (ne_of_gt (ha.trans_le ht.1))
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t ht ↦ (hD t ht).continuousAt.continuousWithinAt)
    · intro t ht
      exact (hD t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 < t := ha.trans_le (interior_subset ht).1
      exact (div_neg_of_neg_of_pos (by nlinarith [hx]) (pow_pos ht0 3)).le
  have hanti : AntitoneOn (deriv F) (Icc a (a + (N + 1 : ℕ))) := by
    intro p hp q hq hpq
    rw [(hF p hp).deriv, (hF q hq).deriv]
    exact hantiD hp hq hpq
  have hKL := kusminLandau_of_deriv_monotone_or_antitone F a hm N
    (fun t ht ↦ (hF t ht).differentiableAt.differentiableWithinAt)
    hbounds (Or.inr hanti)
  calc
    ‖∑ n ∈ range (N + 2), expPhase (-reciprocalPhase x (a + n))‖ ≤ 1 / m := by
      simpa only [F, Pi.neg_apply] using hKL
    _ = B ^ 2 / x := by
      dsimp [m]
      field_simp [ne_of_gt hx, ne_of_gt hB]

/-- Direct reciprocal-phase estimate in the positive-sign convention.  It is
equivalent to `kusminLandau_neg_reciprocalPhase` by complex conjugation. -/
theorem kusminLandau_reciprocalPhase
    (x a B : ℝ) (N : ℕ) (hx : 0 < x) (ha : 0 < a)
    (hendpoint : a + (N + 1 : ℕ) ≤ B)
    (hhalf : x / a ^ 2 ≤ 1 / 2) :
    ‖∑ n ∈ range (N + 2), expPhase (reciprocalPhase x (a + n))‖ ≤ B ^ 2 / x := by
  have hneg := kusminLandau_neg_reciprocalPhase x a B N hx ha hendpoint hhalf
  have hstar :
      (starRingEnd ℂ) (∑ n ∈ range (N + 2), expPhase (reciprocalPhase x (a + n))) =
        ∑ n ∈ range (N + 2), expPhase (-reciprocalPhase x (a + n)) := by
    rw [map_sum]
    apply sum_congr rfl
    intro n hn
    exact star_expPhase _
  calc
    ‖∑ n ∈ range (N + 2), expPhase (reciprocalPhase x (a + n))‖ =
        ‖(starRingEnd ℂ)
          (∑ n ∈ range (N + 2), expPhase (reciprocalPhase x (a + n)))‖ := by
      simpa using
        (Complex.norm_conj
          (∑ n ∈ range (N + 2), expPhase (reciprocalPhase x (a + n)))).symm
    _ = ‖∑ n ∈ range (N + 2), expPhase (-reciprocalPhase x (a + n))‖ := by
      rw [hstar]
    _ ≤ B ^ 2 / x := hneg

end

end Erdos175

#print axioms Erdos175.kusminLandau_discrete_of_monotone_or_antitone
#print axioms Erdos175.kusminLandau_of_deriv_monotone_or_antitone
#print axioms Erdos175.kusminLandau_twiceDiffReciprocal
#print axioms Erdos175.kusminLandau_onceDiffReciprocal
#print axioms Erdos175.kusminLandau_neg_reciprocalPhase
#print axioms Erdos175.kusminLandau_reciprocalPhase
