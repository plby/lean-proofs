import ErdosProblems.Erdos228.Kernel

namespace Erdos228.SineIntegralGrid

open scoped Interval
open Real Set MeasureTheory intervalIntegral

noncomputable section

private def lowerSincPolynomial (x : ℝ) : ℝ :=
  1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040

private def geometricLower (x : ℝ) : ℝ :=
  1 - x / Real.pi + (x / Real.pi) ^ 2 - (x / Real.pi) ^ 3

/-- The next alternating Taylor truncation after the estimates in `Kernel`. -/
private lemma sin_taylor_seven_le {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  let q (t : ℝ) := Real.cos t -
    (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)
  have hqderiv (t : ℝ) :
      deriv q t = -Real.sin t + t - t ^ 3 / 6 + t ^ 5 / 120 := by
    simp (disch := fun_prop) [q]
    ring
  have hqmono : MonotoneOn q (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hqderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [Erdos228.Kernel.sin_le_taylor_five ht0]
  have hq {t : ℝ} (ht : 0 ≤ t) :
      1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 ≤ Real.cos t := by
    have h := hqmono (show (0 : ℝ) ∈ Ici 0 by simp)
      (show t ∈ Ici 0 by exact ht) ht
    dsimp [q] at h
    norm_num at h
    linarith
  let f (t : ℝ) := Real.sin t -
    (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040)
  have hfderiv (t : ℝ) :
      deriv f t = Real.cos t -
        (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) := by
    simp (disch := fun_prop) [f]
    ring
  have hfmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hfderiv]
    have ht0 : 0 ≤ t := by
      rw [interior_Ici, mem_Ioi] at ht
      exact ht.le
    linarith [hq ht0]
  have h := hfmono (show (0 : ℝ) ∈ Ici 0 by simp)
    (show x ∈ Ici 0 by exact hx) hx
  dsimp [f] at h
  norm_num at h
  linarith

private lemma lowerSincPolynomial_le_sinc {x : ℝ} (hx : 0 ≤ x) :
    lowerSincPolynomial x ≤ Real.sinc x := by
  obtain rfl | hxpos := hx.eq_or_lt
  · norm_num [lowerSincPolynomial]
  rw [Real.sinc_of_ne_zero hxpos.ne']
  apply (le_div_iff₀ hxpos).2
  have h := sin_taylor_seven_le hxpos.le
  dsimp [lowerSincPolynomial]
  nlinarith

private lemma sinc_nonneg_on_zero_pi {x : ℝ} (hx0 : 0 ≤ x)
    (hxpi : x ≤ Real.pi) : 0 ≤ Real.sinc x := by
  obtain rfl | hxpos := hx0.eq_or_lt
  · simp
  rw [Real.sinc_of_ne_zero hxpos.ne']
  exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi) hx0

private lemma geometricLower_nonneg {x : ℝ} (hx0 : 0 ≤ x)
    (hxpi : x ≤ Real.pi) : 0 ≤ geometricLower x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hu0 : 0 ≤ x / Real.pi := div_nonneg hx0 hpi.le
  have hu1 : x / Real.pi ≤ 1 := (div_le_one hpi).2 hxpi
  dsimp [geometricLower]
  nlinarith [sq_nonneg (x / Real.pi)]

private lemma geometricLower_le_weight {x : ℝ} (hx0 : 0 ≤ x)
    (hxpi : x ≤ Real.pi) :
    geometricLower x ≤ Real.pi / (x + Real.pi) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hxpi_pos : 0 < x + Real.pi := add_pos_of_nonneg_of_pos hx0 hpi
  apply (le_div_iff₀ hxpi_pos).2
  dsimp [geometricLower]
  field_simp
  ring_nf
  nlinarith [sq_nonneg (x ^ 2)]

private lemma sinc_add_pi_eq_weight (x : ℝ) (hx0 : 0 ≤ x)
    (hxpi : x ≤ Real.pi) :
    Real.sinc x + Real.sinc (x + Real.pi) =
      Real.sinc x * (Real.pi / (x + Real.pi)) := by
  by_cases hx : x = 0
  · subst x
    simp [Real.sinc_of_ne_zero Real.pi_ne_zero]
  have hxpi0 : x + Real.pi ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero hx, Real.sinc_of_ne_zero hxpi0, Real.sin_add_pi]
  field_simp
  ring

private lemma polynomial_pair_le (x : ℝ) (hx : x ∈ Icc (0 : ℝ) Real.pi) :
    lowerSincPolynomial x * geometricLower x ≤
      Real.sinc x + Real.sinc (x + Real.pi) := by
  have hsinc0 := sinc_nonneg_on_zero_pi hx.1 hx.2
  have hpoly := lowerSincPolynomial_le_sinc hx.1
  have hgeom0 := geometricLower_nonneg hx.1 hx.2
  have hweight := geometricLower_le_weight hx.1 hx.2
  rw [sinc_add_pi_eq_weight x hx.1 hx.2]
  exact (mul_le_mul_of_nonneg_right hpoly hgeom0).trans
    (mul_le_mul_of_nonneg_left hweight hsinc0)

private lemma integral_polynomial_pair :
    (∫ x in (0 : ℝ)..Real.pi,
      lowerSincPolynomial x * geometricLower x) =
      -(73 * Real.pi ^ 7) / 12700800 +
        43 * Real.pi ^ 5 / 100800 - 7 * Real.pi ^ 3 / 360 +
          7 * Real.pi / 12 := by
  let F (x : ℝ) :=
    -x ^ 7 / 35280 + x ^ 5 / 600 - x ^ 3 / 18 + x +
    x ^ 8 / (40320 * Real.pi) - x ^ 6 / (720 * Real.pi) +
    x ^ 4 / (24 * Real.pi) - x ^ 2 / (2 * Real.pi) -
    x ^ 9 / (45360 * Real.pi ^ 2) + x ^ 7 / (840 * Real.pi ^ 2) -
    x ^ 5 / (30 * Real.pi ^ 2) + x ^ 3 / (3 * Real.pi ^ 2) +
    x ^ 10 / (50400 * Real.pi ^ 3) - x ^ 8 / (960 * Real.pi ^ 3) +
    x ^ 6 / (36 * Real.pi ^ 3) - x ^ 4 / (4 * Real.pi ^ 3)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F) (f' := fun x => lowerSincPolynomial x * geometricLower x)]
  · dsimp [F]
    field_simp [Real.pi_ne_zero]
    ring
  · intro x hx
    have hdiff : DifferentiableAt ℝ F x := by
      dsimp [F]
      fun_prop
    have hderiv : deriv F x =
        lowerSincPolynomial x * geometricLower x := by
      simp (disch := fun_prop) [F, lowerSincPolynomial, geometricLower]
      field_simp [Real.pi_ne_zero]
      ring
    rw [← hderiv]
    exact hdiff.hasDerivAt
  · exact (by fun_prop : Continuous
      (fun x : ℝ => (1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040) *
        (1 - x / Real.pi + (x / Real.pi) ^ 2 - (x / Real.pi) ^ 3))).intervalIntegrable _ _

private lemma four_thirds_lt_integral_polynomial_pair :
    (4 : ℝ) / 3 < ∫ x in (0 : ℝ)..Real.pi,
      lowerSincPolynomial x * geometricLower x := by
  rw [integral_polynomial_pair]
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi' : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have h3 : Real.pi ^ 3 < (3.15 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hpi' Real.pi_pos.le (by norm_num)
  have h5 : (3.14 : ℝ) ^ 5 < Real.pi ^ 5 :=
    pow_lt_pow_left₀ hpi (by norm_num) (by norm_num)
  have h7 : Real.pi ^ 7 < (3.15 : ℝ) ^ 7 :=
    pow_lt_pow_left₀ hpi' Real.pi_pos.le (by norm_num)
  norm_num at hpi hpi' h3 h5 h7 ⊢
  linarith

/-- The first complete `2π` block of sinc already exceeds `4/3`. -/
theorem four_thirds_lt_sineIntegral_two_pi :
    (4 : ℝ) / 3 < Erdos228.Kernel.sineIntegral (2 * Real.pi) := by
  have hsinc : IntervalIntegrable Real.sinc volume (0 : ℝ) Real.pi :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hsinc' : IntervalIntegrable (fun x : ℝ => Real.sinc (x + Real.pi))
      volume (0 : ℝ) Real.pi :=
    (Real.continuous_sinc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hpoly : IntervalIntegrable
      (fun x : ℝ => lowerSincPolynomial x * geometricLower x)
      volume (0 : ℝ) Real.pi :=
    (by fun_prop : Continuous
      (fun x : ℝ => (1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040) *
        (1 - x / Real.pi + (x / Real.pi) ^ 2 - (x / Real.pi) ^ 3))).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on Real.pi_pos.le hpoly
    (hsinc.add hsinc') polynomial_pair_le
  calc
    (4 : ℝ) / 3 < ∫ x in (0 : ℝ)..Real.pi,
        lowerSincPolynomial x * geometricLower x :=
      four_thirds_lt_integral_polynomial_pair
    _ ≤ ∫ x in (0 : ℝ)..Real.pi,
        (Real.sinc x + Real.sinc (x + Real.pi)) := hmono
    _ = Erdos228.Kernel.sineIntegral (2 * Real.pi) := by
      rw [intervalIntegral.integral_add hsinc hsinc']
      rw [intervalIntegral.integral_comp_add_right Real.sinc Real.pi]
      have hadd := intervalIntegral.integral_add_adjacent_intervals hsinc
        (Real.continuous_sinc.intervalIntegrable Real.pi (2 * Real.pi))
      unfold Erdos228.Kernel.sineIntegral
      convert hadd using 1 <;> ring_nf

private def evenPoint (k : ℕ) : ℝ := (k : ℝ) * (2 * Real.pi)

private lemma evenPoint_nonneg (k : ℕ) : 0 ≤ evenPoint k := by
  exact mul_nonneg (Nat.cast_nonneg k) (by positivity)

private lemma evenPoint_pos {k : ℕ} (hk : 0 < k) : 0 < evenPoint k := by
  dsimp [evenPoint]
  exact mul_pos (by exact_mod_cast hk) (by positivity)

private lemma sin_evenPoint_add (k : ℕ) (x : ℝ) :
    Real.sin (evenPoint k + x) = Real.sin x := by
  rw [add_comm]
  exact Real.sin_add_nat_mul_two_pi x k

private lemma sinc_even_pair_nonneg {k : ℕ} (hk : 0 < k)
    {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    0 ≤ Real.sinc (evenPoint k + x) +
      Real.sinc (evenPoint k + Real.pi + x) := by
  have hc : 0 < evenPoint k := evenPoint_pos hk
  have hcx : 0 < evenPoint k + x := add_pos_of_pos_of_nonneg hc hx0
  have hcxpi : 0 < evenPoint k + Real.pi + x := by positivity
  have hsin : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
  rw [Real.sinc_of_ne_zero hcx.ne', Real.sinc_of_ne_zero hcxpi.ne']
  rw [sin_evenPoint_add]
  have hphase : evenPoint k + Real.pi + x = evenPoint k + (x + Real.pi) := by ring
  rw [hphase, sin_evenPoint_add, Real.sin_add_pi]
  have hden : evenPoint k + x ≤ evenPoint k + (x + Real.pi) := by
    linarith [Real.pi_pos]
  have hrecip := one_div_le_one_div_of_le hcx hden
  calc
    0 ≤ Real.sin x *
        (1 / (evenPoint k + x) - 1 / (evenPoint k + (x + Real.pi))) :=
      mul_nonneg hsin (sub_nonneg.2 hrecip)
    _ = Real.sin x / (evenPoint k + x) +
        -Real.sin x / (evenPoint k + (x + Real.pi)) := by ring

private lemma sinc_odd_pair_nonpos (k : ℕ)
    {x : ℝ} (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    Real.sinc (evenPoint k + Real.pi + x) +
      Real.sinc (evenPoint (k + 1) + x) ≤ 0 := by
  have hfirst : 0 < evenPoint k + Real.pi + x := by
    have := evenPoint_nonneg k
    positivity
  have hsecond : 0 < evenPoint (k + 1) + x := by
    apply add_pos_of_pos_of_nonneg
    · exact evenPoint_pos (Nat.succ_pos k)
    · exact hx0
  have hsin : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
  rw [Real.sinc_of_ne_zero hfirst.ne', Real.sinc_of_ne_zero hsecond.ne']
  have hphase1 : evenPoint k + Real.pi + x = evenPoint k + (x + Real.pi) := by ring
  rw [hphase1, sin_evenPoint_add, Real.sin_add_pi, sin_evenPoint_add]
  have heven : evenPoint (k + 1) = evenPoint k + 2 * Real.pi := by
    simp [evenPoint]
    ring
  have hden : evenPoint k + (x + Real.pi) ≤ evenPoint (k + 1) + x := by
    rw [heven]
    linarith [Real.pi_pos]
  have hfirst' : 0 < evenPoint k + (x + Real.pi) := by
    linarith
  have hrecip := one_div_le_one_div_of_le hfirst' hden
  calc
    -Real.sin x / (evenPoint k + (x + Real.pi)) +
        Real.sin x / (evenPoint (k + 1) + x) =
        Real.sin x *
          (1 / (evenPoint (k + 1) + x) -
            1 / (evenPoint k + (x + Real.pi))) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hsin (sub_nonpos.2 hrecip)

private lemma integral_nonpos_of_nonpos {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : ∀ x ∈ Icc a b, f x ≤ 0) :
    (∫ x in a..b, f x) ≤ 0 := by
  have h := intervalIntegral.integral_nonneg (μ := volume) hab
    (fun x hx => neg_nonneg.2 (hf x hx))
  rw [intervalIntegral.integral_neg] at h
  linarith

private lemma even_full_block_nonneg {k : ℕ} (hk : 0 < k) :
    0 ≤ ∫ x in evenPoint k..evenPoint (k + 1), Real.sinc x := by
  have hs : IntervalIntegrable Real.sinc volume
      (evenPoint k) (evenPoint k + Real.pi) :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hs' : IntervalIntegrable Real.sinc volume
      (evenPoint k + Real.pi) (evenPoint (k + 1)) :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hshift1 := intervalIntegral.integral_comp_add_right Real.sinc (evenPoint k)
    (a := (0 : ℝ)) (b := Real.pi)
  have hshift2 := intervalIntegral.integral_comp_add_right Real.sinc
    (evenPoint k + Real.pi) (a := (0 : ℝ)) (b := Real.pi)
  have hp : 0 ≤ ∫ x in (0 : ℝ)..Real.pi,
      (Real.sinc (evenPoint k + x) +
        Real.sinc (evenPoint k + Real.pi + x)) := by
    apply intervalIntegral.integral_nonneg Real.pi_pos.le
    intro x hx
    exact sinc_even_pair_nonneg hk hx.1 hx.2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hs hs'
  have hi1 : (∫ x in evenPoint k..evenPoint k + Real.pi, Real.sinc x) =
      ∫ x in (0 : ℝ)..Real.pi, Real.sinc (evenPoint k + x) := by
    rw [add_comm (evenPoint k)]
    convert hshift1.symm using 1 <;> ring_nf
  have hi2 : (∫ x in evenPoint k + Real.pi..evenPoint (k + 1), Real.sinc x) =
      ∫ x in (0 : ℝ)..Real.pi, Real.sinc (evenPoint k + Real.pi + x) := by
    convert hshift2.symm using 1 <;> simp [evenPoint] <;> ring_nf
  rw [← hadd]
  rw [hi1, hi2]
  have ha : IntervalIntegrable (fun x : ℝ => Real.sinc (evenPoint k + x))
      volume (0 : ℝ) Real.pi := by
    exact (Real.continuous_sinc.comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hb : IntervalIntegrable
      (fun x : ℝ => Real.sinc (evenPoint k + Real.pi + x))
      volume (0 : ℝ) Real.pi := by
    exact (Real.continuous_sinc.comp
      ((continuous_const.add continuous_const).add continuous_id)).intervalIntegrable _ _
  have hsum := intervalIntegral.integral_add ha hb
  rw [← hsum]
  exact hp

private lemma odd_full_block_nonpos (k : ℕ) :
    (∫ x in evenPoint k + Real.pi..evenPoint (k + 1) + Real.pi,
      Real.sinc x) ≤ 0 := by
  have hs : IntervalIntegrable Real.sinc volume
      (evenPoint k + Real.pi) (evenPoint (k + 1)) :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hs' : IntervalIntegrable Real.sinc volume
      (evenPoint (k + 1)) (evenPoint (k + 1) + Real.pi) :=
    Real.continuous_sinc.intervalIntegrable _ _
  have hshift1 := intervalIntegral.integral_comp_add_right Real.sinc
    (evenPoint k + Real.pi) (a := (0 : ℝ)) (b := Real.pi)
  have hshift2 := intervalIntegral.integral_comp_add_right Real.sinc
    (evenPoint (k + 1)) (a := (0 : ℝ)) (b := Real.pi)
  have hp : (∫ x in (0 : ℝ)..Real.pi,
      (Real.sinc (evenPoint k + Real.pi + x) +
        Real.sinc (evenPoint (k + 1) + x))) ≤ 0 := by
    apply integral_nonpos_of_nonpos Real.pi_pos.le
    intro x hx
    exact sinc_odd_pair_nonpos k hx.1 hx.2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hs hs'
  have hi1 : (∫ x in evenPoint k + Real.pi..evenPoint (k + 1), Real.sinc x) =
      ∫ x in (0 : ℝ)..Real.pi, Real.sinc (evenPoint k + Real.pi + x) := by
    convert hshift1.symm using 1 <;> simp [evenPoint] <;> ring_nf
  have hi2 : (∫ x in evenPoint (k + 1)..evenPoint (k + 1) + Real.pi,
      Real.sinc x) =
      ∫ x in (0 : ℝ)..Real.pi, Real.sinc (evenPoint (k + 1) + x) := by
    rw [add_comm (evenPoint (k + 1))]
    convert hshift2.symm using 1 <;> ring_nf
  rw [← hadd]
  rw [hi1, hi2]
  have ha : IntervalIntegrable
      (fun x : ℝ => Real.sinc (evenPoint k + Real.pi + x))
      volume (0 : ℝ) Real.pi := by
    exact (Real.continuous_sinc.comp
      ((continuous_const.add continuous_const).add continuous_id)).intervalIntegrable _ _
  have hb : IntervalIntegrable
      (fun x : ℝ => Real.sinc (evenPoint (k + 1) + x))
      volume (0 : ℝ) Real.pi := by
    exact (Real.continuous_sinc.comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hsum := intervalIntegral.integral_add ha hb
  rw [← hsum]
  exact hp

private lemma sinc_nonneg_even_half (k : ℕ) {x : ℝ}
    (hlo : evenPoint k ≤ x) (hhi : x ≤ evenPoint k + Real.pi) :
    0 ≤ Real.sinc x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hx0 : 0 ≤ x := (evenPoint_nonneg k).trans hlo
  have ht0 : 0 ≤ x - evenPoint k := sub_nonneg.2 hlo
  have htpi : x - evenPoint k ≤ Real.pi := by linarith
  have hsin_t : 0 ≤ Real.sin (x - evenPoint k) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hphase : evenPoint k + (x - evenPoint k) = x := by ring
  have hsin : Real.sin x = Real.sin (x - evenPoint k) := by
    calc
      Real.sin x = Real.sin (evenPoint k + (x - evenPoint k)) :=
        congrArg Real.sin hphase.symm
      _ = Real.sin (x - evenPoint k) := sin_evenPoint_add _ _
  rw [Real.sinc_of_ne_zero hx, hsin]
  exact div_nonneg hsin_t hx0

private lemma sinc_nonpos_odd_half (k : ℕ) {x : ℝ}
    (hlo : evenPoint k + Real.pi ≤ x) (hhi : x ≤ evenPoint (k + 1)) :
    Real.sinc x ≤ 0 := by
  have hc0 := evenPoint_nonneg k
  have hxpos : 0 < x := lt_of_lt_of_le (by linarith [Real.pi_pos] :
    0 < evenPoint k + Real.pi) hlo
  let t := x - (evenPoint k + Real.pi)
  have ht0 : 0 ≤ t := sub_nonneg.2 hlo
  have heven : evenPoint (k + 1) = evenPoint k + 2 * Real.pi := by
    simp [evenPoint]
    ring
  have htpi : t ≤ Real.pi := by
    dsimp [t]
    rw [heven] at hhi
    linarith
  have hsint : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hphase : x = evenPoint k + (t + Real.pi) := by
    dsimp [t]
    ring
  have hden : 0 ≤ evenPoint k + (t + Real.pi) := by
    rw [← hphase]
    exact hxpos.le
  rw [Real.sinc_of_ne_zero hxpos.ne', hphase, sin_evenPoint_add,
    Real.sin_add_pi]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hsint) hden

private lemma even_partial_block_nonneg {k : ℕ} (hk : 0 < k) {x : ℝ}
    (hlo : evenPoint k ≤ x) (hhi : x ≤ evenPoint (k + 1)) :
    0 ≤ ∫ t in evenPoint k..x, Real.sinc t := by
  by_cases hmid : x ≤ evenPoint k + Real.pi
  · apply intervalIntegral.integral_nonneg (μ := volume) hlo
    intro t ht
    exact sinc_nonneg_even_half k ht.1 (ht.2.trans hmid)
  · have hxmid : evenPoint k + Real.pi ≤ x := le_of_not_ge hmid
    have htail : (∫ t in x..evenPoint (k + 1), Real.sinc t) ≤ 0 := by
      apply integral_nonpos_of_nonpos hhi
      intro t ht
      exact sinc_nonpos_odd_half k (hxmid.trans ht.1) ht.2
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable (evenPoint k) x)
      (Real.continuous_sinc.intervalIntegrable x (evenPoint (k + 1)))
    linarith [even_full_block_nonneg hk]

private lemma odd_partial_block_nonpos (k : ℕ) {x : ℝ}
    (hlo : evenPoint k + Real.pi ≤ x)
    (hhi : x ≤ evenPoint (k + 1) + Real.pi) :
    (∫ t in evenPoint k + Real.pi..x, Real.sinc t) ≤ 0 := by
  by_cases hmid : x ≤ evenPoint (k + 1)
  · apply integral_nonpos_of_nonpos hlo
    intro t ht
    exact sinc_nonpos_odd_half k ht.1 (ht.2.trans hmid)
  · have hxmid : evenPoint (k + 1) ≤ x := le_of_not_ge hmid
    have htail : 0 ≤ ∫ t in x..evenPoint (k + 1) + Real.pi,
        Real.sinc t := by
      apply intervalIntegral.integral_nonneg (μ := volume) hhi
      intro t ht
      exact sinc_nonneg_even_half (k + 1) (hxmid.trans ht.1) ht.2
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable (evenPoint k + Real.pi) x)
      (Real.continuous_sinc.intervalIntegrable x (evenPoint (k + 1) + Real.pi))
    linarith [odd_full_block_nonpos k]

private lemma even_grid_tail_nonneg (k : ℕ) :
    0 ≤ ∫ x in evenPoint 1..evenPoint (k + 1), Real.sinc x := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (evenPoint 1) (evenPoint (k + 1)))
        (Real.continuous_sinc.intervalIntegrable (evenPoint (k + 1))
          (evenPoint (k + 2)))
      have hblock := even_full_block_nonneg (k := k + 1) (Nat.succ_pos k)
      rw [← hadd]
      exact add_nonneg ih hblock

private lemma odd_grid_tail_nonpos (k : ℕ) :
    (∫ x in Real.pi..evenPoint k + Real.pi, Real.sinc x) ≤ 0 := by
  induction k with
  | zero => simp [evenPoint]
  | succ k ih =>
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable Real.pi (evenPoint k + Real.pi))
        (Real.continuous_sinc.intervalIntegrable (evenPoint k + Real.pi)
          (evenPoint (k + 1) + Real.pi))
      have hblock := odd_full_block_nonpos k
      rw [← hadd]
      exact add_nonpos ih hblock

private lemma even_tail_nonneg_of_le_fourteen_pi {x : ℝ}
    (hlo : evenPoint 1 ≤ x) (hhi : x ≤ evenPoint 7) :
    0 ≤ ∫ t in evenPoint 1..x, Real.sinc t := by
  have join (k : ℕ) (hk : 0 < k) (hklow : evenPoint k ≤ x)
      (hkhi : x ≤ evenPoint (k + 1)) :
      0 ≤ ∫ t in evenPoint 1..x, Real.sinc t := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable (evenPoint 1) (evenPoint k))
      (Real.continuous_sinc.intervalIntegrable (evenPoint k) x)
    rw [← hadd]
    exact add_nonneg (by simpa [Nat.sub_add_cancel hk] using even_grid_tail_nonneg (k - 1))
      (even_partial_block_nonneg hk hklow hkhi)
  by_cases h2 : x ≤ evenPoint 2
  · exact join 1 (by norm_num) hlo h2
  by_cases h3 : x ≤ evenPoint 3
  · exact join 2 (by norm_num) (le_of_not_ge h2) h3
  by_cases h4 : x ≤ evenPoint 4
  · exact join 3 (by norm_num) (le_of_not_ge h3) h4
  by_cases h5 : x ≤ evenPoint 5
  · exact join 4 (by norm_num) (le_of_not_ge h4) h5
  by_cases h6 : x ≤ evenPoint 6
  · exact join 5 (by norm_num) (le_of_not_ge h5) h6
  exact join 6 (by norm_num) (le_of_not_ge h6) hhi

private lemma odd_tail_nonpos_of_le_fourteen_pi {x : ℝ}
    (hlo : Real.pi ≤ x) (hhi : x ≤ evenPoint 7) :
    (∫ t in Real.pi..x, Real.sinc t) ≤ 0 := by
  have join (k : ℕ) (hklow : evenPoint k + Real.pi ≤ x)
      (hkhi : x ≤ evenPoint (k + 1) + Real.pi) :
      (∫ t in Real.pi..x, Real.sinc t) ≤ 0 := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable Real.pi (evenPoint k + Real.pi))
      (Real.continuous_sinc.intervalIntegrable (evenPoint k + Real.pi) x)
    rw [← hadd]
    exact add_nonpos (odd_grid_tail_nonpos k)
      (odd_partial_block_nonpos k hklow hkhi)
  by_cases h1 : x ≤ evenPoint 1 + Real.pi
  · exact join 0 (by simpa [evenPoint] using hlo) h1
  by_cases h2 : x ≤ evenPoint 2 + Real.pi
  · exact join 1 (le_of_not_ge h1) h2
  by_cases h3 : x ≤ evenPoint 3 + Real.pi
  · exact join 2 (le_of_not_ge h2) h3
  by_cases h4 : x ≤ evenPoint 4 + Real.pi
  · exact join 3 (le_of_not_ge h3) h4
  by_cases h5 : x ≤ evenPoint 5 + Real.pi
  · exact join 4 (le_of_not_ge h4) h5
  by_cases h6 : x ≤ evenPoint 6 + Real.pi
  · exact join 5 (le_of_not_ge h5) h6
  have hlast : x ≤ evenPoint 7 + Real.pi := hhi.trans (le_add_of_nonneg_right Real.pi_pos.le)
  exact join 6 (le_of_not_ge h6) hlast

/-- On the range needed for six grid cells, the sine integral stays in `[0,2]`. -/
theorem sineIntegral_mem_zero_two {x : ℝ} (hx0 : 0 ≤ x)
    (hx14 : x ≤ 14 * Real.pi) :
    Erdos228.Kernel.sineIntegral x ∈ Icc (0 : ℝ) 2 := by
  have hxEven : x ≤ evenPoint 7 := by
    dsimp [evenPoint]
    convert hx14 using 1 <;> ring
  constructor
  · by_cases hxpi : x ≤ Real.pi
    · apply intervalIntegral.integral_nonneg hx0
      intro t ht
      exact sinc_nonneg_on_zero_pi ht.1 (ht.2.trans hxpi)
    by_cases hx2 : x ≤ evenPoint 1
    · have htail : (∫ t in x..evenPoint 1, Real.sinc t) ≤ 0 := by
        apply integral_nonpos_of_nonpos hx2
        intro t ht
        have htpi : Real.pi ≤ t := (le_of_not_ge hxpi).trans ht.1
        exact sinc_nonpos_odd_half 0 (by simpa [evenPoint] using htpi) ht.2
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (0 : ℝ) x)
        (Real.continuous_sinc.intervalIntegrable x (evenPoint 1))
      have hfirst := four_thirds_lt_sineIntegral_two_pi
      unfold Erdos228.Kernel.sineIntegral at hfirst ⊢
      have heq : evenPoint 1 = 2 * Real.pi := by simp [evenPoint]
      rw [heq] at hadd htail
      linarith
    · have htail := even_tail_nonneg_of_le_fourteen_pi (le_of_not_ge hx2) hxEven
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (0 : ℝ) (evenPoint 1))
        (Real.continuous_sinc.intervalIntegrable (evenPoint 1) x)
      have hfirst := four_thirds_lt_sineIntegral_two_pi
      unfold Erdos228.Kernel.sineIntegral at hfirst ⊢
      have heq : evenPoint 1 = 2 * Real.pi := by simp [evenPoint]
      rw [heq] at hadd htail
      linarith
  · by_cases hxpi : x ≤ Real.pi
    · have htail : 0 ≤ ∫ t in x..Real.pi, Real.sinc t := by
        apply intervalIntegral.integral_nonneg hxpi
        intro t ht
        exact sinc_nonneg_on_zero_pi (hx0.trans ht.1) ht.2
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (0 : ℝ) x)
        (Real.continuous_sinc.intervalIntegrable x Real.pi)
      have hpi := Erdos228.Kernel.sineIntegral_pi_lt_two
      unfold Erdos228.Kernel.sineIntegral at hpi ⊢
      linarith
    · have htail := odd_tail_nonpos_of_le_fourteen_pi (le_of_not_ge hxpi) hxEven
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (Real.continuous_sinc.intervalIntegrable (0 : ℝ) Real.pi)
        (Real.continuous_sinc.intervalIntegrable Real.pi x)
      have hpi := Erdos228.Kernel.sineIntegral_pi_lt_two
      unfold Erdos228.Kernel.sineIntegral at hpi ⊢
      linarith

/-- After the first complete block, the sine integral remains above `4/3`. -/
theorem four_thirds_le_sineIntegral_of_two_pi_le {x : ℝ}
    (hx2 : 2 * Real.pi ≤ x) (hx14 : x ≤ 14 * Real.pi) :
    (4 : ℝ) / 3 ≤ Erdos228.Kernel.sineIntegral x := by
  have hlo : evenPoint 1 ≤ x := by simpa [evenPoint] using hx2
  have hhi : x ≤ evenPoint 7 := by
    dsimp [evenPoint]
    convert hx14 using 1 <;> ring
  have htail := even_tail_nonneg_of_le_fourteen_pi hlo hhi
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (Real.continuous_sinc.intervalIntegrable (0 : ℝ) (evenPoint 1))
    (Real.continuous_sinc.intervalIntegrable (evenPoint 1) x)
  have hfirst := four_thirds_lt_sineIntegral_two_pi
  unfold Erdos228.Kernel.sineIntegral at hfirst ⊢
  have heq : evenPoint 1 = 2 * Real.pi := by simp [evenPoint]
  rw [heq] at hadd htail
  linarith

theorem sineIntegral_neg (x : ℝ) :
    Erdos228.Kernel.sineIntegral (-x) = -Erdos228.Kernel.sineIntegral x := by
  unfold Erdos228.Kernel.sineIntegral
  have h := intervalIntegral.integral_comp_neg (f := Real.sinc)
    (a := (0 : ℝ)) (b := x)
  simp only [Real.sinc_neg] at h
  calc
    (∫ y in (0 : ℝ)..-x, Real.sinc y) =
        -(∫ y in -x..(0 : ℝ), Real.sinc y) :=
      intervalIntegral.integral_symm (-x) 0
    _ = -(∫ y in (0 : ℝ)..x, Real.sinc y) := by
      simpa using (congrArg Neg.neg h).symm

/-- Exact affine change of variables for the continuous odd kernel. -/
theorem integral_scaled_sinc_eq_sineIntegral_sub (n : ℕ) (hn : 0 < n)
    (u v theta : ℝ) :
    (∫ x in u..v,
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))) =
      Erdos228.Kernel.sineIntegral (2 * (n : ℝ) * (v - theta)) -
        Erdos228.Kernel.sineIntegral (2 * (n : ℝ) * (u - theta)) := by
  let c : ℝ := 2 * (n : ℝ)
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hcomp := intervalIntegral.integral_comp_mul_add Real.sinc hc (-c * theta)
    (a := u) (b := v)
  have hscale : (∫ x in u..v, c * Real.sinc (c * x + -c * theta)) =
      ∫ y in c * u + -c * theta..c * v + -c * theta, Real.sinc y := by
    rw [intervalIntegral.integral_const_mul]
    rw [hcomp]
    simp [hc]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (Real.continuous_sinc.intervalIntegrable (0 : ℝ) (c * u + -c * theta))
    (Real.continuous_sinc.intervalIntegrable (c * u + -c * theta)
      (c * v + -c * theta))
  unfold Erdos228.Kernel.sineIntegral
  rw [show (∫ x in u..v,
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))) =
      ∫ x in u..v, c * Real.sinc (c * x + -c * theta) by
        congr 1
        funext x
        dsimp [c]
        ring_nf]
  rw [hscale]
  have hu : c * u + -c * theta = c * (u - theta) := by ring
  have hv : c * v + -c * theta = c * (v - theta) := by ring
  rw [hu, hv] at hadd ⊢
  linarith

private lemma four_thirds_le_sineIntegral_add_of_add_eq_two_pi
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u + v = 2 * Real.pi) :
    (4 : ℝ) / 3 ≤ Erdos228.Kernel.sineIntegral u +
      Erdos228.Kernel.sineIntegral v := by
  have hbound (z w : ℝ) (hzpi : Real.pi ≤ z) (hz2 : z ≤ 2 * Real.pi)
      (hw0 : 0 ≤ w) (hw14 : w ≤ 14 * Real.pi) :
      (4 : ℝ) / 3 ≤ Erdos228.Kernel.sineIntegral w +
        Erdos228.Kernel.sineIntegral z := by
    have htail : (∫ t in z..2 * Real.pi, Real.sinc t) ≤ 0 := by
      apply integral_nonpos_of_nonpos hz2
      intro t ht
      exact sinc_nonpos_odd_half 0 (by simpa [evenPoint] using hzpi.trans ht.1)
        (by simpa [evenPoint] using ht.2)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.intervalIntegrable (0 : ℝ) z)
      (Real.continuous_sinc.intervalIntegrable z (2 * Real.pi))
    have hw := sineIntegral_mem_zero_two hw0 hw14
    rcases hw with ⟨hw_nonneg, hw_le⟩
    have hfirst := four_thirds_lt_sineIntegral_two_pi
    unfold Erdos228.Kernel.sineIntegral at hfirst hw_nonneg hw_le ⊢
    linarith
  by_cases hupi : u ≤ Real.pi
  · have hvpi : Real.pi ≤ v := by linarith
    have hv2 : v ≤ 2 * Real.pi := by linarith
    have hu14 : u ≤ 14 * Real.pi := by nlinarith [Real.pi_pos]
    exact hbound v u hvpi hv2 hu hu14
  · have hvpi : v ≤ Real.pi := by linarith
    have hupi' : Real.pi ≤ u := le_of_not_ge hupi
    have hu2 : u ≤ 2 * Real.pi := by linarith
    have hv14 : v ≤ 14 * Real.pi := by nlinarith [Real.pi_pos]
    simpa [add_comm] using hbound u v hupi' hu2 hv hv14

/-- BBMST Lemma 5.8(a) for a nondegenerate grid interval of at most six cells. -/
theorem principal_grid_interval_inside (n : ℕ) (hn : 0 < n)
    (a b : ℤ) (hab : a < b)
    (hshort : (b : ℝ) * Real.pi / n - (a : ℝ) * Real.pi / n ≤
      6 * Real.pi / n)
    {theta : ℝ}
    (htheta : theta ∈ Icc ((a : ℝ) * Real.pi / n)
      ((b : ℝ) * Real.pi / n)) :
    (∫ x in (a : ℝ) * Real.pi / n..(b : ℝ) * Real.pi / n,
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))) ∈
      Icc ((4 : ℝ) / 3) 4 := by
  let L : ℝ := (a : ℝ) * Real.pi / n
  let U : ℝ := (b : ℝ) * Real.pi / n
  let c : ℝ := 2 * (n : ℝ)
  let u : ℝ := c * (theta - L)
  let v : ℝ := c * (U - theta)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := by dsimp [c]; positivity
  have hu : 0 ≤ u := mul_nonneg hc.le (sub_nonneg.2 htheta.1)
  have hv : 0 ≤ v := mul_nonneg hc.le (sub_nonneg.2 htheta.2)
  have huv : u + v = c * (U - L) := by
    dsimp [u, v]
    ring
  have htotal : u + v = 2 * ((b - a : ℤ) : ℝ) * Real.pi := by
    rw [huv]
    dsimp [c, U, L]
    push_cast
    field_simp
  have hsum12 : u + v ≤ 12 * Real.pi := by
    have hm := mul_le_mul_of_nonneg_left hshort hc.le
    calc
      u + v = c * (U - L) := huv
      _ ≤ c * (6 * Real.pi / n) := by simpa [U, L] using hm
      _ = 12 * Real.pi := by
        dsimp [c]
        field_simp
        norm_num
  have hu14 : u ≤ 14 * Real.pi := by
    nlinarith [Real.pi_pos]
  have hv14 : v ≤ 14 * Real.pi := by
    nlinarith [Real.pi_pos]
  have huMem := sineIntegral_mem_zero_two hu hu14
  have hvMem := sineIntegral_mem_zero_two hv hv14
  rcases huMem with ⟨huSi0, huSi2⟩
  rcases hvMem with ⟨hvSi0, hvSi2⟩
  have hlower : (4 : ℝ) / 3 ≤ Erdos228.Kernel.sineIntegral u +
      Erdos228.Kernel.sineIntegral v := by
    by_cases hgap : b - a = 1
    · apply four_thirds_le_sineIntegral_add_of_add_eq_two_pi hu hv
      rw [htotal, hgap]
      norm_num
    · have hgap2 : (2 : ℤ) ≤ b - a := by omega
      have htotal4 : 4 * Real.pi ≤ u + v := by
        rw [htotal]
        have hcast : (2 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by exact_mod_cast hgap2
        nlinarith [Real.pi_pos]
      by_cases hu2 : 2 * Real.pi ≤ u
      · have hmain := four_thirds_le_sineIntegral_of_two_pi_le hu2 hu14
        linarith
      · have hv2 : 2 * Real.pi ≤ v := by linarith
        have hmain := four_thirds_le_sineIntegral_of_two_pi_le hv2 hv14
        linarith
  have hupper : Erdos228.Kernel.sineIntegral u +
      Erdos228.Kernel.sineIntegral v ≤ 4 := by linarith
  have hid := integral_scaled_sinc_eq_sineIntegral_sub n hn L U theta
  have hL : 2 * (n : ℝ) * (L - theta) = -u := by
    dsimp [c, u]
    ring
  have hU : 2 * (n : ℝ) * (U - theta) = v := by rfl
  dsimp [L, U] at hid ⊢
  rw [hid, hL, hU, sineIntegral_neg]
  constructor <;> linarith

/-- BBMST Lemma 5.8(b), in the near-exterior form used by the interval family.
The closest endpoint is at most one grid cell away. -/
theorem principal_grid_interval_outside_near (n : ℕ) (hn : 0 < n)
    (a b : ℤ) (hab : a < b)
    (hshort : (b : ℝ) * Real.pi / n - (a : ℝ) * Real.pi / n ≤
      6 * Real.pi / n)
    {theta : ℝ}
    (hnear :
      (theta ≤ (a : ℝ) * Real.pi / n ∧
        (a : ℝ) * Real.pi / n - theta ≤ Real.pi / n) ∨
      ((b : ℝ) * Real.pi / n ≤ theta ∧
        theta - (b : ℝ) * Real.pi / n ≤ Real.pi / n)) :
    |∫ x in (a : ℝ) * Real.pi / n..(b : ℝ) * Real.pi / n,
      2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (x - theta))| ≤ 2 := by
  let L : ℝ := (a : ℝ) * Real.pi / n
  let U : ℝ := (b : ℝ) * Real.pi / n
  let c : ℝ := 2 * (n : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := by dsimp [c]; positivity
  have hwidth : c * (U - L) ≤ 12 * Real.pi := by
    have hm := mul_le_mul_of_nonneg_left hshort hc.le
    dsimp [c, U, L] at hm ⊢
    field_simp at hm ⊢
    nlinarith
  have hUL0 : 0 ≤ U - L := by
    have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    dsimp [U, L]
    have hmul : (a : ℝ) * Real.pi ≤ (b : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right habR.le Real.pi_pos.le
    exact sub_nonneg.2 (div_le_div_of_nonneg_right hmul hnR.le)
  have hid := integral_scaled_sinc_eq_sineIntegral_sub n hn L U theta
  rcases hnear with hleft | hright
  · let z : ℝ := c * (L - theta)
    let w : ℝ := c * (U - theta)
    have hz0 : 0 ≤ z := mul_nonneg hc.le (sub_nonneg.2 hleft.1)
    have hzw : w = z + c * (U - L) := by dsimp [z, w]; ring
    have hw0 : 0 ≤ w := by
      rw [hzw]
      exact add_nonneg hz0 (mul_nonneg hc.le hUL0)
    have hz2 : z ≤ 2 * Real.pi := by
      have hm := mul_le_mul_of_nonneg_left hleft.2 hc.le
      dsimp [c, z, L] at hm ⊢
      field_simp at hm ⊢
      nlinarith
    have hw14 : w ≤ 14 * Real.pi := by rw [hzw]; linarith
    have hzMem := sineIntegral_mem_zero_two hz0 (hz2.trans (by nlinarith [Real.pi_pos]))
    have hwMem := sineIntegral_mem_zero_two hw0 hw14
    rcases hzMem with ⟨hzSi0, hzSi2⟩
    rcases hwMem with ⟨hwSi0, hwSi2⟩
    have hL : 2 * (n : ℝ) * (L - theta) = z := by rfl
    have hU : 2 * (n : ℝ) * (U - theta) = w := by rfl
    dsimp [L, U] at hid ⊢
    rw [hid, hL, hU]
    rw [abs_le]
    constructor <;> linarith
  · let z : ℝ := c * (theta - U)
    let w : ℝ := c * (theta - L)
    have hz0 : 0 ≤ z := mul_nonneg hc.le (sub_nonneg.2 hright.1)
    have hzw : w = z + c * (U - L) := by dsimp [z, w]; ring
    have hw0 : 0 ≤ w := by
      rw [hzw]
      exact add_nonneg hz0 (mul_nonneg hc.le hUL0)
    have hz2 : z ≤ 2 * Real.pi := by
      have hm := mul_le_mul_of_nonneg_left hright.2 hc.le
      dsimp [c, z, U] at hm ⊢
      field_simp at hm ⊢
      nlinarith
    have hw14 : w ≤ 14 * Real.pi := by rw [hzw]; linarith
    have hzMem := sineIntegral_mem_zero_two hz0 (hz2.trans (by nlinarith [Real.pi_pos]))
    have hwMem := sineIntegral_mem_zero_two hw0 hw14
    rcases hzMem with ⟨hzSi0, hzSi2⟩
    rcases hwMem with ⟨hwSi0, hwSi2⟩
    have hL : 2 * (n : ℝ) * (L - theta) = -w := by dsimp [c, w]; ring
    have hU : 2 * (n : ℝ) * (U - theta) = -z := by dsimp [c, z]; ring
    dsimp [L, U] at hid ⊢
    rw [hid, hL, hU, sineIntegral_neg z, sineIntegral_neg w]
    rw [abs_le]
    constructor <;> linarith

end

end Erdos228.SineIntegralGrid
