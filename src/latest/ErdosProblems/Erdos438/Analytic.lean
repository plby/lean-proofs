import Mathlib

open Filter
open scoped Pointwise

namespace Erdos587

/-- The standard phase `e(x) = exp(2πix)`. -/
noncomputable def phase (x : ℝ) : ℂ :=
  Real.fourierChar x

@[simp] lemma phase_zero : phase 0 = 1 := by
  simp [phase, AddChar.map_zero_eq_one]

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  change ((Real.fourierChar (x + y) : Circle) : ℂ) =
    ((Real.fourierChar x : Circle) : ℂ) * Real.fourierChar y
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

lemma phase_neg (x : ℝ) : phase (-x) = starRingEnd ℂ (phase x) := by
  change ((Real.fourierChar (-x) : Circle) : ℂ) =
    starRingEnd ℂ ((Real.fourierChar x : Circle) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

@[simp] lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 :=
  Circle.norm_coe _

lemma phase_sub (x y : ℝ) :
    phase (x - y) = phase x * starRingEnd ℂ (phase y) := by
  rw [sub_eq_add_neg, phase_add, phase_neg]

lemma phase_nat_mul (x : ℝ) (n : ℕ) : phase (n * x) = phase x ^ n := by
  change ((Real.fourierChar (n * x) : Circle) : ℂ) =
    ((Real.fourierChar x : Circle) : ℂ) ^ n
  rw [show (n : ℝ) * x = n • x by simp, AddChar.map_nsmul_eq_pow, Circle.coe_pow]

/-- Differencing a quadratic phase produces a linear phase. -/
lemma quadratic_phase_correlation (α β : ℝ) (z h : ℕ) :
    phase (α * (z + h : ℕ) ^ 2 + β * (z + h : ℕ)) *
        starRingEnd ℂ (phase (α * (z : ℕ) ^ 2 + β * z)) =
      phase (2 * α * h * z + α * h ^ 2 + β * h) := by
  rw [← phase_sub]
  congr 1
  push_cast
  ring

/-- Distance from a real number to the nearest integer. -/
noncomputable def nearestIntDist (x : ℝ) : ℝ :=
  |x - (round x : ℝ)|

lemma nearestIntDist_nonneg (x : ℝ) : 0 ≤ nearestIntDist x :=
  abs_nonneg _

lemma nearestIntDist_le_half (x : ℝ) : nearestIntDist x ≤ 1 / 2 := by
  exact abs_sub_round x

lemma fourierChar_intCast (n : ℤ) :
    ((Real.fourierChar (n : ℝ) : Circle) : ℂ) = 1 := by
  rw [Real.fourierChar_apply]
  rw [show (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I =
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- The Fourier character only depends on a real number modulo `ℤ`. -/
lemma fourierChar_sub_round (x : ℝ) :
    ((Real.fourierChar (x - (round x : ℝ)) : Circle) : ℂ) =
      Real.fourierChar x := by
  rw [AddChar.map_sub_eq_div, Circle.coe_div, fourierChar_intCast, div_one]

/-- The chord cut out by the Fourier character controls distance to the
nearest integer. -/
lemma four_mul_nearestIntDist_le_norm_fourierChar_sub_one (x : ℝ) :
    4 * nearestIntDist x ≤
      ‖((Real.fourierChar x : Circle) : ℂ) - 1‖ := by
  let y := x - (round x : ℝ)
  have hy : |y| ≤ 1 / 2 := by
    simpa [y] using (abs_sub_round x)
  have harg : |Real.pi * y| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin harg
  have hscale : 2 / Real.pi * |Real.pi * y| = 2 * |y| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp [Real.pi_ne_zero]
  have hreal : 4 * |y| ≤ 2 * |Real.sin (Real.pi * y)| := by
    rw [hscale] at hsin
    nlinarith
  have hnorm :
      ‖((Real.fourierChar y : Circle) : ℂ) - 1‖ =
        2 * |Real.sin (Real.pi * y)| := by
    rw [Real.fourierChar_apply]
    rw [show (↑(2 * Real.pi * y) : ℂ) * Complex.I =
        Complex.I * (2 * Real.pi * y : ℝ) by push_cast; ring]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    norm_num [abs_mul]
    congr 2
    ring
  rw [← fourierChar_sub_round x]
  change 4 * |y| ≤ ‖((Real.fourierChar y : Circle) : ℂ) - 1‖
  rwa [hnorm]

/-- The geometric-sum estimate used after Weyl differencing.  This is the
normed-field form of the familiar `min(N, ‖ω‖⁻¹)` bound. -/
lemma norm_geom_sum_le_min (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, ζ ^ k‖ ≤
      min (N : ℝ) (2 / ‖ζ - 1‖) := by
  apply le_min
  · calc
      ‖∑ k ∈ Finset.range N, ζ ^ k‖
          ≤ ∑ k ∈ Finset.range N, ‖ζ ^ k‖ := norm_sum_le _ _
      _ = N := by simp [norm_pow, hζ]
  · rw [geom_sum_eq hζ1, norm_div]
    have hden : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ1)
    rw [div_le_div_iff_of_pos_right hden]
    calc
      ‖ζ ^ N - 1‖ ≤ ‖ζ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hζ]

/-- Geometric exponential sum bounded by the inverse distance of its
frequency to the nearest integer. -/
lemma norm_fourier_geom_sum_le_min (x : ℝ) (hx : nearestIntDist x ≠ 0) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, (((Real.fourierChar x : Circle) : ℂ) ^ k)‖ ≤
      min (N : ℝ) (1 / (2 * nearestIntDist x)) := by
  let ζ : ℂ := Real.fourierChar x
  have hζnorm : ‖ζ‖ = 1 := Circle.norm_coe _
  have hdistpos : 0 < nearestIntDist x :=
    (nearestIntDist_nonneg x).lt_of_ne' hx
  have hchord : 4 * nearestIntDist x ≤ ‖ζ - 1‖ := by
    exact four_mul_nearestIntDist_le_norm_fourierChar_sub_one x
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hchord
    nlinarith
  have hchordpos : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ1)
  refine (norm_geom_sum_le_min ζ hζnorm hζ1 N).trans ?_
  apply min_le_min le_rfl
  rw [div_le_div_iff₀ hchordpos (by positivity : 0 < 2 * nearestIntDist x)]
  nlinarith

/-- A finite quadratic exponential sum on `[0,N)`. -/
noncomputable def quadraticSum (α β : ℝ) (N : ℕ) : ℂ :=
  ∑ z ∈ Finset.range N, phase (α * (z : ℝ) ^ 2 + β * z)

lemma norm_quadraticSum_le (α β : ℝ) (N : ℕ) :
    ‖quadraticSum α β N‖ ≤ N := by
  calc
    ‖quadraticSum α β N‖ ≤
        ∑ z ∈ Finset.range N, ‖phase (α * (z : ℝ) ^ 2 + β * z)‖ := by
      exact norm_sum_le _ _
    _ = N := by simp

/-- Exact autocorrelation formula for a quadratic phase over a truncated
range. -/
lemma quadratic_correlation_sum (α β : ℝ) (N h : ℕ) :
    (∑ z ∈ Finset.range (N - h),
        phase (α * (z + h : ℕ) ^ 2 + β * (z + h : ℕ)) *
          starRingEnd ℂ (phase (α * (z : ℕ) ^ 2 + β * z))) =
      phase (α * h ^ 2 + β * h) *
        ∑ z ∈ Finset.range (N - h), phase (2 * α * h) ^ z := by
  calc
    (∑ z ∈ Finset.range (N - h),
        phase (α * (z + h : ℕ) ^ 2 + β * (z + h : ℕ)) *
          starRingEnd ℂ (phase (α * (z : ℕ) ^ 2 + β * z))) =
        ∑ z ∈ Finset.range (N - h),
          phase (2 * α * h * z + α * h ^ 2 + β * h) := by
      apply Finset.sum_congr rfl
      intro z _
      exact quadratic_phase_correlation α β z h
    _ = ∑ z ∈ Finset.range (N - h),
          phase (α * h ^ 2 + β * h) * phase ((z : ℝ) * (2 * α * h)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← phase_add]
      congr 1
      ring
    _ = phase (α * h ^ 2 + β * h) *
          ∑ z ∈ Finset.range (N - h), phase ((z : ℝ) * (2 * α * h)) := by
      rw [Finset.mul_sum]
    _ = phase (α * h ^ 2 + β * h) *
          ∑ z ∈ Finset.range (N - h), phase (2 * α * h) ^ z := by
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      exact phase_nat_mul (2 * α * h) z

/-- The autocorrelation is controlled by a geometric sum. -/
lemma norm_quadratic_correlation_sum_le (α β : ℝ) (N h : ℕ)
    (hfreq : nearestIntDist (2 * α * h) ≠ 0) :
    ‖∑ z ∈ Finset.range (N - h),
        phase (α * (z + h : ℕ) ^ 2 + β * (z + h : ℕ)) *
          starRingEnd ℂ (phase (α * (z : ℕ) ^ 2 + β * z))‖ ≤
      min ((N - h : ℕ) : ℝ) (1 / (2 * nearestIntDist (2 * α * h))) := by
  rw [quadratic_correlation_sum, norm_mul, norm_phase, one_mul]
  exact norm_fourier_geom_sum_le_min (2 * α * h) hfreq (N - h)

/-- The harmonic-sum estimate used after grouping correlation frequencies by
their residue modulo the denominator. -/
lemma sum_Icc_inv_natCast_le_one_add_log (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, ((r : ℝ)⁻¹)) ≤ 1 + Real.log n := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast] using harmonic_le_one_add_log n

/-- Scaled harmonic estimate in the exact form of the nonzero-residue term in
the quadratic Weyl bound. -/
lemma sum_Icc_natCast_div_le (q n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, (q : ℝ) / r) ≤
      q * (1 + Real.log n) := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_Icc_inv_natCast_le_one_add_log n)
    (Nat.cast_nonneg q)

/-- Number of pairs `(m,u)` in the positive box whose product `2*m*u` has a
specified residue.  These are the finite multiplicities in the Weyl estimate. -/
def residuePairCount (q r M N : ℕ) : ℕ :=
  (((Finset.Icc 1 M).product (Finset.Icc 1 N)).filter fun x =>
    (2 * x.1 * x.2) % q = r).card

lemma residuePairCount_le (q r M N : ℕ) :
    residuePairCount q r M N ≤ M * N := by
  calc
    residuePairCount q r M N ≤
        ((Finset.Icc 1 M).product (Finset.Icc 1 N)).card :=
      Finset.card_filter_le _ _
    _ = M * N := by simp

/-- The residue multiplicities partition the entire `(m,u)` box. -/
lemma sum_residuePairCount (q M N : ℕ) (hq : 0 < q) :
    ∑ r ∈ Finset.range q, residuePairCount q r M N = M * N := by
  let s := (Finset.Icc 1 M).product (Finset.Icc 1 N)
  let f : ℕ × ℕ → ℕ := fun x => (2 * x.1 * x.2) % q
  have hmaps : (s : Set (ℕ × ℕ)).MapsTo f (Finset.range q) := by
    intro x _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
  calc
    ∑ r ∈ Finset.range q, residuePairCount q r M N =
        ∑ r ∈ Finset.range q, (s.filter fun x => f x = r).card := by
      rfl
    _ = s.card := (Finset.card_eq_sum_card_fiberwise hmaps).symm
    _ = M * N := by simp [s]

/-- A uniform bound for nonzero residue multiplicities combines with the
harmonic estimate to bound their weighted contribution. -/
lemma weighted_residue_sum_le {c : ℕ → ℕ} {B q n : ℕ}
    (hc : ∀ r ∈ Finset.Icc 1 n, (c r : ℝ) ≤ B) :
    (∑ r ∈ Finset.Icc 1 n, (c r : ℝ) * ((q : ℝ) / r)) ≤
      B * (q * (1 + Real.log n)) := by
  calc
    (∑ r ∈ Finset.Icc 1 n, (c r : ℝ) * ((q : ℝ) / r)) ≤
        ∑ r ∈ Finset.Icc 1 n, (B : ℝ) * ((q : ℝ) / r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_right (hc r hr) (by positivity)
    _ = (B : ℝ) * ∑ r ∈ Finset.Icc 1 n, ((q : ℝ) / r) := by
      rw [Finset.mul_sum]
    _ ≤ (B : ℝ) * (q * (1 + Real.log n)) := by
      exact mul_le_mul_of_nonneg_left (sum_Icc_natCast_div_le q n)
        (Nat.cast_nonneg B)

/-- A set contained in `[1,X]` and lying in one residue class modulo `h`
has at most `X / h + 1` elements.  Mapping to the quotient by `h` gives a
short proof which remains useful when the residue class is specified only
implicitly. -/
lemma card_le_div_add_one_of_pairwise_modEq {s : Finset ℕ} {X h : ℕ}
    (hsX : s ⊆ Finset.Icc 1 X) (_hh : 0 < h)
    (hmod : ∀ a ∈ s, ∀ b ∈ s, a ≡ b [MOD h]) :
    s.card ≤ X / h + 1 := by
  let f : ℕ → ℕ := fun a ↦ a / h
  have hinj : Set.InjOn f s := by
    intro a ha b hb hab
    have hrem : a % h = b % h := hmod a ha b hb
    have hda : h * (a / h) + a % h = a := Nat.div_add_mod a h
    have hdb : h * (b / h) + b % h = b := Nat.div_add_mod b h
    dsimp [f] at hab
    calc
      a = h * (a / h) + a % h := hda.symm
      _ = h * (b / h) + b % h := by rw [hab, hrem]
      _ = b := hdb
  have himage : s.image f ⊆ Finset.range (X / h + 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [Finset.mem_range]
    have haX : a ≤ X := (Finset.mem_Icc.mp (hsX ha)).2
    exact Nat.lt_succ_of_le (Nat.div_le_div_right haX)
  calc
    s.card = (s.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (X / h + 1)).card := Finset.card_le_card himage
    _ = X / h + 1 := Finset.card_range _

end Erdos587
