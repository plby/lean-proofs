import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

/-!
# Gaussian cutoffs for Erdős Problem 230

This file develops the elementary real-variable estimates for the normalized
Gaussian cutoff used in the ultraflat-polynomial construction.  The scale is
a positive real number; the cutoff locations and sampling points are natural
numbers, coerced to `ℝ` only at the analytic boundary.
-/

namespace Erdos230.GaussianCutoff

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

/-- The normalized real Gaussian of scale `s`. -/
def phi (s x : ℝ) : ℝ :=
  s⁻¹ * Real.exp (-Real.pi * (x / s) ^ 2)

/-- The Gaussian smoothing of the indicator of `[K, n-K]`. -/
def chi (s : ℝ) (K n : ℕ) (x : ℝ) : ℝ :=
  ∫ y in (K : ℝ)..(n - K : ℕ), phi s (x - y)

lemma phi_eq_exp_neg_mul_sq {s : ℝ} (hs : s ≠ 0) (x : ℝ) :
    phi s x = s⁻¹ * Real.exp (-(Real.pi / s ^ 2) * x ^ 2) := by
  unfold phi
  apply congrArg (fun t : ℝ => s⁻¹ * Real.exp t)
  field_simp [hs]

lemma phi_nonneg {s : ℝ} (hs : 0 < s) (x : ℝ) : 0 ≤ phi s x := by
  exact mul_nonneg (inv_nonneg.mpr hs.le) (Real.exp_pos _).le

lemma phi_pos {s : ℝ} (hs : 0 < s) (x : ℝ) : 0 < phi s x := by
  exact mul_pos (inv_pos.mpr hs) (Real.exp_pos _)

@[simp] lemma phi_neg (s x : ℝ) : phi s (-x) = phi s x := by
  simp only [phi, neg_div, neg_sq]

lemma continuous_phi {s : ℝ} : Continuous (phi s) := by
  unfold phi
  fun_prop

lemma integrable_phi {s : ℝ} (hs : 0 < s) : Integrable (phi s) := by
  have hb : 0 < Real.pi / s ^ 2 := div_pos Real.pi_pos (sq_pos_of_pos hs)
  have h := (integrable_exp_neg_mul_sq hb).const_mul s⁻¹
  convert h using 1
  funext x
  exact phi_eq_exp_neg_mul_sq hs.ne' x

/-- The normalization was chosen so that the Gaussian has total mass one. -/
theorem integral_phi {s : ℝ} (hs : 0 < s) : ∫ x : ℝ, phi s x = 1 := by
  have hfun : phi s = fun x : ℝ =>
      s⁻¹ * Real.exp (-(Real.pi / s ^ 2) * x ^ 2) := by
    funext x
    exact phi_eq_exp_neg_mul_sq hs.ne' x
  rw [hfun, integral_const_mul, integral_gaussian]
  have hquot : Real.pi / (Real.pi / s ^ 2) = s ^ 2 := by
    field_simp [Real.pi_ne_zero, hs.ne']
  rw [hquot, Real.sqrt_sq_eq_abs, abs_of_pos hs]
  field_simp

/-- Translation and reflection do not change the total Gaussian mass. -/
theorem integral_phi_sub_left {s x : ℝ} (hs : 0 < s) :
    ∫ y : ℝ, phi s (x - y) = 1 := by
  rw [(volume : Measure ℝ).measurePreserving_sub_left x |>.integral_comp
    (Homeomorph.subLeft x).isClosedEmbedding.measurableEmbedding]
  exact integral_phi hs

/-- The Gaussian upper tail, beginning at `r`. -/
def gaussianTail (s r : ℝ) : ℝ :=
  ∫ x in Ioi r, phi s x

lemma integrable_phi_sub_left {s x : ℝ} (hs : 0 < s) :
    Integrable (fun y : ℝ => phi s (x - y)) := by
  exact ((volume : Measure ℝ).measurePreserving_sub_left x).integrable_comp_emb
      (Homeomorph.subLeft x).isClosedEmbedding.measurableEmbedding |>.2 (integrable_phi hs)

lemma cutoff_endpoints_order {K n : ℕ} (hKn : 2 * K ≤ n) :
    (K : ℝ) ≤ (n - K : ℕ) := by
  norm_cast
  omega

theorem chi_nonneg {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) (x : ℝ) :
    0 ≤ chi s K n x := by
  unfold chi
  apply intervalIntegral.integral_nonneg_of_forall (cutoff_endpoints_order hKn)
  exact fun y => phi_nonneg hs (x - y)

theorem chi_le_one {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) (x : ℝ) :
    chi s K n x ≤ 1 := by
  rw [chi, intervalIntegral.integral_of_le (cutoff_endpoints_order hKn)]
  calc
    (∫ y in Ioc (K : ℝ) (n - K : ℕ), phi s (x - y)) ≤
        ∫ y : ℝ, phi s (x - y) := by
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun y => phi_nonneg hs (x - y))
        (integrable_phi_sub_left hs)
    _ = 1 := integral_phi_sub_left hs

theorem chi_mem_Icc {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) (x : ℝ) :
    chi s K n x ∈ Icc 0 1 :=
  ⟨chi_nonneg hs hKn x, chi_le_one hs hKn x⟩

lemma gaussianTail_nonneg {s : ℝ} (hs : 0 < s) (r : ℝ) :
    0 ≤ gaussianTail s r := by
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => phi_nonneg hs x)

lemma integrableOn_phi_Ioi {s : ℝ} (hs : 0 < s) (r : ℝ) :
    IntegrableOn (phi s) (Ioi r) :=
  (integrable_phi hs).integrableOn

lemma integral_phi_Iic_neg_eq_tail {s : ℝ} (r : ℝ) :
    (∫ x in Iic (-r), phi s x) = gaussianTail s r := by
  rw [gaussianTail]
  calc
    (∫ x in Iic (-r), phi s x) = ∫ x in Iic (-r), phi s (-x) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro x _
      simp
    _ = ∫ x in Ioi r, phi s x := by simpa using integral_comp_neg_Iic (-r) (phi s)

lemma chi_eq_shifted_integral (s : ℝ) (K n : ℕ) (x : ℝ) :
    chi s K n x = ∫ u in x - (n - K : ℕ)..x - K, phi s u := by
  exact intervalIntegral.integral_comp_sub_left (phi s) x

/-- Missing Gaussian mass from an interval is exactly the sum of its two tails. -/
theorem one_sub_integral_neg_to_eq_tail_add_tail {s : ℝ} (hs : 0 < s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 - (∫ x in -a..b, phi s x) = gaussianTail s a + gaussianTail s b := by
  have hab : -a ≤ b := by linarith
  have hdisj : Disjoint (Iic (-a)) (Ioi b) := by
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact (not_lt_of_ge (hxa.trans hab)) hxb
  have hunion :
      (∫ x in Iic (-a) ∪ Ioi b, phi s x) =
        (∫ x in Iic (-a), phi s x) + ∫ x in Ioi b, phi s x := by
    exact setIntegral_union hdisj measurableSet_Ioi
      (integrable_phi hs).integrableOn (integrable_phi hs).integrableOn
  have hcompl : (Ioc (-a) b)ᶜ = Iic (-a) ∪ Ioi b := compl_Ioc
  have hmass := integral_add_compl (s := Ioc (-a) b) measurableSet_Ioc (integrable_phi hs)
  rw [integral_phi hs] at hmass
  rw [intervalIntegral.integral_of_le hab]
  rw [hcompl, hunion, integral_phi_Iic_neg_eq_tail] at hmass
  change (∫ x in Ioc (-a) b, phi s x) +
    (gaussianTail s a + gaussianTail s b) = 1 at hmass
  change 1 - (∫ x in Ioc (-a) b, phi s x) =
    gaussianTail s a + gaussianTail s b
  linarith

theorem one_sub_chi_eq_tail_add_tail {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (x : ℝ) (hxK : (K : ℝ) ≤ x) (hxn : x ≤ (n - K : ℕ)) :
    1 - chi s K n x =
      gaussianTail s (x - K) + gaussianTail s ((n - K : ℕ) - x) := by
  rw [chi_eq_shifted_integral]
  have hleft : 0 ≤ x - (K : ℝ) := sub_nonneg.mpr hxK
  have hright : 0 ≤ (n - K : ℕ) - x := sub_nonneg.mpr hxn
  convert one_sub_integral_neg_to_eq_tail_add_tail hs hright hleft using 1 <;> ring_nf

theorem one_sub_chi_sq_le_two_mul_tails {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) (x : ℝ) (hxK : (K : ℝ) ≤ x)
    (hxn : x ≤ (n - K : ℕ)) :
    1 - chi s K n x ^ 2 ≤
      2 * (gaussianTail s (x - K) + gaussianTail s ((n - K : ℕ) - x)) := by
  rcases chi_mem_Icc hs hKn x with ⟨hchi0, hchi1⟩
  rw [← one_sub_chi_eq_tail_add_tail hs x hxK hxn]
  calc
    1 - chi s K n x ^ 2 = (1 - chi s K n x) * (1 + chi s K n x) := by ring
    _ ≤ (1 - chi s K n x) * 2 := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ = 2 * (1 - chi s K n x) := by ring

lemma integrable_id_mul_phi {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : ℝ => x * phi s x) := by
  have hb : 0 < Real.pi / s ^ 2 := div_pos Real.pi_pos (sq_pos_of_pos hs)
  have h := (integrable_mul_exp_neg_mul_sq hb).const_mul s⁻¹
  convert h using 1
  funext x
  rw [phi_eq_exp_neg_mul_sq hs.ne']
  ring

/-- The first moment of the positive half of the normalized Gaussian. -/
theorem integral_id_mul_phi_Ioi {s : ℝ} (hs : 0 < s) :
    (∫ x in Ioi (0 : ℝ), x * phi s x) = s / (2 * Real.pi) := by
  let b : ℝ := Real.pi / s ^ 2
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hmoment : (∫ x : ℝ in Ioi 0, x * Real.exp (-b * x ^ 2)) = (2 * b)⁻¹ := by
    rw [← RCLike.ofReal_inj (K := ℂ), ← integral_ofReal]
    convert integral_mul_cexp_neg_mul_sq (b := (b : ℂ)) (by simpa using hb) using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      push_cast
      simp
    · push_cast
      rfl
  calc
    (∫ x in Ioi (0 : ℝ), x * phi s x) =
        s⁻¹ * ∫ x in Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      change x * phi s x = s⁻¹ * (x * Real.exp (-b * x ^ 2))
      rw [phi_eq_exp_neg_mul_sq hs.ne']
      dsimp [b]
      ring
    _ = s / (2 * Real.pi) := by
      rw [hmoment]
      dsimp [b]
      field_simp [Real.pi_ne_zero, hs.ne']

/-- The integrand whose integral over the positive half-line is the tail at `j`. -/
def tailKernel (s : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  if (j : ℝ) < x then phi s x else 0

lemma gaussianTail_nat_eq_integral_tailKernel (s : ℝ) (j : ℕ) :
    gaussianTail s j = ∫ x in Ioi (0 : ℝ), tailKernel s j x := by
  rw [gaussianTail]
  change (∫ x in Ioi (j : ℝ), phi s x) =
    ∫ x in Ioi (0 : ℝ), (Ioi (j : ℝ)).indicator (phi s) x
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hxj : x ∈ Ioi (j : ℝ)
  · have hx0 : x ∈ Ioi (0 : ℝ) := by
      show 0 < x
      exact lt_of_le_of_lt (Nat.cast_nonneg j) hxj
    simp [indicator_of_mem hxj, indicator_of_mem hx0]
  · simp [indicator_apply, hxj]

lemma integrableOn_tailKernel {s : ℝ} (hs : 0 < s) (j : ℕ) :
    IntegrableOn (tailKernel s j) (Ioi (0 : ℝ)) := by
  have h : Integrable ((Ioi (j : ℝ)).indicator (phi s)) :=
    (integrable_phi hs).indicator measurableSet_Ioi
  exact h.integrableOn

lemma sum_tailKernel_le {s : ℝ} (hs : 0 < s) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    (∑ j ∈ Finset.range (m + 1), tailKernel s j x) ≤ (x + 1) * phi s x := by
  let t : Finset ℕ := (Finset.range (m + 1)).filter fun j => (j : ℝ) < x
  have hsubset : t ⊆ Finset.range (Nat.ceil x) := by
    intro j hj
    simp only [t, Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact Nat.lt_ceil.mpr hj.2
  have hcardNat : t.card ≤ Nat.ceil x := by
    simpa using Finset.card_le_card hsubset
  have hcard : (t.card : ℝ) ≤ x + 1 := by
    calc
      (t.card : ℝ) ≤ (Nat.ceil x : ℕ) := by exact_mod_cast hcardNat
      _ ≤ x + 1 := (Nat.ceil_lt_add_one hx.le).le
  have hphi : 0 ≤ phi s x := phi_nonneg hs x
  change (∑ j ∈ Finset.range (m + 1), if (j : ℝ) < x then phi s x else 0) ≤
    (x + 1) * phi s x
  rw [← Finset.sum_filter]
  change (∑ _j ∈ t, phi s x) ≤ (x + 1) * phi s x
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcard hphi

lemma integral_add_one_mul_phi_Ioi_le {s : ℝ} (hs : 0 < s) :
    (∫ x in Ioi (0 : ℝ), (x + 1) * phi s x) ≤ s + 1 := by
  have hhalf : (∫ x in Ioi (0 : ℝ), phi s x) ≤ 1 := by
    calc
      (∫ x in Ioi (0 : ℝ), phi s x) ≤ ∫ x : ℝ, phi s x := by
        exact integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall (phi_nonneg hs)) (integrable_phi hs)
      _ = 1 := integral_phi hs
  have hmoment : (∫ x in Ioi (0 : ℝ), x * phi s x) ≤ s := by
    rw [integral_id_mul_phi_Ioi hs]
    have hden : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    exact (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2 (by nlinarith)
  have hidint : IntegrableOn (fun x : ℝ => x * phi s x) (Ioi 0) :=
    (integrable_id_mul_phi hs).integrableOn
  have hphiint : IntegrableOn (phi s) (Ioi 0) := (integrable_phi hs).integrableOn
  calc
    (∫ x in Ioi (0 : ℝ), (x + 1) * phi s x) =
        (∫ x in Ioi (0 : ℝ), x * phi s x) + ∫ x in Ioi (0 : ℝ), phi s x := by
      rw [← integral_add hidint hphiint]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      ring
    _ ≤ s + 1 := add_le_add hmoment hhalf

/-- A finite sum of integer Gaussian tails costs at most one scale plus one. -/
theorem sum_gaussianTail_range_le {s : ℝ} (hs : 0 < s) (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), gaussianTail s j) ≤ s + 1 := by
  calc
    (∑ j ∈ Finset.range (m + 1), gaussianTail s j) =
        ∫ x in Ioi (0 : ℝ), ∑ j ∈ Finset.range (m + 1), tailKernel s j x := by
      simp_rw [gaussianTail_nat_eq_integral_tailKernel]
      rw [integral_finsetSum]
      intro j _
      exact integrableOn_tailKernel hs j
    _ ≤ ∫ x in Ioi (0 : ℝ), (x + 1) * phi s x := by
      apply integral_mono_ae
      · exact integrable_finsetSum _ fun j _ => integrableOn_tailKernel hs j
      · exact ((integrable_id_mul_phi hs).add (integrable_phi hs)).integrableOn.congr_fun
          (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact sum_tailKernel_le hs m hx
    _ ≤ s + 1 := integral_add_one_mul_phi_Ioi_le hs

lemma gaussianTail_antitone {s : ℝ} (hs : 0 < s) : Antitone (gaussianTail s) := by
  intro a b hab
  unfold gaussianTail
  exact integral_mono_measure
    (Measure.restrict_mono (by intro x hx; exact hab.trans_lt hx) le_rfl)
    (Filter.Eventually.of_forall fun x => le_of_lt (phi_pos hs x))
    ((integrable_phi hs).integrableOn)

theorem summable_gaussianTail_nat {s : ℝ} (hs : 0 < s) :
    Summable (fun j : ℕ => gaussianTail s j) := by
  apply summable_of_sum_range_le (fun j => gaussianTail_nonneg hs j)
  intro m
  calc
    (∑ j ∈ Finset.range m, gaussianTail s j) ≤
        ∑ j ∈ Finset.range (m + 1), gaussianTail s j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_add_right m 1))
      intro j _ _
      exact gaussianTail_nonneg hs j
    _ ≤ s + 1 := sum_gaussianTail_range_le hs m

theorem tsum_gaussianTail_nat_le {s : ℝ} (hs : 0 < s) :
    (∑' j : ℕ, gaussianTail s j) ≤ s + 1 := by
  apply Real.tsum_le_of_sum_range_le (fun j => gaussianTail_nonneg hs j)
  intro m
  calc
    (∑ j ∈ Finset.range m, gaussianTail s j) ≤
        ∑ j ∈ Finset.range (m + 1), gaussianTail s j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_add_right m 1))
      intro j _ _
      exact gaussianTail_nonneg hs j
    _ ≤ s + 1 := sum_gaussianTail_range_le hs m

lemma chi_le_tail_left {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n)
    (x : ℝ) : chi s K n x ≤ gaussianTail s (K - x) := by
  have hab : x - (n - K : ℕ) ≤ x - K := by
    linarith [cutoff_endpoints_order hKn]
  rw [chi_eq_shifted_integral, intervalIntegral.integral_of_le hab]
  calc
    (∫ u in Ioc (x - (n - K : ℕ)) (x - K), phi s u) ≤
        ∫ u in Iic (x - K), phi s u := by
      exact integral_mono_measure
        (Measure.restrict_mono (by intro u hu; exact hu.2) le_rfl)
        (Filter.Eventually.of_forall (phi_nonneg hs))
        (integrable_phi hs).integrableOn
    _ = gaussianTail s (K - x) := by
      have heq : x - (K : ℝ) = -(K - x) := by ring
      rw [heq, integral_phi_Iic_neg_eq_tail]

lemma chi_le_tail_right {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n)
    (x : ℝ) :
    chi s K n x ≤ gaussianTail s (x - (n - K : ℕ)) := by
  have hab : x - (n - K : ℕ) ≤ x - K := by
    linarith [cutoff_endpoints_order hKn]
  rw [chi_eq_shifted_integral, intervalIntegral.integral_of_le hab]
  calc
    (∫ u in Ioc (x - (n - K : ℕ)) (x - K), phi s u) ≤
        ∫ u in Ioi (x - (n - K : ℕ)), phi s u := by
      exact integral_mono_measure
        (Measure.restrict_mono (by intro u hu; exact hu.1) le_rfl)
        (Filter.Eventually.of_forall (phi_nonneg hs))
        (integrable_phi hs).integrableOn
    _ = gaussianTail s (x - (n - K : ℕ)) := rfl

/-- The exponential factor gained once the Gaussian is sampled at distance `K`. -/
def cutoffExp (s : ℝ) (K : ℕ) : ℝ :=
  Real.exp (-Real.pi * ((K : ℝ) / s) ^ 2 / 2)

lemma cutoffExp_nonneg (s : ℝ) (K : ℕ) : 0 ≤ cutoffExp s K := by
  exact (Real.exp_pos _).le

lemma phi_le_two_mul_cutoffExp_mul_phi_two {s : ℝ} (hs : 0 < s) (K : ℕ)
    {x : ℝ} (hx : (K : ℝ) ≤ x) :
    phi s x ≤ 2 * cutoffExp s K * phi (2 * s) x := by
  have hx0 : 0 ≤ x := (Nat.cast_nonneg K).trans hx
  have hsq : ((K : ℝ) : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
  let d : ℝ := Real.pi / s ^ 2
  have hd : 0 < d := div_pos Real.pi_pos (sq_pos_of_pos hs)
  have hmain : -Real.pi * (x / s) ^ 2 = -d * x ^ 2 := by
    dsimp [d]
    field_simp [hs.ne']
  have hK : -Real.pi * ((K : ℝ) / s) ^ 2 / 2 = -d * (K : ℝ) ^ 2 / 2 := by
    dsimp [d]
    field_simp [hs.ne']
  have htwo : -Real.pi * (x / (2 * s)) ^ 2 = -d * x ^ 2 / 4 := by
    dsimp [d]
    field_simp [hs.ne']
    ring
  have harg : -Real.pi * (x / s) ^ 2 ≤
      -Real.pi * ((K : ℝ) / s) ^ 2 / 2 + -Real.pi * (x / (2 * s)) ^ 2 := by
    rw [hmain, hK, htwo]
    nlinarith
  unfold phi cutoffExp
  have hrhs :
      2 * Real.exp (-Real.pi * ((K : ℝ) / s) ^ 2 / 2) *
          ((2 * s)⁻¹ * Real.exp (-Real.pi * (x / (2 * s)) ^ 2)) =
        s⁻¹ * Real.exp (-Real.pi * ((K : ℝ) / s) ^ 2 / 2 +
          -Real.pi * (x / (2 * s)) ^ 2) := by
    rw [Real.exp_add]
    field_simp [hs.ne']
  rw [hrhs]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (inv_nonneg.mpr hs.le)

lemma gaussianTail_le_two_mul_cutoffExp_mul_tail_two {s : ℝ} (hs : 0 < s) (K : ℕ)
    {r : ℝ} (hr : (K : ℝ) ≤ r) :
    gaussianTail s r ≤ 2 * cutoffExp s K * gaussianTail (2 * s) r := by
  unfold gaussianTail
  rw [← integral_const_mul]
  apply integral_mono_ae
  · exact (integrable_phi hs).integrableOn
  · exact ((integrable_phi (mul_pos two_pos hs)).const_mul (2 * cutoffExp s K)).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact phi_le_two_mul_cutoffExp_mul_phi_two hs K (hr.trans (le_of_lt hx))

/-- Integer samples strictly to the left of `[0,n]`. -/
def outsideLeft (s : ℝ) (K n j : ℕ) : ℝ :=
  chi s K n (-((j + 1 : ℕ) : ℝ))

/-- Integer samples strictly to the right of `[0,n]`. -/
def outsideRight (s : ℝ) (K n j : ℕ) : ℝ :=
  chi s K n ((n + j + 1 : ℕ) : ℝ)

lemma outsideLeft_le_scaled_tail {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n)
    (j : ℕ) :
    outsideLeft s K n j ≤ 2 * cutoffExp s K * gaussianTail (2 * s) j := by
  have hchi : outsideLeft s K n j ≤ gaussianTail s (K + j + 1) := by
    unfold outsideLeft
    simpa only [sub_neg_eq_add, Nat.cast_add, Nat.cast_one, add_assoc] using
      chi_le_tail_left hs hKn (-((j + 1 : ℕ) : ℝ))
  have hscale : gaussianTail s (K + j + 1) ≤
      2 * cutoffExp s K * gaussianTail (2 * s) (K + j + 1) :=
    gaussianTail_le_two_mul_cutoffExp_mul_tail_two hs K (by norm_cast; omega)
  have hmono : gaussianTail (2 * s) (K + j + 1) ≤ gaussianTail (2 * s) j :=
    gaussianTail_antitone (mul_pos two_pos hs) (by norm_cast; omega)
  have hfac : 0 ≤ 2 * cutoffExp s K := mul_nonneg (by norm_num) (cutoffExp_nonneg s K)
  exact hchi.trans (hscale.trans (mul_le_mul_of_nonneg_left hmono hfac))

lemma outsideRight_le_scaled_tail {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) (j : ℕ) :
    outsideRight s K n j ≤ 2 * cutoffExp s K * gaussianTail (2 * s) j := by
  have hchi : outsideRight s K n j ≤ gaussianTail s (K + j + 1) := by
    unfold outsideRight
    have hsub : n - K ≤ n + j + 1 := by omega
    have harg : ((n + j + 1 : ℕ) : ℝ) - ((n - K : ℕ) : ℝ) =
        (K : ℝ) + j + 1 := by
      rw [← Nat.cast_sub hsub]
      norm_cast
      omega
    rw [← harg]
    exact chi_le_tail_right hs hKn _
  have hscale : gaussianTail s (K + j + 1) ≤
      2 * cutoffExp s K * gaussianTail (2 * s) (K + j + 1) :=
    gaussianTail_le_two_mul_cutoffExp_mul_tail_two hs K (by norm_cast; omega)
  have hmono : gaussianTail (2 * s) (K + j + 1) ≤ gaussianTail (2 * s) j :=
    gaussianTail_antitone (mul_pos two_pos hs) (by norm_cast; omega)
  have hfac : 0 ≤ 2 * cutoffExp s K := mul_nonneg (by norm_num) (cutoffExp_nonneg s K)
  exact hchi.trans (hscale.trans (mul_le_mul_of_nonneg_left hmono hfac))

theorem summable_outsideLeft {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) :
    Summable (outsideLeft s K n) := by
  apply summable_of_sum_range_le (fun j => chi_nonneg hs hKn _)
  intro m
  calc
    (∑ j ∈ Finset.range m, outsideLeft s K n j) ≤
        ∑ j ∈ Finset.range m, 2 * cutoffExp s K * gaussianTail (2 * s) j := by
      exact Finset.sum_le_sum fun j _ => outsideLeft_le_scaled_tail hs hKn j
    _ = 2 * cutoffExp s K * ∑ j ∈ Finset.range m, gaussianTail (2 * s) j := by
      rw [Finset.mul_sum]
    _ ≤ 2 * cutoffExp s K * (2 * s + 1) := by
      exact mul_le_mul_of_nonneg_left
        (((summable_gaussianTail_nat (mul_pos two_pos hs)).sum_le_tsum (Finset.range m)
          (fun j _ => gaussianTail_nonneg (mul_pos two_pos hs) j)).trans
            (tsum_gaussianTail_nat_le (mul_pos two_pos hs)))
        (mul_nonneg (by norm_num) (cutoffExp_nonneg s K))

theorem summable_outsideRight {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) :
    Summable (outsideRight s K n) := by
  apply summable_of_sum_range_le (fun j => chi_nonneg hs hKn _)
  intro m
  calc
    (∑ j ∈ Finset.range m, outsideRight s K n j) ≤
        ∑ j ∈ Finset.range m, 2 * cutoffExp s K * gaussianTail (2 * s) j := by
      exact Finset.sum_le_sum fun j _ => outsideRight_le_scaled_tail hs hKn j
    _ = 2 * cutoffExp s K * ∑ j ∈ Finset.range m, gaussianTail (2 * s) j := by
      rw [Finset.mul_sum]
    _ ≤ 2 * cutoffExp s K * (2 * s + 1) := by
      exact mul_le_mul_of_nonneg_left
        (((summable_gaussianTail_nat (mul_pos two_pos hs)).sum_le_tsum (Finset.range m)
          (fun j _ => gaussianTail_nonneg (mul_pos two_pos hs) j)).trans
            (tsum_gaussianTail_nat_le (mul_pos two_pos hs)))
        (mul_nonneg (by norm_num) (cutoffExp_nonneg s K))

/-- Explicit exponentially small `ℓ¹` mass discarded outside the integer interval `[0,n]`. -/
theorem tsum_outside_le {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) :
    (∑' j : ℕ, outsideLeft s K n j) + ∑' j : ℕ, outsideRight s K n j ≤
      4 * cutoffExp s K * (2 * s + 1) := by
  have hleft : (∑' j : ℕ, outsideLeft s K n j) ≤
      2 * cutoffExp s K * (2 * s + 1) := by
    apply (summable_outsideLeft hs hKn).tsum_le_of_sum_le
    intro u
    calc
      (∑ j ∈ u, outsideLeft s K n j) ≤
          ∑ j ∈ u, 2 * cutoffExp s K * gaussianTail (2 * s) j := by
        exact Finset.sum_le_sum fun j _ => outsideLeft_le_scaled_tail hs hKn j
      _ ≤ 2 * cutoffExp s K * (2 * s + 1) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (((summable_gaussianTail_nat (mul_pos two_pos hs)).sum_le_tsum u
            (fun j _ => gaussianTail_nonneg (mul_pos two_pos hs) j)).trans
              (tsum_gaussianTail_nat_le (mul_pos two_pos hs)))
          (mul_nonneg (by norm_num) (cutoffExp_nonneg s K))
  have hright : (∑' j : ℕ, outsideRight s K n j) ≤
      2 * cutoffExp s K * (2 * s + 1) := by
    apply (summable_outsideRight hs hKn).tsum_le_of_sum_le
    intro u
    calc
      (∑ j ∈ u, outsideRight s K n j) ≤
          ∑ j ∈ u, 2 * cutoffExp s K * gaussianTail (2 * s) j := by
        exact Finset.sum_le_sum fun j _ => outsideRight_le_scaled_tail hs hKn j
      _ ≤ 2 * cutoffExp s K * (2 * s + 1) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (((summable_gaussianTail_nat (mul_pos two_pos hs)).sum_le_tsum u
            (fun j _ => gaussianTail_nonneg (mul_pos two_pos hs) j)).trans
              (tsum_gaussianTail_nat_le (mul_pos two_pos hs)))
          (mul_nonneg (by norm_num) (cutoffExp_nonneg s K))
  nlinarith

/-- At the scales used in the construction, the explicit `ℓ¹` truncation bound is below one
already for `m ≥ 2`. -/
theorem cutoffExp_pow_bound_lt_one {m : ℕ} (hm : 2 ≤ m) :
    4 * cutoffExp ((m ^ 12 : ℕ) : ℝ) (m ^ 15) *
        (2 * ((m ^ 12 : ℕ) : ℝ) + 1) < 1 := by
  let x : ℝ := m
  have hx : 2 ≤ x := by
    dsimp [x]
    exact_mod_cast hm
  have hxpos : 0 < x := by linarith
  have hratio : (((m ^ 15 : ℕ) : ℝ) / ((m ^ 12 : ℕ) : ℝ)) = x ^ 3 := by
    dsimp [x]
    push_cast
    field_simp [ne_of_gt hxpos]
  let y : ℝ := x ^ 6
  have hy64 : 64 ≤ y := by
    dsimp [y]
    have := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hx 6
    norm_num at this ⊢
    exact this
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy64
  let A : ℝ := Real.pi * y / 2
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hAlower : (3 / 2 : ℝ) * y < A := by
    dsimp [A]
    have := mul_lt_mul_of_pos_right Real.pi_gt_three hypos
    linarith
  have hcubes : ((3 / 2 : ℝ) * y) ^ 3 < A ^ 3 := by
    exact pow_lt_pow_left₀ hAlower (by positivity) (by norm_num)
  have hygrowth : 64 * y ^ 2 ≤ y ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy64) (sq_nonneg y)]
  have hpoly : 4 * (2 * x ^ 12 + 1) < A ^ 3 / 6 := by
    have hxy : x ^ 12 = y ^ 2 := by dsimp [y]; ring
    rw [hxy]
    nlinarith
  have hexplower : A ^ 3 / 6 ≤ Real.exp A := by
    have h := Real.pow_div_factorial_le_exp A hA0 3
    norm_num at h ⊢
    exact h
  have hden : 4 * (2 * x ^ 12 + 1) < Real.exp A := hpoly.trans_le hexplower
  have hfinal : 4 * Real.exp (-A) * (2 * x ^ 12 + 1) < 1 := by
    rw [Real.exp_neg]
    have hdiv := (div_lt_one (Real.exp_pos A)).2 hden
    rw [div_eq_mul_inv] at hdiv
    nlinarith
  have hcut : cutoffExp ((m ^ 12 : ℕ) : ℝ) (m ^ 15) = Real.exp (-A) := by
    unfold cutoffExp
    rw [hratio]
    congr 1
    dsimp [A, y]
    ring
  rw [hcut]
  simpa [x] using hfinal

theorem eventually_cutoffExp_pow_bound_lt_one :
    ∀ᶠ m : ℕ in Filter.atTop,
      4 * cutoffExp ((m ^ 12 : ℕ) : ℝ) (m ^ 15) *
          (2 * ((m ^ 12 : ℕ) : ℝ) + 1) < 1 := by
  filter_upwards [Filter.eventually_ge_atTop 2] with m hm
  exact cutoffExp_pow_bound_lt_one hm

/-- Direct specialization of the truncation estimate at `(s,K,n)=(m¹²,m¹⁵,m¹⁸)`. -/
theorem tsum_outside_pow_lt_one {m : ℕ} (hm : 2 ≤ m) :
    (∑' j : ℕ, outsideLeft ((m ^ 12 : ℕ) : ℝ) (m ^ 15) (m ^ 18) j) +
        ∑' j : ℕ, outsideRight ((m ^ 12 : ℕ) : ℝ) (m ^ 15) (m ^ 18) j < 1 := by
  have hmpos : 0 < m := by omega
  have hs : 0 < ((m ^ 12 : ℕ) : ℝ) := by positivity
  have hm3 : 2 ≤ m ^ 3 := by
    have hpow := pow_le_pow_left' hm 3
    norm_num at hpow
    omega
  have hKn : 2 * m ^ 15 ≤ m ^ 18 := by
    calc
      2 * m ^ 15 ≤ m ^ 3 * m ^ 15 := Nat.mul_le_mul_right (m ^ 15) hm3
      _ = m ^ 18 := by ring
  exact (tsum_outside_le hs hKn).trans_lt (cutoffExp_pow_bound_lt_one hm)

lemma outsideLeft_sq_le {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n)
    (j : ℕ) : outsideLeft s K n j ^ 2 ≤ gaussianTail s K * gaussianTail s j := by
  have hchi0 : 0 ≤ outsideLeft s K n j := chi_nonneg hs hKn _
  have hchi : outsideLeft s K n j ≤ gaussianTail s (K + j + 1) := by
    unfold outsideLeft
    simpa only [sub_neg_eq_add, Nat.cast_add, Nat.cast_one, add_assoc] using
      chi_le_tail_left hs hKn (-((j + 1 : ℕ) : ℝ))
  have htK : gaussianTail s (K + j + 1) ≤ gaussianTail s K :=
    gaussianTail_antitone hs (by norm_cast; omega)
  have htj : gaussianTail s (K + j + 1) ≤ gaussianTail s j :=
    gaussianTail_antitone hs (by norm_cast; omega)
  nlinarith [gaussianTail_nonneg hs K, gaussianTail_nonneg hs j]

lemma outsideRight_sq_le {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n)
    (j : ℕ) : outsideRight s K n j ^ 2 ≤ gaussianTail s K * gaussianTail s j := by
  have hchi0 : 0 ≤ outsideRight s K n j := chi_nonneg hs hKn _
  have hchi : outsideRight s K n j ≤ gaussianTail s (K + j + 1) := by
    unfold outsideRight
    have hsub : n - K ≤ n + j + 1 := by omega
    have harg : ((n + j + 1 : ℕ) : ℝ) - ((n - K : ℕ) : ℝ) =
        (K : ℝ) + j + 1 := by
      rw [← Nat.cast_sub hsub]
      norm_cast
      omega
    rw [← harg]
    exact chi_le_tail_right hs hKn _
  have htK : gaussianTail s (K + j + 1) ≤ gaussianTail s K :=
    gaussianTail_antitone hs (by norm_cast; omega)
  have htj : gaussianTail s (K + j + 1) ≤ gaussianTail s j :=
    gaussianTail_antitone hs (by norm_cast; omega)
  nlinarith [gaussianTail_nonneg hs K, gaussianTail_nonneg hs j]

theorem summable_outsideLeft_sq {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) :
    Summable (fun j : ℕ => outsideLeft s K n j ^ 2) := by
  apply summable_of_sum_range_le (fun j => sq_nonneg (outsideLeft s K n j))
  intro m
  calc
    (∑ j ∈ Finset.range m, outsideLeft s K n j ^ 2) ≤
        ∑ j ∈ Finset.range m, gaussianTail s K * gaussianTail s j := by
      exact Finset.sum_le_sum fun j _ => outsideLeft_sq_le hs hKn j
    _ = gaussianTail s K * ∑ j ∈ Finset.range m, gaussianTail s j := by
      rw [Finset.mul_sum]
    _ ≤ gaussianTail s K * (s + 1) := by
      exact mul_le_mul_of_nonneg_left
        ((summable_gaussianTail_nat hs).sum_le_tsum (Finset.range m)
          (fun j _ => gaussianTail_nonneg hs j) |>.trans (tsum_gaussianTail_nat_le hs))
        (gaussianTail_nonneg hs K)

theorem summable_outsideRight_sq {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) : Summable (fun j : ℕ => outsideRight s K n j ^ 2) := by
  apply summable_of_sum_range_le (fun j => sq_nonneg (outsideRight s K n j))
  intro m
  calc
    (∑ j ∈ Finset.range m, outsideRight s K n j ^ 2) ≤
        ∑ j ∈ Finset.range m, gaussianTail s K * gaussianTail s j := by
      exact Finset.sum_le_sum fun j _ => outsideRight_sq_le hs hKn j
    _ = gaussianTail s K * ∑ j ∈ Finset.range m, gaussianTail s j := by
      rw [Finset.mul_sum]
    _ ≤ gaussianTail s K * (s + 1) := by
      exact mul_le_mul_of_nonneg_left
        ((summable_gaussianTail_nat hs).sum_le_tsum (Finset.range m)
          (fun j _ => gaussianTail_nonneg hs j) |>.trans (tsum_gaussianTail_nat_le hs))
        (gaussianTail_nonneg hs K)

/-- The squared integer mass discarded outside `[0,n]` is summable and has this explicit tail. -/
theorem tsum_outside_sq_le {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) :
    (∑' j : ℕ, outsideLeft s K n j ^ 2) +
        ∑' j : ℕ, outsideRight s K n j ^ 2 ≤
      2 * gaussianTail s K * (s + 1) := by
  have hleft : (∑' j : ℕ, outsideLeft s K n j ^ 2) ≤
      gaussianTail s K * (s + 1) := by
    apply (summable_outsideLeft_sq hs hKn).tsum_le_of_sum_le
    intro u
    calc
      (∑ j ∈ u, outsideLeft s K n j ^ 2) ≤
          ∑ j ∈ u, gaussianTail s K * gaussianTail s j := by
        exact Finset.sum_le_sum fun j _ => outsideLeft_sq_le hs hKn j
      _ ≤ gaussianTail s K * (s + 1) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          ((summable_gaussianTail_nat hs).sum_le_tsum u
            (fun j _ => gaussianTail_nonneg hs j) |>.trans (tsum_gaussianTail_nat_le hs))
          (gaussianTail_nonneg hs K)
  have hright : (∑' j : ℕ, outsideRight s K n j ^ 2) ≤
      gaussianTail s K * (s + 1) := by
    apply (summable_outsideRight_sq hs hKn).tsum_le_of_sum_le
    intro u
    calc
      (∑ j ∈ u, outsideRight s K n j ^ 2) ≤
          ∑ j ∈ u, gaussianTail s K * gaussianTail s j := by
        exact Finset.sum_le_sum fun j _ => outsideRight_sq_le hs hKn j
      _ ≤ gaussianTail s K * (s + 1) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          ((summable_gaussianTail_nat hs).sum_le_tsum u
            (fun j _ => gaussianTail_nonneg hs j) |>.trans (tsum_gaussianTail_nat_le hs))
          (gaussianTail_nonneg hs K)
  nlinarith

/-- The loss in squared mass at an integer sampling point. -/
def cutoffDefect (s : ℝ) (K n k : ℕ) : ℝ :=
  1 - chi s K n k ^ 2

lemma cutoffDefect_le_one {s : ℝ} (_hs : 0 < s) {K n : ℕ} (_hKn : 2 * K ≤ n)
    (k : ℕ) : cutoffDefect s K n k ≤ 1 := by
  unfold cutoffDefect
  nlinarith [sq_nonneg (chi s K n k)]

lemma cutoffDefect_middle_le {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n)
    {j : ℕ} (hj : j ≤ n - 2 * K) :
    cutoffDefect s K n (K + j) ≤
      2 * (gaussianTail s j + gaussianTail s ((((n - 2 * K) - j : ℕ) : ℝ))) := by
  have hKj : K + j ≤ n - K := by omega
  have hxK : (K : ℝ) ≤ (K + j : ℕ) := by norm_cast; omega
  have hxn : ((K + j : ℕ) : ℝ) ≤ (n - K : ℕ) := by exact_mod_cast hKj
  have harg : ((n - K : ℕ) : ℝ) - ((K + j : ℕ) : ℝ) =
      (((n - 2 * K) - j : ℕ) : ℝ) := by
    rw [← Nat.cast_sub hKj]
    congr 1
    omega
  have h := one_sub_chi_sq_le_two_mul_tails hs hKn ((K + j : ℕ) : ℝ) hxK hxn
  unfold cutoffDefect
  rw [harg] at h
  simpa only [Nat.cast_add, add_sub_cancel_left] using h

lemma sum_cutoffDefect_middle_le {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) :
    (∑ k ∈ Finset.Icc K (n - K), cutoffDefect s K n k) ≤ 4 * (s + 1) := by
  let m := n - 2 * K
  have hrewrite :
      (∑ k ∈ Finset.Icc K (n - K), cutoffDefect s K n k) =
        ∑ j ∈ Finset.range (m + 1), cutoffDefect s K n (K + j) := by
    have hlen : (n - K + 1) - K = m + 1 := by
      dsimp [m]
      omega
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    rw [hlen]
  rw [hrewrite]
  have hreflect :
      (∑ j ∈ Finset.range (m + 1), gaussianTail s (((m - j : ℕ) : ℝ))) =
        ∑ j ∈ Finset.range (m + 1), gaussianTail s j := by
    simpa using Finset.sum_range_reflect (fun j : ℕ => gaussianTail s j) (m + 1)
  calc
    (∑ j ∈ Finset.range (m + 1), cutoffDefect s K n (K + j)) ≤
        ∑ j ∈ Finset.range (m + 1),
          2 * (gaussianTail s j + gaussianTail s (((m - j : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa [m] using cutoffDefect_middle_le hs hKn (j := j) (by
        simp only [Finset.mem_range] at hj
        omega)
    _ = 4 * (∑ j ∈ Finset.range (m + 1), gaussianTail s j) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hreflect]
      ring
    _ ≤ 4 * (s + 1) := by
      exact mul_le_mul_of_nonneg_left (sum_gaussianTail_range_le hs m) (by norm_num)

/-- Total cutoff defect: two boundary strips plus four Gaussian-tail sums. -/
theorem sum_cutoffDefect_range_le {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) :
    (∑ k ∈ Finset.range (n + 1), cutoffDefect s K n k) ≤
      4 * (K : ℝ) + 4 * (s + 1) := by
  let L := Finset.range K
  let M := Finset.Icc K (n - K)
  let R := Finset.Ioc (n - K) n
  have hpartition : (L ∪ M) ∪ R = Finset.range (n + 1) := by
    ext k
    simp only [L, M, R, Finset.mem_union, Finset.mem_range, Finset.mem_Icc,
      Finset.mem_Ioc]
    omega
  have hLM : Disjoint L M := by
    rw [Finset.disjoint_left]
    intro k hkL hkM
    simp only [L, Finset.mem_range] at hkL
    simp only [M, Finset.mem_Icc] at hkM
    omega
  have hLMR : Disjoint (L ∪ M) R := by
    rw [Finset.disjoint_left]
    intro k hkLM hkR
    simp only [Finset.mem_union] at hkLM
    simp only [R, Finset.mem_Ioc] at hkR
    rcases hkLM with hkL | hkM
    · simp only [L, Finset.mem_range] at hkL
      omega
    · simp only [M, Finset.mem_Icc] at hkM
      omega
  have hL : (∑ k ∈ L, cutoffDefect s K n k) ≤ (K : ℝ) := by
    calc
      (∑ k ∈ L, cutoffDefect s K n k) ≤ ∑ _k ∈ L, (1 : ℝ) := by
        exact Finset.sum_le_sum fun k _ => cutoffDefect_le_one hs hKn k
      _ = (K : ℝ) := by simp [L]
  have hR : (∑ k ∈ R, cutoffDefect s K n k) ≤ (K : ℝ) := by
    calc
      (∑ k ∈ R, cutoffDefect s K n k) ≤ ∑ _k ∈ R, (1 : ℝ) := by
        exact Finset.sum_le_sum fun k _ => cutoffDefect_le_one hs hKn k
      _ = (K : ℝ) := by
        simp only [R, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
        norm_cast
        omega
  have hM : (∑ k ∈ M, cutoffDefect s K n k) ≤ 4 * (s + 1) := by
    exact sum_cutoffDefect_middle_le hs hKn
  rw [← hpartition, Finset.sum_union hLMR, Finset.sum_union hLM]
  nlinarith

/-- The total-defect estimate, expanded in the form used by later constructions. -/
theorem sum_one_sub_chi_sq_range_le {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) :
    (∑ k ∈ Finset.range (n + 1), (1 - chi s K n k ^ 2)) ≤
      4 * (K : ℝ) + 4 * (s + 1) := by
  simpa only [cutoffDefect] using sum_cutoffDefect_range_le hs hKn

end

end Erdos230.GaussianCutoff
