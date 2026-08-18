import APAP.Physics.Unbalancing
import ErdosProblems.Erdos140.BalancedRestriction
import ErdosProblems.Erdos140.RegularBohr

/-!
# Localized physical unbalancing on a regular Bohr set

This file is the normalization-sensitive bridge between physical unbalancing
and the balanced-restriction argument.  The weight is not assumed to have a
positive spectrum: it is explicitly the autocorrelation of the convolution
of two normalized Bohr indicators, and hence has the autocorrelation
representation required by `physical_pow_inner_nonneg`.

The width hypothesis is the concrete rank-scale bound

`kappa <= epsilon * |A| / (4800 * max(rank B,1) * |B|)`.

Thus it is `epsilon * alpha / (4800 * max(rank B,1))`, where `alpha` is the
relative density of `A` in `B`.  In particular, it has no dependence on the
cardinality of the ambient group.
-/

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal Pointwise mu

namespace Erdos140
namespace LocalizedUnbalancing

noncomputable section

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The smoothing function whose autocorrelation is the localized weight. -/
def smoothingBase (D E : Finset G) : G → ℝ≥0 :=
  μ_[ℝ≥0] D ∗ᵈ μ E

/-- The concrete spectrally-positive probability weight used in localized
unbalancing. -/
def smoothingWeight (D E : Finset G) : G → ℝ≥0 :=
  smoothingBase D E ○ᵈ smoothingBase D E

lemma smoothingBase_sum {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty) :
    ∑ x : G, smoothingBase D E x = 1 := by
  simp [smoothingBase, sum_ddconv, hD, hE]

lemma smoothingWeight_sum {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty) :
    ∑ x : G, smoothingWeight D E x = 1 := by
  simp [smoothingWeight, sum_dddconv, smoothingBase_sum hD hE]

lemma smoothingWeight_nonneg (D E : Finset G) :
    0 ≤ smoothingWeight D E := by
  simp [smoothingWeight]

/-- The complex autocorrelation representation of the concrete smoothing
weight. -/
lemma smoothingWeight_autocorrelation (D E : Finset G) :
    ((↑) ∘ smoothingBase D E : G → ℂ) ○ᵈ
        ((↑) ∘ smoothingBase D E) =
      (↑) ∘ smoothingWeight D E := by
  let b := smoothingBase D E
  calc
    ((↑) ∘ b : G → ℂ) ○ᵈ ((↑) ∘ b) =
        (↑) ∘ (((↑) ∘ b : G → ℝ) ○ᵈ ((↑) ∘ b)) := by
          exact (Complex.ofReal_comp_dddconv ((↑) ∘ b) ((↑) ∘ b)).symm
    _ = (↑) ∘ (b ○ᵈ b) := by
      rw [← NNReal.coe_comp_dddconv]
      rfl
    _ = (↑) ∘ smoothingWeight D E := by
      funext x
      rfl

/-- `BalancedRestriction.weightedLpNorm` agrees with APAP's weighted norm on
positive natural exponents. -/
lemma weightedLpNorm_eq_wLpNorm (w : G → ℝ≥0) (f : G → ℝ)
    {p : ℕ} (hp : 0 < p) :
    BalancedRestriction.weightedLpNorm ((↑) ∘ w) f p = ‖f‖_[p, w] := by
  rw [BalancedRestriction.weightedLpNorm_of_pos _ _ hp]
  rw [wLpNorm_eq_sum_norm (by exact_mod_cast hp.ne') (by simp)]
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    simp only [weightedAbsMoment, NNReal.smul_def, smul_eq_mul, norm_eq_abs,
      Function.comp_apply, ENNReal.toReal_natCast]
    rw [Real.rpow_natCast]
  · simp [one_div]

/-- Minkowski's inequality in the local natural-exponent notation. -/
lemma weightedLpNorm_sub_le
    (w : G → ℝ≥0) (f g : G → ℝ) {p : ℕ} (hp : 1 ≤ p) :
    BalancedRestriction.weightedLpNorm ((↑) ∘ w) (f - g) p ≤
      BalancedRestriction.weightedLpNorm ((↑) ∘ w) f p +
        BalancedRestriction.weightedLpNorm ((↑) ∘ w) g p := by
  rw [weightedLpNorm_eq_wLpNorm w _ (Nat.zero_lt_of_lt hp),
    weightedLpNorm_eq_wLpNorm w _ (Nat.zero_lt_of_lt hp),
    weightedLpNorm_eq_wLpNorm w _ (Nat.zero_lt_of_lt hp)]
  exact wLpNorm_sub_le (by exact_mod_cast hp) w f g

lemma weightedLpNorm_smul_of_nonneg
    (w : G → ℝ≥0) (f : G → ℝ) (c : ℝ) (hc : 0 ≤ c)
    {p : ℕ} (hp : 0 < p) :
    BalancedRestriction.weightedLpNorm ((↑) ∘ w) (c • f) p =
      c * BalancedRestriction.weightedLpNorm ((↑) ∘ w) f p := by
  rw [weightedLpNorm_eq_wLpNorm w _ hp, weightedLpNorm_eq_wLpNorm w _ hp,
    wLpNorm_smul]
  simp [Real.norm_eq_abs, abs_of_nonneg hc]

lemma weightedLpNorm_le_add_of_add
    (w : G → ℝ≥0) (f g : G → ℝ) {p : ℕ} (hp : 1 ≤ p) :
    BalancedRestriction.weightedLpNorm ((↑) ∘ w) f p ≤
      BalancedRestriction.weightedLpNorm ((↑) ∘ w) (f + g) p +
        BalancedRestriction.weightedLpNorm ((↑) ∘ w) g p := by
  simp_rw [weightedLpNorm_eq_wLpNorm w _ (Nat.zero_lt_of_lt hp)]
  exact wLpNorm_le_add_wLpNorm_add (by exact_mod_cast hp) w f g

/-- A pointwise bound controls the local weighted norm for a probability
weight. -/
lemma weightedLpNorm_le_of_abs_le
    {w : G → ℝ≥0} (hw : ∑ x : G, w x = 1)
    {f : G → ℝ} {C : ℝ} (hC : 0 ≤ C) {p : ℕ} (hp : 0 < p)
    (hf : ∀ x, |f x| ≤ C) :
    BalancedRestriction.weightedLpNorm ((↑) ∘ w) f p ≤ C := by
  rw [weightedLpNorm_eq_wLpNorm w f hp]
  calc
    ‖f‖_[p, w] ≤ ‖(fun _ : G ↦ C)‖_[p, w] := by
      apply lpNorm_mono_real .of_discrete
      simpa [abs_of_nonneg hC] using hf
    _ = C := by
      rw [wLpNorm_eq_sum_norm (by exact_mod_cast hp.ne') (by simp)]
      simp only [ENNReal.toReal_natCast]
      have hsum : ∑ x : G, (w x : ℝ) = 1 := by exact_mod_cast hw
      have heq : ∑ x : G, (w x : ℝ) * ‖C‖ ^ (p : ℝ) = C ^ p := by
        rw [norm_eq_abs, abs_of_nonneg hC, Real.rpow_natCast, ← Finset.sum_mul,
          hsum, one_mul]
      rw [show (∑ x : G, w x • ‖C‖ ^ (p : ℝ)) = C ^ p by
        simpa [NNReal.smul_def] using heq]
      exact Real.pow_rpow_inv_natCast hC hp.ne'

lemma weightedLpNorm_le_of_abs_le_on_support
    {w : G → ℝ≥0} (hw : ∑ x : G, w x = 1)
    {f : G → ℝ} {C : ℝ} (hC : 0 ≤ C) {p : ℕ} (hp : 0 < p)
    (hf : ∀ x, w x ≠ 0 → |f x| ≤ C) :
    BalancedRestriction.weightedLpNorm ((↑) ∘ w) f p ≤ C := by
  let g : G → ℝ := fun x ↦ if w x = 0 then 0 else f x
  have hnorm : BalancedRestriction.weightedLpNorm ((↑) ∘ w) f p =
      BalancedRestriction.weightedLpNorm ((↑) ∘ w) g p := by
    rw [BalancedRestriction.weightedLpNorm_of_pos _ _ hp,
      BalancedRestriction.weightedLpNorm_of_pos _ _ hp]
    apply congrArg (fun z : ℝ ↦ z ^ (1 / (p : ℝ)))
    unfold weightedAbsMoment
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : w x = 0 <;> simp [g, hx]
  rw [hnorm]
  apply weightedLpNorm_le_of_abs_le hw hC hp
  intro x
  by_cases hx : w x = 0
  · simp [g, hx, hC]
  · simpa [g, hx] using hf x hx

/-- APAP's normalized measure agrees with the counting-probability indicator
used by the local Bohr files. -/
lemma mu_eq_normalizedIndicator (S : Finset G) :
    μ_[ℝ] S = normalizedIndicator S := by
  funext x
  by_cases hx : x ∈ S <;> simp [mu_apply, normalizedIndicator, hx]

/-- A mixed normalized correlation with a rank-regular Bohr measure is close
to the constant `1 / |B|` on a narrow dilate. -/
lemma abs_mixedCorrelation_sub_inv_card_le
    {B : BohrData G} (hreg : B.IsRankRegular)
    {A : Finset G} (hA : A.Nonempty) (hAB : A ⊆ B.carrier)
    {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    {t : G} (ht : t ∈ (B.dilate kappa).carrier) :
    |(μ_[ℝ] A ○ᵈ μ B.carrier) t - (B.carrier.card : ℝ)⁻¹| ≤
      (A.card : ℝ)⁻¹ *
        (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) := by
  have hB : B.carrier.Nonempty := B.carrier_nonempty
  have hbase :
      ∑ x : G, μ_[ℝ] A x * μ B.carrier x =
        (B.carrier.card : ℝ)⁻¹ := by
    calc
      ∑ x : G, μ_[ℝ] A x * μ B.carrier x =
          ∑ x : G, μ_[ℝ] A x * (B.carrier.card : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ A
        · rw [mu_apply, mu_apply]
          simp [hx, hAB hx]
        · simp [mu_apply, hx]
      _ = (B.carrier.card : ℝ)⁻¹ := by
        rw [← Finset.sum_mul, sum_mu ℝ hA, one_mul]
  have htranslate :
      ∑ x : G, |μ_[ℝ] B.carrier (x - t) - μ B.carrier x| ≤
        200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ) := by
    simpa only [mu_eq_normalizedIndicator] using
      B.sum_abs_normalizedIndicator_translate_le_of_rankRegular hreg hkappa ht
  rw [dddconv_eq_sum_sub']
  simp only [starRingEnd_apply, star_trivial]
  rw [← hbase]
  rw [← Finset.sum_sub_distrib]
  have hrearrange :
      (∑ x : G, (μ_[ℝ] A x * μ B.carrier (x - t) -
        μ A x * μ B.carrier x)) =
      ∑ x : G, μ_[ℝ] A x *
        (μ B.carrier (x - t) - μ B.carrier x) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hrearrange]
  calc
    |∑ x : G, μ_[ℝ] A x *
        (μ B.carrier (x - t) - μ B.carrier x)| ≤
        ∑ x : G, |μ_[ℝ] A x *
          (μ B.carrier (x - t) - μ B.carrier x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x : G, μ_[ℝ] A x *
          |μ B.carrier (x - t) - μ B.carrier x| := by
      apply Finset.sum_congr rfl
      intro x _
      have hmuAx : 0 ≤ μ_[ℝ] A x := by
        rw [mu_apply]
        positivity
      rw [abs_mul, abs_of_nonneg hmuAx]
    _ ≤ ∑ x : G, (A.card : ℝ)⁻¹ *
          |μ_[ℝ] B.carrier (x - t) - μ B.carrier x| := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [mu_apply]
      split_ifs <;> simp
    _ = (A.card : ℝ)⁻¹ *
          ∑ x : G, |μ_[ℝ] B.carrier (x - t) - μ B.carrier x| := by
      rw [Finset.mul_sum]
    _ ≤ (A.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) :=
      mul_le_mul_of_nonneg_left htranslate (by positivity)

/-- Expansion of the balanced autocorrelation, with every Bohr-boundary term
estimated explicitly. -/
lemma abs_positive_sub_baseline_add_balanced_le
    {B : BohrData G} (hreg : B.IsRankRegular)
    {A : Finset G} (hA : A.Nonempty) (hAB : A ⊆ B.carrier)
    {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    {t : G} (ht : t ∈ (B.dilate kappa).carrier) :
    |(μ_[ℝ] A ○ᵈ μ A) t -
        ((B.carrier.card : ℝ)⁻¹ +
          ((μ_[ℝ] A - μ B.carrier) ○ᵈ
            (μ A - μ B.carrier)) t)| ≤
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
        (B.carrier.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) := by
  let m : ℝ := (B.carrier.card : ℝ)⁻¹
  let eA : ℝ := (A.card : ℝ)⁻¹ *
    (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ))
  let eB : ℝ := (B.carrier.card : ℝ)⁻¹ *
    (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ))
  have hmix := abs_mixedCorrelation_sub_inv_card_le hreg hA hAB hkappa ht
  have hmixNeg := abs_mixedCorrelation_sub_inv_card_le hreg hA hAB hkappa
    (BohrData.neg_mem_carrier.mpr ht)
  have hreverse :
      |(μ_[ℝ] B.carrier ○ᵈ μ A) t - m| ≤ eA := by
    have hsym : (μ_[ℝ] B.carrier ○ᵈ μ A) t =
        (μ A ○ᵈ μ B.carrier) (-t) := by
      have h := dddconv_apply_neg (μ_[ℝ] A) (μ_[ℝ] B.carrier) t
      simpa using h.symm
    simpa [m, eA, hsym] using hmixNeg
  have hself := abs_mixedCorrelation_sub_inv_card_le hreg
    B.carrier_nonempty (fun _ h ↦ h) hkappa ht
  have hsum :
      |((μ_[ℝ] A ○ᵈ μ B.carrier) t - m) +
        ((μ B.carrier ○ᵈ μ A) t - m) -
        ((μ B.carrier ○ᵈ μ B.carrier) t - m)| ≤
          2 * eA + eB := by
    calc
      |((μ_[ℝ] A ○ᵈ μ B.carrier) t - m) +
          ((μ B.carrier ○ᵈ μ A) t - m) -
          ((μ B.carrier ○ᵈ μ B.carrier) t - m)| ≤
          |(μ_[ℝ] A ○ᵈ μ B.carrier) t - m| +
          |(μ B.carrier ○ᵈ μ A) t - m| +
          |(μ B.carrier ○ᵈ μ B.carrier) t - m| := by
            have hsub := abs_sub
              (((μ_[ℝ] A ○ᵈ μ B.carrier) t - m) +
                ((μ B.carrier ○ᵈ μ A) t - m))
              ((μ B.carrier ○ᵈ μ B.carrier) t - m)
            have hadd := abs_add_le
              ((μ_[ℝ] A ○ᵈ μ B.carrier) t - m)
              ((μ B.carrier ○ᵈ μ A) t - m)
            linarith
      _ ≤ eA + eA + eB := by gcongr
      _ = 2 * eA + eB := by ring
  have hexpand :
      (μ_[ℝ] A ○ᵈ μ A) t -
          (m + ((μ A - μ B.carrier) ○ᵈ
            (μ A - μ B.carrier)) t) =
        ((μ A ○ᵈ μ B.carrier) t - m) +
        ((μ B.carrier ○ᵈ μ A) t - m) -
        ((μ B.carrier ○ᵈ μ B.carrier) t - m) := by
    simp only [sub_dddconv, dddconv_sub, Pi.sub_apply]
    ring
  simpa [m, eA, eB, hexpand] using hsum

/-- Autocorrelation representation of the balanced autocorrelation after
normalizing its natural scale `1 / |B|` to one. -/
lemma scaled_balanced_autocorrelation
    (A K : Finset G) :
    ((Real.sqrt (K.card : ℝ) : ℂ) •
          ((↑) ∘ (μ_[ℝ] A - μ K) : G → ℂ)) ○ᵈ
        ((Real.sqrt (K.card : ℝ) : ℂ) •
          ((↑) ∘ (μ_[ℝ] A - μ K) : G → ℂ)) =
      (↑) ∘ ((K.card : ℝ) •
        ((μ_[ℝ] A - μ K) ○ᵈ (μ A - μ K))) := by
  rw [smul_dddconv, dddconv_smul]
  rw [← Complex.ofReal_comp_dddconv]
  funext x
  simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_mul,
    starRingEnd_apply]
  rw [show star (↑(Real.sqrt (K.card : ℝ)) : ℂ) =
      ↑(Real.sqrt (K.card : ℝ)) by simp]
  rw [← mul_assoc]
  norm_cast
  rw [← pow_two, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ K.card)]

/-- The readable rank-scale width bound implies the boundary-error inequality
used by `localized_unbalancing`.  Since `|A| / |B|` is the relative density,
the premise is exactly `kappa ≤ epsilon * alpha / (4800 * d)`. -/
lemma boundary_error_of_rank_width
    {B : BohrData G} {A : Finset G} (hA : A.Nonempty) (hAB : A ⊆ B.carrier)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) {kappa : ℝ≥0}
    (hwidth : (kappa : ℝ) ≤
      epsilon * (A.card : ℝ) /
        (4800 * ((max B.rank 1 : ℕ) : ℝ) * (B.carrier.card : ℝ))) :
    2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
        (B.carrier.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
      epsilon / 8 * (B.carrier.card : ℝ)⁻¹ := by
  let a : ℝ := A.card
  let b : ℝ := B.carrier.card
  let d : ℝ := max B.rank 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hB : B.carrier.Nonempty := B.carrier_nonempty
  have hb : 0 < b := by dsimp [b]; positivity
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hab : a ≤ b := by dsimp [a, b]; exact_mod_cast Finset.card_le_card hAB
  have hscaled :
      (2 * a⁻¹ * (200 * d) + b⁻¹ * (200 * d)) * (kappa : ℝ) ≤
        (2 * a⁻¹ * (200 * d) + b⁻¹ * (200 * d)) *
          (epsilon * (A.card : ℝ) /
            (4800 * ((max B.rank 1 : ℕ) : ℝ) * (B.carrier.card : ℝ))) :=
    mul_le_mul_of_nonneg_left hwidth (by positivity)
  have hcoeff : 1600 * (2 * b + a) ≤ 4800 * b := by nlinarith
  have hprod :
      1600 * (2 * b + a) * ((kappa : ℝ) * d) ≤
        4800 * b * ((kappa : ℝ) * d) :=
    mul_le_mul_of_nonneg_right hcoeff (by positivity)
  dsimp [a, b, d] at hscaled hprod ⊢
  field_simp [ha.ne', hb.ne', hd.ne'] at hscaled ⊢
  nlinarith [hprod]

/-- **Localized unbalancing on a rank-regular Bohr carrier.**

The smoothing weight is the explicit autocorrelation `smoothingWeight D E`;
there is no spectral-positivity assumption.  The geometric hypothesis
`hwidth` is exactly what follows from
`kappa ≤ epsilon * alpha / (4800 * max(rank B,1))` after writing
`alpha = |A| / |B|`. -/
theorem localized_unbalancing
    {B : BohrData G} (hreg : B.IsRankRegular)
    {A : Finset G} (hA : A.Nonempty) (hAB : A ⊆ B.carrier)
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hsupport : ∀ t, smoothingWeight D E t ≠ 0 →
      t ∈ (B.dilate kappa).carrier)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hwidth :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
        (B.carrier.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
        epsilon / 8 * (B.carrier.card : ℝ)⁻¹)
    {p : ℕ} (hp : 0 < p)
    (hlarge :
      epsilon * (B.carrier.card : ℝ)⁻¹ / 2 <
        BalancedRestriction.weightedLpNorm
          ((↑) ∘ smoothingWeight D E)
          ((μ_[ℝ] A - μ B.carrier) ○ᵈ
            (μ A - μ B.carrier))
          (BalancedRestriction.comparisonExponent p)) :
    ∃ r : ℕ, 0 < r ∧ Even r ∧
      r ≤ BalancedRestriction.stoppingExponent epsilon p ∧
      (1 + epsilon / 8) * (B.carrier.card : ℝ)⁻¹ ≤
        BalancedRestriction.weightedLpNorm
          ((↑) ∘ smoothingWeight D E) (μ_[ℝ] A ○ᵈ μ A) r := by
  let K := B.carrier
  let nu := smoothingWeight D E
  let balanced : G → ℝ := μ_[ℝ] A - μ K
  let corr : G → ℝ := balanced ○ᵈ balanced
  let positive : G → ℝ := μ_[ℝ] A ○ᵈ μ A
  let main : ℝ := (K.card : ℝ)⁻¹
  let f : G → ℝ := (K.card : ℝ) • corr
  let surrogate : G → ℝ := main • (f + 1)
  have hK : K.Nonempty := B.carrier_nonempty
  have hKcard : (0 : ℝ) < K.card := by exact_mod_cast hK.card_pos
  have hmain : 0 < main := by simp [main, hKcard]
  have hmass : ∑ x : G, nu x = 1 := smoothingWeight_sum hD hE
  have hprob : BalancedRestriction.ProbabilityWeight ((↑) ∘ nu) :=
    ⟨fun x ↦ by exact_mod_cast (show 0 ≤ nu x by exact smoothingWeight_nonneg D E x),
      by simpa using congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) hmass⟩
  have hfrep :
      ((Real.sqrt (K.card : ℝ) : ℂ) • ((↑) ∘ balanced : G → ℂ)) ○ᵈ
          ((Real.sqrt (K.card : ℝ) : ℂ) • ((↑) ∘ balanced : G → ℂ)) =
        (↑) ∘ f := by
    simpa [K, balanced, corr, f] using scaled_balanced_autocorrelation A K
  have hnurep :
      ((↑) ∘ smoothingBase D E : G → ℂ) ○ᵈ
          ((↑) ∘ smoothingBase D E) = (↑) ∘ nu := by
    simpa [nu] using smoothingWeight_autocorrelation D E
  have hmom : ∀ k : ℕ, 0 ≤ weightedMoment ((↑) ∘ nu) f k := by
    intro k
    have h := physical_pow_inner_nonneg hfrep hnurep k
    simpa [weightedMoment, wInner_one_eq_sum, RCLike.inner_apply, mul_comm] using h
  have hcardmain : (K.card : ℝ) * main = 1 := by
    simp [main, ne_of_gt hKcard]
  have hlargeF : epsilon / 2 <
      BalancedRestriction.weightedLpNorm ((↑) ∘ nu) f
        (BalancedRestriction.comparisonExponent p) := by
    rw [show f = (K.card : ℝ) • corr by rfl,
      weightedLpNorm_smul_of_nonneg nu corr (K.card : ℝ) (by positivity)
        (by simp [BalancedRestriction.comparisonExponent, hp])]
    have hlarge' : epsilon * main / 2 <
        BalancedRestriction.weightedLpNorm ((↑) ∘ nu) corr
          (BalancedRestriction.comparisonExponent p) := by
      simpa [K, nu, balanced, corr, main] using hlarge
    nlinarith
  let qOdd := BalancedRestriction.unbalancingInputExponent p
  have hqOdd : 0 < qOdd := by
    have := BalancedRestriction.five_le_unbalancingInputExponent hp
    omega
  have hpromote := BalancedRestriction.weightedLpNorm_comparison_le_unbalancingInput
    hprob hp (f := f)
  have hlargeOdd : epsilon / 2 <
      BalancedRestriction.weightedLpNorm ((↑) ∘ nu) f qOdd := by
    exact hlargeF.trans_le (by simpa [qOdd] using hpromote)
  have hmomentLarge : (epsilon / 2) ^ qOdd ≤
      weightedAbsMoment ((↑) ∘ nu) f qOdd := by
    calc
      (epsilon / 2) ^ qOdd ≤
          BalancedRestriction.weightedLpNorm ((↑) ∘ nu) f qOdd ^ qOdd :=
        pow_le_pow_left₀ (by positivity) hlargeOdd.le qOdd
      _ = weightedAbsMoment ((↑) ∘ nu) f qOdd :=
        BalancedRestriction.weightedLpNorm_pow hprob hqOdd
  have hscale : ∀ x, surrogate x = main * (1 + f x) := by
    intro x
    simp [surrogate, smul_eq_mul, add_comm]
    ring
  obtain ⟨r, hr, hreven, hrBound, hsurrogate⟩ :=
    BalancedRestriction.unbalancing_of_exact_scaling hprob
      (f := f) (positiveCorr := surrogate) (η := epsilon / 2)
      (mainTerm := main) (by positivity) (by linarith) hmain
      (BalancedRestriction.five_le_unbalancingInputExponent hp)
      (BalancedRestriction.unbalancingInputExponent_odd p) hmom hmomentLarge hscale
  have hrStop : r ≤ BalancedRestriction.stoppingExponent epsilon p := by
    simpa [BalancedRestriction.stoppingExponent, qOdd] using hrBound
  have herrorPoint : ∀ x, nu x ≠ 0 → |positive x - surrogate x| ≤ epsilon / 8 * main := by
    intro x hx
    have hb := abs_positive_sub_baseline_add_balanced_le hreg hA hAB hkappa
      (hsupport x hx)
    have hsurrogatePoint : surrogate x = main + corr x := by
      simp [surrogate, f, smul_eq_mul]
      rw [← mul_assoc, show main * (K.card : ℝ) = 1 by nlinarith, one_mul]
      ring
    simpa [K, balanced, corr, positive, main, hsurrogatePoint] using hb.trans hwidth
  have herror :
      BalancedRestriction.weightedLpNorm ((↑) ∘ nu) (positive - surrogate) r ≤
        epsilon / 8 * main := by
    apply weightedLpNorm_le_of_abs_le_on_support hmass
      (mul_nonneg (by positivity) hmain.le) hr
    intro x hx
    simpa [Pi.sub_apply] using herrorPoint x hx
  have htriangle := weightedLpNorm_le_add_of_add nu surrogate (positive - surrogate)
    (Nat.succ_le_iff.mpr hr)
  have hadd : surrogate + (positive - surrogate) = positive := by ext x; simp
  rw [hadd] at htriangle
  refine ⟨r, hr, hreven, hrStop, ?_⟩
  simpa [K, nu, positive, main] using (by nlinarith [hsurrogate, htriangle, herror])

end

end LocalizedUnbalancing
end Erdos140

#print axioms Erdos140.LocalizedUnbalancing.smoothingWeight_autocorrelation
#print axioms Erdos140.LocalizedUnbalancing.weightedLpNorm_eq_wLpNorm
#print axioms Erdos140.LocalizedUnbalancing.boundary_error_of_rank_width
#print axioms Erdos140.LocalizedUnbalancing.localized_unbalancing
