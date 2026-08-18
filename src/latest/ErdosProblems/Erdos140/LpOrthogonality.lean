import ErdosProblems.Erdos140.FiniteFourier
import ErdosProblems.Erdos140.FiniteConvolution
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Data.Fintype.Pi

/-!
# Even-moment Fourier orthogonality

This file isolates the phase-removal argument used in the balanced-restriction
step for Erdős Problem 140.  All averages are normalized Fintype expectations.
For a positive even natural number `p` we prove that the `p`-th moment of
`f * f` is at most the corresponding moment of `f ○ f`.  We also record the
weighted, translated version: translation contributes only a unit-modulus
character, while a spectrally nonnegative weight contributes nonnegative
Fourier coefficients, so the same triangle-inequality argument applies.
-/

noncomputable section

open AddChar Finset Fintype Function RCLike
open scoped BigOperators ComplexConjugate

namespace Erdos140.LpOrthogonality

open FiniteFourier

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The normalized absolute `p`-th moment on a finite type. -/
def absMoment (f : G → ℂ) (p : ℕ) : ℝ :=
  𝔼 x : G, ‖f x‖ ^ p

/-- A normalized absolute moment with a real physical-space weight. -/
def weightedAbsMoment (nu : G → ℝ) (f : G → ℂ) (p : ℕ) : ℝ :=
  𝔼 x : G, nu x * ‖f x‖ ^ p

/-- Natural-exponent weighted `L^p` norm. -/
def weightedLpNorm (nu : G → ℝ) (f : G → ℂ) (p : ℕ) : ℝ :=
  if p = 0 then 0 else (weightedAbsMoment nu f p) ^ (1 / (p : ℝ))

/-- The Fourier character average of a real weight.  This is the Fourier
coefficient at the inverse character; using this convention makes translation
by `t` contribute the factor `chi t` below. -/
def characterAverage (nu : G → ℝ) (chi : AddChar G ℂ) : ℂ :=
  𝔼 x : G, (nu x : ℂ) * chi x

/-- A real weight is spectrally nonnegative when all its character averages
are nonnegative real numbers.  Equivalently, all of its normalized Fourier
coefficients are nonnegative (inversion of the character only permutes the
dual group). -/
def SpectrallyNonnegative (nu : G → ℝ) : Prop :=
  ∀ chi : AddChar G ℂ,
    0 ≤ (characterAverage nu chi).re ∧ (characterAverage nu chi).im = 0

lemma ofReal_countingConvolution (a b : G → ℝ) (x : G) :
    (Erdos140.normalizedConvolution a b x : ℂ) =
      (Fintype.card G : ℂ) *
        FiniteFourier.convolution ((↑) ∘ a) ((↑) ∘ b) x := by
  unfold Erdos140.normalizedConvolution FiniteFourier.convolution
  rw [Fintype.expect_eq_sum_div_card]
  push_cast
  field_simp
  simp [Function.comp_apply]

lemma ofReal_countingAutocorrelation (a : G → ℝ) (x : G) :
    (Erdos140.normalizedDifferenceConvolution a a x : ℂ) =
      (Fintype.card G : ℂ) *
        differenceConvolution ((↑) ∘ a) ((↑) ∘ a) x := by
  unfold Erdos140.normalizedDifferenceConvolution FiniteFourier.differenceConvolution
  rw [Fintype.expect_eq_sum_div_card]
  push_cast
  field_simp
  refine Fintype.sum_equiv (Equiv.subRight x) _ _ fun y ↦ ?_
  simp

lemma characterAverage_eq_ofReal {nu : G → ℝ}
    (hnu : SpectrallyNonnegative nu) (chi : AddChar G ℂ) :
    characterAverage nu chi = ((characterAverage nu chi).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using (hnu chi).2

lemma characterAverage_translate (nu : G → ℝ) (chi : AddChar G ℂ) (t : G) :
    (𝔼 x : G, (nu (x - t) : ℂ) * chi x) = chi t * characterAverage nu chi := by
  unfold characterAverage
  rw [mul_expect]
  refine Fintype.expect_equiv (M := ℂ) (Equiv.subRight t : G ≃ G) _ _ fun y ↦ ?_
  simp only [Equiv.subRight_apply, sub_eq_add_neg]
  have hc : chi y = chi t * chi (y + -t) := by
    rw [← map_add_eq_mul]
    congr 1
    abel
  rw [hc]
  ring

lemma norm_characterAverage_translate {nu : G → ℝ}
    (hnu : SpectrallyNonnegative nu) (chi : AddChar G ℂ) (t : G) :
    ‖𝔼 x : G, (nu (x - t) : ℂ) * chi x‖ = (characterAverage nu chi).re := by
  rw [characterAverage_translate, norm_mul, AddChar.norm_apply,
    one_mul, characterAverage_eq_ofReal hnu]
  simp [abs_of_nonneg (hnu chi).1]

/-- A counting convolution of two counting autocorrelations has nonnegative
spectrum.  Its normalized Fourier model carries the exact factor `|G|^3`. -/
theorem spectrallyNonnegative_counting_autocorrelation_convolution
    (a b : G → ℝ) :
    SpectrallyNonnegative
      (Erdos140.normalizedConvolution
        (Erdos140.normalizedDifferenceConvolution a a)
        (Erdos140.normalizedDifferenceConvolution b b)) := by
  let ac : G → ℂ := (↑) ∘ a
  let bc : G → ℂ := (↑) ∘ b
  let da : G → ℂ := differenceConvolution ac ac
  let db : G → ℂ := differenceConvolution bc bc
  let h : G → ℂ := FiniteFourier.convolution da db
  have hweight (x : G) :
      (Erdos140.normalizedConvolution
          (Erdos140.normalizedDifferenceConvolution a a)
          (Erdos140.normalizedDifferenceConvolution b b) x : ℂ) =
        (Fintype.card G : ℂ) ^ 3 * h x := by
    rw [ofReal_countingConvolution]
    have hua : ((↑) ∘ Erdos140.normalizedDifferenceConvolution a a) =
        fun y ↦ (Fintype.card G : ℂ) * da y := by
      funext y
      exact ofReal_countingAutocorrelation a y
    have hub : ((↑) ∘ Erdos140.normalizedDifferenceConvolution b b) =
        fun y ↦ (Fintype.card G : ℂ) * db y := by
      funext y
      exact ofReal_countingAutocorrelation b y
    rw [hua, hub]
    simp only [h, da, db, FiniteFourier.convolution,
      Fintype.expect_eq_sum_div_card]
    have hcard : (Fintype.card G : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  intro chi
  have havg :
      characterAverage
          (Erdos140.normalizedConvolution
            (Erdos140.normalizedDifferenceConvolution a a)
            (Erdos140.normalizedDifferenceConvolution b b)) chi =
        (Fintype.card G : ℂ) ^ 3 * coeff h (-chi) := by
    unfold characterAverage
    simp_rw [hweight]
    calc
      (𝔼 x : G, (Fintype.card G : ℂ) ^ 3 * h x * chi x) =
          (Fintype.card G : ℂ) ^ 3 * (𝔼 x : G, h x * chi x) := by
        calc
          _ = 𝔼 x : G, (Fintype.card G : ℂ) ^ 3 * (h x * chi x) := by
            congr 1 with x
            ring
          _ = _ := by rw [← mul_expect]
      _ = _ := by
        congr 1
        simp [coeff, wInner_cWeight_eq_expect, inner_apply, map_neg_eq_conj]
  have hreal :
      characterAverage
          (Erdos140.normalizedConvolution
            (Erdos140.normalizedDifferenceConvolution a a)
            (Erdos140.normalizedDifferenceConvolution b b)) chi =
        (((Fintype.card G : ℝ) ^ 3 * Complex.normSq (coeff ac (-chi)) *
          Complex.normSq (coeff bc (-chi)) : ℝ) : ℂ) := by
    rw [havg]
    simp only [h, coeff_convolution, da, db, coeff_autocorrelation]
    push_cast
    ring
  rw [hreal]
  constructor
  · simpa only [Complex.ofReal_re] using
      (mul_nonneg
      (mul_nonneg (by positivity) (Complex.normSq_nonneg _))
      (Complex.normSq_nonneg _))
  · exact Complex.ofReal_im _

lemma absMoment_nonneg (f : G → ℂ) (p : ℕ) : 0 ≤ absMoment f p := by
  exact expect_nonneg fun _ _ ↦ pow_nonneg (norm_nonneg _) _

/-- The natural-exponent normalized `L^p` norm.  Exponent zero is assigned
zero; all substantive results below assume the exponent is positive. -/
def lpNorm (f : G → ℂ) (p : ℕ) : ℝ :=
  if p = 0 then 0 else (absMoment f p) ^ (1 / (p : ℝ))

lemma lpNorm_of_pos (f : G → ℂ) {p : ℕ} (hp : 0 < p) :
    lpNorm f p = (absMoment f p) ^ (1 / (p : ℝ)) := by
  simp [lpNorm, hp.ne']

lemma lpNorm_nonneg (f : G → ℂ) (p : ℕ) : 0 ≤ lpNorm f p := by
  unfold lpNorm
  split
  · exact le_rfl
  · exact Real.rpow_nonneg (absMoment_nonneg f p) _

/-- Expansion of an even normalized moment of a finite Fourier polynomial.
The two tuples index the `k` conjugated and `k` unconjugated factors. -/
lemma absMoment_two_mul_sum_pow {I : Type*} {k : ℕ} (hk : k ≠ 0)
    (s : Finset I) (u : I → G → ℂ) :
    (absMoment (∑ i ∈ s, u i) (2 * k) : ℂ) =
      ∑ x ∈ s ^^ k, ∑ y ∈ s ^^ k,
        𝔼 a : G, (∏ i, conj (u (x i) a)) * ∏ i, u (y i) a := by
  rw [absMoment]
  push_cast
  simp_rw [Finset.sum_apply]
  calc
    (𝔼 a : G, (‖∑ i ∈ s, u i a‖ : ℂ) ^ (2 * k)) =
        𝔼 a : G, (∑ i ∈ s, conj (u i a)) ^ k *
          (∑ j ∈ s, u j a) ^ k := by
      congr 1 with a
      simp_rw [pow_mul, ← Complex.conj_mul', mul_pow, map_sum]
    _ = _ := by
      simp_rw [sum_pow', Finset.sum_mul_sum, expect_sum_comm]

/-- Weighted version of `absMoment_two_mul_sum_pow`. -/
lemma weightedAbsMoment_two_mul_sum_pow {I : Type*} {k : ℕ} (_hk : k ≠ 0)
    (nu : G → ℝ) (s : Finset I) (u : I → G → ℂ) :
    (weightedAbsMoment nu (∑ i ∈ s, u i) (2 * k) : ℂ) =
      ∑ x ∈ s ^^ k, ∑ y ∈ s ^^ k,
        𝔼 a : G, (nu a : ℂ) *
          ((∏ i, conj (u (x i) a)) * ∏ i, u (y i) a) := by
  rw [weightedAbsMoment]
  push_cast
  simp_rw [Finset.sum_apply]
  calc
    (𝔼 a : G, (nu a : ℂ) * (‖∑ i ∈ s, u i a‖ : ℂ) ^ (2 * k)) =
        𝔼 a : G, (nu a : ℂ) *
          ((∑ i ∈ s, conj (u i a)) ^ k * (∑ j ∈ s, u j a) ^ k) := by
      congr 1 with a
      simp_rw [pow_mul, ← Complex.conj_mul', mul_pow, map_sum]
    _ = _ := by
      simp_rw [sum_pow', Finset.sum_mul_sum, mul_sum, expect_sum_comm]

/-- **Unweighted `L^p` orthogonality / phase removal.**  For a positive even
natural exponent, additive convolution has no larger normalized moment than
autocorrelation. -/
theorem absMoment_convolution_le_autocorrelation {p : ℕ} (hp : p ≠ 0)
    (heven : Even p) (f : G → ℂ) :
    absMoment (convolution f f) p ≤ absMoment (differenceConvolution f f) p := by
  obtain ⟨k, rfl⟩ := heven.two_dvd
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hp
  refine Complex.le_of_eq_sum_of_eq_sum_norm
    (fun ψ : (Fin k → AddChar G ℂ) × (Fin k → AddChar G ℂ) ↦
      conj (∏ i, coeff f (ψ.1 i) ^ 2) *
        (∏ i, coeff f (ψ.2 i) ^ 2) *
          (𝔼 x : G, (∑ i, ψ.2 i - ∑ i, ψ.1 i) x))
    univ (absMoment_nonneg _ _) ?_ ?_
  · push_cast
    have hinv : convolution f f =
        ∑ χ : AddChar G ℂ, fun x ↦ coeff (convolution f f) χ * χ x := by
      funext x
      simpa only [Finset.sum_apply] using (inversion (convolution f f) x).symm
    rw [hinv]
    have hm := absMoment_two_mul_sum_pow (G := G) hp
      (univ : Finset (AddChar G ℂ))
      (fun χ x ↦ coeff (convolution f f) χ * χ x)
    rw [hm]
    simp_rw [coeff_convolution, ← sq,
      Fintype.sum_prod_type, mul_expect, AddChar.sub_apply]
    simp [mul_mul_mul_comm, mul_comm, map_neg_eq_conj, prod_mul_distrib]
  · push_cast
    have hinv : differenceConvolution f f =
        ∑ χ : AddChar G ℂ, fun x ↦ coeff (differenceConvolution f f) χ * χ x := by
      funext x
      simpa only [Finset.sum_apply] using
        (inversion (differenceConvolution f f) x).symm
    rw [hinv]
    have hm := absMoment_two_mul_sum_pow (G := G) hp
      (univ : Finset (AddChar G ℂ))
      (fun χ x ↦ coeff (differenceConvolution f f) χ * χ x)
    rw [hm]
    simp_rw [coeff_differenceConvolution, Complex.mul_conj',
      Fintype.sum_prod_type, mul_expect]
    congr 1 with ψ
    congr 1 with φ
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, Complex.conj_ofReal,
      prod_mul_distrib, mul_mul_mul_comm, ← mul_expect, map_prod, AddChar.sub_apply,
      AddChar.coe_sum, Finset.prod_apply, norm_mul, norm_prod, norm_pow, RCLike.norm_conj,
      Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_pow]
    congr 1
    calc
      𝔼 x : G, (∏ i, conj (ψ i x)) * ∏ i, φ i x =
          𝔼 x : G, (∑ i, φ i - ∑ i, ψ i) x := by
        simp [map_neg_eq_conj, mul_comm, AddChar.sub_apply]
      _ = ‖𝔼 x : G, (∑ i, φ i - ∑ i, ψ i) x‖ := by
        simp [expect_eq_ite, apply_ite]
      _ = ‖𝔼 x : G, (∏ i, φ i x) * ∏ i, (ψ i) (-x)‖ := by
        simp [map_neg_eq_conj, AddChar.sub_apply]

/-- Root form of unweighted `L^p` orthogonality. -/
theorem lpNorm_convolution_le_autocorrelation {p : ℕ} (hp : p ≠ 0)
    (heven : Even p) (f : G → ℂ) :
    lpNorm (convolution f f) p ≤ lpNorm (differenceConvolution f f) p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
  rw [lpNorm_of_pos _ (Nat.pos_of_ne_zero hp), lpNorm_of_pos _ (Nat.pos_of_ne_zero hp)]
  exact Real.rpow_le_rpow (absMoment_nonneg _ _)
    (absMoment_convolution_le_autocorrelation hp heven f)
    (div_nonneg zero_le_one hpR.le)

lemma weightedAbsMoment_nonneg {nu : G → ℝ} (hnu : ∀ x, 0 ≤ nu x)
    (f : G → ℂ) (p : ℕ) : 0 ≤ weightedAbsMoment nu f p := by
  exact expect_nonneg fun x _ ↦ mul_nonneg (hnu x) (pow_nonneg (norm_nonneg _) _)

lemma weightedLpNorm_of_pos (nu : G → ℝ) (f : G → ℂ) {p : ℕ} (hp : 0 < p) :
    weightedLpNorm nu f p = (weightedAbsMoment nu f p) ^ (1 / (p : ℝ)) := by
  simp [weightedLpNorm, hp.ne']

lemma weightedLpNorm_nonneg {nu : G → ℝ} (hnu : ∀ x, 0 ≤ nu x)
    (f : G → ℂ) (p : ℕ) : 0 ≤ weightedLpNorm nu f p := by
  unfold weightedLpNorm
  split
  · exact le_rfl
  · exact Real.rpow_nonneg (weightedAbsMoment_nonneg hnu f p) _

/-- The numerical loss used when passing from a moment estimate with a factor
`2` to its `p`-th-root form. -/
lemma half_le_two_rpow_neg_one_div_nat {p : ℕ} (hp : 0 < p) :
    (1 / 2 : ℝ) ≤ 2 ^ (-(1 / (p : ℝ))) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hq_le : 1 / (p : ℝ) ≤ 1 := by
    exact (div_le_one hpR).2 (by exact_mod_cast hp)
  have h := Real.rpow_le_rpow_of_exponent_ge
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hq_le
  rw [Real.rpow_one] at h
  calc
    (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 / (p : ℝ)) := h
    _ = 2 ^ (-(1 / (p : ℝ))) := by
      rw [Real.rpow_neg_eq_inv_rpow]
      norm_num

/-- Hölder-style root lifting: a factor `2` in a positive `p`-th-moment
estimate costs exactly `2⁻¹ᵖ` after taking `p`-th roots. -/
theorem two_rpow_neg_one_div_mul_weightedLpNorm_le_of_moment_le_two_mul
    {mu nu : G → ℝ} (hmu : ∀ x, 0 ≤ mu x) (hnu : ∀ x, 0 ≤ nu x)
    {f g : G → ℂ} {p : ℕ} (hp : 0 < p)
    (h : weightedAbsMoment mu f p ≤ 2 * weightedAbsMoment nu g p) :
    2 ^ (-(1 / (p : ℝ))) * weightedLpNorm mu f p ≤ weightedLpNorm nu g p := by
  rw [weightedLpNorm_of_pos _ _ hp, weightedLpNorm_of_pos _ _ hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hq : 0 ≤ 1 / (p : ℝ) := div_nonneg zero_le_one hpR.le
  have hroot := Real.rpow_le_rpow (weightedAbsMoment_nonneg hmu f p) h hq
  calc
    2 ^ (-(1 / (p : ℝ))) *
          weightedAbsMoment mu f p ^ (1 / (p : ℝ)) ≤
        2 ^ (-(1 / (p : ℝ))) *
          (2 * weightedAbsMoment nu g p) ^ (1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg (by norm_num) _)
    _ = weightedAbsMoment nu g p ^ (1 / (p : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (weightedAbsMoment_nonneg hnu g p)]
      rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      simp

/-- The convenient uniform version of the preceding root lifting: for every
positive natural `p`, the exact factor `2⁻¹ᵖ` is at least `1/2`. -/
theorem half_weightedLpNorm_le_of_moment_le_two_mul
    {mu nu : G → ℝ} (hmu : ∀ x, 0 ≤ mu x) (hnu : ∀ x, 0 ≤ nu x)
    {f g : G → ℂ} {p : ℕ} (hp : 0 < p)
    (h : weightedAbsMoment mu f p ≤ 2 * weightedAbsMoment nu g p) :
    (1 / 2 : ℝ) * weightedLpNorm mu f p ≤ weightedLpNorm nu g p := by
  exact (mul_le_mul_of_nonneg_right (half_le_two_rpow_neg_one_div_nat hp)
    (weightedLpNorm_nonneg hmu f p)).trans
      (two_rpow_neg_one_div_mul_weightedLpNorm_le_of_moment_le_two_mul
        hmu hnu hp h)

/-- Translated positive-definite-measure comparison. -/
theorem weightedAbsMoment_translate_convolution_le_autocorrelation
    {p : ℕ} (hp : p ≠ 0) (heven : Even p)
    (nu : G → ℝ) (hnu : ∀ x, 0 ≤ nu x)
    (hspec : SpectrallyNonnegative nu) (t : G) (f : G → ℂ) :
    weightedAbsMoment (fun x ↦ nu (x - t)) (convolution f f) p ≤
      weightedAbsMoment nu (differenceConvolution f f) p := by
  obtain ⟨k, rfl⟩ := heven.two_dvd
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hp
  let term : (Fin k → AddChar G ℂ) × (Fin k → AddChar G ℂ) → ℂ :=
    fun psi ↦
      conj (∏ i, coeff f (psi.1 i) ^ 2) *
        (∏ i, coeff f (psi.2 i) ^ 2) *
          (𝔼 x : G, (nu (x - t) : ℂ) *
            ((∑ i, psi.2 i - ∑ i, psi.1 i) x))
  refine Complex.le_of_eq_sum_of_eq_sum_norm term univ
    (weightedAbsMoment_nonneg (fun x ↦ hnu (x - t)) _ _) ?_ ?_
  · have hinv : convolution f f =
        ∑ chi : AddChar G ℂ, fun x ↦ coeff (convolution f f) chi * chi x := by
      funext x
      simpa only [Finset.sum_apply] using (inversion (convolution f f) x).symm
    rw [hinv]
    have hm := weightedAbsMoment_two_mul_sum_pow (G := G) hp
      (fun x ↦ nu (x - t)) (univ : Finset (AddChar G ℂ))
      (fun chi x ↦ coeff (convolution f f) chi * chi x)
    rw [hm]
    simp only [term]
    simp_rw [coeff_convolution, ← sq, Fintype.sum_prod_type, mul_expect,
      AddChar.sub_apply]
    simp [term, mul_mul_mul_comm, mul_comm, map_neg_eq_conj, prod_mul_distrib]
    ring
  · have hinv : differenceConvolution f f =
        ∑ chi : AddChar G ℂ,
          fun x ↦ coeff (differenceConvolution f f) chi * chi x := by
      funext x
      simpa only [Finset.sum_apply] using
        (inversion (differenceConvolution f f) x).symm
    rw [hinv]
    have hm := weightedAbsMoment_two_mul_sum_pow (G := G) hp nu
      (univ : Finset (AddChar G ℂ))
      (fun chi x ↦ coeff (differenceConvolution f f) chi * chi x)
    rw [hm]
    simp only [term]
    simp_rw [coeff_differenceConvolution, Complex.mul_conj',
      Fintype.sum_prod_type, mul_expect]
    congr 1 with psi
    congr 1 with phi
    simp only [map_mul, map_pow, prod_mul_distrib, mul_mul_mul_comm,
      ← mul_expect, map_prod, AddChar.sub_apply, AddChar.coe_sum,
      Finset.prod_apply, norm_mul, norm_prod, norm_pow, RCLike.norm_conj,
      Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_pow,
      Complex.conj_ofReal]
    have hchars :
        (𝔼 x : G, (nu x : ℂ) *
            ((∏ i, conj (psi i x)) * ∏ i, phi i x)) =
          characterAverage nu (∑ i, phi i - ∑ i, psi i) := by
      simp [characterAverage, map_neg_eq_conj, mul_comm, mul_left_comm,
        AddChar.sub_apply]
    let a : ℂ :=
      (∏ i, (‖coeff f (psi i)‖ ^ 2 : ℂ)) *
        ∏ i, (‖coeff f (phi i)‖ ^ 2 : ℂ)
    let c : ℂ :=
      conj (∏ i, coeff f (psi i) ^ 2) * ∏ i, coeff f (phi i) ^ 2
    let eta : AddChar G ℂ := ∑ i, phi i - ∑ i, psi i
    have hleft :
        (𝔼 x : G, (nu x : ℂ) *
            (a * ((∏ i, conj (psi i x)) * ∏ i, phi i x))) =
          a * characterAverage nu eta := by
      calc
        _ = 𝔼 x : G, a * ((nu x : ℂ) *
              ((∏ i, conj (psi i x)) * ∏ i, phi i x)) := by
            congr 1 with x
            ring
        _ = a * (𝔼 x : G, (nu x : ℂ) *
              ((∏ i, conj (psi i x)) * ∏ i, phi i x)) := by
            rw [← mul_expect]
        _ = _ := by simpa only [eta] using congrArg (a * ·) hchars
    have hinside :
        (𝔼 x : G, c * (nu (x - t) : ℂ) *
            ((∏ i, phi i x) * ∏ i, psi i (-x))) =
          c * (𝔼 x : G, (nu (x - t) : ℂ) * eta x) := by
      calc
        _ = 𝔼 x : G, c * ((nu (x - t) : ℂ) * eta x) := by
          congr 1 with x
          dsimp only [eta]
          simp [map_neg_eq_conj, AddChar.sub_apply, mul_comm, mul_left_comm]
          ring
        _ = _ := by rw [← mul_expect]
    have hgoal :
        (𝔼 x : G, (nu x : ℂ) *
            (a * ((∏ i, conj (psi i x)) * ∏ i, phi i x))) =
          (‖𝔼 x : G, c * (nu (x - t) : ℂ) *
            ((∏ i, phi i x) * ∏ i, psi i (-x))‖ : ℂ) := by
      rw [hleft, hinside, norm_mul,
        norm_characterAverage_translate hspec eta t]
      rw [characterAverage_eq_ofReal hspec]
      dsimp only [a, c]
      push_cast
      simp [abs_of_nonneg (hspec eta).1, norm_prod]
    simpa [a, c, pow_two, prod_mul_distrib, mul_assoc, mul_comm, mul_left_comm] using hgoal

/-- Root form of the translated positive-definite-measure comparison. -/
theorem weightedLpNorm_translate_convolution_le_autocorrelation
    {p : ℕ} (hp : p ≠ 0) (heven : Even p)
    (nu : G → ℝ) (hnu : ∀ x, 0 ≤ nu x)
    (hspec : SpectrallyNonnegative nu) (t : G) (f : G → ℂ) :
    weightedLpNorm (fun x ↦ nu (x - t)) (convolution f f) p ≤
      weightedLpNorm nu (differenceConvolution f f) p := by
  have hpN : 0 < p := Nat.pos_of_ne_zero hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpN
  rw [weightedLpNorm_of_pos _ _ hpN, weightedLpNorm_of_pos _ _ hpN]
  exact Real.rpow_le_rpow
    (weightedAbsMoment_nonneg (fun x ↦ hnu (x - t)) _ _)
    (weightedAbsMoment_translate_convolution_le_autocorrelation
      hp heven nu hnu hspec t f)
    (div_nonneg zero_le_one hpR.le)

/-- The translated comparison with unnormalized finite sums. -/
theorem sum_translate_convolution_le_autocorrelation
    {p : ℕ} (hp : p ≠ 0) (heven : Even p)
    (nu : G → ℝ) (hnu : ∀ x, 0 ≤ nu x)
    (hspec : SpectrallyNonnegative nu) (t : G) (f : G → ℂ) :
    ∑ x : G, nu (x - t) * ‖convolution f f x‖ ^ p ≤
      ∑ x : G, nu x * ‖differenceConvolution f f x‖ ^ p := by
  have h := weightedAbsMoment_translate_convolution_le_autocorrelation
    hp heven nu hnu hspec t f
  simp only [weightedAbsMoment, Fintype.expect_eq_sum_div_card] at h
  exact (div_le_div_iff_of_pos_right
    (by positivity : (0 : ℝ) < Fintype.card G)).mp h

#print axioms absMoment_convolution_le_autocorrelation
#print axioms lpNorm_convolution_le_autocorrelation
#print axioms spectrallyNonnegative_counting_autocorrelation_convolution
#print axioms two_rpow_neg_one_div_mul_weightedLpNorm_le_of_moment_le_two_mul
#print axioms half_weightedLpNorm_le_of_moment_le_two_mul
#print axioms weightedAbsMoment_translate_convolution_le_autocorrelation
#print axioms weightedLpNorm_translate_convolution_le_autocorrelation
#print axioms sum_translate_convolution_le_autocorrelation

end Erdos140.LpOrthogonality
