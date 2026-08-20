import ErdosProblems.Erdos783.GSSolutionUnique
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory Set
open scoped Convolution

namespace Erdos783

noncomputable section

/-- Associativity of real convolution under the concrete hypotheses used by
the locally finite kernel-change expansion.  The bounded third factor makes
the final three-variable Fubini integrand integrable at every evaluation
point, rather than merely almost everywhere. -/
theorem gs_convolution_assoc_of_integrable_bounded
    {f g k : ℝ → ℝ} {C x₀ : ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hk : Integrable k)
    (hkbound : ∀ x, ‖k x‖ ≤ C) :
    ((f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) ⋆[ContinuousLinearMap.mul ℝ ℝ] k) x₀ =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ]
        (g ⋆[ContinuousLinearMap.mul ℝ ℝ] k)) x₀ := by
  let M := ContinuousLinearMap.mul ℝ ℝ
  have hfgProd := hf.convolution_integrand M hg
  have hgkProd := hg.convolution_integrand M hk
  have hfg : ∀ᵐ y : ℝ, ConvolutionExistsAt f g y M := by
    simpa [ConvolutionExistsAt, M, ContinuousLinearMap.mul_apply'] using
      hfgProd.prod_right_ae
  have hgk : ∀ᵐ x : ℝ, ConvolutionExistsAt g k x M := by
    simpa [ConvolutionExistsAt, M, ContinuousLinearMap.mul_apply'] using
      hgkProd.prod_right_ae
  have hbase : Integrable
      (fun p : ℝ × ℝ ↦ f p.2 * g (p.1 - p.2)) := hfgProd
  have hktrans : AEStronglyMeasurable (fun x : ℝ ↦ k (x₀ - x)) :=
    hk.aestronglyMeasurable.comp_quasiMeasurePreserving
      (volume.measurePreserving_sub_left x₀).quasiMeasurePreserving
  have hkcomp : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ k (x₀ - p.1)) := hktrans.comp_fst
  have hi : Integrable
      (Function.uncurry fun x y : ℝ ↦ f y * (g (x - y) * k (x₀ - x))) := by
    have := hbase.mul_bdd hkcomp
      (Filter.Eventually.of_forall fun p ↦ hkbound (x₀ - p.1))
    change Integrable
      (fun p : ℝ × ℝ ↦ f p.2 * (g (p.1 - p.2) * k (x₀ - p.1)))
    simpa [mul_assoc] using this
  exact convolution_assoc' M M M M (by
      intro x y z
      simp [M, ContinuousLinearMap.mul_apply']
      ring)
    hfg hgk hi

/-- Commutativity of real-valued convolution. -/
lemma gs_convolution_comm (f g : ℝ → ℝ) :
    f ⋆[ContinuousLinearMap.mul ℝ ℝ] g =
      g ⋆[ContinuousLinearMap.mul ℝ ℝ] f := by
  simpa using
    (convolution_flip
      (L := ContinuousLinearMap.mul ℝ ℝ) (f := g) (g := f))

/-- Compactly localize a function to a positive interval.  The open
endpoints are deliberate: singletons are null, and for `0 ≤ x < K` the
two localized factors in a convolution are simultaneously nonzero exactly
on `0 < t < x`. -/
def gsLocalize (K : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (Ioo (0 : ℝ) K).indicator f

lemma integrable_gsLocalize {f : ℝ → ℝ} {K : ℝ} (_hK : 0 ≤ K)
    (hf : IntervalIntegrable f volume 0 K) : Integrable (gsLocalize K f) := by
  have h := hf.1
  have h' : IntegrableOn f (Ioo (0 : ℝ) K) := by
    exact h.mono_set (Ioo_subset_Ioc_self)
  exact h'.integrable_indicator measurableSet_Ioo

lemma gsLocalize_convolution_apply
    {f g : ℝ → ℝ} {K x : ℝ} (hx0 : 0 ≤ x) (hxK : x < K) :
    ((gsLocalize K f) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        (gsLocalize K g)) x =
      ∫ t : ℝ in 0..x, f t * g (x - t) := by
  by_cases hx : x = 0
  · subst x
    rw [convolution_def, intervalIntegral.integral_same, ← integral_zero]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t ↦ by
      by_cases ht : t ∈ Ioo (0 : ℝ) K
      · have hneg : -t ∉ Ioo (0 : ℝ) K := by
          intro hn
          linarith [ht.1, hn.1]
        simp [gsLocalize, ht, hneg]
      · simp [gsLocalize, ht]
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  rw [convolution_def, intervalIntegral.integral_of_le hx0,
    integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    by_cases ht : t ∈ Ioo (0 : ℝ) x
    · have htK : t ∈ Ioo (0 : ℝ) K := ⟨ht.1, ht.2.trans hxK⟩
      have hsubK : x - t ∈ Ioo (0 : ℝ) K := by
        constructor
        · linarith [ht.2]
        · linarith [ht.1, hxK]
      simp [gsLocalize, ht, htK, hsubK]
    · have hzero : t ∉ Ioo (0 : ℝ) K ∨ x - t ∉ Ioo (0 : ℝ) K := by
        by_contra hnot
        push_neg at hnot
        exact ht ⟨hnot.1.1, by linarith [hnot.2.1]⟩
      rcases hzero with hleft | hright
      · simp [gsLocalize, ht, hleft]
      · simp [gsLocalize, ht, hright]

/-- Commutativity of the additive Volterra convolution on an interval. -/
lemma gs_interval_convolution_comm (f g : ℝ → ℝ) (x : ℝ) :
    (∫ t : ℝ in 0..x, f t * g (x - t)) =
      ∫ t : ℝ in 0..x, g t * f (x - t) := by
  simpa [mul_comm] using
    (intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := x) (fun t : ℝ ↦ g t * f (x - t)) x)

/-- Multiplication by the output coordinate is a derivation for Volterra
convolution.  The two displayed hypotheses are exactly the integrability
needed to split the integral. -/
lemma gs_interval_convolution_coordinate
    (f g : ℝ → ℝ) {x : ℝ}
    (hleft : IntervalIntegrable
      (fun t : ℝ ↦ (t * f t) * g (x - t)) volume 0 x)
    (hright : IntervalIntegrable
      (fun t : ℝ ↦ f t * ((x - t) * g (x - t))) volume 0 x) :
    x * (∫ t : ℝ in 0..x, f t * g (x - t)) =
      (∫ t : ℝ in 0..x, (t * f t) * g (x - t)) +
        ∫ t : ℝ in 0..x, f t * ((x - t) * g (x - t)) := by
  rw [← intervalIntegral.integral_const_mul]
  rw [show (fun t : ℝ ↦ x * (f t * g (x - t))) =
      (fun t ↦ (t * f t) * g (x - t) +
        f t * ((x - t) * g (x - t))) by
    funext t
    ring]
  exact intervalIntegral.integral_add hleft hright

/-- A convolution of functions supported in the positive half-line is
again supported there. -/
lemma gs_convolution_eq_zero_of_nonpos
    {f g : ℝ → ℝ}
    (hf : ∀ t : ℝ, t ≤ 0 → f t = 0)
    (hg : ∀ t : ℝ, t ≤ 0 → g t = 0)
    {x : ℝ} (hx : x ≤ 0) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x = 0 := by
  rw [convolution_def, ← integral_zero]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    by_cases ht : t ≤ 0
    · simp [hf t ht]
    · have hsub : x - t ≤ 0 := by linarith
      simp [hg (x - t) hsub]

/-- For positive-half-line-supported functions, ordinary convolution at a
nonnegative point is precisely Volterra convolution on `[0,x]`. -/
lemma gs_convolution_apply_of_nonpos_eq_zero
    {f g : ℝ → ℝ}
    (hf : ∀ t : ℝ, t ≤ 0 → f t = 0)
    (hg : ∀ t : ℝ, t ≤ 0 → g t = 0)
    {x : ℝ} (hx : 0 ≤ x) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x =
      ∫ t : ℝ in 0..x, f t * g (x - t) := by
  by_cases hxzero : x = 0
  · subst x
    rw [gs_convolution_eq_zero_of_nonpos hf hg le_rfl,
      intervalIntegral.integral_same]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  rw [convolution_def, intervalIntegral.integral_of_le hx,
    integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    by_cases ht : t ∈ Ioo (0 : ℝ) x
    · simp [ht]
    · by_cases ht0 : t ≤ 0
      · simp [ht, hf t ht0]
      · have htx : x ≤ t := by
          by_contra hnot
          exact ht ⟨lt_of_not_ge ht0, lt_of_not_ge hnot⟩
        have hsub : x - t ≤ 0 := sub_nonpos.mpr htx
        simp [ht, hg (x - t) hsub]

/-- Extensionality of positive-half-line convolution from equality on the
only interval visible at the evaluation point. -/
lemma gs_convolution_congr_Icc
    {f g h : ℝ → ℝ}
    (hf : ∀ t : ℝ, t ≤ 0 → f t = 0)
    (hg : ∀ t : ℝ, t ≤ 0 → g t = 0)
    (hh : ∀ t : ℝ, t ≤ 0 → h t = 0)
    {x : ℝ} (hx : 0 ≤ x)
    (heq : ∀ y ∈ Icc (0 : ℝ) x, g y = h y) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ] h) x := by
  rw [gs_convolution_apply_of_nonpos_eq_zero hf hg hx,
    gs_convolution_apply_of_nonpos_eq_zero hf hh hx]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hx] at ht
  dsimp only
  rw [heq (x - t) ⟨sub_nonneg.mpr ht.2, sub_le_self _ ht.1⟩]

/-- An integrable first factor and an integrable bounded second factor
give a convolution integral at every point. -/
lemma gs_convolutionExistsAt_of_integrable_bounded
    {f g : ℝ → ℝ} {C x : ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hgbound : ∀ y : ℝ, ‖g y‖ ≤ C) :
    ConvolutionExistsAt f g x (ContinuousLinearMap.mul ℝ ℝ) := by
  have hgtrans : AEStronglyMeasurable (fun t : ℝ ↦ g (x - t)) :=
    hg.aestronglyMeasurable.comp_quasiMeasurePreserving
      (volume.measurePreserving_sub_left x).quasiMeasurePreserving
  have hi := hf.mul_bdd hgtrans
    (Filter.Eventually.of_forall fun t ↦ hgbound (x - t))
  simpa [ConvolutionExistsAt, ContinuousLinearMap.mul_apply'] using hi

/-- The elementary `L¹ * L∞` pointwise estimate used to keep all
localized iterated convolutions bounded. -/
lemma gs_norm_convolution_le_integral_norm_mul
    {f g : ℝ → ℝ} {C x : ℝ} (hf : Integrable f)
    (hC : 0 ≤ C) (hgbound : ∀ y : ℝ, ‖g y‖ ≤ C) :
    ‖(f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x‖ ≤
      (∫ t : ℝ, ‖f t‖) * C := by
  rw [convolution_def]
  have hdom : Integrable (fun t : ℝ ↦ ‖f t‖ * C) := hf.norm.mul_const C
  calc
    ‖∫ t : ℝ, (ContinuousLinearMap.mul ℝ ℝ (f t)) (g (x - t))‖ ≤
        ∫ t : ℝ, ‖f t‖ * C := by
      apply norm_integral_le_of_norm_le hdom
      exact Filter.Eventually.of_forall fun t ↦ by
        rw [ContinuousLinearMap.mul_apply', norm_mul]
        exact mul_le_mul_of_nonneg_left (hgbound (x - t)) (norm_nonneg _)
    _ = (∫ t : ℝ, ‖f t‖) * C :=
      integral_mul_const C (fun t : ℝ ↦ ‖f t‖)

end

end Erdos783
