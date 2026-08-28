import Wikipedia.SmoothSixDPoincare.WhitneyPairModel
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Embedded sheets and transversality in the Whitney pair model

Both sheets are actual smooth closed embeddings of three-space in six-space.
Their native Euclidean derivatives are injective. At the two intersections,
the sum of their tangent maps is surjective; the crossing slopes have opposite
signs. These facts concern the explicit model, not an assumed native Whitney chart.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

theorem finrank_space : Module.finrank ℝ Space = 6 := by
  simp [Space, Plane, Module.finrank_prod]

theorem finrank_sheet : Module.finrank ℝ Sheet = 3 := by
  simp [Sheet, Plane, Module.finrank_prod]

theorem contDiff_firstSheet : ContDiff ℝ ∞ firstSheet := by
  unfold firstSheet
  fun_prop

theorem contDiff_secondSheet (h : ℝ) : ContDiff ℝ ∞ (secondSheet h) := by
  unfold secondSheet
  fun_prop

/-- The coordinate projection is a genuine continuous left inverse. -/
theorem isClosedEmbedding_firstSheet : IsClosedEmbedding firstSheet := by
  have hleft : LeftInverse (fun z : Space => (z.1.1, z.2.1)) firstSheet := fun _ => rfl
  exact hleft.isClosedEmbedding (by fun_prop) contDiff_firstSheet.continuous

theorem isClosedEmbedding_secondSheet (h : ℝ) : IsClosedEmbedding (secondSheet h) := by
  have hleft : LeftInverse (fun z : Space => (z.1.1, z.2.2)) (secondSheet h) := fun _ => rfl
  exact hleft.isClosedEmbedding (by fun_prop) (contDiff_secondSheet h).continuous

def firstSheetDerivative : Sheet →L[ℝ] Space :=
  ((ContinuousLinearMap.fst ℝ ℝ Plane).prod 0).prod
    ((ContinuousLinearMap.snd ℝ ℝ Plane).prod 0)

def secondSheetDerivative (h s : ℝ) : Sheet →L[ℝ] Space :=
  ((ContinuousLinearMap.fst ℝ ℝ Plane).prod
    ((-2 * h * s) • ContinuousLinearMap.fst ℝ ℝ Plane)).prod
      ((0 : Sheet →L[ℝ] Plane).prod (ContinuousLinearMap.snd ℝ ℝ Plane))

theorem firstSheetDerivative_apply (p : Sheet) :
    firstSheetDerivative p = ((p.1, 0), (p.2, 0)) := rfl

theorem secondSheetDerivative_apply (h s : ℝ) (p : Sheet) :
    secondSheetDerivative h s p = ((p.1, (-2 * h * s) * p.1), (0, p.2)) := rfl

theorem hasFDerivAt_firstSheet (p : Sheet) :
    HasFDerivAt firstSheet firstSheetDerivative p :=
  firstSheetDerivative.hasFDerivAt

theorem hasFDerivAt_secondSheet (h : ℝ) (p : Sheet) :
    HasFDerivAt (secondSheet h) (secondSheetDerivative h p.1) p := by
  have hs := (ContinuousLinearMap.fst ℝ ℝ Plane).hasFDerivAt (x := p)
  have hu := (ContinuousLinearMap.snd ℝ ℝ Plane).hasFDerivAt (x := p)
  have ht := ((hasFDerivAt_const (1 : ℝ) p).sub (hs.pow 2)).const_mul h
  have hd := (hs.prodMk ht).prodMk ((hasFDerivAt_const (0 : Plane) p).prodMk hu)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [secondSheetDerivative, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    zero_apply, sub_apply, smul_apply, smul_eq_mul]
  congr 2
  norm_num [two_smul]
  ring

theorem injective_fderiv_firstSheet (p : Sheet) :
    Injective (fderiv ℝ firstSheet p) := by
  rw [(hasFDerivAt_firstSheet p).fderiv]
  have hleft : LeftInverse (fun z : Space => (z.1.1, z.2.1)) firstSheetDerivative :=
    fun _ => rfl
  exact hleft.injective

theorem injective_fderiv_secondSheet (h : ℝ) (p : Sheet) :
    Injective (fderiv ℝ (secondSheet h) p) := by
  rw [(hasFDerivAt_secondSheet h p).fderiv]
  have hleft : LeftInverse (fun z : Space => (z.1.1, z.2.2))
      (secondSheetDerivative h p.1) := fun _ => rfl
  exact hleft.injective

/-- At every nonzero crossing slope, the actual tangent maps span the ambient space. -/
theorem surjective_tangentSum {h : ℝ} (hh : h ≠ 0) (p q : Sheet) (hq : q.1 ≠ 0) :
    Surjective (fun v : Sheet × Sheet =>
      fderiv ℝ firstSheet p v.1 + fderiv ℝ (secondSheet h) q v.2) := by
  rw [(hasFDerivAt_firstSheet p).fderiv, (hasFDerivAt_secondSheet h q).fderiv]
  intro z
  have hc : -2 * h * q.1 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hh) hq
  refine ⟨((z.1.1 - z.1.2 / (-2 * h * q.1), z.2.1),
    (z.1.2 / (-2 * h * q.1), z.2.2)), ?_⟩
  simp only [firstSheetDerivative_apply, secondSheetDerivative_apply,
    Prod.mk_add_mk, add_zero, zero_add]
  rw [mul_div_cancel₀ _ hc]
  simp

/-- Both actual intersection points are transverse. -/
theorem transverse_at_intersection {h : ℝ} (hh : 0 < h) (p q : Sheet)
    (heq : firstSheet p = secondSheet h q) :
    Surjective (fun v : Sheet × Sheet =>
      fderiv ℝ firstSheet p v.1 + fderiv ℝ (secondSheet h) q v.2) := by
  apply surjective_tangentSum hh.ne' p q
  rcases ((firstSheet_eq_secondSheet_iff hh p q).mp heq).2.2.2 with hq | hq
  · rw [hq]
    norm_num
  · rw [hq]
    norm_num

theorem opposite_crossing_slopes {h : ℝ} (hh : 0 < h) :
    0 < -2 * h * (-1) ∧ -2 * h * 1 < 0 := by
  constructor <;> nlinarith

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
