import Wikipedia.SmoothSixDPoincare.WhitneyPairModel
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# The unequal two-plus-three Whitney model in five dimensions

The two sheets have separate one- and two-dimensional transverse coordinates.
They are genuine smooth closed embeddings. Their explicit derivatives retain
the full arc and transverse directions used by the native adapted chart.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.RankThreeWhitneyModel

abbrev Lower := EuclideanSpace ℝ (Fin 1)
abbrev Upper := EuclideanSpace ℝ (Fin 2)
abbrev Space := (ℝ × ℝ) × (Lower × Upper)
abbrev LowerSheet := ℝ × Lower
abbrev UpperSheet := ℝ × Upper

def firstSheet (p : LowerSheet) : Space := ((p.1, 0), (p.2, 0))

def secondSheet (h : ℝ) (p : UpperSheet) : Space := ((p.1, h * (1 - p.1 ^ 2)), (0, p.2))

theorem finrank_space : Module.finrank ℝ Space = 5 := by
  simp [Space, Lower, Upper, Module.finrank_prod]

theorem finrank_lowerSheet : Module.finrank ℝ LowerSheet = 2 := by
  simp [LowerSheet, Lower, Module.finrank_prod]

theorem finrank_upperSheet : Module.finrank ℝ UpperSheet = 3 := by
  simp [UpperSheet, Upper, Module.finrank_prod]

theorem contDiff_firstSheet : ContDiff ℝ ∞ firstSheet := by
  unfold firstSheet
  fun_prop

theorem contDiff_secondSheet (h : ℝ) : ContDiff ℝ ∞ (secondSheet h) := by
  unfold secondSheet
  fun_prop

theorem isClosedEmbedding_firstSheet : IsClosedEmbedding firstSheet := by
  have hleft : LeftInverse (fun z : Space => (z.1.1, z.2.1)) firstSheet := fun _ => rfl
  exact hleft.isClosedEmbedding (by fun_prop) contDiff_firstSheet.continuous

theorem isClosedEmbedding_secondSheet (h : ℝ) : IsClosedEmbedding (secondSheet h) := by
  have hleft : LeftInverse (fun z : Space => (z.1.1, z.2.2)) (secondSheet h) := fun _ => rfl
  exact hleft.isClosedEmbedding (by fun_prop) (contDiff_secondSheet h).continuous

def firstSheetDerivative : LowerSheet →L[ℝ] Space :=
  ((ContinuousLinearMap.fst ℝ ℝ Lower).prod 0).prod
    ((ContinuousLinearMap.snd ℝ ℝ Lower).prod 0)

def secondSheetDerivative (h s : ℝ) : UpperSheet →L[ℝ] Space :=
  ((ContinuousLinearMap.fst ℝ ℝ Upper).prod
    ((-2 * h * s) • ContinuousLinearMap.fst ℝ ℝ Upper)).prod
      ((0 : UpperSheet →L[ℝ] Lower).prod (ContinuousLinearMap.snd ℝ ℝ Upper))

theorem firstSheetDerivative_apply (p : LowerSheet) :
    firstSheetDerivative p = ((p.1, 0), (p.2, 0)) := rfl

theorem secondSheetDerivative_apply (h s : ℝ) (p : UpperSheet) :
    secondSheetDerivative h s p = ((p.1, (-2 * h * s) * p.1), (0, p.2)) := rfl

theorem hasFDerivAt_firstSheet (p : LowerSheet) :
    HasFDerivAt firstSheet firstSheetDerivative p :=
  firstSheetDerivative.hasFDerivAt

theorem hasFDerivAt_secondSheet (h : ℝ) (p : UpperSheet) :
    HasFDerivAt (secondSheet h) (secondSheetDerivative h p.1) p := by
  have hs := (ContinuousLinearMap.fst ℝ ℝ Upper).hasFDerivAt (x := p)
  have hu := (ContinuousLinearMap.snd ℝ ℝ Upper).hasFDerivAt (x := p)
  have ht := ((hasFDerivAt_const (1 : ℝ) p).sub (hs.pow 2)).const_mul h
  have hd := (hs.prodMk ht).prodMk ((hasFDerivAt_const (0 : Lower) p).prodMk hu)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [secondSheetDerivative, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    zero_apply, sub_apply, smul_apply, smul_eq_mul]
  congr 2
  norm_num [two_smul]
  ring

theorem injective_fderiv_firstSheet (p : LowerSheet) :
    Injective (fderiv ℝ firstSheet p) := by
  rw [(hasFDerivAt_firstSheet p).fderiv]
  have hleft : LeftInverse (fun z : Space => (z.1.1, z.2.1)) firstSheetDerivative :=
    fun _ => rfl
  exact hleft.injective

theorem injective_fderiv_secondSheet (h : ℝ) (p : UpperSheet) :
    Injective (fderiv ℝ (secondSheet h) p) := by
  rw [(hasFDerivAt_secondSheet h p).fderiv]
  have hleft : LeftInverse (fun z : Space => (z.1.1, z.2.2))
      (secondSheetDerivative h p.1) := fun _ => rfl
  exact hleft.injective

theorem surjective_tangentSum {h : ℝ} (hh : h ≠ 0) (p : LowerSheet) (q : UpperSheet)
    (hq : q.1 ≠ 0) :
    Surjective (fun v : LowerSheet × UpperSheet =>
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

end Wikipedia.SmoothSixDPoincare.RankThreeWhitneyModel
