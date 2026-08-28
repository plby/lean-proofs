import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Continuous linear rescaling of the last coordinate in an L2 product -/

noncomputable section

namespace NoExoticSixSphere

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def lastCoordinateScale (c : ℝ) (hc : c ≠ 0) :
    WithLp 2 (E × ℝ) ≃L[ℝ] WithLp 2 (E × ℝ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).trans
    (((ContinuousLinearEquiv.refl ℝ E).prodCongr
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc))).trans
        (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm)

theorem lastCoordinateScale_apply (c : ℝ) (hc : c ≠ 0) (v : WithLp 2 (E × ℝ)) :
    lastCoordinateScale c hc v = WithLp.toLp 2 (v.fst, v.snd * c) := rfl

theorem lastCoordinateScale_symm_apply (c : ℝ) (hc : c ≠ 0)
    (v : WithLp 2 (E × ℝ)) :
    (lastCoordinateScale c hc).symm v = WithLp.toLp 2 (v.fst, v.snd * c⁻¹) := rfl

theorem lastCoordinateScale_one (h : (1 : ℝ) ≠ 0) :
    lastCoordinateScale (E := E) 1 h = ContinuousLinearEquiv.refl ℝ _ := by
  apply ContinuousLinearEquiv.ext
  funext v
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).injective
  exact Prod.ext rfl (mul_one v.snd)

variable {B : Type*} [TopologicalSpace B] {c : B → ℝ}

theorem continuous_lastCoordinateScale_apply (hc : Continuous c) (hn : ∀ b, c b ≠ 0) :
    Continuous (fun p : B × WithLp 2 (E × ℝ) ↦ lastCoordinateScale (c p.1) (hn p.1) p.2) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ
  have hv : Continuous (fun p : B × WithLp 2 (E × ℝ) ↦ e p.2) :=
    e.continuous.comp continuous_snd
  exact e.symm.continuous.comp (hv.fst.prodMk (hv.snd.mul (hc.comp continuous_fst)))

theorem continuous_lastCoordinateScale_symm_apply (hc : Continuous c) (hn : ∀ b, c b ≠ 0) :
    Continuous (fun p : B × WithLp 2 (E × ℝ) ↦
      (lastCoordinateScale (c p.1) (hn p.1)).symm p.2) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ
  have hv : Continuous (fun p : B × WithLp 2 (E × ℝ) ↦ e p.2) :=
    e.continuous.comp continuous_snd
  exact e.symm.continuous.comp
    (hv.fst.prodMk (hv.snd.mul ((hc.inv₀ hn).comp continuous_fst)))

end NoExoticSixSphere
