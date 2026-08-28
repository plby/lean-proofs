import Wikipedia.NoExoticSixSphere.CanonicalRightInverse
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Exact normal-frame compatibility on constant cylinder collars

For a differential that ignores time, its canonical orthogonal right
inverse is the endpoint right inverse with zero time component. The
ambient product uses its L2 inner product. An eventual-equality version
applies directly on constant open collars.
-/

open scoped InnerProductSpace Topology
open Function

namespace NoExoticSixSphere.CylinderNormalFrame

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable def forgetTime (D : E →L[ℝ] F) : WithLp 2 (ℝ × E) →L[ℝ] F :=
  D.comp ((ContinuousLinearMap.snd ℝ ℝ E).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).toContinuousLinearMap)

noncomputable def liftFrame (R : F →L[ℝ] E) : F →L[ℝ] WithLp 2 (ℝ × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.inr ℝ ℝ E).comp R)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem liftFrame_apply (R : F →L[ℝ] E) (v : F) :
    liftFrame R v = WithLp.toLp 2 (0, R v) := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem forgetTime_surjective (D : E →L[ℝ] F) (hD : Surjective D) :
    Surjective (forgetTime D) := by
  intro v
  obtain ⟨w, hw⟩ := hD v
  exact ⟨WithLp.toLp 2 (0, w), hw⟩

theorem orthogonalRightInverse_forgetTime (D : E →L[ℝ] F) (hD : Surjective D) :
    orthogonalRightInverse (forgetTime D) = liftFrame (orthogonalRightInverse D) := by
  apply orthogonalRightInverse_eq_of_rightInverse _ (forgetTime_surjective D hD)
  · intro v
    exact apply_orthogonalRightInverse D hD v
  · rintro _ ⟨v, rfl⟩
    apply (Submodule.mem_orthogonal _ _).mpr
    intro w hw
    have hv : orthogonalRightInverse D v ∈ D.kerᗮ := by
      rw [← range_orthogonalRightInverse D hD]
      exact ⟨v, rfl⟩
    have hw' : w.snd ∈ D.ker := hw
    change ⟪w, WithLp.toLp 2 (0, orthogonalRightInverse D v)⟫_ℝ = 0
    simp only [WithLp.prod_inner_apply, inner_zero_right, zero_add]
    exact D.ker.inner_right_of_mem_orthogonal hw' hv

theorem orthogonalRightInverse_fderiv_of_eventuallyEq
    {f : E → F} {g : WithLp 2 (ℝ × E) → F} {p : WithLp 2 (ℝ × E)}
    (hf : DifferentiableAt ℝ f p.snd)
    (hreg : Surjective (fderiv ℝ f p.snd))
    (heq : g =ᶠ[𝓝 p] (fun q : WithLp 2 (ℝ × E) ↦ f q.snd)) :
    orthogonalRightInverse (fderiv ℝ g p) =
      liftFrame (orthogonalRightInverse (fderiv ℝ f p.snd)) := by
  let P : WithLp 2 (ℝ × E) →L[ℝ] E :=
    (ContinuousLinearMap.snd ℝ ℝ E).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).toContinuousLinearMap
  have hd : HasFDerivAt (fun q : WithLp 2 (ℝ × E) ↦ f q.snd)
      (forgetTime (fderiv ℝ f p.snd)) p := hf.hasFDerivAt.comp p P.hasFDerivAt
  rw [heq.fderiv_eq, hd.fderiv]
  exact orthogonalRightInverse_forgetTime _ hreg

end NoExoticSixSphere.CylinderNormalFrame
