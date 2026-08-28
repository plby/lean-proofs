import Wikipedia.NoExoticSixSphere.FamilyFlatteningGerm
import Wikipedia.NoExoticSixSphere.CorankOneCoordinateCover

/-!
# Rank-adapted linear coordinates for the actual smooth family

The coordinate action on the map differentiates to the coordinate action
on its spatial operator. The source reordering is a continuous linear
equivalence, so a regular Schur residual stays regular in these coordinates.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.FamilyLinearCoordinates

open CorankOne CorankOneCoordinates

variable {T V W E F : Type}
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def family (c : Coordinates V W E F) (f : T → V → W) (t : T) (v : E × ℝ) : E × F :=
  c.2 (f t (c.1.symm v))

def sourceEquiv (c : Coordinates V W E F) : (E × (T × ℝ)) ≃L[ℝ] T × V :=
  FamilyFlattening.sourceOrder.trans ((ContinuousLinearEquiv.refl ℝ T).prodCongr c.1.symm)

theorem sourceEquiv_apply (c : Coordinates V W E F) (q : E × (T × ℝ)) :
    sourceEquiv c q = (q.2.1, c.1.symm (q.1, q.2.2)) := rfl

theorem contDiff_family (c : Coordinates V W E F) (f : T → V → W)
    (hf : ContDiff ℝ ∞ (uncurry f)) : ContDiff ℝ ∞ (uncurry (family c f)) :=
  c.2.contDiff.comp
    (hf.comp ((ContinuousLinearEquiv.refl ℝ T).prodCongr c.1.symm).contDiff)

theorem spatial_family (c : Coordinates V W E F) (f : T → V → W)
    (hf : ContDiff ℝ ∞ (uncurry f)) (q : E × (T × ℝ)) :
    FamilyFlattening.spatial (family c f) q =
      operatorEquiv c (fderiv ℝ (f q.2.1) (c.1.symm (q.1, q.2.2))) := by
  have ht : ContDiff ℝ ∞ (f q.2.1) := hf.comp (contDiff_const.prodMk contDiff_id)
  have hinner := (ht.differentiable (by simp) (c.1.symm (q.1, q.2.2))).hasFDerivAt.comp
    (q.1, q.2.2) c.1.symm.hasFDerivAt
  have hder : HasFDerivAt (family c f q.2.1)
      (c.2.toContinuousLinearMap.comp
        ((fderiv ℝ (f q.2.1) (c.1.symm (q.1, q.2.2))).comp c.1.symm.toContinuousLinearMap))
      (q.1, q.2.2) := c.2.hasFDerivAt.comp (q.1, q.2.2) hinner
  change fderiv ℝ (family c f q.2.1) (q.1, q.2.2) = _
  rw [hder.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  rfl

def residual (c : Coordinates V W E F) (f : T → V → W) (p : T × V) : F :=
  CorankOne.residual (operatorEquiv c (fderiv ℝ (f p.1) p.2))

theorem residual_family (c : Coordinates V W E F) (f : T → V → W)
    (hf : ContDiff ℝ ∞ (uncurry f)) :
    (fun q ↦ CorankOne.residual (FamilyFlattening.spatial (family c f) q)) =
      residual c f ∘ sourceEquiv c := by
  funext q
  rw [spatial_family c f hf]
  rfl

theorem bijective_fderiv_residual [FiniteDimensional ℝ E]
    (c : Coordinates V W E F) (f : T → V → W) (hf : ContDiff ℝ ∞ (uncurry f))
    (q : E × (T × ℝ))
    (hq : fderiv ℝ (f (sourceEquiv c q).1) (sourceEquiv c q).2 ∈ domain c)
    (hb : Bijective (fderiv ℝ (residual c f) (sourceEquiv c q))) :
    Bijective (fderiv ℝ
      (fun p ↦ CorankOne.residual (FamilyFlattening.spatial (family c f) p)) q) := by
  rw [residual_family c f hf]
  have hD := (operatorEquiv c).contDiff.comp (DiskHomotopy.contDiff_spatial_fderiv f hf)
  have hR₀ := (contDiffAt_residual _ (leading_invertible hq)).comp
    (sourceEquiv c q) hD.contDiffAt
  have hR : DifferentiableAt ℝ (residual c f) (sourceEquiv c q) :=
    hR₀.differentiableAt (by simp)
  rw [(hR.hasFDerivAt.comp q (sourceEquiv (T := T) c).hasFDerivAt).fderiv]
  exact hb.comp (sourceEquiv (T := T) c).bijective

end NoExoticSixSphere.FamilyLinearCoordinates
