import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSphereSourceIsometries
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPreimageSourceCharts
import Wikipedia.SmoothSixDPoincare.SphereChartOrientation

/-!
# Coherent outward frames at the twelve seven-sphere preimages

The frame is formed from the actual outward point and the actual ambient
derivative of the smooth source chart. Its transport through the two
cylinder directions preserves orientation at every phase/sign center.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates

local notation "Ambient" => EuclideanSpace ℂ (Fin 3)
local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 8)

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def sourceRadialEquiv (z : UnitSphere) : (ℝ × ParameterSpace z) ≃L[ℝ] SphereAmbient :=
  (LinearEquiv.ofBijective (chartRadialFrame (sphereSourceChart z) 0).toLinearMap
    (bijective_chartRadialFrame (sphereSourceChart z)
      (sphereSourceChart_source z ▸ mem_univ 0))).toContinuousLinearEquiv

theorem sourceRadialEquiv_apply (z : UnitSphere) (p : ℝ × ParameterSpace z) :
    sourceRadialEquiv z p = p.1 • (sphereSourceChart z 0).val +
      fderiv ℝ (fun v : ParameterSpace z ↦ (sphereSourceChart z v).val) 0 p.2 := rfl

theorem transportedSphereSourceChart_radialFrame (e : Ambient ≃ₗᵢ[ℝ] Ambient)
    (z : UnitSphere) :
    chartRadialFrame (transportedSphereSourceChart e z) 0 =
      (sphereSourceIsometry e).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (sourceRadialEquiv z).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro p
  change p.1 • (transportedSphereSourceChart e z 0).val +
    fderiv ℝ (fun v : ParameterSpace z ↦ (transportedSphereSourceChart e z v).val) 0 p.2 =
      sphereSourceIsometry e (sourceRadialEquiv z p)
  rw [(hasFDerivAt_transportedSphereSourceChart e z).fderiv, sourceRadialEquiv_apply]
  change p.1 • sphereSourceIsometry e (sphereSourceChart z 0).val +
    sphereSourceIsometry e (fderiv ℝ (fun v : ParameterSpace z ↦
      (sphereSourceChart z v).val) 0 p.2) = _
  rw [map_add, map_smul]

theorem transportedSphereSourceChart_relativeDet (e : Ambient ≃ₗᵢ[ℝ] Ambient)
    (z : UnitSphere) :
    ((chartRadialFrame (transportedSphereSourceChart e z) 0).comp
      (sourceRadialEquiv z).symm.toContinuousLinearMap).det = e.toLinearEquiv.toLinearMap.det := by
  have h : (chartRadialFrame (transportedSphereSourceChart e z) 0).comp
      (sourceRadialEquiv z).symm.toContinuousLinearMap =
        (sphereSourceIsometry e).toContinuousLinearEquiv.toContinuousLinearMap := by
    rw [transportedSphereSourceChart_radialFrame]
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (sphereSourceIsometry e) ((sourceRadialEquiv z).apply_symm_apply v)
  rw [h]
  exact sphereSourceIsometry_det e

def sphereSourceOutwardFrame (z : UnitSphere)
    (b : Module.Basis (Fin 7) ℝ (ParameterSpace z)) :
    Module.Basis (Unit ⊕ Fin 7) ℝ SphereAmbient :=
  ((Module.Basis.singleton Unit ℝ).prod b).map (sourceRadialEquiv z).toLinearEquiv

theorem sphereSourceOutwardFrame_normal (z : UnitSphere)
    (b : Module.Basis (Fin 7) ℝ (ParameterSpace z)) :
    sphereSourceOutwardFrame z b (Sum.inl ()) = (midpointSphereEmbedding z).val := by
  simp [sphereSourceOutwardFrame, sourceRadialEquiv_apply, sphereSourceChart_zero]

theorem sphereSourceOutwardFrame_tangent (z : UnitSphere)
    (b : Module.Basis (Fin 7) ℝ (ParameterSpace z)) (i : Fin 7) :
    sphereSourceOutwardFrame z b (Sum.inr i) =
      fderiv ℝ (fun v : ParameterSpace z ↦ (sphereSourceChart z v).val) 0 (b i) := by
  simp [sphereSourceOutwardFrame, sourceRadialEquiv_apply]

def transportedSphereOutwardFrame (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere)
    (b : Module.Basis (Fin 7) ℝ (ParameterSpace z)) :
    Module.Basis (Unit ⊕ Fin 7) ℝ SphereAmbient :=
  (sphereSourceOutwardFrame z b).map (sphereSourceIsometry e).toLinearEquiv

theorem transportedSphereOutwardFrame_normal (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere)
    (b : Module.Basis (Fin 7) ℝ (ParameterSpace z)) :
    transportedSphereOutwardFrame e z b (Sum.inl ()) =
      (transportedSphereSourceChart e z 0).val := by
  change sphereSourceIsometry e (sphereSourceOutwardFrame z b (Sum.inl ())) = _
  rw [sphereSourceOutwardFrame_normal]
  change sphereSourceIsometry e (midpointSphereEmbedding z).val =
    sphereSourceIsometry e (sphereSourceChart z 0).val
  rw [sphereSourceChart_zero]

theorem transportedSphereOutwardFrame_tangent (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere)
    (b : Module.Basis (Fin 7) ℝ (ParameterSpace z)) (i : Fin 7) :
    transportedSphereOutwardFrame e z b (Sum.inr i) =
      fderiv ℝ (fun v : ParameterSpace z ↦ (transportedSphereSourceChart e z v).val) 0 (b i) := by
  rw [(hasFDerivAt_transportedSphereSourceChart e z).fderiv]
  change sphereSourceIsometry e (sphereSourceOutwardFrame z b (Sum.inr i)) = _
  rw [sphereSourceOutwardFrame_tangent]
  rfl

theorem transportedSphereOutwardFrame_orientation (e : Ambient ≃ₗᵢ[ℝ] Ambient)
    (he : 0 < e.toLinearEquiv.toLinearMap.det) (z : UnitSphere)
    (b : Module.Basis (Fin 7) ℝ (ParameterSpace z)) :
    (transportedSphereOutwardFrame e z b).orientation =
      (sphereSourceOutwardFrame z b).orientation :=
  ((sphereSourceOutwardFrame z b).orientation_comp_linearEquiv_eq_iff_det_pos
    (sphereSourceIsometry e).toLinearEquiv).mpr ((sphereSourceIsometry_det e).symm ▸ he)

namespace MidpointSeed

def spherePreimageSourceChart (u : unitary ℂ) (b : Bool × Bool) :
    PartialDiffeomorph 𝓘(ℝ, ParameterSpace rotatedInput) (𝓡 7)
      (ParameterSpace rotatedInput) (Sphere 7) ∞ :=
  transportedSphereSourceChart (preimageSourceIsometry u b) rotatedInput

theorem spherePreimageSourceChart_zero (u : unitary ℂ) (b : Bool × Bool) :
    spherePreimageSourceChart u b 0 = midpointSphereEmbedding (phaseInput u b) := by
  rw [spherePreimageSourceChart, transportedSphereSourceChart_zero, preimageSourceIsometry_center]

def spherePreimageOutwardFrame (u : unitary ℂ) (b : Bool × Bool)
    (v : Module.Basis (Fin 7) ℝ (ParameterSpace rotatedInput)) :
    Module.Basis (Unit ⊕ Fin 7) ℝ SphereAmbient :=
  transportedSphereOutwardFrame (preimageSourceIsometry u b) rotatedInput v

theorem spherePreimageOutwardFrame_normal (u : unitary ℂ) (b : Bool × Bool)
    (v : Module.Basis (Fin 7) ℝ (ParameterSpace rotatedInput)) :
    spherePreimageOutwardFrame u b v (Sum.inl ()) =
      (midpointSphereEmbedding (phaseInput u b)).val := by
  change transportedSphereOutwardFrame (preimageSourceIsometry u b) rotatedInput v
    (Sum.inl ()) = _
  rw [transportedSphereOutwardFrame_normal]
  exact congrArg Subtype.val (spherePreimageSourceChart_zero u b)

theorem spherePreimageOutwardFrame_tangent (u : unitary ℂ) (b : Bool × Bool)
    (v : Module.Basis (Fin 7) ℝ (ParameterSpace rotatedInput)) (i : Fin 7) :
    spherePreimageOutwardFrame u b v (Sum.inr i) =
      fderiv ℝ (fun w : ParameterSpace rotatedInput ↦ (spherePreimageSourceChart u b w).val)
        0 (v i) :=
  transportedSphereOutwardFrame_tangent (preimageSourceIsometry u b) rotatedInput v i

theorem spherePreimageOutwardFrame_orientation (u : unitary ℂ) (b : Bool × Bool)
    (v : Module.Basis (Fin 7) ℝ (ParameterSpace rotatedInput)) :
    (spherePreimageOutwardFrame u b v).orientation =
      (sphereSourceOutwardFrame rotatedInput v).orientation :=
  transportedSphereOutwardFrame_orientation (preimageSourceIsometry u b)
    (preimageSourceIsometry_det_pos u b) rotatedInput v

theorem spherePreimageSourceChart_relativeDet_pos (u : unitary ℂ) (b : Bool × Bool) :
    0 < ((chartRadialFrame (spherePreimageSourceChart u b) 0).comp
      (sourceRadialEquiv rotatedInput).symm.toContinuousLinearMap).det := by
  rw [spherePreimageSourceChart, transportedSphereSourceChart_relativeDet]
  exact preimageSourceIsometry_det_pos u b

end MidpointSeed

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
