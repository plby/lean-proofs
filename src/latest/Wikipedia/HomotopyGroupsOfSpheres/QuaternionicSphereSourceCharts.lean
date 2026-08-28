import Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredDiffeomorph
import Wikipedia.HomotopyGroupsOfSpheres.SphereCylinderLatitude
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSpherePreimages
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicProjectedCoordinates
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphProduct

/-!
# Smooth source charts on the literal candidate seven-sphere

Two normalized cylinder charts extend the centered five-sphere chart.
Their exact latitude formulas identify the actual projected sphere map
with the previously differentiated angular formula.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.CylinderLatitude

open NoExoticSixSphere
open Wikipedia.SmoothSixDPoincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

def extendChart (c : PartialDiffeomorph 𝓘(ℝ, E) (𝓡 n) E (Sphere n) ∞) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × E) (𝓡 (n + 1)) (ℝ × E) (Sphere (n + 1)) ∞ :=
  (((PartialChart.vectorProduct ℝ E).toPartialDiffeomorph).trans
    (PartialChart.prod (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph c)).trans
      (SphereCylinder.chart n)

@[simp] theorem extendChart_apply
    (c : PartialDiffeomorph 𝓘(ℝ, E) (𝓡 n) E (Sphere n) ∞) (p : ℝ × E) :
    extendChart c p = SphereCylinder.point n (p.1, c p.2) := rfl

theorem extendChart_source
    (c : PartialDiffeomorph 𝓘(ℝ, E) (𝓡 n) E (Sphere n) ∞) (hc : c.source = univ) :
    (extendChart c).source = univ := by
  apply Set.eq_univ_of_forall
  intro p
  exact ⟨⟨mem_univ _, ⟨mem_univ _, hc ▸ mem_univ _⟩⟩, mem_univ _⟩

end Wikipedia.HomotopyGroupsOfSpheres.CylinderLatitude

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open NoExoticSixSphere
open SphereCenteredCoordinates

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 3)) = 5 + 1) :=
  ⟨complexAmbient_finrank⟩

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 6)) = 5 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def sphereFiveSourceChart (z : UnitSphere) :
    PartialDiffeomorph 𝓘(ℝ, Tangent z) (𝓡 5) (Tangent z) (Sphere 5) ∞ :=
  (inverseDiffeomorph 5 z).trans
    (sphereIsometryDiffeomorph 5 complexRealCoordinates).toPartialDiffeomorph

@[simp] theorem sphereFiveSourceChart_apply (z : UnitSphere) (v : Tangent z) :
    sphereFiveSourceChart z v = sphereFiveHomeomorph.symm (inverse z v) := rfl

theorem sphereFiveSourceChart_source (z : UnitSphere) :
    (sphereFiveSourceChart z).source = univ := by
  apply Set.eq_univ_of_forall
  intro v
  exact ⟨mem_univ _, mem_univ _⟩

def sphereSourceChart (z : UnitSphere) :
    PartialDiffeomorph 𝓘(ℝ, ParameterSpace z) (𝓡 7) (ParameterSpace z) (Sphere 7) ∞ :=
  CylinderLatitude.extendChart (CylinderLatitude.extendChart (sphereFiveSourceChart z))

theorem sphereSourceChart_source (z : UnitSphere) : (sphereSourceChart z).source = univ :=
  CylinderLatitude.extendChart_source _
    (CylinderLatitude.extendChart_source _ (sphereFiveSourceChart_source z))

theorem sphereSourceChart_apply (z : UnitSphere) (p : ParameterSpace z) :
    sphereSourceChart z p = SphereCylinder.point 6
      (p.1, SphereCylinder.point 5 (p.2.1, sphereFiveHomeomorph.symm (localSphere z p))) := rfl

theorem sphereSourceChart_eq_sourcePoint (z : UnitSphere) (p : ParameterSpace z) :
    sphereSourceChart z p = sphereSourcePoint (CylinderLatitude.time p.1)
      (CylinderLatitude.time p.2.1) (localSphere z p) := by
  rw [sphereSourceChart_apply]
  rw [CylinderLatitude.point_eq_latitude, CylinderLatitude.point_eq_latitude]
  rfl

@[simp] theorem sphereSourceChart_zero (z : UnitSphere) :
    sphereSourceChart z 0 = midpointSphereEmbedding z := by
  rw [sphereSourceChart_eq_sourcePoint, localSphere_zero]
  have ht : CylinderLatitude.time 0 = parameterMidpoint := by
    apply Subtype.ext
    exact CylinderLatitude.time_zero
  change sphereSourcePoint (CylinderLatitude.time 0) (CylinderLatitude.time 0) z = _
  rw [ht]
  rfl

theorem contMDiff_sphereSourceChart (z : UnitSphere) :
    ContMDiff 𝓘(ℝ, ParameterSpace z) (𝓡 7) ∞ (sphereSourceChart z) := by
  rw [← contMDiffOn_univ, ← sphereSourceChart_source z]
  exact (sphereSourceChart z).contMDiffOn

theorem sphereSourceChart_isLocalDiffeomorphAt (z : UnitSphere) (p : ParameterSpace z) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ParameterSpace z) (𝓡 7) ∞ (sphereSourceChart z) p :=
  ⟨sphereSourceChart z, sphereSourceChart_source z ▸ mem_univ p, Set.eqOn_refl _ _⟩

def cylinderAngularParameters (z : UnitSphere) (p : ParameterSpace z) : ParameterSpace z :=
  (CylinderLatitude.angleOffset p.1, CylinderLatitude.angleOffset p.2.1, p.2.2)

@[simp] theorem cylinderAngularParameters_zero (z : UnitSphere) :
    cylinderAngularParameters z 0 = 0 := by
  simp [cylinderAngularParameters]

theorem contDiff_cylinderAngularParameters (z : UnitSphere) {n : ℕ∞ω} :
    ContDiff ℝ n (cylinderAngularParameters z) :=
  (CylinderLatitude.contDiff_angleOffset.comp contDiff_fst).prodMk
    ((CylinderLatitude.contDiff_angleOffset.comp contDiff_snd.fst).prodMk contDiff_snd.snd)

theorem sphereCandidateProjection_sourceChart (z : UnitSphere) (p : ParameterSpace z) :
    (sphereCandidateProjection (sphereSourceChart z p)).val =
      localProjection z (cylinderAngularParameters z p) := by
  rw [sphereSourceChart_eq_sourcePoint, sphereCandidateProjection_sourcePoint,
    CylinderLatitude.time_angle, CylinderLatitude.time_angle]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
