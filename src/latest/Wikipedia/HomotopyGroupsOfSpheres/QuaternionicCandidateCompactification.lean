import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSphereNativeRegularity
import Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCompactification

/-!
# The original candidate in the compactified normalized target chart

The compactified map is continuous on the entire source sphere. On the
preimage of the original target chart it is exactly the finite inclusion
of the checked normalized-coordinate function. Its finite-zero fiber is
the original twelve-point fiber.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicColumns QuaternionicBottMatrix

local notation "QSphere" => SphereCenteredCoordinates.UnitSphere (QuaternionSpace 1)

theorem continuous_sphereCandidateQuaternionMap : Continuous sphereCandidateQuaternionMap := by
  apply Continuous.subtype_mk
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ Quaternion ℝ)).comp
    (continuous_subtype_val.comp sphereCandidateProjection.continuous)

def quaternionCandidateMap : C(Sphere 7, QSphere) :=
  ⟨sphereCandidateQuaternionMap, continuous_sphereCandidateQuaternionMap⟩

theorem sphereCandidateQuaternionMap_target_iff (x : Sphere 7) :
    sphereCandidateQuaternionMap x = localColumn MidpointSeed.input 0 ↔
      x ∈ sphereCandidateTargetPreimage := by
  constructor
  · intro h
    have hv : (sphereCandidateProjection x).val = localProjection MidpointSeed.input 0 :=
      congrArg WithLp.ofLp (congrArg Subtype.val h)
    change (sphereCandidateProjection x).val = targetColumn
    exact hv.trans (by rw [localProjection_zero, MidpointSeed.input_hits_target])
  · intro h
    apply Subtype.ext
    change WithLp.toLp 2 (sphereCandidateProjection x).val =
      WithLp.toLp 2 (localProjection MidpointSeed.input 0)
    rw [localProjection_zero, MidpointSeed.input_hits_target]
    exact congrArg (WithLp.toLp 2) h

namespace MidpointSeed

local notation "Parameters" => ParameterSpace rotatedInput

def candidateTargetDomain : Set (Sphere 7) :=
  sphereCandidateQuaternionMap ⁻¹' (SphereCenteredCoordinates.chart (localColumn input 0)).source

theorem isOpen_candidateTargetDomain : IsOpen candidateTargetDomain :=
  (SphereCenteredCoordinates.chart (localColumn input 0)).open_source.preimage
    continuous_sphereCandidateQuaternionMap

theorem target_mem_candidateTargetDomain (x : Sphere 7) (hx : x ∈ sphereCandidateTargetPreimage) :
    x ∈ candidateTargetDomain := by
  change sphereCandidateQuaternionMap x ∈
    (SphereCenteredCoordinates.chart (localColumn input 0)).source
  rw [(sphereCandidateQuaternionMap_target_iff x).mpr hx]
  exact SphereCenteredCoordinates.self_mem_chart_source (localColumn input 0)

def targetCompactification : OnePoint Parameters ≃ₜ QSphere :=
  referenceDerivative.toHomeomorph.onePointCongr.trans
    (SphereCenteredCoordinates.compactification (localColumn input 0))

theorem targetCompactification_coe (p : Parameters) :
    targetCompactification (p : OnePoint Parameters) =
      SphereCenteredCoordinates.inverse (localColumn input 0) (referenceDerivative p) := rfl

theorem targetCompactification_zero :
    targetCompactification ((0 : Parameters) : OnePoint Parameters) = localColumn input 0 := by
  rw [targetCompactification_coe, map_zero, SphereCenteredCoordinates.inverse_zero]

theorem targetCompactification_symm_of_mem (q : QSphere)
    (hq : q ∈ (SphereCenteredCoordinates.chart (localColumn input 0)).source) :
    targetCompactification.symm q =
      (referenceDerivative.symm (SphereCenteredCoordinates.chart (localColumn input 0) q) :
        OnePoint Parameters) := by
  apply targetCompactification.injective
  rw [Homeomorph.apply_symm_apply, targetCompactification_coe,
    referenceDerivative.apply_symm_apply]
  exact ((SphereCenteredCoordinates.chart (localColumn input 0)).left_inv hq).symm

theorem targetCompactification_symm_zero_iff (q : QSphere) :
    targetCompactification.symm q = ((0 : Parameters) : OnePoint Parameters) ↔
      q = localColumn input 0 := by
  constructor
  · intro h
    have he := congrArg targetCompactification h
    simpa only [Homeomorph.apply_symm_apply, targetCompactification_zero] using he
  · intro h
    apply targetCompactification.injective
    rwa [Homeomorph.apply_symm_apply, targetCompactification_zero]

def compactifiedCandidate : C(Sphere 7, OnePoint Parameters) :=
  (targetCompactification.symm : C(QSphere, OnePoint Parameters)).comp quaternionCandidateMap

theorem compactifiedCandidate_eq_coe (x : Sphere 7) (hx : x ∈ candidateTargetDomain) :
    compactifiedCandidate x = (normalizedCandidateCoordinates x : OnePoint Parameters) :=
  targetCompactification_symm_of_mem (sphereCandidateQuaternionMap x) hx

theorem compactifiedCandidate_zero_iff (x : Sphere 7) :
    compactifiedCandidate x = ((0 : Parameters) : OnePoint Parameters) ↔
      x ∈ sphereCandidateTargetPreimage :=
  (targetCompactification_symm_zero_iff (sphereCandidateQuaternionMap x)).trans
    (sphereCandidateQuaternionMap_target_iff x)

theorem compactifiedCandidate_zero_fiber_ncard :
    {x | compactifiedCandidate x = ((0 : Parameters) : OnePoint Parameters)}.ncard = 12 := by
  have he : {x | compactifiedCandidate x = ((0 : Parameters) : OnePoint Parameters)} =
      sphereCandidateTargetPreimage := Set.ext compactifiedCandidate_zero_iff
  rw [he]
  exact sphereCandidateTargetPreimage_ncard_eq_twelve

end MidpointSeed

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
