import Wikipedia.HopfProblem.DegreeCollapseSurgeryOpenCoverCoordinates
import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# The actual exterior-to-end integral homology sequence

Transport the genuine open-cover sequence through the constructed homotopy
coordinates. The first map is the actual boundary map paired with minus
the first projection. The second is the sum of the original exterior
inclusion and the original attaching sphere. No homology vanishing,
freeness, torsion condition, or auxiliary filling is assumed.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorSequence

open Wikipedia.SmoothSixDPoincare PuncturedHandle
open SingularMayerVietoris PeriodTorusHigherHomology
open SurgeryExteriorRetraction SurgeryInteriorCoordinates

variable {E F R X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair E F R X Y)

def coreHomologyEquiv (n : ℕ) :
    SingularHomology (UnitSphere E) n ≃ₗ[ℤ] SingularHomology (interiorSet d) n :=
  homotopyEquivHomologyEquiv (coreHomotopyEquiv d) n

def overlapHomologyEquiv (n : ℕ) :
    SingularHomology (UnitSphere E × UnitSphere F) n ≃ₗ[ℤ]
      SingularHomology (overlapSet d) n :=
  homotopyEquivHomologyEquiv (overlapHomotopyEquiv d) n

def pairHomologyEquiv (n : ℕ) :
    (SingularHomology R n × SingularHomology (UnitSphere E) n) ≃ₗ[ℤ]
      (SingularHomology d.OldComplement n × SingularHomology (interiorSet d) n) :=
  ((oldHomologyEquiv d n).toAddEquiv.prodCongr
    (coreHomologyEquiv d n).toAddEquiv).toIntLinearEquiv

theorem coreHomologyEquiv_original_map (n : ℕ) (c : SingularHomology (UnitSphere E) n) :
    singularHomologyMap (subtypeInclusion (interiorSet d)) n (coreHomologyEquiv d n c) =
      singularHomologyMap d.attachingSphere n c := by
  change singularHomologyMap (subtypeInclusion (interiorSet d)) n
    (singularHomologyMap (coreHomotopyEquiv d).toFun n c) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

theorem overlap_left_homology (n : ℕ)
    (c : SingularHomology (UnitSphere E × UnitSphere F) n) :
    (oldHomologyEquiv d n).symm (singularHomologyMap
      (ContinuousMap.inclusion (inter_subset_left : overlapSet d ⊆ d.OldComplement)) n
        (overlapHomologyEquiv d n c)) = singularHomologyMap (boundaryMap d) n c := by
  change (oldHomologyEquiv d n).symm (singularHomologyMap
    (ContinuousMap.inclusion (inter_subset_left : overlapSet d ⊆ d.OldComplement)) n
      (singularHomologyMap (overlapHomotopyEquiv d).toFun n c)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, overlap_left]
  exact oldHomologyEquiv_radialSphere d halfRadius n c

theorem overlap_right_homology (n : ℕ)
    (c : SingularHomology (UnitSphere E × UnitSphere F) n) :
    (coreHomologyEquiv d n).symm (singularHomologyMap
      (ContinuousMap.inclusion (inter_subset_right : overlapSet d ⊆ interiorSet d)) n
        (overlapHomologyEquiv d n c)) = singularHomologyMap ContinuousMap.fst n c := by
  have h := congrArg (fun f ↦ singularHomologyMap f n c) (overlap_right_projection d)
  change singularHomologyMap (coreHomotopyEquiv d).invFun n (singularHomologyMap
    (ContinuousMap.inclusion (inter_subset_right : overlapSet d ⊆ interiorSet d)) n
      (singularHomologyMap (overlapHomotopyEquiv d).toFun n c)) = _
  simpa only [singularHomologyMap_comp, LinearMap.comp_apply] using h

def leftMap (n : ℕ) : SingularHomology (UnitSphere E × UnitSphere F) n →ₗ[ℤ]
    (SingularHomology R n × SingularHomology (UnitSphere E) n) :=
  (pairHomologyEquiv d n).symm.toLinearMap.comp
    ((leftHomologyMap d.OldComplement (interiorSet d) n).comp
      (overlapHomologyEquiv d n).toLinearMap)

def rightMap (n : ℕ) :
    (SingularHomology R n × SingularHomology (UnitSphere E) n) →ₗ[ℤ] SingularHomology X n :=
  (rightHomologyMap d.OldComplement (interiorSet d) n).comp
    (pairHomologyEquiv d n).toLinearMap

theorem leftMap_apply (n : ℕ) (c : SingularHomology (UnitSphere E × UnitSphere F) n) :
    leftMap d n c =
      (singularHomologyMap (boundaryMap d) n c, -singularHomologyMap ContinuousMap.fst n c) := by
  change (pairHomologyEquiv d n).symm
    (leftHomologyMap d.OldComplement (interiorSet d) n (overlapHomologyEquiv d n c)) = _
  rw [leftHomologyMap_apply]
  apply Prod.ext
  · exact overlap_left_homology d n c
  · change (coreHomologyEquiv d n).symm (-_) = _
    rw [map_neg, overlap_right_homology]

theorem rightMap_apply (n : ℕ)
    (c : SingularHomology R n × SingularHomology (UnitSphere E) n) :
    rightMap d n c =
      singularHomologyMap ⟨d.oldExterior, d.oldExterior_closed.continuous⟩ n c.1 +
        singularHomologyMap d.attachingSphere n c.2 := by
  change singularHomologyMap (subtypeInclusion d.OldComplement) n
    (oldHomologyEquiv d n c.1) + singularHomologyMap (subtypeInclusion (interiorSet d)) n
      (coreHomologyEquiv d n c.2) = _
  exact congrArg₂ (· + ·) (oldHomologyEquiv_original_map d n c.1)
    (coreHomologyEquiv_original_map d n c.2)

variable [ProperSpace E] [T2Space X]

def connecting (n : ℕ) :
    SingularHomology X (n + 1) →ₗ[ℤ] SingularHomology (UnitSphere E × UnitSphere F) n :=
  (overlapHomologyEquiv d n).symm.toLinearMap.comp
    (connectingHomomorphism d.OldComplement (interiorSet d)
      (isOpen_coreComplement d) (isOpen_interiorSet d) (complement_interior_cover d) n)

theorem exact_at_corner (n : ℕ) :
    LinearMap.range (connecting d n) = LinearMap.ker (leftMap d n) := by
  rw [leftMap, (pairHomologyEquiv d n).symm.ker_comp]
  exact rightTransport_range_eq_ker (overlapHomologyEquiv d n).symm
    (connectingHomomorphism d.OldComplement (interiorSet d)
      (isOpen_coreComplement d) (isOpen_interiorSet d) (complement_interior_cover d) n)
    (leftHomologyMap d.OldComplement (interiorSet d) n)
    (exact_at_intersection d.OldComplement (interiorSet d)
      (isOpen_coreComplement d) (isOpen_interiorSet d) (complement_interior_cover d) n)

theorem exact_at_exterior_core (n : ℕ) :
    LinearMap.range (leftMap d n) = LinearMap.ker (rightMap d n) := by
  change LinearMap.range (((pairHomologyEquiv d n).symm.toLinearMap.comp
    (leftHomologyMap d.OldComplement (interiorSet d) n)).comp
      (overlapHomologyEquiv d n).toLinearMap) = _
  rw [(overlapHomologyEquiv d n).range_comp]
  exact rightTransport_range_eq_ker (pairHomologyEquiv d n).symm
    (leftHomologyMap d.OldComplement (interiorSet d) n)
    (rightHomologyMap d.OldComplement (interiorSet d) n)
    (exact_at_pair d.OldComplement (interiorSet d)
      (isOpen_coreComplement d) (isOpen_interiorSet d) (complement_interior_cover d) n)

theorem exact_at_endpoint (n : ℕ) :
    LinearMap.range (rightMap d (n + 1)) = LinearMap.ker (connecting d n) := by
  rw [rightMap, (pairHomologyEquiv d (n + 1)).range_comp,
    connecting, (overlapHomologyEquiv d n).symm.ker_comp]
  exact exact_at_ambient d.OldComplement (interiorSet d)
    (isOpen_coreComplement d) (isOpen_interiorSet d) (complement_interior_cover d) n

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorSequence
