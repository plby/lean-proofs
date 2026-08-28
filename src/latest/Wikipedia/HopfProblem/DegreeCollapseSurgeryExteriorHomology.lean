import Wikipedia.HopfProblem.DegreeCollapseSurgeryExteriorDeformation
import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryReverse
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Actual homology coordinates from the surgery exterior deformations

Both original exterior inclusions give genuine homotopy equivalences onto
the core and belt complements. Their homology coordinates retain the maps
into the original endpoint spaces. Normalizing a smaller radial sphere
recovers exactly the original corner map.
-/

noncomputable section

open ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorRetraction

open Wikipedia.SmoothSixDPoincare PuncturedHandle
open SingularMayerVietoris PeriodTorusHigherHomology

variable {E F R X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair E F R X Y)

def newHomotopyEquiv : R ≃ₕ d.NewComplement := homotopyEquiv d.reverse

theorem newHomotopyEquiv_point (r : R) : (newHomotopyEquiv d r).val = d.newExterior r := rfl

def oldHomologyEquiv (n : ℕ) : SingularHomology R n ≃ₗ[ℤ] SingularHomology d.OldComplement n :=
  homotopyEquivHomologyEquiv (homotopyEquiv d) n

def newHomologyEquiv (n : ℕ) : SingularHomology R n ≃ₗ[ℤ] SingularHomology d.NewComplement n :=
  homotopyEquivHomologyEquiv (newHomotopyEquiv d) n

theorem oldHomologyEquiv_apply (n : ℕ) (c : SingularHomology R n) :
    oldHomologyEquiv d n c = singularHomologyMap (exteriorInclusion d) n c := rfl

theorem newHomologyEquiv_apply (n : ℕ) (c : SingularHomology R n) :
    newHomologyEquiv d n c =
      singularHomologyMap ⟨d.newExteriorMap, d.isClosedEmbedding_newExteriorMap.continuous⟩ n c := rfl

theorem oldHomologyEquiv_original_map (n : ℕ) (c : SingularHomology R n) :
    singularHomologyMap (⟨Subtype.val, continuous_subtype_val⟩ : C(d.OldComplement, X)) n
      (oldHomologyEquiv d n c) =
        singularHomologyMap ⟨d.oldExterior, d.oldExterior_closed.continuous⟩ n c := by
  rw [oldHomologyEquiv_apply, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

theorem newHomologyEquiv_original_map (n : ℕ) (c : SingularHomology R n) :
    singularHomologyMap (⟨Subtype.val, continuous_subtype_val⟩ : C(d.NewComplement, Y)) n
      (newHomologyEquiv d n c) =
        singularHomologyMap ⟨d.newExterior, d.newExterior_closed.continuous⟩ n c := by
  rw [newHomologyEquiv_apply, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

def radialSphereMap (r : Radius) : C(UnitSphere E × UnitSphere F, d.OldComplement) := by
  let q : C(UnitSphere F, PuncturedBall F) :=
    ⟨fun v ↦ point v r, (polar F).symm.continuous.comp
      (continuous_id.prodMk continuous_const)⟩
  exact (puncturedInclusion d).comp (ContinuousMap.fst.prodMk (q.comp ContinuousMap.snd))

theorem radialSphereMap_point (r : Radius) (q : UnitSphere E × UnitSphere F) :
    (radialSphereMap d r q).val =
      d.oldPiece (q.1, puncturedToBall (point q.2 r)) := rfl

theorem retraction_radialSphereMap (r : Radius) :
    (retraction d).comp (radialSphereMap d r) = boundaryMap d := by
  apply ContinuousMap.ext
  intro q
  change retraction d (d.oldPuncturedMap (q.1, point q.2 r)) = d.boundary q
  rw [retraction_punctured]
  have h : PuncturedClosedBallRetraction.direction (point q.2 r) = q.2 :=
    congrArg Prod.fst ((polar F).apply_symm_apply (q.2, r))
  rw [h]

/-- The inverse homology coordinate sends a genuine smaller radial sphere to the actual corner. -/
theorem oldHomologyEquiv_radialSphere (r : Radius) (n : ℕ)
    (c : SingularHomology (UnitSphere E × UnitSphere F) n) :
    (oldHomologyEquiv d n).symm (singularHomologyMap (radialSphereMap d r) n c) =
      singularHomologyMap (boundaryMap d) n c := by
  change singularHomologyMap (retraction d) n
    (singularHomologyMap (radialSphereMap d r) n c) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, retraction_radialSphereMap]

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryExteriorRetraction
