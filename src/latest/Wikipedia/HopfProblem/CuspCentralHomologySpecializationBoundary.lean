import Wikipedia.HopfProblem.CuspCentralHomologySpecializationBoundaryBasic
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationBoundaryComparison
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationBoundaryHomotopy
import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseHomology

/-!
# The actual specialization is surjective onto boundary homology

The restriction of the marked product collapse to compact phases times the
theta graph lands in the literal central boundary.  Its actual phase shear
is interpolated on each edge, giving a genuine homotopy in that boundary to
the character-collapse map.  The previously proved character computation
therefore gives surjectivity on actual integral degree-two singular homology.

The map identities and homotopy need no analytic assumptions.  Admissibility
is used only for the proved homeomorphism between the actual double locus
and the three-circle suspension; no geometric compatibility is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb SpecializationModel
open PeriodTorusHigherHomology SingularMayerVietoris

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The original suspension parametrization, bundled with the already
proved continuity into the literal central boundary. -/
def doubleSuspensionBoundaryContinuousMap :
    C(ThreeCircleSuspension, centralBoundary C ε hε) :=
  ⟨doubleSuspensionBoundaryMap C ε hε,
    doubleSuspensionBoundaryMap_continuous C ε hε⟩

@[simp] theorem doubleSuspensionBoundaryContinuousMap_coe (p : ThreeCircleSuspension) :
    (doubleSuspensionBoundaryContinuousMap C ε hε p : QuotientCentralFibre C ε) =
      doubleSuspensionMap C ε hε p := rfl

/-- Equality in the original central quotient, with the genuine source
phase correction retained on each oriented theta edge. -/
theorem boundaryLift_coe_eq_doubleSuspensionMap (p : CompactFibreTorus × Theta) :
    (boundaryLift C ε hε p : QuotientCentralFibre C ε) =
      doubleSuspensionMap C ε hε (shearedThetaCollapse (C 0) p) := by
  rcases p with ⟨u, q⟩
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rw [boundaryLift_mk_coe, shearedThetaCollapse_mk,
    doubleSuspensionMap_character_orientedEdge]

/-- The actual boundary lift, not an auxiliary map with the same homology,
is exactly the sheared character map in the suspension parametrization. -/
theorem boundaryLift_eq_doubleSuspensionBoundaryMap_comp :
    boundaryLift C ε hε =
      (doubleSuspensionBoundaryContinuousMap C ε hε).comp
        (shearedThetaCollapse (C 0)) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact boundaryLift_coe_eq_doubleSuspensionMap C ε hε p

/-- A genuine homotopy in the literal central boundary removes the source
phase shear.  No radius-smallness or holomorphicity assumption is needed. -/
def boundaryLiftCharacterHomotopy :
    ((doubleSuspensionBoundaryContinuousMap C ε hε).comp thetaCharacterCollapse).Homotopy
      (boundaryLift C ε hε) :=
  ((ContinuousMap.Homotopy.refl (doubleSuspensionBoundaryContinuousMap C ε hε)).comp
    (thetaShearHomotopy (C 0))).cast rfl
      (boundaryLift_eq_doubleSuspensionBoundaryMap_comp C ε hε).symm

/-- The boundary homotopy is given by the original honeycomb collapse,
with the actual linear phase argument scaled by the homotopy parameter. -/
theorem boundaryLiftCharacterHomotopy_mk_coe
    (s : unitInterval) (u : CompactFibreTorus) (t : unitInterval) (j : Fin 3) :
    (boundaryLiftCharacterHomotopy C ε hε (s, (u, Suspension.mk t j)) :
        QuotientCentralFibre C ε) =
      honeycombCollapseMap C ε hε
        (u * sourcePhaseCharacter (C 0) ((s : ℝ) • orientedEdgeBasePoint t j),
          orientedEdgeBasePoint t j) := by
  change doubleSuspensionMap C ε hε
    (thetaShearHomotopy (C 0) (s, (u, Suspension.mk t j))) = _
  rw [thetaShearHomotopy_mk, doubleSuspensionMap_character_orientedEdge]

/-- The exact singular homology formula follows from the constructed
continuous homotopy, in every degree. -/
theorem boundaryLift_homology_eq (n : ℕ) :
    singularHomologyMap (boundaryLift C ε hε) n =
      (singularHomologyMap (doubleSuspensionBoundaryContinuousMap C ε hε) n).comp
        (singularHomologyMap thetaCharacterCollapse n) := by
  rw [← homotopy_homologyMap (boundaryLiftCharacterHomotopy C ε hε) n]
  exact singularHomologyMap_comp thetaCharacterCollapse
    (doubleSuspensionBoundaryContinuousMap C ε hε) n

/-- In particular the phase-corrected map on the actual suspension has
the same surjective degree-two homology map as the character collapse. -/
theorem shearedThetaCollapse_homologyTwo_surjective
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Surjective (singularHomologyMap (shearedThetaCollapse C₀) 2) := by
  rw [← homotopy_homologyMap (thetaShearHomotopy C₀) 2]
  exact thetaCharacterCollapse_homologyTwo_surjective

variable (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The continuous parametrization used in the homotopy is the original
proved homeomorphism onto the actual double locus. -/
theorem doubleSuspensionBoundaryContinuousMap_eq_homeomorph :
    doubleSuspensionBoundaryContinuousMap C ε hε =
      (doubleSuspensionBoundaryHomeomorph C ε hε hε1 hC hR :
        C(ThreeCircleSuspension, centralBoundary C ε hε)) := rfl

/-- Exact comparison using the actual inherited boundary topology. -/
theorem boundaryLift_eq_homeomorph_comp_shearedThetaCollapse :
    boundaryLift C ε hε =
      (doubleSuspensionBoundaryHomeomorph C ε hε hε1 hC hR :
        C(ThreeCircleSuspension, centralBoundary C ε hε)).comp
        (shearedThetaCollapse (C 0)) := by
  rw [boundaryLift_eq_doubleSuspensionBoundaryMap_comp,
    doubleSuspensionBoundaryContinuousMap_eq_homeomorph C ε hε hε1 hC hR]

include hε1 hC hR in
/-- The restriction of the actual product specialization to compact
phases times the marked theta graph surjects onto actual integral `H₂(D)`. -/
theorem boundaryLift_homologyTwo_surjective :
    Function.Surjective (singularHomologyMap (boundaryLift C ε hε) 2) := by
  rw [boundaryLift_homology_eq,
    doubleSuspensionBoundaryContinuousMap_eq_homeomorph C ε hε hε1 hC hR]
  exact (homeomorphHomologyEquiv
    (doubleSuspensionBoundaryHomeomorph C ε hε hε1 hC hR) 2).surjective.comp
      thetaCharacterCollapse_homologyTwo_surjective

include hε1 hC hR in
theorem boundaryLift_homologyTwo_range :
    LinearMap.range (singularHomologyMap (boundaryLift C ε hε) 2) = ⊤ :=
  LinearMap.range_eq_top.mpr (boundaryLift_homologyTwo_surjective C ε hε hε1 hC hR)

include hε1 hC hR in
/-- Every central degree-two class coming from the actual boundary is
already in the image of the actual marked product specialization. -/
theorem boundaryInclusion_homologyTwo_range_le_productCollapse :
    LinearMap.range (singularHomologyMap (centralBoundaryInclusion C ε hε) 2) ≤
      LinearMap.range (singularHomologyMap (productCollapse C ε hε) 2) := by
  rintro _ ⟨b, rfl⟩
  obtain ⟨c, hc⟩ := boundaryLift_homologyTwo_surjective C ε hε hε1 hC hR b
  refine ⟨singularHomologyMap thetaProductMap 2 c, ?_⟩
  have h := congrArg (fun f => singularHomologyMap f 2)
    (centralBoundaryInclusion_comp_boundaryLift C ε hε)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  have he := LinearMap.congr_fun h c
  change singularHomologyMap (centralBoundaryInclusion C ε hε) 2
      (singularHomologyMap (boundaryLift C ε hε) 2 c) =
    singularHomologyMap (productCollapse C ε hε) 2
      (singularHomologyMap thetaProductMap 2 c) at he
  rw [hc] at he
  exact he.symm

end Wikipedia.HopfProblem.CuspCentralHomology
