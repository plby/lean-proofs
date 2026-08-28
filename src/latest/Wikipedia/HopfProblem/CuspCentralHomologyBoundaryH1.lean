import Wikipedia.HopfProblem.CuspCentralHomologyLowDegrees
import Wikipedia.HopfProblem.CuspCentralHomologyDoubleLocusHomology
import Wikipedia.HopfProblem.CuspCentralHomologyInnerNullhomotopy
import Wikipedia.HopfProblem.CuspCentralHomologyBoundaryLoopNullhomotopy
import Wikipedia.HopfProblem.CuspCentralHomologyAttachingCrossNull
import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Actual first homology of the boundary inclusion

The inner-region inclusion is genuinely nullhomotopic.  Mayer–Vietoris
therefore makes the boundary inclusion surjective on first homology.
Both actual groups were independently computed as the integral rank-two
module, so the inclusion is an isomorphism over `ℤ`.  The actual boundary
direction loop extends across its hexagonal disk in the whole central
fibre; injectivity then proves that its first-homology class already
vanishes in the boundary.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

include hε1 hC hR

theorem centralBoundary_pathConnectedSpace :
    PathConnectedSpace (centralBoundary C ε hε) :=
  (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).symm.surjective.pathConnectedSpace
    (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).symm.continuous

theorem overlapRegion_pathConnectedSpace (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    PathConnectedSpace (overlapRegion C ε hε a) := by
  let : PathConnectedSpace Radial.CellFrontier :=
    Radial.frontierCellCircleHomeomorph.symm.surjective.pathConnectedSpace
      Radial.frontierCellCircleHomeomorph.symm.continuous
  let : PathConnectedSpace (Ioo a 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ioo a 1).isPathConnected (nonempty_Ioo.mpr ha1))
  exact (overlapHomeomorph C ε hε hε1 hC hR a ha).symm.surjective.pathConnectedSpace
    (overlapHomeomorph C ε hε hε1 hC hR a ha).symm.continuous

local notation "W" => QuotientCentralFibre C ε
local notation "U" => outerRegion C ε hε (1 / 2)
local notation "V" => innerRegion C ε hε
local notation "A" => overlapRegion C ε hε (1 / 2)
local notation "D" => centralBoundary C ε hε

/-- The degree-zero intersection map is injective, as it must be for
the actual connected overlap.  The proof uses genuine augmentations. -/
theorem halfCoverLeftHomologyZero_injective :
    Function.Injective (leftHomologyMap U V 0) := by
  let := centralBoundary_pathConnectedSpace C ε hε hε1 hC hR
  let := overlapRegion_pathConnectedSpace C ε hε hε1 hC hR
    (1 / 2) (by norm_num) (by norm_num)
  let e := outerRegionBoundaryHomotopyEquiv C ε hε (1 / 2)
    (by norm_num) (by norm_num) hε1 hC hR
  let i : C(A, U) := ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)
  let g : C(A, D) := e.toFun.comp i
  intro a b hab
  have hi : singularHomologyMap i 0 a = singularHomologyMap i 0 b := by
    have h := congrArg Prod.fst hab
    simp only [leftHomologyMap_apply] at h
    change singularHomologyMap i 0 a = singularHomologyMap i 0 b at h
    exact h
  have hg : singularHomologyMap g 0 a = singularHomologyMap g 0 b := by
    dsimp [g]
    rw [singularHomologyMap_comp]
    exact congrArg (singularHomologyMap e.toFun 0) hi
  apply (connectedHomologyZeroEquiv A).injective
  have hn := congrArg (connectedHomologyZeroEquiv D) hg
  exact (connectedHomologyZeroEquiv_natural g a).symm.trans
    (hn.trans (connectedHomologyZeroEquiv_natural g b))

/-- The degree-one sum of actual inclusion maps is surjective for this
connected two-set cover. -/
theorem halfCoverRightHomologyOne_surjective :
    Function.Surjective (rightHomologyMap U V 1) := by
  let hU := outerRegion_isOpen C ε hε hε1 hC hR (1 / 2)
  let hV := innerRegion_isOpen C ε hε hε1 hC hR
  let hc := outerRegion_union_innerRegion C ε hε (1 / 2) (by norm_num)
  intro a
  have hz : connectingHomomorphism U V hU hV hc 0 a = 0 := by
    apply halfCoverLeftHomologyZero_injective C ε hε hε1 hC hR
    have h := LinearMap.congr_fun (connectingHomomorphism_comp_left U V hU hV hc 0) a
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using h
  have hm : a ∈ LinearMap.ker (connectingHomomorphism U V hU hV hc 0) := hz
  rw [← exact_at_ambient U V hU hV hc 0] at hm
  exact hm

/-- All positive-degree classes of the inner open set die in the
original central fibre, by its explicit geometric nullhomotopy. -/
theorem innerRegionInclusion_homology_eq_zero (n : ℕ) :
    singularHomologyMap (innerRegionInclusion C ε hε) (n + 1) = 0 :=
  singularHomologyMap_eq_zero_of_nullhomotopic _
    (innerRegionInclusion_nullhomotopic C ε hε hε1 hC hR) (n + 1) (Nat.succ_ne_zero n)

/-- Every actual first-homology class of the central fibre comes from
its actual double locus. -/
theorem centralBoundaryInclusion_homology_one_surjective :
    Function.Surjective (singularHomologyMap (centralBoundaryInclusion C ε hε) 1) := by
  let e := outerRegionBoundaryHomotopyEquiv C ε hε (1 / 2)
    (by norm_num) (by norm_num) hε1 hC hR
  let E := homotopyEquivHomologyEquiv e 1
  have he : (subtypeInclusion U).comp e.symm.toFun = centralBoundaryInclusion C ε hε := by
    apply ContinuousMap.ext
    intro q
    rfl
  intro a
  obtain ⟨⟨x, y⟩, hxy⟩ := halfCoverRightHomologyOne_surjective C ε hε hε1 hC hR a
  refine ⟨E x, ?_⟩
  rw [← he, singularHomologyMap_comp]
  change singularHomologyMap (subtypeInclusion U) 1 (E.symm (E x)) = a
  rw [E.symm_apply_apply]
  have hv : singularHomologyMap (subtypeInclusion V) 1 = 0 :=
    innerRegionInclusion_homology_eq_zero C ε hε hε1 hC hR 0
  simpa only [rightHomologyMap_apply, hv, LinearMap.zero_apply, add_zero] using hxy

/-- Surjectivity between the two independently computed integral
rank-two groups is injectivity over `ℤ`, not merely after tensoring. -/
theorem centralBoundaryInclusion_homology_one_injective :
    Function.Injective (singularHomologyMap (centralBoundaryInclusion C ε hε) 1) := by
  let := centralSingularH1_finite C ε hε hC
  let i := (centralBoundaryHomologyOneEquiv C ε hε hε1 hC hR).trans
    (centralSingularH1Equiv C ε hε hC).symm
  exact IsNoetherian.injective_of_surjective_of_injective i.toLinearMap
    (singularHomologyMap (centralBoundaryInclusion C ε hε) 1) i.injective
    (centralBoundaryInclusion_homology_one_surjective C ε hε hε1 hC hR)

/-- The isomorphism is precisely the map induced by the literal boundary inclusion. -/
def centralBoundaryInclusionHomologyOneEquiv :
    SingularHomology D 1 ≃ₗ[ℤ] SingularHomology W 1 :=
  LinearEquiv.ofBijective (singularHomologyMap (centralBoundaryInclusion C ε hε) 1)
    ⟨centralBoundaryInclusion_homology_one_injective C ε hε hε1 hC hR,
      centralBoundaryInclusion_homology_one_surjective C ε hε hε1 hC hR⟩

/-- The actual boundary-direction loop has zero integral first homology
already in the double locus, because it contracts in the whole fibre
and the actual inclusion is injective on first homology. -/
theorem boundaryLoop_homology_one_eq_zero :
    singularHomologyMap (boundaryLoop C ε hε) 1 = 0 := by
  have hzero := singularHomologyMap_eq_zero_of_nullhomotopic _
    (centralBoundaryInclusion_comp_boundaryLoop_nullhomotopic C ε hε) 1 (by decide)
  rw [singularHomologyMap_comp] at hzero
  apply LinearMap.ext
  intro a
  apply centralBoundaryInclusion_homology_one_injective C ε hε hε1 hC hR
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using
    LinearMap.congr_fun hzero a

end Wikipedia.HopfProblem.CuspCentralHomology
