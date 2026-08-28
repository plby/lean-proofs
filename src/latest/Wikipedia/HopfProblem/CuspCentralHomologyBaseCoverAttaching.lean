import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverCompatibility
import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseForget
import Wikipedia.HopfProblem.CuspCentralHomologySuspension
import Wikipedia.HopfProblem.CuspCentralHomologyAttachingCrossNull
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroups
import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Homology of the actual hexagonal attaching circle

Mayer--Vietoris for the actual base-torus radial cover makes the literal
theta inclusion surjective on first homology: the inner region is
contractible and the overlap is connected. Forgetting the circle in the
three-circle suspension has an explicit continuous section. The composite
of this forgetful map and the theta inclusion is therefore a surjection
between the two independently computed integral rank-two groups. Orzech's
theorem makes this composite injective, hence the actual theta inclusion
is injective on first homology.

The original attaching circle contracts in the base torus by the proved
radial homotopy. Its first-homology map already vanishes in the theta
graph by the preceding injectivity. Higher degrees vanish in the actual
theta graph by its suspension Mayer--Vietoris calculation.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

open ToricSpace SingularMayerVietoris PeriodTorusHigherHomology

/-- Connectedness is transported from the actual frontier and open radial interval. -/
theorem overlapRegion_pathConnectedSpace (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    PathConnectedSpace (overlapRegion a) := by
  let : PathConnectedSpace Radial.CellFrontier :=
    Radial.frontierCellCircleHomeomorph.symm.surjective.pathConnectedSpace
      Radial.frontierCellCircleHomeomorph.symm.continuous
  let : PathConnectedSpace (Ioo a 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ioo a 1).isPathConnected (nonempty_Ioo.mpr ha1))
  exact (overlapHomeomorph a ha).symm.surjective.pathConnectedSpace
    (overlapHomeomorph a ha).symm.continuous

local notation "U" => outerRegion (1 / 2)
local notation "V" => innerRegion
local notation "A" => overlapRegion (1 / 2)

/-- The actual degree-zero intersection map is injective. Its inner
component preserves the genuine connected-space augmentation. -/
theorem halfCoverLeftHomologyZero_injective :
    Function.Injective (leftHomologyMap U V 0) := by
  let := overlapRegion_pathConnectedSpace (1 / 2) (by norm_num) (by norm_num)
  let i : C(A, V) := ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)
  intro x y hxy
  have hi : singularHomologyMap i 0 x = singularHomologyMap i 0 y := by
    have h := congrArg Prod.snd hxy
    simp only [leftHomologyMap_apply, neg_inj] at h
    change singularHomologyMap i 0 x = singularHomologyMap i 0 y at h
    exact h
  apply (connectedHomologyZeroEquiv A).injective
  have h := congrArg (connectedHomologyZeroEquiv V) hi
  exact (connectedHomologyZeroEquiv_natural i x).symm.trans
    (h.trans (connectedHomologyZeroEquiv_natural i y))

/-- The genuine Mayer--Vietoris sum of inclusions is surjective in
degree one because the connecting map has zero image in degree zero. -/
theorem halfCoverRightHomologyOne_surjective :
    Function.Surjective (rightHomologyMap U V 1) := by
  let hU := outerRegion_isOpen (1 / 2)
  let hV := innerRegion_isOpen
  let hc := outerRegion_union_innerRegion (1 / 2) (by norm_num)
  intro x
  have hz : connectingHomomorphism U V hU hV hc 0 x = 0 := by
    apply halfCoverLeftHomologyZero_injective
    have h := LinearMap.congr_fun (connectingHomomorphism_comp_left U V hU hV hc 0) x
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using h
  have hm : x ∈ LinearMap.ker (connectingHomomorphism U V hU hV hc 0) := hz
  rw [← exact_at_ambient U V hU hV hc 0] at hm
  exact hm

/-- Every actual first-homology class of the base torus comes from its
literal theta boundary. The inner-region summand is zero by contractibility. -/
theorem thetaBaseMap_homology_one_surjective :
    Function.Surjective (singularHomologyMap thetaBaseMap 1) := by
  let : Subsingleton (SingularHomology V 1) :=
    contractible_homology_subsingleton V 1 (by decide)
  let e := outerRegionThetaHomotopyEquiv (1 / 2) (by norm_num) (by norm_num)
  let E := homotopyEquivHomologyEquiv e 1
  have he : (subtypeInclusion U).comp e.symm.toFun = thetaBaseMap := by
    apply ContinuousMap.ext
    intro q
    rfl
  intro z
  obtain ⟨⟨x, y⟩, hxy⟩ := halfCoverRightHomologyOne_surjective z
  refine ⟨E x, ?_⟩
  rw [← he, singularHomologyMap_comp]
  change singularHomologyMap (subtypeInclusion U) 1 (E.symm (E x)) = z
  rw [E.symm_apply_apply]
  have hy : y = 0 := Subsingleton.elim _ _
  simpa only [rightHomologyMap_apply, hy, map_zero, add_zero] using hxy

/-- The actual forgetful map has a section obtained by setting all
compact phase coordinates equal to one in the character collapse. -/
def thetaForgetSection : C(Theta, ThreeCircleSuspension) :=
  ⟨fun q => thetaCharacterCollapse (1, q),
    thetaCharacterCollapse.continuous.comp (continuous_const.prodMk continuous_id)⟩

@[simp] theorem thetaForgetCircle_section (q : Theta) :
    thetaForgetCircle (thetaForgetSection q) = q :=
  thetaForgetCircle_collapse 1 q

theorem thetaForgetCircle_comp_section :
    thetaForgetCircle.comp thetaForgetSection = ContinuousMap.id Theta := by
  apply ContinuousMap.ext
  exact thetaForgetCircle_section

/-- This surjectivity is induced by an actual continuous section, in every degree. -/
theorem thetaForgetCircle_homology_surjective (n : ℕ) :
    Function.Surjective (singularHomologyMap thetaForgetCircle n) := by
  have h : (singularHomologyMap thetaForgetCircle n).comp
      (singularHomologyMap thetaForgetSection n) = LinearMap.id := by
    rw [← singularHomologyMap_comp, thetaForgetCircle_comp_section,
      singularHomologyMap_id]
  intro x
  exact ⟨singularHomologyMap thetaForgetSection n x, LinearMap.congr_fun h x⟩

/-- The actual suspension-to-base composite is injective over the integers,
by the independently computed rank-two groups and Orzech's theorem. -/
theorem thetaBaseMap_comp_forget_homology_one_injective :
    Function.Injective ((singularHomologyMap thetaBaseMap 1).comp
      (singularHomologyMap thetaForgetCircle 1)) := by
  let : Module.Finite ℤ (SingularHomology BaseTorus 1) :=
    productTorus_homology_finite 2 1
  let e : SingularHomology BaseTorus 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
    productTorusHomologyEquiv 2 1
  let i := threeCircleSuspensionHomologyOneEquiv.trans e.symm
  exact IsNoetherian.injective_of_surjective_of_injective i.toLinearMap _ i.injective
    (thetaBaseMap_homology_one_surjective.comp (thetaForgetCircle_homology_surjective 1))

/-- The literal theta inclusion is injective on actual integral first
homology, since every theta class lifts through the actual forgetful map. -/
theorem thetaBaseMap_homology_one_injective :
    Function.Injective (singularHomologyMap thetaBaseMap 1) := by
  intro x y hxy
  obtain ⟨x', rfl⟩ := thetaForgetCircle_homology_surjective 1 x
  obtain ⟨y', rfl⟩ := thetaForgetCircle_homology_surjective 1 y
  exact congrArg (singularHomologyMap thetaForgetCircle 1)
    (thetaBaseMap_comp_forget_homology_one_injective hxy)

/-- The isomorphism is precisely the homology map of the actual theta inclusion. -/
def thetaBaseMapHomologyOneEquiv :
    SingularHomology Theta 1 ≃ₗ[ℤ] SingularHomology BaseTorus 1 :=
  LinearEquiv.ofBijective (singularHomologyMap thetaBaseMap 1)
    ⟨thetaBaseMap_homology_one_injective, thetaBaseMap_homology_one_surjective⟩

@[simp] theorem thetaBaseMapHomologyOneEquiv_apply (x : SingularHomology Theta 1) :
    thetaBaseMapHomologyOneEquiv x = singularHomologyMap thetaBaseMap 1 x := rfl

/-- The actual theta graph has integral first homology of rank two,
marked through its literal inclusion into the already marked base torus. -/
def thetaHomologyOneEquiv : SingularHomology Theta 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  thetaBaseMapHomologyOneEquiv.trans (productTorusHomologyEquiv 2 1)

/-- The actual hexagonal attaching circle is zero on first homology:
its image contracts in the base torus and the theta inclusion is injective. -/
theorem circleThetaMap_homology_one_eq_zero :
    singularHomologyMap circleThetaMap 1 = 0 := by
  have hzero := singularHomologyMap_eq_zero_of_nullhomotopic
    (thetaBaseMap.comp circleThetaMap)
    ⟨baseTorusPoint 0, thetaBaseMap_circleThetaMap_homotopic_const⟩ 1 (by decide)
  rw [singularHomologyMap_comp] at hzero
  apply LinearMap.ext
  intro x
  apply thetaBaseMap_homology_one_injective
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using
    LinearMap.congr_fun hzero x

/-- The original attaching circle induces zero in every positive degree. -/
theorem circleThetaMap_homology_eq_zero (n : ℕ) :
    singularHomologyMap circleThetaMap (n + 1) = 0 := by
  cases n with
  | zero => exact circleThetaMap_homology_one_eq_zero
  | succ n =>
      let : Subsingleton (SingularHomology Theta (n + 2)) :=
        theta_homology_subsingleton n
      exact Subsingleton.elim _ _

end Wikipedia.HopfProblem.CuspCentralHomology.BaseCover
