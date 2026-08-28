import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePointClass
import Wikipedia.HopfProblem.FirstHurewiczPathChains

/-!
# Actual point classes detect path components

A path-component indicator on singular zero-chains kills every actual
one-boundary. Thus equality of integral point classes forces a path, without
local connectedness assumptions on the space.
-/

noncomputable section

open Function ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

open Classical in
def componentChainWeight (x : X) : Chains X 0 →ₗ[ℤ] ℤ :=
  chainLift X 0 (fun σ => if Joined x (σ (stdSimplex.vertex 0)) then 1 else 0)

open Classical in
theorem componentChainWeight_point (x y : X) :
    componentChainWeight x (pointChain y) = if Joined x y then 1 else 0 := by
  exact chainLift_simplex X 0 _ _

theorem componentChainWeight_boundary (x : X) (b : Chains X 1) :
    componentChainWeight x (boundaryOne X b) = 0 := by
  classical
  have heq : (componentChainWeight x).comp (boundaryOne X) = 0 := by
    apply chainMap_ext X 1
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, boundaryOne_simplex, map_sub,
      componentChainWeight, chainLift_simplex, ContinuousMap.comp_apply,
      simplexFace_zero_zero, simplexFace_zero_one]
    have hp : Joined (σ (stdSimplex.vertex 0)) (σ (stdSimplex.vertex 1)) :=
      ⟨simplexPath σ⟩
    have hi : Joined x (σ (stdSimplex.vertex 1)) ↔
        Joined x (σ (stdSimplex.vertex 0)) :=
      ⟨fun h => h.trans hp.symm, fun h => h.trans hp⟩
    rw [hi, sub_self]
  exact LinearMap.congr_fun heq b

theorem pointClass_eq_iff_joined (x y : X) : pointClass x = pointClass y ↔ Joined x y := by
  classical
  constructor
  · intro h
    by_contra hn
    obtain ⟨b, hb⟩ := (ModuleHomology.cycleClass_eq_iff (singularComplex X) 0
      (pointCycle x) (pointCycle y)).mp h
    have he := congrArg (componentChainWeight x) hb
    change componentChainWeight x (boundaryOne X b) =
      componentChainWeight x (pointChain x - pointChain y) at he
    rw [componentChainWeight_boundary, map_sub, componentChainWeight_point,
      componentChainWeight_point, if_pos (Joined.refl x), if_neg hn] at he
    norm_num at he
  · rintro ⟨p⟩
    apply (ModuleHomology.cycleClass_eq_iff (singularComplex X) 0
      (pointCycle x) (pointCycle y)).mpr
    exact ⟨pathChain p.symm, boundaryOne_pathChain p.symm⟩

theorem joined_iff_of_homologyZero_injective (f : C(X, Y))
    (hf : Injective (singularHomologyMap f 0)) (x y : X) :
    Joined (f x) (f y) ↔ Joined x y := by
  rw [← pointClass_eq_iff_joined, ← pointClass_eq_iff_joined,
    ← singularHomologyMap_pointClass f, ← singularHomologyMap_pointClass f, hf.eq_iff]

theorem pathConnectedSpace_of_homologyZero_injective [Nonempty X] [PathConnectedSpace Y]
    (f : C(X, Y)) (hf : Injective (singularHomologyMap f 0)) : PathConnectedSpace X := by
  exact ⟨inferInstance, fun x y => (joined_iff_of_homologyZero_injective f hf x y).mp
    (PathConnectedSpace.joined (f x) (f y))⟩

theorem pathConnectedSpace_of_homotopyEquiv [PathConnectedSpace Y]
    (e : X ≃ₕ Y) : PathConnectedSpace X := by
  let : Nonempty X := ⟨e.invFun (Classical.arbitrary Y)⟩
  exact pathConnectedSpace_of_homologyZero_injective e.toFun
    (homotopyEquivHomologyEquiv e 0).injective

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
