import Wikipedia.HopfProblem.CuspCentralHomologySuspensionMayerVietoris
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionCircles

/-!
# The actual Mayer–Vietoris kernel for three intersection components

If the two covering sets are path connected and their actual intersection
is homotopy equivalent to three circles, the difference of the two
intersection inclusions has kernel the sum-zero integer triples. The two
last coordinates give an integral basis of that kernel.

The inclusion formulas are proved from naturality of the actual singular
degree-zero augmentation; no coordinate formula for an unspecified map
is assumed.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open SingularMayerVietoris PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X]
variable (U V : Set X)

/-- The three actual component coordinates of the intersection, transported
through its specified genuine homotopy equivalence. -/
def threeCirclesIntersectionHomologyZeroEquiv
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles) :
    SingularHomology (U ∩ V : Set X) 0 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  ((homotopyEquivHomologyEquiv e 0).toAddEquiv.trans
    threeCirclesHomologyZeroEquiv.toAddEquiv).toIntLinearEquiv

@[simp] theorem threeCirclesIntersectionHomologyZeroEquiv_apply
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles)
    (a : SingularHomology (U ∩ V : Set X) 0) :
    threeCirclesIntersectionHomologyZeroEquiv U V e a =
      threeCirclesHomologyZeroEquiv (homotopyEquivHomologyEquiv e 0 a) := rfl

/-- Every map from the actual intersection to a path-connected target
adds its three component coordinates. -/
theorem threeCirclesIntersectionHomologyZeroEquiv_map
    {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y]
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles)
    (f : C((U ∩ V : Set X), Y))
    (a : SingularHomology (U ∩ V : Set X) 0) :
    connectedHomologyZeroEquiv Y (singularHomologyMap f 0 a) =
      sumCoordinates (threeCirclesIntersectionHomologyZeroEquiv U V e a) :=
  threeCirclesHomologyZeroEquiv_map_homotopyEquiv e f a

variable [PathConnectedSpace U] [PathConnectedSpace V]

/-- The actual difference-of-inclusions map vanishes exactly on the
sum-zero three-component coordinates. -/
theorem threeCirclesIntersectionLeftMap_zero_iff
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles)
    (a : SingularHomology (U ∩ V : Set X) 0) :
    leftHomologyMap U V 0 a = 0 ↔
      sumCoordinates (threeCirclesIntersectionHomologyZeroEquiv U V e a) = 0 := by
  constructor
  · intro ha
    have hleft : singularHomologyMap
        (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) 0 a = 0 := by
      rw [leftHomologyMap_apply] at ha
      exact congrArg Prod.fst ha
    have hsum := threeCirclesIntersectionHomologyZeroEquiv_map U V e
      (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) a
    rw [hleft, map_zero] at hsum
    exact hsum.symm
  · intro ha
    have hleft : singularHomologyMap
        (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) 0 a = 0 := by
      apply (connectedHomologyZeroEquiv U).injective
      rw [map_zero, threeCirclesIntersectionHomologyZeroEquiv_map U V e]
      exact ha
    have hright : singularHomologyMap
        (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) 0 a = 0 := by
      apply (connectedHomologyZeroEquiv V).injective
      rw [map_zero, threeCirclesIntersectionHomologyZeroEquiv_map U V e]
      exact ha
    rw [leftHomologyMap_apply, hleft, hright, neg_zero]
    rfl

theorem threeCirclesIntersection_mem_ker_iff
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles)
    (a : SingularHomology (U ∩ V : Set X) 0) :
    a ∈ LinearMap.ker (leftHomologyMap U V 0) ↔
      threeCirclesIntersectionHomologyZeroEquiv U V e a ∈
        LinearMap.ker sumCoordinates :=
  threeCirclesIntersectionLeftMap_zero_iff U V e a

/-- The actual degree-zero Mayer–Vietoris kernel identifies with the
actual kernel of the three-coordinate augmentation. -/
def threeCirclesIntersectionKernelToSumEquiv
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles) :
    LinearMap.ker (leftHomologyMap U V 0) ≃ₗ[ℤ] LinearMap.ker sumCoordinates :=
  ({ toFun a := ⟨threeCirclesIntersectionHomologyZeroEquiv U V e a,
       (threeCirclesIntersection_mem_ker_iff U V e a).mp a.property⟩
     invFun b := ⟨(threeCirclesIntersectionHomologyZeroEquiv U V e).symm b, by
       apply (threeCirclesIntersection_mem_ker_iff U V e _).mpr
       simpa only [LinearEquiv.apply_symm_apply] using b.property⟩
     left_inv a := Subtype.ext
       ((threeCirclesIntersectionHomologyZeroEquiv U V e).symm_apply_apply a)
     right_inv b := Subtype.ext
       ((threeCirclesIntersectionHomologyZeroEquiv U V e).apply_symm_apply b)
     map_add' a b := Subtype.ext
       ((threeCirclesIntersectionHomologyZeroEquiv U V e).map_add a b) } :
    LinearMap.ker (leftHomologyMap U V 0) ≃+ LinearMap.ker sumCoordinates).toIntLinearEquiv

@[simp] theorem threeCirclesIntersectionKernelToSumEquiv_coe
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles)
    (a : LinearMap.ker (leftHomologyMap U V 0)) :
    (threeCirclesIntersectionKernelToSumEquiv U V e a : Fin 3 → ℤ) =
      threeCirclesIntersectionHomologyZeroEquiv U V e a := rfl

/-- Two component differences form an actual integral basis of the
Mayer–Vietoris kernel of an intersection homotopy equivalent to three circles. -/
def threeCirclesIntersectionKernelEquiv
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles) :
    LinearMap.ker (leftHomologyMap U V 0) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((threeCirclesIntersectionKernelToSumEquiv U V e).toAddEquiv.trans
    sumCoordinatesKernelEquiv.toAddEquiv).toIntLinearEquiv

@[simp] theorem threeCirclesIntersectionKernelEquiv_apply
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles)
    (a : LinearMap.ker (leftHomologyMap U V 0)) :
    threeCirclesIntersectionKernelEquiv U V e a =
      ![threeCirclesIntersectionHomologyZeroEquiv U V e a 1,
        threeCirclesIntersectionHomologyZeroEquiv U V e a 2] := rfl

end Wikipedia.HopfProblem.CuspCentralHomology
