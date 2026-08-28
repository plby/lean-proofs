import Wikipedia.HopfProblem.ThreefoldHomologyStarMaps
import Wikipedia.HopfProblem.ThreefoldHomologyStarTopology
import Wikipedia.HopfProblem.ThreefoldHomologyLowDegrees

/-!
# The actual star homology maps in degree zero

The coordinates below are the genuine singular augmentations of the
path-connected regular family, fillings, and overlaps.  Naturality makes
the signed overlap map the literal map `a ↦ (∑ i, a i, -a)`.  In particular,
the actual degree-zero overlap map is injective.  The following map is the
sum of all four coordinates in the augmentation of the actual threefold.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris PeriodTorusHigherHomology

local instance : PathConnectedSpace SpecialRegularFamily := by
  have := liftedPatch_pathConnectedSpace none
  exact originalRegularPatchHomeomorph.symm.surjective.pathConnectedSpace
    originalRegularPatchHomeomorph.symm.continuous

local instance (i : Puncture) : PathConnectedSpace (localPiece (some i)) := by
  have := liftedPatch_pathConnectedSpace (some i)
  exact (originalPatchHomeomorph (some i)).symm.surjective.pathConnectedSpace
    (originalPatchHomeomorph (some i)).symm.continuous

local instance (i : Puncture) : PathConnectedSpace (RegularOverlap i) :=
  liftedPatch_regular_inter_pathConnectedSpace i

/-- The canonical augmentation on the original regular family. -/
def starRegularH0Equiv : SingularHomology SpecialRegularFamily 0 ≃ₗ[ℤ] ℤ :=
  connectedHomologyZeroEquiv SpecialRegularFamily

/-- The canonical augmentation on an actual regular/filling overlap. -/
def starOverlapComponentH0Equiv (i : Puncture) :
    SingularHomology (RegularOverlap i) 0 ≃ₗ[ℤ] ℤ :=
  connectedHomologyZeroEquiv (RegularOverlap i)

/-- The canonical augmentation on an original geometric filling. -/
def starFillingComponentH0Equiv (i : Puncture) :
    SingularHomology (localPiece (some i)) 0 ≃ₗ[ℤ] ℤ :=
  connectedHomologyZeroEquiv (localPiece (some i))

/-- Augmentation coordinates on the three actual overlap homology groups. -/
def starOverlapH0Equiv : StarOverlapHomology 0 ≃ₗ[ℤ] (Puncture → ℤ) :=
  (AddEquiv.piCongrRight (fun i => (starOverlapComponentH0Equiv i).toAddEquiv)).toIntLinearEquiv

/-- Augmentation coordinates on the three original filling homology groups. -/
def starFillingH0Equiv : StarFillingHomology 0 ≃ₗ[ℤ] (Puncture → ℤ) :=
  (AddEquiv.piCongrRight (fun i => (starFillingComponentH0Equiv i).toAddEquiv)).toIntLinearEquiv

/-- The regular augmentation together with the three filling augmentations. -/
def starPairH0Equiv : StarPairHomology 0 ≃ₗ[ℤ] (ℤ × (Puncture → ℤ)) :=
  (starRegularH0Equiv.toAddEquiv.prodCongr starFillingH0Equiv.toAddEquiv).toIntLinearEquiv

@[simp] theorem starOverlapH0Equiv_apply (a : StarOverlapHomology 0) (i : Puncture) :
    starOverlapH0Equiv a i = starOverlapComponentH0Equiv i (a i) := rfl

@[simp] theorem starFillingH0Equiv_apply (a : StarFillingHomology 0) (i : Puncture) :
    starFillingH0Equiv a i = starFillingComponentH0Equiv i (a i) := rfl

@[simp] theorem starPairH0Equiv_apply (a : StarPairHomology 0) :
    starPairH0Equiv a = (starRegularH0Equiv a.1, starFillingH0Equiv a.2) := rfl

@[simp] theorem starRegularH0Equiv_pointClass (x : SpecialRegularFamily) :
    starRegularH0Equiv (pointClass x) = 1 :=
  connectedHomologyZeroEquiv_pointClass x

@[simp] theorem starOverlapComponentH0Equiv_pointClass (i : Puncture)
    (x : RegularOverlap i) : starOverlapComponentH0Equiv i (pointClass x) = 1 :=
  connectedHomologyZeroEquiv_pointClass x

@[simp] theorem starFillingComponentH0Equiv_pointClass (i : Puncture)
    (x : localPiece (some i)) : starFillingComponentH0Equiv i (pointClass x) = 1 :=
  connectedHomologyZeroEquiv_pointClass x

/-- The actual left overlap inclusion is the identity in augmentation coordinates. -/
theorem starRegularH0Equiv_overlap (i : Puncture)
    (a : SingularHomology (RegularOverlap i) 0) :
    starRegularH0Equiv (singularHomologyMap (overlapToRegularFamily i) 0 a) =
      starOverlapComponentH0Equiv i a :=
  connectedHomologyZeroEquiv_natural (overlapToRegularFamily i) a

/-- The actual right overlap inclusion is also the identity in augmentation coordinates. -/
theorem starFillingComponentH0Equiv_overlap (i : Puncture)
    (a : SingularHomology (RegularOverlap i) 0) :
    starFillingComponentH0Equiv i (singularHomologyMap (overlapToFilling i) 0 a) =
      starOverlapComponentH0Equiv i a :=
  connectedHomologyZeroEquiv_natural (overlapToFilling i) a

/-- The literal integral degree-zero signed matrix of the star cover. -/
def starLeftH0Coordinates : (Puncture → ℤ) →ₗ[ℤ] (ℤ × (Puncture → ℤ)) :=
  ({ toFun := fun a : Puncture → ℤ => (∑ i : Puncture, a i, -a)
     map_zero' := by simp
     map_add' := by
       intro a b
       apply Prod.ext
       · change Finset.univ.sum (fun i : Puncture => a i + b i) =
           Finset.univ.sum a + Finset.univ.sum b
         rw [Finset.sum_add_distrib]
       · exact neg_add a b } : (Puncture → ℤ) →+ (ℤ × (Puncture → ℤ))).toIntLinearMap

@[simp] theorem starLeftH0Coordinates_apply (a : Puncture → ℤ) :
    starLeftH0Coordinates a = (∑ i : Puncture, a i, -a) := rfl

/-- The full actual signed map, not only its columns, has the stated integral coordinates. -/
theorem starLeftHomologyMap_zero_coordinates (a : StarOverlapHomology 0) :
    starPairH0Equiv (starLeftHomologyMap 0 a) =
      starLeftH0Coordinates (starOverlapH0Equiv a) := by
  apply Prod.ext
  · change starRegularH0Equiv
      (∑ i : Puncture, singularHomologyMap (overlapToRegularFamily i) 0 (a i)) =
        ∑ i : Puncture, starOverlapComponentH0Equiv i (a i)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact starRegularH0Equiv_overlap i (a i)
  · funext i
    change starFillingComponentH0Equiv i
      (-singularHomologyMap (overlapToFilling i) 0 (a i)) =
        -starOverlapComponentH0Equiv i (a i)
    rw [map_neg, starFillingComponentH0Equiv_overlap]

theorem starLeftHomologyMap_zero_diagram :
    starPairH0Equiv.toLinearMap.comp (starLeftHomologyMap 0) =
      starLeftH0Coordinates.comp starOverlapH0Equiv.toLinearMap := by
  apply LinearMap.ext
  exact starLeftHomologyMap_zero_coordinates

theorem starLeftH0Coordinates_injective : Function.Injective starLeftH0Coordinates := by
  intro a b h
  have hn := congrArg Prod.snd h
  change -a = -b at hn
  exact neg_injective hn

/-- The actual degree-zero signed star-overlap map is injective. -/
theorem starLeftHomologyMap_zero_injective : Function.Injective (starLeftHomologyMap 0) := by
  intro a b h
  apply starOverlapH0Equiv.injective
  apply starLeftH0Coordinates_injective
  exact (starLeftHomologyMap_zero_coordinates a).symm.trans
    ((congrArg starPairH0Equiv h).trans (starLeftHomologyMap_zero_coordinates b))

/-- The following degree-zero map adds the regular and all filling coordinates. -/
def starRightH0Coordinates : (ℤ × (Puncture → ℤ)) →ₗ[ℤ] ℤ :=
  ({ toFun := fun a : ℤ × (Puncture → ℤ) => a.1 + Finset.univ.sum a.2
     map_zero' := by simp
     map_add' := by
       intro a b
       change (a.1 + b.1) + Finset.univ.sum (fun i : Puncture => a.2 i + b.2 i) =
         (a.1 + Finset.univ.sum a.2) + (b.1 + Finset.univ.sum b.2)
       rw [Finset.sum_add_distrib]
       abel } : (ℤ × (Puncture → ℤ)) →+ ℤ).toIntLinearMap

@[simp] theorem starRightH0Coordinates_apply (a : ℤ × (Puncture → ℤ)) :
    starRightH0Coordinates a = a.1 + ∑ i : Puncture, a.2 i := rfl

/-- The genuine global inclusion map is the sum of all four augmentations. -/
theorem starRightHomologyMap_zero_coordinates (a : StarPairHomology 0) :
    LowDegrees.singularH0Equiv (starRightHomologyMap 0 a) =
      starRightH0Coordinates (starPairH0Equiv a) := by
  change LowDegrees.singularH0Equiv
      (singularHomologyMap originalRegularInclusion 0 a.1 +
        ∑ i : Puncture, singularHomologyMap (originalPieceInclusion (some i)) 0 (a.2 i)) =
    starRegularH0Equiv a.1 + ∑ i : Puncture, starFillingComponentH0Equiv i (a.2 i)
  rw [map_add, map_sum]
  apply congrArg₂ (fun x y : ℤ => x + y)
  · exact LowDegrees.singularH0Equiv_natural originalRegularInclusion a.1
  · apply Finset.sum_congr rfl
    intro i _
    exact LowDegrees.singularH0Equiv_natural (originalPieceInclusion (some i)) (a.2 i)

theorem starRightHomologyMap_zero_diagram :
    LowDegrees.singularH0Equiv.toLinearMap.comp (starRightHomologyMap 0) =
      starRightH0Coordinates.comp starPairH0Equiv.toLinearMap := by
  apply LinearMap.ext
  exact starRightHomologyMap_zero_coordinates

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
