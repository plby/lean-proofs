import Wikipedia.HopfProblem.ThreefoldHomologyGluingOriginalPieces
import Mathlib.LinearAlgebra.Pi

/-!
# The literal homology maps for the threefold star cover

The source is the finite product of the homology groups of the three
actual overlaps.  Its map to the regular family and the three original
fillings has components the sum of the actual regular inclusions and
the negatives of the actual filling inclusions.  The following map is
the sum of all four actual inclusions into the constructed threefold.

No coordinates or ranks for any of these homology groups are chosen.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris

/-- The actual homology of all three regular/filling overlaps. -/
abbrev StarOverlapHomology (n : ℕ) :=
  ∀ i : Puncture, SingularHomology (RegularOverlap i) n

/-- The actual homology of all three original filling pieces. -/
abbrev StarFillingHomology (n : ℕ) :=
  ∀ i : Puncture, SingularHomology (localPiece (some i)) n

/-- The regular-family factor together with the three filling factors. -/
abbrev StarPairHomology (n : ℕ) :=
  SingularHomology SpecialRegularFamily n × StarFillingHomology n

/-- Sum the three actual maps into the original regular family. -/
def starOverlapToRegularHomologyMap (n : ℕ) :
    StarOverlapHomology n →ₗ[ℤ] SingularHomology SpecialRegularFamily n where
  toFun a := ∑ i : Puncture, singularHomologyMap (overlapToRegularFamily i) n (a i)
  map_add' a b := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [Pi.smul_apply, map_zsmul, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact (int_smul_eq_zsmul ..).symm

/-- The three original filling inclusions, component by component. -/
def starOverlapToFillingsHomologyMap (n : ℕ) :
    StarOverlapHomology n →ₗ[ℤ] StarFillingHomology n where
  toFun a i := singularHomologyMap (overlapToFilling i) n (a i)
  map_add' a b := by ext i; exact map_add _ _ _
  map_smul' r a := by
    ext i
    simp only [Pi.smul_apply, map_zsmul, RingHom.id_apply]

/-- The signed overlap map: positive on the regular factor, negative
on each of the three actual filling factors. -/
def starLeftHomologyMap (n : ℕ) :
    StarOverlapHomology n →ₗ[ℤ] StarPairHomology n :=
  ((starOverlapToRegularHomologyMap n).toAddMonoidHom.prod
    (-(starOverlapToFillingsHomologyMap n).toAddMonoidHom)).toIntLinearMap

/-- Sum the actual inclusions of the three original fillings into the
constructed global threefold. -/
def starFillingsToSpaceHomologyMap (n : ℕ) :
    StarFillingHomology n →ₗ[ℤ] SingularHomology Space n where
  toFun a := ∑ i : Puncture, singularHomologyMap (originalPieceInclusion (some i)) n (a i)
  map_add' a b := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [Pi.smul_apply, map_zsmul, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact (int_smul_eq_zsmul ..).symm

/-- The sum of the four literal piece inclusions into the actual threefold. -/
def starRightHomologyMap (n : ℕ) :
    StarPairHomology n →ₗ[ℤ] SingularHomology Space n := by
  let f := (singularHomologyMap originalRegularInclusion n).toAddMonoidHom.coprod
    (starFillingsToSpaceHomologyMap n).toAddMonoidHom
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' r a := by
        convert! f.map_zsmul r a using 1
        exact int_smul_eq_zsmul .. }

@[simp] theorem starOverlapToRegularHomologyMap_apply (n : ℕ)
    (a : StarOverlapHomology n) :
    starOverlapToRegularHomologyMap n a =
      ∑ i : Puncture, singularHomologyMap (overlapToRegularFamily i) n (a i) := rfl

@[simp] theorem starOverlapToFillingsHomologyMap_apply (n : ℕ)
    (a : StarOverlapHomology n) (i : Puncture) :
    starOverlapToFillingsHomologyMap n a i =
      singularHomologyMap (overlapToFilling i) n (a i) := rfl

@[simp] theorem starLeftHomologyMap_apply (n : ℕ) (a : StarOverlapHomology n) :
    starLeftHomologyMap n a =
      (∑ i : Puncture, singularHomologyMap (overlapToRegularFamily i) n (a i),
        fun i => -singularHomologyMap (overlapToFilling i) n (a i)) := rfl

@[simp] theorem starFillingsToSpaceHomologyMap_apply (n : ℕ)
    (a : StarFillingHomology n) :
    starFillingsToSpaceHomologyMap n a =
      ∑ i : Puncture, singularHomologyMap (originalPieceInclusion (some i)) n (a i) := rfl

@[simp] theorem starRightHomologyMap_apply (n : ℕ) (a : StarPairHomology n) :
    starRightHomologyMap n a =
      singularHomologyMap originalRegularInclusion n a.1 +
        ∑ i : Puncture, singularHomologyMap (originalPieceInclusion (some i)) n (a.2 i) := rfl

/-- Each overlap column consists of its genuine regular inclusion and
the negative of its genuine filling inclusion, with other filling entries zero. -/
theorem starLeftHomologyMap_single (n : ℕ) (i : Puncture)
    (a : SingularHomology (RegularOverlap i) n) :
    starLeftHomologyMap n (Pi.single i a) =
      (singularHomologyMap (overlapToRegularFamily i) n a,
        Pi.single i (-singularHomologyMap (overlapToFilling i) n a)) := by
  rw [starLeftHomologyMap_apply]
  apply Prod.ext
  · rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, map_zero]
    · simp
  · funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne h]

/-- The right map on a regular class and a single actual filling class. -/
theorem starRightHomologyMap_single (n : ℕ) (i : Puncture)
    (a : SingularHomology SpecialRegularFamily n)
    (b : SingularHomology (localPiece (some i)) n) :
    starRightHomologyMap n (a, Pi.single i b) =
      singularHomologyMap originalRegularInclusion n a +
        singularHomologyMap (originalPieceInclusion (some i)) n b := by
  change singularHomologyMap originalRegularInclusion n a +
    starFillingsToSpaceHomologyMap n (Pi.single i b) = _
  rw [starFillingsToSpaceHomologyMap_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

/-- The signed overlap map followed by the genuine global inclusion
map is zero, because the two routes agree as actual continuous maps. -/
theorem starRightHomologyMap_comp_left (n : ℕ) :
    (starRightHomologyMap n).comp (starLeftHomologyMap n) = 0 := by
  apply LinearMap.toAddMonoidHom_injective
  apply AddMonoidHom.functions_ext
  intro i a
  change starRightHomologyMap n (starLeftHomologyMap n (Pi.single i a)) = 0
  rw [starLeftHomologyMap_single, starRightHomologyMap_single, map_neg]
  have h := LinearMap.congr_fun
    ((originalPieceInclusion_homology_overlapToRegularFamily i n).trans
      (originalPieceInclusion_homology_overlapToFilling i n).symm) a
  change singularHomologyMap originalRegularInclusion n
      (singularHomologyMap (overlapToRegularFamily i) n a) =
    singularHomologyMap (originalPieceInclusion (some i)) n
      (singularHomologyMap (overlapToFilling i) n a) at h
  rw [h, add_neg_cancel]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
