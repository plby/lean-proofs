import Wikipedia.HopfProblem.ThreefoldHomologyGluingOriginalPieces
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The actual threefold star cover as disjoint unions

The full regular patch and the union of the three disjoint filling patches
cover the constructed threefold.  Their overlap is the disjoint union of
the genuine regular/filling overlaps.  All maps use the original patch
homeomorphisms and preserve the underlying point of the threefold.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris

/-- A disjoint family of open subsets is homeomorphic to its literal union. -/
def disjointOpenUnionHomeomorph {ι X : Type*} [TopologicalSpace X]
    (U : ι → TopologicalSpace.Opens X)
    (h : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X))) :
    (Σ i, U i) ≃ₜ (⋃ i, (U i : Set X)) := by
  refine (Equiv.ofBijective _ (Set.sigmaToiUnion_bijective
    (fun i => (U i : Set X)) h)).toHomeomorphOfContinuousOpen ?_ ?_
  · exact continuous_sigma (fun i => continuous_subtype_val.subtype_mk _)
  · exact isOpenMap_sigma.mpr
      (fun i => (U i).isOpen.isOpenMap_subtype_val.subtype_mk _)

@[simp] theorem disjointOpenUnionHomeomorph_apply_val {ι X : Type*}
    [TopologicalSpace X] (U : ι → TopologicalSpace.Opens X)
    (h : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X)))
    (x : Σ i, U i) :
    (disjointOpenUnionHomeomorph U h x : X) = (x.2 : X) := rfl

/-- The open union of the three actual filling patches. -/
def starFillings : TopologicalSpace.Opens Space :=
  ⟨⋃ i : Puncture, (liftedPatch (some i) : Set Space),
    isOpen_iUnion (fun i => (liftedPatch (some i)).isOpen)⟩

/-- The literal overlap of the regular patch with the filling union. -/
def starOverlap : TopologicalSpace.Opens Space := liftedPatch none ⊓ starFillings

@[simp] theorem starFillings_coe :
    (starFillings : Set Space) = ⋃ i : Puncture, (liftedPatch (some i) : Set Space) := rfl

@[simp] theorem mem_starFillings (x : Space) :
    x ∈ starFillings ↔ ∃ i : Puncture, x ∈ liftedPatch (some i) :=
  Set.mem_iUnion

theorem filling_le_starFillings (i : Puncture) :
    (liftedPatch (some i) : Set Space) ⊆ starFillings := by
  intro x hx
  exact (mem_starFillings x).mpr ⟨i, hx⟩

/-- The full regular patch and all three full fillings cover the actual space. -/
theorem star_cover : (liftedPatch none : Set Space) ∪ starFillings = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x _
  have hx : x ∈ ⋃ i : Index, (liftedPatch i : Set Space) := by
    rw [liftedPatch_iUnion]
    trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  cases i with
  | none => exact Or.inl hi
  | some i => exact Or.inr (filling_le_starFillings i hi)

/-- The star overlap is the union of the literal regular/filling overlaps. -/
theorem starOverlap_eq_iUnion :
    (starOverlap : Set Space) = ⋃ i : Puncture, (RegularOverlap i : Set Space) := by
  change (liftedPatch none : Set Space) ∩
      (⋃ i : Puncture, (liftedPatch (some i) : Set Space)) =
    ⋃ i : Puncture, (liftedPatch none : Set Space) ∩ liftedPatch (some i)
  exact Set.inter_iUnion _ _

/-- Distinct components of the actual star overlap are disjoint. -/
theorem regularOverlap_pairwise_disjoint :
    Pairwise (fun i j : Puncture =>
      Disjoint (RegularOverlap i : Set Space) (RegularOverlap j : Set Space)) := by
  intro i j hij
  exact (liftedFilling_disjoint hij).mono Set.inter_subset_right Set.inter_subset_right

/-- The disjoint original fillings carry their actual original patch homeomorphisms. -/
def sigmaOriginalFillingHomeomorph :
    (Σ i : Puncture, localPiece (some i)) ≃ₜ
      (Σ i : Puncture, liftedPatch (some i)) where
  toEquiv := Equiv.sigmaCongrRight (fun i => (originalPatchHomeomorph (some i)).toEquiv)
  continuous_toFun := continuous_sigma
    (fun i => continuous_sigmaMk.comp (originalPatchHomeomorph (some i)).continuous)
  continuous_invFun := continuous_sigma
    (fun i => continuous_sigmaMk.comp (originalPatchHomeomorph (some i)).symm.continuous)

/-- The union of the actual fillings is their disjoint topological sum. -/
def starFillingsHomeomorph :
    (Σ i : Puncture, localPiece (some i)) ≃ₜ starFillings :=
  sigmaOriginalFillingHomeomorph.trans
    (disjointOpenUnionHomeomorph (fun i : Puncture => liftedPatch (some i))
      (fun _ _ hij => liftedFilling_disjoint hij))

@[simp] theorem starFillingsHomeomorph_val (i : Puncture) (x : localPiece (some i)) :
    (starFillingsHomeomorph ⟨i, x⟩ : Space) = inclusion (some i) x := rfl

theorem starFillingsHomeomorph_apply_val (x : Σ i : Puncture, localPiece (some i)) :
    (starFillingsHomeomorph x : Space) = inclusion (some x.1) x.2 := rfl

/-- The full star overlap is the disjoint sum of its genuine components. -/
def starOverlapHomeomorph :
    (Σ i : Puncture, RegularOverlap i) ≃ₜ starOverlap :=
  (disjointOpenUnionHomeomorph
    (fun i : Puncture => liftedPatch none ⊓ liftedPatch (some i))
    regularOverlap_pairwise_disjoint).trans
      (Homeomorph.setCongr starOverlap_eq_iUnion.symm)

@[simp] theorem starOverlapHomeomorph_val (i : Puncture) (x : RegularOverlap i) :
    (starOverlapHomeomorph ⟨i, x⟩ : Space) = x.val := rfl

theorem starOverlapHomeomorph_apply_val (x : Σ i : Puncture, RegularOverlap i) :
    (starOverlapHomeomorph x : Space) = x.2.val := rfl

/-- The original geometric filling included in the open filling union. -/
def fillingToStar (i : Puncture) : C(localPiece (some i), starFillings) :=
  (ContinuousMap.inclusion (filling_le_starFillings i)).comp
    (originalPatchHomeomorph (some i) : C(localPiece (some i), liftedPatch (some i)))

@[simp] theorem fillingToStar_val (i : Puncture) (x : localPiece (some i)) :
    (fillingToStar i x : Space) = inclusion (some i) x := rfl

/-- The literal inclusion of one regular/filling overlap into the star overlap. -/
def overlapToStar (i : Puncture) : C(RegularOverlap i, starOverlap) :=
  ⟨fun x => ⟨x.val, x.property.1, filling_le_starFillings i x.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp] theorem overlapToStar_val (i : Puncture) (x : RegularOverlap i) :
    (overlapToStar i x : Space) = x.val := rfl

/-- The actual left inclusion of the star overlap. -/
def starOverlapToRegularPatch : C(starOverlap, liftedPatch none) :=
  ContinuousMap.inclusion Set.inter_subset_left

/-- The actual right inclusion of the star overlap. -/
def starOverlapToFillings : C(starOverlap, starFillings) :=
  ContinuousMap.inclusion Set.inter_subset_right

/-- The left overlap map expressed in the original regular-family coordinates. -/
def starOverlapToRegular : C(starOverlap, SpecialRegularFamily) :=
  (originalRegularPatchHomeomorph.symm :
    C(liftedPatch none, SpecialRegularFamily)).comp starOverlapToRegularPatch

@[simp] theorem starOverlapToRegularPatch_val (x : starOverlap) :
    (starOverlapToRegularPatch x : Space) = x.val := rfl

@[simp] theorem starOverlapToFillings_val (x : starOverlap) :
    (starOverlapToFillings x : Space) = x.val := rfl

theorem starOverlapToRegular_overlapToStar (i : Puncture) :
    starOverlapToRegular.comp (overlapToStar i) = overlapToRegularFamily i := rfl

/-- Each right overlap inclusion is the original filling map followed by
the genuine inclusion of that filling into the union. -/
theorem starOverlapToFillings_overlapToStar (i : Puncture) :
    starOverlapToFillings.comp (overlapToStar i) =
      (fillingToStar i).comp (overlapToFilling i) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact (inclusion_overlapToFilling i x).symm

theorem fillingToStar_ambient (i : Puncture) :
    (subtypeInclusion (starFillings : Set Space)).comp (fillingToStar i) =
      originalPieceInclusion (some i) := rfl

theorem overlapToStar_ambient (i : Puncture) :
    (subtypeInclusion (starOverlap : Set Space)).comp (overlapToStar i) =
      subtypeInclusion (RegularOverlap i : Set Space) := rfl

/-- The filling homeomorphism restricts to each literal coproduct inclusion. -/
theorem starFillingsHomeomorph_sigmaMk (i : Puncture) :
    (starFillingsHomeomorph : C((Σ j : Puncture, localPiece (some j)), starFillings)).comp
        (ContinuousMap.sigmaMk i) = fillingToStar i := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The overlap homeomorphism restricts to each literal coproduct inclusion. -/
theorem starOverlapHomeomorph_sigmaMk (i : Puncture) :
    (starOverlapHomeomorph : C((Σ j : Puncture, RegularOverlap j), starOverlap)).comp
        (ContinuousMap.sigmaMk i) = overlapToStar i := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

theorem starOverlapToRegular_homeomorph_sigmaMk (i : Puncture) :
    (starOverlapToRegular.comp
      (starOverlapHomeomorph : C((Σ j : Puncture, RegularOverlap j), starOverlap))).comp
        (ContinuousMap.sigmaMk i) = overlapToRegularFamily i := by
  change starOverlapToRegular.comp
    ((starOverlapHomeomorph : C((Σ j : Puncture, RegularOverlap j), starOverlap)).comp
      (ContinuousMap.sigmaMk i)) = _
  rw [starOverlapHomeomorph_sigmaMk, starOverlapToRegular_overlapToStar]

theorem starOverlapToFillings_homeomorph_sigmaMk (i : Puncture) :
    (starOverlapToFillings.comp
      (starOverlapHomeomorph : C((Σ j : Puncture, RegularOverlap j), starOverlap))).comp
        (ContinuousMap.sigmaMk i) =
      ((starFillingsHomeomorph :
        C((Σ j : Puncture, localPiece (some j)), starFillings)).comp
          (ContinuousMap.sigmaMk i)).comp (overlapToFilling i) := by
  change starOverlapToFillings.comp
    ((starOverlapHomeomorph : C((Σ j : Puncture, RegularOverlap j), starOverlap)).comp
      (ContinuousMap.sigmaMk i)) = _
  rw [starOverlapHomeomorph_sigmaMk, starFillingsHomeomorph_sigmaMk,
    starOverlapToFillings_overlapToStar]

/-- The disjoint filling coordinates preserve the original ambient inclusions. -/
theorem starFillingsHomeomorph_ambient :
    (subtypeInclusion (starFillings : Set Space)).comp
        (starFillingsHomeomorph :
          C((Σ i : Puncture, localPiece (some i)), starFillings)) =
      ContinuousMap.sigma (fun i : Puncture => originalPieceInclusion (some i)) := rfl

/-- The overlap coordinates preserve the literal ambient subtype inclusions. -/
theorem starOverlapHomeomorph_ambient :
    (subtypeInclusion (starOverlap : Set Space)).comp
        (starOverlapHomeomorph : C((Σ i : Puncture, RegularOverlap i), starOverlap)) =
      ContinuousMap.sigma (fun i : Puncture =>
        subtypeInclusion (RegularOverlap i : Set Space)) := rfl

/-- In original regular-family coordinates the left star map is the
continuous map assembled from the actual individual overlap maps. -/
theorem starOverlapHomeomorph_regular :
    starOverlapToRegular.comp
        (starOverlapHomeomorph : C((Σ i : Puncture, RegularOverlap i), starOverlap)) =
      ContinuousMap.sigma overlapToRegularFamily := rfl

/-- The right star map is assembled from the actual individual filling maps. -/
theorem starOverlapHomeomorph_fillings :
    starOverlapToFillings.comp
        (starOverlapHomeomorph : C((Σ i : Puncture, RegularOverlap i), starOverlap)) =
      (starFillingsHomeomorph :
        C((Σ i : Puncture, localPiece (some i)), starFillings)).comp
          (ContinuousMap.sigma (fun i : Puncture =>
            (ContinuousMap.sigmaMk i).comp (overlapToFilling i))) := by
  apply ContinuousMap.ext
  rintro ⟨i, x⟩
  apply Subtype.ext
  exact (inclusion_overlapToFilling i x).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
