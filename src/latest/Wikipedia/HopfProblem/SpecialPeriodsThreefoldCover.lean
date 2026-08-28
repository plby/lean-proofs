import Wikipedia.HopfProblem.SpecialPeriodsThreefoldBase
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegular
import Mathlib.Topology.Sets.OpenCover

/-!
# The finite actual base cover for the threefold construction

The entire regular three-puncture complement, together with the three
small genuine chart discs, covers the actual compact triangle curve.
The filling discs are pairwise disjoint.  Inside each disc the intersection
with the regular base is exactly its punctured coordinate disc, so distinct
fillings have no overlap and every nontrivial transition uses the regular
family.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

/-- One regular patch and one filling patch for each of the three marks. -/
abbrev Index := Option Puncture

theorem mem_regularPatch_iff_ne_puncture (x : TriangleCompactifiedOrbitSpace) :
    x ∈ regularPatch ↔ ∀ i : Puncture, x ≠ puncturePoint i := by
  rw [mem_regularPatch]
  constructor
  · rintro ⟨hc, h₁, h₂⟩ i
    cases i with
    | none => exact hc
    | some j => cases j <;> assumption
  · intro h
    exact ⟨h none, h (some .three), h (some .four)⟩

theorem not_mem_regularPatch_iff (x : TriangleCompactifiedOrbitSpace) :
    x ∉ regularPatch ↔ ∃ i : Puncture, x = puncturePoint i := by
  classical
  rw [mem_regularPatch_iff_ne_puncture]
  simp only [not_forall, ne_eq, not_not]

namespace BaseCover

variable (C : BaseCover)

/-- The actual four-patch open family on the original compact quotient. -/
def patch : Index → TopologicalSpace.Opens TriangleCompactifiedOrbitSpace
  | none => regularPatch
  | some i => C.fillingPatch i

@[simp] theorem patch_regular : C.patch none = regularPatch := rfl

@[simp] theorem patch_filling (i : Puncture) : C.patch (some i) = C.fillingPatch i := rfl

/-- Every point of the actual compact curve belongs to one of these four
patches; no supplied covering assertion is used. -/
theorem exists_patch (x : TriangleCompactifiedOrbitSpace) : ∃ i : Index, x ∈ C.patch i := by
  classical
  by_cases hx : x ∈ regularPatch
  · exact ⟨none, hx⟩
  · obtain ⟨i, rfl⟩ := (not_mem_regularPatch_iff x).mp hx
    exact ⟨some i, C.point_mem_fillingPatch i⟩

theorem isOpenCover : TopologicalSpace.IsOpenCover C.patch := by
  change (⨆ i, C.patch i) = ⊤
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := C.exists_patch x
  exact (le_iSup C.patch i) hi

theorem patch_iUnion :
    ⋃ i : Index, (C.patch i : Set TriangleCompactifiedOrbitSpace) = univ :=
  C.isOpenCover.iSup_set_eq_univ

/-- Distinct filling patches cannot meet even at a regular point. -/
theorem filling_indices_eq_of_mem {i j : Puncture} {x : TriangleCompactifiedOrbitSpace}
    (hi : x ∈ C.fillingPatch i) (hj : x ∈ C.fillingPatch j) : i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (C.fillingPatch_disjoint hij) hi hj

/-- Inside a filling disc the regular part removes exactly its own
marked center; the other two marked points are already excluded. -/
theorem fillingPatch_regular_iff (i : Puncture) {x : TriangleCompactifiedOrbitSpace}
    (hx : x ∈ C.fillingPatch i) :
    x ∈ regularPatch ↔ x ≠ puncturePoint i := by
  constructor
  · intro h
    exact (mem_regularPatch_iff_ne_puncture x).mp h i
  · intro hne
    apply (mem_regularPatch_iff_ne_puncture x).mpr
    intro j hxj
    have hji : j = i := (C.point_mem_fillingPatch_iff j i).mp (hxj ▸ hx)
    exact hne (hxj.trans (congrArg puncturePoint hji))

/-- Equivalently, the entire regular overlap is exactly the nonzero
part of the original genuine local coordinate. -/
theorem fillingPatch_regular_iff_coordinate_ne_zero (i : Puncture)
    {x : TriangleCompactifiedOrbitSpace} (hx : x ∈ C.fillingPatch i) :
    x ∈ regularPatch ↔ punctureChart i x ≠ 0 :=
  (C.fillingPatch_regular_iff i hx).trans (not_congr (C.chart_eq_zero_iff i hx)).symm

theorem fillingPatch_inter_regular (i : Puncture) :
    (C.fillingPatch i : Set TriangleCompactifiedOrbitSpace) ∩ regularPatch =
      (C.fillingPatch i : Set TriangleCompactifiedOrbitSpace) \ {puncturePoint i} := by
  ext x
  constructor
  · rintro ⟨hx, hr⟩
    exact ⟨hx, (C.fillingPatch_regular_iff i hx).mp hr⟩
  · rintro ⟨hx, hp⟩
    exact ⟨hx, (C.fillingPatch_regular_iff i hx).mpr hp⟩

/-- The inverse original coordinate identifies the punctured ball with
the full overlap with the regular base. -/
theorem inverse_mem_regular_iff (i : Puncture) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (C.radius i)) :
    (punctureChart i).symm z ∈ regularPatch ↔ z ≠ 0 := by
  rw [C.fillingPatch_regular_iff_coordinate_ne_zero i (C.inverse_mem_fillingPatch i hz),
    (punctureChart i).right_inv (C.coordinateBall_subset_target i hz)]

/-- There is no intersection of three distinct patches.  In particular
no extra triple-overlap compatibility between different fillings is needed. -/
theorem triple_mem_indices {i j k : Index} {x : TriangleCompactifiedOrbitSpace}
    (hi : x ∈ C.patch i) (hj : x ∈ C.patch j) (hk : x ∈ C.patch k) :
    i = j ∨ j = k ∨ i = k := by
  cases i with
  | none =>
      cases j with
      | none => exact Or.inl rfl
      | some j =>
          cases k with
          | none => exact Or.inr (Or.inr rfl)
          | some k => exact Or.inr (Or.inl (congrArg some (C.filling_indices_eq_of_mem hj hk)))
  | some i =>
      cases j with
      | none =>
          cases k with
          | none => exact Or.inr (Or.inl rfl)
          | some k => exact Or.inr (Or.inr (congrArg some (C.filling_indices_eq_of_mem hi hk)))
      | some j => exact Or.inl (congrArg some (C.filling_indices_eq_of_mem hi hj))

end BaseCover

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
