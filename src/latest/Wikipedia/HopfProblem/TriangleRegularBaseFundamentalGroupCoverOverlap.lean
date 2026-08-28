import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCoverSets
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Tactic.FinCases

/-!
# The three components of the slit-cover overlap

The upper and lower slit domains overlap in three disjoint open vertical
strips.  Each strip is convex and contains a specified real basepoint, so
each is contractible and simply connected.  The strips are proved to be
exactly the connected components and the path components of the overlap.
-/

noncomputable section

open Set Complex
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The left, middle, and right open strips in the slit-cover overlap. -/
def overlapStrip : Fin 3 → Set ℂ
  | 0 => {z | z.re < 0}
  | 1 => {z | 0 < z.re ∧ z.re < 1}
  | 2 => {z | 1 < z.re}

/-- Explicit real basepoints in the three overlap strips. -/
def overlapStripBasepoint : Fin 3 → ℂ
  | 0 => -1
  | 1 => ((1 / 2 : ℝ) : ℂ)
  | 2 => 2

theorem overlapStrip_basepoint_mem (i : Fin 3) :
    overlapStripBasepoint i ∈ overlapStrip i := by
  fin_cases i <;> norm_num [overlapStripBasepoint, overlapStrip]

/-- Each overlap strip with its specified basepoint. -/
def overlapStripPoint (i : Fin 3) : overlapStrip i :=
  ⟨overlapStripBasepoint i, overlapStrip_basepoint_mem i⟩

theorem overlapStrip_nonempty (i : Fin 3) : (overlapStrip i).Nonempty :=
  ⟨overlapStripBasepoint i, overlapStrip_basepoint_mem i⟩

theorem overlapStrip_isOpen (i : Fin 3) : IsOpen (overlapStrip i) := by
  fin_cases i
  · exact isOpen_lt continuous_re continuous_const
  · exact (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)
  · exact isOpen_lt continuous_const continuous_re

theorem overlapStrip_convex (i : Fin 3) : Convex ℝ (overlapStrip i) := by
  fin_cases i
  · exact convex_halfSpace_re_lt 0
  · exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  · exact convex_halfSpace_re_gt 1

theorem overlapStrip_isPathConnected (i : Fin 3) : IsPathConnected (overlapStrip i) :=
  (overlapStrip_convex i).isPathConnected (overlapStrip_nonempty i)

theorem overlapStrip_isConnected (i : Fin 3) : IsConnected (overlapStrip i) :=
  (overlapStrip_isPathConnected i).isConnected

instance overlapStrip_contractibleSpace (i : Fin 3) : ContractibleSpace (overlapStrip i) :=
  (overlapStrip_convex i).contractibleSpace (overlapStrip_nonempty i)

instance overlapStrip_simplyConnectedSpace (i : Fin 3) :
    SimplyConnectedSpace (overlapStrip i) :=
  SimplyConnectedSpace.ofContractible _

/-- Any two points in one strip are joined by a path staying in that strip. -/
theorem overlapStrip_joinedIn (i : Fin 3) {z w : ℂ}
    (hz : z ∈ overlapStrip i) (hw : w ∈ overlapStrip i) :
    JoinedIn (overlapStrip i) z w :=
  JoinedIn.of_segment_subset ((overlapStrip_convex i).segment_subset hz hw)

theorem overlapStrip_pairwise_disjoint :
    Pairwise (fun i j : Fin 3 => Disjoint (overlapStrip i) (overlapStrip j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  fin_cases i <;> fin_cases j <;> simp_all [overlapStrip] <;> linarith

/-- The overlap is exactly the disjoint union of the three actual strips. -/
theorem overlapStrip_iUnion :
    (⋃ i : Fin 3, overlapStrip i) = upperSlitPlane ∩ lowerSlitPlane := by
  rw [slitPlanes_inter]
  ext z
  rw [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp only [overlapStrip, mem_ofPred_eq] at hi ⊢ <;>
      constructor <;> intro heq <;> linarith
  · rintro ⟨hzero, hone⟩
    rcases lt_or_gt_of_ne hzero with hneg | hpos
    · exact ⟨0, hneg⟩
    · rcases lt_or_gt_of_ne hone with hlt | hgt
      · exact ⟨1, hpos, hlt⟩
      · exact ⟨2, hgt⟩

theorem overlapStrip_subset_overlap (i : Fin 3) :
    overlapStrip i ⊆ upperSlitPlane ∩ lowerSlitPlane := by
  rw [← overlapStrip_iUnion]
  exact subset_iUnion overlapStrip i

/-- Each strip is precisely the connected component of any of its points
inside the overlap of the two slit domains. -/
theorem overlapStrip_connectedComponentIn (i : Fin 3) {z : ℂ}
    (hz : z ∈ overlapStrip i) :
    connectedComponentIn (upperSlitPlane ∩ lowerSlitPlane) z = overlapStrip i := by
  let R : Set ℂ := ⋃ j : Fin 3, ⋃ (_ : j ≠ i), overlapStrip j
  have hRopen : IsOpen R :=
    isOpen_iUnion fun j => isOpen_iUnion fun _ => overlapStrip_isOpen j
  have hdisj : Disjoint (overlapStrip i) R := by
    apply disjoint_iUnion_right.mpr
    intro j
    apply disjoint_iUnion_right.mpr
    intro hji
    exact overlapStrip_pairwise_disjoint hji.symm
  have hcover : upperSlitPlane ∩ lowerSlitPlane ⊆ overlapStrip i ∪ R := by
    rw [← overlapStrip_iUnion]
    intro w hw
    obtain ⟨j, hj⟩ := mem_iUnion.mp hw
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j, hji, hj⟩)
  apply subset_antisymm
  · have hc : IsPreconnected (connectedComponentIn (upperSlitPlane ∩ lowerSlitPlane) z) :=
      isPreconnected_connectedComponentIn
    exact hc.subset_left_of_subset_union (overlapStrip_isOpen i) hRopen hdisj
      ((connectedComponentIn_subset _ _).trans hcover)
      ⟨z, mem_connectedComponentIn (overlapStrip_subset_overlap i hz), hz⟩
  · exact (overlapStrip_isConnected i).isPreconnected.subset_connectedComponentIn hz
      (overlapStrip_subset_overlap i)

/-- The same strips are precisely the path components of the overlap. -/
theorem overlapStrip_pathComponentIn (i : Fin 3) {z : ℂ}
    (hz : z ∈ overlapStrip i) :
    pathComponentIn (upperSlitPlane ∩ lowerSlitPlane) z = overlapStrip i := by
  have hzO := overlapStrip_subset_overlap i hz
  apply subset_antisymm
  · calc
      pathComponentIn (upperSlitPlane ∩ lowerSlitPlane) z ⊆
          connectedComponentIn (upperSlitPlane ∩ lowerSlitPlane) z :=
        (isPathConnected_pathComponentIn hzO).isConnected.isPreconnected.subset_connectedComponentIn
          (mem_pathComponentIn_self hzO) pathComponentIn_subset
      _ = overlapStrip i := overlapStrip_connectedComponentIn i hz
  · exact (overlapStrip_isPathConnected i).subset_pathComponentIn hz
      (overlapStrip_subset_overlap i)

/-- Two points can be joined inside the slit-cover overlap exactly when
they lie in the same one of the three strips. -/
theorem overlap_joinedIn_iff {z w : ℂ} :
    JoinedIn (upperSlitPlane ∩ lowerSlitPlane) z w ↔
      ∃ i : Fin 3, z ∈ overlapStrip i ∧ w ∈ overlapStrip i := by
  constructor
  · intro h
    have hz : z ∈ ⋃ i : Fin 3, overlapStrip i := by
      rw [overlapStrip_iUnion]
      exact h.source_mem
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    refine ⟨i, hi, ?_⟩
    have hm : w ∈ pathComponentIn (upperSlitPlane ∩ lowerSlitPlane) z := h
    rwa [overlapStrip_pathComponentIn i hi] at hm
  · rintro ⟨i, hz, hw⟩
    exact (overlapStrip_joinedIn i hz hw).mono (overlapStrip_subset_overlap i)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
