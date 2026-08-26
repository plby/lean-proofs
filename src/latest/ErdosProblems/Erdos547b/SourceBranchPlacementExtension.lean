/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceOriginalBranchPlacement

/-!
# Image-preserving extension of literal branch placements

New closed matching chunks can be attached to an existing partial forest
without changing any earlier image. Assignment and orientation are pasted
on the actual disjoint source domains. The exact used-image union is proved
as well, so later root exclusions can be tied to the constructed state.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceOriginalBranchPlacement

open Finset SimpleGraph
open Erdos547b.RegularPair Erdos547b.ForestMatching

universe u v

variable {b : ℕ} {V : Type u} {K : Type v}
variable {F : OrderedRootedForest b} {G : SimpleGraph V}
variable {parent : Fin b → V} {endpoint : K → Fin 2 → Finset V}
variable {s t : Finset (Fin b)}

def BranchPlacement.empty (F : OrderedRootedForest b) (G : SimpleGraph V)
    (parent : Fin b → V) (endpoint : K → Fin 2 → Finset V) :
    BranchPlacement F G ∅ parent endpoint where
  edge i := (Finset.notMem_empty _ i.2).elim
  orient i := (Finset.notMem_empty _ i.2).elim
  forestCopy := {
    componentCopy := fun _ hi => (Finset.notMem_empty _ hi).elim
    disjoint_ranges := fun _ hi => (Finset.notMem_empty _ hi).elim }
  attach _ hi := (Finset.notMem_empty _ hi).elim
  map_side _ hi := (Finset.notMem_empty _ hi).elim

/-- Updating the outer-root map preserves every placed branch image. -/
def BranchPlacement.reparent (E : BranchPlacement F G s parent endpoint)
    (parent' : Fin b → V) (hagrees : ∀ i ∈ s, parent' i = parent i) :
    BranchPlacement F G s parent' endpoint where
  edge := E.edge
  orient := E.orient
  forestCopy := E.forestCopy
  attach i hi := by rw [hagrees i hi]; exact E.attach i hi
  map_side := E.map_side

private theorem disjoint_ranges_of_support
    (E₁ : BranchPlacement F G s parent endpoint)
    (E₂ : BranchPlacement F G t parent endpoint)
    (hsupport : ∀ i : {i // i ∈ s}, ∀ j : {j // j ∈ t}, ∀ c d,
      Disjoint (endpoint (E₁.edge i) c) (endpoint (E₂.edge j) d))
    (i : Fin b) (hi : i ∈ s) (j : Fin b) (hj : j ∈ t) :
    Disjoint (Set.range (E₁.forestCopy.componentCopy i hi : Fin (F.size i) → V))
      (Set.range (E₂.forestCopy.componentCopy j hj : Fin (F.size j) → V)) := by
  rw [Set.disjoint_left]
  rintro x ⟨a, rfl⟩ ⟨d, h⟩
  have ha := E₁.map_side i hi a
  have hd := E₂.map_side j hj d
  exact Finset.disjoint_left.mp (hsupport ⟨i, hi⟩ ⟨j, hj⟩ _ _) ha (h ▸ hd)

/-- Append an independently realized batch on disjoint matching supports.
Every copy already present in the first state is definitionally preserved. -/
def BranchPlacement.append
    (E₁ : BranchPlacement F G s parent endpoint)
    (E₂ : BranchPlacement F G t parent endpoint)
    (hsupport : ∀ i : {i // i ∈ s}, ∀ j : {j // j ∈ t}, ∀ c d,
      Disjoint (endpoint (E₁.edge i) c) (endpoint (E₂.edge j) d)) :
    BranchPlacement F G (s ∪ t) parent endpoint := by
  let edge := fun i : {i // i ∈ s ∪ t} =>
    if hi : i.1 ∈ s then E₁.edge ⟨i.1, hi⟩
    else E₂.edge ⟨i.1, (Finset.mem_union.mp i.2).resolve_left hi⟩
  let orient := fun i : {i // i ∈ s ∪ t} =>
    if hi : i.1 ∈ s then E₁.orient ⟨i.1, hi⟩
    else E₂.orient ⟨i.1, (Finset.mem_union.mp i.2).resolve_left hi⟩
  let copy : ∀ i, i ∈ s ∪ t → (F.tree i).Copy G := fun i hi =>
    if his : i ∈ s then E₁.forestCopy.componentCopy i his
    else E₂.forestCopy.componentCopy i ((Finset.mem_union.mp hi).resolve_left his)
  refine {
    edge := edge
    orient := orient
    forestCopy := { componentCopy := copy, disjoint_ranges := ?_ }
    attach := ?_
    map_side := ?_ }
  · intro i hi j hj hij
    by_cases his : i ∈ s
    · by_cases hjs : j ∈ s
      · simpa only [copy, dif_pos his, dif_pos hjs] using E₁.forestCopy.disjoint_ranges i his j hjs hij
      · simpa only [copy, dif_pos his, dif_neg hjs] using
          disjoint_ranges_of_support E₁ E₂ hsupport i his j ((Finset.mem_union.mp hj).resolve_left hjs)
    · have hit := (Finset.mem_union.mp hi).resolve_left his
      by_cases hjs : j ∈ s
      · simpa only [copy, dif_neg his, dif_pos hjs] using
          (disjoint_ranges_of_support E₁ E₂ hsupport j hjs i hit).symm
      · have hjt := (Finset.mem_union.mp hj).resolve_left hjs
        simpa only [copy, dif_neg his, dif_neg hjs] using E₂.forestCopy.disjoint_ranges i hit j hjt hij
  · intro i hi
    by_cases his : i ∈ s
    · simpa only [copy, dif_pos his] using E₁.attach i his
    · simpa only [copy, dif_neg his] using E₂.attach i ((Finset.mem_union.mp hi).resolve_left his)
  · intro i hi a
    by_cases his : i ∈ s
    · simpa only [copy, edge, orient, dif_pos his] using E₁.map_side i his a
    · simpa only [copy, edge, orient, dif_neg his] using
        E₂.map_side i ((Finset.mem_union.mp hi).resolve_left his) a

theorem BranchPlacement.append_copy_left
    (E₁ : BranchPlacement F G s parent endpoint)
    (E₂ : BranchPlacement F G t parent endpoint)
    (hsupport : ∀ i : {i // i ∈ s}, ∀ j : {j // j ∈ t}, ∀ c d,
      Disjoint (endpoint (E₁.edge i) c) (endpoint (E₂.edge j) d))
    (i : Fin b) (hi : i ∈ s) :
    (E₁.append E₂ hsupport).forestCopy.componentCopy i (Finset.mem_union_left _ hi) =
      E₁.forestCopy.componentCopy i hi := by
  simp only [BranchPlacement.append, dif_pos hi]

theorem BranchPlacement.append_copy_right
    (E₁ : BranchPlacement F G s parent endpoint)
    (E₂ : BranchPlacement F G t parent endpoint)
    (hsupport : ∀ i : {i // i ∈ s}, ∀ j : {j // j ∈ t}, ∀ c d,
      Disjoint (endpoint (E₁.edge i) c) (endpoint (E₂.edge j) d))
    (hst : Disjoint s t) (i : Fin b) (hi : i ∈ t) :
    (E₁.append E₂ hsupport).forestCopy.componentCopy i (Finset.mem_union_right _ hi) =
      E₂.forestCopy.componentCopy i hi := by
  have hnot : i ∉ s := fun his => Finset.disjoint_left.mp hst his hi
  simp only [BranchPlacement.append, dif_neg hnot]

theorem BranchPlacement.append_edge_left
    (E₁ : BranchPlacement F G s parent endpoint)
    (E₂ : BranchPlacement F G t parent endpoint)
    (hsupport : ∀ i : {i // i ∈ s}, ∀ j : {j // j ∈ t}, ∀ c d,
      Disjoint (endpoint (E₁.edge i) c) (endpoint (E₂.edge j) d))
    (i : Fin b) (hi : i ∈ s) :
    (E₁.append E₂ hsupport).edge ⟨i, Finset.mem_union_left _ hi⟩ = E₁.edge ⟨i, hi⟩ := by
  simp only [BranchPlacement.append, dif_pos hi]

theorem BranchPlacement.append_edge_right
    (E₁ : BranchPlacement F G s parent endpoint)
    (E₂ : BranchPlacement F G t parent endpoint)
    (hsupport : ∀ i : {i // i ∈ s}, ∀ j : {j // j ∈ t}, ∀ c d,
      Disjoint (endpoint (E₁.edge i) c) (endpoint (E₂.edge j) d))
    (hst : Disjoint s t) (i : Fin b) (hi : i ∈ t) :
    (E₁.append E₂ hsupport).edge ⟨i, Finset.mem_union_right _ hi⟩ = E₂.edge ⟨i, hi⟩ := by
  have hnot : i ∉ s := fun his => Finset.disjoint_left.mp hst his hi
  simp only [BranchPlacement.append, dif_neg hnot]

def BranchPlacement.used [DecidableEq V] (E : BranchPlacement F G s parent endpoint) : Finset V :=
  Finset.univ.biUnion fun i : {i // i ∈ s} => Finset.univ.image (E.forestCopy.componentCopy i.1 i.2)

theorem BranchPlacement.mem_used [DecidableEq V] (E : BranchPlacement F G s parent endpoint)
    (x : V) : x ∈ E.used ↔ ∃ i hi a, E.forestCopy.componentCopy i hi a = x := by
  simp only [BranchPlacement.used, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨i, hi⟩, a, h⟩
    exact ⟨i, hi, a, h⟩
  · rintro ⟨i, hi, a, h⟩
    exact ⟨⟨i, hi⟩, a, h⟩

theorem BranchPlacement.copy_mem_used [DecidableEq V]
    (E : BranchPlacement F G s parent endpoint) (i : Fin b) (hi : i ∈ s) (a : Fin (F.size i)) :
    E.forestCopy.componentCopy i hi a ∈ E.used :=
  (E.mem_used _).mpr ⟨i, hi, a, rfl⟩

/-- The consumed host-vertex count is exactly the sum of the sizes of
the literal placed branches, not merely a sum of capacity estimates. -/
theorem BranchPlacement.card_used [DecidableEq V]
    (E : BranchPlacement F G s parent endpoint) : E.used.card = ∑ i ∈ s, F.size i := by
  unfold BranchPlacement.used
  rw [Finset.card_biUnion]
  · calc
      (∑ i : {i // i ∈ s}, #(Finset.univ.image (E.forestCopy.componentCopy i.1 i.2))) =
          ∑ i : {i // i ∈ s}, F.size i.1 := by
        apply Finset.sum_congr rfl
        intro i _
        have hc := Finset.card_image_of_injective
          (f := fun a : Fin (F.size i.1) => E.forestCopy.componentCopy i.1 i.2 a)
          Finset.univ (fun a d h => (E.forestCopy.componentCopy i.1 i.2).injective h)
        simpa only [Finset.card_univ, Fintype.card_fin] using hc
      _ = ∑ i ∈ s, F.size i := Finset.sum_attach s F.size
  · intro i _ j _ hij
    change Disjoint (Finset.univ.image (E.forestCopy.componentCopy i.1 i.2))
      (Finset.univ.image (E.forestCopy.componentCopy j.1 j.2))
    rw [Finset.disjoint_left]
    intro x hx hjx
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hjx
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    exact Set.disjoint_left.mp (E.forestCopy.disjoint_ranges i.1 i.2 j.1 j.2 hne)
      ⟨a, ha⟩ ⟨d, hd⟩

theorem BranchPlacement.used_reparent [DecidableEq V]
    (E : BranchPlacement F G s parent endpoint) (parent' : Fin b → V)
    (hagrees : ∀ i ∈ s, parent' i = parent i) :
    (E.reparent parent' hagrees).used = E.used := rfl

theorem BranchPlacement.used_append [DecidableEq V]
    (E₁ : BranchPlacement F G s parent endpoint)
    (E₂ : BranchPlacement F G t parent endpoint)
    (hsupport : ∀ i : {i // i ∈ s}, ∀ j : {j // j ∈ t}, ∀ c d,
      Disjoint (endpoint (E₁.edge i) c) (endpoint (E₂.edge j) d))
    (hst : Disjoint s t) : (E₁.append E₂ hsupport).used = E₁.used ∪ E₂.used := by
  ext x
  rw [BranchPlacement.mem_used, Finset.mem_union, BranchPlacement.mem_used, BranchPlacement.mem_used]
  constructor
  · rintro ⟨i, hi, a, h⟩
    by_cases his : i ∈ s
    · left
      refine ⟨i, his, a, ?_⟩
      rwa [E₁.append_copy_left E₂ hsupport i his] at h
    · have hit := (Finset.mem_union.mp hi).resolve_left his
      right
      refine ⟨i, hit, a, ?_⟩
      rwa [E₁.append_copy_right E₂ hsupport hst i hit] at h
  · rintro (⟨i, hi, a, h⟩ | ⟨i, hi, a, h⟩)
    · refine ⟨i, Finset.mem_union_left _ hi, a, ?_⟩
      rw [E₁.append_copy_left E₂ hsupport i hi]
      exact h
    · refine ⟨i, Finset.mem_union_right _ hi, a, ?_⟩
      rw [E₁.append_copy_right E₂ hsupport hst i hi]
      exact h

end Erdos547b.ZhaoSourceOriginalBranchPlacement

#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.BranchPlacement.empty
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.BranchPlacement.reparent
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.BranchPlacement.append
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.BranchPlacement.append_copy_left
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.BranchPlacement.append_copy_right
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.BranchPlacement.append_edge_left
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.BranchPlacement.append_edge_right
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.BranchPlacement.mem_used
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.BranchPlacement.card_used
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.BranchPlacement.used_reparent
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.BranchPlacement.used_append
