import ErdosProblems.Erdos118.Imported591.InterlacingGraph
import Mathlib.Tactic.FinCases

/-!
# Finite audit of the abstract tagged interlacing graph

The graph-defining records come from this task's isolated snapshot of
`Erdos591/InterlacingGraph.lean`; the active shared task is not edited.
The ten explicit witnesses prove that the abstract K6-free graph contains
a K5. The vertices are arbitrary tagged words, not literal good sequences.
This is an audit of a tempting sharpening, not the ordinal counterexample.
The search that found the data is not used in any proof.
-/

namespace Erdos118.InterlacingAudit

open Erdos118.Negative

instance (s t : List TaggedCoord) : Decidable (AllLT s t) := by
  unfold AllLT
  infer_instance

instance (s : List TaggedCoord) : Decidable (HasBox s) := by
  unfold HasBox
  infer_instance

instance (s : List TaggedCoord) : Decidable (NoBox s) := by
  unfold NoBox
  infer_instance

def v0 : List TaggedCoord :=
  [⟨0, true⟩, ⟨3, false⟩, ⟨5, false⟩, ⟨6, false⟩, ⟨7, false⟩,
    ⟨14, false⟩, ⟨19, true⟩, ⟨25, false⟩, ⟨44, true⟩]

def v1 : List TaggedCoord :=
  [⟨1, true⟩, ⟨16, false⟩, ⟨24, false⟩, ⟨26, true⟩, ⟨28, false⟩,
    ⟨31, false⟩, ⟨41, true⟩, ⟨42, true⟩, ⟨43, true⟩]

def v2 : List TaggedCoord :=
  [⟨2, true⟩, ⟨4, false⟩, ⟨22, false⟩, ⟨30, false⟩, ⟨32, true⟩,
    ⟨33, true⟩, ⟨35, false⟩, ⟨38, false⟩, ⟨40, true⟩]

def v3 : List TaggedCoord :=
  [⟨8, true⟩, ⟨10, false⟩, ⟨13, true⟩, ⟨15, false⟩, ⟨17, false⟩,
    ⟨23, false⟩, ⟨27, false⟩, ⟨37, false⟩, ⟨39, true⟩]

def v4 : List TaggedCoord :=
  [⟨9, true⟩, ⟨11, false⟩, ⟨12, false⟩, ⟨18, false⟩, ⟨20, false⟩,
    ⟨21, false⟩, ⟨29, false⟩, ⟨34, false⟩, ⟨36, true⟩]

def vertices (i : Fin 5) : List TaggedCoord :=
  match i.val with
  | 0 => v0
  | 1 => v1
  | 2 => v2
  | 3 => v3
  | _ => v4

def w01 : InterlacingWitness v0 v1 where
  X := {
    p0 := [⟨0, true⟩]
    p1 := [⟨3, false⟩, ⟨5, false⟩, ⟨6, false⟩, ⟨7, false⟩, ⟨14, false⟩]
    p2 := [⟨19, true⟩]
    p3 := [⟨25, false⟩]
    p4 := [⟨44, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide
    ne4 := by decide }
  Y := {
    p0 := [⟨1, true⟩]
    p1 := [⟨16, false⟩]
    p2 := [⟨24, false⟩]
    p3 := [⟨26, true⟩, ⟨28, false⟩, ⟨31, false⟩, ⟨41, true⟩, ⟨42, true⟩, ⟨43, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide }
  x0_y0 := by decide
  y0_x1 := by decide
  x1_y1 := by decide
  y1_x2 := by decide
  x2_y2 := by decide
  y2_x3 := by decide
  x3_y3 := by decide
  y3_x4 := by decide
  box_x0 := by decide
  box_x2 := by decide
  box_x4 := by decide
  box_y0 := by decide
  box_y3 := by decide
  noBox_x1 := by decide
  noBox_x3 := by decide
  noBox_y1 := by decide
  noBox_y2 := by decide

def w02 : InterlacingWitness v0 v2 where
  X := {
    p0 := [⟨0, true⟩]
    p1 := [⟨3, false⟩]
    p2 := [⟨5, false⟩, ⟨6, false⟩, ⟨7, false⟩, ⟨14, false⟩, ⟨19, true⟩]
    p3 := [⟨25, false⟩]
    p4 := [⟨44, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide
    ne4 := by decide }
  Y := {
    p0 := [⟨2, true⟩]
    p1 := [⟨4, false⟩]
    p2 := [⟨22, false⟩]
    p3 := [⟨30, false⟩, ⟨32, true⟩, ⟨33, true⟩, ⟨35, false⟩, ⟨38, false⟩, ⟨40, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide }
  x0_y0 := by decide
  y0_x1 := by decide
  x1_y1 := by decide
  y1_x2 := by decide
  x2_y2 := by decide
  y2_x3 := by decide
  x3_y3 := by decide
  y3_x4 := by decide
  box_x0 := by decide
  box_x2 := by decide
  box_x4 := by decide
  box_y0 := by decide
  box_y3 := by decide
  noBox_x1 := by decide
  noBox_x3 := by decide
  noBox_y1 := by decide
  noBox_y2 := by decide

def w03 : InterlacingWitness v0 v3 where
  X := {
    p0 := [⟨0, true⟩, ⟨3, false⟩, ⟨5, false⟩, ⟨6, false⟩, ⟨7, false⟩]
    p1 := [⟨14, false⟩]
    p2 := [⟨19, true⟩]
    p3 := [⟨25, false⟩]
    p4 := [⟨44, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide
    ne4 := by decide }
  Y := {
    p0 := [⟨8, true⟩, ⟨10, false⟩, ⟨13, true⟩]
    p1 := [⟨15, false⟩, ⟨17, false⟩]
    p2 := [⟨23, false⟩]
    p3 := [⟨27, false⟩, ⟨37, false⟩, ⟨39, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide }
  x0_y0 := by decide
  y0_x1 := by decide
  x1_y1 := by decide
  y1_x2 := by decide
  x2_y2 := by decide
  y2_x3 := by decide
  x3_y3 := by decide
  y3_x4 := by decide
  box_x0 := by decide
  box_x2 := by decide
  box_x4 := by decide
  box_y0 := by decide
  box_y3 := by decide
  noBox_x1 := by decide
  noBox_x3 := by decide
  noBox_y1 := by decide
  noBox_y2 := by decide

def w04 : InterlacingWitness v0 v4 where
  X := {
    p0 := [⟨0, true⟩, ⟨3, false⟩, ⟨5, false⟩, ⟨6, false⟩, ⟨7, false⟩]
    p1 := [⟨14, false⟩]
    p2 := [⟨19, true⟩]
    p3 := [⟨25, false⟩]
    p4 := [⟨44, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide
    ne4 := by decide }
  Y := {
    p0 := [⟨9, true⟩, ⟨11, false⟩, ⟨12, false⟩]
    p1 := [⟨18, false⟩]
    p2 := [⟨20, false⟩, ⟨21, false⟩]
    p3 := [⟨29, false⟩, ⟨34, false⟩, ⟨36, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide }
  x0_y0 := by decide
  y0_x1 := by decide
  x1_y1 := by decide
  y1_x2 := by decide
  x2_y2 := by decide
  y2_x3 := by decide
  x3_y3 := by decide
  y3_x4 := by decide
  box_x0 := by decide
  box_x2 := by decide
  box_x4 := by decide
  box_y0 := by decide
  box_y3 := by decide
  noBox_x1 := by decide
  noBox_x3 := by decide
  noBox_y1 := by decide
  noBox_y2 := by decide

def w12 : InterlacingWitness v1 v2 where
  X := {
    p0 := [⟨1, true⟩]
    p1 := [⟨16, false⟩]
    p2 := [⟨24, false⟩, ⟨26, true⟩, ⟨28, false⟩]
    p3 := [⟨31, false⟩]
    p4 := [⟨41, true⟩, ⟨42, true⟩, ⟨43, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide
    ne4 := by decide }
  Y := {
    p0 := [⟨2, true⟩, ⟨4, false⟩]
    p1 := [⟨22, false⟩]
    p2 := [⟨30, false⟩]
    p3 := [⟨32, true⟩, ⟨33, true⟩, ⟨35, false⟩, ⟨38, false⟩, ⟨40, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide }
  x0_y0 := by decide
  y0_x1 := by decide
  x1_y1 := by decide
  y1_x2 := by decide
  x2_y2 := by decide
  y2_x3 := by decide
  x3_y3 := by decide
  y3_x4 := by decide
  box_x0 := by decide
  box_x2 := by decide
  box_x4 := by decide
  box_y0 := by decide
  box_y3 := by decide
  noBox_x1 := by decide
  noBox_x3 := by decide
  noBox_y1 := by decide
  noBox_y2 := by decide

def w13 : InterlacingWitness v1 v3 where
  X := {
    p0 := [⟨1, true⟩]
    p1 := [⟨16, false⟩]
    p2 := [⟨24, false⟩, ⟨26, true⟩]
    p3 := [⟨28, false⟩, ⟨31, false⟩]
    p4 := [⟨41, true⟩, ⟨42, true⟩, ⟨43, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide
    ne4 := by decide }
  Y := {
    p0 := [⟨8, true⟩, ⟨10, false⟩, ⟨13, true⟩, ⟨15, false⟩]
    p1 := [⟨17, false⟩, ⟨23, false⟩]
    p2 := [⟨27, false⟩]
    p3 := [⟨37, false⟩, ⟨39, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide }
  x0_y0 := by decide
  y0_x1 := by decide
  x1_y1 := by decide
  y1_x2 := by decide
  x2_y2 := by decide
  y2_x3 := by decide
  x3_y3 := by decide
  y3_x4 := by decide
  box_x0 := by decide
  box_x2 := by decide
  box_x4 := by decide
  box_y0 := by decide
  box_y3 := by decide
  noBox_x1 := by decide
  noBox_x3 := by decide
  noBox_y1 := by decide
  noBox_y2 := by decide

def w14 : InterlacingWitness v1 v4 where
  X := {
    p0 := [⟨1, true⟩]
    p1 := [⟨16, false⟩]
    p2 := [⟨24, false⟩, ⟨26, true⟩, ⟨28, false⟩]
    p3 := [⟨31, false⟩]
    p4 := [⟨41, true⟩, ⟨42, true⟩, ⟨43, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide
    ne4 := by decide }
  Y := {
    p0 := [⟨9, true⟩, ⟨11, false⟩, ⟨12, false⟩]
    p1 := [⟨18, false⟩, ⟨20, false⟩, ⟨21, false⟩]
    p2 := [⟨29, false⟩]
    p3 := [⟨34, false⟩, ⟨36, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide }
  x0_y0 := by decide
  y0_x1 := by decide
  x1_y1 := by decide
  y1_x2 := by decide
  x2_y2 := by decide
  y2_x3 := by decide
  x3_y3 := by decide
  y3_x4 := by decide
  box_x0 := by decide
  box_x2 := by decide
  box_x4 := by decide
  box_y0 := by decide
  box_y3 := by decide
  noBox_x1 := by decide
  noBox_x3 := by decide
  noBox_y1 := by decide
  noBox_y2 := by decide

def w23 : InterlacingWitness v2 v3 where
  X := {
    p0 := [⟨2, true⟩, ⟨4, false⟩]
    p1 := [⟨22, false⟩]
    p2 := [⟨30, false⟩, ⟨32, true⟩, ⟨33, true⟩, ⟨35, false⟩]
    p3 := [⟨38, false⟩]
    p4 := [⟨40, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide
    ne4 := by decide }
  Y := {
    p0 := [⟨8, true⟩, ⟨10, false⟩, ⟨13, true⟩, ⟨15, false⟩, ⟨17, false⟩]
    p1 := [⟨23, false⟩, ⟨27, false⟩]
    p2 := [⟨37, false⟩]
    p3 := [⟨39, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide }
  x0_y0 := by decide
  y0_x1 := by decide
  x1_y1 := by decide
  y1_x2 := by decide
  x2_y2 := by decide
  y2_x3 := by decide
  x3_y3 := by decide
  y3_x4 := by decide
  box_x0 := by decide
  box_x2 := by decide
  box_x4 := by decide
  box_y0 := by decide
  box_y3 := by decide
  noBox_x1 := by decide
  noBox_x3 := by decide
  noBox_y1 := by decide
  noBox_y2 := by decide

def w24 : InterlacingWitness v2 v4 where
  X := {
    p0 := [⟨2, true⟩, ⟨4, false⟩]
    p1 := [⟨22, false⟩]
    p2 := [⟨30, false⟩, ⟨32, true⟩, ⟨33, true⟩]
    p3 := [⟨35, false⟩]
    p4 := [⟨38, false⟩, ⟨40, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide
    ne4 := by decide }
  Y := {
    p0 := [⟨9, true⟩, ⟨11, false⟩, ⟨12, false⟩, ⟨18, false⟩, ⟨20, false⟩, ⟨21, false⟩]
    p1 := [⟨29, false⟩]
    p2 := [⟨34, false⟩]
    p3 := [⟨36, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide }
  x0_y0 := by decide
  y0_x1 := by decide
  x1_y1 := by decide
  y1_x2 := by decide
  x2_y2 := by decide
  y2_x3 := by decide
  x3_y3 := by decide
  y3_x4 := by decide
  box_x0 := by decide
  box_x2 := by decide
  box_x4 := by decide
  box_y0 := by decide
  box_y3 := by decide
  noBox_x1 := by decide
  noBox_x3 := by decide
  noBox_y1 := by decide
  noBox_y2 := by decide

def w34 : InterlacingWitness v3 v4 where
  X := {
    p0 := [⟨8, true⟩]
    p1 := [⟨10, false⟩]
    p2 := [⟨13, true⟩, ⟨15, false⟩, ⟨17, false⟩]
    p3 := [⟨23, false⟩, ⟨27, false⟩]
    p4 := [⟨37, false⟩, ⟨39, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide
    ne4 := by decide }
  Y := {
    p0 := [⟨9, true⟩]
    p1 := [⟨11, false⟩, ⟨12, false⟩]
    p2 := [⟨18, false⟩, ⟨20, false⟩, ⟨21, false⟩]
    p3 := [⟨29, false⟩, ⟨34, false⟩, ⟨36, true⟩]
    eq_append := rfl
    ne0 := by decide
    ne1 := by decide
    ne2 := by decide
    ne3 := by decide }
  x0_y0 := by decide
  y0_x1 := by decide
  x1_y1 := by decide
  y1_x2 := by decide
  x2_y2 := by decide
  y2_x3 := by decide
  x3_y3 := by decide
  y3_x4 := by decide
  box_x0 := by decide
  box_x2 := by decide
  box_x4 := by decide
  box_y0 := by decide
  box_y3 := by decide
  noBox_x1 := by decide
  noBox_x3 := by decide
  noBox_y1 := by decide
  noBox_y2 := by decide

theorem all_increasing :
    ∀ i : Fin 5, ((vertices i).map TaggedCoord.value).Pairwise (· < ·) := by
  decide

theorem all_ordered_pairs (i j : Fin 5) (hij : i < j) :
    Interlaces (vertices i) (vertices j) := by
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals first
  | exact ⟨w01⟩
  | exact ⟨w02⟩
  | exact ⟨w03⟩
  | exact ⟨w04⟩
  | exact ⟨w12⟩
  | exact ⟨w13⟩
  | exact ⟨w14⟩
  | exact ⟨w23⟩
  | exact ⟨w24⟩
  | exact ⟨w34⟩

theorem five_clique : (interlacingGraph vertices).IsNClique 5 Finset.univ := by
  refine ⟨?_, by simp⟩
  intro i _ j _ hij
  apply (SimpleGraph.fromRel_adj _ _ _).mpr
  refine ⟨hij, ?_⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact Or.inl (all_ordered_pairs i j hlt)
  · exact Or.inr (all_ordered_pairs j i hgt)

theorem not_cliqueFree_five : ¬ (interlacingGraph vertices).CliqueFree 5 :=
  five_clique.not_cliqueFree

end Erdos118.InterlacingAudit
