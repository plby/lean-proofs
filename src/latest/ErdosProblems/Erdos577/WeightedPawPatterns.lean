import ErdosProblems.Erdos577.WeightedPawModel
import ErdosProblems.Erdos577.FirstPawPatterns

/-! Exact weighted patterns in the original graph, with an unrestricted center row. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace WeightedPawBlock

def Row (p : Paw G) (q : Quadrilateral G) (i : Fin 4) (mask : ℕ) : Prop :=
  ∀ j : Fin 4, G.Adj (p.vertices i) (q j) ↔ mask.testBit j.val = true

def Pattern9 (p : Paw G) (q : Quadrilateral G) : Prop :=
  degreeIn G (p.vertices 0) q.support = 1 ∧ Row p q 2 14 ∧ Row p q 3 14

def Pattern10 (p : Paw G) (q : Quadrilateral G) : Prop :=
  G.Adj (q 0) (q 2) ∧ G.Adj (q 1) (q 3) ∧
    Row p q 0 15 ∧ Row p q 3 0 ∧
      ∀ j : Fin 4, (14 : ℕ).testBit j.val = true → G.Adj (p.vertices 2) (q j)

def Pattern11 (p : Paw G) (q : Quadrilateral G) : Prop :=
  G.Adj (q 1) (q 3) ∧
    Row p q 0 7 ∧ Row p q 2 15 ∧ Row p q 3 0

def Pattern12 (p : Paw G) (q : Quadrilateral G) : Prop :=
  G.Adj (q 1) (q 3) ∧
    Row p q 0 7 ∧ Row p q 2 7 ∧ Row p q 3 8

def Pattern13 (p : Paw G) (q : Quadrilateral G) : Prop :=
  ¬G.Adj (q 1) (q 3) ∧
    Row p q 0 1 ∧ Row p q 2 13 ∧ Row p q 3 7

def Pattern14 (p : Paw G) (q : Quadrilateral G) : Prop :=
  ¬G.Adj (q 1) (q 3) ∧
    Row p q 0 5 ∧ Row p q 2 13 ∧ Row p q 3 5

def Pattern15 (p : Paw G) (q : Quadrilateral G) : Prop :=
  PawBlock.OnlyFirst q ∧
    Row p q 0 1 ∧ Row p q 2 15 ∧ Row p q 3 6

def Pattern16 (p : Paw G) (q : Quadrilateral G) : Prop :=
  ¬G.Adj (q 1) (q 3) ∧
    Row p q 0 5 ∧ Row p q 2 13 ∧ Row p q 3 7

def Pattern17 (p : Paw G) (q : Quadrilateral G) : Prop :=
  ¬G.Adj (q 1) (q 3) ∧
    Row p q 0 5 ∧ Row p q 2 13 ∧ Row p q 3 3

def Pattern18 (p : Paw G) (q : Quadrilateral G) : Prop :=
  PawBlock.OnlyFirst q ∧
    Row p q 0 3 ∧ Row p q 2 15 ∧ Row p q 3 4

def Pattern19 (p : Paw G) (q : Quadrilateral G) : Prop :=
  ¬G.Adj (q 0) (q 2) ∧ ¬G.Adj (q 1) (q 3) ∧
    Row p q 0 3 ∧ Row p q 2 7 ∧ Row p q 3 9

def Pattern20 (p : Paw G) (q : Quadrilateral G) : Prop :=
  PawBlock.OnlyFirst q ∧
    Row p q 0 3 ∧ Row p q 2 13 ∧ Row p q 3 5

def Classified (p : Paw G) (q : Quadrilateral G) : Prop :=
  ∃ swap : Bool, ∃ q' : Quadrilateral G, q'.support = q.support ∧
    (Pattern9 (FirstPaw.normalizedPaw p swap) q' ∨
      Pattern10 (FirstPaw.normalizedPaw p swap) q' ∨
      Pattern11 (FirstPaw.normalizedPaw p swap) q' ∨
      Pattern12 (FirstPaw.normalizedPaw p swap) q' ∨
      Pattern13 (FirstPaw.normalizedPaw p swap) q' ∨
      Pattern14 (FirstPaw.normalizedPaw p swap) q' ∨
      Pattern15 (FirstPaw.normalizedPaw p swap) q' ∨
      Pattern16 (FirstPaw.normalizedPaw p swap) q' ∨
      Pattern17 (FirstPaw.normalizedPaw p swap) q' ∨
      Pattern18 (FirstPaw.normalizedPaw p swap) q' ∨
      Pattern19 (FirstPaw.normalizedPaw p swap) q' ∨
      Pattern20 (FirstPaw.normalizedPaw p swap) q')

end WeightedPawBlock

namespace WeightedPaw

open FirstPaw

omit [DecidableEq V] in
lemma row_transport_iff (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols) (i : Fin 4) (mask : ℕ) :
    Row (PawEncoding.encoded p q).val swap cols i mask ↔
      WeightedPawBlock.Row (normalizedPaw p swap) (orderedQuad q cols hc) i mask := by
  unfold Row WeightedPawBlock.Row
  apply forall_congr'
  intro j
  rw [bit_encoded p q swap cols hc, Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]

lemma Pattern9.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern9 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    WeightedPawBlock.Pattern9 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  simpa only [Pattern9, WeightedPawBlock.Pattern9,
    rowCount_encoded p q swap cols hc,
    orderedQuad_support,
    row_transport_iff p q swap cols hc] using h

omit [DecidableEq V] in
lemma Pattern10.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern10 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    WeightedPawBlock.Pattern10 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  simpa only [Pattern10, WeightedPawBlock.Pattern10,
    quadAdj_ordered_iff q cols hc,
    row_transport_iff p q swap cols hc,
    bit_true_iff p q swap cols hc] using h

omit [DecidableEq V] in
lemma Pattern11.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern11 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    WeightedPawBlock.Pattern11 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  simpa only [Pattern11, WeightedPawBlock.Pattern11,
    quadAdj_ordered_iff q cols hc,
    row_transport_iff p q swap cols hc] using h

omit [DecidableEq V] in
lemma Pattern12.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern12 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    WeightedPawBlock.Pattern12 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  simpa only [Pattern12, WeightedPawBlock.Pattern12,
    quadAdj_ordered_iff q cols hc,
    row_transport_iff p q swap cols hc] using h

omit [DecidableEq V] in
lemma Pattern13.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern13 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    WeightedPawBlock.Pattern13 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  simpa only [Pattern13, WeightedPawBlock.Pattern13,
    quadAdj_ordered_iff q cols hc,
    row_transport_iff p q swap cols hc] using h

omit [DecidableEq V] in
lemma Pattern14.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern14 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    WeightedPawBlock.Pattern14 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  simpa only [Pattern14, WeightedPawBlock.Pattern14,
    quadAdj_ordered_iff q cols hc,
    row_transport_iff p q swap cols hc] using h

omit [DecidableEq V] in
lemma Pattern15.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern15 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    WeightedPawBlock.Pattern15 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  simpa only [Pattern15, WeightedPawBlock.Pattern15,
    FirstPaw.OnlyFirst,
    PawBlock.OnlyFirst,
    quadAdj_ordered_iff q cols hc,
    row_transport_iff p q swap cols hc] using h

omit [DecidableEq V] in
lemma Pattern16.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern16 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    WeightedPawBlock.Pattern16 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  simpa only [Pattern16, WeightedPawBlock.Pattern16,
    quadAdj_ordered_iff q cols hc,
    row_transport_iff p q swap cols hc] using h

omit [DecidableEq V] in
lemma Pattern17.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern17 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    WeightedPawBlock.Pattern17 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  simpa only [Pattern17, WeightedPawBlock.Pattern17,
    quadAdj_ordered_iff q cols hc,
    row_transport_iff p q swap cols hc] using h

omit [DecidableEq V] in
lemma Pattern18.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern18 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    WeightedPawBlock.Pattern18 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  simpa only [Pattern18, WeightedPawBlock.Pattern18,
    FirstPaw.OnlyFirst,
    PawBlock.OnlyFirst,
    quadAdj_ordered_iff q cols hc,
    row_transport_iff p q swap cols hc] using h

omit [DecidableEq V] in
lemma Pattern19.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern19 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    WeightedPawBlock.Pattern19 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  simpa only [Pattern19, WeightedPawBlock.Pattern19,
    quadAdj_ordered_iff q cols hc,
    row_transport_iff p q swap cols hc] using h

omit [DecidableEq V] in
lemma Pattern20.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern20 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    WeightedPawBlock.Pattern20 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  simpa only [Pattern20, WeightedPawBlock.Pattern20,
    FirstPaw.OnlyFirst,
    PawBlock.OnlyFirst,
    quadAdj_ordered_iff q cols hc,
    row_transport_iff p q swap cols hc] using h

lemma Classified.transport (p : Paw G) (q : Quadrilateral G)
    (h : Classified (Unattached.diagonal q) (PawEncoding.encoded p q).val) :
    WeightedPawBlock.Classified p q := by
  obtain ⟨swap, cols, hc, hpattern⟩ := h
  refine ⟨swap, orderedQuad q cols hc, orderedQuad_support q cols hc, ?_⟩
  rcases hpattern with h | h | h | h | h | h | h | h | h | h | h | h
  · left
    exact h.transport p q swap cols hc
  · right
    left
    exact h.transport p q swap cols hc
  · right
    right
    left
    exact h.transport p q swap cols hc
  · right
    right
    right
    left
    exact h.transport p q swap cols hc
  · right
    right
    right
    right
    left
    exact h.transport p q swap cols hc
  · right
    right
    right
    right
    right
    left
    exact h.transport p q swap cols hc
  · right
    right
    right
    right
    right
    right
    left
    exact h.transport p q swap cols hc
  · right
    right
    right
    right
    right
    right
    right
    left
    exact h.transport p q swap cols hc
  · right
    right
    right
    right
    right
    right
    right
    right
    left
    exact h.transport p q swap cols hc
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    exact h.transport p q swap cols hc
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    exact h.transport p q swap cols hc
  · right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    exact h.transport p q swap cols hc

end WeightedPaw

end Erdos577
