import ErdosProblems.Erdos577.FirstPawTransport

/-! Source patterns (3)–(8) as exact statements about the original graph. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace PawBlock

def OnlyFirst (q : Quadrilateral G) : Prop := G.Adj (q 0) (q 2) ∧ ¬G.Adj (q 1) (q 3)

def ExactRows (p : Paw G) (q : Quadrilateral G) (rows : Fin 4 → ℕ) : Prop :=
  ∀ i j : Fin 4, G.Adj (p.vertices i) (q j) ↔ (rows i).testBit j.val = true

def Pattern3 (p : Paw G) (q : Quadrilateral G) : Prop :=
  OnlyFirst q ∧ ExactRows p q ![1, 15, 9, 3]

def Pattern4 (p : Paw G) (q : Quadrilateral G) : Prop :=
  G.Adj (q 0) (q 2) ∧ 3 ≤ degreeIn G p.center q.support ∧
    degreeIn G p.center q.support ≤ 4 ∧ ∀ j : Fin 4,
      G.Adj (p.vertices 0) (q j) ∨ G.Adj (p.vertices 2) (q j) ∨ G.Adj (p.vertices 3) (q j) →
        j = 0 ∨ j = 2

def Pattern5 (p : Paw G) (q : Quadrilateral G) : Prop :=
  OnlyFirst q ∧
    (∀ j : Fin 4, G.Adj (p.vertices 0) (q j) ∨ G.Adj (p.vertices 1) (q j) → j = 0 ∨ j = 2) ∧
    (∀ j : Fin 4, G.Adj (p.vertices 2) (q j) → j ≠ 1) ∧
    (∀ j : Fin 4, G.Adj (p.vertices 3) (q j) → j ≠ 3)

def Pattern6 (p : Paw G) (q : Quadrilateral G) : Prop :=
  OnlyFirst q ∧
    (∀ j : Fin 4, G.Adj (p.vertices 0) (q j) → j = 0 ∨ j = 1) ∧
    (∀ j : Fin 4, G.Adj (p.vertices 2) (q j) → j ≠ 3) ∧
    (∀ j : Fin 4, G.Adj (p.vertices 3) (q j) → j = 0)

def Pattern7 (p : Paw G) (q : Quadrilateral G) : Prop :=
  OnlyFirst q ∧ ExactRows p q ![1, 7, 7, 5]

def Pattern8 (p : Paw G) (q : Quadrilateral G) : Prop :=
  G.Adj (q 0) (q 2) ∧ ExactRows p q ![1, 15, 15, 0]

/-- The exact row classification; the outside-vertex factor consequences
of patterns (3) and (8) are separate positive constructions. -/
def Classified (p : Paw G) (q : Quadrilateral G) : Prop :=
  contacts G p.support q.support ≤ 10 ∧ degreeIn G p.leaf q.support ≤ 2 ∧
    ∃ swap : Bool, ∃ q' : Quadrilateral G, q'.support = q.support ∧
      (Pattern3 (FirstPaw.normalizedPaw p swap) q' ∨
        Pattern4 (FirstPaw.normalizedPaw p swap) q' ∨
        Pattern5 (FirstPaw.normalizedPaw p swap) q' ∨
        Pattern6 (FirstPaw.normalizedPaw p swap) q' ∨
        Pattern7 (FirstPaw.normalizedPaw p swap) q' ∨
        Pattern8 (FirstPaw.normalizedPaw p swap) q')

end PawBlock

namespace FirstPaw

omit [DecidableEq V] in
lemma bit_true_iff (p : Paw G) (q : Quadrilateral G) (swap : Bool) (cols : Fin 4 ↪ Fin 4)
    (hc : CycleOrder (Unattached.diagonal q) cols) (i j : Fin 4) :
    bit (PawEncoding.encoded p q).val swap cols i j = true ↔
      G.Adj ((normalizedPaw p swap).vertices i) (orderedQuad q cols hc j) := by
  rw [bit_encoded p q swap cols hc]
  exact ⟨of_decide_eq_true, decide_eq_true⟩

omit [DecidableEq V] in
lemma Pattern3.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern3 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    PawBlock.Pattern3 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  obtain ⟨hd, hr⟩ := h
  exact ⟨hd.transport q cols hc, fun i j ↦ hr.transport p q swap cols hc _ i j⟩

lemma Pattern4.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern4 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    PawBlock.Pattern4 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  obtain ⟨hd, hr, hrows⟩ := h
  refine ⟨(quadAdj_ordered_iff q cols hc 0 2).mp hd, ?_, ?_, ?_⟩
  · rw [rowCount_encoded p q swap cols hc] at hr
    change 3 ≤ degreeIn G ((normalizedPaw p swap).vertices 1) (orderedQuad q cols hc).support
    simpa only [orderedQuad_support] using hr
  · have hbound := degreeIn_le_card G (normalizedPaw p swap).center (orderedQuad q cols hc).support
    simpa only [Quadrilateral.card_support] using hbound
  · simpa only [bit_true_iff p q swap cols hc] using hrows

omit [DecidableEq V] in
lemma Pattern5.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern5 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    PawBlock.Pattern5 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  obtain ⟨hd, h01, h2, h3⟩ := h
  refine ⟨hd.transport q cols hc, ?_, ?_, ?_⟩
  · simpa only [bit_true_iff p q swap cols hc] using h01
  · simpa only [bit_true_iff p q swap cols hc] using h2
  · simpa only [bit_true_iff p q swap cols hc] using h3

omit [DecidableEq V] in
lemma Pattern6.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern6 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    PawBlock.Pattern6 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  obtain ⟨hd, h0, h2, h3⟩ := h
  refine ⟨hd.transport q cols hc, ?_, ?_, ?_⟩
  · simpa only [bit_true_iff p q swap cols hc] using h0
  · simpa only [bit_true_iff p q swap cols hc] using h2
  · simpa only [bit_true_iff p q swap cols hc] using h3

omit [DecidableEq V] in
lemma Pattern7.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern7 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    PawBlock.Pattern7 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  obtain ⟨hd, hr⟩ := h
  exact ⟨hd.transport q cols hc, fun i j ↦ hr.transport p q swap cols hc _ i j⟩

omit [DecidableEq V] in
lemma Pattern8.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern8 (Unattached.diagonal q) (PawEncoding.encoded p q).val swap cols) :
    PawBlock.Pattern8 (normalizedPaw p swap) (orderedQuad q cols hc) := by
  obtain ⟨hd, hr⟩ := h
  exact ⟨(quadAdj_ordered_iff q cols hc 0 2).mp hd,
    fun i j ↦ hr.transport p q swap cols hc _ i j⟩

lemma Classified.transport (p : Paw G) (q : Quadrilateral G)
    (h : Classified (Unattached.diagonal q) (PawEncoding.encoded p q).val) :
    PawBlock.Classified p q := by
  obtain ⟨hcount, hleaf, swap, cols, hc, hpattern⟩ := h
  rw [PawEncoding.crossCount_encoded] at hcount
  rw [PawEncoding.terminalCount_encoded] at hleaf
  refine ⟨hcount, hleaf, swap, orderedQuad q cols hc, orderedQuad_support q cols hc, ?_⟩
  rcases hpattern with h | h | h | h | h | h
  · exact Or.inl (h.transport p q swap cols hc)
  · exact Or.inr (Or.inl (h.transport p q swap cols hc))
  · exact Or.inr (Or.inr (Or.inl (h.transport p q swap cols hc)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h.transport p q swap cols hc))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h.transport p q swap cols hc)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.transport p q swap cols hc)))))

end FirstPaw

end Erdos577
