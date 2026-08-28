import ErdosProblems.Erdos577.PathClassTransport

/-! The two path-block patterns and all their replacement assertions in the actual graph. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace PathBlock

def PatternA (p : FourPath G) (q : Quadrilateral G) : Prop :=
  (∀ j : Fin 4, G.Adj (p.vertices 0) (q j) ∨ G.Adj (p.vertices 2) (q j) → j ≠ 3) ∧
    3 ≤ degreeIn G (p.vertices 1) q.support ∧ degreeIn G (p.vertices 1) q.support ≤ 4 ∧
    degreeIn G (p.vertices 3) q.support = 0

def PatternB (p : FourPath G) (q : Quadrilateral G) : Prop :=
  (∀ j : Fin 4, G.Adj (p.vertices 0) (q j) ∨ G.Adj (p.vertices 3) (q j) → j = 0 ∨ j = 1) ∧
    ∀ j : Fin 4, G.Adj (p.vertices 1) (q j) ∨ G.Adj (p.vertices 2) (q j) → j ≠ 3

def CommonA (p : FourPath G) (q : Quadrilateral G) : Prop :=
  ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l →
    CommonReplacement G (p.vertices (Fin.castAdd 1 j)) (p.vertices (Fin.castAdd 1 l))
      (p.vertices (Fin.castAdd 1 i)) q.support

def CommonB (p : FourPath G) (q : Quadrilateral G) : Prop :=
  ∃ i : Fin 4, (i = 1 ∨ i = 2) ∧ degreeIn G (p.vertices i) q.support = 3 ∧
    ∀ j l : Fin 4, j ≠ i → l ≠ i → j ≠ l →
      CommonReplacement G (p.vertices j) (p.vertices l) (p.vertices i) q.support

def Classified (p : FourPath G) (q : Quadrilateral G) : Prop :=
  contacts G p.support q.support ≤ 10 ∧ ∃ reverse : Bool, ∃ q' : Quadrilateral G,
    q'.support = q.support ∧
      ((PatternA (PathClass.normalizedPath p reverse) q' ∧
        CommonA (PathClass.normalizedPath p reverse) q') ∨
       (PatternB (PathClass.normalizedPath p reverse) q' ∧
        CommonB (PathClass.normalizedPath p reverse) q'))

end PathBlock

namespace PathClass

lemma PatternA.transport (p : FourPath G) (q : Quadrilateral G) (hq : G.IsNClique 4 q.support)
    (reverse : Bool) (cols : Fin 4 ↪ Fin 4)
    (h : PatternA (PathExchange.encoded p q).val reverse cols) :
    PathBlock.PatternA (normalizedPath p reverse) (q.relabelOfClique hq cols) := by
  obtain ⟨hrows, hhigh, hzero⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    apply hrows j
    rcases hj with hj | hj
    · left
      rw [bit_encoded p q hq]
      exact decide_eq_true hj
    · right
      rw [bit_encoded p q hq]
      exact decide_eq_true hj
  · rw [rowCount_encoded p q hq] at hhigh
    simpa only [Quadrilateral.relabelOfClique_support] using hhigh
  · have hbound := degreeIn_le_card G ((normalizedPath p reverse).vertices 1)
      (q.relabelOfClique hq cols).support
    simpa only [Quadrilateral.card_support] using hbound
  · rw [rowCount_encoded p q hq] at hzero
    simpa only [Quadrilateral.relabelOfClique_support] using hzero

lemma PatternB.transport (p : FourPath G) (q : Quadrilateral G) (hq : G.IsNClique 4 q.support)
    (reverse : Bool) (cols : Fin 4 ↪ Fin 4)
    (h : PatternB (PathExchange.encoded p q).val reverse cols) :
    PathBlock.PatternB (normalizedPath p reverse) (q.relabelOfClique hq cols) := by
  obtain ⟨hend, hmiddle⟩ := h
  constructor
  · intro j hj
    apply hend j
    rcases hj with hj | hj
    · left
      rw [bit_encoded p q hq]
      exact decide_eq_true hj
    · right
      rw [bit_encoded p q hq]
      exact decide_eq_true hj
  · intro j hj
    apply hmiddle j
    rcases hj with hj | hj
    · left
      rw [bit_encoded p q hq]
      exact decide_eq_true hj
    · right
      rw [bit_encoded p q hq]
      exact decide_eq_true hj

lemma CommonA.transport (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hq : G.IsNClique 4 q.support)
    (reverse : Bool) (cols : Fin 4 ↪ Fin 4)
    (h : CommonA (PathExchange.encoded p q).val reverse cols) :
    PathBlock.CommonA (normalizedPath p reverse) (q.relabelOfClique hq cols) := by
  intro i j l hij hil hjl
  have hr := (h i j l hij hil hjl).transport p q hd hq reverse cols
    (Fin.castAdd 1 i) (Fin.castAdd 1 j) (Fin.castAdd 1 l)
  simpa only [Quadrilateral.relabelOfClique_support] using hr

lemma CommonB.transport (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hq : G.IsNClique 4 q.support)
    (reverse : Bool) (cols : Fin 4 ↪ Fin 4)
    (h : CommonB (PathExchange.encoded p q).val reverse cols) :
    PathBlock.CommonB (normalizedPath p reverse) (q.relabelOfClique hq cols) := by
  obtain ⟨i, hi, hrow, hcommon⟩ := h
  refine ⟨i, hi, ?_, ?_⟩
  · rw [rowCount_encoded p q hq] at hrow
    simpa only [Quadrilateral.relabelOfClique_support] using hrow
  · intro j l hji hli hjl
    have hr := (hcommon j l hji hli hjl).transport p q hd hq reverse cols i j l
    simpa only [Quadrilateral.relabelOfClique_support] using hr

lemma Classified.transport (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hq : G.IsNClique 4 q.support)
    (h : Classified (PathExchange.encoded p q).val) : PathBlock.Classified p q := by
  obtain ⟨hcount, reverse, cols, hpattern⟩ := h
  rw [PathExchange.crossCount_encoded] at hcount
  refine ⟨hcount, reverse, q.relabelOfClique hq cols, q.relabelOfClique_support hq cols, ?_⟩
  rcases hpattern with ⟨ha, hc⟩ | ⟨hb, hc⟩
  · exact Or.inl ⟨ha.transport p q hq reverse cols, hc.transport p q hd hq reverse cols⟩
  · exact Or.inr ⟨hb.transport p q hq reverse cols, hc.transport p q hd hq reverse cols⟩

end PathClass

end Erdos577
