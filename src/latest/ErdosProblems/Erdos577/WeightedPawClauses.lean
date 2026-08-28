import ErdosProblems.Erdos577.WeightedPawReplacements
import ErdosProblems.Erdos577.PawCommonFactor

/-! All replacement clauses and the initial twelve-pattern conclusion, before global exclusions. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace WeightedPawBlock

def ReplacementClauses (p : Paw G) (q : Quadrilateral G) : Prop :=
  (∀ u ∈ q.support, QuadOn G (insert (p.vertices 2) (q.support.erase u))) ∧
    ∀ z : V, z ∉ p.support ∪ q.support → 2 ≤ degreeIn G z q.support →
      CommonReplacement G p.leaf (p.vertices 2) z q.support ∧
        LocalFactor G (insert z ({p.vertices 0, p.vertices 1, p.vertices 2} ∪ q.support))

lemma Pattern10.replacement_clauses (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Pattern10 p q) : ReplacementClauses p q := by
  refine ⟨h.universal p q hd, ?_⟩
  intro z hz hdegree
  have hcommon := h.common_replacement p q z (fun he ↦ hz (mem_union_right _ he)) hdegree
  exact ⟨hcommon, p.common_replacement_factor q hd z hz hcommon⟩

lemma Pattern11.replacement_clauses (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Pattern11 p q) : ReplacementClauses p q := by
  refine ⟨h.universal p q hd, ?_⟩
  intro z hz hdegree
  have hcommon := h.common_replacement p q z (fun he ↦ hz (mem_union_right _ he)) hdegree
  exact ⟨hcommon, p.common_replacement_factor q hd z hz hcommon⟩

lemma Pattern12.replacement_clauses (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Pattern12 p q) : ReplacementClauses p q := by
  refine ⟨h.universal p q hd, ?_⟩
  intro z hz hdegree
  have hcommon := h.common_replacement p q z (fun he ↦ hz (mem_union_right _ he)) hdegree
  exact ⟨hcommon, p.common_replacement_factor q hd z hz hcommon⟩

def PatternsWithReplacements (p : Paw G) (q : Quadrilateral G) : Prop :=
  Pattern9 p q ∨
    (Pattern10 p q ∧ ReplacementClauses p q) ∨
    (Pattern11 p q ∧ ReplacementClauses p q) ∨
    (Pattern12 p q ∧ ReplacementClauses p q) ∨
    Pattern13 p q ∨
    Pattern14 p q ∨
    Pattern15 p q ∨
    Pattern16 p q ∨
    Pattern17 p q ∨
    Pattern18 p q ∨
    Pattern19 p q ∨
    Pattern20 p q

def FullClassification (p : Paw G) (q : Quadrilateral G) : Prop :=
  ∃ swap : Bool, ∃ q' : Quadrilateral G, q'.support = q.support ∧
    PatternsWithReplacements (FirstPaw.normalizedPaw p swap) q'

lemma Classified.with_replacements (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Classified p q) : FullClassification p q := by
  obtain ⟨swap, q', hq', hp⟩ := h
  have hd' : Disjoint (FirstPaw.normalizedPaw p swap).support q'.support := by
    rw [FirstPaw.normalizedPaw_support, hq']
    exact hd
  refine ⟨swap, q', hq', ?_⟩
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h
  · left
    exact h
  · right
    left
    exact ⟨h, h.replacement_clauses _ _ hd'⟩
  · right
    right
    left
    exact ⟨h, h.replacement_clauses _ _ hd'⟩
  · right
    right
    right
    left
    exact ⟨h, h.replacement_clauses _ _ hd'⟩
  · right
    right
    right
    right
    left
    exact h
  · right
    right
    right
    right
    right
    left
    exact h
  · right
    right
    right
    right
    right
    right
    left
    exact h
  · right
    right
    right
    right
    right
    right
    right
    left
    exact h
  · right
    right
    right
    right
    right
    right
    right
    right
    left
    exact h
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
    exact h
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
    exact h
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
    exact h

end WeightedPawBlock

end Erdos577
