import ErdosProblems.Erdos577.FirstPaw
import ErdosProblems.Erdos577.FirstPawOutside

/-! The complete first paw-block classification, including both outside-vertex factor clauses. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace PawBlock

def OutsideFactor (p : Paw G) (q : Quadrilateral G) : Prop :=
  ∀ z : V, z ∉ p.support ∪ q.support → 2 ≤ degreeIn G z q.support →
    LocalFactor G (insert z (p.triangle ∪ q.support))

def PatternsWithOutside (p : Paw G) (q : Quadrilateral G) : Prop :=
  (Pattern3 p q ∧ OutsideFactor p q) ∨ Pattern4 p q ∨ Pattern5 p q ∨
    Pattern6 p q ∨ Pattern7 p q ∨ (Pattern8 p q ∧ OutsideFactor p q)

def FullClassification (p : Paw G) (q : Quadrilateral G) : Prop :=
  contacts G p.support q.support ≤ 10 ∧ degreeIn G p.leaf q.support ≤ 2 ∧
    ∃ swap : Bool, ∃ q' : Quadrilateral G, q'.support = q.support ∧
      PatternsWithOutside (FirstPaw.normalizedPaw p swap) q'

lemma Classified.with_outside (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Classified p q) : FullClassification p q := by
  obtain ⟨hcount, hleaf, swap, q', hq', hp⟩ := h
  have hd' : Disjoint (FirstPaw.normalizedPaw p swap).support q'.support := by
    rw [FirstPaw.normalizedPaw_support, hq']
    exact hd
  refine ⟨hcount, hleaf, swap, q', hq', ?_⟩
  rcases hp with h | h | h | h | h | h
  · exact Or.inl ⟨h, fun z hz hdegree ↦ h.outside_factor _ _ hd' z hz hdegree⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨h, fun z hz hdegree ↦ h.outside_factor _ _ hd' z hz hdegree⟩))))

end PawBlock

variable [Fintype V]

/-- All six source patterns and the outside factor clauses of Wang 4.3,
with the exact global hypotheses used to exclude a two-edge gain. -/
theorem TriangleChain.Feasible.first_paw_classification {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 9 ≤ contacts G p.support q.support) (hleaf : 0 < degreeIn G p.leaf q.support) :
    PawBlock.FullClassification p q := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    apply disjoint_left.mpr
    intro v hv hvb
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hvb)).2 hv
  exact (hc.first_paw_rows hcard hdeg hn p hp hb q hq hheavy hleaf).with_outside p q hd

end Erdos577
