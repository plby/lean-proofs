import ErdosProblems.Erdos577.WeightedPawClassification
import ErdosProblems.Erdos577.WeightedAdjacentExcluded
import ErdosProblems.Erdos577.WeightedOppositeExcluded
import ErdosProblems.Erdos577.WeightedNineteenExcluded
import ErdosProblems.Erdos577.WeightedFifteenExcluded

/-! Wang's six remaining weighted patterns, with every replacement clause. -/

namespace Erdos577

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace WeightedPawBlock

def SixPatternsWithReplacements (p : Paw G) (q : Quadrilateral G) : Prop :=
  Pattern9 p q ∨
    (Pattern10 p q ∧ ReplacementClauses p q) ∨
    (Pattern11 p q ∧ ReplacementClauses p q) ∨
    (Pattern12 p q ∧ ReplacementClauses p q) ∨
    Pattern13 p q ∨ Pattern14 p q

def FinalClassification (p : Paw G) (q : Quadrilateral G) : Prop :=
  ∃ swap : Bool, ∃ q' : Quadrilateral G, q'.support = q.support ∧
    SixPatternsWithReplacements (FirstPaw.normalizedPaw p swap) q'

end WeightedPawBlock

variable [Fintype V]

theorem TriangleChain.Feasible.weighted_paw_classification {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support) (hleaf : 0 < degreeIn G p.leaf q.support) :
    WeightedPawBlock.FinalClassification p q := by
  obtain ⟨swap, q', hq', hpatt⟩ := hc.weighted_paw_initial hcard hdeg hn p hp hb q hq hheavy hleaf
  have hp' : (FirstPaw.normalizedPaw p swap).support = c.remainder := by
    rw [FirstPaw.normalizedPaw_support, hp]
  have hqb : q'.support = b := hq'.trans hq
  refine ⟨swap, q', hq', ?_⟩
  rcases hpatt with h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact False.elim (hc.not_weighted_pattern15 hcard hdeg hn _ hp' hb q' hqb h)
  · exact False.elim (hc.not_weighted_pattern16 hcard hdeg hn _ hp' hb q' hqb h)
  · exact False.elim (hc.not_weighted_pattern17 hcard hdeg hn _ hp' hb q' hqb h)
  · exact False.elim (hc.not_weighted_pattern18 hcard hdeg hn _ hp' hb q' hqb h)
  · exact False.elim (hc.not_weighted_pattern19 hcard hdeg hn _ hp' hb q' hqb h)
  · exact False.elim (hc.not_weighted_pattern20 hcard hdeg hn _ hp' hb q' hqb h)

end Erdos577
