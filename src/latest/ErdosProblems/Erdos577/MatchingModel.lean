import ErdosProblems.Erdos577.MatchingData

/-! Positive local outcomes for two disjoint edges beside a quadrilateral. -/

namespace Erdos577.MatchingExchange

open Finset

def basePairs : Finset (Fin 8 × Fin 8) :=
  {(0, 1), (2, 3), (4, 5), (5, 6), (6, 7), (4, 7)}

def relation (m : ℕ) (a b : Fin 8) : Prop :=
  (a, b) ∈ basePairs ∨ (a.val < 4 ∧ 4 ≤ b.val ∧ m.testBit (4 * a.val + b.val - 4) = true)

instance (m : ℕ) : DecidableRel (relation m) := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

def graph (m : ℕ) : SimpleGraph (Fin 8) := SimpleGraph.fromRel (relation m)

instance (m : ℕ) : DecidableRel (graph m).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (relation m)).Adj)

def Positive (m : ℕ) : Prop := ScoredExchange (graph m) univ 5 ∨ PathReduction (graph m) univ 6

lemma graph_mono {small large : ℕ} (h : large &&& small = small) : graph small ≤ graph large := by
  have hb (i : ℕ) (hi : small.testBit i = true) : large.testBit i = true := by
    have he := congrArg (fun n : ℕ ↦ n.testBit i) h
    simpa only [Nat.testBit_and, hi, Bool.and_true] using he
  have hr {a b : Fin 8} (h : relation small a b) : relation large a b := by
    rcases h with h | ⟨ha, hb', hbit⟩
    · exact Or.inl h
    · exact Or.inr ⟨ha, hb', hb _ hbit⟩
  intro a b hab
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨hne, h | h⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl (hr h)⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inr (hr h)⟩

lemma Positive.mono {small large : ℕ} (hs : Positive small) (h : large &&& small = small) :
    Positive large := by
  let f := SimpleGraph.Copy.ofLE (graph small) (graph large) (graph_mono h)
  rcases hs with hs | hs
  · left
    simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f
  · right
    simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f

end Erdos577.MatchingExchange
