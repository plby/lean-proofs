import ErdosProblems.Erdos577.ScoredExchange
import ErdosProblems.Erdos577.UnattachedModel
import ErdosProblems.Erdos577.PathWitnesses

/-! Path--quadrilateral models retaining the old block's diagonal score. -/

namespace Erdos577.PathLoss

open Finset

def basePairs (diagonal : Fin 4) : Finset (Fin 8 × Fin 8) :=
  PathExchange.basePairs ∪ (if diagonal.val.testBit 0 then {(4, 6)} else ∅) ∪
    (if diagonal.val.testBit 1 then {(5, 7)} else ∅)

def relation (diagonal : Fin 4) (m : ℕ) (a b : Fin 8) : Prop :=
  (a, b) ∈ basePairs diagonal ∨
    (a.val < 4 ∧ 4 ≤ b.val ∧ m.testBit (4 * a.val + b.val - 4) = true)

instance (diagonal : Fin 4) (m : ℕ) : DecidableRel (relation diagonal m) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

def graph (diagonal : Fin 4) (m : ℕ) : SimpleGraph (Fin 8) :=
  SimpleGraph.fromRel (relation diagonal m)

instance (diagonal : Fin 4) (m : ℕ) : DecidableRel (graph diagonal m).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (relation diagonal m)).Adj)

def Positive (diagonal : Fin 4) (m : ℕ) : Prop :=
  ScoredExchange (graph diagonal m) univ (min (Unattached.oldEdges diagonal) 5)

lemma graph_mono (diagonal : Fin 4) {small large : ℕ} (h : large &&& small = small) :
    graph diagonal small ≤ graph diagonal large := by
  have hb (i : ℕ) (hi : small.testBit i = true) : large.testBit i = true := by
    have he := congrArg (fun n : ℕ ↦ n.testBit i) h
    simpa only [Nat.testBit_and, hi, Bool.and_true] using he
  have hr {a b : Fin 8} (h : relation diagonal small a b) : relation diagonal large a b := by
    rcases h with h | ⟨ha, hb', hbit⟩
    · exact Or.inl h
    · exact Or.inr ⟨ha, hb', hb _ hbit⟩
  intro a b hab
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨hne, h | h⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl (hr h)⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inr (hr h)⟩

lemma Positive.mono {diagonal : Fin 4} {small large : ℕ}
    (hs : Positive diagonal small) (h : large &&& small = small) : Positive diagonal large := by
  change ScoredExchange (graph diagonal large) univ (min (Unattached.oldEdges diagonal) 5)
  let f := SimpleGraph.Copy.ofLE (graph diagonal small) (graph diagonal large)
    (graph_mono diagonal h)
  simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f

lemma base_graph_le (diagonal : Fin 4) (m : ℕ) : PathExchange.graph m ≤ graph diagonal m := by
  have hr {a b : Fin 8} (h : PathExchange.relation m a b) : relation diagonal m a b := by
    rcases h with h | h
    · exact Or.inl (mem_union_left _ (mem_union_left _ h))
    · exact Or.inr h
  intro a b hab
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨hne, h | h⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl (hr h)⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inr (hr h)⟩

/-- The four-edge case reuses the existing path theorem and its certified witnesses. -/
theorem finite_zero (m : Fin 65536) (h : 9 ≤ PathExchange.crossCount m.val) :
    Positive 0 m.val := by
  have hp := (PathExchange.finite_exchange m h).scored_four (by decide)
  let f := SimpleGraph.Copy.ofLE _ _ (base_graph_le 0 m.val)
  change ScoredExchange (graph 0 m.val) univ 4
  simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hp.image f

end Erdos577.PathLoss
