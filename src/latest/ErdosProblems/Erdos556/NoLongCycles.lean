import ErdosProblems.Erdos556.Basic

/-!
# Hereditary absence of long cycles
-/

namespace Erdos556

open SimpleGraph

def NoLongCycles {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length < m

theorem NoLongCycles.of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {m : ℕ} (hH : NoLongCycles H m) (f : G ↪g H) : NoLongCycles G m := by
  intro v c hc
  have h := hH (f v) (c.map f.toHom) (hc.map f.injective)
  simpa only [Walk.length_map] using h

theorem NoLongCycles.induce {V : Type*} {G : SimpleGraph V} {m : ℕ}
    (hG : NoLongCycles G m) (S : Set V) : NoLongCycles (G.induce S) m :=
  hG.of_embedding (SimpleGraph.Embedding.induce S)

def induceComplementEmbedding {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (G.induce S)ᶜ ↪g Gᶜ where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := by
    intro x y
    change Gᶜ.Adj x.val y.val ↔ (G.induce S)ᶜ.Adj x y
    simp only [compl_adj, induce_adj, ne_eq, Subtype.coe_inj]

theorem NoLongCycles.complement_induce {V : Type*} {G : SimpleGraph V} {m : ℕ}
    (hG : NoLongCycles Gᶜ m) (S : Set V) : NoLongCycles (G.induce S)ᶜ m :=
  hG.of_embedding (induceComplementEmbedding G S)

theorem NoLongCycles.not_cycle {V : Type*} {G : SimpleGraph V} {m : ℕ}
    (hG : NoLongCycles G m) (n : ℕ) (hn : 3 ≤ n) (hmn : m ≤ n) : ¬ cycleGraph n ⊑ G := by
  intro h
  obtain ⟨v, c, hc, hlen⟩ := (cycleGraph_isContained_iff (by omega)).mp h
  have hshort := hG v c hc
  omega

#print axioms induceComplementEmbedding
#print axioms NoLongCycles.complement_induce

end Erdos556
