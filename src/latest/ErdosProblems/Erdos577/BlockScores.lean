import ErdosProblems.Erdos577.PartitionExchange

/-! Additive score identities for disjoint block replacement. -/

namespace Erdos577

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

namespace BlockPartition

variable {s t : Finset V}

lemma block_ne_empty (p : BlockPartition G s) {q : Finset V} (hq : q ∈ p.blocks) : q ≠ ∅ := by
  intro he
  have hc := (p.quad q hq).card
  simp only [he, card_empty] at hc
  contradiction

lemma disjoint_blocks (p : BlockPartition G s) (q : BlockPartition G t) (h : Disjoint s t) :
    Disjoint p.blocks q.blocks := by
  apply disjoint_left.mpr
  intro b hb hc
  have hd : Disjoint b b := h.mono (p.block_subset hb) (q.block_subset hc)
  exact p.block_ne_empty hb (disjoint_self.mp hd)

def weightSum (p : BlockPartition G s) (w : Finset V → ℕ) : ℕ := ∑ b ∈ p.blocks, w b

lemma weightSum_union (p : BlockPartition G s) (q : BlockPartition G t)
    (h : Disjoint s t) (w : Finset V → ℕ) :
    (p.union q h).weightSum w = p.weightSum w + q.weightSum w := by
  exact sum_union (p.disjoint_blocks q h)

@[simp] lemma weightSum_single {s : Finset V} (h : QuadOn G s) (w : Finset V → ℕ) :
    (single h).weightSum w = w s := by simp [weightSum, single]

lemma weightSum_remove_add (p : BlockPartition G s) (q : Finset V) (hq : q ∈ p.blocks)
    (w : Finset V → ℕ) : (p.remove q hq).weightSum w + w q = p.weightSum w := by
  exact sum_erase_add _ _ hq

lemma weightSum_replace_add (p : BlockPartition G s) (q : Finset V) (hq : q ∈ p.blocks)
    {r : Finset V} (hr : QuadOn G r) (hd : Disjoint (s \ q) r) (w : Finset V → ℕ) :
    ((p.remove q hq).union (single hr) hd).weightSum w + w q = p.weightSum w + w r := by
  rw [weightSum_union, weightSum_single]
  have he := p.weightSum_remove_add q hq w
  omega

end BlockPartition

end Erdos577
