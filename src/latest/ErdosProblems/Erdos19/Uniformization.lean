import ErdosProblems.Erdos19.ApproximateColoring

/-!
# Private padding of bounded-rank hypergraphs

Each edge receives its own private vertices. Original degrees and codegrees
are unchanged, and every new vertex has degree at most one.
-/

namespace Erdos19

open Erdos76 Erdos76.FiniteHypergraph

namespace Uniformization

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

def padded (H : FiniteHypergraph V E) (r : ℕ) : FiniteHypergraph (V ⊕ (E × ℕ)) E where
  vertexSet := H.vertexSet.image Sum.inl ∪
    ((Finset.univ : Finset E) ×ˢ Finset.range r).image Sum.inr
  support e := (H.support e).image Sum.inl ∪
    (Finset.range (r - (H.support e).card)).image (fun i ↦ Sum.inr (e, i))
  support_subset_vertexSet := by
    intro e x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨v, H.support_subset_vertexSet e hv, rfl⟩)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(e, i), Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      have hi' := Finset.mem_range.mp hi
      exact Finset.mem_range.mpr (by omega)

@[simp]
lemma mem_padded_support_inl (H : FiniteHypergraph V E) (r : ℕ) (e : E) (v : V) :
    Sum.inl v ∈ (padded H r).support e ↔ v ∈ H.support e := by
  simp [padded]

@[simp]
lemma mem_padded_support_inr (H : FiniteHypergraph V E) (r : ℕ) (e f : E) (i : ℕ) :
    Sum.inr (f, i) ∈ (padded H r).support e ↔
      e = f ∧ i < r - (H.support e).card := by
  simp [padded, and_left_comm, and_assoc, and_comm]

@[simp]
lemma mem_padded_vertexSet_inl (H : FiniteHypergraph V E) (r : ℕ) (v : V) :
    Sum.inl v ∈ (padded H r).vertexSet ↔ v ∈ H.vertexSet := by
  simp [padded]

lemma padded_isUniform (H : FiniteHypergraph V E) (r : ℕ) (hbound : H.IsBounded r) :
    (padded H r).IsUniform r := by
  intro e
  have hd : Disjoint ((H.support e).image (Sum.inl : V → V ⊕ (E × ℕ)))
      ((Finset.range (r - (H.support e).card)).image (fun i ↦ Sum.inr (e, i))) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hy
    cases heq
  change (((H.support e).image Sum.inl) ∪
    (Finset.range (r - (H.support e).card)).image (fun i ↦ Sum.inr (e, i))).card = r
  rw [Finset.card_union_of_disjoint hd]
  rw [Finset.card_image_of_injective _ (by intro a b h; exact Sum.inl.inj h)]
  rw [Finset.card_image_of_injective _ (by
    intro a b h
    exact congrArg Prod.snd (Sum.inr.inj h))]
  rw [Finset.card_range]
  exact Nat.add_sub_of_le (hbound e)

@[simp]
lemma padded_edgeDegree_inl (H : FiniteHypergraph V E) (r : ℕ) (v : V) :
    (padded H r).edgeDegree (Sum.inl v) = H.edgeDegree v := by
  simp [edgeDegree]

@[simp]
lemma padded_edgePairDegree_inl (H : FiniteHypergraph V E) (r : ℕ) (u v : V) :
    (padded H r).edgePairDegree (Sum.inl u) (Sum.inl v) = H.edgePairDegree u v := by
  simp [edgePairDegree]

lemma padded_edgeDegree_inr_le_one (H : FiniteHypergraph V E) (r : ℕ) (e : E) (i : ℕ) :
    (padded H r).edgeDegree (Sum.inr (e, i)) ≤ 1 := by
  unfold edgeDegree
  calc
    ((Finset.univ : Finset E).filter fun f ↦
        Sum.inr (e, i) ∈ (padded H r).support f).card ≤ ({e} : Finset E).card := by
          apply Finset.card_le_card
          intro f hf
          have h := (mem_padded_support_inr H r f e i).mp (Finset.mem_filter.mp hf).2
          exact Finset.mem_singleton.mpr h.1
    _ = 1 := Finset.card_singleton e

lemma pairDegree_le_degree_left (H : FiniteHypergraph V E) (u v : V) :
    H.edgePairDegree u v ≤ H.edgeDegree u := by
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2.1⟩

lemma pairDegree_le_degree_right (H : FiniteHypergraph V E) (u v : V) :
    H.edgePairDegree u v ≤ H.edgeDegree v := by
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2.2⟩

def restrictColoring (H : FiniteHypergraph V E) (r q : ℕ)
    (c : (padded H r).EdgeColoring q) : H.EdgeColoring q :=
  SimpleGraph.Coloring.mk c (by
    intro e f hef
    apply c.valid
    refine ⟨hef.1, ?_⟩
    obtain ⟨v, hv, hv'⟩ := Finset.not_disjoint_iff.mp hef.2
    exact Finset.not_disjoint_iff.mpr
      ⟨Sum.inl v, (mem_padded_support_inl H r e v).mpr hv,
        (mem_padded_support_inl H r f v).mpr hv'⟩)

end Uniformization

#print axioms Uniformization.padded_isUniform
#print axioms Uniformization.padded_edgeDegree_inr_le_one
#print axioms Uniformization.restrictColoring

end Erdos19
