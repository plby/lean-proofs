import Arxiv.Arxiv2411_18291.CliqueExtensionCount

/-!
# Bounded hypergraphs

The paper's boundedness condition is a strict upper bound on every face
degree. Common-neighborhood typicality controls these degrees, since adding
one vertex gives a bijection between neighbors and containing edges.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {r h : ℕ}

theorem card_neighbors_eq_degree (G : Hypergraph V (r + 1)) (S : Block V r) :
    (neighbors G S).card = (G.filter fun e => S.val ⊆ e.val).card := by
  apply card_bij (fun v hv => extendBlock S v ((mem_neighbors G S v).mp hv).choose)
  · intro v hv
    exact mem_filter.mpr ⟨((mem_neighbors G S v).mp hv).choose_spec, subset_insert _ _⟩
  · intro v hv w hw he
    exact extendBlock_vertex_injective S _ _ he
  · intro e he
    obtain ⟨heG, hSe⟩ := mem_filter.mp he
    obtain ⟨v, hv, hve⟩ := exists_eq_insert_iff.mpr ⟨hSe, by rw [S.property, e.property]⟩
    have heq : extendBlock S v hv = e := Subtype.ext hve
    refine ⟨v, (mem_neighbors G S v).mpr ⟨hv, heq.symm ▸ heG⟩, ?_⟩
    exact heq

/-- Strict boundedness as defined in the paper's notation section. -/
def IsGraphBounded (G : Hypergraph V (r + 1)) (θ : ℝ) : Prop :=
  ∀ S : Block V r, ((G.filter fun e => S.val ⊆ e.val).card : ℝ) < θ * Fintype.card V

@[simp] theorem commonNeighbors_singleton (G : Hypergraph V (r + 1)) (S : Block V r) :
    commonNeighbors G {S} = neighbors G S := by
  ext v
  simp

theorem IsTypical.degree_upper {G : Hypergraph V (r + 1)} {c : ℝ}
    (hT : IsTypical G c h) (hh : 1 ≤ h) (S : Block V r) :
    ((G.filter fun e => S.val ⊆ e.val).card : ℝ) ≤
      (1 + c) * density G * Fintype.card V := by
  have ht := hT {S} (by simpa only [card_singleton] using hh)
  rw [commonNeighbors_singleton, card_singleton, pow_one, card_neighbors_eq_degree] at ht
  have hu := (abs_le.mp ht).2
  nlinarith

theorem IsTypical.graphBounded {G : Hypergraph V (r + 1)} {c θ : ℝ}
    (hT : IsTypical G c h) (hh : 1 ≤ h) (hn : 0 < Fintype.card V)
    (hθ : (1 + c) * density G < θ) : IsGraphBounded G θ := by
  intro S
  exact (hT.degree_upper hh S).trans_lt
    (mul_lt_mul_of_pos_right hθ (by exact_mod_cast hn))

theorem IsGraphBounded.mono {G : Hypergraph V (r + 1)} {θ θ' : ℝ}
    (hG : IsGraphBounded G θ) (hθ : θ ≤ θ') : IsGraphBounded G θ' := by
  intro S
  exact (hG S).trans_le (mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _))

end Arxiv2411_18291
