import Arxiv.Arxiv2411_18291.EmbeddingCliqueImages
import Arxiv.Arxiv2411_18291.EdgeFamilyBoundedness

/-!
# Clique patterns rooted at one edge

Any two edges of the same size have an explicit chosen root bijection.
Rooting a complete clique pattern at one edge is admissible. An injective
enumeration of a bounded leave gives bounded input root-edge families.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} {r : ℕ}

def edgeRootEquiv (F₀ : Block W r) (e : Block V r) : F₀.val ≃ e.val :=
  Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, F₀.property, e.property])

def edgeRootMap (F₀ : Block W r) (e : Block V r) : F₀.val ↪ V :=
  (edgeRootEquiv F₀ e).toEmbedding.trans (Function.Embedding.subtype (· ∈ e.val))

theorem edgeRootMap_usedVertices (F₀ : Block W r) (e : Block V r) :
    usedVertices (edgeRootMap F₀ e) = e.val := by
  ext v
  constructor
  · intro hv
    obtain ⟨x, hx⟩ := (mem_usedVertices (edgeRootMap F₀ e) v).mp hv
    change ((edgeRootEquiv F₀ e) x).val = v at hx
    exact hx ▸ ((edgeRootEquiv F₀ e) x).property
  · intro hv
    refine (mem_usedVertices (edgeRootMap F₀ e) v).mpr
      ⟨(edgeRootEquiv F₀ e).symm ⟨v, hv⟩, ?_⟩
    change ((edgeRootEquiv F₀ e) ((edgeRootEquiv F₀ e).symm ⟨v, hv⟩)).val = v
    rw [Equiv.apply_symm_apply]

variable [DecidableEq W] [DecidableEq V]

omit [DecidableEq V] in
theorem rootImage_self (F₀ : Block W r) (φ : F₀.val ↪ V) :
    (rootImage φ F₀ (Subset.refl _)).val = usedVertices φ := by
  change (F₀.val.subtype (· ∈ F₀.val)).map φ = univ.map φ
  have hfull : F₀.val.subtype (· ∈ F₀.val) = univ := by
    ext x
    simp only [mem_subtype, mem_univ, iff_true]
    exact x.property
  rw [hfull]

omit [DecidableEq V] in
theorem rootImage_edgeRootMap (F₀ : Block W r) (e : Block V r) :
    rootImage (edgeRootMap F₀ e) F₀ (Subset.refl _) = e :=
  Subtype.ext ((rootImage_self F₀ _).trans (edgeRootMap_usedVertices F₀ e))

variable [Fintype W] [Fintype V]

theorem complete_root_admissible (F₀ : Block W (r + 1)) :
    IsAdmissible (complete W (r + 1)) F₀.val := by
  intro _ _ _
  exact ⟨F₀, mem_univ _, Subset.refl _, inter_subset_right⟩

variable {I : Type*} [Fintype I]

omit [Fintype W] [DecidableEq W] in
theorem IsGraphBounded.edgeFamily {G : Hypergraph V (r + 1)} {θ : ℝ}
    (hG : IsGraphBounded G θ) (E : I → Block V (r + 1)) (hE : ∀ i, E i ∈ G)
    (hinj : Function.Injective E) : IsEdgeFamilyBounded E θ := by
  intro S
  have hc : familyDegree E S.val ≤ (G.filter fun e => S.val ⊆ e.val).card := by
    apply card_le_card_of_injOn E
    · intro i hi
      exact mem_filter.mpr ⟨hE i, (mem_filter.mp hi).2⟩
    · exact hinj.injOn
  have hreal : (familyDegree E S.val : ℝ) ≤ (G.filter fun e => S.val ⊆ e.val).card := by
    exact_mod_cast hc
  exact hreal.trans_lt (hG S)

omit [Fintype W] [DecidableEq W] in
theorem isGraphBounded_empty {θ : ℝ} (hθ : 0 < θ) (hn : 0 < Fintype.card V) :
    IsGraphBounded (∅ : Hypergraph V (r + 1)) θ := by
  intro S
  simp only [filter_empty, card_empty, Nat.cast_zero]
  have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  positivity

end Arxiv2411_18291
