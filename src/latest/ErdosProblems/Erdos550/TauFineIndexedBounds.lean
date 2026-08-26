import Mathlib
import ErdosProblems.Erdos550.TauFineIndexedData

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Aggregate bounds for the indexed τ-fine components

The regularity allocation consumes scalar totals rather than quotient-level
component statements.  These lemmas derive the required aggregate inequalities:
the number of shrubs is bounded by their total mass, attachment incidences are
bounded by the number of shrubs times the separator bound, and every attachment
is an actual seed with an adjacent witness inside its shrub.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {α : Type} [Fintype α] [DecidableEq α]

lemma componentNonseedVertices_card_pos
    (T : SimpleGraph α) (S : Finset α) (c : NonseedComponent T S) :
    0 < (componentNonseedVertices T S c.1).card := by
  exact Finset.card_pos.mpr ( componentNonseedVertices_nonempty T S c )

lemma nonseedComponent_card_le_sum_sizes
    (T : SimpleGraph α) (S : Finset α) :
    Fintype.card (NonseedComponent T S) ≤
      ∑ c : NonseedComponent T S,
        (componentNonseedVertices T S c.1).card := by
  exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => componentNonseedVertices_card_pos T S _ )

lemma nonseedComponent_card_le_complement
    (T : SimpleGraph α) (S : Finset α) :
    Fintype.card (NonseedComponent T S) ≤ Fintype.card α - S.card := by
  convert! nonseedComponent_card_le_sum_sizes T S using 1;
  convert! sum_componentNonseedVertices_card T S |> Eq.symm using 1

lemma nonseedComponent_card_le_total
    (T : SimpleGraph α) (S : Finset α) :
    Fintype.card (NonseedComponent T S) ≤ Fintype.card α := by
  convert! nonseedComponent_card_le_complement T S |> le_trans <| Nat.sub_le _ _

lemma sum_component_attachment_card_le
    (T : SimpleGraph α) (S : Finset α) (r : ℕ)
    (hatt : ∀ c : NonseedComponent T S,
      (componentSeeds T S c.1).card ≤ r) :
    (∑ c : NonseedComponent T S, (componentSeeds T S c.1).card)
      ≤ Fintype.card (NonseedComponent T S) * r := by
  exact le_trans ( Finset.sum_le_sum fun _ _ => hatt _ ) ( by norm_num )

lemma sum_component_attachment_card_le_complement
    (T : SimpleGraph α) (S : Finset α) (r : ℕ)
    (hatt : ∀ c : NonseedComponent T S,
      (componentSeeds T S c.1).card ≤ r) :
    (∑ c : NonseedComponent T S, (componentSeeds T S c.1).card)
      ≤ (Fintype.card α - S.card) * r := by
  refine' le_trans _ ( Nat.mul_le_mul_right _ ( show Fintype.card ( NonseedComponent T S ) ≤ Fintype.card α - #S from _ ) );
  · exact le_trans ( Finset.sum_le_sum fun _ _ => hatt _ ) ( by norm_num );
  · convert! nonseedComponent_card_le_complement T S using 1

lemma sum_component_attachment_card_le_total
    (T : SimpleGraph α) (S : Finset α) (r : ℕ)
    (hatt : ∀ c : NonseedComponent T S,
      (componentSeeds T S c.1).card ≤ r) :
    (∑ c : NonseedComponent T S, (componentSeeds T S c.1).card)
      ≤ Fintype.card α * r := by
  convert! sum_component_attachment_card_le T S r hatt |> le_trans <| Nat.mul_le_mul_right r ( nonseedComponent_card_le_total T S ) using 1

lemma component_attachment_mem_seed
    (T : SimpleGraph α) (S : Finset α)
    (c : NonseedComponent T S) {s : α}
    (hs : s ∈ componentSeeds T S c.1) : s ∈ S := by
  convert! Set.mem_setOf.mp ( componentSeeds_subset T S c.1 hs ) using 1

lemma component_attachment_has_internal_neighbour
    (T : SimpleGraph α) (S : Finset α)
    (c : NonseedComponent T S) {s : α}
    (hs : s ∈ componentSeeds T S c.1) :
    ∃ v, v ∉ S ∧ v ∈ c.1.supp ∧ T.Adj s v := by
  -- By definition of `componentSeeds`, there exists some `v ∈ c.1.supp` such that `T.Adj s v`.
  obtain ⟨v, hv⟩ : ∃ v ∈ c.1.supp, T.Adj s v := by
    unfold componentSeeds at hs; aesop;
  by_cases hvS : v ∈ S;
  · have := componentNonseedVertices_eq_supp T S c; simp_all +decide [ Set.ext_iff ] ;
    specialize this v; simp_all +decide [ componentNonseedVertices ] ;
  · exact ⟨ v, hvS, hv ⟩

lemma seed_component_incidence_iff
    (T : SimpleGraph α) (S : Finset α)
    (c : NonseedComponent T S) (s : α) :
    s ∈ componentSeeds T S c.1 ↔
      s ∈ S ∧ ∃ v ∈ componentNonseedVertices T S c.1, T.Adj s v := by
  -- By definition of componentSeeds, we have that s ∈ componentSeeds T S c if and only if s ∈ S and there exists v ∈ c.supp such that T.Adj s v.
  unfold componentSeeds;
  have := componentNonseedVertices_eq_supp T S c;
  simp +decide [ ← this ]

/-
Aggregate attachment bound returned directly from the τ-fine theorem.
-/
theorem tree_tau_fine_aggregate_attachment_bound
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (τ : ℝ) (hτ : 0 < τ)
    (hn : (1 : ℝ) ≤ τ * Fintype.card α) :
    ∃ S : Finset α,
      (S.card : ℝ) ≤ 1 / τ ∧
      (∀ c : NonseedComponent T S,
        ((componentNonseedVertices T S c.1).card : ℝ)
          ≤ τ * Fintype.card α) ∧
      (∑ c : NonseedComponent T S, (componentSeeds T S c.1).card)
        ≤ (Fintype.card α - S.card) * Nat.floor (1 / τ) := by
  obtain ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩ := tree_tau_fine_indexed_data T hT τ hτ hn;
  exact ⟨ S, hS₁, hS₂, by simpa [ ← hS₄.1 ] using! sum_component_attachment_card_le_complement T S _ hS₃ ⟩

end Erdos550
