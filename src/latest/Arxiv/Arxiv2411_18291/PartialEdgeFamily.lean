import Arxiv.Arxiv2411_18291.GraphBoundedness
import Mathlib.Data.Finset.Option

/-!
# Graphs formed by partial edge families

An aborted or stopped step contributes no edge. Degrees in the underlying
simple graph are bounded by the sum of the incidence indicators of the
individual steps, whether or not some of their edge images coincide.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

def edgeIncidence (e : Option (Block V r)) (S : Finset V) : ℕ :=
  match e with
  | none => 0
  | some g => if S ⊆ g.val then 1 else 0

def partialFamilyDegree (s : Finset I) (E : I → Option (Block V r)) (S : Finset V) : ℕ :=
  ∑ i ∈ s, edgeIncidence (E i) S

def partialFamilyGraph (s : Finset I) (E : I → Option (Block V r)) : Hypergraph V r :=
  s.biUnion fun i => (E i).toFinset

omit [Fintype V] in
theorem edgeIncidence_le_one (e : Option (Block V r)) (S : Finset V) : edgeIncidence e S ≤ 1 := by
  cases e <;> simp only [edgeIncidence]
  · omega
  · split_ifs <;> omega

omit [Fintype V] in
theorem partialFamilyGraph_degree_le (s : Finset I) (E : I → Option (Block V r))
    (S : Finset V) :
    ((partialFamilyGraph s E).filter fun e => S ⊆ e.val).card ≤ partialFamilyDegree s E S := by
  rw [partialFamilyGraph, filter_biUnion]
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro i _
  cases h : E i with
  | none => simp [edgeIncidence]
  | some e =>
    by_cases he : S ⊆ e.val <;> simp [edgeIncidence, filter_singleton, he]

omit [Fintype V] in
theorem partialFamilyDegree_mono {s t : Finset I} (hst : s ⊆ t)
    (E : I → Option (Block V r)) (S : Finset V) :
    partialFamilyDegree s E S ≤ partialFamilyDegree t E S :=
  sum_le_sum_of_subset_of_nonneg hst (fun _ _ _ => Nat.zero_le _)

theorem IsGraphBounded.union_biUnion_degree_le {B : Hypergraph V (r + 1)} {θ : ℝ}
    (hB : IsGraphBounded B θ) (s : Finset I) (G : I → Hypergraph V (r + 1))
    (γ : I → ℝ)
    (hG : ∀ i ∈ s, ∀ S : Block V r, ((G i).filter fun e => S.val ⊆ e.val).card ≤
      γ i * Fintype.card V) :
    IsGraphBounded (B ∪ s.biUnion G) (θ + ∑ i ∈ s, γ i) := by
  intro S
  have hc : (((s.biUnion G).filter fun e => S.val ⊆ e.val).card : ℝ) ≤
      ∑ i ∈ s, γ i * Fintype.card V := by
    rw [filter_biUnion]
    calc
      _ ≤ ∑ i ∈ s, (((G i).filter fun e => S.val ⊆ e.val).card : ℝ) := by
        exact_mod_cast (card_biUnion_le (s := s) (t := fun i => (G i).filter
          (fun e => S.val ⊆ e.val)))
      _ ≤ _ := sum_le_sum fun i hi => hG i hi S
  have hu : (((B ∪ s.biUnion G).filter fun e => S.val ⊆ e.val).card : ℝ) ≤
      (B.filter fun e => S.val ⊆ e.val).card +
        ((s.biUnion G).filter fun e => S.val ⊆ e.val).card := by
    rw [filter_union]
    exact_mod_cast (card_union_le (s := B.filter (fun e => S.val ⊆ e.val))
      (t := (s.biUnion G).filter (fun e => S.val ⊆ e.val)))
  calc
    _ ≤ _ := hu
    _ < θ * Fintype.card V + ∑ i ∈ s, γ i * Fintype.card V := add_lt_add_of_lt_of_le (hB S) hc
    _ = _ := by rw [← sum_mul, add_mul]

end Arxiv2411_18291
