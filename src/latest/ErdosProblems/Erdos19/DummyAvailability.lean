import ErdosProblems.Erdos76.Kahn
import Mathlib.Tactic

/-! # Deterministic availability of dummy vertices -/

namespace Erdos19

open Finset Erdos76 Erdos76.FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The sum of codegrees from a fixed vertex into any pool is at most rank
times its degree. Diagonal codegrees are included, so no exception is hidden. -/
theorem sum_pairDegree_le_rank_mul_degree (H : FiniteHypergraph V E)
    (R : ℕ) (hbound : H.IsBounded R) (v : V) (P : Finset V) :
    (∑ d ∈ P, H.edgePairDegree v d) ≤ R * H.edgeDegree v := by
  classical
  have hpair (d : V) : H.edgePairDegree v d =
      ∑ e : E, if v ∈ H.support e ∧ d ∈ H.support e then 1 else 0 := by
    unfold edgePairDegree
    rw [card_eq_sum_ones, sum_filter]
  have hcount : (∑ d ∈ P, H.edgePairDegree v d) =
      ∑ e ∈ univ.filter (fun e ↦ v ∈ H.support e), (P ∩ H.support e).card := by
    simp_rw [hpair]
    rw [sum_comm, sum_filter]
    apply sum_congr rfl
    intro e _
    by_cases hv : v ∈ H.support e
    · simp [hv]
    · simp [hv]
  rw [hcount]
  calc
    _ ≤ ∑ _e ∈ univ.filter (fun e ↦ v ∈ H.support e), R := by
      apply sum_le_sum
      intro e _
      exact (card_le_card inter_subset_right).trans (hbound e)
    _ = R * H.edgeDegree v := by simp [edgeDegree, Nat.mul_comm]

theorem high_pairDegree_card_mul_le (H : FiniteHypergraph V E)
    (R L : ℕ) (hbound : H.IsBounded R) (v : V) (P : Finset V) :
    (P.filter fun d ↦ L ≤ H.edgePairDegree v d).card * L ≤ R * H.edgeDegree v := by
  classical
  calc
    _ = ∑ _d ∈ P.filter (fun d ↦ L ≤ H.edgePairDegree v d), L := by simp
    _ ≤ ∑ d ∈ P.filter (fun d ↦ L ≤ H.edgePairDegree v d), H.edgePairDegree v d :=
      sum_le_sum fun d hd ↦ (mem_filter.mp hd).2
    _ ≤ ∑ d ∈ P, H.edgePairDegree v d :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ Nat.zero_le _)
    _ ≤ R * H.edgeDegree v := sum_pairDegree_le_rank_mul_degree H R hbound v P

theorem high_degree_card_mul_le (H : FiniteHypergraph V E) (D : ℕ) (P : Finset V) :
    (P.filter fun d ↦ D ≤ H.edgeDegree d).card * D ≤ ∑ d ∈ P, H.edgeDegree d := by
  classical
  calc
    _ = ∑ _d ∈ P.filter (fun d ↦ D ≤ H.edgeDegree d), D := by simp
    _ ≤ ∑ d ∈ P.filter (fun d ↦ D ≤ H.edgeDegree d), H.edgeDegree d :=
      sum_le_sum fun d hd ↦ (mem_filter.mp hd).2
    _ ≤ ∑ d ∈ P, H.edgeDegree d :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ Nat.zero_le _)

/-- Choose a pool vertex that is not saturated, is not already in the current
support, and has codegree below `L` with every current support vertex. The pool
load budget may be the final demand budget of an iterative assignment. -/
theorem exists_dummy_with_degree_and_pairDegree_slack (H : FiniteHypergraph V E)
    (R D L M : ℕ) (hbound : H.IsBounded R) (hD : 0 < D) (hL : 0 < L)
    (S P : Finset V) (hdeg : ∀ x ∈ S, H.edgeDegree x ≤ D)
    (hload : (∑ d ∈ P, H.edgeDegree d) ≤ M)
    (hroom : M / D + S.card + S.card * (R * D / L) < P.card) :
    ∃ d ∈ P, d ∉ S ∧ H.edgeDegree d < D ∧
      ∀ x ∈ S, H.edgePairDegree x d < L := by
  classical
  let full := P.filter fun d ↦ D ≤ H.edgeDegree d
  let high : V → Finset V := fun x ↦ P.filter fun d ↦ L ≤ H.edgePairDegree x d
  let blocked := (full ∪ S) ∪ S.biUnion high
  have hfull : full.card ≤ M / D :=
    (Nat.le_div_iff_mul_le hD).mpr ((high_degree_card_mul_le H D P).trans hload)
  have hhigh : ∀ x ∈ S, (high x).card ≤ R * D / L := by
    intro x hx
    apply (Nat.le_div_iff_mul_le hL).mpr
    exact (high_pairDegree_card_mul_le H R L hbound x P).trans
      (Nat.mul_le_mul_left R (hdeg x hx))
  have hblocked : blocked.card < P.card := by
    calc
      blocked.card ≤ (full ∪ S).card + (S.biUnion high).card := card_union_le _ _
      _ ≤ (full.card + S.card) + ∑ x ∈ S, (high x).card :=
        Nat.add_le_add (card_union_le _ _) card_biUnion_le
      _ ≤ (M / D + S.card) + ∑ _x ∈ S, R * D / L := by
        exact Nat.add_le_add (Nat.add_le_add_right hfull _) (sum_le_sum hhigh)
      _ = M / D + S.card + S.card * (R * D / L) := by simp
      _ < P.card := hroom
  obtain ⟨d, hdP, hd⟩ := exists_mem_notMem_of_card_lt_card hblocked
  have hdS : d ∉ S := fun h ↦ hd (mem_union_left _ (mem_union_right _ h))
  have hddeg : H.edgeDegree d < D := by
    by_contra h
    exact hd (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hdP, by omega⟩)))
  refine ⟨d, hdP, hdS, hddeg, ?_⟩
  intro x hx
  by_contra h
  exact hd (mem_union_right _ (mem_biUnion.mpr
    ⟨x, hx, mem_filter.mpr ⟨hdP, by omega⟩⟩))

#print axioms sum_pairDegree_le_rank_mul_degree
#print axioms exists_dummy_with_degree_and_pairDegree_slack

end Erdos19
