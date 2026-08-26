import ErdosProblems.Erdos19.MatchingFamilyDegrees
import ErdosProblems.Erdos19.ColorCoverCounting

/-! # Bounding matching-repair loads by the original uncovered requests -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [Fintype I]

theorem sum_request_cards_le (A : I → Set V) (a : ℕ)
    (hrequests : ∀ v, (∑ i : I, if v ∈ A i then 1 else 0) ≤ a) :
    (∑ i : I, (A i).ncard) ≤ Fintype.card V * a := by
  simp_rw [ncard_eq_sum_indicator]
  rw [sum_comm]
  calc
    _ ≤ ∑ _v : V, a := sum_le_sum (fun v _ ↦ hrequests v)
    _ = _ := by simp

theorem matching_family_total_degree (G : _root_.SimpleGraph V) (M : I → G.Subgraph)
    (hM : ∀ i, (M i).IsMatching)
    (hdis : Pairwise fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe) :
    (∑ v : V, ((⨆ i, (M i).spanningCoe).neighborSet v).ncard) =
      ∑ i : I, (M i).verts.ncard := by
  simp_rw [matching_family_degree G M hM hdis]
  rw [sum_comm]
  exact sum_congr rfl (fun i _ ↦ (ncard_eq_sum_indicator (M i).verts).symm)

theorem matching_family_total_degree_le_requests (G : _root_.SimpleGraph V)
    (M : I → G.Subgraph) (hM : ∀ i, (M i).IsMatching)
    (hdis : Pairwise fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe)
    (A : I → Set V) (a : ℕ) (hsize : ∀ i, (M i).verts.ncard ≤ 2 * (A i).ncard)
    (hrequests : ∀ v, (∑ i : I, if v ∈ A i then 1 else 0) ≤ a) :
    (∑ v : V, ((⨆ i, (M i).spanningCoe).neighborSet v).ncard) ≤
      2 * (Fintype.card V * a) := by
  rw [matching_family_total_degree G M hM hdis]
  calc
    _ ≤ ∑ i : I, 2 * (A i).ncard := sum_le_sum (fun i _ ↦ hsize i)
    _ = 2 * ∑ i : I, (A i).ncard := (mul_sum _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left 2 (sum_request_cards_le A a hrequests)

theorem matching_family_load_at_required_vertex (G : _root_.SimpleGraph V)
    (M : I → G.Subgraph) (hM : ∀ i, (M i).IsMatching)
    (hdis : Pairwise fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe)
    (A : I → Set V) (U Y : Set V) (hUY : Disjoint U Y)
    (hverts : ∀ i, (M i).verts ⊆ A i ∪ Y) (a : ℕ)
    (hrequests : ∀ v, (∑ i : I, if v ∈ A i then 1 else 0) ≤ a) (v : V) (hv : v ∈ U) :
    ((⨆ i, (M i).spanningCoe).neighborSet v).ncard ≤ a := by
  rw [matching_family_degree G M hM hdis]
  apply le_trans _ (hrequests v)
  apply sum_le_sum
  intro i _
  by_cases hvM : v ∈ (M i).verts
  · have hvA : v ∈ A i := (hverts i hvM).resolve_right (Set.disjoint_left.mp hUY hv)
    simp only [hvM, hvA, ↓reduceIte, le_refl]
  · simp only [hvM, ↓reduceIte, Nat.zero_le]

theorem overloaded_set_card_le (f : V → ℕ) (threshold E : ℕ) (hthreshold : 0 < threshold)
    (htotal : (∑ v : V, f v) ≤ threshold * E) :
    ({v | threshold ≤ f v} : Set V).ncard ≤ E := by
  classical
  let Z : Set V := {v | threshold ≤ f v}
  have hcount : threshold * Z.ncard ≤ ∑ v : V, f v := by
    calc
      _ = ∑ _v ∈ Z.toFinset, threshold := by
        rw [Set.ncard_eq_toFinset_card']
        simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ Z.toFinset, f v := by
        apply sum_le_sum
        intro v hv
        have hvZ : v ∈ Z := Set.mem_toFinset.mp hv
        exact hvZ
      _ ≤ _ := sum_le_sum_of_subset (subset_univ _)
  exact Nat.le_of_mul_le_mul_left (hcount.trans htotal) hthreshold

#print axioms matching_family_total_degree_le_requests
#print axioms matching_family_load_at_required_vertex
#print axioms overloaded_set_card_le

end Erdos19
