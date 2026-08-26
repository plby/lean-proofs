import ErdosProblems.Erdos547.ShrubStateCounts
import ErdosProblems.Erdos547.AvailableVertices

/-!
# Private reservations and occupied vertices share the same head budget
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

theorem card_reserved_in_cluster_le {A V I : Type*} [DecidableEq A]
    [DecidableEq V] [DecidableEq I] (F : Finset A)
    (C : I → Finset V) (head : A → I) (R : A → Finset V) (w : A → ℕ)
    (hC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hR : ∀ a ∈ F, R a ⊆ C (head a)) (hw : ∀ a ∈ F, (R a).card ≤ w a) (i : I) :
    (C i ∩ F.biUnion R).card ≤ ∑ a ∈ F, if head a = i then w a else 0 := by
  classical
  have hsub : C i ∩ F.biUnion R ⊆ F.biUnion (fun a ↦ C i ∩ R a) := by
    intro v hv
    obtain ⟨hvi, hv⟩ := Finset.mem_inter.mp hv
    obtain ⟨a, ha, hva⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_inter.mpr ⟨hvi, hva⟩⟩
  apply (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans _)
  apply Finset.sum_le_sum
  intro a ha
  by_cases hai : head a = i
  · rw [if_pos hai]
    exact (Finset.card_le_card Finset.inter_subset_right).trans (hw a ha)
  · rw [if_neg hai]
    have he : C i ∩ R a = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hvi, hva⟩ := Finset.mem_inter.mp hv
      exact Finset.disjoint_left.mp (hC (head a) i hai) (hR a ha hva) hvi
    rw [he, Finset.card_empty]

namespace ShrubState

variable {U V I : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]
  [DecidableEq I] {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} {C : I → Finset V} {head : ↥P.shrubs → I}
  {seed : (T.induce (P.seeds : Set U)).Copy G}
variable (E : ShrubState P G C head seed)

theorem occupied_reserved_card_le
    (hC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (F : Finset ↥P.shrubs) (hEF : Disjoint E.placed F) (R : ↥P.shrubs → Finset V)
    (hR : ∀ S ∈ F, R S ⊆ C (head S))
    (hRsize : ∀ S ∈ F, (R S).card ≤ (P.nearPart S).card) (i : I) :
    (C i ∩ E.occupied).card + (C i ∩ F.biUnion R).card ≤
      P.seeds.card + (∑ S, if head S = i then (P.nearPart S).card else 0) + E.farUsed i := by
  classical
  have hused := E.occupied_cluster_card_le hC i
  have hres := card_reserved_in_cluster_le F C head R (fun S ↦ (P.nearPart S).card)
    hC hR hRsize i
  have htotal : E.nearUsed i + (∑ S ∈ F, if head S = i then (P.nearPart S).card else 0) ≤
      ∑ S, if head S = i then (P.nearPart S).card else 0 := by
    rw [nearUsed, ← Finset.sum_union hEF]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ Nat.zero_le _)
  omega

theorem available_from_loads
    (hC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (F : Finset ↥P.shrubs) (hEF : Disjoint E.placed F) (R : ↥P.shrubs → Finset V)
    (hR : ∀ S ∈ F, R S ⊆ C (head S))
    (hRsize : ∀ S ∈ F, (R S).card ≤ (P.nearPart S).card)
    (i : I) (Q : Finset V) (m m₀ q : ℕ)
    (hm : (C i).card = m) (hQ : Q.card = q) (hmain : m₀ + 2 * q = m)
    (hseed : 2 * P.seeds.card ≤ q)
    (hload : (∑ S, if head S = i then (P.nearPart S).card else 0) + E.farUsed i ≤ m₀) :
    (q : ℝ) / 2 ≤ ((C i \ (Q ∪ E.occupied ∪ F.biUnion R)).card : ℝ) := by
  have hcount := E.occupied_reserved_card_le hC F hEF R hR hRsize i
  apply available_vertices_half_buffer (C i) Q E.occupied (F.biUnion R)
    m m₀ q P.seeds.card hm hQ hmain _ hseed
  omega

end ShrubState
end Erdos547

#print axioms Erdos547.ShrubState.available_from_loads
