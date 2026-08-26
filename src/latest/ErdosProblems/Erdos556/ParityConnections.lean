import ErdosProblems.Erdos556.DeletionOddCycles
import ErdosProblems.Erdos556.ShortAttachments
import ErdosProblems.Erdos556.OddCycleArcs

/-!
# Bounded parity connections avoiding a prescribed set

A short odd cycle and two disjoint short attachments form a bounded set
supporting paths of both parities. Endpoints are excluded from the set that
is packed and sampled.
-/

namespace Erdos556

open SimpleGraph Finset

def ParityConnection {V : Type*} (G : SimpleGraph V) (L : ℕ) (u v : V)
    (S : Finset V) : Prop :=
  ∀ r : Fin 2, ∃ p : G.Walk u v, p.IsPath ∧ p.length ≤ L ∧ p.length % 2 = r.val ∧
    ∀ x ∈ p.support, x ≠ u → x ≠ v → x ∈ S

theorem ParityConnection.mono {V : Type*} {G : SimpleGraph V} {L : ℕ} {u v : V}
    {S T : Finset V} (h : ParityConnection G L u v S) (hST : S ⊆ T) :
    ParityConnection G L u v T := by
  intro r
  obtain ⟨p, hp, hlen, hpar, hs⟩ := h r
  exact ⟨p, hp, hlen, hpar, fun x hx hxu hxv => hST (hs x hx hxu hxv)⟩

theorem exists_short_parity_connection_avoiding {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b d D : ℕ)
    (hconn : ConnectedAfterDeleting G (b + 3 * D + 3))
    (hnonbip : NonbipartiteAfterDeleting G (b + 3 * D + 3))
    (hd : 0 < d) (hdeg : ∀ w, d + (b + 3 * D + 3) ≤ G.degree w)
    (hN : Fintype.card V ≤ D * d) (u v : V) (huv : u ≠ v)
    (S : Finset V) (hS : S.card ≤ b) :
    ∃ T : Finset V, ParityConnection G (12 * D + 3) u v T ∧
      T.card ≤ 12 * D + 3 ∧ Disjoint S T := by
  classical
  let S₀ := (S.erase u).erase v
  have hS₀ : S₀.card ≤ b :=
    (card_le_card ((erase_subset v (S.erase u)).trans (erase_subset u S))).trans hS
  let F := insert u (insert v S₀)
  have hF : F.card ≤ b + 3 * D + 3 := by
    have h1 := card_insert_le u (insert v S₀)
    have h2 := card_insert_le v S₀
    dsimp [F]
    omega
  obtain ⟨w, c, hc, hodd, hclen, hcav⟩ := exists_short_odd_cycle_avoiding G
    (b + 3 * D + 3) d hconn hnonbip hd hdeg F hF
  have hcshort : c.length ≤ 6 * D := by nlinarith
  let C : Set V := {z | z ∈ c.support}
  have hC : C.Nontrivial := by
    refine ⟨w, c.start_mem_support, c.snd, ?_, (c.adj_snd hc.not_nil).ne⟩
    exact List.mem_of_mem_tail (Walk.snd_mem_tail_support hc.not_nil)
  have hCS (z : V) (hz : z ∈ C) : z ∉ S₀ := by
    intro hzS
    exact hcav z hz (mem_insert_of_mem (mem_insert_of_mem hzS))
  obtain ⟨x, hxC, y, hyC, p, q, hp, hq, hplen, hqlen, hxy, hpC, hqC, hpq, hpav, hqav⟩ :=
    exists_disjoint_short_attachments G (b + 3 * D + 3) d D hconn hd hdeg hN
      S₀ (by omega) C hC hCS u v (by simp [S₀]) (by simp [S₀]) huv
  obtain ⟨p₀, p₁, hp₀, hp₁, hpar, hlen₀, hlen₁, hs₀, hs₁⟩ :=
    exists_opposite_parity_paths_through_cycle c hc hodd p q hp hq hxC hyC hxy hpC hqC hpq
  let U := (p.support.toFinset ∪ q.support.toFinset) ∪ c.support.toFinset
  let T := (U.erase u).erase v
  have hmem {z : V} (hz : z ∈ p.support ∨ z ∈ q.support ∨ z ∈ c.support)
      (hzu : z ≠ u) (hzv : z ≠ v) : z ∈ T := by
    simp only [T, U, mem_erase, mem_union, List.mem_toFinset]
    exact ⟨hzv, hzu, by tauto⟩
  have hTsize : T.card ≤ 12 * D + 3 := by
    have hTle : T.card ≤ U.card :=
      card_le_card ((erase_subset v (U.erase u)).trans (erase_subset u U))
    have hUle : U.card ≤ p.support.toFinset.card + q.support.toFinset.card +
        c.support.toFinset.card :=
      (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    have hpcard := List.toFinset_card_le p.support
    have hqcard := List.toFinset_card_le q.support
    have hccard := List.toFinset_card_le c.support
    rw [p.length_support] at hpcard
    rw [q.length_support] at hqcard
    rw [c.length_support] at hccard
    omega
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro z hzS hzT
    simp only [T, U, mem_erase, mem_union, List.mem_toFinset] at hzT
    have hzS₀ : z ∈ S₀ := by
      simp only [S₀, mem_erase]
      exact ⟨hzT.1, hzT.2.1, hzS⟩
    rcases hzT.2.2 with (hzp | hzq) | hzc
    · exact hpav z hzp hzS₀
    · exact hqav z hzq hzS₀
    · exact hCS z hzc hzS₀
  refine ⟨T, ?_, hTsize, hST⟩
  intro r
  by_cases h : p₀.length % 2 = r.val
  · exact ⟨p₀, hp₀, by omega, h, fun z hz hzu hzv => hmem (hs₀ z hz) hzu hzv⟩
  · have hr : p₁.length % 2 = r.val := by have := r.isLt; omega
    exact ⟨p₁, hp₁, by omega, hr, fun z hz hzu hzv => hmem (hs₁ z hz) hzu hzv⟩

#print axioms exists_short_parity_connection_avoiding

end Erdos556
