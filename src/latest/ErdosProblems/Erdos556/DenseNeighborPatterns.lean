import ErdosProblems.Erdos556.CommonNeighbors

/-!
# A large common-neighbor class from degree bounds

Partition vertices by their complete neighborhood pattern on a fixed
small set. Double counting first gives many vertices with large patterns;
a largest pattern class then supplies a complete bipartite subgraph.
-/

namespace Erdos556

open Finset

theorem exists_large_common_neighbor_class {V : Type*} [Fintype V] [DecidableEq V]
    (D L d : ℕ) (hL : 0 < L) (hN : 0 < Fintype.card V)
    (hscale : Fintype.card V ≤ D * d)
    (S : Fin (2 * D * L) → Finset V) (hsize : ∀ i, d ≤ (S i).card) :
    ∃ (X : Finset (Fin (2 * D * L))) (W : Finset V),
      L ≤ X.card ∧ Fintype.card V ≤ 2 * D * 2 ^ (2 * D * L) * W.card ∧
      ∀ i ∈ X, ∀ v ∈ W, v ∈ S i := by
  classical
  let I := Fin (2 * D * L)
  let pattern (v : V) : Finset I := univ.filter (fun i => v ∈ S i)
  let A := univ.filter (fun v => L ≤ (pattern v).card)
  have hinc : (∑ i : I, (S i).card) = ∑ v : V, (pattern v).card := by
    have hs (i : I) : (S i).card = ∑ v : V, if v ∈ S i then 1 else 0 := by simp
    have hp (v : V) : (pattern v).card = ∑ i : I, if v ∈ S i then 1 else 0 := by
      simp [pattern]
    simp_rw [hs, hp]
    exact sum_comm
  have hlower : (2 * D * L) * d ≤ ∑ v : V, (pattern v).card := by
    rw [← hinc]
    calc
      (2 * D * L) * d = ∑ _i : I, d := by simp [I]
      _ ≤ ∑ i : I, (S i).card := sum_le_sum fun i _ => hsize i
  have hpoint (v : V) : (pattern v).card ≤ L + if v ∈ A then 2 * D * L else 0 := by
    by_cases hv : v ∈ A
    · rw [if_pos hv]
      have h := card_le_univ (pattern v)
      simp only [I, Fintype.card_fin] at h
      omega
    · rw [if_neg hv]
      have h : ¬ L ≤ (pattern v).card := by simpa only [A, mem_filter, mem_univ, true_and] using hv
      omega
  have hupper : (∑ v : V, (pattern v).card) ≤ L * Fintype.card V + (2 * D * L) * A.card := by
    calc
      (∑ v : V, (pattern v).card) ≤ ∑ v : V, (L + if v ∈ A then 2 * D * L else 0) :=
        sum_le_sum fun v _ => hpoint v
      _ = L * Fintype.card V + (2 * D * L) * A.card := by
        simp [sum_add_distrib, Nat.mul_comm]
  have hA : Fintype.card V ≤ 2 * D * A.card := by
    have hscaled := Nat.mul_le_mul_left (2 * L) hscale
    have h : L * Fintype.card V ≤ L * (2 * D * A.card) := by
      nlinarith only [hlower, hupper, hscaled]
    exact (mul_le_mul_iff_right₀ hL).mp h
  let fiber (X : Finset I) := A.filter (fun v => pattern v = X)
  obtain ⟨X, _, hmax⟩ := exists_max_image (univ : Finset (Finset I))
    (fun X => (fiber X).card) univ_nonempty
  have hfib : A.card = ∑ X : Finset I, (fiber X).card :=
    card_eq_sum_card_fiberwise (fun v _ => mem_univ (pattern v))
  have hbound : A.card ≤ 2 ^ (2 * D * L) * (fiber X).card := by
    rw [hfib]
    calc
      (∑ Y : Finset I, (fiber Y).card) ≤ ∑ _Y : Finset I, (fiber X).card :=
        sum_le_sum fun Y _ => hmax Y (mem_univ Y)
      _ = 2 ^ (2 * D * L) * (fiber X).card := by simp [I]
  have hlarge : Fintype.card V ≤ 2 * D * 2 ^ (2 * D * L) * (fiber X).card := by
    calc
      Fintype.card V ≤ 2 * D * A.card := hA
      _ ≤ 2 * D * (2 ^ (2 * D * L) * (fiber X).card) := Nat.mul_le_mul_left _ hbound
      _ = 2 * D * 2 ^ (2 * D * L) * (fiber X).card := by ring
  have hnon : (fiber X).Nonempty := by
    apply card_pos.mp
    by_contra h
    have hz : (fiber X).card = 0 := by omega
    rw [hz, mul_zero] at hlarge
    omega
  obtain ⟨v, hv⟩ := hnon
  have hvA := (mem_filter.mp hv).1
  have hvX := (mem_filter.mp hv).2
  have hX : L ≤ X.card := by
    rw [← hvX]
    exact (mem_filter.mp hvA).2
  refine ⟨X, fiber X, hX, hlarge, ?_⟩
  intro i hi v hv
  have hpat := (mem_filter.mp hv).2
  have hi' : i ∈ pattern v := by rw [hpat]; exact hi
  exact (mem_filter.mp hi').2

#print axioms exists_large_common_neighbor_class

theorem exists_complete_bipartite_from_degree_pattern {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D L d : ℕ) (hL : 0 < L)
    (hN : 0 < Fintype.card V) (hscale : Fintype.card V ≤ D * d)
    (hdegree : ∀ v, d ≤ G.degree v) (a : Fin (2 * D * L) ↪ V) :
    ∃ X W : Finset V, X.card = L ∧ X ⊆ univ.map a ∧ Disjoint X W ∧
      Fintype.card V ≤ 2 * D * 2 ^ (2 * D * L) * W.card ∧
      ∀ x ∈ X, ∀ w ∈ W, G.Adj x w := by
  classical
  obtain ⟨I, W, hI, hW, hcommon⟩ := exists_large_common_neighbor_class D L d hL hN hscale
    (fun i => G.neighborFinset (a i)) (fun i => by
      simpa only [G.card_neighborFinset_eq_degree] using hdegree (a i))
  obtain ⟨J, hJI, hJ⟩ := exists_subset_card_eq hI
  have hadj (x : V) (hx : x ∈ J.map a) (w : V) (hw : w ∈ W) : G.Adj x w := by
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
    exact (G.mem_neighborFinset _ _).mp (hcommon i (hJI hi) w hw)
  refine ⟨J.map a, W, by simpa only [card_map] using hJ, map_subset_map.mpr (subset_univ _),
    ?_, hW, hadj⟩
  rw [Finset.disjoint_left]
  intro x hx hw
  exact (hadj x hx x hw).ne rfl

#print axioms exists_complete_bipartite_from_degree_pattern

end Erdos556
