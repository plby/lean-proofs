import ErdosProblems.Erdos556.OrePath
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Elementary path bounds

These lemmas supply the longest-path argument and the edge-density path bound
used by the reservoir and nonbipartite-block arguments.
-/

namespace Erdos556

open SimpleGraph

theorem exists_two_edge_path {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (hu : 2 ≤ G.degree u) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ p.length = 2 := by
  have hnb : 1 < (G.neighborFinset u).card := by
    rw [card_neighborFinset_eq_degree]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hnb
  have hua : G.Adj u a := (G.mem_neighborFinset u a).mp ha
  have hub : G.Adj u b := (G.mem_neighborFinset u b).mp hb
  let p := Walk.cons hua.symm (Walk.cons hub Walk.nil)
  refine ⟨a, b, p, ?_, rfl⟩
  simp [p, Walk.cons_isPath_iff, hua.ne.symm, hub.ne, hab]

/-- The standard connected longest-path bound, with a minimum-degree
parameter at least two. The conclusion counts vertices of the path. -/
theorem exists_long_path_of_min_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (d : ℕ) (hd : 2 ≤ d) (hdeg : ∀ v, d ≤ G.degree v) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧
      min (2 * d + 1) (Fintype.card V) ≤ p.length + 1 := by
  classical
  have : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨u, v, p, hp, ?_⟩
  by_contra hlong
  have hshort : p.length + 1 < min (2 * d + 1) (Fintype.card V) := by omega
  obtain ⟨a, b, q, hq, hqlen⟩ := exists_two_edge_path G u (hd.trans (hdeg u))
  have hlen : 2 ≤ p.length := by
    have h := hmax a b q hq
    omega
  have hham := longest_path_hamiltonian_of_endpoint_degree_sum G hconn p hp
    (fun {_ _} q hq => hmax _ _ q hq) hlen (by
      have hu := hdeg u
      have hv := hdeg v
      omega)
  obtain ⟨z, q, hq⟩ := hham (by omega)
  have h := hmax _ _ q.tail hq.isCycle.isPath_tail
  rw [Walk.length_tail, hq.length_eq] at h
  omega

theorem degree_le_one_of_path_length_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmax : ∀ {u v} (p : G.Walk u v), p.IsPath → p.length ≤ 1) (v : V) :
    G.degree v ≤ 1 := by
  by_contra h
  obtain ⟨a, b, p, hp, hlen⟩ := exists_two_edge_path G v (by omega)
  have := hmax p hp
  omega

theorem degree_eq_zero_of_path_length_le_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmax : ∀ {u v} (p : G.Walk u v), p.IsPath → p.length ≤ 0) (v : V) :
    G.degree v = 0 := by
  by_contra h
  have hn : (G.neighborFinset v).Nonempty := by
    rw [← Finset.card_pos, card_neighborFinset_eq_degree]
    omega
  obtain ⟨w, hw⟩ := hn
  have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
  have hp : (Walk.cons hadj Walk.nil).IsPath := by
    simp [Walk.cons_isPath_iff, hadj.ne]
  have := hmax _ hp
  simp only [Walk.length_cons, Walk.length_nil] at this
  omega

/-- Degrees do not change when passing to a whole connected component. -/
theorem degree_component {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.ConnectedComponent)
    [Fintype C] [DecidableRel C.toSimpleGraph.Adj] (v : C) :
    C.toSimpleGraph.degree v = G.degree v.val := by
  let e : C.toSimpleGraph.neighborSet v ≃ G.neighborSet v.val :=
    { toFun := fun w => ⟨w.val.val, w.property⟩
      invFun := fun w => ⟨⟨w.val, C.mem_supp_of_adj_mem_supp v.property w.property⟩,
        w.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact Fintype.card_congr e

/-- If all degrees exceed half a path-length bound, every connected
component is small enough that all degrees are at most that bound. -/
theorem degree_le_path_bound_of_min_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 2 ≤ k)
    (hmin : ∀ v, k < 2 * G.degree v)
    (hmax : ∀ {u v} (p : G.Walk u v), p.IsPath → p.length ≤ k) (v : V) :
    G.degree v ≤ k := by
  classical
  let C := G.connectedComponentMk v
  have hd : ∀ w : C, k / 2 + 1 ≤ C.toSimpleGraph.degree w := by
    intro w
    rw [degree_component]
    have h := hmin w.val
    omega
  obtain ⟨a, b, p, hp, hlen⟩ := exists_long_path_of_min_degree C.toSimpleGraph
    C.connected_toSimpleGraph (k / 2 + 1) (by omega) hd
  have hp' : (p.map C.toSimpleGraph_hom).IsPath :=
    hp.map (by intro x y h; exact Subtype.ext h)
  have hbound := hmax _ hp'
  rw [Walk.length_map] at hbound
  have hcard : Fintype.card C ≤ k + 1 := by omega
  let v' : C := ⟨v, ConnectedComponent.connectedComponentMk_mem⟩
  have hdeg := C.toSimpleGraph.degree_lt_card_verts v'
  rw [degree_component] at hdeg
  exact Nat.le_of_lt_succ (hdeg.trans_le hcard)

#print axioms exists_long_path_of_min_degree
#print axioms degree_le_path_bound_of_min_degree

theorem twice_edges_le_of_degree_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hdeg : ∀ v, G.degree v ≤ k) :
    2 * G.edgeFinset.card ≤ k * Fintype.card V := by
  calc
    2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
    _ ≤ ∑ _v : V, k := Finset.sum_le_sum fun v _ => hdeg v
    _ = k * Fintype.card V := by simp [Nat.mul_comm]

universe u

private theorem path_edge_bound_aux (N : ℕ) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], Fintype.card V = N →
      ∀ k : ℕ,
      (∀ {a b : V} (p : G.Walk a b), p.IsPath → p.length ≤ k) →
      2 * G.edgeFinset.card ≤ k * Fintype.card V := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro V _ _ G _ hcard k hmax
      classical
      by_cases hsmall : k ≤ 1
      · apply twice_edges_le_of_degree_le G k
        intro v
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsmall with rfl | rfl
        · exact (degree_eq_zero_of_path_length_le_zero G hmax v).le
        · exact degree_le_one_of_path_length_le_one G hmax v
      · have hk : 2 ≤ k := by omega
        by_cases hlow : ∃ v, 2 * G.degree v ≤ k
        · obtain ⟨v, hv⟩ := hlow
          let S : Set V := {v}ᶜ
          let H := G.induce S
          have hS : Fintype.card S = Fintype.card V - 1 := by
            simpa [S] using Set.card_ne_eq v
          have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
          have hlt : Fintype.card S < N := by omega
          have hmaxH : ∀ {a b : S} (p : H.Walk a b), p.IsPath → p.length ≤ k := by
            intro a b p hp
            let f := (Embedding.induce (G := G) S).toHom
            have hp' : (p.map f).IsPath := hp.map (by
              intro x y h
              exact Subtype.ext h)
            simpa only [Walk.length_map] using hmax (p.map f) hp'
          have hrec := ih (Fintype.card S) hlt S H rfl k hmaxH
          have hedge : H.edgeFinset.card + G.degree v = G.edgeFinset.card := by
            dsimp [H, S]
            rw [card_edgeFinset_induce_compl_singleton,
              card_edgeFinset_deleteIncidenceSet]
            exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)
          have hcardadd : Fintype.card S + 1 = Fintype.card V := by omega
          nlinarith
        · apply twice_edges_le_of_degree_le G k
          apply degree_le_path_bound_of_min_degree G k hk
          · intro v
            by_contra h
            exact hlow ⟨v, by omega⟩
          · exact hmax

/-- The finite Erdős--Gallai path edge bound. -/
theorem path_edge_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hmax : ∀ {a b : V} (p : G.Walk a b), p.IsPath → p.length ≤ k) :
    2 * G.edgeFinset.card ≤ k * Fintype.card V :=
  path_edge_bound_aux (Fintype.card V) V G rfl k hmax

/-- Strict edge density forces a path longer than the given integer bound. -/
theorem exists_path_of_twice_edges_gt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (he : k * Fintype.card V < 2 * G.edgeFinset.card) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ k < p.length := by
  by_contra h
  push Not at h
  have hb := path_edge_bound G k (fun p hp => h _ _ p hp)
  omega

#print axioms path_edge_bound
#print axioms exists_path_of_twice_edges_gt

end Erdos556
