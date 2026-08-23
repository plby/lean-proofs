import ErdosProblems.Erdos551.Erdos551BondyChvatal
import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

open SimpleGraph

/-- Ore's criterion with the standard restriction to distinct vertices. -/
theorem hamiltonian_of_distinct_degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : 3 ≤ Fintype.card V)
    (hdeg : ∀ u v, u ≠ v → Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian := by
  classical
  have hclosure : G.closure = ⊤ := by
    apply le_antisymm le_top
    intro u v hne
    apply G.closure_spec hne
    exact (hdeg u v hne).trans (Nat.add_le_add
      (G.degree_le_of_le (v := u) G.self_le_closure)
      (G.degree_le_of_le (v := v) G.self_le_closure))
  apply (SimpleGraph.from_closure_iff (G := G)).mp
  rw [hclosure]
  apply SimpleGraph.dirac_theorem hV
  intro v
  rw [((⊤ : SimpleGraph V).degree_eq_card_sub_one v).mpr (by simp [IsUniversal])]
  omega

/-- The endpoint form of Ore's theorem, obtained from Bondy--Chvátal closure. -/
theorem hamiltonian_of_endpoint_degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (p : G.Walk u v) (hp : p.IsHamiltonian)
    (hcard : 3 ≤ Fintype.card V) (hdeg : Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian := by
  classical
  have hlen := hp.length_eq
  have hlen₂ : 2 ≤ p.length := by omega
  have hne : u ≠ v := by
    intro h
    have heq : p.getVert 0 = p.getVert p.length := by simpa using h
    have hi : 0 = p.length := hp.isPath.getVert_injOn (by simp) (by simp) heq
    omega
  have hcl := G.self_le_closure
  have hcladj : G.closure.Adj u v := G.closure_spec hne
    (hdeg.trans (Nat.add_le_add (G.degree_le_of_le (v := u) hcl)
      (G.degree_le_of_le (v := v) hcl)))
  have hsub : ∀ e ∈ p.edges, e ∈ G.closure.edgeSet :=
    fun _ he ↦ edgeSet_mono hcl (p.edges_subset_edgeSet he)
  let p' := p.transfer G.closure hsub
  have hp' : p'.IsHamiltonian := by
    apply (hp.isPath.transfer hsub).isHamiltonian_of_mem
    intro x
    rw [Walk.support_transfer]
    exact hp.mem_support x
  let q := Walk.cons hcladj.symm p'
  have hq : q.IsCycle := by
    apply (Walk.cons_isCycle_iff p' hcladj.symm).mpr
    refine ⟨hp'.isPath, ?_⟩
    intro he
    have h := hp'.isPath.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    have hp'len : p'.length = p.length := Walk.length_transfer p hsub
    omega
  have hqham : q.IsHamiltonianCycle := by
    apply Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
    refine ⟨hq, ?_⟩
    dsimp only [q, p']
    rw [Walk.length_cons, Walk.length_transfer]
    omega
  exact (SimpleGraph.from_closure_iff (G := G)).mp (fun _ ↦ ⟨v, q, hqham⟩)

/-- The endpoint criterion also applies to a path inside a larger graph:
degrees here count only neighbors lying on the path. -/
theorem cycle_contained_in_support_of_path_endpoint_degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hlen : 2 ≤ p.length)
    (hdeg : p.length + 1 ≤
      (G.induce {x | x ∈ p.support}).degree ⟨u, p.start_mem_support⟩ +
      (G.induce {x | x ∈ p.support}).degree ⟨v, p.end_mem_support⟩) :
    cycleGraph (p.length + 1) ⊑ G.induce {x | x ∈ p.support} := by
  classical
  let S : Set V := {x | x ∈ p.support}
  let p' := p.induce S (fun _ hx ↦ hx)
  have hp' : p'.IsPath := by
    apply (Walk.isPath_map_iff_of_injective (f := (Embedding.induce (G := G) S).toHom)
      (p := p') (Embedding.induce (G := G) S).injective).mp
    rw [Walk.map_induce]
    exact hp
  have hham : p'.IsHamiltonian := by
    apply hp'.isHamiltonian_of_mem
    intro x
    rw [Walk.support_induce]
    simpa only [List.mem_attachWith] using (show x.val ∈ p.support from x.property)
  have hcard : Fintype.card S = p.length + 1 := by
    have hS : S = (p.support.toFinset : Set V) := by ext x; simp [S]
    calc
      Fintype.card S = S.ncard := Nat.card_eq_fintype_card.symm
      _ = p.support.toFinset.card := by rw [hS, Set.ncard_coe_finset]
      _ = p.length + 1 := by
        rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]
  have hG := hamiltonian_of_endpoint_degree_sum (G.induce S) p' hham
    (by rw [hcard]; omega) (by rw [hcard]; exact hdeg)
  obtain ⟨z, q, hq⟩ := hG (by rw [hcard]; omega)
  have hc : cycleGraph (p.length + 1) ⊑ G.induce S :=
    (cycleGraph_isContained_iff (by omega)).mpr
      ⟨z, q, hq.isCycle, hq.length_eq.trans hcard⟩
  exact hc

theorem cycle_contained_of_path_endpoint_degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hlen : 2 ≤ p.length)
    (hdeg : p.length + 1 ≤
      (G.induce {x | x ∈ p.support}).degree ⟨u, p.start_mem_support⟩ +
      (G.induce {x | x ∈ p.support}).degree ⟨v, p.end_mem_support⟩) :
    cycleGraph (p.length + 1) ⊑ G :=
  (cycle_contained_in_support_of_path_endpoint_degree_sum G p hp hlen hdeg).trans
    (Embedding.induce {x | x ∈ p.support}).isContained

/-- Closing a simple path gives a cycle inside exactly its support. -/
theorem cycle_contained_in_support_of_endpoint_adj {V : Type*}
    (G : SimpleGraph V) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hlen : 2 ≤ p.length) (hclose : G.Adj v u) :
    cycleGraph (p.length + 1) ⊑ G.induce {x | x ∈ p.support} := by
  let S : Set V := {x | x ∈ p.support}
  let p' := p.induce S (fun _ hx ↦ hx)
  have hp' : p'.IsPath := by
    apply (Walk.isPath_map_iff_of_injective (f := (Embedding.induce (G := G) S).toHom)
      (p := p') (Embedding.induce (G := G) S).injective).mp
    rw [Walk.map_induce]
    exact hp
  have hclose' : (G.induce S).Adj ⟨v, p.end_mem_support⟩ ⟨u, p.start_mem_support⟩ := hclose
  have hlenp : p'.length = p.length := by
    rw [← Walk.length_map (Embedding.induce (G := G) S).toHom p', Walk.map_induce]
    rfl
  let q := Walk.cons hclose' p'
  have hq : q.IsCycle := by
    apply (Walk.cons_isCycle_iff p' hclose').mpr
    refine ⟨hp', ?_⟩
    intro he
    have h := hp'.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    rw [hlenp] at h
    omega
  apply (cycleGraph_isContained_iff (by omega)).mpr
  exact ⟨_, q, hq, by rw [Walk.length_cons, hlenp]⟩

/-- In a connected graph, a cycle longer than every simple path must span
the graph: an external neighbor would extend a rotated cycle tail. -/
theorem hamiltonian_of_cycle_longer_than_paths {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) {v : V} (q : G.Walk v v) (hq : q.IsCycle)
    (hmax : ∀ {a b : V} (p : G.Walk a b), p.IsPath → p.length < q.length) :
    G.IsHamiltonian := by
  classical
  have hall : ∀ x, x ∈ q.support := by
    intro x
    by_contra hx
    obtain ⟨p⟩ := hconn.preconnected v x
    obtain ⟨d, _, hd, hdout⟩ := p.exists_boundary_dart {z | z ∈ q.support}
      q.start_mem_support hx
    let r := q.rotate d.fst hd
    have hr : r.IsCycle := hq.rotate hd
    have houts : d.snd ∉ r.tail.support := by
      intro hmem
      have hmem' : d.snd ∈ r.support := by
        rw [← Walk.cons_support_tail hr.not_nil]
        exact List.mem_cons_of_mem _ hmem
      exact hdout ((q.mem_support_rotate_iff d.fst hd).mp hmem')
    have hp' := hr.isPath_tail.concat houts d.adj
    have hlt := hmax _ hp'
    have heq : (r.tail.concat d.adj).length = q.length := by
      rw [Walk.length_concat, Walk.length_tail, Walk.length_rotate]
      exact Nat.sub_add_cancel (by have := hq.three_le_length; omega)
    rw [heq] at hlt
    exact hlt.false
  refine fun _ ↦ ⟨v, q, ⟨hq, ?_⟩⟩
  apply hq.isPath_tail.isHamiltonian_of_mem
  intro x
  have hx := hall x
  rw [← Walk.cons_tail_support q] at hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact q.tail.end_mem_support
  · rwa [Walk.support_tail_of_not_nil q hq.not_nil]

lemma degree_induce_eq_of_neighbors_mem {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)]
    (v : V) (hv : v ∈ S) (hwithin : ∀ w, G.Adj v w → w ∈ S) :
    (G.induce S).degree ⟨v, hv⟩ = G.degree v := by
  let e : (G.induce S).neighborSet ⟨v, hv⟩ ≃ G.neighborSet v :=
    { toFun := fun w ↦ ⟨w.val.val, w.property⟩
      invFun := fun w ↦ ⟨⟨w.val, hwithin w.val w.property⟩, w.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact Fintype.card_congr e

/-- Ore's endpoint criterion for a longest path in a connected graph. -/
theorem longest_path_hamiltonian_of_endpoint_degree_sum {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hmax : ∀ {a b : V} (q : G.Walk a b), q.IsPath → q.length ≤ p.length)
    (hlen : 2 ≤ p.length) (hdeg : p.length + 1 ≤ G.degree u + G.degree v) :
    G.IsHamiltonian := by
  classical
  have hstart : ∀ w, G.Adj u w → w ∈ p.support := by
    intro w hw
    by_contra hnot
    have hq : (Walk.cons hw.symm p).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hnot⟩
    have h := hmax _ hq
    simp only [Walk.length_cons] at h
    omega
  have hend : ∀ w, G.Adj v w → w ∈ p.support := by
    intro w hw
    by_contra hnot
    have h := hmax _ (hp.concat hnot hw)
    simp only [Walk.length_concat] at h
    omega
  have hcopy := cycle_contained_of_path_endpoint_degree_sum G p hp hlen (by
    rw [degree_induce_eq_of_neighbors_mem G {x | x ∈ p.support} u p.start_mem_support hstart,
      degree_induce_eq_of_neighbors_mem G {x | x ∈ p.support} v p.end_mem_support hend]
    exact hdeg)
  obtain ⟨x, q, hq, hqlen⟩ := (cycleGraph_isContained_iff (by omega)).mp hcopy
  apply hamiltonian_of_cycle_longer_than_paths G hconn q hq
  intro a b r hr
  rw [hqlen]
  exact Nat.lt_succ_of_le (hmax r hr)

/-- The connected degree-sum criterion supplies a long path whenever the
component has enough vertices. -/
theorem path_contained_of_degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (k : ℕ) (hk : 3 ≤ k) (hcard : k ≤ Fintype.card V)
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hdeg : ∀ u v, u ≠ v → k - 1 ≤ G.degree u + G.degree v) :
    pathGraph k ⊑ G := by
  classical
  have : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  by_cases hlong : k ≤ p.length + 1
  · exact ⟨hp.pathGraphCopy.comp (pathCopyOfLE hlong)⟩
  have hlen : 2 ≤ p.length := by
    have hnb : 1 < (G.neighborFinset u).card := by
      rw [card_neighborFinset_eq_degree]
      have := hmin u
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hnb
    have hua : G.Adj u a := (G.mem_neighborFinset u a).mp ha
    have hub : G.Adj u b := (G.mem_neighborFinset u b).mp hb
    let p₂ := Walk.cons hua.symm (Walk.cons hub Walk.nil)
    have hp₂ : p₂.IsPath := by
      simp [p₂, Walk.cons_isPath_iff, hua.ne.symm, hub.ne, hab]
    have h := hmax _ _ p₂ hp₂
    simpa only [p₂, Walk.length_cons, Walk.length_nil] using h
  have huv : u ≠ v := by
    intro h
    have heq : p.getVert 0 = p.getVert p.length := by simpa using h
    have hi : 0 = p.length := hp.getVert_injOn (by simp) (by simp) heq
    omega
  have hG := longest_path_hamiltonian_of_endpoint_degree_sum G hconn p hp
    (fun {_ _} q hq ↦ hmax _ _ q hq) hlen (by have := hdeg u v huv; omega)
  obtain ⟨z, q, hq⟩ := hG (by omega)
  have hbound := hmax _ _ q.tail hq.isCycle.isPath_tail
  rw [Walk.length_tail, hq.length_eq] at hbound
  omega

#print axioms hamiltonian_of_endpoint_degree_sum
#print axioms cycle_contained_of_path_endpoint_degree_sum
#print axioms hamiltonian_of_cycle_longer_than_paths
#print axioms longest_path_hamiltonian_of_endpoint_degree_sum
#print axioms path_contained_of_degree_sum

end Erdos1105
