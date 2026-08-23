import ErdosProblems.Erdos1105.HamiltonianConnected

namespace Erdos1105

open SimpleGraph

/-- A Hamiltonian graph has a simple path of every shorter length,
starting at any specified vertex. -/
theorem exists_path_length_from_hamiltonian {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsHamiltonian) (hcard : 3 ≤ Fintype.card V)
    (a : V) (m : ℕ) (hm : m < Fintype.card V) :
    ∃ b, ∃ p : G.Walk a b, p.IsPath ∧ p.length = m := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨q, hq⟩ := hG.exists_isHamiltonianCycle a
  refine ⟨q.dropLast.getVert m, q.dropLast.take m, hq.isCycle.isPath_dropLast.take m, ?_⟩
  rw [Walk.take_length, Walk.length_dropLast, hq.length_eq]
  exact min_eq_left (by omega)

/-- If every Hamiltonian path has equal endpoint labels, then all vertex
labels agree. Apply the hypothesis to tails of rotated Hamiltonian cycles. -/
theorem constant_of_hamiltonian_path_endpoints {V D : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsHamiltonian) (hcard : 3 ≤ Fintype.card V) (F : V → D)
    (hF : ∀ a b (p : G.Walk a b), p.IsHamiltonian → F a = F b) (a b : V) : F a = F b := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨q, hq⟩ := hG.exists_isHamiltonianCycle a
  have hstep (i : ℕ) (hi : i < q.length) : F (q.getVert (i + 1)) = F (q.getVert i) := by
    let v := q.getVert i
    have hv : v ∈ q.support := q.getVert_mem_support i
    let r := q.rotate v hv
    have hr : r.IsHamiltonianCycle := hq.rotate hv
    have hlabels : F r.snd = F v := hF r.snd v r.tail hr.isHamiltonian_tail
    have hnext : q.getVert (i + 1) = hq.next v := hq.getVert_succ_eq_next v hi rfl
    have hrnext : r.snd = hr.next v := hr.getVert_succ_eq_next v
      (i := 0) (by have := hr.isCycle.three_le_length; omega) r.getVert_zero
    have hrot : hr.next v = hq.next v := Walk.IsHamiltonianCycle.rotate_next v hq hv v
    rw [hnext, ← hrot, ← hrnext]
    exact hlabels
  have hall (i : ℕ) (hi : i ≤ q.length) : F (q.getVert i) = F a := by
    induction i with
    | zero => simp
    | succ i ih => exact (hstep i (by omega)).trans (ih (by omega))
  obtain ⟨i, hi, hilen⟩ := Walk.mem_support_iff_exists_getVert.mp (hq.mem_support b)
  have h := hall i hilen
  rw [hi] at h
  exact h.symm

lemma exists_third_vertex {V : Type*} [Fintype V] (hcard : 3 ≤ Fintype.card V) (a b : V) :
    ∃ v, v ≠ a ∧ v ≠ b := by
  classical
  by_contra! h
  have hsub : (Finset.univ : Finset V) ⊆ {a, b} := by
    intro v _
    by_cases hv : v = a
    · simp [hv]
    · simp [h v hv]
  have hle := Finset.card_le_card hsub
  have hpair := Finset.card_insert_le a ({b} : Finset V)
  simp only [Finset.card_singleton] at hpair
  rw [Finset.card_univ] at hle
  omega

end Erdos1105
