import ErdosProblems.Erdos556.DensePathShortening

/-!
# Repeated bounded shortening

Strong induction places a path in any requested length window while
preserving its endpoints, parity, and internal avoidance of a reservoir.
-/

namespace Erdos556

open SimpleGraph

theorem exists_path_in_length_window {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D d : ℕ) (hD : 0 < D)
    (hscale : Fintype.card V ≤ D * d) (hdegree : ∀ v, d ≤ G.degree v)
    (hN : 8 * (4 * D) ^ 2 ≤ Fintype.card V)
    (R : Finset V) (hR : 2 * (R.card + 16 * D + 1) ≤ d)
    (t : ℕ) (ht : 16 * D ≤ t) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hlen : t ≤ p.length)
    (hoff : ∀ z ∈ p.support, z ∈ R → z = u ∨ z = v) :
    ∃ q : G.Walk u v, q.IsPath ∧ q.length ≤ t ∧
      t < q.length + (16 * D + 8 * (4 * D) ^ 2) ∧
      q.length % 2 = p.length % 2 ∧
      ∀ z ∈ q.support, z ∈ R → z = u ∨ z = v := by
  have aux : ∀ M : ℕ, ∀ p : G.Walk u v, p.length = M → p.IsPath → t ≤ p.length →
      (∀ z ∈ p.support, z ∈ R → z = u ∨ z = v) →
      ∃ q : G.Walk u v, q.IsPath ∧ q.length ≤ t ∧
        t < q.length + (16 * D + 8 * (4 * D) ^ 2) ∧
        q.length % 2 = p.length % 2 ∧
        ∀ z ∈ q.support, z ∈ R → z = u ∨ z = v := by
    intro M
    induction M using Nat.strong_induction_on with
    | h M ih =>
        intro p hpM hp htP hoff
        by_cases hstop : p.length ≤ t
        · exact ⟨p, hp, hstop, by omega, rfl, hoff⟩
        obtain ⟨q, hq, hlt, hbound, hpar, hsupp⟩ :=
          exists_shorter_same_parity_path_of_min_degree G D d hD hscale hdegree hN R hR
            p hp (by omega)
        have hoffq : ∀ z ∈ q.support, z ∈ R → z = u ∨ z = v := by
          intro z hz hzR
          rcases hsupp z hz with hzp | hzoff
          · exact hoff z hzp hzR
          · exact (hzoff hzR).elim
        by_cases htq : t ≤ q.length
        · obtain ⟨w, hw, hwt, hwin, hwpar, hwoff⟩ :=
            ih q.length (by omega) q rfl hq htq hoffq
          exact ⟨w, hw, hwt, hwin, hwpar.trans hpar, hwoff⟩
        · exact ⟨q, hq, by omega, by omega, hpar, hoffq⟩
  exact aux p.length p rfl hp hlen hoff

#print axioms exists_path_in_length_window

end Erdos556
