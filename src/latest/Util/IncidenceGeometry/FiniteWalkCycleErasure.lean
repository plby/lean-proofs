import Mathlib.Combinatorics.SimpleGraph.Paths
import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma FiniteWalkCycleErasure {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) {u v : V} (p : G.Walk u v) (huv : u ≠ v) :
    ∃ q : G.Walk u v,
      q.IsPath ∧
        q.support.Nodup ∧
          q.support.head? = some u ∧
            q.support.getLast? = some v ∧
              2 ≤ q.support.length ∧
                q.support ⊆ p.support ∧
                  q.edges ⊆ p.edges := by
  let q : G.Walk u v := p.bypass
  refine ⟨q, p.bypass_isPath, p.bypass_isPath.support_nodup, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_eq_some_head q.support_ne_nil]
    simp [q]
  · rw [List.getLast?_eq_getLast_of_ne_nil q.support_ne_nil]
    simp [q]
  · have hnon : ¬ q.Nil := SimpleGraph.Walk.not_nil_of_ne huv
    have hpos : 0 < q.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp hnon
    rw [SimpleGraph.Walk.length_support]
    omega
  · exact p.support_bypass_subset
  · exact p.edges_bypass_subset

