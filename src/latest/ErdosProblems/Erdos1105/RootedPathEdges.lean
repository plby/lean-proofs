import ErdosProblems.Erdos1105.CycleCutSupport
import ErdosProblems.Erdos1105.SetPath
import ErdosProblems.Erdos1105.PathCycleSplice
import ErdosProblems.Erdos767.Dirac

namespace Erdos1105

open SimpleGraph

/-- A cycle in a connected graph can be reached from any specified root,
then opened into a path containing all its vertices. -/
theorem rooted_path_length_ge_cycle_pred {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (hconn : G.Preconnected) (v : V) {z : V}
    (p : G.Walk z z) (hp : p.IsCycle) :
    ∃ w, ∃ q : G.Walk v w, q.IsPath ∧ p.length ≤ q.length + 1 := by
  obtain ⟨r, hr⟩ := hconn.exists_isPath v z
  obtain ⟨a, ha, b, hb, r', hr', _, _, hmeet⟩ := exists_set_path_within G
    {v} {w | w ∈ p.support} Set.univ
    ⟨v, rfl, z, p.start_mem_support, r, hr, fun _ _ ↦ Set.mem_univ _⟩
  have hav : a = v := ha
  subst a
  obtain ⟨w, s, hs, hslen, hsub, _⟩ := cycle_path_from_vertex p hp hb
  have hq : (r'.append s).IsPath := by
    apply isPath_append_of_inter_eq_end hr' hs
    intro x hx hy
    exact hmeet x hx (hsub hy)
  refine ⟨w, r'.append s, hq, ?_⟩
  rw [Walk.length_append]
  omega

/-- A rooted-path bound gives a circumference bound, and hence the sharp
Erdős--Gallai edge bound. This is the counting input for the two-attachment
case of the low-core stability argument. -/
theorem edges_le_of_rooted_path_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Preconnected)
    (v : V) {d : ℕ} (hd : 1 ≤ d)
    (hpath : ∀ w, ∀ p : G.Walk v w, p.IsPath → p.length ≤ d) :
    2 * G.edgeFinset.card ≤ (d + 1) * (Fintype.card V - 1) := by
  apply Erdos767Dirac.erdosGallai_cycle G (d + 1) (by omega)
  intro z p hp
  obtain ⟨w, q, hq, hlen⟩ := rooted_path_length_ge_cycle_pred hconn v p hp
  have := hpath w q hq
  omega

end Erdos1105

#print axioms Erdos1105.edges_le_of_rooted_path_bound
