import ErdosProblems.Erdos1105.UniversalPosa
import ErdosProblems.Erdos1105.LongestSetPath

namespace Erdos1105

open SimpleGraph Finset

/-- In a saturated cone with no long cycle, the high-degree core is a
clique. This is the first structural step of Kopylov's disintegration proof. -/
theorem saturated_cone_core_isClique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {u : V} {k d : ℕ}
    (hG : NoLongCycle G k) (hk : 3 ≤ k) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (hmax : ∀ J : SimpleGraph V, G ≤ J → NoLongCycle J k → J = G)
    (hd : k ≤ 2 * (d + 1)) : G.IsClique (vertexCore G d : Set V) := by
  classical
  intro a ha b hb hab
  by_contra hnab
  obtain ⟨p₀, hp₀, hlen₀⟩ := long_path_of_saturated_nonedge G k hG hmax hab hnab
  obtain ⟨x, hx, y, hy, p, hp, hlong⟩ := exists_longest_path_between_sets G
    (vertexCore G d : Set V) (vertexCore G d : Set V) ⟨a, ha, b, hb, p₀, hp₀⟩
  have hplen : k ≤ p.length + 1 := by
    have h := hlong a ha b hb p₀ hp₀
    omega
  have hleft : ∀ w ∈ vertexCore G d, G.Adj x w → w ∈ p.support := by
    intro w hw hxw
    by_contra hwnot
    let q := Walk.cons hxw.symm p
    have hq : q.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hwnot⟩
    have h := hlong w hw y hy q hq
    simp only [q, Walk.length_cons] at h
    omega
  have hright : ∀ w ∈ vertexCore G d, G.Adj y w → w ∈ p.support := by
    intro w hw hyw
    by_contra hwnot
    have h := hlong x hx w hw (p.concat hyw) (hp.concat hwnot hyw)
    rw [Walk.length_concat] at h
    omega
  have hxdeg := (vertexCore_degree G d hx).trans_le
    (degreeWithin_le_of_neighbors_mem G (vertexCore G d) p.support.toFinset x
      (fun w hw hadj ↦ List.mem_toFinset.mpr (hleft w hw hadj)))
  have hydeg := (vertexCore_degree G d hy).trans_le
    (degreeWithin_le_of_neighbors_mem G (vertexCore G d) p.support.toFinset y
      (fun w hw hadj ↦ List.mem_toFinset.mpr (hright w hw hadj)))
  have h := universal_posa_degree_bound hG hk hu hconn p hp hplen
  omega

end Erdos1105

#print axioms Erdos1105.saturated_cone_core_isClique
