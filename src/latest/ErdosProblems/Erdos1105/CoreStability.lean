import ErdosProblems.Erdos1105.CoreClique
import ErdosProblems.Erdos1105.CoreBasics

namespace Erdos1105

open SimpleGraph Finset

/-- Once the high-degree core of a saturated cone is a clique, lowering
the disintegration threshold to `k - r` does not enlarge it. -/
theorem saturated_cone_core_stable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {u : V} {k d : ℕ}
    (hG : NoLongCycle G k) (hk : 3 ≤ k) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (hmax : ∀ J : SimpleGraph V, G ≤ J → NoLongCycle J k → J = G)
    (hclique : G.IsClique (vertexCore G d : Set V))
    (hne : (vertexCore G d).Nonempty)
    (hrk : (vertexCore G d).card ≤ k)
    (hthreshold : k - (vertexCore G d).card ≤ d) :
    vertexCore G (k - (vertexCore G d).card) = vertexCore G d := by
  classical
  let H := vertexCore G d
  let a := k - H.card
  have hsub : H ⊆ vertexCore G a := vertexCore_antitone G hthreshold
  apply Subset.antisymm ?_ hsub
  intro v hv
  by_contra hvH
  have hex : ∃ w ∈ H, ¬G.Adj v w := by
    by_contra! h
    exact hvH (mem_vertexCore_of_all_adj G d hne h)
  obtain ⟨w, hw, hvw⟩ := hex
  have hne_vw : v ≠ w := fun h ↦ hvH (h ▸ hw)
  obtain ⟨p₀, hp₀, hlen₀⟩ := long_path_of_saturated_nonedge G k hG hmax hne_vw hvw
  obtain ⟨x, hx, y, hy, p, hp, hlong⟩ := exists_longest_path_between_sets G
    ((vertexCore G a : Set V) \ (H : Set V)) (H : Set V)
    ⟨v, ⟨hv, hvH⟩, w, hw, p₀, hp₀⟩
  have hplen : k ≤ p.length + 1 := by
    have h := hlong v ⟨hv, hvH⟩ w hw p₀ hp₀
    omega
  have hleft : ∀ z ∈ vertexCore G a, G.Adj x z → z ∈ p.support := by
    intro z hz hxz
    by_contra hznot
    let q := Walk.cons hxz.symm p
    have hq : q.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hznot⟩
    by_cases hzH : z ∈ H
    · have hzy : z ≠ y := fun h ↦ hznot (h ▸ p.end_mem_support)
      have hadj := hclique hzH hy hzy
      exact long_path_endpoints_not_adjacent hG hk q hq
        (by simp only [q, Walk.length_cons]; omega) hadj
    · have h := hlong z ⟨hz, hzH⟩ y hy q hq
      simp only [q, Walk.length_cons] at h
      omega
  have hright : ∀ z ∈ H, G.Adj y z → z ∈ p.support := by
    intro z hz hyz
    by_contra hznot
    have h := hlong x hx z hz (p.concat hyz) (hp.concat hznot hyz)
    rw [Walk.length_concat] at h
    omega
  have hxdeg := (vertexCore_degree G a hx.1).trans_le
    (degreeWithin_le_of_neighbors_mem G (vertexCore G a) p.support.toFinset x
      (fun z hz hadj ↦ List.mem_toFinset.mpr (hleft z hz hadj)))
  have hydeg := degreeWithin_le_of_neighbors_mem G H p.support.toFinset y
    (fun z hz hadj ↦ List.mem_toFinset.mpr (hright z hz hadj))
  rw [degreeWithin_clique G hclique hy] at hydeg
  have h := universal_posa_degree_bound hG hk hu hconn p hp hplen
  have hcard := vertexCore_card_lower G d hne
  dsimp only [a, H] at *
  omega

end Erdos1105

#print axioms Erdos1105.saturated_cone_core_stable
