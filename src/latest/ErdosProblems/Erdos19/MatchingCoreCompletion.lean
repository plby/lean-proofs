import ErdosProblems.Erdos19.MatchingColorCompletion
import ErdosProblems.Erdos19.MatchingCoreColoring
import ErdosProblems.Erdos19.PairColoring

/-! # Completing packed matchings with a degree-sized residual palette -/

namespace Erdos19

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem exists_edgeLabeling_from_matchings_and_residual
    {V I K : Type*} [Fintype V] (G : _root_.SimpleGraph V)
    (M : I → G.Subgraph) (hM : ∀ i, (M i).IsMatching)
    (c₀ : (G \ ⨆ i, (M i).spanningCoe).EdgeLabeling K)
    (hc₀ : ∀ x y z (hxy : (G \ ⨆ i, (M i).spanningCoe).Adj x y)
      (hxz : (G \ ⨆ i, (M i).spanningCoe).Adj x z),
      c₀.get x y hxy = c₀.get x z hxz → y = z) :
    ∃ c : G.EdgeLabeling (I ⊕ K),
      (∀ x y z (hxy : G.Adj x y) (hxz : G.Adj x z),
        c.get x y hxy = c.get x z hxz → y = z) ∧
      (∀ (e : G.edgeSet) (i : I), c e = Sum.inl i → e.1 ∈ (M i).edgeSet) := by
  let F : I ⊕ K → _root_.SimpleGraph V := Sum.elim (fun i ↦ (M i).spanningCoe) c₀.labelGraph
  have hFdegree : ∀ i v, ((F i).neighborSet v).ncard ≤ 1 := by
    intro i v
    cases i with
    | inl i =>
      change ((M i).spanningCoe.neighborSet v).ncard ≤ 1
      rw [matching_neighbor_ncard G (M i) (hM i)]
      split_ifs <;> omega
    | inr k =>
      apply Set.ncard_le_one_iff_subsingleton.mpr
      intro x hx y hy
      obtain ⟨hvx, hcx⟩ := (EdgeLabeling.labelGraph_adj v x).mp hx
      obtain ⟨hvy, hcy⟩ := (EdgeLabeling.labelGraph_adj v y).mp hy
      exact hc₀ v x y hvx hvy (hcx.trans hcy.symm)
  have hFcover : ∀ x y, G.Adj x y → ∃ i, (F i).Adj x y := by
    intro x y hxy
    by_cases hused : (⨆ i, (M i).spanningCoe).Adj x y
    · obtain ⟨i, hi⟩ := iSup_adj.mp hused
      exact ⟨Sum.inl i, hi⟩
    · have hR : (G \ ⨆ i, (M i).spanningCoe).Adj x y := ⟨hxy, hused⟩
      refine ⟨Sum.inr (c₀.get x y hR), ?_⟩
      exact (EdgeLabeling.labelGraph_adj x y).mpr ⟨hR, rfl⟩
  obtain ⟨c, hc, hclass⟩ := exists_edgeLabeling_of_matching_cover G F hFdegree hFcover
  refine ⟨c, hc, ?_⟩
  intro e i he
  have h := hclass e
  rw [he] at h
  exact h

namespace SetHypergraph

theorem edgeColorable_of_avoiding_matching_family_core {V : Type*} [Fintype V]
    (H J : SetHypergraph V) (hJH : J ⊆ H)
    (hrest : ∀ e : H, e.1 ∉ J → e.1.ncard = 2) (m D : ℕ) (hD : 0 < D)
    (large : J.EdgeColoring (Fin m)) (M : Fin m → H.twoGraph.Subgraph)
    (hM : ∀ i, (M i).IsMatching)
    (havoid : ∀ e : J, ∀ x ∈ e.1, x ∉ (M (large.color e)).verts)
    (hdegree : ∀ v, (H.twoGraph \ ⨆ i, (M i).spanningCoe).degree v ≤ D)
    (hcore : Vizing.HasMatchingDegreeCore (H.twoGraph \ ⨆ i, (M i).spanningCoe) D) :
    H.EdgeColorable (m + D) := by
  let R := H.twoGraph \ ⨆ i, (M i).spanningCoe
  let : DecidableRel R.Adj := fun x y ↦ Classical.propDecidable (R.Adj x y)
  have hdegree' : ∀ v, R.degree v ≤ D := by
    intro v
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hdegree v
  have hcore' : Vizing.HasMatchingDegreeCore R D := by
    intro x y z hx hxy hxz hy hz
    apply hcore x y z
    · simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hx
    · exact hxy
    · exact hxz
    · simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hy
    · simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hz
  obtain ⟨c₀, hc₀⟩ := Vizing.exists_edgeLabeling_of_matching_core R D hD hdegree' hcore'
  obtain ⟨pairs, hpairs, hclasses⟩ := exists_edgeLabeling_from_matchings_and_residual H.twoGraph M hM c₀ hc₀
  obtain ⟨color⟩ := H.edgeColoring_of_large_part_and_pairLabeling J hJH hrest large pairs hpairs (by
    intro e x hx y hxy hcolor
    have hclass := hclasses ⟨s(x, y), hxy⟩ (large.color e) hcolor
    have hadj : (M (large.color e)).Adj x y := Subgraph.mem_edgeSet.mp hclass
    exact havoid e x hx hadj.fst_mem)
  refine ⟨⟨fun e ↦ finSumFinEquiv (color.color e), ?_⟩⟩
  intro e f hef hinter heq
  exact color.valid hef hinter (finSumFinEquiv.injective heq)

#print axioms edgeColorable_of_avoiding_matching_family_core

end SetHypergraph
end Erdos19
