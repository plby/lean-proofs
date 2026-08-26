import ErdosProblems.Erdos19.MatchingFamilyDegrees
import ErdosProblems.Erdos19.Vizing

/-! # Completing a matching family with fresh graph colors -/

namespace Erdos19

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V]

theorem exists_edgeLabeling_of_matching_cover (G : _root_.SimpleGraph V)
    (F : I → _root_.SimpleGraph V)
    (hdegree : ∀ i v, ((F i).neighborSet v).ncard ≤ 1)
    (hcover : ∀ x y, G.Adj x y → ∃ i, (F i).Adj x y) :
    ∃ c : G.EdgeLabeling I,
      (∀ x y z (hxy : G.Adj x y) (hxz : G.Adj x z),
        c.get x y hxy = c.get x z hxz → y = z) ∧
      (∀ e : G.edgeSet, e.1 ∈ (F (c e)).edgeSet) := by
  classical
  have hex : ∀ e : G.edgeSet, ∃ i, e.1 ∈ (F i).edgeSet := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
      obtain ⟨i, hi⟩ := hcover x y (by simpa only [mem_edgeSet] using he)
      exact ⟨i, by simpa only [mem_edgeSet] using hi⟩
  choose c hc using hex
  refine ⟨c, ?_, hc⟩
  intro x y z hxy hxz heq
  have hy : (F (c ⟨s(x, y), hxy⟩)).Adj x y := by
    simpa only [mem_edgeSet] using hc ⟨s(x, y), hxy⟩
  have hz : (F (c ⟨s(x, z), hxz⟩)).Adj x z := by
    simpa only [mem_edgeSet] using hc ⟨s(x, z), hxz⟩
  change c ⟨s(x, y), hxy⟩ = c ⟨s(x, z), hxz⟩ at heq
  rw [← heq] at hz
  exact (Set.ncard_le_one_iff_subsingleton.mp (hdegree _ x)) hy hz

theorem exists_edgeLabeling_completing_matchings [Fintype I]
    (G : _root_.SimpleGraph V) (M : I → G.Subgraph)
    (hM : ∀ i, (M i).IsMatching)
    (hdis : Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe)) (D : ℕ)
    (hbudget : ∀ v, (G.neighborSet v).ncard +
      (∑ i : I, if v ∈ (M i).verts then 0 else 1) ≤ D + Fintype.card I) :
    ∃ c : G.EdgeLabeling (I ⊕ Fin (D + 1)),
      (∀ x y z (hxy : G.Adj x y) (hxz : G.Adj x z),
        c.get x y hxy = c.get x z hxz → y = z) ∧
      (∀ (e : G.edgeSet) (i : I), c e = Sum.inl i → e.1 ∈ (M i).edgeSet) := by
  classical
  let U := ⨆ i, (M i).spanningCoe
  let R := G \ U
  letI : DecidableRel R.Adj := fun x y ↦ Classical.propDecidable (R.Adj x y)
  have hD : ∀ v, R.degree v ≤ D := by
    intro v
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using
      residual_degree_bound_after_matching_family G M hM hdis D hbudget v
  obtain ⟨P, hPdegree, _, hPunion⟩ := Vizing.exists_matching_color_decomposition R D hD
  let F : I ⊕ Fin (D + 1) → _root_.SimpleGraph V := Sum.elim (fun i ↦ (M i).spanningCoe) P
  have hFdegree : ∀ i v, ((F i).neighborSet v).ncard ≤ 1 := by
    intro i v
    cases i with
    | inl i =>
      change ((M i).spanningCoe.neighborSet v).ncard ≤ 1
      rw [matching_neighbor_ncard G (M i) (hM i)]
      split_ifs <;> omega
    | inr i =>
      change ((P i).neighborSet v).ncard ≤ 1
      simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hPdegree i v
  have hFcover : ∀ x y, G.Adj x y → ∃ i, (F i).Adj x y := by
    intro x y hxy
    by_cases hU : U.Adj x y
    · obtain ⟨i, hi⟩ := iSup_adj.mp hU
      exact ⟨Sum.inl i, hi⟩
    · have hR : R.Adj x y := ⟨hxy, hU⟩
      rw [← hPunion] at hR
      obtain ⟨i, hi⟩ := iSup_adj.mp hR
      exact ⟨Sum.inr i, hi⟩
  obtain ⟨c, hc, hcF⟩ := exists_edgeLabeling_of_matching_cover G F hFdegree hFcover
  refine ⟨c, hc, ?_⟩
  intro e i he
  have h := hcF e
  rw [he] at h
  exact h

#print axioms exists_edgeLabeling_completing_matchings

end Erdos19
