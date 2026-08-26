/- Arbitrary-linkage deletion: the full finite deletion/contraction induction. -/
import ErdosProblems.Erdos73.NormalizedLinkageDeletion
import ErdosProblems.Erdos73.MinimalLinkageGraph
import ErdosProblems.Erdos73.ContractLinkage
import ErdosProblems.Erdos73.LinkageDeletionData

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
open Erdos73Infrastructure.SimpleGraph.TreewidthSparsifier
open Erdos73Infrastructure.SimpleGraph.LinkageNormalization
universe u v

private theorem perfect_linkage_deletion_by_card
    {I : Type v} [Fintype I] (g h m : ℕ) (hh : 0 < h)
    (hm : qualitativeGrillRows g h ≤ m)
    (hsize : (m + 1) * (2 * qualitativeGrillColumns g h) ≤ Fintype.card I) :
    ∀ n, ∀ (V : Type u) [Fintype V] [DecidableEq V], Fintype.card V = n →
      ∀ (G : SimpleGraph V) (A B : Finset V) (R : PerfectPathPacking G A B),
      R.card = m → ∀ (Q : I → Finset V),
      (∀ i, (Q i).Nonempty) →
      (∀ i, (G.induce (Q i : Set V)).Connected) →
      (Pairwise fun i j => Disjoint (Q i) (Q j)) →
      ¬ IsMinor (squareGrid g) G →
      ¬ IsMinor (completeBipartiteGraph (Fin h) (Fin h)) G →
      HasColumnAvoidingPacking G A B Q (m / (2 * qualitativeGrillRows g h) + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ dV hV
    cases Subsingleton.elim dV (Classical.decEq V)
    intro G A B R hR Q hne hconn hdisj hgrid hbip
    by_contra hfail
    obtain ⟨H, hHG, ⟨R₀⟩, hHQ, hmin⟩ := exists_edgeMinimal Q R hconn
    have hR₀ : R₀.card = m := by
      rw [R₀.card_eq_left_card, ← R.card_eq_left_card, hR]
    have hfH : ¬ HasColumnAvoidingPacking H A B Q
        (m / (2 * qualitativeGrillRows g h) + 1) :=
      fun h => hfail (h.mono hHG)
    have hgridH : ¬ IsMinor (squareGrid g) H := fun h => hgrid (h.mono hHG)
    have hbipH : ¬ IsMinor (completeBipartiteGraph (Fin h) (Fin h)) H :=
      fun h => hbip (h.mono hHG)
    have hcontract (P : PerfectPathPacking H A B) {a b : V}
        (hab : H.Adj a b) (hp : P.toPathPacking.NoSplitAcross a b)
        (i : I) (ha : a ∈ Q i) (hb : b ∈ Q i) : False := by
      let C := contractEdgeGraph H hab
      let P' := P.contractEdge hab hp
      have hPcard : P'.card = m := by
        rw [PerfectPathPacking.contractEdge_card, P.card_eq_left_card,
          ← R.card_eq_left_card, hR]
      have hlt : Fintype.card (EdgeContractVertex V a b) < n := by
        rw [← hV]
        exact EdgeContractVertex.card_lt_of_ne hab.ne
      have hCminor : IsMinor C H := contractEdgeGraph.isMinor
      have hres := ih _ hlt (EdgeContractVertex V a b) rfl C
        (edgeContractImageSet (a := a) (b := b) A) (edgeContractImageSet B) P' hPcard
        (fun j => edgeContractImageSet (Q j))
        (fun j => edgeContractImageSet_nonempty (hne j))
        (fun j => edgeContractImageSet_connected hab (Q j) (hHQ j))
        (edgeContractImageSet_pairwise_disjoint Q hdisj i ha hb)
        (fun hx => hgridH (hx.trans hCminor))
        (fun hx => hbipH (hx.trans hCminor))
      exact hfH (hres.of_contract hab)
    have hedge_disjoint (P : PerfectPathPacking H A B) :
        Disjoint P.toPathPacking.spanningGraph (columnGraph Q H) := by
      rw [disjoint_iff_inf_le]
      intro a b hab
      obtain ⟨⟨r, hr⟩, _⟩ := P.toPathPacking.spanningGraph_adj_iff_exists_path_edge.mp hab.1
      obtain ⟨hadj, i, ha, hb⟩ := hab.2
      obtain ⟨har, hbr⟩ := (P.path r).endpoints_mem_vertexSet_of_edgeSet hr
      exact (hcontract P hadj
        (P.toPathPacking.noSplitAcross_of_samePath r har hbr) i ha hb).elim
    have hspan : R₀.SpansVertices := by
      intro x
      by_contra hx
      by_cases hxQ : ∃ i, x ∈ Q i
      · obtain ⟨i, hxi⟩ := hxQ
        rcases connected_finset_singleton_or_adj (Q i) (hHQ i) x hxi with hsing | hadj
        · have hmpos : 0 < m := (qualitativeGrillRows_pos g h).trans_le hm
          have hdpos : 1 < 2 * qualitativeGrillRows g h := by
            have := qualitativeGrillRows_pos g h
            omega
          have hk : m / (2 * qualitativeGrillRows g h) + 1 ≤ R₀.toPathPacking.card := by
            change _ ≤ R₀.card
            rw [hR₀]
            have := Nat.div_lt_self hmpos hdpos
            omega
          apply hfH (hasColumnAvoidingPacking_of_disjoint R₀.toPathPacking i hk ?_)
          intro r
          rw [hsing, Finset.disjoint_singleton_right]
          intro hxr
          exact hx (R₀.toPathPacking.mem_vertexSet.mpr ⟨r, hxr⟩)
        · obtain ⟨y, hyi, hxy⟩ := hadj
          exact hcontract R₀ hxy (R₀.toPathPacking.noSplitAcross_of_left_unused hx)
            i hxi hyi
      · have hxQ' : ∀ i, x ∉ Q i := fun i hi => hxQ ⟨i, hi⟩
        let U := (Finset.univ : Finset V).erase x
        have hRU : R₀.toPathPacking.StaysIn U := by
          intro r y hy
          apply Finset.mem_erase.mpr
          refine ⟨?_, Finset.mem_univ _⟩
          intro he
          exact hx (he ▸ R₀.toPathPacking.mem_vertexSet.mpr ⟨r, hy⟩)
        have hAU : A ⊆ U := by
          intro y hy
          exact Finset.mem_erase.mpr
            ⟨fun he => hx (he ▸ R₀.left_subset_vertexSet hy), Finset.mem_univ _⟩
        have hBU : B ⊆ U := by
          intro y hy
          exact Finset.mem_erase.mpr
            ⟨fun he => hx (he ▸ R₀.right_subset_vertexSet hy), Finset.mem_univ _⟩
        have hQU : ∀ i, Q i ⊆ U := by
          intro i y hy
          exact Finset.mem_erase.mpr
            ⟨fun he => hxQ' i (he ▸ hy), Finset.mem_univ _⟩
        let Q' (i : I) := PathPacking.subtypeFinset (Q i) U (hQU i)
        have hQ'ne (i : I) : (Q' i).Nonempty := by
          obtain ⟨y, hy⟩ := hne i
          exact ⟨⟨y, hQU i hy⟩, (PathPacking.mem_subtypeFinset (hQU i) _).mpr hy⟩
        have hQ'disj : Pairwise fun i j => Disjoint (Q' i) (Q' j) := by
          intro i j hij
          rw [Finset.disjoint_left]
          intro y hyi hyj
          exact Finset.disjoint_left.mp (hdisj hij)
            ((PathPacking.mem_subtypeFinset (hQU i) y).mp hyi)
            ((PathPacking.mem_subtypeFinset (hQU j) y).mp hyj)
        have hlt : Fintype.card {y : V // y ∈ U} < n := by
          rw [Fintype.card_coe, ← hV]
          exact (Finset.card_lt_card (Finset.erase_ssubset (Finset.mem_univ x))).trans_eq
            (Finset.card_univ)
        have hUminor : IsMinor (H.induce {y | y ∈ U}) H :=
          ⟨MinorModel.of_embedding (SimpleGraph.Embedding.induce _)⟩
        have hres := ih _ hlt {y : V // y ∈ U} rfl (H.induce {y | y ∈ U})
          (PathPacking.subtypeFinset A U hAU) (PathPacking.subtypeFinset B U hBU)
          (R₀.induce U hRU hAU hBU) hR₀ Q' hQ'ne
          (fun i => connected_subtypeFinset (hQU i) (hHQ i)) hQ'disj
          (fun hz => hgridH (hz.trans hUminor))
          (fun hz => hbipH (hz.trans hUminor))
        exact hfH (hres.of_induce U hAU hBU hQU)
    have hu : R₀.IsUniqueLinkage :=
      ⟨hspan, fun P => hmin.linkage_edgeSet_eq Q hHQ hedge_disjoint P R₀⟩
    have hm₀ : qualitativeGrillRows g h ≤ R₀.card := hR₀.symm ▸ hm
    have hs₀ : (R₀.card + 1) * (2 * qualitativeGrillColumns g h) ≤ Fintype.card I :=
      hR₀.symm ▸ hsize
    have hres := unique_linkage_avoiding_connected_column R₀ hu Q hne hHQ hdisj
      g h hh hm₀ hs₀ hgridH hbipH
    apply hfH
    simpa only [HasColumnAvoidingPacking, hR₀] using hres

/-- The linkage-deletion theorem for a perfect linkage, without any
uniqueness or spanning assumption. The numerical bound is qualitative. -/
theorem perfect_linkage_avoiding_connected_column
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} {A B : Finset V}
    (R : PerfectPathPacking G A B)
    (Q : I → Finset V) (hne : ∀ i, (Q i).Nonempty)
    (hconn : ∀ i, (G.induce (Q i : Set V)).Connected)
    (hdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    (g h : ℕ) (hh : 0 < h) (hm : qualitativeGrillRows g h ≤ R.card)
    (hsize : (R.card + 1) * (2 * qualitativeGrillColumns g h) ≤ Fintype.card I)
    (hgrid : ¬ IsMinor (squareGrid g) G)
    (hbip : ¬ IsMinor (completeBipartiteGraph (Fin h) (Fin h)) G) :
    ∃ i, ∃ P : PathPacking G (A \ Q i) (B \ Q i),
      R.card / (2 * qualitativeGrillRows g h) + 1 ≤ P.card ∧
        ∀ r, Disjoint (P.path r).vertexSet (Q i) :=
  perfect_linkage_deletion_by_card g h R.card hh hm hsize (Fintype.card V)
    V rfl G A B R rfl Q hne hconn hdisj hgrid hbip

/-- The full arbitrary-linkage version of Leaf--Seymour's deletion lemma,
with the elementary grill constants proved in this development. -/
theorem linkage_avoiding_connected_column
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} {A B : Finset V}
    (R : PathPacking G A B)
    (Q : I → Finset V) (hne : ∀ i, (Q i).Nonempty)
    (hconn : ∀ i, (G.induce (Q i : Set V)).Connected)
    (hdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    (g h : ℕ) (hh : 0 < h) (hm : qualitativeGrillRows g h ≤ R.card)
    (hsize : (R.card + 1) * (2 * qualitativeGrillColumns g h) ≤ Fintype.card I)
    (hgrid : ¬ IsMinor (squareGrid g) G)
    (hbip : ¬ IsMinor (completeBipartiteGraph (Fin h) (Fin h)) G) :
    ∃ i, ∃ P : PathPacking G (A \ Q i) (B \ Q i),
      R.card / (2 * qualitativeGrillRows g h) + 1 ≤ P.card ∧
        ∀ r, Disjoint (P.path r).vertexSet (Q i) := by
  have hres : HasColumnAvoidingPacking G R.sourceSet R.targetSet Q
      (R.card / (2 * qualitativeGrillRows g h) + 1) :=
    perfect_linkage_avoiding_connected_column R.toPerfectUsedTerminals Q hne hconn
      hdisj g h hh hm hsize hgrid hbip
  exact hres.widen R.sourceSet_subset_left R.targetSet_subset_right

end
end Erdos73
