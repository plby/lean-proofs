/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Tactic
import ErdosProblems.Erdos622.External.Erdos88.Concentration
import ErdosProblems.Erdos622.HallMatching
import ErdosProblems.Erdos622.Concentration

/-!
# Random induced matchings from a minimum vertex cover

This file contains the deterministic Hall-theoretic core of the random-cover
matching argument used in the proof of Erdős Problem 622.
-/

open scoped SimpleGraph
open scoped BigOperators

namespace Erdos622

namespace RandomCover

open SimpleGraph
open Classical Finset Real

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite vertex cover is minimum if no finite vertex cover has smaller cardinality. -/
def IsMinimumVertexCover (G : SimpleGraph V) (C : Finset V) : Prop :=
  G.IsVertexCover (C : Set V) ∧
    ∀ D : Finset V, G.IsVertexCover (D : Set V) → C.card ≤ D.card

lemma IsMinimumVertexCover.isVertexCover {G : SimpleGraph V} {C : Finset V}
    (hC : IsMinimumVertexCover G C) : G.IsVertexCover (C : Set V) :=
  hC.1

lemma IsMinimumVertexCover.card_le {G : SimpleGraph V} {C D : Finset V}
    (hC : IsMinimumVertexCover G C) (hD : G.IsVertexCover (D : Set V)) :
    C.card ≤ D.card :=
  hC.2 D hD

/-- The bipartite graph consisting of the edges from `D` to the complement of `C`. -/
def outsideGraph (G : SimpleGraph V) (C D : Finset V) : SimpleGraph V :=
  G.between (D : Set V) (C : Set V)ᶜ

lemma outsideGraph_le (G : SimpleGraph V) (C D : Finset V) :
    outsideGraph G C D ≤ G :=
  SimpleGraph.between_le

lemma outsideGraph_isBipartiteWith (G : SimpleGraph V) (C D : Finset V)
    (hDC : D ⊆ C) :
    (outsideGraph G C D).IsBipartiteWith (D : Set V) (C : Set V)ᶜ := by
  apply SimpleGraph.between_isBipartiteWith
  exact Set.disjoint_left.2 fun _ hxD hxC ↦ hxC (hDC hxD)

/-- The set-level exchange argument behind the random-cover matching lemma. -/
private theorem hall_exchange_set
    (J : SimpleGraph V) (C D : Set V)
    (hC : J.IsVertexCover C)
    (hmin : ∀ C' : Set V, J.IsVertexCover C' → C.ncard ≤ C'.ncard)
    (hDC : D ⊆ C) (hD : J.IsIndepSet D) :
    ∃ M : Subgraph (J.between D Cᶜ), D ⊆ M.verts ∧ M.IsMatching := by
  classical
  have hdisjDC : Disjoint D Cᶜ := by
    exact Set.disjoint_left.2 fun _ hxD hxC ↦ hxC (hDC hxD)
  apply exists_isMatching_of_forall_ncard_le
      (J.between_isBipartiteWith hdisjDC)
  intro s hsD
  let N : Set V := ⋃ x ∈ s, (J.between D Cᶜ).neighborSet x
  have hNC : N ⊆ Cᶜ := by
    intro y hy
    simp only [N, Set.mem_iUnion] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact (J.between_isBipartiteWith hdisjDC).mem_of_mem_adj (hsD hx) hxy
  have hcover : J.IsVertexCover ((C \ s) ∪ N) := by
    intro v w hvw
    by_cases hv : v ∈ C \ s
    · exact Or.inl (Set.mem_union_left _ hv)
    by_cases hw : w ∈ C \ s
    · exact Or.inr (Set.mem_union_left _ hw)
    rcases hC hvw with hvC | hwC
    · by_cases hwC' : w ∈ C
      · have hvS : v ∈ s := by
          by_contra hvS
          exact hv ⟨hvC, hvS⟩
        have hwS : w ∈ s := by
          by_contra hwS
          exact hw ⟨hwC', hwS⟩
        exact (hD (hsD hvS) (hsD hwS) hvw.ne hvw).elim
      · have hvS : v ∈ s := by
          by_contra hvS
          exact hv ⟨hvC, hvS⟩
        exact Or.inr <| Set.mem_union_right _ <| by
          simp only [N, Set.mem_iUnion]
          exact ⟨v, hvS, by simp [between_adj, hsD hvS, hwC', hvw]⟩
    · have hvC' : v ∉ C := by
        intro hvC
        have hvS : v ∈ s := by
          by_contra hvS
          exact hv ⟨hvC, hvS⟩
        have hwS : w ∈ s := by
          by_contra hwS
          exact hw ⟨hwC, hwS⟩
        exact hD (hsD hvS) (hsD hwS) hvw.ne hvw
      have hwS : w ∈ s := by
        by_contra hwS
        exact hw ⟨hwC, hwS⟩
      exact Or.inl <| Set.mem_union_right _ <| by
        simp only [N, Set.mem_iUnion]
        exact ⟨w, hwS, by simp [between_adj, hsD hwS, hvC', hvw.symm]⟩
  have hmin' := hmin ((C \ s) ∪ N) hcover
  have hsC : s ⊆ C := hsD.trans hDC
  have hdisj : Disjoint (C \ s) N := by
    refine Set.disjoint_left.2 ?_
    intro x hxC hxN
    exact (hNC hxN) hxC.1
  rw [Set.ncard_union_eq hdisj, ← Set.ncard_sdiff_add_ncard_of_subset hsC] at hmin'
  change s.ncard ≤ N.ncard
  omega

/-- Hall's theorem supplies a matching which covers an independent subset of
a minimum vertex cover and uses only vertices outside the cover on its other
side. -/
theorem exists_matching_cover_independent {G : SimpleGraph V} {C D : Finset V}
    (hC : IsMinimumVertexCover G C) (hDC : D ⊆ C)
    (hDind : G.IsIndepSet (D : Set V)) :
    ∃ M : (outsideGraph G C D).Subgraph,
      (D : Set V) ⊆ M.verts ∧ M.IsMatching := by
  classical
  have hminSet : ∀ C' : Set V, G.IsVertexCover C' →
      (C : Set V).ncard ≤ C'.ncard := by
    intro C' hC'
    have hC'f : G.IsVertexCover (C'.toFinset : Set V) := by
      simpa using hC'
    have hcard := hC.2 C'.toFinset hC'f
    rw [Set.ncard_coe_finset, Set.ncard_eq_toFinset_card']
    exact hcard
  exact hall_exchange_set G (C : Set V) (D : Set V) hC.1 hminSet
    (by simpa using hDC) hDind

/-- Functional form of the Hall matching: an independent subset of a
minimum cover has distinct adjacent representatives outside that cover. -/
theorem exists_injective_outside_partner
    {G : SimpleGraph V} {C D : Finset V}
    (hC : IsMinimumVertexCover G C) (hDC : D ⊆ C)
    (hDind : G.IsIndepSet (D : Set V)) :
    ∃ f : D → V, Function.Injective f ∧
      ∀ d : D, G.Adj d (f d) ∧ f d ∉ C := by
  classical
  obtain ⟨N, hDN, hNmatch⟩ :=
    exists_matching_cover_independent hC hDC hDind
  let f : D → V := fun d ↦ Classical.choose (hNmatch (hDN d.property))
  have hfadj (d : D) : N.Adj d (f d) :=
    (Classical.choose_spec (hNmatch (hDN d.property))).1
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hNmatch.eq_of_adj_right (hfadj a)
    simpa only [hab] using hfadj b
  refine ⟨f, hfinj, ?_⟩
  intro d
  have hJadj := (hfadj d).adj_sub
  have hGadj : G.Adj d (f d) := (outsideGraph_le G C D) hJadj
  have hout : f d ∈ (C : Set V)ᶜ :=
    (outsideGraph_isBipartiteWith G C D hDC).mem_of_mem_adj d.property hJadj
  exact ⟨hGadj, hout⟩

/-- Deterministic two-stage decomposition used in DKM Lemma 4.4.  For every
revealed subset `T` of a minimum cover, first take a maximal matching inside
`T`; the uncovered part `D` is independent, and Hall's theorem then supplies
a matching from all of `D` to vertices outside the original cover. -/
theorem exists_internal_outside_matching_decomposition
    {G : SimpleGraph V} {C T : Finset V}
    (hC : IsMinimumVertexCover G C) (hTC : T ⊆ C) :
    ∃ M : G.Subgraph,
      M.IsMatching ∧ M.verts ⊆ (T : Set V) ∧
      let D := T.filter fun v ↦ v ∉ M.verts
      G.IsIndepSet (D : Set V) ∧
        ∃ N : (outsideGraph G C D).Subgraph,
          (D : Set V) ⊆ N.verts ∧ N.IsMatching := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce (T : Set V)
  obtain ⟨K, hKmatch, hKcover⟩ :=
    Erdos622.exists_isMatching_isVertexCover_verts H.coe
  let M : G.Subgraph := H.coeSubgraph K
  have hMmatch : M.IsMatching := hKmatch.coeSubgraph
  have hMH : M ≤ H := Subgraph.coeSubgraph_le K
  have hMverts : M.verts ⊆ (T : Set V) := by
    intro v hv
    have hvH := hMH.left hv
    simpa [H] using hvH
  let D := T.filter fun v ↦ v ∉ M.verts
  have hDT : D ⊆ T := Finset.filter_subset _ _
  have hDind : G.IsIndepSet (D : Set V) := by
    intro v hvD w hwD hvw hAdj
    have hvD' : v ∈ T ∧ v ∉ M.verts := by simpa [D] using hvD
    have hwD' : w ∈ T ∧ w ∉ M.verts := by simpa [D] using hwD
    have hHAdj : H.coe.Adj ⟨v, by simpa [H] using hvD'.1⟩
        ⟨w, by simpa [H] using hwD'.1⟩ := by
      have hh : H.Adj v w := by
        exact ⟨by simpa [H] using hvD'.1, by simpa [H] using hwD'.1, hAdj⟩
      exact hh.coe
    rcases hKcover hHAdj with hvK | hwK
    · exact hvD'.2 ⟨_, hvK, rfl⟩
    · exact hwD'.2 ⟨_, hwK, rfl⟩
  have hDC : D ⊆ C := hDT.trans hTC
  obtain ⟨N, hDN, hNmatch⟩ :=
    exists_matching_cover_independent hC hDC hDind
  exact ⟨M, hMmatch, hMverts, hDind, N, hDN, hNmatch⟩

/-- The same decomposition with Hall's matching exposed as an injective
outside-partner map, the form convenient for exact powerset counting. -/
theorem exists_internal_matching_and_partner_injection
    {G : SimpleGraph V} {C T : Finset V}
    (hC : IsMinimumVertexCover G C) (hTC : T ⊆ C) :
    ∃ M : G.Subgraph,
      M.IsMatching ∧ M.verts ⊆ (T : Set V) ∧
      let D := T.filter fun v ↦ v ∉ M.verts
      G.IsIndepSet (D : Set V) ∧
        ∃ f : D → V, Function.Injective f ∧
          ∀ d : D, G.Adj d (f d) ∧ f d ∉ C := by
  obtain ⟨M, hM, hMT, hDind, -⟩ :=
    exists_internal_outside_matching_decomposition hC hTC
  let D := T.filter fun v ↦ v ∉ M.verts
  have hDC : D ⊆ C := (Finset.filter_subset _ _).trans hTC
  obtain ⟨f, hfinj, hf⟩ :=
    exists_injective_outside_partner hC hDC hDind
  exact ⟨M, hM, hMT, hDind, f, hfinj, hf⟩

/-! ## Exact block-fiber counting -/

/-- Splitting every subset of `O` into its part in `R` and its part in
`O \ R` shows that an event depending only on the `R`-coordinates has the
expected power-of-two fiber multiplicity. -/
private lemma powerset_inter_filter_card
    {A : Type*} [DecidableEq A] (O R : Finset A) (hRO : R ⊆ O)
    (P : Finset A → Prop) [DecidablePred P] :
    (O.powerset.filter fun S ↦ P (S ∩ R)).card =
      (R.powerset.filter P).card * 2 ^ (O.card - R.card) := by
  classical
  let Q := O \ R
  let source := (R.powerset.filter P) ×ˢ Q.powerset
  have hcardQ : Q.card = O.card - R.card := by
    simp [Q, Finset.card_sdiff_of_subset hRO]
  have hcardSource : source.card =
      (R.powerset.filter P).card * 2 ^ (O.card - R.card) := by
    simp [source, hcardQ]
  rw [← hcardSource]
  symm
  refine Finset.card_bij (fun p _ ↦ p.1 ∪ p.2) ?_ ?_ ?_
  · intro p hp
    have hp' := Finset.mem_product.mp hp
    have hp1 := Finset.mem_filter.mp hp'.1
    have hp2 := Finset.mem_powerset.mp hp'.2
    have hp1R := Finset.mem_powerset.mp hp1.1
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      exact Finset.union_subset (hp1R.trans hRO)
        (hp2.trans Finset.sdiff_subset)
    · have hinter : (p.1 ∪ p.2) ∩ R = p.1 := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hx1 | hx2, hxR⟩
          · exact hx1
          · exact (Finset.mem_sdiff.mp (hp2 hx2)).2 hxR |>.elim
        · intro hx1
          exact ⟨Or.inl hx1, hp1R hx1⟩
      rw [hinter]
      exact hp1.2
  · intro p hp q hq hpq
    apply Prod.ext
    · have hp' := Finset.mem_product.mp hp
      have hq' := Finset.mem_product.mp hq
      have hp1R := Finset.mem_powerset.mp (Finset.mem_filter.mp hp'.1).1
      have hq1R := Finset.mem_powerset.mp (Finset.mem_filter.mp hq'.1).1
      ext x
      have hx := Finset.ext_iff.mp hpq x
      simp only [Finset.mem_union] at hx
      constructor
      · intro hxp
        have hxR := hp1R hxp
        rcases hx.mp (Or.inl hxp) with hxq | hxq
        · exact hxq
        · exact (Finset.mem_sdiff.mp
            (Finset.mem_powerset.mp hq'.2 hxq)).2 hxR |>.elim
      · intro hxq
        have hxR := hq1R hxq
        rcases hx.mpr (Or.inl hxq) with hxp | hxp
        · exact hxp
        · exact (Finset.mem_sdiff.mp
            (Finset.mem_powerset.mp hp'.2 hxp)).2 hxR |>.elim
    · have hp' := Finset.mem_product.mp hp
      have hq' := Finset.mem_product.mp hq
      have hp2Q := Finset.mem_powerset.mp hp'.2
      have hq2Q := Finset.mem_powerset.mp hq'.2
      ext x
      have hx := Finset.ext_iff.mp hpq x
      simp only [Finset.mem_union] at hx
      constructor
      · intro hxp
        have hxnotR := (Finset.mem_sdiff.mp (hp2Q hxp)).2
        rcases hx.mp (Or.inr hxp) with hxq | hxq
        · exact (hxnotR ((Finset.mem_powerset.mp
              (Finset.mem_filter.mp hq'.1).1) hxq)).elim
        · exact hxq
      · intro hxq
        have hxnotR := (Finset.mem_sdiff.mp (hq2Q hxq)).2
        rcases hx.mpr (Or.inr hxq) with hxp | hxp
        · exact (hxnotR ((Finset.mem_powerset.mp
              (Finset.mem_filter.mp hp'.1).1) hxp)).elim
        · exact hxp
  · intro S hS
    have hS' := Finset.mem_filter.mp hS
    let p : Finset A × Finset A := (S ∩ R, S \ R)
    have hp : p ∈ source := by
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_powerset.mpr (Finset.inter_subset_right), hS'.2⟩
      · apply Finset.mem_powerset.mpr
        intro x hx
        have hx' := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_powerset.mp hS'.1 hx'.1, hx'.2⟩
    refine ⟨p, hp, ?_⟩
    ext x
    simp only [p, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      by_cases hxR : x ∈ R
      · exact Or.inl ⟨hx, hxR⟩
      · exact Or.inr ⟨hx, hxR⟩

/-- Hoeffding lower tail for how many vertices of a fixed `R ⊆ O` are
retained by a uniformly sampled subset of `O`, with all unused coordinates
counted exactly. -/
theorem powerset_inter_card_lowerTail
    {A : Type*} [Fintype A] [DecidableEq A]
    (O R : Finset A) (hRO : R ⊆ O) {t : ℝ} (ht : 0 ≤ t) :
    ((O.powerset.filter fun S ↦
        ((S ∩ R).card : ℝ) ≤ (R.card : ℝ) / 2 - t).card : ℝ) ≤
      (2 : ℝ) ^ O.card * Real.exp (-2 * t ^ 2 / R.card) := by
  have hsmall := Erdos622.Concentration.subsetCard_lowerTail R ht
  rw [powerset_inter_filter_card O R hRO
    (fun S ↦ (S.card : ℝ) ≤ (R.card : ℝ) / 2 - t)]
  push_cast
  have hpow : (2 : ℝ) ^ O.card =
      (2 : ℝ) ^ R.card * 2 ^ (O.card - R.card) := by
    rw [← pow_add]
    congr
    have hcard := Finset.card_le_card hRO
    omega
  calc
    ((R.powerset.filter fun S ↦
        (S.card : ℝ) ≤ (R.card : ℝ) / 2 - t).card : ℝ) *
        (2 : ℝ) ^ (O.card - R.card) ≤
      ((2 : ℝ) ^ R.card * Real.exp (-2 * t ^ 2 / R.card)) *
        (2 : ℝ) ^ (O.card - R.card) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = (2 : ℝ) ^ O.card * Real.exp (-2 * t ^ 2 / R.card) := by
      rw [hpow]
      ring

/-! ## Combining the revealed internal matching with surviving Hall edges -/

/-- A matching has as many edges as half its number of vertices.  We package
the lower-bound formulation used below without choosing an enumeration of
the edge finset. -/
def HasMatchingAtLeast (G : SimpleGraph V) (S : Finset V) (r : ℝ) : Prop :=
  ∃ M : G.Subgraph, M.IsMatching ∧ M.verts ⊆ (S : Set V) ∧
    r ≤ (M.verts.toFinset.card : ℝ) / 2

/-- If `M` is the matching found inside the revealed cover-set `T` and `f`
is Hall's injective outside-partner map for the unmatched vertices `D`, then
the edges whose partners lie in `U` can be added disjointly to `M`.

The cardinal conclusion is deliberately integral: it says that the combined
matching has at least half of `|V(M)| + 2 |{d : f(d) ∈ U}|` edges. -/
theorem exists_matching_of_internal_and_selected_partners
    {G : SimpleGraph V} {C T D U : Finset V} {M : G.Subgraph}
    (hM : M.IsMatching) (hMT : M.verts ⊆ (T : Set V))
    (hTC : T ⊆ C) (hDT : D ⊆ T)
    (hDM : ∀ d ∈ D, d ∉ M.verts)
    (f : D → V) (hfinj : Function.Injective f)
    (hf : ∀ d : D, G.Adj d (f d) ∧ f d ∉ C) :
    ∃ P : G.Subgraph, P.IsMatching ∧ P.verts ⊆ ((T ∪ U : Finset V) : Set V) ∧
      M.verts.toFinset.card +
          2 * (Finset.univ.filter fun d : D ↦ f d ∈ U).card ≤
        P.verts.toFinset.card := by
  classical
  let X : Finset D := Finset.univ.filter fun d : D ↦ f d ∈ U
  let L : G.Subgraph := ⨆ d : X, G.subgraphOfAdj (hf d.1).1
  have hLmatch : L.IsMatching := by
    apply Subgraph.IsMatching.iSup
    · intro d
      exact Subgraph.IsMatching.subgraphOfAdj (hf d.1).1
    · intro a b hab
      rw [SimpleGraph.support_subgraphOfAdj,
        SimpleGraph.support_subgraphOfAdj, Set.disjoint_left]
      intro v hva hvb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hva hvb
      rcases hva with hva | hva <;> rcases hvb with hvb | hvb
      · exact hab (Subtype.ext (Subtype.ext (hva.symm.trans hvb)))
      · have hvaC : (a.1.1 : V) ∈ C := hTC (hDT a.1.2)
        have heq : (a.1.1 : V) = f b.1 := hva.symm.trans hvb
        exact (hf b.1).2 (heq ▸ hvaC)
      · have hvbC : (b.1.1 : V) ∈ C := hTC (hDT b.1.2)
        have heq : f a.1 = (b.1.1 : V) := hva.symm.trans hvb
        exact (hf a.1).2 (heq.symm ▸ hvbC)
      · have heq : f a.1 = f b.1 := hva.symm.trans hvb
        exact hab (Subtype.ext (hfinj heq))
  have hML : Disjoint M.support L.support := by
    rw [hM.support_eq_verts, hLmatch.support_eq_verts, Set.disjoint_left]
    intro v hvM hvL
    change v ∈ (⨆ d : X, G.subgraphOfAdj (hf d.1).1).verts at hvL
    rw [Subgraph.verts_iSup] at hvL
    obtain ⟨d, hvd⟩ := Set.mem_iUnion.mp hvL
    simp only [SimpleGraph.subgraphOfAdj_verts,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hvd
    rcases hvd with rfl | rfl
    · exact hDM d.1 (d.1.2) hvM
    · exact (hf d.1).2 (hTC (hMT hvM))
  let P : G.Subgraph := M ⊔ L
  have hPmatch : P.IsMatching := hM.sup hLmatch hML
  have hPsub : P.verts ⊆ ((T ∪ U : Finset V) : Set V) := by
    intro v hv
    change v ∈ (M ⊔ L).verts at hv
    rw [Subgraph.verts_sup] at hv
    rcases hv with hvM | hvL
    · exact Finset.mem_union_left U (hMT hvM)
    · change v ∈ (⨆ d : X, G.subgraphOfAdj (hf d.1).1).verts at hvL
      rw [Subgraph.verts_iSup] at hvL
      obtain ⟨d, hvd⟩ := Set.mem_iUnion.mp hvL
      simp only [SimpleGraph.subgraphOfAdj_verts,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hvd
      rcases hvd with rfl | rfl
      · exact Finset.mem_union_left U (hDT d.1.2)
      · exact Finset.mem_union_right T
          (Finset.mem_filter.mp d.2).2
  refine ⟨P, hPmatch, hPsub, ?_⟩
  have hcardP : P.verts.toFinset.card =
      M.verts.toFinset.card + L.verts.toFinset.card := by
    change (M ⊔ L).verts.toFinset.card = _
    rw [Subgraph.verts_sup, Set.toFinset_union,
      Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro v hvM hvL
    exact (Set.disjoint_left.mp hML)
      (hM.support_eq_verts.symm ▸ (Set.mem_toFinset.mp hvM))
      (hLmatch.support_eq_verts.symm ▸ (Set.mem_toFinset.mp hvL))
  have hcardL : 2 * X.card ≤ L.verts.toFinset.card := by
    let DX : Finset V := X.image fun d ↦ (d.1 : V)
    let FX : Finset V := X.image fun d ↦ f d
    have hDXcard : DX.card = X.card := by
      exact Finset.card_image_of_injective _ fun _ _ h ↦
        Subtype.ext h
    have hFXcard : FX.card = X.card := by
      apply Finset.card_image_of_injective
      intro a b hab
      exact hfinj hab
    have hdisj : Disjoint DX FX := by
      rw [Finset.disjoint_left]
      intro v hvDX hvFX
      obtain ⟨d, hdX, rfl⟩ := Finset.mem_image.mp hvDX
      obtain ⟨e, heX, heq⟩ := Finset.mem_image.mp hvFX
      have hdC : (d.1 : V) ∈ C := hTC (hDT d.2)
      exact (hf e).2 (heq.symm ▸ hdC)
    have hsub : DX ∪ FX ⊆ L.verts.toFinset := by
      intro v hv
      rw [Finset.mem_union] at hv
      rw [Set.mem_toFinset]
      change v ∈ (⨆ d : X, G.subgraphOfAdj (hf d.1).1).verts
      rw [Subgraph.verts_iSup]
      rcases hv with hvDX | hvFX
      · obtain ⟨d, hdX, rfl⟩ := Finset.mem_image.mp hvDX
        exact Set.mem_iUnion.mpr ⟨⟨d, hdX⟩, by simp⟩
      · obtain ⟨d, hdX, rfl⟩ := Finset.mem_image.mp hvFX
        exact Set.mem_iUnion.mpr ⟨⟨d, hdX⟩, by simp⟩
    calc
      2 * X.card = DX.card + FX.card := by omega
      _ = (DX ∪ FX).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ L.verts.toFinset.card := Finset.card_le_card hsub
  simp only [X] at hcardL ⊢
  omega

private lemma card_selected_image
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset A) (f : A → B) (hf : Function.Injective f) (u : Finset B) :
    (s.filter fun a ↦ f a ∈ u).card = (u ∩ s.image f).card := by
  have himage : (s.filter fun a ↦ f a ∈ u).image f = u ∩ s.image f := by
    ext b
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨a, ⟨has, hfu⟩, rfl⟩
      exact ⟨hfu, ⟨a, has, rfl⟩⟩
    · rintro ⟨hbu, a, has, rfl⟩
      exact ⟨a, ⟨has, hbu⟩, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ hf]

private lemma powerset_union_filter_card
    {A : Type*} [DecidableEq A] (C O : Finset A) (hCO : Disjoint C O)
    (P : Finset A → Prop) [DecidablePred P] :
    ((C ∪ O).powerset.filter P).card =
      (((C.powerset ×ˢ O.powerset).filter fun p ↦ P (p.1 ∪ p.2)).card) := by
  classical
  symm
  refine Finset.card_bij (fun p _ ↦ p.1 ∪ p.2) ?_ ?_ ?_
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpC := Finset.mem_powerset.mp (Finset.mem_product.mp hp'.1).1
    have hpO := Finset.mem_powerset.mp (Finset.mem_product.mp hp'.1).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.union_subset
        (hpC.trans (Finset.subset_union_left))
        (hpO.trans (Finset.subset_union_right))), hp'.2⟩
  · intro p hp q hq hpq
    have hp' := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have hq' := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
    have hpC := Finset.mem_powerset.mp hp'.1
    have hpO := Finset.mem_powerset.mp hp'.2
    have hqC := Finset.mem_powerset.mp hq'.1
    have hqO := Finset.mem_powerset.mp hq'.2
    apply Prod.ext
    · ext x
      have hx := Finset.ext_iff.mp hpq x
      simp only [Finset.mem_union] at hx
      constructor
      · intro hxp
        have hxC := hpC hxp
        rcases hx.mp (Or.inl hxp) with hxq | hxq
        · exact hxq
        · exact (Finset.disjoint_left.mp hCO hxC (hqO hxq)).elim
      · intro hxq
        have hxC := hqC hxq
        rcases hx.mpr (Or.inl hxq) with hxp | hxp
        · exact hxp
        · exact (Finset.disjoint_left.mp hCO hxC (hpO hxp)).elim
    · ext x
      have hx := Finset.ext_iff.mp hpq x
      simp only [Finset.mem_union] at hx
      constructor
      · intro hxp
        have hxO := hpO hxp
        rcases hx.mp (Or.inr hxp) with hxq | hxq
        · exact (Finset.disjoint_left.mp hCO (hqC hxq) hxO).elim
        · exact hxq
      · intro hxq
        have hxO := hqO hxq
        rcases hx.mpr (Or.inr hxq) with hxp | hxp
        · exact (Finset.disjoint_left.mp hCO (hpC hxp) hxO).elim
        · exact hxp
  · intro S hS
    have hS' := Finset.mem_filter.mp hS
    let p : Finset A × Finset A := (S ∩ C, S ∩ O)
    have hp : p ∈ (C.powerset ×ˢ O.powerset).filter
        (fun q ↦ P (q.1 ∪ q.2)) := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
            Finset.mem_powerset.mpr Finset.inter_subset_right⟩
      · have hunion : (S ∩ C) ∪ (S ∩ O) = S := by
          ext x
          have hxsub := Finset.mem_powerset.mp hS'.1
          simp only [Finset.mem_union, Finset.mem_inter]
          constructor
          · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
          · intro hx
            rcases Finset.mem_union.mp (hxsub hx) with hxC | hxO
            · exact Or.inl ⟨hx, hxC⟩
            · exact Or.inr ⟨hx, hxO⟩
        rw [hunion]
        exact hS'.2
    refine ⟨p, hp, ?_⟩
    dsimp only [p]
    ext x
    have hxsub := Finset.mem_powerset.mp hS'.1
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    · intro hx
      rcases Finset.mem_union.mp (hxsub hx) with hxC | hxO
      · exact Or.inl ⟨hx, hxC⟩
      · exact Or.inr ⟨hx, hxO⟩

private lemma card_filter_product_eq_sum
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset A) (u : Finset B) (P : A → B → Prop)
    [DecidablePred fun p : A × B ↦ P p.1 p.2] :
    (((s ×ˢ u).filter fun p ↦ P p.1 p.2).card : ℝ) =
      ∑ a ∈ s, ((u.filter fun b ↦ P a b).card : ℝ) := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product, Finset.sum_ite_irrel, Finset.filter_filter]
  push_cast
  rfl

/-- Exact conditional finite-counting form of DKM Lemma 4.4.  Once the
vertices `T = C ∩ S` of the minimum cover have been revealed, all but the
displayed Hoeffding-sized family of choices outside `C` contain a matching
of size at least `|T|/2 - t`.

The proof chooses a maximal internal matching, applies the Hall exchange
lemma to its independent remainder, and counts the unused outside
coordinates by exact powerset fibers. -/
theorem conditional_minimumCover_randomMatching
    {G : SimpleGraph V} {C T : Finset V}
    (hC : IsMinimumVertexCover G C) (hTC : T ⊆ C)
    {t : ℝ} (ht : 0 ≤ t) :
    let O := (Finset.univ : Finset V) \ C
    ((O.powerset.filter fun U ↦
        ¬ HasMatchingAtLeast G (T ∪ U) ((T.card : ℝ) / 2 - t)).card : ℝ) ≤
      (2 : ℝ) ^ O.card * Real.exp (-2 * t ^ 2 / T.card) := by
  classical
  dsimp only
  let O : Finset V := (Finset.univ : Finset V) \ C
  obtain ⟨M, hM, hMT, hDind, f, hfinj, hf⟩ :=
    exists_internal_matching_and_partner_injection hC hTC
  let D := T.filter fun v ↦ v ∉ M.verts
  let R : Finset V := Finset.univ.image f
  have hRO : R ⊆ O := by
    intro v hvR
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hvR
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (hf d).2⟩
  have hRcard : R.card = D.card := by
    change (Finset.univ.image f).card = D.card
    rw [Finset.card_image_of_injective _ hfinj,
      Finset.card_univ, Fintype.card_coe]
  have hMfin : M.verts.toFinset ⊆ T := by
    intro v hv
    exact hMT (Set.mem_toFinset.mp hv)
  have hDcard : D.card = T.card - M.verts.toFinset.card := by
    have hDeq : D = T \ M.verts.toFinset := by
      ext v
      simp [D]
    rw [hDeq, Finset.card_sdiff_of_subset hMfin]
  have hDT : D ⊆ T := Finset.filter_subset _ _
  have hDM : ∀ d ∈ D, d ∉ M.verts := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2
  by_cases hD0 : D.card = 0
  · have hDempty : D = ∅ := Finset.card_eq_zero.mp hD0
    have hMcardLe := Finset.card_le_card hMfin
    have hMcard : M.verts.toFinset.card = T.card := by omega
    have hfilter :
        (O.powerset.filter fun U ↦
          ¬ HasMatchingAtLeast G (T ∪ U) ((T.card : ℝ) / 2 - t)) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro U hU
      have hbad := (Finset.mem_filter.mp hU).2
      apply hbad
      refine ⟨M, hM, ?_, ?_⟩
      · intro v hv
        exact Finset.mem_union_left U (hMT hv)
      · rw [hMcard]
        linarith
    rw [hfilter]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by positivity) (Real.exp_nonneg _)
  · have hDpos : 0 < D.card := Nat.pos_of_ne_zero hD0
    have hbadsub :
        O.powerset.filter (fun U ↦
          ¬ HasMatchingAtLeast G (T ∪ U) ((T.card : ℝ) / 2 - t)) ⊆
        O.powerset.filter (fun U ↦
          ((U ∩ R).card : ℝ) ≤ (R.card : ℝ) / 2 - t) := by
      intro U hU
      have hUpow := (Finset.mem_filter.mp hU).1
      have hbad := (Finset.mem_filter.mp hU).2
      apply Finset.mem_filter.mpr
      refine ⟨hUpow, ?_⟩
      by_contra hnot
      push Not at hnot
      apply hbad
      obtain ⟨P, hP, hPsub, hPcard⟩ :=
        exists_matching_of_internal_and_selected_partners hM hMT hTC hDT hDM
          f hfinj hf
      refine ⟨P, hP, hPsub, ?_⟩
      have hsel :
          (Finset.univ.filter fun d : D ↦ f d ∈ U).card =
            (U ∩ R).card := by
        simpa only [R] using
          card_selected_image (Finset.univ : Finset D) f hfinj U
      rw [hsel] at hPcard
      have hDcast : (D.card : ℝ) =
          (T.card : ℝ) - M.verts.toFinset.card := by
        rw [hDcard, Nat.cast_sub (Finset.card_le_card hMfin)]
      have hPcardR :
          (M.verts.toFinset.card : ℝ) + 2 * (U ∩ R).card ≤
            P.verts.toFinset.card := by exact_mod_cast hPcard
      rw [hRcard] at hnot
      nlinarith
    have hcount := Finset.card_le_card hbadsub
    have htail := powerset_inter_card_lowerTail O R hRO ht
    have hcountR :
        ((O.powerset.filter fun U ↦
          ¬ HasMatchingAtLeast G (T ∪ U) ((T.card : ℝ) / 2 - t)).card : ℝ) ≤
        ((O.powerset.filter fun U ↦
          ((U ∩ R).card : ℝ) ≤ (R.card : ℝ) / 2 - t).card : ℝ) := by
      exact_mod_cast hcount
    calc
      ((O.powerset.filter fun U ↦
        ¬ HasMatchingAtLeast G (T ∪ U) ((T.card : ℝ) / 2 - t)).card : ℝ) ≤
          ((O.powerset.filter fun U ↦
            ((U ∩ R).card : ℝ) ≤ (R.card : ℝ) / 2 - t).card : ℝ) := hcountR
      _ ≤ (2 : ℝ) ^ O.card * Real.exp (-2 * t ^ 2 / R.card) := htail
      _ ≤ (2 : ℝ) ^ O.card * Real.exp (-2 * t ^ 2 / T.card) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        rw [hRcard]
        have hDTcard : D.card ≤ T.card := Finset.card_le_card hDT
        have ht2 : 0 ≤ 2 * t ^ 2 := by positivity
        have hDreal : (0 : ℝ) < D.card := by exact_mod_cast hDpos
        by_cases hT0 : T.card = 0
        · omega
        · have hTreal : (0 : ℝ) < T.card := by
            exact_mod_cast Nat.pos_of_ne_zero hT0
          by_cases ht0 : t = 0
          · simp [ht0]
          · have htpos : 0 < 2 * t ^ 2 := by
              positivity
            have hdiv : (2 * t ^ 2) / T.card ≤
                (2 * t ^ 2) / D.card := by
              exact (div_le_div_iff_of_pos_left htpos hTreal hDreal).2 (by
                exact_mod_cast hDTcard)
            have hneg := neg_le_neg hdiv
            calc
              -2 * t ^ 2 / (D.card : ℝ) =
                  -(2 * t ^ 2 / (D.card : ℝ)) := by ring
              _ ≤ -(2 * t ^ 2 / (T.card : ℝ)) := hneg
              _ = -2 * t ^ 2 / (T.card : ℝ) := by ring

/-- Unconditional finite-count version of DKM Lemma 4.4.  The two error
terms are respectively the lower tail for `|C ∩ S|` and the conditional
lower tail for the Hall partners. -/
theorem minimumCover_randomMatching_count
    {G : SimpleGraph V} {C : Finset V}
    (hC : IsMinimumVertexCover G C) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hCpos : 0 < C.card) (harange : 2 * a < C.card) :
    ((((Finset.univ : Finset V).powerset.filter fun S ↦
        ¬ HasMatchingAtLeast G S
          ((C.card : ℝ) / 4 - a / 2 - b)).card : ℝ)) ≤
      (2 : ℝ) ^ Fintype.card V *
        (Real.exp (-2 * a ^ 2 / C.card) +
          Real.exp (-2 * b ^ 2 / C.card)) := by
  classical
  let O : Finset V := (Finset.univ : Finset V) \ C
  have hCO : Disjoint C O := by
    simp [O, Finset.disjoint_left]
  have hCU : C ∪ O = (Finset.univ : Finset V) := by
    ext v
    simp [O]
  let bad : Finset V → Prop := fun S ↦
    ¬ HasMatchingAtLeast G S ((C.card : ℝ) / 4 - a / 2 - b)
  have hsplit := powerset_union_filter_card C O hCO bad
  rw [hCU] at hsplit
  have hsum := card_filter_product_eq_sum C.powerset O.powerset
    (fun T U ↦ bad (T ∪ U))
  have hbadSum :
      ((((Finset.univ : Finset V).powerset.filter bad).card : ℝ)) =
        ∑ T ∈ C.powerset,
          ((O.powerset.filter fun U ↦ bad (T ∪ U)).card : ℝ) := by
    rw [hsplit]
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro T hT
    norm_cast
    apply congrArg Finset.card
    ext U
    simp only [Finset.mem_filter]
  rw [hbadSum]
  let eB : ℝ := Real.exp (-2 * b ^ 2 / C.card)
  have hpoint : ∀ T ∈ C.powerset,
      ((O.powerset.filter fun U ↦ bad (T ∪ U)).card : ℝ) ≤
        (if (T.card : ℝ) ≤ (C.card : ℝ) / 2 - a
          then (2 : ℝ) ^ O.card else 0) + (2 : ℝ) ^ O.card * eB := by
    intro T hTpow
    have hTC := Finset.mem_powerset.mp hTpow
    by_cases hsmall : (T.card : ℝ) ≤ (C.card : ℝ) / 2 - a
    · rw [if_pos hsmall]
      have hcard :
          (O.powerset.filter fun U ↦ bad (T ∪ U)).card ≤ O.powerset.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have htotal : O.powerset.card = 2 ^ O.card := Finset.card_powerset O
      have hcardR :
          ((O.powerset.filter fun U ↦ bad (T ∪ U)).card : ℝ) ≤
            (2 : ℝ) ^ O.card := by
        calc
          ((O.powerset.filter fun U ↦ bad (T ∪ U)).card : ℝ) ≤
              (O.powerset.card : ℝ) := by exact_mod_cast hcard
          _ = (2 : ℝ) ^ O.card := by norm_cast
      exact hcardR.trans (le_add_of_nonneg_right (mul_nonneg (by positivity)
        (Real.exp_nonneg _)))
    · rw [if_neg hsmall, zero_add]
      have hcond := conditional_minimumCover_randomMatching hC hTC (t := b) hb
      have hsub :
          O.powerset.filter (fun U ↦ bad (T ∪ U)) ⊆
          O.powerset.filter (fun U ↦
            ¬ HasMatchingAtLeast G (T ∪ U) ((T.card : ℝ) / 2 - b)) := by
        intro U hU
        have hUpow := (Finset.mem_filter.mp hU).1
        have hbad := (Finset.mem_filter.mp hU).2
        apply Finset.mem_filter.mpr
        refine ⟨hUpow, ?_⟩
        intro hhigh
        apply hbad
        rcases hhigh with ⟨M, hM, hMS, hcard⟩
        refine ⟨M, hM, hMS, ?_⟩
        push Not at hsmall
        linarith
      have hsubcard :
          ((O.powerset.filter (fun U ↦ bad (T ∪ U))).card : ℝ) ≤
          ((O.powerset.filter (fun U ↦
            ¬ HasMatchingAtLeast G (T ∪ U) ((T.card : ℝ) / 2 - b))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      refine hsubcard.trans (hcond.trans ?_)
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      have hTcard : T.card ≤ C.card := Finset.card_le_card hTC
      have hTpos : 0 < T.card := by
        push Not at hsmall
        have hCr : (0 : ℝ) < C.card := by exact_mod_cast hCpos
        by_contra h0
        have : T.card = 0 := Nat.eq_zero_of_not_pos h0
        rw [this] at hsmall
        nlinarith
      have hTr : (0 : ℝ) < T.card := by exact_mod_cast hTpos
      have hCr : (0 : ℝ) < C.card := by exact_mod_cast hCpos
      by_cases hb0 : b = 0
      · simp [hb0]
      · have hbpos : 0 < 2 * b ^ 2 := by positivity
        have hdiv : (2 * b ^ 2) / C.card ≤
            (2 * b ^ 2) / T.card := by
          exact (div_le_div_iff_of_pos_left hbpos hCr hTr).2 (by
            exact_mod_cast hTcard)
        have hneg := neg_le_neg hdiv
        change -2 * b ^ 2 / (T.card : ℝ) ≤
          -2 * b ^ 2 / (C.card : ℝ)
        calc
          -2 * b ^ 2 / (T.card : ℝ) =
              -(2 * b ^ 2 / (T.card : ℝ)) := by ring
          _ ≤ -(2 * b ^ 2 / (C.card : ℝ)) := hneg
          _ = -2 * b ^ 2 / (C.card : ℝ) := by ring
  calc
    ∑ T ∈ C.powerset,
        ((O.powerset.filter fun U ↦ bad (T ∪ U)).card : ℝ) ≤
      ∑ T ∈ C.powerset,
        ((if (T.card : ℝ) ≤ (C.card : ℝ) / 2 - a
          then (2 : ℝ) ^ O.card else 0) + (2 : ℝ) ^ O.card * eB) := by
        exact Finset.sum_le_sum fun T hT ↦ hpoint T hT
    _ = (((C.powerset.filter fun T ↦
          (T.card : ℝ) ≤ (C.card : ℝ) / 2 - a).card : ℝ) *
          (2 : ℝ) ^ O.card) +
        (2 : ℝ) ^ C.card * ((2 : ℝ) ^ O.card * eB) := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, Finset.card_powerset,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ ((2 : ℝ) ^ C.card * Real.exp (-2 * a ^ 2 / C.card)) *
          (2 : ℝ) ^ O.card +
        (2 : ℝ) ^ C.card * ((2 : ℝ) ^ O.card * eB) := by
      gcongr
      exact Erdos622.Concentration.subsetCard_lowerTail C ha
    _ = (2 : ℝ) ^ Fintype.card V *
        (Real.exp (-2 * a ^ 2 / C.card) +
          Real.exp (-2 * b ^ 2 / C.card)) := by
      have hcards : C.card + O.card = Fintype.card V := by
        rw [← Finset.card_union_of_disjoint hCO, hCU, Finset.card_univ]
      have hpow : (2 : ℝ) ^ C.card * (2 : ℝ) ^ O.card =
          (2 : ℝ) ^ Fintype.card V := by
        rw [← pow_add, hcards]
      simp only [eB]
      rw [← hpow]
      ring

/-- The normalized error appearing after choosing both deviations in the
minimum-cover argument to be fixed multiples of the cover size. -/
noncomputable def minimumCoverFailureMajorant (eps : ℝ) (m : ℕ) : ℝ :=
  Real.exp ((-2 * eps ^ 2) * (m : ℝ)) +
    Real.exp (-(eps ^ 2 / 2) * (m : ℝ))

/-- Relative-error form of the finite DKM minimum-cover estimate.  Apart
from the displayed exceptional mass, a subset contains a matching with at
least `(1/4-eps)|C|` edges. -/
theorem minimumCover_randomMatching_count_relative
    {G : SimpleGraph V} {C : Finset V}
    (hC : IsMinimumVertexCover G C) {eps : ℝ}
    (heps : 0 ≤ eps) (hepsHalf : eps < 1 / 2)
    (hCpos : 0 < C.card) :
    ((((Finset.univ : Finset V).powerset.filter fun S ↦
        ¬ HasMatchingAtLeast G S
          ((1 / 4 - eps) * C.card)).card : ℝ)) ≤
      (2 : ℝ) ^ Fintype.card V *
        minimumCoverFailureMajorant eps C.card := by
  have hCr : (0 : ℝ) < C.card := by exact_mod_cast hCpos
  have harange : 2 * (eps * (C.card : ℝ)) < C.card := by
    nlinarith
  have h := minimumCover_randomMatching_count hC
    (a := eps * (C.card : ℝ)) (b := eps * (C.card : ℝ) / 2)
    (mul_nonneg heps hCr.le) (div_nonneg (mul_nonneg heps hCr.le) (by norm_num))
    hCpos harange
  have hCne : (C.card : ℝ) ≠ 0 := ne_of_gt hCr
  have hthreshold :
      (C.card : ℝ) / 4 - (eps * C.card) / 2 -
          (eps * C.card / 2) = (1 / 4 - eps) * C.card := by
    ring
  have hexp₁ :
      -2 * (eps * (C.card : ℝ)) ^ 2 / C.card =
        (-2 * eps ^ 2) * C.card := by
    field_simp
  have hexp₂ :
      -2 * (eps * (C.card : ℝ) / 2) ^ 2 / C.card =
        -(eps ^ 2 / 2) * C.card := by
    field_simp
  rw [hthreshold, hexp₁, hexp₂] at h
  simpa only [minimumCoverFailureMajorant] using h

/-- For every fixed positive relative error, the normalized exceptional
mass in the minimum-cover argument tends to zero with the cover size. -/
theorem minimumCoverFailureMajorant_tendsto_zero {eps : ℝ}
    (heps : 0 < eps) :
    Filter.Tendsto (minimumCoverFailureMajorant eps)
      Filter.atTop (nhds 0) := by
  have hepsSq : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hfirst : Filter.Tendsto
      (fun m : ℕ ↦ Real.exp ((-2 * eps ^ 2) * (m : ℝ)))
      Filter.atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by
      nlinarith)
  have hsecond : Filter.Tendsto
      (fun m : ℕ ↦ Real.exp (-(eps ^ 2 / 2) * (m : ℝ)))
      Filter.atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by
      nlinarith)
  change Filter.Tendsto
    (fun m : ℕ ↦ Real.exp ((-2 * eps ^ 2) * (m : ℝ)) +
      Real.exp (-(eps ^ 2 / 2) * (m : ℝ))) Filter.atTop (nhds 0)
  simpa only [add_zero] using hfirst.add hsecond

/-- Fully uniform eventually/epsilon form of DKM Lemma 4.4.  Once the
minimum cover has at least `m` vertices, the same threshold works for every
finite graph, and fewer than a `delta` fraction of all vertex subsets fail
to contain a matching of `(1/4-eps)|C|` edges. -/
theorem eventually_minimumCover_randomMatching_count_le
    {eps delta : ℝ} (heps : 0 < eps) (hepsHalf : eps < 1 / 2)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in Filter.atTop,
      ∀ (W : Type) [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) (C : Finset W),
        IsMinimumVertexCover G C → m ≤ C.card →
        ((((Finset.univ : Finset W).powerset.filter fun S ↦
            ¬ HasMatchingAtLeast G S
              ((1 / 4 - eps) * C.card)).card : ℝ)) ≤
          delta * (2 : ℝ) ^ Fintype.card W := by
  have hmajor : ∀ᶠ m : ℕ in Filter.atTop,
      minimumCoverFailureMajorant eps m < delta :=
    (minimumCoverFailureMajorant_tendsto_zero heps).eventually
      (gt_mem_nhds hdelta)
  filter_upwards [Filter.eventually_ge_atTop 1, hmajor] with m hm hmaj
  intro W instF instD G C hC hmC
  letI : Fintype W := instF
  letI : DecidableEq W := instD
  have hCpos : 0 < C.card := lt_of_lt_of_le hm hmC
  have hfinite := minimumCover_randomMatching_count_relative hC heps.le
    hepsHalf hCpos
  have hmR : (m : ℝ) ≤ C.card := by exact_mod_cast hmC
  have hcoeff₁ : (-2 * eps ^ 2) * (C.card : ℝ) ≤
      (-2 * eps ^ 2) * (m : ℝ) :=
    mul_le_mul_of_nonpos_left hmR (by nlinarith [sq_nonneg eps])
  have hcoeff₂ : -(eps ^ 2 / 2) * (C.card : ℝ) ≤
      -(eps ^ 2 / 2) * (m : ℝ) :=
    mul_le_mul_of_nonpos_left hmR (by nlinarith [sq_nonneg eps])
  have hmajorC : minimumCoverFailureMajorant eps C.card ≤
      minimumCoverFailureMajorant eps m := by
    exact add_le_add (Real.exp_le_exp.mpr hcoeff₁)
      (Real.exp_le_exp.mpr hcoeff₂)
  calc
    ((((Finset.univ : Finset W).powerset.filter fun S ↦
        ¬ HasMatchingAtLeast G S
          ((1 / 4 - eps) * C.card)).card : ℝ)) ≤
        (2 : ℝ) ^ Fintype.card W *
          minimumCoverFailureMajorant eps C.card := hfinite
    _ ≤ (2 : ℝ) ^ Fintype.card W *
        minimumCoverFailureMajorant eps m :=
      mul_le_mul_of_nonneg_left hmajorC (by positivity)
    _ ≤ delta * (2 : ℝ) ^ Fintype.card W := by
      nlinarith [show 0 < (2 : ℝ) ^ Fintype.card W by positivity]

/-- The specialization used for graphs on `2*n` vertices.  The conclusion
is already in unnormalized finite-count form, so it can be combined directly
with the other exceptional-family estimates in the random-good-cut proof. -/
theorem eventually_minimumCover_randomMatching_fin_two_mul
    {eps delta : ℝ} (heps : 0 < eps) (hepsHalf : eps < 1 / 2)
    (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n))) (C : Finset (Fin (2 * n))),
        IsMinimumVertexCover G C → n ≤ C.card →
        ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun S ↦
            ¬ HasMatchingAtLeast G S
              ((1 / 4 - eps) * C.card)).card : ℝ)) ≤
          delta * (2 : ℝ) ^ (2 * n) := by
  have h := eventually_minimumCover_randomMatching_count_le
    heps hepsHalf hdelta
  filter_upwards [h] with n hn
  intro G C hC hnC
  simpa only [Fintype.card_fin] using
    hn (Fin (2 * n)) G C hC hnC

/-- The exceptional proportion for a sequence of minimum covers in graphs
on `2*n` vertices. -/
noncomputable def minimumCoverBadProportionTwoMul
    (G : ∀ n : ℕ, SimpleGraph (Fin (2 * n)))
    (C : ∀ n : ℕ, Finset (Fin (2 * n)))
    (eps : ℝ) (n : ℕ) : ℝ :=
  ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun S ↦
      ¬ HasMatchingAtLeast (G n) S
        ((1 / 4 - eps) * (C n).card)).card : ℝ)) /
    (2 : ℝ) ^ (2 * n)

/-- Sequence-level asymptotic form of DKM Lemma 4.4: whenever the minimum
cover sizes tend to infinity, the proportion of subsets failing to contain
a `(1/4-eps)`-fractional matching tends to zero. -/
theorem minimumCoverBadProportionTwoMul_tendsto_zero
    (G : ∀ n : ℕ, SimpleGraph (Fin (2 * n)))
    (C : ∀ n : ℕ, Finset (Fin (2 * n)))
    (hC : ∀ n, IsMinimumVertexCover (G n) (C n))
    (hCgrow : Filter.Tendsto (fun n ↦ (C n).card)
      Filter.atTop Filter.atTop)
    {eps : ℝ} (heps : 0 < eps) (hepsHalf : eps < 1 / 2) :
    Filter.Tendsto (minimumCoverBadProportionTwoMul G C eps)
      Filter.atTop (nhds 0) := by
  have hmajor : Filter.Tendsto
      (fun n ↦ minimumCoverFailureMajorant eps (C n).card)
      Filter.atTop (nhds 0) :=
    (minimumCoverFailureMajorant_tendsto_zero heps).comp hCgrow
  refine squeeze_zero' (g := fun n ↦
    minimumCoverFailureMajorant eps (C n).card) ?_ ?_ hmajor
  · exact Filter.Eventually.of_forall fun n ↦ by
      exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · have hCpos : ∀ᶠ n : ℕ in Filter.atTop, 0 < (C n).card :=
      hCgrow (Filter.eventually_gt_atTop 0)
    filter_upwards [hCpos] with n hn
    have hfinite := minimumCover_randomMatching_count_relative
      (hC n) heps.le hepsHalf hn
    change
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun S ↦
          ¬ HasMatchingAtLeast (G n) S
            ((1 / 4 - eps) * (C n).card)).card : ℝ)) /
        (2 : ℝ) ^ (2 * n) ≤
          minimumCoverFailureMajorant eps (C n).card
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * n))]
    simpa only [Fintype.card_fin, mul_comm] using hfinite

/-- Fully quantified eventually/epsilon form for a growing sequence of
minimum covers. -/
theorem eventually_minimumCoverBadProportionTwoMul_lt
    (G : ∀ n : ℕ, SimpleGraph (Fin (2 * n)))
    (C : ∀ n : ℕ, Finset (Fin (2 * n)))
    (hC : ∀ n, IsMinimumVertexCover (G n) (C n))
    (hCgrow : Filter.Tendsto (fun n ↦ (C n).card)
      Filter.atTop Filter.atTop)
    {eps delta : ℝ} (heps : 0 < eps) (hepsHalf : eps < 1 / 2)
    (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      minimumCoverBadProportionTwoMul G C eps n < delta :=
  (minimumCoverBadProportionTwoMul_tendsto_zero G C hC hCgrow
    heps hepsHalf).eventually (gt_mem_nhds hdelta)

/-! ## Exact concentration for half-subsets -/

/-- The number of selected coordinates, written as a real-valued function on
the finite Boolean cube. -/
def trueCount (n : ℕ) (x : Fin n → Bool) : ℝ :=
  ∑ i, if x i then 1 else 0

lemma trueCount_cons (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    trueCount (n + 1) (Fin.cons b y) = (if b then 1 else 0) + trueCount n y := by
  unfold trueCount
  rw [Fin.sum_univ_succ]
  rfl

/-- Exact first moment of the cardinality of a uniform half-subset. -/
lemma trueCount_sum (n : ℕ) :
    (∑ x : Fin n → Bool, trueCount n x) = (2 : ℝ) ^ n * n / 2 := by
  induction n with
  | zero => simp [trueCount]
  | succ n ih =>
      rw [Erdos88.Concentration.sum_fin_succ_eq]
      simp_rw [trueCount_cons]
      rw [Finset.sum_eq_add false true] <;> try simp +decide
      rw [Finset.sum_add_distrib]
      simp [ih, pow_succ]
      ring

/-- Changing one coordinate changes the selected cardinality by at most one. -/
lemma trueCount_bdd (n : ℕ) (i : Fin n) (x y : Fin n → Bool)
    (h : ∀ j, j ≠ i → x j = y j) :
    |trueCount n x - trueCount n y| ≤ 1 := by
  simp only [trueCount]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hs : (∑ j ∈ Finset.univ.erase i, if x j then (1 : ℝ) else 0) =
      ∑ j ∈ Finset.univ.erase i, if y j then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [h j (Finset.ne_of_mem_erase hj)]
  rw [hs]
  split <;> split <;> norm_num

lemma trueCount_mean (n : ℕ) :
    (∑ x : Fin n → Bool, trueCount n x) / (2 : ℝ) ^ n = (n : ℝ) / 2 := by
  rw [trueCount_sum]
  field_simp

/-- Exact finite counting lower-tail bound for the cardinality of a uniform
half-subset. -/
theorem trueCount_lower_tail (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ((Finset.univ.filter fun x : Fin n → Bool ↦
        trueCount n x ≤ (n : ℝ) / 2 - t).card : ℝ) ≤
      (2 : ℝ) ^ n * Real.exp (-2 * t ^ 2 / n) := by
  have h := Erdos88.Concentration.cube_lower_tail n (trueCount n)
    (fun _ ↦ (1 : ℝ)) (trueCount_bdd n) (fun _ ↦ by norm_num) t ht
  have hsum : (∑ _ : Fin n, (1 : ℝ) ^ 2) = n := by simp
  rw [hsum] at h
  simpa only [trueCount_mean] using h

/-- Proportion of half-subsets whose cardinality lies `eps * n` below its
mean. -/
noncomputable def lowerTailProportion (eps : ℝ) (n : ℕ) : ℝ :=
  ((Finset.univ.filter fun x : Fin n → Bool ↦
      trueCount n x ≤ (n : ℝ) / 2 - eps * n).card : ℝ) / (2 : ℝ) ^ n

/-- The exceptional lower-tail proportion tends to zero. -/
theorem lowerTailProportion_tendsto_zero {eps : ℝ} (heps : 0 < eps) :
    Filter.Tendsto (lowerTailProportion eps) Filter.atTop (nhds 0) := by
  have hexp : Filter.Tendsto
      (fun n : ℕ ↦ Real.exp ((-2 * eps ^ 2) * (n : ℝ)))
      Filter.atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by
      nlinarith [sq_pos_of_pos heps])
  refine squeeze_zero' (g := fun n : ℕ ↦
    Real.exp ((-2 * eps ^ 2) * (n : ℝ))) ?_ ?_ hexp
  · exact Filter.Eventually.of_forall fun n ↦ by
      exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
    have hp := trueCount_lower_tail n (t := eps * n)
      (mul_nonneg heps.le (Nat.cast_nonneg n))
    change
      ((Finset.univ.filter fun x : Fin n → Bool ↦
          trueCount n x ≤ (n : ℝ) / 2 - eps * n).card : ℝ) / (2 : ℝ) ^ n ≤
        Real.exp ((-2 * eps ^ 2) * n)
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
    calc
      ((Finset.univ.filter fun x : Fin n → Bool ↦
          trueCount n x ≤ (n : ℝ) / 2 - eps * n).card : ℝ) ≤
          (2 : ℝ) ^ n * Real.exp (-2 * (eps * n) ^ 2 / n) := hp
      _ = (2 : ℝ) ^ n * Real.exp ((-2 * eps ^ 2) * n) := by
        congr 2
        field_simp
      _ = Real.exp ((-2 * eps ^ 2) * n) * (2 : ℝ) ^ n := by ring

/-- Explicit eventually/epsilon form of the preceding convergence theorem. -/
theorem eventually_lowerTailProportion_lt {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in Filter.atTop, lowerTailProportion eps n < delta :=
  (lowerTailProportion_tendsto_zero heps).eventually (gt_mem_nhds hdelta)

/-! ## Survival of a fixed matching -/

/-- The upper-tail companion to `cube_lower_tail`. -/
theorem cube_upper_tail :
    ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ) (b : Fin n → ℝ),
    (∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i) →
    (∀ i, 0 ≤ b i) →
    ∀ t : ℝ, t ≥ 0 →
    let mean := (∑ x : Fin n → Bool, f x) / (2 ^ n : ℝ)
    ((Finset.univ.filter fun x : Fin n → Bool ↦ mean + t ≤ f x).card : ℝ) ≤
      (2 ^ n : ℝ) * Real.exp (-2 * t ^ 2 / ∑ i, (b i) ^ 2) := by
  intro n f b hbd hb t ht
  have h := Erdos88.Concentration.cube_lower_tail n (fun x ↦ -f x) b (by
    intro i x y hxy
    simpa only [neg_sub_neg, abs_sub_comm] using hbd i x y hxy) hb t ht
  have heq :
      Finset.univ.filter (fun x : Fin n → Bool ↦
        -f x ≤ (∑ z, -f z) / (2 : ℝ) ^ n - t) =
      Finset.univ.filter (fun x : Fin n → Bool ↦
        (∑ z, f z) / (2 : ℝ) ^ n + t ≤ f x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.sum_neg_distrib, neg_div]
    constructor
    · intro hx
      rw [← neg_le_neg_iff]
      convert hx using 1 <;> ring
    · intro hx
      rw [← neg_le_neg_iff] at hx
      convert hx using 1 <;> ring
  dsimp only at h ⊢
  rw [heq] at h
  exact h

/-- Two-sided bounded-differences inequality on the Boolean cube. -/
theorem cube_two_sided_tail
    (n : ℕ) (f : (Fin n → Bool) → ℝ) (b : Fin n → ℝ)
    (hbd : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (hb : ∀ i, 0 ≤ b i) (t : ℝ) (ht : 0 ≤ t) :
    let mean := (∑ x : Fin n → Bool, f x) / (2 ^ n : ℝ)
    ((Finset.univ.filter fun x : Fin n → Bool ↦ |mean - f x| ≥ t).card : ℝ) ≤
      2 * ((2 ^ n : ℝ) * Real.exp (-2 * t ^ 2 / ∑ i, (b i) ^ 2)) := by
  let mean := (∑ x : Fin n → Bool, f x) / (2 ^ n : ℝ)
  let L := Finset.univ.filter fun x : Fin n → Bool ↦ f x ≤ mean - t
  let U := Finset.univ.filter fun x : Fin n → Bool ↦ mean + t ≤ f x
  have hsub :
      Finset.univ.filter (fun x : Fin n → Bool ↦ |mean - f x| ≥ t) ⊆ L ∪ U := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Finset.mem_union]
    simp only [L, U, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : f x ≤ mean - t
    · exact Or.inl h
    · right
      by_contra h'
      push_neg at h h'
      have habs : |mean - f x| < t := (abs_lt).2 ⟨by linarith, by linarith⟩
      linarith
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le L U
  have hlow := Erdos88.Concentration.cube_lower_tail n f b hbd hb t ht
  have hupp := cube_upper_tail n f b hbd hb t ht
  change ((Finset.univ.filter fun x : Fin n → Bool ↦ |mean - f x| ≥ t).card : ℝ) ≤ _
  have hcard' :
      ((Finset.univ.filter (fun x : Fin n → Bool ↦ |mean - f x| ≥ t)).card : ℝ) ≤
        ((L ∪ U).card : ℝ) := by exact_mod_cast hcard
  have hunion' : ((L ∪ U).card : ℝ) ≤ (L.card : ℝ) + U.card := by
    exact_mod_cast hunion
  change (L.card : ℝ) ≤ _ at hlow
  change (U.card : ℝ) ≤ _ at hupp
  linarith

lemma sum_fin_succ_eq_generic {D : Type*} [Fintype D]
    {n : ℕ} (f : (Fin (n + 1) → D) → ℝ) :
    ∑ x : Fin (n + 1) → D, f x =
      ∑ d : D, ∑ y : Fin n → D, f (Fin.cons d y) := by
  classical
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun x _ ↦ (x 0, x ∘ Fin.succ)) ?_ ?_ ?_ ?_
  · simp
  · intro x₁ x₂ _ _ h
    funext i
    induction i using Fin.inductionOn
    · exact congrArg Prod.fst h
    · exact congrFun (congrArg Prod.snd h) _
  · intro p _
    exact ⟨Fin.cons p.1 p.2, by simp⟩
  · intro x _
    congr
    ext i
    induction i using Fin.inductionOn <;> simp

/-- Number of indexed disjoint pairs whose two endpoint bits both survive. -/
def pairSurviveVec {m : ℕ} (z : Fin m → Bool × Bool) : ℝ :=
  ((Finset.univ.filter fun i ↦ (z i).1 = true ∧ (z i).2 = true).card : ℝ)

lemma pairSurviveVec_cons {m : ℕ} (b : Bool × Bool)
    (z : Fin m → Bool × Bool) :
    pairSurviveVec (Fin.cons b z) = pairSurviveVec z +
      if b.1 = true ∧ b.2 = true then 1 else 0 := by
  let C := Finset.univ.filter fun i : Fin m ↦ (z i).1 = true ∧ (z i).2 = true
  by_cases hb : b.1 = true ∧ b.2 = true
  · have hset :
        Finset.univ.filter (fun i : Fin (m + 1) ↦
          (@Fin.cons m (fun _ ↦ Bool × Bool) b z i).1 = true ∧
            (@Fin.cons m (fun _ ↦ Bool × Bool) b z i).2 = true) =
          insert 0 (C.map (Fin.succEmb m)) := by
      ext i
      induction i using Fin.cases with
      | zero => simp [C, hb]
      | succ i => simp [C]
    simp only [pairSurviveVec, hb, if_true]
    rw [hset]
    have hzero : (0 : Fin (m + 1)) ∉ C.map (Fin.succEmb m) := by simp
    rw [Finset.card_insert_of_notMem hzero, Finset.card_map]
    push_cast
    simp [C, hb, add_comm]
  · have hset :
        Finset.univ.filter (fun i : Fin (m + 1) ↦
          (@Fin.cons m (fun _ ↦ Bool × Bool) b z i).1 = true ∧
            (@Fin.cons m (fun _ ↦ Bool × Bool) b z i).2 = true) =
          C.map (Fin.succEmb m) := by
      ext i
      induction i using Fin.cases with
      | zero => simp [C, hb]
      | succ i => simp [C]
    simp only [pairSurviveVec, hb, if_false]
    rw [hset, Finset.card_map]
    simp [C]

lemma sum_pairSurviveVec (m : ℕ) :
    ∑ z : Fin m → Bool × Bool, pairSurviveVec z =
      (4 : ℝ) ^ m * (m : ℝ) / 4 := by
  induction m with
  | zero => simp [pairSurviveVec]
  | succ m ih =>
      rw [sum_fin_succ_eq_generic, Finset.sum_comm]
      have hhead : ∑ b : Bool × Bool,
          (if b.1 = true ∧ b.2 = true then (1 : ℝ) else 0) = 1 := by
        norm_num [Fintype.sum_prod_type, Fintype.sum_bool]
        decide
      have hinner : ∀ z : Fin m → Bool × Bool,
          ∑ b : Bool × Bool, pairSurviveVec (Fin.cons b z) =
            4 * pairSurviveVec z + 1 := by
        intro z
        simp_rw [pairSurviveVec_cons]
        rw [Finset.sum_add_distrib, hhead, Finset.sum_const,
          Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
        norm_num
      simp_rw [hinner]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ih]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul]
      norm_num [pow_succ]
      push_cast
      ring

/-- Split two Boolean blocks into the two endpoints of each indexed pair. -/
def pairVecEquiv (m : ℕ) :
    (Fin m → Bool × Bool) ≃ (Fin (m + m) → Bool) where
  toFun z := Fin.addCases (fun i ↦ (z i).1) (fun i ↦ (z i).2)
  invFun x := fun i ↦ (x (Fin.castAdd m i), x (Fin.natAdd m i))
  left_inv z := by
    funext i
    apply Prod.ext
    · change Fin.addCases (fun i ↦ (z i).1) (fun i ↦ (z i).2)
          (Fin.castAdd m i) = (z i).1
      exact Fin.addCases_left i
    · change Fin.addCases (fun i ↦ (z i).1) (fun i ↦ (z i).2)
          (Fin.natAdd m i) = (z i).2
      exact Fin.addCases_right i
  right_inv x := by
    funext i
    exact Fin.addCases_castAdd_natAdd x i

/-- Number of surviving edges in the canonical matching of size `m`. -/
def pairSurvive (m : ℕ) (x : Fin (m + m) → Bool) : ℝ :=
  ((Finset.univ.filter fun i : Fin m ↦
      x (Fin.castAdd m i) = true ∧ x (Fin.natAdd m i) = true).card : ℝ)

@[simp] lemma pairSurvive_pairVecEquiv (m : ℕ) (z : Fin m → Bool × Bool) :
    pairSurvive m (pairVecEquiv m z) = pairSurviveVec z := by
  unfold pairSurvive pairSurviveVec pairVecEquiv
  apply congrArg Nat.cast
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (Fin.addCases (fun i ↦ (z i).1) (fun i ↦ (z i).2)
      (Fin.castAdd m i) = true ∧
    Fin.addCases (fun i ↦ (z i).1) (fun i ↦ (z i).2)
      (Fin.natAdd m i) = true) ↔ _
  rw [Fin.addCases_left, Fin.addCases_right]

lemma sum_pairSurvive (m : ℕ) :
    ∑ x : Fin (m + m) → Bool, pairSurvive m x =
      (2 : ℝ) ^ (m + m) * (m : ℝ) / 4 := by
  rw [← (pairVecEquiv m).sum_comp]
  simp only [pairSurvive_pairVecEquiv, sum_pairSurviveVec]
  rw [show (4 : ℝ) ^ m = (2 : ℝ) ^ m * (2 : ℝ) ^ m by
    rw [← mul_pow]
    norm_num]
  rw [pow_add]

lemma pairSurvive_boundedDiff (m : ℕ) (j : Fin (m + m))
    (x y : Fin (m + m) → Bool)
    (hxy : ∀ k, k ≠ j → x k = y k) :
    |pairSurvive m x - pairSurvive m y| ≤ 1 := by
  induction j using Fin.addCases with
  | left i =>
      let px : Fin m → Bool := fun k ↦ x (Fin.castAdd m k) && x (Fin.natAdd m k)
      let py : Fin m → Bool := fun k ↦ y (Fin.castAdd m k) && y (Fin.natAdd m k)
      have hx : pairSurvive m x = trueCount m px := by
        simp [pairSurvive, trueCount, px, Bool.and_eq_true]
      have hy : pairSurvive m y = trueCount m py := by
        simp [pairSurvive, trueCount, py, Bool.and_eq_true]
      rw [hx, hy]
      apply trueCount_bdd m i
      intro k hki
      have hleft : x (Fin.castAdd m k) = y (Fin.castAdd m k) :=
        hxy _ (by simpa using hki)
      have hright : x (Fin.natAdd m k) = y (Fin.natAdd m k) :=
        hxy _ (by
          intro heq
          have hv := congrArg Fin.val heq
          simp at hv
          omega)
      simp only [px, py, hleft, hright]
  | right i =>
      let px : Fin m → Bool := fun k ↦ x (Fin.castAdd m k) && x (Fin.natAdd m k)
      let py : Fin m → Bool := fun k ↦ y (Fin.castAdd m k) && y (Fin.natAdd m k)
      have hx : pairSurvive m x = trueCount m px := by
        simp [pairSurvive, trueCount, px, Bool.and_eq_true]
      have hy : pairSurvive m y = trueCount m py := by
        simp [pairSurvive, trueCount, py, Bool.and_eq_true]
      rw [hx, hy]
      apply trueCount_bdd m i
      intro k hki
      have hleft : x (Fin.castAdd m k) = y (Fin.castAdd m k) :=
        hxy _ (by
          intro heq
          have hv := congrArg Fin.val heq
          simp at hv
          omega)
      have hright : x (Fin.natAdd m k) = y (Fin.natAdd m k) :=
        hxy _ (by simpa using hki)
      simp only [px, py, hleft, hright]

lemma pairSurvive_mean (m : ℕ) :
    (∑ x : Fin (m + m) → Bool, pairSurvive m x) /
      (2 : ℝ) ^ (m + m) = (m : ℝ) / 4 := by
  rw [sum_pairSurvive]
  field_simp

/-- Exact two-sided concentration around the one-quarter survival rate for a
fixed matching. -/
theorem pairSurvive_concentration (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((Finset.univ.filter fun x : Fin (m + m) → Bool ↦
        |pairSurvive m x - (m : ℝ) / 4| ≥ t).card : ℝ) ≤
      2 * (2 : ℝ) ^ (m + m) * Real.exp (-t ^ 2 / m) := by
  have h := cube_two_sided_tail (m + m) (pairSurvive m) (fun _ ↦ 1)
    (fun j x y hxy ↦ pairSurvive_boundedDiff m j x y hxy)
    (fun _ ↦ by norm_num) t ht
  rw [pairSurvive_mean] at h
  simp only [abs_sub_comm, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, one_pow, Nat.cast_add,
    mul_assoc] at h
  by_cases hm : m = 0
  · subst m
    simpa using h
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hexp : -2 * t ^ 2 / ((m : ℝ) + m) = -t ^ 2 / m := by
      field_simp
      ring
    rw [hexp] at h
    simpa only [abs_sub_comm, mul_assoc] using h

/-- Bad proportion for one-quarter survival in the canonical matching. -/
noncomputable def pairBadProportion (eps : ℝ) (m : ℕ) : ℝ :=
  ((Finset.univ.filter fun x : Fin (m + m) → Bool ↦
      |pairSurvive m x - (m : ℝ) / 4| ≥ eps * m).card : ℝ) /
    (2 : ℝ) ^ (m + m)

/-- The proportion of subsets on which a fixed matching fails the
one-quarter survival estimate tends to zero. -/
theorem pairBadProportion_tendsto_zero {eps : ℝ} (heps : 0 < eps) :
    Filter.Tendsto (pairBadProportion eps) Filter.atTop (nhds 0) := by
  have hexp : Filter.Tendsto
      (fun m : ℕ ↦ 2 * Real.exp ((-eps ^ 2) * (m : ℝ)))
      Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto
        (fun m : ℕ ↦ Real.exp ((-eps ^ 2) * (m : ℝ)))
        Filter.atTop (nhds 0) := by
      apply Real.tendsto_exp_atBot.comp
      exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by
        nlinarith [sq_pos_of_pos heps])
    simpa using hbase.const_mul 2
  refine squeeze_zero' (g := fun m : ℕ ↦
    2 * Real.exp ((-eps ^ 2) * (m : ℝ))) ?_ ?_ hexp
  · exact Filter.Eventually.of_forall fun m ↦ by
      exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · filter_upwards [Filter.eventually_gt_atTop 0] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hm)
    have hp := pairSurvive_concentration m (eps * m)
      (mul_nonneg heps.le (Nat.cast_nonneg m))
    change
      ((Finset.univ.filter fun x : Fin (m + m) → Bool ↦
          |pairSurvive m x - (m : ℝ) / 4| ≥ eps * m).card : ℝ) /
          (2 : ℝ) ^ (m + m) ≤
        2 * Real.exp ((-eps ^ 2) * m)
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (m + m))]
    calc
      ((Finset.univ.filter fun x : Fin (m + m) → Bool ↦
          |pairSurvive m x - (m : ℝ) / 4| ≥ eps * m).card : ℝ) ≤
          2 * (2 : ℝ) ^ (m + m) * Real.exp (-(eps * m) ^ 2 / m) := hp
      _ = (2 * Real.exp ((-eps ^ 2) * m)) * (2 : ℝ) ^ (m + m) := by
        have hexponent : -(eps * (m : ℝ)) ^ 2 / (m : ℝ) =
            (-eps ^ 2) * (m : ℝ) := by
          field_simp
        rw [hexponent]
        ring

/-- Eventually/epsilon form of fixed-matching one-quarter survival. -/
theorem eventually_pairBadProportion_lt {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in Filter.atTop, pairBadProportion eps m < delta :=
  (pairBadProportion_tendsto_zero heps).eventually (gt_mem_nhds hdelta)

/-! ## Powerset form of the one-quarter law -/

private lemma card_filter_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : B → Prop) [DecidablePred P] :
    (Finset.univ.filter fun a ↦ P (e a)).card =
      (Finset.univ.filter P).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv fun _ ↦ Iff.rfl)

/-- The standard equivalence between Boolean indicator functions and finite
subsets.  It is used only to transport an already proved counting bound, so
no probability space is hidden in the statement. -/
def boolFunEquivFinset (I : Type*) [Fintype I] [DecidableEq I] :
    (I → Bool) ≃ Finset I where
  toFun x := Finset.univ.filter fun i ↦ x i = true
  invFun S := fun i ↦ decide (i ∈ S)
  left_inv x := by
    funext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases x i <;> simp
  right_inv S := by
    ext i
    simp

/-- Number of canonical matching edges whose two endpoints lie in `S`. -/
def canonicalPairCount (m : ℕ) (S : Finset (Fin (m + m))) : ℝ :=
  ((Finset.univ.filter fun i : Fin m ↦
      Fin.castAdd m i ∈ S ∧ Fin.natAdd m i ∈ S).card : ℝ)

@[simp] lemma canonicalPairCount_boolFunEquivFinset
    (m : ℕ) (x : Fin (m + m) → Bool) :
    canonicalPairCount m (boolFunEquivFinset (Fin (m + m)) x) =
      pairSurvive m x := by
  unfold canonicalPairCount boolFunEquivFinset pairSurvive
  congr 2
  ext i
  simp

/-- Finite-powerset counting form of concentration for a matching: apart
from the displayed exceptional family, a uniformly selected vertex subset
spans `m/4 ± t` of the `m` disjoint canonical edges. -/
theorem canonicalPairCount_powerset_concentration
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((((Finset.univ : Finset (Fin (m + m))).powerset.filter fun S ↦
        |canonicalPairCount m S - (m : ℝ) / 4| ≥ t).card : ℝ)) ≤
      2 * (2 : ℝ) ^ (m + m) * Real.exp (-t ^ 2 / m) := by
  have h := pairSurvive_concentration m t ht
  have hcard := card_filter_comp_equiv
    (boolFunEquivFinset (Fin (m + m)))
    (fun S : Finset (Fin (m + m)) ↦
      |canonicalPairCount m S - (m : ℝ) / 4| ≥ t)
  have hcard' :
      (Finset.univ.filter fun x : Fin (m + m) → Bool ↦
          |pairSurvive m x - (m : ℝ) / 4| ≥ t).card =
        ((Finset.univ : Finset (Fin (m + m))).powerset.filter fun S ↦
          |canonicalPairCount m S - (m : ℝ) / 4| ≥ t).card := by
    simpa using hcard
  rw [hcard'] at h
  exact h

/-- Exceptional proportion in the literal powerset sample space. -/
noncomputable def pairPowersetBadProportion (eps : ℝ) (m : ℕ) : ℝ :=
  ((((Finset.univ : Finset (Fin (m + m))).powerset.filter fun S ↦
      |canonicalPairCount m S - (m : ℝ) / 4| ≥ eps * m).card : ℝ)) /
    (2 : ℝ) ^ (m + m)

lemma pairPowersetBadProportion_eq (eps : ℝ) (m : ℕ) :
    pairPowersetBadProportion eps m = pairBadProportion eps m := by
  unfold pairPowersetBadProportion pairBadProportion
  have hcard := card_filter_comp_equiv
    (boolFunEquivFinset (Fin (m + m)))
    (fun S : Finset (Fin (m + m)) ↦
      |canonicalPairCount m S - (m : ℝ) / 4| ≥ eps * m)
  have hcard' :
      (Finset.univ.filter fun x : Fin (m + m) → Bool ↦
          |pairSurvive m x - (m : ℝ) / 4| ≥ eps * m).card =
        ((Finset.univ : Finset (Fin (m + m))).powerset.filter fun S ↦
          |canonicalPairCount m S - (m : ℝ) / 4| ≥ eps * m).card := by
    simpa using hcard
  rw [hcard']

/-- Explicit asymptotic one-quarter law in finite-powerset language. -/
theorem pairPowersetBadProportion_tendsto_zero {eps : ℝ} (heps : 0 < eps) :
    Filter.Tendsto (pairPowersetBadProportion eps) Filter.atTop (nhds 0) := by
  rw [show pairPowersetBadProportion eps = pairBadProportion eps by
    funext m
    exact pairPowersetBadProportion_eq eps m]
  exact pairBadProportion_tendsto_zero heps

/-- Fully quantified eventually/epsilon form of the powerset one-quarter
law: for every relative error and every exceptional-mass tolerance, all
sufficiently large matchings satisfy the required estimate. -/
theorem eventually_pairPowersetBadProportion_lt {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in Filter.atTop, pairPowersetBadProportion eps m < delta :=
  (pairPowersetBadProportion_tendsto_zero heps).eventually
    (gt_mem_nhds hdelta)

end RandomCover

end Erdos622
