/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.EdmondsGallaiDecomposition
import ErdosProblems.Erdos547b.GallaiEdmonds
import ErdosProblems.Erdos547b.Stability

open scoped SimpleGraph

noncomputable section

namespace GallaiEdmonds547Port

open SimpleGraph

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The matching assembled from all factor-critical components and the
separator bridges in a Gallai--Edmonds witness.  `representative C` is the
one vertex omitted by the internal near-perfect matching of `C`; in a
component targeted by the separator it is the bridge endpoint and hence is
covered by the bridge matching. -/
structure ZhaoGallaiEdmondsMatching (Z : ZhaoGallaiEdmondsWitness H) where
  representative : (C : (H.induce Z.separatorᶜ).ConnectedComponent) → C.supp
  representative_injective : Function.Injective
    (fun C ↦ (representative C).1.1 :
      (H.induce Z.separatorᶜ).ConnectedComponent → W)
  bridge_representative : ∀ s : Z.separator,
    (representative (Z.targetComponent s)).1.1 = (Z.bridgeVertex s).1.1
  M : H.Subgraph
  isMatching : M.IsMatching
  uncovered_eq : M.vertsᶜ =
    Set.range (fun C ↦ (representative C).1.1) \
      Set.range (fun s : Z.separator ↦ (Z.bridgeVertex s).1.1)
  edge_location : ∀ ⦃u v : W⦄, M.Adj u v →
    (∃ s : Z.separator,
        (u = s.1 ∧ v = (Z.bridgeVertex s).1.1) ∨
        (v = s.1 ∧ u = (Z.bridgeVertex s).1.1)) ∨
      ∃ C : (H.induce Z.separatorᶜ).ConnectedComponent,
        ∃ (u' v' : ↑(Z.separatorᶜ : Set W)),
          u'.1 = u ∧ v'.1 = v ∧ u' ∈ C.supp ∧ v' ∈ C.supp

theorem ZhaoGallaiEdmondsWitness.exists_assembledMatching
    (Z : ZhaoGallaiEdmondsWitness H) :
    Nonempty (ZhaoGallaiEdmondsMatching H Z) := by
  classical
  let K : SimpleGraph ↑(Z.separatorᶜ : Set W) := H.induce Z.separatorᶜ
  let representative : (C : K.ConnectedComponent) → C.supp := fun C ↦
    if h : ∃ s : Z.separator, Z.targetComponent s = C then
      let s := Classical.choose h
      ⟨(Z.bridgeVertex s).1, by
        rw [← Classical.choose_spec h]
        exact (Z.bridgeVertex s).2⟩
    else
      ⟨Classical.choose C.nonempty_supp, Classical.choose_spec C.nonempty_supp⟩
  have representative_bridge (s : Z.separator) :
      (representative (Z.targetComponent s)).1 = (Z.bridgeVertex s).1 := by
    unfold representative
    split
    · rename_i h
      dsimp only
      have ht : Classical.choose h = s :=
        Z.targetComponent_injective (Classical.choose_spec h)
      rw [ht]
    · rename_i h
      exact (h ⟨s, rfl⟩).elim
  have representative_injective : Function.Injective
      (fun C ↦ (representative C).1.1 : K.ConnectedComponent → W) := by
    intro C D hCD
    apply ConnectedComponent.eq_of_common_vertex
        (v := (representative C).1)
    · exact (representative C).2
    · have hv : (representative C).1 = (representative D).1 :=
        Subtype.ext hCD
      rw [hv]
      exact (representative D).2
  choose N hN_matching hN_support using fun C : K.ConnectedComponent ↦
    (Z.component_factorCritical C).2 (representative C).1 (representative C).2
  have hN_verts (C : K.ConnectedComponent) :
      (N C).verts = C.supp \ {(representative C).1} := by
    rw [← (hN_matching C).support_eq_verts, hN_support C]
  have hN_pairwise : Pairwise fun C D : K.ConnectedComponent ↦
      Disjoint (N C).support (N D).support := by
    intro C D hCD
    rw [hN_support C, hN_support D]
    exact Disjoint.mono Set.sdiff_subset Set.sdiff_subset
      (K.pairwise_disjoint_supp_connectedComponent hCD)
  let Nall : K.Subgraph := ⨆ C : K.ConnectedComponent, N C
  have hNall_matching : Nall.IsMatching :=
    Subgraph.IsMatching.iSup hN_matching hN_pairwise
  let emb : K ↪g H := SimpleGraph.Embedding.induce Z.separatorᶜ
  let e : K →g H := emb.toHom
  let Q : H.Subgraph := Nall.map e
  have hQ_matching : Q.IsMatching :=
    hNall_matching.map e emb.injective
  have hQ_verts : Q.verts = Z.separatorᶜ \
      Set.range (fun C ↦ (representative C).1.1) := by
    ext v
    constructor
    · intro hv
      rw [Subgraph.map_verts] at hv
      rcases hv with ⟨v', hvC, hv'v⟩
      rw [Subgraph.verts_iSup] at hvC
      rcases Set.mem_iUnion.mp hvC with ⟨C, hvC⟩
      have hvC' : v' ∈ C.supp \ {(representative C).1} := by
        rwa [hN_verts C] at hvC
      refine ⟨?_, ?_⟩
      · rw [← hv'v]
        exact v'.2
      · rintro ⟨D, hDv⟩
        have hcommon : C = D := by
          apply ConnectedComponent.eq_of_common_vertex (v := v')
          · exact hvC'.1
          · have hv'rep : v' = (representative D).1 := by
              apply Subtype.ext
              exact hv'v.trans hDv.symm
            rw [hv'rep]
            exact (representative D).2
        apply hvC'.2
        simp only [Set.mem_singleton_iff]
        apply Subtype.ext
        rw [hcommon]
        exact hv'v.trans hDv.symm
    · rintro ⟨hvS, hvrep⟩
      let v' : ↑(Z.separatorᶜ : Set W) := ⟨v, hvS⟩
      have hvuniv : v' ∈ (Set.univ : Set ↑(Z.separatorᶜ : Set W)) := Set.mem_univ _
      rw [← K.iUnion_connectedComponentSupp] at hvuniv
      rcases Set.mem_iUnion.mp hvuniv with ⟨C, hvC⟩
      rw [Subgraph.map_verts]
      refine ⟨v', ?_, rfl⟩
      rw [Subgraph.verts_iSup]
      apply Set.mem_iUnion.mpr
      refine ⟨C, ?_⟩
      rw [hN_verts C]
      refine ⟨hvC, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hv'eq
      apply hvrep
      refine ⟨C, ?_⟩
      exact congrArg Subtype.val hv'eq.symm
  let f : Z.separator → ↑(Z.separatorᶜ : Set W) :=
    fun s ↦ (Z.bridgeVertex s).1
  have hf : Function.Injective f := by
    intro s t hst
    apply Z.targetComponent_injective
    apply ConnectedComponent.eq_of_common_vertex (v := f s)
    · exact (Z.bridgeVertex s).2
    · have hval : (f s).1 = (f t).1 := congrArg Subtype.val hst
      have hsub : f s = f t := Subtype.ext hval
      rw [hsub]
      exact (Z.bridgeVertex t).2
  have hadj : ∀ s : Z.separator, H.Adj s (f s) := Z.bridge_adj
  let P : H.Subgraph := ⨆ s : Z.separator, H.subgraphOfAdj (hadj s)
  have hP_pairwise : Pairwise fun s t : Z.separator ↦
      Disjoint (H.subgraphOfAdj (hadj s)).support
        (H.subgraphOfAdj (hadj t)).support := by
    intro s t hst
    rw [(Subgraph.IsMatching.subgraphOfAdj (hadj s)).support_eq_verts,
      (Subgraph.IsMatching.subgraphOfAdj (hadj t)).support_eq_verts,
      subgraphOfAdj_verts, subgraphOfAdj_verts]
    simp only [Set.disjoint_left, Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro v (rfl | rfl) (hvs | hvs)
    · exact hst (Subtype.ext hvs)
    · exact (f t).2 (hvs ▸ s.2)
    · exact (f s).2 (hvs ▸ t.2)
    · exact hst (hf (Subtype.ext hvs))
  have hP_matching : P.IsMatching :=
    Subgraph.IsMatching.iSup (fun s ↦ Subgraph.IsMatching.subgraphOfAdj (hadj s))
      hP_pairwise
  have hP_verts : P.verts =
      Z.separator ∪ Set.range (fun s : Z.separator ↦ (Z.bridgeVertex s).1.1) := by
    ext v
    simp only [P, Subgraph.verts_iSup, Set.mem_iUnion, subgraphOfAdj_verts,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_range]
    constructor
    · rintro ⟨s, rfl | rfl⟩
      · exact Or.inl s.2
      · exact Or.inr ⟨s, rfl⟩
    · rintro (hvS | ⟨s, rfl⟩)
      · exact ⟨⟨v, hvS⟩, Or.inl rfl⟩
      · exact ⟨s, Or.inr rfl⟩
  have hP_edge ⦃u v : W⦄ (huv : P.Adj u v) :
      ∃ s : Z.separator,
        (u = s.1 ∧ v = (Z.bridgeVertex s).1.1) ∨
        (v = s.1 ∧ u = (Z.bridgeVertex s).1.1) := by
    obtain ⟨s, hs⟩ := Subgraph.iSup_adj.mp huv
    refine ⟨s, ?_⟩
    simp only [subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk] at hs
    rcases hs with hs | hs
    · exact Or.inl ⟨hs.1.symm, hs.2.symm⟩
    · exact Or.inr ⟨hs.1.symm, hs.2.symm⟩
  have hP_Q_disjoint : Disjoint P.support Q.support := by
    rw [hP_matching.support_eq_verts, hQ_matching.support_eq_verts, Set.disjoint_iff]
    rintro v ⟨hvP, hvQ⟩
    rw [hP_verts] at hvP
    rw [Subgraph.map_verts] at hvQ
    rcases hvQ with ⟨v', hvC, hv'v⟩
    rw [Subgraph.verts_iSup] at hvC
    rcases Set.mem_iUnion.mp hvC with ⟨C, hvC⟩
    rcases hvP with hvS | hvbridge
    · rw [← hv'v] at hvS
      exact v'.2 hvS
    · rcases hvbridge with ⟨s, rfl⟩
      change v'.1 = (Z.bridgeVertex s).1.1 at hv'v
      have hcomponent : C = Z.targetComponent s := by
        apply ConnectedComponent.eq_of_common_vertex (v := f s)
        · have hmem : v' ∈ C.supp \ {(representative C).1} := by
            rw [← hN_verts C]
            exact hvC
          have hv'eq : v' = f s := Subtype.ext hv'v
          rw [hv'eq] at hmem
          exact hmem.1
        · exact (Z.bridgeVertex s).2
      have hmem : v' ∈ C.supp \ {(representative C).1} := by
        rw [← hN_verts C]
        exact hvC
      have hv'eq : v' = (representative C).1 := by
        apply Subtype.ext
        rw [hcomponent, representative_bridge]
        exact hv'v
      exact hmem.2 (by simpa using hv'eq)
  let M : H.Subgraph := P ⊔ Q
  have hM_matching : M.IsMatching :=
    Subgraph.IsMatching.sup hP_matching hQ_matching hP_Q_disjoint
  refine ⟨{
    representative := representative
    representative_injective := representative_injective
    bridge_representative := fun s ↦ congrArg Subtype.val (representative_bridge s)
    M := M
    isMatching := hM_matching
    uncovered_eq := ?_
    edge_location := ?_ }⟩
  · ext v
    change v ∉ M.verts ↔
      v ∈ Set.range (fun C ↦ (representative C).1.1) ∧
        v ∉ Set.range (fun s : Z.separator ↦ (Z.bridgeVertex s).1.1)
    rw [show M.verts = P.verts ∪ Q.verts by
      exact Subgraph.verts_sup P Q]
    rw [hP_verts, hQ_verts]
    constructor
    · intro hv
      have hvS : v ∉ Z.separator := by
        intro hvS
        exact hv (Or.inl (Or.inl hvS))
      have hvbridge : v ∉
          Set.range (fun s : Z.separator ↦ (Z.bridgeVertex s).1.1) := by
        intro hvbridge
        exact hv (Or.inl (Or.inr hvbridge))
      refine ⟨?_, hvbridge⟩
      by_contra hvrep
      apply hv
      right
      exact ⟨hvS, hvrep⟩
    · rintro ⟨⟨C, hCv⟩, hvbridge⟩ hv
      change (representative C).1.1 = v at hCv
      rcases hv with (hvS | hvbridge') | ⟨-, hvrep⟩
      · have hsepcompl : (representative C).1.1 ∈ Z.separatorᶜ :=
          (representative C).1.2
        apply hsepcompl
        rw [hCv]
        exact hvS
      · exact hvbridge hvbridge'
      · exact hvrep ⟨C, hCv⟩
  · intro u v huv
    change (P ⊔ Q).Adj u v at huv
    rcases Subgraph.sup_adj.mp huv with huvP | huvQ
    · exact Or.inl (hP_edge huvP)
    · right
      rw [Subgraph.map_adj] at huvQ
      rcases huvQ with ⟨u', v', huv', hu'u, hv'v⟩
      change u'.1 = u at hu'u
      change v'.1 = v at hv'v
      obtain ⟨C, hC⟩ := Subgraph.iSup_adj.mp huv'
      refine ⟨C, u', v', ?_, ?_, ?_, ?_⟩
      · exact hu'u
      · exact hv'v
      · have huverts : u' ∈ (N C).verts := (N C).edge_vert hC
        rw [hN_verts C] at huverts
        exact huverts.1
      · have hvverts : v' ∈ (N C).verts := (N C).edge_vert hC.symm
        rw [hN_verts C] at hvverts
        exact hvverts.1

end GallaiEdmonds547Port

namespace Erdos547b.ZhaoStability

open SimpleGraph
open GallaiEdmonds547Port

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Natural-number form of Zhao's Claim 6.7.  The hypotheses are the
reduced-graph data supplied by Claim 6.1: the graph has `2*k` clusters,
`L` has at least `k-c` members, every member of `L` has degree at least
`k-c`, and `L` is not independent.  No conclusion of `Claim67Certificate`
is assumed. -/
theorem exists_claim67Certificate_of_reducedGraph
    (R : SimpleGraph W) [DecidableRel R.Adj]
    (L : Finset W) (k c : ℕ)
    (hcard : Fintype.card W = 2 * k)
    (hL_card : k - c ≤ L.card)
    (hL_degree : ∀ v ∈ L, k - c ≤ R.degree v)
    (hL_nonindependent : ¬ R.IsIndepSet (L : Set W)) :
    Nonempty (Claim67Certificate R L (2 * c + 1)) := by
  classical
  let Z : ZhaoGallaiEdmondsWitness R :=
    Classical.choice (exists_zhaoGallaiEdmondsWitness R)
  let A : ZhaoGallaiEdmondsMatching R Z :=
    Classical.choice (Z.exists_assembledMatching R)
  let K : SimpleGraph ↑(Z.separatorᶜ : Set W) := R.induce Z.separatorᶜ
  let sep : Finset W := Z.separator.toFinite.toFinset
  let rep : Finset W := Finset.univ.image
    (fun C : K.ConnectedComponent ↦ (A.representative C).1.1)
  let bridge : Finset W := Finset.univ.image
    (fun s : Z.separator ↦ (Z.bridgeVertex s).1.1)
  let uncovered : Finset W := Finset.univ \ matchingSupport A.M
  have hrep_card : rep.card = Fintype.card K.ConnectedComponent := by
    calc
      rep.card = (Finset.univ : Finset K.ConnectedComponent).card := by
        apply Finset.card_image_iff.mpr
        exact fun C _ D _ h ↦ A.representative_injective h
      _ = Fintype.card K.ConnectedComponent := Finset.card_univ
  have hbridge_card : bridge.card = sep.card := by
    calc
      bridge.card = (Finset.univ : Finset Z.separator).card := by
        apply Finset.card_image_iff.mpr
        intro s _ t _ hst
        exact Z.bridgeVertex_injective R hst
      _ = sep.card := by simp [sep]
  have hbridge_subset_rep : bridge ⊆ rep := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨s, -, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨Z.targetComponent s, Finset.mem_univ _, ?_⟩
    exact A.bridge_representative s
  have huncovered_eq : uncovered = rep \ bridge := by
    ext v
    simp only [uncovered, Finset.mem_sdiff, Finset.mem_univ, true_and,
      mem_matchingSupport, rep, bridge, Finset.mem_image, Finset.mem_univ,
      true_and]
    rw [← Set.mem_compl_iff, A.uncovered_eq]
    simp only [Set.mem_sdiff, Set.mem_range]
    rfl
  have huncovered_add_sep : uncovered.card + sep.card = rep.card := by
    rw [huncovered_eq, ← hbridge_card]
    exact Finset.card_sdiff_add_card_eq_card hbridge_subset_rep
  let compVerts (C : K.ConnectedComponent) : Finset W :=
    C.supp.toFinite.toFinset.image Subtype.val
  have hcomp_card (C : K.ConnectedComponent) :
      (compVerts C).card = C.supp.ncard := by
    calc
      (compVerts C).card = C.supp.toFinite.toFinset.card := by
        apply Finset.card_image_iff.mpr
        exact fun x _ y _ h ↦ Subtype.ext h
      _ = C.supp.ncard := by
        simp [Set.ncard_eq_toFinset_card']
  have mem_compVerts (C : K.ConnectedComponent) (v : W) :
      v ∈ compVerts C ↔
        ∃ v' : ↑(Z.separatorᶜ : Set W), v'.1 = v ∧ v' ∈ C.supp := by
    simp [compVerts]
  have component_degree_upper (C : K.ConnectedComponent)
      (v' : ↑(Z.separatorᶜ : Set W)) (hvC : v' ∈ C.supp) :
      R.degree v'.1 ≤ sep.card + (compVerts C).card - 1 := by
    have hvcomp : v'.1 ∈ compVerts C :=
      (mem_compVerts C v'.1).2 ⟨v', rfl, hvC⟩
    have hsub : R.neighborFinset v'.1 ⊆
        sep ∪ (compVerts C).erase v'.1 := by
      intro w hw
      have hadj : R.Adj v'.1 w := (R.mem_neighborFinset v'.1 w).1 hw
      by_cases hwS : w ∈ Z.separator
      · apply Finset.mem_union_left
        simpa [sep, Set.Finite.mem_toFinset] using hwS
      · apply Finset.mem_union_right
        apply Finset.mem_erase.mpr
        refine ⟨hadj.ne', ?_⟩
        let w' : ↑(Z.separatorᶜ : Set W) := ⟨w, hwS⟩
        apply (mem_compVerts C w).2
        refine ⟨w', rfl, ?_⟩
        exact (C.mem_supp_congr_adj (show K.Adj v' w' from hadj)).1 hvC
    calc
      R.degree v'.1 = (R.neighborFinset v'.1).card := by
        rw [R.card_neighborFinset_eq_degree]
      _ ≤ (sep ∪ (compVerts C).erase v'.1).card :=
        Finset.card_le_card hsub
      _ ≤ sep.card + ((compVerts C).erase v'.1).card :=
        Finset.card_union_le _ _
      _ = sep.card + (compVerts C).card - 1 := by
        rw [Finset.card_erase_of_mem hvcomp]
        have hpos : 0 < (compVerts C).card := Finset.card_pos.mpr ⟨v'.1, hvcomp⟩
        omega
  have hsep_disjoint_comp (C : K.ConnectedComponent) :
      Disjoint sep (compVerts C) := by
    rw [Finset.disjoint_left]
    intro v hvS hvC
    have hvS' : v ∈ Z.separator := by simpa [sep] using hvS
    rcases (mem_compVerts C v).1 hvC with ⟨v', rfl, -⟩
    exact v'.2 hvS'
  have hcomp_disjoint (C D : K.ConnectedComponent) (hCD : C ≠ D) :
      Disjoint (compVerts C) (compVerts D) := by
    rw [Finset.disjoint_left]
    intro v hvC hvD
    rcases (mem_compVerts C v).1 hvC with ⟨vC, hvCv, hvCsupp⟩
    rcases (mem_compVerts D v).1 hvD with ⟨vD, hvDv, hvDsupp⟩
    apply hCD
    apply ConnectedComponent.eq_of_common_vertex (v := vC)
    · exact hvCsupp
    · have hsub : vC = vD := Subtype.ext (hvCv.trans hvDv.symm)
      rwa [hsub]
  have hrep_mem (C : K.ConnectedComponent) :
      (A.representative C).1.1 ∈ rep := by
    apply Finset.mem_image.mpr
    exact ⟨C, Finset.mem_univ _, rfl⟩
  have hrep_erase_one_subset (C : K.ConnectedComponent) :
      rep.erase (A.representative C).1.1 ⊆
        Finset.univ \ (sep ∪ compVerts C) := by
    intro v hv
    have hverase := Finset.mem_erase.mp hv
    rcases Finset.mem_image.mp hverase.2 with ⟨D, -, hDv⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hvunion
    rcases Finset.mem_union.mp hvunion with hvS | hvC
    · have hvS' : v ∈ Z.separator := by simpa [sep] using hvS
      have hDcompl : (A.representative D).1.1 ∈ Z.separatorᶜ :=
        (A.representative D).1.2
      exact hDcompl (hDv ▸ hvS')
    · rcases (mem_compVerts C v).1 hvC with ⟨vC, hvCv, hvCsupp⟩
      have hDC : D = C := by
        apply ConnectedComponent.eq_of_common_vertex (v := (A.representative D).1)
        · exact (A.representative D).2
        · have heq : (A.representative D).1 = vC :=
            Subtype.ext (hDv.trans hvCv.symm)
          rwa [heq]
      apply hverase.1
      rw [← hDC]
      exact hDv.symm
  have hrep_one_count (C : K.ConnectedComponent) :
      rep.card - 1 + sep.card + (compVerts C).card ≤ Fintype.card W := by
    have hle := Finset.card_le_card (hrep_erase_one_subset C)
    have herase : (rep.erase (A.representative C).1.1).card = rep.card - 1 :=
      Finset.card_erase_of_mem (hrep_mem C)
    have hunion : (sep ∪ compVerts C).card = sep.card + (compVerts C).card :=
      Finset.card_union_of_disjoint (hsep_disjoint_comp C)
    have hpartition := Finset.card_sdiff_add_card_eq_card
      (show sep ∪ compVerts C ⊆ (Finset.univ : Finset W) by simp)
    rw [herase] at hle
    rw [hunion, Finset.card_univ] at hpartition
    omega
  have hrep_erase_two_subset (C D : K.ConnectedComponent) (hCD : C ≠ D) :
      (rep.erase (A.representative C).1.1).erase (A.representative D).1.1 ⊆
        Finset.univ \ ((sep ∪ compVerts C) ∪ compVerts D) := by
    intro v hv
    have hvD := Finset.mem_erase.mp hv
    have hvC := Finset.mem_erase.mp hvD.2
    rcases Finset.mem_image.mp hvC.2 with ⟨E, -, hEv⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hvunion
    rcases Finset.mem_union.mp hvunion with hvSC | hvDin
    · rcases Finset.mem_union.mp hvSC with hvS | hvCin
      · have hvS' : v ∈ Z.separator := by simpa [sep] using hvS
        exact (A.representative E).1.2 (hEv ▸ hvS')
      · rcases (mem_compVerts C v).1 hvCin with ⟨vC, hvCv, hvCsupp⟩
        have hEC : E = C := by
          apply ConnectedComponent.eq_of_common_vertex (v := (A.representative E).1)
          · exact (A.representative E).2
          · have heq : (A.representative E).1 = vC :=
              Subtype.ext (hEv.trans hvCv.symm)
            rwa [heq]
        apply hvC.1
        rw [← hEC]
        exact hEv.symm
    · rcases (mem_compVerts D v).1 hvDin with ⟨vD, hvDv, hvDsupp⟩
      have hED : E = D := by
        apply ConnectedComponent.eq_of_common_vertex (v := (A.representative E).1)
        · exact (A.representative E).2
        · have heq : (A.representative E).1 = vD :=
            Subtype.ext (hEv.trans hvDv.symm)
          rwa [heq]
      apply hvD.1
      rw [← hED]
      exact hEv.symm
  have hrep_two_count (C D : K.ConnectedComponent) (hCD : C ≠ D) :
      rep.card - 2 + sep.card + (compVerts C).card + (compVerts D).card ≤
        Fintype.card W := by
    have hle := Finset.card_le_card (hrep_erase_two_subset C D hCD)
    have hrep_ne : (A.representative C).1.1 ≠ (A.representative D).1.1 :=
      fun h ↦ hCD (A.representative_injective h)
    have hDmem : (A.representative D).1.1 ∈
        rep.erase (A.representative C).1.1 :=
      Finset.mem_erase.mpr ⟨hrep_ne.symm, hrep_mem D⟩
    have heraseC := Finset.card_erase_of_mem (hrep_mem C)
    have heraseD := Finset.card_erase_of_mem hDmem
    have hsepC : (sep ∪ compVerts C).card =
        sep.card + (compVerts C).card :=
      Finset.card_union_of_disjoint (hsep_disjoint_comp C)
    have hSC_D : Disjoint (sep ∪ compVerts C) (compVerts D) :=
      Finset.disjoint_union_left.mpr
        ⟨hsep_disjoint_comp D, hcomp_disjoint C D hCD⟩
    have hunion : ((sep ∪ compVerts C) ∪ compVerts D).card =
        sep.card + (compVerts C).card + (compVerts D).card := by
      rw [Finset.card_union_of_disjoint hSC_D, hsepC]
    have hpartition := Finset.card_sdiff_add_card_eq_card
      (show (sep ∪ compVerts C) ∪ compVerts D ⊆
        (Finset.univ : Finset W) by simp)
    rw [heraseD, heraseC] at hle
    rw [hunion, Finset.card_univ] at hpartition
    omega
  have hrep_sep_count : rep.card + sep.card ≤ Fintype.card W := by
    have hsubset : rep ⊆ Finset.univ \ sep := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨C, -, hCv⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hvS
      have hvS' : v ∈ Z.separator := by simpa [sep] using hvS
      exact (A.representative C).1.2 (hCv ▸ hvS')
    have hle := Finset.card_le_card hsubset
    have hpartition := Finset.card_sdiff_add_card_eq_card
      (show sep ⊆ (Finset.univ : Finset W) by simp)
    rw [Finset.card_univ] at hpartition
    omega
  have hlargeEdge : ∃ a ∈ L, ∃ b ∈ L, R.Adj a b := by
    by_contra h
    apply hL_nonindependent
    intro a ha b hb hab
    intro hadj
    apply h
    exact ⟨a, ha, b, hb, hadj⟩
  by_cases hlocal : ∃ C : K.ConnectedComponent,
      ∃ a ∈ L ∩ compVerts C, ∃ b ∈ L ∩ compVerts C, R.Adj a b
  · obtain ⟨C, a, ha, b, hb, hab⟩ := hlocal
    have local_missed (u : W) (hu : u ∈ compVerts C) :
        (R.neighborFinset u \ matchingSupport A.M).card ≤ 2 * c + 1 := by
      have hsubset : R.neighborFinset u \ matchingSupport A.M ⊆
          {(A.representative C).1.1} := by
        intro v hv
        have hv' := Finset.mem_sdiff.mp hv
        have hvuncovered : v ∈ uncovered := by
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv'.2⟩
        rw [huncovered_eq] at hvuncovered
        rcases Finset.mem_image.mp (Finset.mem_sdiff.mp hvuncovered).1 with
          ⟨D, -, hDv⟩
        rcases (mem_compVerts C u).1 hu with ⟨u', hu'u, huC⟩
        let v' : ↑(Z.separatorᶜ : Set W) := (A.representative D).1
        have huv' : K.Adj u' v' := by
          change R.Adj u'.1 v'.1
          simpa [v', hu'u, hDv] using (R.mem_neighborFinset u v).1 hv'.1
        have hvC : v' ∈ C.supp := (C.mem_supp_congr_adj huv').1 huC
        have hCD : C = D :=
          ConnectedComponent.eq_of_common_vertex hvC (A.representative D).2
        simp only [Finset.mem_singleton]
        rw [← hCD] at hDv
        exact hDv.symm
      have hcardone := Finset.card_le_card hsubset
      simp only [Finset.card_singleton] at hcardone
      omega
    refine ⟨{
      O := compVerts C
      M := A.M
      isMatching := A.isMatching
      adjacentLarge := ⟨a, ha, b, hb, hab⟩
      neighbors_missed := local_missed
      doubleNeighbor_outside := ?_ }⟩
    intro u hu
    rw [Set.ncard_le_one_iff_subsingleton]
    intro v hv w hw
    have outside_bridge {x : W}
        (hx : x ∈ matchingDoubleNeighborSet R A.M u \ (compVerts C : Set W)) :
        ∃ s : Z.separator, x = s.1 ∧ Z.targetComponent s = C := by
      rcases hx with ⟨hxdouble, hxout⟩
      rcases hxdouble.2 with ⟨y, hxy, hux, huy⟩
      rcases A.edge_location hxy with hbridge | hinternal
      · rcases hbridge with ⟨s, hs | hs⟩
        · rcases hs with ⟨rfl, rfl⟩
          refine ⟨s, rfl, ?_⟩
          rcases (mem_compVerts C u).1 hu with ⟨u', hu'u, huC⟩
          have hadj' : K.Adj u' (Z.bridgeVertex s).1 := by
            change R.Adj u'.1 (Z.bridgeVertex s).1.1
            rwa [hu'u]
          have hbC : (Z.bridgeVertex s).1 ∈ C.supp :=
            (C.mem_supp_congr_adj hadj').1 huC
          exact (ConnectedComponent.eq_of_common_vertex
            (Z.bridgeVertex s).2 hbC)
        · rcases hs with ⟨rfl, rfl⟩
          exfalso
          apply hxout
          rcases (mem_compVerts C u).1 hu with ⟨u', hu'u, huC⟩
          apply (mem_compVerts C (Z.bridgeVertex s).1.1).2
          refine ⟨(Z.bridgeVertex s).1, rfl, ?_⟩
          have hadj' : K.Adj u' (Z.bridgeVertex s).1 := by
            change R.Adj u'.1 (Z.bridgeVertex s).1.1
            rwa [hu'u]
          exact (C.mem_supp_congr_adj hadj').1 huC
      · rcases hinternal with ⟨D, x', y', hx'x, hy'y, hx'D, hy'D⟩
        exfalso
        apply hxout
        rcases (mem_compVerts C u).1 hu with ⟨u', hu'u, huC⟩
        apply (mem_compVerts C x).2
        refine ⟨x', hx'x, ?_⟩
        have hadj' : K.Adj u' x' := by
          change R.Adj u'.1 x'.1
          rw [hu'u, hx'x]
          exact hux
        exact (C.mem_supp_congr_adj hadj').1 huC
    obtain ⟨s, hvs, hsC⟩ := outside_bridge hv
    obtain ⟨t, hwt, htC⟩ := outside_bridge hw
    have hst : s = t := Z.targetComponent_injective (hsC.trans htC.symm)
    rw [hvs, hwt, hst]
  · have hglobal : uncovered.card ≤ 2 * c + 1 := by
      by_cases hallS : ∀ v ∈ L, v ∈ Z.separator
      · have hLsep : L ⊆ sep := by
          intro v hv
          simpa [sep] using hallS v hv
        have hLsep_card := Finset.card_le_card hLsep
        omega
      · push Not at hallS
        obtain ⟨a, haL, haS⟩ := hallS
        let a' : ↑(Z.separatorᶜ : Set W) := ⟨a, haS⟩
        let C : K.ConnectedComponent := K.connectedComponentMk a'
        have haC : a' ∈ C.supp := by rfl
        by_cases htwo : ∃ b : W, b ∈ L ∧
            ∃ hbS : b ∉ Z.separator,
              K.connectedComponentMk (⟨b, hbS⟩ :
                ↑(Z.separatorᶜ : Set W)) ≠ C
        · obtain ⟨b, hbL, hbS, hbCne⟩ := htwo
          let b' : ↑(Z.separatorᶜ : Set W) := ⟨b, hbS⟩
          let D : K.ConnectedComponent := K.connectedComponentMk b'
          have hbD : b' ∈ D.supp := by rfl
          have hCD : C ≠ D := hbCne.symm
          have hdegA := component_degree_upper C a' haC
          have hdegB := component_degree_upper D b' hbD
          change R.degree a ≤ sep.card + (compVerts C).card - 1 at hdegA
          change R.degree b ≤ sep.card + (compVerts D).card - 1 at hdegB
          have hlowA := hL_degree a haL
          have hlowB := hL_degree b hbL
          have hcount := hrep_two_count C D hCD
          have hrep2 : 2 ≤ rep.card := by
            have hne : (A.representative C).1.1 ≠
                (A.representative D).1.1 :=
              fun h ↦ hCD (A.representative_injective h)
            have : 1 < rep.card := Finset.one_lt_card_iff.mpr
              ⟨(A.representative C).1.1, (A.representative D).1.1,
                hrep_mem C, hrep_mem D, hne⟩
            omega
          rw [hcard] at hcount
          have hCpos : 0 < (compVerts C).card := Finset.card_pos.mpr
            ⟨a, (mem_compVerts C a).2 ⟨a', rfl, haC⟩⟩
          have hDpos : 0 < (compVerts D).card := Finset.card_pos.mpr
            ⟨b, (mem_compVerts D b).2 ⟨b', rfl, hbD⟩⟩
          have hAC : k - c + 1 ≤ sep.card + (compVerts C).card := by omega
          have hBD : k - c + 1 ≤ sep.card + (compVerts D).card := by omega
          have hcount' : rep.card + sep.card + (compVerts C).card +
              (compVerts D).card ≤ 2 * k + 2 := by omega
          omega
        · have hallOutsideC : ∀ v ∈ L, ∀ hvS : v ∉ Z.separator,
              K.connectedComponentMk
                (⟨v, hvS⟩ : ↑(Z.separatorᶜ : Set W)) = C := by
            intro v hvL hvS
            by_contra hne
            apply htwo
            exact ⟨v, hvL, hvS, hne⟩
          let LC : Finset W := L ∩ compVerts C
          let nonL : Finset W := compVerts C \ L
          have hLsubset : L ⊆ sep ∪ LC := by
            intro v hvL
            by_cases hvS : v ∈ Z.separator
            · apply Finset.mem_union_left
              simpa [sep] using hvS
            · apply Finset.mem_union_right
              apply Finset.mem_inter.mpr
              refine ⟨hvL, ?_⟩
              apply (mem_compVerts C v).2
              let v' : ↑(Z.separatorᶜ : Set W) := ⟨v, hvS⟩
              refine ⟨v', rfl, ?_⟩
              exact (C.mem_supp_iff v').2 (hallOutsideC v hvL hvS)
          have hLcount0 := Finset.card_le_card hLsubset
          have hLcount : L.card ≤ sep.card + LC.card := by
            exact hLcount0.trans (Finset.card_union_le _ _)
          have hneigh : R.neighborFinset a ⊆ sep ∪ nonL := by
            intro v hv
            have hav : R.Adj a v := (R.mem_neighborFinset a v).1 hv
            by_cases hvS : v ∈ Z.separator
            · apply Finset.mem_union_left
              simpa [sep] using hvS
            · apply Finset.mem_union_right
              apply Finset.mem_sdiff.mpr
              refine ⟨?_, ?_⟩
              · apply (mem_compVerts C v).2
                let v' : ↑(Z.separatorᶜ : Set W) := ⟨v, hvS⟩
                refine ⟨v', rfl, ?_⟩
                have hadj' : K.Adj a' v' := by
                  exact hav
                exact (C.mem_supp_congr_adj hadj').1 haC
              · intro hvL
                apply hlocal
                refine ⟨C, a, ?_, v, ?_, hav⟩
                · exact Finset.mem_inter.mpr
                    ⟨haL, (mem_compVerts C a).2 ⟨a', rfl, haC⟩⟩
                · exact Finset.mem_inter.mpr
                    ⟨hvL, (mem_compVerts C v).2
                      ⟨⟨v, hvS⟩, rfl,
                        (C.mem_supp_congr_adj
                          (show K.Adj a' ⟨v, hvS⟩ from hav)).1 haC⟩⟩
          have hdegA : R.degree a ≤ sep.card + nonL.card := by
            calc
              R.degree a = (R.neighborFinset a).card := by
                rw [R.card_neighborFinset_eq_degree]
              _ ≤ (sep ∪ nonL).card := Finset.card_le_card hneigh
              _ ≤ sep.card + nonL.card := Finset.card_union_le _ _
          have hpartition := Finset.card_sdiff_add_card_inter (compVerts C) L
          have hparts : nonL.card + LC.card = (compVerts C).card := by
            simpa [nonL, LC, Finset.inter_comm] using hpartition
          have hlowA := hL_degree a haL
          have hcount := hrep_one_count C
          have hrep1 : 1 ≤ rep.card := Finset.one_le_card.mpr ⟨_, hrep_mem C⟩
          omega
    exact ⟨claim67Certificate_of_nearPerfectMatching
      R L (2 * c + 1) A.M A.isMatching hglobal hlargeEdge⟩

end Erdos547b.ZhaoStability

#print axioms GallaiEdmonds547Port.ZhaoGallaiEdmondsWitness.exists_assembledMatching
#print axioms Erdos547b.ZhaoStability.exists_claim67Certificate_of_reducedGraph
