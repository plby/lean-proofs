import Util.IncidenceGeometry.GeometricArcDrawing
import Util.IncidenceGeometry.PolygonalReplacementControlDisks
import Util.IncidenceGeometry.PolygonalReplacementTubeChains
import Util.IncidenceGeometry.EndpointFixedPolygonalDiskFillingClean
import Util.IncidenceGeometry.PolygonalReplacementLocalDiskFillings
import Util.IncidenceGeometry.PolygonalReplacementEdgeAssemblies
import Util.IncidenceGeometry.PolygonalReplacementOrdinaryDrawingFromAssemblies
import Util.IncidenceGeometry.CrossingInjectionIntoBranchPairs
import Util.IncidenceGeometry.PolygonalReplacementCrossingNumberFromLocalSum

open Classical
noncomputable section


lemma PolygonalReplacementForGeometricArcs {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G) :
    ∃ D' : OrdinaryPolygonalDrawing G,
      D'.crossingSet.card ≤ D.localPairCount ∧
        CrossingNumber G ≤ D.localPairCount := by
  obtain ⟨D', hsum⟩ :
      ∃ D' : OrdinaryPolygonalDrawing G,
        D'.crossingSet.card ≤
          D.intersectionPoints.sum (fun p =>
            Nat.choose (((Finset.univ : Finset G.edgeFinset).filter
              (fun e => p ∈ D.edgeRelativeInterior e)).card) 2) := by
    obtain ⟨controlDisks⟩ := PolygonalReplacementControlDisks G D
    have hVertexRadii : ∀ v, 0 < controlDisks.vertexRadius v :=
      controlDisks.vertexRadius_pos
    have hIntersectionRadii :
        ∀ x, 0 < controlDisks.intersectionRadius x :=
      controlDisks.intersectionRadius_pos
    obtain ⟨tubeChains⟩ :=
      PolygonalReplacementTubeChains G D controlDisks
    have hTubeNoCrossings :
        ∀ ⦃i j : tubeChains.pieceIndex⦄, i ≠ j →
          Disjoint (tubeChains.chain i).carrier (tubeChains.chain j).carrier :=
      tubeChains.chain_carriers_pairwise_disjoint
    obtain ⟨localDiskFillings⟩ :=
      PolygonalReplacementLocalDiskFillings G D controlDisks tubeChains
    obtain ⟨edgeAssemblies⟩ :=
      PolygonalReplacementEdgeAssemblies G D controlDisks tubeChains
        localDiskFillings
    have hAssembledEdgeSource :
        ∀ e, (edgeAssemblies.edgeArc e).source = D.edgeSource e :=
      edgeAssemblies.edgeArc_source
    have hAssembledEdgeTarget :
        ∀ e, (edgeAssemblies.edgeArc e).target = D.edgeTarget e :=
      edgeAssemblies.edgeArc_target
    have hAssembledEdgeLocalization :
        ∀ ⦃e : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
          p ∈ (edgeAssemblies.edgeArc e).relativeInterior →
            (∃ (v : V) (hve : v ∈ e.1),
              p ∈
                (localDiskFillings.vertex_spoke v ⟨e, hve⟩).carrier) ∨
            (∃ i : tubeChains.pieceIndex,
              tubeChains.owner i = e ∧ p ∈ (tubeChains.chain i).carrier) ∨
            (∃ (x : {q // q ∈ D.intersectionPoints})
                (hxe : x.1 ∈ D.edgeRelativeInterior e),
              p ∈
                (localDiskFillings.intersection_chain x ⟨e, hxe⟩).carrier) :=
      edgeAssemblies.edgeArc_relativeInterior_localized
    have hVertexSpokeNoCrossings :=
      localDiskFillings.vertex_spokes_same_vertex_disjoint
    have hIntersectionDiskPairBound :=
      localDiskFillings.intersection_chains_pairwise_at_most_one
    have hLocalBranchPairCounting :
        ∀ (x : {p // p ∈ D.intersectionPoints})
          (S : Finset (EuclideanSpace ℝ (Fin 2)))
          (branchPair :
            EuclideanSpace ℝ (Fin 2) →
              (⊤ : SimpleGraph
                {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}).edgeFinset),
          Set.InjOn branchPair (↑S : Set (EuclideanSpace ℝ (Fin 2))) →
            S.card ≤
              Nat.choose (((Finset.univ : Finset G.edgeFinset).filter
                (fun e => x.1 ∈ D.edgeRelativeInterior e)).card) 2 := by
      intro x S branchPair hinj
      exact CrossingInjectionIntoBranchPairs G D x S branchPair hinj
    obtain ⟨Dpoly, hDpoly_vertexPlacement, hDpoly_edgeArc,
        hDpoly_crossings_localized⟩ :=
      PolygonalReplacementOrdinaryDrawingFromAssemblies G D controlDisks
        tubeChains localDiskFillings edgeAssemblies
    refine ⟨Dpoly, ?_⟩
    let P (x : {q // q ∈ D.intersectionPoints})
        (p : EuclideanSpace ℝ (Fin 2)) : Prop :=
      ∃ (e f : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        e ≠ f ∧
          p ∈ (localDiskFillings.intersection_chain x e).relativeInterior ∧
            p ∈ (localDiskFillings.intersection_chain x f).relativeInterior
    let S (x : {q // q ∈ D.intersectionPoints}) :
        Finset (EuclideanSpace ℝ (Fin 2)) :=
      Dpoly.crossingSet.filter (fun p => P x p)
    have hS_bound :
        ∀ x : {q // q ∈ D.intersectionPoints},
          (S x).card ≤
            Nat.choose (((Finset.univ : Finset G.edgeFinset).filter
              (fun e => x.1 ∈ D.edgeRelativeInterior e)).card) 2 := by
      intro x
      rcases (D.intersectionPoints_spec x.1).mp x.2 with
        ⟨e₀, f₀, hef₀, he₀, hf₀⟩
      let b₀ : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} :=
        ⟨e₀, he₀⟩
      let b₁ : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} :=
        ⟨f₀, hf₀⟩
      have hb₀₁ : b₀ ≠ b₁ := by
        intro h
        exact hef₀ (congrArg Subtype.val h)
      let defaultPair :
          (⊤ : SimpleGraph
            {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}).edgeFinset :=
        ⟨Sym2.mk b₀ b₁, by simp [hb₀₁]⟩
      let chosenLeft :
          EuclideanSpace ℝ (Fin 2) →
            {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} :=
        fun p => if hp : P x p then Classical.choose hp else b₀
      let chosenRight :
          EuclideanSpace ℝ (Fin 2) →
            {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} :=
        fun p =>
          if hp : P x p then
            Classical.choose (Classical.choose_spec hp)
          else b₁
      have hchosen :
          ∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            P x p →
              chosenLeft p ≠ chosenRight p ∧
                p ∈
                  (localDiskFillings.intersection_chain x
                    (chosenLeft p)).relativeInterior ∧
                  p ∈
                    (localDiskFillings.intersection_chain x
                      (chosenRight p)).relativeInterior := by
        intro p hp
        simpa [chosenLeft, chosenRight, hp] using
          (Classical.choose_spec
            (Classical.choose_spec hp))
      let branchPair :
          EuclideanSpace ℝ (Fin 2) →
            (⊤ : SimpleGraph
              {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}).edgeFinset :=
        fun p =>
          if hp : P x p then
            ⟨Sym2.mk (chosenLeft p) (chosenRight p), by
              exact by
                simp [(hchosen hp).1]⟩
          else defaultPair
      have hinj :
          Set.InjOn branchPair
            (↑(S x) : Set (EuclideanSpace ℝ (Fin 2))) := by
        intro p hpS q hqS hpq
        have hpP : P x p := (Finset.mem_filter.mp hpS).2
        have hqP : P x q := (Finset.mem_filter.mp hqS).2
        have hpChosen := hchosen hpP
        have hqChosen := hchosen hqP
        have hsym :
            Sym2.mk (chosenLeft p) (chosenRight p) =
              Sym2.mk (chosenLeft q) (chosenRight q) := by
          have hpq' := congrArg Subtype.val hpq
          simpa [branchPair, hpP, hqP] using hpq'
        have hcases :
            (chosenLeft p, chosenRight p) =
                (chosenLeft q, chosenRight q) ∨
              (chosenLeft p, chosenRight p) =
                (chosenLeft q, chosenRight q).swap :=
          (Sym2.mk_eq_mk_iff
            (α := {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e})
            (p := (chosenLeft p, chosenRight p))
            (q := (chosenLeft q, chosenRight q))).mp hsym
        rcases hcases with hdir | hswap
        · have hleft : chosenLeft p = chosenLeft q := congrArg Prod.fst hdir
          have hright : chosenRight p = chosenRight q := congrArg Prod.snd hdir
          exact
            localDiskFillings.intersection_chains_pairwise_at_most_one x
              hpChosen.1 hpChosen.2.1 hpChosen.2.2
              (by simpa [hleft] using hqChosen.2.1)
              (by simpa [hright] using hqChosen.2.2)
        · have hleft : chosenLeft p = chosenRight q := congrArg Prod.fst hswap
          have hright : chosenRight p = chosenLeft q := congrArg Prod.snd hswap
          exact
            localDiskFillings.intersection_chains_pairwise_at_most_one x
              hpChosen.1 hpChosen.2.1 hpChosen.2.2
              (by simpa [hleft] using hqChosen.2.2)
              (by simpa [hright] using hqChosen.2.1)
      exact hLocalBranchPairCounting x (S x) branchPair hinj
    have hcover :
        Dpoly.crossingSet ⊆
          D.intersectionPoints.attach.biUnion S := by
      intro p hp
      rcases hDpoly_crossings_localized hp with
        ⟨x, e, f, hef, hpe, hpf⟩
      rw [Finset.mem_biUnion]
      refine ⟨x, by simp, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨hp, ⟨e, f, hef, hpe, hpf⟩⟩
    calc
      Dpoly.crossingSet.card ≤
          (D.intersectionPoints.attach.biUnion S).card :=
        Finset.card_le_card hcover
      _ ≤ D.intersectionPoints.attach.sum (fun x => (S x).card) :=
        Finset.card_biUnion_le
      _ ≤ D.intersectionPoints.attach.sum (fun x =>
          Nat.choose (((Finset.univ : Finset G.edgeFinset).filter
            (fun e => x.1 ∈ D.edgeRelativeInterior e)).card) 2) := by
        exact Finset.sum_le_sum (by
          intro x hx
          exact hS_bound x)
      _ = D.intersectionPoints.sum (fun p =>
            Nat.choose (((Finset.univ : Finset G.edgeFinset).filter
              (fun e => p ∈ D.edgeRelativeInterior e)).card) 2) := by
        simpa using
          (Finset.sum_attach D.intersectionPoints
            (fun p =>
              Nat.choose (((Finset.univ : Finset G.edgeFinset).filter
                (fun e => p ∈ D.edgeRelativeInterior e)).card) 2))
  exact ⟨D', PolygonalReplacementCrossingNumberFromLocalSum G D D' hsum⟩
