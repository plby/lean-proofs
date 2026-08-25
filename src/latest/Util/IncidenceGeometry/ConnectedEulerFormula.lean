import Util.IncidenceGeometry.PlaneTreeOneFace
import Util.IncidenceGeometry.DeleteNonbridgeMergesFaces
import Util.IncidenceGeometry.PlaneFaceData

open Classical
noncomputable section

lemma ConnectedEulerFormula {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    G.Connected →
      (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) +
        (@Fintype.card A.Face A.faceFintype : ℤ) = 2 := by
  intro hconn
  classical
  have delete_card :
      ∀ (G' : SimpleGraph V), [Fintype G'.edgeSet] → [DecidableRel G'.Adj] →
        ∀ e : G'.edgeFinset,
          ((G'.deleteEdges ({e.1} : Set (Sym2 V))).edgeFinset.card + 1 =
            G'.edgeFinset.card) := by
    intro G' _ _ e
    have hmem : e.1 ∈ G'.edgeFinset := e.2
    have hto :
        Set.toFinset (G'.edgeSet \ ({e.1} : Set (Sym2 V))) =
          G'.edgeFinset.erase e.1 := by
      ext z
      simp [SimpleGraph.edgeFinset, and_comm]
    have hdel_to :
        Set.toFinset ((G'.deleteEdges ({e.1} : Set (Sym2 V))).edgeSet) =
          Set.toFinset (G'.edgeSet \ ({e.1} : Set (Sym2 V))) := by
      ext z
      simp [SimpleGraph.edgeSet_deleteEdges]
    change
      (Set.toFinset ((G'.deleteEdges ({e.1} : Set (Sym2 V))).edgeSet)).card + 1 =
        G'.edgeFinset.card
    rw [hdel_to, hto]
    exact Finset.card_erase_add_one hmem
  have connected_delete :
      ∀ (G' : SimpleGraph V), [Fintype G'.edgeSet] → [DecidableRel G'.Adj] →
        G'.Connected → ∀ e : G'.edgeFinset,
          ¬ G'.IsBridge e.1 →
            (G'.deleteEdges ({e.1} : Set (Sym2 V))).Connected := by
    intro G' _ _ hconn' e he
    revert he
    induction e.1 using Sym2.ind with
    | h x y =>
        intro he
        exact hconn'.connected_delete_edge_of_not_isBridge he
  have hmain :
      ∀ m : ℕ,
        ∀ (G' : SimpleGraph V), [Fintype G'.edgeSet] → [DecidableRel G'.Adj] →
          ∀ (D' : OrdinaryPolygonalDrawing G') (hD' : D'.crossingSet.card = 0)
            (A' : PlaneFaceData G' D'),
            G'.edgeFinset.card = m →
              G'.Connected →
                (Fintype.card V : ℤ) - (G'.edgeFinset.card : ℤ) +
                  (@Fintype.card A'.Face A'.faceFintype : ℤ) = 2 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro G' _ _ D' hD' A' hm hconn'
        by_cases htree : G'.IsTree
        · have hfacesNat :
              @Fintype.card A'.Face A'.faceFintype = 1 :=
            PlaneTreeOneFace G' D' hD' A' htree
          have hedgeNat : G'.edgeFinset.card + 1 = Fintype.card V :=
            SimpleGraph.IsTree.card_edgeFinset htree
          omega
        · have hnacyc : ¬ G'.IsAcyclic := by
            intro hacyc
            exact htree ⟨hconn', hacyc⟩
          rw [SimpleGraph.isAcyclic_iff_forall_edge_isBridge] at hnacyc
          push Not at hnacyc
          rcases hnacyc with ⟨eSym, he_mem, he_nonbridge⟩
          let eFin : G'.edgeFinset :=
            ⟨eSym, by simpa [SimpleGraph.mem_edgeFinset] using he_mem⟩
          let Gdel : SimpleGraph V := G'.deleteEdges ({eFin.1} : Set (Sym2 V))
          have hconn_del : Gdel.Connected :=
            connected_delete G' hconn' eFin he_nonbridge
          have hcard_del_succ : Gdel.edgeFinset.card + 1 = G'.edgeFinset.card :=
            delete_card G' eFin
          have hlt : Gdel.edgeFinset.card < m := by
            omega
          rcases DeleteNonbridgeMergesFaces G' D' hD' A' eFin hconn' he_nonbridge with
            ⟨Ddel, hDdel, _, _, Adel, _, _, _, _, _, _, _, _, _, _, hfaceCount⟩
          have hEulerDel :
              (Fintype.card V : ℤ) - (Gdel.edgeFinset.card : ℤ) +
                (@Fintype.card Adel.Face Adel.faceFintype : ℤ) = 2 := by
            exact ih Gdel.edgeFinset.card hlt Gdel Ddel hDdel Adel rfl hconn_del
          omega
  exact hmain G.edgeFinset.card G D hD A rfl hconn
