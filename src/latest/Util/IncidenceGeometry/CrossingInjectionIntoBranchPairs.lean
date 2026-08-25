import Util.IncidenceGeometry.GeometricArcDrawing

open Classical
noncomputable section

lemma CrossingInjectionIntoBranchPairs {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (x : {p // p ∈ D.intersectionPoints})
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (branchPair :
      EuclideanSpace ℝ (Fin 2) →
        (⊤ : SimpleGraph {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}).edgeFinset)
    (hinj : Set.InjOn branchPair (↑S : Set (EuclideanSpace ℝ (Fin 2)))) :
    S.card ≤
      Nat.choose (((Finset.univ : Finset G.edgeFinset).filter
        (fun e => x.1 ∈ D.edgeRelativeInterior e)).card) 2 := by
  classical
  calc
    S.card ≤
        (Finset.univ :
          Finset ((⊤ : SimpleGraph
            {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}).edgeFinset)).card := by
      refine Finset.card_le_card_of_injOn branchPair ?_ ?_
      · intro p hp
        simp
      · intro p hp q hq hpq
        exact hinj hp hq hpq
    _ = Nat.choose
          (Fintype.card {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}) 2 := by
      simpa using
        (SimpleGraph.card_edgeFinset_top_eq_card_choose_two
          (V := {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}))
    _ = Nat.choose (((Finset.univ : Finset G.edgeFinset).filter
          (fun e => x.1 ∈ D.edgeRelativeInterior e)).card) 2 := by
      have hcard :
          Fintype.card {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} =
            ((Finset.univ : Finset G.edgeFinset).filter
              (fun e => x.1 ∈ D.edgeRelativeInterior e)).card := by
        simpa using
          (Fintype.card_subtype
            (fun e : G.edgeFinset => x.1 ∈ D.edgeRelativeInterior e))
      rw [hcard]
