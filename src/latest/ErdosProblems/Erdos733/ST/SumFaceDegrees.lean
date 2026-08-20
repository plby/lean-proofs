import ErdosProblems.Erdos733.ST.PlaneFaceData

open Classical
noncomputable section

-- [TABLET NODE: SumFaceDegrees]
lemma SumFaceDegrees {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    ((@Finset.univ A.Face A.faceFintype).sum A.faceDegree) =
      2 * G.edgeFinset.card := by
-- BODY
  classical
  letI := A.faceFintype
  have _ : D.crossingSet.card = 0 := hD
  have hfaces :
      ((@Finset.univ A.Face A.faceFintype).sum
          (fun F => Fintype.card {d : G.Dart // A.leftFace d = F})) =
        Fintype.card G.Dart := by
    symm
    simpa [Fintype.card_subtype] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset G.Dart))
        (t := (@Finset.univ A.Face A.faceFintype))
        (f := A.leftFace)
        (fun d _hd => Finset.mem_univ (A.leftFace d)))
  have hdarts : Fintype.card G.Dart = 2 * G.edgeFinset.card := by
    refine G.dart_card_eq_twice_card_edges.trans ?_
    congr 1
    apply congrArg Finset.card
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  calc
    ((@Finset.univ A.Face A.faceFintype).sum A.faceDegree)
        = ((@Finset.univ A.Face A.faceFintype).sum
            (fun F => Fintype.card {d : G.Dart // A.leftFace d = F})) := by
          refine Finset.sum_congr rfl ?_
          intro F _hF
          exact A.faceDegree_eq F
    _ = Fintype.card G.Dart := hfaces
    _ = 2 * G.edgeFinset.card := hdarts
