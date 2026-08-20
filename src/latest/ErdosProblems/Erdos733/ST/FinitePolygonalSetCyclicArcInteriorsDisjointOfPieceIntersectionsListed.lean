import ErdosProblems.Erdos733.ST.FinitePolygonalSet

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicArcInteriorsDisjointOfPieceIntersectionsListed]
lemma FinitePolygonalSetCyclicArcInteriorsDisjointOfPieceIntersectionsListed
    (K : FinitePolygonalSet)
    {PieceIndex : Type}
    (successor : Equiv.Perm {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
    (pieceCarrier : PieceIndex → Set (EuclideanSpace ℝ (Fin 2)))
    (arcPieceOrder :
      {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} → List PieceIndex)
    (arcCarrier arcInterior :
      {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points} →
        Set (EuclideanSpace ℝ (Fin 2)))
    (arcCarrier_eq_pieceOrder :
      ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        arcCarrier p =
          ⋃ i : {i : PieceIndex // i ∈ arcPieceOrder p}, pieceCarrier i.1)
    (arcInterior_eq :
      ∀ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        arcInterior p =
          arcCarrier p \ ({p.1, (successor p).1} :
            Set (EuclideanSpace ℝ (Fin 2))))
    (no_listed_point_in_arcInterior :
      ∀ (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points})
        (v : EuclideanSpace ℝ (Fin 2)),
          v ∈ K.points → v ∉ arcInterior p)
    (piece_intersections_listed :
      ∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
        p ≠ q →
          ∀ i j : PieceIndex, i ∈ arcPieceOrder p → j ∈ arcPieceOrder q →
            ∀ x : EuclideanSpace ℝ (Fin 2),
              x ∈ pieceCarrier i → x ∈ pieceCarrier j → x ∈ K.points) :
    ∀ p q : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points},
      p ≠ q → Disjoint (arcInterior p) (arcInterior q) := by
-- BODY
  intro p q hpq
  rw [Set.disjoint_left]
  intro x hxP hxQ
  have hxP_carrier : x ∈ arcCarrier p := by
    have hxP' := hxP
    rw [arcInterior_eq p] at hxP'
    exact hxP'.1
  have hxQ_carrier : x ∈ arcCarrier q := by
    have hxQ' := hxQ
    rw [arcInterior_eq q] at hxQ'
    exact hxQ'.1
  rw [arcCarrier_eq_pieceOrder p] at hxP_carrier
  rw [arcCarrier_eq_pieceOrder q] at hxQ_carrier
  rcases Set.mem_iUnion.mp hxP_carrier with ⟨i, hxi⟩
  rcases Set.mem_iUnion.mp hxQ_carrier with ⟨j, hxj⟩
  have hxK : x ∈ K.points :=
    piece_intersections_listed p q hpq i.1 j.1 i.2 j.2 x hxi hxj
  exact no_listed_point_in_arcInterior p x hxK hxP
