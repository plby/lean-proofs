import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: EndpointSidePrefixAttachment]
structure EndpointSidePrefixAttachment
    (Aarc Barc BplusArc : PolygonalArc)
    (Rbeta H Bad DeltaX Qx : Set (EuclideanSpace ℝ (Fin 2)))
    (K : FinitePolygonalSet)
    (XA : Finset (EuclideanSpace ℝ (Fin 2))) where
-- BODY
  r : ℕ
  prefixPiece : ℕ → PolygonalArc
  xPrefix : Finset (EuclideanSpace ℝ (Fin 2))
  chargePrefix :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)
  omega : EuclideanSpace ℝ (Fin 2)
  terminalSide : PolygonalArc
  terminalConnector : PolygonalArc
  presentation_carrier : K.carrier = H
  copied_prefix_disjoint_tail : Disjoint Aarc.carrier Rbeta
  prefix_source : (prefixPiece 0).source = Aarc.source
  prefix_target : (prefixPiece r).target = terminalSide.source
  prefix_consecutive_sources :
    ∀ i : ℕ, i < r →
      (prefixPiece i).target = (prefixPiece (i + 1)).source
  prefix_consecutive_meets :
    ∀ i : ℕ, i < r →
      (prefixPiece i).carrier ∩ (prefixPiece (i + 1)).carrier =
        ({(prefixPiece i).target} : Set (EuclideanSpace ℝ (Fin 2)))
  prefix_nonconsecutive_disjoint :
    ∀ i j : ℕ, i ≤ r → j ≤ r → i + 1 < j →
      Disjoint (prefixPiece i).carrier (prefixPiece j).carrier
  prefix_internal_gates_avoid :
    ∀ i : ℕ, i < r →
      (prefixPiece i).target ∉
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad)
  prefix_relative_interiors_avoid :
    ∀ i : ℕ, i ≤ r →
      (prefixPiece i).relativeInterior ∩
          (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
            Rbeta ∪ Bad) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2)))
  xPrefix_spec :
    ∀ z : EuclideanSpace ℝ (Fin 2),
      z ∈ xPrefix ↔
        (∃ i : ℕ, i ≤ r ∧ z ∈ (prefixPiece i).relativeInterior) ∧
          z ∈ H
  chargePrefix_mem :
    ∀ z : EuclideanSpace ℝ (Fin 2),
      z ∈ xPrefix → chargePrefix z ∈ XA
  chargePrefix_injective :
    ∀ z w : EuclideanSpace ℝ (Fin 2),
      z ∈ xPrefix → w ∈ xPrefix →
        chargePrefix z = chargePrefix w → z = w
  xPrefix_clean :
    ∀ z : EuclideanSpace ℝ (Fin 2),
      z ∈ xPrefix →
        z ∉ Bad ∧
          z ∉ (K.points : Set (EuclideanSpace ℝ (Fin 2))) ∧
            ∃ i : ℕ,
              i ≤ r ∧
                ∃ j : ℕ,
                  ∃ hj : j + 1 < (prefixPiece i).vertices.length,
                    z ∈
                        openSegment ℝ
                          (prefixPiece i).vertices[j]
                          (prefixPiece i).vertices[j + 1] ∧
                      ∃! s :
                        EuclideanSpace ℝ (Fin 2) ×
                          EuclideanSpace ℝ (Fin 2),
                        s ∈ K.segments ∧
                          z ∈ openSegment ℝ s.1 s.2 ∧
                            ¬ ∃ c : ℝ,
                              s.2 - s.1 =
                                c •
                                  ((prefixPiece i).vertices[j + 1] -
                                    (prefixPiece i).vertices[j])
  terminal_source_mem_delta : terminalSide.source ∈ DeltaX
  terminal_source_not_mem_Q : terminalSide.source ∉ Qx
  terminal_source_avoid :
    terminalSide.source ∉
      (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
        Rbeta ∪ H ∪ Bad)
  terminal_side_target : terminalSide.target = omega
  terminal_connector_source : terminalConnector.source = omega
  terminal_connector_target : terminalConnector.target = BplusArc.target
  omega_mem_Q : omega ∈ Qx
  omega_ne_target : omega ≠ BplusArc.target
  omega_avoid :
    omega ∉
      (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
        Rbeta ∪ H ∪ Bad)
  terminal_side_subset_delta : terminalSide.carrier ⊆ DeltaX
  terminal_side_meets_Q :
    terminalSide.carrier ∩ Qx =
      ({omega} : Set (EuclideanSpace ℝ (Fin 2)))
  terminal_side_relativeInterior_avoid :
    terminalSide.relativeInterior ∩
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) =
      (∅ : Set (EuclideanSpace ℝ (Fin 2)))
  terminal_connector_subset_Q : terminalConnector.carrier ⊆ Qx
  terminal_connector_relativeInterior_avoid :
    terminalConnector.relativeInterior ∩
        (Aarc.carrier ∪ Barc.carrier ∪ BplusArc.carrier ∪
          Rbeta ∪ H ∪ Bad) =
      (∅ : Set (EuclideanSpace ℝ (Fin 2)))
  predecessor_meets_terminal :
    (prefixPiece r).carrier ∩ terminalSide.carrier =
      ({terminalSide.source} : Set (EuclideanSpace ℝ (Fin 2)))
  earlier_prefix_disjoint_terminal :
    ∀ i : ℕ, i < r →
      Disjoint (prefixPiece i).carrier terminalSide.carrier
  prefix_disjoint_terminal_connector :
    ∀ i : ℕ, i ≤ r →
      Disjoint (prefixPiece i).carrier terminalConnector.carrier
