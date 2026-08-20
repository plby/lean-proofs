import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: SimpleClosedPolygonalCurve]
structure SimpleClosedPolygonalCurve where
-- BODY
  carrier : Set (EuclideanSpace ℝ (Fin 2))
  edgeArcs : Finset PolygonalArc
  edgeArcs_nonempty : edgeArcs.Nonempty
  carrier_eq :
    carrier = ⋃ γ : {γ // γ ∈ edgeArcs}, γ.1.carrier
  successor : Equiv.Perm {γ : PolygonalArc // γ ∈ edgeArcs}
  successor_single_cycle :
    ∀ γ δ : {γ : PolygonalArc // γ ∈ edgeArcs},
      ∃ n : ℕ, (successor^[n]) γ = δ
  adjacent_endpoint :
    ∀ γ : {γ : PolygonalArc // γ ∈ edgeArcs},
      γ.1.target = (successor γ).1.source
  adjacent_intersection :
    ∀ γ : {γ : PolygonalArc // γ ∈ edgeArcs},
      γ.1.carrier ∩ (successor γ).1.carrier = {γ.1.target}
  nonadjacent_disjoint :
    ∀ γ δ : {γ : PolygonalArc // γ ∈ edgeArcs},
      δ ≠ γ → δ ≠ successor γ → successor δ ≠ γ →
        Disjoint γ.1.carrier δ.1.carrier
