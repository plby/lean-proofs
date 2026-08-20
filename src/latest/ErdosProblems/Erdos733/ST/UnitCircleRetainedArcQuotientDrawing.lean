import ErdosProblems.Erdos733.ST.GeometricArcDrawing
import ErdosProblems.Erdos733.ST.UnitCircle
import ErdosProblems.Erdos733.ST.UnitCircleRetainedArcDrawingAssembly
import ErdosProblems.Erdos733.ST.UnitCircleRetainedArcEndpointQuotient
import ErdosProblems.Erdos733.ST.UnitCirclesIntersectionsAtMostTwo

open Classical
open scoped BigOperators
open scoped Real
noncomputable section

-- [TABLET NODE: UnitCircleRetainedArcQuotientDrawing]
lemma UnitCircleRetainedArcQuotientDrawing
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ (ι : Type) (instF : Fintype ι) (instD : DecidableEq ι)
      (A : Finset ι) (endpoint : ι → Sym2 P),
      (A.card : ℝ) =
          ∑ p ∈ P.filter
            (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card),
            ((P.filter (fun q => q ∈ UnitCircle p)).card : ℝ) ∧
        (∀ i ∈ A, ¬ (endpoint i).IsDiag) ∧
          (∀ e ∈ A.image endpoint,
            (A.filter (fun i => endpoint i = e)).card ≤ 2) ∧
            (∀ (G : SimpleGraph P) [Fintype G.edgeSet],
              G.edgeFinset = A.image endpoint →
                ∃ D : GeometricArcDrawing G,
                  (D.localPairCount : ℝ) ≤ 2 * (P.card : ℝ) ^ 2) := by
-- BODY
  rcases UnitCircleRetainedArcEndpointQuotient P with
    ⟨ι, instF, instD, A, endpoint, center, arcStart, arcEnd, carrier,
      arcInterior, γ, h_card, h_nondiag, h_multiplicity, h_retained,
      h_endpoint_eq, h_endpoints_distinct, h_endpoints_on_circle, h_arc_param,
      h_carrier_circle, h_no_vertex_in_interior, h_same_center_disjoint,
      h_same_center_endpoint_unique⟩
  refine ⟨ι, instF, instD, A, endpoint, h_card, h_nondiag, h_multiplicity, ?_⟩
  exact UnitCircleRetainedArcDrawingAssembly P A endpoint center arcStart arcEnd
    carrier arcInterior γ h_endpoint_eq h_endpoints_distinct h_endpoints_on_circle
    h_arc_param h_carrier_circle h_no_vertex_in_interior h_same_center_disjoint
