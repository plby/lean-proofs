import Wikipedia.HopfProblem.SheafCupProductCuspCoefficients

/-!
# The original cusp coefficient isomorphisms preserve the actual cup

The degree-one isomorphism is the original constants inclusion. On the
actual degree-two edge kernel, the degree-two isomorphism is that same
inclusion following the original kernel inclusion. Consequently the
lifted constant cup maps to the actual reduced-holomorphic cup, with no
singular-cohomology identification or nonvanishing assertion.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SheafCupProduct.Cusp

open CuspNormalization SheafResolution SheafCohomologyConstantEdge
open CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The original constants map on cusp cohomology preserves the native cup. -/
theorem reducedConstantsMap_cup
    (a b : CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1) :
    CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) 2
        (constantCup (TopCat.of (CentralSpace C ε)) a b) =
      holomorphicCuspCup C ε hε hε1 hC hR
        (CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) 1 a)
        (CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) 1 b) := by
  have h := cup_naturality (reducedConstantsRingMap C ε hε hε1 hC hR)
    (constantScalarEnd (TopCat.of (CentralSpace C ε)))
    (SheafCohomologyScalarResolution.reducedSheafScalarEnd C ε hε hε1 hC hR) a b
  change CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) 2
      (constantCup (TopCat.of (CentralSpace C ε)) a b) =
    holomorphicCuspCup C ε hε hε1 hC hR
      (CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) 1 a)
      (CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) 1 b) at h
  exact h

/-- The actual degree-two edge isomorphism sends the lifted constant
cup to the actual holomorphic cup of the degree-one coefficient images. -/
theorem constantsH2EdgeIso_constantCup
    (a b : CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1) :
    (constantsH2EdgeIso C ε hε hε1 hC hR).hom
        (constantCupInEdge C ε hε hε1 hC hR a b) =
      holomorphicCuspCup C ε hε hε1 hC hR
        ((constantsH1Iso C ε hε hε1 hC hR).hom a)
        ((constantsH1Iso C ε hε hε1 hC hR).hom b) := by
  change CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) 2
      (kernel.ι (constantH2EdgeMap C ε hε) (constantCupInEdge C ε hε hε1 hC hR a b)) =
    holomorphicCuspCup C ε hε hε1 hC hR
      (CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) 1 a)
      (CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) 1 b)
  exact (congrArg (CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) 2)
    (constantCupInEdge_ι C ε hε hε1 hC hR a b)).trans
      (reducedConstantsMap_cup C ε hε hε1 hC hR a b)

end Wikipedia.HopfProblem.SheafCupProduct.Cusp
