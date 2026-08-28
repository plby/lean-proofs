import Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishingComparison

/-!
# The actual holomorphic cusp cup is nonzero

The original native constant cup lies in the literal normalization edge
kernel. Its nonzero class is carried by the proved original edge
isomorphism to the cup of the actual holomorphic one-classes. The
normalization term's constant H² is not assumed to vanish.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing

open CuspNormalization SheafResolution SheafCohomologyConstantEdge
open CuspQuotient ToricSpace SheafCupProduct SheafCupProduct.Cusp

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
  (hR : SmallDrift C r)

/-- The named constant cup is nonzero in the actual normalization edge kernel. -/
theorem constantGamma_cup_constantU_inEdge_ne_zero :
    constantCupInEdge C r hr hr1 hC hR
      (constantGamma C r hr hr1 hC hR) (constantU C r hr hr1 hC hR) ≠ 0 := by
  intro h
  apply constantGamma_cup_constantU_ne_zero C r hr hr1 hC hR
  exact (constantCupInEdge_ι C r hr hr1 hC hR _ _).symm.trans
    ((congrArg (kernel.ι (constantH2EdgeMap C r hr)).hom h).trans
      (map_zero (kernel.ι (constantH2EdgeMap C r hr)).hom))

/-- The original two holomorphic cusp classes have genuinely nonzero cup product. -/
theorem holomorphicGamma_cup_holomorphicU_ne_zero :
    holomorphicCuspCup C r hr hr1 hC hR
      (holomorphicGamma C r hr hr1 hC hR) (holomorphicU C r hr hr1 hC hR) ≠ 0 := by
  intro h
  apply constantGamma_cup_constantU_inEdge_ne_zero C r hr hr1 hC hR
  apply (constantsH2EdgeIso C r hr hr1 hC hR).addCommGroupIsoToAddEquiv.injective
  change (constantsH2EdgeIso C r hr hr1 hC hR).hom
      (constantCupInEdge C r hr hr1 hC hR
        (constantGamma C r hr hr1 hC hR) (constantU C r hr hr1 hC hR)) =
    (constantsH2EdgeIso C r hr hr1 hC hR).hom 0
  exact (constantsH2EdgeIso_constantCup C r hr hr1 hC hR _ _).trans
    (h.trans (map_zero
      (constantsH2EdgeIso C r hr hr1 hC hR).addCommGroupIsoToAddEquiv).symm)

end Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing
