import Wikipedia.HopfProblem.SheafCupProductFunctions
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyConstantEdge

/-!
# The actual constant cup vanishes after cusp normalization

The normalization pullback is an actual ring-sheaf morphism to the
actual constant direct image. Its complex constants are the images of
the original global constants. Naturality of the native cup and the
proved H¹ vanishing of that direct image show that every constant cup
belongs to the genuine H² edge kernel. No H² vanishing is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.SheafCupProduct.Cusp

open GodementRing CuspNormalization
open SheafResolution SheafCohomologyConstantEdge CuspQuotient ToricCharts ToricSpace

private theorem map_cup_eq_zero_of_h1 {X : TopCat.{0}} {F G : RingSheaf X}
    (f : F ⟶ G) (ρ : ℂ →+* End ((forgetSheaf X).obj F))
    (σ : ℂ →+* End ((forgetSheaf X).obj G)) (h : Subsingleton (H G 1))
    (a b : H F 1) : cohomologyMap f 2 (cup F ρ a b) = 0 := by
  rw [cup_naturality f ρ σ]
  have hz : cohomologyMap f 1 a = 0 := h.elim _ _
  rw [hz, map_zero, AddMonoidHom.zero_apply]

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual ring-valued constant direct image from the normalization. -/
def normalizationConstantRingSheaf : RingSheaf (TopCat.of (CentralSpace C ε)) :=
  (TopCat.Sheaf.pushforward CommRingCat (normalizationMap C ε hε)).obj
    (SheafConstants.complexSheaf (TopCat.of (rayDivisor 0)))

/-- The original geometric normalization pulls back actual constant ring sections. -/
def normalizationConstantRingPullback :
    SheafConstants.complexSheaf (TopCat.of (CentralSpace C ε)) ⟶
      normalizationConstantRingSheaf C ε hε :=
  SheafConstants.pullbackMap (normalizationMap C ε hε)

theorem forget_normalizationConstantRingSheaf :
    (forgetSheaf (TopCat.of (CentralSpace C ε))).obj
        (normalizationConstantRingSheaf C ε hε) = normalizationConstantSheaf C ε hε := rfl

theorem forget_normalizationConstantRingPullback :
    (forgetSheaf (TopCat.of (CentralSpace C ε))).map
        (normalizationConstantRingPullback C ε hε) =
      normalizationConstantPullback C ε hε := rfl

/-- Actual global constants on the direct image, sent by the normalization map. -/
def normalizationCoefficients : Scalars.Coefficients (normalizationConstantRingSheaf C ε hε) :=
  Scalars.pushCoefficients (normalizationConstantRingPullback C ε hε)
    (constantCoefficients (TopCat.of (CentralSpace C ε)))

variable (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

include hε1 hC hR

/-- The literal normalization H² map kills the genuine constant-sheaf cup. -/
theorem constantCup_normalization_zero
    (a b : CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1) :
    constantH2EdgeMap C ε hε (constantCup (TopCat.of (CentralSpace C ε)) a b) = 0 :=
  map_cup_eq_zero_of_h1 (normalizationConstantRingPullback C ε hε)
    (constantScalarEnd (TopCat.of (CentralSpace C ε)))
    (Scalars.scalarEnd (normalizationCoefficients C ε hε))
    (normalizationConstant_h1_subsingleton C ε hε hε1 hC hR) a b

end Wikipedia.HopfProblem.SheafCupProduct.Cusp
