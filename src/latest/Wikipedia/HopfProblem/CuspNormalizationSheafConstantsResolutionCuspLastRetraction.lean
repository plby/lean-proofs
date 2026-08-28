import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionCuspRetraction
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionCuspEvaluation
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionComparison

/-!
# The actual last normalization differential commutes with stalk retractions

The actual boundary retraction preserves each curve projection and each
endpoint evaluation. It therefore preserves their source-oriented sum
`+ - +`. The actual finite-biproduct stalk comparison combines the two
endpoint identities into the final differential square, with identity on
the same two scalar skyscraper stalks.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (x : CentralSpace C ε)

local notation "Base" => TopCat.of (CentralSpace C ε)
local notation "F" => SheafBiproduct.stalkFunctor Base x
local notation "AC" => curveConstantSheaf C ε hε
local notation "AH" => curveSheaf C ε hε hε1 hC hR
local notation "AT" => triplePointSheaf C ε hε

/-- Each actual projected endpoint evaluation commutes with the genuine
boundary-stalk retraction. -/
theorem projectedEvaluation_stalkConstantRetraction_naturality (k : Fin 3) (t : Fin 2) :
    boundaryStalkConstantRetractionHom C ε hε hε1 hC hR x ≫
        (F).map (biproduct.π AC k ≫ curveConstantEvaluation C ε hε k t) =
      (F).map (biproduct.π AH k ≫ curveEvaluation C ε hε hε1 hC hR k t) := by
  let r : (F).obj (boundarySheaf C ε hε hε1 hC hR) ⟶
      (F).obj (boundaryConstantSheaf C ε hε) :=
    boundaryStalkConstantRetractionHom C ε hε hε1 hC hR x
  let rk : (F).obj (AH k) ⟶ (F).obj (AC k) :=
    curveStalkConstantRetractionHom C ε hε hε1 hC hR k x
  have hproj : r ≫ (F).map (biproduct.π AC k) =
      (F).map (biproduct.π AH k) ≫ rk :=
    boundaryStalkConstantRetraction_component_hom C ε hε hε1 hC hR x k
  have heval : rk ≫ (F).map (curveConstantEvaluation C ε hε k t) =
      (F).map (curveEvaluation C ε hε hε1 hC hR k t) :=
    curveEvaluation_stalkConstantRetraction_naturality C ε hε hε1 hC hR k t x
  change r ≫ (F).map _ = (F).map _
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc,
    hproj, Category.assoc, heval]

/-- At either actual triple point, the retraction preserves the
source's actual alternating endpoint map on every base stalk. -/
theorem deltaOneAt_stalkConstantRetraction_naturality (t : Fin 2) :
    boundaryStalkConstantRetractionHom C ε hε hε1 hC hR x ≫
        (F).map (constantDeltaOneAt C ε hε t) =
      (F).map (deltaOneAt C ε hε hε1 hC hR t) := by
  let r : (F).obj (boundarySheaf C ε hε hε1 hC hR) ⟶
      (F).obj (boundaryConstantSheaf C ε hε) :=
    boundaryStalkConstantRetractionHom C ε hε hε1 hC hR x
  have h (k : Fin 3) :
      r ≫ (F).map (biproduct.π AC k ≫ curveConstantEvaluation C ε hε k t) =
        (F).map (biproduct.π AH k ≫ curveEvaluation C ε hε hε1 hC hR k t) :=
    projectedEvaluation_stalkConstantRetraction_naturality C ε hε hε1 hC hR x k t
  change r ≫ (F).map _ = (F).map _
  simp only [constantDeltaOneAt, deltaOneAt, Functor.map_add, Functor.map_sub,
    Preadditive.comp_add, Preadditive.comp_sub, h]

/-- The genuine final differential square for the actual constant
stalk retractions, with identity on both actual skyscraper summands. -/
theorem deltaOne_stalkConstantRetraction_naturality :
    boundaryStalkConstantRetractionHom C ε hε hε1 hC hR x ≫
        (F).map (constantDeltaOne C ε hε) =
      (F).map (deltaOne C ε hε hε1 hC hR) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply (SheafBiproduct.finiteStalkEquiv Base AT x).injective
  funext t
  have hC' : (F).map (constantDeltaOne C ε hε) ≫ (F).map (biproduct.π AT t) =
      (F).map (constantDeltaOneAt C ε hε t) :=
    ((F).map_comp _ _).symm.trans
      (congrArg (F).map (constantDeltaOne_component C ε hε t))
  have hH' : (F).map (deltaOne C ε hε hε1 hC hR) ≫ (F).map (biproduct.π AT t) =
      (F).map (deltaOneAt C ε hε hε1 hC hR t) :=
    ((F).map_comp _ _).symm.trans
      (congrArg (F).map (deltaOne_component C ε hε hε1 hC hR t))
  exact (SheafBiproduct.finiteStalkEquiv_apply Base AT x
    ((F).map (constantDeltaOne C ε hε)
      (boundaryStalkConstantRetractionHom C ε hε hε1 hC hR x s)) t).trans
    ((ConcreteCategory.congr_hom hC'
      (boundaryStalkConstantRetractionHom C ε hε hε1 hC hR x s)).trans
        ((ConcreteCategory.congr_hom
          (deltaOneAt_stalkConstantRetraction_naturality C ε hε hε1 hC hR x t) s).trans
            ((ConcreteCategory.congr_hom hH' s).symm.trans
              (SheafBiproduct.finiteStalkEquiv_apply Base AT x
                ((F).map (deltaOne C ε hε hε1 hC hR) s) t).symm)))

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
