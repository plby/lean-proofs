import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionCuspRetractionNaturality

/-!
# The actual boundary-stalk retraction and its differential square

The actual finite-biproduct stalk equivalence assembles the three
curve retractions into a retraction of the actual boundary stalk.
Its coordinates are the genuine stalk maps of the biproduct
projections.  Those formulas and the actual signed curve naturality
prove compatibility with the genuine normalization differential.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (x : CentralSpace C ε)

local notation "K" => SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x
local notation "AC" => curveConstantSheaf C ε hε
local notation "AH" => curveSheaf C ε hε hε1 hC hR

/-- Assemble the actual curve retractions through the actual finite
direct-sum stalk comparison, with no replacement boundary object. -/
def boundaryStalkConstantRetraction :
    (boundarySheaf C ε hε hε1 hC hR).presheaf.stalk x →+
      (boundaryConstantSheaf C ε hε).presheaf.stalk x :=
  (SheafBiproduct.finiteStalkEquiv (TopCat.of (CentralSpace C ε)) AC x).symm.toAddMonoidHom.comp
    (AddMonoidHom.pi fun k =>
      (curveStalkConstantRetraction C ε hε hε1 hC hR k x).comp
        ((K).map (biproduct.π AH k)).hom)

/-- The boundary retraction as a genuine additive stalk morphism. -/
def boundaryStalkConstantRetractionHom :
    (boundarySheaf C ε hε hε1 hC hR).presheaf.stalk x ⟶
      (boundaryConstantSheaf C ε hε).presheaf.stalk x :=
  AddCommGrpCat.ofHom (boundaryStalkConstantRetraction C ε hε hε1 hC hR x)

/-- Each coordinate is the actual curve retraction after the actual
stalk map of the holomorphic biproduct projection. -/
theorem boundaryStalkConstantRetraction_component
    (s : (boundarySheaf C ε hε hε1 hC hR).presheaf.stalk x) (k : Fin 3) :
    SheafBiproduct.finiteStalkEquiv (TopCat.of (CentralSpace C ε)) AC x
        (boundaryStalkConstantRetraction C ε hε hε1 hC hR x s) k =
      curveStalkConstantRetraction C ε hε hε1 hC hR k x ((K).map (biproduct.π AH k) s) :=
  congrFun ((SheafBiproduct.finiteStalkEquiv (TopCat.of (CentralSpace C ε)) AC x).apply_symm_apply
    (fun k => curveStalkConstantRetraction C ε hε hε1 hC hR k x
      ((K).map (biproduct.π AH k) s))) k

/-- The coordinate formula as an equality of actual additive stalk
morphisms, retaining both categorical biproduct projections. -/
theorem boundaryStalkConstantRetraction_component_hom (k : Fin 3) :
    boundaryStalkConstantRetractionHom C ε hε hε1 hC hR x ≫ (K).map (biproduct.π AC k) =
      (K).map (biproduct.π AH k) ≫ curveStalkConstantRetractionHom C ε hε hε1 hC hR k x := by
  ext s
  exact (SheafBiproduct.finiteStalkEquiv_apply (TopCat.of (CentralSpace C ε)) AC x
    (boundaryStalkConstantRetraction C ε hε hε1 hC hR x s) k).symm.trans
      (boundaryStalkConstantRetraction_component C ε hε hε1 hC hR x s k)

/-- Actual constant boundary-stalk morphisms are determined by their
composites with the actual stalk maps of the curve projections. -/
theorem boundaryConstantStalk_hom_ext {A : AddCommGrpCat}
    {φ ψ : A ⟶ (boundaryConstantSheaf C ε hε).presheaf.stalk x}
    (h : ∀ k : Fin 3, φ ≫ (K).map (biproduct.π AC k) = ψ ≫ (K).map (biproduct.π AC k)) :
    φ = ψ := by
  ext s
  apply (SheafBiproduct.finiteStalkEquiv (TopCat.of (CentralSpace C ε)) AC x).injective
  funext k
  exact (SheafBiproduct.finiteStalkEquiv_apply (TopCat.of (CentralSpace C ε)) AC x (φ s) k).trans
    ((ConcreteCategory.congr_hom (h k) s).trans
      (SheafBiproduct.finiteStalkEquiv_apply (TopCat.of (CentralSpace C ε)) AC x (ψ s) k).symm)

/-- The actual boundary constants inclusion followed by its assembled
stalk retraction is the identity on the genuine constant boundary stalk. -/
theorem boundaryStalkConstantRetraction_comp :
    (K).map (boundaryConstantsMap C ε hε hε1 hC hR) ≫
        boundaryStalkConstantRetractionHom C ε hε hε1 hC hR x =
      𝟙 ((boundaryConstantSheaf C ε hε).presheaf.stalk x) := by
  ext s
  apply (SheafBiproduct.finiteStalkEquiv (TopCat.of (CentralSpace C ε)) AC x).injective
  funext k
  have hproj :
      (K).map (biproduct.π AH k) ((K).map (boundaryConstantsMap C ε hε hε1 hC hR) s) =
        (K).map (curveConstantsMap C ε hε hε1 hC hR k) ((K).map (biproduct.π AC k) s) :=
    (ConcreteCategory.congr_hom
      ((K).map_comp (boundaryConstantsMap C ε hε hε1 hC hR) (biproduct.π AH k)) s).symm.trans
      ((congrArg (fun m => (K).map m s)
        (boundaryConstantsMap_component C ε hε hε1 hC hR k)).trans
        (ConcreteCategory.congr_hom
          ((K).map_comp (biproduct.π AC k) (curveConstantsMap C ε hε hε1 hC hR k)) s))
  exact (boundaryStalkConstantRetraction_component C ε hε hε1 hC hR x
    ((K).map (boundaryConstantsMap C ε hε hε1 hC hR) s) k).trans
    ((congrArg (curveStalkConstantRetraction C ε hε hε1 hC hR k x) hproj).trans
      ((curveStalkConstantRetraction_leftInverse C ε hε hε1 hC hR k x
        ((K).map (biproduct.π AC k) s)).trans
        (SheafBiproduct.finiteStalkEquiv_apply (TopCat.of (CentralSpace C ε)) AC x s k).symm))

/-- The assembled retraction is a left inverse on actual boundary-stalk elements. -/
theorem boundaryStalkConstantRetraction_leftInverse :
    Function.LeftInverse (boundaryStalkConstantRetraction C ε hε hε1 hC hR x)
      ((K).map (boundaryConstantsMap C ε hε hε1 hC hR)) := by
  intro s
  exact ConcreteCategory.congr_hom (boundaryStalkConstantRetraction_comp C ε hε hε1 hC hR x) s

/-- The genuine normalization differential commutes with the actual
normalization and boundary stalk retractions. -/
theorem deltaZero_stalkConstantRetraction_naturality :
    normalizationStalkConstantRetractionHom C ε hε hε1 hC hR x ≫
        (K).map (constantDeltaZero C ε hε hε1 hC hR) =
      (K).map (deltaZero C ε hε hε1 hC hR) ≫
        boundaryStalkConstantRetractionHom C ε hε hε1 hC hR x := by
  ext s
  apply (SheafBiproduct.finiteStalkEquiv (TopCat.of (CentralSpace C ε)) AC x).injective
  funext k
  have hcproj :
      (K).map (biproduct.π AC k)
          ((K).map (constantDeltaZero C ε hε hε1 hC hR)
            (normalizationStalkConstantRetraction C ε hε hε1 hC hR x s)) =
        (K).map (constantBoundaryDifference C ε hε hε1 hC hR k)
          (normalizationStalkConstantRetraction C ε hε hε1 hC hR x s) :=
    (ConcreteCategory.congr_hom
      ((K).map_comp (constantDeltaZero C ε hε hε1 hC hR) (biproduct.π AC k))
      (normalizationStalkConstantRetraction C ε hε hε1 hC hR x s)).symm.trans
      (congrArg (fun m : normalizationConstantSheaf C ε hε ⟶ curveConstantSheaf C ε hε k =>
        (K).map m (normalizationStalkConstantRetraction C ε hε hε1 hC hR x s))
        (constantDeltaZero_component C ε hε hε1 hC hR k))
  have hhproj :
      (K).map (biproduct.π AH k) ((K).map (deltaZero C ε hε hε1 hC hR) s) =
        (K).map (boundaryDifference C ε hε hε1 hC hR k) s :=
    (ConcreteCategory.congr_hom
      ((K).map_comp (deltaZero C ε hε hε1 hC hR) (biproduct.π AH k)) s).symm.trans
      (congrArg (fun m : normalizationSheaf C ε hε ⟶ curveSheaf C ε hε hε1 hC hR k =>
        (K).map m s) (deltaZero_component C ε hε hε1 hC hR k))
  have hn := ConcreteCategory.congr_hom
    (boundaryDifference_stalkConstantRetraction_naturality C ε hε hε1 hC hR k x) s
  exact (SheafBiproduct.finiteStalkEquiv_apply (TopCat.of (CentralSpace C ε)) AC x
    ((K).map (constantDeltaZero C ε hε hε1 hC hR)
      (normalizationStalkConstantRetraction C ε hε hε1 hC hR x s)) k).trans
    (hcproj.trans (hn.symm.trans
      ((congrArg (curveStalkConstantRetraction C ε hε hε1 hC hR k x) hhproj.symm).trans
        (boundaryStalkConstantRetraction_component C ε hε hε1 hC hR x
          ((K).map (deltaZero C ε hε hε1 hC hR) s) k).symm)))

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
