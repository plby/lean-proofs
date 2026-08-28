import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionStalkRetraction
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationNaturalityBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationStalkNaturality

/-!
# Naturality of the actual scalar-evaluation stalk retraction

For actual holomorphic maps over the base, retracting to constant stalk
values commutes with pullback.  Equality is checked through the proved
finite-fibre equivalence, using the independent naturality of actual
holomorphic evaluation and actual constant-sheaf evaluation.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace G] (J : ModelWithCorners ℂ F G)
  {N : Type} [TopologicalSpace N] [ChartedSpace G N] [T2Space N]
  {B : Type} [TopologicalSpace B]

/-- The actual retraction commutes with the actual holomorphic and
constant-sheaf pullbacks over a common base. -/
theorem holomorphicStalkConstantRetraction_naturality
    (p : TopCat.of M ⟶ TopCat.of B) (hp : IsClosedMap p)
    (q : TopCat.of N ⟶ TopCat.of B) (hq : IsClosedMap q)
    (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, p (g x) = q x)
    (b : B) (hfiniteP : (p ⁻¹' {b}).Finite) (hfiniteQ : (q ⁻¹' {b}).Finite)
    (s : (SheafEvaluation.pushedHolomorphicSheaf I p).presheaf.stalk b) :
    holomorphicStalkConstantRetraction J q hq b hfiniteQ
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
          (SheafOverBase.additivePullback I J p q g hg).hom s) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
        (additiveOverBaseMap p q (holomorphicTopMap I J g) hg).hom
        (holomorphicStalkConstantRetraction I p hp b hfiniteP s) := by
  apply (constantFibreValueEquiv q hq b hfiniteQ).injective
  funext x
  calc
    _ = SheafEvaluation.stalkEvaluationAt J q x.val b x.property
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
          (SheafOverBase.additivePullback I J p q g hg).hom s) :=
      holomorphicStalkConstantRetraction_component J q hq b hfiniteQ _ x
    _ = SheafEvaluation.stalkEvaluationAt I p (g x.val) b
        ((hg x.val).trans x.property) s :=
      SheafEvaluation.stalkEvaluationAt_naturality I J p q g hg x.val b x.property s
    _ = constantStalkEvaluationAt p (g x.val) b ((hg x.val).trans x.property)
        (holomorphicStalkConstantRetraction I p hp b hfiniteP s) :=
      (holomorphicStalkConstantRetraction_eval I p hp b hfiniteP s
        (g x.val) ((hg x.val).trans x.property)).symm
    _ = constantStalkEvaluationAt q x.val b x.property
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
          (additiveOverBaseMap p q (holomorphicTopMap I J g) hg).hom
          (holomorphicStalkConstantRetraction I p hp b hfiniteP s)) :=
      (constantStalkEvaluationAt_naturality p q (holomorphicTopMap I J g) hg
        x.val b x.property (holomorphicStalkConstantRetraction I p hp b hfiniteP s)).symm
    _ = _ := (constantFibreValueEquiv_apply q hq b hfiniteQ _ x).symm

/-- The same naturality as a commuting square of actual additive stalk
morphisms, suitable for maps between stalk complexes. -/
theorem holomorphicStalkConstantRetraction_naturality_hom
    (p : TopCat.of M ⟶ TopCat.of B) (hp : IsClosedMap p)
    (q : TopCat.of N ⟶ TopCat.of B) (hq : IsClosedMap q)
    (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, p (g x) = q x)
    (b : B) (hfiniteP : (p ⁻¹' {b}).Finite) (hfiniteQ : (q ⁻¹' {b}).Finite) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
        (SheafOverBase.additivePullback I J p q g hg).hom ≫
      holomorphicStalkConstantRetractionHom J q hq b hfiniteQ =
        holomorphicStalkConstantRetractionHom I p hp b hfiniteP ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
            (additiveOverBaseMap p q (holomorphicTopMap I J g) hg).hom := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact holomorphicStalkConstantRetraction_naturality I J p hp q hq g hg
    b hfiniteP hfiniteQ s

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
