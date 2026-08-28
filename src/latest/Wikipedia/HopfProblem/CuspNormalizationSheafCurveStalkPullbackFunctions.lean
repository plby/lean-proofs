import Wikipedia.HopfProblem.CuspNormalizationSheafCuspTerms
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkChartSections

/-!
# Literal extensions of the two normalization-boundary pullbacks

A holomorphic map over a fixed base takes the inverse image of every
base open set to the corresponding inverse image.  Consequently its
section pullback commutes with extension by zero as a global equality
of functions, including outside the original open set.

The two specializations below concern the actual positive and negative
boundary lifts from the actual double curves of the cusp fibre.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk

section OverBase

variable {E H M F G N B : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace G]
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace B]
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F G)
  (p : TopCat.of M ⟶ TopCat.of B) (q : TopCat.of N ⟶ TopCat.of B)
  (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, p (g x) = q x)

/-- Literal section pullback over a base commutes with zero extension
on the actual inverse images of a base open set. -/
theorem sectionPullback_extend (U : Opens B)
    (f : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U)) :
    HolomorphicFunctionSheaf.extendManifoldSection J ((Opens.map q).obj U)
      (SheafOverBase.sectionPullback I J p q g hg U f) =
    fun x : N => HolomorphicFunctionSheaf.extendManifoldSection I
      ((Opens.map p).obj U) f (g x) := by
  classical
  funext x
  have hmem : x ∈ (Opens.map q).obj U ↔ g x ∈ (Opens.map p).obj U := by
    change q x ∈ U ↔ p (g x) ∈ U
    rw [hg x]
  by_cases hx : x ∈ (Opens.map q).obj U
  · have hgx := hmem.mp hx
    rw [HolomorphicFunctionSheaf.extendManifoldSection_apply J _ _ x hx,
      HolomorphicFunctionSheaf.extendManifoldSection_apply I _ f (g x) hgx]
    rfl
  · have hgx : g x ∉ (Opens.map p).obj U := fun h => hx (hmem.mpr h)
    simp only [HolomorphicFunctionSheaf.extendManifoldSection, dif_neg hx, dif_neg hgx]

/-- The same global identity for the actual additive sheaf morphism. -/
theorem additivePullback_extend (U : Opens B)
    (f : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U)) :
    HolomorphicFunctionSheaf.extendManifoldSection J ((Opens.map q).obj U)
      ((SheafOverBase.additivePullback I J p q g hg).hom.app (op U) f) =
    fun x : N => HolomorphicFunctionSheaf.extendManifoldSection I
      ((Opens.map p).obj U) f (g x) :=
  sectionPullback_extend I J p q g hg U f

end OverBase

open CuspQuotient ToricCharts ToricSpace SheafResolution
open CuspQuotient.NormalizationCurves

local notation "I₂" => 𝓘(ℂ, CoordinateSpace 2)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The positive boundary pullback's zero extension is the literal
composition with the actual positive lift into the normalization. -/
theorem plusPullback_extend (k : Fin 3) (U : Opens (CentralSpace C ε))
    (f : HolomorphicFunctionSheaf.Section I₂ (rayDivisor 0)
      ((Opens.map (normalizationMap C ε hε)).obj U)) :
    letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
    HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, ℂ)
      ((Opens.map (sourceCurveMap C ε hε k)).obj U)
      ((plusPullback C ε hε hε1 hC hR k).hom.app (op U) f) =
    fun d : sourceDoubleCurve C ε hε k =>
      HolomorphicFunctionSheaf.extendManifoldSection I₂
        ((Opens.map (normalizationMap C ε hε)).obj U) f
        (sourcePlusLift C ε hε k d) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact additivePullback_extend I₂ 𝓘(ℂ, ℂ)
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k)
    ⟨sourcePlusLift C ε hε k, sourcePlusLift_holomorphic C ε hε hε1 hC hR k⟩
    (normalization_sourcePlusLift C ε hε k) U f

/-- The negative boundary pullback's zero extension is the literal
composition with the actual negative lift into the normalization. -/
theorem minusPullback_extend (k : Fin 3) (U : Opens (CentralSpace C ε))
    (f : HolomorphicFunctionSheaf.Section I₂ (rayDivisor 0)
      ((Opens.map (normalizationMap C ε hε)).obj U)) :
    letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
    HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, ℂ)
      ((Opens.map (sourceCurveMap C ε hε k)).obj U)
      ((minusPullback C ε hε hε1 hC hR k).hom.app (op U) f) =
    fun d : sourceDoubleCurve C ε hε k =>
      HolomorphicFunctionSheaf.extendManifoldSection I₂
        ((Opens.map (normalizationMap C ε hε)).obj U) f
        (sourceMinusLift C ε hε k d) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact additivePullback_extend I₂ 𝓘(ℂ, ℂ)
    (normalizationMap C ε hε) (sourceCurveMap C ε hε k)
    ⟨sourceMinusLift C ε hε k, sourceMinusLift_holomorphic C ε hε hε1 hC hR k⟩
    (normalization_sourceMinusLift C ε hε k) U f

end Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk
