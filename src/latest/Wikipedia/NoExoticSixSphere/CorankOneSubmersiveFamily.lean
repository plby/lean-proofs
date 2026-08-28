import Wikipedia.NoExoticSixSphere.CorankOneChart
import Wikipedia.NoExoticSixSphere.ParametricRegularOpen

/-!
# Corank-one transversality for a submersive operator family

The parameter dependence may be nonlinear. On an actual open joint domain,
surjectivity of the operator-family derivative makes the residual a submersion.
Parametric Sard then gives spatial residual regularity almost everywhere.
-/

noncomputable section

open Set Function TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.CorankOneSubmersion

open CorankOne

variable {P X E F : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def domain (D : P × X → BlockMap E F) (U : Opens (P × X))
    (hD : ContinuousOn D U) : Opens (P × X) :=
  ⟨(U : Set (P × X)) ∩ D ⁻¹' (chart (E := E) (F := F) : Set (BlockMap E F)),
    ContinuousOn.isOpen_inter_preimage (f := D)
      (t := (chart (E := E) (F := F) : Set (BlockMap E F))) hD U.isOpen
      (chart (E := E) (F := F)).isOpen⟩

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ X] [FiniteDimensional ℝ F] in
theorem contDiffOn_residual_family (D : P × X → BlockMap E F) (U : Opens (P × X))
    (hD : ContDiffOn ℝ ∞ D U) :
    ContDiffOn ℝ ∞ (fun q ↦ residual (D q)) (domain D U hD.continuousOn) := by
  intro q hq
  have hDd := hD.contDiffAt (U.isOpen.mem_nhds hq.1)
  exact ((contDiffAt_residual (D q) (leading_invertible hq.2)).comp
    (f := D) q hDd).contDiffWithinAt

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ X] [FiniteDimensional ℝ F] in
theorem surjective_fderiv_residual_family (D : P × X → BlockMap E F)
    (U : Opens (P × X)) (hD : ContDiffOn ℝ ∞ D U) (q : P × X)
    (hq : q ∈ domain D U hD.continuousOn) (hs : Surjective (fderiv ℝ D q)) :
    Surjective (fderiv ℝ (fun q ↦ residual (D q)) q) := by
  have hDd := (hD.contDiffAt (U.isOpen.mem_nhds hq.1)).differentiableAt (by simp)
  have hR := (contDiffAt_residual (D q) (leading_invertible hq.2))
  have hRd := hR.differentiableAt (by simp)
  have he := (hRd.hasFDerivAt.comp q hDd.hasFDerivAt).fderiv
  change Surjective (fderiv ℝ (residual ∘ D) q)
  rw [he]
  exact (surjective_fderiv_residual (D q) (leading_invertible hq.2)).comp hs

theorem ae_regular_family [MeasurableSpace P] [BorelSpace P]
    (μ : Measure P) [IsAddHaarMeasure μ] (D : P × X → BlockMap E F)
    (U : Opens (P × X)) (hD : ContDiffOn ℝ ∞ D U)
    (hs : ∀ q ∈ U, Surjective (fderiv ℝ D q)) :
    ∀ᵐ p ∂μ, ∀ x, (p, x) ∈ U → D (p, x) ∈ chart → residual (D (p, x)) = 0 →
      Surjective (fderiv ℝ (fun y ↦ residual (D (p, y))) x) := by
  have h := ParametricRegular.ae_parameters_on μ (fun q ↦ residual (D q))
    (domain D U hD.continuousOn) (contDiffOn_residual_family D U hD)
    (fun q hq _ ↦ surjective_fderiv_residual_family D U hD q hq (hs q hq.1))
  exact h.mono fun p hp x hx hc hz ↦ hp x ⟨hx, hc⟩ hz

end NoExoticSixSphere.CorankOneSubmersion
