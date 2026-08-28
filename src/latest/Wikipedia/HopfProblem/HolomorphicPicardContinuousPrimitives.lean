import Wikipedia.HopfProblem.HolomorphicPicardContinuousSmooth
import Wikipedia.HopfProblem.HolomorphicPicardCechSheafMap
import Wikipedia.HopfProblem.HolomorphicExponentialSheafUnitsExponential
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothFine
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyFineCocycle

/-!
# Actual continuous coordinates from smooth cocycle primitives

The genuine smooth-function sheaf is fine by a smooth partition of unity.
It therefore solves each actual additive holomorphic cocycle after
restricting scalars in the original charts.  Exponentiating the negatives
of these actual primitives gives compatible nonzero continuous fibre
coordinates for the original exponentiated unit cocycle.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicard.ContinuousSmooth

open HolomorphicSheafCohomology HolomorphicFunctionSheaf.SphereH1
  HolomorphicExponentialSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M]
    {ι : Type} (U : ι → Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i)
    (c : CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, E) M) U)

include hU

/-- A real smooth primitive exists on the original cover, with literal
pointwise differences equal to the original holomorphic cocycle. -/
theorem exists_smooth_primitive :
    ∃ b : ∀ i, SmoothFunctions.Section 𝓘(ℝ, E) M (U i),
      ∀ i j (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
        b i ⟨x, hi⟩ - b j ⟨x, hj⟩ =
          DFunLike.coe (F := HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M (U i ⊓ U j))
            (c.value i j) ⟨x, hi, hj⟩ := by
  let d := Cech.mapCocycle (sheafMap M) c
  obtain ⟨b, hb⟩ := (SmoothFunctions.finiteFine 𝓘(ℝ, E) M).cechOneVanishing
    ι U hU d
  refine ⟨b, ?_⟩
  intro i j x hi hj
  have h := congrArg
    (fun s : SmoothFunctions.Section 𝓘(ℝ, E) M (U i ⊓ U j) => s ⟨x, hi, hj⟩)
    (hb i j)
  exact h

/-- Smooth primitives give actual nonzero continuous coordinates with
the original coordinate-transition convention. -/
theorem exists_exponential_coordinates :
    ∃ a : ∀ i, C(U i, ℂ),
      (∀ i x, a i x ≠ 0) ∧
      ∀ i j (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
        unitSectionEval ((Cech.mapCocycle (exponential 𝓘(ℂ, E) M) c).value i j)
          ⟨x, hi, hj⟩ * a i ⟨x, hi⟩ = a j ⟨x, hj⟩ := by
  obtain ⟨b, hb⟩ := exists_smooth_primitive M U hU c
  let a : ∀ i, C(U i, ℂ) := fun i =>
    ⟨fun x => Complex.exp (-b i x), Complex.continuous_exp.comp (b i).property.continuous.neg⟩
  refine ⟨a, fun i x => Complex.exp_ne_zero _, ?_⟩
  intro i j x hi hj
  change Complex.exp
    (DFunLike.coe (F := HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M (U i ⊓ U j))
      (c.value i j) ⟨x, hi, hj⟩) *
    Complex.exp (-b i ⟨x, hi⟩) = Complex.exp (-b j ⟨x, hj⟩)
  rw [← Complex.exp_add, ← hb i j x hi hj]
  congr 1
  ring

end Wikipedia.HopfProblem.HolomorphicPicard.ContinuousSmooth
