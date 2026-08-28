import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivativeRegularity
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDolbeaultLocal

/-!
# A genuine local Cauchy--Green primitive of the original base mean

The zero Fourier coefficient is the original normalized Haar mean. Its
real smoothness has already been proved from the actual joint smoothness
of the torus family. The proved one-variable Cauchy--Green construction
therefore supplies a globally smooth scalar function solving the base
equation on an actual smaller open neighborhood.
-/

noncomputable section

open TopologicalSpace Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeBasePrimitive

open FourierParameter

variable {U : Opens ℂ} {d : Type*} [Fintype d]

/-- The actual Haar mean has a local primitive, witnessed by the proved Cauchy--Green solver. -/
theorem exists_local_mean_primitive (f : SmoothFamily U d) (b₀ : U) :
    ∃ V : Opens ℂ, V ≤ U ∧ (b₀ : ℂ) ∈ V ∧
      ∃ u : ℂ → ℂ, ContDiff ℝ ∞ u ∧
        ∀ b : V, (fderiv ℝ u (b : ℂ) 1 +
          Complex.I * fderiv ℝ u (b : ℂ) Complex.I) / 2 =
            f.coefficientValue 0 (b : ℂ) := by
  obtain ⟨u, hu, he⟩ :=
    HolomorphicSheafCohomology.DolbeaultLocal.exists_smooth_dbar_primitive_germ
      U.isOpen (f.coefficientValue_contDiffOn 0) b₀.property
  obtain ⟨W, hW, hWo, hbW⟩ := mem_nhds_iff.mp
    (inter_mem (U.isOpen.mem_nhds b₀.property) he)
  refine ⟨⟨W, hWo⟩, fun z hz => (hW hz).1, hbW, u, hu, ?_⟩
  intro b
  exact (hW b.property).2

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeBasePrimitive
