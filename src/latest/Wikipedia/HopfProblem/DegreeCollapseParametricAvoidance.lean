import Wikipedia.NoExoticSixSphere.ParametricRegularOpen

/-!
# Actual parametric avoidance when the source dimension is smaller

Parametric Sard makes the original spatial derivative surjective at
every zero for almost every parameter. If the original spatial source
has smaller dimension than the target, no such derivative can be onto.
Thus those actual parameter slices have no zeros on the actual open
domain, including domains coupling the parameter and source variables.
-/

noncomputable section

open Function Set TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ParametricAvoidance

variable {P E F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem surjective_fderiv_of_parameter (f : P × E → F) (q : P × E)
    (hf : DifferentiableAt ℝ f q)
    (hp : Surjective (fderiv ℝ (fun p : P ↦ f (p, q.2)) q.1)) :
    Surjective (fderiv ℝ f q) := by
  have hi : HasFDerivAt (fun p : P ↦ (p, q.2))
      (ContinuousLinearMap.inl ℝ P E) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hf.hasFDerivAt.comp q.1 hi).fderiv
  change fderiv ℝ (fun p : P ↦ f (p, q.2)) q.1 = _ at he
  rw [he] at hp
  intro y
  obtain ⟨v, hv⟩ := hp y
  exact ⟨(v, 0), hv⟩

theorem ae_avoid_zero_on [MeasurableSpace P] [BorelSpace P]
    (μ : Measure P) [IsAddHaarMeasure μ] (f : P × E → F) (U : Opens (P × E))
    (hf : ContDiffOn ℝ ∞ f U)
    (hreg : ∀ q ∈ U, f q = 0 → Surjective (fderiv ℝ f q))
    (hd : Module.finrank ℝ E < Module.finrank ℝ F) :
    ∀ᵐ p ∂μ, ∀ x : E, (p, x) ∈ U → f (p, x) ≠ 0 := by
  apply (NoExoticSixSphere.ParametricRegular.ae_parameters_on μ f U hf hreg).mono
  intro p hp x hx hz
  have hle := LinearMap.finrank_le_finrank_of_surjective
    (f := (fderiv ℝ (fun y ↦ f (p, y)) x).toLinearMap) (hp x hx hz)
  exact (not_le_of_gt hd) hle

theorem ae_avoid_zero_of_parameter [MeasurableSpace P] [BorelSpace P]
    (μ : Measure P) [IsAddHaarMeasure μ] (f : P × E → F) (U : Opens (P × E))
    (hf : ContDiffOn ℝ ∞ f U)
    (hp : ∀ q ∈ U, Surjective (fderiv ℝ (fun p : P ↦ f (p, q.2)) q.1))
    (hd : Module.finrank ℝ E < Module.finrank ℝ F) :
    ∀ᵐ p ∂μ, ∀ x : E, (p, x) ∈ U → f (p, x) ≠ 0 := by
  apply ae_avoid_zero_on μ f U hf _ hd
  intro q hq _
  exact surjective_fderiv_of_parameter f q
    ((hf.contDiffAt (U.isOpen.mem_nhds hq)).differentiableAt (by simp)) (hp q hq)

end Wikipedia.HopfProblem.DegreeCollapse.ParametricAvoidance
