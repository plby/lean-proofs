import Wikipedia.SmoothSixDPoincare.MorseCompactStability

/-!
# Smooth spatial derivatives and Morse points on open coordinate domains

Chart expressions are only smooth on their open targets. These lemmas use
the actual unrestricted derivatives there, without assuming that the chart
expression is globally smooth outside its domain.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.MorsePerturbation

section SpatialDerivative

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Spatial differentiation is smooth wherever the joint function is smooth. -/
theorem contDiffAt_spatialDerivative {f : P → E → F} {q : P × E}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) q) :
    ContDiffAt ℝ ∞ (fun r : P × E => fderiv ℝ (f r.1) r.2) q := by
  let g : (P × E) → E → F := fun r x => f r.1 x
  have hg : ContDiffAt ℝ ∞ (Function.uncurry g) (q, q.2) :=
    hf.comp (q, q.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact hg.fderiv contDiffAt_snd (by simp)

/-- The parameter-dependent derivative is smooth on an arbitrary open joint domain. -/
theorem contDiffOn_spatialDerivative {f : P → E → F} {U : Set (P × E)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) U) :
    ContDiffOn ℝ ∞ (fun q : P × E => fderiv ℝ (f q.1) q.2) U := by
  intro q hq
  exact (contDiffAt_spatialDerivative
    (hf.contDiffAt (hU.mem_nhds hq))).contDiffWithinAt

end SpatialDerivative

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Regular points and nondegenerate critical points form an open subset of the joint domain. -/
theorem isOpen_goodJetOn {f : P → E → ℝ} {U : Set (P × E)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) U) :
    IsOpen {q : P × E | q ∈ U ∧ (fderiv ℝ (f q.1) q.2 ≠ 0 ∨
      Function.Bijective (fderiv ℝ (fderiv ℝ (f q.1)) q.2))} := by
  have h₁ := contDiffOn_spatialDerivative hU hf
  have h₂ := contDiffOn_spatialDerivative (f := fun p x => fderiv ℝ (f p) x) hU h₁
  have hd : ContinuousOn (fun q : P × E =>
      (dualEquiv.symm.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ (f q.1)) q.2)).det) U :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_const.clm_comp h₂.continuousOn)
  have ha := h₁.continuousOn.isOpen_inter_preimage hU
    (isClosed_singleton (x := (0 : E →L[ℝ] ℝ))).isOpen_compl
  have hb := hd.isOpen_inter_preimage hU (isClosed_singleton (x := (0 : ℝ))).isOpen_compl
  have heq : {q : P × E | q ∈ U ∧ (fderiv ℝ (f q.1) q.2 ≠ 0 ∨
      Function.Bijective (fderiv ℝ (fderiv ℝ (f q.1)) q.2))} =
      (U ∩ (fun q : P × E => fderiv ℝ (f q.1) q.2) ⁻¹' {0}ᶜ) ∪
      (U ∩ (fun q : P × E => (dualEquiv.symm.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ (f q.1)) q.2)).det) ⁻¹' {0}ᶜ) := by
    ext q
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_preimage, mem_compl_iff,
      mem_singleton_iff, bijective_hessian_iff]
    exact and_or_left
  rw [heq]
  exact ha.union hb

end Wikipedia.SmoothSixDPoincare.MorsePerturbation
