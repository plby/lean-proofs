import Wikipedia.HopfProblem.SmoothCircleApproximation
import Wikipedia.HopfProblem.SmoothCircleAverageSmooth
import Wikipedia.HopfProblem.SmoothCircleAverageBasicEstimates

/-!
# Relative smoothing preserving the original circle action

First approximate the original invariant unit-complex map by a genuine smooth
complex-valued map. Average that approximation over the given period-one real
action before normalizing. The original invariant map controls the average's
distance and prevents zeros. Both invariance and the prescribed relative
values are preserved exactly. No quotient atlas or equivariant approximation
theorem is assumed.
-/

noncomputable section

open Set
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SmoothCircleApproximation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- The literal average of a relative smooth approximation is nonzero,
smooth and invariant, while retaining the original values on the closed set. -/
theorem exists_invariant_nonzero_smooth_and_eqOn
    (act : ℝ → M → M)
    (hact : ContMDiff ((𝓘(ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => act p.1 p.2))
    (hadd : ∀ (t s : ℝ) (x : M), act (t + s) x = act t (act s x))
    (hperiod : ∀ (t : ℝ) (x : M), act (t + 1) x = act t x)
    {f : M → ℂ} (hf : Continuous f) (hunit : ∀ x, ‖f x‖ = 1)
    (hinv : ∀ (t : ℝ) (x : M), f (act t x) = f x)
    {S U : Set M} (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hSI : ∀ t : ℝ, MapsTo (act t) S S)
    (hfs : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f U) :
    ∃ g : M → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ g ∧
      (∀ x, dist (g x) (f x) ≤ (1 / 2 : ℝ)) ∧
      (∀ x, g x ≠ 0) ∧ EqOn g f S ∧
      (∀ (t : ℝ) (x : M), g (act t x) = g x) := by
  obtain ⟨g, hclose, _, heq⟩ :=
    exists_nonzero_smooth_approx_and_eqOn 𝓘(ℝ, E) hf hunit hS hU hfs
  refine ⟨SmoothCircleAverage.average act g,
    SmoothCircleAverage.contMDiff_average act hact g.contMDiff, ?_, ?_, ?_, ?_⟩
  · exact SmoothCircleAverage.dist_average_le_half_of_invariant_close
      act hact.continuous g.contMDiff.continuous f hinv hclose
  · intro x
    exact SmoothCircleAverage.average_ne_zero_of_invariant_close
      act hact.continuous g.contMDiff.continuous f hinv hclose x (hunit x)
  · exact SmoothCircleAverage.average_eqOn_of_invariant act g f hSI heq hinv
  · exact SmoothCircleAverage.average_invariant act hadd hperiod g

/-- A continuous invariant unit phase has a genuine smooth invariant unit
phase with exactly the same values on the prescribed closed relative set. -/
theorem exists_invariant_smooth_unit_and_eqOn
    (act : ℝ → M → M)
    (hact : ContMDiff ((𝓘(ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => act p.1 p.2))
    (hadd : ∀ (t s : ℝ) (x : M), act (t + s) x = act t (act s x))
    (hperiod : ∀ (t : ℝ) (x : M), act (t + 1) x = act t x)
    {f : M → ℂ} (hf : Continuous f) (hunit : ∀ x, ‖f x‖ = 1)
    (hinv : ∀ (t : ℝ) (x : M), f (act t x) = f x)
    {S U : Set M} (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hSI : ∀ t : ℝ, MapsTo (act t) S S)
    (hfs : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f U) :
    ∃ g : M → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ g ∧
      (∀ x, ‖g x‖ = 1) ∧ EqOn g f S ∧
      (∀ (t : ℝ) (x : M), g (act t x) = g x) := by
  obtain ⟨g, hg, _, hne, heq, hgi⟩ :=
    exists_invariant_nonzero_smooth_and_eqOn act hact hadd hperiod
      hf hunit hinv hS hU hSI hfs
  refine ⟨fun x => normalize (g x),
    StandardSixSphereCircleModel.contMDiff_normalize_of_ne_zero hg hne,
    fun x => norm_normalize (hne x), ?_, ?_⟩
  · intro x hx
    change normalize (g x) = f x
    rw [heq hx]
    exact normalize_eq_self (hunit x)
  · intro t x
    exact congrArg normalize (hgi t x)

end Wikipedia.HopfProblem.SmoothCircleApproximation
