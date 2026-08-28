import Wikipedia.HopfProblem.SmoothCircleApproximationInvariant
import Wikipedia.HopfProblem.SmoothCirclePhaseHomotopy

/-!
# Invariant relative smoothing in the original circle homotopy class

The actual averaged approximation gives a smooth map to the native complex
unit circle. Its normalized straight-line homotopy starts at the original
continuous phase and preserves both the prescribed relative values and the
original action throughout. No smoothness of the starting phase is assumed
outside its specified relative neighborhood.
-/

noncomputable section

open Set
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SmoothCircleApproximation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- Relative invariant smoothing retains the actual unit-circle homotopy
class, with a single native homotopy fixed on the entire prescribed set. -/
theorem exists_invariant_smooth_circle_homotopy
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
    ∃ g : C(M, _root_.Circle),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (fun x => (g x : ℂ)) ∧
      EqOn g (SmoothCirclePhaseHomotopy.unitCircleMap f hf hunit) S ∧
      (∀ (t : ℝ) (x : M), g (act t x) = g x) ∧
      Nonempty (ContinuousMap.HomotopyWith
        (SmoothCirclePhaseHomotopy.unitCircleMap f hf hunit) g
        (fun k => EqOn k (SmoothCirclePhaseHomotopy.unitCircleMap f hf hunit) S ∧
          ∀ (t : ℝ) (x : M), k (act t x) = k x)) := by
  obtain ⟨g, hg, hclose, hne, heq, hgi⟩ :=
    exists_invariant_nonzero_smooth_and_eqOn act hact hadd hperiod
      hf hunit hinv hS hU hSI hfs
  refine ⟨SmoothCirclePhaseHomotopy.normalizedCircleMap g hg.continuous hne,
    StandardSixSphereCircleModel.contMDiff_normalize_of_ne_zero hg hne, ?_, ?_, ?_⟩
  · intro x hx
    apply _root_.Circle.ext
    change normalize (g x) = f x
    rw [heq hx]
    exact normalize_eq_self (hunit x)
  · intro t x
    exact _root_.Circle.ext (congrArg normalize (hgi t x))
  · exact ⟨SmoothCirclePhaseHomotopy.relativeInvariantCircleHomotopy
      f g hf hg.continuous hunit hclose S heq act hinv hgi⟩

end Wikipedia.HopfProblem.SmoothCircleApproximation
