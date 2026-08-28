import Wikipedia.NoExoticSixSphere.SpherePositiveHomologyFinite
import Wikipedia.SmoothSixDPoincare.MorseCellHomologySequence
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finite generation propagates across an actual Morse handle

The original Morse exact sequence presents the new homology as an extension
of a quotient of the old homology by a submodule of the attaching-sphere
homology. Finite generation of those genuine groups proves finite generation
above the handle; no homology model is substituted.
-/

noncomputable section

namespace NoExoticSixSphere

theorem module_finite_of_range_eq_ker
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module ℤ A] [Module ℤ B] [Module ℤ C]
    [Module.Finite ℤ A] [Module.Finite ℤ C]
    (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C) (he : LinearMap.range f = LinearMap.ker g) :
    Module.Finite ℤ B := by
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker g ?_ ?_⟩
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq, ← he]
    exact Submodule.fg_range f

end NoExoticSixSphere

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

theorem upperHomology_finite (hf : Continuous f) (k : ℕ) (hk : k ≠ 0)
    [Module.Finite ℤ (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} (k + 1))] :
    Module.Finite ℤ (SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} (k + 1)) := by
  let := NoExoticSixSphere.unitSphere_positive_homology_finite
    d.chart.NegativeCoordinates k hk
  exact NoExoticSixSphere.module_finite_of_range_eq_ker
    (d.lowerRealizationHomologyMap (k + 1)) (d.morseConnectingMap hf k)
    (d.morse_exact_at_upper hf k)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
