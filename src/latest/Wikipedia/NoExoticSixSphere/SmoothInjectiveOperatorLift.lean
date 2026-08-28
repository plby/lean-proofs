import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth recovery from a varying injective linear operator

A solution of `A x (w x) = v x` is smooth near an injective `A x₀` when
`A` and `v` are smooth. No prior continuity of the solution is required.
A fixed left inverse at the base point reduces the proof to inversion of
square operators near the identity. No inner product on the source is used.
-/

noncomputable section

open Function Filter Set
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {B H X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace X] [ChartedSpace H X]

theorem contMDiffAt_of_eventually_injective_apply_eq
    {A : X → E →L[ℝ] F} {v : X → F} {w : X → E} {x : X}
    (hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) ∞ A x)
    (hv : ContMDiffAt I 𝓘(ℝ, F) ∞ v x) (hi : Injective (A x))
    (he : ∀ᶠ y in 𝓝 x, A y (w y) = v y) : ContMDiffAt I 𝓘(ℝ, E) ∞ w x := by
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hi
  have hLA : L.comp (A x) = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    exact hL
  have hsq : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (fun y ↦ L.comp (A y)) x :=
    contMDiffAt_const.clm_comp hA
  have hix : (L.comp (A x)).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.refl ℝ E, ?_⟩
    exact hLA.symm
  have hinv : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun y ↦ (L.comp (A y)).inverse) x :=
    ContDiffAt.comp_contMDiffAt (f := fun y ↦ L.comp (A y)) (x := x)
      hix.contDiffAt_map_inverse hsq
  have hLv : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun y ↦ L (v y)) x :=
    L.contDiff.contMDiff.contMDiffAt.comp x hv
  have ho : IsOpen {T : E →L[ℝ] E | T.IsInvertible} := ContinuousLinearEquiv.isOpen
  have heq : w =ᶠ[𝓝 x] (fun y ↦ (L.comp (A y)).inverse (L (v y))) := by
    filter_upwards [hsq.continuousAt (ho.mem_nhds hix), he] with y hy hyw
    change (L.comp (A y)).IsInvertible at hy
    rw [← hyw]
    exact (hy.inverse_apply_self (w y)).symm
  exact heq.contMDiffAt_iff.mpr (hinv.clm_apply hLv)

end NoExoticSixSphere
