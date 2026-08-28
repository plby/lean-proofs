import Wikipedia.NoExoticSixSphere.RegularLevelManifold
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# The tangent space of the constructed regular level

The subtype inclusion has injective differential. At a regular point its
image is exactly the kernel of the defining differential, not merely a
subspace of the right dimension chosen independently of the inclusion.
-/

open scoped Manifold ContDiff
open Set Module

namespace NoExoticSixSphere.RegularLevelAtlas

variable {B H M F K : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K]
  {f : M → F} (A : RegularLevelAtlas (K := K) I f)

theorem injective_mfderiv_subtype_val (x : {x : M // f x = 0}) :
    letI := A.chartedSpace;
    Function.Injective (mfderiv 𝓘(ℝ, K) I ((↑) : {x : M // f x = 0} → M) x) := by
  let := A.chartedSpace
  let := A.isManifold
  let g : M → K := fun y ↦ (A.normalForm x y).2
  have hg : ContMDiffAt I 𝓘(ℝ, K) ∞ g x.val :=
    contDiff_snd.contMDiff.contMDiffAt.comp x.val
      ((A.normalForm x).contMDiffOn_toFun.contMDiffAt
        ((A.normalForm x).open_source.mem_nhds (A.mem_source x)))
  have hi := A.contMDiff_subtype_val.mdifferentiable (by simp) x
  have hc : Function.Injective (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, K) (A.chart x) x) :=
    (mdifferentiable_chart (I := 𝓘(ℝ, K)) x).mfderiv_injective (A.mem_chart_source x)
  have heq : (A.chart x : {x : M // f x = 0} → K) =
      g ∘ ((↑) : {x : M // f x = 0} → M) := rfl
  rw [heq, mfderiv_comp x (hg.mdifferentiableAt (by simp)) hi] at hc
  intro v w hvw
  apply hc
  exact congrArg (mfderiv I 𝓘(ℝ, K) g x.val) hvw

theorem differential_comp_inclusion (x : {x : M // f x = 0})
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x.val) :
    letI := A.chartedSpace;
    (mfderiv I 𝓘(ℝ, F) f x.val).comp
      (mfderiv 𝓘(ℝ, K) I ((↑) : {x : M // f x = 0} → M) x) = 0 := by
  let := A.chartedSpace
  have h := mfderiv_comp x hf (A.contMDiff_subtype_val.mdifferentiable (by simp) x)
  have heq : f ∘ ((↑) : {x : M // f x = 0} → M) = fun _ ↦ (0 : F) :=
    funext (fun z ↦ z.property)
  rw [heq, mfderiv_const] at h
  exact h.symm

theorem range_inclusion_le_kernel (x : {x : M // f x = 0})
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x.val) :
    letI := A.chartedSpace;
    (mfderiv 𝓘(ℝ, K) I ((↑) : {x : M // f x = 0} → M) x).range ≤
      (mfderiv I 𝓘(ℝ, F) f x.val).ker := by
  let := A.chartedSpace
  rintro v ⟨w, rfl⟩
  change (mfderiv I 𝓘(ℝ, F) f x.val)
    ((mfderiv 𝓘(ℝ, K) I ((↑) : {x : M // f x = 0} → M) x) w) = 0
  exact congrArg (fun L : TangentSpace 𝓘(ℝ, K) x →L[ℝ] F ↦ L w)
    (A.differential_comp_inclusion x hf)

variable [FiniteDimensional ℝ B] [FiniteDimensional ℝ F] [FiniteDimensional ℝ K]

omit [FiniteDimensional ℝ F] in
theorem range_inclusion_eq_kernel (x : {x : M // f x = 0})
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x.val)
    (hreg : Function.Surjective (mfderiv I 𝓘(ℝ, F) f x.val))
    (hd : finrank ℝ B = finrank ℝ F + finrank ℝ K) :
    letI := A.chartedSpace;
    (mfderiv 𝓘(ℝ, K) I ((↑) : {x : M // f x = 0} → M) x).range =
      (mfderiv I 𝓘(ℝ, F) f x.val).ker := by
  let := A.chartedSpace
  let : FiniteDimensional ℝ (TangentSpace I x.val) := inferInstanceAs (FiniteDimensional ℝ B)
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, K) x) := inferInstanceAs (FiniteDimensional ℝ K)
  apply Submodule.eq_of_le_of_finrank_eq (A.range_inclusion_le_kernel x hf)
  rw [LinearMap.finrank_range_of_inj (A.injective_mfderiv_subtype_val x)]
  let D : B →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f x.val
  exact (finrank_kernel_of_surjective D hreg (finrank ℝ K) hd).symm

end NoExoticSixSphere.RegularLevelAtlas
