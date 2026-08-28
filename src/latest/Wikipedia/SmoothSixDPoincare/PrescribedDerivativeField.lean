import Wikipedia.SmoothSixDPoincare.RegularPointField
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Global fields with prescribed derivative supported in the regular locus

The equation `df(V) = χ` defines a convex affine subset in each tangent
space. The constructed regular-point fields provide local solutions; near
the critical locus the supported right-hand side vanishes and the zero
field is a local solution. Mathlib's proved smooth-section gluing theorem
assembles these into an actual global smooth vector field.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- Construct a global field solving `df(V) = χ` when `χ` is supported away from critical points. -/
theorem exists_prescribedDerivativeField {f χ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ)
    (hsupp : tsupport χ ⊆ (ManifoldMorse.criticalPoints E f)ᶜ) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      ∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) = χ x := by
  let C : (x : M) → Set (TangentSpace 𝓘(ℝ, E) x) :=
    fun x => {w | mvfderiv 𝓘(ℝ, E) f x w = χ x}
  have hC (x : M) : Convex ℝ (C x) :=
    (convex_singleton (χ x)).linear_preimage (mvfderiv 𝓘(ℝ, E) f x).toLinearMap
  have hlocal : ∀ p : M, ∃ U ∈ 𝓝 p,
      ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) U ∧
        ∀ x ∈ U, V x ∈ C x := by
    intro p
    by_cases hp : p ∉ ManifoldMorse.criticalPoints E f
    · obtain ⟨U, hU, hpU, V, hV, hVunit⟩ := exists_unitSpeedField_near_regular hf hp
      refine ⟨U, hU.mem_nhds hpU, (fun x => χ x • V x),
        hχ.contMDiffOn.smul_section hV, ?_⟩
      intro x hx
      change mvfderiv 𝓘(ℝ, E) f x (χ x • V x) = χ x
      rw [map_smul, hVunit x hx, smul_eq_mul, mul_one]
    · have hps : p ∉ tsupport χ := fun h => hp (hsupp h)
      refine ⟨(tsupport χ)ᶜ, (isClosed_tsupport χ).isOpen_compl.mem_nhds hps,
        (fun _ => 0), (Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, E))).contMDiffOn, ?_⟩
      intro x hx
      change mvfderiv 𝓘(ℝ, E) f x 0 = χ x
      rw [map_zero, image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨V, hV⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    (n := ⊤) 𝓘(ℝ, E) (TangentSpace 𝓘(ℝ, E) (M := M)) C hC hlocal
  exact ⟨V, V.contMDiff, hV⟩

end Wikipedia.SmoothSixDPoincare.FlowConstruction
