import Wikipedia.SmoothSixDPoincare.ImmersionLocalInjectivity

/-!
# An injective immersion near a compact core from pointwise smoothness

Smoothness is only assumed at points of the compact core. Local inverse
functions for a left-inverse projection of the actual map give local
injectivity. Compactness and continuity then give one open injectivity
neighborhood, which is intersected with the interior immersion locus.
No uniform smooth neighborhood is inferred from pointwise infinite smoothness.
-/

noncomputable section

open Function Set
open scoped ContDiff Topology

namespace NoExoticSixSphere.CompactCoreImmersion

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_open_injOn_at {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hi : Injective (fderiv ℝ f x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ InjOn f V := by
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hi
  have hs : ContDiffAt ℝ ∞ (L ∘ f) x := L.contDiff.contDiffAt.comp x hf
  have hd : HasFDerivAt (L ∘ f)
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) x := by
    convert L.hasFDerivAt.comp x (hf.differentiableAt (by simp)).hasFDerivAt using 1
    ext v
    exact (hL v).symm
  let Φ := hs.toOpenPartialHomeomorph (L ∘ f) hd (by simp)
  refine ⟨Φ.source, Φ.open_source, hs.mem_toOpenPartialHomeomorph_source hd (by simp), ?_⟩
  intro y hy z hz he
  exact Φ.injOn hy hz (congrArg L he)

theorem exists_open_injOn_near_compact {f : E → F} {K : Set E}
    (hK : IsCompact K) (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) (hinj : InjOn f K)
    (hi : ∀ x ∈ K, Injective (fderiv ℝ f x)) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ InjOn f V ∧
      ∀ x ∈ V, Injective (fderiv ℝ f x) := by
  have hlocal : ∀ x ∈ K, ∃ V ∈ nhds x, InjOn f V := by
    intro x hx
    obtain ⟨V, hV, hxV, hVi⟩ := exists_open_injOn_at (hf x hx) (hi x hx)
    exact ⟨V, hV.mem_nhds hxV, hVi⟩
  obtain ⟨V, hV, hKV, hVi⟩ :=
    hinj.exists_isOpen_superset hK (fun x hx ↦ (hf x hx).continuousAt) hlocal
  let W := interior {x | Injective (fderiv ℝ f x)}
  have hKW : K ⊆ W := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    exact (hf x hx).continuousAt_fderiv (by simp)
      (ContinuousLinearMap.isOpen_injective.mem_nhds (hi x hx))
  exact ⟨V ∩ W, hV.inter isOpen_interior, fun x hx ↦ ⟨hKV hx, hKW hx⟩,
    hVi.mono inter_subset_left, fun _ hx ↦ interior_subset hx.2⟩

end NoExoticSixSphere.CompactCoreImmersion
