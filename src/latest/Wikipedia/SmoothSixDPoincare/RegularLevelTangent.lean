import Wikipedia.SmoothSixDPoincare.RegularLevelSmoothMaps
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# The native tangent space of an actual regular level

The inclusion has injective differential, and its image is exactly the kernel
of the original height differential. These are properties of the constructed
slice atlas on the original subspace, not of a replacement manifold.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.RegularLevel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)

/-- The actual regular-level inclusion is an immersion. -/
theorem injective_mfderiv_inclusion (x : {x : M // f x = b}) :
    letI := chartedSpace hf hreg
    Injective (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E)
      (Subtype.val : {x : M // f x = b} → M) x) := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  let Φ := heightChart hf hreg x
  have hΦ := Φ.contMDiffOn_toFun.contMDiffAt
    (Φ.open_source.mem_nhds (heightChart_mem_source hf hreg x))
  have hprojection : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Model E) ∞
      (fun y : M => (Φ y).2) (x : M) :=
    contDiff_snd.contMDiff.contMDiffAt.comp (x : M) hΦ
  have hi := (mdifferentiable_chart (I := 𝓘(ℝ, Model E)) x).mfderiv_injective
    (mem_chart_source (Model E) x)
  change Injective (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, Model E)
    ((fun y : M => (Φ y).2) ∘ Subtype.val) x) at hi
  rw [mfderiv_comp x (hprojection.mdifferentiableAt (by simp))
    ((contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))] at hi
  exact fun u v huv => hi (congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Model E)
    (fun y : M => (Φ y).2) (x : M)) huv)

/-- Height has zero derivative on every native tangent vector to its level. -/
theorem height_derivative_comp_inclusion (x : {x : M // f x = b}) :
    letI := chartedSpace hf hreg
    (mvfderiv 𝓘(ℝ, E) f (x : M)).comp
      (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E)
        (Subtype.val : {x : M // f x = b} → M) x) = 0 := by
  let _ := chartedSpace hf hreg
  have heq : f ∘ (Subtype.val : {x : M // f x = b} → M) = fun _ => b :=
    funext (fun y => y.property)
  have hc := mfderiv_comp x (hf.mdifferentiableAt (by simp))
    ((contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))
  rw [heq, mfderiv_const] at hc
  exact hc.symm

/-- The native tangent image of the original level is the entire kernel of the height map. -/
theorem range_mfderiv_inclusion (x : {x : M // f x = b}) :
    letI := chartedSpace hf hreg
    (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E)
      (Subtype.val : {x : M // f x = b} → M) x).range =
        (mvfderiv 𝓘(ℝ, E) f (x : M)).ker := by
  let _ := chartedSpace hf hreg
  let A : Model E →L[ℝ] E := mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E)
    (Subtype.val : {x : M // f x = b} → M) x
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (x : M)
  change A.range = L.ker
  have hsub : A.range ≤ L.ker := by
    rintro _ ⟨v, rfl⟩
    change L (A v) = 0
    exact congrArg (fun T => T v) (height_derivative_comp_inclusion hf hreg x)
  have hAi : Injective A := injective_mfderiv_inclusion hf hreg x
  have hL : L ≠ 0 := hreg x x.property
  have hdim := finrank_kernel_add_one hL
  have hAr : Module.finrank ℝ A.range = Module.finrank ℝ E - 1 := by
    rw [LinearMap.finrank_range_of_inj hAi]
    exact finrank_euclideanSpace_fin
  apply Submodule.eq_of_le_of_finrank_eq hsub
  rw [hAr]
  omega

/-- The level tangent directions together with one transverse height direction. -/
def transverseTangentMap (x : {x : M // f x = b}) (v : E) : Model E × ℝ →L[ℝ] E :=
  letI := chartedSpace hf hreg
  (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E)
    (Subtype.val : {x : M // f x = b} → M) x).coprod
      ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

/-- A vector of unit height derivative completes the actual level tangent space. -/
theorem bijective_transverseTangentMap (x : {x : M // f x = b}) (v : E)
    (hv : mvfderiv 𝓘(ℝ, E) f (x : M) v = 1) :
    Bijective (transverseTangentMap hf hreg x v) := by
  let _ := chartedSpace hf hreg
  let A : Model E →L[ℝ] E := mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E)
    (Subtype.val : {x : M // f x = b} → M) x
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (x : M)
  have hLA (u : Model E) : L (A u) = 0 :=
    congrArg (fun T => T u) (height_derivative_comp_inclusion hf hreg x)
  have hAi : Injective A := injective_mfderiv_inclusion hf hreg x
  change L v = 1 at hv
  constructor
  · intro z w hzw
    change A z.1 + z.2 • v = A w.1 + w.2 • v at hzw
    have ht : z.2 = w.2 := by
      have h := congrArg L hzw
      simpa only [map_add, map_smul, hLA, hv, smul_eq_mul, mul_one, zero_add] using h
    rw [ht] at hzw
    exact Prod.ext (hAi (add_right_cancel hzw)) ht
  · intro w
    have hrem : w - L w • v ∈ L.ker := by
      change L (w - L w • v) = 0
      simp only [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
    have hrange : A.range = L.ker := range_mfderiv_inclusion hf hreg x
    rw [← hrange] at hrem
    obtain ⟨u, hu⟩ := hrem
    change A u = w - L w • v at hu
    refine ⟨(u, L w), ?_⟩
    change A u + L w • v = w
    rw [hu, sub_add_cancel]

variable {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- A right inverse for the ambient normal derivative, lying in the actual height kernel,
proves surjectivity after restriction to the original regular level. -/
theorem surjective_normal_derivative_of_tangent_lift {n : M → N}
    (x : {x : M // f x = b}) (hn : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) n (x : M))
    (R : N →L[ℝ] E)
    (hheight : (mvfderiv 𝓘(ℝ, E) f (x : M)).comp R = 0)
    (hnormal : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (x : M) : E →L[ℝ] N).comp R =
      ContinuousLinearMap.id ℝ N) :
    letI := chartedSpace hf hreg
    Surjective (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, N)
      (n ∘ (Subtype.val : {x : M // f x = b} → M)) x) := by
  let _ := chartedSpace hf hreg
  let A : Model E →L[ℝ] E := mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E)
    (Subtype.val : {x : M // f x = b} → M) x
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (x : M)
  let B : E →L[ℝ] N := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (x : M)
  change L.comp R = 0 at hheight
  change B.comp R = ContinuousLinearMap.id ℝ N at hnormal
  have hrange : A.range = L.ker := range_mfderiv_inclusion hf hreg x
  rw [mfderiv_comp x hn ((contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))]
  change Surjective (B.comp A)
  intro z
  have hker : R z ∈ L.ker := by
    change L (R z) = 0
    exact congrArg (fun T : N →L[ℝ] ℝ => T z) hheight
  rw [← hrange] at hker
  obtain ⟨v, hv⟩ := hker
  change A v = R z at hv
  refine ⟨v, ?_⟩
  change B (A v) = z
  rw [hv]
  exact congrArg (fun T : N →L[ℝ] N => T z) hnormal

end Wikipedia.SmoothSixDPoincare.RegularLevel
