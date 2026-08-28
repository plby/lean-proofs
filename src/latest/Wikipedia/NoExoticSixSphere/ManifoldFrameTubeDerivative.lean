import Wikipedia.NoExoticSixSphere.SmoothManifoldHeightCylinder
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Actual manifold derivatives of linear frame displacements at the zero section -/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {E H X F K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

theorem hasMFDerivAt_clm_apply_zero {g : X → K →L[ℝ] F} {f : X → K} {x : X}
    {dg : E →L[ℝ] K →L[ℝ] F} {df : E →L[ℝ] K}
    (hg : HasMFDerivAt I 𝓘(ℝ, K →L[ℝ] F) g x dg)
    (hf : HasMFDerivAt I 𝓘(ℝ, K) f x df) (hz : f x = 0) :
    HasMFDerivAt I 𝓘(ℝ, F) (fun y ↦ g y (f y)) x ((g x).comp df) := by
  let b : (K →L[ℝ] F) × K → F := fun p ↦ p.1 p.2
  have hb : IsBoundedBilinearMap ℝ b := isBoundedBilinearMap_apply
  have hd : (hb.deriv (g x, f x)).comp (dg.prod df) = (g x).comp df := by
    apply ContinuousLinearMap.ext
    intro v
    change g x (df v) + dg v (f x) = g x (df v)
    rw [hz, map_zero, add_zero]
  have he := (hb.hasFDerivAt (g x, f x)).hasMFDerivAt.comp x
    (hasMFDerivAt_prodMk_space hg hf)
  exact (congrArg
    (fun L : E →L[ℝ] F ↦ HasMFDerivAt I 𝓘(ℝ, F) (fun y ↦ g y (f y)) x L) hd).mp he

theorem mvfderiv_frameTube_core {D : X → F} {B : X → K →L[ℝ] F} (x : X)
    (hD : MDifferentiableAt I 𝓘(ℝ, F) D x)
    (hB : MDifferentiableAt I 𝓘(ℝ, K →L[ℝ] F) B x) :
    mvfderiv (I.prod 𝓘(ℝ, K)) (fun p : X × K ↦ D p.1 + B p.1 p.2) (x, 0) =
      (mvfderiv I D x).coprod (B x) := by
  have hd := hD.hasMFDerivAt.comp (x, (0 : K))
    (hasMFDerivAt_fst (I := I) (I' := 𝓘(ℝ, K)) (x, (0 : K)))
  have hb := hB.hasMFDerivAt.comp (x, (0 : K))
    (hasMFDerivAt_fst (I := I) (I' := 𝓘(ℝ, K)) (x, (0 : K)))
  have he := hasMFDerivAt_clm_apply_zero hb
    (hasMFDerivAt_snd (I := I) (I' := 𝓘(ℝ, K)) (x, (0 : K))) rfl
  have h := (hd.add he).mfderiv
  change mvfderiv (I.prod 𝓘(ℝ, K)) (fun p : X × K ↦ D p.1 + B p.1 p.2) (x, 0) = _ at h
  rw [h]
  ext v
  rfl

end NoExoticSixSphere
