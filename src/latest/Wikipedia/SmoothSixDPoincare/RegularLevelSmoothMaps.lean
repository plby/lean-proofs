import Wikipedia.SmoothSixDPoincare.RegularLevelManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Smooth maps to and from the actual regular level

The inclusion is smooth for the constructed slice atlas. Conversely, a map
landing in the level is smooth whenever its composition with the inclusion is
smooth; its level-chart expression is the second ambient height coordinate.
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

/-- The inclusion of the actual level, with its constructed smooth atlas, is smooth. -/
theorem contMDiff_inclusion :
    letI := chartedSpace hf hreg
    ContMDiff 𝓘(ℝ, Model E) 𝓘(ℝ, E) ∞ (Subtype.val : {x : M // f x = b} → M) := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  intro x
  let Φ := heightChart hf hreg x
  let c := levelChart hf hreg x
  have hx : x ∈ c.source := heightChart_mem_source hf hreg x
  have hc : ContMDiffAt 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ∞ c x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hx
  have ht : (b, c x) ∈ Φ.target := c.map_source hx
  have hslice : ContMDiffAt 𝓘(ℝ, Model E) 𝓘(ℝ, E) ∞
      (fun v => Φ.symm (b, v)) (c x) :=
    (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds ht)).comp (c x)
      (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt
  have hcomp := hslice.comp x hc
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hx] with y hy
  change (y : M) = Φ.symm (b, c y)
  have heq : (b, c y) = Φ y :=
    Prod.ext ((heightChart_height hf hreg x y hy).trans y.property).symm rfl
  rw [heq]
  exact (Φ.left_inv' hy).symm

variable {G H X : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
  [TopologicalSpace X] [ChartedSpace H X]

/-- Pointwise smoothness into the level is detected by the original ambient inclusion. -/
theorem contMDiffAt_iff_inclusion (g : X → {x : M // f x = b}) (x : X) :
    letI := chartedSpace hf hreg
    ContMDiffAt I 𝓘(ℝ, Model E) ∞ g x ↔
      ContMDiffAt I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) x := by
  let _ := chartedSpace hf hreg
  constructor
  · intro hg
    exact (contMDiff_inclusion hf hreg).contMDiffAt.comp x hg
  · intro hg
    apply contMDiffAt_iff_target.mpr
    refine ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hg.continuousAt, ?_⟩
    let Φ := heightChart hf hreg (g x)
    have hΦ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Model E) ∞ Φ (g x) :=
      Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (heightChart_mem_source hf hreg (g x)))
    have hcomp := hΦ.comp x hg
    change ContMDiffAt I 𝓘(ℝ, Model E) ∞ (fun y => (Φ (g y)).2) x
    exact contDiff_snd.contMDiff.contMDiffAt.comp x hcomp

/-- Global smooth lifting to the actual regular level, without any extension hypothesis. -/
theorem contMDiff_iff_inclusion (g : X → {x : M // f x = b}) :
    letI := chartedSpace hf hreg
    ContMDiff I 𝓘(ℝ, Model E) ∞ g ↔ ContMDiff I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) := by
  let _ := chartedSpace hf hreg
  exact forall_congr' (contMDiffAt_iff_inclusion hf hreg I g)

/-- An injective ambient differential gives an injective differential into the actual level. -/
theorem injective_mfderiv_of_inclusion (g : X → {x : M // f x = b}) (x : X)
    (hg : ContMDiffAt I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) x)
    (hi : Injective (mfderiv I 𝓘(ℝ, E) (Subtype.val ∘ g) x)) :
    letI := chartedSpace hf hreg
    Injective (mfderiv I 𝓘(ℝ, Model E) g x) := by
  let _ := chartedSpace hf hreg
  have hgl := (contMDiffAt_iff_inclusion hf hreg I g x).mpr hg
  have hv := (contMDiff_inclusion hf hreg).contMDiffAt (x := g x)
  rw [mfderiv_comp x (hv.mdifferentiableAt (by simp))
    (hgl.mdifferentiableAt (by simp))] at hi
  exact fun v w hvw => hi (congrArg (mfderiv 𝓘(ℝ, Model E) 𝓘(ℝ, E)
    (Subtype.val : {x : M // f x = b} → M) (g x)) hvw)

end Wikipedia.SmoothSixDPoincare.RegularLevel
