import Wikipedia.SmoothSixDPoincare.RegularLevelSmoothMaps

/-!
# Relative smoothness into an actual regular level

Smoothness within a parameter set is detected by the original ambient
inclusion, just as pointwise and global smoothness are. This permits the
closed attaching-face parameters to be retained during exterior transport.
-/

noncomputable section

open Set Function Manifold Topology
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.RegularLevel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
  {G H X : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
  [TopologicalSpace X] [ChartedSpace H X]

theorem contMDiffWithinAt_iff_inclusion (g : X → {x : M // f x = b}) (S : Set X) (x : X) :
    letI := chartedSpace hf hreg
    ContMDiffWithinAt I 𝓘(ℝ, Model E) ∞ g S x ↔
      ContMDiffWithinAt I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) S x := by
  let _ := chartedSpace hf hreg
  constructor
  · intro hg
    exact (contMDiff_inclusion hf hreg).contMDiffAt.comp_contMDiffWithinAt x hg
  · intro hg
    apply contMDiffWithinAt_iff_target.mpr
    refine ⟨IsInducing.subtypeVal.continuousWithinAt_iff.mpr hg.continuousWithinAt, ?_⟩
    let Φ := heightChart hf hreg (g x)
    have hΦ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Model E) ∞ Φ (g x) :=
      Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (heightChart_mem_source hf hreg (g x)))
    have hcomp := hΦ.comp_contMDiffWithinAt x hg
    change ContMDiffWithinAt I 𝓘(ℝ, Model E) ∞ (fun y => (Φ (g y)).2) S x
    exact contDiff_snd.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hcomp

theorem contMDiffOn_iff_inclusion (g : X → {x : M // f x = b}) (S : Set X) :
    letI := chartedSpace hf hreg
    ContMDiffOn I 𝓘(ℝ, Model E) ∞ g S ↔
      ContMDiffOn I 𝓘(ℝ, E) ∞ (Subtype.val ∘ g) S := by
  let _ := chartedSpace hf hreg
  exact forall_congr' (fun x => forall_congr' (fun _ =>
    contMDiffWithinAt_iff_inclusion hf hreg I g S x))

end Wikipedia.SmoothSixDPoincare.RegularLevel
