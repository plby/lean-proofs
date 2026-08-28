import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Separation.Hausdorff

/-!
# An explicit relative embedding after adding coordinates

The map `x ↦ (f x, β x, β x • x)` is injective and immersive wherever `β` is
nonzero. On its zero set it suffices for the original map to have these
properties. This retains the original map exactly on every region where the
weight vanishes, and avoids the old ambient space wherever the weight is nonzero.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff

namespace NoExoticSixSphere.SupportedGraph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Adding a weighted copy of the source, together with its weight. -/
def map (f : E → F) (β : E → ℝ) (x : E) : F × (ℝ × E) :=
  (f x, β x, β x • x)

theorem map_eq_of_zero (f : E → F) (β : E → ℝ) {x : E} (hx : β x = 0) :
    map f β x = (f x, 0) := by
  simp [map, hx]

theorem map_ne_oldAmbient (f : E → F) (β : E → ℝ) {x : E} (hx : β x ≠ 0)
    (y : F) : map f β x ≠ (y, 0) := by
  intro h
  exact hx (congrArg (fun z : F × (ℝ × E) ↦ z.2.1) h)

/-- The only possible collisions lie entirely in the original zero-weight locus. -/
theorem injOn_map (f : E → F) (β : E → ℝ) {K : Set E}
    (hf : InjOn f (K ∩ {x | β x = 0})) : InjOn (map f β) K := by
  intro x hx y hy h
  have hβ : β x = β y := congrArg (fun z : F × (ℝ × E) ↦ z.2.1) h
  by_cases hz : β x = 0
  · exact hf ⟨hx, hz⟩ ⟨hy, hβ.symm.trans hz⟩ (congrArg Prod.fst h)
  · have hv : β x • x = β y • y := congrArg (fun z : F × (ℝ × E) ↦ z.2.2) h
    rw [← hβ] at hv
    exact smul_right_injective E hz hv

variable [NormedAddCommGroup F]

theorem continuousOn_map (f : E → F) (β : E → ℝ) {K : Set E}
    (hf : ContinuousOn f K) (hβ : ContinuousOn β K) : ContinuousOn (map f β) K :=
  hf.prodMk (hβ.prodMk (hβ.smul continuousOn_id))

variable [NormedSpace ℝ F]

theorem contDiffAt_map (f : E → F) (β : E → ℝ) {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hβ : ContDiffAt ℝ ∞ β x) :
    ContDiffAt ℝ ∞ (map f β) x :=
  hf.prodMk (hβ.prodMk (hβ.smul contDiffAt_id))

/-- The derivative keeps the scalar derivative as a separate coordinate. -/
theorem fderiv_map_apply (f : E → F) (β : E → ℝ) {x : E}
    (hf : DifferentiableAt ℝ f x) (hβ : DifferentiableAt ℝ β x) (v : E) :
    fderiv ℝ (map f β) x v =
      (fderiv ℝ f x v, fderiv ℝ β x v, β x • v + (fderiv ℝ β x v) • x) := by
  have hd := hf.hasFDerivAt.prodMk
    (hβ.hasFDerivAt.prodMk (hβ.hasFDerivAt.smul (hasFDerivAt_id x)))
  rw [show fderiv ℝ (map f β) x = _ from hd.fderiv]
  rfl

/-- No immersion hypothesis is needed away from the zero set of the weight. -/
theorem injective_fderiv_map (f : E → F) (β : E → ℝ) {x : E}
    (hf : DifferentiableAt ℝ f x) (hβ : DifferentiableAt ℝ β x)
    (hi : β x = 0 → Injective (fderiv ℝ f x)) :
    Injective (fderiv ℝ (map f β) x) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [fderiv_map_apply f β hf hβ] at hv
  by_cases hz : β x = 0
  · apply hi hz
    simpa only [map_zero, Prod.fst_zero] using congrArg Prod.fst hv
  · have hβv : fderiv ℝ β x v = 0 :=
      congrArg (fun z : F × (ℝ × E) ↦ z.2.1) hv
    have hv' : β x • v = 0 := by
      simpa only [hβv, zero_smul, add_zero, Prod.snd_zero] using
        congrArg (fun z : F × (ℝ × E) ↦ z.2.2) hv
    exact (smul_eq_zero.mp hv').resolve_left hz

omit [NormedSpace ℝ F] in
/-- On a compact region the explicitly constructed map is a closed embedding. -/
theorem isClosedEmbedding_restrict (f : E → F) (β : E → ℝ) {K : Set E}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hβ : ContinuousOn β K)
    (hi : InjOn f (K ∩ {x | β x = 0})) :
    IsClosedEmbedding (fun x : K ↦ map f β x.val) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply (continuousOn_iff_continuous_domRestrict.mp
    (continuousOn_map f β hf hβ)).isClosedEmbedding
  intro x y h
  exact Subtype.ext (injOn_map f β hi x.property y.property h)

end NoExoticSixSphere.SupportedGraph
