import Wikipedia.SmoothSixDPoincare.ManifoldMorse
import Wikipedia.SmoothSixDPoincare.MorseCriticalPoints
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Native critical points of a manifold Morse function

Critical points are defined by the native manifold derivative. The chart
chain rule identifies them with zeros of the coordinate derivative; the
inverse function theorem then isolates each nondegenerate critical point.
-/

noncomputable section

open Set Topology Filter
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]

/-- The critical set uses the native derivative on the original manifold. -/
def criticalPoints (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E M] (f : M → ℝ) : Set M :=
  {x | mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0}

omit [FiniteDimensional ℝ E] in
/-- Vanishing of the manifold derivative is equivalent to vanishing in any smooth chart. -/
theorem mem_criticalPoints_iff {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {x : M} (hx : x ∈ e.source) :
    x ∈ criticalPoints E f ↔ fderiv ℝ (f ∘ e.symm) (e x) = 0 := by
  have he' : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  have hcomp : fderiv ℝ (f ∘ e.symm) (e x) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp (e x)
      (hf.mdifferentiableAt (by simp)) (he'.mdifferentiableAt_symm (e.map_source hx))]
    rw [e.left_inv hx]
  rw [hcomp]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0 ↔ _
  constructor
  · intro h
    rw [h]
    ext v
    rfl
  · intro h
    ext v
    obtain ⟨w, hw⟩ := he'.symm.mfderiv_surjective (e.map_source hx) v
    have hh := congrArg (fun A : E →L[ℝ] ℝ => A w) h
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)) w) = 0 at hh
    rw [hw] at hh
    exact hh

variable [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- The native critical set is closed, as can be checked in each smooth chart. -/
theorem criticalPoints_isClosed {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) : IsClosed (criticalPoints E f) := by
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_mem_nhds]
  intro x hx
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hxS : x ∈ e.source := mem_chart_source E x
  have hd := (contDiffOn_chartExpression hf he).fderiv_of_isOpen e.open_target
    (m := ∞) (by simp)
  let V : Set E := e.target ∩ (fderiv ℝ (f ∘ e.symm)) ⁻¹' {0}ᶜ
  have hV : IsOpen V := hd.continuousOn.isOpen_inter_preimage e.open_target
    (isClosed_singleton (x := (0 : E →L[ℝ] ℝ))).isOpen_compl
  have hU := e.continuousOn.isOpen_inter_preimage e.open_source hV
  have hxU : x ∈ e.source ∩ e ⁻¹' V :=
    ⟨hxS, e.map_source hxS, fun h => hx ((mem_criticalPoints_iff hf he hxS).mpr h)⟩
  apply mem_of_superset (hU.mem_nhds hxU)
  intro y hy hc
  exact hy.2.2 ((mem_criticalPoints_iff hf he hy.1).mp hc)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Each native critical point of a smooth Morse function is isolated. -/
theorem criticalPoints_isDiscrete {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) :
    IsDiscrete (criticalPoints E f) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨e, he, hxS, hreg | hH⟩ := hm x
  · exact False.elim (hreg ((mem_criticalPoints_iff hf he hxS).mp hx))
  · have hc : fderiv ℝ (f ∘ e.symm) (e x) = 0 :=
      (mem_criticalPoints_iff hf he hxS).mp hx
    have hloc := (contDiffOn_chartExpression hf he).contDiffAt
      (e.open_target.mem_nhds (e.map_source hxS))
    have hdf := hloc.fderiv_right (m := ∞) (by simp)
    let L := MorsePerturbation.hessianEquiv (f ∘ e.symm) (e x) hH
    have hL : HasFDerivAt (fderiv ℝ (f ∘ e.symm)) L.toContinuousLinearMap (e x) := by
      rw [show L.toContinuousLinearMap = fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e x) from
        MorsePerturbation.hessianEquiv_toContinuousLinearMap _ _ hH]
      exact (hdf.differentiableAt (by simp)).hasFDerivAt
    let d := hdf.toOpenPartialHomeomorph (fderiv ℝ (f ∘ e.symm)) hL (by simp)
    have hd : e x ∈ d.source := hdf.mem_toOpenPartialHomeomorph_source hL (by simp)
    let U := e.source ∩ e ⁻¹' d.source
    have hU : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source d.open_source
    refine ⟨U, hU, ?_⟩
    ext y
    constructor
    · rintro ⟨hy, hyc⟩
      apply mem_singleton_iff.mpr
      apply e.injOn hy.1 hxS
      apply d.injOn hy.2 hd
      exact ((mem_criticalPoints_iff hf he hy.1).mp hyc).trans hc.symm
    · intro hy
      rcases mem_singleton_iff.mp hy with rfl
      exact ⟨⟨hxS, hd⟩, hx⟩

/-- On a compact manifold a smooth Morse function has finitely many native critical points. -/
theorem finite_criticalPoints [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) :
    (criticalPoints E f).Finite :=
  (criticalPoints_isClosed hf).isCompact.finite (criticalPoints_isDiscrete hf hm)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
