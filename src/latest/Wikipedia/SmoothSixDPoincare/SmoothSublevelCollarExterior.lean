import Wikipedia.SmoothSixDPoincare.SmoothFlowCollarBoundary
import Wikipedia.SmoothSixDPoincare.AttachmentExteriorFrontier
import Wikipedia.SmoothSixDPoincare.RegularLevelSmoothMaps

/-!
# Smooth native exterior maps of an actual sublevel flow collar

The lower map is the inverse collar homeomorphism restricted to the lower
level away from the closed handle. The upper map is the original collar
homeomorphism restricted to upper points landing outside that handle.
Their smoothness is proved in the original regular-level atlases.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData

variable {M : Type} [TopologicalSpace M] [T2Space M]
  {f : M → ℝ} {a b : ℝ} {K : Set M} {F : Flow ℝ M}
  [CompactSpace ↥({x : M | f x ≤ b})]
  (d : FlowCollarData F ({x | f x ≤ a} ∪ K) {x | f x ≤ b})

def lowerExteriorMap (x : {x : M // f x = a}) : M :=
  (d.homeomorph.symm ⟨x.val, Or.inl x.property.le⟩).val

def upperExteriorMap (x : {x : M // f x = b}) : M :=
  (d.homeomorph ⟨x.val, x.property.le⟩).val

theorem lowerExteriorMap_level (hK : IsClosed K)
    (ha : frontier {x | f x ≤ a} = {x | f x = a})
    (hb : frontier {x | f x ≤ b} = {x | f x = b})
    (x : {x : M // f x = a}) (hx : x.val ∉ K) : f (d.lowerExteriorMap x) = b := by
  let y : ↥({x | f x ≤ a} ∪ K) := ⟨x.val, Or.inl x.property.le⟩
  have hy : y.val ∈ frontier ({x | f x ≤ a} ∪ K) := by
    apply (mem_frontier_union_iff_of_not_mem_closed hK hx).mpr
    rw [ha]
    exact x.property
  have hfront := (d.homeomorph_mem_frontier_iff (d.homeomorph.symm y)).mp
    (by rwa [d.homeomorph.apply_symm_apply])
  rw [hb] at hfront
  exact hfront

theorem upperExteriorMap_level (hf : Continuous f) (hK : IsClosed K)
    (hb : frontier {x | f x ≤ b} = {x | f x = b})
    (x : {x : M // f x = b}) (hx : d.upperExteriorMap x ∉ K) :
    f (d.upperExteriorMap x) = a := by
  have hxfront : x.val ∈ frontier {y | f y ≤ b} := by rw [hb]; exact x.property
  have hfront := (d.homeomorph_mem_frontier_iff ⟨x.val, x.property.le⟩).mpr hxfront
  exact height_of_attachment_frontier hf hK hfront hx

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
    (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
  (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) v)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

include hv hcurve

theorem contMDiffOn_lowerExteriorMap (hK : IsClosed K)
    (hrega : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f)
    (ha : frontier {x | f x ≤ a} = {x | f x = a})
    (hb : frontier {x | f x ≤ b} = {x | f x = b})
    (htrans : ∀ x, f x = b → mvfderiv 𝓘(ℝ, E) f x (v x) ≠ 0) :
    letI := RegularLevel.chartedSpace hf hrega
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞ d.lowerExteriorMap
      {x | x.val ∉ K} := by
  let _ := RegularLevel.chartedSpace hf hrega
  let _ := RegularLevel.isManifold hf hrega
  let i : {x : M // f x = a} → ↥({x | f x ≤ a} ∪ K) :=
    fun x => ⟨x.val, Or.inl x.property.le⟩
  apply contMDiffOn_inverseBoundary hv hcurve hf d
    (i := i) (b := b) (RegularLevel.contMDiff_inclusion hf hrega)
  · intro x hx
    apply (mem_frontier_union_iff_of_not_mem_closed hK hx).mpr
    rw [ha]
    exact x.property
  · exact fun x hx => d.lowerExteriorMap_level hK ha hb x hx
  · exact fun x hx => htrans _ (d.lowerExteriorMap_level hK ha hb x hx)

theorem contMDiffOn_upperExteriorMap (hK : IsClosed K)
    (hregb : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)
    (hb : frontier {x | f x ≤ b} = {x | f x = b})
    (htrans : ∀ x, f x = a → mvfderiv 𝓘(ℝ, E) f x (v x) ≠ 0) :
    letI := RegularLevel.chartedSpace hf hregb
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞ d.upperExteriorMap
      {x | d.upperExteriorMap x ∉ K} := by
  let _ := RegularLevel.chartedSpace hf hregb
  let _ := RegularLevel.isManifold hf hregb
  let i : {x : M // f x = b} → {x : M // f x ≤ b} := fun x => ⟨x.val, x.property.le⟩
  apply contMDiffOn_forwardBoundary hv hcurve hf d
    (i := i) (b := a) (RegularLevel.contMDiff_inclusion hf hregb)
  · intro x _
    rw [hb]
    exact x.property
  · exact fun x hx => d.upperExteriorMap_level hf.continuous hK hb x hx
  · exact fun x hx => htrans _ (d.upperExteriorMap_level hf.continuous hK hb x hx)

end Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData
