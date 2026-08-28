import Wikipedia.SmoothSixDPoincare.NativeRegularLevelCoordinates

/-! # Charts on the actual regular level subspace, with its original topology -/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.RegularLevel

section Slice

variable {M D : Type*} [TopologicalSpace M] [TopologicalSpace D]
  {f : M → ℝ} {b : ℝ} (e : OpenPartialHomeomorph M (ℝ × D))
  (he : ∀ y ∈ e.source, (e y).1 = f y)

include he in
theorem inverse_height {v : D} (hv : (b, v) ∈ e.target) :
    f (e.symm (b, v)) = b := by
  have h := he (e.symm (b, v)) (e.map_target hv)
  rw [e.right_inv hv] at h
  exact h.symm

open Classical in
def sliceInverse (base : {x : M // f x = b}) (v : D) : {x : M // f x = b} :=
  if hv : (b, v) ∈ e.target then ⟨e.symm (b, v), inverse_height e he hv⟩ else base

open Classical in
/-- Restrict a height-straightening chart to the genuine fiber, retaining its subtype topology. -/
def sliceChart (base : {x : M // f x = b}) : OpenPartialHomeomorph {x : M // f x = b} D where
  toFun x := (e x).2
  invFun := sliceInverse e he base
  source := {x | (x : M) ∈ e.source}
  target := {v | (b, v) ∈ e.target}
  map_source' := by
    intro x hx
    have hp : (b, (e x).2) = e x := Prod.ext ((he x hx).trans x.property).symm rfl
    change (b, (e x).2) ∈ e.target
    rw [hp]
    exact e.map_source hx
  map_target' := by
    intro v hv
    change (b, v) ∈ e.target at hv
    change (sliceInverse e he base v : M) ∈ e.source
    simp only [sliceInverse, dif_pos hv]
    exact e.map_target hv
  left_inv' := by
    intro x hx
    have hp : (b, (e x).2) = e x := Prod.ext ((he x hx).trans x.property).symm rfl
    have ht : (b, (e x).2) ∈ e.target := hp ▸ e.map_source hx
    simp only [sliceInverse, dif_pos ht]
    apply Subtype.ext
    change e.symm (b, (e x).2) = x
    rw [hp]
    exact e.left_inv hx
  right_inv' := by
    intro v hv
    change (b, v) ∈ e.target at hv
    simp only [sliceInverse, dif_pos hv]
    rw [e.right_inv hv]
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun := continuous_snd.comp_continuousOn
    (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx))
  continuousOn_invFun := by
    apply IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (e.symm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => hv)).congr
    intro v hv
    change (b, v) ∈ e.target at hv
    simp only [comp_apply, sliceInverse, dif_pos hv]
    rfl

open Classical in
theorem sliceChart_symm_coe (base : {x : M // f x = b}) {v : D}
    (hv : v ∈ (sliceChart e he base).target) :
    ((sliceChart e he base).symm v : M) = e.symm (b, v) := by
  change (b, v) ∈ e.target at hv
  change (sliceInverse e he base v : M) = _
  simp only [sliceInverse, dif_pos hv]

end Slice

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Every point of a regular level has a genuine chart on that level's subspace topology. -/
theorem exists_level_chart {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {b : ℝ} (x : {x : M // f x = b})
    (hx : (x : M) ∉ ManifoldMorse.criticalPoints E f) :
    ∃ c : OpenPartialHomeomorph {x : M // f x = b} (Model E), x ∈ c.source := by
  obtain ⟨Φ, hΦ, he, -⟩ := exists_native_height_chart hf hx
  exact ⟨sliceChart Φ.toOpenPartialHomeomorph he x, hΦ⟩

end Wikipedia.SmoothSixDPoincare.RegularLevel
