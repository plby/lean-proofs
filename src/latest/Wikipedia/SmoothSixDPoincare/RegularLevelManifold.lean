import Wikipedia.SmoothSixDPoincare.RegularLevelSliceChart

/-!
# The smooth manifold structure on an actual regular level

Transition maps are restrictions of the original ambient smooth chart changes
to a fixed-height slice. The topology remains the original subspace topology.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.RegularLevel

section Transition

variable {E D M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {b : ℝ}
  (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × D) M (ℝ × D) ∞)
  (hΦ : ∀ y ∈ Φ.source, (Φ y).1 = f y) (hΨ : ∀ y ∈ Ψ.source, (Ψ y).1 = f y)
  (x y : {z : M // f z = b})

theorem contDiffOn_slice_transition :
    let c := sliceChart Φ.toOpenPartialHomeomorph hΦ x
    let d := sliceChart Ψ.toOpenPartialHomeomorph hΨ y
    ContDiffOn ℝ ∞ (c.symm.trans d) (c.symm.trans d).source := by
  let c := sliceChart Φ.toOpenPartialHomeomorph hΦ x
  let d := sliceChart Ψ.toOpenPartialHomeomorph hΨ y
  let S := (c.symm.trans d).source
  have hS (v : D) (hv : v ∈ S) :
      (b, v) ∈ Φ.target ∧ Φ.symm (b, v) ∈ Ψ.source := by
    refine ⟨hv.1, ?_⟩
    have hh : (c.symm v : M) ∈ Ψ.source := hv.2
    rwa [sliceChart_symm_coe Φ.toOpenPartialHomeomorph hΦ x hv.1] at hh
  have hfirst : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (fun v => Φ.symm (b, v)) S :=
    Φ.contMDiffOn_invFun.comp
      ((contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn) (fun v hv => (hS v hv).1)
  have hsecond := Ψ.contMDiffOn_toFun.comp hfirst (fun v hv => (hS v hv).2)
  have hfull : ContDiffOn ℝ ∞ (fun v => (Ψ (Φ.symm (b, v))).2) S :=
    (contDiff_snd.contMDiff.comp_contMDiffOn hsecond).contDiffOn
  apply hfull.congr
  intro v hv
  change (Ψ (c.symm v : M)).2 = (Ψ (Φ.symm (b, v))).2
  rw [sliceChart_symm_coe Φ.toOpenPartialHomeomorph hΦ x hv.1]
  rfl

end Transition

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)

def heightChart (x : {x : M // f x = b}) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Model E) M (ℝ × Model E) ∞ :=
  Classical.choose (exists_native_height_chart hf (hreg x x.property))

theorem heightChart_mem_source (x : {x : M // f x = b}) :
    (x : M) ∈ (heightChart hf hreg x).source :=
  (Classical.choose_spec (exists_native_height_chart hf (hreg x x.property))).1

theorem heightChart_height (x : {x : M // f x = b}) :
    ∀ y ∈ (heightChart hf hreg x).source, (heightChart hf hreg x y).1 = f y :=
  (Classical.choose_spec (exists_native_height_chart hf (hreg x x.property))).2.1

def levelChart (x : {x : M // f x = b}) :
    OpenPartialHomeomorph {x : M // f x = b} (Model E) :=
  sliceChart (heightChart hf hreg x).toOpenPartialHomeomorph (heightChart_height hf hreg x) x

/-- The charts cover the regular level in its existing subspace topology. -/
@[instance_reducible]
def chartedSpace : ChartedSpace (Model E) {x : M // f x = b} where
  atlas := range (levelChart hf hreg)
  chartAt := levelChart hf hreg
  mem_chart_source := heightChart_mem_source hf hreg
  chart_mem_atlas := fun x => ⟨x, rfl⟩

/-- Compatibility is proved by restricting the ambient smooth transition maps. -/
theorem isManifold :
    letI := chartedSpace hf hreg
    IsManifold 𝓘(ℝ, Model E) ∞ {x : M // f x = b} := by
  let _ := chartedSpace hf hreg
  apply isManifold_of_contDiffOn
  intro c d hc hd
  obtain ⟨x, rfl⟩ := hc
  obtain ⟨y, rfl⟩ := hd
  simpa only [mfld_simps, levelChart] using contDiffOn_slice_transition
    (heightChart hf hreg x) (heightChart hf hreg y)
    (heightChart_height hf hreg x) (heightChart_height hf hreg y) x y

end Wikipedia.SmoothSixDPoincare.RegularLevel
