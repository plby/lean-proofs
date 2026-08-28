import Wikipedia.HopfProblem.DegreeCollapseRelativeSurgeryFlowRealization

/-!
# Transport an entire disjoint sheet family through the actual common flow

When every point of a sheet family reaches a second regular level, one
native partial diffeomorphism transports the whole family. Compactness,
injectivity, native immersion, and all pairwise disjointness are retained.
The exact original flow-orbit formula is recorded for every parameter.
-/

noncomputable section

open Set Function Filter Manifold Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {ι E M F H X : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X]

theorem AdaptedSurgeryWindows.exists_native_family_level_transport
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (za : {x : M // f x = a}) (zb : {x : M // f x = b})
    (α : ι → X → {x : M // f x = a}) :
    let _ := RegularLevel.chartedSpace hf ha
    let _ := RegularLevel.chartedSpace hf hb
    (∀ j, ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) →
    (∀ j, Injective (α j)) →
    (∀ j x, Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (α j) x)) →
    Pairwise (fun i j => Disjoint (range (α i)) (range (α j))) →
    (∀ j x, (α j x).val ∈ FlowCancellation.levelBasin S.flow f b) →
    ∃ β : ι → X → {x : M // f x = b},
      (∀ j, ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (β j)) ∧
      (∀ j, IsClosedEmbedding (β j)) ∧
      (∀ j x, Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (β j) x)) ∧
      Pairwise (fun i j => Disjoint (range (β i)) (range (β j))) ∧
      ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  let _ := RegularLevel.isManifold hf ha
  let _ := RegularLevel.isManifold hf hb
  dsimp only
  intro hα hαinj hαimm hpair hreach
  obtain ⟨P, hsource, -, horbit⟩ := S.exists_native_level_basin_transport hf ha hb za zb
  have hsrc (j : ι) (x : X) : α j x ∈ P.source := by
    rw [hsource]
    exact hreach j x
  let β : ι → X → {x : M // f x = b} := fun j => P ∘ α j
  have hβ (j : ι) : ContMDiff I 𝓘(ℝ, RegularLevel.Model E) ∞ (β j) := by
    intro x
    exact (P.contMDiffOn_toFun.contMDiffAt (P.open_source.mem_nhds (hsrc j x))).comp
      x (hα j).contMDiffAt
  have hinj (j : ι) : Injective (β j) := by
    intro x y hxy
    exact hαinj j (P.toPartialEquiv.injOn (hsrc j x) (hsrc j y) hxy)
  refine ⟨β, hβ, fun j => (hβ j).continuous.isClosedEmbedding (hinj j), ?_, ?_,
    fun j x => horbit (α j x) (hsrc j x)⟩
  · intro j x
    have hP := P.contMDiffOn_toFun.contMDiffAt (P.open_source.mem_nhds (hsrc j x))
    change Injective (mfderiv I 𝓘(ℝ, RegularLevel.Model E) (P ∘ α j) x)
    rw [mfderiv_comp x (hP.mdifferentiableAt (by simp)) ((hα j).mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv P (hsrc j x)).injective.comp (hαimm j x)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hiz hjz
    obtain ⟨x, hx⟩ := hiz
    obtain ⟨y, hy⟩ := hjz
    have heq : α i x = α j y :=
      P.toPartialEquiv.injOn (hsrc i x) (hsrc j y) (hx.trans hy.symm)
    exact Set.disjoint_left.mp (hpair hij) (mem_range_self x) ⟨y, heq.symm⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
