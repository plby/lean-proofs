import Wikipedia.HopfProblem.DegreeCollapseCleanArcLocalGerms
import Wikipedia.SmoothSixDPoincare.CleanEmbeddedSheetNeighborhood
import Wikipedia.SmoothSixDPoincare.CenteredParametrization

/-!
# A native normal-axis chart recognizing an entire embedded sheet

The original embedded immersive sheet determines clean coordinates in any
prescribed neighborhood of its point. A selected normal coordinate is the
longitudinal axis; the whole sheet is exactly the zero longitudinal and
remaining-normal coordinates inside the chart.
-/

noncomputable section

open Set Function Metric Manifold Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {D B : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def sheetAxisShuffle : (ℝ × (D × B)) ≃L[ℝ] (D × (ℝ × B)) where
  toLinearEquiv := {
    toFun := fun p => (p.2.1, (p.1, p.2.2))
    invFun := fun p => (p.2.1, (p.1, p.2.2))
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  continuous_toFun := continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)
  continuous_invFun := continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)

variable {E M X : Type*} [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace X] [ChartedSpace D X] [IsManifold 𝓘(ℝ, D) ∞ X]

theorem exists_clean_sheet_axis_chart {f : X → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (hemb : IsEmbedding f)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hdim : Module.finrank ℝ D + (1 + n) = Module.finrank ℝ E)
    (x : X) {U : Set M} (hU : IsOpen U) (hxU : f x ∈ U) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (D × EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, E)
        (ℝ × (D × EuclideanSpace ℝ (Fin n))) M ∞,
      (0 : ℝ × (D × EuclideanSpace ℝ (Fin n))) ∈ Φ.source ∧
      Φ 0 = f x ∧ Φ.target ⊆ U ∧
      ∀ z ∈ Φ.source, Φ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0 := by
  let c := NativeParametrization.centered (D := D) x
  have hc0 : (0 : D) ∈ c.source := NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := NativeParametrization.centered_zero x
  obtain ⟨ε, hε, Q, hprod, -, hQU, hzero, hrecognition⟩ :=
    exists_clean_embedded_sheet_neighborhood hf hemb c isCompact_singleton
      (mem_singleton (0 : D)) (starConvex_singleton (0 : D))
      (singleton_subset_iff.mpr hc0) (fun z _ => hi (c z)) (1 + n) hdim hU
      (show MapsTo (f ∘ c) {0} U by
        intro z hz
        rcases mem_singleton_iff.mp hz with rfl
        change f (c 0) ∈ U
        rw [hcx]
        exact hxU)
  let B := EuclideanSpace ℝ (Fin n)
  let N := EuclideanSpace ℝ (Fin (1 + n))
  let L : (ℝ × B) ≃L[ℝ] N := ContinuousLinearEquiv.ofFinrankEq (by
    simp only [B, N, Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin])
  let P : (ℝ × (D × B)) ≃L[ℝ] (D × N) :=
    (sheetAxisShuffle (D := D) (B := B)).trans ((ContinuousLinearEquiv.refl ℝ D).prodCongr L)
  let Φ := P.toDiffeomorph.toPartialDiffeomorph.trans Q
  have hQ0 : (0 : D × N) ∈ Q.source :=
    hprod ⟨mem_singleton 0, mem_closedBall_self hε.le⟩
  have hΦ0 : (0 : ℝ × (D × B)) ∈ Φ.source := by
    refine ⟨mem_univ _, ?_⟩
    change P 0 ∈ Q.source
    rw [map_zero]
    exact hQ0
  refine ⟨Φ, hΦ0, ?_, fun z hz => hQU hz.1, ?_⟩
  · change Q (P 0) = f x
    rw [map_zero]
    exact (hzero 0 hQ0).trans (congrArg f hcx)
  · intro z hz
    change Q (P z) ∈ range f ↔ _
    rw [hrecognition (P z) hz.2]
    change L (z.1, z.2.2) = 0 ↔ z.1 = 0 ∧ z.2.2 = 0
    constructor
    · intro h
      have he : (z.1, z.2.2) = (0, (0 : B)) := L.injective (h.trans L.map_zero.symm)
      exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
      exact L.map_zero

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
