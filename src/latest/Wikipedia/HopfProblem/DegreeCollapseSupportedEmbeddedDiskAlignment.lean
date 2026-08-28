import Wikipedia.HopfProblem.DegreeCollapseSupportedDiskChartAlignment
import Wikipedia.HopfProblem.DegreeCollapseEmbeddedDiskAlignment

/-!
# Embedded disk alignment supported in a prescribed open set

Both full tubular charts are constructed inside the supplied open set.
The resulting isotopy identifies the whole closed disks pointwise, has
one compact support in that open set, and fixes their common center.
-/

noncomputable section

open Set Function Metric
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking

variable {D E M : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_supported_embedded_disk_alignment {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : InjOn f (closedBall (0 : D) 1)) (hgi : InjOn g (closedBall (0 : D) 1))
    (hfd : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) (hcenter : f 0 = g 0)
    {U : Set M} (hU : IsOpen U)
    (hfU : MapsTo f (closedBall (0 : D) 1) U)
    (hgU : MapsTo g (closedBall (0 : D) 1) U) :
    ∃ (P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (K : Set M),
      IsCompact K ∧ K ⊆ U ∧ Nonempty (SupportedRelativeIsotopy P K {g 0}) ∧
      ∀ x ∈ closedBall (0 : D) 1, P (f x) = g x := by
  classical
  let B := EuclideanSpace ℝ (Fin n)
  obtain ⟨ε, hε, Φ, hΦprod, hΦzero, hΦU⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_closedBall hf hfi hfd n hdim hU hfU
  obtain ⟨δ, hδ, Ψ, hΨprod, hΨzero, hΨU⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_closedBall hg hgi hgd n hdim hU hgU
  have hΦ : closedBall (0 : D) 1 ×ˢ {(0 : B)} ⊆ Φ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    rcases mem_singleton_iff.mp hz with rfl
    exact hΦprod ⟨hx, mem_closedBall_self hε.le⟩
  have hΨ : closedBall (0 : D) 1 ×ˢ {(0 : B)} ⊆ Ψ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    rcases mem_singleton_iff.mp hz with rfl
    exact hΨprod ⟨hx, mem_closedBall_self hδ.le⟩
  have hcenter' : Φ 0 = Ψ 0 := by
    change Φ (0, 0) = Ψ (0, 0)
    rw [hΦzero 0 (mem_closedBall_self zero_le_one),
      hΨzero 0 (mem_closedBall_self zero_le_one), hcenter]
  have hB : 0 < Module.finrank ℝ B := by simpa only [B, finrank_euclideanSpace_fin] using hn
  have hDB : 2 ≤ Module.finrank ℝ (D × B) := by
    simpa only [Module.finrank_prod, B, finrank_euclideanSpace_fin, hdim] using hE
  let _ : Nontrivial (Fin (Module.finrank ℝ (D × B))) := Fin.nontrivial_iff_two_le.mpr hDB
  obtain ⟨P, K, hK, hKt, hIso, hformula⟩ := SupportedGerms.exists_supported_disk_chart_alignment
    (Module.finBasis ℝ B) ⟨0, hB⟩ (Module.finBasis ℝ (D × B)) Φ Ψ hΦ hΨ hcenter'
  refine ⟨P, K, hK, hKt.trans (union_subset hΦU hΨU), ?_, ?_⟩
  · change Nonempty (SupportedRelativeIsotopy P K {Ψ (0, 0)}) at hIso
    rwa [hΨzero 0 (mem_closedBall_self zero_le_one)] at hIso
  · intro x hx
    rw [← hΦzero x hx, hformula x hx, hΨzero x hx]

end Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking
