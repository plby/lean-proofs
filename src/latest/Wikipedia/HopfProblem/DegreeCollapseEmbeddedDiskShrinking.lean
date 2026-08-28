import Wikipedia.HopfProblem.DegreeCollapseChartDiskShrinking

/-!
# Shrinking an original embedded disk by supported ambient diffeomorphisms

The native tubular neighborhood and its supporting ellipsoid are constructed
from the original disk. The resulting isotopy can compress that entire disk
into any prescribed open neighborhood of its center, while staying supported
in any prescribed open neighborhood of the original disk.
-/

noncomputable section

open Set Metric Function
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking

variable {D E M : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_embedded_disk_shrinking {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hinj : InjOn f (closedBall (0 : D) 1))
    (hi : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hfO : MapsTo f (closedBall (0 : D) 1) O)
    {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ O ∧ ∃ P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      Nonempty (SupportedRelativeIsotopy P K {f 0}) ∧
      ∀ x ∈ closedBall (0 : D) 1, P (f x) = f (a • x) := by
  obtain ⟨ε, hε, Φ, hprod, hzero, htarget⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_closedBall hf hinj hi n hdim hO hfO
  have hsource : closedBall (0 : D) 1 ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Φ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    rcases mem_singleton_iff.mp hz with rfl
    exact hprod ⟨hx, mem_closedBall_self hε.le⟩
  obtain ⟨K, hK, hKt, P, hP, hformula⟩ := exists_chart_disk_shrinking Φ hsource ha ha₁
  have h0 : Φ (0, 0) = f 0 := hzero 0 (mem_closedBall_self zero_le_one)
  refine ⟨K, hK, hKt.trans htarget, P, h0 ▸ hP, ?_⟩
  intro x hx
  have hax : a • x ∈ closedBall (0 : D) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact (mul_le_of_le_one_right ha.le (mem_closedBall_zero_iff.mp hx)).trans ha₁
  rw [← hzero x hx, hformula x (mem_closedBall_zero_iff.mp hx), hzero (a • x) hax]

theorem exists_embedded_disk_shrinking_into_open {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hinj : InjOn f (closedBall (0 : D) 1))
    (hi : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    {O U : Set M} (hO : IsOpen O) (hfO : MapsTo f (closedBall (0 : D) 1) O)
    (hU : IsOpen U) (h0U : f 0 ∈ U) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∃ K : Set M, IsCompact K ∧ K ⊆ O ∧
      ∃ P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
        Nonempty (SupportedRelativeIsotopy P K {f 0}) ∧
        (∀ x ∈ closedBall (0 : D) 1, P (f x) = f (a • x)) ∧
        MapsTo (P ∘ f) (closedBall (0 : D) 1) U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hU.preimage hf.continuous).mem_nhds h0U)
  let a : ℝ := min 1 ε
  have ha : 0 < a := lt_min zero_lt_one hε
  have ha₁ : a ≤ 1 := min_le_left _ _
  obtain ⟨K, hK, hKO, P, hP, hformula⟩ :=
    exists_embedded_disk_shrinking hf hinj hi n hdim hO hfO ha ha₁
  refine ⟨a, ha, ha₁, K, hK, hKO, P, hP, hformula, ?_⟩
  intro x hx
  change P (f x) ∈ U
  rw [hformula x hx]
  apply hεU
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  exact (mul_le_of_le_one_right ha.le (mem_closedBall_zero_iff.mp hx)).trans (min_le_right _ _)

end Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking
