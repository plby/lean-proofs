import Wikipedia.HopfProblem.DegreeCollapseNativeDiskGermAlignment
import Wikipedia.HopfProblem.DegreeCollapseChartDiskShrinking
import Wikipedia.SmoothSixDPoincare.AmbientIsotopyInverse

/-!
# Pointwise ambient isotopy between two whole disk charts

Compress both original disks by the same positive factor, align their germs
by a constructed supported native isotopy, and undo the second compression.
The endpoint formula holds on the entire closed disk, including its boundary.
-/

noncomputable section

open Set Function Filter Metric
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms

variable {A B E H M ι κ : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nontrivial κ]

theorem exists_disk_chart_isotopy (b : Module.Basis ι ℝ B) (i : ι)
    (basis : Module.Basis κ ℝ (A × B))
    (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, A × B) J (A × B) M ∞)
    (hΦ : closedBall (0 : A) 1 ×ˢ {(0 : B)} ⊆ Φ.source)
    (hΨ : closedBall (0 : A) 1 ×ˢ {(0 : B)} ⊆ Ψ.source)
    (hcenter : Φ 0 = Ψ 0) :
    ∃ D : Diffeomorph J J M M ∞, IsotopicToIdentity D ∧
      ∀ x ∈ closedBall (0 : A) 1, D (Φ (x, 0)) = Ψ (x, 0) := by
  have hz : (0 : A × B) ∈ closedBall (0 : A) 1 ×ˢ {(0 : B)} :=
    ⟨mem_closedBall_self zero_le_one, rfl⟩
  obtain ⟨D, K, -, -, ⟨HD⟩, hgerm⟩ :=
    exists_native_disk_germ_alignment b i basis Φ Ψ (hΦ hz) (hΨ hz) hcenter
  obtain ⟨ε, hε, hεeq⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hgerm
  let a : ℝ := min 1 ε
  have ha : 0 < a := lt_min zero_lt_one hε
  have ha1 : a ≤ 1 := min_le_left _ _
  obtain ⟨KΦ, -, -, P, ⟨HP⟩, hP⟩ := DiskShrinking.exists_chart_disk_shrinking Φ hΦ ha ha1
  obtain ⟨KΨ, -, -, Q, ⟨HQ⟩, hQ⟩ := DiskShrinking.exists_chart_disk_shrinking Ψ hΨ ha ha1
  refine ⟨(P.trans D).trans Q.symm,
    (HP.isotopicToIdentity.trans HD.isotopicToIdentity).trans HQ.isotopicToIdentity.symm, ?_⟩
  intro x hx
  have hn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  have hsmall : a • x ∈ closedBall (0 : A) ε := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact (mul_le_of_le_one_right ha.le hn).trans (min_le_right _ _)
  have heq : D (Φ (a • x, 0)) = Ψ (a • x, 0) := hεeq hsmall
  change Q.symm (D (P (Φ (x, 0)))) = Ψ (x, 0)
  rw [hP x hn, heq, ← hQ x hn, Q.symm_apply_apply]

end Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms
