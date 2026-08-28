import Wikipedia.HopfProblem.DegreeCollapseRadialDiskShrinking
import Wikipedia.HopfProblem.DegreeCollapseDiskEllipsoidChart
import Wikipedia.SmoothSixDPoincare.SupportedIsotopyExtension

/-!
# Supported shrinking of a whole disk through its original tubular chart

The ellipsoid and radial family extend to genuine diffeomorphisms of the
target manifold. The entire disk is scaled exactly in its original disk
coordinates, with common compact support and the disk center fixed at all
times. No enlargement of the given tubular chart is assumed.
-/

noncomputable section

open Set Metric Function
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking

variable {D Z E H M : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

theorem exists_chart_disk_shrinking
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) I (D × Z) M ∞)
    (hzero : closedBall (0 : D) 1 ×ˢ {(0 : Z)} ⊆ Φ.source)
    {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ Φ.target ∧ ∃ P : Diffeomorph I I M M ∞,
      Nonempty (SupportedRelativeIsotopy P K {Φ (0, 0)}) ∧
      ∀ x : D, ‖x‖ ≤ 1 → P (Φ (x, 0)) = Φ (a • x, 0) := by
  obtain ⟨R, hR, L, hLzero, hLsource⟩ := exists_disk_ellipsoid_in_open Φ.open_source hzero
  let Ψ := L.toDiffeomorph.toPartialDiffeomorph.trans Φ
  have hsource : closedBall (0 : WithLp 2 (D × Z)) R ⊆ Ψ.source := by
    intro z hz
    exact ⟨mem_univ z, hLsource hz⟩
  have htarget : Ψ.target ⊆ Φ.target := fun _ hy => hy.1
  have hΨ (x : D) : Ψ (WithLp.toLp 2 (x, (0 : Z))) = Φ (x, 0) := by
    change Φ (L (WithLp.toLp 2 (x, (0 : Z)))) = _
    rw [hLzero]
  have hΨ0 : Ψ (0 : WithLp 2 (D × Z)) = Φ (0, 0) := hΨ 0
  have h0source : (0 : WithLp 2 (D × Z)) ∈ Ψ.source :=
    hsource (mem_closedBall_self (zero_le_one.trans hR.le))
  have hfix : ∀ t (z : WithLp 2 (D × Z)), z ∉ closedBall 0 R → family R a (t, z) = z := by
    intro t z hz
    exact family_outer hR a t (le_of_not_ge (fun hn => hz (mem_closedBall_zero_iff.mpr hn)))
  obtain ⟨B, K, hK, hKt, hB, hB0, hBt, hBfix, -, hchart⟩ :=
    exists_supported_isotopy_extension Ψ (contMDiff_family R a) (family_zero R a)
      (family_slices hR ha ha₁) (isCompact_closedBall 0 R) hsource hfix
  obtain ⟨P, hP⟩ := hBt 1
  refine ⟨K, hK, hKt.trans htarget, P, ⟨{
    family := B
    smooth := hB
    zero := hB0
    one := fun y => (hP y).symm
    slices := hBt
    fixedOutside := hBfix
    fixedOn := ?_ }⟩, ?_⟩
  · intro t y hy
    rcases mem_singleton_iff.mp hy with rfl
    rw [← hΨ0, hchart t 0 h0source, family_origin]
  · intro x hx
    have hn : ‖WithLp.toLp 2 (x, (0 : Z))‖ ≤ 1 := by
      simpa only [WithLp.norm_toLp_fst] using hx
    have hs : WithLp.toLp 2 (x, (0 : Z)) ∈ Ψ.source :=
      hsource (mem_closedBall_zero_iff.mpr (hn.trans hR.le))
    have hsmul : a • WithLp.toLp 2 (x, (0 : Z)) = WithLp.toLp 2 (a • x, (0 : Z)) := by
      change WithLp.toLp 2 (a • x, a • (0 : Z)) = _
      rw [smul_zero]
    rw [← hΨ x, hP, hchart 1 _ hs, family_one_inner hR a hn, hsmul, hΨ]

end Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking
