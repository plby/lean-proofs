import Wikipedia.HopfProblem.DegreeCollapsePrescribedMorsePatchField

/-!
# Compact original Morse blocks and their inner neighborhoods

The actual inverse chart maps a compact coordinate block to a closed
patch of the original manifold. Its quadratic height stays in the stated
closed interval, and every strictly smaller coordinate block has a full
native neighborhood inside that patch.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}

open Classical in
def morseClosedBlock (c : SignedMorseChart (E := E) f p) (R : ℝ) : Set M :=
  c.splitChart.symm '' (closedBall (0 : c.NegativeCoordinates) R ×ˢ
    closedBall (0 : c.PositiveCoordinates) R)

open Classical in
theorem morseClosedBlock_subset_source (c : SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock : closedBall (0 : c.NegativeCoordinates) R ×ˢ
      closedBall (0 : c.PositiveCoordinates) R ⊆ c.splitChart.target) :
    morseClosedBlock c R ⊆ c.splitChart.source := by
  rintro x ⟨z, hz, rfl⟩
  exact c.splitChart.map_target' (hblock hz)

open Classical in
theorem morseClosedBlock_height (c : SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock : closedBall (0 : c.NegativeCoordinates) R ×ˢ
      closedBall (0 : c.PositiveCoordinates) R ⊆ c.splitChart.target) :
    morseClosedBlock c R ⊆ f ⁻¹' Icc (f p - R ^ 2) (f p + R ^ 2) := by
  rintro x ⟨z, hz, rfl⟩
  have hn : ‖z.1‖ ≤ R := mem_closedBall_zero_iff.mp hz.1
  have hp : ‖z.2‖ ≤ R := mem_closedBall_zero_iff.mp hz.2
  have hn2 : ‖z.1‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hp2 : ‖z.2‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  change f (c.splitChart.symm z) ∈ Icc (f p - R ^ 2) (f p + R ^ 2)
  rw [c.splitChart_inverse_equation (hblock hz)]
  constructor <;> nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]

open Classical in
theorem morseClosedBlock_mem_nhds (c : SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock : closedBall (0 : c.NegativeCoordinates) R ×ˢ
      closedBall (0 : c.PositiveCoordinates) R ⊆ c.splitChart.target)
    {z : c.NegativeCoordinates × c.PositiveCoordinates}
    (hn : ‖z.1‖ < R) (hp : ‖z.2‖ < R) :
    morseClosedBlock c R ∈ 𝓝 (c.splitChart.symm z) := by
  have hz : z ∈ c.splitChart.target := hblock
    ⟨mem_closedBall_zero_iff.mpr hn.le, mem_closedBall_zero_iff.mpr hp.le⟩
  have hx : c.splitChart.symm z ∈ c.splitChart.source := c.splitChart.map_target' hz
  have hc : c.splitChart (c.splitChart.symm z) = z := c.splitChart.right_inv' hz
  have ho : ball (0 : c.NegativeCoordinates) R ×ˢ ball (0 : c.PositiveCoordinates) R ∈
      𝓝 (c.splitChart (c.splitChart.symm z)) := by
    rw [hc]
    exact (isOpen_ball.prod isOpen_ball).mem_nhds
      ⟨mem_ball_zero_iff.mpr hn, mem_ball_zero_iff.mpr hp⟩
  have hnear := (c.splitChart.toOpenPartialHomeomorph.continuousAt hx) ho
  filter_upwards [c.splitChart.open_source.mem_nhds hx, hnear] with y hy hcy
  exact ⟨c.splitChart y, ⟨ball_subset_closedBall hcy.1, ball_subset_closedBall hcy.2⟩,
    c.splitChart.left_inv' hy⟩

variable [FiniteDimensional ℝ E]

open Classical in
theorem isCompact_morseClosedBlock (c : SignedMorseChart (E := E) f p) (R : ℝ)
    (hblock : closedBall (0 : c.NegativeCoordinates) R ×ˢ
      closedBall (0 : c.PositiveCoordinates) R ⊆ c.splitChart.target) :
    IsCompact (morseClosedBlock c R) :=
  (isCompact_closedBall (0 : c.NegativeCoordinates) R).prod
    (isCompact_closedBall (0 : c.PositiveCoordinates) R) |>.image_of_continuousOn
      (c.splitChart.symm.contMDiffOn_toFun.continuousOn.mono hblock)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
