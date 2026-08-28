import Wikipedia.SmoothSixDPoincare.FramedSurgerySmoothBoundary

/-! # Check a map's native smoothness on the two actual surgery patches -/

noncomputable section

open Set Function Topology Filter
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery.SmoothBoundaryData

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  {A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X}
  {n : ℕ} [Fact (Module.finrank ℝ F = n + 1)] (P : SmoothBoundaryData A n)

theorem contMDiff_oldMap :
    letI := P.charted
    ContMDiff J J ∞ (oldMap A n) := by
  let _ := P.charted
  have h : ContMDiff J J ∞ P.oldPartial := by
    rw [← contMDiffOn_univ, ← P.old_source]
    exact P.oldPartial.contMDiffOn
  exact h.congr (fun x => (P.old_point x).symm)

theorem contMDiff_newMap :
    letI := P.charted
    ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) J ∞ (newMap A n) := by
  let _ := P.charted
  have h : ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) J ∞ P.newPartial := by
    rw [← contMDiffOn_univ, ← P.new_source]
    exact P.newPartial.contMDiffOn
  exact h.congr (fun x => (P.new_point x).symm)

variable {G' H' Y : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
  [TopologicalSpace H'] {I : ModelWithCorners ℝ G' H'}
  [TopologicalSpace Y] [ChartedSpace H' Y]

theorem contMDiff_of_patches (f : Boundary A n → Y) :
    letI := P.charted
    ContMDiff J I ∞ (f ∘ oldMap A n) →
    ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) I ∞ (f ∘ newMap A n) → ContMDiff J I ∞ f := by
  let _ := P.charted
  intro hold hnew z
  rcases cover A n z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · have hx : oldMap A n x ∈ P.oldPartial.target := by
      rw [← P.old_point]
      exact P.oldPartial.map_source (P.old_source.symm ▸ mem_univ x)
    have hp := P.oldPartial.symm.contMDiffOn.contMDiffAt (P.oldPartial.open_target.mem_nhds hx)
    apply (hold.contMDiffAt.comp _ hp).congr_of_eventuallyEq
    filter_upwards [P.oldPartial.open_target.mem_nhds hx] with y hy
    apply congrArg f
    exact (P.oldPartial.right_inv hy).symm.trans (P.old_point (P.oldPartial.symm y))
  · have hy : newMap A n y ∈ P.newPartial.target := by
      rw [← P.new_point]
      exact P.newPartial.map_source (P.new_source.symm ▸ mem_univ y)
    have hp := P.newPartial.symm.contMDiffOn.contMDiffAt (P.newPartial.open_target.mem_nhds hy)
    apply (hnew.contMDiffAt.comp _ hp).congr_of_eventuallyEq
    filter_upwards [P.newPartial.open_target.mem_nhds hy] with z hz
    apply congrArg f
    exact (P.newPartial.right_inv hz).symm.trans (P.new_point (P.newPartial.symm z))

end Wikipedia.SmoothSixDPoincare.FramedSurgery.SmoothBoundaryData
