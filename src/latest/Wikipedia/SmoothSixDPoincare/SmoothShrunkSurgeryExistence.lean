import Wikipedia.SmoothSixDPoincare.ShrunkExteriorSmoothness

/-!
# Constructing shrunk surgery realizations with smooth exteriors retained

The supported belt shrinking and its height-preserving ambient extension
are constructed as before. This result retains that actual extension and
its whole-attachment formula. The original smooth exterior data therefore
transfer to both maps of the same chosen shrunk realization.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

include hf in
theorem exists_shrunkSurgeryRealization_with_ambient (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v₀ : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates)
    {a : ℝ} (ha : 0 < a) (ha₁ : a < 1) :
    ∃ R : d.ShrunkSurgeryRealization a, Nonempty R.AmbientExtension := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  obtain ⟨K, _, _, e, ⟨I⟩, hscale⟩ := d.exists_belt_disk_shrinking hf n v₀ ha ha₁.le
  obtain ⟨_, _, D, _, _, hDlevel, hDheight, _⟩ :=
    RegularLevel.exists_height_preserving_ambient_extension hf d.upper_regular e
      I.isotopicToIdentity
  have hsub (x : M) : f x ≤ f p + d.radius ^ 2 ↔ f (D x) ≤ f p + d.radius ^ 2 := by
    rw [hDheight]
  let Q : {x : M // f x ≤ f p + d.radius ^ 2} ≃ₜ
      {x : M // f x ≤ f p + d.radius ^ 2} := D.toHomeomorph.subtype hsub
  let A := d.attachmentHomeomorph.trans Q
  have hfront : ∀ x, f (A x) = f p + d.radius ^ 2 ↔
      x.val ∈ frontier ({y | f y ≤ f p - d.radius ^ 2} ∪
        range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)) := by
    intro x
    change f (D (d.attachmentHomeomorph x).val) = f p + d.radius ^ 2 ↔ _
    rw [hDheight]
    exact d.attachment_frontier x
  have hrange : range (d.surgery.changeNewBoundary e.toHomeomorph).newPiece =
      d.closedBeltTube a := by
    have heq : (d.surgery.changeNewBoundary e.toHomeomorph).newPiece =
        e.toHomeomorph ∘ d.surgery.newPiece := rfl
    rw [heq, range_comp]
    exact d.image_newPiece_eq_closedBeltTube_of_scales ha ha₁ e.toHomeomorph hscale
  let R : d.ShrunkSurgeryRealization a := {
    boundaryHomeomorph := e.toHomeomorph
    attachmentHomeomorph := A
    frontier := hfront
    fixed_belt := fun v => I.endpoint_fixed_on _ ⟨v, rfl⟩
    scales_disk := fun u v => congrArg (fun y : d.UpperLevel => (y : M)) (hscale u v)
    newPiece_range := hrange
    newPiece_eq := by
      intro z
      change (e (d.surgery.newPiece z) : M) = D _
      exact (hDlevel (d.surgery.newPiece z)).symm.trans (congrArg D (d.newPiece_eq z))
    newExterior_eq := by
      intro r
      change (e (d.surgery.newExterior r) : M) = D _
      exact (hDlevel (d.surgery.newExterior r)).symm.trans (congrArg D (d.newExterior_eq r)) }
  exact ⟨R, ⟨{
    ambient := D
    preserves_height := hDheight
    attachment_eq := fun _ => rfl
    boundary_eq := fun x => (hDlevel x).symm }⟩⟩

theorem exists_smooth_shrunkSurgeryRealization (hd : d.HasSmoothExterior hf) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v₀ : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates)
    {a : ℝ} (ha : 0 < a) (ha₁ : a < 1) :
    ∃ R : d.ShrunkSurgeryRealization a, Nonempty R.AmbientExtension ∧ R.HasSmoothExterior hf := by
  obtain ⟨R, ⟨H⟩⟩ := d.exists_shrunkSurgeryRealization_with_ambient hf n v₀ ha ha₁
  exact ⟨R, ⟨H⟩, H.hasSmoothExterior hf hd⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
