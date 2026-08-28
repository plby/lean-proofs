import Wikipedia.SmoothSixDPoincare.BeltDiskShrinking
import Wikipedia.SmoothSixDPoincare.BeltClosedDiskTube
import Wikipedia.SmoothSixDPoincare.RegularLevelIsotopyExtension

/-!
# Shrinking the surgery presentation while retaining its whole-sublevel realization

The old boundary and attaching piece are unchanged. A supported upper-level
isotopy makes the new piece exactly any prescribed sufficiently small closed
belt tube. Its ambient height-preserving extension supplies a new attachment
homeomorphism onto the original upper sublevel, with the exact new-piece map.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
/-- A smaller presentation of this same surgery, including its original
whole-upper-sublevel realization and exact positive-face map. -/
structure ShrunkSurgeryRealization (a : ℝ) where
  boundaryHomeomorph : d.UpperLevel ≃ₜ d.UpperLevel
  attachmentHomeomorph :
    ↥({x : M | f x ≤ f p - d.radius ^ 2} ∪
      range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)) ≃ₜ
      {x : M // f x ≤ f p + d.radius ^ 2}
  frontier : ∀ x, f (attachmentHomeomorph x) = f p + d.radius ^ 2 ↔
    x.val ∈ frontier ({y | f y ≤ f p - d.radius ^ 2} ∪
      range (d.chart.attachingHandleMap d.radius d.radius_pos d.block))
  fixed_belt : ∀ v, boundaryHomeomorph (d.surgery.beltSphere v) = d.surgery.beltSphere v
  scales_disk : ∀ u v, (boundaryHomeomorph (d.beltClosedDiskMap (u, v)) : M) =
    d.chart.splitChart.symm (d.chart.beltRawCoordinates d.radius (v, a • u.val))
  newPiece_range : range (d.surgery.changeNewBoundary boundaryHomeomorph).newPiece =
    d.closedBeltTube a
  newPiece_eq : ∀ z, ((d.surgery.changeNewBoundary boundaryHomeomorph).newPiece z : M) =
    (attachmentHomeomorph ⟨d.chart.normHandleMap d.radius d.radius_pos d.block
      (z.1, PuncturedHandle.sphereToBall z.2),
      Or.inr ⟨d.chart.handleBallCoordinates (z.1, PuncturedHandle.sphereToBall z.2), rfl⟩⟩).val
  newExterior_eq : ∀ r, ((d.surgery.changeNewBoundary boundaryHomeomorph).newExterior r : M) =
    (attachmentHomeomorph ⟨r.val, Or.inl r.property.1.le⟩).val

open Classical in
theorem image_newPiece_eq_closedBeltTube_of_scales {a : ℝ} (ha : 0 < a) (ha₁ : a < 1)
    (e : d.UpperLevel ≃ₜ d.UpperLevel)
    (hscale : ∀ u v, e (d.beltClosedDiskMap (u, v)) =
      d.beltClosedDiskMap (d.normalDiskScale ha ha₁.le u, v)) :
    e '' range d.surgery.newPiece = d.closedBeltTube a := by
  rw [d.range_newPiece_eq_range_beltClosedDiskMap,
    d.closedBeltTube_eq_beltClosedDiskMap_image ha₁]
  ext y
  constructor
  · rintro ⟨_, ⟨⟨u, v⟩, rfl⟩, rfl⟩
    refine ⟨(d.normalDiskScale ha ha₁.le u, v), ?_, (hscale u v).symm⟩
    change ‖a • u.val‖ ≤ a
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_of_le_one_right ha.le u.property
  · rintro ⟨⟨u, v⟩, hu, rfl⟩
    change ‖u.val‖ ≤ a at hu
    have hnorm : ‖a⁻¹ • u.val‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
      exact (inv_mul_le_iff₀ ha).mpr (by simpa only [mul_one] using hu)
    let u₀ : PuncturedHandle.UnitBall d.chart.NegativeCoordinates := ⟨a⁻¹ • u.val, hnorm⟩
    have hscaled : d.normalDiskScale ha ha₁.le u₀ = u :=
      Subtype.ext (smul_inv_smul₀ ha.ne' u.val)
    refine ⟨d.beltClosedDiskMap (u₀, v), ⟨(u₀, v), rfl⟩, ?_⟩
    rw [hscale, hscaled]

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

include hf in
open Classical in
/-- A genuinely smaller surgery presentation still realizes the original
whole upper sublevel and retains its precise positive-face attachment map. -/
theorem exists_shrunk_surgery_realization (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v₀ : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates)
    {a : ℝ} (ha : 0 < a) (ha₁ : a < 1) :
    ∃ e : d.UpperLevel ≃ₜ d.UpperLevel,
      ∃ A : ↥({x : M | f x ≤ f p - d.radius ^ 2} ∪
          range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)) ≃ₜ
          {x : M // f x ≤ f p + d.radius ^ 2},
        (∀ x, f (A x) = f p + d.radius ^ 2 ↔
          x.val ∈ frontier ({y | f y ≤ f p - d.radius ^ 2} ∪
            range (d.chart.attachingHandleMap d.radius d.radius_pos d.block))) ∧
        (∀ v, e (d.surgery.beltSphere v) = d.surgery.beltSphere v) ∧
        (∀ u v, e (d.beltClosedDiskMap (u, v)) =
          d.beltClosedDiskMap (d.normalDiskScale ha ha₁.le u, v)) ∧
        (range (d.surgery.changeNewBoundary e).newPiece = d.closedBeltTube a) ∧
        (∀ z, ((d.surgery.changeNewBoundary e).newPiece z : M) =
          (A ⟨d.chart.normHandleMap d.radius d.radius_pos d.block
            (z.1, PuncturedHandle.sphereToBall z.2),
            Or.inr ⟨d.chart.handleBallCoordinates
              (z.1, PuncturedHandle.sphereToBall z.2), rfl⟩⟩).val) ∧
        ∀ r, ((d.surgery.changeNewBoundary e).newExterior r : M) =
          (A ⟨r.val, Or.inl r.property.1.le⟩).val := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  obtain ⟨K, _, _, e, ⟨I⟩, hscale⟩ :=
    d.exists_belt_disk_shrinking hf n v₀ ha ha₁.le
  obtain ⟨_, _, D, _, _, hDlevel, hDheight, _⟩ :=
    RegularLevel.exists_height_preserving_ambient_extension hf d.upper_regular e
      I.isotopicToIdentity
  have hsub (x : M) : f x ≤ f p + d.radius ^ 2 ↔ f (D x) ≤ f p + d.radius ^ 2 := by
    rw [hDheight]
  let Q : {x : M // f x ≤ f p + d.radius ^ 2} ≃ₜ
      {x : M // f x ≤ f p + d.radius ^ 2} := D.toHomeomorph.subtype hsub
  let A := d.attachmentHomeomorph.trans Q
  refine ⟨e.toHomeomorph, A, ?_, ?_, hscale, ?_, ?_, ?_⟩
  · intro x
    change f (D (d.attachmentHomeomorph x).val) = f p + d.radius ^ 2 ↔ _
    rw [hDheight]
    exact d.attachment_frontier x
  · intro v
    exact I.endpoint_fixed_on _ ⟨v, rfl⟩
  · have heq : (d.surgery.changeNewBoundary e.toHomeomorph).newPiece =
        e.toHomeomorph ∘ d.surgery.newPiece := rfl
    rw [heq, range_comp]
    exact d.image_newPiece_eq_closedBeltTube_of_scales ha ha₁ e.toHomeomorph hscale
  · intro z
    change (e (d.surgery.newPiece z) : M) = D _
    exact (hDlevel (d.surgery.newPiece z)).symm.trans (congrArg D (d.newPiece_eq z))
  · intro r
    change (e (d.surgery.newExterior r) : M) = D _
    exact (hDlevel (d.surgery.newExterior r)).symm.trans (congrArg D (d.newExterior_eq r))

include hf in
open Classical in
/-- Construct all data of the refined surgery at the requested radius. -/
theorem nonempty_shrunkSurgeryRealization (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v₀ : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates)
    {a : ℝ} (ha : 0 < a) (ha₁ : a < 1) : Nonempty (d.ShrunkSurgeryRealization a) := by
  obtain ⟨e, A, hfront, hfixed, hscale, hrange, hpiece, hexterior⟩ :=
    d.exists_shrunk_surgery_realization hf n v₀ ha ha₁
  refine ⟨{
    boundaryHomeomorph := e
    attachmentHomeomorph := A
    frontier := hfront
    fixed_belt := hfixed
    scales_disk := ?_
    newPiece_range := hrange
    newPiece_eq := hpiece
    newExterior_eq := hexterior }⟩
  intro u v
  exact congrArg (fun y : d.UpperLevel => (y : M)) (hscale u v)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
