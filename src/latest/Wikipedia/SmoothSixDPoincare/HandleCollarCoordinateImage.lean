import Wikipedia.SmoothSixDPoincare.HandleCollarCoordinates

/-!
# The whole image of the explicit new-face collar coordinates

The quadratic depth and its recovered radius give actual inverse
parameters for every shallow model point. In particular, deleting the
inner time end gives exactly the strict depth sublevel in the model.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.HandleCollarCoordinates

open CollaredDiskAttachment (Disk Sphere Handle)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_coordinates_of_depth_le_half (z : Handle E F)
    (hz : HandleCollarDepth.depth (2 * ‖z.1.val‖ - 1) (1 - ‖z.2.val‖) ≤ 1 / 2) :
    ∃ q : (Disk E × Sphere F) × unitInterval, coordinates q = z ∧
      time q.2 = HandleCollarDepth.depth (2 * ‖z.1.val‖ - 1) (1 - ‖z.2.val‖) := by
  let s := 2 * ‖z.1.val‖ - 1
  let d := 1 - ‖z.2.val‖
  let w := HandleCollarDepth.depth s d
  have hs : -1 ≤ s := by dsimp [s]; linarith [norm_nonneg z.1.val]
  have hd : 0 ≤ d := sub_nonneg.mpr (mem_closedBall_zero_iff.mp z.2.property)
  have hw₀ : 0 ≤ w := HandleCollarDepth.depth_nonneg s hd
  have hw₁ : w ≤ 1 / 2 := hz
  have hden : 0 < 1 + w := by linarith
  have hF : 0 < ‖z.2.val‖ := by
    have h := HandleCollarDepth.normal_pos_of_depth_lt_one hs hd
      (show HandleCollarDepth.depth s d < 1 by linarith)
    dsimp [d] at h
    linarith
  let t : unitInterval := ⟨2 * w, by constructor <;> linarith⟩
  have htime : time t = w := by dsimp [time, t]; ring
  have hnorm : ‖(2 / (1 + w)) • z.1.val‖ = HandleCollarDepth.radius s d := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hden)]
    change 2 / (1 + w) * ‖z.1.val‖ = (s + 1) / (1 + w)
    dsimp [s]
    field_simp
    ring
  let u : Disk E := ⟨(2 / (1 + w)) • z.1.val, mem_closedBall_zero_iff.mpr
    (hnorm.trans_le (HandleCollarDepth.radius_le_one s hd))⟩
  let v : Sphere F := RadialExtension.direction z.2.val (norm_pos_iff.mp hF)
  have hu : ‖u.val‖ = HandleCollarDepth.radius s d := hnorm
  have hscale : normalScale u t = ‖z.2.val‖ := by
    rw [normalScale, htime, hu]
    change 1 - HandleCollarDepth.depth s d * (1 - HandleCollarDepth.radius s d) = ‖z.2.val‖
    rw [HandleCollarDepth.deficit_reconstruct s hd]
    dsimp [d]
    ring
  refine ⟨((u, v), t), ?_, htime⟩
  apply Prod.ext
  · apply Subtype.ext
    change factor t • ((2 / (1 + w)) • z.1.val) = z.1.val
    have hfactor : factor t * (2 / (1 + w)) = 1 := by
      rw [factor, htime]
      field_simp
    rw [smul_smul, hfactor, one_smul]
  · apply Subtype.ext
    change normalScale u t • (‖z.2.val‖⁻¹ • z.2.val) = z.2.val
    rw [hscale, smul_inv_smul₀ hF.ne']

theorem coordinates_image : range (coordinates (E := E) (F := F)) =
    {z : Handle E F | HandleCollarDepth.depth (2 * ‖z.1.val‖ - 1) (1 - ‖z.2.val‖) ≤ 1 / 2} := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    change HandleCollarDepth.depth _ _ ≤ 1 / 2
    rw [depth_coordinates]
    exact time_le_half q.2
  · intro hz
    obtain ⟨q, hq, _⟩ := exists_coordinates_of_depth_le_half z hz
    exact ⟨q, hq⟩

theorem coordinates_inner_image :
    coordinates (E := E) (F := F) '' {q : (Disk E × Sphere F) × unitInterval | q.2 < 1} =
      {z : Handle E F | HandleCollarDepth.depth (2 * ‖z.1.val‖ - 1) (1 - ‖z.2.val‖) < 1 / 2} := by
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    change HandleCollarDepth.depth _ _ < 1 / 2
    rw [depth_coordinates]
    have ht : (q.2 : ℝ) < 1 := hq
    unfold time
    linarith
  · intro hz
    have hz' : HandleCollarDepth.depth (2 * ‖z.1.val‖ - 1) (1 - ‖z.2.val‖) < 1 / 2 := hz
    obtain ⟨q, hq, ht⟩ := exists_coordinates_of_depth_le_half z hz'.le
    refine ⟨q, ?_, hq⟩
    change (q.2 : ℝ) < 1
    unfold time at ht
    linarith

end Wikipedia.SmoothSixDPoincare.HandleCollarCoordinates
