import Wikipedia.SmoothSixDPoincare.HandleCollarDepth
import Wikipedia.SmoothSixDPoincare.CollaredDiskAttachment

/-!
# Exact collar coordinates on the whole new handle face

Inside the collar-plus-handle product model, expand the negative radius
and decrease the positive radius in a linked way. At the common corner
this is the old collar, and at time zero it is the original whole handle.
The explicit depth recovers time and proves that all parameters are retained.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.HandleCollarCoordinates

open CollaredDiskAttachment (Disk Sphere Handle)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def time (t : unitInterval) : ℝ := (t : ℝ) / 2

theorem time_nonneg (t : unitInterval) : 0 ≤ time t := div_nonneg t.property.1 (by norm_num)

theorem time_le_half (t : unitInterval) : time t ≤ 1 / 2 :=
  div_le_div_of_nonneg_right t.property.2 (by norm_num)

def factor (t : unitInterval) : ℝ := (1 + time t) / 2

theorem factor_pos (t : unitInterval) : 0 < factor t := by
  unfold factor
  linarith [time_nonneg t]

theorem factor_le_one (t : unitInterval) : factor t ≤ 1 := by
  unfold factor
  linarith [time_le_half t]

def normalScale (u : Disk E) (t : unitInterval) : ℝ := 1 - time t * (1 - ‖u.val‖)

omit [NormedSpace ℝ E] in
theorem normalScale_bounds (u : Disk E) (t : unitInterval) :
    1 / 2 ≤ normalScale u t ∧ normalScale u t ≤ 1 := by
  have hr₀ := norm_nonneg u.val
  have hr₁ := mem_closedBall_zero_iff.mp u.property
  have ht₀ := time_nonneg t
  have ht₁ := time_le_half t
  unfold normalScale
  constructor <;> nlinarith

omit [NormedSpace ℝ E] in
theorem normalScale_pos (u : Disk E) (t : unitInterval) : 0 < normalScale u t :=
  lt_of_lt_of_le (by norm_num) (normalScale_bounds u t).1

def coordinates : C((Disk E × Sphere F) × unitInterval, Handle E F) := by
  refine ⟨fun q =>
    (⟨factor q.2 • q.1.1.val, ?_⟩, ⟨normalScale q.1.1 q.2 • q.1.2.val, ?_⟩), ?_⟩
  · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (factor_pos q.2)]
    exact (mul_le_of_le_one_right (factor_pos q.2).le
      (mem_closedBall_zero_iff.mp q.1.1.property)).trans (factor_le_one q.2)
  · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (normalScale_pos q.1.1 q.2), mem_sphere_zero_iff_norm.mp q.1.2.property, mul_one]
    exact (normalScale_bounds q.1.1 q.2).2
  · have ht : Continuous (fun q : (Disk E × Sphere F) × unitInterval => time q.2) :=
      (continuous_subtype_val.comp continuous_snd).div_const 2
    have hu : Continuous (fun q : (Disk E × Sphere F) × unitInterval => q.1.1.val) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
    have hv : Continuous (fun q : (Disk E × Sphere F) × unitInterval => q.1.2.val) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
    exact ((((continuous_const.add ht).div_const 2).smul hu).subtype_mk _).prodMk
      (((continuous_const.sub (ht.mul (continuous_const.sub hu.norm))).smul hv).subtype_mk _)

theorem coordinates_fst_norm (q : (Disk E × Sphere F) × unitInterval) :
    ‖(coordinates q).1.val‖ = factor q.2 * ‖q.1.1.val‖ := by
  change ‖factor q.2 • q.1.1.val‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (factor_pos q.2)]

theorem coordinates_snd_norm (q : (Disk E × Sphere F) × unitInterval) :
    ‖(coordinates q).2.val‖ = normalScale q.1.1 q.2 := by
  change ‖normalScale q.1.1 q.2 • q.1.2.val‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (normalScale_pos q.1.1 q.2),
    mem_sphere_zero_iff_norm.mp q.1.2.property, mul_one]

theorem depth_coordinates (q : (Disk E × Sphere F) × unitInterval) :
    HandleCollarDepth.depth (2 * ‖(coordinates q).1.val‖ - 1)
      (1 - ‖(coordinates q).2.val‖) = time q.2 := by
  rw [coordinates_fst_norm, coordinates_snd_norm]
  have ht : 2 * (factor q.2 * ‖q.1.1.val‖) - 1 = ‖q.1.1.val‖ * (1 + time q.2) - 1 := by
    unfold factor
    ring
  have hd : 1 - normalScale q.1.1 q.2 = time q.2 * (1 - ‖q.1.1.val‖) := by
    unfold normalScale
    ring
  rw [ht, hd]
  exact HandleCollarDepth.depth_corner (mem_closedBall_zero_iff.mp q.1.1.property) (time_nonneg q.2)

theorem coordinates_injective : Injective (coordinates (E := E) (F := F)) := by
  rintro ⟨⟨u, v⟩, t⟩ ⟨⟨u', v'⟩, t'⟩ h
  have ht : t = t' := by
    apply Subtype.ext
    have hd := congrArg (fun p : Handle E F =>
      HandleCollarDepth.depth (2 * ‖p.1.val‖ - 1) (1 - ‖p.2.val‖)) h
    rw [depth_coordinates, depth_coordinates] at hd
    change (t : ℝ) / 2 = (t' : ℝ) / 2 at hd
    linarith
  subst t'
  have hu : u = u' := by
    apply Subtype.ext
    have he := congrArg (fun p : Handle E F => (factor t)⁻¹ • p.1.val) h
    change (factor t)⁻¹ • (factor t • u.val) = (factor t)⁻¹ • (factor t • u'.val) at he
    simpa only [inv_smul_smul₀ (factor_pos t).ne'] using he
  subst u'
  have hv : v = v' := by
    apply Subtype.ext
    have he := congrArg (fun p : Handle E F => (normalScale u t)⁻¹ • p.2.val) h
    change (normalScale u t)⁻¹ • (normalScale u t • v.val) =
      (normalScale u t)⁻¹ • (normalScale u t • v'.val) at he
    simpa only [inv_smul_smul₀ (normalScale_pos u t).ne'] using he
  subst v'
  rfl

theorem coordinates_zero (u : Disk E) (v : Sphere F) :
    coordinates ((u, v), 0) =
      CollaredDiskAttachment.newMap (u, ⟨v.val, sphere_subset_closedBall v.property⟩) := by
  apply Prod.ext <;> apply Subtype.ext
  · change ((1 + (0 : ℝ) / 2) / 2) • u.val = (1 / 2 : ℝ) • u.val
    norm_num
  · change (1 - (0 : ℝ) / 2 * (1 - ‖u.val‖)) • v.val = v.val
    norm_num

def oldTime (t : unitInterval) : unitInterval :=
  ⟨time t, time_nonneg t, (time_le_half t).trans (by norm_num)⟩

theorem coordinates_corner (u : Sphere E) (v : Sphere F) (t : unitInterval) :
    coordinates ((⟨u.val, sphere_subset_closedBall u.property⟩, v), t) =
      CollaredDiskAttachment.oldMap
        (u, oldTime t, ⟨v.val, sphere_subset_closedBall v.property⟩) := by
  apply Prod.ext <;> apply Subtype.ext
  · rfl
  · change (1 - time t * (1 - ‖u.val‖)) • v.val = v.val
    rw [mem_sphere_zero_iff_norm.mp u.property, sub_self, mul_zero, sub_zero, one_smul]

theorem coordinates_isClosedEmbedding [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] :
    IsClosedEmbedding (coordinates (E := E) (F := F)) :=
  coordinates.continuous.isClosedEmbedding coordinates_injective

end Wikipedia.SmoothSixDPoincare.HandleCollarCoordinates
