import Wikipedia.NoExoticSixSphere.SphereSuspension

/-!
# Retraction of the twice-punctured sphere onto its equator

Keep the orthogonal component and shrink the pole component to zero,
normalizing throughout. The orthogonal component never vanishes away
from the two poles. This gives a strong deformation retract on the actual
sphere complement, with every equatorial point fixed.
-/

noncomputable section

open scoped unitInterval ContinuousMap

namespace NoExoticSixSphere.SphereEquatorRetraction

open SphereSuspension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_zero_iff (v y : UnitSphere E) : radial v y = 0 ↔ y = v ∨ y = antipode v := by
  constructor
  · intro hy
    have hs := norm_radial_sq v y
    rw [hy, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hs
    have ha : latitude (height v y) = 1 ∨ latitude (height v y) = -1 := by
      rcases le_total 0 (latitude (height v y)) with hp | hn
      · left; nlinarith
      · right; nlinarith
    have he : (y : E) = latitude (height v y) • (v : E) := sub_eq_zero.mp hy
    rcases ha with ha | ha
    · left
      exact Subtype.ext (by simpa only [ha, one_smul] using he)
    · right
      apply Subtype.ext
      change (y : E) = -(v : E)
      simpa only [ha, neg_one_smul] using he
  · rintro (rfl | rfl)
    · simp [radial, latitude_height]
    · simp [radial, latitude_height, antipode]

def punctured (v : UnitSphere E) : Set (UnitSphere E) := {y | radial v y ≠ 0}

theorem punctured_eq (v : UnitSphere E) : punctured v = {v}ᶜ ∩ {antipode v}ᶜ := by
  ext y
  change (¬ radial v y = 0) ↔ y ≠ v ∧ y ≠ antipode v
  rw [radial_zero_iff, not_or]

theorem continuous_radial (v : UnitSphere E) : Continuous (radial v) := by
  change Continuous (fun y : UnitSphere E ↦ (y : E) - latitude (height v y) • (v : E))
  simp only [latitude_height]
  exact continuous_subtype_val.sub
    ((continuous_const.inner continuous_subtype_val).smul continuous_const)

theorem radial_equator (v : UnitSphere E) (x : Equator v) : radial v x.val = (x.val : E) := by
  rw [radial, latitude_height, x.property, zero_smul, sub_zero]

theorem equator_mem (v : UnitSphere E) (x : Equator v) : x.val ∈ punctured v := by
  intro h
  change radial v x.val = 0 at h
  rw [radial_equator] at h
  have hn := ClosedHemisphere.unit_norm x.val
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

def inclusion (v : UnitSphere E) : C(Equator v, punctured v) :=
  ⟨fun x ↦ ⟨x.val, equator_mem v x⟩, continuous_subtype_val.subtype_mk _⟩

def vector (v : UnitSphere E) (s : I) (y : punctured v) : E :=
  radial v y.val + ((1 - (s : ℝ)) * inner ℝ (v : E) (y.val : E)) • (v : E)

theorem inner_vector (v : UnitSphere E) (s : I) (y : punctured v) :
    inner ℝ (v : E) (vector v s y) = (1 - (s : ℝ)) * inner ℝ (v : E) (y.val : E) := by
  rw [vector, inner_add_right, inner_radial, real_inner_smul_right,
    real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm]
  ring

theorem vector_ne_zero (v : UnitSphere E) (s : I) (y : punctured v) : vector v s y ≠ 0 := by
  intro he
  have ha := inner_vector v s y
  rw [he, inner_zero_right] at ha
  change radial v y.val + ((1 - (s : ℝ)) * inner ℝ (v : E) (y.val : E)) • (v : E) = 0 at he
  rw [← ha, zero_smul, add_zero] at he
  exact y.property he

theorem continuous_vector (v : UnitSphere E) :
    Continuous (fun p : I × punctured v ↦ vector v p.1 p.2) := by
  have hs : Continuous (fun p : I × punctured v ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hy : Continuous (fun p : I × punctured v ↦ p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_radial v).comp hy).add
    (((continuous_const.sub hs).mul
      (continuous_const.inner (continuous_subtype_val.comp hy))).smul continuous_const)

def normalized (v : UnitSphere E) (s : I) (y : punctured v) : UnitSphere E :=
  ⟨NormedSpace.normalize (vector v s y), by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      NormedSpace.norm_normalize (vector_ne_zero v s y)⟩

theorem radial_normalized (v : UnitSphere E) (s : I) (y : punctured v) :
    radial v (normalized v s y) = ‖vector v s y‖⁻¹ • radial v y.val := by
  change NormedSpace.normalize (vector v s y) -
    latitude (height v (normalized v s y)) • (v : E) = _
  rw [latitude_height]
  change ‖vector v s y‖⁻¹ • vector v s y -
    inner ℝ (v : E) (‖vector v s y‖⁻¹ • vector v s y) • (v : E) = _
  rw [real_inner_smul_right, inner_vector, vector, smul_add, smul_smul, add_sub_cancel_right]

theorem normalized_mem (v : UnitSphere E) (s : I) (y : punctured v) :
    normalized v s y ∈ punctured v := by
  change radial v (normalized v s y) ≠ 0
  rw [radial_normalized]
  exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr (vector_ne_zero v s y))) y.property

theorem continuous_normalized (v : UnitSphere E) :
    Continuous (fun p : I × punctured v ↦ normalized v p.1 p.2) := by
  apply Continuous.subtype_mk
  have hv := continuous_vector v
  exact ((hv.norm.inv₀ (fun p ↦ norm_ne_zero_iff.mpr (vector_ne_zero v p.1 p.2))).smul hv)

def point (v : UnitSphere E) (s : I) (y : punctured v) : punctured v :=
  ⟨normalized v s y, normalized_mem v s y⟩

theorem continuous_point (v : UnitSphere E) :
    Continuous (fun p : I × punctured v ↦ point v p.1 p.2) :=
  (continuous_normalized v).subtype_mk _

def retraction (v : UnitSphere E) : C(punctured v, Equator v) where
  toFun y := direction v y.val y.property
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hr : Continuous (fun y : punctured v ↦ radial v y.val) :=
      (continuous_radial v).comp continuous_subtype_val
    exact (hr.norm.inv₀ (fun y ↦ norm_ne_zero_iff.mpr y.property)).smul hr

theorem retraction_inclusion (v : UnitSphere E) (x : Equator v) :
    retraction v (inclusion v x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  change NormedSpace.normalize (radial v x.val) = (x.val : E)
  rw [radial_equator]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm x.val)

theorem point_zero (v : UnitSphere E) (y : punctured v) : point v 0 y = y := by
  apply Subtype.ext
  apply Subtype.ext
  change NormedSpace.normalize (vector v 0 y) = (y.val : E)
  have he : vector v 0 y = (y.val : E) := by
    simp [vector, radial, latitude_height]
  rw [he]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm y.val)

theorem point_one (v : UnitSphere E) (y : punctured v) :
    point v 1 y = inclusion v (retraction v y) := by
  apply Subtype.ext
  apply Subtype.ext
  change NormedSpace.normalize (vector v 1 y) = NormedSpace.normalize (radial v y.val)
  congr 1
  simp [vector]

theorem point_inclusion (v : UnitSphere E) (s : I) (x : Equator v) :
    point v s (inclusion v x) = inclusion v x := by
  apply Subtype.ext
  apply Subtype.ext
  change NormedSpace.normalize (vector v s (inclusion v x)) = (x.val : E)
  have he : vector v s (inclusion v x) = (x.val : E) := by
    change radial v x.val + ((1 - (s : ℝ)) * inner ℝ (v : E) (x.val : E)) • (v : E) = _
    rw [radial_equator, x.property, mul_zero, zero_smul, add_zero]
  rw [he]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm x.val)

def deformation (v : UnitSphere E) : (ContinuousMap.id (punctured v)).HomotopyRel
    ((inclusion v).comp (retraction v)) (Set.range (inclusion v)) where
  toFun p := point v p.1 p.2
  continuous_toFun := continuous_point v
  map_zero_left := point_zero v
  map_one_left := point_one v
  prop' s y hy := by
    obtain ⟨x, rfl⟩ := hy
    exact point_inclusion v s x

end NoExoticSixSphere.SphereEquatorRetraction
