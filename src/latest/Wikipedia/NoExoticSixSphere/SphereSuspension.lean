import Wikipedia.NoExoticSixSphere.HemisphereCone

/-!
# The actual sphere as the suspension of its equator

The latitude parameter runs from the pole to its antipode. The continuous
parametrization is onto, and its only identifications collapse the two endpoint
slices. This will allow homotopies of meridian path families to descend to
homotopies of sphere maps.
-/

open Set unitInterval

namespace NoExoticSixSphere.SphereSuspension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def latitude (t : I) : ℝ := 1 - 2 * (t : ℝ)

theorem latitude_bounds (t : I) : -1 ≤ latitude t ∧ latitude t ≤ 1 := by
  dsimp [latitude]
  constructor <;> linarith [t.2.1, t.2.2]

theorem radicand_nonneg (t : I) : 0 ≤ 1 - latitude t ^ 2 := by
  obtain ⟨h₁, h₂⟩ := latitude_bounds t
  nlinarith

noncomputable def vector (v : UnitSphere E) (t : I) (x : Equator v) : E :=
  Real.sqrt (1 - latitude t ^ 2) • (x.1 : E) + latitude t • (v : E)

theorem norm_vector (v : UnitSphere E) (t : I) (x : Equator v) : ‖vector v t x‖ = 1 := by
  have hvx : inner ℝ (x.1 : E) (v : E) = 0 := by
    rw [real_inner_comm]
    exact x.2
  have hs : ‖vector v t x‖ ^ 2 = 1 := by
    rw [vector, norm_add_sq_real, norm_smul, norm_smul,
      ClosedHemisphere.unit_norm, ClosedHemisphere.unit_norm,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_one, mul_one, sq_abs, real_inner_smul_left, real_inner_smul_right, hvx]
    nlinarith [Real.sq_sqrt (radicand_nonneg t)]
  nlinarith [norm_nonneg (vector v t x)]

theorem inner_vector (v : UnitSphere E) (t : I) (x : Equator v) :
    inner ℝ (v : E) (vector v t x) = latitude t := by
  rw [vector, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    x.2, real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm]
  ring

noncomputable def point (v : UnitSphere E) (p : I × Equator v) : UnitSphere E :=
  ⟨vector v p.1 p.2, by
    simpa only [Metric.mem_sphere, dist_zero_right] using norm_vector v p.1 p.2⟩

theorem continuous_point (v : UnitSphere E) : Continuous (point v) := by
  have ht : Continuous (fun p : I × Equator v ↦ latitude p.1) :=
    continuous_const.sub (continuous_const.mul (continuous_subtype_val.comp continuous_fst))
  have hx : Continuous (fun p : I × Equator v ↦ (p.2.1 : E)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact (((continuous_const.sub (ht.pow 2)).sqrt.smul hx).add
    (ht.smul continuous_const)).subtype_mk _

theorem point_zero (v : UnitSphere E) (x : Equator v) : point v (0, x) = v := by
  apply Subtype.ext
  change vector v 0 x = (v : E)
  simp [vector, latitude]

theorem point_one (v : UnitSphere E) (x : Equator v) : point v (1, x) = antipode v := by
  apply Subtype.ext
  change vector v 1 x = -(v : E)
  norm_num [vector, latitude]

theorem inner_bounds (v y : UnitSphere E) :
    -1 ≤ inner ℝ (v : E) (y : E) ∧ inner ℝ (v : E) (y : E) ≤ 1 := by
  have h := abs_real_inner_le_norm (v : E) (y : E)
  rw [ClosedHemisphere.unit_norm, ClosedHemisphere.unit_norm, mul_one] at h
  exact abs_le.mp h

noncomputable def height (v y : UnitSphere E) : I :=
  ⟨(1 - inner ℝ (v : E) (y : E)) / 2, by
    obtain ⟨h₁, h₂⟩ := inner_bounds v y
    constructor <;> linarith⟩

theorem latitude_height (v y : UnitSphere E) :
    latitude (height v y) = inner ℝ (v : E) (y : E) := by
  dsimp [latitude, height]
  ring

theorem height_point (v : UnitSphere E) (t : I) (x : Equator v) :
    height v (point v (t, x)) = t := by
  apply Subtype.ext
  change (1 - inner ℝ (v : E) (vector v t x)) / 2 = (t : ℝ)
  rw [inner_vector]
  dsimp [latitude]
  ring

theorem continuous_height (v : UnitSphere E) : Continuous (height v) :=
  ((continuous_const.sub (continuous_const.inner continuous_subtype_val)).div_const 2).subtype_mk _

noncomputable def radial (v y : UnitSphere E) : E :=
  (y : E) - latitude (height v y) • (v : E)

theorem inner_radial (v y : UnitSphere E) : inner ℝ (v : E) (radial v y) = 0 := by
  rw [radial, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    ClosedHemisphere.unit_norm, one_pow, mul_one, latitude_height, sub_self]

theorem norm_radial_sq (v y : UnitSphere E) :
    ‖radial v y‖ ^ 2 = 1 - latitude (height v y) ^ 2 := by
  rw [radial, norm_sub_sq_real, norm_smul, ClosedHemisphere.unit_norm,
    ClosedHemisphere.unit_norm, Real.norm_eq_abs, mul_one, sq_abs,
    real_inner_smul_right, real_inner_comm, ← latitude_height v y]
  ring

theorem norm_radial (v y : UnitSphere E) :
    ‖radial v y‖ = Real.sqrt (1 - latitude (height v y) ^ 2) := by
  rw [← norm_radial_sq, Real.sqrt_sq (norm_nonneg _)]

noncomputable def direction (v y : UnitSphere E) (hy : radial v y ≠ 0) : Equator v :=
  ⟨⟨NormedSpace.normalize (radial v y), by
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hy⟩, by
    change inner ℝ (v : E) (‖radial v y‖⁻¹ • radial v y) = 0
    rw [real_inner_smul_right, inner_radial, mul_zero]⟩

theorem point_height_direction (v y : UnitSphere E) (hy : radial v y ≠ 0) :
    point v (height v y, direction v y hy) = y := by
  apply Subtype.ext
  change Real.sqrt (1 - latitude (height v y) ^ 2) •
    (‖radial v y‖⁻¹ • radial v y) + latitude (height v y) • (v : E) = (y : E)
  rw [← norm_radial, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]
  exact sub_add_cancel _ _

theorem surjective_point (v : UnitSphere E) [Nonempty (Equator v)] :
    Function.Surjective (point v) := by
  intro y
  by_cases hy : radial v y = 0
  · have hs := norm_radial_sq v y
    rw [hy, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hs
    have hlat : latitude (height v y) = 1 ∨ latitude (height v y) = -1 := by
      rcases le_total 0 (latitude (height v y)) with hp | hn
      · left; nlinarith
      · right; nlinarith
    have hvec : (y : E) = latitude (height v y) • (v : E) := sub_eq_zero.mp hy
    rcases hlat with hp | hn
    · refine ⟨(0, Classical.choice inferInstance), ?_⟩
      rw [point_zero]
      apply Subtype.ext
      simpa only [hp, one_smul] using hvec.symm
    · refine ⟨(1, Classical.choice inferInstance), ?_⟩
      rw [point_one]
      apply Subtype.ext
      change -(v : E) = (y : E)
      simpa only [hn, neg_one_smul] using hvec.symm
  · exact ⟨(height v y, direction v y hy), point_height_direction v y hy⟩

theorem point_fibers (v : UnitSphere E) (p q : I × Equator v)
    (hpq : point v p = point v q) :
    p = q ∨ (p.1 = 0 ∧ q.1 = 0) ∨ (p.1 = 1 ∧ q.1 = 1) := by
  have ht : p.1 = q.1 := by
    exact (height_point v p.1 p.2).symm.trans
      ((congrArg (height v) hpq).trans (height_point v q.1 q.2))
  rcases p with ⟨t, x⟩
  rcases q with ⟨s, y⟩
  dsimp only at ht
  subst s
  by_cases h0 : t = 0
  · exact Or.inr (Or.inl ⟨h0, h0⟩)
  by_cases h1 : t = 1
  · exact Or.inr (Or.inr ⟨h1, h1⟩)
  left
  have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (by
    intro h; exact h0 (Subtype.ext h.symm))
  have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (by
    intro h; exact h1 (Subtype.ext h))
  have hr : Real.sqrt (1 - latitude t ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by
    dsimp [latitude]
    nlinarith))
  have hvec := congrArg (fun z : UnitSphere E ↦ (z : E)) hpq
  change Real.sqrt (1 - latitude t ^ 2) • (x.1 : E) + latitude t • (v : E) =
    Real.sqrt (1 - latitude t ^ 2) • (y.1 : E) + latitude t • (v : E) at hvec
  have hxy : (x.1 : E) = (y.1 : E) := (smul_right_injective E hr) (add_right_cancel hvec)
  exact congrArg (fun z : Equator v ↦ (t, z)) (Subtype.ext (Subtype.ext hxy))

theorem isQuotientMap_point [FiniteDimensional ℝ E] (v : UnitSphere E)
    [Nonempty (Equator v)] : Topology.IsQuotientMap (point v) :=
  .of_surjective_continuous (surjective_point v) (continuous_point v)

end NoExoticSixSphere.SphereSuspension
