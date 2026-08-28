import Wikipedia.HopfProblem.DegreeCollapseHopfBlockGeometry

/-!
# An explicit homotopy for the Hopf identity-block formula

The block formula and the radial-suspension formula have nonnegative
inner product everywhere. Their straight segment never vanishes, so
normalizing it gives an actual homotopy. This includes all zero-radius
faces and retains an arbitrary family parameter.
-/

noncomputable section

open scoped Topology InnerProductSpace
open NoExoticSixSphere GLOrthonormalization unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.HopfBlockHomotopy

open OrthogonalHopfMap HopfBlockGeometry

theorem scalar_inner_nonnegative (a b c r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (he : r ^ 2 = a ^ 2 + b ^ 2) :
    0 ≤ r⁻¹ * ((a ^ 2 + b ^ 2) ^ 2 - c ^ 2 * (a ^ 2 - b ^ 2)) + 2 * a * c ^ 2 := by
  by_cases hz : r = 0
  · rw [hz, inv_zero, zero_mul, zero_add]
    positivity
  · have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    have har : a ≤ r := by nlinarith [sq_nonneg b]
    have hcore : 0 ≤ 2 * a * r - a ^ 2 + b ^ 2 := by
      nlinarith [mul_nonneg ha (sub_nonneg.mpr har), sq_nonneg a, sq_nonneg b]
    have hid :
        (r⁻¹ * ((a ^ 2 + b ^ 2) ^ 2 - c ^ 2 * (a ^ 2 - b ^ 2)) +
          2 * a * c ^ 2) * r =
          (a ^ 2 + b ^ 2) ^ 2 + c ^ 2 * (2 * a * r - a ^ 2 + b ^ 2) := by
      field_simp
      ring
    apply (mul_nonneg_iff_of_pos_right hp).mp
    rw [hid]
    exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg c) hcore)

variable {P E G : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] {n : ℕ}

theorem block_suspended_inner (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : Triple E (Vector n) G) :
    ⟪blockVector f p x, suspendedVector f p x⟫_ℝ =
      ‖head x‖⁻¹ * ((‖x.fst‖ ^ 2 + ‖x.snd.fst‖ ^ 2) ^ 2 -
        ‖x.snd.snd‖ ^ 2 * (‖x.fst‖ ^ 2 - ‖x.snd.fst‖ ^ 2)) +
        2 * ‖x.fst‖ * ‖x.snd.snd‖ ^ 2 := by
  simp only [WithLp.prod_inner_apply]
  change ⟪‖x.fst‖ ^ 2 - ‖x.snd.fst‖ ^ 2 - ‖x.snd.snd‖ ^ 2,
      ‖head x‖⁻¹ * (‖x.fst‖ ^ 2 - ‖x.snd.fst‖ ^ 2)⟫_ℝ +
    (⟪(2 : ℝ) • RadialSphereAction.value (action f) p x.fst x.snd.fst,
        ‖head x‖⁻¹ • ((2 : ℝ) • RadialSphereAction.value (action f) p x.fst x.snd.fst)⟫_ℝ +
      ⟪(2 * ‖x.fst‖) • x.snd.snd, x.snd.snd⟫_ℝ) = _
  simp only [Real.inner_apply, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    RadialSphereAction.value_norm (action f) (action_norm f)]
  ring

theorem block_suspended_inner_nonnegative (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : Triple E (Vector n) G) :
    0 ≤ ⟪blockVector f p x, suspendedVector f p x⟫_ℝ := by
  rw [block_suspended_inner]
  exact scalar_inner_nonnegative ‖x.fst‖ ‖x.snd.fst‖ ‖x.snd.snd‖ ‖head x‖
    (norm_nonneg _) (norm_nonneg _) (WithLp.prod_norm_sq_eq_of_L2 (head x))

section SphereSegment

variable {X W : Type*} [TopologicalSpace X]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem segment_ne_zero (u v : UnitSphere W) (h : 0 ≤ ⟪u.val, v.val⟫_ℝ) (t : I) :
    (1 - (t : ℝ)) • u.val + (t : ℝ) • v.val ≠ 0 := by
  intro hz
  by_cases ht : (t : ℝ) = 1
  · have hv : v.val = 0 := by simpa only [ht, sub_self, zero_smul, one_smul, zero_add] using hz
    exact ne_zero_of_mem_unit_sphere v hv
  · have hp : 0 < 1 - (t : ℝ) := sub_pos.mpr (lt_of_le_of_ne t.property.2 ht)
    have hh := congrArg (fun w : W ↦ ⟪u.val, w⟫_ℝ) hz
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp u.property, one_pow,
      inner_zero_right] at hh
    have hmul := mul_nonneg t.property.1 h
    linarith

def nonnegativeHomotopy (f g : C(X, UnitSphere W)) (h : ∀ x, 0 ≤ ⟪(f x).val, (g x).val⟫_ℝ) :
    f.Homotopy g := by
  let V : C(I × X, W) := ⟨fun z ↦
    (1 - (z.1 : ℝ)) • (f z.2).val + (z.1 : ℝ) • (g z.2).val, by
      have ht : Continuous (fun z : I × X ↦ (z.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      have hf : Continuous (fun z : I × X ↦ (f z.2).val) :=
        continuous_subtype_val.comp (f.continuous.comp continuous_snd)
      have hg : Continuous (fun z : I × X ↦ (g z.2).val) :=
        continuous_subtype_val.comp (g.continuous.comp continuous_snd)
      exact ((continuous_const.sub ht).smul hf).add (ht.smul hg)⟩
  let H := normalizedSphereMap V (fun z ↦ segment_ne_zero (f z.2) (g z.2) (h z.2) z.1)
  refine { toContinuousMap := H, map_zero_left := ?_, map_one_left := ?_ }
  · intro x
    apply Subtype.ext
    change NormedSpace.normalize ((1 - (0 : ℝ)) • (f x).val + (0 : ℝ) • (g x).val) = (f x).val
    rw [sub_zero, one_smul, zero_smul, add_zero]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp (f x).property)
  · intro x
    apply Subtype.ext
    change NormedSpace.normalize ((1 - (1 : ℝ)) • (f x).val + (1 : ℝ) • (g x).val) = (g x).val
    rw [sub_self, zero_smul, one_smul, zero_add]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp (g x).property)

end SphereSegment

def blockHomotopy (f : C(P × UnitSphere E, OrthogonalOperators n)) :
    (blockMap (G := G) f).Homotopy (suspendedMap (G := G) f) :=
  nonnegativeHomotopy (blockMap f) (suspendedMap f)
    (fun z ↦ block_suspended_inner_nonnegative f z.1 z.2.val)

theorem block_nullhomotopic_iff_suspended (f : C(P × UnitSphere E, OrthogonalOperators n)) :
    (blockMap (G := G) f).Nullhomotopic ↔ (suspendedMap (G := G) f).Nullhomotopic := by
  constructor
  · rintro ⟨c, ⟨H⟩⟩
    exact ⟨c, ⟨(blockHomotopy f).symm.trans H⟩⟩
  · rintro ⟨c, ⟨H⟩⟩
    exact ⟨c, ⟨(blockHomotopy f).trans H⟩⟩

end Wikipedia.HopfProblem.DegreeCollapse.HopfBlockHomotopy
