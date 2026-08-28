import Wikipedia.HopfProblem.DegreeCollapseOrthogonalHopfMap

/-!
# The Hopf construction of a null orthogonal family is null

For a constant family the Hopf map factors through the closed ball in
the second variable. Radially contracting that ball gives an explicit
nullhomotopy. Together with the actual parameter homotopy, this proves
nullity for every orthogonal family supplied with a nullhomotopy.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere GLOrthonormalization unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.OrthogonalHopfMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

abbrev Disk (n : ℕ) := Metric.closedBall (0 : Vector n) 1

theorem disk_norm_le (b : Disk n) : ‖b.val‖ ≤ 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using b.property

def capVector (T : OrthogonalOperators n) (b : Vector n) : WithLp 2 (ℝ × Vector n) :=
  WithLp.toLp 2 (1 - 2 * ‖b‖ ^ 2,
    (2 * Real.sqrt (1 - ‖b‖ ^ 2)) • T.val.val b)

theorem capVector_mem_sphere (T : OrthogonalOperators n) (b : Disk n) :
    capVector T b.val ∈ UnitSphere (WithLp 2 (ℝ × Vector n)) := by
  have hn : 0 ≤ 1 - ‖b.val‖ ^ 2 := by
    nlinarith [disk_norm_le b, norm_nonneg b.val]
  have hs : ‖capVector T b.val‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖1 - 2 * ‖b.val‖ ^ 2‖ ^ 2 +
      ‖(2 * Real.sqrt (1 - ‖b.val‖ ^ 2)) • T.val.val b.val‖ ^ 2 = 1
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, T.property,
      Real.sq_sqrt hn]
    ring
  rw [mem_sphere_zero_iff_norm]
  nlinarith [norm_nonneg (capVector T b.val)]

theorem continuous_capVector (T : OrthogonalOperators n) : Continuous (capVector T) := by
  have hs : Continuous (fun b : Vector n ↦ 2 * Real.sqrt (1 - ‖b‖ ^ 2)) :=
    continuous_const.mul ((continuous_const.sub (continuous_norm.pow 2)).sqrt)
  exact (WithLp.prod_continuous_toLp 2 ℝ (Vector n)).comp
    ((continuous_const.sub (continuous_const.mul (continuous_norm.pow 2))).prodMk
      (hs.smul T.val.val.continuous))

def cap (T : OrthogonalOperators n) : C(Disk n, Target n) :=
  ⟨fun b ↦ ⟨capVector T b.val, capVector_mem_sphere T b⟩,
    ((continuous_capVector T).comp continuous_subtype_val).subtype_mk _⟩

omit [NormedSpace ℝ E] in
theorem source_second_norm_le (x : Source E n) : ‖x.val.snd‖ ≤ 1 := by
  have h := source_norms x
  nlinarith [sq_nonneg ‖x.val.fst‖, norm_nonneg x.val.snd]

def shrinkingSecond (t : I) (x : Source E n) : Disk n :=
  ⟨(1 - (t : ℝ)) • x.val.snd, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr t.property.2)]
    exact (mul_le_of_le_one_left (norm_nonneg x.val.snd)
      (by linarith [t.property.1])).trans (source_second_norm_le x)⟩

omit [NormedSpace ℝ E] in
theorem continuous_shrinkingSecond :
    Continuous (fun z : I × Source E n ↦ shrinkingSecond z.1 z.2) := by
  apply Continuous.subtype_mk
  have ht : Continuous (fun z : I × Source E n ↦ 1 - (z.1 : ℝ)) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  have hx : Continuous (fun z : I × Source E n ↦ z.2.val.snd) :=
    (WithLp.continuous_snd 2 E (Vector n)).comp
      (continuous_subtype_val.comp continuous_snd)
  exact ht.smul hx

theorem cap_shrinking_zero (T : OrthogonalOperators n) (x : Source E n) :
    cap T (shrinkingSecond 0 x) = sphereMap (ContinuousMap.const (UnitSphere E) T) x := by
  apply Subtype.ext
  rw [sphereMap_val]
  simp only [ContinuousMap.const_apply]
  rw [RadialSphereAction.value_const]
  have ha : Real.sqrt (1 - ‖x.val.snd‖ ^ 2) = ‖x.val.fst‖ := by
    have h := source_norms x
    have he : 1 - ‖x.val.snd‖ ^ 2 = ‖x.val.fst‖ ^ 2 := by linarith
    rw [he, Real.sqrt_sq (norm_nonneg _)]
  change capVector T ((1 - (0 : ℝ)) • x.val.snd) = _
  rw [sub_zero, one_smul]
  unfold capVector
  rw [ha, smul_smul]
  congr 2
  nlinarith [source_norms x]

omit [NormedSpace ℝ E] in
theorem cap_shrinking_one (T : OrthogonalOperators n) (x : Source E n) :
    cap T (shrinkingSecond 1 x) = pole n := by
  apply Subtype.ext
  change capVector T ((1 - (1 : ℝ)) • x.val.snd) = WithLp.toLp 2 (1, 0)
  simp only [sub_self, zero_smul, capVector, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero, map_zero, smul_zero]

def constantHomotopy (T : OrthogonalOperators n) :
    (sphereMap (ContinuousMap.const (UnitSphere E) T)).Homotopy
      (ContinuousMap.const (Source E n) (pole n)) where
  toFun z := cap T (shrinkingSecond z.1 z.2)
  continuous_toFun := (cap T).continuous.comp continuous_shrinkingSecond
  map_zero_left := cap_shrinking_zero T
  map_one_left := cap_shrinking_one T

def nullhomotopy {f : C(UnitSphere E, OrthogonalOperators n)} (T : OrthogonalOperators n)
    (H : f.Homotopy (ContinuousMap.const _ T)) :
    (sphereMap f).Homotopy (ContinuousMap.const (Source E n) (pole n)) :=
  (mapHomotopy H).trans (constantHomotopy T)

theorem nullhomotopic_of_family {f : C(UnitSphere E, OrthogonalOperators n)}
    (T : OrthogonalOperators n) (h : f.Homotopic (ContinuousMap.const _ T)) :
    (sphereMap f).Homotopic (ContinuousMap.const (Source E n) (pole n)) := by
  obtain ⟨H⟩ := h
  exact ⟨nullhomotopy T H⟩

end Wikipedia.HopfProblem.DegreeCollapse.OrthogonalHopfMap
