import Wikipedia.NoExoticSixSphere.MooreLoopReversal

/-!
# Jointly continuous cancellation of a Moore loop and its reverse

The cancellation curve traverses the initial segment of the original
loop up to time (1-s)L and retraces it. Its actual duration is 2(1-s)L.
The min formula is continuous even when this duration is zero and fixes
the exact Moore identity. Both cancellation orders are therefore actual
based homotopies, not additional algebraic inverse laws.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.Moore.Loop

variable {Y : Type*} [TopologicalSpace Y] {y₀ : Y}

def retraceDuration (u : I × Loop y₀) : ℝ := 2 * (1 - (u.1 : ℝ)) * u.2.duration

theorem retraceDuration_nonneg (u : I × Loop y₀) : 0 ≤ retraceDuration u :=
  mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr u.1.property.2)) u.2.duration_nonneg

theorem continuous_retraceDuration : Continuous (retraceDuration (y₀ := y₀)) :=
  (continuous_const.mul
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst))).mul
      (continuous_duration.comp continuous_snd)

def retrace (u : I × Loop y₀) : Loop y₀ :=
  ⟨(retraceDuration u, ⟨fun t ↦ u.2.curve (min t (retraceDuration u - t)),
      u.2.curve.continuous.comp (continuous_id.min (continuous_const.sub continuous_id))⟩),
    retraceDuration_nonneg u,
    fun _ ht ↦ u.2.curve_of_nonpos _ ((min_le_left _ _).trans ht),
    fun _ ht ↦ u.2.curve_of_nonpos _ ((min_le_right _ _).trans (sub_nonpos.mpr ht))⟩

theorem retrace_duration (u : I × Loop y₀) : (retrace u).duration = retraceDuration u := rfl

theorem retrace_curve (u : I × Loop y₀) (t : ℝ) :
    (retrace u).curve t = u.2.curve (min t (retraceDuration u - t)) := rfl

theorem continuous_retrace : Continuous (retrace : I × Loop y₀ → Loop y₀) := by
  have hc : Continuous (fun u : I × Loop y₀ ↦ (retrace u).curve) :=
    ContinuousMap.continuous_of_continuous_uncurry _
      (continuous_curve_apply (fun u : (I × Loop y₀) × ℝ ↦ u.1.2)
        (continuous_snd.comp continuous_fst)
        (fun u ↦ min u.2 (retraceDuration u.1 - u.2))
        (continuous_snd.min ((continuous_retraceDuration.comp continuous_fst).sub continuous_snd)))
  exact (continuous_retraceDuration.prodMk hc).subtype_mk _

theorem retrace_zero (p : Loop y₀) : retrace (0, p) = p * reverse p := by
  have hd : retraceDuration (0, p) = 2 * p.duration := by
    simp [retraceDuration]
  apply ext
  · rw [retrace_duration, hd, duration_mul, duration_reverse]
    ring
  · intro t
    rw [retrace_curve, hd, curve_mul, curve_reverse]
    by_cases ht : t ≤ p.duration
    · rw [if_pos ht, min_eq_left (by linarith : t ≤ 2 * p.duration - t)]
    · rw [if_neg ht, min_eq_right (by linarith : 2 * p.duration - t ≤ t)]
      congr 1
      ring

theorem retrace_one (p : Loop y₀) : retrace (1, p) = 1 := by
  apply eq_one_of_duration_zero
  change 2 * (1 - (1 : ℝ)) * p.duration = 0
  rw [sub_self, mul_zero, zero_mul]

theorem retrace_identity (s : I) : retrace (s, (1 : Loop y₀)) = 1 := by
  apply eq_one_of_duration_zero
  change 2 * (1 - (s : ℝ)) * (1 : Loop y₀).duration = 0
  rw [duration_one, mul_zero]

def selfReverseMap : C(Loop y₀, Loop y₀) :=
  ⟨fun p ↦ p * reverse p, continuous_id.mul continuous_reverse⟩

theorem selfReverseMap_one : selfReverseMap (1 : Loop y₀) = 1 := by
  change (1 : Loop y₀) * reverse 1 = 1
  rw [reverse_one, mul_one]

def cancellationHomotopy : (selfReverseMap (y₀ := y₀)).HomotopyRel
    (ContinuousMap.const _ 1) {1} where
  toFun := retrace
  continuous_toFun := continuous_retrace
  map_zero_left := retrace_zero
  map_one_left := retrace_one
  prop' := by
    intro s p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact (retrace_identity s).trans selfReverseMap_one.symm

def reverseSelfMap : C(Loop y₀, Loop y₀) :=
  ⟨fun p ↦ reverse p * p, continuous_reverse.mul continuous_id⟩

def leftCancellationHomotopy : (reverseSelfMap (y₀ := y₀)).HomotopyRel
    (ContinuousMap.const _ 1) {1} where
  toFun u := retrace (u.1, reverse u.2)
  continuous_toFun := continuous_retrace.comp
    (continuous_fst.prodMk (continuous_reverse.comp continuous_snd))
  map_zero_left p := by
    change retrace (0, reverse p) = reverse p * p
    rw [retrace_zero, reverse_reverse]
  map_one_left p := retrace_one (reverse p)
  prop' := by
    intro s p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change retrace (s, reverse (1 : Loop y₀)) = reverse 1 * 1
    rw [reverse_one, retrace_identity, mul_one]

end NoExoticSixSphere.Moore.Loop
