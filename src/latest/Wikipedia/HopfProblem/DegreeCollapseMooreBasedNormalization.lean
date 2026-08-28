import Wikipedia.NoExoticSixSphere.JamesSphereMeridianReflection

/-!
# Based Moore homotopies with the original zero-duration identity

Interpolate the two actual durations while retaining a supplied based
homotopy of their normalized paths. The first duration is assumed to
vanish only at the basepoint. At a zero interpolated duration the path
is therefore constant, so the existing timed-family continuity theorem
applies. This gives a based version of the meridian-reversal homotopy.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.MooreBasedNormalization

open NoExoticSixSphere Moore

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {y : Y}
variable (f g : C(X, Loop y))

def duration (u : I × X) : ℝ :=
  (1 - (u.1 : ℝ)) * (f u.2).duration + (u.1 : ℝ) * (g u.2).duration

theorem duration_nonneg (u : I × X) : 0 ≤ duration f g u :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr u.1.property.2) (f u.2).duration_nonneg)
    (mul_nonneg u.1.property.1 (g u.2).duration_nonneg)

theorem duration_continuous : Continuous (duration f g) := by
  have ht : Continuous (fun u : I × X ↦ (u.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  exact ((continuous_const.sub ht).mul
    (Loop.continuous_duration.comp (f.continuous.comp continuous_snd))).add
      (ht.mul (Loop.continuous_duration.comp (g.continuous.comp continuous_snd)))

theorem duration_zero (x : X) : duration f g (0, x) = (f x).duration := by
  change (1 - (0 : ℝ)) * (f x).duration + 0 * (g x).duration = _
  ring

theorem duration_one (x : X) : duration f g (1, x) = (g x).duration := by
  change (1 - (1 : ℝ)) * (f x).duration + 1 * (g x).duration = _
  ring

variable {f g} {x₀ : X}
variable (hf : f x₀ = 1) (hg : g x₀ = 1)
variable (hzero : ∀ x, (f x).duration = 0 → x = x₀)
variable (H : (Loop.normalizationMap.comp f).HomotopyRel
  (Loop.normalizationMap.comp g) {x₀})

include hf hzero in
theorem path_eq_refl_of_duration_zero (u : I × X) (hu : duration f g u = 0) :
    H u = Path.refl y := by
  by_cases ht : u.1 = 1
  · rcases u with ⟨t, x⟩
    change t = 1 at ht
    subst t
    rw [duration_one] at hu
    exact (H.apply_one x).trans (Loop.toPath_eq_refl_of_duration_zero (g x) hu)
  · have ht' : (u.1 : ℝ) < 1 := lt_of_le_of_ne u.1.property.2
      (fun he ↦ ht (Subtype.ext he))
    have hleft := (f u.2).duration_nonneg
    have hright := mul_nonneg u.1.property.1 (g u.2).duration_nonneg
    have hfd : (f u.2).duration = 0 := by
      change (1 - (u.1 : ℝ)) * (f u.2).duration +
        (u.1 : ℝ) * (g u.2).duration = 0 at hu
      nlinarith
    have hx : u.2 = x₀ := hzero u.2 hfd
    have hH := H.eq_fst u.1 (show u.2 ∈ ({x₀} : Set X) from hx)
    change H u = Loop.toPath (f u.2) at hH
    rw [hx, hf, Loop.toPath_one] at hH
    exact hH

def basedHomotopy : f.HomotopyRel g {x₀} where
  toFun u := Loop.timed H (duration f g) (duration_nonneg f g) u
  continuous_toFun := Loop.continuous_timed H H.continuous (duration f g)
    (duration_continuous f g) (duration_nonneg f g)
      (path_eq_refl_of_duration_zero hf hzero H)
  map_zero_left x := Loop.timed_eq_of_duration_eq H (duration f g)
    (duration_nonneg f g) (0, x) (f x) (H.apply_zero x) (duration_zero f g x)
  map_one_left x := Loop.timed_eq_of_duration_eq H (duration f g)
    (duration_nonneg f g) (1, x) (g x) (H.apply_one x) (duration_one f g x)
  prop' t x hx := by
    have he : x = x₀ := hx
    subst x
    have hd : duration f g (t, x₀) = 0 := by
      simp only [duration, hf, hg, Loop.duration_one, mul_zero, add_zero]
    exact (Loop.timed_eq_one_of_zero H (duration f g) (duration_nonneg f g)
      (t, x₀) hd).trans hf.symm

end Wikipedia.HopfProblem.DegreeCollapse.MooreBasedNormalization

namespace Wikipedia.HopfProblem.DegreeCollapse.MeridianBasedReversal

open NoExoticSixSphere JamesSphere MeridianCommutator

theorem reversed_meridians_based (n : ℕ) [NeZero n] (hn : 0 < n) (i : Fin n) :
    (reversedMeridians n).HomotopicRel
      ((meridians n).comp (SmoothCube.reflection n hn i)) {spherePole n} := by
  obtain ⟨H⟩ := reversed_meridian_paths n hn i
  have hf : reversedMeridians n (spherePole n) = 1 := by
    change Moore.Loop.reverse (mooreGenerator n (spherePole n)) = 1
    rw [mooreGenerator_pole, Moore.Loop.reverse_one]
  have hg : ((meridians n).comp (SmoothCube.reflection n hn i)) (spherePole n) = 1 := by
    change mooreGenerator n (SmoothCube.reflection n hn i (spherePole n)) = 1
    rw [SmoothCube.reflection_pole, mooreGenerator_pole]
  refine ⟨MooreBasedNormalization.basedHomotopy hf hg (fun x hx ↦ ?_)
    (H.cast (reversedMeridians_normalization n).symm
      (reflectedMeridians_normalization n hn i).symm)⟩
  exact dist_eq_zero.mp hx

end Wikipedia.HopfProblem.DegreeCollapse.MeridianBasedReversal
