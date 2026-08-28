import Wikipedia.NoExoticSixSphere.RealIntervalProgress
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# Making a small zero-avoiding perturbation relative

Blend with a nearby nonzero map only where the original vector is small.
The result stays nonzero, agrees with the original map away from zero, and
the joining homotopy has the same uniform approximation bound.
-/

open Set unitInterval

namespace NoExoticSixSphere.ZeroAvoidanceCutoff

open RealIntervalProgress

variable {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def weight (f : C(X, F)) (ε : ℝ) : C(X, ℝ) :=
  ⟨fun x ↦ 1 - progress ε (2 * ε) ‖f x‖,
    continuous_const.sub ((continuous_progress ε (2 * ε)).comp f.continuous.norm)⟩

omit [NormedSpace ℝ F] in
theorem weight_bounds (f : C(X, F)) (ε : ℝ) (x : X) :
    0 ≤ weight f ε x ∧ weight f ε x ≤ 1 := by
  have hp : progress ε (2 * ε) ‖f x‖ ∈ Icc (0 : ℝ) 1 :=
    (projIcc (0 : ℝ) 1 zero_le_one ((‖f x‖ - ε) / (2 * ε - ε))).property
  change 0 ≤ 1 - progress ε (2 * ε) ‖f x‖ ∧ 1 - progress ε (2 * ε) ‖f x‖ ≤ 1
  constructor <;> linarith [hp.1, hp.2]

omit [NormedSpace ℝ F] in
theorem weight_small (f : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X} (hx : ‖f x‖ ≤ ε) :
    weight f ε x = 1 := by
  simp only [weight, ContinuousMap.coe_mk, progress_before (by linarith : ε ≤ 2 * ε) hx,
    sub_zero]

omit [NormedSpace ℝ F] in
theorem weight_large (f : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X} (hx : 2 * ε ≤ ‖f x‖) :
    weight f ε x = 0 := by
  simp only [weight, ContinuousMap.coe_mk, progress_after (by linarith : ε < 2 * ε) hx,
    sub_self]

noncomputable def blend (f g : C(X, F)) (ε : ℝ) : C(X, F) :=
  ⟨fun x ↦ f x + weight f ε x • (g x - f x),
    f.continuous.add ((weight f ε).continuous.smul (g.continuous.sub f.continuous))⟩

theorem blend_small (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X} (hx : ‖f x‖ ≤ ε) :
    blend f g ε x = g x := by
  change f x + weight f ε x • (g x - f x) = g x
  rw [weight_small f ε hε hx, one_smul]
  abel

theorem blend_large (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X} (hx : 2 * ε ≤ ‖f x‖) :
    blend f g ε x = f x := by
  change f x + weight f ε x • (g x - f x) = f x
  rw [weight_large f ε hε hx, zero_smul, add_zero]

theorem dist_blend_le (f g : C(X, F)) (ε : ℝ) (x : X) :
    dist (blend f g ε x) (f x) ≤ dist (g x) (f x) := by
  simp only [dist_eq_norm]
  change ‖f x + weight f ε x • (g x - f x) - f x‖ ≤ ‖g x - f x‖
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_bounds f ε x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (weight_bounds f ε x).2

theorem blend_ne_zero (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε)
    (hg : ∀ x, g x ≠ 0) (hclose : ∀ x, dist (g x) (f x) < ε) (x : X) :
    blend f g ε x ≠ 0 := by
  by_cases hx : ‖f x‖ ≤ ε
  · rw [blend_small f g ε hε hx]
    exact hg x
  · intro hz
    have hh := (dist_blend_le f g ε x).trans_lt (hclose x)
    rw [hz, dist_zero_left] at hh
    exact hx hh.le

noncomputable def homotopy (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε) :
    ContinuousMap.HomotopyRel f (blend f g ε) {x | 2 * ε ≤ ‖f x‖} where
  toFun p := f p.2 + (p.1 : ℝ) • (blend f g ε p.2 - f p.2)
  continuous_toFun := (f.continuous.comp continuous_snd).add
    ((continuous_subtype_val.comp continuous_fst).smul
      (((blend f g ε).continuous.comp continuous_snd).sub (f.continuous.comp continuous_snd)))
  map_zero_left x := by simp
  map_one_left x := by
    change f x + (1 : ℝ) • (blend f g ε x - f x) = blend f g ε x
    rw [one_smul]
    abel
  prop' t x hx := by
    change f x + (t : ℝ) • (blend f g ε x - f x) = f x
    rw [blend_large f g ε hε hx, sub_self, smul_zero, add_zero]

theorem homotopy_dist_lt (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε)
    (hclose : ∀ x, dist (g x) (f x) < ε) (t : I) (x : X) :
    dist (homotopy f g ε hε (t, x)) (f x) < ε := by
  rw [dist_eq_norm]
  change ‖f x + (t : ℝ) • (blend f g ε x - f x) - f x‖ < ε
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
  calc
    (t : ℝ) * ‖blend f g ε x - f x‖ ≤ ‖blend f g ε x - f x‖ :=
      mul_le_of_le_one_left (norm_nonneg _) t.2.2
    _ ≤ dist (g x) (f x) := by
      simpa only [dist_eq_norm] using dist_blend_le f g ε x
    _ < ε := hclose x

end NoExoticSixSphere.ZeroAvoidanceCutoff
