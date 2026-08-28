import Mathlib.Topology.Path
import Mathlib.Topology.Order.OrderClosed

/-!
# A continuous connecting curve with prescribed endpoint germs

Concatenate paths through the supplied endpoint values and paste to the two
given real curves. The paste points lie strictly inside the unit interval,
so the original curves are retained on whole endpoint neighborhoods.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.CurveImmersion

variable {N : Type*} [TopologicalSpace N]

/-- Prescribed continuous real curves can be joined without changing their endpoint germs. -/
theorem exists_continuous_curve_with_endpoint_germs (a b : C(ℝ, N))
    (γ : Path (a 0) (b 1)) :
    ∃ f : C(ℝ, N), EqOn f a (Iic (1 / 4 : ℝ)) ∧ EqOn f b (Ici (3 / 4 : ℝ)) := by
  classical
  let α : Path (a (1 / 4)) (a 0) := Path.ofLine (f := fun t : ℝ => a ((1 - t) / 4))
    ((a.continuous.comp ((continuous_const.sub continuous_id).div_const 4)).continuousOn)
    (by norm_num) (by norm_num)
  let β : Path (b 1) (b (3 / 4)) := Path.ofLine (f := fun t : ℝ => b (1 - t / 4))
    ((b.continuous.comp (continuous_const.sub (continuous_id.div_const 4))).continuousOn)
    (by norm_num) (by norm_num)
  let η := α.trans (γ.trans β)
  let mid : ℝ → N := fun t => η.extend (2 * t - 1 / 2)
  have hmid : Continuous mid := η.continuous_extend.comp
    ((continuous_const.mul continuous_id).sub continuous_const)
  have hm₀ : mid (1 / 4) = a (1 / 4) := by
    change η.extend (2 * (1 / 4) - 1 / 2) = _
    norm_num
  have hm₁ : mid (3 / 4) = b (3 / 4) := by
    change η.extend (2 * (3 / 4) - 1 / 2) = _
    norm_num
  let right : ℝ → N := fun t => if t ≤ 3 / 4 then mid t else b t
  have hr : Continuous right := hmid.if_le b.continuous continuous_id continuous_const
    (fun t ht => ht ▸ hm₁)
  let f : ℝ → N := fun t => if t ≤ 1 / 4 then a t else right t
  have hf : Continuous f := a.continuous.if_le hr continuous_id continuous_const (by
    intro t ht
    subst t
    simpa only [right, if_pos (show (1 / 4 : ℝ) ≤ 3 / 4 by norm_num)] using hm₀.symm)
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro t ht
    exact if_pos ht
  · intro t ht
    change 3 / 4 ≤ t at ht
    change (if t ≤ 1 / 4 then a t else if t ≤ 3 / 4 then mid t else b t) = b t
    rw [if_neg (show ¬t ≤ 1 / 4 by linarith)]
    by_cases hte : t = 3 / 4
    · subst t
      simpa only [if_pos le_rfl] using hm₁
    · exact if_neg (by intro h; exact hte (le_antisymm h ht))

end Wikipedia.SmoothSixDPoincare.CurveImmersion
