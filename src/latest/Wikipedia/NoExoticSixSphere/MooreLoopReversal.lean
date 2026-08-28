import Wikipedia.NoExoticSixSphere.MooreLoopMultiplication

/-!
# Continuous reversal of actual Moore loops

Reverse the real-parameter curve at its original duration. This is a
continuous involution, preserves the exact zero-duration identity, and
reverses the order of concatenation. Normalization gives the actual
native path reversal. No strict inverse law for Moore loops is asserted.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.Moore.Loop

variable {Y : Type*} [TopologicalSpace Y] {y₀ : Y}

def reverse (p : Loop y₀) : Loop y₀ :=
  ⟨(p.duration, ⟨fun t ↦ p.curve (p.duration - t),
      p.curve.continuous.comp (continuous_const.sub continuous_id)⟩),
    p.duration_nonneg,
    fun t ht ↦ p.curve_of_duration_le _ (by linarith),
    fun t ht ↦ p.curve_of_nonpos _ (by linarith)⟩

theorem duration_reverse (p : Loop y₀) : (reverse p).duration = p.duration := rfl

theorem curve_reverse (p : Loop y₀) (t : ℝ) :
    (reverse p).curve t = p.curve (p.duration - t) := rfl

theorem continuous_reverse : Continuous (reverse : Loop y₀ → Loop y₀) := by
  have hc : Continuous (fun p : Loop y₀ ↦ (reverse p).curve) :=
    ContinuousMap.continuous_of_continuous_uncurry _
      (continuous_curve_apply _ continuous_fst
        (fun u : Loop y₀ × ℝ ↦ u.1.duration - u.2)
        ((continuous_duration.comp continuous_fst).sub continuous_snd))
  exact (continuous_duration.prodMk hc).subtype_mk _

theorem reverse_one : reverse (1 : Loop y₀) = 1 :=
  eq_one_of_duration_zero _ rfl

theorem reverse_reverse (p : Loop y₀) : reverse (reverse p) = p := by
  apply ext
  · rfl
  · intro t
    change p.curve (p.duration - (p.duration - t)) = p.curve t
    congr 1
    ring

theorem reverse_mul (p q : Loop y₀) : reverse (p * q) = reverse q * reverse p := by
  apply ext
  · change p.duration + q.duration = q.duration + p.duration
    exact add_comm _ _
  · intro t
    rw [curve_reverse, duration_mul, curve_mul, curve_mul,
      duration_reverse, curve_reverse, curve_reverse]
    rcases lt_trichotomy t q.duration with ht | rfl | ht
    · rw [if_neg (by linarith : ¬ p.duration + q.duration - t ≤ p.duration), if_pos ht.le]
      congr 1
      ring
    · rw [add_sub_cancel_right, if_pos le_rfl, if_pos le_rfl, sub_self,
        curve_duration, curve_zero]
    · rw [if_pos (by linarith : p.duration + q.duration - t ≤ p.duration),
        if_neg (not_le.mpr ht)]
      congr 1
      ring

theorem toPath_reverse (p : Loop y₀) : toPath (reverse p) = (toPath p).symm := by
  apply Path.ext
  funext t
  change p.curve (p.duration - p.duration * (t : ℝ)) =
    p.curve (p.duration * (1 - (t : ℝ)))
  congr 1
  ring

def reverseMap : C(Loop y₀, Loop y₀) := ⟨reverse, continuous_reverse⟩

end NoExoticSixSphere.Moore.Loop
