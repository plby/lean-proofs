import Wikipedia.NoExoticSixSphere.OrthogonalLocalSegment
import Wikipedia.NoExoticSixSphere.PrefixCoordinates

/-!
# A continuous prefix-replacement homotopy

At stage `s`, replace the prefix ending at `s` by its logarithmic exponential
segment and leave the remaining tail unchanged. This is a genuine jointly
continuous homotopy, including at the zero-length prefix. Both endpoints and
all stationary parameters stay fixed. The energy comparison is separate.
-/

open Set unitInterval

namespace NoExoticSixSphere.OrthogonalExponential.LocalSegment

open GLOrthonormalization CayleyTransform PrefixCoordinates

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, OrthogonalOperators n))
  (h : ∀ p : I × X, (H (0, p.2))⁻¹ * H p ∈ (logarithmChart n).source)

noncomputable def prefixReplacement : C(I × (I × X), OrthogonalOperators n) where
  toFun q := H (0, q.2.2) * exp (straightening (logs H h) (logs_zero H h) q)
  continuous_toFun :=
    (H.continuous.comp (continuous_const.prodMk (continuous_snd.comp continuous_snd))).mul
      (contMDiff_exp.continuous.comp (straightening (logs H h) (logs_zero H h)).continuous)

theorem prefixReplacement_prefix (s t : I) (x : X) (ht : t ≤ s) :
    prefixReplacement H h (s, (t, x)) =
      H (0, x) * exp (((t : ℝ) / (s : ℝ)) • logs H h (s, x)) := by
  change H (0, x) * exp (straightening (logs H h) (logs_zero H h) (s, (t, x))) = _
  rw [straightening_prefix _ _ s t x ht]

theorem prefixReplacement_tail (s t : I) (x : X) (ht : s ≤ t) :
    prefixReplacement H h (s, (t, x)) = H (t, x) := by
  change H (0, x) * exp (straightening (logs H h) (logs_zero H h) (s, (t, x))) = _
  rw [straightening_tail _ _ s t x ht, exp_logs,
    ← mul_assoc, mul_inv_cancel, one_mul]

theorem prefixReplacement_zero (p : I × X) : prefixReplacement H h (0, p) = H p :=
  prefixReplacement_tail H h 0 p.1 p.2 p.1.2.1

theorem prefixReplacement_one (p : I × X) :
    prefixReplacement H h (1, p) = segment H h p := by
  rw [prefixReplacement_prefix H h 1 p.1 p.2 p.1.2.2]
  change H (0, p.2) * exp (((p.1 : ℝ) / 1) • logs H h (1, p.2)) = _
  rw [div_one]
  rfl

theorem prefixReplacement_time_zero (s : I) (x : X) :
    prefixReplacement H h (s, (0, x)) = H (0, x) := by
  rw [prefixReplacement_prefix H h s 0 x s.2.1]
  change H (0, x) * exp (((0 : ℝ) / (s : ℝ)) • logs H h (s, x)) = _
  rw [zero_div, zero_smul, exp_zero, mul_one]

theorem prefixReplacement_time_one (s : I) (x : X) :
    prefixReplacement H h (s, (1, x)) = H (1, x) :=
  prefixReplacement_tail H h s 1 x s.2.2

theorem prefixReplacement_stationary (s t : I) (x : X)
    (hx : ∀ u, H (u, x) = H (0, x)) : prefixReplacement H h (s, (t, x)) = H (t, x) := by
  change H (0, x) * exp (coefficient s t • logs H h (endingTime s t, x)) = _
  rw [logs_of_stationary H h x hx, smul_zero, exp_zero, mul_one, hx t]

noncomputable def prefixHomotopyRel (S : Set X)
    (hS : ∀ x ∈ S, ∀ t, H (t, x) = H (0, x)) :
    H.HomotopyRel (segment H h) {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 ∈ S} where
  toContinuousMap := prefixReplacement H h
  map_zero_left := prefixReplacement_zero H h
  map_one_left := prefixReplacement_one H h
  prop' s p hp := by
    rcases p with ⟨t, x⟩
    rcases hp with ht | ht | hx
    · change t = 0 at ht
      subst t
      exact prefixReplacement_time_zero H h s x
    · change t = 1 at ht
      subst t
      exact prefixReplacement_time_one H h s x
    · exact prefixReplacement_stationary H h s t x (hS x hx)

end NoExoticSixSphere.OrthogonalExponential.LocalSegment
