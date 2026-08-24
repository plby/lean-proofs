/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.Core

/-!
# Erdős 360: lower-bound analytic endgame

This scratch module isolates the exact interface between the still-finite
monochromatic subset-sum argument and the already formalized analytic scale.
The finite argument only has to force the target for the natural floor of a
positive constant times `resolutionScale`.
-/

namespace Erdos360

open Filter

/-- If an integer-valued number of colors forces the target and its successor
dominates a real scale, then the extremal function dominates that scale. -/
lemma eventual_f_lower_of_eventually_forces
    (r : ℕ → ℕ) (g : ℕ → ℝ)
    (hforce : ∀ᶠ n : ℕ in atTop, ForcesTarget n (r n))
    (hsize : ∀ᶠ n : ℕ in atTop, g n ≤ (r n : ℝ) + 1) :
    ∀ᶠ n : ℕ in atTop, g n ≤ (f n : ℝ) := by
  filter_upwards [hforce, hsize, eventually_gt_atTop 0] with n hnforce hnsize hn
  have hrlt : r n < f n :=
    (forcesTarget_iff_lt_f hn).mp hnforce
  have hrsucc : r n + 1 ≤ f n := Nat.succ_le_iff.mpr hrlt
  have hrsuccReal : (r n : ℝ) + 1 ≤ (f n : ℝ) := by
    exact_mod_cast hrsucc
  exact hnsize.trans hrsuccReal

/-- The canonical finite statement needed for the diagonal lower bound:
eventually, every coloring with the natural floor of `c * resolutionScale n`
colors has a monochromatic subset summing to `n`. -/
def EventuallyForcesResolutionFloor (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ForcesTarget n ⌊c * resolutionScale n⌋₊

/-- The floor in `EventuallyForcesResolutionFloor` costs no multiplicative
constant: strict forcing gives `floor(c * scale) + 1 ≤ f(n)`. -/
lemma eventually_resolution_lower_of_forces_floor {c : ℝ}
    (hforce : EventuallyForcesResolutionFloor c) :
    ∀ᶠ n : ℕ in atTop,
      c * resolutionScale n ≤ (f n : ℝ) := by
  apply eventual_f_lower_of_eventually_forces
      (fun n ↦ ⌊c * resolutionScale n⌋₊)
      (fun n ↦ c * resolutionScale n) hforce
  filter_upwards with n
  exact (Nat.lt_floor_add_one (c * resolutionScale n)).le

/-- Once the finite forcing theorem is supplied at one positive constant,
the existing upper bound in `Core` completes the full resolution. -/
theorem resolution_of_exists_eventually_forces_floor
    (hlower : ∃ c : ℝ, 0 < c ∧ EventuallyForcesResolutionFloor c) :
    Resolution := by
  obtain ⟨c, hc, hforce⟩ := hlower
  obtain ⟨C, hC, hupper⟩ := exists_resolution_upper
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [eventually_resolution_lower_of_forces_floor hforce,
    hupper] with n hnLower hnUpper
  exact ⟨hnLower, hnUpper⟩

/-- A formulation without floors, convenient when the finite proof naturally
handles every integral number of colors up to a real threshold. -/
lemma eventually_forces_floor_of_threshold {c : ℝ}
    (hc : 0 ≤ c)
    (hthreshold : ∀ᶠ n : ℕ in atTop, ∀ r : ℕ,
      (r : ℝ) ≤ c * resolutionScale n → ForcesTarget n r) :
    EventuallyForcesResolutionFloor c := by
  have hscale : ∀ᶠ n : ℕ in atTop, 0 ≤ resolutionScale n :=
    resolutionScale_tendsto_atTop.eventually (eventually_ge_atTop 0)
  filter_upwards [hthreshold, hscale] with n hn hnscale
  exact hn _ (Nat.floor_le (mul_nonneg hc hnscale))

end Erdos360
