import StackExchange.Puzzling139335.N7Geometry.Bounds

/-!
# Matrix parameters forced by the two gap endpoints

The hypotheses are coordinate inequalities obtained from actual source
points.  They select the two possible singleton placements without an
angle or sector assumption.
-/

namespace Puzzling139335.N7.SingletonPlacement

open N7Geometry

private theorem direct_relation {a t : ℝ}
    (hR : 0 ≤ t / 2 - a * c)
    (hL : c * (t * c - a / 2) ≤ (a * c + t / 2) / 2) :
    t / 2 = a * c := by
  have hcircle := congrArg (fun x : ℝ => t * x) c_sq
  have hupper : t / 2 ≤ a * c := by
    nlinarith only [hL, hcircle]
  exact le_antisymm hupper (by linarith only [hR])

/-- The direct matrix is rotation through sixty degrees. -/
theorem direct_parameters {a t : ℝ}
    (hunit : a ^ 2 + t ^ 2 = 1)
    (hxL : 0 ≤ a * c + t / 2)
    (hyR : 0 ≤ t / 2 - a * c)
    (hwL : c * (t * c - a / 2) ≤ (a * c + t / 2) / 2) :
    a = (1 / 2 : ℝ) ∧ t = c := by
  have hrel := direct_relation hyR hwL
  have hac : 0 ≤ a * c := by linarith only [hxL, hrel]
  have ha : 0 ≤ a := (mul_nonneg_iff_of_pos_right c_pos).mp hac
  have hsq := congrArg (fun x : ℝ => x ^ 2) hrel
  have hcircle := congrArg (fun x : ℝ => a ^ 2 * x) c_sq
  have haq : a ^ 2 = (1 / 2 : ℝ) ^ 2 := by
    nlinarith only [hunit, hsq, hcircle]
  have hae : a = (1 / 2 : ℝ) :=
    (sq_eq_sq₀ ha (by norm_num)).mp haq
  refine ⟨hae, ?_⟩
  rw [hae] at hrel
  linarith only [hrel]

private theorem reversing_relation {a t : ℝ}
    (hL : 0 ≤ a / 2 - t * c)
    (hR : c * (a * c - t / 2) ≤ (a / 2 + t * c) / 2) :
    a / 2 = t * c := by
  have hcircle := congrArg (fun x : ℝ => a * x) c_sq
  have hupper : a / 2 ≤ t * c := by
    nlinarith only [hR, hcircle]
  exact le_antisymm hupper (by linarith only [hL])

/-- The reversing matrix exchanges the coordinates of that rotation. -/
theorem reversing_parameters {a t : ℝ}
    (hunit : a ^ 2 + t ^ 2 = 1)
    (hxR : 0 ≤ a / 2 + t * c)
    (hyL : 0 ≤ a / 2 - t * c)
    (hwR : c * (a * c - t / 2) ≤ (a / 2 + t * c) / 2) :
    a = c ∧ t = (1 / 2 : ℝ) := by
  have hrel := reversing_relation hyL hwR
  have htc : 0 ≤ t * c := by linarith only [hxR, hrel]
  have ht : 0 ≤ t := (mul_nonneg_iff_of_pos_right c_pos).mp htc
  have hsq := congrArg (fun x : ℝ => x ^ 2) hrel
  have hcircle := congrArg (fun x : ℝ => t ^ 2 * x) c_sq
  have htq : t ^ 2 = (1 / 2 : ℝ) ^ 2 := by
    nlinarith only [hunit, hsq, hcircle]
  have hte : t = (1 / 2 : ℝ) :=
    (sq_eq_sq₀ ht (by norm_num)).mp htq
  refine ⟨?_, hte⟩
  rw [hte] at hrel
  linarith only [hrel]

end Puzzling139335.N7.SingletonPlacement
