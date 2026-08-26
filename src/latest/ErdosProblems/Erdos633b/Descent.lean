import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.NormNum

/-!
# Local obstructions for the arithmetic descent

The lemmas here are proved residue obstructions, not assumed rank or torsion
classifications. The global descent is still under development.
-/

namespace Erdos633b

theorem negative_cover_mod_three :
    ∀ u v w : ZMod 3, w ^ 2 = -u ^ 4 + 10 * u ^ 2 * v ^ 2 - v ^ 4 →
      u = 0 ∧ v = 0 := by
  decide

/-- The negative square-class covering for the curve with coefficients `(10, 1)`
has no primitive integral point. -/
theorem negative_cover_no_primitive (u v w : ℤ) (hc : IsCoprime u v) :
    w ^ 2 ≠ -u ^ 4 + 10 * u ^ 2 * v ^ 2 - v ^ 4 := by
  intro h
  have hz : (w : ZMod 3) ^ 2 = -(u : ZMod 3) ^ 4 +
      10 * (u : ZMod 3) ^ 2 * (v : ZMod 3) ^ 2 - (v : ZMod 3) ^ 4 := by
    simpa using congrArg (Int.castRingHom (ZMod 3)) h
  obtain ⟨hu, hv⟩ := negative_cover_mod_three u v w hz
  have hu' : (3 : ℤ) ∣ u := (ZMod.intCast_zmod_eq_zero_iff_dvd u 3).mp hu
  have hv' : (3 : ℤ) ∣ v := (ZMod.intCast_zmod_eq_zero_iff_dvd v 3).mp hv
  obtain ⟨a, b, hab⟩ := hc
  have hdiv : (3 : ℤ) ∣ 1 := by
    rw [← hab]
    exact dvd_add (dvd_mul_of_dvd_right hu' a) (dvd_mul_of_dvd_right hv' b)
  norm_num at hdiv

end Erdos633b
