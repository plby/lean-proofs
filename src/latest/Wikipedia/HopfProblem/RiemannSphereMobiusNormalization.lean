import Wikipedia.HopfProblem.RiemannSphereMobius

/-!
# Three-point normalization of the analytic Riemann sphere

The cross-ratio map is constructed as a composition of actual affine
biholomorphisms and reciprocal inversion. Its formula away from the pole,
and all three prescribed values, hold in the fixed sphere atlas.
-/

noncomputable section

open Set OnePoint
open scoped ContDiff

namespace Wikipedia.HopfProblem.RiemannSphere

variable (a b c : ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)

include hab hbc in
theorem crossRatioScale_ne_zero : (b - c) / (b - a) ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr hbc) (sub_ne_zero.mpr hab.symm)

include hab hac hbc in
theorem crossRatioResidue_ne_zero : (c - a) * ((b - c) / (b - a)) ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr hac.symm) (crossRatioScale_ne_zero a b c hab hbc)

/-- Normalize three distinct finite points to `0`, `1`, and infinity. -/
def threePointBiholomorph : Biholomorph :=
  ((affineBiholomorph 1 (-c) one_ne_zero).trans reciprocalBiholomorph).trans
    (affineBiholomorph ((c - a) * ((b - c) / (b - a))) ((b - c) / (b - a))
      (crossRatioResidue_ne_zero a b c hab hac hbc))

theorem threePointBiholomorph_coe (z : ℂ) (hz : z ≠ c) :
    threePointBiholomorph a b c hab hac hbc (z : RiemannSphere) =
      ((((z - a) * (b - c)) / ((z - c) * (b - a)) : ℂ) : RiemannSphere) := by
  change affineBiholomorph _ _ _
    (reciprocalBiholomorph (affineBiholomorph 1 (-c) one_ne_zero (z : RiemannSphere))) = _
  simp only [affineBiholomorph_coe, one_mul, ← sub_eq_add_neg,
    reciprocalBiholomorph_apply, reciprocal_coe,
    infinityParametrization_of_ne (sub_ne_zero.mpr hz), affineBiholomorph_coe]
  congr 1
  field_simp
  ring

@[simp] theorem threePointBiholomorph_third :
    threePointBiholomorph a b c hab hac hbc (c : RiemannSphere) = (∞ : RiemannSphere) := by
  change affineBiholomorph _ _ _
    (reciprocalBiholomorph (affineBiholomorph 1 (-c) one_ne_zero (c : RiemannSphere))) = _
  simp

@[simp] theorem threePointBiholomorph_first :
    threePointBiholomorph a b c hab hac hbc (a : RiemannSphere) = ((0 : ℂ) : RiemannSphere) := by
  rw [threePointBiholomorph_coe a b c hab hac hbc a hac]
  simp

@[simp] theorem threePointBiholomorph_second :
    threePointBiholomorph a b c hab hac hbc (b : RiemannSphere) = ((1 : ℂ) : RiemannSphere) := by
  rw [threePointBiholomorph_coe a b c hab hac hbc b hbc]
  congr 1
  field_simp

@[simp] theorem threePointBiholomorph_infty :
    threePointBiholomorph a b c hab hac hbc (∞ : RiemannSphere) =
      (((b - c) / (b - a) : ℂ) : RiemannSphere) := by
  change affineBiholomorph _ _ _
    (reciprocalBiholomorph (affineBiholomorph 1 (-c) one_ne_zero (∞ : RiemannSphere))) = _
  simp

theorem threePointBiholomorph_eq_infty_iff (p : RiemannSphere) :
    threePointBiholomorph a b c hab hac hbc p = (∞ : RiemannSphere) ↔
      p = (c : RiemannSphere) := by
  rw [← threePointBiholomorph_third a b c hab hac hbc]
  exact (threePointBiholomorph a b c hab hac hbc).injective.eq_iff

include hab hac hbc in
/-- The normalized map is an analytic automorphism with the prescribed values
and the literal cross-ratio formula on every finite point other than its pole. -/
theorem exists_three_point_biholomorph :
    ∃ e : Biholomorph,
      e (a : RiemannSphere) = ((0 : ℂ) : RiemannSphere) ∧
      e (b : RiemannSphere) = ((1 : ℂ) : RiemannSphere) ∧
      e (c : RiemannSphere) = (∞ : RiemannSphere) ∧
      ∀ z : ℂ, z ≠ c → e (z : RiemannSphere) =
        ((((z - a) * (b - c)) / ((z - c) * (b - a)) : ℂ) : RiemannSphere) :=
  ⟨threePointBiholomorph a b c hab hac hbc,
    threePointBiholomorph_first a b c hab hac hbc,
    threePointBiholomorph_second a b c hab hac hbc,
    threePointBiholomorph_third a b c hab hac hbc,
    threePointBiholomorph_coe a b c hab hac hbc⟩

end Wikipedia.HopfProblem.RiemannSphere
