import Wikipedia.NoExoticSixSphere.SignedSphereCollar

/-!
# Injectivity of the actual signed radial collar

A nonzero height coefficient determines the radius. An injective original
sphere map determines the radial direction. Together they make the signed
collar injective on the outer half-annulus; immersion alone is not used as
a substitute for injectivity.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SignedSphereCollar

open GLOrthonormalization

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (b : Sphere n) (f : Sphere n → F) (c slope : ℝ)

theorem injOn_outer_half (hslope : slope ≠ 0) (hi : Injective f) :
    InjOn (map b f c slope) {x : Vector (n + 1) | 1 / 2 ≤ ‖x‖} := by
  have hradial (x : Vector (n + 1)) (hx : 1 / 2 ≤ ‖x‖) :
      ‖x‖ • (SphereRadialRetraction.retract b x).val = x := by
    have hne : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx
      norm_num at hx
    simp only [SphereRadialRetraction.retract, dif_neg hne]
    exact NormedSpace.norm_smul_normalize x
  have hmap (x : Vector (n + 1)) (hx : 1 / 2 ≤ ‖x‖) :
      map b f c slope x =
        (c + slope * (‖x‖ ^ 2 - 1), f (SphereRadialRetraction.retract b x)) := by
    calc
      _ = map b f c slope (‖x‖ • (SphereRadialRetraction.retract b x).val) :=
        congrArg (map b f c slope) (hradial x hx).symm
      _ = _ := map_radial b f c slope ‖x‖ hx (SphereRadialRetraction.retract b x)
  intro x hx y hy hxy
  rw [hmap x hx, hmap y hy] at hxy
  have hh := congrArg Prod.fst hxy
  have hs : ‖x‖ ^ 2 = ‖y‖ ^ 2 := by
    have hm : slope * (‖x‖ ^ 2 - 1) = slope * (‖y‖ ^ 2 - 1) := add_left_cancel hh
    have he := mul_left_cancel₀ hslope hm
    linarith
  have hn : ‖x‖ = ‖y‖ := (sq_eq_sq₀ (norm_nonneg x) (norm_nonneg y)).mp hs
  have hd := hi (congrArg Prod.snd hxy)
  calc
    x = ‖x‖ • (SphereRadialRetraction.retract b x).val := (hradial x hx).symm
    _ = ‖y‖ • (SphereRadialRetraction.retract b y).val := by rw [hn, hd]
    _ = y := hradial y hy

end NoExoticSixSphere.SignedSphereCollar
