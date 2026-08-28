import Wikipedia.NoExoticSixSphere.Equator
import Wikipedia.NoExoticSixSphere.SphereRadialRetraction

/-!
# A smooth fold of the actual sphere along its equator

For a unit pole `v`, the polynomial map `x ↦ 2 ⟪v,x⟫ x - v` is sphere-valued.
It sends the equator exactly to the antipodal pole and is unchanged by the
source antipode. Its restrictions to the two open hemispheres will supply
the two genuine geometric sheets of the sphere-sum construction.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def height (v x : UnitSphere E) : ℝ := inner ℝ (v : E) (x : E)

def ambient (v x : UnitSphere E) : E := (2 * height v x) • (x : E) - (v : E)

theorem norm_ambient (v x : UnitSphere E) : ‖ambient v x‖ = 1 := by
  have hsq : ‖ambient v x‖ ^ 2 = 1 := by
    rw [ambient, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      ClosedHemisphere.unit_norm x, mul_one, ClosedHemisphere.unit_norm v,
      real_inner_smul_left, real_inner_comm (v : E) (x : E)]
    change |2 * height v x| ^ 2 - 2 * (2 * height v x * height v x) + 1 ^ 2 = 1
    rw [sq_abs]
    ring
  nlinarith [norm_nonneg (ambient v x)]

def fold (v x : UnitSphere E) : UnitSphere E :=
  ⟨ambient v x, by simpa only [Metric.mem_sphere, dist_zero_right] using norm_ambient v x⟩

theorem fold_val (v x : UnitSphere E) : (fold v x : E) =
    (2 * height v x) • (x : E) - (v : E) := rfl

theorem continuous_fold (v : UnitSphere E) : Continuous (fold v) :=
  (((continuous_const.mul (continuous_const.inner continuous_subtype_val)).smul
    continuous_subtype_val).sub continuous_const).subtype_mk _

def foldMap (v : UnitSphere E) : C(UnitSphere E, UnitSphere E) := ⟨fold v, continuous_fold v⟩

theorem height_antipode (v x : UnitSphere E) : height v (antipode x) = -height v x :=
  inner_neg_right _ _

theorem fold_antipode (v x : UnitSphere E) : fold v (antipode x) = fold v x := by
  apply Subtype.ext
  rw [fold_val, fold_val, height_antipode]
  change (2 * -height v x) • (-(x : E)) - (v : E) = _
  rw [mul_neg, neg_smul, smul_neg, neg_neg]

theorem fold_eq_antipode_iff (v x : UnitSphere E) :
    fold v x = antipode v ↔ height v x = 0 := by
  constructor
  · intro h
    have he := congrArg (fun y : UnitSphere E ↦ (y : E) + (v : E)) h
    change ((2 * height v x) • (x : E) - (v : E)) + (v : E) = -(v : E) + (v : E) at he
    rw [sub_add_cancel, neg_add_cancel] at he
    rcases smul_eq_zero.mp he with hs | hx
    · linarith
    · exact False.elim (ne_zero_of_mem_unit_sphere x hx)
  · intro h
    apply Subtype.ext
    simp only [fold_val, h, mul_zero, zero_smul, zero_sub, antipode]

theorem height_fold (v x : UnitSphere E) : height v (fold v x) = 2 * (height v x) ^ 2 - 1 := by
  change inner ℝ (v : E) ((2 * height v x) • (x : E) - (v : E)) = _
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    ClosedHemisphere.unit_norm v]
  change 2 * height v x * height v x - 1 ^ 2 = _
  ring

variable {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem contMDiff_fold (v : UnitSphere E) : ContMDiff (𝓡 n) (𝓡 n) ∞ (fold v) := by
  have hx : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val : UnitSphere E → E) :=
    contMDiff_coe_sphere (E := E) (n := n) (m := ∞)
  have ht : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (height v) :=
    (innerSL ℝ (v : E)).contDiff.contMDiff.comp hx
  have ha : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (ambient v) :=
    ((contMDiff_const.mul ht).smul hx).sub contMDiff_const
  exact ha.codRestrict_sphere (n := n) (fun x ↦ (fold v x).property)

end NoExoticSixSphere.SphereFold
