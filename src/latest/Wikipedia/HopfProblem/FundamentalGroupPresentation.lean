import Wikipedia.HopfProblem.Arithmetic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The abstract group presentation in §7 of `tex/s6.tex`

This file constructs the presented group in Theorem 7.17 and proves its
algebraic properties. It does not assume, or assert, that a threefold realizing
this fundamental group has been constructed.
-/

namespace Wikipedia.HopfProblem

open scoped Matrix

/-- In order: centrality of `c`, the boundary relation, and the two filling
relations. The generator indices are `c = 0`, `x = 1`, `y = 2`. -/
def twistRelators (a b d : ℤ) : Fin 5 → FreeGroup (Fin 3) :=
  let c := FreeGroup.of (0 : Fin 3)
  let x := FreeGroup.of (1 : Fin 3)
  let y := FreeGroup.of (2 : Fin 3)
  ![c * x * (x * c)⁻¹, c * y * (y * c)⁻¹, x * y * (c ^ a)⁻¹,
    x ^ 3 * (c ^ b)⁻¹, y ^ 4 * (c ^ d)⁻¹]

/-- The group specified by the presentation displayed in Theorem 7.17. -/
abbrev TwistGroup (a b d : ℤ) := PresentedGroup (Set.range (twistRelators a b d))

namespace TwistGroup

variable (a b d : ℤ)

def c : TwistGroup a b d := PresentedGroup.of 0
def x : TwistGroup a b d := PresentedGroup.of 1
def y : TwistGroup a b d := PresentedGroup.of 2

theorem relator (i : Fin 5) :
    PresentedGroup.mk (Set.range (twistRelators a b d)) (twistRelators a b d i) = 1 :=
  PresentedGroup.one_of_mem (Set.mem_range_self i)

theorem c_commute_x : Commute (c a b d) (x a b d) := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range.mpr ⟨0, rfl⟩)

theorem c_commute_y : Commute (c a b d) (y a b d) := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range.mpr ⟨1, rfl⟩)

theorem x_mul_y : x a b d * y a b d = c a b d ^ a := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range.mpr ⟨2, rfl⟩)

theorem x_cube : x a b d ^ 3 = c a b d ^ b := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range.mpr ⟨3, rfl⟩)

theorem y_fourth : y a b d ^ 4 = c a b d ^ d := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range.mpr ⟨4, rfl⟩)

theorem x_commute_y : Commute (x a b d) (y a b d) := by
  change x a b d * y a b d = y a b d * x a b d
  apply mul_left_cancel (a := x a b d)
  calc
    x a b d * (x a b d * y a b d) = x a b d * c a b d ^ a := by rw [x_mul_y]
    _ = c a b d ^ a * x a b d := ((c_commute_x a b d).symm.zpow_right a).eq
    _ = x a b d * (y a b d * x a b d) := by rw [← x_mul_y, mul_assoc]

theorem x_fourth : x a b d ^ 4 = c a b d ^ (4 * a - d) := by
  calc
    x a b d ^ 4 = (x a b d * y a b d) ^ 4 * (y a b d ^ 4)⁻¹ := by
      rw [(x_commute_y a b d).mul_pow]; group
    _ = (c a b d ^ a) ^ 4 * (c a b d ^ d)⁻¹ := by rw [x_mul_y, y_fourth]
    _ = c a b d ^ (4 * a - d) := by
      rw [← zpow_natCast _ 4, ← zpow_mul, ← zpow_sub]
      congr 1
      ring

theorem x_eq_c_power : x a b d = c a b d ^ (4 * a - b - d) := by
  calc
    x a b d = x a b d ^ 4 * (x a b d ^ 3)⁻¹ := by group
    _ = c a b d ^ (4 * a - d) * (c a b d ^ b)⁻¹ := by rw [x_fourth, x_cube]
    _ = c a b d ^ (4 * a - b - d) := by
      rw [← zpow_sub]
      congr 1
      ring

theorem y_eq_c_power : y a b d = c a b d ^ (-3 * a + b + d) := by
  calc
    y a b d = (x a b d)⁻¹ * (x a b d * y a b d) := by group
    _ = (c a b d ^ (4 * a - b - d))⁻¹ * c a b d ^ a := by rw [x_mul_y, x_eq_c_power]
    _ = c a b d ^ (-3 * a + b + d) := by
      rw [← zpow_neg, ← zpow_add]
      congr 1
      ring

theorem c_twistOrder : c a b d ^ twistOrder a b d = 1 := by
  have h := x_cube a b d
  rw [x_eq_c_power, ← zpow_natCast _ 3, ← zpow_mul] at h
  have h' := congrArg (fun z => z * (c a b d ^ b)⁻¹) h
  rw [mul_inv_cancel, ← zpow_sub] at h'
  norm_num only [Nat.cast_ofNat] at h'
  have he : (4 * a - b - d) * 3 - b = twistOrder a b d := by unfold twistOrder; ring
  rwa [he] at h'

theorem generated_by_c (z : TwistGroup a b d) : z ∈ Subgroup.zpowers (c a b d) := by
  apply PresentedGroup.generated_by
  intro j
  fin_cases j
  · exact Subgroup.mem_zpowers _
  · change x a b d ∈ _
    rw [x_eq_c_power]
    exact Subgroup.zpow_mem_zpowers _ _
  · change y a b d ∈ _
    rw [y_eq_c_power]
    exact Subgroup.zpow_mem_zpowers _ _

instance isCyclic : IsCyclic (TwistGroup a b d) := ⟨c a b d, generated_by_c a b d⟩

private def cyclicImages : Fin 3 → Multiplicative (ZMod (twistOrder a b d).natAbs) :=
  ![Multiplicative.ofAdd 1, Multiplicative.ofAdd (4 * a - b - d : ℤ),
    Multiplicative.ofAdd (-3 * a + b + d : ℤ)]

private theorem cyclicImages_relations :
    ∀ r ∈ Set.range (twistRelators a b d), FreeGroup.lift (cyclicImages a b d) r = 1 := by
  have hp : (twistOrder a b d : ZMod (twistOrder a b d).natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natCast_dvd.mpr (dvd_refl _)
  change ((12 * a - 4 * b - 3 * d : ℤ) : ZMod (twistOrder a b d).natAbs) = 0 at hp
  push_cast at hp
  rintro r ⟨i, rfl⟩
  apply Multiplicative.toAdd.injective
  fin_cases i <;>
    simp [twistRelators, cyclicImages, map_mul, map_inv, map_zpow, map_pow,
      FreeGroup.lift_apply_of, mul_comm, mul_left_comm, mul_assoc]
  · ring
  · ring
  · ring
  · linear_combination hp
  · linear_combination -hp

/-- The reverse homomorphism rules out an extra relation on the central
generator. In particular, the computation gives the exact order, not a bound. -/
def toCyclic : TwistGroup a b d →* Multiplicative (ZMod (twistOrder a b d).natAbs) :=
  PresentedGroup.toGroup (cyclicImages_relations a b d)

@[simp] theorem toCyclic_c : toCyclic a b d (c a b d) = Multiplicative.ofAdd 1 := by
  exact PresentedGroup.toGroup.of (cyclicImages_relations a b d)

theorem orderOf_c : orderOf (c a b d) = (twistOrder a b d).natAbs := by
  apply Nat.dvd_antisymm
  · exact Int.natCast_dvd.mp (orderOf_dvd_iff_zpow_eq_one.mpr (c_twistOrder a b d))
  · have h := orderOf_map_dvd (toCyclic a b d) (c a b d)
    simpa using h

theorem natCard : Nat.card (TwistGroup a b d) = (twistOrder a b d).natAbs := by
  rw [← orderOf_eq_card_of_forall_mem_zpowers (generated_by_c a b d), orderOf_c]

/-- The exact cyclic-group identification for the presentation, also valid
when `p = 0`, in which case `ZMod 0` is the infinite cyclic group. -/
noncomputable def cyclicEquiv :
    Multiplicative (ZMod (twistOrder a b d).natAbs) ≃* TwistGroup a b d :=
  zmodMulEquivOfGenerator (generated_by_c a b d) (natCard a b d)

theorem main_group_trivial (z : TwistGroup 0 1 (-1)) : z = 1 := by
  have hc : c 0 1 (-1) = 1 := by
    simpa only [main_twist_value, zpow_neg_one, inv_eq_one] using c_twistOrder 0 1 (-1)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (generated_by_c 0 1 (-1) z)
  simp [hc]

theorem comparison_group_card : Nat.card (TwistGroup 0 1 1) = 7 := by
  rw [natCard, comparison_twist_value]
  rfl

end TwistGroup

end Wikipedia.HopfProblem
