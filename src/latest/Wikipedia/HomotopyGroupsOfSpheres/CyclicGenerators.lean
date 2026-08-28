import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Equiv.Basic

/-! # Generator comparisons under actual group homomorphisms -/

namespace Wikipedia.HomotopyGroupsOfSpheres.CyclicGenerators

variable {G H : Type*} [Group G] [Group H]

theorem of_coordinate_natAbs (e : G ≃* Multiplicative ℤ) (g : G)
    (h : Int.natAbs (e g).toAdd = 1) : Function.Surjective (fun k : ℤ ↦ g ^ k) := by
  let k := (e g).toAdd
  have hk : k * k = 1 := Int.isUnit_mul_self (Int.isUnit_iff_natAbs_eq.mpr h)
  intro a
  refine ⟨(e a).toAdd * k, e.injective ?_⟩
  rw [map_zpow]
  change Multiplicative.ofAdd (((e a).toAdd * k) • k) = Multiplicative.ofAdd (e a).toAdd
  apply congrArg Multiplicative.ofAdd
  rw [Int.zsmul_eq_mul, mul_assoc, hk, mul_one]

theorem map_generates_iff (f : G →* H) (g : G)
    (hg : Function.Surjective (fun k : ℤ ↦ g ^ k)) :
    Function.Surjective (fun k : ℤ ↦ (f g) ^ k) ↔ Function.Surjective f := by
  constructor
  · intro h a
    obtain ⟨k, hk⟩ := h a
    exact ⟨g ^ k, (map_zpow f g k).trans hk⟩
  · intro h a
    obtain ⟨u, rfl⟩ := h a
    obtain ⟨k, rfl⟩ := hg u
    exact ⟨k, (map_zpow f g k).symm⟩

theorem equiv_generates_iff (e : G ≃* H) (g : G) :
    Function.Surjective (fun k : ℤ ↦ (e g) ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ g ^ k) := by
  constructor
  · intro h a
    obtain ⟨k, hk⟩ := h (e a)
    exact ⟨k, e.injective ((map_zpow e g k).trans hk)⟩
  · intro h a
    obtain ⟨k, hk⟩ := h (e.symm a)
    refine ⟨k, ?_⟩
    change e g ^ k = a
    change g ^ k = e.symm a at hk
    rw [← map_zpow, hk, e.apply_symm_apply]

end Wikipedia.HomotopyGroupsOfSpheres.CyclicGenerators
