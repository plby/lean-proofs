import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Tactic

/-!
# A cyclic kernel with equal finite torsion forces a primitive free coordinate

If the kernel of a map `Z × Z/m -> Z/m` is the image of `Z`, then
the image of its generator has free coordinate of absolute value one.
The proof uses the actual kernel and does not choose a new marking.
-/

namespace NoExoticSixSphere.CyclicKernelPrimitiveCoordinate

variable {m : ℕ} [NeZero m]
  (A : ℤ →+ ℤ × ZMod m) (B : ℤ × ZMod m →+ ZMod m)
  (hex : ∀ x, B x = 0 ↔ ∃ k : ℤ, A k = x)

omit [NeZero m] in
theorem first_apply (k : ℤ) : (A k).1 = k * (A 1).1 := by
  have h := congrArg Prod.fst (map_zsmul A k (1 : ℤ))
  change (A (k • (1 : ℤ))).1 = k • (A 1).1 at h
  simpa only [Int.zsmul_eq_mul, mul_one] using h

include hex

theorem first_one_ne_zero : (A 1).1 ≠ 0 := by
  have hb : B ((m : ℤ), 0) = 0 := by
    calc
      B ((m : ℤ), 0) = B (m • ((1 : ℤ), (0 : ZMod m))) := by congr 1; simp
      _ = m • B ((1 : ℤ), 0) := map_nsmul B _ _
      _ = 0 := by simp [nsmul_eq_mul]
  obtain ⟨k, hk⟩ := (hex _).mp hb
  have hf := congrArg Prod.fst hk
  rw [first_apply] at hf
  intro hz
  rw [hz, mul_zero] at hf
  exact (Nat.cast_ne_zero.mpr (NeZero.ne m) : (m : ℤ) ≠ 0) hf.symm

theorem torsion_injective : Function.Injective (fun t : ZMod m ↦ B (0, t)) := by
  intro x y h
  change B (0, x) = B (0, y) at h
  have hb : B (0, x - y) = 0 := by
    have he : ((0 : ℤ), x - y) = (0, x) - (0, y) := by ext <;> simp
    rw [he, map_sub, h, sub_self]
  obtain ⟨k, hk⟩ := (hex _).mp hb
  have hf := congrArg Prod.fst hk
  rw [first_apply] at hf
  have hk₀ : k = 0 := (mul_eq_zero.mp hf).resolve_right (first_one_ne_zero A B hex)
  have ht := congrArg Prod.snd hk
  rw [hk₀, map_zero] at ht
  exact sub_eq_zero.mp ht.symm

theorem first_one_natAbs : (A 1).1.natAbs = 1 := by
  have hs := Finite.surjective_of_injective (torsion_injective A B hex)
  obtain ⟨t, ht⟩ := hs (B (1, 0))
  change B (0, t) = B (1, 0) at ht
  have hb : B (1, -t) = 0 := by
    have he : ((1 : ℤ), -t) = (1, 0) - (0, t) := by ext <;> simp
    rw [he, map_sub, ht, sub_self]
  obtain ⟨k, hk⟩ := (hex _).mp hb
  have hf := congrArg Prod.fst hk
  rw [first_apply] at hf
  have hu : IsUnit (A 1).1 := IsUnit.of_mul_eq_one k (by simpa only [mul_comm] using hf)
  exact Int.natAbs_of_isUnit hu

end NoExoticSixSphere.CyclicKernelPrimitiveCoordinate
