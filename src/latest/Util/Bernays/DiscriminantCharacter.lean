import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Complex.Basic

/-!
# A quadratic Dirichlet character for any negative discriminant

We use modulus `4|D|`, so the bad primes include `2` and every divisor of
the discriminant. On odd coprime natural numbers the value is the Jacobi symbol.
-/

open scoped Classical

namespace Bernays

def discriminantLevel (D : ℤ) : ℕ := 4 * D.natAbs

theorem discriminantLevel_pos {D : ℤ} (hD : D ≠ 0) : 0 < discriminantLevel D :=
  Nat.mul_pos (by decide) (Int.natAbs_pos.mpr hD)

theorem discriminantLevel_one_lt {D : ℤ} (hD : D ≠ 0) : 1 < discriminantLevel D := by
  have := Int.natAbs_pos.mpr hD
  unfold discriminantLevel
  omega

theorem odd_of_coprime_discriminantLevel {D : ℤ} {n : ℕ}
    (hn : n.Coprime (discriminantLevel D)) : Odd n :=
  (hn.of_dvd_right (show 2 ∣ discriminantLevel D by exact ⟨2 * D.natAbs, by
    unfold discriminantLevel; ring⟩)).odd_of_right

theorem odd_val_of_isUnit_discriminant {D : ℤ} (hD : D ≠ 0) {a : ZMod (discriminantLevel D)}
    (ha : IsUnit a) : Odd a.val := by
  letI : NeZero (discriminantLevel D) := ⟨(discriminantLevel_pos hD).ne'⟩
  apply odd_of_coprime_discriminantLevel (D := D)
  exact (ZMod.isUnit_iff_coprime a.val _).mp (by simpa using ha)

noncomputable def discriminantCharacter (D : ℤ) (hD : D ≠ 0) :
    DirichletCharacter ℂ (discriminantLevel D) where
  toFun a := if IsUnit a then (jacobiSym D a.val : ℂ) else 0
  map_nonunit' a ha := by simp [ha]
  map_one' := by
    simp only [isUnit_one, if_true]
    rw [ZMod.val_one'' (discriminantLevel_one_lt hD).ne', jacobiSym.one_right, Int.cast_one]
  map_mul' a b := by
    by_cases ha : IsUnit a
    · by_cases hb : IsUnit b
      · simp only [ha, hb, ha.mul hb, if_true]
        have hao := odd_val_of_isUnit_discriminant hD ha
        have hbo := odd_val_of_isUnit_discriminant hD hb
        rw [ZMod.val_mul]
        change (jacobiSym D (a.val * b.val % (4 * D.natAbs)) : ℂ) = _
        rw [← jacobiSym.mod_right D (hao.mul hbo),
          jacobiSym.mul_right' D hao.pos.ne' hbo.pos.ne', Int.cast_mul]
      · simp [ha, hb, IsUnit.mul_iff]
    · simp [ha, IsUnit.mul_iff]

theorem discriminantCharacter_apply_of_coprime (D : ℤ) (hD : D ≠ 0)
    {n : ℕ} (hn : n.Coprime (discriminantLevel D)) :
    discriminantCharacter D hD n = (jacobiSym D n : ℂ) := by
  have hu := (ZMod.isUnit_iff_coprime n (discriminantLevel D)).mpr hn
  change (if IsUnit (n : ZMod (discriminantLevel D)) then
    (jacobiSym D (n : ZMod (discriminantLevel D)).val : ℂ) else 0) = _
  rw [if_pos hu, ZMod.val_natCast]
  exact congrArg (Int.cast : ℤ → ℂ) (jacobiSym.mod_right D (odd_of_coprime_discriminantLevel hn)).symm

theorem discriminantCharacter_sq (D : ℤ) (hD : D ≠ 0) :
    discriminantCharacter D hD ^ 2 = 1 := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mp
  intro a
  change (if IsUnit a then (jacobiSym D a.val : ℂ) else 0) = 0 ∨
    (if IsUnit a then (jacobiSym D a.val : ℂ) else 0) = 1 ∨
      (if IsUnit a then (jacobiSym D a.val : ℂ) else 0) = -1
  by_cases ha : IsUnit a
  · simp only [ha, if_true]
    rcases jacobiSym.trichotomy D a.val with h | h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (Or.inl (by simp [h]))
    · exact Or.inr (Or.inr (by simp [h]))
  · exact Or.inl (if_neg ha)

theorem jacobiSym_natAbs_predecessor {D : ℤ} (hD : D ≠ 0) :
    jacobiSym (D.natAbs : ℤ) (discriminantLevel D - 1) = 1 := by
  have hN := discriminantLevel_one_lt hD
  have ho : Odd (discriminantLevel D - 1) := by
    rw [Nat.odd_iff]
    unfold discriminantLevel at *
    omega
  have hmod : (4 * (D.natAbs : ℤ)) % (discriminantLevel D - 1 : ℕ) =
      (1 : ℤ) % (discriminantLevel D - 1 : ℕ) := by
    have hcast : ((discriminantLevel D - 1 : ℕ) : ℤ) = 4 * D.natAbs - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ discriminantLevel D)]
      simp [discriminantLevel]
    rw [hcast]
    simpa only [sub_add_cancel, Int.emod_self, zero_add, Int.emod_emod] using
      (Int.add_emod (4 * (D.natAbs : ℤ) - 1) 1 (4 * D.natAbs - 1))
  have h := jacobiSym.mod_left' hmod
  rw [jacobiSym.mul_left, jacobiSym.at_four ho, one_mul, jacobiSym.one_left] at h
  exact h

theorem discriminantCharacter_ne_one {D : ℤ} (hD : D < 0) :
    discriminantCharacter D hD.ne = 1 → False := by
  intro hχ
  have hN := discriminantLevel_one_lt hD.ne
  have hc : (discriminantLevel D - 1).Coprime (discriminantLevel D) := by
    have h : discriminantLevel D - 1 + 1 = discriminantLevel D := by omega
    have hc := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right (discriminantLevel D - 1))
    simpa only [h] using hc
  have ho := odd_of_coprime_discriminantLevel hc
  have hval : jacobiSym D (discriminantLevel D - 1) = -1 := by
    have hneg : D = -(D.natAbs : ℤ) := by rw [Int.natCast_natAbs, abs_of_neg hD, neg_neg]
    nth_rw 1 [hneg]
    rw [jacobiSym.neg _ ho]
    have hthree : (discriminantLevel D - 1) % 4 = 3 := by
      unfold discriminantLevel at *
      omega
    rw [ZMod.χ₄_nat_three_mod_four hthree, jacobiSym_natAbs_predecessor hD.ne, mul_one]
  have hv := discriminantCharacter_apply_of_coprime D hD.ne hc
  rw [hχ, MulChar.one_apply (by exact (ZMod.isUnit_iff_coprime _ _).mpr hc), hval] at hv
  norm_num at hv

end Bernays
