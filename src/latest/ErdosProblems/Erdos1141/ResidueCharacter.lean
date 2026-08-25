import ErdosProblems.Erdos1141.NonprincipalCRT

/-!
# Characters detecting a prescribed quadratic residue
-/

open scoped BigOperators

namespace Erdos1141.CharacterSums

lemma squarefree_two_odd_decomposition {d : ℕ} (hd : Squarefree d) :
    ∃ e r : ℕ, e ≤ 1 ∧ d = 2 ^ e * r ∧ Odd r ∧ Squarefree r := by
  by_cases htwo : 2 ∣ d
  · refine ⟨1, d / 2, le_rfl, ?_, ?_, hd.squarefree_of_dvd (Nat.div_dvd_of_dvd htwo)⟩
    · simpa only [pow_one, Nat.mul_comm] using (Nat.div_mul_cancel htwo).symm
    · apply Nat.not_even_iff_odd.mp
      rw [even_iff_two_dvd]
      intro h
      have hfour : 2 * 2 ∣ d := (Nat.dvd_div_iff_mul_dvd htwo).mp h
      exact (Nat.squarefree_iff_prime_squarefree.mp hd) 2 Nat.prime_two hfour
  · exact ⟨0, d, by omega, by simp,
      Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using htwo), hd⟩

noncomputable def auxiliaryResidueCharacter (e r : ℕ) : DirichletCharacter ℤ 8 :=
  ZMod.χ₈ ^ e * (DirichletCharacter.changeLevel (by decide : 4 ∣ 8) ZMod.χ₄) ^ (r / 2)

lemma auxiliaryResidueCharacter_isQuadratic (e r : ℕ) :
    (auxiliaryResidueCharacter e r).IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  have hfour : (DirichletCharacter.changeLevel (by decide : 4 ∣ 8) ZMod.χ₄) ^ 2 = 1 := by
    rw [← map_pow, ZMod.isQuadratic_χ₄.sq_eq_one, map_one]
  rw [auxiliaryResidueCharacter, mul_pow, ← pow_mul, Nat.mul_comm e 2, pow_mul,
    ZMod.isQuadratic_χ₈.sq_eq_one, one_pow, one_mul, ← pow_mul, Nat.mul_comm (r / 2) 2,
    pow_mul, hfour, one_pow]

lemma auxiliaryResidueCharacter_natCast (e r n : ℕ) (hn : Odd n) :
    auxiliaryResidueCharacter e r (n : ZMod 8) =
      (ZMod.χ₈ (n : ZMod 8)) ^ e * (ZMod.χ₄ (n : ZMod 4)) ^ (r / 2) := by
  have hcop : n.Coprime 8 := by
    rw [show 8 = 2 ^ 3 by norm_num]
    exact (Nat.coprime_two_right.mpr hn).pow_right 3
  have hu : IsUnit (n : ZMod 8) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
  have hfour : DirichletCharacter.changeLevel (by decide : 4 ∣ 8) ZMod.χ₄ (n : ZMod 8) =
      ZMod.χ₄ (n : ZMod 4) := by
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ZMod.χ₄
      (by decide : 4 ∣ 8) hu.unit
    simpa only [IsUnit.unit_spec, ZMod.cast_natCast (by decide : 4 ∣ 8)] using h
  rw [auxiliaryResidueCharacter, MulChar.mul_apply]
  rw [← hu.unit_spec, MulChar.pow_apply_coe, MulChar.pow_apply_coe, hu.unit_spec, hfour]

lemma auxiliaryResidueCharacter_reciprocity (e r n : ℕ) (hr : Odd r) (hn : Odd n) :
    auxiliaryResidueCharacter e r (n : ZMod 8) * jacobiSym (n : ℤ) r =
      jacobiSym ((2 ^ e * r : ℕ) : ℤ) n := by
  rw [auxiliaryResidueCharacter_natCast e r n hn, Nat.cast_mul, jacobiSym.mul_left,
    Nat.cast_pow, Nat.cast_ofNat, jacobiSym.pow_left, jacobiSym.at_two hn,
    jacobiSym.quadratic_reciprocity hr hn, ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hn),
    ← pow_mul, Nat.mul_comm (n / 2) (r / 2)]
  ring

lemma auxiliaryResidueCharacter_two_ne_one : auxiliaryResidueCharacter 1 1 ≠ 1 := by
  have heq : auxiliaryResidueCharacter 1 1 = ZMod.χ₈ := by simp [auxiliaryResidueCharacter]
  rw [heq]
  intro h
  have heval := congrArg (fun χ : DirichletCharacter ℤ 8 ↦ χ (3 : ZMod 8)) h
  have hu : IsUnit (3 : ZMod 8) := (ZMod.isUnit_iff_coprime 3 8).mpr (by decide)
  rw [MulChar.one_apply hu] at heval
  norm_num [ZMod.χ₈] at heval

end Erdos1141.CharacterSums
