import ErdosProblems.Erdos1141.TwistedCharacterSums

/-!
# Nonprincipal CRT characters
-/

open scoped BigOperators

namespace Erdos1141.CharacterSums

lemma crtMulChar_ne_one_of_right {m n : ℕ} (hmn : m.Coprime n)
    (ψ : DirichletCharacter ℤ m) (χ : DirichletCharacter ℤ n) (hχ : χ ≠ 1) :
    crtMulChar hmn ψ χ ≠ 1 := by
  intro h
  apply hχ
  apply MulChar.ext
  intro u
  let x := (ZMod.chineseRemainder hmn).symm (1, (u : ZMod n))
  have hx : IsUnit x := (Prod.isUnit_iff.mpr ⟨isUnit_one, u.isUnit⟩).map
    (ZMod.chineseRemainder hmn).symm.toMonoidHom
  have heval := congrArg (fun φ : DirichletCharacter ℤ (m * n) ↦ φ x) h
  rw [crtMulChar_apply, show ZMod.chineseRemainder hmn x = (1, (u : ZMod n)) from
    (ZMod.chineseRemainder hmn).apply_symm_apply _, MulChar.one_apply hx] at heval
  simpa only [map_one, one_mul, MulChar.one_apply_coe] using heval

lemma crtMulChar_ne_one_of_left {m n : ℕ} (hmn : m.Coprime n)
    (ψ : DirichletCharacter ℤ m) (χ : DirichletCharacter ℤ n) (hψ : ψ ≠ 1) :
    crtMulChar hmn ψ χ ≠ 1 := by
  intro h
  apply hψ
  apply MulChar.ext
  intro u
  let x := (ZMod.chineseRemainder hmn).symm ((u : ZMod m), 1)
  have hx : IsUnit x := (Prod.isUnit_iff.mpr ⟨u.isUnit, isUnit_one⟩).map
    (ZMod.chineseRemainder hmn).symm.toMonoidHom
  have heval := congrArg (fun φ : DirichletCharacter ℤ (m * n) ↦ φ x) h
  rw [crtMulChar_apply, show ZMod.chineseRemainder hmn x = ((u : ZMod m), 1) from
    (ZMod.chineseRemainder hmn).apply_symm_apply _, MulChar.one_apply hx] at heval
  simpa only [map_one, mul_one, MulChar.one_apply_coe] using heval

lemma primeProductMulChar_ne_one {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise fun i j ↦ (p i).Coprime (p j)) (i : ι) (hi : p i ≠ 2) :
    primeProductMulChar p hc ≠ 1 := by
  classical
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one'
    (by simpa only [ZMod.ringChar_zmod_n] using hi : ringChar (ZMod (p i)) ≠ 2)
  let y : ∀ j, ZMod (p j) := Function.update (fun _ ↦ 1) i (a : ZMod (p i))
  let x := (ZMod.prodEquivPi p hc).symm y
  have hy : IsUnit y := isUnit_iff_exists_inv.mpr ⟨fun j ↦ (y j)⁻¹, by
    ext j
    by_cases hj : j = i
    · subst j
      change y i * (y i)⁻¹ = 1
      have hyi : y i = (a : ZMod (p i)) := Function.update_self i _ _
      rw [hyi]
      exact mul_inv_cancel₀ a.ne_zero
    · simp [y, Function.update_of_ne hj]⟩
  have hx : IsUnit x := hy.map (ZMod.prodEquivPi p hc).symm.toMonoidHom
  have hvalue : primeProductMulChar p hc x = -1 := by
    change (∏ j, quadraticChar (ZMod (p j)) (ZMod.prodEquivPi p hc x j)) = -1
    rw [show ZMod.prodEquivPi p hc x = y from (ZMod.prodEquivPi p hc).apply_symm_apply _]
    calc
      _ = quadraticChar (ZMod (p i)) (y i) := by
        apply Finset.prod_eq_single i
        · intro j _ hji
          simp [y, Function.update_of_ne hji]
        · simp
      _ = -1 := by simpa [y] using ha
  intro h
  rw [h, MulChar.one_apply hx] at hvalue
  norm_num at hvalue

end Erdos1141.CharacterSums
