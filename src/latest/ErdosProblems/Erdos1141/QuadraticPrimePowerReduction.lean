import ErdosProblems.Erdos1141.QuadraticFieldClassification
import ErdosProblems.Erdos1141.QuadraticPrimePowerSquares

/-!
# Reducing quadratic characters at prime powers
-/

namespace Pollack17

theorem quadratic_factorsThrough_of_kernel_squares {m d : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) (hχ : χ.IsQuadratic) (hd : d ∣ m)
    (hsquare : ∀ a : ℤ, (d : ℤ) ∣ 1 - a → IsSquare (a : ZMod m)) :
    χ.FactorsThrough d := by
  apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  apply Units.ext
  change χ (x : ZMod m) = 1
  apply quadratic_apply_square_unit χ hχ x.isUnit
  have hval : (((x : ZMod m).val : ℕ) : ZMod d) = 1 := by
    have h := congrArg Units.val hx
    simpa only [ZMod.unitsMap_val, ZMod.cast_eq_val, Units.val_one] using h
  have hdiv : (d : ℤ) ∣ 1 - ((x : ZMod m).val : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub, Int.cast_one, Int.cast_natCast, hval, sub_self]
  have hsq := hsquare ((x : ZMod m).val : ℤ) hdiv
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hsq

theorem quadratic_odd_prime_power_factorsThrough {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    (χ : DirichletCharacter ℂ (p ^ n)) (hχ : χ.IsQuadratic) :
    χ.FactorsThrough p := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply quadratic_factorsThrough_of_kernel_squares χ hχ (dvd_pow_self p (by omega : n ≠ 0))
  exact fun a ha => isSquare_zmod_odd_prime_pow_of_one_mod hp hp2 a n ha

theorem quadratic_two_power_factorsThrough {n : ℕ} (hn : 3 ≤ n)
    (χ : DirichletCharacter ℂ (2 ^ n)) (hχ : χ.IsQuadratic) :
    χ.FactorsThrough 8 := by
  have : NeZero (2 ^ n) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hd : 8 ∣ 2 ^ n := by
    have h := Nat.pow_dvd_pow 2 hn
    norm_num at h
    exact h
  exact quadratic_factorsThrough_of_kernel_squares χ hχ hd
    (fun a ha => isSquare_zmod_two_pow_of_one_mod_eight a n ha)

theorem quadratic_of_changeLevel {m d : ℕ} [NeZero m] (hd : d ∣ m)
    (ψ : DirichletCharacter ℂ d) (hψ : (DirichletCharacter.changeLevel hd ψ).IsQuadratic) :
    ψ.IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  apply DirichletCharacter.changeLevel_injective hd
  rw [map_pow, map_one, hψ.sq_eq_one]

theorem changeLevel_natCast {R : Type*} [CommMonoidWithZero R] {m d : ℕ}
    (hd : d ∣ m) (ψ : DirichletCharacter R d)
    (a : ℕ) (ha : a.Coprime m) :
    DirichletCharacter.changeLevel hd ψ (a : ZMod m) = ψ (a : ZMod d) := by
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hd (ZMod.unitOfCoprime a ha)
  simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd] using h

theorem quadratic_odd_prime_power_values {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    (χ : DirichletCharacter ℂ (p ^ n)) (hχ : χ.IsQuadratic) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ b : Bool, ∀ a : ℕ, a.Coprime p → χ (a : ZMod (p ^ n)) =
      if b then (quadraticChar (ZMod p) (a : ZMod p) : ℂ) else 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let hfactor := quadratic_odd_prime_power_factorsThrough hp hp2 hn χ hχ
  let ψ := hfactor.χ₀
  have hψ : ψ.IsQuadratic := quadratic_of_changeLevel hfactor.dvd ψ (by
    rw [← hfactor.eq_changeLevel]
    exact hχ)
  have heval (a : ℕ) (ha : a.Coprime p) : χ (a : ZMod (p ^ n)) = ψ (a : ZMod p) := by
    rw [hfactor.eq_changeLevel]
    exact changeLevel_natCast hfactor.dvd ψ a (ha.pow_right n)
  by_cases hψ1 : ψ = 1
  · refine ⟨false, fun a ha => ?_⟩
    rw [heval a ha, hψ1]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime a p).mpr ha)
  · refine ⟨true, fun a ha => ?_⟩
    rw [heval a ha]
    exact quadratic_field_eq_quadraticChar ψ hψ hψ1 _

theorem quadratic_two_power_small_level (n : ℕ)
    (χ : DirichletCharacter ℂ (2 ^ n)) (hχ : χ.IsQuadratic) :
    ∃ e : ℕ, e ≤ 3 ∧ e ≤ n ∧ ∃ θ : DirichletCharacter ℂ (2 ^ e), θ.IsQuadratic ∧
      ∀ a : ℕ, a.Coprime (2 ^ n) → χ (a : ZMod (2 ^ n)) = θ (a : ZMod (2 ^ e)) := by
  by_cases hn : n ≤ 3
  · exact ⟨n, hn, le_rfl, χ, hχ, fun _ _ => rfl⟩
  have : NeZero (2 ^ n) := ⟨pow_ne_zero _ (by norm_num)⟩
  let hfactor := quadratic_two_power_factorsThrough (by omega : 3 ≤ n) χ hχ
  let θ := hfactor.χ₀
  have hθ : θ.IsQuadratic := quadratic_of_changeLevel hfactor.dvd θ (by
    rw [← hfactor.eq_changeLevel]
    exact hχ)
  refine ⟨3, le_rfl, by omega, θ, hθ, fun a ha => ?_⟩
  rw [hfactor.eq_changeLevel]
  exact changeLevel_natCast hfactor.dvd θ a ha

end Pollack17
