import ErdosProblems.Erdos1148.BiquadraticConvolution

/-! # Products of real characters of different moduli -/

namespace Erdos1148.DukeArithmetic

noncomputable def productDirichletCharacter {q r : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) : DirichletCharacter ℝ (q * r) :=
  χ.changeLevel (Nat.dvd_mul_right q r) * ψ.changeLevel (Nat.dvd_mul_left r q)

lemma changeLevel_natCast_of_isUnit {q m : ℕ} (χ : DirichletCharacter ℝ q)
    (hqm : q ∣ m) (n : ℕ) (hn : IsUnit (n : ZMod m)) :
    χ.changeLevel hqm n = χ n := by
  have h := χ.changeLevel_eq_cast_of_dvd hqm hn.unit
  simpa only [hn.unit_spec, ZMod.cast_natCast hqm] using h

theorem productDirichletCharacter_apply_nat {q r : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) (n : ℕ) :
    productDirichletCharacter χ ψ n = χ n * ψ n := by
  by_cases hn : IsUnit (n : ZMod (q * r))
  · change (χ.changeLevel (Nat.dvd_mul_right q r)) n *
      (ψ.changeLevel (Nat.dvd_mul_left r q)) n = _
    rw [changeLevel_natCast_of_isUnit χ _ n hn, changeLevel_natCast_of_isUnit ψ _ n hn]
  · rw [(productDirichletCharacter χ ψ).map_nonunit hn]
    simp only [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right, not_and_or] at hn
    rcases hn with hq | hr
    · rw [χ.map_nonunit (fun h => hq ((ZMod.isUnit_iff_coprime n q).mp h)), zero_mul]
    · rw [ψ.map_nonunit (fun h => hr ((ZMod.isUnit_iff_coprime n r).mp h)), mul_zero]

theorem realCharacterArithmetic_product {q r : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) :
    realCharacterArithmetic (productDirichletCharacter χ ψ) =
      (realCharacterArithmetic χ).pmul (realCharacterArithmetic ψ) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero]
  · rw [ArithmeticFunction.pmul_apply, realCharacterArithmetic, realCharacterArithmetic,
      realCharacterArithmetic,
      ← (productDirichletCharacter χ ψ).apply_eq_toArithmeticFunction_apply hn,
      ← χ.apply_eq_toArithmeticFunction_apply hn, ← ψ.apply_eq_toArithmeticFunction_apply hn,
      productDirichletCharacter_apply_nat]

lemma productDirichletCharacter_eq_one_implies_changeLevel_eq {q r : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r)
    (h : productDirichletCharacter χ ψ = 1) :
    χ.changeLevel (Nat.dvd_mul_right q r) = ψ.changeLevel (Nat.dvd_mul_left r q) := by
  have hsquare := (realDirichletCharacter_isQuadratic
    (χ.changeLevel (Nat.dvd_mul_right q r))).sq_eq_one
  rw [pow_two] at hsquare
  exact mul_left_cancel (hsquare.trans h.symm)

theorem productDirichletCharacter_ne_one_of_primitive_moduli_ne {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hqr : q ≠ r) :
    productDirichletCharacter χ ψ ≠ 1 := by
  intro h
  have heq := congrArg DirichletCharacter.conductor
    (productDirichletCharacter_eq_one_implies_changeLevel_eq χ ψ h)
  change χ.conductor = q at hχ
  change ψ.conductor = r at hψ
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel,
    hχ, hψ] at heq
  exact hqr heq

theorem productDirichletCharacter_ne_one_of_ne {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℝ q) (hne : χ ≠ ψ) : productDirichletCharacter χ ψ ≠ 1 := by
  intro h
  exact hne (DirichletCharacter.changeLevel_injective (Nat.dvd_mul_right q q)
    (productDirichletCharacter_eq_one_implies_changeLevel_eq χ ψ h))

lemma realBiquadraticConvolution_grouped {q r : ℕ}
    (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r) :
    realBiquadraticConvolution χ ψ = realZetaConvolution χ *
      (realCharacterArithmetic ψ * realCharacterArithmetic (productDirichletCharacter χ ψ)) := by
  rw [realCharacterArithmetic_product]
  unfold realBiquadraticConvolution realZetaConvolution
  ring

end Erdos1148.DukeArithmetic
