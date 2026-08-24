import ErdosProblems.Erdos587.RankTwoSmoothing

/-! A short linear interval meets the values of a nonprimitive quadratic coefficient. -/

namespace Erdos587

lemma quadratic_common_factor_cost {u g : ℕ} (hu : 0 < u) (Q : ℕ) :
    ((g.gcd u + g.gcd u * (7 + 8 * (Q + Nat.sqrt (ordCompl[2] (u / g.gcd u)))) : ℕ) : ℝ) ≤
      (16 + 8 * (Q : ℝ)) * Real.sqrt ((g.gcd u : ℝ) * u) := by
  let d := g.gcd u
  have hd : 0 < d := Nat.gcd_pos_of_pos_right g hu
  have hdvd : d ∣ u := Nat.gcd_dvd_right g u
  have hdle : d ≤ u := Nat.le_of_dvd hu hdvd
  have hfactor : d * (u / d) = u := Nat.mul_div_cancel' hdvd
  have hoddle : ordCompl[2] (u / d) ≤ u / d := Nat.ordCompl_le _ _
  have hrootSq : (d * Nat.sqrt (ordCompl[2] (u / d))) ^ 2 ≤ d * u := by
    calc
      _ = (d * d) * (Nat.sqrt (ordCompl[2] (u / d))) ^ 2 := by ring
      _ ≤ (d * d) * (u / d) :=
        Nat.mul_le_mul_left _ ((Nat.sqrt_le' _).trans hoddle)
      _ = d * u := by rw [Nat.mul_assoc, hfactor]
  have hroot : ((d * Nat.sqrt (ordCompl[2] (u / d)) : ℕ) : ℝ) ≤ Real.sqrt ((d : ℝ) * u) := by
    have hh : (((d * Nat.sqrt (ordCompl[2] (u / d)) : ℕ) : ℝ)) ^ 2 ≤ (d : ℝ) * u := by
      exact_mod_cast hrootSq
    have hs := Real.sqrt_le_sqrt hh
    rwa [Real.sqrt_sq (Nat.cast_nonneg _)] at hs
  have hdroot : (d : ℝ) ≤ Real.sqrt ((d : ℝ) * u) := by
    have hh : (d : ℝ) ^ 2 ≤ (d : ℝ) * u := by exact_mod_cast (show d ^ 2 ≤ d * u by nlinarith)
    have hs := Real.sqrt_le_sqrt hh
    rwa [Real.sqrt_sq (Nat.cast_nonneg _)] at hs
  change ((d + d * (7 + 8 * (Q + Nat.sqrt (ordCompl[2] (u / d)))) : ℕ) : ℝ) ≤ _
  push_cast at hroot ⊢
  have hQ := Nat.cast_nonneg (α := ℝ) Q
  nlinarith

theorem exists_nonprimitive_quadratic_residue :
    ∃ A : ℝ, 0 < A ∧ ∀ (g u v t J : ℕ), 0 < u → v.Coprime u →
      A * Real.sqrt ((g.gcd u : ℝ) * u) ≤ J →
      ∃ y ≤ J, ∃ z : ℕ, g * z ^ 2 ≡ t + v * y [MOD u] := by
  obtain ⟨Q, hQ⟩ := exists_quadraticRootAllUniformThreshold
  refine ⟨16 + 8 * Q, by positivity, ?_⟩
  intro g u v t J hu hvu hJ
  letI : NeZero u := ⟨hu.ne'⟩
  let e : (ZMod u)ˣ := ZMod.unitOfCoprime v hvu
  let A : ℕ := (((e⁻¹ : (ZMod u)ˣ) : ZMod u) * (g : ZMod u)).val
  let C : ℕ := (((e⁻¹ : (ZMod u)ˣ) : ZMod u) * (-(t : ZMod u))).val
  have hAgcd : A.gcd u = g.gcd u := gcd_val_unit_mul_nat u g e⁻¹
  obtain ⟨y, hy, z, hz⟩ := hQ (q := u) (A := A) (B := 0) (C := C) hu.ne'
  simp only [Nat.gcd_zero_right, hAgcd] at hy
  have hyJ : y ≤ J := by
    have hh : (y : ℝ) ≤ J := (by exact_mod_cast hy : (y : ℝ) ≤
      ((g.gcd u + g.gcd u * (7 + 8 * (Q + Nat.sqrt (ordCompl[2] (u / g.gcd u)))) : ℕ) : ℝ)).trans
        ((quadratic_common_factor_cost hu Q).trans hJ)
    exact_mod_cast hh
  have hAval : (A : ZMod u) = ((e⁻¹ : (ZMod u)ˣ) : ZMod u) * g := ZMod.natCast_zmod_val _
  have hCval : (C : ZMod u) = ((e⁻¹ : (ZMod u)ˣ) : ZMod u) * (-t) := ZMod.natCast_zmod_val _
  simp only [Nat.cast_zero, zero_mul, add_zero, hAval, hCval] at hz
  have he : (e : ZMod u) = v := ZMod.coe_unitOfCoprime v hvu
  have hinv : (e : ZMod u) * ((e⁻¹ : (ZMod u)ˣ) : ZMod u) = 1 := by
    rw [← Units.val_mul]
    simp
  have hscaled := congrArg (fun w : ZMod u => (e : ZMod u) * w) hz
  have hroot : (g : ZMod u) * z ^ 2 = (t : ZMod u) + v * y := by
    simp only [mul_add, ← mul_assoc, hinv, one_mul] at hscaled
    rw [he] at hscaled
    linear_combination hscaled
  refine ⟨y, hyJ, z.val, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact hroot

end Erdos587
