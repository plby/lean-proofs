import Wikipedia.HopfProblem.SpecialPeriodsTriangleModularRepresentation

/-!
# Primitiveness of the actual triangle cusp generator

The constructed integral modular representation sends the cusp generator
to `T⁻¹`.  A matrix commuting with this translation is triangular with
equal diagonal entries.  Every entry above the diagonal in its `n`th
power is therefore divisible by `n`, so `T⁻¹` has no proper root over the
integers.  Applying the representation proves the assertion for the
actual abstract triangle group.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

private theorem equalDiagonalTriangular_pow_succ {R : Type*} [CommSemiring R]
    (a b : R) (n : ℕ) :
    (!![a, b; 0, a] : Matrix (Fin 2) (Fin 2) R) ^ (n + 1) =
      !![a ^ (n + 1), ((n + 1 : ℕ) : R) * a ^ n * b; 0, a ^ (n + 1)] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Nat.cast_add, Nat.cast_one]
    all_goals ring

private theorem integerTriangular_pow_upper_right_dvd (a b : ℤ) (n : ℕ) :
    (n : ℤ) ∣ ((!![a, b; 0, a] : Matrix (Fin 2) (Fin 2) ℤ) ^ n) 0 1 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [equalDiagonalTriangular_pow_succ]
    refine ⟨a ^ n * b, ?_⟩
    simp [mul_assoc]

private theorem integerMatrix_commute_translation_entries
    (M : Matrix (Fin 2) (Fin 2) ℤ)
    (h : Commute M !![1, -1; 0, 1]) :
    M 1 0 = 0 ∧ M 0 0 = M 1 1 := by
  have h₀ := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℤ => N 0 0) h.eq
  have h₁ := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℤ => N 0 1) h.eq
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h₀ h₁
  constructor <;> linarith

/-- Even among all integral matrices, the unit translation has no
nontrivial natural-power root. -/
theorem integerMatrix_translationInverse_pow_exponent
    (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ)
    (h : M ^ n = !![1, -1; 0, 1]) : n = 1 := by
  have hc : Commute M !![1, -1; 0, 1] := by
    rw [← h]
    exact Commute.self_pow M n
  obtain ⟨hc₀, hc₁⟩ := integerMatrix_commute_translation_entries M hc
  have hM : M = !![M 0 0, M 0 1; 0, M 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc₀, hc₁]
  have hd := integerTriangular_pow_upper_right_dvd (M 0 0) (M 0 1) n
  rw [← hM, h] at hd
  apply Nat.eq_one_of_dvd_one
  simpa [Int.natCast_dvd] using hd

/-- `T⁻¹` is primitive in the actual integral special-linear group. -/
theorem modular_T_inv_pow_exponent (M : SL(2, ℤ)) (n : ℕ)
    (h : M ^ n = ModularGroup.T⁻¹) : n = 1 := by
  apply integerMatrix_translationInverse_pow_exponent (M : Matrix (Fin 2) (Fin 2) ℤ) n
  simpa only [Matrix.SpecialLinearGroup.coe_pow, ModularGroup.coe_T_inv] using
    congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ)) h

/-- A natural-power root of the triangle cusp can only have exponent one.
This follows through the constructed integral representation, without
assuming faithfulness of that representation. -/
theorem triangleCuspGenerator_pow_root_exponent (g : TriangleGroup) (n : ℕ)
    (h : g ^ n = triangleCuspGenerator) : n = 1 := by
  apply modular_T_inv_pow_exponent (triangleModularLinearRepresentation g) n
  rw [← map_pow, h, triangleModularLinearRepresentation_cusp]

theorem triangleCuspGenerator_pow_eq_iff (g : TriangleGroup) (n : ℕ) :
    g ^ n = triangleCuspGenerator ↔ n = 1 ∧ g = triangleCuspGenerator := by
  constructor
  · intro h
    have hn := triangleCuspGenerator_pow_root_exponent g n h
    exact ⟨hn, by simpa only [hn, pow_one] using h⟩
  · rintro ⟨rfl, rfl⟩
    exact pow_one _

/-- The actual cusp generator is not a proper natural power. -/
theorem triangleCuspGenerator_not_proper_power (g : TriangleGroup) (n : ℕ) (hn : 1 < n) :
    g ^ n ≠ triangleCuspGenerator := by
  intro h
  have := triangleCuspGenerator_pow_root_exponent g n h
  omega

/-- The integer exponent of any cusp root has absolute value one. -/
theorem triangleCuspGenerator_zpow_root_exponent (g : TriangleGroup) (k : ℤ)
    (h : g ^ k = triangleCuspGenerator) : k.natAbs = 1 := by
  cases k with
  | ofNat n =>
    apply triangleCuspGenerator_pow_root_exponent g n
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using h
  | negSucc n =>
    apply triangleCuspGenerator_pow_root_exponent g⁻¹ (n + 1)
    simpa only [zpow_negSucc, inv_pow] using h

end Wikipedia.HopfProblem.SpecialPeriods
