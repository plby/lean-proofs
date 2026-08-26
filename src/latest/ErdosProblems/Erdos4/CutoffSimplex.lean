import ErdosProblems.Erdos4.IdealAction

/-!
# The actual divisor cutoff gives the variational simplex

Products of coordinate divisors recover the total divisor exactly. Hence
the logarithmic coordinates of every supported coefficient are
nonnegative and have sum at most one, with the anchor-completion endpoint
given by the logarithm of its complementary divisor.
-/

open scoped BigOperators

namespace Erdos4.CutoffSimplex

open DivisorCoefficients

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

theorem totalDivisor_eq_prod_coordinates (ell : P → ℕ) (a : P → Option (Fin k)) :
    totalDivisor ell a = ∏ i : Fin k, coordinateDivisor ell a i := by
  unfold totalDivisor coordinateDivisor
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p _hp
  cases hp : a p with
  | none => simp
  | some i => simp

theorem log_totalDivisor (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p)
    (a : P → Option (Fin k)) :
    Real.log (totalDivisor ell a) = ∑ i : Fin k, Real.log (coordinateDivisor ell a i) := by
  rw [totalDivisor_eq_prod_coordinates, Nat.cast_prod, Real.log_prod]
  intro i _hi
  exact_mod_cast (coordinateDivisor_pos ell hell a i).ne'

noncomputable def coordinate (R : ℕ) (ell : P → ℕ) (a : P → Option (Fin k)) (i : Fin k) : ℝ :=
  Real.log (coordinateDivisor ell a i) / Real.log R

theorem coordinate_nonneg {R : ℕ} (ell : P → ℕ)
    (a : P → Option (Fin k)) (i : Fin k) : 0 ≤ coordinate R ell a i := by
  exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

theorem sum_coordinate_le_one {R : ℕ} (hR : 2 ≤ R) (ell : P → ℕ)
    (hell : ∀ p, 1 ≤ ell p) (a : P → Option (Fin k)) (ha : totalDivisor ell a ≤ R) :
    (∑ i : Fin k, coordinate R ell a i) ≤ 1 := by
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  unfold coordinate
  rw [← Finset.sum_div, ← log_totalDivisor ell hell a]
  apply (div_le_one hlog).mpr
  exact Real.log_le_log (by exact_mod_cast totalDivisor_pos ell hell a) (by exact_mod_cast ha)

theorem coordinate_le_one {R : ℕ} (hR : 2 ≤ R) (ell : P → ℕ)
    (hell : ∀ p, 1 ≤ ell p) (a : P → Option (Fin k)) (ha : totalDivisor ell a ≤ R) (i : Fin k) :
    coordinate R ell a i ≤ 1 := by
  exact (Finset.single_le_sum (fun j _hj => coordinate_nonneg ell a j) (Finset.mem_univ i)).trans
    (sum_coordinate_le_one hR ell hell a ha)

def cofactor (ell : P → ℕ) (j : Fin k) (a : P → Option (Fin k)) : ℕ :=
  totalDivisor ell (fun p => IdealProjection.freeze j (a p))

theorem cofactor_mul_coordinateDivisor (ell : P → ℕ) (j : Fin k) (a : P → Option (Fin k)) :
    cofactor ell j a * coordinateDivisor ell a j = totalDivisor ell a := by
  unfold cofactor totalDivisor coordinateDivisor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _hp
  cases hp : a p with
  | none => simp [IdealProjection.freeze, hp]
  | some i =>
    by_cases hij : i = j <;> simp [IdealProjection.freeze, hp, hij]

theorem cofactor_pos (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (j : Fin k)
    (a : P → Option (Fin k)) : 0 < cofactor ell j a := totalDivisor_pos ell hell _

theorem cofactor_le_totalDivisor (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (j : Fin k)
    (a : P → Option (Fin k)) : cofactor ell j a ≤ totalDivisor ell a := by
  rw [← cofactor_mul_coordinateDivisor ell j a]
  exact le_mul_of_one_le_right (Nat.zero_le _) (coordinateDivisor_pos ell hell a j)

/-- The argument of the profile primitive is exactly the logarithmic
completion interval for the anchor coordinate. -/
theorem completion_parameter_eq {R : ℕ} (hR : 2 ≤ R) (ell : P → ℕ)
    (hell : ∀ p, 1 ≤ ell p) (j : Fin k) (a : P → Option (Fin k)) :
    1 - (∑ i : Fin k, coordinate R ell a i) + coordinate R ell a j =
      (Real.log R - Real.log (cofactor ell j a)) / Real.log R := by
  have hlog : Real.log (R : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hR)).ne'
  have hc : (cofactor ell j a : ℝ) ≠ 0 := by exact_mod_cast (cofactor_pos ell hell j a).ne'
  have hd : (coordinateDivisor ell a j : ℝ) ≠ 0 := by
    exact_mod_cast (coordinateDivisor_pos ell hell a j).ne'
  unfold coordinate
  rw [← Finset.sum_div, ← log_totalDivisor ell hell a,
    ← cofactor_mul_coordinateDivisor ell j a, Nat.cast_mul, Real.log_mul hc hd]
  field_simp
  ring

end Erdos4.CutoffSimplex
