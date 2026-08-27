import ErdosProblems.Erdos4.FGKMTDivisorLabels
import ErdosProblems.Erdos4.FGKMTRationalLinearLaw

/-! The actual orthogonal sieve coefficients for the rational product profile. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open DivisorCoefficients RestrictedProductNorm Classical

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def rationalProfileProduct (b : ℝ) (ell : P → ℕ)
    (a : P → Option (Fin k)) : ℝ :=
  ∏ i : Fin k, logarithmicReciprocal b (coordinateDivisor ell a i)

noncomputable def rationalCoefficient (b : ℝ) (R : ℕ) (ell : P → ℕ)
    (a : P → Option (Fin k)) : ℝ :=
  if totalDivisor ell a ≤ R then rationalProfileProduct b ell a * normalization ell a else 0

noncomputable def rationalSieveTupleWeight (W : ℕ) (b : ℝ) (d : Fin k → ℕ) : ℝ :=
  ∏ i : Fin k, logarithmicReciprocal b (d i) ^ 2 * squarefreeHarmonicWeight W (d i)

theorem rationalSieveTupleWeight_nonneg (W : ℕ) (b : ℝ) (d : Fin k → ℕ) :
    0 ≤ rationalSieveTupleWeight W b d :=
  Finset.prod_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (squarefreeHarmonicWeight_nonneg W (d i)))

omit [DecidableEq P] in
theorem rationalProfileProduct_nonneg {b : ℝ} (hb : 0 ≤ b) (ell : P → ℕ)
    (a : P → Option (Fin k)) : 0 ≤ rationalProfileProduct b ell a :=
  Finset.prod_nonneg (fun _i _ => logarithmicReciprocal_nat_nonneg hb _)

omit [DecidableEq P] in
theorem rationalCoefficient_nonneg {b : ℝ} (hb : 0 ≤ b) (R : ℕ) (ell : P → ℕ)
    (a : P → Option (Fin k)) : 0 ≤ rationalCoefficient b R ell a := by
  unfold rationalCoefficient
  split_ifs
  · exact mul_nonneg (rationalProfileProduct_nonneg hb ell a) (normalization_nonneg ell a)
  · exact le_rfl

theorem rationalProfileProduct_le_erase {b : ℝ} (hb : 0 ≤ b)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P) (a : P → Option (Fin k)) :
    rationalProfileProduct b ell a ≤ rationalProfileProduct b ell (erase J a) := by
  unfold rationalProfileProduct
  apply Finset.prod_le_prod (fun i _ => logarithmicReciprocal_nat_nonneg hb _)
  intro i _
  apply logarithmicReciprocal_antitone hb
  · change (1 : ℝ) ≤ coordinateDivisor ell (erase J a) i
    exact_mod_cast (show 1 ≤ coordinateDivisor ell (erase J a) i from
      coordinateDivisor_pos ell hell (erase J a) i)
  · change (1 : ℝ) ≤ coordinateDivisor ell a i
    exact_mod_cast (show 1 ≤ coordinateDivisor ell a i from coordinateDivisor_pos ell hell a i)
  · exact_mod_cast coordinateDivisor_erase_le ell hell J a i

theorem rationalCoefficient_le_removedFactor_mul_erase {b : ℝ} (hb : 0 ≤ b)
    (R : ℕ) (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P)
    (a : P → Option (Fin k)) :
    rationalCoefficient b R ell a ≤ removedFactor ell J a * rationalCoefficient b R ell (erase J a) := by
  by_cases ha : totalDivisor ell a ≤ R
  · have he := (totalDivisor_erase_le ell hell J a).trans ha
    rw [rationalCoefficient, if_pos ha, rationalCoefficient, if_pos he, normalization_erase ell J a]
    have hh := mul_le_mul_of_nonneg_right (rationalProfileProduct_le_erase hb ell hell J a)
      (mul_nonneg (removedFactor_nonneg ell J a) (normalization_nonneg ell (erase J a)))
    exact hh.trans_eq (by ring)
  · rw [rationalCoefficient, if_neg ha]
    exact mul_nonneg (removedFactor_nonneg ell J a) (rationalCoefficient_nonneg hb R ell _)

omit [DecidableEq P] in
theorem rationalCoefficient_none (b : ℝ) {R : ℕ} (hR : 1 ≤ R) (ell : P → ℕ) :
    rationalCoefficient (k := k) b R ell (fun _ => none) = 1 := by
  simp [rationalCoefficient, rationalProfileProduct, totalDivisor, coordinateDivisor,
    normalization, localWeight, logarithmicReciprocal, hR]

theorem one_le_rationalCoefficient_energy (b : ℝ) {R : ℕ} (hR : 1 ≤ R) (ell : P → ℕ) :
    1 ≤ energy (rationalCoefficient (k := k) b R ell) := by
  have hh := Finset.single_le_sum (s := (Finset.univ : Finset (P → Option (Fin k))))
    (f := fun a => rationalCoefficient b R ell a ^ 2) (fun a _ => sq_nonneg _)
    (Finset.mem_univ (fun _ : P => (none : Option (Fin k))))
  simpa only [rationalCoefficient_none b hR ell, one_pow, energy] using hh

theorem rationalCoefficient_sq (b : ℝ) (R : ℕ) (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell) {W : ℕ}
    (hcop : ∀ p, (ell p).Coprime W) (a : P → Option (Fin k)) :
    rationalCoefficient b R ell a ^ 2 =
      if totalDivisor ell a ≤ R then rationalSieveTupleWeight W b (coordinateDivisor ell a) else 0 := by
  by_cases ha : totalDivisor ell a ≤ R
  · rw [rationalCoefficient, if_pos ha, if_pos ha, mul_pow,
      normalization_sq_eq_harmonic_product ell hprime hinj hcop a]
    unfold rationalProfileProduct rationalSieveTupleWeight
    rw [← Finset.prod_pow, Finset.prod_mul_distrib]
  · simp only [rationalCoefficient, if_neg ha, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

omit [DecidableEq P] in
theorem coordinateDivisor_le_totalDivisor (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p)
    (a : P → Option (Fin k)) (i : Fin k) : coordinateDivisor ell a i ≤ totalDivisor ell a := by
  unfold coordinateDivisor totalDivisor
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro p _
  cases ha : a p with
  | none => simp
  | some j =>
    simp only [Option.some.injEq, reduceCtorEq, if_false]
    split_ifs
    · exact le_rfl
    · exact hell p

end Erdos4.FGKMT
