import ErdosProblems.Erdos4.PrimitiveProfile
import ErdosProblems.Erdos4.SliceBounds

/-!
# The actual product-cutoff divisor coefficient vector

A label assigns each sieve prime either to one coordinate or to no
coordinate. Erasing labels preserves the product cutoff and increases the
decreasing profile. The square-root divisor factors separate exactly.
-/

open scoped BigOperators

namespace Erdos4.DivisorCoefficients

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

def totalDivisor (ell : P → ℕ) (a : P → Option (Fin k)) : ℕ :=
  ∏ p, if a p = none then 1 else ell p

def coordinateDivisor (ell : P → ℕ) (a : P → Option (Fin k)) (i : Fin k) : ℕ :=
  ∏ p, if a p = some i then ell p else 1

def erase (J : Finset P) (a : P → Option (Fin k)) (p : P) : Option (Fin k) :=
  if p ∈ J then none else a p

noncomputable def localWeight (ell : ℕ) : Option (Fin k) → ℝ
  | none => 1
  | some _ => (Real.sqrt ((ell : ℝ) - 1))⁻¹

noncomputable def normalization (ell : P → ℕ) (a : P → Option (Fin k)) : ℝ :=
  ∏ p, localWeight (ell p) (a p)

noncomputable def removedFactor (ell : P → ℕ) (J : Finset P) (a : P → Option (Fin k)) : ℝ :=
  ∏ p ∈ J, localWeight (ell p) (a p)

noncomputable def profileProduct (m : ℝ) (R : ℕ) (ell : P → ℕ) (a : P → Option (Fin k)) : ℝ :=
  ∏ i : Fin k, PrimitiveProfile.profile m k
    (Real.log (coordinateDivisor ell a i) / Real.log R)

noncomputable def coefficient (m : ℝ) (R : ℕ) (ell : P → ℕ) (a : P → Option (Fin k)) : ℝ :=
  if totalDivisor ell a ≤ R then profileProduct m R ell a * normalization ell a else 0

theorem localWeight_nonneg (ell : ℕ) (a : Option (Fin k)) : 0 ≤ localWeight ell a := by
  cases a <;> simp only [localWeight]
  · exact zero_le_one
  · exact inv_nonneg.mpr (Real.sqrt_nonneg _)

omit [DecidableEq P] in
theorem normalization_nonneg (ell : P → ℕ) (a : P → Option (Fin k)) :
    0 ≤ normalization ell a := Finset.prod_nonneg (fun p _hp => localWeight_nonneg (ell p) (a p))

omit [Fintype P] [DecidableEq P] in
theorem removedFactor_nonneg (ell : P → ℕ) (J : Finset P) (a : P → Option (Fin k)) :
    0 ≤ removedFactor ell J a := Finset.prod_nonneg (fun p _hp => localWeight_nonneg (ell p) (a p))

omit [DecidableEq P] in
theorem coordinateDivisor_pos (ell : P → ℕ) (hell : ∀ p, 0 < ell p)
    (a : P → Option (Fin k)) (i : Fin k) : 0 < coordinateDivisor ell a i := by
  unfold coordinateDivisor
  apply Finset.prod_pos
  intro p _hp
  split_ifs
  · exact hell p
  · exact Nat.zero_lt_one

omit [DecidableEq P] in
theorem totalDivisor_pos (ell : P → ℕ) (hell : ∀ p, 0 < ell p)
    (a : P → Option (Fin k)) : 0 < totalDivisor ell a := by
  unfold totalDivisor
  apply Finset.prod_pos
  intro p _hp
  split_ifs
  · exact Nat.zero_lt_one
  · exact hell p

theorem coordinateDivisor_erase_le (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p)
    (J : Finset P) (a : P → Option (Fin k)) (i : Fin k) :
    coordinateDivisor ell (erase J a) i ≤ coordinateDivisor ell a i := by
  unfold coordinateDivisor
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro p _hp
  by_cases hp : p ∈ J
  · simp only [erase, if_pos hp, reduceCtorEq, ↓reduceIte]
    split_ifs <;> simp_all
  · simp only [erase, if_neg hp]
    exact le_rfl

theorem totalDivisor_erase_le (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p)
    (J : Finset P) (a : P → Option (Fin k)) :
    totalDivisor ell (erase J a) ≤ totalDivisor ell a := by
  unfold totalDivisor
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro p _hp
  by_cases hp : p ∈ J
  · simp only [erase, if_pos hp, ↓reduceIte]
    split_ifs <;> simp_all
  · simp only [erase, if_neg hp]
    exact le_rfl

theorem normalization_erase (ell : P → ℕ) (J : Finset P) (a : P → Option (Fin k)) :
    normalization ell a = removedFactor ell J a * normalization ell (erase J a) := by
  have hlocal : ∀ p, localWeight (ell p) (a p) =
      (if p ∈ J then localWeight (ell p) (a p) else 1) * localWeight (ell p) (erase J a p) := by
    intro p
    by_cases hp : p ∈ J <;> simp [erase, hp, localWeight]
  have hJ : (∏ p : P, if p ∈ J then localWeight (ell p) (a p) else 1) = removedFactor ell J a := by
    rw [← Finset.prod_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, removedFactor]
  unfold normalization
  calc
    (∏ p, localWeight (ell p) (a p)) =
        ∏ p, (if p ∈ J then localWeight (ell p) (a p) else 1) * localWeight (ell p) (erase J a p) :=
      Finset.prod_congr rfl (fun p _hp => hlocal p)
    _ = _ := by rw [Finset.prod_mul_distrib, hJ]

omit [DecidableEq P] in
theorem profileProduct_nonneg {m : ℝ} (hm : 0 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (a : P → Option (Fin k)) : 0 ≤ profileProduct m R ell a := by
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  unfold profileProduct
  apply Finset.prod_nonneg
  intro i _hi
  exact (PrimitiveProfile.profile_pos hm (Nat.cast_nonneg _)
    (div_nonneg (Real.log_natCast_nonneg _) hlog.le)).le

omit [DecidableEq P] in
theorem coefficient_nonneg {m : ℝ} (hm : 0 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (a : P → Option (Fin k)) : 0 ≤ coefficient m R ell a := by
  unfold coefficient
  split_ifs
  · exact mul_nonneg (profileProduct_nonneg hm hR ell a) (normalization_nonneg ell a)
  · exact le_rfl

theorem profileProduct_le_erase {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P) (a : P → Option (Fin k)) :
    profileProduct m R ell a ≤ profileProduct m R ell (erase J a) := by
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  unfold profileProduct
  apply Finset.prod_le_prod
  · intro i _hi
    exact (PrimitiveProfile.profile_pos (by linarith) (Nat.cast_nonneg _)
      (div_nonneg (Real.log_natCast_nonneg _) hlog.le)).le
  · intro i _hi
    apply PrimitiveProfile.profile_antitoneOn hm (Nat.cast_nonneg _)
      (div_nonneg (Real.log_natCast_nonneg _) hlog.le)
      (div_nonneg (Real.log_natCast_nonneg _) hlog.le)
    apply div_le_div_of_nonneg_right _ hlog.le
    apply Real.log_le_log
    · exact_mod_cast coordinateDivisor_pos ell hell (erase J a) i
    · exact_mod_cast coordinateDivisor_erase_le ell hell J a i

/-- The actual monotone coefficient vector satisfies the erasure bound used
to control every conductor-coordinate slice. -/
theorem coefficient_le_removedFactor_mul_erase {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P) (a : P → Option (Fin k)) :
    coefficient m R ell a ≤ removedFactor ell J a * coefficient m R ell (erase J a) := by
  by_cases ha : totalDivisor ell a ≤ R
  · have he : totalDivisor ell (erase J a) ≤ R := (totalDivisor_erase_le ell hell J a).trans ha
    rw [coefficient, if_pos ha, coefficient, if_pos he, normalization_erase ell J a]
    have hh := mul_le_mul_of_nonneg_right (profileProduct_le_erase hm hR ell hell J a)
      (mul_nonneg (removedFactor_nonneg ell J a) (normalization_nonneg ell (erase J a)))
    nlinarith
  · rw [coefficient, if_neg ha]
    exact mul_nonneg (removedFactor_nonneg ell J a) (coefficient_nonneg (by linarith) hR ell _)

omit [DecidableEq P] in
theorem coefficient_none (m : ℝ) {R : ℕ} (hR : 1 ≤ R) (ell : P → ℕ) :
    coefficient (k := k) m R ell (fun _ => none) = 1 := by
  simp [coefficient, totalDivisor, coordinateDivisor, profileProduct, normalization,
    localWeight, PrimitiveProfile.profile_zero, hR]

theorem one_le_coefficient_energy (m : ℝ) {R : ℕ} (hR : 1 ≤ R) (ell : P → ℕ) :
    1 ≤ RestrictedProductNorm.energy (coefficient (k := k) m R ell) := by
  have hh := Finset.single_le_sum (s := (Finset.univ : Finset (P → Option (Fin k))))
    (f := fun a => coefficient m R ell a ^ 2) (fun a _ha => sq_nonneg _)
    (Finset.mem_univ (fun _ : P => (none : Option (Fin k))))
  simpa only [coefficient_none m hR ell, one_pow, RestrictedProductNorm.energy] using hh

end Erdos4.DivisorCoefficients
