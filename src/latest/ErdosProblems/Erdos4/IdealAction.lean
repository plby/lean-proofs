import ErdosProblems.Erdos4.IdealProjection

/-!
# Exact ideal projection action on the cutoff vector

Only the anchor coordinate changes inside an ideal-projection fiber. The
other profile factors and the output divisor normalization separate
exactly, leaving a positive reciprocal-totient fiber sum with the genuine
product cutoff.
-/

open scoped BigOperators

namespace Erdos4.IdealAction

open DivisorCoefficients IdealProjection

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

def Compatible (j : Fin k) (a b : P → Option (Fin k)) : Prop :=
  ∀ p, freeze j (a p) = freeze j (b p)

noncomputable def otherProfile (m : ℝ) (R : ℕ) (ell : P → ℕ) (j : Fin k)
    (a : P → Option (Fin k)) : ℝ :=
  ∏ i ∈ Finset.univ.erase j, PrimitiveProfile.profile m k
    (Real.log (coordinateDivisor ell a i) / Real.log R)

noncomputable def activeDensity (ell : P → ℕ) (j : Fin k) (a : P → Option (Fin k)) : ℝ :=
  ∏ p, if freeze j (a p) = none then ((ell p : ℝ) - 1) / ell p else 1

noncomputable def fiberWeight (ell : P → ℕ) (j : Fin k)
    (a b : P → Option (Fin k)) : ℝ :=
  ∏ p, if freeze j (a p) = none then localWeight (ell p) (b p) ^ 2 else 1

omit [DecidableEq P] in
theorem coordinateDivisor_eq_of_compatible (ell : P → ℕ) (j i : Fin k) (hij : i ≠ j)
    (a b : P → Option (Fin k)) (hab : Compatible j a b) :
    coordinateDivisor ell a i = coordinateDivisor ell b i := by
  unfold coordinateDivisor
  apply Finset.prod_congr rfl
  intro p _hp
  have heq : (a p = some i) ↔ (b p = some i) := by
    rw [← freeze_eq_some_iff j i hij (a p), hab p, freeze_eq_some_iff j i hij (b p)]
  simp only [heq]

omit [DecidableEq P] in
theorem otherProfile_eq_of_compatible (m : ℝ) (R : ℕ) (ell : P → ℕ) (j : Fin k)
    (a b : P → Option (Fin k)) (hab : Compatible j a b) :
    otherProfile m R ell j a = otherProfile m R ell j b := by
  unfold otherProfile
  apply Finset.prod_congr rfl
  intro i hi
  rw [coordinateDivisor_eq_of_compatible ell j i (Finset.ne_of_mem_erase hi) a b hab]

omit [DecidableEq P] in
theorem profileProduct_eq_otherProfile (m : ℝ) (R : ℕ) (ell : P → ℕ) (j : Fin k)
    (a b : P → Option (Fin k)) (hab : Compatible j a b) :
    profileProduct m R ell b = otherProfile m R ell j a *
      PrimitiveProfile.profile m k (Real.log (coordinateDivisor ell b j) / Real.log R) := by
  rw [otherProfile_eq_of_compatible m R ell j a b hab]
  unfold profileProduct otherProfile
  rw [← Finset.mul_prod_erase Finset.univ
    (fun i : Fin k => PrimitiveProfile.profile m k
      (Real.log (coordinateDivisor ell b i) / Real.log R)) (Finset.mem_univ j)]
  ring

omit [DecidableEq P] in
theorem kernelProduct_zero_of_not_compatible (ell : P → ℕ) (j : Fin k)
    (a b : P → Option (Fin k)) (hab : ¬Compatible j a b) :
    (∏ p, kernel (ell p : ℝ) j (a p) (b p)) = 0 := by
  have hex : ∃ p, freeze j (a p) ≠ freeze j (b p) := by
    simpa only [Compatible, not_forall] using hab
  obtain ⟨p, hp⟩ := hex
  exact Finset.prod_eq_zero (Finset.mem_univ p)
    (kernel_eq_zero_of_freeze_ne (ell p : ℝ) j (a p) (b p) hp)

omit [DecidableEq P] in
theorem kernelProduct_mul_normalization (ell : P → ℕ) (hell : ∀ p, 2 ≤ ell p)
    (j : Fin k) (a b : P → Option (Fin k)) (hab : Compatible j a b) :
    (∏ p, kernel (ell p : ℝ) j (a p) (b p)) * normalization ell b =
      normalization ell a * activeDensity ell j a * fiberWeight ell j a b := by
  unfold normalization activeDensity fiberWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [weighted_kernel_formula (hell p) j (a p) (b p), if_pos (hab p)]
  split_ifs <;> ring

noncomputable def fiberSum (m : ℝ) (R : ℕ) (ell : P → ℕ) (j : Fin k)
    (a : P → Option (Fin k)) : ℝ := by
  classical
  exact ∑ b : P → Option (Fin k), if Compatible j a b ∧ totalDivisor ell b ≤ R then
    PrimitiveProfile.profile m k (Real.log (coordinateDivisor ell b j) / Real.log R) *
      fiberWeight ell j a b else 0

/-- Exact separation of the genuine product-cutoff ideal projection. -/
theorem action_coefficient (m : ℝ) (R : ℕ) (ell : P → ℕ) (hell : ∀ p, 2 ≤ ell p)
    (j : Fin k) (a : P → Option (Fin k)) :
    ProjectionKernel.action (ProjectionKernel.tensor (fun p => normal (ell p : ℝ) j))
      (coefficient m R ell) a =
      normalization ell a * otherProfile m R ell j a * activeDensity ell j a *
        fiberSum m R ell j a := by
  classical
  unfold ProjectionKernel.action ProjectionKernel.tensor fiberSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  change (∏ p, kernel (ell p : ℝ) j (a p) (b p)) * coefficient m R ell b = _
  by_cases hab : Compatible j a b
  · by_cases hb : totalDivisor ell b ≤ R
    · rw [if_pos ⟨hab, hb⟩, coefficient, if_pos hb,
        profileProduct_eq_otherProfile m R ell j a b hab]
      calc
        (∏ p, kernel (ell p : ℝ) j (a p) (b p)) *
            (otherProfile m R ell j a * PrimitiveProfile.profile m k
              (Real.log (coordinateDivisor ell b j) / Real.log R) * normalization ell b) =
            (otherProfile m R ell j a * PrimitiveProfile.profile m k
              (Real.log (coordinateDivisor ell b j) / Real.log R)) *
                ((∏ p, kernel (ell p : ℝ) j (a p) (b p)) * normalization ell b) := by ring
        _ = _ := by rw [kernelProduct_mul_normalization ell hell j a b hab]; ring
    · have hconj : ¬(Compatible j a b ∧ totalDivisor ell b ≤ R) := fun hh => hb hh.2
      simp only [coefficient, if_neg hb, if_neg hconj, mul_zero]
  · rw [if_neg (fun hh => hab hh.1), kernelProduct_zero_of_not_compatible ell j a b hab,
      zero_mul, mul_zero]

theorem action_coefficient_nonneg {m : ℝ} (hm : 0 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 2 ≤ ell p) (j : Fin k) (a : P → Option (Fin k)) :
    0 ≤ ProjectionKernel.action (ProjectionKernel.tensor (fun p => normal (ell p : ℝ) j))
      (coefficient m R ell) a := by
  apply Finset.sum_nonneg
  intro b _hb
  apply mul_nonneg _ (coefficient_nonneg hm hR ell b)
  exact Finset.prod_nonneg (fun p _hp => kernel_nonneg (by exact_mod_cast hell p) j (a p) (b p))

omit [DecidableEq P] in
theorem density_product_le_active (ell : P → ℕ) (hell : ∀ p, 2 ≤ ell p)
    (j : Fin k) (a : P → Option (Fin k)) :
    (∏ p, ((ell p : ℝ) - 1) / ell p) ≤ activeDensity ell j a := by
  unfold activeDensity
  apply Finset.prod_le_prod
  · intro p _hp
    have hp : (1 : ℝ) < ell p := by exact_mod_cast hell p
    exact div_nonneg (by linarith) (by linarith)
  · intro p _hp
    split_ifs
    · exact le_rfl
    · have hp : (0 : ℝ) < ell p := by exact_mod_cast (show 0 < ell p by have := hell p; omega)
      exact (div_le_one hp).mpr (by linarith)

/-- The supported-vector action identity has no division by a possibly
vanishing coefficient. Only the positive profile coordinate is divided out. -/
theorem action_coefficient_eq_ratio {m : ℝ} (hm : 0 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 2 ≤ ell p) (j : Fin k)
    (a : P → Option (Fin k)) (ha : totalDivisor ell a ≤ R) :
    ProjectionKernel.action (ProjectionKernel.tensor (fun p => normal (ell p : ℝ) j))
      (coefficient m R ell) a =
      coefficient m R ell a * activeDensity ell j a * fiberSum m R ell j a /
        PrimitiveProfile.profile m k (Real.log (coordinateDivisor ell a j) / Real.log R) := by
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hg := PrimitiveProfile.profile_pos hm (Nat.cast_nonneg k)
    (div_nonneg (Real.log_natCast_nonneg (coordinateDivisor ell a j)) hlog.le)
  rw [action_coefficient m R ell hell j a, coefficient, if_pos ha,
    profileProduct_eq_otherProfile m R ell j a a (fun _ => rfl)]
  field_simp

end Erdos4.IdealAction
