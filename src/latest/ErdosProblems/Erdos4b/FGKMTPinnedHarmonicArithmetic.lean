/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedEulerRegroup

/-! # Literal rough weights of the pinned divisor, including excluded primes -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι κ : Type*} [Fintype α]

theorem prime_dvd_assignmentPrimeProduct_iff {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (r : α → Option ι) (q : α) :
    p q ∣ assignmentPrimeProduct p r ↔ r q ≠ none := by
  classical
  constructor
  · intro h
    obtain ⟨s, _hs, hdiv⟩ := ((hp q).prime.dvd_finsetProd_iff _).mp h
    by_cases hs : r s = none
    · rw [if_pos hs] at hdiv
      exact ((hp q).ne_one (Nat.dvd_one.mp hdiv)).elim
    · rw [if_neg hs] at hdiv
      have heq := hinj ((Nat.prime_dvd_prime_iff_eq (hp q) (hp s)).mp hdiv)
      simpa only [heq] using hs
  · intro h
    exact (by simp only [if_neg h, dvd_refl] : p q ∣ if r q = none then 1 else p q).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ q))

theorem assignmentScalarWeight_eq_rough_masked {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (M : ℕ)
    (g : ℕ → ℝ) (r : α → Option ι) :
    assignmentScalarWeight (fun q => if p q ∣ M then 0 else 1 / g (p q)) r =
      roughSieveWeight M g (assignmentPrimeProduct p r) := by
  rw [assignmentScalarWeight_eq_primeFactors hp hinj (fun l => if l ∣ M then 0 else 1 / g l),
    roughSieveWeight, squarefreePrimeWeight_apply_of_squarefree _
      (assignmentPrimeProduct_squarefree hp hinj r)]

theorem assignmentWeight_away_from_tuple_eq_rough {M : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hM : ∀ q, ¬p q ∣ M)
    (g : ℕ → ℝ) (r : α → Option ι) (a : α → Option κ) :
    assignmentScalarWeight (fun q => if r q = none then 1 / g (p q) else 0) a =
      roughSieveWeight (M * assignmentPrimeProduct p r) g (assignmentPrimeProduct p a) := by
  classical
  rw [← assignmentScalarWeight_eq_rough_masked hp hinj]
  apply Finset.prod_congr rfl
  intro q _hq
  have hd : p q ∣ M * assignmentPrimeProduct p r ↔ r q ≠ none := by
    simp only [(hp q).dvd_mul, hM q, false_or, prime_dvd_assignmentPrimeProduct_iff hp hinj]
  by_cases ha : a q = none <;> by_cases hr : r q = none <;> simp [ha, hr, hd]

theorem pinnedDivisorFactor_eq_rough {m M : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hM : ∀ q, ¬p q ∣ M)
    (r : α → Option (Fin m)) (a : α → Option Unit) :
    pinnedDivisorFactor p r a = roughSieveWeight (M * assignmentPrimeProduct p r)
      (fun l => (l : ℝ) - (m + 1)) (assignmentPrimeProduct p a) := by
  rw [pinnedDivisorFactor_eq_scalar]
  exact assignmentWeight_away_from_tuple_eq_rough hp hinj hM
    (fun l => (l : ℝ) - (m + 1)) r a

theorem pinnedHarmonicWeight_eq_rough {m M : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hM : ∀ q, ¬p q ∣ M)
    (r : α → Option (Fin m)) (a : α → Option Unit) :
    pinnedHarmonicWeight p r a = roughSieveWeight (M * assignmentPrimeProduct p r)
      (fun l => pinnedLocalDenominator (m + 1) l) (assignmentPrimeProduct p a) :=
  assignmentWeight_away_from_tuple_eq_rough hp hinj hM
    (fun l => pinnedLocalDenominator (m + 1) l) r a

theorem pinnedUnshiftedValue_eq_rough [DecidableEq α] {m M R : ℕ} (hm : 1 ≤ m)
    {p : α → ℕ} (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (hM : ∀ q, ¬p q ∣ M) (hrough : ∀ q, 2 * (m + 1) ^ 2 < p q)
    (j : Fin (m + 1)) (r : α → Option (Fin m)) :
    pinnedUnshiftedValue m R p j r =
      (pinnedBaseFactor p r * pinnedBaseEulerProduct p r) *
        ∑ a : α → Option Unit,
          roughSieveWeight (M * assignmentPrimeProduct p r)
            (fun l => pinnedLocalDenominator (m + 1) l) (assignmentPrimeProduct p a) *
          sieveProfile (m + 1) (m + 1) (sieveLogTuple R (pinnedBaseTuple p j r a)) := by
  rw [pinnedUnshiftedValue_eq_harmonic hm hrough]
  simp only [pinnedHarmonicWeight_eq_rough hp hinj hM]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.assignmentWeight_away_from_tuple_eq_rough
#print axioms Erdos4b.FGKMT.pinnedHarmonicWeight_eq_rough
#print axioms Erdos4b.FGKMT.pinnedUnshiftedValue_eq_rough
