/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCommonPinnedCoefficients
import ErdosProblems.Erdos4b.FGKMTAssignmentDivisibility

/-!
# The original divisor weight when one form is prime

An external prime value forces the pinned divisor to be one. The exact
coordinate inclusion then identifies the original finite sum with the
restricted coefficients already used in the pinned quadratic mean.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] [Fintype α] in
theorem mapPrimeAssignment_injective {ι κ : Type*} (e : ι ↪ κ) :
    Function.Injective (mapPrimeAssignment (α := α) e) := by
  intro r s h
  funext q
  have hq := congrFun h q
  cases hr : r q with
  | none =>
      cases hs : s q with
      | none => rfl
      | some i => simp [mapPrimeAssignment, hr, hs] at hq
  | some i =>
      cases hs : s q with
      | none => simp [mapPrimeAssignment, hr, hs] at hq
      | some l =>
          simp only [mapPrimeAssignment, hr, hs, Option.map_some, Option.some.injEq] at hq
          exact congrArg some (e.injective hq)

omit [DecidableEq α] in
theorem assignmentDivisorCondition_map_unpinned {m : ℕ} (p : α → ℕ)
    (j : Fin (m + 1)) (d : α → Option (Fin m)) (forms : Fin (m + 1) → ℤ) :
    (∀ i, (assignmentPrimeTuple p (mapPrimeAssignment j.succAboveEmb d) i : ℤ) ∣ forms i) ↔
      ∀ i, (assignmentPrimeTuple p d i : ℤ) ∣ forms (j.succAbove i) := by
  rw [Fin.forall_iff_succAbove j]
  have hpin := mapPrimeAssignment_tuple_missing p j.succAboveEmb d j (by
    intro i
    simp)
  have himage (i : Fin m) :
      assignmentPrimeTuple p (mapPrimeAssignment j.succAboveEmb d) (j.succAbove i) =
        assignmentPrimeTuple p d i := mapPrimeAssignment_tuple_image p j.succAboveEmb d i
  rw [hpin]
  simp only [Nat.cast_one, one_dvd, true_and, himage]

omit [DecidableEq α] in
theorem assignmentPrimeTuple_eq_one_of_dvd_external_prime {m Q : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hQ : Q.Prime)
    (hnot : ∀ q, p q ≠ Q) (j : Fin (m + 1)) (d : α → Option (Fin (m + 1)))
    (hd : (assignmentPrimeTuple p d j : ℤ) ∣ (Q : ℤ)) :
    assignmentPrimeTuple p d j = 1 := by
  apply (assignmentPrimeTuple_eq_one_iff hp d j).mpr
  intro q hq
  have hdiv : p q ∣ Q := by
    exact_mod_cast (assignmentPrimeTuple_int_dvd_iff hp hinj d j (Q : ℤ)).mp hd q hq
  exact hnot q ((Nat.dvd_prime hQ).mp hdiv |>.resolve_left (hp q).ne_one)

open scoped Classical in
def commonPinnedDivisorWeight (m R : ℕ) (p : α → ℕ) (j : Fin (m + 1))
    (forms : Fin m → ℤ) : ℝ :=
  (∑ d : α → Option (Fin m),
    if ∀ i, (assignmentPrimeTuple p d i : ℤ) ∣ forms i then
      commonPinnedCoefficient m R p j d else 0) ^ 2

theorem commonDivisorWeight_eq_pinned {m R Q : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hQ : Q.Prime)
    (hnot : ∀ q, p q ≠ Q) (j : Fin (m + 1)) (forms : Fin (m + 1) → ℤ)
    (hpin : forms j = Q) :
    commonDivisorWeight (m + 1) R p forms =
      commonPinnedDivisorWeight m R p j (fun i => forms (j.succAbove i)) := by
  classical
  unfold commonDivisorWeight commonPinnedDivisorWeight
  congr 1
  symm
  apply Finset.sum_bij_ne_zero (fun d _hd _hz => mapPrimeAssignment j.succAboveEmb d)
  · intro d _hd _hz
    exact Finset.mem_univ _
  · intro d _hd _hz e _he _hez hde
    exact mapPrimeAssignment_injective j.succAboveEmb hde
  · intro s _hs hszero
    have hdiv : ∀ i, (assignmentPrimeTuple p s i : ℤ) ∣ forms i := by
      by_contra hh
      simp only [if_neg hh] at hszero
      exact hszero rfl
    have hpinDiv : (assignmentPrimeTuple p s j : ℤ) ∣ (Q : ℤ) := by
      simpa only [hpin] using hdiv j
    have hone := assignmentPrimeTuple_eq_one_of_dvd_external_prime hp hinj hQ hnot j s hpinDiv
    obtain ⟨d, rfl⟩ := (exists_map_unpinned_iff_divisor_one hp j s).mpr hone
    refine ⟨d, Finset.mem_univ _, ?_, rfl⟩
    simpa only [assignmentDivisorCondition_map_unpinned, commonPinnedCoefficient] using hszero
  · intro d _hd _hz
    simp only [assignmentDivisorCondition_map_unpinned, commonPinnedCoefficient]

theorem commonPrimeSieveWeight_at_prime_pin {m W M R P Q : ℕ} (hQ : Q.Prime)
    (hRQ : R < Q) (y : ℝ) (h : Fin (m + 1) → ℕ) (j : Fin (m + 1)) :
    commonPrimeSieveWeight (m + 1) W M R y h P ((Q : ℤ) - (h j : ℤ) * P) =
      if |(((Q : ℤ) - (h j : ℤ) * P : ℤ) : ℝ)| ≤ y ∧
          (∏ i, ((Q : ℤ) - (h j : ℤ) * P + (h i : ℤ) * P).natAbs).Coprime W then
        commonPinnedDivisorWeight m R (fun q : commonPrimeUniverse M R => q.val) j
          (fun i => (Q : ℤ) - (h j : ℤ) * P + (h (j.succAbove i) : ℤ) * P)
      else 0 := by
  unfold commonPrimeSieveWeight
  split_ifs
  · apply commonDivisorWeight_eq_pinned commonPrimeUniverse_prime Subtype.val_injective hQ
    · intro q
      have hqR := (mem_commonPrimeUniverse.mp q.property).2.1
      omega
    · ring
  · rfl

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonDivisorWeight_eq_pinned
#print axioms Erdos4b.FGKMT.commonPrimeSieveWeight_at_prime_pin
