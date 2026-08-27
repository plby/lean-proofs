/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCommonWeights
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.ModEq

/-!
# Integer divisibility and the distinct roots of the actual forms

Each squarefree coordinate condition is exactly the conjunction of its
selected prime conditions. Distinct small shifts remain distinct modulo
every coefficient prime, since the label prime is larger than the radius.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [Fintype α] [DecidableEq ι]

theorem assignmentPrimeTuple_int_dvd_iff {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (r : α → Option ι) (i : ι) (n : ℤ) :
    (assignmentPrimeTuple p r i : ℤ) ∣ n ↔
      ∀ q, r q = some i → (p q : ℤ) ∣ n := by
  classical
  simp only [Int.natCast_dvd]
  constructor
  · intro hd q hq
    exact ((prime_dvd_assignmentPrimeTuple_iff hp hinj r q i).mpr hq).trans hd
  · intro hd
    apply Fintype.prod_dvd_of_isRelPrime
    · intro q s hqs
      apply Nat.coprime_iff_isRelPrime.mp
      have hcop := (Nat.coprime_primes (hp q) (hp s)).mpr (hinj.ne hqs)
      change (if r q = some i then p q else 1).Coprime
        (if r s = some i then p s else 1)
      by_cases hq : r q = some i
      · by_cases hs : r s = some i
        · simpa only [if_pos hq, if_pos hs] using hcop
        · rw [if_neg hs]
          exact Nat.coprime_one_right _
      · rw [if_neg hq]
        exact Nat.coprime_one_left _
    · intro q
      by_cases hq : r q = some i
      · simpa only [if_pos hq] using hd q hq
      · simp only [if_neg hq, one_dvd]

theorem assignmentDivisorCondition_iff_local {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (r : α → Option ι) (forms : ι → ℤ) :
    (∀ i, (assignmentPrimeTuple p r i : ℤ) ∣ forms i) ↔
      ∀ q i, r q = some i → (p q : ℤ) ∣ forms i := by
  simp only [assignmentPrimeTuple_int_dvd_iff hp hinj]
  exact forall_comm

omit [Fintype α] [DecidableEq ι] in
theorem smallShift_roots_distinct {Q P B : ℕ} (hcop : Q.Coprime P)
    (h : ι → ℕ) (hinj : Function.Injective h) (hsmall : ∀ i, h i < B) (hQ : B ≤ Q)
    {i j : ι} (hdiv : (Q : ℤ) ∣ (h i : ℤ) * P - (h j : ℤ) * P) : i = j := by
  have hm : h j * P ≡ h i * P [MOD Q] := by
    rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd]
    simpa only [Nat.cast_mul] using hdiv
  have hh : h j ≡ h i [MOD Q] := hm.cancel_right_of_coprime hcop
  exact hinj (hh.eq_of_lt_of_lt ((hsmall j).trans_le hQ)
    ((hsmall i).trans_le hQ)).symm

omit [Fintype α] in
theorem commonPrimeUniverse_shift_roots_distinct {k M R P : ℕ}
    (hsmall : ∀ q : ℕ, q.Prime → q ≤ 2 * k ^ 2 → q ∣ M)
    (hP : P.Prime) (hRP : R < P) (h : Fin k → ℕ) (hinj : Function.Injective h)
    (hshift : ∀ i, h i < 2 * k ^ 2) (q : commonPrimeUniverse M R)
    {i j : Fin k} (hdiv : (q.val : ℤ) ∣ (h i : ℤ) * P - (h j : ℤ) * P) : i = j := by
  have hq := commonPrimeUniverse_prime q
  have hqR := (mem_commonPrimeUniverse.mp q.property).2.1
  have hcop : q.val.Coprime P := (Nat.coprime_primes hq hP).mpr (by omega)
  exact smallShift_roots_distinct hcop h hinj hshift
    (commonPrimeUniverse_large hsmall q).le hdiv

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.assignmentDivisorCondition_iff_local
#print axioms Erdos4b.FGKMT.commonPrimeUniverse_shift_roots_distinct
