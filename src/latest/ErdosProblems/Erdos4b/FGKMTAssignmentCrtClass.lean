/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentCompatibility
import ErdosProblems.Erdos4b.FGKMTIntegerCrt

/-!
# The exact CRT class of one assignment and one presieve residue

The moduli are the presieve modulus and each selected coefficient prime.
Absent primes contribute modulus one. This gives the literal period
`W * assignmentPrimeProduct`, including the empty assignment.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [Fintype α] [DecidableEq ι]

def assignmentPreSieveModulus (W : ℕ) (p : α → ℕ) (r : α → Option ι) : Option α → ℕ
  | none => W
  | some q => if r q = none then 1 else p q

def assignmentPreSieveResidue (v : ℤ) (a : ι → ℤ) (r : α → Option ι) : Option α → ℤ
  | none => v
  | some q => match r q with
    | none => 0
    | some i => -a i

omit [DecidableEq ι] in
theorem prod_assignmentPreSieveModulus (W : ℕ) (p : α → ℕ) (r : α → Option ι) :
    (∏ q, assignmentPreSieveModulus W p r q) = W * assignmentPrimeProduct p r := by
  rw [Fintype.prod_option]
  rfl

omit [Fintype α] [DecidableEq ι] in
theorem assignmentPreSieveModulus_pos {W : ℕ} {p : α → ℕ}
    (hW : 0 < W) (hp : ∀ q, 0 < p q) (r : α → Option ι) (q : Option α) :
    0 < assignmentPreSieveModulus W p r q := by
  cases q with
  | none => exact hW
  | some q =>
    change 0 < if r q = none then 1 else p q
    split_ifs
    · exact zero_lt_one
    · exact hp q

omit [Fintype α] [DecidableEq ι] in
theorem assignmentPreSieveModulus_pairwise {W : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (hcop : ∀ q, (p q).Coprime W) (r : α → Option ι) :
    Pairwise (fun q s => (assignmentPreSieveModulus W p r q).Coprime
      (assignmentPreSieveModulus W p r s)) := by
  intro q s hqs
  cases q with
  | none =>
    cases s with
    | none => exact (hqs rfl).elim
    | some s =>
      change W.Coprime (if r s = none then 1 else p s)
      split_ifs
      · exact Nat.coprime_one_right W
      · exact (hcop s).symm
  | some q =>
    cases s with
    | none =>
      change (if r q = none then 1 else p q).Coprime W
      split_ifs
      · exact Nat.coprime_one_left W
      · exact hcop q
    | some s =>
      change (if r q = none then 1 else p q).Coprime
        (if r s = none then 1 else p s)
      by_cases hq : r q = none
      · rw [if_pos hq]
        exact Nat.coprime_one_left _
      · rw [if_neg hq]
        split_ifs
        · exact Nat.coprime_one_right _
        · exact (Nat.coprime_primes (hp q) (hp s)).mpr
            (hinj.ne (fun hh => hqs (congrArg some hh)))

omit [Fintype α] [DecidableEq ι] in
theorem assignmentPreSieve_local_iff (W : ℕ) (p : α → ℕ) (v n : ℤ)
    (a : ι → ℤ) (r : α → Option ι) (q : α) :
    n ≡ assignmentPreSieveResidue v a r (some q)
      [ZMOD assignmentPreSieveModulus W p r (some q)] ↔
      ∀ i, r q = some i → (p q : ℤ) ∣ n + a i := by
  cases hr : r q with
  | none => simp [assignmentPreSieveResidue, assignmentPreSieveModulus, hr, Int.modEq_one]
  | some j =>
    simp only [assignmentPreSieveResidue, assignmentPreSieveModulus, hr,
      Option.some_ne_none, if_false, Option.some.injEq, forall_eq']
    rw [Int.modEq_iff_dvd, show -a j - n = -(n + a j) by ring, dvd_neg]

theorem exists_assignmentPreSieve_class {W : ℕ} (hW : 0 < W) {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hcop : ∀ q, (p q).Coprime W)
    (v : ℤ) (a : ι → ℤ) (r : α → Option ι) :
    ∃ c : ℤ, ∀ n : ℤ,
      (n ≡ v [ZMOD W] ∧ ∀ i, (assignmentPrimeTuple p r i : ℤ) ∣ n + a i) ↔
        n ≡ c [ZMOD (W * assignmentPrimeProduct p r : ℕ)] := by
  obtain ⟨c, hc⟩ := exists_integerCrt_class (assignmentPreSieveModulus W p r)
    (assignmentPreSieveModulus_pos hW (fun q => (hp q).pos) r)
    (assignmentPreSieveModulus_pairwise hp hinj hcop r) (assignmentPreSieveResidue v a r)
  refine ⟨c, fun n => ?_⟩
  rw [← prod_assignmentPreSieveModulus W p r, ← hc n,
    assignmentDivisorCondition_iff_local hp hinj]
  constructor
  · rintro ⟨hn, hd⟩ q
    cases q with
    | none => exact hn
    | some q => exact (assignmentPreSieve_local_iff W p v n a r q).mpr (hd q)
  · intro hn
    exact ⟨hn none, fun q => (assignmentPreSieve_local_iff W p v n a r q).mp (hn (some q))⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_assignmentPreSieve_class
