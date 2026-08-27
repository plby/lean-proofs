/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Fintype.BigOperators

/-!
# Prime assignments and actual divisor tuples

Each label carries a distinct prime and is either absent or assigned to
one coordinate. The associated integer tuple is injective, has positive
coordinates, and coordinate divisibility is exactly assignment extension.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [Fintype α] [DecidableEq ι]

def assignmentPrimeTuple (p : α → ℕ) (r : α → Option ι) (i : ι) : ℕ :=
  ∏ q, if r q = some i then p q else 1

def assignmentPrimeProduct (p : α → ℕ) (r : α → Option ι) : ℕ :=
  ∏ q, if r q = none then 1 else p q

def AssignmentExtends (d r : α → Option ι) : Prop :=
  ∀ q i, d q = some i → r q = some i

theorem assignmentPrimeTuple_pos {p : α → ℕ} (hp : ∀ q, 0 < p q)
    (r : α → Option ι) (i : ι) : 0 < assignmentPrimeTuple p r i := by
  apply Finset.prod_pos
  intro q _hq
  split_ifs
  · exact hp q
  · exact zero_lt_one

omit [DecidableEq ι] in
theorem assignmentPrimeProduct_pos {p : α → ℕ} (hp : ∀ q, 0 < p q)
    (r : α → Option ι) : 0 < assignmentPrimeProduct p r := by
  apply Finset.prod_pos
  intro q _hq
  split_ifs
  · exact zero_lt_one
  · exact hp q

theorem prod_assignmentPrimeTuple [Fintype ι] (p : α → ℕ) (r : α → Option ι) :
    (∏ i, assignmentPrimeTuple p r i) = assignmentPrimeProduct p r := by
  classical
  unfold assignmentPrimeTuple assignmentPrimeProduct
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro q _hq
  cases r q with
  | none => simp
  | some i => simp

theorem prime_dvd_assignmentPrimeTuple_iff {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (r : α → Option ι) (q : α) (i : ι) :
    p q ∣ assignmentPrimeTuple p r i ↔ r q = some i := by
  classical
  unfold assignmentPrimeTuple
  constructor
  · intro h
    obtain ⟨s, _hs, hdiv⟩ := ((hp q).prime.dvd_finsetProd_iff _).mp h
    by_cases hsi : r s = some i
    · rw [if_pos hsi] at hdiv
      have heq : q = s := hinj ((Nat.prime_dvd_prime_iff_eq (hp q) (hp s)).mp hdiv)
      simpa only [heq] using hsi
    · rw [if_neg hsi] at hdiv
      exact ((hp q).ne_one (Nat.dvd_one.mp hdiv)).elim
  · intro h
    exact (by simp only [if_pos h, dvd_refl] : p q ∣ if r q = some i then p q else 1).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ q))

theorem assignmentExtends_iff_coordinate_dvd {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (d r : α → Option ι) :
    AssignmentExtends d r ↔ ∀ i, assignmentPrimeTuple p d i ∣ assignmentPrimeTuple p r i := by
  classical
  constructor
  · intro h i
    apply Finset.prod_dvd_prod_of_dvd
    intro q _hq
    by_cases hdi : d q = some i
    · simp only [hdi, h q i hdi, if_true, dvd_refl]
    · simp only [if_neg hdi, one_dvd]
  · intro h q i hdi
    apply (prime_dvd_assignmentPrimeTuple_iff hp hinj r q i).mp
    exact ((prime_dvd_assignmentPrimeTuple_iff hp hinj d q i).mpr hdi).trans (h i)

theorem assignmentPrimeTuple_injective {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) :
    Function.Injective (assignmentPrimeTuple p : (α → Option ι) → ι → ℕ) := by
  intro r s hrs
  funext q
  have hsel (i : ι) : r q = some i ↔ s q = some i := by
    rw [← prime_dvd_assignmentPrimeTuple_iff hp hinj r q i,
      ← prime_dvd_assignmentPrimeTuple_iff hp hinj s q i, hrs]
  cases hr : r q with
  | none =>
    cases hs : s q with
    | none => rfl
    | some i =>
      have h := (hsel i).mpr hs
      rw [hr] at h
      cases h
  | some i => exact ((hsel i).mp hr).symm

omit [DecidableEq ι] in
theorem assignmentPrimeProduct_squarefree {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (r : α → Option ι) : Squarefree (assignmentPrimeProduct p r) := by
  classical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro q _hq s _hs hqs
    apply Nat.coprime_iff_isRelPrime.mp
    have hcop := (Nat.coprime_primes (hp q) (hp s)).mpr (hinj.ne hqs)
    by_cases hq : r q = none
    · simp [hq]
    · by_cases hs : r s = none
      · simp [hq, hs]
      · simpa only [if_neg hq, if_neg hs] using hcop
  · intro q _hq
    split_ifs
    · exact squarefree_one
    · exact (hp q).squarefree

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.assignmentExtends_iff_coordinate_dvd
#print axioms Erdos4b.FGKMT.assignmentPrimeTuple_injective
#print axioms Erdos4b.FGKMT.assignmentPrimeProduct_squarefree
