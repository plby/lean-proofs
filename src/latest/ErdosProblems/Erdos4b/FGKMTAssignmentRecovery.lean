/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentArithmetic

/-!
# Recovering every supported squarefree divisor tuple

Squarefreeness of the whole product forces a prime to occur in at most
one coordinate. Assigning each available prime to that coordinate gives
the inverse to the integer-tuple map; the finite model loses no tuple.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [Fintype α] [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
theorem prime_dvd_assignmentPrimeTuple_iff_exists {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) {l : ℕ} (hl : l.Prime)
    (r : α → Option ι) (i : ι) :
    l ∣ assignmentPrimeTuple p r i ↔ ∃ q, r q = some i ∧ p q = l := by
  classical
  constructor
  · intro h
    obtain ⟨q, _hq, hdiv⟩ := (hl.prime.dvd_finsetProd_iff _).mp h
    by_cases hqi : r q = some i
    · rw [if_pos hqi] at hdiv
      exact ⟨q, hqi, ((Nat.prime_dvd_prime_iff_eq hl (hp q)).mp hdiv).symm⟩
    · rw [if_neg hqi] at hdiv
      exact (hl.ne_one (Nat.dvd_one.mp hdiv)).elim
  · rintro ⟨q, hqi, rfl⟩
    exact (by simp only [if_pos hqi, dvd_refl] : p q ∣ if r q = some i then p q else 1).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ q))

omit [DecidableEq ι] in
theorem coordinates_coprime_of_squarefree_prod {r : ι → ℕ}
    (hr : Squarefree (∏ i, r i)) {i j : ι} (hij : i ≠ j) : (r i).Coprime (r j) := by
  classical
  have hdiv := Finset.prod_dvd_prod_of_subset ({i, j} : Finset ι) Finset.univ r
    (Finset.subset_univ _)
  rw [Finset.prod_pair hij] at hdiv
  exact Nat.coprime_of_squarefree_mul (hr.squarefree_of_dvd hdiv)

omit [DecidableEq ι] in
theorem prime_divisor_coordinate_unique {r : ι → ℕ}
    (hr : Squarefree (∏ i, r i)) {l : ℕ} (hl : l.Prime) {i j : ι}
    (hi : l ∣ r i) (hj : l ∣ r j) : i = j := by
  by_contra hij
  exact hl.ne_one (Nat.eq_one_of_dvd_coprimes
    (coordinates_coprime_of_squarefree_prod hr hij) hi hj)

open scoped Classical in
def assignmentOfTuple (p : α → ℕ) (r : ι → ℕ) (q : α) : Option ι :=
  if h : ∃ i, p q ∣ r i then some (Classical.choose h) else none

omit [Fintype α] [DecidableEq ι] in
theorem assignmentOfTuple_eq_some_iff {p : α → ℕ} (hp : ∀ q, (p q).Prime)
    {r : ι → ℕ} (hr : Squarefree (∏ i, r i)) (q : α) (i : ι) :
    assignmentOfTuple p r q = some i ↔ p q ∣ r i := by
  classical
  unfold assignmentOfTuple
  by_cases h : ∃ i, p q ∣ r i
  · rw [dif_pos h]
    constructor
    · intro heq
      have hi := Option.some.inj heq
      simpa only [hi] using Classical.choose_spec h
    · intro hi
      exact congrArg some (prime_divisor_coordinate_unique hr (hp q) (Classical.choose_spec h) hi)
  · rw [dif_neg h]
    constructor
    · intro heq
      cases heq
    · intro hi
      exact (h ⟨i, hi⟩).elim

omit [Fintype ι] in
theorem assignmentPrimeTuple_squarefree {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (r : α → Option ι) (i : ι) : Squarefree (assignmentPrimeTuple p r i) := by
  let s : α → Option Unit := fun q => if r q = some i then some () else none
  have h := assignmentPrimeProduct_squarefree hp hinj s
  have heq : assignmentPrimeProduct p s = assignmentPrimeTuple p r i := by
    apply Finset.prod_congr rfl
    intro q _hq
    by_cases hqi : r q = some i <;> simp [s, hqi]
  exact heq ▸ h

theorem assignmentPrimeTuple_assignmentOfTuple {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) {r : ι → ℕ}
    (hr : Squarefree (∏ i, r i))
    (hcover : ∀ l : ℕ, l.Prime → l ∣ (∏ i, r i) → ∃ q, p q = l) :
    assignmentPrimeTuple p (assignmentOfTuple p r) = r := by
  funext i
  have hi : Squarefree (r i) := hr.squarefree_of_dvd
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  rw [Nat.Squarefree.ext_iff (assignmentPrimeTuple_squarefree hp hinj _ i) hi]
  intro l hl
  rw [prime_dvd_assignmentPrimeTuple_iff_exists hp hl]
  constructor
  · rintro ⟨q, hq, heq⟩
    have hd := (assignmentOfTuple_eq_some_iff hp hr q i).mp hq
    simpa only [heq] using hd
  · intro hli
    obtain ⟨q, hq⟩ := hcover l hl
      (hli.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
    refine ⟨q, (assignmentOfTuple_eq_some_iff hp hr q i).mpr ?_, hq⟩
    simpa only [hq] using hli

def AssignmentTupleSupported (p : α → ℕ) (r : ι → ℕ) : Prop :=
  Squarefree (∏ i, r i) ∧ ∀ l : ℕ, l.Prime → l ∣ (∏ i, r i) → ∃ q, p q = l

theorem assignmentPrimeTuple_supported {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (r : α → Option ι) :
    AssignmentTupleSupported p (assignmentPrimeTuple p r) := by
  constructor
  · rw [prod_assignmentPrimeTuple]
    exact assignmentPrimeProduct_squarefree hp hinj r
  · intro l hl hld
    rw [prod_assignmentPrimeTuple] at hld
    have hlmem : l ∈ (assignmentPrimeProduct p r).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hl, hld,
        (assignmentPrimeProduct_pos (fun q => (hp q).pos) r).ne'⟩
    rw [assignmentPrimeProduct_primeFactors hp r] at hlmem
    obtain ⟨q, _hq, heq⟩ := Finset.mem_image.mp hlmem
    exact ⟨q, heq⟩

def primeAssignmentEquiv {p : α → ℕ} (hp : ∀ q, (p q).Prime)
    (hinj : Function.Injective p) :
    (α → Option ι) ≃ {r : ι → ℕ // AssignmentTupleSupported p r} where
  toFun r := ⟨assignmentPrimeTuple p r, assignmentPrimeTuple_supported hp hinj r⟩
  invFun r := assignmentOfTuple p r.val
  left_inv r := by
    apply assignmentPrimeTuple_injective hp hinj
    exact assignmentPrimeTuple_assignmentOfTuple hp hinj
      (assignmentPrimeTuple_supported hp hinj r).1 (assignmentPrimeTuple_supported hp hinj r).2
  right_inv r := by
    apply Subtype.ext
    exact assignmentPrimeTuple_assignmentOfTuple hp hinj r.property.1 r.property.2

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.assignmentPrimeTuple_assignmentOfTuple
#print axioms Erdos4b.FGKMT.primeAssignmentEquiv
