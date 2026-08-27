/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeAssignment
import ErdosProblems.Erdos4b.FGKMTFiniteTransform
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# The arithmetic factors of prime assignments

The row normalization is the product of `p - m` over the actual prime
divisors. The inverse coefficient kernel is exactly the Möbius factor
times the divisor product, restricted by coordinatewise divisibility.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [Fintype α] [DecidableEq ι]

def assignmentUsedPrimes (p : α → ℕ) (r : α → Option ι) : Finset ℕ :=
  (Finset.univ.filter (fun q => r q ≠ none)).image p

omit [DecidableEq ι] in
theorem assignmentPrimeProduct_primeFactors {p : α → ℕ} (hp : ∀ q, (p q).Prime)
    (r : α → Option ι) :
    (assignmentPrimeProduct p r).primeFactors = assignmentUsedPrimes p r := by
  classical
  have hpos := assignmentPrimeProduct_pos (fun q => (hp q).pos) r
  ext l
  constructor
  · intro hl
    obtain ⟨hlp, hld, _hl0⟩ := Nat.mem_primeFactors.mp hl
    obtain ⟨q, _hq, hdiv⟩ := (hlp.prime.dvd_finsetProd_iff _).mp hld
    by_cases hq0 : r q = none
    · rw [if_pos hq0] at hdiv
      exact (hlp.ne_one (Nat.dvd_one.mp hdiv)).elim
    · rw [if_neg hq0] at hdiv
      have heq := (Nat.prime_dvd_prime_iff_eq hlp (hp q)).mp hdiv
      exact Finset.mem_image.mpr
        ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq0⟩, heq.symm⟩
  · intro hl
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hl
    have hq0 := (Finset.mem_filter.mp hq).2
    apply Nat.mem_primeFactors.mpr
    refine ⟨hp q, ?_, hpos.ne'⟩
    exact (by simp only [if_neg hq0, dvd_refl] : p q ∣ if r q = none then 1 else p q).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ q))

omit [DecidableEq ι] in
theorem assignmentPrimeProduct_coprime {p : α → ℕ} (hp : ∀ q, (p q).Prime)
    {M : ℕ} (hM : ∀ q, ¬p q ∣ M) (r : α → Option ι) :
    (assignmentPrimeProduct p r).Coprime M := by
  apply Nat.Coprime.prod_left
  intro q _hq
  split_ifs
  · exact Nat.coprime_one_left M
  · exact (hp q).coprime_iff_not_dvd.mpr (hM q)

omit [DecidableEq ι] in
theorem assignmentRowWeight_eq_primeFactors [Fintype ι] {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (r : α → Option ι) :
    assignmentRowWeight (fun q => (p q : ℝ)) r =
      ∏ l ∈ (assignmentPrimeProduct p r).primeFactors, ((l : ℝ) - Fintype.card ι) := by
  rw [assignmentPrimeProduct_primeFactors hp r]
  unfold assignmentUsedPrimes assignmentRowWeight
  rw [Finset.prod_image (fun q _hq s _hs hqs => hinj hqs), Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro q _hq
  cases r q <;> simp [localRowWeight]

omit [DecidableEq ι] in
theorem assignmentPrimeProduct_moebius {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (r : α → Option ι) :
    (ArithmeticFunction.moebius (assignmentPrimeProduct p r) : ℝ) =
      ∏ q, if r q = none then 1 else (-1 : ℝ) := by
  classical
  let f := fun q => if r q = none then 1 else p q
  have hpair : (↑(Finset.univ : Finset α) : Set α).Pairwise
      (fun q s => (f q).Coprime (f s)) := by
    intro q _hq s _hs hqs
    have hcop := (Nat.coprime_primes (hp q) (hp s)).mpr (hinj.ne hqs)
    dsimp only [f]
    by_cases hq : r q = none
    · simp [hq]
    · by_cases hs : r s = none
      · simp [hq, hs]
      · simpa only [if_neg hq, if_neg hs] using hcop
  have hmu : ArithmeticFunction.moebius (assignmentPrimeProduct p r) =
      ∏ q, if r q = none then 1 else (-1 : ℤ) := by
    change ArithmeticFunction.moebius (∏ q, f q) = _
    rw [ArithmeticFunction.IsMultiplicative.map_prod f ArithmeticFunction.isMultiplicative_moebius
      Finset.univ hpair]
    apply Finset.prod_congr rfl
    intro q _hq
    by_cases hq : r q = none
    · simp [f, hq]
    · simp [f, hq, ArithmeticFunction.moebius_apply_prime (hp q)]
  exact_mod_cast hmu

omit [DecidableEq ι] in
theorem assignmentPrimeProduct_signed {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (r : α → Option ι) :
    (ArithmeticFunction.moebius (assignmentPrimeProduct p r) : ℝ) *
        assignmentPrimeProduct p r = ∏ q, if r q = none then 1 else -(p q : ℝ) := by
  rw [assignmentPrimeProduct_moebius hp hinj r, assignmentPrimeProduct,
    Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q _hq
  by_cases hq : r q = none <;> simp [hq]

open scoped Classical in
theorem assignmentCoeffKernel_eq_moebius {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (d r : α → Option ι) :
    assignmentCoeffKernel (fun q => (p q : ℝ)) d r =
      if AssignmentExtends d r then
        (ArithmeticFunction.moebius (assignmentPrimeProduct p d) : ℝ) * assignmentPrimeProduct p d
      else 0 := by
  classical
  by_cases h : AssignmentExtends d r
  · rw [if_pos h, assignmentPrimeProduct_signed hp hinj d]
    apply Finset.prod_congr rfl
    intro q _hq
    cases hd : d q with
    | none => simp [localDivisorCoeff]
    | some i => simp [localDivisorCoeff, h q i hd]
  · rw [if_neg h]
    unfold AssignmentExtends at h
    push Not at h
    obtain ⟨q, i, hd, hr⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    simp [localDivisorCoeff, hd, hr]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.assignmentPrimeProduct_primeFactors
#print axioms Erdos4b.FGKMT.assignmentRowWeight_eq_primeFactors
#print axioms Erdos4b.FGKMT.assignmentCoeffKernel_eq_moebius
