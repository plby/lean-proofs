/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentSplit
import ErdosProblems.Erdos4b.FGKMTAssignmentArithmetic
import ErdosProblems.Erdos4b.FGKMTRoughSupport

/-!
# Exact common and moved arithmetic weights of the absolute kernel

An unchanged prime contributes `(p - 1) / (p - k)^2`, while a moved
prime contributes `1 / (p - k)^2`. The former is the rough squarefree
weight with denominator `(p - k)^2 / (p - 1)`.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [Fintype α] [DecidableEq ι] [Fintype ι]

def assignmentScalarWeight (a : α → ℝ) (r : α → Option ι) : ℝ :=
  ∏ q, if r q = none then 1 else a q

def absoluteSieveDenominator (a : ℝ) (k : ℕ) (p : ℕ) : ℝ :=
  ((p : ℝ) - k) ^ 2 / ((p : ℝ) - a)

omit [DecidableEq ι] [Fintype ι] in
theorem assignmentScalarWeight_nonneg {a : α → ℝ} (ha : ∀ q, 0 ≤ a q)
    (r : α → Option ι) : 0 ≤ assignmentScalarWeight a r := by
  apply Finset.prod_nonneg
  intro q _hq
  split_ifs
  · exact zero_le_one
  · exact ha q

omit [Fintype α] in
theorem localAbsoluteKernel_split {v : ℝ} (hv : 1 ≤ v) {r s : Option ι}
    (h : r = none ↔ s = none) :
    |localQuadraticKernel v r s| / (localRowWeight v r * localRowWeight v s) =
      (if (if r = s then r else none) = none then 1 else
        (v - 1) / (v - Fintype.card ι) ^ 2) *
      (if (if r = s then none else r) = none then 1 else
        1 / (v - Fintype.card ι) ^ 2) := by
  cases r with
  | none =>
    have hs := h.mp rfl
    subst s
    simp [localQuadraticKernel, localRowWeight]
  | some i =>
    cases s with
    | none => simp at h
    | some j =>
      by_cases hij : i = j
      · subst j
        simp [localQuadraticKernel, localRowWeight, abs_of_nonneg (sub_nonneg.mpr hv), pow_two]
      · simp [localQuadraticKernel, localRowWeight, hij, pow_two]

theorem assignmentAbsoluteKernel_split {v : α → ℝ} (hv : ∀ q, 1 ≤ v q)
    {r s : α → Option ι} (h : SamePrimeSupport r s) :
    |assignmentQuadraticKernel v r s| /
        (assignmentRowWeight v r * assignmentRowWeight v s) =
      assignmentScalarWeight (fun q => (v q - 1) / (v q - Fintype.card ι) ^ 2)
        (commonAssignment r s) *
      assignmentScalarWeight (fun q => 1 / (v q - Fintype.card ι) ^ 2)
        (movedAssignment r s) := by
  unfold assignmentQuadraticKernel assignmentRowWeight assignmentScalarWeight
  rw [Finset.abs_prod, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q _hq
  exact localAbsoluteKernel_split (hv q) (h q)

omit [DecidableEq ι] [Fintype ι] in
theorem assignmentScalarWeight_eq_primeFactors {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (a : ℕ → ℝ)
    (r : α → Option ι) :
    assignmentScalarWeight (fun q => a (p q)) r =
      ∏ l ∈ (assignmentPrimeProduct p r).primeFactors, a l := by
  classical
  rw [assignmentPrimeProduct_primeFactors hp r]
  unfold assignmentUsedPrimes assignmentScalarWeight
  rw [Finset.prod_image (fun q _hq s _hs hqs => hinj hqs), Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro q _hq
  by_cases hq : r q = none <;> simp [hq]

omit [DecidableEq ι] [Fintype ι] in
theorem assignmentScalarWeight_eq_rough {M : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hM : ∀ q, ¬p q ∣ M)
    (g : ℕ → ℝ) (r : α → Option ι) :
    assignmentScalarWeight (fun q => 1 / g (p q)) r =
      roughSieveWeight M g (assignmentPrimeProduct p r) := by
  rw [assignmentScalarWeight_eq_primeFactors hp hinj (fun l => 1 / g l),
    roughSieveWeight_apply_of_squarefree_coprime (assignmentPrimeProduct_squarefree hp hinj r)
      (assignmentPrimeProduct_coprime hp hM r).symm g]

theorem assignmentAbsoluteKernel_eq_rough {k M : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hM : ∀ q, ¬p q ∣ M)
    {r s : α → Option (Fin k)} (hrs : SamePrimeSupport r s) :
    |assignmentQuadraticKernel (fun q => (p q : ℝ)) r s| /
        (assignmentRowWeight (fun q => (p q : ℝ)) r *
          assignmentRowWeight (fun q => (p q : ℝ)) s) =
      roughSieveWeight M (absoluteSieveDenominator 1 k)
        (assignmentPrimeProduct p (commonAssignment r s)) *
      roughSieveWeight M (fun l => ((l : ℝ) - k) ^ 2)
        (assignmentPrimeProduct p (movedAssignment r s)) := by
  rw [assignmentAbsoluteKernel_split (fun q => by exact_mod_cast (hp q).one_le) hrs]
  simp only [Fintype.card_fin]
  have hcommon : (fun q => ((p q : ℝ) - 1) / ((p q : ℝ) - k) ^ 2) =
      fun q => 1 / absoluteSieveDenominator 1 k (p q) := by
    funext q
    simp [absoluteSieveDenominator, div_eq_mul_inv]
  rw [hcommon, assignmentScalarWeight_eq_rough hp hinj hM (absoluteSieveDenominator 1 k),
    assignmentScalarWeight_eq_rough hp hinj hM (fun l => ((l : ℝ) - k) ^ 2)]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.assignmentAbsoluteKernel_split
#print axioms Erdos4b.FGKMT.assignmentAbsoluteKernel_eq_rough
