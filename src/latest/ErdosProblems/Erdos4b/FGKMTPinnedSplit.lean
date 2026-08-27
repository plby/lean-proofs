/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFinitePushforward
import ErdosProblems.Erdos4b.FGKMTPinnedSplitLocal
import ErdosProblems.Erdos4b.FGKMTPinnedMovedMass

/-! # Exact finite regrouping by the pinned divisor and moved factors -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

def pinnedSplitAssignment {m : ℕ} (j : Fin (m + 1)) (r : α → Option (Fin m))
    (a : α → Option Unit) (b : α → Option (Fin m)) : α → Option (Fin (m + 1)) :=
  fun q => localPinnedSplitState j (r q) (a q) (b q)

def pinnedBaseFactor {m : ℕ} (p : α → ℕ) (r : α → Option (Fin m)) : ℝ :=
  ∏ q, localPinnedBaseWeight (p q) (r q)

def pinnedDivisorFactor {m : ℕ} (p : α → ℕ) (r : α → Option (Fin m))
    (a : α → Option Unit) : ℝ :=
  ∏ q, localPinnedDivisorWeight (p q) (r q) (a q)

def pinnedMovedFactor {m : ℕ} (p : α → ℕ) (r : α → Option (Fin m))
    (a : α → Option Unit) (b : α → Option (Fin m)) : ℝ :=
  ∏ q, localPinnedMovedCoeff (p q) (r q) (a q) (b q)

omit [DecidableEq α] in
theorem pinnedSplitWeight_product {m : ℕ} (p : α → ℕ) (r : α → Option (Fin m))
    (a : α → Option Unit) (b : α → Option (Fin m)) :
    (∏ q, localPinnedSplitWeight (p q) (r q) (a q) (b q)) =
      pinnedBaseFactor p r * pinnedDivisorFactor p r a * pinnedMovedFactor p r a b := by
  simp only [localPinnedSplitWeight, Finset.prod_mul_distrib,
    pinnedBaseFactor, pinnedDivisorFactor, pinnedMovedFactor]

omit [DecidableEq α] in
theorem pinnedBaseFactor_eq_totient_ratio {m : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (r : α → Option (Fin m)) :
    pinnedBaseFactor p r =
      (assignmentPrimeProduct p r : ℝ) / (assignmentPrimeProduct p r).totient := by
  rw [assignmentPrimeProduct_totient hp hinj, assignmentPrimeProduct,
    Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro q _hq
  by_cases hr : r q = none <;> simp [localPinnedBaseWeight, hr]

omit [DecidableEq α] in
theorem pinnedDivisorFactor_eq_scalar {m : ℕ} (p : α → ℕ)
    (r : α → Option (Fin m)) (a : α → Option Unit) :
    pinnedDivisorFactor p r a = assignmentScalarWeight
      (fun q => if r q = none then 1 / ((p q : ℝ) - (m + 1)) else 0) a := rfl

omit [DecidableEq α] in
theorem pinnedMovedFactor_eq_scalar {m : ℕ} (p : α → ℕ)
    (r : α → Option (Fin m)) (a : α → Option Unit) (b : α → Option (Fin m)) :
    pinnedMovedFactor p r a b = assignmentScalarWeight
      (fun q => if r q = none ∧ a q = none then -pinnedMovedWeight (m + 1) (p q) else 0) b :=
  rfl

theorem commonPinnedProfile_eq_split {m R : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hlarge : ∀ q, m + 1 < p q)
    (j : Fin (m + 1)) (r : α → Option (Fin m)) :
    commonPinnedProfile m R p j r = pinnedBaseFactor p r *
      ∑ a : α → Option Unit, pinnedDivisorFactor p r a *
        ∑ b : α → Option (Fin m), pinnedMovedFactor p r a b *
          primeAssignmentProfile (m + 1) R p (pinnedSplitAssignment j r a b) := by
  unfold pinnedSplitAssignment
  rw [commonPinnedProfile_eq_product hp]
  have hv (q : α) : (p q : ℝ) - (m + 1) ≠ 0 :=
    (sub_pos.mpr (by exact_mod_cast hlarge q)).ne'
  rw [finite_double_product_pushforward
    (fun q => localPinnedSplitState j (r q))
    (fun q => localPinnedSplitWeight (p q) (r q))
    (fun q s => localPinnedProfileKernel (p q) j.succAboveEmb (r q) s)
    (fun q s => localPinnedSplit_pushforward (hv q) j (r q) s)]
  simp only [pinnedSplitWeight_product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedBaseFactor_eq_totient_ratio
#print axioms Erdos4b.FGKMT.commonPinnedProfile_eq_split
