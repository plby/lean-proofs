/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMajorantSupport
import ErdosProblems.Erdos4b.FGKMTCommonOffDiagonalMass

/-!
# Injecting the actual arithmetic majorant into its full coordinate box

On every nonzero summand the clipped coordinate map is exact. Distinct
prime labels make it injective there. Extending its image to the whole
box adds only nonnegative rough-weight terms.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

def assignmentMajorantBox (k R : ℕ) (p : α → ℕ) (r : α → Option (Fin k)) :
    Fin k → Fin (R ^ 2 + 1) :=
  fun i => ⟨min (assignmentPrimeTuple p r i) (R ^ 2),
    Nat.lt_succ_of_le (min_le_right _ _)⟩

omit [DecidableEq α] in
theorem assignmentMajorantBox_val {k R : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hR : 1 < R) (p : α → ℕ)
    {r : α → Option (Fin k)} (hr : primeAssignmentMajorant k R p r ≠ 0) :
    (fun i => (assignmentMajorantBox k R p r i).val) = assignmentPrimeTuple p r := by
  funext i
  exact min_eq_left (primeAssignmentMajorant_coord_lt_sq hk hlog hR p hr i).le

theorem absoluteAssignmentMajorantSum_le_box {k M R : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hR : 1 < R) {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hM : ∀ q, ¬p q ∣ M) :
    absoluteAssignmentMajorantSum k R p ≤
      majorantSieveSum k M (absoluteSieveDenominator 1 k) R k := by
  classical
  let f := fun r : α → Option (Fin k) =>
    primeAssignmentMajorant k R p r ^ 2 * commonKernelWeight k p r
  let G := fun e : Fin k → Fin (R ^ 2 + 1) =>
    sieveProfileMajorant k k (sieveLogTuple R (fun i => (e i).val)) ^ 2 *
      roughSieveWeight M (absoluteSieveDenominator 1 k) (∏ i, (e i).val)
  let S : Finset (α → Option (Fin k)) := Finset.univ.filter (fun r => f r ≠ 0)
  have hprofile {r : α → Option (Fin k)} (hr : r ∈ S) :
      primeAssignmentMajorant k R p r ≠ 0 := by
    have hnon := (Finset.mem_filter.mp hr).2
    intro hz
    exact hnon (by simp only [f, hz, zero_pow (by norm_num : 2 ≠ 0), zero_mul])
  have heq {r : α → Option (Fin k)} (hr : r ∈ S) : f r = G (assignmentMajorantBox k R p r) := by
    dsimp only [G]
    rw [assignmentMajorantBox_val hk hlog hR p (hprofile hr), prod_assignmentPrimeTuple]
    unfold f primeAssignmentMajorant commonKernelWeight
    congr 1
    have hweight := assignmentScalarWeight_eq_rough hp hinj hM (absoluteSieveDenominator 1 k) r
    simpa only [absoluteSieveDenominator, one_div_div] using hweight
  have hcode : Set.InjOn (assignmentMajorantBox k R p) (↑S : Set (α → Option (Fin k))) := by
    intro r hr s hs hcode
    apply assignmentPrimeTuple_injective hp hinj
    rw [← assignmentMajorantBox_val hk hlog hR p (hprofile hr),
      ← assignmentMajorantBox_val hk hlog hR p (hprofile hs), hcode]
  have hG (e : Fin k → Fin (R ^ 2 + 1)) : 0 ≤ G e := by
    apply mul_nonneg (sq_nonneg _)
    apply roughSieveWeight_nonneg
    intro q hq _hqM
    exact div_nonneg (sq_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hq.one_le))
  calc
    _ = ∑ r ∈ S, f r := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r _hr
      change f r = if f r ≠ 0 then f r else 0
      by_cases h : f r = 0 <;> simp only [h, ne_eq, not_true_eq_false, not_false_eq_true,
        if_false, if_true]
    _ = ∑ r ∈ S, G (assignmentMajorantBox k R p r) :=
      Finset.sum_congr rfl (fun r hr => heq hr)
    _ = ∑ e ∈ S.image (assignmentMajorantBox k R p), G e := (Finset.sum_image hcode).symm
    _ ≤ ∑ e, G e := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun e _he _hnot => hG e)
    _ = _ := rfl

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.absoluteAssignmentMajorantSum_le_box
