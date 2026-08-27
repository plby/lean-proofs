/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCommonPinnedCoefficients
import ErdosProblems.Erdos4b.FGKMTSieveLocal

/-! # Exact pinned row normalization, radius cutoff, and local Euler factor -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] in
theorem assignmentPrimeProduct_map {ι κ : Type*} (p : α → ℕ) (e : ι ↪ κ)
    (r : α → Option ι) :
    assignmentPrimeProduct p (mapPrimeAssignment e r) = assignmentPrimeProduct p r := by
  apply Finset.prod_congr rfl
  intro q _hq
  cases hr : r q <;> simp [mapPrimeAssignment, hr]

omit [DecidableEq α] in
theorem commonPinnedRowWeight_eq_primeFactors {m : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (r : α → Option (Fin m)) :
    assignmentRowWeight (fun q => (p q : ℝ) - 1) r =
      ∏ l ∈ (assignmentPrimeProduct p r).primeFactors, ((l : ℝ) - (m + 1)) := by
  rw [assignmentPrimeProduct_primeFactors hp r]
  unfold assignmentUsedPrimes assignmentRowWeight
  rw [Finset.prod_image (fun q _hq s _hs hqs => hinj hqs), Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro q _hq
  cases r q <;> simp [localRowWeight, sub_sub, add_comm]

theorem commonPinnedCoefficient_zero_of_product_ge {m R : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hR : 1 < R)
    (j : Fin (m + 1)) (d : α → Option (Fin m))
    (hd : R ≤ assignmentPrimeProduct p d) : commonPinnedCoefficient m R p j d = 0 := by
  apply commonSieveCoefficient_zero_of_product_ge hp hinj hR
  rwa [assignmentPrimeProduct_map]

theorem commonPinnedProfile_zero_of_product_ge {m R : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hR : 1 < R)
    (j : Fin (m + 1)) (r : α → Option (Fin m))
    (hr : R ≤ assignmentPrimeProduct p r) : commonPinnedProfile m R p j r = 0 := by
  classical
  rw [commonPinnedProfile_eq_moebius_totient hp hinj]
  suffices (∑ d : α → Option (Fin m),
      if ∀ i, assignmentPrimeTuple p r i ∣ assignmentPrimeTuple p d i then
        commonPinnedCoefficient m R p j d / (assignmentPrimeProduct p d).totient else 0) = 0 by
    rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro d _hd
  by_cases hdiv : ∀ i, assignmentPrimeTuple p r i ∣ assignmentPrimeTuple p d i
  · rw [if_pos hdiv]
    have hprod : assignmentPrimeProduct p r ∣ assignmentPrimeProduct p d := by
      rw [← prod_assignmentPrimeTuple p r, ← prod_assignmentPrimeTuple p d]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _hi => hdiv i)
    have hle := Nat.le_of_dvd (assignmentPrimeProduct_pos (fun q => (hp q).pos) d) hprod
    rw [commonPinnedCoefficient_zero_of_product_ge hp hinj hR j d (hr.trans hle), zero_div]
  · exact if_neg hdiv

theorem sum_unpinned_localProfileKernel {m : ℕ} (v : ℝ) (j : Fin (m + 1)) :
    (∑ s : Option (Fin m), localPinnedProfileKernel v j.succAboveEmb none
      (s.map j.succAboveEmb)) = pinnedLocalFactor (m + 1) v := by
  rw [Fintype.sum_option]
  simp only [Option.map_none, Option.map_some, localPinnedProfileKernel_none_none,
    localPinnedProfileKernel_none_image, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  unfold pinnedLocalFactor
  simp only [Nat.cast_add, Nat.cast_one]
  ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedProfile_zero_of_product_ge
#print axioms Erdos4b.FGKMT.commonPinnedRowWeight_eq_primeFactors
#print axioms Erdos4b.FGKMT.sum_unpinned_localProfileKernel
