/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SlopeAwareEuler
import ErdosProblems.Erdos851.ConcreteBetaCutoff
import ErdosProblems.Erdos851.FiniteBetaProductRatio

/-!
# Beta-sieve main terms after deleting slope primes

The Rosser stopping geometry depends only on the order and sizes of the
remaining primes.  Filtering the usual descending prime list therefore
preserves the same beta cutoff prefixes.  At a retained slope prime the
two-affine local density is no larger than the determinant pair density, so
every filtered inverse prefix product is bounded by the already checked
dimension-two prefix product.
-/

namespace Erdos822

open scoped BigOperators
open Erdos851
open Erdos851.FiniteCombinatorialSieve
open Erdos851.BetaSieveFundamental

/-- The decreasing slope-aware list is literally the ordinary decreasing
prime list with the common-slope primes removed. -/
theorem reverse_ascendingSlopeAwareSievePrimes
    (a b z y : ℕ) :
    (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse =
      (descendingSievePrimes z y).filter fun p ↦
        decide (¬ p ∣ a ∨ ¬ p ∣ b) := by
  unfold ascendingSlopeAwareSievePrimes descendingSievePrimes
    Erdos851.ascendingSievePrimes
  simp only [Nat.add_sub_cancel, List.filter_reverse]

/-- The usual beta prefix with common-slope primes removed. -/
noncomputable def slopeAwareBetaCutoffPrefix
    (a b z y r : ℕ) : List ℕ :=
  (betaCutoffPrefix z y r).filter fun p ↦
    decide (¬ p ∣ a ∨ ¬ p ∣ b)

/-- Decidable wrapper for the real-valued beta eligibility predicate, used
when filtering lists in theorem statements. -/
noncomputable def slopeAwareBetaEligibleBool (y r p : ℕ) : Bool := by
  classical
  exact decide (1 < p ∧ betaEligible y r p)

@[simp]
theorem slopeAwareBetaEligibleBool_eq_true {y r p : ℕ} :
    slopeAwareBetaEligibleBool y r p = true ↔
      1 < p ∧ betaEligible y r p := by
  classical
  simp [slopeAwareBetaEligibleBool]

theorem slopeAwareBetaCutoffPrefix_isPrefix
    (a b z y r : ℕ) (hy : 1 ≤ y) :
    slopeAwareBetaCutoffPrefix a b z y r <+:
      (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse := by
  rw [reverse_ascendingSlopeAwareSievePrimes]
  unfold slopeAwareBetaCutoffPrefix
  exact (betaCutoffPrefix_isPrefix z y r hy).filter _

theorem slopeAwareBetaCutoffPrefix_nodup
    (a b z y r : ℕ) :
    (slopeAwareBetaCutoffPrefix a b z y r).Nodup := by
  unfold slopeAwareBetaCutoffPrefix betaCutoffPrefix
  exact ((descendingSievePrimes_nodup z y).filter _).filter _

theorem mem_slopeAwareBetaCutoffPrefix_slope
    {a b z y r p : ℕ}
    (hp : p ∈ slopeAwareBetaCutoffPrefix a b z y r) :
    ¬ p ∣ a ∨ ¬ p ∣ b := by
  unfold slopeAwareBetaCutoffPrefix at hp
  exact of_decide_eq_true (List.mem_filter.mp hp).2

theorem mem_slopeAwareBetaCutoffPrefix_prime
    {a b z y r p : ℕ}
    (hp : p ∈ slopeAwareBetaCutoffPrefix a b z y r) :
    p.Prime := by
  unfold slopeAwareBetaCutoffPrefix betaCutoffPrefix at hp
  have hp' : p ∈ descendingSievePrimes z y :=
    (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  exact (Erdos851.mem_sievePrimes.mp
    (mem_descendingSievePrimes.mp hp')).2.2

theorem mem_slopeAwareBetaCutoffPrefix_gt_two
    {a b z y r p : ℕ} (hz : 2 ≤ z)
    (hp : p ∈ slopeAwareBetaCutoffPrefix a b z y r) :
    2 < p := by
  unfold slopeAwareBetaCutoffPrefix betaCutoffPrefix at hp
  have hp' : p ∈ descendingSievePrimes z y :=
    (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  have := (Erdos851.mem_sievePrimes.mp
    (mem_descendingSievePrimes.mp hp')).1
  omega

theorem mem_slopeAwareSievePrimes_of_mem_betaCutoff
    {a b z y r p : ℕ}
    (hp : p ∈ slopeAwareBetaCutoffPrefix a b z y r) :
    p ∈ slopeAwareSievePrimes a b z (y + 1) := by
  unfold slopeAwareBetaCutoffPrefix betaCutoffPrefix at hp
  have hpDesc : p ∈ descendingSievePrimes z y :=
    (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  have hpData := Erdos851.mem_sievePrimes.mp
    (mem_descendingSievePrimes.mp hpDesc)
  rw [mem_slopeAwareSievePrimes_iff]
  exact ⟨hpData.2.2, hpData.1, by omega,
    of_decide_eq_true (List.mem_filter.mp hp).2⟩

/-- On a filtered prefix, the two-affine inverse Euler product is bounded by
the ordinary determinant pair inverse product on the full beta prefix. -/
theorem slopeAwareBetaCutoff_inverse_le_pairShift
    {a s b t z y r : ℕ} (hz : 2 ≤ z)
    (hconstants : ∀ p ∈ slopeAwareSievePrimes a b z (y + 1),
      ¬ p ∣ s ∧ ¬ p ∣ t) :
    (buchstabProduct (twoAffineNu a s b t)
        (slopeAwareBetaCutoffPrefix a b z y r))⁻¹ ≤
      (buchstabProduct
        (Erdos851.pairShiftDensity (affineDetNat a s b t))
        (betaCutoffPrefix z y r))⁻¹ := by
  classical
  let Q := slopeAwareBetaCutoffPrefix a b z y r
  let R := betaCutoffPrefix z y r
  change
    (buchstabProduct (twoAffineNu a s b t) Q)⁻¹ ≤
      (buchstabProduct
        (Erdos851.pairShiftDensity (affineDetNat a s b t)) R)⁻¹
  have hQnodup : Q.Nodup := slopeAwareBetaCutoffPrefix_nodup a b z y r
  have hRnodup : R.Nodup := by
    unfold R betaCutoffPrefix
    exact (descendingSievePrimes_nodup z y).filter _
  have hQsubR : Q.toFinset ⊆ R.toFinset := by
    intro p hp
    have hpQ : p ∈ Q := List.mem_toFinset.mp hp
    unfold Q slopeAwareBetaCutoffPrefix at hpQ
    exact List.mem_toFinset.mpr (List.mem_filter.mp hpQ).1
  have hterm :
      ∀ p ∈ Q.toFinset,
        (1 - twoAffineNu a s b t p)⁻¹ ≤
          (1 - Erdos851.pairShiftDensity (affineDetNat a s b t) p)⁻¹ := by
    intro p hp
    have hpQ : p ∈ Q := List.mem_toFinset.mp hp
    have hpPrime : p.Prime := mem_slopeAwareBetaCutoffPrefix_prime hpQ
    have hp2 : 2 < p := mem_slopeAwareBetaCutoffPrefix_gt_two hz hpQ
    have hpSlope := mem_slopeAwareBetaCutoffPrefix_slope hpQ
    have hpSlopeSet : p ∈ slopeAwareSievePrimes a b z (y + 1) :=
      mem_slopeAwareSievePrimes_of_mem_betaCutoff hpQ
    have hnu := twoAffineNu_pos_lt_one_of_not_dvd_constants_one_slope
      hpPrime hp2 (hconstants p hpSlopeSet).1 (hconstants p hpSlopeSet).2
      hpSlope
    have hpair : Erdos851.pairShiftDensity (affineDetNat a s b t) p < 1 :=
      Erdos851.pairShiftDensity_lt_one hpPrime hp2
    apply (inv_le_inv₀ (sub_pos.mpr hnu.2) (sub_pos.mpr hpair)).2
    exact sub_le_sub_left
      (twoAffineNu_le_pairShiftDensity_of_not_dvd_constants_one_slope
        hpPrime (hconstants p hpSlopeSet).1 (hconstants p hpSlopeSet).2 hpSlope) 1
  have hpairOne :
      ∀ p ∈ R.toFinset, p ∉ Q.toFinset →
        1 ≤ (1 - Erdos851.pairShiftDensity (affineDetNat a s b t) p)⁻¹ := by
    intro p hpR _hpQ
    have hpR' : p ∈ R := List.mem_toFinset.mp hpR
    have hpS : p ∈ descendingSievePrimes z y := by
      unfold R betaCutoffPrefix at hpR'
      exact (List.mem_filter.mp hpR').1
    have hpData := Erdos851.mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp hpS)
    have hpos := Erdos851.pairShift_localFactor_pos
      (h := affineDetNat a s b t)
      hpData.2.2 (by omega)
    exact (one_le_inv₀ hpos).2
      (sub_le_self _ (Erdos851.pairShiftDensity_pos hpData.2.2).le)
  unfold buchstabProduct
  rw [← List.prod_toFinset (fun p ↦ 1 - twoAffineNu a s b t p) hQnodup,
    ← Finset.prod_inv_distrib,
    ← List.prod_toFinset
      (fun p ↦ 1 - Erdos851.pairShiftDensity (affineDetNat a s b t) p)
      hRnodup,
    ← Finset.prod_inv_distrib]
  calc
    (∏ p ∈ Q.toFinset, (1 - twoAffineNu a s b t p)⁻¹) ≤
        ∏ p ∈ Q.toFinset,
          (1 - Erdos851.pairShiftDensity (affineDetNat a s b t) p)⁻¹ := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpQ : p ∈ Q := List.mem_toFinset.mp hp
        have hpSet : p ∈ slopeAwareSievePrimes a b z (y + 1) :=
          mem_slopeAwareSievePrimes_of_mem_betaCutoff hpQ
        have hnu := twoAffineNu_pos_lt_one_of_not_dvd_constants_one_slope
          (mem_slopeAwareBetaCutoffPrefix_prime hpQ)
          (mem_slopeAwareBetaCutoffPrefix_gt_two hz hpQ)
          (hconstants p hpSet).1 (hconstants p hpSet).2
          (mem_slopeAwareBetaCutoffPrefix_slope hpQ)
        exact (inv_nonneg.mpr (sub_pos.mpr hnu.2).le)
      · intro p hp
        exact hterm p hp
    _ ≤ ∏ p ∈ R.toFinset,
          (1 - Erdos851.pairShiftDensity (affineDetNat a s b t) p)⁻¹ :=
      Finset.prod_le_prod_of_subset_of_one_le hQsubR
        (by
          intro p hp
          have hpQ : p ∈ Q := List.mem_toFinset.mp hp
          have hpPrime := mem_slopeAwareBetaCutoffPrefix_prime hpQ
          have hp2 := mem_slopeAwareBetaCutoffPrefix_gt_two hz hpQ
          exact (inv_nonneg.mpr
            (Erdos851.pairShift_localFactor_pos hpPrime hp2).le))
        hpairOne

theorem slopeAwareBetaCutoffPrefix_eq_filter_reverse
    (a b z y r : ℕ) :
    slopeAwareBetaCutoffPrefix a b z y r =
      (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse.filter
        fun p ↦ slopeAwareBetaEligibleBool y r p := by
  classical
  rw [reverse_ascendingSlopeAwareSievePrimes]
  unfold slopeAwareBetaCutoffPrefix betaCutoffPrefix
  simp only [List.filter_filter]
  apply List.filter_congr
  intro p
  by_cases hpa : p ∣ a <;> by_cases hpb : p ∣ b <;>
    by_cases hp1 : 1 < p <;> by_cases helig : betaEligible y r p <;>
      simp [slopeAwareBetaEligibleBool, hpa, hpb, hp1, helig]

private theorem getLast_le_of_pairwise_desc_822 :
    ∀ {l : List ℕ} (hn : l ≠ []),
      l.Pairwise (fun p q ↦ q < p) →
      ∀ p ∈ l, l.getLast hn ≤ p := by
  intro l hn hdesc
  induction l with
  | nil => contradiction
  | cons a l ih =>
      cases l with
      | nil => simp
      | cons b l =>
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · have htail := (List.pairwise_cons.mp hdesc).1
              ((b :: l).getLast (by simp)) (List.getLast_mem (by simp))
            simpa using htail.le
          · have htaildesc := (List.pairwise_cons.mp hdesc).2
            simpa using ih (by simp) htaildesc p (by simpa using hp)

theorem reverse_ascendingSlopeAwareSievePrimes_pairwise_desc
    (a b z y : ℕ) :
    (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse.Pairwise
      (fun p q ↦ q < p) := by
  rw [reverse_ascendingSlopeAwareSievePrimes]
  exact (descendingSievePrimes_pairwise z y).filter _

private theorem chain_sublist_slopeAwareBetaCutoffPrefix_of_terminal
    {a b z y r : ℕ} {chain : List ℕ}
    (hsub : chain.Sublist
      (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse)
    (hnonempty : chain ≠ [])
    (hterminal : Real.log (y : ℝ) /
        Real.log (chain.getD (chain.length - 1) 2 : ℝ) <
      betaRatio ^ (r - 1)) :
    chain.Sublist (slopeAwareBetaCutoffPrefix a b z y r) := by
  classical
  have hdesc : chain.Pairwise (fun p q ↦ q < p) :=
    (reverse_ascendingSlopeAwareSievePrimes_pairwise_desc a b z y).sublist hsub
  let q := chain.getLast hnonempty
  have hlenpos : 0 < chain.length := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hnonempty (List.length_eq_zero_iff.mp hz)
  have hqmem : q ∈ chain := List.getLast_mem hnonempty
  have hqLarge : 1 < q := by
    have hqP := hsub.subset hqmem
    rw [reverse_ascendingSlopeAwareSievePrimes] at hqP
    have hqDesc := (List.mem_filter.mp hqP).1
    exact (Erdos851.mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp hqDesc)).2.2.one_lt
  have hget : chain.getD (chain.length - 1) 2 = q := by
    calc
      chain.getD (chain.length - 1) 2 = chain[chain.length - 1] := by
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega : chain.length - 1 < chain.length)]
      _ = q := (List.getLast_eq_getElem hnonempty).symm
  have hqEligible : betaEligible y r q := by
    unfold betaEligible
    rw [hget] at hterminal
    exact hterminal
  have hchainEligible :
      ∀ p ∈ chain, 1 < p ∧ betaEligible y r p := by
    intro p hp
    have hpP := hsub.subset hp
    rw [reverse_ascendingSlopeAwareSievePrimes] at hpP
    have hpDesc := (List.mem_filter.mp hpP).1
    have hpLarge : 1 < p :=
      (Erdos851.mem_sievePrimes.mp
        (mem_descendingSievePrimes.mp hpDesc)).2.2.one_lt
    refine ⟨hpLarge, ?_⟩
    have hqp := getLast_le_of_pairwise_desc_822 hnonempty hdesc p hp
    rcases hqp.eq_or_lt with hEq | hlt
    · exact hEq ▸ hqEligible
    · exact betaEligible_of_lt
        (by
          have hpUpper := (Erdos851.mem_sievePrimes.mp
            (mem_descendingSievePrimes.mp hpDesc)).2.1
          omega)
        hqLarge hlt hqEligible
  have hfiltered : chain.filter
      (fun p ↦ slopeAwareBetaEligibleBool y r p) = chain :=
    List.filter_eq_self.mpr (fun p hp ↦ by simp [hchainEligible p hp])
  rw [slopeAwareBetaCutoffPrefix_eq_filter_reverse]
  simpa only [hfiltered] using
    hsub.filter (fun p ↦ slopeAwareBetaEligibleBool y r p)

theorem upperFailureTerm_chain_sublist_slopeAwareBetaCutoffPrefix
    {a b z y S fuel r : ℕ} {t : List ℕ × List ℕ}
    (ht : t ∈ upperFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse)
    (hS : 101 ≤ S) (hlen : t.1.length = r) :
    t.1.Sublist (slopeAwareBetaCutoffPrefix a b z y r) := by
  have hsub := upperFailureTerms_chain_sublist
    (descendingRosserStop 100 (y ^ S)) fuel []
      (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse ht
  have hlarge : ∀ p ∈
      (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse, 1 < p := by
    intro p hp
    rw [reverse_ascendingSlopeAwareSievePrimes] at hp
    exact (Erdos851.mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (List.mem_filter.mp hp).1)).2.2.one_lt
  have hupper : ∀ p ∈
      (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse, p ≤ y := by
    intro p hp
    rw [reverse_ascendingSlopeAwareSievePrimes] at hp
    exact (Erdos851.mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (List.mem_filter.mp hp).1)).2.1
  have hcut := upperFailureTerm_log_ratio_lt_betaRatio_pow
    ht hlarge hupper
    (reverse_ascendingSlopeAwareSievePrimes_pairwise_desc a b z y) hS
  have hnonempty : t.1 ≠ [] := by
    obtain ⟨k, hk⟩ := upperFailureTerms_chain_length_odd
      (descendingRosserStop 100 (y ^ S)) fuel []
        (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse ht
    intro hempty
    rw [hempty] at hk
    simp at hk
  apply chain_sublist_slopeAwareBetaCutoffPrefix_of_terminal hsub hnonempty
  simpa [hlen] using hcut

theorem lowerFailureTerm_chain_sublist_slopeAwareBetaCutoffPrefix
    {a b z y S fuel r : ℕ} {t : List ℕ × List ℕ}
    (ht : t ∈ lowerFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse)
    (hS : 101 ≤ S) (hlen : t.1.length = r) :
    t.1.Sublist (slopeAwareBetaCutoffPrefix a b z y r) := by
  have hsub := lowerFailureTerms_chain_sublist
    (descendingRosserStop 100 (y ^ S)) fuel []
      (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse ht
  have hlarge : ∀ p ∈
      (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse, 1 < p := by
    intro p hp
    rw [reverse_ascendingSlopeAwareSievePrimes] at hp
    exact (Erdos851.mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (List.mem_filter.mp hp).1)).2.2.one_lt
  have hupper : ∀ p ∈
      (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse, p ≤ y := by
    intro p hp
    rw [reverse_ascendingSlopeAwareSievePrimes] at hp
    exact (Erdos851.mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp (List.mem_filter.mp hp).1)).2.1
  have hcut := lowerFailureTerm_log_ratio_lt_betaRatio_pow
    ht hlarge hupper
    (reverse_ascendingSlopeAwareSievePrimes_pairwise_desc a b z y) hS
  have hnonempty : t.1 ≠ [] := by
    obtain ⟨_init, _last, _before, hchain, _hrem⟩ :=
      ((failureTerms_structure (descendingRosserStop 100 (y ^ S))
        fuel [] (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse).2 t ht).2
    rw [hchain]
    simp
  apply chain_sublist_slopeAwareBetaCutoffPrefix_of_terminal hsub hnonempty
  simpa [hlen] using hcut

theorem upperFailureTerm_start_depth_slopeAware
    {a b z y S fuel : ℕ} {t : List ℕ × List ℕ}
    (hy : 1 < y)
    (ht : t ∈ upperFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse) :
    S - 100 ≤ t.1.length := by
  have hfail : ¬ rosserStoppingPredicate 100 (y ^ S) t.1.reverse :=
    upperFailureTerms_not_descendingRosserStoppingPredicate ht
  have hupper : ∀ p ∈ t.1.reverse, p ≤ y := by
    intro p hp
    have hpChain : p ∈ t.1 := by simpa using hp
    have hsub := upperFailureTerms_chain_sublist
      (descendingRosserStop 100 (y ^ S)) fuel []
        (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse ht
    rw [reverse_ascendingSlopeAwareSievePrimes] at hsub
    exact (Erdos851.mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp
        (List.mem_filter.mp (hsub.subset hpChain)).1)).2.1
  have hdepth := Erdos851.RosserBoundaryEstimate.stopping_failure_forces_depth
    hy rfl hupper hfail
  simp only [List.length_reverse] at hdepth
  omega

theorem lowerFailureTerm_start_depth_slopeAware
    {a b z y S fuel : ℕ} {t : List ℕ × List ℕ}
    (hy : 1 < y)
    (ht : t ∈ lowerFailureTerms (descendingRosserStop 100 (y ^ S))
      fuel [] (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse) :
    S - 100 ≤ t.1.length := by
  have hfail : ¬ rosserStoppingPredicate 100 (y ^ S) t.1.reverse :=
    lowerFailureTerms_not_descendingRosserStoppingPredicate ht
  have hupper : ∀ p ∈ t.1.reverse, p ≤ y := by
    intro p hp
    have hpChain : p ∈ t.1 := by simpa using hp
    have hsub := lowerFailureTerms_chain_sublist
      (descendingRosserStop 100 (y ^ S)) fuel []
        (ascendingSlopeAwareSievePrimes a b z (y + 1)).reverse ht
    rw [reverse_ascendingSlopeAwareSievePrimes] at hsub
    exact (Erdos851.mem_sievePrimes.mp
      (mem_descendingSievePrimes.mp
        (List.mem_filter.mp (hsub.subset hpChain)).1)).2.1
  have hdepth := Erdos851.RosserBoundaryEstimate.stopping_failure_forces_depth
    hy rfl hupper hfail
  simp only [List.length_reverse] at hdepth
  omega

theorem finiteEulerProduct_ascendingSlopeAware_eq
    (a s b t z y : ℕ) :
    finiteEulerProduct (twoAffineNu a s b t)
        (ascendingSlopeAwareSievePrimes a b z (y + 1)) =
      ∏ p ∈ slopeAwareSievePrimes a b z (y + 1),
        (1 - twoAffineNu a s b t p) := by
  classical
  unfold finiteEulerProduct
  rw [← List.prod_toFinset
    (fun p ↦ 1 - twoAffineNu a s b t p)
    (ascendingSlopeAwareSievePrimes_nodup a b z (y + 1))]
  congr 1
  ext p
  simp [mem_ascendingSlopeAwareSievePrimes_iff]

/-- The filtered affine prime list satisfies the same concrete
dimension-two beta-sieve main-term estimate as the ordinary pair list.
The main Euler product is the genuine slope-aware affine one. -/
theorem exists_slopeAware_concrete_finiteMainTerm_bounds :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ a s b t z y S : ℕ,
        2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        (∀ p ∈ slopeAwareSievePrimes a b z (y + 1),
          ¬ p ∣ s ∧ ¬ p ∣ t) →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let P := ascendingSlopeAwareSievePrimes a b z (y + 1)
        let stop := rosserStoppingPredicate 100 (y ^ S)
        let V := ∏ p ∈ slopeAwareSievePrimes a b z (y + 1),
          (1 - twoAffineNu a s b t p)
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (1 - eta) * V ≤ lowerMainTerm stop (twoAffineNu a s b t) P ∧
          upperMainTerm stop (twoAffineNu a s b t) P ≤
            (1 + eta) * V := by
  classical
  obtain ⟨C, hC, hdimension⟩ :=
    Erdos851.BetaSieveFundamental.exists_pairShift_dimension_bound_one_le
  refine ⟨3 * C, by nlinarith, ?_⟩
  intro a s b t z y S hz hzy hy hS hconstants hlog
  dsimp only
  let P := ascendingSlopeAwareSievePrimes a b z (y + 1)
  let stop := rosserStoppingPredicate 100 (y ^ S)
  have hstop :
      (fun u => decide (stop u.reverse)) =
        descendingRosserStop 100 (y ^ S) := by
    funext u
    rw [Bool.eq_iff_iff]
    simp [stop, descendingRosserStoppingPredicate]
  have hg0 : ∀ p : ℕ, 0 ≤ twoAffineNu a s b t p := by
    intro p
    by_cases hp0 : p = 0
    · subst p
      simp [twoAffineNu]
    · rw [twoAffineNu, ArithmeticFunction.prodPrimeFactors_apply hp0]
      apply Finset.prod_nonneg
      intro q hq
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hg1 : ∀ p ∈ P, twoAffineNu a s b t p < 1 := by
    intro p hp
    have hpSet : p ∈ slopeAwareSievePrimes a b z (y + 1) :=
      mem_ascendingSlopeAwareSievePrimes_iff.mp hp
    have hpData := mem_slopeAwareSievePrimes_iff.mp hpSet
    exact (twoAffineNu_pos_lt_one_of_not_dvd_constants_one_slope
      hpData.1 (hz.trans_lt hpData.2.1)
      (hconstants p hpSet).1 (hconstants p hpSet).2 hpData.2.2.2).2
  have hmain := Erdos851.finiteMainTerms_bounds_of_prefixProductRatio
    stop (twoAffineNu a s b t) P
    (slopeAwareBetaCutoffPrefix a b z y)
    (slopeAwareBetaCutoffPrefix a b z y)
    (A := 3 * C) (κ := 2) (start := S - 100)
    hg0 hg1 (ascendingSlopeAwareSievePrimes_nodup a b z (y + 1))
    (by
      intro r hr
      exact slopeAwareBetaCutoffPrefix_isPrefix a b z y r hy.le)
    (by
      intro r hr
      exact slopeAwareBetaCutoffPrefix_isPrefix a b z y r hy.le)
    (by
      intro r hr u hu hlen
      rw [hstop] at hu
      exact upperFailureTerm_chain_sublist_slopeAwareBetaCutoffPrefix
        hu hS hlen)
    (by
      intro r hr u hu hlen
      rw [hstop] at hu
      exact lowerFailureTerm_chain_sublist_slopeAwareBetaCutoffPrefix
        hu hS hlen)
    (by
      intro u hu
      rw [hstop] at hu
      exact upperFailureTerm_start_depth_slopeAware hy hu)
    (by
      intro u hu
      rw [hstop] at hu
      exact lowerFailureTerm_start_depth_slopeAware hy hu)
    (by nlinarith) (by norm_num) (by norm_num)
    (by
      intro r hr hstart
      calc
        (buchstabProduct (twoAffineNu a s b t)
          (slopeAwareBetaCutoffPrefix a b z y r))⁻¹ ≤
            (buchstabProduct
              (Erdos851.pairShiftDensity (affineDetNat a s b t))
              (betaCutoffPrefix z y r))⁻¹ :=
          slopeAwareBetaCutoff_inverse_le_pairShift hz hconstants
        _ ≤ (3 * C) * Real.rpow betaRatio ((2 : ℝ) * r) :=
          pairShift_betaCutoffPrefix_inverse_bound hC hdimension
            (affineDetNat a s b t) hz hzy)
    (by
      intro r hr hstart
      calc
        (buchstabProduct (twoAffineNu a s b t)
          (slopeAwareBetaCutoffPrefix a b z y r))⁻¹ ≤
            (buchstabProduct
              (Erdos851.pairShiftDensity (affineDetNat a s b t))
              (betaCutoffPrefix z y r))⁻¹ :=
          slopeAwareBetaCutoff_inverse_le_pairShift hz hconstants
        _ ≤ (3 * C) * Real.rpow betaRatio ((2 : ℝ) * r) :=
          pairShift_betaCutoffPrefix_inverse_bound hC hdimension
            (affineDetNat a s b t) hz hzy)
    (by
      intro r hstart hr
      have hrR : ((S - 100 : ℕ) : ℝ) ≤ r := by exact_mod_cast hstart
      norm_num at hlog ⊢
      nlinarith)
  dsimp only at hmain
  rw [finiteEulerProduct_ascendingSlopeAware_eq] at hmain
  exact hmain

end Erdos822
