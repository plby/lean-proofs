import ErdosProblems.Erdos4.TiltedCompositeRootVariance
import ErdosProblems.Erdos4.TiltedCompositeCoverBudget
import ErdosProblems.Erdos4.TiltedPartitionCover

/-! Legal composite residue choices with an arbitrarily small expected remainder. -/

open scoped BigOperators

namespace Erdos4.Tilted

open Filter FGKMT RandomResidueSieve

open Classical in
noncomputable def compositeRemainder (c : ℝ) (x : ℕ) (a : SieveState x)
    (b : ∀ p : compositeColors x, ZMod p.val) : Finset ℕ :=
  (compositeTargets c x).filter (fun n => Survives (sievePrimeValue x) a {n} ∧
    ∀ p, (n : ZMod p.val) ≠ b p)

theorem selectedPart_has_residue {C : Finset ℕ} (P : Finpartition C) (p : ℕ)
    (hfiber : ∀ E ∈ P.parts, ∀ n ∈ E, ∀ m ∈ E, (n : ZMod p) = (m : ZMod p))
    (e : Option P.parts) : ∃ b : ZMod p, ∀ n ∈ selectedPart P e, (n : ZMod p) = b := by
  classical
  by_cases hE : (selectedPart P e).Nonempty
  · obtain ⟨n, hn⟩ := hE
    refine ⟨(n : ZMod p), fun m hm => ?_⟩
    have hpart : selectedPart P e ∈ P.parts :=
      (selectedPart_mem_or_empty P e).resolve_left (Finset.Nonempty.ne_empty ⟨n, hn⟩)
    exact hfiber _ hpart m hm n hn
  · exact ⟨0, fun n hn => False.elim (hE ⟨n, hn⟩)⟩

theorem exists_composite_residues_of_partition {c : ℝ} {x : ℕ} [Nonempty (compositeColors x)]
    (F : CompositeFiberFamily c x) (hC : (compositeTargets c x).Nonempty)
    (hτ : 0 ≤ tiltExponent x) (a : SieveState x) :
    ∃ b : ∀ p : compositeColors x, ZMod p.val,
      ((compositeRemainder c x a b).card : ℝ) ≤
        partitionMissCost (actualSieveLaw x hτ) F.partition hC
          (fun n a => Survives (sievePrimeValue x) a {n}) a := by
  classical
  obtain ⟨e, _, hcard⟩ := exists_partition_cover (actualSieveLaw x hτ) F.partition hC
    (fun n a => Survives (sievePrimeValue x) a {n}) a
  choose b hb using fun p => selectedPart_has_residue (F.partition p) p.val (F.fiber p) (e p)
  refine ⟨b, (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans hcard⟩
  intro n hn
  obtain ⟨hnC, hnR, hnmiss⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnC, hnR⟩, ?_⟩
  intro p hp
  exact hnmiss p (hb p n hp)

theorem eventually_partitionMissCost_small {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ [Nonempty (compositeColors x)] (F : CompositeFiberFamily c x)
      (hC : (compositeTargets c x).Nonempty) (hτ : 0 ≤ tiltExponent x),
      (actualSieveLaw x hτ).mean (partitionMissCost (actualSieveLaw x hτ) F.partition hC
        (fun n a => Survives (sievePrimeValue x) a {n})) ≤ ε * (x : ℝ) / Real.log (x : ℝ) := by
  classical
  filter_upwards [eventually_composite_block_variance hc, eventually_composite_root_variance hc,
    eventually_actual_composite_survival hc, eventually_composite_cover_numeric_budget hc hε,
    eventually_ge_atTop 1] with x hblock hroot hsurv hbudget hx
  intro _ F hC hτ
  have hh := partitionMissCost_mean_le (actualSieveLaw x hτ) F.partition hC
    (fun n a => Survives (sievePrimeValue x) a {n}) (fun _ => 0)
    (Q := compositeSurvivalBound x) (B := 17 * (x : ℝ))
    (δroot := 1 / Real.log (x : ℝ) ^ (30 : ℕ)) (δblock := 1 / Real.log (x : ℝ) ^ (30 : ℕ))
    (compositeSurvivalBound_pos hx) (by positivity) (by positivity)
    (fun v => (hsurv hτ v.val v.property).1.ne') (fun v => (hsurv hτ v.val v.property).2)
    F.size (fun p => by exact_mod_cast F.count_le p) (hroot F hτ) (hblock F hC hτ)
  exact hh.trans (by simpa only [Fintype.card_coe] using hbudget)

open Classical in
theorem mean_surviving_targets_le {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω)
    (C : Finset ℕ) (R : ℕ → Ω → Prop) {Q : ℝ} (hq : ∀ n ∈ C, ν.prob (R n) ≤ Q) :
    ν.mean (fun a => ((C.filter (fun n => R n a)).card : ℝ)) ≤ (C.card : ℝ) * Q := by
  classical
  have heq (a : Ω) : ((C.filter (fun n => R n a)).card : ℝ) =
      ∑ n ∈ C, if R n a then (1 : ℝ) else 0 := (Finset.sum_boole _ _).symm
  calc
    _ = ν.mean (fun a => ∑ n ∈ C, if R n a then (1 : ℝ) else 0) := ν.mean_congr heq
    _ = ∑ n ∈ C, ν.prob (R n) := by
      rw [FiniteLaw.mean_finset_sum]
      exact Finset.sum_congr rfl (fun n _ => (ν.prob_eq_mean (R n)).symm)
    _ ≤ ∑ _n ∈ C, Q := Finset.sum_le_sum (fun n hn => hq n hn)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem eventually_small_composite_survivors {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, (x : ℝ) * compositeSurvivalBound x ≤ ε * (x : ℝ) / Real.log (x : ℝ) := by
  filter_upwards [eventually_compositeSurvivalBound, eventually_outerScale_bounds,
    log_two_tendsto.eventually (eventually_ge_atTop (1 / ε))] with x hQ hb hl
  have hL : 0 < Real.log (x : ℝ) := by linarith [hb.1]
  have hl1 : 1 ≤ Real.log (Real.log (x : ℝ)) := hb.2.1
  have hlpos : 0 < Real.log (Real.log (x : ℝ)) := lt_of_lt_of_le zero_lt_one hl1
  have hcoeff : 1 / Real.log (Real.log (x : ℝ)) ^ (2 : ℕ) ≤ ε := by
    apply (div_le_iff₀ (pow_pos hlpos 2)).mpr
    have hh := (div_le_iff₀ hε).mp hl
    have hp : Real.log (Real.log (x : ℝ)) ≤ Real.log (Real.log (x : ℝ)) ^ (2 : ℕ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hp hε.le]
  calc
    _ ≤ (x : ℝ) * (1 / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ (2 : ℕ))) :=
      mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg x)
    _ = (1 / Real.log (Real.log (x : ℝ)) ^ (2 : ℕ)) * (x : ℝ) / Real.log (x : ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg x)) hL.le

theorem exists_composite_cover_cost {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ hτ : 0 ≤ tiltExponent x,
      ∃ cost : SieveState x → ℝ, (∀ a, 0 ≤ cost a) ∧
        (actualSieveLaw x hτ).mean cost ≤ ε * (x : ℝ) / Real.log (x : ℝ) ∧
        ∀ a, ∃ b : ∀ p : compositeColors x, ZMod p.val,
          ((compositeRemainder c x a b).card : ℝ) ≤ cost a := by
  classical
  filter_upwards [eventually_partitionMissCost_small hc hε, eventually_small_composite_survivors hε,
    eventually_actual_composite_survival hc, eventually_color_supply, eventually_ge_atTop 1]
    with x hlarge hsmall hsurv hcolors hx
  intro hτ
  let instColors : Nonempty (compositeColors x) :=
    nonempty_subtype.mpr (Finset.card_pos.mp hcolors.1)
  by_cases hC : x ≤ (compositeTargets c x).card
  · obtain ⟨F⟩ := exists_compositeFiberFamily hx hC
    let hnonempty := F.targets_nonempty hx
    refine ⟨partitionMissCost (actualSieveLaw x hτ) F.partition hnonempty
      (fun n a => Survives (sievePrimeValue x) a {n}), ?_, hlarge F hnonempty hτ, ?_⟩
    · intro a
      exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
    · exact exists_composite_residues_of_partition F hnonempty hτ
  · let cost : SieveState x → ℝ := fun a =>
      (((compositeTargets c x).filter (fun n => Survives (sievePrimeValue x) a {n})).card : ℝ)
    refine ⟨cost, fun _ => Nat.cast_nonneg _, ?_, ?_⟩
    · apply (mean_surviving_targets_le (actualSieveLaw x hτ) (compositeTargets c x)
        (fun n a => Survives (sievePrimeValue x) a {n}) (fun n hn => (hsurv hτ n hn).2)).trans
      exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega))
        (compositeSurvivalBound_nonneg x)).trans hsmall
    · intro a
      refine ⟨fun _ => 0, Nat.cast_le.mpr (Finset.card_le_card ?_)⟩
      intro n hn
      obtain ⟨hnC, hnR, _⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hnC, hnR⟩

end Erdos4.Tilted
