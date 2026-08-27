import ErdosProblems.Erdos4.TiltedCompositeFamily
import ErdosProblems.Erdos4.TiltedCompositeErrorBudget
import ErdosProblems.Erdos4.TiltedPartitionCapMass
import ErdosProblems.Erdos4.TiltedConditionedWeights

/-! The actual composite partitions satisfy both variance estimates uniformly. -/

open scoped BigOperators

namespace Erdos4.Tilted

open Filter FGKMT RandomResidueSieve

theorem eventually_composite_block_variance {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ (F : CompositeFiberFamily c x) (hC : (compositeTargets c x).Nonempty)
      (hτ : 0 ≤ tiltExponent x) (p : compositeColors x),
      (actualSieveLaw x hτ).mean (fun a =>
        (partitionNormalizer (actualSieveLaw x hτ) (F.partition p) hC
          (fun n a => Survives (sievePrimeValue x) a {n}) a - 1) ^ 2) ≤
        1 / Real.log (x : ℝ) ^ (30 : ℕ) := by
  classical
  filter_upwards [eventually_actual_block_weight_bounds hc (by norm_num : (0 : ℝ) < 1 / 16),
    eventually_composite_width hc, eventually_smallCutoff_bounds, eventually_gapTarget_bounds hc,
    eventually_actual_gcd_error hc, eventually_actual_correlation_budgets hc,
    eventually_variance_budget, eventually_coordinate_size_margin hc,
    eventually_outerScale_bounds, eventually_ge_atTop 1]
    with x hweights hwidth hw hY herror hcorr hvariance hsmall hb hx
  intro F hC hτ p
  let P := F.partition p
  let σ := uniformPartLaw P hC
  let b : ℝ := 1 / (P.parts.card : ℝ)
  let η := gcdTiltError (smallCutoff x) (Nat.sqrt x)
    (gapTarget c x ^ blockSize x (compositeTargets c x)) (tiltExponent x)
    ((b * (((x + p.val : ℕ) : ℝ) + x)) ^ 2) ((offsetLimit x : ℝ) ^ 2)
  have hxpos : 0 < x := hx
  have hxR : (0 : ℝ) < x := Nat.cast_pos.mpr hxpos
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hbmax : b ≤ Real.log (x : ℝ) ^ (2 : ℕ) / x := by
    apply (inverse_partition_count_le hxpos P (F.count_lower p)).trans
    apply div_le_div_of_nonneg_right _ hxR.le
    nlinarith [hb.1]
  have hσ : ∀ E, σ.weight E ≤ b := fun _ => le_rfl
  have hS : ∀ s ∈ sievePrimes x, s.Prime ∧ smallCutoff x < s ∧ s ≤ x := by
    intro s hs
    have hh := mem_coordinatePrimes.mp hs
    exact ⟨hh.1, hh.2.1, hh.2.2.trans (Nat.div_le_self x 64)⟩
  have hpos : ∀ E : P.parts, ∀ n ∈ E.val, 0 < n := by
    intro E n hn
    exact (Nat.zero_le x).trans_lt (compositeTargets_properties (P.subset E.property hn)).1
  have hcomplete : ∀ E D : P.parts, ∀ s ∈ blockGcd E.val D.val |>.primeFactors,
      ∃ l, sievePrimeValue x l = s := by
    intro E D s hs
    have hh := blockGcd_factors_subset E.val D.val (sievePrimes x) (hpos E)
      (fun n hn => composite_factors_supported (P.subset E.property hn) hwidth) hs
    exact ⟨⟨s, hh⟩, rfl⟩
  have hm := partition_gcd_tilt_moment P σ (sievePrimes x)
    (x := x) (p := p.val) (Y := gapTarget c x) (U := offsetLimit x)
    (W := smallCutoff x) (R := Nat.sqrt x) (X := x)
    (K := blockSize x (compositeTargets c x))
    (mem_compositeColors.mp p.property).1.pos hY.1 (by omega : 0 < smallCutoff x)
    (Nat.le_sqrt.mpr (by omega)) (Nat.sqrt_le x) hS
    (fun n hn => ⟨(compositeTargets_properties hn).1, (compositeTargets_properties hn).2.1⟩)
    (color_offset_width hxpos (mem_compositeColors.mp p.property).2.1.le hY.2.2.2.2.2.2.2.1)
    (F.fiber p) (F.size p) (F.part_squarefree hwidth p)
    (fun n hn => composite_factors_supported hn hwidth) hb0 hσ hτ hb.2.2.2.2.2.2.2
  have hη : η ≤ 1 / Real.log (x : ℝ) ^ (40 : ℕ) := by
    apply herror b (offsetLimit x) (x + p.val) hb0 hbmax
      (by have hh := (mem_compositeColors.mp p.property).2.2; omega)
      (Nat.cast_nonneg _) (by linarith [Nat.cast_nonneg (α := ℝ) (offsetLimit x)])
  have hη0 : 0 ≤ η := gcdTiltError_nonneg _ _ _ _ (sq_nonneg _) (sq_nonneg _)
  have hv := disjoint_block_variance (sievePrimeValue x) (sievePrimeValue_injective x)
    (tiltExponent x) hτ σ (fun E : P.parts => E.val)
    (K := blockSize x (compositeTargets c x)) (Y := gapTarget c x)
    (fun E => F.size p E.val E.property)
    (fun E D hED => P.disjoint E.property D.property (fun he => hED (Subtype.ext he)))
    (fun l => by have hh := hsmall l; omega) hY.1
    (fun E n hn => (compositeTargets_properties (P.subset E.property hn)).2.1)
    (w := (smallCutoff x : ℝ)) (B := (x : ℝ) ^ (1 / 16 : ℝ))
    (b := b) (η := η) (by exact_mod_cast (show 0 < smallCutoff x by omega))
    (fun l => Nat.cast_le.mpr (mem_coordinatePrimes.mp l.property).2.1.le)
    (Real.rpow_nonneg hxR.le _) hσ
    (fun E => (hweights hτ).2 E.val (P.subset E.property) (F.size p E.val E.property)
      (F.part_squarefree hwidth p E.val E.property))
    (fun E D => blockGcd_squarefree E.val D.val (F.part_squarefree hwidth p E.val E.property))
    hcomplete hm
  have hfinal := hv.trans (hvariance _ _ _ _ (Real.rpow_nonneg hxR.le _) le_rfl
    hb0 hbmax hcorr.1 hη0 hη)
  have hevents : (fun E : P.parts =>
      blockEvent (fun n a => Survives (sievePrimeValue x) a {n}) E.val) =
        (fun E a => Survives (sievePrimeValue x) a E.val) := by
    funext E a
    exact propext (blockEvent_survives _ _ _)
  change (actualSieveLaw x hτ).mean (fun a =>
    (eventNormalizer (actualSieveLaw x hτ) σ
      (fun E : P.parts => blockEvent (fun n a => Survives (sievePrimeValue x) a {n}) E.val) a - 1) ^ 2) ≤ _
  rw [hevents]
  exact hfinal

end Erdos4.Tilted
