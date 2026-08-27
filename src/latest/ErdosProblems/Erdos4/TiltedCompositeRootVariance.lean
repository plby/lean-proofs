import ErdosProblems.Erdos4.TiltedCompositeVariances

/-! Uniform conditional variance at every surviving composite root. -/

open scoped BigOperators

namespace Erdos4.Tilted

open Filter FGKMT RandomResidueSieve

theorem eventually_composite_root_variance {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ [Nonempty (compositeColors x)]
      (F : CompositeFiberFamily c x) (hτ : 0 ≤ tiltExponent x) (v : compositeTargets c x),
      (rootedSieveLaw (sievePrimeValue x) (tiltExponent x) hτ v.val).mean (fun a =>
        (partitionRootNormalizer (actualSieveLaw x hτ) F.partition
          (fun n a => Survives (sievePrimeValue x) a {n}) v a - 1) ^ 2) ≤
        1 / Real.log (x : ℝ) ^ (30 : ℕ) := by
  classical
  filter_upwards [eventually_actual_block_weight_bounds hc (by norm_num : (0 : ℝ) < 1 / 16),
    eventually_composite_width hc, eventually_smallCutoff_bounds, eventually_gapTarget_bounds hc,
    eventually_actual_gcd_error hc, eventually_actual_correlation_budgets hc,
    eventually_variance_budget, eventually_coordinate_size_margin hc,
    eventually_outerScale_bounds, eventually_offset_le_smallCutoff, eventually_color_supply,
    eventually_ge_atTop 1]
    with x hweights hwidth hw hY herror hcorr hvariance hsmall hb hU hcolors hx
  intro _ F hτ v
  let σ := uniformLabelLaw (compositeColors x)
  let T : compositeColors x → Finset ℕ := fun p => F.companion v p.val
  let b : ℝ := 1 / ((compositeColors x).card : ℝ)
  let η := gcdTiltError (smallCutoff x) (Nat.sqrt x)
    (gapTarget c x ^ blockSize x (compositeTargets c x)) (tiltExponent x)
    ((b * (((16 * x : ℕ) : ℝ) + x)) ^ 2) ((2 * (offsetLimit x : ℝ)) ^ 2)
  have hxpos : 0 < x := hx
  have hxR : (0 : ℝ) < x := Nat.cast_pos.mpr hxpos
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hbmax : b ≤ Real.log (x : ℝ) ^ (2 : ℕ) / x := hcolors.2.2.1
  have hσ : ∀ p, σ.weight p ≤ b := by
    intro p
    simp only [σ, uniformLabelLaw, Fintype.card_coe, b, one_div, le_refl]
  have hS : ∀ s ∈ sievePrimes x, s.Prime ∧ smallCutoff x < s ∧ s ≤ x := by
    intro s hs
    have hh := mem_coordinatePrimes.mp hs
    exact ⟨hh.1, hh.2.1, hh.2.2.trans (Nat.div_le_self x 64)⟩
  have hpos : ∀ p : compositeColors x, ∀ n ∈ T p, 0 < n := by
    intro p n hn
    exact (Nat.zero_le x).trans_lt
      (compositeTargets_properties (F.companion_subset v p hn)).1
  have hfactors : ∀ p : compositeColors x, ∀ n ∈ T p, n.primeFactors ⊆ sievePrimes x :=
    fun p n hn => composite_factors_supported (F.companion_subset v p hn) hwidth
  have hcomplete : ∀ p q : compositeColors x, ∀ s ∈ (blockGcd (T p) (T q)).primeFactors,
      ∃ l, sievePrimeValue x l = s := by
    intro p q s hs
    have hh := blockGcd_factors_subset (T p) (T q) (sievePrimes x) (hpos p) (hfactors p) hs
    exact ⟨⟨s, hh⟩, rfl⟩
  have hm := rooted_gcd_tilt_moment (compositeColors x) (F.companion v) σ (sievePrimes x)
    (v := v.val) (Y := gapTarget c x) (U := offsetLimit x) (M := 16 * x)
    (W := smallCutoff x) (R := Nat.sqrt x) (X := x)
    (K := blockSize x (compositeTargets c x))
    hY.1 (by omega : 0 < smallCutoff x) (Nat.le_sqrt.mpr (by omega)) (Nat.sqrt_le x) hS
    (fun s hs => hU.trans (hS s hs).2.1.le)
    (fun p hp => ⟨(mem_compositeColors.mp hp).1.one_lt.le, (mem_compositeColors.mp hp).2.2⟩)
    (compositeTargets_properties v.property).2.1
    (fun p hp => color_offset_width hxpos (mem_compositeColors.mp hp).2.1.le hY.2.2.2.2.2.2.2.1)
    (fun p hp => F.companion_properties v ⟨p, hp⟩)
    (fun p hp => hpos ⟨p, hp⟩) (fun p hp => F.companion_card v ⟨p, hp⟩)
    (fun p hp => F.companion_squarefree hwidth v ⟨p, hp⟩)
    (fun p hp => hfactors ⟨p, hp⟩) hb0 hσ hτ hb.2.2.2.2.2.2.2
  have hη : η ≤ 1 / Real.log (x : ℝ) ^ (40 : ℕ) :=
    herror b (2 * (offsetLimit x : ℝ)) (16 * x) hb0 hbmax (by omega) (by positivity) le_rfl
  have hη0 : 0 ≤ η := gcdTiltError_nonneg _ _ _ _ (sq_nonneg _) (sq_nonneg _)
  have hqpos := sieveLaw_singleton_pos (sievePrimeValue x) (tiltExponent x) hτ v.val
  have hπ (p : compositeColors x) :
      0 < (actualSieveLaw x hτ).prob (fun a => Survives (sievePrimeValue x) a ((F.partition p).part v.val)) := by
    apply sieveLaw_survival_pos
    intro l
    have hsz := F.size p _ ((F.partition p).part_mem.mpr v.property)
    have hh := hsmall l
    omega
  have hrootprob (p : compositeColors x) :
      (rootedSieveLaw (sievePrimeValue x) (tiltExponent x) hτ v.val).prob
        (fun a => Survives (sievePrimeValue x) a (T p)) =
      (actualSieveLaw x hτ).prob (fun a => Survives (sievePrimeValue x) a ((F.partition p).part v.val)) /
        (actualSieveLaw x hτ).prob (fun a => Survives (sievePrimeValue x) a {v.val}) := by
    rw [rootedSieveLaw_survival_insert]
    simp only [T, F.companion_apply, insert_rootCompanions _ v.property]
  have hdiag (p : compositeColors x) :
      1 / (rootedSieveLaw (sievePrimeValue x) (tiltExponent x) hτ v.val).prob
        (fun a => Survives (sievePrimeValue x) a (T p)) ≤ (x : ℝ) ^ (1 / 16 : ℝ) := by
    rw [hrootprob]
    calc
      _ = (actualSieveLaw x hτ).prob (fun a => Survives (sievePrimeValue x) a {v.val}) /
          (actualSieveLaw x hτ).prob (fun a => Survives (sievePrimeValue x) a ((F.partition p).part v.val)) := by
        rw [one_div_div]
      _ ≤ 1 / (actualSieveLaw x hτ).prob
          (fun a => Survives (sievePrimeValue x) a ((F.partition p).part v.val)) :=
        div_le_div_of_nonneg_right ((actualSieveLaw x hτ).prob_le_one _) (hπ p).le
      _ ≤ _ := (hweights hτ).2 _ ((F.partition p).part_subset v.val)
        (F.size p _ ((F.partition p).part_mem.mpr v.property))
        (F.part_squarefree hwidth p _ ((F.partition p).part_mem.mpr v.property))
  have hv := rooted_block_variance (sievePrimeValue x) (sievePrimeValue_injective x)
    (tiltExponent x) hτ v.val σ T
    (K := blockSize x (compositeTargets c x)) (Y := gapTarget c x)
    (F.companion_card v) (F.companions_disjoint hY.2.2.2.1 v)
    (F.companion_avoid_root hwidth v) hsmall hY.1
    (fun p n hn => (F.companion_properties v p n hn).1)
    (w := (smallCutoff x : ℝ)) (B := (x : ℝ) ^ (1 / 16 : ℝ)) (b := b) (η := η)
    (by exact_mod_cast (show 0 < smallCutoff x by omega))
    (fun l => Nat.cast_le.mpr (mem_coordinatePrimes.mp l.property).2.1.le)
    (Real.rpow_nonneg hxR.le _) hσ
    (fun p => by rw [hrootprob]; exact (div_pos (hπ p) hqpos).ne') hdiag
    (fun p q => blockGcd_squarefree _ _ (F.companion_squarefree hwidth v p)) hcomplete hm
  have hfinal := hv.trans (hvariance _ _ _ _ (Real.rpow_nonneg hxR.le _) le_rfl
    hb0 hbmax hcorr.2 hη0 hη)
  have hevents (p : compositeColors x) (a : SieveState x) :
      blockEvent (fun n a => Survives (sievePrimeValue x) a {n})
        (partitionRoot (F.partition p) v).val a ↔
      Survives (sievePrimeValue x) a {v.val} ∧ Survives (sievePrimeValue x) a (T p) := by
    rw [blockEvent_survives, ← survives_insert]
    simp only [T, F.companion_apply, insert_rootCompanions _ v.property, partitionRoot]
  have heq := condition_normalizer_variance_eq (actualSieveLaw x hτ) σ
    (fun p => blockEvent (fun n a => Survives (sievePrimeValue x) a {n})
      (partitionRoot (F.partition p) v).val)
    (fun p a => Survives (sievePrimeValue x) a (T p))
    (fun a => Survives (sievePrimeValue x) a {v.val}) (fun _ => 0) hqpos.ne' hevents
  change (rootedSieveLaw (sievePrimeValue x) (tiltExponent x) hτ v.val).mean (fun a =>
    ((actualSieveLaw x hτ).prob (fun a => Survives (sievePrimeValue x) a {v.val}) *
      eventNormalizer (actualSieveLaw x hτ) σ
        (fun p => blockEvent (fun n a => Survives (sievePrimeValue x) a {n})
          (partitionRoot (F.partition p) v).val) a - 1) ^ 2) ≤ _
  exact heq.le.trans hfinal

end Erdos4.Tilted
