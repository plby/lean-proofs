import ErdosProblems.Erdos4.TiltedJointResidues

/-! Fresh-prime cleanup and translation of the covered interval to offsets starting at one. -/

namespace Erdos4.Tilted

open Filter FGKMT

open Classical in
theorem cover_with_fresh_primes (S P R : Finset ℕ) (a : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) (hdis : Disjoint P R)
    (hcard : (S.filter (fun n => ∀ p ∈ P, ¬n ≡ a p [MOD p])).card ≤ R.card) :
    ∃ cover : Erdos4.PartialResidueCover S, cover.primes = P ∪ R := by
  let missed := S.filter (fun n => ∀ p ∈ P, ¬n ≡ a p [MOD p])
  let left : Erdos4.PartialResidueCover (S \ missed) := {
    primes := P
    residue := a
    prime := hP
    covers := by
      intro n hn
      obtain ⟨hnS, hnmiss⟩ := Finset.mem_sdiff.mp hn
      have hh : ¬∀ p ∈ P, ¬n ≡ a p [MOD p] := fun hall => hnmiss (Finset.mem_filter.mpr ⟨hnS, hall⟩)
      push Not at hh
      exact hh }
  obtain ⟨right, hright⟩ := Erdos4.PartialResidueCover.exists_of_card_le hR hcard
  have hd : Disjoint left.primes right.primes := by simpa only [hright] using hdis
  have heq : (S \ missed) ∪ missed = S := Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
  exact ⟨(left.union right hd).reindex heq, by
    simp only [Erdos4.PartialResidueCover.reindex_primes, Erdos4.PartialResidueCover.union, hright, left]⟩

noncomputable def shift_interval_cover {x Y : ℕ}
    (cover : Erdos4.PartialResidueCover (Finset.Ioc x Y)) : Erdos4.ResidueCover (Y - x) where
  primes := cover.primes
  residue p := ((cover.residue p : ZMod p) - (x : ZMod p)).val
  prime := cover.prime
  covers i hi1 hiy := by
    obtain ⟨p, hp, hmod⟩ := cover.covers (x + i) (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
    let instPrime : Fact p.Prime := ⟨cover.prime p hp⟩
    refine ⟨p, hp, ?_⟩
    apply (ZMod.natCast_eq_natCast_iff i ((cover.residue p : ZMod p) - (x : ZMod p)).val p).mp
    rw [ZMod.natCast_zmod_val]
    have heq := (ZMod.natCast_eq_natCast_iff (x + i) (cover.residue p) p).mpr hmod
    rw [Nat.cast_add] at heq
    exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using heq)

theorem eventually_roughNonsquarefree_small {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      ((roughNonsquarefree (gapTarget c x) (smallCutoff x)).card : ℝ) ≤
        ε * (x : ℝ) / Real.log (x : ℝ) := by
  filter_upwards [eventually_gapTarget_bounds hc, eventually_smallCutoff_bounds,
    eventually_outerScale_bounds, log_tendsto.eventually (eventually_ge_atTop (1 / ε))]
    with x hY hw hb hLε
  let L := Real.log (x : ℝ)
  have hL1 : 1 ≤ L := by have hh := hb.1; change 16 ≤ L at hh; linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hwpos : 0 < smallCutoff x := by omega
  have hW : L ^ (4 : ℕ) ≤ (smallCutoff x : ℝ) :=
    (pow_le_pow_right₀ hL1 (by norm_num : 4 ≤ (98 : ℕ))).trans hw.2.2.1
  have hcoeff : 1 ≤ ε * L ^ (2 : ℕ) := by
    have hh := (div_le_iff₀ hε).mp hLε
    change 1 ≤ L * ε at hh
    have hpow : L ≤ L ^ (2 : ℕ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hpow hε.le]
  calc
    _ ≤ (gapTarget c x : ℝ) / smallCutoff x := roughNonsquarefree_card_le hwpos _
    _ ≤ ((x : ℝ) * L) / smallCutoff x := div_le_div_of_nonneg_right hY.2.2.2.2.2.2.2.1 (Nat.cast_nonneg _)
    _ ≤ ((x : ℝ) * L) / L ^ (4 : ℕ) := div_le_div_of_nonneg_left (by positivity) (by positivity) hW
    _ = (x : ℝ) / L ^ (3 : ℕ) := by field_simp
    _ ≤ (ε * L ^ (2 : ℕ)) * (x : ℝ) / L ^ (3 : ℕ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg x)
    _ = _ := by
      change (ε * L ^ (2 : ℕ)) * (x : ℝ) / L ^ (3 : ℕ) = ε * (x : ℝ) / L
      field_simp

theorem exists_tilted_interval_cover :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      ∃ cover : Erdos4.ResidueCover (gapTarget c x - x), cover.primes ⊆ (256 * x).primesLE := by
  classical
  let ε := Real.log 2 / 8
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨c, hc, hprime⟩ := exists_prime_cover_cost hε
  refine ⟨c, hc, ?_⟩
  filter_upwards [hprime, exists_composite_cover_cost hc hε,
    eventually_roughNonsquarefree_small hc hε, eventually_smallCutoff_bounds,
    eventually_color_supply, eventually_outerScale_bounds]
    with x hprime hcomp hsq hw hcolors hb
  have hτ : 0 ≤ tiltExponent x := hb.2.2.2.2.2.2.1.le
  have hLpos : 0 < Real.log (x : ℝ) := by linarith [hb.1]
  obtain ⟨primeCost, _, hprimeMean, hprimeChoice⟩ := hprime hτ
  obtain ⟨compCost, _, hcompMean, hcompChoice⟩ := hcomp hτ
  obtain ⟨a, _, ha⟩ := (actualSieveLaw x hτ).exists_support_le_mean (fun a => compCost a + primeCost a)
  rw [FiniteLaw.mean_add] at ha
  have hsum : compCost a + primeCost a ≤ 2 * ε * (x : ℝ) / Real.log (x : ℝ) :=
    ha.trans ((add_le_add hcompMean hprimeMean).trans_eq (by ring))
  obtain ⟨b, hb⟩ := hprimeChoice a
  obtain ⟨d, hd⟩ := hcompChoice a
  have hcard : (frontierRemainder c x a b d).card ≤ (reserveColors x).card := by
    have hh : ((frontierRemainder c x a b d).card : ℝ) ≤
        (compositeRemainder c x a d).card +
          (sourceSurvivors (growingSourcePrimes x) (primeTargets c x) (primeSurvivors c x a) b).card +
          (roughNonsquarefree (gapTarget c x) (smallCutoff x)).card := by
      exact_mod_cast frontierRemainder_card_le hw.2.1 a b d
    have htotal : ((frontierRemainder c x a b d).card : ℝ) ≤
        Real.log 2 * (x : ℝ) / Real.log (x : ℝ) := by
      calc
        _ ≤ (compCost a + primeCost a) + ε * (x : ℝ) / Real.log (x : ℝ) :=
          hh.trans (add_le_add (add_le_add hd hb) hsq)
        _ ≤ (2 * ε * (x : ℝ) / Real.log (x : ℝ)) + ε * (x : ℝ) / Real.log (x : ℝ) :=
          add_le_add hsum le_rfl
        _ = 3 * ε * (x : ℝ) / Real.log (x : ℝ) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by dsimp [ε]; linarith : 3 * ε ≤ Real.log 2) (Nat.cast_nonneg x)) hLpos.le
    exact_mod_cast htotal.trans hcolors.2.2.2
  have hfresh : Disjoint ((16 * x).primesLE) (reserveColors x) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (not_le_of_gt (mem_reserveColors.mp hq).2.1) (Nat.mem_primesLE.mp hp).1
  obtain ⟨cover, hcover⟩ := cover_with_fresh_primes (Finset.Ioc x (gapTarget c x))
    (16 * x).primesLE (reserveColors x) (frontierResidue x a b d)
    (fun p hp => (Nat.mem_primesLE.mp hp).2) (fun p hp => (mem_reserveColors.mp hp).1) hfresh
    (by
      apply le_trans _ hcard
      apply le_of_eq
      apply congrArg Finset.card
      ext n
      simp only [frontierRemainder, Finset.mem_filter])
  refine ⟨shift_interval_cover cover, ?_⟩
  change cover.primes ⊆ (256 * x).primesLE
  rw [hcover]
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · have hh := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨by omega, hh.2⟩
  · have hh := mem_reserveColors.mp hp
    exact Nat.mem_primesLE.mpr ⟨hh.2.2, hh.1⟩

end Erdos4.Tilted
