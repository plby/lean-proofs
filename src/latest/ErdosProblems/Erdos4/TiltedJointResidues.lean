import ErdosProblems.Erdos4.TiltedCompositeCover
import ErdosProblems.Erdos4.TiltedPrimeLayer

/-! Assemble both layers on one residue assignment and classify every remaining integer. -/

namespace Erdos4.Tilted

open FGKMT RandomResidueSieve

open Classical in
noncomputable def frontierResidue (x : ℕ) (a : SieveState x)
    (b : ∀ p : growingSourcePrimes x, ZMod p.val)
    (d : ∀ p : compositeColors x, ZMod p.val) (p : ℕ) : ℕ :=
  if hp : p ∈ sievePrimes x then (a ⟨p, hp⟩).val
  else if hp : p ∈ growingSourcePrimes x then (b ⟨p, hp⟩).val
  else if hp : p ∈ compositeColors x then (d ⟨p, hp⟩).val else 0

theorem source_not_sieve {x p : ℕ} (hp : p ∈ growingSourcePrimes x) : p ∉ sievePrimes x := by
  intro hq
  have hp' := (mem_growingSourcePrimes.mp hp).2.1
  have hq' := (mem_coordinatePrimes.mp hq).2.2
  unfold sieveCutoff at hq'
  omega

theorem composite_not_sieve {x p : ℕ} (hp : p ∈ compositeColors x) : p ∉ sievePrimes x := by
  intro hq
  exact (not_le_of_gt (mem_compositeColors.mp hp).2.1) (sievePrimeValue_le x ⟨p, hq⟩)

theorem composite_not_source {x p : ℕ} (hp : p ∈ compositeColors x) : p ∉ growingSourcePrimes x := by
  intro hq
  exact (not_le_of_gt (mem_compositeColors.mp hp).2.1) (mem_growingSourcePrimes.mp hq).2.2

theorem frontierResidue_sieve (x : ℕ) (a : SieveState x)
    (b : ∀ p : growingSourcePrimes x, ZMod p.val) (d : ∀ p : compositeColors x, ZMod p.val)
    (p : sievePrimes x) : frontierResidue x a b d p.val = (a p).val := by
  simp only [frontierResidue, dif_pos p.property]

theorem frontierResidue_source (x : ℕ) (a : SieveState x)
    (b : ∀ p : growingSourcePrimes x, ZMod p.val) (d : ∀ p : compositeColors x, ZMod p.val)
    (p : growingSourcePrimes x) : frontierResidue x a b d p.val = (b p).val := by
  simp only [frontierResidue, dif_neg (source_not_sieve p.property), dif_pos p.property]

theorem frontierResidue_composite (x : ℕ) (a : SieveState x)
    (b : ∀ p : growingSourcePrimes x, ZMod p.val) (d : ∀ p : compositeColors x, ZMod p.val)
    (p : compositeColors x) : frontierResidue x a b d p.val = (d p).val := by
  simp only [frontierResidue, dif_neg (composite_not_sieve p.property),
    dif_neg (composite_not_source p.property), dif_pos p.property]

theorem frontierResidue_small {x : ℕ} (hw : smallCutoff x ≤ sieveCutoff x) (a : SieveState x)
    (b : ∀ p : growingSourcePrimes x, ZMod p.val) (d : ∀ p : compositeColors x, ZMod p.val)
    {p : ℕ} (hp : p ≤ smallCutoff x) : frontierResidue x a b d p = 0 := by
  have hsieve : p ∉ sievePrimes x := fun h => (not_lt_of_ge hp) (mem_coordinatePrimes.mp h).2.1
  have hsource : p ∉ growingSourcePrimes x := by
    intro h
    have hh := (mem_growingSourcePrimes.mp h).2.1
    unfold sieveCutoff at hw
    omega
  have hcomp : p ∉ compositeColors x := by
    intro h
    have hh := (mem_compositeColors.mp h).2.1
    have hlow := hp.trans (hw.trans (Nat.div_le_self x 64))
    omega
  simp only [frontierResidue, dif_neg hsieve, dif_neg hsource, dif_neg hcomp]

open Classical in
noncomputable def frontierRemainder (c : ℝ) (x : ℕ) (a : SieveState x)
    (b : ∀ p : growingSourcePrimes x, ZMod p.val) (d : ∀ p : compositeColors x, ZMod p.val) : Finset ℕ :=
  (Finset.Ioc x (gapTarget c x)).filter (fun n =>
    ∀ p ∈ (16 * x).primesLE, ¬n ≡ frontierResidue x a b d p [MOD p])

theorem frontierRemainder_subset {c : ℝ} {x : ℕ} (hw : smallCutoff x ≤ sieveCutoff x)
    (a : SieveState x) (b : ∀ p : growingSourcePrimes x, ZMod p.val)
    (d : ∀ p : compositeColors x, ZMod p.val) :
    frontierRemainder c x a b d ⊆
      (compositeRemainder c x a d ∪
        (sourceSurvivors (growingSourcePrimes x) (primeTargets c x) (primeSurvivors c x a) b).image Subtype.val) ∪
      roughNonsquarefree (gapTarget c x) (smallCutoff x) := by
  classical
  intro n hn
  simp only [frontierRemainder, Finset.mem_filter] at hn
  obtain ⟨hnI, hav⟩ := hn
  obtain ⟨hxn, hnY⟩ := Finset.mem_Ioc.mp hnI
  have hrough : IsRough (smallCutoff x) n := by
    intro p hp hpn
    by_contra hlarge
    have hpw : p ≤ smallCutoff x := le_of_not_gt hlarge
    have hpx : p ≤ x := hpw.trans (hw.trans (Nat.div_le_self x 64))
    apply hav p (Nat.mem_primesLE.mpr ⟨by omega, hp⟩)
    rw [frontierResidue_small hw a b d hpw]
    exact Nat.modEq_zero_iff_dvd.mpr hpn
  have hsurv : Survives (sievePrimeValue x) a {n} := by
    apply (survives_singleton (sievePrimeValue x) a n).mpr
    intro p heq
    have hp := (mem_coordinatePrimes.mp p.property).1
    have hpx := sievePrimeValue_le x p
    apply hav p.val (Nat.mem_primesLE.mpr ⟨by change p.val ≤ x at hpx; omega, hp⟩)
    rw [frontierResidue_sieve x a b d p]
    apply (ZMod.natCast_eq_natCast_iff n (a p).val (sievePrimeValue x p)).mp
    simpa only [ZMod.natCast_zmod_val] using heq.symm
  have hsource : ∀ p : growingSourcePrimes x, (n : ZMod p.val) ≠ b p := by
    intro p heq
    have hp := mem_growingSourcePrimes.mp p.property
    let instPrime : Fact p.val.Prime := ⟨hp.1⟩
    apply hav p.val (Nat.mem_primesLE.mpr ⟨by omega, hp.1⟩)
    rw [frontierResidue_source x a b d p]
    apply (ZMod.natCast_eq_natCast_iff n (b p).val p.val).mp
    simpa only [ZMod.natCast_zmod_val] using heq
  have hcomp : ∀ p : compositeColors x, (n : ZMod p.val) ≠ d p := by
    intro p heq
    have hp := mem_compositeColors.mp p.property
    let instPrime : Fact p.val.Prime := ⟨hp.1⟩
    apply hav p.val (Nat.mem_primesLE.mpr ⟨hp.2.2, hp.1⟩)
    rw [frontierResidue_composite x a b d p]
    apply (ZMod.natCast_eq_natCast_iff n (d p).val p.val).mp
    simpa only [ZMod.natCast_zmod_val] using heq
  by_cases hprime : n.Prime
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    have hnt : n ∈ primeTargets c x := ChebyshevIntervals.mem_primeInterval.mpr ⟨hprime, hxn, hnY⟩
    exact Finset.mem_image.mpr ⟨⟨n, hnt⟩, Finset.mem_filter.mpr
      ⟨(mem_primeSurvivors c x a ⟨n, hnt⟩).mpr hsurv, hsource⟩, rfl⟩
  · by_cases hsq : Squarefree n
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      have hC : n ∈ compositeTargets c x := mem_roughComposites.mpr ⟨hxn, hnY, hprime, hsq, hrough⟩
      exact Finset.mem_filter.mpr ⟨hC, hsurv, hcomp⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, hnY⟩, hrough⟩, hsq⟩

theorem frontierRemainder_card_le {c : ℝ} {x : ℕ} (hw : smallCutoff x ≤ sieveCutoff x)
    (a : SieveState x) (b : ∀ p : growingSourcePrimes x, ZMod p.val)
    (d : ∀ p : compositeColors x, ZMod p.val) :
    (frontierRemainder c x a b d).card ≤ (compositeRemainder c x a d).card +
      (sourceSurvivors (growingSourcePrimes x) (primeTargets c x) (primeSurvivors c x a) b).card +
        (roughNonsquarefree (gapTarget c x) (smallCutoff x)).card := by
  apply (Finset.card_le_card (frontierRemainder_subset hw a b d)).trans
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add_right
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)

end Erdos4.Tilted
