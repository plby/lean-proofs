/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.AnalyticMean
import ErdosProblems.Erdos48.External.Erdos4.ResidualPrimeFiberTail

/-!
# Sieve encoding of the large shifted-prime-factor exception

If `p + 1 = q*r*b*s`, where `p` and `s` are prime and `s` is larger than
the proposed smoothness frontier, then `s` lies in the residual prime fibre
with cofactor `q*r*b`.  This file proves the exact finite union bound needed
before applying the already formalized beta-sieve estimate for those fibres.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- The finite-witness predicate used in `representedLargeFactorPrimes`. -/
def IsRepresentedLargeFactor (x u q r B p : ℕ) : Prop :=
  ∃ b ∈ Finset.Icc 1 B, ∃ s ∈ Finset.Icc 1 (x + 1),
    s.Prime ∧ u < s ∧ p + 1 = q * r * b * s

noncomputable def isRepresentedLargeFactorDecidable (x u q r B : ℕ) :
    DecidablePred (IsRepresentedLargeFactor x u q r B) :=
  Classical.decPred _

/-- Primes having a represented large factor in the shifted value.  The
cofactor bound `B` is kept explicit for the later FLP parameter choice. -/
noncomputable def representedLargeFactorPrimes
    (x u q r B : ℕ) : Finset ℕ :=
  @Finset.filter ℕ (IsRepresentedLargeFactor x u q r B)
    (isRepresentedLargeFactorDecidable x u q r B) (Nat.primesLE x)

theorem mem_representedLargeFactorPrimes {x u q r B p : ℕ} :
    p ∈ representedLargeFactorPrimes x u q r B ↔
      p ≤ x ∧ p.Prime ∧
        IsRepresentedLargeFactor x u q r B p := by
  change
    p ∈ @Finset.filter ℕ (IsRepresentedLargeFactor x u q r B)
        (isRepresentedLargeFactorDecidable x u q r B) (Nat.primesLE x) ↔ _
  rw [@Finset.mem_filter ℕ (IsRepresentedLargeFactor x u q r B)
      (isRepresentedLargeFactorDecidable x u q r B), Nat.mem_primesLE]
  tauto

/-- The part of a residual fibre for which the shifted predecessor is also
prime.  This extra filter is essential when separating even and odd
cofactors: an odd cofactor has no such members beyond the trivial endpoint. -/
def residualPrimePairFiber (U y z m : ℕ) : Finset ℕ :=
  (Erdos4.residualPrimeFiber U y z m).filter fun s ↦
    (m * s - 1).Prime

@[simp] theorem mem_residualPrimePairFiber {U y z m s : ℕ} :
    s ∈ residualPrimePairFiber U y z m ↔
      s ∈ Erdos4.residualPrimeFiber U y z m ∧ (m * s - 1).Prime := by
  simp [residualPrimePairFiber]

/-- The image of one prime-pair residual fibre under `s ↦ m*s-1`. -/
def residualPrimeImage (U y z m : ℕ) : Finset ℕ :=
  (residualPrimePairFiber U y z m).image fun s ↦ m * s - 1

/-- Every represented large-factor prime belongs to the residual image for
its cofactor.  Primality of `p` makes `p` coprime to the small primorial once
`y < p`. -/
theorem representedLargeFactorPrimes_subset_biUnion_residualPrimeImage
    {x u q r B y z : ℕ}
    (hzu : z ≤ u) (hyp : y + 1 < q * r) :
    representedLargeFactorPrimes x u q r B ⊆
      (Finset.Icc 1 B).biUnion fun b ↦
        residualPrimeImage (x + 1) y z (q * r * b) := by
  intro p hp
  have hpData := mem_representedLargeFactorPrimes.mp hp
  change p ≤ x ∧ p.Prime ∧
    (∃ b ∈ Finset.Icc 1 B, ∃ s ∈ Finset.Icc 1 (x + 1),
      s.Prime ∧ u < s ∧ p + 1 = q * r * b * s) at hpData
  obtain ⟨b, hb, s, hsRange, hsPrime, hus, heq⟩ := hpData.2.2
  rw [Finset.mem_biUnion]
  refine ⟨b, hb, ?_⟩
  rw [residualPrimeImage, Finset.mem_image]
  refine ⟨s, ?_, ?_⟩
  · rw [mem_residualPrimePairFiber, Erdos4.mem_residualPrimeFiber]
    have hbPos : 0 < b := (Finset.mem_Icc.mp hb).1
    have hqrPos : 0 < q * r := lt_trans (by omega) hyp
    have hms : q * r * b * s = p + 1 := heq.symm
    have hsBound : s ≤ x + 1 := (Finset.mem_Icc.mp hsRange).2
    have hpLarge : y < p := by
      have hqrLe : q * r ≤ q * r * b * s := by
        exact (Nat.le_mul_of_pos_right (q * r) hbPos).trans
          (Nat.le_mul_of_pos_right (q * r * b) hsPrime.pos)
      rw [hms] at hqrLe
      omega
    have hcop : Nat.Coprime p (primorial y) := by
      apply Nat.coprime_of_dvd
      intro ℓ hℓPrime hℓp hℓprim
      have hℓy : ℓ ≤ y := hℓPrime.dvd_primorial_iff.mp hℓprim
      have hpeq : ℓ = p :=
        (Nat.prime_dvd_prime_iff_eq hℓPrime hpData.2.1).mp hℓp
      omega
    refine ⟨⟨hsBound, hsPrime, lt_of_le_of_lt hzu hus, ?_, ?_⟩, ?_⟩
    · calc
        q * r * b * s = p + 1 := hms
        _ ≤ x + 1 := Nat.add_le_add_right hpData.1 1
    · simpa [hms] using hcop
    · simpa [hms] using hpData.2.1
  · rw [← heq]
    omega

/-- Cardinal union bound for the represented large-factor exception. -/
theorem card_representedLargeFactorPrimes_le_sum_residualPrimeFiber
    {x u q r B y z : ℕ}
    (hzu : z ≤ u) (hyp : y + 1 < q * r) :
    (representedLargeFactorPrimes x u q r B).card ≤
      ∑ b ∈ Finset.Icc 1 B,
        (residualPrimePairFiber (x + 1) y z (q * r * b)).card := by
  calc
    (representedLargeFactorPrimes x u q r B).card ≤
        ((Finset.Icc 1 B).biUnion fun b ↦
          residualPrimeImage (x + 1) y z (q * r * b)).card :=
      Finset.card_le_card
        (representedLargeFactorPrimes_subset_biUnion_residualPrimeImage hzu hyp)
    _ ≤ ∑ b ∈ Finset.Icc 1 B,
        (residualPrimeImage (x + 1) y z (q * r * b)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ b ∈ Finset.Icc 1 B,
        (residualPrimePairFiber (x + 1) y z (q * r * b)).card := by
      apply Finset.sum_le_sum
      intro b hb
      unfold residualPrimeImage
      exact Finset.card_image_le

/-- Beyond `2`, a prime-pair fibre has an even cofactor. -/
theorem cofactor_even_of_mem_residualPrimePairFiber
    {U y z m s : ℕ} (hz : 2 ≤ z) (hm : 3 ≤ m)
    (hs : s ∈ residualPrimePairFiber U y z m) : Even m := by
  have hsData := mem_residualPrimePairFiber.mp hs
  have hsFiber := Erdos4.mem_residualPrimeFiber.mp hsData.1
  by_contra hmEven
  have hmOdd : Odd m := Nat.not_even_iff_odd.mp hmEven
  have hsNeTwo : s ≠ 2 := by omega
  have hsOdd : Odd s := hsFiber.2.1.odd_of_ne_two hsNeTwo
  have hpredEven : Even (m * s - 1) :=
    Nat.Odd.sub_odd (hmOdd.mul hsOdd) odd_one
  have hpredTwo : m * s - 1 = 2 := hsData.2.even_iff.mp hpredEven
  have hsThree : 3 ≤ s := hsFiber.2.1.odd_iff.mp hsOdd
  have hprodOne : 1 ≤ m * s := by nlinarith
  have hprodThree : m * s = 3 := by
    calc
      m * s = (m * s - 1) + 1 := (Nat.sub_add_cancel hprodOne).symm
      _ = 3 := by omega
  nlinarith

/-- Reindex the cofactor `q*r*b` and discard the empty odd-cofactor
prime-pair fibres.  The result is in the exact interval form consumed by the
summed residual beta-sieve theorem. -/
theorem sum_residualPrimePairFiber_mul_le_evenCofactorSum
    {U y z q r B : ℕ} (hz : 2 ≤ z) (hy : 1 < y)
    (hqr : y + 1 < q * r) :
    (∑ b ∈ Finset.Icc 1 B,
        ((residualPrimePairFiber U y z (q * r * b)).card : ℝ)) ≤
      ∑ m ∈ Erdos4.residualEvenCofactors (q * r - 1) (q * r * B),
        ((Erdos4.residualPrimeFiber U y z m).card : ℝ) := by
  classical
  let bs := (Finset.Icc 1 B).filter fun b ↦ Even (q * r * b)
  let ms := bs.image fun b ↦ q * r * b
  have hqrPos : 0 < q * r := by omega
  have hzero (b : ℕ) (hb : b ∈ Finset.Icc 1 B)
      (hbOdd : ¬Even (q * r * b)) :
      (residualPrimePairFiber U y z (q * r * b)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro s hs
    exact hbOdd (cofactor_even_of_mem_residualPrimePairFiber hz
      (by
        have hle : q * r ≤ q * r * b :=
          Nat.le_mul_of_pos_right (q * r) (Finset.mem_Icc.mp hb).1
        omega)
      hs)
  have hrestrict :
      (∑ b ∈ Finset.Icc 1 B,
          ((residualPrimePairFiber U y z (q * r * b)).card : ℝ)) =
        ∑ b ∈ bs,
          ((residualPrimePairFiber U y z (q * r * b)).card : ℝ) := by
    rw [show bs = (Finset.Icc 1 B).filter fun b ↦ Even (q * r * b) by rfl]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases heven : Even (q * r * b)
    · simp [heven]
    · simp [heven, hzero b hb heven]
  have hinj : Set.InjOn (fun b : ℕ ↦ q * r * b) bs := by
    intro a ha b hb hab
    exact Nat.mul_left_cancel hqrPos hab
  have himage : ms ⊆
      Erdos4.residualEvenCofactors (q * r - 1) (q * r * B) := by
    intro m hm
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hm
    have hbData := Finset.mem_filter.mp hb
    rw [Erdos4.mem_residualEvenCofactors]
    refine ⟨?_, ?_, hbData.2⟩
    · have hle : q * r ≤ q * r * b :=
        Nat.le_mul_of_pos_right (q * r) (Finset.mem_Icc.mp hbData.1).1
      omega
    · exact Nat.mul_le_mul_left (q * r) (Finset.mem_Icc.mp hbData.1).2
  rw [hrestrict]
  calc
    (∑ b ∈ bs,
        ((residualPrimePairFiber U y z (q * r * b)).card : ℝ)) ≤
        ∑ b ∈ bs,
          ((Erdos4.residualPrimeFiber U y z (q * r * b)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ = ∑ m ∈ ms,
        ((Erdos4.residualPrimeFiber U y z m).card : ℝ) := by
      rw [show ms = bs.image (fun b ↦ q * r * b) by rfl]
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj ha hb hab
    _ ≤ ∑ m ∈ Erdos4.residualEvenCofactors
        (q * r - 1) (q * r * B),
        ((Erdos4.residualPrimeFiber U y z m).card : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun _ _ _ ↦ by positivity)

/-- End-to-end finite upper bound for the large shifted-prime-factor
exception.  All scale conditions are explicit; the right side is precisely
the principal beta-sieve term plus the two Bombieri--Vinogradov endpoint
losses from the repository's residual-fibre theorem. -/
theorem exists_representedLargeFactorPrimes_beta_mertens_upper_bound :
    ∃ Aβ Cπ CV : ℝ,
      1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧
      ∀ {theta Bexp CBV L : ℝ}
        {X₀ x u q r B y z S : ℕ},
        2 ≤ z → z ≤ u → 1 < y → y + 1 < q * r → 1 ≤ B →
        0 < L → 101 ≤ S →
        Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 →
        BoundedGaps.Maynard.PrimeLevelWitness theta Bexp CBV X₀ →
        X₀ ≤ z →
        y ^ S ≤ BoundedGaps.Maynard.modulusCutoff theta z →
        (∀ m ∈ Erdos4.residualEvenCofactors
            (q * r - 1) (q * r * B),
          z ≤ (x + 1) / m ∧ X₀ ≤ (x + 1) / m ∧
          y ^ S ≤ BoundedGaps.Maynard.modulusCutoff theta ((x + 1) / m) ∧
          2 ≤ (x + 1) / m) →
        (∀ m ∈ Finset.Ioc (q * r - 1) (q * r * B),
          L ≤ Real.log (((x + 1) / m : ℕ) : ℝ)) →
        let eta := (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((representedLargeFactorPrimes x u q r B).card : ℝ) ≤
          (Cπ * (1 + eta) * CV * ((x + 1 : ℕ) : ℝ) /
              (L * Real.log (y : ℝ))) *
            (4 * (1 + Real.log
              (((q * r * B : ℕ) : ℝ) / (q * r - 1 : ℕ)))) +
          ∑ m ∈ Erdos4.residualEvenCofactors
              (q * r - 1) (q * r * B),
            (CBV * ((((x + 1) / m : ℕ) : ℝ)) /
                Real.rpow (Real.log ((((x + 1) / m : ℕ) : ℝ))) Bexp +
              CBV * (z : ℝ) /
                Real.rpow (Real.log (z : ℝ)) Bexp) := by
  obtain ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, hsum⟩ :=
    Erdos4.exists_sum_residualPrimeFiber_beta_mertens_upper_bound
  refine ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, ?_⟩
  intro theta Bexp CBV L X₀ x u q r B y z S hz hzu hy hqr hB hL hS
    hlogAβ hw hXz hDz hparams hlog
  dsimp only
  have hqrPos : 0 < q * r := by omega
  have hAco : 0 < q * r - 1 := by omega
  have hABco : q * r - 1 ≤ q * r * B := by
    have hle : q * r ≤ q * r * B := Nat.le_mul_of_pos_right (q * r) hB
    omega
  have hcardNat :=
    card_representedLargeFactorPrimes_le_sum_residualPrimeFiber
      (x := x) (u := u) (q := q) (r := r) (B := B) (y := y) (z := z)
      hzu hqr
  have hcard :
      ((representedLargeFactorPrimes x u q r B).card : ℝ) ≤
        ∑ b ∈ Finset.Icc 1 B,
          ((residualPrimePairFiber (x + 1) y z (q * r * b)).card : ℝ) := by
    exact_mod_cast hcardNat
  have hreindex := sum_residualPrimePairFiber_mul_le_evenCofactorSum
    (U := x + 1) (q := q) (r := r) (B := B) hz hy hqr
  have hsieve := hsum hAco hABco hL hy hS hlogAβ hw hXz hDz hparams hlog
  exact hcard.trans (hreindex.trans hsieve)

end

end Erdos48
