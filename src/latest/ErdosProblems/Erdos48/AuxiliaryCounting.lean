/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.LargeFactorSieveSharp
import ErdosProblems.Erdos48.GoodBranchSelection
import ErdosProblems.Erdos48.EndpointMass

/-!
# Finite auxiliary-prime counting for FLP Lemma 2.6

This file isolates the purely finite incidence argument in the proof of the
few-bad-moduli lemma.  For each auxiliary prime `r`, primes in the progression
`-1 mod q*r` are retained after deleting the large shifted-prime-factor
exception.  The remaining fibres lie in the required shifted-smooth set.
Their cardinalities may be summed because any one shifted prime has only a
bounded number of auxiliary prime divisors.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- The progression fibre after deleting the explicitly represented
large-factor exception. -/
def usableAuxiliaryFiber
    (x u q r B : ℕ) : Finset ℕ :=
  primesInProgression x (q * r) (q * r - 1) \
    representedLargeFactorPrimes x u q r B

@[simp] theorem mem_usableAuxiliaryFiber
    {x u q r B p : ℕ} :
    p ∈ usableAuxiliaryFiber x u q r B ↔
      p ∈ primesInProgression x (q * r) (q * r - 1) ∧
        p ∉ representedLargeFactorPrimes x u q r B := by
  simp [usableAuxiliaryFiber]

/-- Membership in the residue class `-1 mod m` gives divisibility of the
shift.  This tiny congruence conversion is used repeatedly in FLP's
auxiliary-prime argument. -/
theorem dvd_add_one_of_mem_primesInProgression
    {x m p : ℕ} (hm : 1 < m)
    (hp : p ∈ primesInProgression x m (m - 1)) :
    m ∣ p + 1 := by
  have hres : p ≡ m - 1 [MOD m] :=
    (mem_primesInProgression.mp hp).2.2
  apply Nat.modEq_zero_iff_dvd.mp
  calc
    p + 1 ≡ (m - 1) + 1 [MOD m] :=
      hres.add (Nat.ModEq.refl 1)
    _ = m := Nat.sub_add_cancel (by omega)
    _ ≡ 0 [MOD m] := by simp [Nat.ModEq]

/-- Extract the large prime factor of a nonsmooth shift and package the
remaining cofactor in `representedLargeFactorPrimes`.  The final cofactor
bound is kept as an explicit hypothesis, since in FLP it follows from the
chosen ranges `p ≤ x`, `q`, `r`, and `s > u`. -/
theorem mem_representedLargeFactorPrimes_of_not_smooth
    {x u q r B p : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hqu : q ≤ u) (hru : r ≤ u)
    (hp : p ∈ primesInProgression x (q * r) (q * r - 1))
    (hnonsmooth : ¬ SmoothAtMost u (p + 1))
    (hcofactor : ∀ s : ℕ, s.Prime → u < s → s ∣ p + 1 →
      (p + 1) / (q * r * s) ≤ B) :
    p ∈ representedLargeFactorPrimes x u q r B := by
  classical
  have hshift : p + 1 ≠ 0 := by omega
  have hsExists : ∃ s : ℕ, s.Prime ∧ s ∣ p + 1 ∧ u < s := by
    by_contra hnone
    apply hnonsmooth
    rw [smoothAtMost_iff_prime_dvd hshift]
    intro s hsPrime hsdiv
    by_contra hsu
    apply hnone
    exact ⟨s, hsPrime, hsdiv, Nat.lt_of_not_ge hsu⟩
  obtain ⟨s, hsPrime, hsdiv, hus⟩ := hsExists
  have hqrDiv : q * r ∣ p + 1 :=
    dvd_add_one_of_mem_primesInProgression (by
      have hqTwo := hq.two_le
      have hrTwo := hr.two_le
      have hfour : 2 * 2 ≤ q * r := Nat.mul_le_mul hqTwo hrTwo
      omega) hp
  have hqs : q ≠ s := by omega
  have hrs : r ≠ s := by omega
  have hcop : Nat.Coprime (q * r) s :=
    (Nat.coprime_mul_iff_left).2
      ⟨(Nat.coprime_primes hq hsPrime).2 hqs,
        (Nat.coprime_primes hr hsPrime).2 hrs⟩
  have hprodDiv : q * r * s ∣ p + 1 :=
    hcop.mul_dvd_of_dvd_of_dvd hqrDiv hsdiv
  let b := (p + 1) / (q * r * s)
  have hbPos : 1 ≤ b := by
    apply (Nat.one_le_div_iff
      (Nat.mul_pos (Nat.mul_pos hq.pos hr.pos) hsPrime.pos)).2
    exact Nat.le_of_dvd (by omega) hprodDiv
  have hbB : b ≤ B := hcofactor s hsPrime hus hsdiv
  rw [mem_representedLargeFactorPrimes]
  refine ⟨(mem_primesInProgression.mp hp).1,
    (mem_primesInProgression.mp hp).2.1, ?_⟩
  refine ⟨b, Finset.mem_Icc.mpr ⟨hbPos, hbB⟩, s,
    Finset.mem_Icc.mpr ⟨hsPrime.pos, ?_⟩, hsPrime, hus, ?_⟩
  · exact (Nat.le_of_dvd (by omega) hsdiv).trans
      (Nat.add_le_add_right (mem_primesInProgression.mp hp).1 1)
  · have hquot := Nat.mul_div_cancel' hprodDiv
    dsimp only [b]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hquot.symm

/-- Product divisibility for a finite pairwise-coprime natural family.
The generic `IsCoprime` lemma is not suitable over `ℕ`, so we record the
natural-number form directly. -/
theorem finset_prod_dvd_of_pairwise_coprime_nat
    {I : Type*} [DecidableEq I] (s : Finset I) (f : I → ℕ) (N : ℕ)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j))
    (hdvd : ∀ i ∈ s, f i ∣ N) :
    ∏ i ∈ s, f i ∣ N := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hcop : Nat.Coprime (f a) (∏ i ∈ s, f i) := by
        apply Nat.Coprime.prod_right
        intro i hi
        exact hpair a (Finset.mem_insert_self a s) i
          (Finset.mem_insert_of_mem hi) (fun hai ↦ ha (hai ▸ hi))
      apply hcop.mul_dvd_of_dvd_of_dvd
      · exact hdvd a (Finset.mem_insert_self a s)
      · apply ih
        · intro i hi j hj hij
          exact hpair i (Finset.mem_insert_of_mem hi) j
            (Finset.mem_insert_of_mem hj) hij
        · intro i hi
          exact hdvd i (Finset.mem_insert_of_mem hi)

/-- Product bound for the number of distinct auxiliary prime divisors of a
shift.  If every auxiliary prime exceeds `R0`, then `D + 1` such divisors
would force `(R0 + 1)^(D + 1) ≤ p + 1`. -/
theorem card_filter_prime_dvd_shift_le_of_pow
    {R : Finset ℕ} {R0 D x p : ℕ}
    (hp : p ≤ x)
    (hprime : ∀ r ∈ R, r.Prime)
    (hlower : ∀ r ∈ R, R0 < r)
    (hpow : x + 1 < (R0 + 1) ^ (D + 1)) :
    (R.filter fun r ↦ r ∣ p + 1).card ≤ D := by
  classical
  let T := R.filter fun r ↦ r ∣ p + 1
  have hprodDiv : (∏ r ∈ T, r) ∣ p + 1 := by
    apply finset_prod_dvd_of_pairwise_coprime_nat T id (p + 1)
    · intro a ha b hb hab
      apply (Nat.coprime_primes
        (hprime a (Finset.mem_filter.mp ha).1)
        (hprime b (Finset.mem_filter.mp hb).1)).2
      simpa only [id_eq] using hab
    intro r hr
    exact (Finset.mem_filter.mp hr).2
  have hpowerProduct : (R0 + 1) ^ T.card ≤ ∏ r ∈ T, r := by
    apply Finset.pow_card_le_prod
    intro r hr
    have hrLower := hlower r (Finset.mem_filter.mp hr).1
    omega
  have hproductShift : (∏ r ∈ T, r) ≤ p + 1 :=
    Nat.le_of_dvd (by omega) hprodDiv
  by_contra hcard
  have hDcard : D + 1 ≤ T.card := by
    dsimp only [T] at hcard ⊢
    omega
  have hpowers : (R0 + 1) ^ (D + 1) ≤ (R0 + 1) ^ T.card :=
    Nat.pow_le_pow_right (by omega) hDcard
  have hxp : p + 1 ≤ x + 1 := Nat.add_le_add_right hp 1
  exact (not_lt_of_ge
    (hpowers.trans (hpowerProduct.trans (hproductShift.trans hxp)))) hpow

/-- If every nonsmooth member of the progression has been represented by
the large-factor parametrization, the usable fibre is contained in the raw
shifted-smooth `q`-fibre. -/
theorem usableAuxiliaryFiber_subset_smoothShiftedFiber
    {x u q r B : ℕ}
    (hdiv : ∀ p ∈ primesInProgression x (q * r) (q * r - 1),
      q ∣ p + 1)
    (hrepresent : ∀ p ∈ primesInProgression x (q * r) (q * r - 1),
      ¬ SmoothAtMost u (p + 1) →
        p ∈ representedLargeFactorPrimes x u q r B) :
    usableAuxiliaryFiber x u q r B ⊆
      (smoothShiftedPrimes x u).filter fun p ↦ q ∣ p + 1 := by
  intro p hp
  have hpData := mem_usableAuxiliaryFiber.mp hp
  rw [Finset.mem_filter, mem_smoothShiftedPrimes]
  refine ⟨⟨(mem_primesInProgression.mp hpData.1).1,
    (mem_primesInProgression.mp hpData.1).2.1, ?_⟩, hdiv p hpData.1⟩
  by_contra hnonsmooth
  exact hpData.2 (hrepresent p hpData.1 hnonsmooth)

/-- Source-shaped specialization of the preceding inclusion.  The
progression itself supplies divisibility by `q`, while nonsmooth shifts are
represented by their extracted large prime factor. -/
theorem usableAuxiliaryFiber_subset_smoothShiftedFiber_of_ranges
    {x u q r B : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hqu : q ≤ u) (hru : r ≤ u)
    (hcofactor : ∀ p ∈ primesInProgression x (q * r) (q * r - 1),
      ∀ s : ℕ, s.Prime → u < s → s ∣ p + 1 →
        (p + 1) / (q * r * s) ≤ B) :
    usableAuxiliaryFiber x u q r B ⊆
      (smoothShiftedPrimes x u).filter fun p ↦ q ∣ p + 1 := by
  apply usableAuxiliaryFiber_subset_smoothShiftedFiber
  · intro p hp
    have hprod : q * r ∣ p + 1 :=
      dvd_add_one_of_mem_primesInProgression (by
        have hfour : 2 * 2 ≤ q * r := Nat.mul_le_mul hq.two_le hr.two_le
        omega) hp
    exact (dvd_mul_right q r).trans hprod
  · intro p hp hnonsmooth
    exact mem_representedLargeFactorPrimes_of_not_smooth hq hr hqu hru hp
      hnonsmooth (hcofactor p hp)

/-- The usable-fibre multiplicity is bounded by the number of auxiliary
prime divisors of the shift, and hence by the preceding product estimate. -/
theorem card_filter_mem_usableAuxiliaryFiber_le_of_pow
    {R : Finset ℕ} {R0 D x u q B p : ℕ}
    (hp : p ≤ x)
    (hq : q.Prime)
    (hprime : ∀ r ∈ R, r.Prime)
    (hlower : ∀ r ∈ R, R0 < r)
    (hpow : x + 1 < (R0 + 1) ^ (D + 1)) :
    (R.filter fun r ↦ p ∈ usableAuxiliaryFiber x u q r B).card ≤ D := by
  apply (Finset.card_le_card ?_).trans
    (card_filter_prime_dvd_shift_le_of_pow hp hprime hlower hpow)
  intro r hr
  have hrData := Finset.mem_filter.mp hr
  rw [Finset.mem_filter]
  refine ⟨hrData.1, ?_⟩
  have hpProg := (mem_usableAuxiliaryFiber.mp hrData.2).1
  have hprod : q * r ∣ p + 1 :=
    dvd_add_one_of_mem_primesInProgression (by
      have hrPrime := hprime r hrData.1
      have hfour : 2 * 2 ≤ q * r :=
        Nat.mul_le_mul hq.two_le hrPrime.two_le
      omega) hpProg
  exact (dvd_mul_left r q).trans (by simpa [Nat.mul_comm] using hprod)

/-- Deleting an arbitrary exception set costs at most its cardinality. -/
theorem card_sub_le_card_usableAuxiliaryFiber
    (x u q r B : ℕ) :
    (primesInProgression x (q * r) (q * r - 1)).card -
        (representedLargeFactorPrimes x u q r B).card ≤
      (usableAuxiliaryFiber x u q r B).card := by
  unfold usableAuxiliaryFiber
  have hinter :
      (primesInProgression x (q * r) (q * r - 1) ∩
        representedLargeFactorPrimes x u q r B).card ≤
          (representedLargeFactorPrimes x u q r B).card :=
    Finset.card_le_card (Finset.inter_subset_right)
  have hdecomp := Finset.card_sdiff_add_card_inter
    (primesInProgression x (q * r) (q * r - 1))
    (representedLargeFactorPrimes x u q r B)
  omega

/-- Double-counting a finite family whose point multiplicities are bounded.
This is the exact inequality used to correct for a shifted prime having
several auxiliary prime divisors. -/
theorem sum_card_le_mul_card_of_bounded_multiplicity
    {I A : Type*} [DecidableEq I] [DecidableEq A]
    (s : Finset I) (U : Finset A) (F : I → Finset A) (D : ℕ)
    (hsub : ∀ i ∈ s, F i ⊆ U)
    (hmult : ∀ a ∈ U, (s.filter fun i ↦ a ∈ F i).card ≤ D) :
    (∑ i ∈ s, (F i).card) ≤ D * U.card := by
  classical
  have hrewrite (i : I) (hi : i ∈ s) :
      (F i).card = ∑ a ∈ U, if a ∈ F i then 1 else 0 := by
    have hfilter : U.filter (fun a ↦ a ∈ F i) = F i := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · exact fun ha ↦ ha.2
      · intro ha
        exact ⟨hsub i hi ha, ha⟩
    calc
      (F i).card = ∑ a ∈ F i, 1 := by simp
      _ = ∑ a ∈ U, if a ∈ F i then 1 else 0 := by
        rw [← Finset.sum_filter, hfilter]
  calc
    (∑ i ∈ s, (F i).card) =
        ∑ i ∈ s, ∑ a ∈ U, if a ∈ F i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrewrite i hi
    _ = ∑ a ∈ U, ∑ i ∈ s, if a ∈ F i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a ∈ U, (s.filter fun i ↦ a ∈ F i).card := by
      apply Finset.sum_congr rfl
      intro a ha
      simp
    _ ≤ ∑ _a ∈ U, D := by
      apply Finset.sum_le_sum
      intro a ha
      exact hmult a ha
    _ = D * U.card := by simp [Nat.mul_comm]

/-- Real-weighted lower-bound form of the auxiliary-prime incidence count.
The pointwise input has the source shape `W/r`; summing it produces the
reciprocal-prime mass without any rounding. -/
theorem mul_sum_inv_le_mul_card_smoothShiftedFiber
    {x u q B D : ℕ} {R : Finset ℕ} {W : ℝ}
    (hsub : ∀ r ∈ R, usableAuxiliaryFiber x u q r B ⊆
      (smoothShiftedPrimes x u).filter fun p ↦ q ∣ p + 1)
    (hmult : ∀ p ∈ (smoothShiftedPrimes x u).filter
        (fun p ↦ q ∣ p + 1),
      (R.filter fun r ↦ p ∈ usableAuxiliaryFiber x u q r B).card ≤ D)
    (hpoint : ∀ r ∈ R,
      W * (r : ℝ)⁻¹ ≤ ((usableAuxiliaryFiber x u q r B).card : ℝ)) :
    W * ∑ r ∈ R, (r : ℝ)⁻¹ ≤
      (D : ℝ) *
        (((smoothShiftedPrimes x u).filter
          fun p ↦ q ∣ p + 1).card : ℝ) := by
  have hsumPoint :
      ∑ r ∈ R, W * (r : ℝ)⁻¹ ≤
        ∑ r ∈ R, ((usableAuxiliaryFiber x u q r B).card : ℝ) := by
    exact Finset.sum_le_sum hpoint
  have hfinite := sum_card_le_mul_card_of_bounded_multiplicity R
    ((smoothShiftedPrimes x u).filter fun p ↦ q ∣ p + 1)
    (fun r ↦ usableAuxiliaryFiber x u q r B) D hsub hmult
  calc
    W * ∑ r ∈ R, (r : ℝ)⁻¹ =
        ∑ r ∈ R, W * (r : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ R,
        ((usableAuxiliaryFiber x u q r B).card : ℝ) := hsumPoint
    _ ≤ (D : ℝ) *
        (((smoothShiftedPrimes x u).filter
          fun p ↦ q ∣ p + 1).card : ℝ) := by
      exact_mod_cast hfinite

/-- Complete finite auxiliary-prime bridge.  A progression lower bound after
paying for the represented large-factor exception is summed over auxiliary
primes; the only loss is the explicit divisor multiplicity `D`. -/
theorem mul_sum_inv_le_mul_card_smoothShiftedFiber_of_progression
    {x u q B D R0 : ℕ} {R : Finset ℕ} {W : ℝ}
    (hW : 0 ≤ W)
    (hq : q.Prime)
    (hprime : ∀ r ∈ R, r.Prime)
    (hqu : q ≤ u)
    (hru : ∀ r ∈ R, r ≤ u)
    (hlower : ∀ r ∈ R, R0 < r)
    (hpow : x + 1 < (R0 + 1) ^ (D + 1))
    (hcofactor : ∀ r ∈ R,
      ∀ p ∈ primesInProgression x (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → u < s → s ∣ p + 1 →
          (p + 1) / (q * r * s) ≤ B)
    (hprogress : ∀ r ∈ R,
      ((representedLargeFactorPrimes x u q r B).card : ℝ) +
          W * (r : ℝ)⁻¹ ≤
        ((primesInProgression x (q * r) (q * r - 1)).card : ℝ)) :
    W * ∑ r ∈ R, (r : ℝ)⁻¹ ≤
      (D : ℝ) *
        (((smoothShiftedPrimes x u).filter
          fun p ↦ q ∣ p + 1).card : ℝ) := by
  apply mul_sum_inv_le_mul_card_smoothShiftedFiber
  · intro r hr
    exact usableAuxiliaryFiber_subset_smoothShiftedFiber_of_ranges
      hq (hprime r hr) hqu (hru r hr) (hcofactor r hr)
  · intro p hp
    exact card_filter_mem_usableAuxiliaryFiber_le_of_pow
      (mem_smoothShiftedPrimes.mp (Finset.mem_filter.mp hp).1).1
      hq hprime hlower hpow
  · intro r hr
    have hprog := hprogress r hr
    have hwterm : 0 ≤ W * (r : ℝ)⁻¹ :=
      mul_nonneg hW (inv_nonneg.mpr (by positivity))
    have hrep :
        (representedLargeFactorPrimes x u q r B).card ≤
          (primesInProgression x (q * r) (q * r - 1)).card := by
      exact_mod_cast (show
        ((representedLargeFactorPrimes x u q r B).card : ℝ) ≤
          ((primesInProgression x (q * r) (q * r - 1)).card : ℝ) by
            linarith)
    have hdelete := card_sub_le_card_usableAuxiliaryFiber x u q r B
    calc
      W * (r : ℝ)⁻¹ ≤
          ((primesInProgression x (q * r) (q * r - 1)).card : ℝ) -
            ((representedLargeFactorPrimes x u q r B).card : ℝ) := by
        linarith
      _ = (((primesInProgression x (q * r) (q * r - 1)).card -
          (representedLargeFactorPrimes x u q r B).card : ℕ) : ℝ) := by
        rw [Nat.cast_sub hrep]
      _ ≤ ((usableAuxiliaryFiber x u q r B).card : ℝ) := by
        exact_mod_cast hdelete

/-- A divisor of a product of two primes is one of the four evident
divisors. -/
theorem dvd_prime_mul_prime_cases
    {d q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hd : d ∣ q * r) :
    d = 1 ∨ d = q ∨ d = r ∨ d = q * r := by
  rcases Nat.dvd_mul.mp hd with ⟨a, b, ha, hb, rfl⟩
  rcases (Nat.dvd_prime hq).mp ha with rfl | rfl <;>
    rcases (Nat.dvd_prime hr).mp hb with rfl | rfl <;> simp

/-- Convert the source endpoint-mass hypotheses and one explicit numerical
budget into the progression-cardinality inequality consumed by the finite
auxiliary-prime bridge. -/
theorem represented_add_weight_le_progression_card_of_endpoint_good
    {x u q r B : ℕ} {W : ℝ}
    (hx : 2 ≤ x)
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hqGood : primitiveEndpointMass x q ≤ (x : ℝ) / 10)
    (hrGood : primitiveEndpointMass x r ≤ (x : ℝ) / 10)
    (hqrGood : primitiveEndpointMass x (q * r) ≤ (x : ℝ) / 10)
    (hnumeric :
      ((representedLargeFactorPrimes x u q r B).card : ℝ) +
          W * (r : ℝ)⁻¹ ≤
        (Chebyshev.theta (x : ℝ) / ((q * r).totient : ℝ) -
          (Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
            ((q * r).totient : ℝ)⁻¹ * (4 * ((x : ℝ) / 10)) +
              (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)))) /
            Real.log (x : ℝ)) :
    ((representedLargeFactorPrimes x u q r B).card : ℝ) +
        W * (r : ℝ)⁻¹ ≤
      ((primesInProgression x (q * r) (q * r - 1)).card : ℝ) := by
  have hgood : ∀ d ∈ (q * r).divisors, d ≠ 1 →
      primitiveEndpointMass x d ≤ (x : ℝ) / 10 := by
    intro d hd hdOne
    rcases dvd_prime_mul_prime_cases hq hr
        (Nat.dvd_of_mem_divisors hd) with rfl | rfl | rfl | rfl
    · exact (hdOne rfl).elim
    · exact hqGood
    · exact hrGood
    · exact hqrGood
  have hcop : (q * r - 1).Coprime (q * r) := by
    rw [Nat.coprime_self_sub_left]
    · simp
    · exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hq.ne_zero hr.ne_zero)
  apply hnumeric.trans
  apply div_log_le_card_primesInProgression hx
  exact thetaProgressionSum_prime_mul_endpoint_lower hx hq hr hqr hcop hgood

/-- End-to-end auxiliary-prime lower bound in the exact form used in the
few-bad-moduli argument.  The analytic work is isolated in the three
endpoint-mass bounds and the displayed numerical budget. -/
theorem mul_sum_inv_le_mul_card_smoothShiftedFiber_of_endpoint_good
    {x u q B D R0 : ℕ} {R : Finset ℕ} {W : ℝ}
    (hx : 2 ≤ x) (hW : 0 ≤ W)
    (hq : q.Prime)
    (hprime : ∀ r ∈ R, r.Prime)
    (hqu : q ≤ u)
    (hqUpper : q ≤ R0)
    (hru : ∀ r ∈ R, r ≤ u)
    (hlower : ∀ r ∈ R, R0 < r)
    (hpow : x + 1 < (R0 + 1) ^ (D + 1))
    (hqGood : primitiveEndpointMass x q ≤ (x : ℝ) / 10)
    (hrGood : ∀ r ∈ R,
      primitiveEndpointMass x r ≤ (x : ℝ) / 10)
    (hqrGood : ∀ r ∈ R,
      primitiveEndpointMass x (q * r) ≤ (x : ℝ) / 10)
    (hcofactor : ∀ r ∈ R,
      ∀ p ∈ primesInProgression x (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → u < s → s ∣ p + 1 →
          (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ r ∈ R,
      ((representedLargeFactorPrimes x u q r B).card : ℝ) +
          W * (r : ℝ)⁻¹ ≤
        (Chebyshev.theta (x : ℝ) / ((q * r).totient : ℝ) -
          (Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
            ((q * r).totient : ℝ)⁻¹ * (4 * ((x : ℝ) / 10)) +
              (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)))) /
            Real.log (x : ℝ)) :
    W * ∑ r ∈ R, (r : ℝ)⁻¹ ≤
      (D : ℝ) *
        (((smoothShiftedPrimes x u).filter
          fun p ↦ q ∣ p + 1).card : ℝ) := by
  apply mul_sum_inv_le_mul_card_smoothShiftedFiber_of_progression
    hW hq hprime hqu hru hlower hpow hcofactor
  intro r hr
  exact represented_add_weight_le_progression_card_of_endpoint_good
    hx hq (hprime r hr) (by
      intro hqr
      subst r
      have hrLower := hlower q hr
      omega) hqGood (hrGood r hr) (hqrGood r hr) (hnumeric r hr)

end

end Erdos48
