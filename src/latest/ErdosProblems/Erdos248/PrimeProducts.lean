import ErdosProblems.Erdos248.TransformedInterval

/-!
# Erdős Problem 248: products of fixed-prime events

This file iterates the one-prime coefficient identities.  The iteration is
finite and exact: the indicator of a product divisibility event is absorbed
into the pre-sieve residue and a successively transformed `Y`-variable.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance primeProductsDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

def fromYWeight {H : Finset ℕ} (R W v : ℕ)
    (y : (H → ℕ) → ℝ) (n : ℕ) : ℝ :=
  preSievedSquareDivisorWeight H (maynardDivisorTupleSupport H R W)
    (maynardCoefficientFromY H R W y) v W n

theorem indicator_separatedPrime_fromYWeight
    {H : Finset ℕ} {R W v p k n : ℕ} {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY H R W y)
    (hk : ∀ h : H, k ≠ h.1)
    (hsep : ∀ h : H, Nat.dist k h.1 < p) :
    (if p ∣ n + k then fromYWeight R W v y n else 0) =
      fromYWeight R (W * p) (extendPrimeEventResidue hpW.symm v k)
        (erasePrimeY R W p y) n := by
  by_cases hnW : n ≡ v [MOD W]
  · by_cases hpn : p ∣ n + k
    · rw [if_pos hpn]
      exact preSievedWeight_on_separated_prime_event_at_residue
        hp hpW hy hnW hpn hk hsep
    · rw [if_neg hpn]
      have hnew : ¬n ≡ extendPrimeEventResidue hpW.symm v k [MOD W * p] := by
        intro hnew
        exact hpn ((modEq_extendPrimeEventResidue_iff hp.pos hpW.symm).mp hnew).2
      simp [fromYWeight, preSievedSquareDivisorWeight, hnew]
  · have hnew : ¬n ≡ extendPrimeEventResidue hpW.symm v k [MOD W * p] := by
      intro hnew
      exact hnW ((modEq_extendPrimeEventResidue_iff hp.pos hpW.symm).mp hnew).1
    simp [fromYWeight, preSievedSquareDivisorWeight, hnW, hnew]

theorem indicator_coordinatePrime_fromYWeight
    {H : Finset ℕ} {R W v p n : ℕ} {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY H R W y) (m : H)
    (hsep : ∀ h : H, h ≠ m → Nat.dist m.1 h.1 < p) :
    (if p ∣ n + m.1 then fromYWeight R W v y n else 0) =
      fromYWeight R (W * p) (extendPrimeEventResidue hpW.symm v m.1)
        (differencePrimeY R W p m y) n := by
  by_cases hnW : n ≡ v [MOD W]
  · by_cases hpn : p ∣ n + m.1
    · rw [if_pos hpn]
      exact preSievedWeight_on_coordinate_prime_event_at_residue
        hp hpW hy m hnW hpn hsep
    · rw [if_neg hpn]
      have hnew :
          ¬n ≡ extendPrimeEventResidue hpW.symm v m.1 [MOD W * p] := by
        intro hnew
        exact hpn ((modEq_extendPrimeEventResidue_iff hp.pos hpW.symm).mp hnew).2
      simp [fromYWeight, preSievedSquareDivisorWeight, hnew]
  · have hnew :
        ¬n ≡ extendPrimeEventResidue hpW.symm v m.1 [MOD W * p] := by
      intro hnew
      exact hnW ((modEq_extendPrimeEventResidue_iff hp.pos hpW.symm).mp hnew).1
    simp [fromYWeight, preSievedSquareDivisorWeight, hnW, hnew]

theorem prime_coprime_preSieveModulus {K p : ℕ}
    (hp : p.Prime) (hcut : tinyCutoff K < p) :
    Nat.Coprime p (preSieveModulus K) := by
  rw [preSieveModulus]
  exact hp.coprime_iff_not_dvd.mpr fun hpd =>
    (not_le_of_gt hcut) (hp.dvd_primorial_iff.mp hpd)

theorem prime_coprime_finset_prod {p : ℕ} {P : Finset ℕ}
    (hp : p.Prime) (hpP : p ∉ P) (hP : ∀ q ∈ P, q.Prime) :
    Nat.Coprime p (∏ q ∈ P, q) := by
  rw [Nat.coprime_prod_right_iff]
  intro q hq
  exact (Nat.coprime_primes hp (hP q hq)).2 fun hpq =>
    hpP (hpq ▸ hq)

theorem prime_coprime_preSieve_mul_prod
    {K p : ℕ} {P : Finset ℕ}
    (hp : p.Prime) (hcut : tinyCutoff K < p)
    (hpP : p ∉ P) (hP : ∀ q ∈ P, q.Prime) :
    Nat.Coprime p (preSieveModulus K * ∏ q ∈ P, q) := by
  rw [Nat.coprime_mul_iff_right]
  exact ⟨prime_coprime_preSieveModulus hp hcut,
    prime_coprime_finset_prod hp hpP hP⟩

/-- Exact finite-product realization for a shift outside the near tuple. -/
theorem exists_separatedPrimeProductTransform
    {K k : ℕ} {P : Finset ℕ}
    (hk : ∀ h : nearShifts K, k ≠ h.1)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p)
    (hPsep : ∀ p ∈ P, ∀ h : nearShifts K, Nat.dist k h.1 < p) :
    ∃ (y : (nearShifts K → ℕ) → ℝ) (v : ℕ),
      IsSupportedMaynardY (nearShifts K) (globalRadius K)
        (preSieveModulus K * ∏ p ∈ P, p) y ∧
      IsVaryingSupported K y ∧
      (∀ r, |y r| ≤ (2 : ℝ) ^ P.card) ∧
      ∀ n,
        (if ∀ p ∈ P, p ∣ n + k then sieveWeight K n else 0) =
          fromYWeight (globalRadius K)
            (preSieveModulus K * ∏ p ∈ P, p) v y n := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      refine ⟨sieveY K, 0, ?_, sieveY_varyingSupported K, ?_, ?_⟩
      · simpa using sieveY_supported K
      · intro r
        simpa using abs_sieveY_le_one K r
      · intro n
        unfold fromYWeight sieveWeight sieveDivisorSupport sieveCoefficient
          sieveY
        rw [show maynardCoefficient (nearShifts K) (globalRadius K)
            (preSieveModulus K) (tupleCutoff K) =
            maynardCoefficientFromY (nearShifts K) (globalRadius K)
              (preSieveModulus K)
              (maynardYValue (nearShifts K) (globalRadius K)
                (preSieveModulus K) (tupleCutoff K)) by
          funext d
          exact maynardCoefficient_eq_fromYValue _ _ _ _ d]
        simp
  | @insert p P hpP ih =>
      have hp := hPprime p (Finset.mem_insert_self p P)
      have hpCut := hPcut p (Finset.mem_insert_self p P)
      have hPprime' : ∀ q ∈ P, q.Prime := fun q hq =>
        hPprime q (Finset.mem_insert_of_mem hq)
      have hPcut' : ∀ q ∈ P, tinyCutoff K < q := fun q hq =>
        hPcut q (Finset.mem_insert_of_mem hq)
      have hPsep' : ∀ q ∈ P, ∀ h : nearShifts K, Nat.dist k h.1 < q :=
        fun q hq => hPsep q (Finset.mem_insert_of_mem hq)
      obtain ⟨y, v, hy, hySharp, hyBound, hpoint⟩ :=
        ih hPprime' hPcut' hPsep'
      have hpW := prime_coprime_preSieve_mul_prod hp hpCut hpP hPprime'
      let z := erasePrimeY (globalRadius K)
        (preSieveModulus K * ∏ q ∈ P, q) p y
      let v' := extendPrimeEventResidue hpW.symm v k
      refine ⟨z, v', ?_, ?_, ?_, ?_⟩
      · simpa [z, Finset.prod_insert hpP, mul_assoc, mul_left_comm,
          mul_comm] using
          erasePrimeY_supported (globalRadius K)
            (preSieveModulus K * ∏ q ∈ P, q) p y
      · exact erasePrimeY_varyingSupported hp.pos hySharp
      · intro r
        have hraw := abs_erasePrimeY_le
          (R := globalRadius K)
          (W := preSieveModulus K * ∏ q ∈ P, q)
          (B := (2 : ℝ) ^ P.card)
          (by positivity) hyBound hp r
        have hfactor :
            (1 : ℝ) + (Fintype.card (nearShifts K) : ℝ) /
              (p - 1 : ℕ) ≤ 2 := by
          rw [Fintype.card_coe, nearShifts_card]
          have hKle : K ≤ p - 1 := by
            exact (K_le_tinyCutoff K).trans (by omega)
          have hden : (0 : ℝ) < (p - 1 : ℕ) := by
            exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
          have hdiv : (K : ℝ) / (p - 1 : ℕ) ≤ 1 := by
            apply (div_le_iff₀ hden).2
            norm_num
            exact_mod_cast hKle
          linarith
        calc
          |z r| ≤ (2 : ℝ) ^ P.card *
              (1 + (Fintype.card (nearShifts K) : ℝ) / (p - 1 : ℕ)) := by
            simpa [z] using hraw
          _ ≤ (2 : ℝ) ^ P.card * 2 :=
            mul_le_mul_of_nonneg_left hfactor (by positivity)
          _ = (2 : ℝ) ^ (Finset.card (insert p P)) := by
            rw [Finset.card_insert_of_notMem hpP, pow_succ]
      · intro n
        have hone := indicator_separatedPrime_fromYWeight
          (R := globalRadius K) hp hpW hy hk
          (hPsep p (Finset.mem_insert_self p P)) (n := n) (v := v)
        have hlogic :
            (∀ q ∈ insert p P, q ∣ n + k) ↔
              p ∣ n + k ∧ ∀ q ∈ P, q ∣ n + k := by simp [hpP]
        rw [show (if ∀ q ∈ insert p P, q ∣ n + k then sieveWeight K n else 0) =
            if p ∣ n + k then
              (if ∀ q ∈ P, q ∣ n + k then sieveWeight K n else 0)
            else 0 by
          by_cases hpn : p ∣ n + k <;>
            simp [hlogic, hpn]]
        rw [hpoint n, hone]
        simpa only [z, v', Finset.prod_insert hpP, mul_assoc, mul_left_comm,
          mul_comm]

/-- Exact finite-product realization at a near coordinate when every event
prime is at least that coordinate's radius.  In this range the forced-prime
transform equals the prime-erasing transform. -/
theorem exists_largeCoordinatePrimeProductTransform
    {K : ℕ} (m : nearShifts K) {P : Finset ℕ}
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p)
    (hPradius : ∀ p ∈ P, shiftRadius K m ≤ p)
    (hPsep : ∀ p ∈ P, ∀ h : nearShifts K,
      h ≠ m → Nat.dist m.1 h.1 < p) :
    ∃ (y : (nearShifts K → ℕ) → ℝ) (v : ℕ),
      IsSupportedMaynardY (nearShifts K) (globalRadius K)
        (preSieveModulus K * ∏ p ∈ P, p) y ∧
      IsVaryingSupported K y ∧
      (∀ r, |y r| ≤ (2 : ℝ) ^ P.card) ∧
      ∀ n,
        (if ∀ p ∈ P, p ∣ n + m.1 then sieveWeight K n else 0) =
          fromYWeight (globalRadius K)
            (preSieveModulus K * ∏ p ∈ P, p) v y n := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      refine ⟨sieveY K, 0, ?_, sieveY_varyingSupported K, ?_, ?_⟩
      · simpa using sieveY_supported K
      · intro r
        simpa using abs_sieveY_le_one K r
      · intro n
        unfold fromYWeight sieveWeight sieveDivisorSupport sieveCoefficient
          sieveY
        rw [show maynardCoefficient (nearShifts K) (globalRadius K)
            (preSieveModulus K) (tupleCutoff K) =
            maynardCoefficientFromY (nearShifts K) (globalRadius K)
              (preSieveModulus K)
              (maynardYValue (nearShifts K) (globalRadius K)
                (preSieveModulus K) (tupleCutoff K)) by
          funext d
          exact maynardCoefficient_eq_fromYValue _ _ _ _ d]
        simp
  | @insert p P hpP ih =>
      have hp := hPprime p (Finset.mem_insert_self p P)
      have hpCut := hPcut p (Finset.mem_insert_self p P)
      have hpRadius := hPradius p (Finset.mem_insert_self p P)
      have hpSep := hPsep p (Finset.mem_insert_self p P)
      have hPprime' : ∀ q ∈ P, q.Prime := fun q hq =>
        hPprime q (Finset.mem_insert_of_mem hq)
      have hPcut' : ∀ q ∈ P, tinyCutoff K < q := fun q hq =>
        hPcut q (Finset.mem_insert_of_mem hq)
      have hPradius' : ∀ q ∈ P, shiftRadius K m ≤ q := fun q hq =>
        hPradius q (Finset.mem_insert_of_mem hq)
      have hPsep' : ∀ q ∈ P, ∀ h : nearShifts K,
          h ≠ m → Nat.dist m.1 h.1 < q :=
        fun q hq => hPsep q (Finset.mem_insert_of_mem hq)
      obtain ⟨y, v, hy, hySharp, hyBound, hpoint⟩ :=
        ih hPprime' hPcut' hPradius' hPsep'
      have hpW := prime_coprime_preSieve_mul_prod hp hpCut hpP hPprime'
      let z := erasePrimeY (globalRadius K)
        (preSieveModulus K * ∏ q ∈ P, q) p y
      let v' := extendPrimeEventResidue hpW.symm v m.1
      refine ⟨z, v', ?_, ?_, ?_, ?_⟩
      · simpa [z, Finset.prod_insert hpP, mul_assoc, mul_left_comm,
          mul_comm] using
          erasePrimeY_supported (globalRadius K)
            (preSieveModulus K * ∏ q ∈ P, q) p y
      · exact erasePrimeY_varyingSupported hp.pos hySharp
      · intro r
        have hraw := abs_erasePrimeY_le
          (R := globalRadius K)
          (W := preSieveModulus K * ∏ q ∈ P, q)
          (B := (2 : ℝ) ^ P.card)
          (by positivity) hyBound hp r
        have hfactor :
            (1 : ℝ) + (Fintype.card (nearShifts K) : ℝ) /
              (p - 1 : ℕ) ≤ 2 := by
          rw [Fintype.card_coe, nearShifts_card]
          have hKle : K ≤ p - 1 :=
            (K_le_tinyCutoff K).trans (by omega)
          have hden : (0 : ℝ) < (p - 1 : ℕ) := by
            exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
          have hdiv : (K : ℝ) / (p - 1 : ℕ) ≤ 1 := by
            apply (div_le_iff₀ hden).2
            norm_num
            exact_mod_cast hKle
          linarith
        calc
          |z r| ≤ (2 : ℝ) ^ P.card *
              (1 + (Fintype.card (nearShifts K) : ℝ) / (p - 1 : ℕ)) := by
            simpa [z] using hraw
          _ ≤ (2 : ℝ) ^ P.card * 2 :=
            mul_le_mul_of_nonneg_left hfactor (by positivity)
          _ = (2 : ℝ) ^ (Finset.card (insert p P)) := by
            rw [Finset.card_insert_of_notMem hpP, pow_succ]
      · intro n
        have hone := indicator_coordinatePrime_fromYWeight
          (R := globalRadius K) hp hpW hy m hpSep (n := n) (v := v)
        have htransform := differencePrimeY_eq_erasePrimeY_of_radius_le
          hy hySharp m hpRadius
        rw [htransform] at hone
        rw [show (if ∀ q ∈ insert p P, q ∣ n + m.1 then
              sieveWeight K n else 0) =
            if p ∣ n + m.1 then
              (if ∀ q ∈ P, q ∣ n + m.1 then sieveWeight K n else 0)
            else 0 by
          by_cases hpn : p ∣ n + m.1 <;> simp [hpn]]
        rw [hpoint n, hone]
        simpa only [z, v', Finset.prod_insert hpP, mul_assoc, mul_left_comm,
          mul_comm]

end Erdos248
