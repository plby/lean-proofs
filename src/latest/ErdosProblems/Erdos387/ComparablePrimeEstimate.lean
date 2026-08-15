/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ComparablePrimeCertificates
import ErdosProblems.Erdos387.PrimeReciprocalBound
import Mathlib.Analysis.PSeries

/-!
# The reciprocal estimate for comparable prime pairs

The two-prime CRT reduction leaves the sum of `1/(q*r)` over primes with
`r < q < gap*r`.  We group both primes into binary logarithmic shells.
Chebyshev gives `O(1/j)` reciprocal mass in shell `j`; comparability leaves
only `O(log₂ gap)` adjacent inner shells, and the remaining outer sum is a
convergent inverse-square tail.
-/

namespace Erdos387

open scoped BigOperators
open Finset Nat Real

namespace CoverBPZ

noncomputable def comparablePrimePairs
    (secondMin gap medium : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Nat.primesLE medium).product (Nat.primesLE medium)).filter
    fun qr => secondMin < qr.2 ∧ qr.2 < qr.1 ∧ qr.1 < gap * qr.2

noncomputable def comparablePrimePairReciprocalSum
    (secondMin gap medium : ℕ) : ℝ :=
  ∑ qr ∈ comparablePrimePairs secondMin gap medium,
    (1 : ℝ) / (qr.1 * qr.2 : ℕ)

theorem sum_comparablePrimeSource_reciprocal_le
    {k secondMin gap medium : ℕ} :
    (∑ s : ComparablePrimeSource k secondMin gap medium,
        (1 : ℝ) / (s.q.val * s.r.val : ℕ)) ≤
      (k : ℝ) ^ 2 *
        comparablePrimePairReciprocalSum secondMin gap medium := by
  classical
  let P := comparablePrimePairs secondMin gap medium
  let T := (Finset.univ : Finset (Fin k)).product
    ((Finset.univ : Finset (Fin k)).product P)
  let encode : ComparablePrimeSource k secondMin gap medium →
      Fin k × (Fin k × (ℕ × ℕ)) :=
    fun s => (s.i, (s.j, (s.q.val, s.r.val)))
  let weight : Fin k × (Fin k × (ℕ × ℕ)) → ℝ :=
    fun x => (1 : ℝ) / (x.2.2.1 * x.2.2.2 : ℕ)
  have henc : Function.Injective encode := by
    intro a b hab
    cases a
    cases b
    simp only [encode, Prod.mk.injEq] at hab
    congr <;> simp_all only [Fin.ext_iff]
  have himage : (Finset.univ.image encode) ⊆ T := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨s, _, rfl⟩ := hx
    dsimp [T, encode]
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp [P]
    rw [comparablePrimePairs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr
      ⟨Nat.mem_primesLE.mpr ⟨s.q_le_medium, s.q_prime⟩,
        Nat.mem_primesLE.mpr ⟨s.r_le_medium, s.r_prime⟩⟩, ?_⟩
    exact ⟨s.second_lt_r, s.r_lt_q, s.q_lt_gap_mul_r⟩
  calc
    (∑ s : ComparablePrimeSource k secondMin gap medium,
        (1 : ℝ) / (s.q.val * s.r.val : ℕ)) =
        ∑ x ∈ Finset.univ.image encode, weight x := by
      simpa [encode, weight] using
        (Finset.sum_image (s := (Finset.univ : Finset
          (ComparablePrimeSource k secondMin gap medium)))
          (f := weight) (g := encode) henc.injOn).symm
    _ ≤ ∑ x ∈ T, weight x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage
        (by intro x _ _; dsimp [weight]; positivity)
    _ = (k : ℝ) ^ 2 *
        comparablePrimePairReciprocalSum secondMin gap medium := by
      change (∑ x ∈ (Finset.univ : Finset (Fin k)).product
          ((Finset.univ : Finset (Fin k)).product P), weight x) = _
      rw [show (∑ x ∈ (Finset.univ : Finset (Fin k)).product
            ((Finset.univ : Finset (Fin k)).product P), weight x) =
          ∑ i ∈ (Finset.univ : Finset (Fin k)),
            ∑ jp ∈ (Finset.univ : Finset (Fin k)).product P,
              weight (i, jp) by
        exact Finset.sum_product _ _ _]
      rw [show (∑ i ∈ (Finset.univ : Finset (Fin k)),
            ∑ jp ∈ (Finset.univ : Finset (Fin k)).product P,
              weight (i, jp)) =
          ∑ i ∈ (Finset.univ : Finset (Fin k)),
            ∑ j ∈ (Finset.univ : Finset (Fin k)),
              ∑ qr ∈ P, weight (i, (j, qr)) by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_product _ _ _]
      dsimp [weight]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      unfold comparablePrimePairReciprocalSum
      dsimp [P]
      push_cast
      ring

theorem comparablePrimePairReciprocalSum_eq_outer
    (secondMin gap medium : ℕ) :
    comparablePrimePairReciprocalSum secondMin gap medium =
      ∑ q ∈ Nat.primesLE medium,
        (1 : ℝ) / q *
          ∑ r ∈ (Nat.primesLE medium).filter (fun r =>
            secondMin < r ∧ r < q ∧ q < gap * r),
            (1 : ℝ) / r := by
  classical
  unfold comparablePrimePairReciprocalSum comparablePrimePairs
  rw [Finset.sum_filter]
  rw [show (∑ a ∈ (Nat.primesLE medium).product (Nat.primesLE medium),
        if secondMin < a.2 ∧ a.2 < a.1 ∧ a.1 < gap * a.2 then
          (1 : ℝ) / (a.1 * a.2 : ℕ) else 0) =
      ∑ q ∈ Nat.primesLE medium, ∑ r ∈ Nat.primesLE medium,
        if secondMin < r ∧ r < q ∧ q < gap * r then
          (1 : ℝ) / (q * r : ℕ) else 0 by
    exact Finset.sum_product _ _ _]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : secondMin < r ∧ r < q ∧ q < gap * r
  · simp only [if_pos h]
    push_cast
    field_simp
  · simp [h]

theorem pairwiseDisjoint_primeLogShell_on (z : ℕ) (J : Finset ℕ) :
    (↑J : Set ℕ).PairwiseDisjoint (PrimeReciprocal.primeLogShell z) := by
  classical
  intro i hi j hj hij
  change Disjoint (PrimeReciprocal.primeLogShell z i)
    (PrimeReciprocal.primeLogShell z j)
  rw [Finset.disjoint_left]
  intro p hpi hpj
  rw [PrimeReciprocal.primeLogShell, Finset.mem_filter] at hpi hpj
  exact hij (hpi.2.symm.trans hpj.2)

theorem sum_primeLogShell_le_harmonicSummand
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {z j : ℕ} (hj : 1 ≤ j) :
    (∑ p ∈ PrimeReciprocal.primeLogShell z j, (1 : ℝ) / p) ≤
      (2 * C / Real.log 2) * (j : ℝ)⁻¹ :=
  (PrimeReciprocal.sum_primeLogShell_le_primeCounting_div_pow z j).trans
    (PrimeReciprocal.primeCounting_pow_div_pow_le_harmonicSummand
      hC hcheb hj)

def admissibleInnerShells (R G jq : ℕ) : Finset ℕ :=
  (Finset.Icc R jq).filter fun jr => jq ≤ jr + G + 1

theorem card_admissibleInnerShells_le (R G jq : ℕ) :
    (admissibleInnerShells R G jq).card ≤ G + 2 := by
  calc
    (admissibleInnerShells R G jq).card ≤
        (Finset.Icc (jq - (G + 1)) jq).card := by
      apply Finset.card_le_card
      intro jr hjr
      rw [admissibleInnerShells, Finset.mem_filter, Finset.mem_Icc] at hjr
      rw [Finset.mem_Icc]
      refine ⟨?_, hjr.1.2⟩
      rw [Nat.sub_le_iff_le_add]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hjr.2
    _ ≤ G + 2 := by simp; omega

theorem comparableInnerPrimes_subset_shellUnion
    {secondMin gap medium R G q : ℕ}
    (hR : 2 ^ R ≤ secondMin) (hG : gap ≤ 2 ^ G) :
    (Nat.primesLE medium).filter (fun r =>
        secondMin < r ∧ r < q ∧ q < gap * r) ⊆
      (admissibleInnerShells R G (Nat.log 2 q)).biUnion
        (PrimeReciprocal.primeLogShell medium) := by
  classical
  intro r hr
  rw [Finset.mem_filter] at hr
  have hrPrime : r.Prime := Nat.prime_of_mem_primesLE hr.1
  have hrPos : r ≠ 0 := hrPrime.ne_zero
  let jr := Nat.log 2 r
  let jq := Nat.log 2 q
  have hRjr : R ≤ jr := by
    apply Nat.le_log_of_pow_le (by norm_num)
    exact hR.trans (Nat.le_of_lt hr.2.1)
  have hjrjq : jr ≤ jq := Nat.log_mono_right (Nat.le_of_lt hr.2.2.1)
  have hrPow : r < 2 ^ (jr + 1) := by
    simpa [jr] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) r
  have hqPow : q < 2 ^ (G + (jr + 1)) := by
    calc
      q < gap * r := hr.2.2.2
      _ ≤ 2 ^ G * r := Nat.mul_le_mul_right r hG
      _ < 2 ^ G * 2 ^ (jr + 1) :=
        (Nat.mul_lt_mul_left (show 0 < 2 ^ G by positivity)).2 hrPow
      _ = 2 ^ (G + (jr + 1)) := (pow_add 2 G (jr + 1)).symm
  have hjq : jq ≤ jr + G + 1 := by
    have hlt := Nat.log_lt_of_lt_pow' (by omega : G + (jr + 1) ≠ 0) hqPow
    omega
  rw [Finset.mem_biUnion]
  refine ⟨jr, ?_, ?_⟩
  · rw [admissibleInnerShells, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hRjr, hjrjq⟩, hjq⟩
  · rw [PrimeReciprocal.primeLogShell, Finset.mem_filter]
    exact ⟨hr.1, rfl⟩

theorem comparableInnerPrimeReciprocalSum_le
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {secondMin gap medium R G q : ℕ}
    (hRone : 1 ≤ R) (hsmall : 2 * (G + 1) ≤ R)
    (hR : 2 ^ R ≤ secondMin) (hG : gap ≤ 2 ^ G)
    (hqR : R ≤ Nat.log 2 q) :
    (∑ r ∈ (Nat.primesLE medium).filter (fun r =>
        secondMin < r ∧ r < q ∧ q < gap * r), (1 : ℝ) / r) ≤
      2 * (2 * C / Real.log 2) * (G + 2 : ℕ) *
        (Nat.log 2 q : ℝ)⁻¹ := by
  classical
  let jq := Nat.log 2 q
  let J := admissibleInnerShells R G jq
  let A : ℝ := 2 * C / Real.log 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hjqPosNat : 0 < jq := hRone.trans hqR
  have hjqPos : (0 : ℝ) < jq := by exact_mod_cast hjqPosNat
  have hsubset :
      (Nat.primesLE medium).filter (fun r =>
          secondMin < r ∧ r < q ∧ q < gap * r) ⊆
        J.biUnion (PrimeReciprocal.primeLogShell medium) := by
    simpa [J, jq] using
      comparableInnerPrimes_subset_shellUnion hR hG
  calc
    (∑ r ∈ (Nat.primesLE medium).filter (fun r =>
        secondMin < r ∧ r < q ∧ q < gap * r), (1 : ℝ) / r) ≤
        ∑ r ∈ J.biUnion (PrimeReciprocal.primeLogShell medium),
          (1 : ℝ) / r :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (by intro r _ _; positivity)
    _ = ∑ jr ∈ J,
        ∑ r ∈ PrimeReciprocal.primeLogShell medium jr,
          (1 : ℝ) / r := by
      rw [Finset.sum_biUnion (pairwiseDisjoint_primeLogShell_on medium J)]
    _ ≤ ∑ jr ∈ J, A * (jr : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro jr hjr
      have hjrData : R ≤ jr ∧ jr ≤ jq ∧ jq ≤ jr + G + 1 := by
        dsimp [J] at hjr
        rw [admissibleInnerShells, Finset.mem_filter,
          Finset.mem_Icc] at hjr
        exact ⟨hjr.1.1, hjr.1.2, hjr.2⟩
      have hjrOne : 1 ≤ jr := hRone.trans hjrData.1
      simpa [A] using
        sum_primeLogShell_le_harmonicSummand hC hcheb hjrOne
    _ ≤ ∑ _jr ∈ J, 2 * A * (jq : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro jr hjr
      have hjrData : R ≤ jr ∧ jr ≤ jq ∧ jq ≤ jr + G + 1 := by
        dsimp [J] at hjr
        rw [admissibleInnerShells, Finset.mem_filter,
          Finset.mem_Icc] at hjr
        exact ⟨hjr.1.1, hjr.1.2, hjr.2⟩
      have hjrPosNat : 0 < jr := hRone.trans hjrData.1
      have hjrPos : (0 : ℝ) < jr := by exact_mod_cast hjrPosNat
      have hjqLe : jq ≤ 2 * jr := by omega
      have hInv : (jr : ℝ)⁻¹ ≤ 2 * (jq : ℝ)⁻¹ := by
        have hhalfPos : (0 : ℝ) < (jq : ℝ) / 2 := by positivity
        have hhalfLe : (jq : ℝ) / 2 ≤ jr := by
          exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
            (by
              have : (jq : ℝ) ≤ 2 * (jr : ℝ) := by exact_mod_cast hjqLe
              simpa [mul_comm] using this)
        calc
          (jr : ℝ)⁻¹ ≤ ((jq : ℝ) / 2)⁻¹ := inv_anti₀ hhalfPos hhalfLe
          _ = 2 * (jq : ℝ)⁻¹ := by field_simp
      calc
        A * (jr : ℝ)⁻¹ ≤ A * (2 * (jq : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hInv hA
        _ = 2 * A * (jq : ℝ)⁻¹ := by ring
    _ = (J.card : ℝ) * (2 * A * (jq : ℝ)⁻¹) := by simp
    _ ≤ (G + 2 : ℕ) * (2 * A * (jq : ℝ)⁻¹) := by
      gcongr
      exact_mod_cast card_admissibleInnerShells_le R G jq
    _ = 2 * (2 * C / Real.log 2) * (G + 2 : ℕ) *
        (Nat.log 2 q : ℝ)⁻¹ := by
      dsimp [A, jq]
      ring

theorem comparablePrimePairReciprocalSum_eq_filteredOuter
    (secondMin gap medium : ℕ) :
    comparablePrimePairReciprocalSum secondMin gap medium =
      ∑ q ∈ (Nat.primesLE medium).filter (secondMin < ·),
        (1 : ℝ) / q *
          ∑ r ∈ (Nat.primesLE medium).filter (fun r =>
            secondMin < r ∧ r < q ∧ q < gap * r),
            (1 : ℝ) / r := by
  classical
  rw [comparablePrimePairReciprocalSum_eq_outer, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hsecondQ : secondMin < q
  · simp only [if_pos hsecondQ]
  · have hempty : (Nat.primesLE medium).filter (fun r =>
        secondMin < r ∧ r < q ∧ q < gap * r) = ∅ := by
      ext r
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      intro hr
      omega
    rw [hempty]
    simp [hsecondQ]

theorem comparableOuterPrimes_subset_shellUnion
    {secondMin medium R Q : ℕ}
    (hR : 2 ^ R ≤ secondMin) (hQ : medium ≤ 2 ^ Q) :
    (Nat.primesLE medium).filter (secondMin < ·) ⊆
      (Finset.Icc R Q).biUnion
        (PrimeReciprocal.primeLogShell medium) := by
  classical
  intro q hq
  rw [Finset.mem_filter] at hq
  have hqPrime : q.Prime := Nat.prime_of_mem_primesLE hq.1
  have hqR : R ≤ Nat.log 2 q := by
    apply Nat.le_log_of_pow_le (by norm_num)
    exact hR.trans (Nat.le_of_lt hq.2)
  have hqQ : Nat.log 2 q ≤ Q := by
    calc
      Nat.log 2 q ≤ Nat.log 2 (2 ^ Q) :=
        Nat.log_mono_right ((Nat.mem_primesLE.mp hq.1).1.trans hQ)
      _ = Q := Nat.log_pow (by norm_num) Q
  rw [Finset.mem_biUnion]
  refine ⟨Nat.log 2 q, Finset.mem_Icc.mpr ⟨hqR, hqQ⟩, ?_⟩
  rw [PrimeReciprocal.primeLogShell, Finset.mem_filter]
  exact ⟨hq.1, rfl⟩

/-- The elementary comparable-prime estimate.  The quotient `(G+2)/R`
is the binary-logarithmic width of the permitted multiplicative interval. -/
theorem comparablePrimePairReciprocalSum_le_shellRatio
    {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {secondMin gap medium R G Q : ℕ}
    (hRone : 1 ≤ R) (hsmall : 2 * (G + 1) ≤ R)
    (hR : 2 ^ R ≤ secondMin) (hG : gap ≤ 2 ^ G)
    (hQ : medium ≤ 2 ^ Q) :
    comparablePrimePairReciprocalSum secondMin gap medium ≤
      4 * (2 * C / Real.log 2) ^ 2 * (G + 2 : ℕ) / R := by
  classical
  let A : ℝ := 2 * C / Real.log 2
  let J := Finset.Icc R Q
  let O := (Nat.primesLE medium).filter (secondMin < ·)
  let inner : ℕ → ℝ := fun q =>
    ∑ r ∈ (Nat.primesLE medium).filter (fun r =>
      secondMin < r ∧ r < q ∧ q < gap * r), (1 : ℝ) / r
  let F : ℕ → ℝ := fun q => (1 : ℝ) / q * inner q
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hO : O ⊆ J.biUnion (PrimeReciprocal.primeLogShell medium) := by
    simpa [O, J] using comparableOuterPrimes_subset_shellUnion hR hQ
  have htail :
      (∑ j ∈ J, (((j : ℝ) ^ 2)⁻¹)) ≤ 2 / (R : ℝ) := by
    have hJ : J = Finset.Ioo (R - 1) (Q + 1) := by
      ext j
      simp only [J, Finset.mem_Icc, Finset.mem_Ioo]
      omega
    rw [hJ]
    have hden : (((R - 1 : ℕ) : ℝ) + 1) = (R : ℝ) := by
      rw [Nat.cast_sub hRone]
      norm_num
    simpa [hden] using (sum_Ioo_inv_sq_le (α := ℝ) (R - 1) (Q + 1))
  rw [comparablePrimePairReciprocalSum_eq_filteredOuter]
  change (∑ q ∈ O, F q) ≤ _
  calc
    (∑ q ∈ O, F q) ≤
        ∑ q ∈ J.biUnion (PrimeReciprocal.primeLogShell medium), F q :=
      Finset.sum_le_sum_of_subset_of_nonneg hO (by
        intro q _ _
        dsimp [F, inner]
        positivity)
    _ = ∑ jq ∈ J,
        ∑ q ∈ PrimeReciprocal.primeLogShell medium jq, F q := by
      rw [Finset.sum_biUnion (pairwiseDisjoint_primeLogShell_on medium J)]
    _ ≤ ∑ jq ∈ J,
        2 * A ^ 2 * (G + 2 : ℕ) * (((jq : ℝ) ^ 2)⁻¹) := by
      apply Finset.sum_le_sum
      intro jq hjq
      have hjqData : R ≤ jq ∧ jq ≤ Q := by
        dsimp [J] at hjq
        exact Finset.mem_Icc.mp hjq
      have hjqOne : 1 ≤ jq := hRone.trans hjqData.1
      have hinner : ∀ q ∈ PrimeReciprocal.primeLogShell medium jq,
          inner q ≤ 2 * A * (G + 2 : ℕ) * (jq : ℝ)⁻¹ := by
        intro q hq
        have hqLog : Nat.log 2 q = jq := by
          rw [PrimeReciprocal.primeLogShell, Finset.mem_filter] at hq
          exact hq.2
        have hqR : R ≤ Nat.log 2 q := by simpa [hqLog] using hjqData.1
        have hi := comparableInnerPrimeReciprocalSum_le hC hcheb
          (medium := medium) hRone hsmall hR hG hqR
        dsimp [inner]
        rw [hqLog] at hi
        simpa [A] using hi
      calc
        (∑ q ∈ PrimeReciprocal.primeLogShell medium jq, F q) ≤
            ∑ q ∈ PrimeReciprocal.primeLogShell medium jq,
              (1 : ℝ) / q *
                (2 * A * (G + 2 : ℕ) * (jq : ℝ)⁻¹) := by
          apply Finset.sum_le_sum
          intro q hq
          dsimp [F]
          exact mul_le_mul_of_nonneg_left (hinner q hq) (by positivity)
        _ = (∑ q ∈ PrimeReciprocal.primeLogShell medium jq,
              (1 : ℝ) / q) *
                (2 * A * (G + 2 : ℕ) * (jq : ℝ)⁻¹) := by
          rw [Finset.sum_mul]
        _ ≤ (A * (jq : ℝ)⁻¹) *
                (2 * A * (G + 2 : ℕ) * (jq : ℝ)⁻¹) := by
          gcongr
          simpa [A] using
            sum_primeLogShell_le_harmonicSummand hC hcheb hjqOne
        _ = 2 * A ^ 2 * (G + 2 : ℕ) * (((jq : ℝ) ^ 2)⁻¹) := by
          rw [← inv_pow]
          ring
    _ = (2 * A ^ 2 * (G + 2 : ℕ)) *
        (∑ jq ∈ J, (((jq : ℝ) ^ 2)⁻¹)) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * A ^ 2 * (G + 2 : ℕ)) * (2 / (R : ℝ)) := by
      gcongr
    _ = 4 * (2 * C / Real.log 2) ^ 2 * (G + 2 : ℕ) / R := by
      dsimp [A]
      ring

/-- Consolidated finite comparable-error bound: one reciprocal prime-pair
term, one source-count term from the CRT endpoints, and the Brun endpoint
remainder. -/
theorem refinedComparablePrimeErrors_card_le_brun_envelope
    {B K X z secondMin gap medium L : ℕ}
    (S : BPZSection6Input B K)
    (hsecond : 2 * S.k ≤ secondMin)
    (hmediumHalf : medium * medium ≤ X / 2)
    (hzSecond : z ≤ secondMin)
    (hX : S.k ≤ X / 2) (hk : 0 < S.k) (hz : 1 ≤ z)
    (hL : Even L)
    (hmainNonneg : 0 ≤
      (refinedBinomialBoundingSieve S X z).mainSum
        (brunUpperWeight L)) :
    ((RefinedComparablePrimeErrors S X z secondMin gap medium).card : ℝ) ≤
      (((X : ℝ) *
            (∑ s : ComparablePrimeSource S.k secondMin gap medium,
              (1 : ℝ) / (s.q.val * s.r.val : ℕ)) +
          2 * Fintype.card
            (ComparablePrimeSource S.k secondMin gap medium)) *
        (refinedBinomialBoundingSieve S X z).mainSum
          (brunUpperWeight L) +
        Fintype.card (ComparablePrimeSource S.k secondMin gap medium) *
          ((4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L)) := by
  classical
  have hbase := refinedComparablePrimeErrors_card_le_primePairBrunSum
    (gap := gap) S hsecond hmediumHalf hzSecond hX hk hz hL hmainNonneg
  let main : ℝ := (refinedBinomialBoundingSieve S X z).mainSum
    (brunUpperWeight L)
  let endpoint : ℝ :=
    (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L
  let Src := ComparablePrimeSource S.k secondMin gap medium
  have hXreal : (0 : ℝ) ≤ X := by positivity
  have hH : ((X - X / 2 : ℕ) : ℝ) ≤ X := by
    exact_mod_cast Nat.sub_le X (X / 2)
  have hMone : (1 : ℝ) ≤ refinementModulus S := by
    exact_mod_cast refinementModulus_pos S
  have hpoint : ∀ s : Src,
      ((((X - X / 2 : ℕ) : ℝ) /
            (refinementModulus S * (s.q.val * s.r.val) : ℕ) + 2) *
          main + endpoint) ≤
        (((X : ℝ) / (s.q.val * s.r.val : ℕ) + 2) * main +
          endpoint) := by
    intro s
    have hqrPosNat : 0 < s.q.val * s.r.val :=
      Nat.mul_pos s.q_prime.pos s.r_prime.pos
    have hqrPos : (0 : ℝ) < (s.q.val * s.r.val : ℕ) := by
      exact_mod_cast hqrPosNat
    have hMqr : ((s.q.val * s.r.val : ℕ) : ℝ) ≤
        (refinementModulus S * (s.q.val * s.r.val) : ℕ) := by
      push_cast
      calc
        (s.q.val : ℝ) * s.r.val =
            1 * ((s.q.val : ℝ) * s.r.val) := by ring
        _ ≤ (refinementModulus S : ℝ) *
            ((s.q.val : ℝ) * s.r.val) :=
          mul_le_mul_of_nonneg_right hMone (by positivity)
    have hdenPos : (0 : ℝ) <
        (refinementModulus S * (s.q.val * s.r.val) : ℕ) := by
      exact_mod_cast Nat.mul_pos (refinementModulus_pos S) hqrPosNat
    have hfrac : ((X - X / 2 : ℕ) : ℝ) /
          (refinementModulus S * (s.q.val * s.r.val) : ℕ) ≤
        (X : ℝ) / (s.q.val * s.r.val : ℕ) := by
      calc
        ((X - X / 2 : ℕ) : ℝ) /
            (refinementModulus S * (s.q.val * s.r.val) : ℕ) ≤
          (X : ℝ) /
            (refinementModulus S * (s.q.val * s.r.val) : ℕ) := by
              exact div_le_div_of_nonneg_right hH hdenPos.le
        _ ≤ (X : ℝ) / (s.q.val * s.r.val : ℕ) := by
          exact div_le_div_of_nonneg_left hXreal hqrPos hMqr
    have hmul := mul_le_mul_of_nonneg_right
      (add_le_add_right hfrac 2) hmainNonneg
    linarith
  refine hbase.trans ?_
  change (∑ s : Src,
      ((((X - X / 2 : ℕ) : ℝ) /
          (refinementModulus S * (s.q.val * s.r.val) : ℕ) + 2) *
        main + endpoint)) ≤ _
  calc
    (∑ s : Src,
      ((((X - X / 2 : ℕ) : ℝ) /
          (refinementModulus S * (s.q.val * s.r.val) : ℕ) + 2) *
        main + endpoint)) ≤
      ∑ s : Src, (((X : ℝ) / (s.q.val * s.r.val : ℕ) + 2) *
        main + endpoint) := Finset.sum_le_sum fun s _ => hpoint s
    _ = (((X : ℝ) *
            (∑ s : Src, (1 : ℝ) / (s.q.val * s.r.val : ℕ)) +
          2 * Fintype.card Src) * main +
        Fintype.card Src * endpoint) := by
      simp_rw [div_eq_mul_inv, add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        show (∑ s : Src,
            (X : ℝ) * (((s.q.val * s.r.val : ℕ) : ℝ)⁻¹) * main) =
          (X : ℝ) * (∑ s : Src,
            (((s.q.val * s.r.val : ℕ) : ℝ)⁻¹)) * main by
            calc
              (∑ s : Src, (X : ℝ) *
                  (((s.q.val * s.r.val : ℕ) : ℝ)⁻¹) * main) =
                  ∑ s : Src, (X : ℝ) *
                    ((((s.q.val * s.r.val : ℕ) : ℝ)⁻¹) * main) := by
                    apply Finset.sum_congr rfl
                    intro s hs
                    ring
              _ = (X : ℝ) * (∑ s : Src,
                    (((s.q.val * s.r.val : ℕ) : ℝ)⁻¹) * main) :=
                (Finset.mul_sum (Finset.univ : Finset Src)
                  (fun s => (((s.q.val * s.r.val : ℕ) : ℝ)⁻¹) * main) X).symm
              _ = (X : ℝ) * ((∑ s : Src,
                    (((s.q.val * s.r.val : ℕ) : ℝ)⁻¹)) * main) := by
                rw [Finset.sum_mul]
              _ = (X : ℝ) * (∑ s : Src,
                    (((s.q.val * s.r.val : ℕ) : ℝ)⁻¹)) * main := by ring]
      simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The same consolidated bound without discarding the density of the
refined progression.  Retaining `refinementModulus S` is essential when this
upper bound is compared with the refined sifted lower bound. -/
theorem refinedComparablePrimeErrors_card_le_brun_envelope_with_modulus
    {B K X z secondMin gap medium L : ℕ}
    (S : BPZSection6Input B K)
    (hsecond : 2 * S.k ≤ secondMin)
    (hmediumHalf : medium * medium ≤ X / 2)
    (hzSecond : z ≤ secondMin)
    (hX : S.k ≤ X / 2) (hk : 0 < S.k) (hz : 1 ≤ z)
    (hL : Even L)
    (hmainNonneg : 0 ≤
      (refinedBinomialBoundingSieve S X z).mainSum
        (brunUpperWeight L)) :
    ((RefinedComparablePrimeErrors S X z secondMin gap medium).card : ℝ) ≤
      ((((X : ℝ) / refinementModulus S) *
            (∑ s : ComparablePrimeSource S.k secondMin gap medium,
              (1 : ℝ) / (s.q.val * s.r.val : ℕ)) +
          2 * Fintype.card
            (ComparablePrimeSource S.k secondMin gap medium)) *
        (refinedBinomialBoundingSieve S X z).mainSum
          (brunUpperWeight L) +
        Fintype.card (ComparablePrimeSource S.k secondMin gap medium) *
          ((4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L)) := by
  classical
  have hbase := refinedComparablePrimeErrors_card_le_primePairBrunSum
    (gap := gap) S hsecond hmediumHalf hzSecond hX hk hz hL hmainNonneg
  let main : ℝ := (refinedBinomialBoundingSieve S X z).mainSum
    (brunUpperWeight L)
  let endpoint : ℝ :=
    (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L
  let Src := ComparablePrimeSource S.k secondMin gap medium
  have hMpos : (0 : ℝ) < refinementModulus S := by
    exact_mod_cast refinementModulus_pos S
  have hXhalf : ((X - X / 2 : ℕ) : ℝ) ≤ X := by
    exact_mod_cast Nat.sub_le X (X / 2)
  have hpoint (s : Src) :
      ((((X - X / 2 : ℕ) : ℝ) /
            (refinementModulus S * (s.q.val * s.r.val) : ℕ) + 2) *
          main + endpoint) ≤
        (((((X : ℝ) / refinementModulus S) /
              (s.q.val * s.r.val : ℕ)) + 2) * main + endpoint) := by
    have hqrNat : 0 < s.q.val * s.r.val :=
      Nat.mul_pos s.q_prime.pos s.r_prime.pos
    have hqr : (0 : ℝ) < (s.q.val * s.r.val : ℕ) := by
      exact_mod_cast hqrNat
    have hden : (0 : ℝ) <
        (refinementModulus S * (s.q.val * s.r.val) : ℕ) := by
      exact_mod_cast Nat.mul_pos (refinementModulus_pos S) hqrNat
    have hfrac : ((X - X / 2 : ℕ) : ℝ) /
          (refinementModulus S * (s.q.val * s.r.val) : ℕ) ≤
        ((X : ℝ) / refinementModulus S) /
          (s.q.val * s.r.val : ℕ) := by
      calc
        ((X - X / 2 : ℕ) : ℝ) /
            (refinementModulus S * (s.q.val * s.r.val) : ℕ) ≤
          (X : ℝ) /
            (refinementModulus S * (s.q.val * s.r.val) : ℕ) :=
          div_le_div_of_nonneg_right hXhalf hden.le
        _ = ((X : ℝ) / refinementModulus S) /
            (s.q.val * s.r.val : ℕ) := by
          push_cast
          field_simp
    have hmul := mul_le_mul_of_nonneg_right
      (add_le_add_right hfrac 2) hmainNonneg
    linarith
  refine hbase.trans ?_
  change (∑ s : Src,
      ((((X - X / 2 : ℕ) : ℝ) /
          (refinementModulus S * (s.q.val * s.r.val) : ℕ) + 2) *
        main + endpoint)) ≤ _
  calc
    (∑ s : Src,
      ((((X - X / 2 : ℕ) : ℝ) /
          (refinementModulus S * (s.q.val * s.r.val) : ℕ) + 2) *
        main + endpoint)) ≤
      ∑ s : Src, (((((X : ℝ) / refinementModulus S) /
          (s.q.val * s.r.val : ℕ)) + 2) * main + endpoint) :=
      Finset.sum_le_sum fun s _ => hpoint s
    _ = ((((X : ℝ) / refinementModulus S) *
            (∑ s : Src, (1 : ℝ) / (s.q.val * s.r.val : ℕ)) +
          2 * Fintype.card Src) * main +
        Fintype.card Src * endpoint) := by
      simp_rw [div_eq_mul_inv, add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        show (∑ s : Src,
            ((X : ℝ) * (refinementModulus S : ℝ)⁻¹) *
                (((s.q.val * s.r.val : ℕ) : ℝ)⁻¹) * main) =
          ((X : ℝ) * (refinementModulus S : ℝ)⁻¹) *
            (∑ s : Src, (((s.q.val * s.r.val : ℕ) : ℝ)⁻¹)) * main by
          calc
            (∑ s : Src,
                ((X : ℝ) * (refinementModulus S : ℝ)⁻¹) *
                  (((s.q.val * s.r.val : ℕ) : ℝ)⁻¹) * main) =
              ∑ s : Src, ((X : ℝ) * (refinementModulus S : ℝ)⁻¹) *
                ((((s.q.val * s.r.val : ℕ) : ℝ)⁻¹) * main) := by
                  apply Finset.sum_congr rfl
                  intro s hs
                  ring
            _ = ((X : ℝ) * (refinementModulus S : ℝ)⁻¹) *
                (∑ s : Src,
                  (((s.q.val * s.r.val : ℕ) : ℝ)⁻¹) * main) := by
              rw [Finset.mul_sum]
            _ = ((X : ℝ) * (refinementModulus S : ℝ)⁻¹) *
                ((∑ s : Src,
                  (((s.q.val * s.r.val : ℕ) : ℝ)⁻¹)) * main) := by
              rw [Finset.sum_mul]
            _ = _ := by ring]
      simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end CoverBPZ

end Erdos387
