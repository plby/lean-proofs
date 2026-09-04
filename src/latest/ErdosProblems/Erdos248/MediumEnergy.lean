import ErdosProblems.Erdos248.PrimeProducts

/-!
# Erdős Problem 248: the two-prime energy at a near coordinate

For a prime below the radius of a near coordinate, forcing divisibility is
represented by a finite difference of the product Selberg cutoff.  This file
records the pointwise one- and two-prime estimates needed for the second
moment argument.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance mediumEnergyDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

theorem radiusProduct_one_le (K : ℕ) : 1 ≤ radiusProduct K := by
  rw [radiusProduct_eq_pow]
  exact Nat.one_le_pow _ _ (by norm_num)

theorem shiftRadius_le_radiusProduct {K : ℕ} (m : nearShifts K) :
    shiftRadius K m ≤ radiusProduct K := by
  unfold radiusProduct
  exact Finset.single_le_prod'
    (fun h _ => shiftRadius_pos K h) m.property

theorem radiusProduct_pow_lt_globalRadius {K e : ℕ} (hK : 0 < K)
    (he : e ≤ 99) :
    radiusProduct K ^ e < globalRadius K := by
  have hpow : radiusProduct K ^ e ≤ radiusProduct K ^ 99 :=
    pow_le_pow_right' (radiusProduct_one_le K) he
  exact hpow.trans_lt (by
    simpa [globalRadius] using radiusProduct_pow_lt_intervalStart hK)

theorem maynardYValue_sieve_eq_coordinateProduct
    {K : ℕ} {r : nearShifts K → ℕ}
    (hr : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K) r) :
    sieveY K r =
      ∏ h : nearShifts K, coordinateCutoff K h (r h) := by
  unfold sieveY maynardYValue
  rw [if_pos ⟨hr.1, hr.2.1, hr.2.2⟩]
  exact tupleCutoff_eq_coordinateProduct K r

theorem isMaynard_base_of_enlarged
    {K R W : ℕ} {r : nearShifts K → ℕ}
    (hmod : preSieveModulus K ∣ W)
    (hr : IsMaynardDivisorTuple (nearShifts K) R W r) :
    IsMaynardDivisorTuple (nearShifts K) R (preSieveModulus K) r := by
  exact ⟨hr.1, hr.2.1.coprime_dvd_right hmod, hr.2.2⟩

theorem insertPrime_isMaynard_base
    {K W p : ℕ} {r : nearShifts K → ℕ}
    (hK : 0 < K) (hp : p.Prime)
    (hpCut : tinyCutoff K < p)
    (hmod : preSieveModulus K * p ∣ W)
    (hr : IsMaynardDivisorTuple (nearShifts K) (globalRadius K) W r)
    (hrBox : r ∈ varyingTupleBox K) (m : nearShifts K)
    (hpRadius : p < shiftRadius K m) :
    IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K) (insertTuplePrime p m r) := by
  have hpProd : Nat.Coprime p (divisorTupleProduct (nearShifts K) r) := by
    have hc : Nat.Coprime (divisorTupleProduct (nearShifts K) r) p :=
      hr.2.1.coprime_dvd_right
        ((dvd_mul_left p (preSieveModulus K)).trans hmod)
    exact hc.symm
  have hprod : divisorTupleProduct (nearShifts K) r ≤ radiusProduct K :=
    varyingTupleBox_product_le_radiusProduct hrBox
  have hpR : p ≤ radiusProduct K :=
    hpRadius.le.trans (shiftRadius_le_radiusProduct m)
  refine ⟨?_, ?_, ?_⟩
  · rw [divisorTupleProduct_insertTuplePrime]
    calc
      p * divisorTupleProduct (nearShifts K) r ≤
          radiusProduct K * radiusProduct K := Nat.mul_le_mul hpR hprod
      _ = radiusProduct K ^ 2 := by ring
      _ < globalRadius K := radiusProduct_pow_lt_globalRadius hK (by norm_num)
  · rw [divisorTupleProduct_insertTuplePrime]
    rw [Nat.coprime_mul_iff_left]
    exact ⟨prime_coprime_preSieveModulus hp hpCut,
      (isMaynard_base_of_enlarged
        (dvd_mul_right (preSieveModulus K) p |>.trans hmod) hr).2.1⟩
  · rw [divisorTupleProduct_insertTuplePrime]
    exact (Nat.squarefree_mul hpProd).2 ⟨hp.squarefree, hr.2.2⟩

theorem varyingTupleBox_of_isMaynard_of_lt
    {K R W : ℕ} {r : nearShifts K → ℕ}
    (hmod : preSieveModulus K ∣ W)
    (hr : IsMaynardDivisorTuple (nearShifts K) R W r)
    (hlt : ∀ h : nearShifts K, r h < shiftRadius K h) :
    r ∈ varyingTupleBox K := by
  rw [varyingTupleBox, Fintype.mem_piFinset]
  intro h
  rw [varyingCoordinateSupport, preSievedCommonCoordinateSupport,
    Finset.mem_filter]
  have hsq := hr.coordinate_squarefree h
  exact ⟨Finset.mem_range.mpr (hlt h), Nat.pos_of_ne_zero hsq.ne_zero,
    hsq, (hr.coordinate_coprime_W h).coprime_dvd_right hmod⟩

/-- Insertion at an arbitrary coordinate only needs a global bound for the
inserted prime; the distinguished coordinate is used later to supply it. -/
theorem insertPrime_isMaynard_base_of_le_radiusProduct
    {K W p : ℕ} {r : nearShifts K → ℕ}
    (hK : 0 < K) (hp : p.Prime) (hpCut : tinyCutoff K < p)
    (hmod : preSieveModulus K * p ∣ W)
    (hr : IsMaynardDivisorTuple (nearShifts K) (globalRadius K) W r)
    (hrBox : r ∈ varyingTupleBox K) (i : nearShifts K)
    (hpR : p ≤ radiusProduct K) :
    IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K) (insertTuplePrime p i r) := by
  have hpProd : Nat.Coprime p (divisorTupleProduct (nearShifts K) r) := by
    have hc : Nat.Coprime (divisorTupleProduct (nearShifts K) r) p :=
      hr.2.1.coprime_dvd_right
        ((dvd_mul_left p (preSieveModulus K)).trans hmod)
    exact hc.symm
  have hprod : divisorTupleProduct (nearShifts K) r ≤ radiusProduct K :=
    varyingTupleBox_product_le_radiusProduct hrBox
  refine ⟨?_, ?_, ?_⟩
  · rw [divisorTupleProduct_insertTuplePrime]
    calc
      p * divisorTupleProduct (nearShifts K) r ≤
          radiusProduct K * radiusProduct K := Nat.mul_le_mul hpR hprod
      _ = radiusProduct K ^ 2 := by ring
      _ < globalRadius K := radiusProduct_pow_lt_globalRadius hK (by norm_num)
  · rw [divisorTupleProduct_insertTuplePrime, Nat.coprime_mul_iff_left]
    exact ⟨prime_coprime_preSieveModulus hp hpCut,
      (isMaynard_base_of_enlarged
        (dvd_mul_right (preSieveModulus K) p |>.trans hmod) hr).2.1⟩
  · rw [divisorTupleProduct_insertTuplePrime]
    exact (Nat.squarefree_mul hpProd).2 ⟨hp.squarefree, hr.2.2⟩

/-- Two distinct inserted primes remain in the base Maynard support. -/
theorem insertTwoPrimes_isMaynard_base
    {K W p q : ℕ} {r : nearShifts K → ℕ}
    (hK : 0 < K) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpCut : tinyCutoff K < p) (hqCut : tinyCutoff K < q)
    (hmod : (preSieveModulus K * p) * q ∣ W)
    (hr : IsMaynardDivisorTuple (nearShifts K) (globalRadius K) W r)
    (hrBox : r ∈ varyingTupleBox K) (i j : nearShifts K)
    (hpR : p ≤ radiusProduct K) (hqR : q ≤ radiusProduct K) :
    IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K)
        (insertTuplePrime q j (insertTuplePrime p i r)) := by
  let d := divisorTupleProduct (nearShifts K) r
  have hpd : Nat.Coprime p d := by
    have hc : Nat.Coprime d p := hr.2.1.coprime_dvd_right
      ((dvd_mul_left p (preSieveModulus K)).trans
        ((dvd_mul_right (preSieveModulus K * p) q).trans hmod))
    exact hc.symm
  have hqd : Nat.Coprime q d := by
    have hc : Nat.Coprime d q := hr.2.1.coprime_dvd_right
      ((dvd_mul_left q (preSieveModulus K * p)).trans hmod)
    exact hc.symm
  have hqp : Nat.Coprime q p :=
    (Nat.coprime_primes hq hp).2 (Ne.symm hpq)
  have hqpd : Nat.Coprime q (p * d) := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨hqp, hqd⟩
  have hdR : d ≤ radiusProduct K :=
    varyingTupleBox_product_le_radiusProduct hrBox
  have hbase := isMaynard_base_of_enlarged
    ((dvd_mul_right (preSieveModulus K) p).trans
      ((dvd_mul_right (preSieveModulus K * p) q).trans hmod)) hr
  refine ⟨?_, ?_, ?_⟩
  · rw [divisorTupleProduct_insertTuplePrime,
      divisorTupleProduct_insertTuplePrime]
    calc
      q * (p * d) ≤ radiusProduct K *
          (radiusProduct K * radiusProduct K) :=
        Nat.mul_le_mul hqR (Nat.mul_le_mul hpR hdR)
      _ = radiusProduct K ^ 3 := by ring
      _ < globalRadius K := radiusProduct_pow_lt_globalRadius hK (by norm_num)
  · rw [divisorTupleProduct_insertTuplePrime,
      divisorTupleProduct_insertTuplePrime, Nat.coprime_mul_iff_left,
      Nat.coprime_mul_iff_left]
    exact ⟨prime_coprime_preSieveModulus hq hqCut,
      prime_coprime_preSieveModulus hp hpCut, hbase.2.1⟩
  · rw [divisorTupleProduct_insertTuplePrime,
      divisorTupleProduct_insertTuplePrime]
    exact (Nat.squarefree_mul hqpd).2 ⟨hq.squarefree,
      (Nat.squarefree_mul hpd).2 ⟨hp.squarefree, hr.2.2⟩⟩

/-- On its enlarged Maynard support, `differencePrimeY` is a distinguished
finite difference plus the insertions in the other coordinates.  This
identity isolates the principal medium-prime term from the cross-coordinate
remainder. -/
theorem differencePrimeY_eq_firstDifference_add_cross
    {H : Finset ℕ} {R W p : ℕ} (hp : p.Prime) (m : H)
    (y : (H → ℕ) → ℝ) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R (W * p) r) :
    differencePrimeY R W p m y r =
      y r - y (insertTuplePrime p m r) +
        ∑ h ∈ (Finset.univ : Finset H).erase m,
          y (insertTuplePrime p h r) / (Nat.totient p : ℝ) := by
  classical
  unfold differencePrimeY
  rw [if_pos hr]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset H)
    (fun h : H => y (insertTuplePrime p h r) / (Nat.totient p : ℝ))
    (Finset.mem_univ m)
  rw [← hsplit]
  rw [Nat.totient_prime hp]
  have hpred : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hpcast : (p : ℝ) = (p - 1 : ℕ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hp.one_le).symm
  rw [hpcast]
  field_simp
  ring

/-- The same decomposition applied to an iterated prime transform. -/
theorem iteratedDifferencePrimeY_eq_firstDifference_add_cross
    {H : Finset ℕ} {R W p q : ℕ} (hq : q.Prime) (m : H)
    (y : (H → ℕ) → ℝ) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R ((W * p) * q) r) :
    differencePrimeY R (W * p) q m (differencePrimeY R W p m y) r =
      differencePrimeY R W p m y r -
          differencePrimeY R W p m y (insertTuplePrime q m r) +
        ∑ h ∈ (Finset.univ : Finset H).erase m,
          differencePrimeY R W p m y (insertTuplePrime q h r) /
            (Nat.totient q : ℝ) := by
  exact differencePrimeY_eq_firstDifference_add_cross hq m
    (differencePrimeY R W p m y) hr

/-- Abstract pointwise bound for the outer step of an iterated prime
transform.  The only remaining input is the distinguished finite difference
of the inner transform; every other coordinate costs `K / φ(q)`. -/
theorem abs_iteratedDifferencePrimeY_le
    {K R W p q : ℕ} (hq : q.Prime) (m : nearShifts K)
    (y : (nearShifts K → ℕ) → ℝ) {r : nearShifts K → ℕ}
    (hr : IsMaynardDivisorTuple (nearShifts K) R ((W * p) * q) r)
    {A B : ℝ} (hB : 0 ≤ B)
    (hdist : |differencePrimeY R W p m y r -
        differencePrimeY R W p m y (insertTuplePrime q m r)| ≤ A)
    (hcross : ∀ h : nearShifts K, h ≠ m →
      |differencePrimeY R W p m y (insertTuplePrime q h r)| ≤ B) :
    |differencePrimeY R (W * p) q m (differencePrimeY R W p m y) r| ≤
      A + (K : ℝ) * B / (q - 1 : ℕ) := by
  rw [iteratedDifferencePrimeY_eq_firstDifference_add_cross hq m y hr]
  have hsum :
      |∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          differencePrimeY R W p m y (insertTuplePrime q h r) /
            (Nat.totient q : ℝ)| ≤
        (K : ℝ) * B / (q - 1 : ℕ) := by
    rw [Nat.totient_prime hq]
    calc
      |∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          differencePrimeY R W p m y (insertTuplePrime q h r) /
            ((q - 1 : ℕ) : ℝ)| ≤
          ∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
            |differencePrimeY R W p m y (insertTuplePrime q h r) /
              ((q - 1 : ℕ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          B / (q - 1 : ℕ) := by
        apply Finset.sum_le_sum
        intro h hh
        have hne : h ≠ m := (Finset.mem_erase.mp hh).1
        rw [abs_div, abs_of_nonneg (by positivity :
          (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ))]
        exact div_le_div_of_nonneg_right (hcross h hne) (by positivity)
      _ ≤ ∑ _h : nearShifts K, B / (q - 1 : ℕ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro h hh hnot
        exact div_nonneg hB (by positivity)
      _ = (K : ℝ) * B / (q - 1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          nearShifts_card]
        simp only [nsmul_eq_mul]
        ring
  calc
    |(differencePrimeY R W p m y r -
          differencePrimeY R W p m y (insertTuplePrime q m r)) +
        ∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          differencePrimeY R W p m y (insertTuplePrime q h r) /
            (Nat.totient q : ℝ)| ≤
      |differencePrimeY R W p m y r -
          differencePrimeY R W p m y (insertTuplePrime q m r)| +
        |∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          differencePrimeY R W p m y (insertTuplePrime q h r) /
            (Nat.totient q : ℝ)| := abs_add_le _ _
    _ ≤ A + (K : ℝ) * B / (q - 1 : ℕ) := add_le_add hdist hsum

/-- A second finite difference of the quadratic cutoff is controlled by the
product of the two increments.  The proof only uses the first-order
Lipschitz estimate, so it remains valid across the corner of the cutoff. -/
theorem sq_selbergCutoff_secondDifference_le
    {a δ ε : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    (selbergCutoff a - selbergCutoff (a + δ) -
        selbergCutoff (a + ε) + selbergCutoff (a + δ + ε)) ^ 2 ≤
      16 * δ * ε := by
  let E := selbergCutoff a - selbergCutoff (a + δ) -
    selbergCutoff (a + ε) + selbergCutoff (a + δ + ε)
  have hEδ : |E| ≤ 4 * δ := by
    have h1 := abs_selbergCutoff_sub_le ha (add_nonneg ha hδ)
    have h2 := abs_selbergCutoff_sub_le (add_nonneg ha hε)
      (add_nonneg (add_nonneg ha hε) hδ)
    have htri : |E| ≤
        |selbergCutoff a - selbergCutoff (a + δ)| +
          |selbergCutoff (a + ε) - selbergCutoff (a + ε + δ)| := by
      rw [show E =
          (selbergCutoff a - selbergCutoff (a + δ)) -
            (selbergCutoff (a + ε) - selbergCutoff (a + ε + δ)) by
        dsimp [E]
        ring_nf]
      exact abs_sub _ _
    calc
      |E| ≤ |selbergCutoff a - selbergCutoff (a + δ)| +
          |selbergCutoff (a + ε) - selbergCutoff (a + ε + δ)| := htri
      _ ≤ 2 * |a - (a + δ)| +
          2 * |(a + ε) - (a + ε + δ)| := add_le_add h1 h2
      _ = 4 * δ := by
        rw [show a - (a + δ) = -δ by ring,
          show a + ε - (a + ε + δ) = -δ by ring,
          abs_neg, abs_of_nonneg hδ]
        ring
  have hEε : |E| ≤ 4 * ε := by
    have h1 := abs_selbergCutoff_sub_le ha (add_nonneg ha hε)
    have h2 := abs_selbergCutoff_sub_le (add_nonneg ha hδ)
      (add_nonneg (add_nonneg ha hδ) hε)
    have htri : |E| ≤
        |selbergCutoff a - selbergCutoff (a + ε)| +
          |selbergCutoff (a + δ) - selbergCutoff (a + δ + ε)| := by
      rw [show E =
          (selbergCutoff a - selbergCutoff (a + ε)) -
            (selbergCutoff (a + δ) - selbergCutoff (a + δ + ε)) by
        dsimp [E]
        ring]
      exact abs_sub _ _
    calc
      |E| ≤ |selbergCutoff a - selbergCutoff (a + ε)| +
          |selbergCutoff (a + δ) - selbergCutoff (a + δ + ε)| := htri
      _ ≤ 2 * |a - (a + ε)| +
          2 * |(a + δ) - (a + δ + ε)| := add_le_add h1 h2
      _ = 4 * ε := by
        rw [show a - (a + ε) = -ε by ring,
          show a + δ - (a + δ + ε) = -ε by ring,
          abs_neg, abs_of_nonneg hε]
        ring
  have hmul : |E| * |E| ≤ (4 * δ) * (4 * ε) :=
    mul_le_mul hEδ hEε (abs_nonneg E) (mul_nonneg (by norm_num) hδ)
  calc
    (selbergCutoff a - selbergCutoff (a + δ) -
        selbergCutoff (a + ε) + selbergCutoff (a + δ + ε)) ^ 2 =
        |E| * |E| := by
          dsimp [E]
          simpa [sq] using (sq_abs
            (selbergCutoff a - selbergCutoff (a + δ) -
              selbergCutoff (a + ε) + selbergCutoff (a + δ + ε))).symm
    _ ≤ (4 * δ) * (4 * ε) := hmul
    _ = 16 * δ * ε := by ring

theorem coordinateCutoff_mul_eq_add
    {K p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (h : nearShifts K) :
    coordinateCutoff K h (p * n) =
      selbergCutoff
        (((100 ^ (h : ℕ) : ℕ) : ℝ) *
            (Real.log n / Real.log (globalRadius K)) +
          primeLogDisplacement K h p) := by
  unfold coordinateCutoff primeLogDisplacement
  rw [Nat.cast_mul,
    Real.log_mul (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hp))
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))]
  ring_nf

theorem sq_coordinateCutoff_secondDifference_le
    {K p q n : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (h : nearShifts K) :
    (coordinateCutoff K h n - coordinateCutoff K h (p * n) -
        coordinateCutoff K h (q * n) +
          coordinateCutoff K h (q * (p * n))) ^ 2 ≤
      16 * primeLogDisplacement K h p * primeLogDisplacement K h q := by
  let a : ℝ := ((100 ^ (h : ℕ) : ℕ) : ℝ) *
    (Real.log n / Real.log (globalRadius K))
  let δ := primeLogDisplacement K h p
  let ε := primeLogDisplacement K h q
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hδ : 0 ≤ δ := primeLogDisplacement_nonneg hp h
  have hε : 0 ≤ ε := primeLogDisplacement_nonneg hq h
  have hpn : 1 ≤ p * n := Nat.mul_pos hp hn
  have hbase : coordinateCutoff K h n = selbergCutoff a := by
    rfl
  have hpbase : coordinateCutoff K h (p * n) = selbergCutoff (a + δ) := by
    simpa [a, δ] using coordinateCutoff_mul_eq_add hp hn h
  have hqbase : coordinateCutoff K h (q * n) = selbergCutoff (a + ε) := by
    simpa [a, ε] using coordinateCutoff_mul_eq_add hq hn h
  have hpqbase :
      coordinateCutoff K h (q * (p * n)) = selbergCutoff (a + δ + ε) := by
    rw [coordinateCutoff_mul_eq_add hq hpn h]
    simp only [a, δ, ε, primeLogDisplacement]
    rw [Nat.cast_mul, Real.log_mul
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hp))
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))]
    congr 1
    ring
  rw [hbase, hpbase, hqbase, hpqbase]
  change (selbergCutoff a - selbergCutoff (a + δ) -
      selbergCutoff (a + ε) + selbergCutoff (a + δ + ε)) ^ 2 ≤
    16 * δ * ε
  exact sq_selbergCutoff_secondDifference_le ha hδ hε

def coordinateProductExcept (K : ℕ) (m : nearShifts K)
    (r : nearShifts K → ℕ) : ℝ :=
  ∏ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
    coordinateCutoff K h (r h)

theorem coordinateProduct_eq_mul_except (K : ℕ) (m : nearShifts K)
    (r : nearShifts K → ℕ) :
    (∏ h : nearShifts K, coordinateCutoff K h (r h)) =
      coordinateCutoff K m (r m) * coordinateProductExcept K m r := by
  symm
  exact Finset.mul_prod_erase Finset.univ
    (fun h : nearShifts K => coordinateCutoff K h (r h))
    (Finset.mem_univ m)

theorem coordinateProductExcept_insert_same (K : ℕ)
    (m : nearShifts K) (p : ℕ) (r : nearShifts K → ℕ) :
    coordinateProductExcept K m (insertTuplePrime p m r) =
      coordinateProductExcept K m r := by
  unfold coordinateProductExcept
  apply Finset.prod_congr rfl
  intro h hh
  rw [Finset.mem_erase] at hh
  rw [insertTuplePrime_apply_ne p hh.1]

theorem coordinateProductExcept_nonneg (K : ℕ) (m : nearShifts K)
    (r : nearShifts K → ℕ) :
    0 ≤ coordinateProductExcept K m r := by
  unfold coordinateProductExcept
  exact Finset.prod_nonneg fun h _ => coordinateCutoff_nonneg K h (r h)

theorem coordinateProductExcept_le_one (K : ℕ) (m : nearShifts K)
    (r : nearShifts K → ℕ) :
    coordinateProductExcept K m r ≤ 1 := by
  unfold coordinateProductExcept
  exact Finset.prod_le_one
    (fun h _ => coordinateCutoff_nonneg K h (r h))
    (fun h _ => coordinateCutoff_le_one K h (r h))

/-- Exact factorization of the first coordinate finite difference. -/
theorem coordinateProduct_firstDifference_eq (K : ℕ)
    (m : nearShifts K) (p : ℕ) (r : nearShifts K → ℕ) :
    (∏ h : nearShifts K, coordinateCutoff K h (r h)) -
        ∏ h : nearShifts K,
          coordinateCutoff K h (insertTuplePrime p m r h) =
      (coordinateCutoff K m (r m) -
          coordinateCutoff K m (p * r m)) *
        coordinateProductExcept K m r := by
  rw [coordinateProduct_eq_mul_except K m r,
    coordinateProduct_eq_mul_except K m (insertTuplePrime p m r),
    coordinateProductExcept_insert_same K m p r]
  simp only [insertTuplePrime_apply_same]
  ring

/-- Pointwise quadratic control of the first coordinate finite difference. -/
theorem sq_coordinateProduct_firstDifference_le
    {K p : ℕ} (hp : 1 ≤ p) (m : nearShifts K)
    {r : nearShifts K → ℕ} (hr : 1 ≤ r m) :
    ((∏ h : nearShifts K, coordinateCutoff K h (r h)) -
        ∏ h : nearShifts K,
          coordinateCutoff K h (insertTuplePrime p m r h)) ^ 2 ≤
      4 * primeLogDisplacement K m p ^ 2 *
        coordinateProductExcept K m r ^ 2 := by
  rw [coordinateProduct_firstDifference_eq]
  have hdiff := coordinateCutoff_mul_sub_le hp hr m
  have hδ := primeLogDisplacement_nonneg hp m
  have hsq :
      (coordinateCutoff K m (r m) -
          coordinateCutoff K m (p * r m)) ^ 2 ≤
        4 * primeLogDisplacement K m p ^ 2 := by
    rw [← sq_abs]
    have := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (by norm_num) hδ)).mpr hdiff
    nlinarith
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- On Maynard-supported tuples, the first finite difference of `sieveY`
is exactly the corresponding coordinate-product difference. -/
theorem sieveY_firstDifference_eq
    {K p : ℕ} (m : nearShifts K) (r : nearShifts K → ℕ)
    (hr : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K) r)
    (hrp : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K) (insertTuplePrime p m r)) :
    sieveY K r - sieveY K (insertTuplePrime p m r) =
      (coordinateCutoff K m (r m) -
          coordinateCutoff K m (p * r m)) *
        coordinateProductExcept K m r := by
  rw [maynardYValue_sieve_eq_coordinateProduct hr,
    maynardYValue_sieve_eq_coordinateProduct hrp]
  exact coordinateProduct_firstDifference_eq K m p r

/-- A medium prime transform of the original cutoff is the principal
Lipschitz difference plus a uniformly small cross-coordinate remainder. -/
theorem abs_differencePrimeY_sieveY_le
    {K p : ℕ} (hK : 0 < K) (hp : p.Prime)
    (hpCut : tinyCutoff K < p) (m : nearShifts K)
    (hpRadius : p < shiftRadius K m) {r : nearShifts K → ℕ}
    (hr : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K * p) r)
    (hrBox : r ∈ varyingTupleBox K) :
    |differencePrimeY (globalRadius K) (preSieveModulus K) p m
        (sieveY K) r| ≤
      2 * primeLogDisplacement K m p +
        (K : ℝ) / (p - 1 : ℕ) := by
  have hrBase : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K) r :=
    isMaynard_base_of_enlarged (dvd_mul_right (preSieveModulus K) p) hr
  have hrp : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K) (insertTuplePrime p m r) :=
    insertPrime_isMaynard_base hK hp hpCut (dvd_refl _) hr hrBox m hpRadius
  rw [differencePrimeY_eq_firstDifference_add_cross hp m (sieveY K) hr]
  have hprincipal :
      |sieveY K r - sieveY K (insertTuplePrime p m r)| ≤
        2 * primeLogDisplacement K m p := by
    rw [sieveY_firstDifference_eq m r hrBase hrp, abs_mul,
      abs_of_nonneg (coordinateProductExcept_nonneg K m r)]
    exact (mul_le_mul
      (coordinateCutoff_mul_sub_le hp.one_le
        (varyingTupleBox_coordinate hrBox m).2.1 m)
      (coordinateProductExcept_le_one K m r)
      (coordinateProductExcept_nonneg K m r)
      (mul_nonneg (by norm_num)
        (primeLogDisplacement_nonneg hp.one_le m))).trans_eq (by ring)
  have hcross :
      |∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          sieveY K (insertTuplePrime p h r) / (Nat.totient p : ℝ)| ≤
        (K : ℝ) / (p - 1 : ℕ) := by
    rw [Nat.totient_prime hp]
    calc
      |∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          sieveY K (insertTuplePrime p h r) / ((p - 1 : ℕ) : ℝ)| ≤
          ∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
            |sieveY K (insertTuplePrime p h r) /
              ((p - 1 : ℕ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          (1 : ℝ) / (p - 1 : ℕ) := by
        apply Finset.sum_le_sum
        intro h hh
        rw [abs_div, abs_of_nonneg (by positivity :
          (0 : ℝ) ≤ ((p - 1 : ℕ) : ℝ))]
        exact div_le_div_of_nonneg_right (abs_sieveY_le_one K _) (by positivity)
      _ ≤ ∑ _h : nearShifts K, (1 : ℝ) / (p - 1 : ℕ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro h hh hnot
        positivity
      _ = (K : ℝ) / (p - 1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          nearShifts_card]
        simp only [nsmul_eq_mul]
        ring
  calc
    |(sieveY K r - sieveY K (insertTuplePrime p m r)) +
        ∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          sieveY K (insertTuplePrime p h r) / (Nat.totient p : ℝ)| ≤
      |sieveY K r - sieveY K (insertTuplePrime p m r)| +
        |∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          sieveY K (insertTuplePrime p h r) /
            (Nat.totient p : ℝ)| := abs_add_le _ _
    _ ≤ 2 * primeLogDisplacement K m p +
        (K : ℝ) / (p - 1 : ℕ) := add_le_add hprincipal hcross

/-- Exact factorization of the mixed two-prime coordinate finite
difference.  This is the algebraic source of the product of logarithmic
displacements in the medium-prime correlation estimate. -/
theorem coordinateProduct_secondDifference_eq (K : ℕ)
    (m : nearShifts K) (p q : ℕ) (r : nearShifts K → ℕ) :
    ((∏ h : nearShifts K, coordinateCutoff K h (r h)) -
          (∏ h : nearShifts K,
            coordinateCutoff K h (insertTuplePrime p m r h)) -
        (∏ h : nearShifts K,
          coordinateCutoff K h (insertTuplePrime q m r h)) +
      ∏ h : nearShifts K,
        coordinateCutoff K h
          (insertTuplePrime q m (insertTuplePrime p m r) h)) =
      (coordinateCutoff K m (r m) -
          coordinateCutoff K m (p * r m) -
          coordinateCutoff K m (q * r m) +
          coordinateCutoff K m (q * (p * r m))) *
        coordinateProductExcept K m r := by
  rw [coordinateProduct_eq_mul_except K m r,
    coordinateProduct_eq_mul_except K m (insertTuplePrime p m r),
    coordinateProduct_eq_mul_except K m (insertTuplePrime q m r),
    coordinateProduct_eq_mul_except K m
      (insertTuplePrime q m (insertTuplePrime p m r)),
    coordinateProductExcept_insert_same K m p r,
    coordinateProductExcept_insert_same K m q r,
    coordinateProductExcept_insert_same K m q (insertTuplePrime p m r),
    coordinateProductExcept_insert_same K m p r]
  simp only [insertTuplePrime_apply_same]
  ring

/-- The sharp pointwise two-prime bound, retaining the cutoff product in
all coordinates other than the distinguished one. -/
theorem sq_coordinateProduct_secondDifference_le
    {K p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (m : nearShifts K) {r : nearShifts K → ℕ} (hr : 1 ≤ r m) :
    ((∏ h : nearShifts K, coordinateCutoff K h (r h)) -
          (∏ h : nearShifts K,
            coordinateCutoff K h (insertTuplePrime p m r h)) -
        (∏ h : nearShifts K,
          coordinateCutoff K h (insertTuplePrime q m r h)) +
      ∏ h : nearShifts K,
        coordinateCutoff K h
          (insertTuplePrime q m (insertTuplePrime p m r) h)) ^ 2 ≤
      16 * primeLogDisplacement K m p * primeLogDisplacement K m q *
        coordinateProductExcept K m r ^ 2 := by
  rw [coordinateProduct_secondDifference_eq]
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right
    (sq_coordinateCutoff_secondDifference_le hp hq hr m) (sq_nonneg _)

/-- On Maynard-supported tuples, the mixed finite difference of `sieveY`
is the exact product finite difference above. -/
theorem sieveY_secondDifference_eq
    {K p q : ℕ} (m : nearShifts K) (r : nearShifts K → ℕ)
    (hr : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K) r)
    (hrp : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K) (insertTuplePrime p m r))
    (hrq : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K) (insertTuplePrime q m r))
    (hrpq : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K)
        (insertTuplePrime q m (insertTuplePrime p m r))) :
    sieveY K r - sieveY K (insertTuplePrime p m r) -
        sieveY K (insertTuplePrime q m r) +
        sieveY K (insertTuplePrime q m (insertTuplePrime p m r)) =
      (coordinateCutoff K m (r m) -
          coordinateCutoff K m (p * r m) -
          coordinateCutoff K m (q * r m) +
          coordinateCutoff K m (q * (p * r m))) *
        coordinateProductExcept K m r := by
  rw [maynardYValue_sieve_eq_coordinateProduct hr,
    maynardYValue_sieve_eq_coordinateProduct hrp,
    maynardYValue_sieve_eq_coordinateProduct hrq,
    maynardYValue_sieve_eq_coordinateProduct hrpq]
  exact coordinateProduct_secondDifference_eq K m p q r

/-- The actual twice-transformed `Y`-variable representing simultaneous
divisibility by `p` and `q` at the near coordinate `m`. -/
def mediumPairTransformY (K : ℕ) (m : nearShifts K) (p q : ℕ) :
    (nearShifts K → ℕ) → ℝ :=
  differencePrimeY (globalRadius K) (preSieveModulus K * p) q m
    (differencePrimeY (globalRadius K) (preSieveModulus K) p m (sieveY K))

theorem mediumPairTransformY_supported (K : ℕ) (m : nearShifts K)
    (p q : ℕ) :
    IsSupportedMaynardY (nearShifts K) (globalRadius K)
      ((preSieveModulus K * p) * q) (mediumPairTransformY K m p q) := by
  exact differencePrimeY_supported _ _ _ _ _

theorem mediumPairTransformY_varyingSupported
    {K p q : ℕ} (hp : 0 < p) (hq : 0 < q) (m : nearShifts K) :
    IsVaryingSupported K (mediumPairTransformY K m p q) := by
  exact differencePrimeY_varyingSupported hq
    (differencePrimeY_varyingSupported hp (sieveY_varyingSupported K) m) m

/-- Concrete pointwise square bound for the actual iterated medium-prime
transform.  The first term is the principal mixed finite difference; the
other two terms are respectively the inner and outer cross-coordinate
remainders. -/
theorem sq_mediumPairTransformY_le
    {K p q : ℕ} (hK : 0 < K) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpCut : tinyCutoff K < p)
    (hqCut : tinyCutoff K < q) (m : nearShifts K)
    (hpRadius : p < shiftRadius K m) (hqRadius : q < shiftRadius K m)
    {r : nearShifts K → ℕ}
    (hr : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      ((preSieveModulus K * p) * q) r)
    (hrBox : r ∈ varyingTupleBox K) :
    mediumPairTransformY K m p q r ^ 2 ≤
      64 * primeLogDisplacement K m p * primeLogDisplacement K m q +
        4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
          (p - 1 : ℕ)) ^ 2 +
        2 * ((K : ℝ) *
          (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
          (q - 1 : ℕ)) ^ 2 := by
  let W := preSieveModulus K
  let y := sieveY K
  let zp := differencePrimeY (globalRadius K) W p m y
  let δp := primeLogDisplacement K m p
  let δq := primeLogDisplacement K m q
  let X := y r - y (insertTuplePrime p m r) -
    y (insertTuplePrime q m r) +
      y (insertTuplePrime q m (insertTuplePrime p m r))
  let Y := ∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
    (y (insertTuplePrime p h r) -
      y (insertTuplePrime q m (insertTuplePrime p h r))) /
        (Nat.totient p : ℝ)
  let Z := ∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
    zp (insertTuplePrime q h r) / (Nat.totient q : ℝ)
  let B := 2 * δp + (K : ℝ) / (p - 1 : ℕ)
  have hpR : p ≤ radiusProduct K :=
    hpRadius.le.trans (shiftRadius_le_radiusProduct m)
  have hqR : q ≤ radiusProduct K :=
    hqRadius.le.trans (shiftRadius_le_radiusProduct m)
  have hWpq : W * p * q = (preSieveModulus K * p) * q := rfl
  have hrW : IsMaynardDivisorTuple (nearShifts K) (globalRadius K) W r :=
    isMaynard_base_of_enlarged
      ((dvd_mul_right W p).trans (dvd_mul_right (W * p) q)) hr
  have hrWp : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (W * p) r :=
    ⟨hr.1, hr.2.1.coprime_dvd_right (dvd_mul_right (W * p) q), hr.2.2⟩
  have hpIns : ∀ i : nearShifts K,
      IsMaynardDivisorTuple (nearShifts K) (globalRadius K) W
        (insertTuplePrime p i r) := fun i =>
    insertPrime_isMaynard_base_of_le_radiusProduct hK hp hpCut
      (dvd_mul_right (W * p) q) hr hrBox i hpR
  have hqDiv : W * q ∣ (W * p) * q := by
    refine ⟨p, ?_⟩
    ring
  have hqIns : ∀ i : nearShifts K,
      IsMaynardDivisorTuple (nearShifts K) (globalRadius K) W
        (insertTuplePrime q i r) := fun i =>
    insertPrime_isMaynard_base_of_le_radiusProduct hK hq hqCut
      hqDiv hr hrBox i hqR
  have hpqIns : ∀ i j : nearShifts K,
      IsMaynardDivisorTuple (nearShifts K) (globalRadius K) W
        (insertTuplePrime q j (insertTuplePrime p i r)) := fun i j =>
    insertTwoPrimes_isMaynard_base hK hp hq hpq hpCut hqCut
      (dvd_refl _) hr hrBox i j hpR hqR
  have hcommSame : insertTuplePrime p m (insertTuplePrime q m r) =
      insertTuplePrime q m (insertTuplePrime p m r) := by
    funext i
    by_cases hi : i = m
    · subst i
      simp only [insertTuplePrime_apply_same]
      ring
    · simp [insertTuplePrime, hi]
  have hcommCross : ∀ i : nearShifts K, i ≠ m →
      insertTuplePrime p i (insertTuplePrime q m r) =
        insertTuplePrime q m (insertTuplePrime p i r) := by
    intro i him
    funext j
    by_cases hji : j = i
    · subst j
      simp [insertTuplePrime, him]
    · by_cases hjm : j = m
      · subst j
        simp [insertTuplePrime, him, Ne.symm him]
      · simp [insertTuplePrime, hji, hjm]
  have hqrWp : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (W * p) (insertTuplePrime q m r) := by
    have hqd : Nat.Coprime q (divisorTupleProduct (nearShifts K) r) := by
      have hc := hr.2.1.coprime_dvd_right
        ((dvd_mul_left q (W * p)).trans (dvd_refl ((W * p) * q)))
      exact hc.symm
    have hqWp : Nat.Coprime q (W * p) := by
      rw [Nat.coprime_mul_iff_right]
      exact ⟨prime_coprime_preSieveModulus hq hqCut,
        (Nat.coprime_primes hq hp).2 (Ne.symm hpq)⟩
    have hrWpCop : Nat.Coprime (divisorTupleProduct (nearShifts K) r)
        (W * p) := hrWp.2.1
    refine ⟨?_, ?_, ?_⟩
    · rw [divisorTupleProduct_insertTuplePrime]
      calc
        q * divisorTupleProduct (nearShifts K) r ≤
            radiusProduct K * radiusProduct K :=
          Nat.mul_le_mul hqR (varyingTupleBox_product_le_radiusProduct hrBox)
        _ = radiusProduct K ^ 2 := by ring
        _ < globalRadius K := radiusProduct_pow_lt_globalRadius hK (by norm_num)
    · rw [divisorTupleProduct_insertTuplePrime,
        Nat.coprime_mul_iff_left]
      exact ⟨hqWp, hrWpCop⟩
    · rw [divisorTupleProduct_insertTuplePrime]
      exact (Nat.squarefree_mul hqd).2 ⟨hq.squarefree, hr.2.2⟩
  have hXeq : X =
      (coordinateCutoff K m (r m) -
          coordinateCutoff K m (p * r m) -
          coordinateCutoff K m (q * r m) +
          coordinateCutoff K m (q * (p * r m))) *
        coordinateProductExcept K m r := by
    dsimp [X, y]
    exact sieveY_secondDifference_eq m r hrW (hpIns m) (hqIns m) (hpqIns m m)
  have hXsq : X ^ 2 ≤ 16 * δp * δq := by
    rw [hXeq, mul_pow]
    have hraw := sq_coordinateCutoff_secondDifference_le
      hp.one_le hq.one_le (varyingTupleBox_coordinate hrBox m).2.1 m
    have hex0 := coordinateProductExcept_nonneg K m r
    have hex1 := coordinateProductExcept_le_one K m r
    have hexsq : coordinateProductExcept K m r ^ 2 ≤ 1 := by nlinarith
    calc
      (coordinateCutoff K m (r m) - coordinateCutoff K m (p * r m) -
          coordinateCutoff K m (q * r m) +
          coordinateCutoff K m (q * (p * r m))) ^ 2 *
          coordinateProductExcept K m r ^ 2 ≤
        (16 * δp * δq) * coordinateProductExcept K m r ^ 2 :=
          mul_le_mul_of_nonneg_right hraw (sq_nonneg _)
      _ ≤ (16 * δp * δq) * 1 := by
        apply mul_le_mul_of_nonneg_left hexsq
        exact mul_nonneg
          (mul_nonneg (by norm_num) (primeLogDisplacement_nonneg hp.one_le m))
          (primeLogDisplacement_nonneg hq.one_le m)
      _ = 16 * δp * δq := by ring
  have hcrossEach : ∀ i : nearShifts K, i ≠ m →
      |y (insertTuplePrime p i r) -
        y (insertTuplePrime q m (insertTuplePrime p i r))| ≤ 2 * δq := by
    intro i him
    rw [sieveY_firstDifference_eq m (insertTuplePrime p i r)
      (hpIns i) (hpqIns i m), abs_mul,
      abs_of_nonneg (coordinateProductExcept_nonneg K m
        (insertTuplePrime p i r))]
    have hcoord : insertTuplePrime p i r m = r m := by
      exact insertTuplePrime_apply_ne p (Ne.symm him) r
    rw [hcoord]
    exact (mul_le_mul
      (coordinateCutoff_mul_sub_le hq.one_le
        (varyingTupleBox_coordinate hrBox m).2.1 m)
      (coordinateProductExcept_le_one K m (insertTuplePrime p i r))
      (coordinateProductExcept_nonneg K m (insertTuplePrime p i r))
      (mul_nonneg (by norm_num)
        (primeLogDisplacement_nonneg hq.one_le m))).trans_eq (by ring)
  have hYabs : |Y| ≤
      2 * (K : ℝ) * δq / (p - 1 : ℕ) := by
    dsimp [Y]
    rw [Nat.totient_prime hp]
    calc
      |∑ i ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          (y (insertTuplePrime p i r) -
            y (insertTuplePrime q m (insertTuplePrime p i r))) /
              ((p - 1 : ℕ) : ℝ)| ≤
          ∑ i ∈ (Finset.univ : Finset (nearShifts K)).erase m,
            |(y (insertTuplePrime p i r) -
              y (insertTuplePrime q m (insertTuplePrime p i r))) /
                ((p - 1 : ℕ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          (2 * δq) / (p - 1 : ℕ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_div, abs_of_nonneg (by positivity :
          (0 : ℝ) ≤ ((p - 1 : ℕ) : ℝ))]
        exact div_le_div_of_nonneg_right
          (hcrossEach i (Finset.mem_erase.mp hi).1) (by positivity)
      _ ≤ ∑ _i : nearShifts K, (2 * δq) / (p - 1 : ℕ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro i hi hnot
        exact div_nonneg
          (mul_nonneg (by norm_num) (primeLogDisplacement_nonneg hq.one_le m))
          (by positivity)
      _ = 2 * (K : ℝ) * δq / (p - 1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          nearShifts_card]
        simp only [nsmul_eq_mul]
        ring
  have hzpCross : ∀ i : nearShifts K, i ≠ m →
      |zp (insertTuplePrime q i r)| ≤ B := by
    intro i him
    by_cases hz : zp (insertTuplePrime q i r) = 0
    · simp [hz, B]
      exact add_nonneg
        (mul_nonneg (by norm_num) (primeLogDisplacement_nonneg hp.one_le m))
        (div_nonneg (by positivity) (by positivity))
    · have hsup : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
          (W * p) (insertTuplePrime q i r) := by
        exact differencePrimeY_supported (globalRadius K) W p m y _ hz
      have hlt : ∀ j : nearShifts K,
          insertTuplePrime q i r j < shiftRadius K j :=
        differencePrimeY_varyingSupported hp.pos (sieveY_varyingSupported K) m hz
      have hbox : insertTuplePrime q i r ∈ varyingTupleBox K :=
        varyingTupleBox_of_isMaynard_of_lt (dvd_mul_right W p) hsup hlt
      simpa [zp, B, δp, W, y] using
        abs_differencePrimeY_sieveY_le hK hp hpCut m hpRadius hsup hbox
  have hZabs : |Z| ≤ (K : ℝ) * B / (q - 1 : ℕ) := by
    dsimp [Z]
    rw [Nat.totient_prime hq]
    calc
      |∑ i ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          zp (insertTuplePrime q i r) / ((q - 1 : ℕ) : ℝ)| ≤
          ∑ i ∈ (Finset.univ : Finset (nearShifts K)).erase m,
            |zp (insertTuplePrime q i r) /
              ((q - 1 : ℕ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          B / (q - 1 : ℕ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_div, abs_of_nonneg (by positivity :
          (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ))]
        exact div_le_div_of_nonneg_right
          (hzpCross i (Finset.mem_erase.mp hi).1) (by positivity)
      _ ≤ ∑ _i : nearShifts K, B / (q - 1 : ℕ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro i hi hnot
        dsimp [B, δp]
        exact div_nonneg
          (add_nonneg
            (mul_nonneg (by norm_num) (primeLogDisplacement_nonneg hp.one_le m))
            (div_nonneg (by positivity) (by positivity)))
          (by positivity)
      _ = (K : ℝ) * B / (q - 1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          nearShifts_card]
        simp only [nsmul_eq_mul]
        ring
  have hinnerEq : zp r - zp (insertTuplePrime q m r) = X + Y := by
    have hsums :
        (∑ i ∈ (nearShifts K).attach.erase m,
            y (insertTuplePrime p i r) / (Nat.totient p : ℝ)) -
          (∑ i ∈ (nearShifts K).attach.erase m,
            y (insertTuplePrime p i (insertTuplePrime q m r)) /
              (Nat.totient p : ℝ)) =
          ∑ i ∈ (nearShifts K).attach.erase m,
            (y (insertTuplePrime p i r) -
              y (insertTuplePrime q m (insertTuplePrime p i r))) /
                (Nat.totient p : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcommCross i (Finset.mem_erase.mp hi).1]
      ring
    dsimp only [zp]
    rw [differencePrimeY_eq_firstDifference_add_cross hp m y hrWp,
      differencePrimeY_eq_firstDifference_add_cross hp m y hqrWp]
    dsimp [X, Y]
    rw [hcommSame]
    linear_combination hsums
  have htotalEq : mediumPairTransformY K m p q r = X + Y + Z := by
    have hout := iteratedDifferencePrimeY_eq_firstDifference_add_cross hq m y hr
    rw [show mediumPairTransformY K m p q r =
        zp r - zp (insertTuplePrime q m r) + Z by
      simpa [mediumPairTransformY, zp, Z, W, y] using hout]
    rw [hinnerEq]
  rw [htotalEq]
  have hXY : (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by
    nlinarith [sq_nonneg (X - Y)]
  have hXYZ : (X + Y + Z) ^ 2 ≤ 2 * (X + Y) ^ 2 + 2 * Z ^ 2 := by
    nlinarith [sq_nonneg (X + Y - Z)]
  have hYsq : Y ^ 2 ≤
      (2 * (K : ℝ) * δq / (p - 1 : ℕ)) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _)
      (by dsimp [δq]
          exact div_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
              (primeLogDisplacement_nonneg hq.one_le m))
            (by positivity) :
        0 ≤ 2 * (K : ℝ) * δq / (p - 1 : ℕ))).mpr hYabs
  have hZsq : Z ^ 2 ≤ ((K : ℝ) * B / (q - 1 : ℕ)) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _)
      (by dsimp [B, δp]
          exact div_nonneg
            (mul_nonneg (by positivity)
              (add_nonneg
                (mul_nonneg (by norm_num)
                  (primeLogDisplacement_nonneg hp.one_le m))
                (div_nonneg (by positivity) (by positivity))))
            (by positivity) :
        0 ≤ (K : ℝ) * B / (q - 1 : ℕ))).mpr hZabs
  dsimp [δp, δq, B] at hXsq hYsq hZsq ⊢
  nlinarith

/-- Energy bound for the actual iterated medium-prime transform. -/
theorem varyingYEnergy_mediumPairTransformY_le
    {K p q : ℕ} (hK : 0 < K) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpCut : tinyCutoff K < p)
    (hqCut : tinyCutoff K < q) (m : nearShifts K)
    (hpRadius : p < shiftRadius K m) (hqRadius : q < shiftRadius K m) :
    varyingYEnergy K (mediumPairTransformY K m p q) ≤
      (64 * primeLogDisplacement K m p * primeLogDisplacement K m q +
        4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
          (p - 1 : ℕ)) ^ 2 +
        2 * ((K : ℝ) *
          (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
          (q - 1 : ℕ)) ^ 2) *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  let C : ℝ :=
    64 * primeLogDisplacement K m p * primeLogDisplacement K m q +
      4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
        (p - 1 : ℕ)) ^ 2 +
      2 * ((K : ℝ) *
        (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
        (q - 1 : ℕ)) ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    have hδp := primeLogDisplacement_nonneg hp.one_le m
    have hδq := primeLogDisplacement_nonneg hq.one_le m
    positivity
  calc
    varyingYEnergy K (mediumPairTransformY K m p q) ≤
        ∑ r ∈ varyingTupleBox K,
          C * reciprocalTotientTupleWeight (nearShifts K) r := by
      unfold varyingYEnergy
      apply Finset.sum_le_sum
      intro r hrBox
      apply mul_le_mul_of_nonneg_right _ (by
        unfold reciprocalTotientTupleWeight
        positivity)
      by_cases hz : mediumPairTransformY K m p q r = 0
      · rw [hz, zero_pow (by norm_num : 2 ≠ 0)]
        exact hC
      · have hr := mediumPairTransformY_supported K m p q r hz
        exact sq_mediumPairTransformY_le hK hp hq hpq hpCut hqCut m
          hpRadius hqRadius hr hrBox
    _ = C * (∑ r ∈ varyingTupleBox K,
        reciprocalTotientTupleWeight (nearShifts K) r) := by
      rw [Finset.mul_sum]
    _ ≤ C * ∏ h : nearShifts K, varyingCoordinateMajorant K h :=
      mul_le_mul_of_nonneg_left (varyingTupleReciprocalWeightSum_le K) hC
    _ = (64 * primeLogDisplacement K m p * primeLogDisplacement K m q +
        4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
          (p - 1 : ℕ)) ^ 2 +
        2 * ((K : ℝ) *
          (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
          (q - 1 : ℕ)) ^ 2) *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := rfl

/-- Normalized form of the actual iterated-transform energy estimate. -/
theorem varyingYEnergy_mediumPairTransformY_le_productEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K p q : ℕ} (hreg : NormalizationRegular A K)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpCut : tinyCutoff K < p) (hqCut : tinyCutoff K < q)
    (m : nearShifts K) (hpRadius : p < shiftRadius K m)
    (hqRadius : q < shiftRadius K m) :
    varyingYEnergy K (mediumPairTransformY K m p q) ≤
      (64 * primeLogDisplacement K m p * primeLogDisplacement K m q +
        4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
          (p - 1 : ℕ)) ^ 2 +
        2 * ((K : ℝ) *
          (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
          (q - 1 : ℕ)) ^ 2) *
        (96 ^ K * productCoordinateEnergy K) := by
  let C : ℝ :=
    64 * primeLogDisplacement K m p * primeLogDisplacement K m q +
      4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
        (p - 1 : ℕ)) ^ 2 +
      2 * ((K : ℝ) *
        (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
        (q - 1 : ℕ)) ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    have hδp := primeLogDisplacement_nonneg hp.one_le m
    have hδq := primeLogDisplacement_nonneg hq.one_le m
    positivity
  calc
    varyingYEnergy K (mediumPairTransformY K m p q) ≤
        C * ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
      simpa [C] using varyingYEnergy_mediumPairTransformY_le
        hreg.1 hp hq hpq hpCut hqCut m hpRadius hqRadius
    _ ≤ C * (96 ^ K * productCoordinateEnergy K) :=
      mul_le_mul_of_nonneg_left (varyingMajorantProduct_le_energy hA hreg) hC
    _ = (64 * primeLogDisplacement K m p * primeLogDisplacement K m q +
        4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
          (p - 1 : ℕ)) ^ 2 +
        2 * ((K : ℝ) *
          (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
          (q - 1 : ℕ)) ^ 2) *
        (96 ^ K * productCoordinateEnergy K) := rfl

/-- The principal first finite-difference `Y`-variable. -/
def mediumPrimeProductY (K : ℕ) (m : nearShifts K) (p : ℕ)
    (r : nearShifts K → ℕ) : ℝ :=
  (∏ h : nearShifts K, coordinateCutoff K h (r h)) -
    ∏ h : nearShifts K,
      coordinateCutoff K h (insertTuplePrime p m r h)

theorem varyingYEnergy_mediumPrimeProductY_le
    {K p : ℕ} (hp : 1 ≤ p) (m : nearShifts K) :
    varyingYEnergy K (mediumPrimeProductY K m p) ≤
      4 * primeLogDisplacement K m p ^ 2 *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  let C : ℝ := 4 * primeLogDisplacement K m p ^ 2
  have hC : 0 ≤ C := by positivity
  unfold varyingYEnergy
  calc
    (∑ r ∈ varyingTupleBox K,
        mediumPrimeProductY K m p r ^ 2 *
          reciprocalTotientTupleWeight (nearShifts K) r) ≤
        ∑ r ∈ varyingTupleBox K,
          C * reciprocalTotientTupleWeight (nearShifts K) r := by
      apply Finset.sum_le_sum
      intro r hrBox
      apply mul_le_mul_of_nonneg_right _ (by
        unfold reciprocalTotientTupleWeight
        positivity)
      calc
        mediumPrimeProductY K m p r ^ 2 ≤
            C * coordinateProductExcept K m r ^ 2 := by
          exact sq_coordinateProduct_firstDifference_le hp m
            (varyingTupleBox_coordinate hrBox m).2.1
        _ ≤ C * 1 := by
          apply mul_le_mul_of_nonneg_left _ hC
          have hnonneg := coordinateProductExcept_nonneg K m r
          have hle := coordinateProductExcept_le_one K m r
          nlinarith [sq_nonneg (coordinateProductExcept K m r)]
        _ = C := by ring
    _ = C * (∑ r ∈ varyingTupleBox K,
        reciprocalTotientTupleWeight (nearShifts K) r) := by
      rw [Finset.mul_sum]
    _ ≤ C * ∏ h : nearShifts K, varyingCoordinateMajorant K h :=
      mul_le_mul_of_nonneg_left (varyingTupleReciprocalWeightSum_le K) hC
    _ = 4 * primeLogDisplacement K m p ^ 2 *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := rfl

/-- The principal mixed two-prime finite-difference `Y`-variable. -/
def mediumPairProductY (K : ℕ) (m : nearShifts K) (p q : ℕ)
    (r : nearShifts K → ℕ) : ℝ :=
  (∏ h : nearShifts K, coordinateCutoff K h (r h)) -
      (∏ h : nearShifts K,
        coordinateCutoff K h (insertTuplePrime p m r h)) -
    (∏ h : nearShifts K,
      coordinateCutoff K h (insertTuplePrime q m r h)) +
    ∏ h : nearShifts K,
      coordinateCutoff K h
        (insertTuplePrime q m (insertTuplePrime p m r) h)

/-- Quadratic energy of the principal mixed finite difference on the sharp
varying box. -/
def mediumPairProductEnergy (K : ℕ) (m : nearShifts K) (p q : ℕ) : ℝ :=
  ∑ r ∈ varyingTupleBox K,
    mediumPairProductY K m p q r ^ 2 *
      reciprocalTotientTupleWeight (nearShifts K) r

theorem mediumPairProductEnergy_nonneg (K : ℕ) (m : nearShifts K)
    (p q : ℕ) :
    0 ≤ mediumPairProductEnergy K m p q := by
  unfold mediumPairProductEnergy reciprocalTotientTupleWeight
  positivity

theorem varyingYEnergy_mediumPairProductY_eq (K : ℕ)
    (m : nearShifts K) (p q : ℕ) :
    varyingYEnergy K (mediumPairProductY K m p q) =
      mediumPairProductEnergy K m p q := by
  rfl

/-- The principal two-prime energy is bounded by the product of the two
normalized logarithmic displacements and the independent coordinate
majorants. -/
theorem mediumPairProductEnergy_le
    {K p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (m : nearShifts K) :
    mediumPairProductEnergy K m p q ≤
      16 * primeLogDisplacement K m p * primeLogDisplacement K m q *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  let C : ℝ :=
    16 * primeLogDisplacement K m p * primeLogDisplacement K m q
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (primeLogDisplacement_nonneg hp m))
      (primeLogDisplacement_nonneg hq m)
  calc
    mediumPairProductEnergy K m p q ≤
        ∑ r ∈ varyingTupleBox K,
          C * reciprocalTotientTupleWeight (nearShifts K) r := by
      unfold mediumPairProductEnergy
      apply Finset.sum_le_sum
      intro r hrBox
      apply mul_le_mul_of_nonneg_right _ (by
        unfold reciprocalTotientTupleWeight
        positivity)
      calc
        mediumPairProductY K m p q r ^ 2 ≤
            C * coordinateProductExcept K m r ^ 2 := by
          exact sq_coordinateProduct_secondDifference_le hp hq m
            (varyingTupleBox_coordinate hrBox m).2.1
        _ ≤ C * 1 := by
          apply mul_le_mul_of_nonneg_left _ hC
          have hnonneg := coordinateProductExcept_nonneg K m r
          have hle := coordinateProductExcept_le_one K m r
          nlinarith [sq_nonneg (coordinateProductExcept K m r)]
        _ = C := by ring
    _ = C * (∑ r ∈ varyingTupleBox K,
        reciprocalTotientTupleWeight (nearShifts K) r) := by
      rw [Finset.mul_sum]
    _ ≤ C * ∏ h : nearShifts K, varyingCoordinateMajorant K h :=
      mul_le_mul_of_nonneg_left (varyingTupleReciprocalWeightSum_le K) hC
    _ = 16 * primeLogDisplacement K m p *
        primeLogDisplacement K m q *
          ∏ h : nearShifts K, varyingCoordinateMajorant K h := rfl

theorem varyingYEnergy_mediumPairProductY_le
    {K p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (m : nearShifts K) :
    varyingYEnergy K (mediumPairProductY K m p q) ≤
      16 * primeLogDisplacement K m p * primeLogDisplacement K m q *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  rw [varyingYEnergy_mediumPairProductY_eq]
  exact mediumPairProductEnergy_le hp hq m

/-- Normalized form of the mixed-energy estimate, replacing the independent
coordinate majorants by the reference Selberg energy. -/
theorem varyingYEnergy_mediumPairProductY_le_productEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K p q : ℕ} (hreg : NormalizationRegular A K)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (m : nearShifts K) :
    varyingYEnergy K (mediumPairProductY K m p q) ≤
      16 * primeLogDisplacement K m p * primeLogDisplacement K m q *
        (96 ^ K * productCoordinateEnergy K) := by
  calc
    varyingYEnergy K (mediumPairProductY K m p q) ≤
        16 * primeLogDisplacement K m p * primeLogDisplacement K m q *
          ∏ h : nearShifts K, varyingCoordinateMajorant K h :=
      varyingYEnergy_mediumPairProductY_le hp hq m
    _ ≤ 16 * primeLogDisplacement K m p *
        primeLogDisplacement K m q *
          (96 ^ K * productCoordinateEnergy K) := by
      apply mul_le_mul_of_nonneg_left (varyingMajorantProduct_le_energy hA hreg)
      exact mul_nonneg
        (mul_nonneg (by norm_num) (primeLogDisplacement_nonneg hp m))
        (primeLogDisplacement_nonneg hq m)

end Erdos248
