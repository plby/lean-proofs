import ErdosProblems.Erdos248.PrimeTransform

/-!
# Erdős Problem 248: fixed-prime correlations

This file turns divisibility events for `n + k` into ordinary pre-sieved
square-divisor weights with enlarged modulus.  The first part is completely
generic: it records the CRT residue, the monotonicity of the shift-difference
coverage condition, and the exact main/error formula for an arbitrary
supported `Y`-variable.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance correlationDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

theorem CoversShiftDifferencePrimes.mono_modulus {H : Finset ℕ}
    {W W' : ℕ} (h : CoversShiftDifferencePrimes H W) (hWW' : W ∣ W') :
    CoversShiftDifferencePrimes H W' := by
  intro a b hab p hp hpd
  exact (h hab p hp hpd).trans hWW'

/-- The exact S1 main term for coefficients obtained from any supported
`Y`-variable.  The library theorem specialized to a cutoff is only a
convenience wrapper around this identity. -/
theorem compatibleDivisorPairMainSum_eq_yDiagonal_sub_incompatible
    {H : Finset ℕ} {R W N : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) :
    compatibleDivisorPairMainSum H (maynardDivisorTupleSupport H R W) W N
        (maynardCoefficientFromY H R W y) =
      (N : ℝ) / W *
        (maynardYDiagonalSum H R W y -
          incompatibleDivisorPairCommonDivisorTupleSum H
            (maynardDivisorTupleSupport H R W)
            (maynardCoefficientFromY H R W y)) := by
  rw [compatibleDivisorPairMainSum_eq_commonDivisorTupleSum
    (fun d hd => isMaynardDivisorTuple_of_mem_support hd)]
  rw [compatibleCommonDivisorTupleSum_eq_yDiagonal_sub_incompatible hy]

/-- Exact interval-counting decomposition for any supported `Y`-variable. -/
theorem sieveWeightSum_fromY_eq_main_add_error
    {H : Finset ℕ} {R W N v : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y)
    (hcoverage : CoversShiftDifferencePrimes H W) :
    sieveWeightSum N
        (preSievedSquareDivisorWeight H
          (maynardDivisorTupleSupport H R W)
          (maynardCoefficientFromY H R W y) v W) =
      (N : ℝ) / W *
          (maynardYDiagonalSum H R W y -
            incompatibleDivisorPairCommonDivisorTupleSum H
              (maynardDivisorTupleSupport H R W)
              (maynardCoefficientFromY H R W y)) +
        compatibleDivisorPairErrorSum H
          (maynardDivisorTupleSupport H R W) v W N
          (maynardCoefficientFromY H R W y) := by
  rw [sieveWeightSum_preSieved_eq_compatibleDivisorPairMainSum_add_error
    (fun d hd => isMaynardDivisorTuple_of_mem_support hd) hcoverage]
  rw [compatibleDivisorPairMainSum_eq_yDiagonal_sub_incompatible hy]

/-- The simultaneous CRT residue for `n ≡ 0 (mod W)` and `p ∣ n+k`. -/
def primeEventResidue {W p : ℕ} (hcop : Nat.Coprime W p) (k : ℕ) : ℕ :=
  Nat.chineseRemainder hcop 0 (negativeShiftResidue p k)

/-- The simultaneous CRT residue extending an arbitrary residue modulo the
current pre-sieve modulus by one prime-divisibility condition. -/
def extendPrimeEventResidue {W p : ℕ} (hcop : Nat.Coprime W p)
    (v k : ℕ) : ℕ :=
  Nat.chineseRemainder hcop v (negativeShiftResidue p k)

theorem modEq_extendPrimeEventResidue_iff {W p v k n : ℕ}
    (hp : 0 < p) (hcop : Nat.Coprime W p) :
    n ≡ extendPrimeEventResidue hcop v k [MOD W * p] ↔
      n ≡ v [MOD W] ∧ p ∣ n + k := by
  constructor
  · intro hn
    have hnW := hn.of_dvd (dvd_mul_right W p)
    have hnp := hn.of_dvd (dvd_mul_left p W)
    have hresW : extendPrimeEventResidue hcop v k ≡ v [MOD W] :=
      (Nat.chineseRemainder hcop v (negativeShiftResidue p k)).property.1
    have hresp : extendPrimeEventResidue hcop v k ≡
        negativeShiftResidue p k [MOD p] :=
      (Nat.chineseRemainder hcop v (negativeShiftResidue p k)).property.2
    exact ⟨hnW.trans hresW,
      (modEq_negativeShiftResidue_iff_dvd_add p k n hp).mp
        (hnp.trans hresp)⟩
  · rintro ⟨hnW, hpk⟩
    have hnp : n ≡ negativeShiftResidue p k [MOD p] :=
      (modEq_negativeShiftResidue_iff_dvd_add p k n hp).mpr hpk
    exact Nat.chineseRemainder_modEq_unique hcop hnW hnp

theorem modEq_primeEventResidue_iff {W p k n : ℕ}
    (hW : 0 < W) (hp : 0 < p) (hcop : Nat.Coprime W p) :
    n ≡ primeEventResidue hcop k [MOD W * p] ↔
      n ≡ 0 [MOD W] ∧ p ∣ n + k := by
  constructor
  · intro hn
    have hWdvd : W ∣ W * p := dvd_mul_right W p
    have hpdvd : p ∣ W * p := dvd_mul_left p W
    have hnW := hn.of_dvd hWdvd
    have hnp := hn.of_dvd hpdvd
    have hresW : primeEventResidue hcop k ≡ 0 [MOD W] :=
      (Nat.chineseRemainder hcop 0 (negativeShiftResidue p k)).property.1
    have hresp : primeEventResidue hcop k ≡
        negativeShiftResidue p k [MOD p] :=
      (Nat.chineseRemainder hcop 0 (negativeShiftResidue p k)).property.2
    exact ⟨hnW.trans hresW,
      (modEq_negativeShiftResidue_iff_dvd_add p k n hp).mp
        (hnp.trans hresp)⟩
  · rintro ⟨hnW, hpk⟩
    have hnp : n ≡ negativeShiftResidue p k [MOD p] :=
      (modEq_negativeShiftResidue_iff_dvd_add p k n hp).mpr hpk
    exact Nat.chineseRemainder_modEq_unique hcop hnW hnp

/-- If a prime divides two translates of `n`, it divides the distance
between the two shifts. -/
theorem prime_dvd_shift_distance {p n a b : ℕ}
    (hpa : p ∣ n + a) (hpb : p ∣ n + b) :
    p ∣ Nat.dist a b := by
  by_cases hab : a ≤ b
  · have hsub : p ∣ (n + b) - (n + a) := Nat.dvd_sub hpb hpa
    rw [Nat.dist_eq_sub_of_le hab]
    simpa [Nat.add_sub_add_left] using hsub
  · have hba : b ≤ a := le_of_not_ge hab
    have hsub : p ∣ (n + a) - (n + b) := Nat.dvd_sub hpa hpb
    rw [Nat.dist_comm a b, Nat.dist_eq_sub_of_le hba]
    simpa [Nat.add_sub_add_left] using hsub

/-- On an event `p ∣ n+k` separated by distance less than `p` from every
sieve coordinate, no divisor tuple satisfying its translate conditions can
contain `p`. -/
theorem not_prime_dvd_tupleProduct_of_event_separated
    {H : Finset ℕ} {R W p n k : ℕ} {d : H → ℕ}
    (hp : p.Prime) (hd : IsMaynardDivisorTuple H R W d)
    (hdn : divisorTupleCondition H n d) (hpn : p ∣ n + k)
    (hk : ∀ h : H, k ≠ h.1)
    (hsep : ∀ h : H, Nat.dist k h.1 < p) :
    ¬p ∣ divisorTupleProduct H d := by
  intro hpProd
  obtain ⟨h, _hh, hph⟩ :=
    Prime.exists_mem_finset_dvd (Nat.prime_iff.mp hp) hpProd
  have hpnh : p ∣ n + h.1 := hph.trans (hdn h)
  have hpdist : p ∣ Nat.dist k h.1 :=
    prime_dvd_shift_distance hpn hpnh
  have hdistPos : 0 < Nat.dist k h.1 := by
    exact Nat.dist_pos_of_ne (hk h)
  have hple : p ≤ Nat.dist k h.1 := Nat.le_of_dvd hdistPos hpdist
  exact (not_le_of_gt (hsep h)) hple

/-- Exact equality of the divisor sums after a separated prime is adjoined
to the modulus. -/
theorem divisorSum_eq_erasePrimeDivisorSum
    {H : Finset ℕ} {R W p n k : ℕ} {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (hy : IsSupportedMaynardY H R W y)
    (hpn : p ∣ n + k) (hk : ∀ h : H, k ≠ h.1)
    (hsep : ∀ h : H, Nat.dist k h.1 < p) :
    (∑ d ∈ (maynardDivisorTupleSupport H R W).filter
        (divisorTupleCondition H n),
        maynardCoefficientFromY H R W y d) =
      ∑ d ∈ (maynardDivisorTupleSupport H R (W * p)).filter
        (divisorTupleCondition H n),
        maynardCoefficientFromY H R (W * p)
          (erasePrimeY R W p y) d := by
  classical
  let D := maynardDivisorTupleSupport H R W
  let Dp := maynardDivisorTupleSupport H R (W * p)
  let P : (H → ℕ) → Prop := fun d => p ∣ divisorTupleProduct H d
  let C : (H → ℕ) → Prop := divisorTupleCondition H n
  have hDp : Dp = D.filter (fun d => ¬P d) := by
    ext d
    simp only [Dp, D, P, Finset.mem_filter]
    exact mem_support_mul_prime_iff hp d
  have hremove :
      (∑ d ∈ D.filter C, maynardCoefficientFromY H R W y d) =
        ∑ d ∈ (D.filter (fun d => ¬P d)).filter C,
          maynardCoefficientFromY H R W y d := by
    symm
    apply Finset.sum_subset
    · intro d hd
      have hdData := Finset.mem_filter.mp hd
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hdData.1).1, hdData.2⟩
    · intro d hdOld hdNot
      have hdData := Finset.mem_filter.mp hdOld
      have hpProd : P d := by
        by_contra hpNot
        exact hdNot (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hdData.1, hpNot⟩, hdData.2⟩)
      have hnot := not_prime_dvd_tupleProduct_of_event_separated hp
        (isMaynardDivisorTuple_of_mem_support hdData.1) hdData.2 hpn hk hsep
      exact False.elim (hnot hpProd)
  rw [hremove, ← hDp]
  apply Finset.sum_congr rfl
  intro d hd
  have hdSupport := (Finset.mem_filter.mp hd).1
  have hpNot : ¬p ∣ divisorTupleProduct H d :=
    (mem_support_mul_prime_iff hp d).mp hdSupport |>.2
  have hpCop : Nat.Coprime p (divisorTupleProduct H d) :=
    hp.coprime_iff_not_dvd.mpr hpNot
  rw [maynardCoefficientFromY_erasePrimeY hp hy d, if_pos hpCop]

/-- Pointwise realization of a separated divisibility event as an ordinary
pre-sieved square-divisor weight at modulus `W*p`. -/
theorem preSievedWeight_on_separated_prime_event
    {H : Finset ℕ} {R W p n k : ℕ} {y : (H → ℕ) → ℝ}
    (hW : 0 < W) (hp : p.Prime) (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY H R W y)
    (hnW : n ≡ 0 [MOD W]) (hpn : p ∣ n + k)
    (hk : ∀ h : H, k ≠ h.1)
    (hsep : ∀ h : H, Nat.dist k h.1 < p) :
    preSievedSquareDivisorWeight H (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) 0 W n =
      preSievedSquareDivisorWeight H
        (maynardDivisorTupleSupport H R (W * p))
        (maynardCoefficientFromY H R (W * p)
          (erasePrimeY R W p y))
        (primeEventResidue hpW.symm k) (W * p) n := by
  have hcrt : n ≡ primeEventResidue hpW.symm k [MOD W * p] :=
    (modEq_primeEventResidue_iff hW hp.pos hpW.symm).mpr ⟨hnW, hpn⟩
  unfold preSievedSquareDivisorWeight
  rw [if_pos hnW, if_pos hcrt]
  unfold squareDivisorWeight
  rw [divisorSum_eq_erasePrimeDivisorSum hp hy hpn hk hsep]

/-- Arbitrary-residue form of `preSievedWeight_on_separated_prime_event`,
used when several distinct primes are adjoined successively. -/
theorem preSievedWeight_on_separated_prime_event_at_residue
    {H : Finset ℕ} {R W p v n k : ℕ} {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY H R W y)
    (hnW : n ≡ v [MOD W]) (hpn : p ∣ n + k)
    (hk : ∀ h : H, k ≠ h.1)
    (hsep : ∀ h : H, Nat.dist k h.1 < p) :
    preSievedSquareDivisorWeight H (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) v W n =
      preSievedSquareDivisorWeight H
        (maynardDivisorTupleSupport H R (W * p))
        (maynardCoefficientFromY H R (W * p)
          (erasePrimeY R W p y))
        (extendPrimeEventResidue hpW.symm v k) (W * p) n := by
  have hcrt : n ≡ extendPrimeEventResidue hpW.symm v k [MOD W * p] :=
    (modEq_extendPrimeEventResidue_iff hp.pos hpW.symm).mpr ⟨hnW, hpn⟩
  unfold preSievedSquareDivisorWeight
  rw [if_pos hnW, if_pos hcrt]
  unfold squareDivisorWeight
  rw [divisorSum_eq_erasePrimeDivisorSum hp hy hpn hk hsep]

/-- Inserting the event prime in its distinguished coordinate preserves the
divisor-tuple condition, provided the original tuple is `p`-free. -/
theorem divisorTupleCondition_insert_event_prime_iff
    {H : Finset ℕ} {p n : ℕ} {d : H → ℕ} (hp : p.Prime)
    (m : H) (hpcop : Nat.Coprime p (divisorTupleProduct H d))
    (hpn : p ∣ n + m.1) :
    divisorTupleCondition H n (insertTuplePrime p m d) ↔
      divisorTupleCondition H n d := by
  constructor
  · intro hins h
    by_cases hh : h = m
    · subst h
      have hdiv := hins m
      exact (dvd_mul_left (d m) p).trans (by simpa using hdiv)
    · simpa [insertTuplePrime, hh] using hins h
  · intro hd h
    by_cases hh : h = m
    · subst h
      have hcopCoord : Nat.Coprime p (d m) :=
        hpcop.coprime_dvd_right (divisorTupleCoordinate_dvd_product d m)
      have hmul : p * d m ∣ n + m.1 :=
        hcopCoord.mul_dvd_of_dvd_of_dvd hpn (hd m)
      simpa using hmul
    · simpa [insertTuplePrime, hh] using hd h

/-- Under a prime event at one sieve coordinate and separation from every
other coordinate, an admissible divisor tuple containing `p` contains it at
that distinguished coordinate. -/
theorem prime_dvd_distinguished_coordinate_of_event
    {H : Finset ℕ} {R W p n : ℕ} {d : H → ℕ}
    (hp : p.Prime) (hd : IsMaynardDivisorTuple H R W d)
    (hdn : divisorTupleCondition H n d) (m : H)
    (hpn : p ∣ n + m.1)
    (hsep : ∀ h : H, h ≠ m → Nat.dist m.1 h.1 < p)
    (hpProd : p ∣ divisorTupleProduct H d) :
    p ∣ d m := by
  obtain ⟨h, _hh, hph⟩ :=
    Prime.exists_mem_finset_dvd (Nat.prime_iff.mp hp) hpProd
  have heq : h = m := by
    by_contra hne
    have hpnh : p ∣ n + h.1 := hph.trans (hdn h)
    have hpdist : p ∣ Nat.dist m.1 h.1 :=
      prime_dvd_shift_distance hpn hpnh
    have hdistPos : 0 < Nat.dist m.1 h.1 :=
      Nat.dist_pos_of_ne (fun he => hne (Subtype.ext he.symm))
    have hple : p ≤ Nat.dist m.1 h.1 := Nat.le_of_dvd hdistPos hpdist
    exact (not_le_of_gt (hsep h hne)) hple
  simpa [heq] using hph

/-- A coefficient with `p` inserted beyond the old Maynard support vanishes.
The hypotheses ensure that the only possible support failure is the common
product-radius bound. -/
theorem coefficient_insertPrime_eq_zero_of_not_mem_support
    {H : Finset ℕ} {R W p : ℕ} {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY H R W y) {d : H → ℕ}
    (hd : d ∈ maynardDivisorTupleSupport H R (W * p)) (m : H)
    (hnot : insertTuplePrime p m d ∉
      maynardDivisorTupleSupport H R W) :
    maynardCoefficientFromY H R W y (insertTuplePrime p m d) = 0 := by
  have hdMaynard := isMaynardDivisorTuple_of_mem_support hd
  have hpCop : Nat.Coprime p (divisorTupleProduct H d) := by
    have hprodP : Nat.Coprime (divisorTupleProduct H d) p :=
      hdMaynard.2.1.coprime_dvd_right (dvd_mul_left p W)
    exact hprodP.symm
  have hinsCop : Nat.Coprime
      (divisorTupleProduct H (insertTuplePrime p m d)) W := by
    rw [divisorTupleProduct_insertTuplePrime]
    exact hpW.mul_left
      (hdMaynard.2.1.coprime_dvd_right (dvd_mul_right W p))
  have hinsSq : Squarefree
      (divisorTupleProduct H (insertTuplePrime p m d)) := by
    rw [divisorTupleProduct_insertTuplePrime]
    exact (Nat.squarefree_mul hpCop).mpr ⟨hp.squarefree, hdMaynard.2.2⟩
  have hRle : R ≤ divisorTupleProduct H (insertTuplePrime p m d) := by
    by_contra hlt
    have hinsMaynard : IsMaynardDivisorTuple H R W
        (insertTuplePrime p m d) :=
      ⟨Nat.lt_of_not_ge hlt, hinsCop, hinsSq⟩
    exact hnot (mem_maynardDivisorTupleSupport_iff.mpr
      ⟨hinsMaynard.mem_maynardDivisorTupleBox, hinsMaynard⟩)
  rw [maynardCoefficientFromY_eq_coreSum hy]
  rw [if_pos hinsCop]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro r hr
  unfold inverseYTerm
  by_cases hdiv : tupleDvd (insertTuplePrime p m d) r
  · rw [if_pos hdiv]
    have hprodDvd : divisorTupleProduct H (insertTuplePrime p m d) ∣
        divisorTupleProduct H r := by
      unfold divisorTupleProduct
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun h _ => hdiv h)
    have hrMaynard := isMaynardDivisorTuple_of_mem_support hr
    have hprodPos : 0 < divisorTupleProduct H r :=
      Nat.pos_of_ne_zero hrMaynard.2.2.ne_zero
    have hle : divisorTupleProduct H (insertTuplePrime p m d) ≤
        divisorTupleProduct H r := Nat.le_of_dvd hprodPos hprodDvd
    exact False.elim (not_lt_of_ge (hRle.trans hle) hrMaynard.1)
  · rw [if_neg hdiv]

/-- Exact equality of divisor sums when the prime is forced at one of the
sieve coordinates. -/
theorem divisorSum_eq_differencePrimeDivisorSum
    {H : Finset ℕ} {R W p n : ℕ} {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY H R W y) (m : H)
    (hpn : p ∣ n + m.1)
    (hsep : ∀ h : H, h ≠ m → Nat.dist m.1 h.1 < p) :
    (∑ d ∈ (maynardDivisorTupleSupport H R W).filter
        (divisorTupleCondition H n),
        maynardCoefficientFromY H R W y d) =
      ∑ d ∈ (maynardDivisorTupleSupport H R (W * p)).filter
        (divisorTupleCondition H n),
        maynardCoefficientFromY H R (W * p)
          (differencePrimeY R W p m y) d := by
  classical
  let D := maynardDivisorTupleSupport H R W
  let Dp := maynardDivisorTupleSupport H R (W * p)
  let P : (H → ℕ) → Prop := fun d => p ∣ divisorTupleProduct H d
  let Q : (H → ℕ) → Prop := fun d => p ∣ d m
  let C : (H → ℕ) → Prop := divisorTupleCondition H n
  let L : (H → ℕ) → ℝ := maynardCoefficientFromY H R W y
  let f : (H → ℕ) → ℝ := fun d => if C d then L d else 0
  have hDp : Dp = D.filter (fun d => ¬P d) := by
    ext d
    simp only [Dp, D, P, Finset.mem_filter]
    exact mem_support_mul_prime_iff hp d
  have hQP : D.filter Q ⊆ D.filter P := by
    intro d hd
    have hdData := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨hdData.1,
      hdData.2.trans (divisorTupleCoordinate_dvd_product d m)⟩
  have hPQ :
      (∑ d ∈ D.filter P, f d) = ∑ d ∈ D.filter Q, f d := by
    symm
    apply Finset.sum_subset hQP
    intro d hdP hdNotQ
    have hdData := Finset.mem_filter.mp hdP
    have hnQ : ¬Q d := by
      intro hq
      exact hdNotQ (Finset.mem_filter.mpr ⟨hdData.1, hq⟩)
    have hnC : ¬C d := by
      intro hc
      exact hnQ (prime_dvd_distinguished_coordinate_of_event hp
        (isMaynardDivisorTuple_of_mem_support hdData.1) hc m hpn hsep
        hdData.2)
    simp [f, hnC]
  have hpartition :
      (∑ d ∈ D, f d) =
        (∑ d ∈ D.filter (fun d => ¬P d), f d) +
          ∑ d ∈ D.filter Q, f d := by
    calc
      (∑ d ∈ D, f d) =
          (∑ d ∈ D.filter (fun d => ¬P d), f d) +
            ∑ d ∈ D.filter P, f d := by
        rw [add_comm]
        exact (Finset.sum_filter_add_sum_filter_not D P f).symm
      _ = _ := by rw [hPQ]
  have hinsert :
      (∑ d ∈ D.filter Q, f d) =
        ∑ r ∈ Dp,
          if C r then L (insertTuplePrime p m r) else 0 := by
    calc
      (∑ d ∈ D.filter Q, f d) =
          ∑ r ∈ insertedTupleSupportAt H R W p m,
            f (insertTuplePrime p m r) := by
        symm
        simpa [D, Q] using
          (sum_insertedTupleSupportAt_eq_coordinate_filter hp m f)
      _ = ∑ r ∈ insertedTupleSupportAt H R W p m,
          if C r then L (insertTuplePrime p m r) else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrSupport := (Finset.mem_filter.mp hr).1
        have hrMaynard := isMaynardDivisorTuple_of_mem_support hrSupport
        have hpCop : Nat.Coprime p (divisorTupleProduct H r) := by
          have hprodP : Nat.Coprime (divisorTupleProduct H r) p :=
            hrMaynard.2.1.coprime_dvd_right (dvd_mul_left p W)
          exact hprodP.symm
        unfold f
        rw [show C (insertTuplePrime p m r) ↔ C r by
          exact divisorTupleCondition_insert_event_prime_iff hp m hpCop hpn]
      _ = ∑ r ∈ Dp,
          if C r then L (insertTuplePrime p m r) else 0 := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro r hrDp hrNot
        have hinsNot : insertTuplePrime p m r ∉ D := by
          intro hins
          exact hrNot (Finset.mem_filter.mpr ⟨hrDp, hins⟩)
        have hzero : L (insertTuplePrime p m r) = 0 := by
          exact coefficient_insertPrime_eq_zero_of_not_mem_support hp hpW hy
            hrDp m hinsNot
        simp [hzero]
  calc
    (∑ d ∈ D.filter C, L d) = ∑ d ∈ D, f d := by
      rw [Finset.sum_filter]
    _ = (∑ d ∈ D.filter (fun d => ¬P d), f d) +
        ∑ d ∈ D.filter Q, f d := hpartition
    _ = (∑ d ∈ Dp, f d) +
        ∑ d ∈ Dp, if C d then L (insertTuplePrime p m d) else 0 := by
      rw [← hDp, hinsert]
    _ = ∑ d ∈ Dp.filter C,
        (L d + L (insertTuplePrime p m d)) := by
      rw [Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hcd : C d <;> simp [f, C, hcd]
    _ = ∑ d ∈ Dp.filter C,
        maynardCoefficientFromY H R (W * p)
          (differencePrimeY R W p m y) d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdSupport := (Finset.mem_filter.mp hd).1
      have hdMaynard := isMaynardDivisorTuple_of_mem_support hdSupport
      have hpCop : Nat.Coprime p (divisorTupleProduct H d) := by
        have hprodP : Nat.Coprime (divisorTupleProduct H d) p :=
          hdMaynard.2.1.coprime_dvd_right (dvd_mul_left p W)
        exact hprodP.symm
      symm
      exact maynardCoefficientFromY_differencePrimeY hp hpW hy hpCop m

/-- Pointwise realization of divisibility at a sieve coordinate by the
forced-prime `Y`-transform. -/
theorem preSievedWeight_on_coordinate_prime_event
    {H : Finset ℕ} {R W p n : ℕ} {y : (H → ℕ) → ℝ}
    (hW : 0 < W) (hp : p.Prime) (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY H R W y) (m : H)
    (hnW : n ≡ 0 [MOD W]) (hpn : p ∣ n + m.1)
    (hsep : ∀ h : H, h ≠ m → Nat.dist m.1 h.1 < p) :
    preSievedSquareDivisorWeight H (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) 0 W n =
      preSievedSquareDivisorWeight H
        (maynardDivisorTupleSupport H R (W * p))
        (maynardCoefficientFromY H R (W * p)
          (differencePrimeY R W p m y))
        (primeEventResidue hpW.symm m.1) (W * p) n := by
  have hcrt : n ≡ primeEventResidue hpW.symm m.1 [MOD W * p] :=
    (modEq_primeEventResidue_iff hW hp.pos hpW.symm).mpr ⟨hnW, hpn⟩
  unfold preSievedSquareDivisorWeight
  rw [if_pos hnW, if_pos hcrt]
  unfold squareDivisorWeight
  rw [divisorSum_eq_differencePrimeDivisorSum hp hpW hy m hpn hsep]

/-- Arbitrary-residue form of the distinguished-coordinate prime-event
identity, used in product correlations. -/
theorem preSievedWeight_on_coordinate_prime_event_at_residue
    {H : Finset ℕ} {R W p v n : ℕ} {y : (H → ℕ) → ℝ}
    (hp : p.Prime) (hpW : Nat.Coprime p W)
    (hy : IsSupportedMaynardY H R W y) (m : H)
    (hnW : n ≡ v [MOD W]) (hpn : p ∣ n + m.1)
    (hsep : ∀ h : H, h ≠ m → Nat.dist m.1 h.1 < p) :
    preSievedSquareDivisorWeight H (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) v W n =
      preSievedSquareDivisorWeight H
        (maynardDivisorTupleSupport H R (W * p))
        (maynardCoefficientFromY H R (W * p)
          (differencePrimeY R W p m y))
        (extendPrimeEventResidue hpW.symm v m.1) (W * p) n := by
  have hcrt : n ≡ extendPrimeEventResidue hpW.symm v m.1 [MOD W * p] :=
    (modEq_extendPrimeEventResidue_iff hp.pos hpW.symm).mpr ⟨hnW, hpn⟩
  unfold preSievedSquareDivisorWeight
  rw [if_pos hnW, if_pos hcrt]
  unfold squareDivisorWeight
  rw [divisorSum_eq_differencePrimeDivisorSum hp hpW hy m hpn hsep]

end Erdos248
