import ErdosProblems.Erdos372.Erdos372AffineSieve

/-!
# Prime-weighted finite affine sieve
-/

namespace Erdos372.AffineMaynard

open scoped BigOperators
open Erdos6.Maynard
open BoundedGaps.Maynard

noncomputable section

local instance affinePrimeDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def affinePrimeCount {H : Finset ℕ} (A : H → ℕ) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun h : H => (A h * n + 1).Prime).card

def affinePrimeWeightedSieveSum (H : Finset ℕ) (A : H → ℕ)
    (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Ico N (2 * N), (affinePrimeCount A n : ℝ) * w n

theorem affinePrimeCount_eq_indicator_sum {H : Finset ℕ}
    (A : H → ℕ) (n : ℕ) :
    (affinePrimeCount A n : ℝ) =
      ∑ h : H, if (A h * n + 1).Prime then 1 else 0 := by
  unfold affinePrimeCount
  simp

def affinePrimeWeightedPairInnerSum
    (H : Finset ℕ) (A : H → ℕ) (W N : ℕ)
    (lambda : (H → ℕ) → ℝ) (d e : H → ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico N (2 * N), ∑ h : H,
    if n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e ∧
        (A h * n + 1).Prime
    then lambda d * lambda e else 0

def affineCompatiblePrimeWeightedPairSum
    (H : Finset ℕ) (A : H → ℕ) (D : Finset (H → ℕ))
    (W N : ℕ) (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D.filter (fun e => IsCrossCoordinateCoprime H d e),
    affinePrimeWeightedPairInnerSum H A W N lambda d e

def affinePrimeProgressionCount (N A q a : ℕ) : ℕ :=
  ((Finset.Ico N (2 * N)).filter fun n =>
    n ≡ a [MOD q] ∧ (A * n + 1).Prime).card

theorem affinePrimeWeightedSieveSum_eq_pairIndicator
    (H : Finset ℕ) (A : H → ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (N W : ℕ) :
    affinePrimeWeightedSieveSum H A N
        (preSievedAffineSquareDivisorWeight A D lambda W) =
      ∑ d ∈ D, ∑ e ∈ D,
        affinePrimeWeightedPairInnerSum H A W N lambda d e := by
  classical
  unfold affinePrimeWeightedSieveSum
  simp_rw [affinePrimeCount_eq_indicator_sum]
  simp_rw [preSievedAffineSquareDivisorWeight_eq_pair_indicator]
  unfold affinePrimeWeightedPairInnerSum
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hp : (A h * n + 1).Prime <;>
    by_cases hc : n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e <;>
      simp [hp, hc]

theorem affinePrimeWeightedSieveSum_eq_compatiblePairSum
    {H : Finset ℕ} {A : H → ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W N : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversAffineDifferencePrimes A W) :
    affinePrimeWeightedSieveSum H A N
        (preSievedAffineSquareDivisorWeight A D lambda W) =
      affineCompatiblePrimeWeightedPairSum H A D W N lambda := by
  classical
  rw [affinePrimeWeightedSieveSum_eq_pairIndicator]
  unfold affineCompatiblePrimeWeightedPairSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hcross : IsCrossCoordinateCoprime H d e
  · simp [hcross]
  · have hzero : affinePrimeWeightedPairInnerSum H A W N lambda d e = 0 := by
      unfold affinePrimeWeightedPairInnerSum
      apply Finset.sum_eq_zero
      intro n hn
      apply Finset.sum_eq_zero
      intro h hh
      have hfalse :
          ¬(n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e) := by
        intro hc
        exact hcross (isCrossCoordinateCoprime_of_affinePairCondition
          (hD d hd) (hD e he) hcoverage hc.2)
      have hfalse' :
          ¬(n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e ∧
            (A h * n + 1).Prime) := by
        intro hc
        exact hfalse ⟨hc.1, hc.2.1⟩
      simp [hfalse']
    simp [hcross, hzero]

theorem affinePrimeWeightedPairInnerSum_eq_progressionCounts
    {H : Finset ℕ} {A : H → ℕ} {R W N : ℕ} {d e : H → ℕ}
    (hApos : ∀ h, 0 < A h) (hAprimes : CoversCoefficientPrimes A W)
    (hW : 0 < W) (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (lambda : (H → ℕ) → ℝ) :
    affinePrimeWeightedPairInnerSum H A W N lambda d e =
      ∑ h : H,
        (affinePrimeProgressionCount N (A h) (divisorPairModulus H W d e)
          (affineDivisorPairCrtResidue A R W d e hd he hcross) : ℝ) *
          (lambda d * lambda e) := by
  classical
  unfold affinePrimeWeightedPairInnerSum affinePrimeProgressionCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Ico N (2 * N)).filter (fun n =>
        n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e ∧
          (A h * n + 1).Prime) =
      (Finset.Ico N (2 * N)).filter (fun n =>
        n ≡ affineDivisorPairCrtResidue A R W d e hd he hcross
          [MOD divisorPairModulus H W d e] ∧ (A h * n + 1).Prime) := by
    ext n
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨hres, hpair, hp⟩
      exact ⟨(modEq_affineDivisorPairCrtResidue_iff
        hApos hAprimes hW hd he hcross n).mpr ⟨hres, hpair⟩, hp⟩
    · rintro ⟨hcrt, hp⟩
      obtain ⟨hres, hpair⟩ := (modEq_affineDivisorPairCrtResidue_iff
        hApos hAprimes hW hd he hcross n).mp hcrt
      exact ⟨hres, hpair, hp⟩
  rw [hfilter, Finset.sum_const]
  simp [nsmul_eq_mul]

theorem isMaynard_coordinate_lt_affinePrime
    {H : Finset ℕ} {A : H → ℕ} {R W N n : ℕ} {d : H → ℕ}
    (hApos : ∀ h, 0 < A h) (hd : IsMaynardDivisorTuple H R W d)
    (hRN : R ≤ N) (hn : N ≤ n) (h : H) :
    d h < A h * n + 1 := by
  have hprodPos : 0 < divisorTupleProduct H d := by
    unfold divisorTupleProduct
    apply Finset.prod_pos
    intro i hi
    exact Nat.pos_of_ne_zero (hd.coordinate_squarefree i).ne_zero
  have hcoord : d h ≤ divisorTupleProduct H d :=
    Nat.le_of_dvd hprodPos (divisorTupleCoordinate_dvd_product d h)
  have hdN : d h < N := (hcoord.trans_lt hd.1).trans_le hRN
  have hnform : n < A h * n + 1 := by
    have := hApos h
    nlinarith
  exact hdN.trans_le hn |>.trans hnform

theorem affinePrimeProgressionCount_eq_zero_of_coordinate_ne_one
    {H : Finset ℕ} {A : H → ℕ} {R W N : ℕ} {d e : H → ℕ}
    (hApos : ∀ h, 0 < A h) (hAprimes : CoversCoefficientPrimes A W)
    (hW : 0 < W) (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (hRN : R ≤ N) (h : H) (hc : d h ≠ 1 ∨ e h ≠ 1) :
    affinePrimeProgressionCount N (A h) (divisorPairModulus H W d e)
      (affineDivisorPairCrtResidue A R W d e hd he hcross) = 0 := by
  classical
  unfold affinePrimeProgressionCount
  apply Finset.card_eq_zero.mpr
  ext n
  simp only [Finset.mem_filter]
  constructor
  · intro hn
    have hnrange := Finset.mem_Ico.mp hn.1
    have hpair := (modEq_affineDivisorPairCrtResidue_iff
      hApos hAprimes hW hd he hcross n).mp hn.2.1
    rcases hc with hdh | heh
    · obtain hone | hsame := (Nat.dvd_prime hn.2.2).mp (hpair.2.1 h)
      · exact (hdh hone).elim
      · have hlt := isMaynard_coordinate_lt_affinePrime
          hApos hd hRN hnrange.1 h
        omega
    · obtain hone | hsame := (Nat.dvd_prime hn.2.2).mp (hpair.2.2 h)
      · exact (heh hone).elim
      · have hlt := isMaynard_coordinate_lt_affinePrime
          hApos he hRN hnrange.1 h
        omega
  · simp

def affineRestrictedS2Main
    (H : Finset ℕ) (A : H → ℕ) (D : Finset (H → ℕ))
    (W N : ℕ) (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d : D, ∑ e : D.filter
      (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
    ∑ h : H,
      if d.1 h = 1 ∧ e.1 h = 1 then
        (((primeCountTotal (2 * A h * N) : ℝ) -
            (primeCountTotal (A h * N) : ℝ)) /
          (Nat.totient (A h * divisorPairModulus H W d.1 e.1) : ℝ)) *
            (lambda d.1 * lambda e.1)
      else 0

def affineRestrictedS2Error
    (H : Finset ℕ) (A : H → ℕ) (D : Finset (H → ℕ))
    (R W N : ℕ) (lambda : (H → ℕ) → ℝ)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) : ℝ :=
  ∑ d : D, ∑ e : D.filter
      (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
    ∑ h : H,
      if d.1 h = 1 ∧ e.1 h = 1 then
        ((affinePrimeProgressionCount N (A h)
            (divisorPairModulus H W d.1 e.1)
            (affineDivisorPairCrtResidue A R W d.1 e.1
              (hD d.1 d.2) (hD e.1 (Finset.mem_filter.mp e.2).1)
              (Finset.mem_filter.mp e.2).2) : ℝ) -
          ((primeCountTotal (2 * A h * N) : ℝ) -
            (primeCountTotal (A h * N) : ℝ)) /
              (Nat.totient (A h * divisorPairModulus H W d.1 e.1) : ℝ)) *
            (lambda d.1 * lambda e.1)
      else 0

theorem affineCompatiblePrimeWeightedPairSum_eq_main_add_error
    {H : Finset ℕ} {A : H → ℕ} {D : Finset (H → ℕ)}
    {R W N : ℕ} {lambda : (H → ℕ) → ℝ}
    (hApos : ∀ h, 0 < A h) (hAprimes : CoversCoefficientPrimes A W)
    (hW : 0 < W) (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hRN : R ≤ N) :
    affineCompatiblePrimeWeightedPairSum H A D W N lambda =
      affineRestrictedS2Main H A D W N lambda +
        affineRestrictedS2Error H A D R W N lambda hD := by
  classical
  unfold affineCompatiblePrimeWeightedPairSum affineRestrictedS2Main
    affineRestrictedS2Error
  rw [← Finset.sum_attach]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_filter, Finset.univ_eq_attach, ← Finset.sum_filter,
    ← Finset.sum_attach, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨heD, hcross⟩ := Finset.mem_filter.mp e.2
  rw [affinePrimeWeightedPairInnerSum_eq_progressionCounts
    hApos hAprimes hW (hD d.1 d.2) (hD e.1 heD) hcross lambda]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hc : d.1 h = 1 ∧ e.1 h = 1
  · simp [hc]
    ring
  · have hz := affinePrimeProgressionCount_eq_zero_of_coordinate_ne_one
      hApos hAprimes hW (hD d.1 d.2) (hD e.1 heD) hcross hRN h
        (not_and_or.mp hc)
    simp [hc, hz]

theorem totient_mul_of_primeFactors_subset
    {A q : ℕ} (hA : 0 < A)
    (hsub : A.primeFactors ⊆ q.primeFactors) :
    Nat.totient (A * q) = A * Nat.totient q := by
  induction A using Nat.strong_induction_on with
  | h A ih =>
      by_cases hAone : A = 1
      · subst A
        simp
      obtain ⟨p, hp, hpA⟩ := Nat.exists_prime_and_dvd hAone
      let b := A / p
      have hAeq : p * b = A := by
        simpa [b, mul_comm] using Nat.div_mul_cancel hpA
      have hbpos : 0 < b :=
        Nat.div_pos (Nat.le_of_dvd hA hpA) hp.pos
      have hblt : b < A := by
        rw [← hAeq]
        exact lt_mul_of_one_lt_left hbpos hp.one_lt
      have hbDvd : b ∣ A := ⟨p, by rw [← hAeq, mul_comm]⟩
      have hbsub : b.primeFactors ⊆ q.primeFactors :=
        (Nat.primeFactors_mono hbDvd hA.ne').trans hsub
      have hpMem : p ∈ A.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hpA, hA.ne'⟩
      have hpq : p ∣ q := Nat.dvd_of_mem_primeFactors (hsub hpMem)
      calc
        Nat.totient (A * q) = Nat.totient (p * (b * q)) := by rw [← hAeq]; ring_nf
        _ = p * Nat.totient (b * q) :=
          Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_of_dvd_right hpq b)
        _ = p * (b * Nat.totient q) := by rw [ih b hblt hbpos hbsub]
        _ = A * Nat.totient q := by rw [← hAeq]; ring

theorem affinePrimeProgressionCount_eq_primeVariableProgressionCount
    (N A q a : ℕ) (hA : 0 < A) :
    affinePrimeProgressionCount N A q a =
      primeVariableProgressionCount (A * N + 1) (A * (2 * N) + 1)
        (A * q) (A * a + 1) := by
  unfold affinePrimeProgressionCount primeVariableProgressionCount
  apply Finset.card_bij (fun n hn => A * n + 1)
  · intro n hn
    obtain ⟨hnI, hnmod, hnprime⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ico.mp hnI
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨by gcongr, by gcongr⟩, hnprime, ?_⟩
    exact (hnmod.mul_left' A).add_right 1
  · intro n₁ hn₁ n₂ hn₂ heq
    have hmul : A * n₁ = A * n₂ := by omega
    exact Nat.eq_of_mul_eq_mul_left hA hmul
  · intro m hm
    obtain ⟨hmI, hmprime, hmmod⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmlo, hmhi⟩ := Finset.mem_Ico.mp hmI
    have hmodA : m ≡ 1 [MOD A] :=
      (hmmod.of_dvd (dvd_mul_right A q)).trans
        (Nat.ModEq.modulus_mul_add (m := A) (a := a) (b := 1))
    have hdiv : A ∣ m - 1 :=
      (Nat.modEq_iff_dvd' (by omega : 1 ≤ m)).mp hmodA.symm
    let n := (m - 1) / A
    have hnEq : A * n + 1 = m := by
      have hmul : n * A = m - 1 := Nat.div_mul_cancel hdiv
      dsimp [n] at hmul ⊢
      rw [mul_comm, hmul]
      omega
    have hnlo : N ≤ n := by
      by_contra hn
      have hlt := Nat.mul_lt_mul_of_pos_left (lt_of_not_ge hn) hA
      rw [← hnEq] at hmlo
      omega
    have hnhi : n < 2 * N := by
      by_contra hn
      have hle := Nat.mul_le_mul_left A (le_of_not_gt hn)
      rw [← hnEq] at hmhi
      omega
    have hnmod : n ≡ a [MOD q] := by
      apply Nat.ModEq.mul_left_cancel' hA.ne'
      apply Nat.ModEq.add_right_cancel' 1
      simpa [hnEq] using hmmod
    refine ⟨n, Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hnlo, hnhi⟩, hnmod, by simpa [hnEq] using hmprime⟩,
      hnEq⟩

def affinePrimeIntervalCount (N A : ℕ) : ℝ :=
  ((primeCountTotal (2 * A * N) : ℝ) -
    (primeCountTotal (A * N) : ℝ)) / A

theorem affineRestrictedS2Main_eq_shift_sum
    {H : Finset ℕ} {A : H → ℕ} {D : Finset (H → ℕ)}
    {R W N : ℕ} {lambda : (H → ℕ) → ℝ}
    (hApos : ∀ h, 0 < A h) (hAprimes : CoversCoefficientPrimes A W)
    (hW : 0 < W) (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    affineRestrictedS2Main H A D W N lambda =
      ∑ h : H, affinePrimeIntervalCount N (A h) *
        restrictedMainArithmeticCoefficient H D W lambda h := by
  classical
  let term (d : D) (e : D.filter
      (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e)) (h : H) : ℝ :=
    if d.1 h = 1 ∧ e.1 h = 1 then
      (((primeCountTotal (2 * A h * N) : ℝ) -
          (primeCountTotal (A h * N) : ℝ)) /
        (Nat.totient (A h * divisorPairModulus H W d.1 e.1) : ℝ)) *
          (lambda d.1 * lambda e.1)
    else 0
  change (∑ d : D, ∑ e : D.filter
      (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
        ∑ h : H, term d e h) = _
  simp only [Finset.univ_eq_attach]
  have hswap :
      (∑ d ∈ D.attach,
        ∑ e ∈ (D.filter
          (fun e : H → ℕ => IsCrossCoordinateCoprime H (d : H → ℕ) e)).attach,
          ∑ h ∈ H.attach, term d e h) =
      ∑ h ∈ H.attach,
        ∑ d ∈ D.attach,
          ∑ e ∈ (D.filter
            (fun e : H → ℕ => IsCrossCoordinateCoprime H (d : H → ℕ) e)).attach,
            term d e h := by
    calc
      (∑ d ∈ D.attach,
        ∑ e ∈ (D.filter
          (fun e : H → ℕ => IsCrossCoordinateCoprime H (d : H → ℕ) e)).attach,
          ∑ h ∈ H.attach, term d e h) =
          ∑ d ∈ D.attach, ∑ h ∈ H.attach,
            ∑ e ∈ (D.filter
              (fun e : H → ℕ => IsCrossCoordinateCoprime H (d : H → ℕ) e)).attach,
              term d e h := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro h hh
  unfold restrictedMainArithmeticCoefficient affinePrimeIntervalCount
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨heD, hcross⟩ := Finset.mem_filter.mp e.2
  by_cases hc : d.1 h = 1 ∧ e.1 h = 1
  · have hqpos : 0 < divisorPairModulus H W d.1 e.1 :=
      divisorPairModulus_pos hW (hD d.1 d.2) (hD e.1 heD)
    have hWdvd : W ∣ divisorPairModulus H W d.1 e.1 := by
      unfold divisorPairModulus
      exact dvd_mul_right W _
    have hsub : (A h).primeFactors ⊆
        (divisorPairModulus H W d.1 e.1).primeFactors :=
      (hAprimes h).trans
        (Nat.primeFactors_mono hWdvd hqpos.ne')
    have hphi := totient_mul_of_primeFactors_subset (hApos h) hsub
    simp [term, hc, hphi]
    field_simp [show (A h : ℝ) ≠ 0 by exact_mod_cast (hApos h).ne']
  · simp [term, hc]

end

end Erdos372.AffineMaynard
