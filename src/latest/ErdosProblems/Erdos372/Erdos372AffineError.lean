import ErdosProblems.Erdos372.Erdos372AffineMain

/-!
# Bombieri--Vinogradov error for the affine Maynard sieve
-/

namespace Erdos372.AffineMaynard

open Filter Set
open scoped ArithmeticFunction.omega BigOperators
open Erdos6.Maynard
open BoundedGaps.Maynard

noncomputable section

local instance affineErrorDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem affineDivisorPairCrtResidue_coprime
    {H : Finset ℕ} {A : H → ℕ} {R W : ℕ} {d e : H → ℕ}
    (hApos : ∀ h, 0 < A h)
    (hW : 0 < W)
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (hAprimes : CoversCoefficientPrimes A W)
    (hcoverage : CoversAffineDifferencePrimes A W)
    (h : H) (hdh : d h = 1) (heh : e h = 1) :
    Nat.Coprime
      (A h * affineDivisorPairCrtResidue A R W d e hd he hcross + 1)
      (A h * divisorPairModulus H W d e) := by
  classical
  let a := affineDivisorPairCrtResidue A R W d e hd he hcross
  have haCrt : a ≡ affineDivisorPairCrtResidue A R W d e hd he hcross
      [MOD divisorPairModulus H W d e] := Nat.ModEq.refl _
  obtain ⟨haW, haPair⟩ :=
    (modEq_affineDivisorPairCrtResidue_iff
      hApos hAprimes hW
      hd he hcross a).mp haCrt
  have hcopW : Nat.Coprime (A h * a + 1) W := by
    simpa using preSieve_coprime_of_modEq (haW.mul_left (A h))
      (Nat.coprime_one_left W)
  have hcopProduct : Nat.Coprime (A h * a + 1)
      (∏ j : H, divisorTupleLcm H d e j) := by
    apply Nat.Coprime.prod_right
    intro j hj
    by_cases hjh : j = h
    · subst j
      simp [divisorTupleLcm, hdh, heh]
    · by_contra hnot
      obtain ⟨p, hp, hpFormH, hplcm⟩ :=
        Nat.Prime.not_coprime_iff_dvd.mp hnot
      have hpde : p ∣ d j ∨ p ∣ e j := hp.dvd_or_dvd_of_dvd_lcm hplcm
      have hpFormJ : p ∣ A j * a + 1 := by
        rcases hpde with hpd | hpe
        · exact hpd.trans (haPair.1 j)
        · exact hpe.trans (haPair.2 j)
      have hpaCoprime : Nat.Coprime p a := by
        rw [hp.coprime_iff_not_dvd]
        intro hpa
        have hpMul : p ∣ A h * a := dvd_mul_of_dvd_right hpa (A h)
        have hpOne : p ∣ 1 := by
          simpa using Nat.dvd_sub hpFormH hpMul
        exact hp.not_dvd_one hpOne
      have hpdist : p ∣ Nat.dist (A h) (A j) := by
        by_cases hle : A h ≤ A j
        · have hsub : p ∣ (A j * a + 1) - (A h * a + 1) :=
            Nat.dvd_sub hpFormJ hpFormH
          have hmul : p ∣ (A j - A h) * a := by
            simpa [Nat.add_sub_add_right, Nat.mul_sub_right_distrib] using hsub
          rw [Nat.dist_eq_sub_of_le hle]
          exact hpaCoprime.dvd_of_dvd_mul_right hmul
        · have hle' : A j ≤ A h := le_of_not_ge hle
          have hsub : p ∣ (A h * a + 1) - (A j * a + 1) :=
            Nat.dvd_sub hpFormH hpFormJ
          have hmul : p ∣ (A h - A j) * a := by
            simpa [Nat.add_sub_add_right, Nat.mul_sub_right_distrib] using hsub
          rw [Nat.dist_comm (A h) (A j), Nat.dist_eq_sub_of_le hle']
          exact hpaCoprime.dvd_of_dvd_mul_right hmul
      have hpW : p ∣ W := hcoverage (Ne.symm hjh) p hp hpdist
      have hpcopW : Nat.Coprime p W := by
        rcases hpde with hpd | hpe
        · exact (hd.coordinate_coprime_W j).coprime_dvd_left hpd
        · exact (he.coordinate_coprime_W j).coprime_dvd_left hpe
      exact (hp.coprime_iff_not_dvd.mp hpcopW) hpW
  have hcopA : Nat.Coprime (A h * a + 1) (A h) :=
    (Nat.coprime_mul_left_add_left 1 (A h) a).mpr
      (Nat.coprime_one_left (A h))
  simpa [a, divisorPairModulus, mul_assoc] using
    hcopA.mul_right (hcopW.mul_right hcopProduct)

def affinePrimeProgressionIntervalDiscrepancy
    (N A q a : ℕ) : ℝ :=
  |(affinePrimeProgressionCount N A q a : ℝ) -
    ((primeCountTotal (2 * A * N) : ℝ) -
      (primeCountTotal (A * N) : ℝ)) /
        (Nat.totient (A * q) : ℝ)|

theorem affinePrimeProgressionIntervalDiscrepancy_le_global_max
    {N A q a : ℕ} (hN : 0 < N) (hA : 0 < A)
    (hq : 0 < q) (hcop : Nat.Coprime (A * a + 1) (A * q)) :
    affinePrimeProgressionIntervalDiscrepancy N A q a ≤
      maxProgressionDiscrepancy (2 * A * N) (A * q) +
        maxProgressionDiscrepancy (A * N) (A * q) := by
  have hAq : 0 < A * q := Nat.mul_pos hA hq
  have hres : (A * a + 1) % (A * q) ∈ coprimeResidues (A * q) :=
    coprime_mod_mem_coprimeResidues hAq hcop
  unfold affinePrimeProgressionIntervalDiscrepancy
  rw [affinePrimeProgressionCount_eq_primeVariableProgressionCount N A q a hA]
  have hbase := primeVariableProgressionCount_intervalDiscrepancy_le_global_sum
    (A := A * N + 1) (B := A * (2 * N) + 1)
    (q := A * q) (r := A * a + 1) (by positivity) (by
      gcongr
      omega)
  have hreduce (x : ℕ) : progressionDiscrepancy x (A * q) (A * a + 1) =
      progressionDiscrepancy x (A * q) ((A * a + 1) % (A * q)) := by
    unfold progressionDiscrepancy primeCountUpTo
    simp only [Nat.mod_mod]
  calc
    _ ≤ progressionDiscrepancy (A * (2 * N)) (A * q) (A * a + 1) +
        progressionDiscrepancy (A * N) (A * q) (A * a + 1) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hbase
    _ = progressionDiscrepancy (2 * A * N) (A * q)
          ((A * a + 1) % (A * q)) +
        progressionDiscrepancy (A * N) (A * q)
          ((A * a + 1) % (A * q)) := by
      rw [hreduce, hreduce]
      congr 2 <;> simp [mul_assoc, mul_comm, mul_left_comm]
    _ ≤ _ := add_le_add
      (progressionDiscrepancy_le_max hAq hres)
      (progressionDiscrepancy_le_max hAq hres)

noncomputable def affineCompatiblePairShiftCrtResidue
    (H : Finset ℕ) (A : H → ℕ) (D : Finset (H → ℕ)) (R W : ℕ)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (i : (((H → ℕ) × (H → ℕ)) × H)) : ℕ :=
  if hi : i ∈ compatiblePairShiftIndex H D then
    affineDivisorPairCrtResidue A R W i.1.1 i.1.2
      (hD i.1.1 (compatiblePairShiftIndex_data hi).1)
      (hD i.1.2 (compatiblePairShiftIndex_data hi).2.1)
      (compatiblePairShiftIndex_data hi).2.2.1
  else 0

def affineRestrictedS2AbsoluteError
    (H : Finset ℕ) (A : H → ℕ) (D : Finset (H → ℕ))
    (R W N : ℕ) (lambda : (H → ℕ) → ℝ)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) : ℝ :=
  ∑ d : D, ∑ e : D.filter
      (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
    ∑ h ∈ H.attach,
      if d.1 h = 1 ∧ e.1 h = 1 then
        |lambda d.1 * lambda e.1| *
          affinePrimeProgressionIntervalDiscrepancy N (A h)
            (divisorPairModulus H W d.1 e.1)
            (affineCompatiblePairShiftCrtResidue H A D R W hD
              ((d.1, e.1), h))
      else 0

theorem abs_affineRestrictedS2Error_le_absoluteError
    {H : Finset ℕ} {A : H → ℕ} {D : Finset (H → ℕ)}
    {R W N : ℕ} {lambda : (H → ℕ) → ℝ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    |affineRestrictedS2Error H A D R W N lambda hD| ≤
      affineRestrictedS2AbsoluteError H A D R W N lambda hD := by
  classical
  unfold affineRestrictedS2Error affineRestrictedS2AbsoluteError
  calc
    |∑ d : D, ∑ e : D.filter
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
        else 0| ≤
        ∑ d : D, |∑ e : D.filter
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
            else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d : D, ∑ e : D.filter
        (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
      |∑ h : H,
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
        else 0| := by
      apply Finset.sum_le_sum
      intro d hd
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d : D, ∑ e : D.filter
        (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
      ∑ h : H,
        |if d.1 h = 1 ∧ e.1 h = 1 then
          ((affinePrimeProgressionCount N (A h)
              (divisorPairModulus H W d.1 e.1)
              (affineDivisorPairCrtResidue A R W d.1 e.1
                (hD d.1 d.2) (hD e.1 (Finset.mem_filter.mp e.2).1)
                (Finset.mem_filter.mp e.2).2) : ℝ) -
            ((primeCountTotal (2 * A h * N) : ℝ) -
              (primeCountTotal (A h * N) : ℝ)) /
                (Nat.totient (A h * divisorPairModulus H W d.1 e.1) : ℝ)) *
              (lambda d.1 * lambda e.1)
        else 0| := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro h hh
      by_cases hc : d.1 h = 1 ∧ e.1 h = 1
      · have hi : ((d.1, e.1), h) ∈ compatiblePairShiftIndex H D := by
          unfold compatiblePairShiftIndex
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_univ h⟩, hc⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨d.2, (Finset.mem_filter.mp e.2).1⟩,
            (Finset.mem_filter.mp e.2).2⟩
        have hres : affineCompatiblePairShiftCrtResidue H A D R W hD
            ((d.1, e.1), h) =
            affineDivisorPairCrtResidue A R W d.1 e.1
              (hD d.1 d.2) (hD e.1 (Finset.mem_filter.mp e.2).1)
              (Finset.mem_filter.mp e.2).2 := by
          unfold affineCompatiblePairShiftCrtResidue
          rw [dif_pos hi]
        rw [if_pos hc, if_pos hc, hres, abs_mul]
        unfold affinePrimeProgressionIntervalDiscrepancy
        rw [mul_comm]
      · simp [hc]

def affineCompatiblePairShiftWeightedErrorSum
    (H : Finset ℕ) (A : H → ℕ) (D : Finset (H → ℕ))
    (R W N : ℕ) (lambda : (H → ℕ) → ℝ)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) : ℝ :=
  ∑ i ∈ compatiblePairShiftIndex H D,
    |lambda i.1.1 * lambda i.1.2| *
      affinePrimeProgressionIntervalDiscrepancy N (A i.2)
        (compatiblePairShiftModulus H W i)
        (affineCompatiblePairShiftCrtResidue H A D R W hD i)

theorem affineRestrictedS2AbsoluteError_eq_weightedErrorSum
    {H : Finset ℕ} {A : H → ℕ} {D : Finset (H → ℕ)}
    {R W N : ℕ} {lambda : (H → ℕ) → ℝ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    affineRestrictedS2AbsoluteError H A D R W N lambda hD =
      affineCompatiblePairShiftWeightedErrorSum H A D R W N lambda hD := by
  classical
  unfold affineRestrictedS2AbsoluteError
    affineCompatiblePairShiftWeightedErrorSum
  rw [compatiblePairShiftIndex, Finset.sum_filter]
  symm
  calc
    (∑ a ∈ ((D ×ˢ D).filter (fun de =>
          IsCrossCoordinateCoprime H de.1 de.2)).product Finset.univ,
        if a.1.1 a.2 = 1 ∧ a.1.2 a.2 = 1 then
          |lambda a.1.1 * lambda a.1.2| *
            affinePrimeProgressionIntervalDiscrepancy N (A a.2)
              (compatiblePairShiftModulus H W a)
              (affineCompatiblePairShiftCrtResidue H A D R W hD a)
        else 0) =
        ∑ de ∈ (D ×ˢ D).filter (fun de =>
            IsCrossCoordinateCoprime H de.1 de.2),
          ∑ h : H,
            if de.1 h = 1 ∧ de.2 h = 1 then
              |lambda de.1 * lambda de.2| *
                affinePrimeProgressionIntervalDiscrepancy N (A h)
                  (compatiblePairShiftModulus H W (de, h))
                  (affineCompatiblePairShiftCrtResidue H A D R W hD (de, h))
            else 0 := Finset.sum_product _ Finset.univ _
    _ = ∑ de ∈ D ×ˢ D,
        if IsCrossCoordinateCoprime H de.1 de.2 then
          ∑ h : H,
            if de.1 h = 1 ∧ de.2 h = 1 then
              |lambda de.1 * lambda de.2| *
                affinePrimeProgressionIntervalDiscrepancy N (A h)
                  (compatiblePairShiftModulus H W (de, h))
                  (affineCompatiblePairShiftCrtResidue H A D R W hD (de, h))
            else 0
        else 0 := Finset.sum_filter _ _
    _ = ∑ d ∈ D, ∑ e ∈ D,
        if IsCrossCoordinateCoprime H d e then
          ∑ h : H,
            if d h = 1 ∧ e h = 1 then
              |lambda d * lambda e| *
                affinePrimeProgressionIntervalDiscrepancy N (A h)
                  (compatiblePairShiftModulus H W ((d, e), h))
                  (affineCompatiblePairShiftCrtResidue H A D R W hD ((d, e), h))
            else 0
        else 0 := Finset.sum_product D D _
    _ = ∑ d : D, ∑ e : D.filter
        (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
      ∑ h ∈ H.attach,
        if d.1 h = 1 ∧ e.1 h = 1 then
          |lambda d.1 * lambda e.1| *
            affinePrimeProgressionIntervalDiscrepancy N (A h)
              (divisorPairModulus H W d.1 e.1)
              (affineCompatiblePairShiftCrtResidue H A D R W hD
                ((d.1, e.1), h))
        else 0 := by
      simp only [Finset.univ_eq_attach H]
      unfold compatiblePairShiftModulus
      let g : (H → ℕ) → (H → ℕ) → ℝ := fun d e =>
        ∑ h ∈ H.attach,
          if d h = 1 ∧ e h = 1 then
            |lambda d * lambda e| *
              affinePrimeProgressionIntervalDiscrepancy N (A h)
                (divisorPairModulus H W d e)
                (affineCompatiblePairShiftCrtResidue H A D R W hD ((d, e), h))
          else 0
      change (∑ d ∈ D, ∑ e ∈ D,
          if IsCrossCoordinateCoprime H d e then g d e else 0) =
        ∑ d : D, ∑ e : D.filter
          (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e), g d.1 e.1
      calc
        _ = ∑ d ∈ D, ∑ e ∈ D.filter
            (fun e : H → ℕ => IsCrossCoordinateCoprime H d e), g d e := by
          apply Finset.sum_congr rfl
          intro d hd
          exact (Finset.sum_filter _ _).symm
        _ = ∑ d ∈ D, ∑ e : D.filter
            (fun e : H → ℕ => IsCrossCoordinateCoprime H d e), g d e.1 := by
          apply Finset.sum_congr rfl
          intro d hd
          exact Finset.sum_subtype _ (fun _ => Iff.rfl) _
        _ = _ := Finset.sum_subtype D (fun _ => Iff.rfl) _

theorem affineWeightedErrorSum_le_endpointDiscrepancies
    {H : Finset ℕ} {A : H → ℕ} {D : Finset (H → ℕ)}
    {R W N : ℕ} {lambda : (H → ℕ) → ℝ} {L : ℝ}
    (hApos : ∀ h, 0 < A h) (hW : 0 < W)
    (hAprimes : CoversCoefficientPrimes A W)
    (hcoverage : CoversAffineDifferencePrimes A W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hN : 0 < N) (hL : 0 ≤ L)
    (hbound : ∀ d ∈ D, |lambda d| ≤ L) :
    affineCompatiblePairShiftWeightedErrorSum H A D R W N lambda hD ≤
      L ^ 2 *
        (∑ i ∈ compatiblePairShiftIndex H D,
          (maxProgressionDiscrepancy (2 * A i.2 * N)
              (A i.2 * compatiblePairShiftModulus H W i) +
            maxProgressionDiscrepancy (A i.2 * N)
              (A i.2 * compatiblePairShiftModulus H W i))) := by
  classical
  unfold affineCompatiblePairShiftWeightedErrorSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hiData := compatiblePairShiftIndex_data hi
  have hdi := hD i.1.1 hiData.1
  have hei := hD i.1.2 hiData.2.1
  have hcross : IsCrossCoordinateCoprime H i.1.1 i.1.2 :=
    hiData.2.2.1
  have hres : affineCompatiblePairShiftCrtResidue H A D R W hD i =
      affineDivisorPairCrtResidue A R W i.1.1 i.1.2 hdi hei hcross := by
    unfold affineCompatiblePairShiftCrtResidue
    rw [dif_pos hi]
  have hcop := affineDivisorPairCrtResidue_coprime hApos hW hdi hei hcross
    hAprimes hcoverage i.2 hiData.2.2.2.1 hiData.2.2.2.2
  have herr : affinePrimeProgressionIntervalDiscrepancy N (A i.2)
      (compatiblePairShiftModulus H W i)
      (affineCompatiblePairShiftCrtResidue H A D R W hD i) ≤
      maxProgressionDiscrepancy (2 * A i.2 * N)
          (A i.2 * compatiblePairShiftModulus H W i) +
        maxProgressionDiscrepancy (A i.2 * N)
          (A i.2 * compatiblePairShiftModulus H W i) := by
    rw [hres]
    exact affinePrimeProgressionIntervalDiscrepancy_le_global_max
      hN (hApos i.2)
      (divisorPairModulus_pos hW hdi hei) hcop
  have hcoef : |lambda i.1.1 * lambda i.1.2| ≤ L ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ L * L := mul_le_mul (hbound i.1.1 hiData.1)
        (hbound i.1.2 hiData.2.1) (abs_nonneg _) hL
      _ = L ^ 2 := by ring
  exact mul_le_mul hcoef herr (abs_nonneg _) (sq_nonneg L)

theorem PrimeLevelWitness.sum_tauPow_mul_affineMaxDiscrepancy
    {theta B C : ℝ} {X₀ x d Q A₀ : ℕ}
    (hw : PrimeLevelWitness theta B C X₀) (hx : X₀ ≤ x)
    (hA₀ : 0 < A₀) (S : Finset ℕ)
    (hSQ : S ⊆ Finset.Icc 1 Q)
    (hsq : ∀ q ∈ S, Squarefree q)
    (hAsub : ∀ q ∈ S, A₀.primeFactors ⊆ q.primeFactors)
    (hsize : A₀ * Q ≤ x + 1)
    (hcut : S.image (fun q => A₀ * q) ⊆
      Finset.Icc 1 (modulusCutoff theta x)) :
    (∑ q ∈ S, ((d ^ ω q : ℕ) : ℝ) *
        maxProgressionDiscrepancy x (A₀ * q)) ≤
      Real.sqrt
          ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
            (1 + Real.log Q) ^ (2 * d ^ 2)) *
        Real.sqrt
          (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) B) := by
  have hweighted := sum_weight_mul_le_sqrt_of_pointwise_div S
    (fun q => ((d ^ ω q : ℕ) : ℝ))
    (fun q => maxProgressionDiscrepancy x (A₀ * q))
    (fun q => (Nat.totient q : ℝ))
    ((3 : ℝ) * ((x + 1 : ℕ) : ℝ))
    (fun q hq => maxProgressionDiscrepancy_nonneg x (A₀ * q)) (by
      intro q hq
      have hqData := Finset.mem_Icc.mp (hSQ hq)
      have hqpos : 0 < q := zero_lt_one.trans_le hqData.1
      have hAqpos : 0 < A₀ * q := Nat.mul_pos hA₀ hqpos
      have hAqle : A₀ * q ≤ x + 1 :=
        (Nat.mul_le_mul_left A₀ hqData.2).trans hsize
      have htriv := maxProgressionDiscrepancy_le_three_mul_div hAqpos hAqle
      have hphi := totient_mul_of_primeFactors_subset hA₀ hqpos (hAsub q hq)
      rw [hphi] at htriv
      have hphiPos : (0 : ℝ) < Nat.totient q := by
        exact_mod_cast (Nat.totient_pos.mpr hqpos)
      have hAreal : (1 : ℝ) ≤ A₀ := by exact_mod_cast hA₀
      calc
        maxProgressionDiscrepancy x (A₀ * q) ≤
            3 * ((x + 1 : ℕ) : ℝ) /
              ((A₀ : ℝ) * (Nat.totient q : ℝ)) := by
          simpa only [Nat.cast_mul] using htriv
        _ ≤ 3 * ((x + 1 : ℕ) : ℝ) / (Nat.totient q : ℝ) := by
          apply div_le_div_of_nonneg_left (by positivity) hphiPos
          nlinarith
        _ = ((3 : ℝ) * ((x + 1 : ℕ) : ℝ)) /
              (Nat.totient q : ℝ) := by ring)
  have htau := sum_tauPow_sq_div_totient_le_one_add_log d Q S hSQ hsq
  have himageInj : Function.Injective (fun q : ℕ => A₀ * q) := by
    intro q r hqr
    exact Nat.eq_of_mul_eq_mul_left hA₀ hqr
  have hlevel : (∑ q ∈ S, maxProgressionDiscrepancy x (A₀ * q)) ≤
      C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) B := by
    calc
      _ = ∑ m ∈ S.image (fun q => A₀ * q),
          maxProgressionDiscrepancy x m := by
        rw [Finset.sum_image]
        exact fun q hq r hr hqr => himageInj hqr
      _ ≤ _ := hw.sum_maxProgressionDiscrepancy_subset hx _ hcut
  calc
    _ ≤ Real.sqrt
        (((3 : ℝ) * ((x + 1 : ℕ) : ℝ)) *
          ∑ q ∈ S, (((d ^ ω q : ℕ) : ℝ) ^ 2) /
            (Nat.totient q : ℝ)) *
        Real.sqrt (∑ q ∈ S,
          maxProgressionDiscrepancy x (A₀ * q)) := hweighted
    _ ≤ Real.sqrt
        (((3 : ℝ) * ((x + 1 : ℕ) : ℝ)) *
          (1 + Real.log Q) ^ (2 * d ^ 2)) *
        Real.sqrt (∑ q ∈ S,
          maxProgressionDiscrepancy x (A₀ * q)) := by
      apply mul_le_mul_of_nonneg_right
      · apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_left htau (by positivity)
      · positivity
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlevel)
      positivity

theorem PrimeLevelWitness.sum_affineMaxDiscrepancy_comp_le_tauEnvelope
    {theta B C : ℝ} {X₀ x : ℕ}
    (hw : PrimeLevelWitness theta B C X₀) (hx : X₀ ≤ x)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W A₀ : ℕ}
    (hH : H.Nonempty) (hW : Squarefree W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hA₀ : 0 < A₀) (hAprimes : A₀.primeFactors ⊆ W.primeFactors)
    (hsize : A₀ * (W * R * R) ≤ x + 1)
    (hcut : ((compatiblePairShiftIndex H D).image
        (compatiblePairShiftModulus H W)).image (fun q => A₀ * q) ⊆
      Finset.Icc 1 (modulusCutoff theta x)) :
    (∑ i ∈ compatiblePairShiftIndex H D,
        maxProgressionDiscrepancy x
          (A₀ * compatiblePairShiftModulus H W i)) ≤
      (Fintype.card H : ℝ) *
        (Real.sqrt
            ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
              (1 + Real.log (W * R * R)) ^
                (2 * (3 * Fintype.card H) ^ 2)) *
          Real.sqrt
            (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) B)) := by
  let S := (compatiblePairShiftIndex H D).image
    (compatiblePairShiftModulus H W)
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW.ne_zero
  have hSQ := compatiblePairShiftModulus_image_subset_radius hWpos hD
  have hfiber :
      (∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy x
            (A₀ * compatiblePairShiftModulus H W i)) ≤
        ∑ q ∈ S,
          (((3 * Fintype.card H) ^ ω q * Fintype.card H : ℕ) : ℝ) *
            maxProgressionDiscrepancy x (A₀ * q) := by
    calc
      _ = ∑ q ∈ S,
          (modulusFiberCard (compatiblePairShiftIndex H D)
            (compatiblePairShiftModulus H W) q : ℝ) *
            maxProgressionDiscrepancy x (A₀ * q) := by
        simpa [S] using sum_comp_eq_sum_modulusFiberCard
          (compatiblePairShiftIndex H D) (compatiblePairShiftModulus H W)
          (fun q => maxProgressionDiscrepancy x (A₀ * q))
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast modulusFiberCard_le_tauPow hH hWpos hD
            (squarefree_of_mem_compatiblePairShiftModulus_image hW hD hq)
            (W_dvd_of_mem_compatiblePairShiftModulus_image hq)
        · exact maxProgressionDiscrepancy_nonneg x (A₀ * q)
  have hAsub : ∀ q ∈ S, A₀.primeFactors ⊆ q.primeFactors := by
    intro q hq
    have hWq := W_dvd_of_mem_compatiblePairShiftModulus_image hq
    have hqpos := (Finset.mem_Icc.mp (hSQ hq)).1
    exact hAprimes.trans (Nat.primeFactors_mono hWq (by omega))
  have hweighted := sum_tauPow_mul_affineMaxDiscrepancy
    (d := 3 * Fintype.card H) (Q := W * R * R)
    hw hx hA₀ S hSQ
    (fun q hq => squarefree_of_mem_compatiblePairShiftModulus_image hW hD hq)
    hAsub hsize (by simpa [S] using hcut)
  calc
    _ ≤ ∑ q ∈ S,
        (((3 * Fintype.card H) ^ ω q * Fintype.card H : ℕ) : ℝ) *
          maxProgressionDiscrepancy x (A₀ * q) := hfiber
    _ = (Fintype.card H : ℝ) *
        ∑ q ∈ S, (((3 * Fintype.card H) ^ ω q : ℕ) : ℝ) *
          maxProgressionDiscrepancy x (A₀ * q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      push_cast
      ring
    _ ≤ _ := by
      simpa only [Nat.cast_mul] using
        (mul_le_mul_of_nonneg_left hweighted (Nat.cast_nonneg _))

theorem PrimeLevelWitness.bound_affinePairShiftEndpointSum_tau
    {theta B C : ℝ} {X₀ : ℕ} (hw : PrimeLevelWitness theta B C X₀)
    {H : Finset ℕ} {A : H → ℕ} {D : Finset (H → ℕ)}
    {R W N : ℕ}
    (hH : H.Nonempty) (hW : Squarefree W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hApos : ∀ h, 0 < A h)
    (hAprimes : CoversCoefficientPrimes A W)
    (hupper : ∀ h : H, X₀ ≤ 2 * A h * N)
    (hlower : ∀ h : H, X₀ ≤ A h * N)
    (hcutUpper : ∀ h : H,
      A h * (W * R * R) ≤ modulusCutoff theta (2 * A h * N))
    (hcutLower : ∀ h : H,
      A h * (W * R * R) ≤ modulusCutoff theta (A h * N))
    (hsizeUpper : ∀ h : H, A h * (W * R * R) ≤ 2 * A h * N + 1)
    (hsizeLower : ∀ h : H, A h * (W * R * R) ≤ A h * N + 1) :
    (∑ i ∈ compatiblePairShiftIndex H D,
      (maxProgressionDiscrepancy (2 * A i.2 * N)
          (A i.2 * compatiblePairShiftModulus H W i) +
        maxProgressionDiscrepancy (A i.2 * N)
          (A i.2 * compatiblePairShiftModulus H W i))) ≤
      (∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C B
        (2 * A h * N)) +
      ∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C B
        (A h * N) := by
  let I := compatiblePairShiftIndex H D
  let Q := W * R * R
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW.ne_zero
  have hSQ := compatiblePairShiftModulus_image_subset_radius hWpos hD
  have hcutImage (h : H) (x : ℕ) (hcutx : A h * Q ≤ modulusCutoff theta x) :
      ((compatiblePairShiftIndex H D).image
        (compatiblePairShiftModulus H W)).image (fun q => A h * q) ⊆
          Finset.Icc 1 (modulusCutoff theta x) := by
    intro m hm
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
    have hqData := Finset.mem_Icc.mp (hSQ hq)
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos (hApos h) (zero_lt_one.trans_le hqData.1),
        (Nat.mul_le_mul_left (A h) hqData.2).trans hcutx⟩
  have hupperBound (h : H) :
      (∑ i ∈ I, maxProgressionDiscrepancy (2 * A h * N)
          (A h * compatiblePairShiftModulus H W i)) ≤
        tauIndexedEndpointEnvelope H Q C B (2 * A h * N) := by
    simpa [tauIndexedEndpointEnvelope, I, Q] using
      sum_affineMaxDiscrepancy_comp_le_tauEnvelope hw (hupper h) hH hW hD
        (hApos h) (hAprimes h) (hsizeUpper h)
        (hcutImage h _ (hcutUpper h))
  have hlowerBound (h : H) :
      (∑ i ∈ I, maxProgressionDiscrepancy (A h * N)
          (A h * compatiblePairShiftModulus H W i)) ≤
        tauIndexedEndpointEnvelope H Q C B (A h * N) := by
    simpa [tauIndexedEndpointEnvelope, I, Q] using
      sum_affineMaxDiscrepancy_comp_le_tauEnvelope hw (hlower h) hH hW hD
        (hApos h) (hAprimes h) (hsizeLower h)
        (hcutImage h _ (hcutLower h))
  have hpointUpper (i : (((H → ℕ) × (H → ℕ)) × H)) (hi : i ∈ I) :
      maxProgressionDiscrepancy (2 * A i.2 * N)
          (A i.2 * compatiblePairShiftModulus H W i) ≤
        ∑ h : H, maxProgressionDiscrepancy (2 * A h * N)
          (A h * compatiblePairShiftModulus H W i) := by
    exact Finset.single_le_sum (fun h hh => maxProgressionDiscrepancy_nonneg
      (2 * A h * N) (A h * compatiblePairShiftModulus H W i))
      (Finset.mem_univ i.2)
  have hpointLower (i : (((H → ℕ) × (H → ℕ)) × H)) (hi : i ∈ I) :
      maxProgressionDiscrepancy (A i.2 * N)
          (A i.2 * compatiblePairShiftModulus H W i) ≤
        ∑ h : H, maxProgressionDiscrepancy (A h * N)
          (A h * compatiblePairShiftModulus H W i) := by
    exact Finset.single_le_sum (fun h hh => maxProgressionDiscrepancy_nonneg
      (A h * N) (A h * compatiblePairShiftModulus H W i))
      (Finset.mem_univ i.2)
  calc
    _ ≤ (∑ i ∈ I, ∑ h : H,
          maxProgressionDiscrepancy (2 * A h * N)
            (A h * compatiblePairShiftModulus H W i)) +
        ∑ i ∈ I, ∑ h : H,
          maxProgressionDiscrepancy (A h * N)
            (A h * compatiblePairShiftModulus H W i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      exact add_le_add (hpointUpper i hi) (hpointLower i hi)
    _ = (∑ h : H, ∑ i ∈ I,
          maxProgressionDiscrepancy (2 * A h * N)
            (A h * compatiblePairShiftModulus H W i)) +
        ∑ h : H, ∑ i ∈ I,
          maxProgressionDiscrepancy (A h * N)
            (A h * compatiblePairShiftModulus H W i) := by
      congr 1 <;> rw [Finset.sum_comm]
    _ ≤ _ := add_le_add
      (Finset.sum_le_sum fun h hh => hupperBound h)
      (Finset.sum_le_sum fun h hh => hlowerBound h)

theorem PrimeLevelWitness.bound_abs_affineRestrictedS2Error_tau
    {theta B C : ℝ} {X₀ : ℕ} (hw : PrimeLevelWitness theta B C X₀)
    {H : Finset ℕ} {A : H → ℕ} {D : Finset (H → ℕ)}
    {R W N : ℕ} {lambda : (H → ℕ) → ℝ} {L : ℝ}
    (hH : H.Nonempty) (hW : Squarefree W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hApos : ∀ h, 0 < A h)
    (hAprimes : CoversCoefficientPrimes A W)
    (hcoverage : CoversAffineDifferencePrimes A W)
    (hN : 0 < N) (hL : 0 ≤ L)
    (hbound : ∀ d ∈ D, |lambda d| ≤ L)
    (hupper : ∀ h : H, X₀ ≤ 2 * A h * N)
    (hlower : ∀ h : H, X₀ ≤ A h * N)
    (hcutUpper : ∀ h : H,
      A h * (W * R * R) ≤ modulusCutoff theta (2 * A h * N))
    (hcutLower : ∀ h : H,
      A h * (W * R * R) ≤ modulusCutoff theta (A h * N))
    (hsizeUpper : ∀ h : H, A h * (W * R * R) ≤ 2 * A h * N + 1)
    (hsizeLower : ∀ h : H, A h * (W * R * R) ≤ A h * N + 1) :
    |affineRestrictedS2Error H A D R W N lambda hD| ≤
      L ^ 2 *
        ((∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C B
          (2 * A h * N)) +
        ∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C B
          (A h * N)) := by
  calc
    _ ≤ affineRestrictedS2AbsoluteError H A D R W N lambda hD :=
      abs_affineRestrictedS2Error_le_absoluteError hD
    _ = affineCompatiblePairShiftWeightedErrorSum H A D R W N lambda hD :=
      affineRestrictedS2AbsoluteError_eq_weightedErrorSum hD
    _ ≤ L ^ 2 * (∑ i ∈ compatiblePairShiftIndex H D,
        (maxProgressionDiscrepancy (2 * A i.2 * N)
            (A i.2 * compatiblePairShiftModulus H W i) +
          maxProgressionDiscrepancy (A i.2 * N)
            (A i.2 * compatiblePairShiftModulus H W i))) :=
      affineWeightedErrorSum_le_endpointDiscrepancies hApos
        (Nat.pos_of_ne_zero hW.ne_zero) hAprimes hcoverage hD hN hL hbound
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (bound_affinePairShiftEndpointSum_tau hw hH hW hD hApos hAprimes
        hupper hlower hcutUpper hcutLower hsizeUpper hsizeLower)
      (sq_nonneg L)

end

end Erdos372.AffineMaynard
