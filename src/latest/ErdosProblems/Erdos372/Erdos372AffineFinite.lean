import ErdosProblems.Erdos6.LargeExcess

/-!
# Finite affine Maynard sieve identities

The divisor support and coefficients are those of the bundled bounded-gaps
development; only the congruences defining the square weight are changed to
the positive affine forms `A h * n + 1`.
-/

namespace Erdos372.AffineMaynard

open scoped BigOperators
open Erdos6.Maynard
open BoundedGaps.Maynard

noncomputable section

local instance affineDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def CoversCoefficientPrimes {H : Finset ℕ} (A : H → ℕ) (W : ℕ) : Prop :=
  ∀ h : H, (A h).primeFactors ⊆ W.primeFactors

def CoversAffineDifferencePrimes {H : Finset ℕ}
    (A : H → ℕ) (W : ℕ) : Prop :=
  ∀ {a b : H}, a ≠ b → ∀ p, p.Prime →
    p ∣ Nat.dist (A a) (A b) → p ∣ W

def affineDivisorTupleCondition {H : Finset ℕ}
    (A : H → ℕ) (n : ℕ) (d : H → ℕ) : Prop :=
  ∀ h : H, d h ∣ A h * n + 1

def affineDivisorTuplePairCondition {H : Finset ℕ}
    (A : H → ℕ) (n : ℕ) (d e : H → ℕ) : Prop :=
  affineDivisorTupleCondition A n d ∧ affineDivisorTupleCondition A n e

def affineSquareDivisorWeight {H : Finset ℕ}
    (A : H → ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (n : ℕ) : ℝ :=
  (∑ d ∈ D.filter (affineDivisorTupleCondition A n), lambda d) ^ 2

def preSievedAffineSquareDivisorWeight {H : Finset ℕ}
    (A : H → ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (W n : ℕ) : ℝ :=
  if n ≡ 0 [MOD W] then affineSquareDivisorWeight A D lambda n else 0

theorem preSievedAffineSquareDivisorWeight_nonneg {H : Finset ℕ}
    (A : H → ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (W n : ℕ) :
    0 ≤ preSievedAffineSquareDivisorWeight A D lambda W n := by
  unfold preSievedAffineSquareDivisorWeight affineSquareDivisorWeight
  split_ifs <;> positivity

theorem affineSquareDivisorWeight_eq_double_sum {H : Finset ℕ}
    (A : H → ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (n : ℕ) :
    affineSquareDivisorWeight A D lambda n =
      ∑ d ∈ D.filter (affineDivisorTupleCondition A n),
        ∑ e ∈ D.filter (affineDivisorTupleCondition A n),
          lambda d * lambda e := by
  unfold affineSquareDivisorWeight
  simp only [pow_two, Finset.mul_sum, mul_comm]

theorem preSievedAffineSquareDivisorWeight_eq_pair_indicator
    {H : Finset ℕ} (A : H → ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (W n : ℕ) :
    preSievedAffineSquareDivisorWeight A D lambda W n =
      ∑ d ∈ D, ∑ e ∈ D,
        if n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e
        then lambda d * lambda e else 0 := by
  by_cases hres : n ≡ 0 [MOD W]
  · simp only [preSievedAffineSquareDivisorWeight, if_pos hres]
    rw [affineSquareDivisorWeight_eq_double_sum]
    simp_rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdc : affineDivisorTupleCondition A n d
    · simp [affineDivisorTuplePairCondition, hres, hdc]
    · simp [affineDivisorTuplePairCondition, hres, hdc]
  · simp [preSievedAffineSquareDivisorWeight, hres]

theorem exists_affine_residue {A m : ℕ} (hm : 0 < m)
    (hA : A.Coprime m) : ∃ r : ℕ, m ∣ A * r + 1 := by
  letI : NeZero m := ⟨hm.ne'⟩
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime A hA
  let z : ZMod m := -((u⁻¹ : (ZMod m)ˣ) : ZMod m)
  refine ⟨z.val, ?_⟩
  rw [← Nat.modEq_zero_iff_dvd]
  apply (ZMod.natCast_eq_natCast_iff (A * z.val + 1) 0 m).mp
  push_cast
  rw [ZMod.natCast_zmod_val]
  change ((u : ZMod m) * -((u⁻¹ : (ZMod m)ˣ) : ZMod m) + 1) = 0
  rw [mul_neg, ← Units.val_mul]
  simp

noncomputable def affineResidue (A m : ℕ) : ℕ :=
  if h : ∃ r : ℕ, m ∣ A * r + 1 then Classical.choose h else 0

theorem affineResidue_spec {A m : ℕ} (hm : 0 < m)
    (hA : A.Coprime m) : m ∣ A * affineResidue A m + 1 := by
  unfold affineResidue
  rw [dif_pos (exists_affine_residue hm hA)]
  exact Classical.choose_spec (exists_affine_residue hm hA)

theorem affine_modEq_residue_iff {A m n : ℕ} (hm : 0 < m)
    (hA : A.Coprime m) :
    n ≡ affineResidue A m [MOD m] ↔ m ∣ A * n + 1 := by
  let r := affineResidue A m
  have hr : m ∣ A * r + 1 := affineResidue_spec hm hA
  constructor
  · intro hn
    exact Nat.modEq_zero_iff_dvd.mp
      ((hn.mul_left A).add_right 1 |>.trans
        (Nat.modEq_zero_iff_dvd.mpr hr))
  · intro hn
    have hsumn : A * n + 1 ≡ 0 [MOD m] := Nat.modEq_zero_iff_dvd.mpr hn
    have hsumr : A * r + 1 ≡ 0 [MOD m] := Nat.modEq_zero_iff_dvd.mpr hr
    have hmul : A * n ≡ A * r [MOD m] :=
      Nat.ModEq.add_right_cancel' 1 (hsumn.trans hsumr.symm)
    letI : NeZero m := ⟨hm.ne'⟩
    let u : (ZMod m)ˣ := ZMod.unitOfCoprime A hA
    apply (ZMod.natCast_eq_natCast_iff n r m).mp
    have heq : (u : ZMod m) * (n : ZMod m) =
        (u : ZMod m) * (r : ZMod m) := by
      simpa [u] using
        (ZMod.natCast_eq_natCast_iff (A * n) (A * r) m).mpr hmul
    calc
      (n : ZMod m) = ((u⁻¹ : (ZMod m)ˣ) : ZMod m) *
          ((u : ZMod m) * (n : ZMod m)) := by
        rw [← mul_assoc, ← Units.val_mul]
        simp
      _ = ((u⁻¹ : (ZMod m)ˣ) : ZMod m) *
          ((u : ZMod m) * (r : ZMod m)) := congrArg _ heq
      _ = (r : ZMod m) := by
        rw [← mul_assoc, ← Units.val_mul]
        simp

theorem coefficient_coprime_lcm
    {H : Finset ℕ} {A : H → ℕ} {R W : ℕ} {d e : H → ℕ}
    (hApos : ∀ h, 0 < A h) (hAprimes : CoversCoefficientPrimes A W)
    (hWpos : 0 < W)
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e) (h : H) :
    (A h).Coprime (divisorTupleLcm H d e h) := by
  have hAdvd : A h ∣ W ^ (A h) :=
    (Nat.dvd_pow_self_iff (hApos h).ne' hWpos.ne').mpr (hAprimes h)
  have hWcop : W.Coprime (divisorTupleLcm H d e h) :=
    (isMaynardDivisorTuple_pair_lcm_compatible hd he hcross).1 h (by simp)
  exact Nat.Coprime.of_dvd_left hAdvd (hWcop.pow_left (A h))

def affineDivisorTupleResidue {H : Finset ℕ}
    (A : H → ℕ) (d e : H → ℕ) : H → ℕ :=
  fun h => affineResidue (A h) (divisorTupleLcm H d e h)

theorem affineDivisorTuplePairCondition_iff_lcm_dvd
    {H : Finset ℕ} (A : H → ℕ) (n : ℕ) (d e : H → ℕ) :
    affineDivisorTuplePairCondition A n d e ↔
      ∀ h : H, divisorTupleLcm H d e h ∣ A h * n + 1 := by
  constructor
  · rintro ⟨hd, he⟩ h
    exact Nat.lcm_dvd (hd h) (he h)
  · intro hlcm
    exact ⟨fun h => (Nat.lcm_dvd_iff.mp (hlcm h)).1,
      fun h => (Nat.lcm_dvd_iff.mp (hlcm h)).2⟩

theorem affineDivisorTuplePairCondition_iff_modEq_residue
    {H : Finset ℕ} {A : H → ℕ} {R W : ℕ} {d e : H → ℕ}
    (hApos : ∀ h, 0 < A h) (hAprimes : CoversCoefficientPrimes A W)
    (hW : 0 < W)
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e) (n : ℕ) :
    affineDivisorTuplePairCondition A n d e ↔
      ∀ h : H, n ≡ affineDivisorTupleResidue A d e h
        [MOD divisorTupleLcm H d e h] := by
  rw [affineDivisorTuplePairCondition_iff_lcm_dvd]
  constructor <;> intro h hcoord
  · exact (affine_modEq_residue_iff
      (divisorTupleLcm_pos_of_isMaynard hd he hcoord)
      (coefficient_coprime_lcm hApos hAprimes hW hd he hcross hcoord)).mpr
      (h hcoord)
  · exact (affine_modEq_residue_iff
      (divisorTupleLcm_pos_of_isMaynard hd he hcoord)
      (coefficient_coprime_lcm hApos hAprimes hW hd he hcross hcoord)).mp
      (h hcoord)

noncomputable def affineDivisorPairCrtResidue
    {H : Finset ℕ} (A : H → ℕ) (R W : ℕ) (d e : H → ℕ)
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e) : ℕ :=
  Nat.chineseRemainderOfList
    (preSievedResidue 0 (affineDivisorTupleResidue A d e))
    (preSievedModulus W (divisorTupleLcm H d e))
    (preSievedModulusList H.attach.toList)
    (preSievedModulusList_pairwise W (divisorTupleLcm H d e)
      H.attach.toList
      (isMaynardDivisorTuple_pair_lcm_compatible hd he hcross))

theorem modEq_affineDivisorPairCrtResidue_iff
    {H : Finset ℕ} {A : H → ℕ} {R W : ℕ} {d e : H → ℕ}
    (hApos : ∀ h, 0 < A h) (hAprimes : CoversCoefficientPrimes A W)
    (hW : 0 < W)
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e) (n : ℕ) :
    n ≡ affineDivisorPairCrtResidue A R W d e hd he hcross
        [MOD divisorPairModulus H W d e] ↔
      n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e := by
  rw [← preSievedDivisorPairModulus_eq]
  unfold affineDivisorPairCrtResidue
  rw [modEq_preSieved_crt_iff
    (affineDivisorTupleResidue A d e) (divisorTupleLcm H d e)
    H.attach.toList W 0 n
    (isMaynardDivisorTuple_pair_lcm_compatible hd he hcross)]
  apply and_congr_right
  intro _
  simpa using
    (affineDivisorTuplePairCondition_iff_modEq_residue
      hApos hAprimes hW hd he hcross n).symm

theorem isCrossCoordinateCoprime_of_affinePairCondition
    {H : Finset ℕ} {A : H → ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcoverage : CoversAffineDifferencePrimes A W) {n : ℕ}
    (hpair : affineDivisorTuplePairCondition A n d e) :
    IsCrossCoordinateCoprime H d e := by
  intro a b hab
  have difference_false (x y : H) (hxy : x ≠ y)
      {f g : H → ℕ}
      (hf : f x ∣ A x * n + 1) (hg : g y ∣ A y * n + 1)
      (hfcop : (f x).Coprime W)
      (p : ℕ) (hp : p.Prime) (hpf : p ∣ f x) (hpg : p ∣ g y) :
      False := by
    have hpx : p ∣ A x * n + 1 := hpf.trans hf
    have hpy : p ∣ A y * n + 1 := hpg.trans hg
    have hdist : p ∣ Nat.dist (A x) (A y) := by
      by_cases hle : A x ≤ A y
      · rw [Nat.dist_eq_sub_of_le hle]
        have hsub := Nat.dvd_sub
          (dvd_mul_of_dvd_right hpx (A y))
          (dvd_mul_of_dvd_right hpy (A x))
        have hleft : A y * (A x * n + 1) = A x * A y * n + A y := by ring
        have hright : A x * (A y * n + 1) = A x * A y * n + A x := by ring
        simpa [hleft, hright, Nat.add_sub_add_left] using hsub
      · have hle' : A y ≤ A x := le_of_not_ge hle
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hle']
        have hsub := Nat.dvd_sub
          (dvd_mul_of_dvd_right hpy (A x))
          (dvd_mul_of_dvd_right hpx (A y))
        have hleft : A x * (A y * n + 1) = A x * A y * n + A x := by ring
        have hright : A y * (A x * n + 1) = A x * A y * n + A y := by ring
        simpa [hleft, hright, Nat.add_sub_add_left] using hsub
    have hpW : p ∣ W := hcoverage hxy p hp hdist
    have hpcop : p.Coprime W := hfcop.coprime_dvd_left hpf
    exact (hp.coprime_iff_not_dvd.mp hpcop) hpW
  constructor
  · by_contra hnot
    obtain ⟨p, hp, hpd, hpe⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    exact difference_false a b hab (hpair.1 a) (hpair.2 b)
      (hd.coordinate_coprime_W a) p hp hpd hpe
  · by_contra hnot
    obtain ⟨p, hp, hpe, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    exact difference_false a b hab (hpair.2 a) (hpair.1 b)
      (he.coordinate_coprime_W a) p hp hpe hpd

def affineCompatibleDivisorPairCountError
    {H : Finset ℕ} (A : H → ℕ) (W N : ℕ) (d e : H → ℕ) : ℝ :=
  (((Finset.Ico N (2 * N)).filter (fun n =>
    n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e)).card : ℝ) -
      (N : ℝ) / divisorPairModulus H W d e

def affineCompatibleDivisorPairErrorSum
    (H : Finset ℕ) (A : H → ℕ) (D : Finset (H → ℕ))
    (W N : ℕ) (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D.filter (fun e => IsCrossCoordinateCoprime H d e),
    affineCompatibleDivisorPairCountError A W N d e * (lambda d * lambda e)

theorem affineCompatibleDivisorPairCountError_abs_le_one
    {H : Finset ℕ} {A : H → ℕ} {R W N : ℕ} {d e : H → ℕ}
    (hApos : ∀ h, 0 < A h) (hAprimes : CoversCoefficientPrimes A W)
    (hW : 0 < W) (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e) :
    |affineCompatibleDivisorPairCountError A W N d e| ≤ 1 := by
  let q := divisorPairModulus H W d e
  let r := affineDivisorPairCrtResidue A R W d e hd he hcross
  have hq : 0 < q := divisorPairModulus_pos hW hd he
  obtain ⟨err, herr, hcard⟩ := doublingIntervalModEq_card_decomposition N q r hq
  have hfilter :
      (Finset.Ico N (2 * N)).filter (fun n =>
        n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e) =
      (Finset.Ico N (2 * N)).filter (fun n => n ≡ r [MOD q]) := by
    ext n
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ =>
      (modEq_affineDivisorPairCrtResidue_iff
        hApos hAprimes hW hd he hcross n).symm)
  have herrEq : affineCompatibleDivisorPairCountError A W N d e = err := by
    unfold affineCompatibleDivisorPairCountError
    rw [hfilter, hcard]
    simp [q]
  rw [herrEq]
  exact herr

theorem abs_affineCompatibleDivisorPairErrorSum_le_coefficientMass
    {H : Finset ℕ} {A : H → ℕ} {D : Finset (H → ℕ)}
    {R W N : ℕ} {lambda : (H → ℕ) → ℝ}
    (hApos : ∀ h, 0 < A h) (hAprimes : CoversCoefficientPrimes A W)
    (hW : 0 < W) (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    |affineCompatibleDivisorPairErrorSum H A D W N lambda| ≤
      compatibleDivisorPairCoefficientMass H D lambda := by
  classical
  unfold affineCompatibleDivisorPairErrorSum
    compatibleDivisorPairCoefficientMass
  calc
    |∑ d ∈ D, ∑ e ∈ D.filter
        (fun e => IsCrossCoordinateCoprime H d e),
        affineCompatibleDivisorPairCountError A W N d e *
          (lambda d * lambda e)| ≤
        ∑ d ∈ D, |∑ e ∈ D.filter
          (fun e => IsCrossCoordinateCoprime H d e),
          affineCompatibleDivisorPairCountError A W N d e *
            (lambda d * lambda e)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, ∑ e ∈ D.filter
          (fun e => IsCrossCoordinateCoprime H d e),
          |affineCompatibleDivisorPairCountError A W N d e *
            (lambda d * lambda e)| := by
      apply Finset.sum_le_sum
      intro d hd
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, ∑ e ∈ D.filter
          (fun e => IsCrossCoordinateCoprime H d e),
          |lambda d * lambda e| := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨heD, hcross⟩ := Finset.mem_filter.mp he
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (affineCompatibleDivisorPairCountError_abs_le_one
          hApos hAprimes hW (hD d hd) (hD e heD) hcross)
        (abs_nonneg (lambda d * lambda e))

theorem sieveWeightSum_preSievedAffine_eq_main_add_error
    {H : Finset ℕ} {A : H → ℕ} {D : Finset (H → ℕ)}
    {R W N : ℕ} {lambda : (H → ℕ) → ℝ}
    (hApos : ∀ h, 0 < A h)
    (hAprimes : CoversCoefficientPrimes A W)
    (hcoverage : CoversAffineDifferencePrimes A W)
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    sieveWeightSum N (preSievedAffineSquareDivisorWeight A D lambda W) =
      compatibleDivisorPairMainSum H D W N lambda +
        affineCompatibleDivisorPairErrorSum H A D W N lambda := by
  classical
  unfold sieveWeightSum
  simp_rw [preSievedAffineSquareDivisorWeight_eq_pair_indicator]
  rw [Finset.sum_comm]
  have hrestrict :
      (∑ d ∈ D, ∑ e ∈ D, ∑ n ∈ Finset.Ico N (2 * N),
        if n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e
        then lambda d * lambda e else 0) =
      ∑ d ∈ D, ∑ e ∈ D.filter
          (fun e => IsCrossCoordinateCoprime H d e),
        (((Finset.Ico N (2 * N)).filter (fun n =>
          n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e)).card : ℝ) *
          (lambda d * lambda e) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hcross : IsCrossCoordinateCoprime H d e
    · simp only [hcross, if_true]
      rw [← Finset.sum_filter, Finset.sum_const]
      simp [nsmul_eq_mul]
    · have hzero :
          (∑ n ∈ Finset.Ico N (2 * N),
            if n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e
            then lambda d * lambda e else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        have hfalse :
            ¬(n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e) := by
          intro hcond
          exact hcross (isCrossCoordinateCoprime_of_affinePairCondition
            (hD d hd) (hD e he) hcoverage hcond.2)
        simp [hfalse]
      simp [hcross, hzero]
  calc
    (∑ d ∈ D, ∑ n ∈ Finset.Ico N (2 * N), ∑ e ∈ D,
        if n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e
        then lambda d * lambda e else 0) =
        ∑ d ∈ D, ∑ e ∈ D, ∑ n ∈ Finset.Ico N (2 * N),
          if n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e
          then lambda d * lambda e else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ d ∈ D, ∑ e ∈ D.filter
          (fun e => IsCrossCoordinateCoprime H d e),
        (((Finset.Ico N (2 * N)).filter (fun n =>
          n ≡ 0 [MOD W] ∧ affineDivisorTuplePairCondition A n d e)).card : ℝ) *
          (lambda d * lambda e) := hrestrict
    _ = compatibleDivisorPairMainSum H D W N lambda +
        affineCompatibleDivisorPairErrorSum H A D W N lambda := by
      unfold compatibleDivisorPairMainSum
        affineCompatibleDivisorPairErrorSum
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e he
      unfold affineCompatibleDivisorPairCountError
      ring

end

end Erdos372.AffineMaynard
