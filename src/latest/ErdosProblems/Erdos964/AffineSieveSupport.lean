import ErdosProblems.Erdos964.AffineSieveCongruences

/-!
# The finite support conditions for affine sieve weights

Pre-sieving the leading coefficients and pairwise determinants guarantees
the same compatible divisor-pair support as in the shift sieve.
-/

namespace Erdos964

open BoundedGaps.Maynard

def CoversAffineLeadingPrimes {ι : Type*} (A : ι → ℕ) (W : ℕ) : Prop :=
  ∀ i p, p.Prime → p ∣ A i → p ∣ W

def CoversAffineDeterminantPrimes {ι : Type*} (A B : ι → ℕ) (W : ℕ) : Prop :=
  ∀ i j, i ≠ j → ∀ p, p.Prime → p ∣ Nat.dist (A i * B j) (A j * B i) → p ∣ W

def affineDivisorTupleCondition {ι : Type*} (A B : ι → ℕ) (n : ℕ) (d : ι → ℕ) : Prop :=
  ∀ i, d i ∣ A i * n + B i

def affineDivisorPairCondition {ι : Type*} (A B : ι → ℕ) (n : ℕ)
    (d e : ι → ℕ) : Prop :=
  affineDivisorTupleCondition A B n d ∧ affineDivisorTupleCondition A B n e

theorem coprime_affine_leading_of_cover {ι : Type*} {A : ι → ℕ} {W m : ℕ}
    (hcover : CoversAffineLeadingPrimes A W) (hWm : W.Coprime m) (i : ι) :
    (A i).Coprime m := by
  by_contra hnot
  obtain ⟨p, hp, hpA, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hpW := hcover i p hp hpA
  exact (hp.coprime_iff_not_dvd.mp (hWm.coprime_dvd_left hpW)) hpm

theorem common_affine_divisor_dvd_determinant (a b c d n p : ℕ)
    (hab : p ∣ a * n + b) (hcd : p ∣ c * n + d) :
    p ∣ Nat.dist (a * d) (c * b) := by
  have hleft : p ∣ a * c * n + a * d := by
    have h := dvd_mul_of_dvd_right hcd a
    have heq : a * (c * n + d) = a * c * n + a * d := by ring
    exact heq ▸ h
  have hright : p ∣ a * c * n + c * b := by
    have h := dvd_mul_of_dvd_right hab c
    have heq : c * (a * n + b) = a * c * n + c * b := by ring
    exact heq ▸ h
  have hdist : p ∣ Nat.dist (a * c * n + a * d) (a * c * n + c * b) := by
    exact dvd_add (Nat.dvd_sub hleft hright) (Nat.dvd_sub hright hleft)
  simpa only [Nat.dist_add_add_left] using hdist

theorem affine_pair_implies_cross_coprime
    {H : Finset ℕ} {A B : H → ℕ} {R W n : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) (he : IsMaynardDivisorTuple H R W e)
    (hcover : CoversAffineDeterminantPrimes A B W)
    (hpair : affineDivisorPairCondition A B n d e) : IsCrossCoordinateCoprime H d e := by
  have hcop (f g : H → ℕ) (hf : IsMaynardDivisorTuple H R W f)
      (hfg : affineDivisorPairCondition A B n f g) (i j : H) (hij : i ≠ j) :
      (f i).Coprime (g j) := by
    by_contra hnot
    obtain ⟨p, hp, hpi, hpj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hdet := common_affine_divisor_dvd_determinant (A i) (B i) (A j) (B j) n p
      (hpi.trans (hfg.1 i)) (hpj.trans (hfg.2 j))
    have hpW := hcover i j hij p hp hdet
    exact (hp.coprime_iff_not_dvd.mp
      ((hf.coordinate_coprime_W i).coprime_dvd_left hpi)) hpW
  intro i j hij
  exact ⟨hcop d e hd hpair i j hij, hcop e d he ⟨hpair.2, hpair.1⟩ i j hij⟩

theorem affineDivisorPairCondition_iff_lcm {H : Finset ℕ} (A B : H → ℕ)
    (n : ℕ) (d e : H → ℕ) :
    affineDivisorPairCondition A B n d e ↔
      ∀ i, divisorTupleLcm H d e i ∣ A i * n + B i := by
  constructor
  · intro h i
    exact Nat.lcm_dvd (h.1 i) (h.2 i)
  · intro h
    exact ⟨fun i => (Nat.lcm_dvd_iff.mp (h i)).1,
      fun i => (Nat.lcm_dvd_iff.mp (h i)).2⟩

open scoped Classical in
theorem affine_divisor_pair_count_error_le_one
    {H : Finset ℕ} (A B : H → ℕ) {R W : ℕ} (v N : ℕ) (d e : H → ℕ)
    (hW : 0 < W) (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e) (hcross : IsCrossCoordinateCoprime H d e)
    (hcover : CoversAffineLeadingPrimes A W) :
    |(((Finset.Ico N (2 * N)).filter (fun n =>
        n ≡ v [MOD W] ∧ affineDivisorPairCondition A B n d e)).card : ℝ) -
      (N : ℝ) / divisorPairModulus H W d e| ≤ 1 := by
  classical
  have hcompat := isMaynardDivisorTuple_pair_lcm_compatible hd he hcross
  have hcount := affine_sieve_count_error_le_one A B (divisorTupleLcm H d e)
    H.attach.toList W v N hW hcompat
    (fun i _ => divisorTupleLcm_pos_of_isMaynard hd he i)
    (fun i hi => coprime_affine_leading_of_cover hcover (hcompat.1 i hi) i)
  simpa [affineDivisorPairCondition_iff_lcm, divisorPairModulus] using hcount

end Erdos964
