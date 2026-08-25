import ErdosProblems.Erdos6.BFTResidue
import Util.MaynardBFT.ProgressionModulus

/-!
# Isolating a tuple in a prescribed arithmetic progression

The isolation primes exceed both the span and `q`.  We preserve the existing
BFT congruences at primes not dividing `q`, and use CRT to impose the full
modulus `q`, including its prime powers.
-/

namespace MaynardBFT

open Erdos6.Maynard
open scoped BigOperators

theorem exists_progression_isolating_residue
    {H : Finset ℕ} {q b M D : ℕ} (hq : 0 < q) (hb : b.Coprime q)
    (hH : BoundedGaps.IsAdmissible H)
    (hdiv : ∀ h ∈ H, q ∣ h) (hHM : ∀ h ∈ H, h ≤ M) (hqM : q ≤ M)
    (hD : ∀ a ∈ badOffsets H M, assignedPrime M a ≤ D) :
    ∃ v : ℕ, v ≡ b [MOD q] ∧
      (∀ h ∈ H, Nat.Coprime (v + h) (q * primorial D)) ∧
      ∀ a ∈ badOffsets H M, assignedPrime M a ∣ v + a := by
  classical
  obtain ⟨v₀, _, hv₀, ha₀⟩ := exists_bftPreSieveResidueClass hH hHM hD
  let P := D.primesLE.filter fun p => ¬p ∣ q
  let W := ∏ p ∈ P, p
  have hqW : q.Coprime W := by
    apply Nat.Coprime.prod_right
    intro p hp
    have hdata := Finset.mem_filter.mp hp
    exact ((Nat.prime_of_mem_primesLE hdata.1).coprime_iff_not_dvd.mpr hdata.2).symm
  let v : ℕ := Nat.chineseRemainder hqW b v₀
  have hvq : v ≡ b [MOD q] := (Nat.chineseRemainder hqW b v₀).property.1
  have hvW : v ≡ v₀ [MOD W] := (Nat.chineseRemainder hqW b v₀).property.2
  have hvp (p : ℕ) (hp : p.Prime) (hpD : p ≤ D) (hpq : ¬p ∣ q) :
      v ≡ v₀ [MOD p] := by
    apply hvW.of_dvd
    exact Finset.dvd_prod_of_mem id
      (Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpD, hp⟩, hpq⟩)
  have hcq (h : ℕ) (hh : h ∈ H) : Nat.Coprime (v + h) q := by
    have hmod : v + h ≡ b [MOD q] := by
      simpa only [Nat.add_zero] using hvq.add (Nat.modEq_zero_iff_dvd.mpr (hdiv h hh))
    exact hmod.gcd_eq.trans hb
  refine ⟨v, hvq, ?_, ?_⟩
  · intro h hh
    apply Nat.coprime_mul_iff_right.mpr
    refine ⟨hcq h hh, ?_⟩
    apply Nat.coprime_of_dvd'
    intro p hp hpd hpW
    by_cases hpq : p ∣ q
    · simpa only [(hcq h hh).gcd_eq_one] using Nat.dvd_gcd hpd hpq
    · have hpD := hp.dvd_primorial_iff.mp hpW
      have hmod := (hvp p hp hpD hpq).add_right h
      have hpd₀ : p ∣ v₀ + h := (hmod.dvd_iff (dvd_refl p)).mp hpd
      simpa only [(hv₀ h hh).gcd_eq_one] using Nat.dvd_gcd hpd₀ hpW
  · intro a ha
    let p := assignedPrime M a
    have hp : p.Prime := assignedPrime_prime M a
    have hpq : ¬p ∣ q := by
      intro hpq
      have hp_le_q := Nat.le_of_dvd hq hpq
      have hpM : M < p := assignedPrime_gt M a
      omega
    have hmod := (hvp p hp (hD a ha) hpq).add_right a
    exact (hmod.dvd_iff (dvd_refl p)).mpr (ha₀ a ha)

end MaynardBFT
