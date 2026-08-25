import Util.Bernays.SquareEulerCorrection
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# The finite ramified-prime correction
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

noncomputable def ramifiedPrimes (N : ℕ) : Finset Nat.Primes :=
  N.primeFactors.subtype Nat.Prime

theorem mem_ramifiedPrimes_iff {N : ℕ} (hN : N ≠ 0) (p : Nat.Primes) :
    p ∈ ramifiedPrimes N ↔ (p : ℕ) ∣ N := by
  constructor
  · intro hp
    have hm : (p : ℕ) ∈ N.primeFactors := Finset.mem_subtype.mp hp
    exact (Nat.mem_primeFactors.mp hm).2.1
  · intro hp
    exact Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨p.property, hp, hN⟩)

theorem char_prime_eq_zero_iff {N : ℕ} (χ : DirichletCharacter ℂ N) (p : Nat.Primes) :
    χ p = 0 ↔ (p : ℕ) ∣ N := by
  rw [MulChar.apply_eq_zero_iff, ZMod.isUnit_iff_coprime,
    p.property.coprime_iff_not_dvd, not_not]

theorem primeInversePower_pos (p : Nat.Primes) (s : ℝ) :
    0 < ((((p : ℕ) : ℝ) ^ s)⁻¹) :=
  inv_pos.mpr (rpow_pos_of_pos (by exact_mod_cast p.property.pos) s)

theorem primeInversePower_lt_one (p : Nat.Primes) {s : ℝ} (hs : 0 < s) :
    ((((p : ℕ) : ℝ) ^ s)⁻¹) < 1 :=
  inv_lt_one_of_one_lt₀ (one_lt_rpow (by exact_mod_cast p.property.one_lt) hs)

noncomputable def ramifiedCorrection (R : Finset Nat.Primes) (s : ℝ) : ℝ :=
  ∏ p ∈ R, (1 - ((((p : ℕ) : ℝ) ^ (max (3 / 4) s))⁻¹))⁻¹

theorem ramifiedCorrection_pos (R : Finset Nat.Primes) (s : ℝ) :
    0 < ramifiedCorrection R s := by
  apply Finset.prod_pos
  intro p _
  exact inv_pos.mpr (sub_pos.mpr (primeInversePower_lt_one p
    (lt_of_lt_of_le (by norm_num) (le_max_left (3 / 4 : ℝ) s))))

theorem continuous_ramifiedCorrection (R : Finset Nat.Primes) :
    Continuous (ramifiedCorrection R) := by
  apply continuous_finsetProd
  intro p _
  have hp₀ : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  have hpow : Continuous (fun s : ℝ => (((p : ℕ) : ℝ) ^ max (3 / 4) s)⁻¹) :=
    ((continuous_const_rpow hp₀.ne').comp (continuous_const.max continuous_id)).inv₀
      (fun _ => (rpow_pos_of_pos hp₀ _).ne')
  exact (continuous_const.sub hpow).inv₀ (fun s =>
    (sub_pos.mpr (primeInversePower_lt_one p
      (lt_of_lt_of_le (by norm_num) (le_max_left (3 / 4 : ℝ) s)))).ne')

theorem ramifiedCorrection_hasProd (R : Finset Nat.Primes) {s : ℝ} (hs : 3 / 4 ≤ s) :
    HasProd (fun p : Nat.Primes =>
      if p ∈ R then (1 - ((((p : ℕ) : ℝ) ^ s)⁻¹))⁻¹ else 1)
      (ramifiedCorrection R s) := by
  have h := hasProd_prod_of_ne_finset_one
    (L := SummationFilter.unconditional Nat.Primes) (s := R) (f := fun p : Nat.Primes =>
      if p ∈ R then (1 - ((((p : ℕ) : ℝ) ^ s)⁻¹))⁻¹ else 1)
    (by intro p hp; exact if_neg hp)
  simpa only [ramifiedCorrection, max_eq_right hs, Finset.prod_ite_mem, Finset.inter_self] using h

end Bernays
