import ErdosProblems.Erdos248.PrimeProducts

/-!
# Tao--Teräväinen: lifting a prime event to a prime-power event

After a prime has been adjoined to the Maynard modulus, increasing its
exponent changes only the residue-class density. The divisor support and the
inverse Y-transform coefficients are unchanged because every supported tuple
is already coprime to that prime.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace TaoTeravainen

local instance modulusLiftDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Multiplying a modulus by a power of a prime already dividing it does not
change which integers are coprime to the modulus. -/
theorem coprime_mul_pow_iff_of_dvd {x W p a : ℕ} (hpW : p ∣ W) :
    Nat.Coprime x (W * p ^ a) ↔ Nat.Coprime x W := by
  constructor
  · intro h
    exact h.of_dvd_right (dvd_mul_right W (p ^ a))
  · intro h
    rw [Nat.coprime_mul_iff_right]
    exact ⟨h, (h.coprime_dvd_right hpW).pow_right a⟩

/-- The Maynard tuple predicate is unchanged when an already-present prime
is raised to a higher power in the modulus. -/
theorem isMaynardDivisorTuple_mul_pow_iff_of_dvd
    {H : Finset ℕ} {R W p a : ℕ} {d : H → ℕ} (hpW : p ∣ W) :
    IsMaynardDivisorTuple H R (W * p ^ a) d ↔
      IsMaynardDivisorTuple H R W d := by
  unfold IsMaynardDivisorTuple
  constructor
  · rintro ⟨hlt, hcop, hsq⟩
    exact ⟨hlt, (coprime_mul_pow_iff_of_dvd hpW).mp hcop, hsq⟩
  · rintro ⟨hlt, hcop, hsq⟩
    exact ⟨hlt, (coprime_mul_pow_iff_of_dvd hpW).mpr hcop, hsq⟩

/-- A supported Y-variable remains supported after an already-present prime
is raised to a higher power in the modulus. -/
theorem isSupportedMaynardY_mul_pow_of_dvd
    {H : Finset ℕ} {R W p a : ℕ} {y : (H → ℕ) → ℝ}
    (hpW : p ∣ W) (hy : IsSupportedMaynardY H R W y) :
    IsSupportedMaynardY H R (W * p ^ a) y := by
  intro r hyr
  exact (isMaynardDivisorTuple_mul_pow_iff_of_dvd hpW).mpr (hy r hyr)

/-- The finite tuple support is unchanged under the same modulus lift. -/
theorem maynardDivisorTupleSupport_mul_pow_eq_of_dvd
    (H : Finset ℕ) (R W p a : ℕ) (hpW : p ∣ W) :
    maynardDivisorTupleSupport H R (W * p ^ a) =
      maynardDivisorTupleSupport H R W := by
  classical
  ext d
  simp only [mem_maynardDivisorTupleSupport_iff]
  constructor
  · rintro ⟨hbox, hd⟩
    exact ⟨hbox, (isMaynardDivisorTuple_mul_pow_iff_of_dvd hpW).mp hd⟩
  · rintro ⟨hbox, hd⟩
    exact ⟨hbox, (isMaynardDivisorTuple_mul_pow_iff_of_dvd hpW).mpr hd⟩

/-- The inverse Y-transform coefficient is unchanged under the same modulus
lift. -/
theorem maynardCoefficientFromY_mul_pow_eq_of_dvd
    {H : Finset ℕ} (R W p a : ℕ) (hpW : p ∣ W)
    (y : (H → ℕ) → ℝ) (d : H → ℕ) :
    maynardCoefficientFromY H R (W * p ^ a) y d =
      maynardCoefficientFromY H R W y d := by
  classical
  unfold maynardCoefficientFromY
  by_cases hd : Nat.Coprime (divisorTupleProduct H d) W
  · rw [if_pos hd, if_pos ((coprime_mul_pow_iff_of_dvd hpW).mpr hd)]
  · rw [if_neg hd, if_neg (fun h =>
      hd ((coprime_mul_pow_iff_of_dvd hpW).mp h))]

/-- Rewriting a lifted from-Y weight leaves the divisor support and
coefficient function unchanged; only the outer residue modulus remains. -/
theorem fromYWeight_mul_pow_eq_preSieved_of_dvd
    {H : Finset ℕ} (R W p a v : ℕ) (hpW : p ∣ W)
    (y : (H → ℕ) → ℝ) :
    Erdos248.fromYWeight R (W * p ^ a) v y =
      preSievedSquareDivisorWeight H
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) v (W * p ^ a) := by
  funext n
  unfold Erdos248.fromYWeight
  rw [maynardDivisorTupleSupport_mul_pow_eq_of_dvd H R W p a hpW]
  have hcoeff :
      maynardCoefficientFromY H R (W * p ^ a) y =
        maynardCoefficientFromY H R W y := by
    funext d
    exact maynardCoefficientFromY_mul_pow_eq_of_dvd R W p a hpW y d
  rw [hcoeff]

/-- Restricting a from-Y weight by an event is the same as changing only its
outer residue class whenever the new congruence is exactly the old
congruence together with that event. -/
theorem indicator_fromYWeight_eq_preSieved_of_modEq_iff
    {H : Finset ℕ} {R W W' v v' n : ℕ}
    {y : (H → ℕ) → ℝ} {P : ℕ → Prop}
    (hres : ∀ m : ℕ, m ≡ v' [MOD W'] ↔ m ≡ v [MOD W] ∧ P m) :
    (if P n then Erdos248.fromYWeight R W v y n else 0) =
      preSievedSquareDivisorWeight H
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) v' W' n := by
  classical
  unfold Erdos248.fromYWeight preSievedSquareDivisorWeight
  by_cases hP : P n
  · by_cases hW : n ≡ v [MOD W]
    · rw [if_pos hP, if_pos hW, if_pos ((hres n).mpr ⟨hW, hP⟩)]
    · rw [if_pos hP, if_neg hW, if_neg]
      intro hnew
      exact hW ((hres n).mp hnew).1
  · rw [if_neg hP, if_neg]
    intro hnew
    exact hP ((hres n).mp hnew).2

end TaoTeravainen
