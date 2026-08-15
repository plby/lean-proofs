/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.AdditiveCharacterOrthogonality
import ErdosProblems.Erdos387.ReciprocalEnergy
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Modular reciprocal energy

BNPZ Lemma 9.2 groups tuples by a sum of modular inverses.  This file
connects that modular phase to the integral numerator used in
`ReciprocalEnergy.lean`.  In particular, equality of phases is proved
equivalent to an ordinary natural-number congruence after denominators are
cleared; cancellation uses the explicit coprimality hypotheses.
-/

namespace Erdos387

open scoped BigOperators

section ModularReciprocalNumerator

variable {q : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sum of the inverses of the selected coordinates in `ZMod q`. -/
noncomputable def modularReciprocalSum
    (q : ℕ) (A : Finset ι) (s : ι → ℕ) : ZMod q :=
  ∑ i ∈ A, (s i : ZMod q)⁻¹

theorem cast_product_mul_inv_eq_erased_product
    (s : ι → ℕ) {i : ι} (hcop : (s i).Coprime q) :
    ((∏ j : ι, s j : ℕ) : ZMod q) * (s i : ZMod q)⁻¹ =
      ((∏ j ∈ (Finset.univ : Finset ι).erase i, s j : ℕ) : ZMod q) := by
  have hprod : (∏ j : ι, s j) =
      s i * ∏ j ∈ (Finset.univ : Finset ι).erase i, s j := by
    exact (Finset.mul_prod_erase (Finset.univ : Finset ι) s
      (Finset.mem_univ i)).symm
  rw [hprod]
  push_cast
  calc
    ((s i : ZMod q) *
        (∏ j ∈ (Finset.univ : Finset ι).erase i, (s j : ZMod q))) *
          (s i : ZMod q)⁻¹ =
        ((s i : ZMod q) * (s i : ZMod q)⁻¹) *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, (s j : ZMod q) := by
      ring
    _ = ∏ j ∈ (Finset.univ : Finset ι).erase i, (s j : ZMod q) := by
      rw [ZMod.coe_mul_inv_eq_one _ hcop, one_mul]

/-- Clearing modular inverses gives the cast of the same natural numerator
as clearing rational reciprocals. -/
theorem cast_product_mul_modularReciprocalSum_eq
    (A : Finset ι) (s : ι → ℕ) (hcop : ∀ i, (s i).Coprime q) :
    ((∏ j : ι, s j : ℕ) : ZMod q) * modularReciprocalSum q A s =
      (reciprocalNumerator A s : ZMod q) := by
  simp_rw [modularReciprocalSum, Finset.mul_sum]
  unfold reciprocalNumerator
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  simpa using cast_product_mul_inv_eq_erased_product s (hcop i)

omit [DecidableEq ι] in theorem cast_product_isUnit
    (s : ι → ℕ) (hcop : ∀ i, (s i).Coprime q) :
    IsUnit (((∏ i : ι, s i : ℕ) : ZMod q)) := by
  apply (ZMod.isUnit_iff_coprime _ _).2
  exact Nat.coprime_fintype_prod_left_iff.mpr hcop

/-- Equality of modular reciprocal sums is exactly congruence of the
cleared natural numerators. -/
theorem modularReciprocalSum_eq_iff_cast_numerator_eq
    (A B : Finset ι) (s : ι → ℕ) (hcop : ∀ i, (s i).Coprime q) :
    modularReciprocalSum q A s = modularReciprocalSum q B s ↔
      (reciprocalNumerator A s : ZMod q) =
        (reciprocalNumerator B s : ZMod q) := by
  constructor
  · intro hphase
    calc
      (reciprocalNumerator A s : ZMod q) =
          ((∏ i : ι, s i : ℕ) : ZMod q) *
            modularReciprocalSum q A s :=
        (cast_product_mul_modularReciprocalSum_eq A s hcop).symm
      _ = ((∏ i : ι, s i : ℕ) : ZMod q) *
            modularReciprocalSum q B s := by rw [hphase]
      _ = (reciprocalNumerator B s : ZMod q) :=
        cast_product_mul_modularReciprocalSum_eq B s hcop
  · intro hnum
    apply (cast_product_isUnit s hcop).mul_left_cancel
    rw [cast_product_mul_modularReciprocalSum_eq A s hcop,
      cast_product_mul_modularReciprocalSum_eq B s hcop, hnum]

/-- Natural-congruence form of the modular reciprocal phase identity. -/
theorem modularReciprocalSum_eq_iff_numerator_modEq
    (A B : Finset ι) (s : ι → ℕ) (hcop : ∀ i, (s i).Coprime q) :
    modularReciprocalSum q A s = modularReciprocalSum q B s ↔
      Nat.ModEq q (reciprocalNumerator A s)
        (reciprocalNumerator B s) := by
  rw [modularReciprocalSum_eq_iff_cast_numerator_eq A B s hcop,
    ZMod.natCast_eq_natCast_iff]

/-- An exact rational reciprocal identity is contained in every modular
reciprocal identity for moduli coprime to all coordinates. -/
theorem modularReciprocalSum_eq_of_reciprocalSum_eq
    (A B : Finset ι) (s : ι → ℕ) (hcop : ∀ i, (s i).Coprime q)
    (hnum : reciprocalNumerator A s = reciprocalNumerator B s) :
    modularReciprocalSum q A s = modularReciprocalSum q B s := by
  apply (modularReciprocalSum_eq_iff_numerator_modEq A B s hcop).2
  rw [hnum]

/-- If the modular phases agree but the cleared numerators are not equal,
the modulus divides their (signed) difference. -/
theorem modulus_dvd_numerator_difference
    (A B : Finset ι) (s : ι → ℕ) (hcop : ∀ i, (s i).Coprime q)
    (hphase : modularReciprocalSum q A s =
      modularReciprocalSum q B s) :
    (q : ℤ) ∣ (reciprocalNumerator B s : ℤ) -
      (reciprocalNumerator A s : ℤ) := by
  exact Nat.modEq_iff_dvd.mp
    ((modularReciprocalSum_eq_iff_numerator_modEq A B s hcop).1 hphase)

section FiniteModularEnergy

/-- Tuples drawn from `U` whose two complementary reciprocal sums agree
modulo `q`. -/
noncomputable def modularReciprocalEnergyTuples
    (q : ℕ) (A : Finset ι) (U : Finset ℕ) : Finset (ι → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : ι => U).filter fun s =>
    modularReciprocalSum q A s =
      modularReciprocalSum q ((Finset.univ : Finset ι) \ A) s

/-- The modular reciprocal solutions for which the cleared numerator is
not identically zero over the integers. -/
noncomputable def offDiagonalModularReciprocalTuples
    (q : ℕ) (A : Finset ι) (U : Finset ℕ) : Finset (ι → ℕ) := by
  classical
  exact (modularReciprocalEnergyTuples q A U).filter fun s =>
    reciprocalNumerator A s ≠
      reciprocalNumerator ((Finset.univ : Finset ι) \ A) s

theorem modularReciprocalEnergyTuple_coordinate_mem
    {A : Finset ι} {U : Finset ℕ} {s : ι → ℕ}
    (hs : s ∈ modularReciprocalEnergyTuples q A U) (i : ι) :
    s i ∈ U := by
  classical
  rw [modularReciprocalEnergyTuples, Finset.mem_filter] at hs
  exact Fintype.mem_piFinset.mp hs.1 i

theorem modularReciprocalEnergyTuple_phase
    {A : Finset ι} {U : Finset ℕ} {s : ι → ℕ}
    (hs : s ∈ modularReciprocalEnergyTuples q A U) :
    modularReciprocalSum q A s =
      modularReciprocalSum q ((Finset.univ : Finset ι) \ A) s := by
  classical
  rw [modularReciprocalEnergyTuples, Finset.mem_filter] at hs
  exact hs.2

/-- For positive coordinates, equality of the rational reciprocal sums is
equivalent to equality of their cleared natural numerators. -/
theorem reciprocalSum_eq_iff_numerator_eq
    (A B : Finset ι) (s : ι → ℕ) (hpos : ∀ i, 0 < s i) :
    reciprocalSum A s = reciprocalSum B s ↔
      reciprocalNumerator A s = reciprocalNumerator B s := by
  constructor
  · intro hsum
    have hmul := congrArg
      (fun x : ℚ => ((∏ i : ι, s i : ℕ) : ℚ) * x) hsum
    rw [product_mul_reciprocalSum_eq A s hpos,
      product_mul_reciprocalSum_eq B s hpos] at hmul
    exact_mod_cast hmul
  · intro hnum
    have hprod : ((∏ i : ι, s i : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (Finset.prod_pos fun i _hi => hpos i).ne'
    apply mul_left_cancel₀ hprod
    rw [product_mul_reciprocalSum_eq A s hpos,
      product_mul_reciprocalSum_eq B s hpos, hnum]

/-- Every modular solution is either an exact rational-energy solution or
has a genuinely nonzero cleared numerator difference. -/
theorem modularReciprocalEnergyTuples_subset_diagonal_union_offDiagonal
    (q : ℕ) (A : Finset ι) (U : Finset ℕ)
    (hUpos : ∀ u ∈ U, 0 < u) :
    modularReciprocalEnergyTuples q A U ⊆
      reciprocalEnergyTuples A U ∪
        offDiagonalModularReciprocalTuples q A U := by
  classical
  intro s hs
  have hcoord : ∀ i, s i ∈ U := fun i =>
    modularReciprocalEnergyTuple_coordinate_mem hs i
  have hpos : ∀ i, 0 < s i := fun i => hUpos (s i) (hcoord i)
  by_cases hnum : reciprocalNumerator A s =
      reciprocalNumerator ((Finset.univ : Finset ι) \ A) s
  · apply Finset.mem_union_left
    rw [reciprocalEnergyTuples, Finset.mem_filter]
    exact ⟨Fintype.mem_piFinset.mpr hcoord,
      (reciprocalSum_eq_iff_numerator_eq A
        ((Finset.univ : Finset ι) \ A) s hpos).2 hnum⟩
  · apply Finset.mem_union_right
    rw [offDiagonalModularReciprocalTuples, Finset.mem_filter]
    exact ⟨hs, hnum⟩

theorem modularReciprocalEnergyTuples_card_le_diagonal_add_offDiagonal
    (q : ℕ) (A : Finset ι) (U : Finset ℕ)
    (hUpos : ∀ u ∈ U, 0 < u) :
    (modularReciprocalEnergyTuples q A U).card ≤
      (reciprocalEnergyTuples A U).card +
        (offDiagonalModularReciprocalTuples q A U).card := by
  calc
    (modularReciprocalEnergyTuples q A U).card ≤
        (reciprocalEnergyTuples A U ∪
          offDiagonalModularReciprocalTuples q A U).card :=
      Finset.card_le_card
        (modularReciprocalEnergyTuples_subset_diagonal_union_offDiagonal
          q A U hUpos)
    _ ≤ (reciprocalEnergyTuples A U).card +
        (offDiagonalModularReciprocalTuples q A U).card :=
      Finset.card_union_le _ _

/-- In every off-diagonal modular solution the modulus divides the signed
cleared-numerator difference. -/
theorem offDiagonalModularReciprocalTuple_modulus_dvd
    (A : Finset ι) (U : Finset ℕ)
    (hUcop : ∀ u ∈ U, u.Coprime q)
    {s : ι → ℕ}
    (hs : s ∈ offDiagonalModularReciprocalTuples q A U) :
    (q : ℤ) ∣
      (reciprocalNumerator ((Finset.univ : Finset ι) \ A) s : ℤ) -
        (reciprocalNumerator A s : ℤ) := by
  classical
  rw [offDiagonalModularReciprocalTuples, Finset.mem_filter] at hs
  have hcop : ∀ i, (s i).Coprime q := fun i =>
    hUcop (s i) (modularReciprocalEnergyTuple_coordinate_mem hs.1 i)
  exact modulus_dvd_numerator_difference A
    ((Finset.univ : Finset ι) \ A) s hcop
      (modularReciprocalEnergyTuple_phase hs.1)

end FiniteModularEnergy

end ModularReciprocalNumerator

end Erdos387
