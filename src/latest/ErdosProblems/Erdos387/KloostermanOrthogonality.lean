/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.AdditiveCharacterOrthogonality
import Mathlib.Data.Nat.Totient

/-!
# Elementary mean-square identities for Kloosterman phases

The pointwise Weil estimate is deeper, but its surrounding mean-square
structure is pure finite Fourier analysis.  This file isolates the exact
identity available without any unproved character-sum input.
-/

namespace Erdos387

open scoped BigOperators

namespace Kloosterman

/-- An incomplete inverse-phase sum over an arbitrary finite family of unit
residues. -/
noncomputable def incompleteSum
    (q : ℕ) [NeZero q] (U : Finset (ZMod q))
    (weight : ZMod q → ℂ) (a b : ZMod q) : ℂ :=
  ∑ v ∈ U, weight v * ZMod.stdAddChar (a * v + b * v⁻¹)

theorem incompleteSum_eq_characterSum
    (q : ℕ) [NeZero q] (U : Finset (ZMod q))
    (weight : ZMod q → ℂ) (a b : ZMod q) :
    incompleteSum q U weight a b =
      AdditiveOrthogonality.characterSum U id
        (fun v => weight v * ZMod.stdAddChar (b * v⁻¹)) a := by
  classical
  unfold incompleteSum AdditiveOrthogonality.characterSum
  apply Finset.sum_congr rfl
  intro v _hv
  rw [AddChar.map_add_eq_mul]
  simp only [id_eq]
  ring

theorem equalPhasePairs_id_card_le
    (q : ℕ) (U : Finset (ZMod q)) :
    (AdditiveOrthogonality.equalPhasePairs U id).card ≤ U.card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro vw hvw
    change vw ∈ AdditiveOrthogonality.equalPhasePairs U id at hvw
    rw [AdditiveOrthogonality.equalPhasePairs, Finset.mem_filter,
      Finset.mem_product] at hvw
    exact hvw.1.1
  · intro vw hvw xy hxy heq
    change vw ∈ AdditiveOrthogonality.equalPhasePairs U id at hvw
    change xy ∈ AdditiveOrthogonality.equalPhasePairs U id at hxy
    rw [AdditiveOrthogonality.equalPhasePairs, Finset.mem_filter,
      Finset.mem_product] at hvw hxy
    simp only [id_eq] at hvw hxy
    apply Prod.ext heq
    calc
      vw.2 = vw.1 := hvw.2.symm
      _ = xy.1 := heq
      _ = xy.2 := hxy.2

/-- Complete mean square for an incomplete inverse sum.  Orthogonality in
the linear coefficient sees only the literal diagonal of `U`. -/
theorem sum_norm_incompleteSum_sq_le
    (q : ℕ) [NeZero q] (U : Finset (ZMod q))
    (weight : ZMod q → ℂ) (b : ZMod q)
    (hweight : ∀ v ∈ U, ‖weight v‖ ≤ 1) :
    (∑ a : ZMod q, ‖incompleteSum q U weight a b‖ ^ 2) ≤
      (q * U.card : ℕ) := by
  rw [show (∑ a : ZMod q, ‖incompleteSum q U weight a b‖ ^ 2) =
      ∑ a : ZMod q,
        ‖AdditiveOrthogonality.characterSum U id
          (fun v => weight v * ZMod.stdAddChar (b * v⁻¹)) a‖ ^ 2 by
    apply Finset.sum_congr rfl
    intro a _ha
    rw [incompleteSum_eq_characterSum]]
  have hmodified : ∀ v ∈ U,
      ‖weight v * ZMod.stdAddChar (b * v⁻¹)‖ ≤ 1 := by
    intro v hv
    rw [norm_mul, AddChar.norm_apply, mul_one]
    exact hweight v hv
  exact (AdditiveOrthogonality.sum_norm_characterSum_sq_le
    U id (fun v => weight v * ZMod.stdAddChar (b * v⁻¹)) hmodified).trans
      (by exact_mod_cast
        (Nat.mul_le_mul_left q (equalPhasePairs_id_card_le q U)))

/-- The inverse-phase coefficient, extended by zero away from the unit
residues. -/
noncomputable def coefficient
    (q : ℕ) [NeZero q] (b v : ZMod q) : ℂ :=
  if IsUnit v then ZMod.stdAddChar (b * v⁻¹) else 0

/-- A complete Kloosterman sum, expressed as the additive Fourier transform
of the inverse-phase coefficient. -/
noncomputable def sum
    (q : ℕ) [NeZero q] (a b : ZMod q) : ℂ :=
  AdditiveOrthogonality.stdAddCharFourierSum (coefficient q b) a

/-- Expanded complete sum over the unit residues (written as a zero-extended
sum over all residues). -/
theorem sum_eq_inverse_phase
    (q : ℕ) [NeZero q] (a b : ZMod q) :
    sum q a b =
      ∑ v : ZMod q,
        if IsUnit v then
          ZMod.stdAddChar (a * v + b * v⁻¹)
        else 0 := by
  classical
  unfold Kloosterman.sum AdditiveOrthogonality.stdAddCharFourierSum
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hv : IsUnit v
  · simp only [coefficient, if_pos hv]
    rw [AddChar.map_add_eq_mul]
    ring
  · simp [coefficient, hv]

theorem norm_coefficient_sq
    (q : ℕ) [NeZero q] (b v : ZMod q) :
    ‖coefficient q b v‖ ^ 2 = if IsUnit v then 1 else 0 := by
  by_cases hv : IsUnit v
  · simp [coefficient, hv, AddChar.norm_apply]
  · simp [coefficient, hv]

/-- The number of unit residues, written as a finite indicator sum. -/
theorem sum_isUnit_indicator
    (q : ℕ) [NeZero q] :
    (∑ v : ZMod q, if IsUnit v then (1 : ℝ) else 0) =
      Nat.totient q := by
  classical
  calc
    (∑ v : ZMod q, if IsUnit v then (1 : ℝ) else 0) =
        (((Finset.univ : Finset (ZMod q)).filter IsUnit).card : ℝ) := by
      simpa using
        (Finset.sum_boole (R := ℝ) IsUnit
          (Finset.univ : Finset (ZMod q)))
    _ = Fintype.card (ZMod q)ˣ := by
      have hfilter :
          (Finset.univ : Finset (ZMod q)).filter IsUnit =
            Finset.univ.map
              ⟨((↑) : (ZMod q)ˣ → ZMod q), Units.val_injective⟩ := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_map]
        constructor
        · intro hv
          exact ⟨hv.unit, by simp⟩
        · rintro ⟨u, rfl⟩
          exact u.isUnit
      rw [hfilter, Finset.card_map, Finset.card_univ]
    _ = Nat.totient q := by rw [ZMod.card_units_eq_totient]

/-- Exact second moment over the complete linear coefficient. -/
theorem sum_norm_sq
    (q : ℕ) [NeZero q] (b : ZMod q) :
    (∑ a : ZMod q, ‖sum q a b‖ ^ 2) =
      q * Nat.totient q := by
  change (∑ a : ZMod q,
    ‖AdditiveOrthogonality.stdAddCharFourierSum
      (coefficient q b) a‖ ^ 2) = _
  rw [AdditiveOrthogonality.sum_norm_stdAddCharFourierSum_sq]
  congr 1
  calc
    (∑ v : ZMod q, ‖coefficient q b v‖ ^ 2) =
        ∑ v : ZMod q, if IsUnit v then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact norm_coefficient_sq q b v
    _ = Nat.totient q := sum_isUnit_indicator q

/-- The elementary upper envelope following from the exact second moment. -/
theorem sum_norm_sq_le_square
    (q : ℕ) [NeZero q] (b : ZMod q) :
    (∑ a : ZMod q, ‖sum q a b‖ ^ 2) ≤ q ^ 2 := by
  rw [sum_norm_sq]
  exact_mod_cast (by
    simpa [pow_two] using Nat.mul_le_mul_left q (Nat.totient_le q))

/-- Cauchy--Schwarz combined with the exact complete second moment. -/
theorem norm_weighted_sum_sq_le
    (q : ℕ) [NeZero q] (b : ZMod q) (weight : ZMod q → ℂ) :
    ‖∑ a : ZMod q, weight a * sum q a b‖ ^ 2 ≤
      (∑ a : ZMod q, ‖weight a‖ ^ 2) *
        (q * Nat.totient q) := by
  have htriangle :
      ‖∑ a : ZMod q, weight a * sum q a b‖ ≤
        ∑ a : ZMod q, ‖weight a‖ * ‖sum q a b‖ := by
    calc
      ‖∑ a : ZMod q, weight a * sum q a b‖ ≤
          ∑ a : ZMod q, ‖weight a * sum q a b‖ := norm_sum_le _ _
      _ = ∑ a : ZMod q, ‖weight a‖ * ‖sum q a b‖ := by
        simp only [norm_mul]
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (ZMod q))
    (fun a => ‖weight a‖) (fun a => ‖sum q a b‖)
  calc
    ‖∑ a : ZMod q, weight a * sum q a b‖ ^ 2 ≤
        (∑ a : ZMod q, ‖weight a‖ * ‖sum q a b‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ (∑ a : ZMod q, ‖weight a‖ ^ 2) *
          (∑ a : ZMod q, ‖sum q a b‖ ^ 2) := by
      simpa using hcauchy
    _ = (∑ a : ZMod q, ‖weight a‖ ^ 2) *
          (q * Nat.totient q) := by rw [sum_norm_sq]

end Kloosterman

end Erdos387
