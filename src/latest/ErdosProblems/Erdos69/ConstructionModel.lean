import ErdosProblems.Erdos69.SmallPrimeFourier
import ErdosProblems.Erdos69.FourierProduct
import ErdosProblems.Erdos69.PrimeDecomposition
import ErdosProblems.Erdos69.ParameterPrimeMass

/-! # The finite prime model for the explicit construction -/

open scoped BigOperators

namespace Erdos69.Elementary

abbrev ConstructionPrime (m : ℕ) := ↥(freePrimes (constructionModulus m) (smallPrimeCutoff m))

theorem constructionPrime_prime (m : ℕ) (p : ConstructionPrime m) : p.val.Prime :=
  (Nat.mem_primesLE.mp (Finset.mem_filter.mp p.property).1).2

theorem constructionPrime_pos (m : ℕ) (p : ConstructionPrime m) : 0 < p.val :=
  (constructionPrime_prime m p).pos

theorem constructionPrime_not_dvd (m : ℕ) (p : ConstructionPrime m) :
    ¬p.val ∣ constructionModulus m := (Finset.mem_filter.mp p.property).2

theorem constructionPrime_coprime (m : ℕ) (p : ConstructionPrime m) :
    (constructionModulus m).Coprime p.val :=
  ((constructionPrime_prime m p).coprime_iff_not_dvd.mpr (constructionPrime_not_dvd m p)).symm

theorem constructionPrime_pairwise (m : ℕ) :
    Pairwise (fun p r : ConstructionPrime m ↦ p.val.Coprime r.val) := by
  intro p r hpr
  apply (constructionPrime_prime m p).coprime_iff_not_dvd.mpr
  intro hd
  have heq : p.val = r.val := (Nat.dvd_prime (constructionPrime_prime m r)).mp hd |>.resolve_left
    (constructionPrime_prime m p).ne_one
  exact hpr (Subtype.ext heq)

theorem constructionPrime_distinct_residues (m : ℕ) (p : ConstructionPrime m) :
    ∀ r s : ConstructionShift m, r.val ≡ s.val [MOD p.val] → r = s :=
  construction_shifts_distinct_mod_prime m p.val (constructionPrime_prime m p)
    (constructionPrime_not_dvd m p)

theorem constructionShift_card_le_prime (m : ℕ) (p : ConstructionPrime m) :
    Fintype.card (ConstructionShift m) ≤ p.val :=
  card_le_of_distinct_residues _ (constructionPrime_pos m p) _
    (constructionPrime_distinct_residues m p)

noncomputable def constructionPrimeLaw (m : ℕ) :
    FiniteLaw (ConstructionPrime m → Option (ConstructionShift m)) :=
  FiniteLaw.independentProduct (fun p ↦ FiniteLaw.categorical (ConstructionShift m) p.val
    (constructionPrime_pos m p) (constructionShift_card_le_prime m p))

noncomputable def constructionModelValue (q : ℝ) (m : ℕ)
    (x : ConstructionPrime m → Option (ConstructionShift m)) : ℝ :=
  ∑ p, FiniteLaw.optionalValue (constructionCoefficient m q) (x p)

noncomputable def constructionSmallValue (q : ℝ) (m t : ℕ) : ℝ :=
  ∑ p : ConstructionPrime m, ∑ r : ConstructionShift m,
    constructionCoefficient m q r *
      (if p.val ∣ constructionPoint m t + r.val then (1 : ℝ) else 0)

theorem constructionPrime_reciprocal_le (m : ℕ) :
    (∑ p : ConstructionPrime m, (1 : ℝ) / p.val) ≤ primeReciprocalSum (smallPrimeCutoff m) := by
  rw [Finset.sum_coe_sort (freePrimes (constructionModulus m) (smallPrimeCutoff m))
    (fun p : ℕ ↦ (1 : ℝ) / p)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ ↦ by positivity)

theorem construction_goodPrime_sum (m : ℕ) :
    (∑ p ∈ (Finset.univ : Finset (ConstructionPrime m)).filter
        (fun p ↦ excludedPrimeCutoff m < p.val), (1 : ℝ) / p.val) =
      ∑ p ∈ goodPrimes (constructionModulus m) (excludedPrimeCutoff m) (smallPrimeCutoff m),
        (1 : ℝ) / p := by
  rw [Finset.sum_filter,
    Finset.sum_coe_sort (freePrimes (constructionModulus m) (smallPrimeCutoff m))
      (fun p ↦ if excludedPrimeCutoff m < p then (1 : ℝ) / p else 0), ← Finset.sum_filter]
  have heq : (freePrimes (constructionModulus m) (smallPrimeCutoff m)).filter
      (fun p ↦ excludedPrimeCutoff m < p) =
        goodPrimes (constructionModulus m) (excludedPrimeCutoff m) (smallPrimeCutoff m) := by
    ext p
    simp [freePrimes, goodPrimes, and_left_comm, and_comm, and_assoc]
  rw [heq]

theorem constructionModel_fourier_le {m : ℕ} (hm : 0 < m) (q : ℝ)
    (hfirst : |firstCoefficient q m| ≤ 1 / 2) :
    ‖(constructionPrimeLaw m).complexMean (fun x ↦ fourierPhase (constructionModelValue q m x))‖ ≤
      Real.exp (-4 * firstCoefficient q m ^ 2 *
        ∑ p ∈ goodPrimes (constructionModulus m) (excludedPrimeCutoff m) (smallPrimeCutoff m),
          (1 : ℝ) / p) := by
  classical
  let S := (Finset.univ : Finset (ConstructionPrime m)).filter
    (fun p ↦ excludedPrimeCutoff m < p.val)
  have hS (p : ConstructionPrime m) (hp : p ∈ S) :
      2 * Fintype.card (ConstructionShift m) ≤ p.val :=
    (twice_shift_card_le_excluded hm).trans (Finset.mem_filter.mp hp).2.le
  have hc : |constructionCoefficient m q (constructionFirstShift m)| ≤ 1 / 2 := by
    simpa only [constructionCoefficient_first, firstCoefficient] using hfirst
  have h := FiniteLaw.categorical_product_fourier_le (fun p : ConstructionPrime m ↦ p.val)
    (constructionPrime_pos m) (constructionShift_card_le_prime m) S hS
    (constructionCoefficient m q) (constructionFirstShift m) hc
  rw [constructionCoefficient_first, construction_goodPrime_sum] at h
  exact h

noncomputable def constructionLaw (m : ℕ) : FiniteLaw (Fin (progressionLength m)) :=
  FiniteLaw.uniform _ (progressionLength_pos m)

noncomputable def smallCharacteristic (q : ℝ) (m : ℕ) : ℂ :=
  (constructionLaw m).complexMean (fun t ↦ fourierPhase (constructionSmallValue q m t.val))

noncomputable def modelCharacteristic (q : ℝ) (m : ℕ) : ℂ :=
  (constructionPrimeLaw m).complexMean (fun x ↦ fourierPhase (constructionModelValue q m x))

theorem constructionPrime_card_le (m : ℕ) :
    Fintype.card (ConstructionPrime m) ≤ smallPrimeCutoff m := by
  have hsubset : freePrimes (constructionModulus m) (smallPrimeCutoff m) ⊆
      Finset.Icc 1 (smallPrimeCutoff m) := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_Icc.mpr ⟨hp'.2.one_le, hp'.1⟩
  have hcard := Finset.card_le_card hsubset
  simpa only [Fintype.card_coe, Nat.card_Icc, Nat.add_sub_cancel] using hcard

theorem firstCoefficient_abs_le_mass (q : ℝ) (m : ℕ) :
    |firstCoefficient q m| ≤ coefficientMassBound q m := by
  have hsingle : |constructionCoefficient m q (constructionFirstShift m)| ≤
      ∑ r : ConstructionShift m, |constructionCoefficient m q r| :=
    Finset.single_le_sum (fun r _ ↦ abs_nonneg (constructionCoefficient m q r))
      (Finset.mem_univ (constructionFirstShift m))
  rw [constructionCoefficient_first] at hsingle
  exact hsingle.trans (constructionCoefficient_mass_le m q)

theorem construction_fourier_transfer_raw {m : ℕ} (hm : 0 < m) (q : ℝ)
    (hε : coefficientMassBound q m ≤ 1)
    (hsmall : 4 * Real.pi * coefficientMassBound q m ≤ 1) :
    ‖smallCharacteristic q m - modelCharacteristic q m‖ ≤
      ((smallPrimeCutoff m : ℝ) ^ momentOrder m / progressionLength m) * (1 + momentOrder m) *
        Real.exp (2 * Real.pi) +
        4 * momentOrder m *
          Real.exp ((4 * Real.pi) ^ 2 * coefficientMassBound q m ^ 2 *
            ∑ p : ConstructionPrime m, (1 : ℝ) / p.val) * (1 / 2 : ℝ) ^ momentOrder m := by
  have hsize : (Fintype.card (ConstructionPrime m) : ℝ) * coefficientMassBound q m ≤
      smallPrimeCutoff m := by
    calc
      _ ≤ (Fintype.card (ConstructionPrime m) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hε (by positivity)
      _ ≤ _ := by simpa using (show (Fintype.card (ConstructionPrime m) : ℝ) ≤ smallPrimeCutoff m by
          exact_mod_cast constructionPrime_card_le m)
  exact FiniteLaw.affine_fourier_transfer (fun p : ConstructionPrime m ↦ p.val)
    (constructionPrime_pos m) (constructionPrime_pairwise m)
    (constructionModulus m) (constructionBase m) (constructionPrime_coprime m)
    (fun r : ConstructionShift m ↦ r.val) (constructionPrime_distinct_residues m)
    (constructionShift_card_le_prime m) (constructionCoefficient m q)
    (constructionCoefficient_zero_sum hm q) (coefficientMassBound q m) (smallPrimeCutoff m)
    (constructionCoefficient_mass_le m q) hsmall
    (by have h := smallPrimeCutoff_ge_two m; exact_mod_cast (show 1 ≤ smallPrimeCutoff m by omega))
    hsize (progressionLength m) (progressionLength_pos m) (momentOrder m)
    (momentOrder_pos m) (momentOrder_even m)

end Erdos69.Elementary
