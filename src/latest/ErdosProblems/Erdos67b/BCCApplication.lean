import ErdosProblems.Erdos67b.BCCPrefix
import ErdosProblems.Erdos67b.BCCDecomposition

/-!
# The actual full-divisor BCC application

This file instantiates the generalized BCC Fourier argument with the divisor
decomposition of a completely multiplicative unit-circle-valued function.
The good residue classes are translated by `+ 1`, exactly as required by
`fullDivisorPrefix_eq_primeExtensionPrefix_Icc`.
-/

open scoped BigOperators ZMod
open Finset

namespace Erdos67b

noncomputable section

theorem card_shiftedCyclicGoodResidues (q k H : ℕ) [NeZero q] :
    (shiftedCyclicGoodResidues q k H).card =
      (cyclicGoodResidues q k H).card := by
  rw [shiftedCyclicGoodResidues, Finset.card_map]

theorem sum_shiftedCyclicGoodResidues
    {q k H : ℕ} [NeZero q] {E : Type*} [AddCommMonoid E]
    (F : ZMod (q ^ k) → E) :
    (∑ b ∈ shiftedCyclicGoodResidues q k H, F b) =
      ∑ a ∈ cyclicGoodResidues q k H, F (a + 1) := by
  rw [shiftedCyclicGoodResidues, Finset.sum_map]
  rfl

/-- The generalized BCC upper bound specialized to the actual full divisor
family and its unit coefficients.  Its good-family hypothesis retains the
`a + 1` shift from the exact gcd decomposition. -/
theorem fullDivisor_bcc_normalized_diagonal_le
    {q k H : ℕ} [NeZero q] (hk : 0 < k) (hH : 0 < H) (hq : 1 < q)
    (z : PrimeAssignment) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (selected : Finset ℕ)
    (hselected : selected ⊆ (q ^ (k - 1)).divisors)
    (hdH : ∀ d ∈ selected, 2 * d ≤ H)
    (B : ℝ)
    (hgood :
      (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ cyclicGoodResidues q k H,
              Complex.normSq
                (∑ d ∈ (q ^ (k - 1)).divisors,
                  (primeExtension z d : ℂ) *
                    scaledCharacterPrefix χ d L (a + 1)) ≤ B) :
    (1 / ((q ^ k : ℕ) : ℝ)) *
        ∑ d ∈ selected,
          (d : ℝ) *
            (((q ^ k / (q * d) : ℕ) : ℝ) * (q.totient : ℝ)) ≤
      8 *
        (B +
          (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
              ((2 ^ k : ℕ) : ℝ)) * ((2 * H : ℕ) : ℝ) ^ 2) := by
  classical
  let full : Finset ℕ := (q ^ (k - 1)).divisors
  let t : ℕ → ℕ := fun d ↦ q ^ k / (q * d)
  let good : Finset (ZMod (q ^ k)) := shiftedCyclicGoodResidues q k H
  let delta : ℝ :=
    ((2 * H * q.primeFactors.card : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ)
  let R : ℝ := ((2 * H : ℕ) : ℝ) ^ 2
  letI : NeZero (q ^ k) := ⟨pow_ne_zero k (NeZero.ne q)⟩
  have hfull0 : q ^ (k - 1) ≠ 0 := pow_ne_zero _ (NeZero.ne q)
  have hd (d : ℕ) (hdmem : d ∈ full) : NeZero d := by
    have hddiv : d ∣ q ^ (k - 1) := by
      simpa [full] using Nat.dvd_of_mem_divisors hdmem
    exact ⟨Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hddiv
      (pow_pos (NeZero.pos q) _))⟩
  have ht (d : ℕ) (hdmem : d ∈ full) : NeZero (t d) := by
    letI : NeZero d := hd d hdmem
    apply neZero_pow_div_q_mul hk
    simpa [full] using Nat.dvd_of_mem_divisors hdmem
  have hN (d : ℕ) (hdmem : d ∈ full) :
      q ^ k = t d * (q * d) := by
    apply pow_eq_div_q_mul_mul_q_mul hk
    simpa [full] using Nat.dvd_of_mem_divisors hdmem
  have hsmooth (d : ℕ) (hdmem : d ∈ full) : d ∣ q ^ (k - 1) := by
    simpa [full] using Nat.dvd_of_mem_divisors hdmem
  have hc (d : ℕ) (_hdmem : d ∈ full) :
      Complex.normSq (primeExtension z d : ℂ) = 1 :=
    normSq_primeExtension_coe z d
  have hcardBase :
      (((Finset.univ \ cyclicGoodResidues q k H).card : ℕ) : ℝ) ≤
        ((q ^ k : ℕ) : ℝ) * delta := by
    have hcomplement :
        (Finset.univ \ cyclicGoodResidues q k H).card =
          (cyclicBadResidues q k H).card := by
      congr 1
      ext a
      simp [cyclicGoodResidues]
    have hbadNat := card_cyclicBadResidues_le_twoPow q k H
    have hbadCast :
        (((cyclicBadResidues q k H).card : ℕ) : ℝ) ≤
          (((2 * H) * q.primeFactors.card * (q ^ k / 2 ^ k) : ℕ) : ℝ) := by
      exact_mod_cast hbadNat
    have hquot :
        (((q ^ k / 2 ^ k : ℕ) : ℕ) : ℝ) ≤
          ((q ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ) :=
      Nat.cast_div_le
    rw [hcomplement]
    calc
      (((cyclicBadResidues q k H).card : ℕ) : ℝ) ≤
          (((2 * H) * q.primeFactors.card * (q ^ k / 2 ^ k) : ℕ) : ℝ) :=
        hbadCast
      _ = (((2 * H * q.primeFactors.card : ℕ) : ℝ) *
            (((q ^ k / 2 ^ k : ℕ) : ℕ) : ℝ)) := by norm_num
      _ ≤ (((2 * H * q.primeFactors.card : ℕ) : ℝ) *
            (((q ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ))) := by
        gcongr
      _ = ((q ^ k : ℕ) : ℝ) * delta := by
        dsimp only [delta]
        ring
  have hcard :
      (((Finset.univ \ good).card : ℕ) : ℝ) ≤
        ((q ^ k : ℕ) : ℝ) * delta := by
    rw [show (Finset.univ \ good).card =
        (Finset.univ \ cyclicGoodResidues q k H).card by
      simpa only [good] using card_compl_shiftedCyclicGoodResidues q k H]
    exact hcardBase
  have hgood' :
      (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good,
              Complex.normSq
                (∑ d ∈ full,
                  (primeExtension z d : ℂ) *
                    scaledCharacterPrefix χ d L a) ≤ B := by
    simpa only [good, full, sum_shiftedCyclicGoodResidues] using hgood
  have hbad : ∀ L ∈ Finset.Ioc H (2 * H), ∀ a ∉ good,
      Complex.normSq
        (∑ d ∈ full,
          (primeExtension z d : ℂ) * scaledCharacterPrefix χ d L a) ≤ R := by
    intro L hL a _ha
    have hLle : L ≤ 2 * H := (Finset.mem_Ioc.mp hL).2
    calc
      Complex.normSq
          (∑ d ∈ full,
            (primeExtension z d : ℂ) * scaledCharacterPrefix χ d L a) ≤
          (L : ℝ) ^ 2 := by
        simpa only [full] using
          normSq_fullDivisor_scaledCharacterPrefix_le z χ hq a
      _ ≤ R := by
        dsimp only [R]
        have hLleR : (L : ℝ) ≤ ((2 * H : ℕ) : ℝ) := by
          exact_mod_cast hLle
        nlinarith [show (0 : ℝ) ≤ L by positivity]
  have hmain := bcc_full_family_normalized_diagonal_le_of_good hH
    selected full (by simpa only [full] using hselected) χ hχ
    (fun d ↦ (primeExtension z d : ℂ)) id t hc hd ht hdH hN
    (fun i hi j hj hij ↦ by
      letI : NeZero (t i) := ht i hi
      letI : NeZero (t j) := ht j hj
      exact smoothFrequencyLayer_disjoint_of_smooth_complements
        (hN i hi) (hN j hj) (hsmooth i hi) (hsmooth j hj) hij)
    good B R delta (by positivity) hcard hgood' hbad
  simpa only [full, t, delta, R, id_eq] using hmain

/-- The same bound with its hypothesis stated directly for the original
multiplicative discrepancy prefixes.  The proof uses the exact gcd
decomposition on every good residue and keeps the required `a + 1` spatial
translation visible in the intermediate theorem above. -/
theorem fullDivisor_bcc_normalized_diagonal_le_of_discrepancy
    {q k H : ℕ} [NeZero q] (hk : 0 < k) (hH : 0 < H) (hq : 1 < q)
    (z : PrimeAssignment) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hagree : AgreesWithCharacterAway z χ)
    (selected : Finset ℕ)
    (hselected : selected ⊆ (q ^ (k - 1)).divisors)
    (hdH : ∀ d ∈ selected, 2 * d ≤ H)
    (B : ℝ)
    (hdiscrepancy :
      (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ cyclicGoodResidues q k H,
              Complex.normSq
                (∑ m ∈ Finset.Icc 1 L,
                  (primeExtension z
                    (a + (m : ZMod (q ^ k))).val : ℂ)) ≤ B) :
    (1 / ((q ^ k : ℕ) : ℝ)) *
        ∑ d ∈ selected,
          (d : ℝ) *
            (((q ^ k / (q * d) : ℕ) : ℝ) * (q.totient : ℝ)) ≤
      8 *
        (B +
          (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
              ((2 ^ k : ℕ) : ℝ)) * ((2 * H : ℕ) : ℝ) ^ 2) := by
  apply fullDivisor_bcc_normalized_diagonal_le hk hH hq z χ hχ
    selected hselected hdH B
  have hsum :
      (∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ cyclicGoodResidues q k H,
            Complex.normSq
              (∑ d ∈ (q ^ (k - 1)).divisors,
                (primeExtension z d : ℂ) *
                  scaledCharacterPrefix χ d L (a + 1))) =
        ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ cyclicGoodResidues q k H,
            Complex.normSq
              (∑ m ∈ Finset.Icc 1 L,
                (primeExtension z
                  (a + (m : ZMod (q ^ k))).val : ℂ)) := by
    apply Finset.sum_congr rfl
    intro L hL
    apply Finset.sum_congr rfl
    intro a ha
    rw [fullDivisorPrefix_eq_primeExtensionPrefix_Icc z χ hagree hq ha
      (Finset.mem_Ioc.mp hL).2]
  rw [hsum]
  exact hdiscrepancy

/-- Explicit cardinal consequence for the actual modified-character divisor
family.  This is the finite endpoint used in the Section 4 contradiction. -/
theorem fullDivisor_bcc_selected_card_le_of_discrepancy
    {q k H : ℕ} [NeZero q] (hk : 0 < k) (hH : 0 < H) (hq : 1 < q)
    (z : PrimeAssignment) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hagree : AgreesWithCharacterAway z χ)
    (selected : Finset ℕ)
    (hselected : selected ⊆ (q ^ (k - 1)).divisors)
    (hdH : ∀ d ∈ selected, 2 * d ≤ H)
    (B : ℝ)
    (hdiscrepancy :
      (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ cyclicGoodResidues q k H,
              Complex.normSq
                (∑ m ∈ Finset.Icc 1 L,
                  (primeExtension z
                    (a + (m : ZMod (q ^ k))).val : ℂ)) ≤ B) :
    (selected.card : ℝ) ≤
      8 * (q : ℝ) *
        (B +
          (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
              ((2 ^ k : ℕ) : ℝ)) * ((2 * H : ℕ) : ℝ) ^ 2) := by
  classical
  let t : ℕ → ℕ := fun d ↦ q ^ k / (q * d)
  let X : ℝ :=
    B + (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
      ((2 ^ k : ℕ) : ℝ)) * ((2 * H : ℕ) : ℝ) ^ 2
  have hd (d : ℕ) (hdmem : d ∈ selected) : NeZero d := by
    have hddiv : d ∣ q ^ (k - 1) :=
      Nat.dvd_of_mem_divisors (hselected hdmem)
    exact ⟨Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hddiv
      (pow_pos (NeZero.pos q) _))⟩
  have ht (d : ℕ) (hdmem : d ∈ selected) : NeZero (t d) := by
    letI : NeZero d := hd d hdmem
    apply neZero_pow_div_q_mul hk
    exact Nat.dvd_of_mem_divisors (hselected hdmem)
  have hN (d : ℕ) (hdmem : d ∈ selected) :
      q ^ k = t d * (q * d) := by
    apply pow_eq_div_q_mul_mul_q_mul hk
    exact Nat.dvd_of_mem_divisors (hselected hdmem)
  have hdiag :
      (1 / ((q ^ k : ℕ) : ℝ)) *
          ∑ d ∈ selected,
            (d : ℝ) * ((t d : ℝ) * (q.totient : ℝ)) ≤ 8 * X := by
    simpa only [t, X] using
      fullDivisor_bcc_normalized_diagonal_le_of_discrepancy hk hH hq
        z χ hχ hagree selected hselected hdH B hdiscrepancy
  simpa only [X] using
    bcc_card_le_uniform_of_normalized_diagonal selected id t le_rfl
      hd ht hN X hdiag

/-- Contradiction form of the preceding explicit cardinal endpoint. -/
theorem fullDivisor_bcc_contradiction_of_discrepancy
    {q k H : ℕ} [NeZero q] (hk : 0 < k) (hH : 0 < H) (hq : 1 < q)
    (z : PrimeAssignment) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hagree : AgreesWithCharacterAway z χ)
    (selected : Finset ℕ)
    (hselected : selected ⊆ (q ^ (k - 1)).divisors)
    (hdH : ∀ d ∈ selected, 2 * d ≤ H)
    (B : ℝ)
    (hdiscrepancy :
      (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ cyclicGoodResidues q k H,
              Complex.normSq
                (∑ m ∈ Finset.Icc 1 L,
                  (primeExtension z
                    (a + (m : ZMod (q ^ k))).val : ℂ)) ≤ B)
    (hlarge :
      8 * (q : ℝ) *
          (B +
            (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
                ((2 ^ k : ℕ) : ℝ)) * ((2 * H : ℕ) : ℝ) ^ 2) <
        (selected.card : ℝ)) : False := by
  exact (not_lt_of_ge
    (fullDivisor_bcc_selected_card_le_of_discrepancy hk hH hq z χ hχ
      hagree selected hselected hdH B hdiscrepancy)) hlarge

end

end Erdos67b
