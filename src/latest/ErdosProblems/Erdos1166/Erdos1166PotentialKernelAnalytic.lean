import ErdosProblems.Erdos1166.Erdos1166PotentialKernel
import ErdosProblems.Erdos1166.Erdos1166HeatKernel

namespace Erdos1166.PotentialConvergence

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

open HeatKernel KilledGreen

noncomputable def evenShiftRatio (j a : ℕ) : ℝ :=
  ∏ t ∈ Finset.range a, ((j - t : ℕ) : ℝ) / ((j + t + 1 : ℕ) : ℝ)

theorem evenShiftRatio_zero (j : ℕ) : evenShiftRatio j 0 = 1 := by
  simp [evenShiftRatio]

theorem evenShiftRatio_succ (j a : ℕ) :
    evenShiftRatio j (a + 1) = evenShiftRatio j a *
      (((j - a : ℕ) : ℝ) / ((j + a + 1 : ℕ) : ℝ)) := by
  unfold evenShiftRatio
  rw [Finset.prod_range_succ]

theorem binomMass_even_shift {j a : ℕ} (ha : a ≤ j) :
    binomMass (2 * j) (j - a) =
      evenShiftRatio j a * binomMass (2 * j) j := by
  induction a with
  | zero => simp [evenShiftRatio]
  | succ a ih =>
      have haj : a ≤ j := by omega
      have hk : j - (a + 1) < 2 * j := by omega
      rw [binomMass_previous (2 * j) (j - (a + 1)) hk]
      have hnum : j - (a + 1) + 1 = j - a := by omega
      have hden : 2 * j - (j - (a + 1)) = j + a + 1 := by omega
      rw [hnum, hden, ih haj, evenShiftRatio_succ]
      ring

theorem evenShiftFactor_nonneg {j a : ℕ} (_ha : a ≤ j) :
    0 ≤ (((j - a : ℕ) : ℝ) / ((j + a + 1 : ℕ) : ℝ)) := by
  positivity

theorem evenShiftFactor_le_one {j a : ℕ} (ha : a ≤ j) :
    (((j - a : ℕ) : ℝ) / ((j + a + 1 : ℕ) : ℝ)) ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ) < ((j + a + 1 : ℕ) : ℝ))).2
  exact_mod_cast (show j - a ≤ j + a + 1 by omega)

theorem evenShiftRatio_nonneg {j a : ℕ} (ha : a ≤ j) :
    0 ≤ evenShiftRatio j a := by
  induction a with
  | zero => simp [evenShiftRatio]
  | succ a ih =>
      rw [evenShiftRatio_succ]
      exact mul_nonneg (ih (by omega)) (evenShiftFactor_nonneg (by omega))

theorem evenShiftRatio_le_one {j a : ℕ} (ha : a ≤ j) :
    evenShiftRatio j a ≤ 1 := by
  induction a with
  | zero => simp [evenShiftRatio]
  | succ a ih =>
      rw [evenShiftRatio_succ]
      exact mul_le_one₀ (ih (by omega)) (evenShiftFactor_nonneg (by omega))
        (evenShiftFactor_le_one (by omega))

theorem one_sub_evenShiftFactor_le {j a : ℕ} (hj : 0 < j) (ha : a ≤ j) :
    1 - (((j - a : ℕ) : ℝ) / ((j + a + 1 : ℕ) : ℝ)) ≤
      ((2 * a + 1 : ℕ) : ℝ) / (j : ℝ) := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hdenR : (0 : ℝ) < ((j + a + 1 : ℕ) : ℝ) := by positivity
  have hsub : ((j - a : ℕ) : ℝ) = (j : ℝ) - (a : ℝ) := by
    rw [Nat.cast_sub ha]
  rw [hsub]
  push_cast
  have heq : 1 - ((j : ℝ) - (a : ℝ)) / ((j : ℝ) + (a : ℝ) + 1) =
      (2 * (a : ℝ) + 1) / ((j : ℝ) + (a : ℝ) + 1) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀
    (show (0 : ℝ) < (j : ℝ) + (a : ℝ) + 1 by positivity) hjR).2
  nlinarith

theorem one_sub_evenShiftRatio_le {j a : ℕ} (hj : 0 < j) (ha : a ≤ j) :
    1 - evenShiftRatio j a ≤ (a : ℝ) ^ 2 / (j : ℝ) := by
  induction a with
  | zero => simp [evenShiftRatio]
  | succ a ih =>
      have haj : a ≤ j := by omega
      let R := evenShiftRatio j a
      let f : ℝ := ((j - a : ℕ) : ℝ) / ((j + a + 1 : ℕ) : ℝ)
      have hR0 : 0 ≤ R := by simpa [R] using evenShiftRatio_nonneg haj
      have hR1 : R ≤ 1 := by simpa [R] using evenShiftRatio_le_one haj
      have hf0 : 0 ≤ f := by simpa [f] using evenShiftFactor_nonneg haj
      have hf1 : f ≤ 1 := by simpa [f] using evenShiftFactor_le_one haj
      have hdf : 1 - f ≤ ((2 * a + 1 : ℕ) : ℝ) / (j : ℝ) := by
        simpa [f] using one_sub_evenShiftFactor_le hj haj
      have hih : 1 - R ≤ (a : ℝ) ^ 2 / (j : ℝ) := by
        simpa [R] using ih haj
      rw [evenShiftRatio_succ]
      change 1 - R * f ≤ ((a + 1 : ℕ) : ℝ) ^ 2 / (j : ℝ)
      have hjR : (0 : ℝ) < j := by exact_mod_cast hj
      have hmul : R * (1 - f) ≤ 1 * (((2 * a + 1 : ℕ) : ℝ) / (j : ℝ)) :=
        mul_le_mul hR1 hdf (sub_nonneg.mpr hf1) (by norm_num)
      have hih' : (1 - R) * (j : ℝ) ≤ (a : ℝ) ^ 2 :=
        (le_div_iff₀ hjR).mp hih
      have hmul' : (R * (1 - f)) * (j : ℝ) ≤ ((2 * a + 1 : ℕ) : ℝ) := by
        apply (le_div_iff₀ hjR).mp
        simpa using hmul
      apply (le_div_iff₀ hjR).2
      push_cast at hmul' ⊢
      nlinarith

theorem one_sub_evenShiftRatio_mul_le {j a b : ℕ}
    (hj : 0 < j) (ha : a ≤ j) (hb : b ≤ j) :
    1 - evenShiftRatio j a * evenShiftRatio j b ≤
      ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (j : ℝ) := by
  let A := evenShiftRatio j a
  let B := evenShiftRatio j b
  have hA0 : 0 ≤ A := by simpa [A] using evenShiftRatio_nonneg ha
  have hA1 : A ≤ 1 := by simpa [A] using evenShiftRatio_le_one ha
  have hB1 : B ≤ 1 := by simpa [B] using evenShiftRatio_le_one hb
  have hdA : 1 - A ≤ (a : ℝ) ^ 2 / (j : ℝ) := by
    simpa [A] using one_sub_evenShiftRatio_le hj ha
  have hdB : 1 - B ≤ (b : ℝ) ^ 2 / (j : ℝ) := by
    simpa [B] using one_sub_evenShiftRatio_le hj hb
  have hmul : A * (1 - B) ≤ 1 * ((b : ℝ) ^ 2 / (j : ℝ)) :=
    mul_le_mul hA1 hdB (sub_nonneg.mpr hB1) (by norm_num)
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hdA' : (1 - A) * (j : ℝ) ≤ (a : ℝ) ^ 2 :=
    (le_div_iff₀ hjR).mp hdA
  have hmul' : (A * (1 - B)) * (j : ℝ) ≤ (b : ℝ) ^ 2 := by
    apply (le_div_iff₀ hjR).mp
    simpa using hmul
  apply (le_div_iff₀ hjR).2
  change (1 - A * B) * (j : ℝ) ≤ _
  nlinarith

theorem returnProb_even_eq_binomMass_sq (j : ℕ) :
    returnProb (2 * j) = binomMass (2 * j) j ^ 2 := by
  rw [returnProb, return_real_even]
  unfold binomMass
  have hpow : (4 : ℝ) ^ (2 * j) = ((2 : ℝ) ^ (2 * j)) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hpow, div_pow]

theorem returnProb_even_le_inv (j : ℕ) (hj : 0 < j) :
    returnProb (2 * j) ≤ 1 / (j : ℝ) := by
  have h := return_real_le_two_div_succ (2 * j)
  change returnProb (2 * j) ≤ _ at h
  calc
    returnProb (2 * j) ≤ 2 / (((2 * j : ℕ) : ℝ) + 1) := h
    _ ≤ 1 / (j : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) (by exact_mod_cast hj)).2
      push_cast
      nlinarith

theorem even_endpoint_difference_nonneg {j a b : ℕ}
    (ha : a ≤ j) (hb : b ≤ j) :
    0 ≤ returnProb (2 * j) -
      binomMass (2 * j) (j - a) * binomMass (2 * j) (j - b) := by
  rw [returnProb_even_eq_binomMass_sq, binomMass_even_shift ha,
    binomMass_even_shift hb]
  have hA := evenShiftRatio_le_one ha
  have hB := evenShiftRatio_le_one hb
  have hA0 := evenShiftRatio_nonneg ha
  have hB0 := evenShiftRatio_nonneg hb
  have hc := binomMass_nonneg (2 * j) j
  nlinarith [mul_le_one₀ hA hB0 hB]

theorem even_endpoint_difference_le_inv_sq {j a b : ℕ}
    (hj : 0 < j) (ha : a ≤ j) (hb : b ≤ j) :
    returnProb (2 * j) -
        binomMass (2 * j) (j - a) * binomMass (2 * j) (j - b) ≤
      ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (j : ℝ) ^ 2 := by
  rw [returnProb_even_eq_binomMass_sq, binomMass_even_shift ha,
    binomMass_even_shift hb]
  let c := binomMass (2 * j) j
  let A := evenShiftRatio j a
  let B := evenShiftRatio j b
  change c ^ 2 - (A * c) * (B * c) ≤ _
  have hc0 : 0 ≤ c ^ 2 := sq_nonneg c
  have hc : c ^ 2 ≤ 1 / (j : ℝ) := by
    simpa [c, returnProb_even_eq_binomMass_sq] using returnProb_even_le_inv j hj
  have hdef0 : 0 ≤ 1 - A * B := by
    have hAB := mul_le_one₀ (evenShiftRatio_le_one ha)
      (evenShiftRatio_nonneg hb) (evenShiftRatio_le_one hb)
    exact sub_nonneg.mpr hAB
  have hdef : 1 - A * B ≤
      ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (j : ℝ) := by
    simpa [A, B] using one_sub_evenShiftRatio_mul_le hj ha hb
  have hmul := mul_le_mul hc hdef hdef0 (by positivity : 0 ≤ 1 / (j : ℝ))
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have heq : c ^ 2 - (A * c) * (B * c) = c ^ 2 * (1 - A * B) := by ring
  rw [heq]
  calc
    c ^ 2 * (1 - A * B) ≤
        (1 / (j : ℝ)) *
          (((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (j : ℝ)) := hmul
    _ = ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (j : ℝ) ^ 2 := by field_simp

def centeredEvenIndex (j : ℕ) (a : ℤ) : ℕ :=
  if 0 ≤ a then j - a.natAbs else j + a.natAbs

theorem centeredEvenIndex_le {j : ℕ} {a : ℤ} (ha : a.natAbs ≤ j) :
    centeredEvenIndex j a ≤ 2 * j := by
  unfold centeredEvenIndex
  split_ifs <;> omega

theorem centeredEvenIndex_diagonal {j : ℕ} {a : ℤ} (ha : a.natAbs ≤ j) :
    ((2 * j : ℕ) : ℤ) - 2 * (centeredEvenIndex j a : ℤ) = 2 * a := by
  unfold centeredEvenIndex
  by_cases hapos : 0 ≤ a
  · rw [if_pos hapos, Nat.cast_sub ha, Int.natCast_natAbs, abs_of_nonneg hapos]
    push_cast
    ring
  · rw [if_neg hapos]
    push_cast
    rw [abs_of_neg (lt_of_not_ge hapos)]
    ring

theorem binomMass_centeredEvenIndex {j : ℕ} {a : ℤ} (ha : a.natAbs ≤ j) :
    binomMass (2 * j) (centeredEvenIndex j a) =
      evenShiftRatio j a.natAbs * binomMass (2 * j) j := by
  unfold centeredEvenIndex
  by_cases hapos : 0 ≤ a
  · rw [if_pos hapos]
    exact binomMass_even_shift ha
  · rw [if_neg hapos]
    have hle : j + a.natAbs ≤ 2 * j := by omega
    rw [binomMass, ← Nat.choose_symm hle]
    have hindex : 2 * j - (j + a.natAbs) = j - a.natAbs := by omega
    rw [hindex]
    exact binomMass_even_shift ha

theorem freeOriginWeight_eq_position_real (x : Site) (n : ℕ) :
    (freeOriginWeight x n).toReal =
      incrementLaw.real {ω | simpleRandomWalk ω n = -x} := by
  have hevent : killedEndpointEvent (Set.univ : Set Site) x 0 n =
      {ω | simpleRandomWalk ω n = -x} := by
    ext ω
    constructor
    · intro hω
      exact eq_neg_of_add_eq_zero_right (by simpa [walkFrom] using hω.2)
    · intro hω
      constructor
      · intro r hr
        exact Set.mem_univ _
      · change simpleRandomWalk ω n = -x at hω
        rw [walkFrom, hω]
        exact add_neg_cancel x
  rw [freeOriginWeight, killedWeight, hevent]
  rfl

theorem freeOriginWeight_even_diagonal
    {x : Site} {a b : ℤ} {j : ℕ}
    (h₁ : (-x).1 + (-x).2 = 2 * a)
    (h₂ : (-x).1 - (-x).2 = 2 * b)
    (ha : a.natAbs ≤ j) (hb : b.natAbs ≤ j) :
    (freeOriginWeight x (2 * j)).toReal =
      binomMass (2 * j) (j - a.natAbs) *
        binomMass (2 * j) (j - b.natAbs) := by
  rw [freeOriginWeight_eq_position_real]
  have hd₁ := centeredEvenIndex_diagonal ha
  have hd₂ := centeredEvenIndex_diagonal hb
  have he₁ : ((2 * j : ℕ) : ℤ) -
      2 * (centeredEvenIndex j a : ℤ) = (-x).1 + (-x).2 := hd₁.trans h₁.symm
  have he₂ : ((2 * j : ℕ) : ℤ) -
      2 * (centeredEvenIndex j b : ℤ) = (-x).1 - (-x).2 := hd₂.trans h₂.symm
  rw [increment_position_real_eq_binomMass_mul he₁ he₂,
    binomMass_centeredEvenIndex ha, binomMass_centeredEvenIndex hb,
    ← binomMass_even_shift ha, ← binomMass_even_shift hb]

theorem even_diagonal_potential_term_le_inv_sq
    {x : Site} {a b : ℤ} {j : ℕ}
    (h₁ : (-x).1 + (-x).2 = 2 * a)
    (h₂ : (-x).1 - (-x).2 = 2 * b)
    (hj : 0 < j) (ha : a.natAbs ≤ j) (hb : b.natAbs ≤ j) :
    0 ≤ returnProb (2 * j) - (freeOriginWeight x (2 * j)).toReal ∧
      returnProb (2 * j) - (freeOriginWeight x (2 * j)).toReal ≤
        ((a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2) / (j : ℝ) ^ 2 := by
  rw [freeOriginWeight_even_diagonal h₁ h₂ ha hb]
  exact ⟨even_endpoint_difference_nonneg ha hb,
    even_endpoint_difference_le_inv_sq hj ha hb⟩

theorem endpointPrefixes_odd_empty_of_even_diagonal
    {y : Site} {a : ℤ} (h₁ : y.1 + y.2 = 2 * a) (j : ℕ) :
    endpointPrefixes (2 * j + 1) y = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  have hwy : finitePosition w = y := by
    simpa [endpointPrefixes] using hw
  have hd := diagonal_sum_one w
  rw [sum_boolSign_eq_card_sub_twice] at hd
  simp only [Fintype.card_coe, Finset.card_range] at hd
  change ((2 * j + 1 : ℕ) : ℤ) -
    2 * ((truePositions (prefixBitsEquiv (2 * j + 1) w).1).card : ℤ) =
      (finitePosition w).1 + (finitePosition w).2 at hd
  rw [hwy, h₁] at hd
  omega

theorem freeOriginWeight_odd_eq_zero_of_even_diagonal
    {x : Site} {a : ℤ} (h₁ : (-x).1 + (-x).2 = 2 * a) (j : ℕ) :
    (freeOriginWeight x (2 * j + 1)).toReal = 0 := by
  rw [freeOriginWeight_eq_position_real, Measure.real,
    increment_position_prob_eq_card,
    endpointPrefixes_odd_empty_of_even_diagonal h₁]
  simp

theorem returnProb_odd_eq_zero (j : ℕ) : returnProb (2 * j + 1) = 0 := by
  rw [returnProb, return_real_odd]

theorem summable_even_diagonal_potential_terms
    {x : Site} {a b : ℤ}
    (h₁ : (-x).1 + (-x).2 = 2 * a)
    (h₂ : (-x).1 - (-x).2 = 2 * b) :
    Summable (fun n : ℕ ↦ returnProb n - (freeOriginWeight x n).toReal) := by
  let C : ℝ := 4 * ((a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2)
  have hsbase : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable (fun n : ℕ ↦ C * (1 / (n : ℝ) ^ 2)) :=
    hsbase.mul_left C
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop
    (2 * (max 1 (max a.natAbs b.natAbs)))] with n hn
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hj : 0 < j := by omega
    have ha : a.natAbs ≤ j := by omega
    have hb : b.natAbs ≤ j := by omega
    have ht := even_diagonal_potential_term_le_inv_sq h₁ h₂ hj ha hb
    rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
    dsimp only [C]
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj
    calc
      returnProb (2 * j) - (freeOriginWeight x (2 * j)).toReal ≤
          ((a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2) / (j : ℝ) ^ 2 := ht.2
      _ = 4 * ((a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2) *
          (1 / ((2 * j : ℕ) : ℝ) ^ 2) := by
        push_cast
        field_simp
        ring
  · rw [returnProb_odd_eq_zero,
      freeOriginWeight_odd_eq_zero_of_even_diagonal h₁]
    simp only [sub_zero, norm_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    positivity [C]

noncomputable def oddCenterFactor (j : ℕ) : ℝ :=
  ((2 * j + 1 : ℕ) : ℝ) / ((2 * (j + 1) : ℕ) : ℝ)

noncomputable def oddShiftRatio (j d : ℕ) : ℝ :=
  ∏ t ∈ Finset.range d,
    ((j - t : ℕ) : ℝ) / ((j + t + 2 : ℕ) : ℝ)

theorem oddShiftRatio_zero (j : ℕ) : oddShiftRatio j 0 = 1 := by
  simp [oddShiftRatio]

theorem oddShiftRatio_succ (j d : ℕ) :
    oddShiftRatio j (d + 1) = oddShiftRatio j d *
      (((j - d : ℕ) : ℝ) / ((j + d + 2 : ℕ) : ℝ)) := by
  unfold oddShiftRatio
  rw [Finset.prod_range_succ]

theorem binomMass_odd_center (j : ℕ) :
    binomMass (2 * j + 1) j =
      oddCenterFactor j * binomMass (2 * j) j := by
  unfold binomMass oddCenterFactor
  have hnat := Nat.choose_mul_succ_eq (2 * j) j
  have hden : (0 : ℝ) < ((2 * (j + 1) : ℕ) : ℝ) := by positivity
  have hchoose : ((Nat.choose (2 * j + 1) j : ℕ) : ℝ) =
      (((Nat.choose (2 * j) j : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ)) /
        ((j + 1 : ℕ) : ℝ) := by
    have hnat' : Nat.choose (2 * j) j * (2 * j + 1) =
        Nat.choose (2 * j + 1) j * (j + 1) := by
      have hs : 2 * j + 1 - j = j + 1 := by omega
      rw [hs] at hnat
      exact hnat
    have hreal : ((Nat.choose (2 * j) j : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ) =
        ((Nat.choose (2 * j + 1) j : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat'
    apply (eq_div_iff (by positivity : ((j + 1 : ℕ) : ℝ) ≠ 0)).2
    nlinarith
  rw [hchoose, pow_succ]
  push_cast
  field_simp

theorem binomMass_odd_shift {j d : ℕ} (hd : d ≤ j) :
    binomMass (2 * j + 1) (j - d) =
      oddShiftRatio j d * binomMass (2 * j + 1) j := by
  induction d with
  | zero => simp [oddShiftRatio]
  | succ d ih =>
      have hdj : d ≤ j := by omega
      have hk : j - (d + 1) < 2 * j + 1 := by omega
      rw [binomMass_previous (2 * j + 1) (j - (d + 1)) hk]
      have hnum : j - (d + 1) + 1 = j - d := by omega
      have hden : 2 * j + 1 - (j - (d + 1)) = j + d + 2 := by omega
      rw [hnum, hden, ih hdj, oddShiftRatio_succ]
      ring

theorem oddShiftRatio_nonneg {j d : ℕ} (hd : d ≤ j) :
    0 ≤ oddShiftRatio j d := by
  induction d with
  | zero => simp [oddShiftRatio]
  | succ d ih =>
      rw [oddShiftRatio_succ]
      exact mul_nonneg (ih (by omega)) (by positivity)

theorem oddShiftRatio_le_one {j d : ℕ} (hd : d ≤ j) :
    oddShiftRatio j d ≤ 1 := by
  induction d with
  | zero => simp [oddShiftRatio]
  | succ d ih =>
      rw [oddShiftRatio_succ]
      apply mul_le_one₀ (ih (by omega)) (by positivity)
      apply (div_le_one (by positivity :
        (0 : ℝ) < ((j + d + 2 : ℕ) : ℝ))).2
      exact_mod_cast (show j - d ≤ j + d + 2 by omega)

theorem one_sub_oddShiftRatio_le {j d : ℕ} (hj : 0 < j) (hd : d ≤ j) :
    1 - oddShiftRatio j d ≤ ((d : ℝ) * (d + 1)) / (j : ℝ) := by
  induction d with
  | zero => simp [oddShiftRatio]
  | succ d ih =>
      have hdj : d ≤ j := by omega
      let R := oddShiftRatio j d
      let f : ℝ := ((j - d : ℕ) : ℝ) / ((j + d + 2 : ℕ) : ℝ)
      have hR1 : R ≤ 1 := by simpa [R] using oddShiftRatio_le_one hdj
      have hf1 : f ≤ 1 := by
        apply (div_le_one (by positivity : (0 : ℝ) < ((j + d + 2 : ℕ) : ℝ))).2
        exact_mod_cast (show j - d ≤ j + d + 2 by omega)
      have hdf : 1 - f ≤ ((2 * d + 2 : ℕ) : ℝ) / (j : ℝ) := by
        have hjR : (0 : ℝ) < j := by exact_mod_cast hj
        dsimp only [f]
        have hsub : ((j - d : ℕ) : ℝ) = (j : ℝ) - (d : ℝ) := by
          rw [Nat.cast_sub hdj]
        rw [hsub]
        push_cast
        have heq : 1 - ((j : ℝ) - (d : ℝ)) / ((j : ℝ) + (d : ℝ) + 2) =
            (2 * (d : ℝ) + 2) / ((j : ℝ) + (d : ℝ) + 2) := by
          field_simp
          ring
        rw [heq]
        apply (div_le_div_iff₀
          (show (0 : ℝ) < (j : ℝ) + (d : ℝ) + 2 by positivity) hjR).2
        nlinarith
      have hih : 1 - R ≤ ((d : ℝ) * (d + 1)) / (j : ℝ) := by
        simpa [R] using ih hdj
      have hmul : R * (1 - f) ≤ ((2 * d + 2 : ℕ) : ℝ) / (j : ℝ) := by
        simpa using mul_le_mul hR1 hdf (sub_nonneg.mpr hf1) (by norm_num : (0 : ℝ) ≤ 1)
      rw [oddShiftRatio_succ]
      change 1 - R * f ≤ (((d + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) + 1)) / (j : ℝ)
      have hjR : (0 : ℝ) < j := by exact_mod_cast hj
      apply (le_div_iff₀ hjR).2
      have hih' := (le_div_iff₀ hjR).mp hih
      have hmul' := (le_div_iff₀ hjR).mp hmul
      push_cast at hmul' ⊢
      nlinarith

noncomputable def oddCoordinateRatio (j d : ℕ) : ℝ :=
  oddCenterFactor j * oddShiftRatio j d

theorem oddCenterFactor_nonneg (j : ℕ) : 0 ≤ oddCenterFactor j := by
  unfold oddCenterFactor
  positivity

theorem oddCenterFactor_le_one (j : ℕ) : oddCenterFactor j ≤ 1 := by
  unfold oddCenterFactor
  apply (div_le_one (by positivity : (0 : ℝ) < ((2 * (j + 1) : ℕ) : ℝ))).2
  exact_mod_cast (show 2 * j + 1 ≤ 2 * (j + 1) by omega)

theorem one_sub_oddCenterFactor_le (j : ℕ) (hj : 0 < j) :
    1 - oddCenterFactor j ≤ 1 / (j : ℝ) := by
  unfold oddCenterFactor
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  push_cast
  have heq : 1 - (2 * (j : ℝ) + 1) / (2 * ((j : ℝ) + 1)) =
      1 / (2 * ((j : ℝ) + 1)) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((j : ℝ) + 1)) hjR).2
  nlinarith

theorem oddCoordinateRatio_nonneg {j d : ℕ} (hd : d ≤ j) :
    0 ≤ oddCoordinateRatio j d :=
  mul_nonneg (oddCenterFactor_nonneg j) (oddShiftRatio_nonneg hd)

theorem oddCoordinateRatio_le_one {j d : ℕ} (hd : d ≤ j) :
    oddCoordinateRatio j d ≤ 1 :=
  mul_le_one₀ (oddCenterFactor_le_one j) (oddShiftRatio_nonneg hd)
    (oddShiftRatio_le_one hd)

theorem one_sub_oddCoordinateRatio_le {j d : ℕ}
    (hj : 0 < j) (hd : d ≤ j) :
    1 - oddCoordinateRatio j d ≤
      (1 + (d : ℝ) * (d + 1)) / (j : ℝ) := by
  let F := oddCenterFactor j
  let R := oddShiftRatio j d
  have hF1 : F ≤ 1 := by simpa [F] using oddCenterFactor_le_one j
  have hR1 : R ≤ 1 := by simpa [R] using oddShiftRatio_le_one hd
  have hdF : 1 - F ≤ 1 / (j : ℝ) := by
    simpa [F] using one_sub_oddCenterFactor_le j hj
  have hdR : 1 - R ≤ ((d : ℝ) * (d + 1)) / (j : ℝ) := by
    simpa [R] using one_sub_oddShiftRatio_le hj hd
  have hmul : F * (1 - R) ≤ ((d : ℝ) * (d + 1)) / (j : ℝ) := by
    simpa using mul_le_mul hF1 hdR (sub_nonneg.mpr hR1) (by norm_num : (0 : ℝ) ≤ 1)
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  apply (le_div_iff₀ hjR).2
  change (1 - F * R) * (j : ℝ) ≤ _
  have hdF' := (le_div_iff₀ hjR).mp hdF
  have hmul' := (le_div_iff₀ hjR).mp hmul
  nlinarith

theorem one_sub_oddCoordinateRatio_mul_le {j d e : ℕ}
    (hj : 0 < j) (hd : d ≤ j) (he : e ≤ j) :
    1 - oddCoordinateRatio j d * oddCoordinateRatio j e ≤
      (2 + (d : ℝ) * (d + 1) + (e : ℝ) * (e + 1)) / (j : ℝ) := by
  let D := oddCoordinateRatio j d
  let E := oddCoordinateRatio j e
  have hD1 : D ≤ 1 := by simpa [D] using oddCoordinateRatio_le_one hd
  have hE1 : E ≤ 1 := by simpa [E] using oddCoordinateRatio_le_one he
  have hdD : 1 - D ≤ (1 + (d : ℝ) * (d + 1)) / (j : ℝ) := by
    simpa [D] using one_sub_oddCoordinateRatio_le hj hd
  have hdE : 1 - E ≤ (1 + (e : ℝ) * (e + 1)) / (j : ℝ) := by
    simpa [E] using one_sub_oddCoordinateRatio_le hj he
  have hmul : D * (1 - E) ≤ (1 + (e : ℝ) * (e + 1)) / (j : ℝ) := by
    simpa using mul_le_mul hD1 hdE (sub_nonneg.mpr hE1) (by norm_num : (0 : ℝ) ≤ 1)
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  apply (le_div_iff₀ hjR).2
  change (1 - D * E) * (j : ℝ) ≤ _
  have hdD' := (le_div_iff₀ hjR).mp hdD
  have hmul' := (le_div_iff₀ hjR).mp hmul
  nlinarith

theorem odd_endpoint_difference_le_inv_sq {j d e : ℕ}
    (hj : 0 < j) (hd : d ≤ j) (he : e ≤ j) :
    0 ≤ returnProb (2 * j) -
        binomMass (2 * j + 1) (j - d) * binomMass (2 * j + 1) (j - e) ∧
      returnProb (2 * j) -
          binomMass (2 * j + 1) (j - d) * binomMass (2 * j + 1) (j - e) ≤
        (2 + (d : ℝ) * (d + 1) + (e : ℝ) * (e + 1)) / (j : ℝ) ^ 2 := by
  rw [returnProb_even_eq_binomMass_sq, binomMass_odd_shift hd,
    binomMass_odd_shift he, binomMass_odd_center]
  let c := binomMass (2 * j) j
  let D := oddCoordinateRatio j d
  let E := oddCoordinateRatio j e
  change 0 ≤ c ^ 2 -
      (oddShiftRatio j d * (oddCenterFactor j * c)) *
        (oddShiftRatio j e * (oddCenterFactor j * c)) ∧ _
  have hrewrite :
      (oddShiftRatio j d * (oddCenterFactor j * c)) *
          (oddShiftRatio j e * (oddCenterFactor j * c)) =
        (D * c) * (E * c) := by
    dsimp only [D, E, oddCoordinateRatio]
    ring
  rw [hrewrite]
  have hDE : D * E ≤ 1 :=
    mul_le_one₀ (oddCoordinateRatio_le_one hd) (oddCoordinateRatio_nonneg he)
      (oddCoordinateRatio_le_one he)
  have hdef0 : 0 ≤ 1 - D * E := sub_nonneg.mpr hDE
  have hdef := one_sub_oddCoordinateRatio_mul_le hj hd he
  have hc : c ^ 2 ≤ 1 / (j : ℝ) := by
    simpa [c, returnProb_even_eq_binomMass_sq] using returnProb_even_le_inv j hj
  have hc0 : 0 ≤ c ^ 2 := sq_nonneg c
  have hmul := mul_le_mul hc hdef hdef0 (by positivity : 0 ≤ 1 / (j : ℝ))
  have heq : c ^ 2 - (D * c) * (E * c) = c ^ 2 * (1 - D * E) := by ring
  rw [heq]
  constructor
  · positivity
  · calc
      c ^ 2 * (1 - D * E) ≤
          (1 / (j : ℝ)) *
            ((2 + (d : ℝ) * (d + 1) + (e : ℝ) * (e + 1)) / (j : ℝ)) := hmul
      _ = (2 + (d : ℝ) * (d + 1) + (e : ℝ) * (e + 1)) / (j : ℝ) ^ 2 := by
        field_simp

def centeredOddIndex (j : ℕ) (a : ℤ) : ℕ :=
  if 0 ≤ a then j - a.natAbs else j + a.natAbs

def oddModeDistance (a : ℤ) : ℕ :=
  if 0 ≤ a then a.natAbs else a.natAbs - 1

theorem centeredOddIndex_le {j : ℕ} {a : ℤ} (ha : a.natAbs ≤ j) :
    centeredOddIndex j a ≤ 2 * j + 1 := by
  unfold centeredOddIndex
  split_ifs <;> omega

theorem centeredOddIndex_diagonal {j : ℕ} {a : ℤ} (ha : a.natAbs ≤ j) :
    ((2 * j + 1 : ℕ) : ℤ) - 2 * (centeredOddIndex j a : ℤ) = 2 * a + 1 := by
  unfold centeredOddIndex
  by_cases hapos : 0 ≤ a
  · rw [if_pos hapos, Nat.cast_sub ha, Int.natCast_natAbs, abs_of_nonneg hapos]
    push_cast
    ring
  · rw [if_neg hapos]
    push_cast
    rw [abs_of_neg (lt_of_not_ge hapos)]
    ring

theorem oddModeDistance_le {j : ℕ} {a : ℤ} (ha : a.natAbs ≤ j) :
    oddModeDistance a ≤ j := by
  unfold oddModeDistance
  split_ifs <;> omega

theorem oddModeDistance_le_natAbs (a : ℤ) : oddModeDistance a ≤ a.natAbs := by
  unfold oddModeDistance
  split_ifs <;> omega

theorem binomMass_centeredOddIndex {j : ℕ} {a : ℤ} (ha : a.natAbs ≤ j) :
    binomMass (2 * j + 1) (centeredOddIndex j a) =
      oddCoordinateRatio j (oddModeDistance a) * binomMass (2 * j) j := by
  unfold centeredOddIndex oddModeDistance
  by_cases hapos : 0 ≤ a
  · rw [if_pos hapos, if_pos hapos, oddCoordinateRatio,
      binomMass_odd_shift ha, binomMass_odd_center]
    ring
  · rw [if_neg hapos, if_neg hapos]
    have hneg : a < 0 := lt_of_not_ge hapos
    have habs : 0 < a.natAbs := Int.natAbs_pos.mpr (ne_of_lt hneg)
    have hle : j + a.natAbs ≤ 2 * j + 1 := by omega
    have hindex : 2 * j + 1 - (j + a.natAbs) = j - (a.natAbs - 1) := by
      omega
    have hsym : binomMass (2 * j + 1) (j + a.natAbs) =
        binomMass (2 * j + 1) (j - (a.natAbs - 1)) := by
      unfold binomMass
      rw [← Nat.choose_symm hle, hindex]
    rw [hsym, oddCoordinateRatio,
      binomMass_odd_shift (show a.natAbs - 1 ≤ j by omega),
      binomMass_odd_center]
    ring

theorem freeOriginWeight_odd_diagonal
    {x : Site} {a b : ℤ} {j : ℕ}
    (h₁ : (-x).1 + (-x).2 = 2 * a + 1)
    (h₂ : (-x).1 - (-x).2 = 2 * b + 1)
    (ha : a.natAbs ≤ j) (hb : b.natAbs ≤ j) :
    (freeOriginWeight x (2 * j + 1)).toReal =
      binomMass (2 * j + 1) (j - oddModeDistance a) *
        binomMass (2 * j + 1) (j - oddModeDistance b) := by
  rw [freeOriginWeight_eq_position_real]
  have hd₁ := centeredOddIndex_diagonal ha
  have hd₂ := centeredOddIndex_diagonal hb
  have he₁ : ((2 * j + 1 : ℕ) : ℤ) -
      2 * (centeredOddIndex j a : ℤ) = (-x).1 + (-x).2 := hd₁.trans h₁.symm
  have he₂ : ((2 * j + 1 : ℕ) : ℤ) -
      2 * (centeredOddIndex j b : ℤ) = (-x).1 - (-x).2 := hd₂.trans h₂.symm
  rw [increment_position_real_eq_binomMass_mul he₁ he₂,
    binomMass_centeredOddIndex ha, binomMass_centeredOddIndex hb]
  rw [oddCoordinateRatio, oddCoordinateRatio,
    binomMass_odd_shift (oddModeDistance_le ha),
    binomMass_odd_shift (oddModeDistance_le hb), binomMass_odd_center]
  ring

theorem odd_diagonal_paired_term_le_inv_sq
    {x : Site} {a b : ℤ} {j : ℕ}
    (h₁ : (-x).1 + (-x).2 = 2 * a + 1)
    (h₂ : (-x).1 - (-x).2 = 2 * b + 1)
    (hj : 0 < j) (ha : a.natAbs ≤ j) (hb : b.natAbs ≤ j) :
    0 ≤ returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal ∧
      returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal ≤
        (2 + (oddModeDistance a : ℝ) * (oddModeDistance a + 1) +
          (oddModeDistance b : ℝ) * (oddModeDistance b + 1)) / (j : ℝ) ^ 2 := by
  rw [freeOriginWeight_odd_diagonal h₁ h₂ ha hb]
  exact odd_endpoint_difference_le_inv_sq hj (oddModeDistance_le ha)
    (oddModeDistance_le hb)

theorem summable_odd_diagonal_paired_terms
    {x : Site} {a b : ℤ}
    (h₁ : (-x).1 + (-x).2 = 2 * a + 1)
    (h₂ : (-x).1 - (-x).2 = 2 * b + 1) :
    Summable (fun j : ℕ ↦
      returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal) := by
  let C : ℝ := 2 + (oddModeDistance a : ℝ) * (oddModeDistance a + 1) +
    (oddModeDistance b : ℝ) * (oddModeDistance b + 1)
  have hsbase : Summable (fun j : ℕ ↦ 1 / (j : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable (fun j : ℕ ↦ C * (1 / (j : ℝ) ^ 2)) :=
    hsbase.mul_left C
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop
    (max 1 (max a.natAbs b.natAbs))] with j hj
  have hj0 : 0 < j := by omega
  have ha : a.natAbs ≤ j := by omega
  have hb : b.natAbs ≤ j := by omega
  have ht := odd_diagonal_paired_term_le_inv_sq h₁ h₂ hj0 ha hb
  rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
  dsimp only [C]
  calc
    returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal ≤
        (2 + (oddModeDistance a : ℝ) * (oddModeDistance a + 1) +
          (oddModeDistance b : ℝ) * (oddModeDistance b + 1)) / (j : ℝ) ^ 2 := ht.2
    _ = (2 + (oddModeDistance a : ℝ) * (oddModeDistance a + 1) +
          (oddModeDistance b : ℝ) * (oddModeDistance b + 1)) *
        (1 / (j : ℝ) ^ 2) := by ring

theorem endpointPrefixes_even_empty_of_odd_diagonal
    {y : Site} {a : ℤ} (h₁ : y.1 + y.2 = 2 * a + 1) (j : ℕ) :
    endpointPrefixes (2 * j) y = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  have hwy : finitePosition w = y := by
    simpa [endpointPrefixes] using hw
  have hd := diagonal_sum_one w
  rw [sum_boolSign_eq_card_sub_twice] at hd
  simp only [Fintype.card_coe, Finset.card_range] at hd
  change ((2 * j : ℕ) : ℤ) -
    2 * ((truePositions (prefixBitsEquiv (2 * j) w).1).card : ℤ) =
      (finitePosition w).1 + (finitePosition w).2 at hd
  rw [hwy, h₁] at hd
  omega

theorem freeOriginWeight_even_eq_zero_of_odd_diagonal
    {x : Site} {a : ℤ} (h₁ : (-x).1 + (-x).2 = 2 * a + 1) (j : ℕ) :
    (freeOriginWeight x (2 * j)).toReal = 0 := by
  rw [freeOriginWeight_eq_position_real, Measure.real,
    increment_position_prob_eq_card,
    endpointPrefixes_even_empty_of_odd_diagonal h₁]
  simp

theorem finitePotentialKernel_eq_sum_potential_terms (N : ℕ) (x : Site) :
    finitePotentialKernel N x =
      ∑ n ∈ Finset.range N,
        (returnProb n - (freeOriginWeight x n).toReal) := by
  unfold finitePotentialKernel
  apply Finset.sum_congr rfl
  intro n hn
  rw [freeOriginWeight_zero_eq_return_real]
  rfl

theorem finitePotentialKernel_succ (N : ℕ) (x : Site) :
    finitePotentialKernel (N + 1) x = finitePotentialKernel N x +
      (returnProb N - (freeOriginWeight x N).toReal) := by
  rw [finitePotentialKernel_eq_sum_potential_terms,
    finitePotentialKernel_eq_sum_potential_terms, Finset.sum_range_succ]

theorem finitePotentialKernel_even_eq_sum_paired
    {x : Site} {a : ℤ}
    (h₁ : (-x).1 + (-x).2 = 2 * a + 1) (N : ℕ) :
    finitePotentialKernel (2 * N) x =
      ∑ j ∈ Finset.range N,
        (returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal) := by
  induction N with
  | zero => simp [finitePotentialKernel]
  | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        finitePotentialKernel_succ, finitePotentialKernel_succ, ih,
        Finset.sum_range_succ, freeOriginWeight_even_eq_zero_of_odd_diagonal h₁,
        returnProb_odd_eq_zero]
      ring

theorem finitePotentialKernel_odd_eq_sum_paired_add
    {x : Site} {a : ℤ}
    (h₁ : (-x).1 + (-x).2 = 2 * a + 1) (N : ℕ) :
    finitePotentialKernel (2 * N + 1) x =
      (∑ j ∈ Finset.range N,
        (returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal)) +
      returnProb (2 * N) := by
  rw [finitePotentialKernel_succ,
    finitePotentialKernel_even_eq_sum_paired h₁,
    freeOriginWeight_even_eq_zero_of_odd_diagonal h₁]
  ring

theorem returnProb_even_tendsto_zero :
    Filter.Tendsto (fun N : ℕ ↦ returnProb (2 * N)) Filter.atTop (𝓝 0) := by
  have hupper : Filter.Tendsto (fun N : ℕ ↦ 2 / (((2 * N : ℕ) : ℝ) + 1))
      Filter.atTop (𝓝 0) := by
    have hden : Filter.Tendsto (fun N : ℕ ↦ (((2 * N : ℕ) : ℝ) + 1))
        Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_add_const_right Filter.atTop 1
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    exact tendsto_const_nhds.div_atTop hden
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun N ↦ measureReal_nonneg
  · exact Filter.Eventually.of_forall fun N ↦ return_real_le_two_div_succ (2 * N)

theorem tendsto_of_even_odd_subsequences {α : Type*} [TopologicalSpace α]
    {f : ℕ → α} {z : α}
    (heven : Filter.Tendsto (fun N ↦ f (2 * N)) Filter.atTop (𝓝 z))
    (hodd : Filter.Tendsto (fun N ↦ f (2 * N + 1)) Filter.atTop (𝓝 z)) :
    Filter.Tendsto f Filter.atTop (𝓝 z) := by
  rw [Filter.tendsto_def]
  intro s hs
  obtain ⟨Ne, hNe⟩ := Filter.eventually_atTop.1 (heven hs)
  obtain ⟨No, hNo⟩ := Filter.eventually_atTop.1 (hodd hs)
  apply Filter.eventually_atTop.2
  refine ⟨2 * max Ne No + 1, ?_⟩
  intro n hn
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · rw [hk]
    exact hNe k (by omega)
  · rw [hk]
    exact hNo k (by omega)

theorem finitePotentialKernel_tendsto_even_diagonal
    {x : Site} {a b : ℤ}
    (h₁ : (-x).1 + (-x).2 = 2 * a)
    (h₂ : (-x).1 - (-x).2 = 2 * b) :
    Filter.Tendsto (fun N ↦ finitePotentialKernel N x) Filter.atTop
      (𝓝 (∑' n : ℕ, (returnProb n - (freeOriginWeight x n).toReal))) := by
  rw [show (fun N ↦ finitePotentialKernel N x) = fun N ↦
      ∑ n ∈ Finset.range N,
        (returnProb n - (freeOriginWeight x n).toReal) by
      funext N
      exact finitePotentialKernel_eq_sum_potential_terms N x]
  exact (summable_even_diagonal_potential_terms h₁ h₂).hasSum.tendsto_sum_nat

theorem finitePotentialKernel_tendsto_odd_diagonal
    {x : Site} {a b : ℤ}
    (h₁ : (-x).1 + (-x).2 = 2 * a + 1)
    (h₂ : (-x).1 - (-x).2 = 2 * b + 1) :
    Filter.Tendsto (fun N ↦ finitePotentialKernel N x) Filter.atTop
      (𝓝 (∑' j : ℕ,
        (returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal))) := by
  let g : ℕ → ℝ := fun j ↦
    returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal
  have hg : Summable g := by
    simpa only [g] using summable_odd_diagonal_paired_terms h₁ h₂
  have heven : Filter.Tendsto (fun N ↦ finitePotentialKernel (2 * N) x)
      Filter.atTop (𝓝 (∑' j, g j)) := by
    rw [show (fun N ↦ finitePotentialKernel (2 * N) x) =
        fun N ↦ ∑ j ∈ Finset.range N, g j by
      funext N
      simpa only [g] using finitePotentialKernel_even_eq_sum_paired h₁ N]
    exact hg.hasSum.tendsto_sum_nat
  have hodd : Filter.Tendsto (fun N ↦ finitePotentialKernel (2 * N + 1) x)
      Filter.atTop (𝓝 (∑' j, g j)) := by
    rw [show (fun N ↦ finitePotentialKernel (2 * N + 1) x) =
        fun N ↦ (∑ j ∈ Finset.range N, g j) + returnProb (2 * N) by
      funext N
      simpa only [g] using finitePotentialKernel_odd_eq_sum_paired_add h₁ N]
    simpa using hg.hasSum.tendsto_sum_nat.add returnProb_even_tendsto_zero
  exact tendsto_of_even_odd_subsequences heven hodd

theorem finitePotentialKernel_pointwise_converges (x : Site) :
    ∃ z : ℝ, Filter.Tendsto (fun N ↦ finitePotentialKernel N x)
      Filter.atTop (𝓝 z) := by
  obtain ⟨a, ha | ha⟩ := Int.even_or_odd' ((-x).1 + (-x).2)
  · have hb : (-x).1 - (-x).2 = 2 * (a - (-x).2) := by
      nlinarith
    exact ⟨(∑' n : ℕ, (returnProb n - (freeOriginWeight x n).toReal)),
      finitePotentialKernel_tendsto_even_diagonal ha hb⟩
  · have hb : (-x).1 - (-x).2 = 2 * (a - (-x).2) + 1 := by
      nlinarith
    exact ⟨∑' j : ℕ,
        (returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal),
      finitePotentialKernel_tendsto_odd_diagonal ha hb⟩

theorem exists_planarPotentialKernel :
    ∃ a : Site → ℝ,
      (∀ x, Filter.Tendsto (fun N ↦ finitePotentialKernel N x)
        Filter.atTop (𝓝 (a x))) ∧ IsPlanarPotentialKernel a := by
  choose a ha using finitePotentialKernel_pointwise_converges
  exact ⟨a, ha, isPlanarPotentialKernel_of_finitePotentialKernel_tendsto ha⟩

noncomputable def planarPotentialKernel (x : Site) : ℝ :=
  Classical.choose (finitePotentialKernel_pointwise_converges x)

theorem finitePotentialKernel_tendsto_planarPotentialKernel (x : Site) :
    Filter.Tendsto (fun N ↦ finitePotentialKernel N x) Filter.atTop
      (𝓝 (planarPotentialKernel x)) :=
  Classical.choose_spec (finitePotentialKernel_pointwise_converges x)

theorem planarPotentialKernel_isPlanar :
    IsPlanarPotentialKernel planarPotentialKernel :=
  isPlanarPotentialKernel_of_finitePotentialKernel_tendsto
    finitePotentialKernel_tendsto_planarPotentialKernel

@[simp] theorem planarPotentialKernel_zero : planarPotentialKernel 0 = 0 :=
  finitePotentialKernel_limit_zero finitePotentialKernel_tendsto_planarPotentialKernel

theorem sum_one_div_succ_sq_le_two (N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / (((j + 1 : ℕ) : ℝ) ^ 2)) ≤ 2 := by
  suffices hstrong : (∑ j ∈ Finset.range N,
      1 / (((j + 1 : ℕ) : ℝ) ^ 2)) ≤ 2 - 2 / ((N + 1 : ℕ) : ℝ) by
    exact hstrong.trans (sub_le_self 2 (by positivity))
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hk : (0 : ℝ) < (N + 1 : ℕ) := by positivity
      have hk' : (0 : ℝ) < (N + 2 : ℕ) := by positivity
      calc
        (∑ j ∈ Finset.range N, 1 / (((j + 1 : ℕ) : ℝ) ^ 2)) +
            1 / (((N + 1 : ℕ) : ℝ) ^ 2) ≤
            (2 - 2 / ((N + 1 : ℕ) : ℝ)) +
              1 / (((N + 1 : ℕ) : ℝ) ^ 2) := by gcongr
        _ ≤ 2 - 2 / (((N + 1) + 1 : ℕ) : ℝ) := by
          push_cast
          rw [← sub_nonneg]
          have heq :
              (2 - 2 / ((N : ℝ) + 1 + 1)) -
                ((2 - 2 / ((N : ℝ) + 1)) + 1 / ((N : ℝ) + 1) ^ 2) =
              (N : ℝ) / (((N : ℝ) + 1) ^ 2 * ((N : ℝ) + 2)) := by
            field_simp
            ring
          rw [heq]
          positivity

theorem evenReturnSum_abs_harmonic_le_two (N : ℕ) :
    |(∑ j ∈ Finset.range N, returnProb (2 * (j + 1))) -
        (1 / Real.pi) * (harmonic N : ℝ)| ≤ 2 := by
  have hterm (j : ℕ) :
      |returnProb (2 * (j + 1)) - 1 / (Real.pi * ((j + 1 : ℕ) : ℝ))| ≤
        1 / (((j + 1 : ℕ) : ℝ) ^ 2) := by
    simpa only [show 1 ≤ j + 1 by omega] using
      returnProb_even_localCLT_abs_le_inv_sq (j + 1) (by omega)
  calc
    |(∑ j ∈ Finset.range N, returnProb (2 * (j + 1))) -
        (1 / Real.pi) * (harmonic N : ℝ)| =
        |∑ j ∈ Finset.range N,
          (returnProb (2 * (j + 1)) -
            1 / (Real.pi * ((j + 1 : ℕ) : ℝ)))| := by
          congr 1
          rw [Finset.sum_sub_distrib]
          congr 1
          simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
            one_div, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ ≤ ∑ j ∈ Finset.range N,
        |returnProb (2 * (j + 1)) -
          1 / (Real.pi * ((j + 1 : ℕ) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, 1 / (((j + 1 : ℕ) : ℝ) ^ 2) := by
      gcongr with j hj
      exact hterm j
    _ ≤ 2 := sum_one_div_succ_sq_le_two N

theorem evenReturnSum_lower (N : ℕ) :
    (1 / Real.pi) * (harmonic N : ℝ) - 2 ≤
      ∑ j ∈ Finset.range N, returnProb (2 * (j + 1)) := by
  have h := evenReturnSum_abs_harmonic_le_two N
  rw [abs_le] at h
  linarith

theorem evenReturnSum_upper (N : ℕ) :
    (∑ j ∈ Finset.range N, returnProb (2 * (j + 1))) ≤
      (1 / Real.pi) * (harmonic N : ℝ) + 2 := by
  have h := evenReturnSum_abs_harmonic_le_two N
  rw [abs_le] at h
  linarith

theorem diagonal_natAbs_le_two_siteNormInf (x : Site) :
    (x.1 + x.2).natAbs ≤ 2 * siteNormInf x ∧
      (x.1 - x.2).natAbs ≤ 2 * siteNormInf x := by
  have hx₁ : x.1.natAbs ≤ siteNormInf x := by
    exact le_max_left _ _
  have hx₂ : x.2.natAbs ≤ siteNormInf x := by
    exact le_max_right _ _
  constructor
  · exact (Int.natAbs_add_le x.1 x.2).trans (by omega)
  · exact (Int.natAbs_sub_le x.1 x.2).trans (by omega)

theorem diagonal_parameters_le_two_norm_even
    {x : Site} {a b : ℤ}
    (h₁ : (-x).1 + (-x).2 = 2 * a)
    (h₂ : (-x).1 - (-x).2 = 2 * b) :
    a.natAbs ≤ siteNormInf x ∧ b.natAbs ≤ siteNormInf x := by
  have hd := diagonal_natAbs_le_two_siteNormInf (-x)
  rw [siteNormInf_neg] at hd
  rw [h₁, Int.natAbs_mul] at hd
  rw [h₂, Int.natAbs_mul] at hd
  norm_num at hd
  exact hd

theorem diagonal_parameters_le_two_norm_odd
    {x : Site} {a b : ℤ}
    (h₁ : (-x).1 + (-x).2 = 2 * a + 1)
    (h₂ : (-x).1 - (-x).2 = 2 * b + 1) :
    a.natAbs ≤ 2 * siteNormInf x ∧ b.natAbs ≤ 2 * siteNormInf x := by
  have hd := diagonal_natAbs_le_two_siteNormInf (-x)
  rw [siteNormInf_neg, h₁, h₂] at hd
  have habs_le (c : ℤ) : c.natAbs ≤ (2 * c + 1).natAbs := by
    rw [Int.natAbs_le_iff_sq_le]
    by_cases hc : 0 ≤ c
    · nlinarith [sq_nonneg c]
    · have hc1 : c + 1 ≤ 0 := by omega
      have hc3 : 3 * c + 1 ≤ 0 := by omega
      have hp : 0 ≤ (3 * c + 1) * (c + 1) :=
        mul_nonneg_of_nonpos_of_nonpos hc3 hc1
      nlinarith
  constructor
  · exact (habs_le a).trans hd.1
  · exact (habs_le b).trans hd.2

theorem finitePotentialKernel_even_diagonal_eq_sum
    {x : Site} {a : ℤ}
    (h₁ : (-x).1 + (-x).2 = 2 * a) (N : ℕ) :
    finitePotentialKernel (2 * N) x =
      ∑ j ∈ Finset.range N,
        (returnProb (2 * j) - (freeOriginWeight x (2 * j)).toReal) := by
  induction N with
  | zero => simp [finitePotentialKernel]
  | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        finitePotentialKernel_succ, finitePotentialKernel_succ, ih,
        Finset.sum_range_succ, returnProb_odd_eq_zero,
        freeOriginWeight_odd_eq_zero_of_even_diagonal h₁]
      ring

theorem finitePotentialKernel_even_diagonal_odd_eq_sum_add
    {x : Site} {a : ℤ}
    (h₁ : (-x).1 + (-x).2 = 2 * a) (N : ℕ) :
    finitePotentialKernel (2 * N + 1) x =
      (∑ j ∈ Finset.range N,
        (returnProb (2 * j) - (freeOriginWeight x (2 * j)).toReal)) +
      (returnProb (2 * N) - (freeOriginWeight x (2 * N)).toReal) := by
  rw [finitePotentialKernel_succ,
    finitePotentialKernel_even_diagonal_eq_sum h₁]

theorem finitePotentialKernel_even_cutoff_le_kernel
    {x : Site} {a b : ℤ} {M : ℕ}
    (h₁ : (-x).1 + (-x).2 = 2 * a)
    (h₂ : (-x).1 - (-x).2 = 2 * b)
    (hM : 0 < M) (ha : a.natAbs ≤ M) (hb : b.natAbs ≤ M) :
    finitePotentialKernel (2 * M) x ≤ planarPotentialKernel x := by
  apply ge_of_tendsto (finitePotentialKernel_tendsto_planarPotentialKernel x)
  apply Filter.eventually_atTop.2
  refine ⟨2 * M, ?_⟩
  intro n hn
  obtain ⟨K, hK | hK⟩ := Nat.even_or_odd' n
  · rw [hK, finitePotentialKernel_even_diagonal_eq_sum h₁,
      finitePotentialKernel_even_diagonal_eq_sum h₁]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro j hjM hjK
    simp only [Finset.mem_range] at hjM hjK
    exact (even_diagonal_potential_term_le_inv_sq (j := j) h₁ h₂ (by omega)
      (by omega) (by omega)).1
  · rw [hK, finitePotentialKernel_even_diagonal_eq_sum h₁,
      finitePotentialKernel_even_diagonal_odd_eq_sum_add h₁]
    have hsum : (∑ j ∈ Finset.range M,
        (returnProb (2 * j) - (freeOriginWeight x (2 * j)).toReal)) ≤
        ∑ j ∈ Finset.range K,
          (returnProb (2 * j) - (freeOriginWeight x (2 * j)).toReal) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro j hjM hjK
      simp only [Finset.mem_range] at hjM hjK
      exact (even_diagonal_potential_term_le_inv_sq (j := j) h₁ h₂ (by omega)
        (by omega) (by omega)).1
    have hlast := (even_diagonal_potential_term_le_inv_sq (j := K) h₁ h₂ (by omega)
      (by omega) (by omega)).1
    linarith

theorem finitePotentialKernel_odd_cutoff_le_kernel
    {x : Site} {a b : ℤ} {M : ℕ}
    (h₁ : (-x).1 + (-x).2 = 2 * a + 1)
    (h₂ : (-x).1 - (-x).2 = 2 * b + 1)
    (hM : 0 < M) (ha : a.natAbs ≤ M) (hb : b.natAbs ≤ M) :
    finitePotentialKernel (2 * M) x ≤ planarPotentialKernel x := by
  apply ge_of_tendsto (finitePotentialKernel_tendsto_planarPotentialKernel x)
  apply Filter.eventually_atTop.2
  refine ⟨2 * M, ?_⟩
  intro n hn
  obtain ⟨K, hK | hK⟩ := Nat.even_or_odd' n
  · rw [hK, finitePotentialKernel_even_eq_sum_paired h₁,
      finitePotentialKernel_even_eq_sum_paired h₁]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro j hjM hjK
    simp only [Finset.mem_range] at hjM hjK
    exact (odd_diagonal_paired_term_le_inv_sq (j := j) h₁ h₂ (by omega)
      (by omega) (by omega)).1
  · rw [hK, finitePotentialKernel_even_eq_sum_paired h₁,
      finitePotentialKernel_odd_eq_sum_paired_add h₁]
    have hsum : (∑ j ∈ Finset.range M,
        (returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal)) ≤
        ∑ j ∈ Finset.range K,
          (returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro j hjM hjK
      simp only [Finset.mem_range] at hjM hjK
      exact (odd_diagonal_paired_term_le_inv_sq (j := j) h₁ h₂ (by omega)
        (by omega) (by omega)).1
    have hp : 0 ≤ returnProb (2 * K) := measureReal_nonneg
    linarith

theorem freeOriginWeight_diffusive_prefix_le
    {x : Site} {r : ℕ} (hr : siteNormInf x = r) (hr0 : 0 < r) :
    (∑ n ∈ Finset.range (2 * (4 * r ^ 2 + 1)),
      (freeOriginWeight x n).toReal) ≤ 1224 := by
  have hcut : 2 * (4 * r ^ 2 + 1) ≤ (3 * r) ^ 2 + 1 := by
    nlinarith [sq_nonneg (r - 1)]
  calc
    (∑ n ∈ Finset.range (2 * (4 * r ^ 2 + 1)),
        (freeOriginWeight x n).toReal) ≤
        ∑ n ∈ Finset.range (2 * (4 * r ^ 2 + 1)), heatKernelBound r n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← hr]
      simpa [freeOriginWeight, heatKernelBound] using
        killedWeight_toReal_le_heatKernel (Set.univ : Set Site) x n
    _ ≤ ∑ n ∈ Finset.range ((3 * r) ^ 2 + 1), heatKernelBound r n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hcut)
      intro n hn hnot
      unfold heatKernelBound
      positivity
    _ ≤ 408 * (1 + Real.log ((((3 * r + 1 : ℕ) : ℝ) / (r + 1 : ℕ)))) :=
      sum_heatKernelBound_square_le hr0 (by omega)
    _ ≤ 1224 := by
      have hden : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
      have hratioPos : (0 : ℝ) <
          (((3 * r + 1 : ℕ) : ℝ) / (r + 1 : ℕ)) := by positivity
      have hratio : (((3 * r + 1 : ℕ) : ℝ) / (r + 1 : ℕ)) ≤ 3 := by
        apply (div_le_iff₀ hden).2
        push_cast
        nlinarith
      have hlog := Real.log_le_sub_one_of_pos hratioPos
      nlinarith

theorem originReturnPrefix_even (N : ℕ) :
    (∑ n ∈ Finset.range (2 * (N + 1)), returnProb n) =
      1 + ∑ j ∈ Finset.range N, returnProb (2 * (j + 1)) := by
  induction N with
  | zero =>
      have hodd : returnProb 1 = 0 := by
        simpa using returnProb_odd_eq_zero 0
      have hzero : returnProb 0 = 1 := by
        rw [returnProb]
        convert return_real_even 0 using 1 <;> norm_num
      simp [Finset.sum_range_succ, hzero, hodd]
  | succ N ih =>
      rw [show 2 * (N + 1 + 1) = (2 * (N + 1) + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ, returnProb_odd_eq_zero]
      ring

theorem finitePotentialKernel_diffusive_lower
    {x : Site} {r : ℕ} (hr : siteNormInf x = r) (hr0 : 0 < r) :
    (1 / Real.pi) * (harmonic (4 * r ^ 2) : ℝ) - 1225 ≤
      finitePotentialKernel (2 * (4 * r ^ 2 + 1)) x := by
  rw [finitePotentialKernel_eq_sum_potential_terms, Finset.sum_sub_distrib,
    originReturnPrefix_even (4 * r ^ 2)]
  have hret := evenReturnSum_lower (4 * r ^ 2)
  have hend := freeOriginWeight_diffusive_prefix_le hr hr0
  linarith

theorem two_mul_log_norm_le_harmonic_four_sq {r : ℕ} (hr : 0 < r) :
    2 * Real.log (r : ℝ) ≤ (harmonic (4 * r ^ 2) : ℝ) := by
  have hlogharm := log_add_one_le_harmonic (4 * r ^ 2)
  push_cast at hlogharm
  have hcast : ((r : ℝ) ^ 2) ≤ (((4 * r ^ 2 + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show r ^ 2 ≤ 4 * r ^ 2 + 1 by omega)
  have hlog : Real.log ((r : ℝ) ^ 2) ≤
      Real.log (((4 * r ^ 2 + 1 : ℕ) : ℝ)) :=
    Real.log_le_log (by positivity) hcast
  rw [Real.log_pow] at hlog
  norm_num at hlog
  exact hlog.trans hlogharm

theorem planarPotentialKernel_log_lower (x : Site)
    (hx : 0 < siteNormInf x) :
    (2 / Real.pi) * Real.log (siteNormInf x : ℝ) - 1225 ≤
      planarPotentialKernel x := by
  let r := siteNormInf x
  have hcut := finitePotentialKernel_diffusive_lower (x := x) (r := r) rfl hx
  have hlim : finitePotentialKernel (2 * (4 * r ^ 2 + 1)) x ≤
      planarPotentialKernel x := by
    obtain ⟨a, ha | ha⟩ := Int.even_or_odd' ((-x).1 + (-x).2)
    · have hb : (-x).1 - (-x).2 = 2 * (a - (-x).2) := by nlinarith
      obtain ⟨hpa, hpb⟩ := diagonal_parameters_le_two_norm_even ha hb
      change a.natAbs ≤ r at hpa
      change (a - (-x).2).natAbs ≤ r at hpb
      apply finitePotentialKernel_even_cutoff_le_kernel ha hb
        (by positivity : 0 < 4 * r ^ 2 + 1)
      · exact hpa.trans (by nlinarith)
      · exact hpb.trans (by nlinarith)
    · have hb : (-x).1 - (-x).2 = 2 * (a - (-x).2) + 1 := by nlinarith
      obtain ⟨hpa, hpb⟩ := diagonal_parameters_le_two_norm_odd ha hb
      change a.natAbs ≤ 2 * r at hpa
      change (a - (-x).2).natAbs ≤ 2 * r at hpb
      apply finitePotentialKernel_odd_cutoff_le_kernel ha hb
        (by positivity : 0 < 4 * r ^ 2 + 1)
      · exact hpa.trans (by nlinarith)
      · exact hpb.trans (by nlinarith)
  have hharm := two_mul_log_norm_le_harmonic_four_sq hx
  have hpi : 0 < Real.pi := Real.pi_pos
  dsimp only [r] at hcut hlim ⊢
  have hscaled : (2 / Real.pi) * Real.log (siteNormInf x : ℝ) ≤
      (1 / Real.pi) * (harmonic (4 * siteNormInf x ^ 2) : ℝ) := by
    calc
      (2 / Real.pi) * Real.log (siteNormInf x : ℝ) =
          (1 / Real.pi) * (2 * Real.log (siteNormInf x : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hharm (by positivity)
  linarith

theorem sum_Ico_one_div_sq_le {M K : ℕ} (hM : 0 < M) (hMK : M ≤ K) :
    (∑ j ∈ Finset.Ico M K, 1 / ((j : ℝ) ^ 2)) ≤
      2 / (M : ℝ) - 2 / (K : ℝ) := by
  induction K, hMK using Nat.le_induction with
  | base => simp
  | succ K hMK ih =>
      rw [Finset.sum_Ico_succ_top hMK]
      have hK : (0 : ℝ) < K := by exact_mod_cast hM.trans_le hMK
      have hK1 : (0 : ℝ) < K + 1 := by positivity
      calc
        (∑ j ∈ Finset.Ico M K, 1 / (j : ℝ) ^ 2) + 1 / (K : ℝ) ^ 2 ≤
            (2 / (M : ℝ) - 2 / (K : ℝ)) + 1 / (K : ℝ) ^ 2 := by gcongr
        _ ≤ 2 / (M : ℝ) - 2 / ((K + 1 : ℕ) : ℝ) := by
          push_cast
          rw [← sub_nonneg]
          have heq :
              (2 / (M : ℝ) - 2 / ((K : ℝ) + 1)) -
                ((2 / (M : ℝ) - 2 / (K : ℝ)) + 1 / (K : ℝ) ^ 2) =
              ((K : ℝ) - 1) / ((K : ℝ) ^ 2 * ((K : ℝ) + 1)) := by
            field_simp
            ring
          rw [heq]
          apply div_nonneg
          · exact sub_nonneg.mpr (by exact_mod_cast hM.trans_le hMK)
          · positivity

theorem sum_Ico_one_div_sq_le_two_div {M K : ℕ} (hM : 0 < M) (hMK : M ≤ K) :
    (∑ j ∈ Finset.Ico M K, 1 / ((j : ℝ) ^ 2)) ≤ 2 / (M : ℝ) := by
  exact (sum_Ico_one_div_sq_le hM hMK).trans (sub_le_self _ (by positivity))

theorem planarPotentialKernel_le_even_cutoff_add_tail
    {x : Site} {a b : ℤ} {M : ℕ}
    (h₁ : (-x).1 + (-x).2 = 2 * a)
    (h₂ : (-x).1 - (-x).2 = 2 * b)
    (hM : 0 < M) (ha : a.natAbs ≤ M) (hb : b.natAbs ≤ M) :
    planarPotentialKernel x ≤ finitePotentialKernel (2 * M) x +
      2 * (((a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2) / (M : ℝ)) := by
  have htwo : Filter.Tendsto (fun K : ℕ ↦ 2 * K) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with K hK
    omega
  apply le_of_tendsto
    ((finitePotentialKernel_tendsto_planarPotentialKernel x).comp htwo)
  apply Filter.eventually_atTop.2
  refine ⟨M, ?_⟩
  intro K hMK
  change finitePotentialKernel (2 * K) x ≤ _
  rw [finitePotentialKernel_even_diagonal_eq_sum h₁,
      finitePotentialKernel_even_diagonal_eq_sum h₁,
      ← Finset.sum_range_add_sum_Ico _ hMK]
  have htail : (∑ j ∈ Finset.Ico M K,
        (returnProb (2 * j) - (freeOriginWeight x (2 * j)).toReal)) ≤
        ((a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2) *
          (2 / (M : ℝ)) := by
    calc
        (∑ j ∈ Finset.Ico M K,
            (returnProb (2 * j) - (freeOriginWeight x (2 * j)).toReal)) ≤
            ∑ j ∈ Finset.Ico M K,
              (((a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2) /
                (j : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' := Finset.mem_Ico.mp hj
          exact (even_diagonal_potential_term_le_inv_sq (j := j) h₁ h₂
            (by omega) (by omega) (by omega)).2
        _ = ((a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2) *
              ∑ j ∈ Finset.Ico M K, 1 / (j : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ ≤ ((a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2) *
              (2 / (M : ℝ)) := by
          gcongr
          exact sum_Ico_one_div_sq_le_two_div hM hMK
  calc
      (∑ j ∈ Finset.range M,
          (returnProb (2 * j) - (freeOriginWeight x (2 * j)).toReal)) +
          ∑ j ∈ Finset.Ico M K,
            (returnProb (2 * j) - (freeOriginWeight x (2 * j)).toReal) ≤
          (∑ j ∈ Finset.range M,
            (returnProb (2 * j) - (freeOriginWeight x (2 * j)).toReal)) +
            (((a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2) *
              (2 / (M : ℝ))) := by gcongr
      _ = (∑ j ∈ Finset.range M,
            (returnProb (2 * j) - (freeOriginWeight x (2 * j)).toReal)) +
          2 * (((a.natAbs : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2) / (M : ℝ)) := by
        ring

theorem planarPotentialKernel_le_odd_cutoff_add_tail
    {x : Site} {a b : ℤ} {M : ℕ}
    (h₁ : (-x).1 + (-x).2 = 2 * a + 1)
    (h₂ : (-x).1 - (-x).2 = 2 * b + 1)
    (hM : 0 < M) (ha : a.natAbs ≤ M) (hb : b.natAbs ≤ M) :
    planarPotentialKernel x ≤ finitePotentialKernel (2 * M) x +
      2 * ((2 + (oddModeDistance a : ℝ) * (oddModeDistance a + 1) +
        (oddModeDistance b : ℝ) * (oddModeDistance b + 1)) / (M : ℝ)) := by
  have htwo : Filter.Tendsto (fun K : ℕ ↦ 2 * K) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with K hK
    omega
  apply le_of_tendsto
    ((finitePotentialKernel_tendsto_planarPotentialKernel x).comp htwo)
  apply Filter.eventually_atTop.2
  refine ⟨M, ?_⟩
  intro K hMK
  change finitePotentialKernel (2 * K) x ≤ _
  rw [finitePotentialKernel_even_eq_sum_paired h₁,
    finitePotentialKernel_even_eq_sum_paired h₁,
    ← Finset.sum_range_add_sum_Ico _ hMK]
  let C : ℝ := 2 + (oddModeDistance a : ℝ) * (oddModeDistance a + 1) +
    (oddModeDistance b : ℝ) * (oddModeDistance b + 1)
  have htail : (∑ j ∈ Finset.Ico M K,
      (returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal)) ≤
      C * (2 / (M : ℝ)) := by
    calc
      (∑ j ∈ Finset.Ico M K,
          (returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal)) ≤
          ∑ j ∈ Finset.Ico M K, C / (j : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        simpa only [C] using (odd_diagonal_paired_term_le_inv_sq
          (j := j) h₁ h₂ (by omega) (by omega) (by omega)).2
      _ = C * ∑ j ∈ Finset.Ico M K, 1 / (j : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ C * (2 / (M : ℝ)) := by
        have hC : 0 ≤ C := by dsimp only [C]; positivity
        gcongr
        exact sum_Ico_one_div_sq_le_two_div hM hMK
  dsimp only [C] at htail ⊢
  calc
    (∑ j ∈ Finset.range M,
        (returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal)) +
        ∑ j ∈ Finset.Ico M K,
          (returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal) ≤
        (∑ j ∈ Finset.range M,
          (returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal)) +
          ((2 + (oddModeDistance a : ℝ) * (oddModeDistance a + 1) +
            (oddModeDistance b : ℝ) * (oddModeDistance b + 1)) *
            (2 / (M : ℝ))) := by gcongr
    _ = (∑ j ∈ Finset.range M,
          (returnProb (2 * j) - (freeOriginWeight x (2 * j + 1)).toReal)) +
        2 * ((2 + (oddModeDistance a : ℝ) * (oddModeDistance a + 1) +
          (oddModeDistance b : ℝ) * (oddModeDistance b + 1)) / (M : ℝ)) := by
      ring

theorem finitePotentialKernel_le_originReturnPrefix (N : ℕ) (x : Site) :
    finitePotentialKernel N x ≤ ∑ n ∈ Finset.range N, returnProb n := by
  rw [finitePotentialKernel_eq_sum_potential_terms, Finset.sum_sub_distrib]
  exact sub_le_self _ (Finset.sum_nonneg fun n hn ↦ ENNReal.toReal_nonneg)

theorem log_four_sq_le (r : ℕ) (hr : 0 < r) :
    Real.log ((4 * r ^ 2 : ℕ) : ℝ) ≤ 2 * Real.log (r : ℝ) + 3 := by
  have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  push_cast
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  norm_num
  linarith

theorem planarPotentialKernel_log_upper (x : Site)
    (hx : 0 < siteNormInf x) :
    planarPotentialKernel x ≤
      (2 / Real.pi) * Real.log (siteNormInf x : ℝ) + 20 := by
  let r := siteNormInf x
  let M := 4 * r ^ 2 + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  have hr : 0 < r := hx
  have hrM : r ≤ M := by dsimp only [M]; nlinarith
  have htwoRM : 2 * r ≤ M := by dsimp only [M]; nlinarith
  have hprefix : finitePotentialKernel (2 * M) x ≤
      (1 / Real.pi) * (harmonic (4 * r ^ 2) : ℝ) + 3 := by
    calc
      finitePotentialKernel (2 * M) x ≤
          ∑ n ∈ Finset.range (2 * M), returnProb n :=
        finitePotentialKernel_le_originReturnPrefix _ _
      _ = 1 + ∑ j ∈ Finset.range (4 * r ^ 2), returnProb (2 * (j + 1)) := by
        dsimp only [M]
        exact originReturnPrefix_even (4 * r ^ 2)
      _ ≤ 1 + ((1 / Real.pi) * (harmonic (4 * r ^ 2) : ℝ) + 2) := by
        gcongr
        exact evenReturnSum_upper (4 * r ^ 2)
      _ = (1 / Real.pi) * (harmonic (4 * r ^ 2) : ℝ) + 3 := by ring
  have htail : planarPotentialKernel x ≤ finitePotentialKernel (2 * M) x + 7 := by
    obtain ⟨a, ha | ha⟩ := Int.even_or_odd' ((-x).1 + (-x).2)
    · have hb : (-x).1 - (-x).2 = 2 * (a - (-x).2) := by nlinarith
      obtain ⟨hpa, hpb⟩ := diagonal_parameters_le_two_norm_even ha hb
      change a.natAbs ≤ r at hpa
      change (a - (-x).2).natAbs ≤ r at hpb
      have ht := planarPotentialKernel_le_even_cutoff_add_tail ha hb hM
        (hpa.trans hrM) (hpb.trans hrM)
      have hMr : (0 : ℝ) < M := by exact_mod_cast hM
      have haR : (a.natAbs : ℝ) ≤ r := by exact_mod_cast hpa
      have hbR : ((a - (-x).2).natAbs : ℝ) ≤ r := by exact_mod_cast hpb
      have htailnum : 2 * (((a.natAbs : ℝ) ^ 2 +
          ((a - (-x).2).natAbs : ℝ) ^ 2) / (M : ℝ)) ≤ 7 := by
        rw [show 2 * (((a.natAbs : ℝ) ^ 2 +
          ((a - (-x).2).natAbs : ℝ) ^ 2) / (M : ℝ)) =
          (2 * ((a.natAbs : ℝ) ^ 2 +
            ((a - (-x).2).natAbs : ℝ) ^ 2)) / (M : ℝ) by ring]
        apply (div_le_iff₀ hMr).2
        dsimp only [M]
        push_cast
        nlinarith [sq_nonneg ((a.natAbs : ℝ) - r),
          sq_nonneg (((a - (-x).2).natAbs : ℝ) - r)]
      linarith
    · have hb : (-x).1 - (-x).2 = 2 * (a - (-x).2) + 1 := by nlinarith
      obtain ⟨hpa, hpb⟩ := diagonal_parameters_le_two_norm_odd ha hb
      change a.natAbs ≤ 2 * r at hpa
      change (a - (-x).2).natAbs ≤ 2 * r at hpb
      have ht := planarPotentialKernel_le_odd_cutoff_add_tail ha hb hM
        (hpa.trans htwoRM) (hpb.trans htwoRM)
      have hMr : (0 : ℝ) < M := by exact_mod_cast hM
      have hd₁ : oddModeDistance a ≤ 2 * r :=
        (oddModeDistance_le_natAbs a).trans hpa
      have hd₂ : oddModeDistance (a - (-x).2) ≤ 2 * r :=
        (oddModeDistance_le_natAbs (a - (-x).2)).trans hpb
      have hd₁R : (oddModeDistance a : ℝ) ≤ 2 * r := by exact_mod_cast hd₁
      have hd₂R : (oddModeDistance (a - (-x).2) : ℝ) ≤ 2 * r := by exact_mod_cast hd₂
      have htailnum : 2 * ((2 + (oddModeDistance a : ℝ) *
          (oddModeDistance a + 1) +
          (oddModeDistance (a - (-x).2) : ℝ) *
            (oddModeDistance (a - (-x).2) + 1)) / (M : ℝ)) ≤ 7 := by
        rw [show 2 * ((2 + (oddModeDistance a : ℝ) *
          (oddModeDistance a + 1) +
          (oddModeDistance (a - (-x).2) : ℝ) *
            (oddModeDistance (a - (-x).2) + 1)) / (M : ℝ)) =
          (2 * (2 + (oddModeDistance a : ℝ) *
            (oddModeDistance a + 1) +
            (oddModeDistance (a - (-x).2) : ℝ) *
              (oddModeDistance (a - (-x).2) + 1))) / (M : ℝ) by ring]
        apply (div_le_iff₀ hMr).2
        dsimp only [M]
        push_cast
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ oddModeDistance a by positivity)
            (sub_nonneg.mpr hd₁R),
          mul_nonneg (show (0 : ℝ) ≤ oddModeDistance (a - (-x).2) by positivity)
            (sub_nonneg.mpr hd₂R),
          (show (1 : ℝ) ≤ r by exact_mod_cast hr)]
      linarith
  have hharm := harmonic_le_one_add_log (4 * r ^ 2)
  push_cast at hharm
  have hlog := log_four_sq_le r hx
  push_cast at hlog
  have hpi : (1 : ℝ) ≤ Real.pi := (by norm_num : (1 : ℝ) ≤ 3).trans Real.pi_gt_three.le
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hscaled : (1 / Real.pi) * (harmonic (4 * r ^ 2) : ℝ) ≤
      (2 / Real.pi) * Real.log (r : ℝ) + 4 := by
    have hbase : (harmonic (4 * r ^ 2) : ℝ) ≤
        2 * Real.log (r : ℝ) + 4 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ 1 / Real.pi)
    have hinv : 1 / Real.pi ≤ 1 := (div_le_one hpi0).2 hpi
    calc
      (1 / Real.pi) * (harmonic (4 * r ^ 2) : ℝ) ≤
          (1 / Real.pi) * (2 * Real.log (r : ℝ) + 4) := hmul
      _ = (2 / Real.pi) * Real.log (r : ℝ) + 4 / Real.pi := by ring
      _ ≤ (2 / Real.pi) * Real.log (r : ℝ) + 4 := by
        gcongr
        exact (div_le_iff₀ hpi0).2 (by nlinarith)
  dsimp only [r] at hprefix htail hscaled ⊢
  linarith

def oppositeDirection (d : Direction) : Direction :=
  match d.1 with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | _ => 2

@[simp] theorem oppositeDirection_involutive (d : Direction) :
    oppositeDirection (oppositeDirection d) = d := by
  fin_cases d <;> rfl

theorem directionStep_opposite (d : Direction) :
    directionStep (oppositeDirection d) = -directionStep d := by
  fin_cases d <;> norm_num [oppositeDirection, directionStep]

def negatePrefix {n : ℕ} (w : Prefix n) : Prefix n :=
  fun i ↦ oppositeDirection (w i)

@[simp] theorem negatePrefix_involutive {n : ℕ} (w : Prefix n) :
    negatePrefix (negatePrefix w) = w := by
  funext i
  simp [negatePrefix]

theorem finitePosition_negatePrefix {n : ℕ} (w : Prefix n) :
    finitePosition (negatePrefix w) = - finitePosition w := by
  unfold finitePosition negatePrefix
  simp_rw [directionStep_opposite]
  rw [Finset.sum_neg_distrib]

def endpointPrefixesNegEquiv (n : ℕ) (y : Site) :
    ↑(endpointPrefixes n y) ≃ ↑(endpointPrefixes n (-y)) where
  toFun w := by
    refine ⟨negatePrefix w.1, ?_⟩
    have hw : finitePosition w.1 = y := by
      simpa [endpointPrefixes] using w.2
    simp [endpointPrefixes, finitePosition_negatePrefix, hw]
  invFun w := by
    refine ⟨negatePrefix w.1, ?_⟩
    have hw : finitePosition w.1 = -y := by
      simpa [endpointPrefixes] using w.2
    simp [endpointPrefixes, finitePosition_negatePrefix, hw]
  left_inv w := by
    apply Subtype.ext
    simp
  right_inv w := by
    apply Subtype.ext
    simp

theorem endpointPrefixes_card_neg (n : ℕ) (y : Site) :
    (endpointPrefixes n (-y)).card = (endpointPrefixes n y).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (endpointPrefixesNegEquiv n y).symm

theorem increment_position_real_neg (n : ℕ) (y : Site) :
    incrementLaw.real {ω | simpleRandomWalk ω n = -y} =
      incrementLaw.real {ω | simpleRandomWalk ω n = y} := by
  change (incrementLaw {ω | simpleRandomWalk ω n = -y}).toReal =
    (incrementLaw {ω | simpleRandomWalk ω n = y}).toReal
  rw [increment_position_prob_eq_card n (-y),
    increment_position_prob_eq_card n y, endpointPrefixes_card_neg]

theorem freeOriginWeight_neg (x : Site) (n : ℕ) :
    (freeOriginWeight (-x) n).toReal = (freeOriginWeight x n).toReal := by
  rw [freeOriginWeight_eq_position_real, freeOriginWeight_eq_position_real]
  simpa using increment_position_real_neg n (-x)

theorem finitePotentialKernel_neg (x : Site) (N : ℕ) :
    finitePotentialKernel N (-x) = finitePotentialKernel N x := by
  unfold finitePotentialKernel
  apply Finset.sum_congr rfl
  intro n hn
  rw [freeOriginWeight_neg]

theorem planarPotentialKernel_neg (x : Site) :
    planarPotentialKernel (-x) = planarPotentialKernel x := by
  have hneg := finitePotentialKernel_tendsto_planarPotentialKernel (-x)
  have hx := finitePotentialKernel_tendsto_planarPotentialKernel x
  rw [show (fun N ↦ finitePotentialKernel N (-x)) =
      (fun N ↦ finitePotentialKernel N x) by
    funext N
    exact finitePotentialKernel_neg x N] at hneg
  exact tendsto_nhds_unique hneg hx

theorem siteNormInf_le_of_mem_squareDisk {R : ℕ} {x : Site}
    (hx : x ∈ squareDisk R) : siteNormInf x ≤ R := by
  unfold squareDisk at hx
  have hx' := Finset.mem_product.mp hx
  simp only [Finset.mem_Icc] at hx'
  unfold siteNormInf
  apply max_le
  · have hc : (x.1.natAbs : ℤ) ≤ (R : ℤ) := by
      rw [Int.natCast_natAbs]
      exact (abs_le.mpr hx'.1)
    exact_mod_cast hc
  · have hc : (x.2.natAbs : ℤ) ≤ (R : ℤ) := by
      rw [Int.natCast_natAbs]
      exact (abs_le.mpr hx'.2)
    exact_mod_cast hc

theorem siteNormInf_add_le (x y : Site) :
    siteNormInf (x + y) ≤ siteNormInf x + siteNormInf y := by
  unfold siteNormInf
  have h₁ := Int.natAbs_add_le x.1 y.1
  have h₂ := Int.natAbs_add_le x.2 y.2
  simp only [Prod.fst_add, Prod.snd_add]
  omega

theorem siteNormInf_sub_le (x y : Site) :
    siteNormInf (x - y) ≤ siteNormInf x + siteNormInf y := by
  simpa [sub_eq_add_neg, siteNormInf_neg] using siteNormInf_add_le x (-y)

theorem siteNormInf_pos_of_ne_zero {x : Site} (hx : x ≠ 0) :
    0 < siteNormInf x := by
  apply Nat.pos_of_ne_zero
  intro hzero
  unfold siteNormInf at hzero
  have h₁ : x.1.natAbs = 0 := by omega
  have h₂ : x.2.natAbs = 0 := by omega
  apply hx
  apply Prod.ext <;> simp_all

/-- A uniform quasi-triangle inequality. This weaker estimate is enough for
the punctured-Green argument: its fixed additive error can be absorbed into
the logarithmic outer scale. -/
theorem planarPotentialKernel_quasiTriangle (w z : Site) :
    planarPotentialKernel w ≤
      planarPotentialKernel (w - z) + planarPotentialKernel z + 2500 := by
  let u : Site := w - z
  have hwu : w = u + z := by dsimp only [u]; abel
  by_cases hu0 : u = 0
  · have : w = z := by simpa [hu0] using hwu
    change planarPotentialKernel w ≤
      planarPotentialKernel u + planarPotentialKernel z + 2500
    rw [this, hu0, planarPotentialKernel_zero]
    linarith
  by_cases hz0 : z = 0
  · have : u = w := by simp [u, hz0]
    change planarPotentialKernel w ≤
      planarPotentialKernel u + planarPotentialKernel z + 2500
    rw [this, hz0, planarPotentialKernel_zero]
    linarith
  have huNorm : 0 < siteNormInf u := siteNormInf_pos_of_ne_zero hu0
  have hzNorm : 0 < siteNormInf z := siteNormInf_pos_of_ne_zero hz0
  have hlu := planarPotentialKernel_log_lower u huNorm
  have hlz := planarPotentialKernel_log_lower z hzNorm
  by_cases hw0 : w = 0
  · have haw : planarPotentialKernel w = 0 := by simp [hw0]
    rw [haw]
    have hlogu : 0 ≤ Real.log (siteNormInf u : ℝ) :=
      Real.log_natCast_nonneg _
    have hlogz : 0 ≤ Real.log (siteNormInf z : ℝ) :=
      Real.log_natCast_nonneg _
    have hc : 0 ≤ 2 / Real.pi := by positivity
    nlinarith [mul_nonneg hc hlogu, mul_nonneg hc hlogz]
  have hwNorm : 0 < siteNormInf w := siteNormInf_pos_of_ne_zero hw0
  have huw : siteNormInf w ≤ siteNormInf u + siteNormInf z := by
    rw [hwu]
    exact siteNormInf_add_le u z
  have hprodNat : siteNormInf u + siteNormInf z ≤
      2 * siteNormInf u * siteNormInf z := by
    have huMul : siteNormInf u ≤ siteNormInf u * siteNormInf z :=
      Nat.le_mul_of_pos_right _ hzNorm
    have hzMul : siteNormInf z ≤ siteNormInf u * siteNormInf z := by
      simpa [mul_comm] using Nat.le_mul_of_pos_right (siteNormInf z) huNorm
    calc
      siteNormInf u + siteNormInf z ≤
          siteNormInf u * siteNormInf z + siteNormInf u * siteNormInf z :=
        Nat.add_le_add huMul hzMul
      _ = 2 * siteNormInf u * siteNormInf z := by ring
  have hlog : Real.log (siteNormInf w : ℝ) ≤
      Real.log (2 * siteNormInf u * siteNormInf z : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · change 0 < (siteNormInf w : ℝ)
      exact_mod_cast hwNorm
    · simp only [Set.mem_Ioi]
      positivity
    · exact_mod_cast huw.trans hprodNat
  have hlogProd : Real.log (2 * siteNormInf u * siteNormInf z : ℝ) =
      Real.log 2 + Real.log (siteNormInf u : ℝ) +
        Real.log (siteNormInf z : ℝ) := by
    push_cast
    rw [Real.log_mul (mul_ne_zero (by norm_num) (by positivity)) (by positivity),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
  rw [hlogProd] at hlog
  have hupper := planarPotentialKernel_log_upper w hwNorm
  have hc0 : 0 ≤ 2 / Real.pi := by positivity
  have hc1 : 2 / Real.pi ≤ 1 := by
    apply (div_le_one Real.pi_pos).2
    linarith [Real.pi_gt_three]
  have hlog2nonneg : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlog2le : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hlog hc0
  have hextra : (2 / Real.pi) * Real.log 2 ≤ 1 :=
    (mul_le_mul hc1 hlog2le hlog2nonneg (by norm_num)).trans_eq (one_mul 1)
  nlinarith

theorem planarPotentialKernel_boundary_upper {R : ℕ} {z : Site}
    (hz : z ∈ squareDisk (R + 1)) :
    planarPotentialKernel z ≤
      (2 / Real.pi) * Real.log ((R + 1 : ℕ) : ℝ) + 20 := by
  by_cases hz0 : z = 0
  · subst z
    rw [planarPotentialKernel_zero]
    have hlog : 0 ≤ Real.log ((R + 1 : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ R + 1 by omega)
    positivity
  · have hnorm0 := siteNormInf_pos_of_ne_zero hz0
    have hu := planarPotentialKernel_log_upper z hnorm0
    have hnorm := siteNormInf_le_of_mem_squareDisk hz
    have hlog : Real.log (siteNormInf z : ℝ) ≤
        Real.log ((R + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hnorm
    have hcoef : 0 ≤ 2 / Real.pi := by positivity
    nlinarith

theorem diskGreen_toReal_le_log_ratio_add
    {R : ℕ} {y : Site} (hy : y ∈ squareDisk R)
    (hy0 : 0 < siteNormInf y) :
    (diskGreen R y 0).toReal ≤
      (2 / Real.pi) *
        (Real.log ((R + 1 : ℕ) : ℝ) - Real.log (siteNormInf y : ℝ)) +
      1245 := by
  have h := diskGreen_toReal_le_potential_oscillation
    (R := R) (y := y) planarPotentialKernel_isPlanar
    (upper := (2 / Real.pi) * Real.log ((R + 1 : ℕ) : ℝ) + 20)
    (lower := (2 / Real.pi) * Real.log (siteNormInf y : ℝ) - 1225)
    (by
      intro z hz hzo
      exact planarPotentialKernel_boundary_upper hz)
    hy (planarPotentialKernel_log_lower y hy0)
  convert h using 1 <;> ring

theorem hitZeroBeforeExit_real_le_log_ratio_add
    {R : ℕ} (hR : 2 ≤ R) {y : Site} (hy : y ∈ squareDisk R)
    (hy0 : 0 < siteNormInf y) :
    incrementLaw.real
        (hitBeforeExitEvent (squareDisk R : Set Site) y 0) ≤
      8 * ((2 / Real.pi) *
        (Real.log ((R + 1 : ℕ) : ℝ) - Real.log (siteNormInf y : ℝ)) +
        1245) / Real.log (R : ℝ) := by
  apply hitZeroBeforeExit_real_le_of_diskGreen_le hR y
  exact diskGreen_toReal_le_log_ratio_add hy hy0

end Erdos1166.PotentialConvergence
