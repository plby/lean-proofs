/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZGreenBounds

namespace Erdos1166.HeatKernel

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable def binomMass (n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) / (2 : ℝ) ^ n

theorem binomMass_nonneg (n k : ℕ) : 0 ≤ binomMass n k := by
  unfold binomMass
  positivity

theorem binomMass_previous (n k : ℕ) (hk : k < n) :
    binomMass n k = (((k + 1 : ℕ) : ℝ) / ((n - k : ℕ) : ℝ)) *
      binomMass n (k + 1) := by
  unfold binomMass
  have h := Nat.choose_succ_right_eq n k
  have hden : (((n - k : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hk).ne'
  field_simp [hden]
  exact_mod_cast (by simpa [mul_comm] using h.symm)

theorem one_sub_le_exp_neg (x : ℝ) : 1 - x ≤ Real.exp (-x) := by
  simpa [add_comm] using Real.add_one_le_exp (-x)

theorem lower_ratio_le_exp
    {n m d : ℕ} (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1)
    (hd : d + 1 ≤ m) :
    (((m - d : ℕ) : ℝ) / ((n - (m - d - 1) : ℕ) : ℝ)) ≤
      Real.exp (- (2 * (d : ℝ) / ((n + 1 : ℕ) : ℝ))) := by
  have hmpos : 0 < m - d := by omega
  have hdenpos : 0 < n - (m - d - 1) := by omega
  have hdenle : n - (m - d - 1) ≤ n + 1 := by omega
  have hgap : m - d + 2 * d ≤ n - (m - d - 1) := by omega
  have hcross :
      (n + 1) * (m - d) + 2 * d * (n - (m - d - 1)) ≤
        (n + 1) * (n - (m - d - 1)) := by
    nlinarith
  have hfrac :
      (((m - d : ℕ) : ℝ) / ((n - (m - d - 1) : ℕ) : ℝ)) ≤
        1 - (2 * (d : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    apply (div_le_iff₀ (by positivity :
      (0 : ℝ) < ((n - (m - d - 1) : ℕ) : ℝ))).2
    have hcrossR :
        (((n + 1 : ℕ) : ℝ) * ((m - d : ℕ) : ℝ) +
            2 * (d : ℝ) * ((n - (m - d - 1) : ℕ) : ℝ)) ≤
          ((n + 1 : ℕ) : ℝ) * ((n - (m - d - 1) : ℕ) : ℝ) := by
      exact_mod_cast hcross
    apply le_of_mul_le_mul_right (a := (((n + 1 : ℕ) : ℝ))) ?_ (by positivity)
    field_simp
    nlinarith
  exact hfrac.trans (one_sub_le_exp_neg _)

/-- A central-binomial atom loses a Gaussian factor at distance `d` below
the center.  The exponent is deliberately weakened to make both parities
uniform. -/
theorem binomMass_lower_gaussian
    {n m d : ℕ} (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1) (hd : d ≤ m) :
    binomMass n (m - d) ≤
      Real.exp (- ((d : ℝ) * (d - 1) / ((n + 1 : ℕ) : ℝ))) *
        binomMass n m := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hd' : d ≤ m := by omega
      have hk : m - (d + 1) < n := by omega
      rw [binomMass_previous n (m - (d + 1)) hk]
      have hindex : m - (d + 1) + 1 = m - d := by omega
      rw [hindex]
      calc
        (((m - d : ℕ) : ℝ) / ((n - (m - (d + 1)) : ℕ) : ℝ)) *
            binomMass n (m - d) ≤
          Real.exp (- (2 * (d : ℝ) / ((n + 1 : ℕ) : ℝ))) *
            binomMass n (m - d) := by
          exact mul_le_mul_of_nonneg_right
            (lower_ratio_le_exp hm hm' (by omega)) (binomMass_nonneg _ _)
        _ ≤ Real.exp (- (2 * (d : ℝ) / ((n + 1 : ℕ) : ℝ))) *
            (Real.exp (- ((d : ℝ) * (d - 1) / ((n + 1 : ℕ) : ℝ))) *
              binomMass n m) := by
          exact mul_le_mul_of_nonneg_left (ih hd') (Real.exp_nonneg _)
        _ = Real.exp (- (((d + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) - 1) /
              ((n + 1 : ℕ) : ℝ))) * binomMass n m := by
          calc
            _ = (Real.exp (- (2 * (d : ℝ) / ((n + 1 : ℕ) : ℝ))) *
                  Real.exp (- ((d : ℝ) * (d - 1) / ((n + 1 : ℕ) : ℝ)))) *
                  binomMass n m := by ring
            _ = Real.exp (- (2 * (d : ℝ) / ((n + 1 : ℕ) : ℝ)) +
                  - ((d : ℝ) * (d - 1) / ((n + 1 : ℕ) : ℝ))) *
                  binomMass n m := by rw [Real.exp_add]
            _ = _ := by
              congr 2
              push_cast
              field_simp
              ring

theorem binomMass_le_middle (n k : ℕ) :
    binomMass n k ≤ binomMass n (n / 2) := by
  unfold binomMass
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.choose_le_middle k n) (by positivity)

theorem binomMass_even_middle_sq_le (m : ℕ) :
    binomMass (2 * m) m ^ 2 ≤ 2 / (((2 * m + 1 : ℕ) : ℝ)) := by
  have h := return_real_le_two_div_succ (2 * m)
  rw [return_real_even] at h
  have hpow : ((2 : ℝ) ^ (2 * m)) ^ 2 = (4 : ℝ) ^ (2 * m) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, pow_mul, ← pow_mul]
    congr 1
    omega
  rw [binomMass, div_pow, hpow]
  convert h using 1
  all_goals push_cast
  all_goals ring

theorem choose_odd_middle_le_two_mul_even (m : ℕ) :
    Nat.choose (2 * m + 1) m ≤ 2 * Nat.choose (2 * m) m := by
  cases m with
  | zero => simp
  | succ m =>
      rw [show 2 * (m + 1) + 1 = (2 * (m + 1)) + 1 by omega,
        show m + 1 = m + 1 by rfl, Nat.choose_succ_succ]
      calc
        Nat.choose (2 * (m + 1)) m + Nat.choose (2 * (m + 1)) (m + 1) ≤
            Nat.centralBinom (m + 1) + Nat.centralBinom (m + 1) :=
          Nat.add_le_add (Nat.choose_le_centralBinom m (m + 1))
            (Nat.choose_le_centralBinom (m + 1) (m + 1))
        _ = 2 * Nat.choose (2 * (m + 1)) (m + 1) := by
          simp [Nat.centralBinom, two_mul]

theorem binomMass_odd_middle_le_even (m : ℕ) :
    binomMass (2 * m + 1) m ≤ binomMass (2 * m) m := by
  unfold binomMass
  have h := choose_odd_middle_le_two_mul_even m
  have hR : ((Nat.choose (2 * m + 1) m : ℕ) : ℝ) ≤
      2 * (Nat.choose (2 * m) m : ℝ) := by exact_mod_cast h
  rw [pow_succ]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (2 * m)]

theorem binomMass_middle_sq_le_four_div_succ (n : ℕ) :
    binomMass n (n / 2) ^ 2 ≤ 4 / ((n + 1 : ℕ) : ℝ) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hmid : (2 * m) / 2 = m := by omega
    rw [hmid]
    exact (binomMass_even_middle_sq_le m).trans (by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      push_cast
      nlinarith)
  · have hmid : (2 * m + 1) / 2 = m := by omega
    rw [hmid]
    calc
      binomMass (2 * m + 1) m ^ 2 ≤ binomMass (2 * m) m ^ 2 := by
        exact pow_le_pow_left₀ (binomMass_nonneg _ _)
          (binomMass_odd_middle_le_even m) 2
      _ ≤ 2 / (((2 * m + 1 : ℕ) : ℝ)) := binomMass_even_middle_sq_le m
      _ ≤ 4 / (((2 * m + 1 + 1 : ℕ) : ℝ)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        push_cast
        nlinarith

def modeDistance (n k : ℕ) : ℕ :=
  if k ≤ n / 2 then n / 2 - k else k - (n + 1) / 2

theorem binomMass_gaussian_mode (n k : ℕ) :
    binomMass n k ≤
      Real.exp (- (((modeDistance n k : ℕ) : ℝ) *
        ((modeDistance n k : ℕ) - 1) / ((n + 1 : ℕ) : ℝ))) *
        binomMass n (n / 2) := by
  by_cases hkn : k ≤ n
  · have hfloor : 2 * (n / 2) ≤ n := by omega
    have hceil : n ≤ 2 * (n / 2) + 1 := by omega
    by_cases hk : k ≤ n / 2
    · have hsub : n / 2 - (n / 2 - k) = k := by omega
      simpa [modeDistance, hk, hsub] using
        (binomMass_lower_gaussian hfloor hceil
          (show n / 2 - k ≤ n / 2 by omega))
    · have hnkfloor : n - k ≤ n / 2 := by omega
      have hsub : n / 2 - (n / 2 - (n - k)) = n - k := by omega
      have hdist : n / 2 - (n - k) = k - (n + 1) / 2 := by omega
      rw [binomMass, ← Nat.choose_symm hkn]
      change binomMass n (n - k) ≤ _
      have hg := binomMass_lower_gaussian (d := n / 2 - (n - k))
        hfloor hceil (show n / 2 - (n - k) ≤ n / 2 by omega)
      rw [hsub] at hg
      rw [hdist] at hg
      simpa [modeDistance, hk] using hg
  · have hzero : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt (lt_of_not_ge hkn)
    rw [binomMass, hzero]
    simp only [Nat.cast_zero, zero_div]
    exact mul_nonneg (Real.exp_nonneg _) (binomMass_nonneg _ _)

def endpointPrefixes (n : ℕ) (y : Site) : Finset (Prefix n) :=
  Finset.univ.filter fun w ↦ finitePosition w = y

theorem finitePosition_eq_iff_balanced
    {n j₁ j₂ : ℕ} {y : Site}
    (h₁ : (n : ℤ) - 2 * (j₁ : ℤ) = y.1 + y.2)
    (h₂ : (n : ℤ) - 2 * (j₂ : ℤ) = y.1 - y.2)
    (w : Prefix n) :
    finitePosition w = y ↔
      (truePositions (prefixBitsEquiv n w).1).card = j₁ ∧
      (truePositions (prefixBitsEquiv n w).2).card = j₂ := by
  have hd₁ := diagonal_sum_one w
  have hd₂ := diagonal_sum_two w
  rw [sum_boolSign_eq_card_sub_twice] at hd₁ hd₂
  simp only [Fintype.card_coe, Finset.card_range] at hd₁ hd₂
  change (n : ℤ) - 2 * ((truePositions (prefixBitsEquiv n w).1).card : ℤ) =
    (finitePosition w).1 + (finitePosition w).2 at hd₁
  change (n : ℤ) - 2 * ((truePositions (prefixBitsEquiv n w).2).card : ℤ) =
    (finitePosition w).1 - (finitePosition w).2 at hd₂
  constructor
  · intro hw
    rw [hw] at hd₁ hd₂
    constructor <;> exact_mod_cast (by omega)
  · rintro ⟨hc₁, hc₂⟩
    rw [hc₁] at hd₁
    rw [hc₂] at hd₂
    apply Prod.ext
    · omega
    · omega

def endpointEquivBalanced
    (n j₁ j₂ : ℕ) (y : Site)
    (h₁ : (n : ℤ) - 2 * (j₁ : ℤ) = y.1 + y.2)
    (h₂ : (n : ℤ) - 2 * (j₂ : ℤ) = y.1 - y.2) :
    ↑(endpointPrefixes n y) ≃
      BalancedBits ↑(Finset.range n) j₁ ×
        BalancedBits ↑(Finset.range n) j₂ where
  toFun w := by
    have hw : finitePosition w.1 = y := by
      simpa [endpointPrefixes] using w.2
    have hb := (finitePosition_eq_iff_balanced h₁ h₂ w.1).mp hw
    exact (⟨(prefixBitsEquiv n w.1).1, hb.1⟩,
      ⟨(prefixBitsEquiv n w.1).2, hb.2⟩)
  invFun uv := by
    let w := (prefixBitsEquiv n).symm (uv.1.1, uv.2.1)
    refine ⟨w, ?_⟩
    simp only [endpointPrefixes, Finset.mem_filter, Finset.mem_univ, true_and]
    apply (finitePosition_eq_iff_balanced h₁ h₂ w).mpr
    simpa [w] using And.intro uv.1.2 uv.2.2
  left_inv w := by
    apply Subtype.ext
    simp
  right_inv uv := by
    rcases uv with ⟨u, v⟩
    apply Prod.ext <;> apply Subtype.ext <;> simp

theorem endpointPrefixes_card
    {n j₁ j₂ : ℕ} {y : Site}
    (h₁ : (n : ℤ) - 2 * (j₁ : ℤ) = y.1 + y.2)
    (h₂ : (n : ℤ) - 2 * (j₂ : ℤ) = y.1 - y.2) :
    (endpointPrefixes n y).card = n.choose j₁ * n.choose j₂ := by
  rw [← Fintype.card_coe]
  rw [Fintype.card_congr (endpointEquivBalanced n j₁ j₂ y h₁ h₂),
    Fintype.card_prod, card_balancedBits, card_balancedBits]
  simp

theorem increment_position_prob_eq_card (n : ℕ) (y : Site) :
    incrementLaw {ω | simpleRandomWalk ω n = y} =
      (endpointPrefixes n y).card / (4 : ℝ≥0∞) ^ n := by
  let A := endpointPrefixes n y
  calc
    incrementLaw {ω | simpleRandomWalk ω n = y} =
        (incrementLaw.map (Finset.range n).restrict) (A : Set (Prefix n)) := by
      rw [Measure.map_apply]
      · congr 1
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Finset.mem_coe,
          A, endpointPrefixes, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [finitePosition_restrict]
      · fun_prop
      · measurability
    _ = prefixLaw n (A : Set (Prefix n)) := by rw [increment_restrict_map]
    _ = ∑ w ∈ A, prefixLaw n {w} := by rw [sum_measure_singleton]
    _ = ∑ _w ∈ A, (4 : ℝ≥0∞)⁻¹ ^ n := by
      apply Finset.sum_congr rfl
      intro w hw
      exact prefixLaw_singleton n w
    _ = (A.card : ℝ≥0∞) / (4 : ℝ≥0∞) ^ n := by
      simp [div_eq_mul_inv, ENNReal.inv_pow]
    _ = (endpointPrefixes n y).card / (4 : ℝ≥0∞) ^ n := by rfl

theorem increment_position_real_eq_binomMass_mul
    {n j₁ j₂ : ℕ} {y : Site}
    (h₁ : (n : ℤ) - 2 * (j₁ : ℤ) = y.1 + y.2)
    (h₂ : (n : ℤ) - 2 * (j₂ : ℤ) = y.1 - y.2) :
    incrementLaw.real {ω | simpleRandomWalk ω n = y} =
      binomMass n j₁ * binomMass n j₂ := by
  rw [Measure.real, increment_position_prob_eq_card, endpointPrefixes_card h₁ h₂]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]
  unfold binomMass
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  push_cast
  field_simp

def siteNormInf (y : Site) : ℕ := max y.1.natAbs y.2.natAbs

theorem siteNormInf_le_diagonalMax (y : Site) :
    siteNormInf y ≤ max (y.1 + y.2).natAbs (y.1 - y.2).natAbs := by
  let M := max (y.1 + y.2).natAbs (y.1 - y.2).natAbs
  have hu : (y.1 + y.2).natAbs ≤ M := le_max_left _ _
  have hv : (y.1 - y.2).natAbs ≤ M := le_max_right _ _
  have ha : 2 * y.1.natAbs ≤ (y.1 + y.2).natAbs + (y.1 - y.2).natAbs := by
    have h := Int.natAbs_add_le (y.1 + y.2) (y.1 - y.2)
    have heq : (y.1 + y.2) + (y.1 - y.2) = 2 * y.1 := by ring
    rw [heq, Int.natAbs_mul] at h
    norm_num at h
    exact h
  have hb : 2 * y.2.natAbs ≤ (y.1 + y.2).natAbs + (y.1 - y.2).natAbs := by
    have h := Int.natAbs_sub_le (y.1 + y.2) (y.1 - y.2)
    have heq : (y.1 + y.2) - (y.1 - y.2) = 2 * y.2 := by ring
    rw [heq, Int.natAbs_mul] at h
    norm_num at h
    exact h
  unfold siteNormInf
  omega

theorem natAbs_diagonal_le_modeDistance
    {n j : ℕ} {s : ℤ} (_hj : j ≤ n)
    (hs : (n : ℤ) - 2 * (j : ℤ) = s) :
    s.natAbs ≤ 2 * modeDistance n j + 1 := by
  by_cases hlow : j ≤ n / 2
  · have hsnonneg : 0 ≤ s := by rw [← hs]; omega
    have hnat : s.natAbs = n - 2 * j := by
      apply Int.ofNat_inj.mp
      rw [Int.natCast_natAbs, abs_of_nonneg hsnonneg,
        Nat.cast_sub (show 2 * j ≤ n by omega)]
      push_cast
      omega
    rw [hnat]
    simp only [modeDistance, if_pos hlow]
    omega
  · have hsnonpos : s ≤ 0 := by rw [← hs]; omega
    have hnat : s.natAbs = 2 * j - n := by
      apply Int.ofNat_inj.mp
      rw [Int.natCast_natAbs, abs_of_nonpos hsnonpos,
        Nat.cast_sub (show n ≤ 2 * j by omega)]
      push_cast
      omega
    rw [hnat]
    simp only [modeDistance, if_neg hlow]
    omega

theorem norm_sq_le_mode_cost
    {r d : ℕ} (hrd : r ≤ 2 * d + 1) :
    r ^ 2 ≤ 32 * (d * (d - 1) + 1) := by
  cases d with
  | zero =>
      simp at hrd ⊢
      interval_cases r <;> norm_num
  | succ d =>
      simp only [Nat.succ_sub_one]
      nlinarith

theorem exp_neg_modeCost_le_three_mul_exp_neg_norm
    {n r d : ℕ} (hrd : r ≤ 2 * d + 1) :
    Real.exp (- ((d : ℝ) * ((d : ℝ) - 1) / ((n + 1 : ℕ) : ℝ))) ≤
      3 * Real.exp (- ((r : ℝ) ^ 2 /
        (32 * ((n + 1 : ℕ) : ℝ)))) := by
  have hsq := norm_sq_le_mode_cost hrd
  have hsqR : (r : ℝ) ^ 2 ≤
      32 * (((d * (d - 1) + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hsq
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hcostcast : (d : ℝ) * ((d : ℝ) - 1) =
      (((d * (d - 1) : ℕ) : ℝ)) := by
    cases d <;> push_cast <;> ring
  have hprodcast : (((d * (d - 1) : ℕ) : ℝ)) =
      (d : ℝ) * ((d - 1 : ℕ) : ℝ) := by push_cast; rfl
  have hle :
      - ((d : ℝ) * ((d : ℝ) - 1) / ((n + 1 : ℕ) : ℝ)) ≤
        1 - (r : ℝ) ^ 2 / (32 * ((n + 1 : ℕ) : ℝ)) := by
    push_cast at hsqR
    rw [← hprodcast] at hsqR
    rw [hcostcast]
    field_simp [ne_of_gt hN]
    nlinarith
  calc
    Real.exp (- ((d : ℝ) * ((d : ℝ) - 1) / ((n + 1 : ℕ) : ℝ))) ≤
        Real.exp (1 - (r : ℝ) ^ 2 /
          (32 * ((n + 1 : ℕ) : ℝ))) := Real.exp_le_exp.mpr hle
    _ = Real.exp 1 * Real.exp (- ((r : ℝ) ^ 2 /
          (32 * ((n + 1 : ℕ) : ℝ)))) := by
      rw [sub_eq_add_neg, Real.exp_add]
    _ ≤ 3 * Real.exp (- ((r : ℝ) ^ 2 /
          (32 * ((n + 1 : ℕ) : ℝ)))) := by
      exact mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_nonneg _)

theorem binomMass_mul_le_heat_of_norm_le_mode
    {n j k r : ℕ} (hr : r ≤ 2 * modeDistance n j + 1) :
    binomMass n j * binomMass n k ≤
      (12 / ((n + 1 : ℕ) : ℝ)) *
        Real.exp (- ((r : ℝ) ^ 2 /
          (32 * ((n + 1 : ℕ) : ℝ)))) := by
  let d := modeDistance n j
  let M := binomMass n (n / 2)
  let E := Real.exp (- ((d : ℝ) * ((d : ℝ) - 1) /
    ((n + 1 : ℕ) : ℝ)))
  let H := Real.exp (- ((r : ℝ) ^ 2 /
    (32 * ((n + 1 : ℕ) : ℝ))))
  have hj : binomMass n j ≤ E * M := by
    simpa [d, M, E, Nat.cast_mul] using binomMass_gaussian_mode n j
  have hk : binomMass n k ≤ M := by
    simpa [M] using binomMass_le_middle n k
  have hM : M ^ 2 ≤ 4 / ((n + 1 : ℕ) : ℝ) := by
    simpa [M] using binomMass_middle_sq_le_four_div_succ n
  have hMnonneg : 0 ≤ M := by
    simpa [M] using binomMass_nonneg n (n / 2)
  have hE : E ≤ 3 * H := by
    simpa [d, E, H] using
      (exp_neg_modeCost_le_three_mul_exp_neg_norm (n := n) (r := r)
        (d := d) (by simpa [d] using hr))
  calc
    binomMass n j * binomMass n k ≤ (E * M) * M := by
      exact mul_le_mul hj hk (binomMass_nonneg _ _) (mul_nonneg (Real.exp_nonneg _) hMnonneg)
    _ = E * M ^ 2 := by ring
    _ ≤ E * (4 / ((n + 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hM (by positivity [E])
    _ ≤ (3 * H) * (4 / ((n + 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hE (by positivity)
    _ = (12 / ((n + 1 : ℕ) : ℝ)) * H := by ring

theorem binomMass_mul_le_heat_of_norm_le_either_mode
    {n j₁ j₂ r : ℕ}
    (hr : r ≤ max (2 * modeDistance n j₁ + 1)
      (2 * modeDistance n j₂ + 1)) :
    binomMass n j₁ * binomMass n j₂ ≤
      (12 / ((n + 1 : ℕ) : ℝ)) *
        Real.exp (- ((r : ℝ) ^ 2 /
          (32 * ((n + 1 : ℕ) : ℝ)))) := by
  rcases (le_max_iff.mp hr) with hr | hr
  · exact binomMass_mul_le_heat_of_norm_le_mode hr
  · rw [mul_comm]
    exact binomMass_mul_le_heat_of_norm_le_mode hr

/-- Uniform Gaussian upper bound for the point mass of the planar simple
random walk.  `siteNormInf` is the lattice `ℓ∞` norm. -/
theorem increment_position_real_le_heatKernel (n : ℕ) (y : Site) :
    incrementLaw.real {ω | simpleRandomWalk ω n = y} ≤
      (12 / ((n + 1 : ℕ) : ℝ)) *
        Real.exp (- ((siteNormInf y : ℝ) ^ 2 /
          (32 * ((n + 1 : ℕ) : ℝ)))) := by
  classical
  let A := endpointPrefixes n y
  by_cases hA : A.Nonempty
  · obtain ⟨w, hw⟩ := hA
    have hwy : finitePosition w = y := by
      simpa [A, endpointPrefixes] using hw
    let j₁ := (truePositions (prefixBitsEquiv n w).1).card
    let j₂ := (truePositions (prefixBitsEquiv n w).2).card
    have hj₁ : j₁ ≤ n := by
      dsimp [j₁]
      simpa using Finset.card_le_univ (truePositions (prefixBitsEquiv n w).1)
    have hj₂ : j₂ ≤ n := by
      dsimp [j₂]
      simpa using Finset.card_le_univ (truePositions (prefixBitsEquiv n w).2)
    have h₁ : (n : ℤ) - 2 * (j₁ : ℤ) = y.1 + y.2 := by
      have hd := diagonal_sum_one w
      rw [sum_boolSign_eq_card_sub_twice] at hd
      simp only [Fintype.card_coe, Finset.card_range] at hd
      change (n : ℤ) - 2 * (j₁ : ℤ) =
        (finitePosition w).1 + (finitePosition w).2 at hd
      simpa [hwy] using hd
    have h₂ : (n : ℤ) - 2 * (j₂ : ℤ) = y.1 - y.2 := by
      have hd := diagonal_sum_two w
      rw [sum_boolSign_eq_card_sub_twice] at hd
      simp only [Fintype.card_coe, Finset.card_range] at hd
      change (n : ℤ) - 2 * (j₂ : ℤ) =
        (finitePosition w).1 - (finitePosition w).2 at hd
      simpa [hwy] using hd
    rw [increment_position_real_eq_binomMass_mul h₁ h₂]
    apply binomMass_mul_le_heat_of_norm_le_either_mode
    calc
      siteNormInf y ≤ max (y.1 + y.2).natAbs
          (y.1 - y.2).natAbs := siteNormInf_le_diagonalMax y
      _ ≤ max (2 * modeDistance n j₁ + 1)
          (2 * modeDistance n j₂ + 1) := by
        exact max_le_max (natAbs_diagonal_le_modeDistance hj₁ h₁)
          (natAbs_diagonal_le_modeDistance hj₂ h₂)
  · have hzero : endpointPrefixes n y = ∅ := by
      exact Finset.not_nonempty_iff_eq_empty.mp (by simpa [A] using hA)
    rw [Measure.real, increment_position_prob_eq_card, hzero]
    simp
    positivity

theorem killedWeight_toReal_le_free_neg
    (D : Set Site) (x : Site) (n : ℕ) :
    (KilledGreen.killedWeight D x 0 n).toReal ≤
      incrementLaw.real {ω | simpleRandomWalk ω n = -x} := by
  apply ENNReal.toReal_mono (measure_ne_top incrementLaw _)
  unfold KilledGreen.killedWeight
  apply measure_mono
  intro ω hω
  change simpleRandomWalk ω n = -x
  apply eq_neg_of_add_eq_zero_right
  simpa [KilledGreen.walkFrom] using hω.2

@[simp] theorem siteNormInf_neg (x : Site) : siteNormInf (-x) = siteNormInf x := by
  simp [siteNormInf]

theorem killedWeight_toReal_le_heatKernel
    (D : Set Site) (x : Site) (n : ℕ) :
    (KilledGreen.killedWeight D x 0 n).toReal ≤
      (12 / ((n + 1 : ℕ) : ℝ)) *
        Real.exp (- ((siteNormInf x : ℝ) ^ 2 /
          (32 * ((n + 1 : ℕ) : ℝ)))) := by
  calc
    (KilledGreen.killedWeight D x 0 n).toReal ≤
        incrementLaw.real {ω | simpleRandomWalk ω n = -x} :=
      killedWeight_toReal_le_free_neg D x n
    _ ≤ (12 / ((n + 1 : ℕ) : ℝ)) *
        Real.exp (- ((siteNormInf (-x) : ℝ) ^ 2 /
          (32 * ((n + 1 : ℕ) : ℝ)))) :=
      increment_position_real_le_heatKernel n (-x)
    _ = (12 / ((n + 1 : ℕ) : ℝ)) *
        Real.exp (- ((siteNormInf x : ℝ) ^ 2 /
          (32 * ((n + 1 : ℕ) : ℝ)))) := by simp

noncomputable def heatKernelBound (r n : ℕ) : ℝ :=
  (12 / ((n + 1 : ℕ) : ℝ)) *
    Real.exp (- ((r : ℝ) ^ 2 / (32 * ((n + 1 : ℕ) : ℝ))))

theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ x⁻¹ := by
  rw [Real.exp_neg]
  apply (inv_le_inv₀ (Real.exp_pos x) hx).2
  calc
    x ≤ 1 + x := by linarith
    _ ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x

theorem heatKernelBound_le_384_div_sq
    {r n : ℕ} (hr : 0 < r) :
    heatKernelBound r n ≤ 384 / (r : ℝ) ^ 2 := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  let x : ℝ := (r : ℝ) ^ 2 / (32 * ((n + 1 : ℕ) : ℝ))
  have hx : 0 < x := by
    dsimp [x]
    positivity
  calc
    heatKernelBound r n =
        (12 / ((n + 1 : ℕ) : ℝ)) * Real.exp (-x) := by
      rfl
    _ ≤ (12 / ((n + 1 : ℕ) : ℝ)) * x⁻¹ := by
      exact mul_le_mul_of_nonneg_left (exp_neg_le_inv hx) (by positivity)
    _ = 384 / (r : ℝ) ^ 2 := by
      dsimp [x]
      field_simp
      ring

theorem sum_heatKernelBound_before_sq_le (r : ℕ) :
    (∑ n ∈ Finset.range (r ^ 2), heatKernelBound r n) ≤ 384 := by
  by_cases hr : r = 0
  · simp [hr]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    calc
      (∑ n ∈ Finset.range (r ^ 2), heatKernelBound r n) ≤
          ∑ _n ∈ Finset.range (r ^ 2), 384 / (r : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro n _hn
        apply heatKernelBound_le_384_div_sq hrpos
      _ = 384 := by
        rw [Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul]
        push_cast
        field_simp

theorem reciprocal_succ_le_log_ratio {a : ℕ} (ha : 0 < a) :
    (1 : ℝ) / (a + 1 : ℕ) ≤
      Real.log ((((a + 1 : ℕ) : ℝ) / (a : ℝ))) := by
  have hratio : (0 : ℝ) < (((a + 1 : ℕ) : ℝ) / (a : ℝ)) := by positivity
  calc
    (1 : ℝ) / (a + 1 : ℕ) =
        1 - ((((a + 1 : ℕ) : ℝ) / (a : ℝ)))⁻¹ := by
      push_cast
      field_simp
      ring
    _ ≤ Real.log ((((a + 1 : ℕ) : ℝ) / (a : ℝ))) :=
      Real.one_sub_inv_le_log_of_pos hratio

theorem sum_reciprocal_succ_le_log_div
    {L m : ℕ} (hL : 0 < L) :
    (∑ i ∈ Finset.range m, (1 : ℝ) / (L + i + 1 : ℕ)) ≤
      Real.log ((((L + m : ℕ) : ℝ) / (L : ℝ))) := by
  calc
    (∑ i ∈ Finset.range m, (1 : ℝ) / (L + i + 1 : ℕ)) ≤
        ∑ i ∈ Finset.range m,
          Real.log ((((L + i + 1 : ℕ) : ℝ) / (L + i : ℕ))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact reciprocal_succ_le_log_ratio (Nat.add_pos_left hL i)
    _ = Real.log (L + m : ℕ) - Real.log L := by
      have hterm (i : ℕ) :
          Real.log ((((L + i + 1 : ℕ) : ℝ) / (L + i : ℕ))) =
            Real.log (L + i + 1 : ℕ) - Real.log (L + i : ℕ) := by
        rw [Real.log_div]
        · positivity
        · positivity
      rw [Finset.sum_congr rfl (fun i _ ↦ hterm i)]
      simpa [Nat.add_assoc] using
        (Finset.sum_range_sub (fun i : ℕ ↦ Real.log (L + i : ℕ)) m)
    _ = Real.log ((((L + m : ℕ) : ℝ) / (L : ℝ))) := by
      rw [Real.log_div]
      · positivity
      · positivity

theorem heatKernelBound_le_reciprocal (r n : ℕ) :
    heatKernelBound r n ≤ 12 * ((n + 1 : ℕ) : ℝ)⁻¹ := by
  have hexp : Real.exp (- ((r : ℝ) ^ 2 /
      (32 * ((n + 1 : ℕ) : ℝ)))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (by positivity)
  unfold heatKernelBound
  calc
    (12 / ((n + 1 : ℕ) : ℝ)) *
        Real.exp (- ((r : ℝ) ^ 2 /
          (32 * ((n + 1 : ℕ) : ℝ)))) ≤
        (12 / ((n + 1 : ℕ) : ℝ)) * 1 := by
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 12 * ((n + 1 : ℕ) : ℝ)⁻¹ := by rw [div_eq_mul_inv, mul_one]

theorem sum_heatKernelBound_le_log_ratio
    {r N : ℕ} (hr : 0 < r) (hrN : r ^ 2 ≤ N + 1) :
    (∑ n ∈ Finset.range (N + 1), heatKernelBound r n) ≤
      384 + 12 * Real.log ((((N + 1 : ℕ) : ℝ) / (r : ℝ) ^ 2)) := by
  have htail :
      (∑ n ∈ Finset.Ico (r ^ 2) (N + 1), heatKernelBound r n) ≤
        12 * Real.log ((((N + 1 : ℕ) : ℝ) / (r : ℝ) ^ 2)) := by
    calc
      (∑ n ∈ Finset.Ico (r ^ 2) (N + 1), heatKernelBound r n) ≤
          ∑ n ∈ Finset.Ico (r ^ 2) (N + 1),
            12 * ((n + 1 : ℕ) : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro n hn
        exact heatKernelBound_le_reciprocal r n
      _ = 12 * (∑ n ∈ Finset.Ico (r ^ 2) (N + 1),
            (1 : ℝ) / (n + 1 : ℕ)) := by
        rw [Finset.mul_sum]
        simp [div_eq_mul_inv]
      _ ≤ 12 * Real.log ((((N + 1 : ℕ) : ℝ) / (r : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [Finset.sum_Ico_eq_sum_range]
        have hsum := sum_reciprocal_succ_le_log_div
          (L := r ^ 2) (m := N + 1 - r ^ 2) (pow_pos hr 2)
        have hend : r ^ 2 + (N + 1 - r ^ 2) = N + 1 := by omega
        rw [hend] at hsum
        push_cast at hsum
        simpa [Nat.add_assoc, add_assoc] using hsum
  calc
    (∑ n ∈ Finset.range (N + 1), heatKernelBound r n) =
        (∑ n ∈ Finset.range (r ^ 2), heatKernelBound r n) +
          ∑ n ∈ Finset.Ico (r ^ 2) (N + 1), heatKernelBound r n := by
      exact (Finset.sum_range_add_sum_Ico (heatKernelBound r) hrN).symm
    _ ≤ 384 + 12 * Real.log ((((N + 1 : ℕ) : ℝ) / (r : ℝ) ^ 2)) :=
      add_le_add (sum_heatKernelBound_before_sq_le r) htail

theorem sum_killedWeight_toReal_le_log_ratio
    (D : Set Site) {x : Site} {N : ℕ} (hx : 0 < siteNormInf x)
    (hxN : (siteNormInf x) ^ 2 ≤ N + 1) :
    (∑ n ∈ Finset.range (N + 1),
        (KilledGreen.killedWeight D x 0 n).toReal) ≤
      384 + 12 * Real.log ((((N + 1 : ℕ) : ℝ) /
        (siteNormInf x : ℝ) ^ 2)) := by
  calc
    (∑ n ∈ Finset.range (N + 1),
        (KilledGreen.killedWeight D x 0 n).toReal) ≤
        ∑ n ∈ Finset.range (N + 1), heatKernelBound (siteNormInf x) n := by
      apply Finset.sum_le_sum
      intro n hn
      simpa [heatKernelBound] using killedWeight_toReal_le_heatKernel D x n
    _ ≤ 384 + 12 * Real.log ((((N + 1 : ℕ) : ℝ) /
        (siteNormInf x : ℝ) ^ 2)) :=
      sum_heatKernelBound_le_log_ratio hx hxN

theorem log_sq_ratio_le_two_mul_one_add_log_succ_ratio
    {r R : ℕ} (hr : 0 < r) :
    Real.log ((((R ^ 2 + 1 : ℕ) : ℝ) / (r : ℝ) ^ 2)) ≤
      2 * (1 + Real.log ((((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ)))) := by
  have hrRpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hBpos : (0 : ℝ) < (((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ)) := by positivity
  have hApos : (0 : ℝ) < (((R ^ 2 + 1 : ℕ) : ℝ) / (r : ℝ) ^ 2) := by
    positivity
  have hfirst : (((R ^ 2 + 1 : ℕ) : ℝ) / (r : ℝ) ^ 2) ≤
      (((R + 1 : ℕ) : ℝ) / (r : ℝ)) ^ 2 := by
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ (sq_nonneg (r : ℝ))
    push_cast
    nlinarith [show (0 : ℝ) ≤ R by positivity]
  have hsecond : (((R + 1 : ℕ) : ℝ) / (r : ℝ)) ≤
      2 * (((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ)) := by
    rw [show 2 * (((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ)) =
      (2 * ((R + 1 : ℕ) : ℝ)) / ((r + 1 : ℕ) : ℝ) by ring]
    apply (div_le_div_iff₀ hrRpos
      (by positivity : (0 : ℝ) < ((r + 1 : ℕ) : ℝ))).2
    push_cast
    have hprod : 0 ≤ ((R : ℝ) + 1) * ((r : ℝ) - 1) := by
      have hrOne : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hrOne)
    nlinarith
  have hBnonneg : 0 ≤ (((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ)) := hBpos.le
  have hratio : (((R ^ 2 + 1 : ℕ) : ℝ) / (r : ℝ) ^ 2) ≤
      (2 * (((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ))) ^ 2 :=
    hfirst.trans (pow_le_pow_left₀ (by positivity) hsecond 2)
  calc
    Real.log ((((R ^ 2 + 1 : ℕ) : ℝ) / (r : ℝ) ^ 2)) ≤
        Real.log ((2 * (((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ))) ^ 2) :=
      Real.log_le_log hApos hratio
    _ = 2 * (Real.log 2 +
        Real.log ((((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ)))) := by
      rw [Real.log_pow, Real.log_mul]
      · norm_num
      · norm_num
      · exact hBpos.ne'
    _ ≤ 2 * (1 +
        Real.log ((((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ)))) := by
      have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
        nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith

/-- The requested `1 + log(radius / distance)` form for the free heat-kernel
sum through the diffusive time scale `R²`.  The harmless successors keep the
logarithm defined at every lattice radius. -/
theorem sum_heatKernelBound_square_le
    {r R : ℕ} (hr : 0 < r) (hrR : r ≤ R) :
    (∑ n ∈ Finset.range (R ^ 2 + 1), heatKernelBound r n) ≤
      408 * (1 +
        Real.log ((((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ)))) := by
  have hbase := sum_heatKernelBound_le_log_ratio
    (r := r) (N := R ^ 2) hr (by nlinarith [Nat.pow_le_pow_left hrR 2])
  have hlog := log_sq_ratio_le_two_mul_one_add_log_succ_ratio (R := R) hr
  have hratioOne : (1 : ℝ) ≤
      (((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((r + 1 : ℕ) : ℝ))).2
    simpa only [one_mul] using
      (show (((r + 1 : ℕ) : ℝ)) ≤ ((R + 1 : ℕ) : ℝ) by
        exact_mod_cast (Nat.succ_le_succ hrR))
  have hlogNonneg : 0 ≤
      Real.log ((((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ))) :=
    Real.log_nonneg hratioOne
  calc
    (∑ n ∈ Finset.range (R ^ 2 + 1), heatKernelBound r n) ≤
        384 + 12 * Real.log ((((R ^ 2 + 1 : ℕ) : ℝ) / (r : ℝ) ^ 2)) :=
      hbase
    _ ≤ 384 + 12 * (2 * (1 +
        Real.log ((((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ))))) := by
      gcongr
    _ ≤ 408 * (1 +
        Real.log ((((R + 1 : ℕ) : ℝ) / (r + 1 : ℕ)))) := by
      nlinarith

theorem sum_killedWeight_toReal_square_le
    (D : Set Site) {x : Site} {R : ℕ}
    (hx : 0 < siteNormInf x) (hxR : siteNormInf x ≤ R) :
    (∑ n ∈ Finset.range (R ^ 2 + 1),
        (KilledGreen.killedWeight D x 0 n).toReal) ≤
      408 * (1 + Real.log ((((R + 1 : ℕ) : ℝ) /
        (siteNormInf x + 1 : ℕ)))) := by
  calc
    (∑ n ∈ Finset.range (R ^ 2 + 1),
        (KilledGreen.killedWeight D x 0 n).toReal) ≤
        ∑ n ∈ Finset.range (R ^ 2 + 1),
          heatKernelBound (siteNormInf x) n := by
      apply Finset.sum_le_sum
      intro n hn
      simpa [heatKernelBound] using killedWeight_toReal_le_heatKernel D x n
    _ ≤ 408 * (1 + Real.log ((((R + 1 : ℕ) : ℝ) /
        (siteNormInf x + 1 : ℕ)))) :=
      sum_heatKernelBound_square_le hx hxR

end Erdos1166.HeatKernel
