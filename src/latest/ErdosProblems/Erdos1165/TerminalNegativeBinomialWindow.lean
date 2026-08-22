/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.ExcursionTransition
import ErdosProblems.Erdos1165.AppendixFirstMoment

/-!
# A polynomial lower bound for the terminal negative-binomial window

At the last radial level of the HLOZ auxiliary chain the number of inward
crossings has negative-binomial law with success parameter
`L / (1 + L)`, where `L = 3 log n`.  This file proves, without an asymptotic
local limit theorem, that the atom at the ceiling of its mean has polynomial
mass.  The proof uses only unimodality and Markov's inequality.
-/

open scoped BigOperators NNReal ENNReal
open Filter Real

namespace Erdos1165.TerminalNegativeBinomialWindow

open NegativeBinomial
open ExcursionTransition ThickPoint

noncomputable section

/-- The terminal success parameter, written with an abstract logarithmic
scale `L`. -/
def logarithmicSuccess (L : ℝ) : ℝ := L / (1 + L)

lemma logarithmicSuccess_pos {L : ℝ} (hL : 0 < L) :
    0 < logarithmicSuccess L := by
  unfold logarithmicSuccess
  positivity

lemma logarithmicSuccess_lt_one {L : ℝ} (hL : 0 < L) :
    logarithmicSuccess L < 1 := by
  unfold logarithmicSuccess
  rw [div_lt_one (by positivity : 0 < 1 + L)]
  linarith

lemma logarithmicSuccess_le_one {L : ℝ} (hL : 0 < L) :
    logarithmicSuccess L ≤ 1 := (logarithmicSuccess_lt_one hL).le

lemma one_sub_logarithmicSuccess {L : ℝ} (hL : 0 < L) :
    1 - logarithmicSuccess L = 1 / (1 + L) := by
  unfold logarithmicSuccess
  field_simp
  ring

lemma logarithmic_mean (L : ℝ) {a : ℕ} (ha : 0 < a) (hL : 0 < L) :
    ∑' j : ℕ, (j : ℝ) * mass (logarithmicSuccess L) a j = (a : ℝ) / L := by
  rw [tsum_weighted_mass (logarithmicSuccess_pos hL)
    (logarithmicSuccess_le_one hL) ha]
  rw [one_sub_logarithmicSuccess hL]
  unfold logarithmicSuccess
  field_simp

/-- Above the ceiling of the mean, the terminal negative-binomial mass is
nonincreasing. -/
lemma mass_succ_le_mass_of_mean_ceil_le
    {L : ℝ} (hL : 0 < L) {a j : ℕ} (ha : 0 < a)
    (hj : ⌈(a : ℝ) / L⌉₊ ≤ j) :
    mass (logarithmicSuccess L) a (j + 1) ≤
      mass (logarithmicSuccess L) a j := by
  rw [mass_succ_le_mass_iff (logarithmicSuccess_pos hL)
    (logarithmicSuccess_lt_one hL) ha]
  rw [one_sub_logarithmicSuccess hL]
  have hLj : (a : ℝ) ≤ L * (j : ℝ) := by
    have hmean : (a : ℝ) / L ≤ (j : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hj)
    rw [div_le_iff₀ hL] at hmean
    simpa [mul_comm] using hmean
  have hden : 0 < 1 + L := by positivity
  rw [one_div, ← div_eq_mul_inv]
  rw [div_le_iff₀ hden]
  push_cast
  nlinarith

/-- At least three lattice sites below the ceiling of the mean, the terminal
negative-binomial mass is still nondecreasing.  The two omitted sites are the
only rounding loss needed below. -/
lemma mass_le_mass_succ_of_add_three_le_mean_ceil
    {L : ℝ} (hL : 1 ≤ L) {a j : ℕ} (ha : 0 < a)
    (hj : j + 3 ≤ ⌈(a : ℝ) / L⌉₊) :
    mass (logarithmicSuccess L) a j ≤
      mass (logarithmicSuccess L) a (j + 1) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [mass_le_mass_succ_iff (logarithmicSuccess_pos hL0)
    (logarithmicSuccess_lt_one hL0) ha]
  rw [one_sub_logarithmicSuccess hL0]
  have hceil : (⌈(a : ℝ) / L⌉₊ : ℝ) < (a : ℝ) / L + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hjR : (j : ℝ) + 3 ≤ (⌈(a : ℝ) / L⌉₊ : ℝ) := by
    exact_mod_cast hj
  have hmain : L * ((j : ℝ) + 2) ≤ (a : ℝ) := by
    have : (j : ℝ) + 2 < (a : ℝ) / L := by linarith
    rw [lt_div_iff₀ hL0] at this
    simpa [mul_comm] using this.le
  have hden : 0 < 1 + L := by positivity
  rw [one_div, ← div_eq_mul_inv]
  rw [le_div_iff₀ hden]
  push_cast
  nlinarith

/-- Each of the last two rising-side steps loses at most a factor four. -/
lemma mass_le_four_mul_mass_succ_below_ceil_mean
    {L : ℝ} (hL : 1 ≤ L) {a j : ℕ} (ha : 0 < a)
    (hmean : 1 ≤ (a : ℝ) / L) (hj : j < ⌈(a : ℝ) / L⌉₊) :
    mass (logarithmicSuccess L) a j ≤
      4 * mass (logarithmicSuccess L) a (j + 1) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hmpos := mass_pos (logarithmicSuccess_pos hL0)
    (logarithmicSuccess_lt_one hL0) ha j
  have hratio := mass_succ_div_mass (logarithmicSuccess_pos hL0)
    (logarithmicSuccess_lt_one hL0) ha j
  rw [one_sub_logarithmicSuccess hL0] at hratio
  have hjceil : ((j + 1 : ℕ) : ℝ) ≤ (⌈(a : ℝ) / L⌉₊ : ℝ) := by
    exact_mod_cast hj
  have hceil : (⌈(a : ℝ) / L⌉₊ : ℝ) < (a : ℝ) / L + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hprod : 0 ≤ (L - 1) * ((a : ℝ) / L - 1) :=
    mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hmean)
  have hmu0 : 0 ≤ (a : ℝ) / L := le_trans zero_le_one hmean
  have hLm_ge_L : L ≤ L * ((a : ℝ) / L) :=
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left hmean hL0.le
  have hLm_ge_mu : (a : ℝ) / L ≤ L * ((a : ℝ) / L) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hL hmu0
  have hLm_ge_one : 1 ≤ L * ((a : ℝ) / L) := hmean.trans hLm_ge_mu
  have hcoef : (1 / 4 : ℝ) ≤
      ((a + j : ℕ) : ℝ) * (1 / (1 + L)) / (j + 1 : ℕ) := by
    have hdenL : 0 < 1 + L := by positivity
    have hdenJ : (0 : ℝ) < j + 1 := by positivity
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [le_div_iff₀ hdenJ]
    rw [div_eq_mul_inv]
    field_simp
    push_cast
    have haeq : (a : ℝ) = L * ((a : ℝ) / L) := by field_simp
    have hupper : ((j : ℝ) + 1) * (1 + L) <
        ((a : ℝ) / L + 1) * (1 + L) :=
      mul_lt_mul_of_pos_right (by
        simpa only [Nat.cast_add, Nat.cast_one] using hjceil.trans_lt hceil) hdenL
    nlinarith
  norm_num only [Nat.cast_add, Nat.cast_one] at hratio hcoef
  rw [← hratio] at hcoef
  rw [le_div_iff₀ hmpos] at hcoef
  nlinarith

/-- Every atom is at most sixteen times the atom at the ceiling of the mean.
This deliberately coarse constant makes the two rounding steps elementary. -/
lemma mass_le_sixteen_mul_mass_ceil_mean
    {L : ℝ} (hL : 1 ≤ L) {a : ℕ} (ha : 0 < a)
    (hmean : 1 ≤ (a : ℝ) / L) (j : ℕ) :
    mass (logarithmicSuccess L) a j ≤
      16 * mass (logarithmicSuccess L) a ⌈(a : ℝ) / L⌉₊ := by
  let b := ⌈(a : ℝ) / L⌉₊
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hbpos : 0 < b := by
    dsimp [b]
    rw [Nat.ceil_pos]
    exact lt_of_lt_of_le zero_lt_one hmean
  by_cases hjb : b ≤ j
  · have hanti := antitoneOn_nat_Ici_of_succ_le
        (f := fun k : ℕ ↦ mass (logarithmicSuccess L) a k)
        (k := b) (fun k hk ↦ mass_succ_le_mass_of_mean_ceil_le hL0 ha hk)
    have hto := hanti (show b ≤ b from le_rfl) hjb hjb
    have hm0 := mass_nonneg (logarithmicSuccess_pos hL0).le
      (logarithmicSuccess_le_one hL0) a b
    simpa only [b] using hto.trans (by nlinarith)
  · have hjlt : j < b := Nat.lt_of_not_ge hjb
    by_cases hfar : j + 3 ≤ b
    · have hjle : j ≤ b - 2 := by omega
      have hb3 : 3 ≤ b := by omega
      let f : ℕ → ℝ := fun k ↦
        mass (logarithmicSuccess L) a (min k (b - 2))
      have hf : Monotone f := monotone_nat_of_le_succ fun k ↦ by
        by_cases hk : k < b - 2
        · have hk3 : k + 3 ≤ b := by omega
          simp only [f, Nat.min_eq_left (by omega : k ≤ b - 2),
            Nat.min_eq_left (by omega : k + 1 ≤ b - 2)]
          exact mass_le_mass_succ_of_add_three_le_mean_ceil hL ha hk3
        · simp only [f, Nat.min_eq_right (by omega : b - 2 ≤ k),
            Nat.min_eq_right (by omega : b - 2 ≤ k + 1)]
          exact le_rfl
      have hto : mass (logarithmicSuccess L) a j ≤
          mass (logarithmicSuccess L) a (b - 2) := by
        simpa [f, Nat.min_eq_left hjle] using hf hjle
      have hbm2 : b - 2 < b := by omega
      have hbm1 : b - 1 < b := by omega
      have hbm2' : b - 2 < ⌈(a : ℝ) / L⌉₊ := by simpa only [b] using hbm2
      have hbm1' : b - 1 < ⌈(a : ℝ) / L⌉₊ := by simpa only [b] using hbm1
      have h1 := mass_le_four_mul_mass_succ_below_ceil_mean hL ha hmean hbm2'
      have h2 := mass_le_four_mul_mass_succ_below_ceil_mean hL ha hmean hbm1'
      have hb1 : b - 2 + 1 = b - 1 := by omega
      have hb2 : b - 1 + 1 = b := by omega
      rw [hb1] at h1
      rw [hb2] at h2
      simpa only [b] using hto.trans (by nlinarith)
    · by_cases hbOne : b = 1
      · have hj0 : j = 0 := by omega
        subst j
        have hzero : (0 : ℕ) < ⌈(a : ℝ) / L⌉₊ := by simpa only [← hbOne]
        have hstep := mass_le_four_mul_mass_succ_below_ceil_mean hL ha hmean hzero
        have hm0 := mass_nonneg (logarithmicSuccess_pos hL0).le
          (logarithmicSuccess_le_one hL0) a 1
        have hceilEq : ⌈(a : ℝ) / L⌉₊ = 1 := by simpa only [b] using hbOne
        rw [hceilEq]
        simpa only [Nat.zero_add] using (by nlinarith :
          mass (logarithmicSuccess L) a 0 ≤
            16 * mass (logarithmicSuccess L) a 1)
      · have hb2 : 2 ≤ b := by omega
        have hnear : j = b - 2 ∨ j = b - 1 := by omega
        rcases hnear with rfl | rfl
        · have hbm2 : b - 2 < b := by omega
          have hbm1 : b - 1 < b := by omega
          have hbm2' : b - 2 < ⌈(a : ℝ) / L⌉₊ := by simpa only [b] using hbm2
          have hbm1' : b - 1 < ⌈(a : ℝ) / L⌉₊ := by simpa only [b] using hbm1
          have h1 := mass_le_four_mul_mass_succ_below_ceil_mean hL ha hmean hbm2'
          have h2 := mass_le_four_mul_mass_succ_below_ceil_mean hL ha hmean hbm1'
          have hb1 : b - 2 + 1 = b - 1 := by omega
          have hb2 : b - 1 + 1 = b := by omega
          rw [hb1] at h1
          rw [hb2] at h2
          simpa only [b] using (by nlinarith :
            mass (logarithmicSuccess L) a (b - 2) ≤
              16 * mass (logarithmicSuccess L) a b)
        · have hbm1 : b - 1 < b := by omega
          have hbm1' : b - 1 < ⌈(a : ℝ) / L⌉₊ := by simpa only [b] using hbm1
          have h2 := mass_le_four_mul_mass_succ_below_ceil_mean hL ha hmean hbm1'
          have hb2 : b - 1 + 1 = b := by omega
          rw [hb2] at h2
          have hm0 := mass_nonneg (logarithmicSuccess_pos hL0).le
            (logarithmicSuccess_le_one hL0) a b
          simpa only [b] using (by nlinarith :
            mass (logarithmicSuccess L) a (b - 1) ≤
              16 * mass (logarithmicSuccess L) a b)

/-- Explicit polynomial lower bound at the ceiling of the mean.  The
denominator is the cardinality cost of a prefix containing at least half of
the law, multiplied by the factor-sixteen rounding loss above. -/
theorem one_div_thirtyTwo_ceil_two_mean_le_mass_ceil_mean
    {L : ℝ} (hL : 1 ≤ L) {a : ℕ} (ha : 0 < a)
    (hmean : 1 ≤ (a : ℝ) / L) :
    1 / (32 * (⌈2 * ((a : ℝ) / L)⌉₊ : ℝ)) ≤
      mass (logarithmicSuccess L) a ⌈(a : ℝ) / L⌉₊ := by
  let p := logarithmicSuccess L
  let f : ℕ → ℝ := fun j ↦ mass p a j
  let g : ℕ → ℝ := fun j ↦ (j : ℝ) * f j
  let K := ⌈2 * ((a : ℝ) / L)⌉₊
  let b := ⌈(a : ℝ) / L⌉₊
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hp0 : 0 < p := logarithmicSuccess_pos hL0
  have hp1 : p ≤ 1 := logarithmicSuccess_le_one hL0
  have hf : Summable f := by
    dsimp only [f, p]
    exact summable_mass hp0 hp1 ha
  have hg : Summable g := by
    dsimp only [g, f, p]
    exact (hasSum_weighted_mass hp0 hp1 ha).summable
  have hKpos : 0 < K := by
    dsimp only [K]
    rw [Nat.ceil_pos]
    positivity
  have hKreal : 2 * ((a : ℝ) / L) ≤ (K : ℝ) := by
    dsimp only [K]
    exact Nat.le_ceil _
  have htailPoint : ∀ i : ℕ, f (i + K) ≤ g (i + K) / (K : ℝ) := by
    intro i
    have hmass : 0 ≤ f (i + K) := by
      dsimp only [f, p]
      exact mass_nonneg hp0.le hp1 a (i + K)
    have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
    dsimp only [g]
    rw [le_div_iff₀ hKR]
    push_cast
    nlinarith
  have htailMass :
      ∑' i : ℕ, f (i + K) ≤ (∑' i : ℕ, g (i + K)) / (K : ℝ) := by
    have hleft : Summable (fun i : ℕ ↦ f (i + K)) :=
      (summable_nat_add_iff K).2 hf
    have hright : Summable (fun i : ℕ ↦ g (i + K) / (K : ℝ)) :=
      ((summable_nat_add_iff K).2 hg).div_const _
    have hsum := hleft.tsum_le_tsum htailPoint hright
    simpa only [tsum_div_const] using hsum
  have htotalG : ∑' i : ℕ, g i = (a : ℝ) / L := by
    dsimp only [g, f, p]
    exact logarithmic_mean L ha hL0
  have htailG : ∑' i : ℕ, g (i + K) ≤ (a : ℝ) / L := by
    have hsplit := hg.sum_add_tsum_nat_add K
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range K, g i := by
      apply Finset.sum_nonneg
      intro i hi
      dsimp only [g, f, p]
      exact mul_nonneg (Nat.cast_nonneg _) (mass_nonneg hp0.le hp1 a i)
    rw [htotalG] at hsplit
    linarith
  have htailHalf : ∑' i : ℕ, f (i + K) ≤ 1 / 2 := by
    have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hmeanK : ((a : ℝ) / L) / (K : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hKR]
      nlinarith
    exact htailMass.trans ((div_le_div_of_nonneg_right htailG hKR.le).trans hmeanK)
  have htotalF : ∑' i : ℕ, f i = 1 := by
    dsimp only [f, p]
    exact tsum_mass hp0 hp1 ha
  have hprefixHalf : 1 / 2 ≤ ∑ i ∈ Finset.range K, f i := by
    have hsplit := hf.sum_add_tsum_nat_add K
    rw [htotalF] at hsplit
    linarith
  have hterm : ∀ i ∈ Finset.range K, f i ≤ 16 * f b := by
    intro i hi
    dsimp only [f, p, b]
    exact mass_le_sixteen_mul_mass_ceil_mean hL ha hmean i
  have hprefixUpper : ∑ i ∈ Finset.range K, f i ≤ (K : ℝ) * (16 * f b) := by
    calc
      ∑ i ∈ Finset.range K, f i ≤ ∑ _i ∈ Finset.range K, 16 * f b :=
        Finset.sum_le_sum fun i hi ↦ hterm i hi
      _ = (K : ℝ) * (16 * f b) := by simp [mul_assoc]
  have hfb0 : 0 ≤ f b := by
    dsimp only [f, p, b]
    exact mass_nonneg hp0.le hp1 a _
  have hden : 0 < 32 * (K : ℝ) := by positivity
  dsimp only [f, p, b, K] at hprefixHalf hprefixUpper hfb0 hden ⊢
  rw [div_le_iff₀ hden]
  nlinarith

lemma terminalSuccess_eq_logarithmicSuccess (n : ℕ) :
    terminalSuccess n = logarithmicSuccess (3 * Real.log n) := by
  rfl

/-- The ideal auxiliary-chain mass of the successful terminal-count window. -/
noncomputable def terminalWindowMass (n : ℕ) (delta : ℝ) (a : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3),
    mass (terminalSuccess n) a j

lemma terminalWindowMass_nonneg (n : ℕ) (delta : ℝ) (a : ℕ)
    (hp0 : 0 ≤ terminalSuccess n) (hp1 : terminalSuccess n ≤ 1) :
    0 ≤ terminalWindowMass n delta a := by
  apply Finset.sum_nonneg
  intro j hj
  exact mass_nonneg hp0 hp1 a j

/-- A completely explicit lower bound for the terminal factor in HLOZ A.6.
The hypotheses say exactly that the ceiling of the ideal mean belongs to the
successful terminal window. -/
theorem one_div_thirtyTwo_ceil_two_mean_le_terminalWindowMass
    {n a : ℕ} {delta : ℝ} (ha : 0 < a)
    (hlog : 1 ≤ 3 * Real.log n)
    (hmean : 1 ≤ (a : ℝ) / (3 * Real.log n))
    (hlower : terminalLower n delta ≤ (a : ℝ) / (3 * Real.log n))
    (hupper : ⌈(a : ℝ) / (3 * Real.log n)⌉₊ ≤ n ^ 3) :
    1 / (32 * (⌈2 * ((a : ℝ) / (3 * Real.log n))⌉₊ : ℝ)) ≤
      terminalWindowMass n delta a := by
  let b := ⌈(a : ℝ) / (3 * Real.log n)⌉₊
  have hlog0 : 0 < 3 * Real.log n := lt_of_lt_of_le zero_lt_one hlog
  have hbase := one_div_thirtyTwo_ceil_two_mean_le_mass_ceil_mean
    hlog ha hmean
  rw [← terminalSuccess_eq_logarithmicSuccess n] at hbase
  have hbmem : b ∈ Finset.Icc ⌈terminalLower n delta⌉₊ (n ^ 3) := by
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.ceil_mono hlower
    · exact hupper
  have hn : 2 ≤ n := by
    have hnlog : 0 < Real.log (n : ℝ) := by nlinarith
    have hnR : (1 : ℝ) < n :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ n)).mp hnlog
    exact_mod_cast hnR
  have hterm : mass (terminalSuccess n) a b ≤ terminalWindowMass n delta a := by
    unfold terminalWindowMass
    exact Finset.single_le_sum
      (fun j hj ↦ mass_nonneg (terminalSuccess_pos hn).le
        (terminalSuccess_le_one hn) a j) hbmem
  change 1 / (32 * (⌈2 * ((a : ℝ) / (3 * Real.log n))⌉₊ : ℝ)) ≤
    mass (terminalSuccess n) a b at hbase
  exact hbase.trans hterm

/-- The final internal entry `m_n` of an HLOZ profile. -/
def terminalProfileCount {n : ℕ} (hn : 2 ≤ n)
    (m : AppendixFirstMoment.Profile n) : ℕ :=
  m ⟨n - 2, by omega⟩

@[simp] lemma scaleIndex_terminalProfileIndex {n : ℕ} (hn : 2 ≤ n) :
    AppendixFirstMoment.scaleIndex (⟨n - 2, by omega⟩ : Fin (n - 1)) = n := by
  unfold AppendixFirstMoment.scaleIndex
  change n - 2 + 2 = n
  omega

/-- The constrained profile window puts its last entry above the lower
endpoint used in the successful terminal window. -/
lemma terminalLower_le_terminalProfileCount_div
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ}
    {m : AppendixFirstMoment.Profile n}
    (hm : AppendixFirstMoment.IsConstrainedProfile delta m)
    (hlog : 0 < 3 * Real.log n) :
    terminalLower n delta ≤
      (terminalProfileCount hn m : ℝ) / (3 * Real.log n) := by
  let i : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hi := hm i
  rw [AppendixFirstMoment.InProfileWindow, abs_le] at hi
  have hscale : AppendixFirstMoment.scaleIndex i = n := by
    dsimp only [i]
    exact scaleIndex_terminalProfileIndex hn
  rw [hscale] at hi
  unfold AppendixFirstMoment.profileCenter at hi
  unfold terminalLower terminalProfileCount
  apply (div_le_div_iff_of_pos_right hlog).2
  norm_num only [Fin.isValue]
  have hentry : m ⟨n - 2, by omega⟩ = m i := rfl
  rw [hentry]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hi ⊢
  nlinarith

lemma terminalProfileCount_bounds
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : AppendixFirstMoment.Profile n}
    (hm : AppendixFirstMoment.IsConstrainedProfile delta m) :
    (n : ℝ) ^ 2 ≤ terminalProfileCount hn m ∧
      (terminalProfileCount hn m : ℝ) ≤ 3 * (n : ℝ) ^ 2 := by
  let i : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hi := hm i
  rw [AppendixFirstMoment.InProfileWindow, abs_le] at hi
  have hscale : AppendixFirstMoment.scaleIndex i = n := by
    dsimp only [i]
    exact scaleIndex_terminalProfileIndex hn
  rw [hscale] at hi
  unfold AppendixFirstMoment.profileCenter at hi
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hi
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpow : (n : ℝ) ^ (1 + delta) ≤ (n : ℝ) ^ (2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hnOne
    linarith
  rw [Real.rpow_two] at hpow
  unfold terminalProfileCount
  have hentry : m ⟨n - 2, by omega⟩ = m i := rfl
  rw [hentry]
  constructor <;> nlinarith

/-- Profile-specialized terminal-window lower bound.  Only the elementary
large-scale statements that the mean lies between `1` and `n³` remain as
premises; membership of its ceiling in the lower side of the window follows
directly from constrainedness. -/
theorem one_div_thirtyTwo_ceil_two_terminalProfileMean_le_terminalWindowMass
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ}
    {m : AppendixFirstMoment.Profile n}
    (hm : AppendixFirstMoment.IsConstrainedProfile delta m)
    (hlog : 1 ≤ 3 * Real.log n)
    (hmean : 1 ≤ (terminalProfileCount hn m : ℝ) / (3 * Real.log n))
    (hupper : ⌈(terminalProfileCount hn m : ℝ) / (3 * Real.log n)⌉₊ ≤ n ^ 3) :
    1 / (32 * (⌈2 * ((terminalProfileCount hn m : ℝ) /
        (3 * Real.log n))⌉₊ : ℝ)) ≤
      terminalWindowMass n delta (terminalProfileCount hn m) := by
  have ha : 0 < terminalProfileCount hn m := by
    have hden : 0 < 3 * Real.log n := lt_of_lt_of_le zero_lt_one hlog
    have hcountR : (0 : ℝ) < terminalProfileCount hn m := by
      by_contra hz
      have hcountNonpos : (terminalProfileCount hn m : ℝ) ≤ 0 := le_of_not_gt hz
      have hratioNonpos :
          (terminalProfileCount hn m : ℝ) / (3 * Real.log n) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hcountNonpos hden.le
      linarith
    exact_mod_cast hcountR
  apply one_div_thirtyTwo_ceil_two_mean_le_terminalWindowMass ha hlog hmean
  · exact terminalLower_le_terminalProfileCount_div hn hm
      (lt_of_lt_of_le zero_lt_one hlog)
  · exact hupper

/-- The profile-specialized terminal estimate with all mean/window premises
discharged by elementary inequalities. -/
theorem one_div_thirtyTwo_ceil_two_terminalProfileMean_le_terminalWindowMass_of_bounds
    {n : ℕ} (hn : 3 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : AppendixFirstMoment.Profile n}
    (hm : AppendixFirstMoment.IsConstrainedProfile delta m)
    (hlog : 1 ≤ 3 * Real.log n) :
    1 / (32 * (⌈2 * ((terminalProfileCount (by omega) m : ℝ) /
        (3 * Real.log n))⌉₊ : ℝ)) ≤
      terminalWindowMass n delta (terminalProfileCount (by omega) m) := by
  have hn2 : 2 ≤ n := by omega
  have hbounds := terminalProfileCount_bounds hn2 hdelta hm
  have hnR : (0 : ℝ) < n := by positivity
  have hlogUpper : Real.log (n : ℝ) ≤ (n : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hnR
  have hdenUpper : 3 * Real.log (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hnThree : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 3)]
  have hdenPos : 0 < 3 * Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hmean : 1 ≤
      (terminalProfileCount hn2 m : ℝ) / (3 * Real.log n) := by
    rw [le_div_iff₀ hdenPos]
    simpa only [one_mul] using hdenUpper.trans hbounds.1
  have hratioUpper :
      (terminalProfileCount hn2 m : ℝ) / (3 * Real.log n) ≤ n ^ 3 := by
    have hdenOne : (1 : ℝ) ≤ 3 * Real.log n := hlog
    have hcount0 : 0 ≤ (terminalProfileCount hn2 m : ℝ) := by positivity
    have hdivCount :
        (terminalProfileCount hn2 m : ℝ) / (3 * Real.log n) ≤
          terminalProfileCount hn2 m := by
      exact div_le_self hcount0 hdenOne
    have hnCube : 3 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
      have hnThree : (3 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg (n : ℝ)]
    exact hdivCount.trans (hbounds.2.trans hnCube)
  have hupper :
      ⌈(terminalProfileCount hn2 m : ℝ) / (3 * Real.log n)⌉₊ ≤ n ^ 3 := by
    rw [Nat.ceil_le]
    exact_mod_cast hratioUpper
  exact one_div_thirtyTwo_ceil_two_terminalProfileMean_le_terminalWindowMass
    hn2 hm hlog hmean hupper

/-- Eventual no-premise terminal factor for every constrained profile at a
fixed HLOZ window exponent `delta ≤ 1`. -/
theorem eventually_one_div_thirtyTwo_ceil_two_terminalProfileMean_le_terminalWindowMass
    {delta : ℝ} (hdelta : delta ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn2 : 2 ≤ n) (m : AppendixFirstMoment.Profile n),
        AppendixFirstMoment.IsConstrainedProfile delta m →
          1 / (32 * (⌈2 * ((terminalProfileCount hn2 m : ℝ) /
              (3 * Real.log n))⌉₊ : ℝ)) ≤
            terminalWindowMass n delta (terminalProfileCount hn2 m) := by
  have hlogTendsto : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 3,
    hlogTendsto.eventually (eventually_ge_atTop 1)] with n hn hlog
  intro hn2 m hm
  apply one_div_thirtyTwo_ceil_two_terminalProfileMean_le_terminalWindowMass_of_bounds
    hn hdelta hm
  nlinarith

end

end Erdos1165.TerminalNegativeBinomialWindow
