import ErdosProblems.Erdos239.External.Erdos67.Section4ConvolutionBridge
import ErdosProblems.Erdos239.External.Erdos67.LogResidueUniformity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

/-!
# The concrete finite Dirichlet window in Tao's Section 4

The centers used for Archimedean phase removal start at `Y ^ 2`.  This
means that their finite Dirichlet sum does **not** converge to the full
shifted residue series: there is a fixed low-cutoff contribution.  The
lemmas below keep that contribution separate from the genuinely vanishing
high truncation tail.
-/

open scoped BigOperators
open Filter Set MeasureTheory

namespace Erdos67

noncomputable section

open ShiftedResidueSeries EulerResidue

/-- The finite center interval `[Y²,N]`. -/
def taoWindowCenters (Y N : ℕ) : Finset ℕ :=
  Finset.Icc (Y ^ 2) N

/-- Tao's positive Dirichlet weight at the exponent `1 + 1 / log X`. -/
def taoWindowWeight (X : ℕ) (n : ℕ) : ℝ :=
  realDirichletWeight (taoExponent X) n

/-- The fixed mass omitted below the lower center cutoff. -/
def taoLowCutoffMass (X Y : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (Y ^ 2), taoWindowWeight X n

/-- The part of the fixed low cutoff belonging to one residue class. -/
def taoLowCutoffResidueMass {r : ℕ} (X Y : ℕ) (a : ZMod r) : ℝ :=
  ∑ n ∈ zmodResidueFiber (Finset.range (Y ^ 2)) a, taoWindowWeight X n

/-- The mass above the finite upper cutoff. -/
def taoHighTailMass (X N : ℕ) : ℝ :=
  ∑' j : ℕ, taoWindowWeight X (j + (N + 1))

theorem taoWindowWeight_nonneg (X n : ℕ) :
    0 ≤ taoWindowWeight X n := by
  exact realDirichletWeight_nonneg _ _

theorem taoWindowWeight_pos {X n : ℕ} (hn : 0 < n) :
    0 < taoWindowWeight X n := by
  unfold taoWindowWeight realDirichletWeight
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

theorem taoWindowWeight_zero {X : ℕ} (hX : 1 < X) :
    taoWindowWeight X 0 = 0 := by
  unfold taoWindowWeight realDirichletWeight
  simpa only [Nat.cast_zero] using
    (Real.zero_rpow (show -taoExponent X ≠ 0 by
      linarith [one_lt_taoExponent hX]))

theorem taoWindowWeight_antitoneOn_pos {X : ℕ} (hX : 1 < X)
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    taoWindowWeight X n ≤ taoWindowWeight X m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact realDirichletWeight_add_le (one_lt_taoExponent hX) hm

theorem taoWindowWeight_le_inv {X n : ℕ} (hX : 1 < X) (hn : 0 < n) :
    taoWindowWeight X n ≤ (n : ℝ)⁻¹ := by
  unfold taoWindowWeight realDirichletWeight
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne'))
    (by linarith [one_lt_taoExponent hX])

theorem taoWindowCenter_lower {Y N n : ℕ}
    (hn : n ∈ taoWindowCenters Y N) : Y ^ 2 ≤ n := by
  exact (Finset.mem_Icc.mp hn).1

theorem taoWindowMass_pos {X Y N : ℕ} (hY : 0 < Y) (hYN : Y ^ 2 ≤ N) :
    0 < ∑ n ∈ taoWindowCenters Y N, taoWindowWeight X n := by
  have hmem : Y ^ 2 ∈ taoWindowCenters Y N :=
    Finset.mem_Icc.mpr ⟨le_rfl, hYN⟩
  have hterm : 0 < taoWindowWeight X (Y ^ 2) :=
    taoWindowWeight_pos (pow_pos hY 2)
  exact hterm.trans_le (Finset.single_le_sum
    (fun n _ ↦ taoWindowWeight_nonneg X n) hmem)

/-- The concrete center interval and Dirichlet weight, bundled in the API
used by the same-sample Markov selection theorem. -/
def concreteSection4WeightWindow (H X Y N : ℕ) (hY : 0 < Y)
    (hYN : Y ^ 2 ≤ N) : Section4WeightWindow H Y where
  centers := taoWindowCenters Y N
  weight := taoWindowWeight X
  mass := ∑ n ∈ taoWindowCenters Y N, taoWindowWeight X n
  mass_pos := taoWindowMass_pos hY hYN
  weight_nonneg := fun n _ ↦ taoWindowWeight_nonneg X n
  weight_sum := rfl
  center_lower := fun n hn ↦ taoWindowCenter_lower hn

/-- The elementary integral-test upper bound for the positive real
Dirichlet series. -/
theorem tsum_realDirichletWeight_le_one_add_inv_sub_one
    {u : ℝ} (hu : 1 < u) :
    (∑' n : ℕ, realDirichletWeight u n) ≤ 1 + (u - 1)⁻¹ := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-u)
  have htail :
      (∑' n : ℕ, f (((n + 1 + 1 : ℕ) : ℝ))) ≤
        ∫ x in Set.Ioi (((1 : ℕ) : ℝ)), f x := by
    exact AntitoneOn.tsum_comp_add_le_integral (f := f) 1
      ((Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
        (Set.Ici_subset_Ioi.2
          (show (0 : ℝ) < ((1 : ℕ) : ℝ) by norm_num)))
      (integrableOn_Ioi_rpow_of_lt (by linarith)
        (show (0 : ℝ) < ((1 : ℕ) : ℝ) by norm_num))
      (fun x hx ↦ by
        rw [Set.mem_Ioi] at hx
        have hx0 : (0 : ℝ) ≤ x :=
          (show (0 : ℝ) ≤ ((1 : ℕ) : ℝ) by norm_num).trans hx.le
        exact Real.rpow_nonneg hx0 _)
  have hint : ∫ x in Set.Ioi (((1 : ℕ) : ℝ)), f x = (u - 1)⁻¹ := by
    dsimp only [f]
    rw [integral_Ioi_rpow_of_lt (a := -u) (c := (((1 : ℕ) : ℝ)))
      (by linarith) (by norm_num)]
    norm_num only [Nat.cast_one, Real.one_rpow]
    field_simp [show -u + 1 ≠ 0 by linarith, show u - 1 ≠ 0 by linarith]
    ring
  rw [hint] at htail
  have hsum : Summable (realDirichletWeight u) :=
    summable_realDirichletWeight hu
  have hsum1 : Summable (fun n : ℕ ↦ realDirichletWeight u (n + 1)) :=
    (summable_nat_add_iff 1).mpr hsum
  rw [hsum.tsum_eq_zero_add]
  have hzero : realDirichletWeight u 0 = 0 := by
    unfold realDirichletWeight
    simpa only [Nat.cast_zero] using
      (Real.zero_rpow (show -u ≠ 0 by linarith))
  rw [hzero, zero_add, hsum1.tsum_eq_zero_add]
  have hone : realDirichletWeight u 1 = 1 := by
    simp [realDirichletWeight]
  rw [hone]
  have htail' :
      (∑' n : ℕ, realDirichletWeight u (n + 1 + 1)) ≤ (u - 1)⁻¹ := by
    simpa [f, realDirichletWeight, Nat.cast_add, Nat.cast_one,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
  linarith

theorem taoExponent_sub_one_inv {X : ℕ} (hX : 1 < X) :
    (taoExponent X - 1)⁻¹ = Real.log (X : ℝ) := by
  unfold taoExponent
  have hlog : Real.log (X : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hX))
  field_simp
  ring

theorem tsum_taoWindowWeight_le_one_add_log {X : ℕ} (hX : 1 < X) :
    (∑' n : ℕ, taoWindowWeight X n) ≤ 1 + Real.log (X : ℝ) := by
  unfold taoWindowWeight
  simpa only [taoExponent_sub_one_inv hX] using
    tsum_realDirichletWeight_le_one_add_inv_sub_one (one_lt_taoExponent hX)

theorem taoLowCutoffMass_nonneg (X Y : ℕ) :
    0 ≤ taoLowCutoffMass X Y := by
  exact Finset.sum_nonneg fun n _ ↦ taoWindowWeight_nonneg X n

theorem taoLowCutoffResidueMass_nonneg {r : ℕ} (X Y : ℕ) (a : ZMod r) :
    0 ≤ taoLowCutoffResidueMass X Y a := by
  exact Finset.sum_nonneg fun n _ ↦ taoWindowWeight_nonneg X n

theorem sum_taoLowCutoffResidueMass {r X Y : ℕ} [NeZero r] :
    ∑ a : ZMod r, taoLowCutoffResidueMass X Y a = taoLowCutoffMass X Y := by
  exact sum_zmodResidueFiber_eq (Finset.range (Y ^ 2)) (taoWindowWeight X)

/-- Squaring the classwise low masses costs only their maximum times their
total mass.  This is the aggregate form needed by the classwise finite-tail
bridge. -/
theorem sum_sq_taoLowCutoffResidueMass_le
    {r X Y : ℕ} [NeZero r] (good : Finset (ZMod r)) (Mlow : ℝ)
    (hMlow : 0 ≤ Mlow)
    (hclass : ∀ a ∈ good, taoLowCutoffResidueMass X Y a ≤ Mlow) :
    ∑ a ∈ good, (taoLowCutoffResidueMass X Y a) ^ 2 ≤
      Mlow * taoLowCutoffMass X Y := by
  calc
    (∑ a ∈ good, (taoLowCutoffResidueMass X Y a) ^ 2) ≤
        ∑ a ∈ good, Mlow * taoLowCutoffResidueMass X Y a := by
      apply Finset.sum_le_sum
      intro a ha
      have hnonneg := taoLowCutoffResidueMass_nonneg X Y a
      nlinarith [hclass a ha]
    _ ≤ ∑ a : ZMod r, Mlow * taoLowCutoffResidueMass X Y a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
      intro a _ _
      exact mul_nonneg hMlow (taoLowCutoffResidueMass_nonneg X Y a)
    _ = Mlow * taoLowCutoffMass X Y := by
      rw [← Finset.mul_sum, sum_taoLowCutoffResidueMass]

/-! ## Arithmetic-progression mass bounds -/

/-- Finite Abel summation against any nonnegative decreasing weight.  The
constant `2` comes from the two boundary terms and the telescoping variation
of the weight. -/
theorem abs_weighted_sum_le_two_mul_of_abs_prefix_le
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    (f g : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hf_anti : ∀ {m n}, 0 < m → m ≤ n → f n ≤ f m)
    (hprefix : ∀ N, |∑ n ∈ Finset.range N, g n| ≤ B) :
    |∑ n ∈ Finset.Icc L U, f n * g n| ≤ 2 * B * f L := by
  let G : ℕ → ℝ := fun N ↦ ∑ n ∈ Finset.range N, g n
  have hlt : L < U + 1 := by omega
  have hab := Finset.sum_Ico_by_parts f g hlt
  have hIcc : Finset.Icc L U = Finset.Ico L (U + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc]
  change |∑ n ∈ Finset.Ico L (U + 1), f n • g n| ≤ 2 * B * f L
  rw [hab]
  simp only [Nat.add_sub_cancel, smul_eq_mul]
  have hGU : |G (U + 1)| ≤ B := hprefix (U + 1)
  have hGL : |G L| ≤ B := hprefix L
  have htermU : |f U * G (U + 1)| ≤ f U * B := by
    rw [abs_mul, abs_of_nonneg (hf_nonneg U)]
    exact mul_le_mul_of_nonneg_left hGU (hf_nonneg U)
  have htermL : |f L * G L| ≤ f L * B := by
    rw [abs_mul, abs_of_nonneg (hf_nonneg L)]
    exact mul_le_mul_of_nonneg_left hGL (hf_nonneg L)
  have hsum :
      |∑ n ∈ Finset.Ico L U, (f (n + 1) - f n) * G (n + 1)| ≤
        (f L - f U) * B := by
    calc
      |∑ n ∈ Finset.Ico L U, (f (n + 1) - f n) * G (n + 1)| ≤
          ∑ n ∈ Finset.Ico L U,
            |(f (n + 1) - f n) * G (n + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ico L U, (f n - f (n + 1)) * B := by
        apply Finset.sum_le_sum
        intro n hn
        have hnpos : 0 < n := hL.trans_le (Finset.mem_Ico.mp hn).1
        have hmono : f (n + 1) ≤ f n := hf_anti hnpos (Nat.le_succ n)
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hmono), neg_sub]
        exact mul_le_mul_of_nonneg_left (hprefix (n + 1))
          (sub_nonneg.mpr hmono)
      _ = (f L - f U) * B := by
        rw [← Finset.sum_mul, sum_Ico_sub_succ f hLU]
  let A : ℝ := f U * G (U + 1)
  let D : ℝ := f L * G L
  let S : ℝ := ∑ n ∈ Finset.Ico L U,
    (f (n + 1) - f n) * G (n + 1)
  change |A - D - S| ≤ 2 * B * f L
  have hfUL : f U ≤ f L := hf_anti hL hLU
  calc
    |A - D - S| ≤ |A| + |D| + |S| := by
      calc
        |A - D - S| ≤ |A - D| + |S| := abs_sub _ _
        _ ≤ (|A| + |D|) + |S| := by
          have ht := add_le_add_right (abs_sub A D) |S|
          linarith
        _ = |A| + |D| + |S| := rfl
    _ ≤ f U * B + f L * B + (f L - f U) * B := by linarith
    _ = 2 * B * f L := by ring

theorem abs_sum_taoWindowWeight_mul_centeredResidueIndicator_le
    {r X L U : ℕ} [NeZero r] (hX : 1 < X) (hL : 0 < L)
    (hLU : L ≤ U) (a : ZMod r) :
    |∑ n ∈ Finset.Icc L U,
        taoWindowWeight X n * centeredResidueIndicator r a n| ≤
      2 * taoWindowWeight X L := by
  simpa using abs_weighted_sum_le_two_mul_of_abs_prefix_le hL hLU
    (taoWindowWeight X) (centeredResidueIndicator r a) 1 (by norm_num)
    (taoWindowWeight_nonneg X)
    (fun hm hmn ↦ taoWindowWeight_antitoneOn_pos hX hm hmn)
    (fun N ↦ abs_sum_range_centeredResidueIndicator_le_one r a N)

/-- The mass of the concrete center interval in one residue class. -/
def taoWindowResidueMass {r : ℕ} (X Y N : ℕ) (a : ZMod r) : ℝ :=
  ∑ n ∈ zmodResidueFiber (taoWindowCenters Y N) a, taoWindowWeight X n

/-- The total mass of the concrete center interval. -/
def taoWindowMass (X Y N : ℕ) : ℝ :=
  ∑ n ∈ taoWindowCenters Y N, taoWindowWeight X n

theorem taoWindowResidueMass_nonneg {r : ℕ} (X Y N : ℕ) (a : ZMod r) :
    0 ≤ taoWindowResidueMass X Y N a := by
  exact Finset.sum_nonneg fun n _ ↦ taoWindowWeight_nonneg X n

theorem taoWindowMass_nonneg (X Y N : ℕ) : 0 ≤ taoWindowMass X Y N := by
  exact Finset.sum_nonneg fun n _ ↦ taoWindowWeight_nonneg X n

theorem taoWindowMass_pos_def {X Y N : ℕ} (hY : 0 < Y)
    (hYN : Y ^ 2 ≤ N) : 0 < taoWindowMass X Y N := by
  exact taoWindowMass_pos hY hYN

theorem taoWindowMass_le_one_add_log
    {X Y N : ℕ} (hX : 1 < X) :
    taoWindowMass X Y N ≤ 1 + Real.log (X : ℝ) := by
  unfold taoWindowMass taoWindowCenters
  exact ((summable_realDirichletWeight (one_lt_taoExponent hX)).sum_le_tsum
    (Finset.Icc (Y ^ 2) N) (fun n _ ↦ taoWindowWeight_nonneg X n)).trans
      (tsum_taoWindowWeight_le_one_add_log hX)

/-- Exact centered-indicator identity behind residue equidistribution. -/
theorem taoWindowResidueMass_sub_uniform
    {r X Y N : ℕ} [NeZero r] (a : ZMod r) :
    taoWindowResidueMass X Y N a - (r : ℝ)⁻¹ * taoWindowMass X Y N =
      ∑ n ∈ Finset.Icc (Y ^ 2) N,
        taoWindowWeight X n * centeredResidueIndicator r a n := by
  unfold taoWindowResidueMass taoWindowMass taoWindowCenters
    zmodResidueFiber centeredResidueIndicator
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases ha : (n : ZMod r) = a <;> simp [ha] <;> ring

/-- Residue-fiber mass equals the uniform share of the total mass up to the
optimal `O(weight(Y²))` discrepancy. -/
theorem taoWindowResidueMass_le_uniform_add
    {r X Y N : ℕ} [NeZero r] (hX : 1 < X) (hY : 0 < Y)
    (hYN : Y ^ 2 ≤ N) (a : ZMod r) :
    taoWindowResidueMass X Y N a ≤
      (r : ℝ)⁻¹ * taoWindowMass X Y N +
        2 * taoWindowWeight X (Y ^ 2) := by
  have habs := abs_sum_taoWindowWeight_mul_centeredResidueIndicator_le
    hX (pow_pos hY 2) hYN a
  rw [← taoWindowResidueMass_sub_uniform] at habs
  have hle := (le_abs_self
    (taoWindowResidueMass X Y N a -
      (r : ℝ)⁻¹ * taoWindowMass X Y N)).trans habs
  linarith

theorem taoWindowResidueMass_le_div_add_inv
    {r X Y N : ℕ} [NeZero r] (hX : 1 < X) (hY : 0 < Y)
    (hYN : Y ^ 2 ≤ N) (a : ZMod r) :
    taoWindowResidueMass X Y N a ≤
      taoWindowMass X Y N / (r : ℝ) + 2 / ((Y ^ 2 : ℕ) : ℝ) := by
  calc
    taoWindowResidueMass X Y N a ≤
        (r : ℝ)⁻¹ * taoWindowMass X Y N +
          2 * taoWindowWeight X (Y ^ 2) :=
      taoWindowResidueMass_le_uniform_add hX hY hYN a
    _ ≤ taoWindowMass X Y N / (r : ℝ) + 2 / ((Y ^ 2 : ℕ) : ℝ) := by
      have hw := taoWindowWeight_le_inv hX (pow_pos hY 2)
      rw [div_eq_mul_inv, div_eq_mul_inv]
      nlinarith

theorem taoLowCutoffMass_eq_window_one
    {X Y : ℕ} (hX : 1 < X) (hY : 2 ≤ Y) :
    taoLowCutoffMass X Y = taoWindowMass X 1 (Y ^ 2 - 1) := by
  let f : ℕ → ℝ := taoWindowWeight X
  have hA : 1 ≤ Y ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (ne_of_gt (pow_pos (by omega : 0 < Y) 2))
  have hsum := Finset.sum_range_add_sum_Ico f hA
  have hzero : ∑ n ∈ Finset.range 1, f n = 0 := by
    simp [f, taoWindowWeight_zero hX]
  have hsets : Finset.Ico 1 (Y ^ 2) = Finset.Icc 1 (Y ^ 2 - 1) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  unfold taoLowCutoffMass taoWindowMass taoWindowCenters
  rw [show (1 : ℕ) ^ 2 = 1 by norm_num]
  rw [← hsets]
  linarith

theorem taoLowCutoffResidueMass_eq_window_one
    {r X Y : ℕ} (hX : 1 < X) (hY : 2 ≤ Y) (a : ZMod r) :
    taoLowCutoffResidueMass X Y a =
      taoWindowResidueMass X 1 (Y ^ 2 - 1) a := by
  let f : ℕ → ℝ := fun n ↦
    if (n : ZMod r) = a then taoWindowWeight X n else 0
  have hA : 1 ≤ Y ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (ne_of_gt (pow_pos (by omega : 0 < Y) 2))
  have hsum := Finset.sum_range_add_sum_Ico f hA
  have hzero : ∑ n ∈ Finset.range 1, f n = 0 := by
    simp [f, taoWindowWeight_zero hX]
  have hsets : Finset.Ico 1 (Y ^ 2) = Finset.Icc 1 (Y ^ 2 - 1) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  unfold taoLowCutoffResidueMass taoWindowResidueMass taoWindowCenters
    zmodResidueFiber
  rw [show (1 : ℕ) ^ 2 = 1 by norm_num]
  rw [Finset.sum_filter, Finset.sum_filter]
  change (∑ n ∈ Finset.range (Y ^ 2), f n) =
    ∑ n ∈ Finset.Icc 1 (Y ^ 2 - 1), f n
  rw [← hsets]
  linarith

/-- A class receives its uniform share of the whole low cutoff, with an
absolute discrepancy at most two. -/
theorem taoLowCutoffResidueMass_le_uniform_add_two
    {r X Y : ℕ} [NeZero r] (hX : 1 < X) (hY : 2 ≤ Y)
    (a : ZMod r) :
    taoLowCutoffResidueMass X Y a ≤
      (r : ℝ)⁻¹ * taoLowCutoffMass X Y + 2 := by
  rw [taoLowCutoffResidueMass_eq_window_one hX hY,
    taoLowCutoffMass_eq_window_one hX hY]
  have hbase := taoWindowResidueMass_le_uniform_add
    (r := r) (X := X) (Y := 1) (N := Y ^ 2 - 1)
    hX (by norm_num) (by
      have hsq : (2 : ℕ) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hY 2
      norm_num at hsq ⊢
      omega) a
  simpa [taoWindowWeight, realDirichletWeight] using hbase

/-- The total low-cutoff mass only grows like `log(Y²)`, independently of
the much larger scale `X = Y^D`. -/
theorem taoLowCutoffMass_le_one_add_log_sq
    {X Y : ℕ} (hX : 1 < X) (hY : 2 ≤ Y) :
    taoLowCutoffMass X Y ≤ 1 + Real.log ((Y ^ 2 : ℕ) : ℝ) := by
  let f : ℕ → ℝ := taoWindowWeight X
  have hA : 1 ≤ Y ^ 2 :=
    Nat.one_le_iff_ne_zero.mpr (ne_of_gt (pow_pos (by omega : 0 < Y) 2))
  have hsum := Finset.sum_range_add_sum_Ico f hA
  have hzero : ∑ n ∈ Finset.range 1, f n = 0 := by
    simp [f, taoWindowWeight_zero hX]
  have hlowEq : taoLowCutoffMass X Y = ∑ n ∈ Finset.Ico 1 (Y ^ 2), f n := by
    unfold taoLowCutoffMass
    linarith
  rw [hlowEq]
  calc
    (∑ n ∈ Finset.Ico 1 (Y ^ 2), f n) ≤
        ∑ n ∈ Finset.Ico 1 (Y ^ 2), (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      exact taoWindowWeight_le_inv hX (by
        exact (Finset.mem_Ico.mp hn).1)
    _ ≤ ∑ n ∈ Finset.Icc 1 (Y ^ 2), (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self
      intro n _ _
      positivity
    _ = ((harmonic (Y ^ 2) : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log ((Y ^ 2 : ℕ) : ℝ) := harmonic_le_one_add_log _

/-- Fully explicit aggregate square bound for all selected low residue
classes. -/
theorem sum_sq_taoLowCutoffResidueMass_le_explicit
    {r X Y : ℕ} [NeZero r] (good : Finset (ZMod r))
    (hX : 1 < X) (hY : 2 ≤ Y) :
    ∑ a ∈ good, (taoLowCutoffResidueMass X Y a) ^ 2 ≤
      ((r : ℝ)⁻¹ * taoLowCutoffMass X Y + 2) *
        taoLowCutoffMass X Y := by
  apply sum_sq_taoLowCutoffResidueMass_le good
  · have hr : (0 : ℝ) ≤ (r : ℝ)⁻¹ := by positivity
    exact add_nonneg
      (mul_nonneg hr (taoLowCutoffMass_nonneg X Y)) (by norm_num)
  · intro a ha
    exact taoLowCutoffResidueMass_le_uniform_add_two hX hY a

theorem taoHighTailMass_nonneg (X N : ℕ) :
    0 ≤ taoHighTailMass X N := by
  exact tsum_nonneg fun n ↦ taoWindowWeight_nonneg X _

theorem taoLowCutoffMass_le_one_add_log {X Y : ℕ} (hX : 1 < X) :
    taoLowCutoffMass X Y ≤ 1 + Real.log (X : ℝ) := by
  exact (summable_realDirichletWeight (one_lt_taoExponent hX)).sum_le_tsum
    (Finset.range (Y ^ 2)) (fun n _ ↦ taoWindowWeight_nonneg X n) |>.trans
      (tsum_taoWindowWeight_le_one_add_log hX)

theorem tendsto_taoHighTailMass_zero {X : ℕ} (hX : 1 < X) :
    Tendsto (taoHighTailMass X) atTop (nhds 0) := by
  have hsum : Summable (taoWindowWeight X) :=
    summable_realDirichletWeight (one_lt_taoExponent hX)
  have hprefix := hsum.hasSum.tendsto_sum_nat
  have hprefixSucc : Tendsto
      (fun N : ℕ ↦ ∑ n ∈ Finset.range (N + 1), taoWindowWeight X n)
      atTop (nhds (∑' n : ℕ, taoWindowWeight X n)) := by
    convert hprefix.comp (tendsto_add_atTop_nat 1) using 1
    funext N
    simp only [Function.comp_apply]
  have heq (N : ℕ) :
      taoHighTailMass X N =
        (∑' n : ℕ, taoWindowWeight X n) -
          ∑ n ∈ Finset.range (N + 1), taoWindowWeight X n := by
    rw [← hsum.sum_add_tsum_nat_add (N + 1)]
    simp only [taoHighTailMass, Nat.add_assoc]
    ring
  rw [show taoHighTailMass X = fun N ↦
      (∑' n : ℕ, taoWindowWeight X n) -
        ∑ n ∈ Finset.range (N + 1), taoWindowWeight X n by
    funext N
    exact heq N]
  have ht : Tendsto
      (fun N : ℕ ↦ (∑' n : ℕ, taoWindowWeight X n) -
        ∑ n ∈ Finset.range (N + 1), taoWindowWeight X n)
      atTop (nhds ((∑' n : ℕ, taoWindowWeight X n) -
        ∑' n : ℕ, taoWindowWeight X n)) :=
    tendsto_const_nhds.sub hprefixSucc
  simpa only [sub_self] using ht

theorem exists_taoHighTailMass_le {X A : ℕ} (hX : 1 < X)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ N ≥ A, taoHighTailMass X N ≤ eps := by
  have ht := tendsto_taoHighTailMass_zero hX
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N0, hN0⟩ := ht eps heps
  refine ⟨max A N0, le_max_left _ _, ?_⟩
  have habs := hN0 (max A N0) (le_max_right _ _)
  rw [Real.dist_eq] at habs
  exact le_of_lt (by simpa [abs_of_nonneg (taoHighTailMass_nonneg X _)] using habs)

/-- Absolute domination of every shifted residue summand by the positive
Dirichlet weight. -/
theorem norm_shiftedResidueSummand_le_taoWindowWeight
    {r : ℕ} {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    (a : ZMod r) (m : ℕ) {X : ℕ} (hX : 1 < X) (n : ℕ) :
    ‖shiftedResidueSummand h a m (taoExponent X : ℂ) n‖ ≤
      taoWindowWeight X n := by
  rcases n with _ | n
  · rw [shiftedResidueSummand_zero a (one_lt_taoExponent hX)]
    simpa only [norm_zero] using taoWindowWeight_nonneg X 0
  · unfold shiftedResidueSummand
    split_ifs
    · rw [norm_mul, hh (by omega : n + 1 + m ≠ 0), one_mul,
        Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 1)]
      rfl
    · simp only [norm_zero]
      exact taoWindowWeight_nonneg X (n + 1)

/-- The same domination with the residue indicator retained. -/
theorem norm_shiftedResidueSummand_le_taoResidueWeight
    {r : ℕ} {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    (a : ZMod r) (m : ℕ) {X : ℕ} (hX : 1 < X) (n : ℕ) :
    ‖shiftedResidueSummand h a m (taoExponent X : ℂ) n‖ ≤
      if (n : ZMod r) = a then taoWindowWeight X n else 0 := by
  by_cases ha : (n : ZMod r) = a
  · rw [if_pos ha]
    exact norm_shiftedResidueSummand_le_taoWindowWeight hh a m hX n
  · rw [if_neg ha]
    unfold shiftedResidueSummand
    rw [if_neg ha]
    simp

/-- The finite series over `[Y²,N]` is the corresponding interval sum of
the raw shifted-series summand. -/
theorem finiteShiftedResidueSeries_taoWindow_eq
    {r : ℕ} (h : ℕ →*₀ ℂ) (a : ZMod r) (m X Y N : ℕ) :
    finiteShiftedResidueSeries (taoWindowCenters Y N) (taoWindowWeight X)
        h a m =
      ∑ n ∈ Finset.Icc (Y ^ 2) N,
        shiftedResidueSummand h a m (taoExponent X : ℂ) n := by
  unfold finiteShiftedResidueSeries zmodResidueFiber taoWindowCenters
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  unfold shiftedResidueSummand
  by_cases ha : (n : ZMod r) = a
  · rw [if_pos ha]
    have hweight :
        (taoWindowWeight X n : ℂ) =
          (n : ℂ) ^ (-(taoExponent X : ℂ)) := by
      unfold taoWindowWeight realDirichletWeight
      convert Complex.ofReal_cpow (Nat.cast_nonneg n) (-taoExponent X) using 1 <;>
        simp
    rw [hweight]
    rw [if_pos ha]
    ring
  · rw [if_neg ha]
    simp only [ha, ↓reduceIte]

/-- Honest finite-window error: a fixed low cutoff plus a vanishing high
tail.  The estimate is uniform in the residue and in the shift. -/
theorem norm_finiteShiftedResidueSeries_taoWindow_sub_le
    {r : ℕ} {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    (a : ZMod r) (m : ℕ) {X Y N : ℕ} (hX : 1 < X)
    (hYN : Y ^ 2 ≤ N + 1) :
    ‖finiteShiftedResidueSeries (taoWindowCenters Y N) (taoWindowWeight X)
          h a m - shiftedResidueSeries h a m (taoExponent X : ℂ)‖ ≤
      taoLowCutoffResidueMass X Y a + taoHighTailMass X N := by
  let F : ℕ → ℂ := fun n ↦
    shiftedResidueSummand h a m (taoExponent X : ℂ) n
  have hsumF : Summable F :=
    shiftedResidueSummable hh a m (by simpa using one_lt_taoExponent hX)
  have hsplit :
      (∑ n ∈ Finset.range (Y ^ 2), F n) +
          (∑ n ∈ Finset.Icc (Y ^ 2) N, F n) +
          (∑' j : ℕ, F (j + (N + 1))) = ∑' n : ℕ, F n := by
    rw [show Finset.Icc (Y ^ 2) N = Finset.Ico (Y ^ 2) (N + 1) by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega]
    rw [Finset.sum_range_add_sum_Ico _ hYN]
    simpa only [Nat.add_assoc] using hsumF.sum_add_tsum_nat_add (N + 1)
  rw [finiteShiftedResidueSeries_taoWindow_eq]
  change ‖(∑ n ∈ Finset.Icc (Y ^ 2) N, F n) - ∑' n : ℕ, F n‖ ≤ _
  rw [← hsplit]
  ring_nf
  have htailEq :
      (∑' j : ℕ, F (1 + j + N)) =
        ∑' j : ℕ, F (j + (N + 1)) := by
    apply tsum_congr
    intro j
    congr 1
    omega
  rw [htailEq]
  calc
    ‖-(∑ n ∈ Finset.range (Y ^ 2), F n) -
        ∑' j : ℕ, F (j + (N + 1))‖ ≤
        ‖∑ n ∈ Finset.range (Y ^ 2), F n‖ +
          ‖∑' j : ℕ, F (j + (N + 1))‖ := by
      simpa only [norm_neg, sub_eq_add_neg] using norm_add_le
        (-(∑ n ∈ Finset.range (Y ^ 2), F n))
        (-(∑' j : ℕ, F (j + (N + 1))))
    _ ≤ taoLowCutoffResidueMass X Y a + taoHighTailMass X N := by
      apply add_le_add
      · refine (norm_sum_le _ _).trans ?_
        calc
          (∑ n ∈ Finset.range (Y ^ 2), ‖F n‖) ≤
              ∑ n ∈ Finset.range (Y ^ 2),
                if (n : ZMod r) = a then taoWindowWeight X n else 0 := by
            exact Finset.sum_le_sum fun n _ ↦
              norm_shiftedResidueSummand_le_taoResidueWeight hh a m hX n
          _ = taoLowCutoffResidueMass X Y a := by
            unfold taoLowCutoffResidueMass zmodResidueFiber
            rw [Finset.sum_filter]
      · have htailSummable : Summable (fun j : ℕ ↦ F (j + (N + 1))) := by
          simpa only [Nat.add_comm] using (summable_nat_add_iff (N + 1)).mpr hsumF
        refine (norm_tsum_le_tsum_norm htailSummable.norm).trans ?_
        apply Summable.tsum_le_tsum
        · intro j
          exact norm_shiftedResidueSummand_le_taoWindowWeight hh a m hX _
        · exact htailSummable.norm
        · simpa only [taoWindowWeight, Nat.add_comm] using
            (summable_nat_add_iff (N + 1)).mpr
              (summable_realDirichletWeight (one_lt_taoExponent hX))

/-- Given any positive requested high-tail error, one upper cutoff works
simultaneously for every residue class and every shift because the
dominating scalar tail is independent of both. -/
theorem exists_taoWindow_uniform_shiftedResidue_tail
    {r : ℕ} {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {X Y : ℕ} (hX : 1 < X) {eps : ℝ} (heps : 0 < eps) :
    ∃ N ≥ Y ^ 2,
      taoHighTailMass X N ≤ eps ∧
      ∀ (a : ZMod r) (m : ℕ),
        ‖finiteShiftedResidueSeries (taoWindowCenters Y N) (taoWindowWeight X)
              h a m - shiftedResidueSeries h a m (taoExponent X : ℂ)‖ ≤
          taoLowCutoffResidueMass X Y a + eps := by
  obtain ⟨N, hN, htail⟩ :=
    exists_taoHighTailMass_le (X := X) (A := Y ^ 2) hX heps
  refine ⟨N, hN, htail, fun a m ↦ ?_⟩
  exact (norm_finiteShiftedResidueSeries_taoWindow_sub_le hh a m hX
    (hN.trans (Nat.le_succ N))).trans (add_le_add (le_refl _) htail)

end

end Erdos67
