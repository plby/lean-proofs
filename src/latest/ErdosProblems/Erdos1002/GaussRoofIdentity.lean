import ErdosProblems.Erdos1002.GaussPrefixMobius

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact continued-fraction roof identity

For a positive Gauss prefix `w` and a point in its half-open cylinder, the
product of the first `w.length` Gauss iterates is the reciprocal of
`Q_w + Q_{w-1} x_w`.  Taking logarithms gives the exact finite roof identity
used in the denominator-time change.  This file proves the algebraic identity
and the uniform `log 2` comparison with the terminal denominator; no ergodic
or limiting assertion is assumed here.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- Product of the first `n` points on a Gauss orbit. -/
def gaussOrbitProduct (n : ℕ) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.range n, gaussOrbit j x

/-- Exact finite product identity on a positive prefix cylinder. -/
theorem gaussOrbitProduct_eq_prefixDenominator
    {w : List ℕ} (hpos : IsPositiveCFWord w)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hw : x ∈ gaussHalfOpenPrefixCylinder w) :
    gaussOrbitProduct w.length x =
      1 / (((gaussPrefixMobius w).C : ℝ) * gaussOrbit w.length x +
        (gaussPrefixMobius w).D) := by
  induction w using List.reverseRecOn generalizing x with
  | nil => simp [gaussOrbitProduct, gaussPrefixMobius, gaussOrbit]
  | append_singleton w q ih =>
      have hq : 0 < q := hpos q (by simp)
      have hprefixPos : IsPositiveCFWord w := by
        intro a ha
        exact hpos a (by simp [ha])
      have hsplit :=
        (mem_gaussHalfOpenPrefixCylinder_append_iff w [q] hx).1 hw
      have ih' := ih hprefixPos hx hsplit.1
      let y : ℝ := gaussOrbit w.length x
      let z : ℝ := gaussOrbit (w.length + 1) x
      have hyIco : y ∈ Ico (0 : ℝ) 1 := by
        dsimp [y]
        cases w.length with
        | zero => simpa [gaussOrbit] using! hx
        | succ n => exact gaussOrbit_succ_mem_Ico n x
      have hyFirst : y ∈ firstDigitCylinder q := by
        exact hsplit.2.1
      have hzIco : z ∈ Ico (0 : ℝ) 1 := by
        dsimp [z]
        simpa [gaussOrbit_succ] using! gaussOrbit_succ_mem_Ico w.length x
      have hyEq : y = 1 / ((q : ℝ) + z) := by
        have hbranch := (gaussInverseBranch_gaussMap hq hyFirst).symm
        change y = gaussInverseBranch q (gaussMap y) at hbranch
        have horbit : gaussMap y = z := by
          dsimp [y, z]
          exact (gaussOrbit_succ w.length x).symm
        rw [horbit] at hbranch
        simpa [gaussInverseBranch] using! hbranch
      have hqz : (0 : ℝ) < (q : ℝ) + z := by
        have hqR : (0 : ℝ) < q := by exact_mod_cast hq
        linarith [hzIco.1]
      have hD : (0 : ℝ) < (gaussPrefixMobius w).D := by
        exact_mod_cast gaussPrefixMobius_D_pos hprefixPos
      have hC0 : (0 : ℝ) ≤ (gaussPrefixMobius w).C := by positivity
      have hden : (0 : ℝ) <
          ((gaussPrefixMobius w).C : ℝ) * y +
            (gaussPrefixMobius w).D := by
        exact add_pos_of_nonneg_of_pos (mul_nonneg hC0 hyIco.1) hD
      have hfinal : (0 : ℝ) <
          (gaussPrefixMobius w).C + (q : ℝ) * (gaussPrefixMobius w).D +
            z * (gaussPrefixMobius w).D := by
        have hqR : (0 : ℝ) < q := by exact_mod_cast hq
        have hqD : (0 : ℝ) <
            (q : ℝ) * (gaussPrefixMobius w).D := mul_pos hqR hD
        have hzD : (0 : ℝ) ≤
            z * (gaussPrefixMobius w).D := mul_nonneg hzIco.1 hD.le
        linarith
      have hprodSucc :
          gaussOrbitProduct (w.length + 1) x =
            gaussOrbitProduct w.length x * gaussOrbit w.length x := by
        unfold gaussOrbitProduct
        rw [Finset.prod_range_succ]
      change gaussOrbitProduct w.length x =
        1 / (((gaussPrefixMobius w).C : ℝ) * y +
          (gaussPrefixMobius w).D) at ih'
      simp only [List.length_append, List.length_singleton] at ⊢
      rw [gaussPrefixMobius_append_singleton]
      simp only
      rw [hprodSucc]
      change gaussOrbitProduct w.length x * y =
        1 / (((gaussPrefixMobius w).D : ℝ) * z +
          ((gaussPrefixMobius w).C + q * (gaussPrefixMobius w).D : ℕ))
      rw [ih', hyEq]
      push_cast
      field_simp [ne_of_gt hqz, ne_of_gt hD, ne_of_gt hden,
        ne_of_gt hfinal]
      convert! (div_self (ne_of_gt hfinal)).symm using 1
      all_goals ring

/-- The penultimate denominator coefficient never exceeds the terminal
denominator for a positive word. -/
theorem gaussPrefixMobius_C_le_D
    {w : List ℕ} (hpos : IsPositiveCFWord w) :
    (gaussPrefixMobius w).C ≤ (gaussPrefixMobius w).D := by
  induction w using List.reverseRecOn with
  | nil => simp [gaussPrefixMobius]
  | append_singleton w q ih =>
      have hq : 0 < q := hpos q (by simp)
      have hprefixPos : IsPositiveCFWord w := by
        intro a ha
        exact hpos a (by simp [ha])
      rw [gaussPrefixMobius_append_singleton]
      simp only
      exact (Nat.le_mul_of_pos_left _ hq).trans (Nat.le_add_left _ _)

/-- Finite sum of the roof observable `-log x` along a Gauss orbit. -/
def gaussRoofSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, -Real.log (gaussOrbit j x)

/-- Exact finite roof identity
`Σ_{j<n} -log x_j = log(Q_n + Q_{n-1} x_n)`. -/
theorem gaussRoofSum_eq_log_prefixDenominator
    {w : List ℕ} (hpos : IsPositiveCFWord w)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hw : x ∈ gaussHalfOpenPrefixCylinder w)
    (hnonzero : ∀ j : ℕ, gaussOrbit j x ≠ 0) :
    gaussRoofSum w.length x =
      Real.log (((gaussPrefixMobius w).C : ℝ) *
        gaussOrbit w.length x + (gaussPrefixMobius w).D) := by
  have hprod := gaussOrbitProduct_eq_prefixDenominator hpos hx hw
  have hlogProd :
      Real.log (gaussOrbitProduct w.length x) =
        ∑ j ∈ Finset.range w.length, Real.log (gaussOrbit j x) := by
    unfold gaussOrbitProduct
    exact Real.log_prod (fun j _hj ↦ hnonzero j)
  calc
    gaussRoofSum w.length x =
        -(∑ j ∈ Finset.range w.length, Real.log (gaussOrbit j x)) := by
      simp [gaussRoofSum, Finset.sum_neg_distrib]
    _ = -Real.log (gaussOrbitProduct w.length x) := by rw [hlogProd]
    _ = -Real.log
        (1 / (((gaussPrefixMobius w).C : ℝ) *
          gaussOrbit w.length x + (gaussPrefixMobius w).D)) := by rw [hprod]
    _ = Real.log (((gaussPrefixMobius w).C : ℝ) *
          gaussOrbit w.length x + (gaussPrefixMobius w).D) := by
      rw [one_div, Real.log_inv, neg_neg]

/-- The exact roof sum differs from the logarithm of the terminal denominator
by at most `log 2`, uniformly in the prefix and tail. -/
theorem abs_gaussRoofSum_sub_log_terminalDenominator_le_log_two
    {w : List ℕ} (hpos : IsPositiveCFWord w)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hw : x ∈ gaussHalfOpenPrefixCylinder w)
    (hnonzero : ∀ j : ℕ, gaussOrbit j x ≠ 0) :
    |gaussRoofSum w.length x -
        Real.log (cfTerminalDenominator w : ℝ)| ≤ Real.log 2 := by
  let C : ℝ := (gaussPrefixMobius w).C
  let D : ℝ := (gaussPrefixMobius w).D
  let y : ℝ := gaussOrbit w.length x
  have hroof := gaussRoofSum_eq_log_prefixDenominator
    hpos hx hw hnonzero
  change gaussRoofSum w.length x = Real.log (C * y + D) at hroof
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast gaussPrefixMobius_D_pos hpos
  have hC0 : 0 ≤ C := by positivity
  have hy0 : 0 ≤ y := by
    dsimp [y]
    cases w.length with
    | zero => simpa [gaussOrbit] using! hx.1
    | succ n => exact (gaussOrbit_succ_mem_Ico n x).1
  have hy1 : y ≤ 1 := by
    dsimp [y]
    cases w.length with
    | zero => exact hx.2.le
    | succ n => exact (gaussOrbit_succ_mem_Ico n x).2.le
  have hCDNat := gaussPrefixMobius_C_le_D hpos
  have hCD : C ≤ D := by
    dsimp [C, D]
    exact_mod_cast hCDNat
  have hCy : C * y ≤ C := by
    exact mul_le_of_le_one_right hC0 hy1
  have hdenLower : D ≤ C * y + D := by nlinarith [mul_nonneg hC0 hy0]
  have hdenPos : 0 < C * y + D := hD.trans_le hdenLower
  have hdenUpper : C * y + D ≤ 2 * D := by linarith
  have hlogLower : Real.log D ≤ Real.log (C * y + D) :=
    Real.log_le_log hD hdenLower
  have hlogUpper : Real.log (C * y + D) ≤ Real.log (2 * D) :=
    Real.log_le_log hdenPos hdenUpper
  have hlogMul : Real.log (2 * D) = Real.log 2 + Real.log D := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hD.ne']
  rw [hlogMul] at hlogUpper
  have hDterm : D = (cfTerminalDenominator w : ℝ) := by
    dsimp [D]
    rw [gaussPrefixMobius_D_eq_terminalDenominator]
  rw [← hDterm]
  rw [hroof, abs_of_nonneg (sub_nonneg.mpr hlogLower)]
  linarith

end

end Erdos1002
