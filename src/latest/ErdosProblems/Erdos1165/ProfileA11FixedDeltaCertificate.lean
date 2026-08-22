/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.AppendixA11A12OnePoint

/-!
# Uniform shifted-A.11 certificate at profile exponent `1/5`

This module verifies all Taylor hypotheses for an arbitrary finite family of
Gaussian blocks.  Only the global centre and width bounds are needed.  At a
scale outside every block the embedded deviation is zero, so no separate
coverage hypothesis is required.
-/

namespace Erdos1165.ProfileA11FixedDeltaCertificate

noncomputable section

open AppendixFirstMoment ProfileSmallBall ProfileTaylor ProfileA11Assembly
  GaussianSmallBall GaussianBlockFactorization GaussianMultiBlockProfile
  GaussianProfileReindex AppendixA11A12OnePoint

private lemma eighteen_le_rpow_four_fifths {l : ℕ}
    (hl : 18 ^ 5 ≤ l) :
    (18 : ℝ) ≤ (l : ℝ) ^ (4 / 5 : ℝ) := by
  have hlReal : ((18 : ℝ) ^ 5) ≤ (l : ℝ) := by exact_mod_cast hl
  have hroot := Real.rpow_le_rpow (by positivity) hlReal
    (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have heq : (((18 : ℝ) ^ 5) : ℝ) ^ (1 / 5 : ℝ) = 18 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 18)]
    norm_num
  rw [heq] at hroot
  exact hroot.trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ l by omega) : (1 : ℝ) ≤ l)
    (by norm_num : (1 / 5 : ℝ) ≤ 4 / 5))

private lemma rpow_six_fifths_eq {l : ℕ} (hl : 1 ≤ l) :
    (l : ℝ) ^ (1 + (1 / 5 : ℝ)) =
      (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by
  rw [Real.rpow_add (by positivity), Real.rpow_one]

private lemma eighteen_mul_rpow_six_fifths_le_sq {l : ℕ}
    (hl : 18 ^ 5 ≤ l) :
    18 * (l : ℝ) ^ (1 + (1 / 5 : ℝ)) ≤ (l : ℝ) ^ 2 := by
  have h18 := eighteen_le_rpow_four_fifths hl
  calc
    18 * (l : ℝ) ^ (1 + (1 / 5 : ℝ)) ≤
        (l : ℝ) ^ (4 / 5 : ℝ) *
          (l : ℝ) ^ (1 + (1 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_right h18 (by positivity)
    _ = (l : ℝ) ^ 2 := by
      rw [← Real.rpow_add (by positivity)]
      norm_num [Real.rpow_two]

private lemma one_le_rpow_six_fifths {l : ℕ} (hl : 1 ≤ l) :
    (1 : ℝ) ≤ (l : ℝ) ^ (1 + (1 / 5 : ℝ)) :=
  Real.one_le_rpow (by exact_mod_cast hl) (by norm_num)

private lemma rpow_six_fifths_succ_le {l : ℕ} (hl : 2 ≤ l) :
    ((l + 1 : ℕ) : ℝ) ^ (1 + (1 / 5 : ℝ)) ≤
      (9 / 4 : ℝ) * (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by
  have hbase : ((l + 1 : ℕ) : ℝ) ≤ (3 / 2 : ℝ) * l := by
    push_cast
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hpow := Real.rpow_le_rpow (by positivity) hbase
    (by norm_num : (0 : ℝ) ≤ 1 + 1 / 5)
  calc
    ((l + 1 : ℕ) : ℝ) ^ (1 + (1 / 5 : ℝ)) ≤
        ((3 / 2 : ℝ) * l) ^ (1 + (1 / 5 : ℝ)) := hpow
    _ = (3 / 2 : ℝ) ^ (1 + (1 / 5 : ℝ)) *
        (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) (by positivity)]
    _ ≤ (3 / 2 : ℝ) ^ (2 : ℝ) *
        (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
      · exact Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 3 / 2)
          (by norm_num : (1 + 1 / 5 : ℝ) ≤ 2)
      · positivity
    _ = (9 / 4 : ℝ) * (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by
      norm_num [Real.rpow_two]

private lemma deviation_abs_le
    {blocks : List GaussianBlock}
    (hwidth : ∀ b ∈ blocks, ∀ l, BlockContains b l →
      (b.radius : ℝ) ≤ (l : ℝ) ^ (1 + (1 / 5 : ℝ)))
    (p : IndependentGaussianBlockPaths blocks) (l : ℕ) :
    |(independentBlockDeviation p l : ℝ)| ≤
      (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by
  rcases independentBlockDeviation_eq_zero_or_mem p l with
    hz | ⟨b, hb, hbl, hmem⟩
  · rw [hz]
    simp only [Int.cast_zero, abs_zero]
    positivity
  · have hbox := mem_gaussianBox.mp hmem
    have habsInt : |independentBlockDeviation p l| ≤ (b.radius : ℤ) := by
      rw [abs_le]
      exact hbox
    have habsReal : |(independentBlockDeviation p l : ℝ)| ≤ b.radius := by
      exact_mod_cast habsInt
    exact habsReal.trans (hwidth b hb l hbl)

private lemma deviation_increment_abs_le
    {blocks : List GaussianBlock}
    (hwidth : ∀ b ∈ blocks, ∀ l, BlockContains b l →
      (b.radius : ℝ) ≤ (l : ℝ) ^ (1 + (1 / 5 : ℝ)))
    (p : IndependentGaussianBlockPaths blocks) {l : ℕ} (hl : 2 ≤ l) :
    |(independentBlockDeviation p (l + 1) : ℝ) -
      (independentBlockDeviation p l : ℝ)| ≤
        (13 / 4 : ℝ) * (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by
  have h0 := deviation_abs_le hwidth p l
  have h1 := deviation_abs_le hwidth p (l + 1)
  have hsucc := rpow_six_fifths_succ_le hl
  calc
    |(independentBlockDeviation p (l + 1) : ℝ) -
        (independentBlockDeviation p l : ℝ)| ≤
      |(independentBlockDeviation p (l + 1) : ℝ)| +
        |(independentBlockDeviation p l : ℝ)| := abs_sub _ _
    _ ≤ ((l + 1 : ℕ) : ℝ) ^ (1 + (1 / 5 : ℝ)) +
        (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := add_le_add h1 h0
    _ ≤ (9 / 4 : ℝ) * (l : ℝ) ^ (1 + (1 / 5 : ℝ)) +
        (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by gcongr
    _ = (13 / 4 : ℝ) * (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by ring

/-- All shifted A.11 hypotheses at exponent `1/5`, uniformly for any block
family satisfying the exact centre and width constraints. -/
theorem embeddedTailA11Certificate_one_fifth
    {n start : ℕ} {blocks : List GaussianBlock}
    (hstartLarge : 18 ^ 5 ≤ start)
    (hcenter : ∀ b ∈ blocks, ∀ l, BlockContains b l →
      b.radius ≤ profileCenter l)
    (hwidth : ∀ b ∈ blocks, ∀ l, BlockContains b l →
      (b.radius : ℝ) ≤ (l : ℝ) ^ (1 + (1 / 5 : ℝ))) :
    EmbeddedTailA11Certificate n start (1 / 5 : ℝ) 2 1 10 blocks := by
  have hcenteredReal : ∀ (p : IndependentGaussianBlockPaths blocks) l,
      (centeredProfileValue l (independentBlockDeviation p l) : ℝ) =
        2 * (l : ℝ) ^ 2 + (independentBlockDeviation p l : ℝ) := by
    intro p l
    exact centeredProfileValue_real_eq
      (independentBlockDeviation_lower p hcenter l)
  have htwo : ∀ (p : IndependentGaussianBlockPaths blocks) l,
      l ∈ Finset.Ico start n →
      2 ≤ centeredProfileValue l (independentBlockDeviation p l) := by
    intro p l hl
    have hl' := Finset.mem_Ico.mp hl
    have hlLarge := hstartLarge.trans hl'.1
    have hD := deviation_abs_le hwidth p l
    have hstrong := eighteen_mul_rpow_six_fifths_le_sq hlLarge
    have hR0 : 0 ≤ (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by positivity
    have hRle : (l : ℝ) ^ (1 + (1 / 5 : ℝ)) ≤ (l : ℝ) ^ 2 := by
      linarith
    have hDlow := neg_le_of_abs_le hD
    have hm := hcenteredReal p l
    have hlReal : (2 : ℝ) ≤ l := by exact_mod_cast (show 2 ≤ l by omega)
    have hmTwo : (2 : ℝ) ≤
        centeredProfileValue l (independentBlockDeviation p l) := by
      rw [hm]
      nlinarith [sq_nonneg ((l : ℝ) - 1)]
    exact_mod_cast hmTwo
  have hbase : ∀ (p : IndependentGaussianBlockPaths blocks) l,
      l ∈ Finset.Ico start n →
      (l : ℝ) ^ 2 ≤
        (centeredProfileValue l (independentBlockDeviation p l) - 1 : ℕ) := by
    intro p l hl
    have hl' := Finset.mem_Ico.mp hl
    have hlLarge := hstartLarge.trans hl'.1
    have ht := htwo p l hl
    have hD := deviation_abs_le hwidth p l
    have hstrong := eighteen_mul_rpow_six_fifths_le_sq hlLarge
    have hRone := one_le_rpow_six_fifths (show 1 ≤ l by omega)
    have hDlow := neg_le_of_abs_le hD
    have hm := hcenteredReal p l
    rw [Nat.cast_sub (by omega : 1 ≤
      centeredProfileValue l (independentBlockDeviation p l))]
    push_cast
    rw [hm]
    linarith
  have hclose : ∀ (p : IndependentGaussianBlockPaths blocks) l,
      l ∈ Finset.Ico start n →
      |2 * (l : ℝ) ^ 2 -
        (centeredProfileValue l (independentBlockDeviation p l) - 1 : ℕ)| ≤
          2 * (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by
    intro p l hl
    have ht := htwo p l hl
    have hD := deviation_abs_le hwidth p l
    have hm := hcenteredReal p l
    have hRone := one_le_rpow_six_fifths (show 1 ≤ l by
      have := (Finset.mem_Ico.mp hl).1
      omega)
    rw [Nat.cast_sub (by omega : 1 ≤
      centeredProfileValue l (independentBlockDeviation p l))]
    push_cast
    rw [hm]
    rw [rpow_six_fifths_eq (show 1 ≤ l by
      have := (Finset.mem_Ico.mp hl).1
      omega)] at hD hRone
    calc
      |2 * (l : ℝ) ^ 2 -
          (2 * (l : ℝ) ^ 2 + (independentBlockDeviation p l : ℝ) - 1)| =
          |1 - (independentBlockDeviation p l : ℝ)| := by congr 1 <;> ring
      _ ≤ 1 + |(independentBlockDeviation p l : ℝ)| := by
        simpa only [abs_one] using abs_sub 1 (independentBlockDeviation p l : ℝ)
      _ ≤ 2 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) := by linarith
      _ = 2 * (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by ring
  have hinc : ∀ (p : IndependentGaussianBlockPaths blocks) l,
      l ∈ Finset.Ico start n →
      |parabolicTransitionIncrement
        (centeredProfileValue l (independentBlockDeviation p l))
        (centeredProfileValue (l + 1) (independentBlockDeviation p (l + 1)))| ≤
          10 * (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by
    intro p l hl
    have hl' := Finset.mem_Ico.mp hl
    have hm0 := hcenteredReal p l
    have hm1 := hcenteredReal p (l + 1)
    have hDinc := deviation_increment_abs_le hwidth p
      (show 2 ≤ l by omega)
    have hRone := one_le_rpow_six_fifths (show 1 ≤ l by omega)
    have hlReal : (2 : ℝ) ≤ l := by exact_mod_cast (show 2 ≤ l by omega)
    unfold parabolicTransitionIncrement
    rw [hm0, hm1]
    push_cast
    rw [rpow_six_fifths_eq (show 1 ≤ l by omega)] at hDinc hRone
    have hpOne : (1 : ℝ) ≤ (l : ℝ) ^ (1 / 5 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ l by omega)) (by norm_num)
    have hlR : (l : ℝ) ≤ (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ l by positivity)
        (sub_nonneg.mpr hpOne)]
    have hlinear : 4 * (l : ℝ) + 2 ≤
        (5 : ℝ) * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) := by
      nlinarith
    calc
      |(2 * ((l : ℝ) + 1) ^ 2 +
          (independentBlockDeviation p (l + 1) : ℝ)) -
        (2 * (l : ℝ) ^ 2 + (independentBlockDeviation p l : ℝ))| =
          |(4 * (l : ℝ) + 2) +
            ((independentBlockDeviation p (l + 1) : ℝ) -
              (independentBlockDeviation p l : ℝ))| := by congr 1 <;> ring
      _ ≤ |4 * (l : ℝ) + 2| +
          |(independentBlockDeviation p (l + 1) : ℝ) -
            (independentBlockDeviation p l : ℝ)| := abs_add_le _ _
      _ = (4 * (l : ℝ) + 2) +
          |(independentBlockDeviation p (l + 1) : ℝ) -
            (independentBlockDeviation p l : ℝ)| := by
        rw [abs_of_nonneg (by positivity)]
      _ ≤ (5 : ℝ) * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) +
          (13 / 4 : ℝ) * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) :=
        add_le_add hlinear hDinc
      _ ≤ 10 * (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by
        have : 0 ≤ (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by positivity
        nlinarith
  have hwindow : ∀ (p : IndependentGaussianBlockPaths blocks) l,
      l ∈ Finset.Ico start n →
      InEdgeTaylorWindow
        (centeredProfileValue l (independentBlockDeviation p l))
        (centeredProfileValue (l + 1) (independentBlockDeviation p (l + 1))) := by
    intro p l hl
    have hl' := Finset.mem_Ico.mp hl
    have hlLarge := hstartLarge.trans hl'.1
    have ht := htwo p l hl
    have hb := hbase p l hl
    have hm0 := hcenteredReal p l
    have hm1 := hcenteredReal p (l + 1)
    have hDinc := deviation_increment_abs_le hwidth p
      (show 2 ≤ l by omega)
    have hstrong := eighteen_mul_rpow_six_fifths_le_sq hlLarge
    have hRone := one_le_rpow_six_fifths (show 1 ≤ l by omega)
    have hlReal : (2 : ℝ) ≤ l := by exact_mod_cast (show 2 ≤ l by omega)
    unfold InEdgeTaylorWindow edgeDeviation
    rw [Nat.cast_sub (by omega : 1 ≤
      centeredProfileValue l (independentBlockDeviation p l))]
    push_cast
    rw [hm0, hm1]
    rw [rpow_six_fifths_eq (show 1 ≤ l by omega)] at hDinc hRone hstrong
    have hpOne : (1 : ℝ) ≤ (l : ℝ) ^ (1 / 5 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ l by omega)) (by norm_num)
    have hlR : (l : ℝ) ≤ (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ l by positivity)
        (sub_nonneg.mpr hpOne)]
    have hlinear : 4 * (l : ℝ) + 3 ≤
        (23 / 4 : ℝ) * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) := by
      nlinarith
    have hedge :
        |(2 * ((l : ℝ) + 1) ^ 2 +
            (independentBlockDeviation p (l + 1) : ℝ)) -
          (2 * (l : ℝ) ^ 2 + (independentBlockDeviation p l : ℝ) - 1)| ≤
          9 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) := by
      calc
        _ = |(4 * (l : ℝ) + 3) +
            ((independentBlockDeviation p (l + 1) : ℝ) -
              (independentBlockDeviation p l : ℝ))| := by congr 1 <;> ring
        _ ≤ |4 * (l : ℝ) + 3| +
            |(independentBlockDeviation p (l + 1) : ℝ) -
              (independentBlockDeviation p l : ℝ)| := abs_add_le _ _
        _ = (4 * (l : ℝ) + 3) +
            |(independentBlockDeviation p (l + 1) : ℝ) -
              (independentBlockDeviation p l : ℝ)| := by
          rw [abs_of_nonneg (by positivity)]
        _ ≤ (23 / 4 : ℝ) * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) +
            (13 / 4 : ℝ) * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) :=
          add_le_add hlinear hDinc
        _ = 9 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) := by ring
    have hhalf :
        9 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) ≤
          ((centeredProfileValue l (independentBlockDeviation p l) - 1 : ℕ) : ℝ) /
            2 := by
      have hs : 18 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) ≤
          (l : ℝ) ^ 2 := hstrong
      nlinarith
    have hcastSucc : (((l + 1 : ℕ) : ℝ)) = (l : ℝ) + 1 := by push_cast; ring
    rw [hcastSucc]
    refine hedge.trans ?_
    calc
      9 * ((l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ)) ≤
          ((centeredProfileValue l (independentBlockDeviation p l) - 1 : ℕ) : ℝ) /
            2 := hhalf
      _ = (2 * (l : ℝ) ^ 2 + (independentBlockDeviation p l : ℝ) - 1) / 2 := by
        rw [Nat.cast_sub (by omega : 1 ≤
          centeredProfileValue l (independentBlockDeviation p l))]
        push_cast
        rw [hm0]
  refine {
    delta_pos := by norm_num
    delta_le_third := by norm_num
    A_nonneg := by norm_num
    B_nonneg := by norm_num
    C_nonneg := by norm_num
    entry_two_le := htwo
    taylorWindow := hwindow
    base := hbase
    close := hclose
    moderate := ?_
    increment := hinc
    deviation := ?_
    deviationIncrement := ?_ }
  · intro l hl
    have hl' := Finset.mem_Ico.mp hl
    have hs := eighteen_mul_rpow_six_fifths_le_sq
      (hstartLarge.trans hl'.1)
    rw [rpow_six_fifths_eq (show 1 ≤ l by omega)] at hs
    have hR0 : 0 ≤ (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by positivity
    nlinarith
  · intro p l hl
    have hD := deviation_abs_le hwidth p l
    rw [rpow_six_fifths_eq (show 1 ≤ l by
      have hl' := Finset.mem_Icc.mp hl
      have := hstartLarge.trans hl'.1
      omega)] at hD
    simpa only [one_mul] using hD
  · intro p l hl
    have hl' := Finset.mem_Ico.mp hl
    have hD := deviation_increment_abs_le hwidth p (show 2 ≤ l by omega)
    rw [rpow_six_fifths_eq (show 1 ≤ l by omega)] at hD
    have hR0 : 0 ≤ (l : ℝ) * (l : ℝ) ^ (1 / 5 : ℝ) := by positivity
    exact hD.trans (by nlinarith)

end

end Erdos1165.ProfileA11FixedDeltaCertificate
