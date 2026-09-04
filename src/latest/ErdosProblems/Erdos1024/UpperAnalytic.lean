/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1024.UpperCriterion
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Quantitative parameters for the upper bound

We use `144 n` equiprobable colors and require every
`ceil (200 * sqrt (n log n))`-set to contain a selected triple.  The larger
constants make every elementary estimate comfortably strict.
-/

open Filter
open scoped BigOperators

namespace Erdos1024
namespace Upper

def colorCount (n : ℕ) : ℕ := 144 * n

noncomputable def upperScale (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * Real.log n)

noncomputable def upperThreshold (n : ℕ) : ℕ :=
  ⌈200 * upperScale n⌉₊

noncomputable def overlapCharge (n : ℕ) : ℝ :=
  3 * (((1 : ℝ) / colorCount n) ^ 2)

noncomputable def holeProbability (n : ℕ) : ℝ :=
  ((((colorCount n - 1 : ℕ) : ℝ) / colorCount n) ^
    (upperThreshold n).choose 3)

noncomputable def holeCharge (n : ℕ) (_S : HoleIndex n (upperThreshold n)) : ℝ :=
  2 * holeProbability n * Real.exp
    (2 * overlapCharge n *
      (6 * n * (upperThreshold n).choose 3 : ℕ))

lemma card_holeIndex (n t : ℕ) : Fintype.card (HoleIndex n t) = n.choose t := by
  classical
  rw [Fintype.card_subtype]
  change ((Finset.univ : Finset (Finset (Fin n))).filter
    (fun S ↦ S.card = t)).card = n.choose t
  have heq : (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S ↦ S.card = t) = Finset.univ.powersetCard t := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [heq, Finset.card_powersetCard]
  simp

lemma choose_three_lower {t : ℕ} (ht : 4 ≤ t) :
    (t : ℝ) ^ 3 / 48 ≤ (t.choose 3 : ℕ) := by
  have ht1Nat : t ≤ 2 * (t - 1) := by omega
  have ht2Nat : t ≤ 2 * (t - 2) := by omega
  have ht1Cast : (t : ℝ) ≤ 2 * ((t - 1 : ℕ) : ℝ) := by exact_mod_cast ht1Nat
  have ht2Cast : (t : ℝ) ≤ 2 * ((t - 2 : ℕ) : ℝ) := by exact_mod_cast ht2Nat
  have hcast1 : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hcast2 : ((t - 2 : ℕ) : ℝ) = (t : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have ht1 : (t : ℝ) / 2 ≤ (t : ℝ) - 1 := by
    rw [← hcast1]
    nlinarith
  have ht2 : (t : ℝ) / 2 ≤ (t : ℝ) - 2 := by
    rw [← hcast2]
    nlinarith
  have hdescNat : 6 * t.choose 3 = t * (t - 1) * (t - 2) := by
    calc
      6 * t.choose 3 = Nat.factorial 3 * t.choose 3 := by norm_num
      _ = t.descFactorial 3 := (Nat.descFactorial_eq_factorial_mul_choose t 3).symm
      _ = t * (t - 1) * (t - 2) := by
        simp [Nat.descFactorial_succ, Nat.descFactorial, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc]
  have hdesc : (6 : ℝ) * (t.choose 3 : ℕ) =
      (t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - 2) := by
    have hdescCast : (6 : ℝ) * (t.choose 3 : ℕ) =
        (t : ℝ) * ((t - 1 : ℕ) : ℝ) * ((t - 2 : ℕ) : ℝ) := by
      exact_mod_cast hdescNat
    simpa [hcast1, hcast2] using hdescCast
  have ht0 : 0 ≤ (t : ℝ) := by positivity
  have hprod : (t : ℝ) * ((t : ℝ) / 2) * ((t : ℝ) / 2) ≤
      (t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - 2) := by
    gcongr <;> nlinarith
  nlinarith

lemma exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hden : 0 < 1 + 2 * x := by linarith
  have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * x)
  have hinv : 1 / Real.exp (2 * x) ≤ 1 / (1 + 2 * x) :=
    one_div_le_one_div_of_le hden hexp
  have hrat : 1 / (1 + 2 * x) ≤ 1 - x := by
    rw [div_le_iff₀ hden]
    nlinarith
  simpa [Real.exp_neg] using hinv.trans hrat

lemma one_le_exp_mul_pow_one_sub {x : ℝ} {D : ℕ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    1 ≤ Real.exp (2 * x * D) * (1 - x) ^ D := by
  have hone := exp_neg_two_mul_le_one_sub hx0 hxhalf
  have hpows : (Real.exp (-2 * x)) ^ D ≤ (1 - x) ^ D :=
    pow_le_pow_left₀ (Real.exp_pos _).le hone D
  have hexp : Real.exp (-2 * x * D) ≤ (1 - x) ^ D := by
    calc
      Real.exp (-2 * x * D) = (Real.exp (-2 * x)) ^ D := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := hpows
  have hmul := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (2 * x * D)).le
  calc
    1 = Real.exp (2 * x * D) * Real.exp (-2 * x * D) := by
      rw [← Real.exp_add]
      ring_nf
      simp
    _ ≤ _ := hmul

lemma overlapCharge_nonneg (n : ℕ) : 0 ≤ overlapCharge n := by
  unfold overlapCharge
  positivity

lemma overlapCharge_le_half {n : ℕ} (hn : 0 < n) :
    overlapCharge n ≤ 1 / 2 := by
  have hKpos : (0 : ℝ) < colorCount n := by
    exact_mod_cast (show 0 < colorCount n by simp [colorCount, hn])
  unfold overlapCharge
  rw [div_pow]
  norm_num only [one_pow]
  rw [show 3 * (1 / (colorCount n : ℝ) ^ 2) =
    3 / (colorCount n : ℝ) ^ 2 by ring]
  rw [div_le_iff₀ (sq_pos_of_pos hKpos)]
  have hKlarge : (144 : ℝ) ≤ colorCount n := by
    exact_mod_cast (show 144 ≤ colorCount n by dsimp [colorCount]; omega)
  nlinarith [sq_nonneg ((colorCount n : ℝ) - 144)]

lemma hole_criterion {n : ℕ} (hn : 0 < n)
    (S : HoleIndex n (upperThreshold n)) :
    2 * badProbability (colorCount n) (Sum.inr S) ≤
      holeCharge n S *
        (1 - overlapCharge n) ^
          (6 * n * (upperThreshold n).choose 3) := by
  have hKpos : (0 : ℝ) < colorCount n := by
    exact_mod_cast (show 0 < colorCount n by simp [colorCount, hn])
  have hx0 := overlapCharge_nonneg n
  have hxhalf := overlapCharge_le_half hn
  have hone := one_le_exp_mul_pow_one_sub
    (D := 6 * n * (upperThreshold n).choose 3) hx0 hxhalf
  change 2 * holeProbability n ≤ 2 * holeProbability n *
      Real.exp (2 * overlapCharge n *
        (6 * n * (upperThreshold n).choose 3 : ℕ)) *
      (1 - overlapCharge n) ^ (6 * n * (upperThreshold n).choose 3)
  have hq0 : 0 ≤ holeProbability n := by
    unfold holeProbability
    positivity
  nlinarith

lemma overlap_loss_le {n : ℕ} (hn : 0 < n) :
    (12 * n : ℝ) * overlapCharge n ≤ 1 / 4 := by
  have hKpos : (0 : ℝ) < colorCount n := by
    exact_mod_cast (show 0 < colorCount n by simp [colorCount, hn])
  unfold overlapCharge
  rw [div_pow]
  norm_num only [one_pow]
  rw [show 12 * (n : ℝ) * (3 * (1 / (colorCount n : ℝ) ^ 2)) =
    36 * (n : ℝ) / (colorCount n : ℝ) ^ 2 by ring]
  rw [div_le_iff₀ (sq_pos_of_pos hKpos)]
  norm_num [colorCount]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

lemma threshold_bounds {n : ℕ} (hn : 3 ≤ n) :
    200 * upperScale n ≤ upperThreshold n ∧
      (upperThreshold n : ℝ) ≤ 201 * upperScale n ∧
      4 ≤ upperThreshold n := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog : 1 < Real.log (n : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hnpos]
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hn)
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hinside : 1 ≤ (n : ℝ) * Real.log n := by nlinarith
  have hg : 1 ≤ upperScale n := by
    rw [upperScale]
    exact Real.one_le_sqrt.mpr hinside
  have hlower : 200 * upperScale n ≤ (upperThreshold n : ℝ) := by
    exact Nat.le_ceil _
  have hupper0 : (upperThreshold n : ℝ) < 200 * upperScale n + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hupper : (upperThreshold n : ℝ) ≤ 201 * upperScale n := by
    nlinarith
  have ht4 : 4 ≤ upperThreshold n := by
    exact_mod_cast (show (4 : ℝ) ≤ upperThreshold n by nlinarith)
  exact ⟨hlower, hupper, ht4⟩

lemma exponential_exponent_le {n : ℕ} (hn : 3 ≤ n) :
    (upperThreshold n : ℝ) * Real.log n -
        ((upperThreshold n).choose 3 : ℕ) / (192 * n : ℝ) ≤ -3 := by
  let g := upperScale n
  have hb := threshold_bounds hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog : 1 < Real.log (n : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hnpos]
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hn)
  have hg0 : 0 ≤ g := Real.sqrt_nonneg _
  have hgsq : g ^ 2 = (n : ℝ) * Real.log n := by
    dsimp [g, upperScale]
    exact Real.sq_sqrt (mul_nonneg hnpos.le (by linarith))
  have hM := choose_three_lower hb.2.2
  have ht0 : 0 ≤ (upperThreshold n : ℝ) := by positivity
  have htCube : (200 * g) ^ 3 ≤ (upperThreshold n : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hb.1 3
  have hglog : 1 ≤ g * Real.log n := by
    have hinside : 1 ≤ (n : ℝ) * Real.log n := by
      have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hg : 1 ≤ g := by
      dsimp [g, upperScale]
      exact Real.one_le_sqrt.mpr hinside
    nlinarith
  have hratio : 800 * (g * Real.log n) ≤
      ((upperThreshold n).choose 3 : ℕ) / (192 * n : ℝ) := by
    have hcore : 800 * 192 * g ^ 3 ≤
        ((upperThreshold n).choose 3 : ℕ) := by
      nlinarith [htCube, hM]
    have hidentity : g ^ 3 = (n : ℝ) * (g * Real.log n) := by
      calc
        g ^ 3 = g * g ^ 2 := by ring
        _ = g * ((n : ℝ) * Real.log n) := by rw [hgsq]
        _ = (n : ℝ) * (g * Real.log n) := by ring
    rw [le_div_iff₀ (by positivity)]
    calc
      800 * (g * Real.log n) * (192 * (n : ℝ)) =
          800 * 192 * g ^ 3 := by rw [hidentity]; ring
      _ ≤ _ := hcore
  have htlog : (upperThreshold n : ℝ) * Real.log n ≤
      201 * (g * Real.log n) := by
    dsimp [g]
    calc
      (upperThreshold n : ℝ) * Real.log n ≤
          (201 * upperScale n) * Real.log n :=
        mul_le_mul_of_nonneg_right hb.2.1 (by linarith)
      _ = 201 * (upperScale n * Real.log n) := by ring
  nlinarith

lemma two_mul_exp_neg_three_le_quarter :
    2 * Real.exp (-3) ≤ (1 / 4 : ℝ) := by
  have he : (8 : ℝ) < Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [Real.exp_one_gt_two, Real.exp_pos 1]
  rw [Real.exp_neg]
  have hdiv : 2 / Real.exp 3 < (1 / 4 : ℝ) := by
    rw [div_lt_iff₀ (Real.exp_pos 3)]
    nlinarith
  simpa [div_eq_mul_inv] using hdiv.le

lemma total_hole_charge_le {n : ℕ} (hn : 3 ≤ n) :
    ∑ S : HoleIndex n (upperThreshold n), holeCharge n S ≤ 1 / 4 := by
  have hn0 : 0 < n := by omega
  have hK : 0 < colorCount n := by simp [colorCount, hn0]
  have hchoose : ((n.choose (upperThreshold n) : ℕ) : ℝ) ≤
      (n : ℝ) ^ upperThreshold n := by exact_mod_cast Nat.choose_le_pow n (upperThreshold n)
  have hpowexp : (n : ℝ) ^ upperThreshold n =
      Real.exp ((upperThreshold n : ℝ) * Real.log n) := by
    symm
    calc
      Real.exp ((upperThreshold n : ℝ) * Real.log n) =
          Real.exp (Real.log n) ^ upperThreshold n :=
        Real.exp_nat_mul _ _
      _ = (n : ℝ) ^ upperThreshold n := by rw [Real.exp_log (by positivity)]
  have hq : holeProbability n ≤
      Real.exp (-((upperThreshold n).choose 3 : ℕ) / colorCount n) := by
    have hbase : (((colorCount n - 1 : ℕ) : ℝ) / colorCount n) =
        1 - 1 / (colorCount n : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      field_simp
      ring
    rw [holeProbability, hbase]
    have hbase0 : 0 ≤ 1 - 1 / (colorCount n : ℝ) := by
      have hKone : (1 : ℝ) ≤ colorCount n := by exact_mod_cast hK
      rw [sub_nonneg]
      exact div_le_one (by positivity) |>.2 (by simpa using hKone)
    calc
      (1 - 1 / (colorCount n : ℝ)) ^ (upperThreshold n).choose 3 ≤
          (Real.exp (-(1 / (colorCount n : ℝ)))) ^
            (upperThreshold n).choose 3 := by
        exact pow_le_pow_left₀ hbase0 (Real.one_sub_le_exp_neg _) _
      _ = Real.exp (-((upperThreshold n).choose 3 : ℕ) /
          colorCount n) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
  have hcorr : 2 * overlapCharge n *
      (6 * n * (upperThreshold n).choose 3 : ℕ) =
      ((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ) := by
    simp only [overlapCharge, colorCount]
    push_cast
    field_simp
    ring
  have hexponent := exponential_exponent_le hn
  simp only [holeCharge, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_holeIndex]
  rw [hcorr]
  calc
    (n.choose (upperThreshold n) : ℝ) *
        (2 * holeProbability n *
          Real.exp (((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ))) ≤
      2 * Real.exp ((upperThreshold n : ℝ) * Real.log n -
        ((upperThreshold n).choose 3 : ℕ) / (192 * n : ℝ)) := by
          have hnonneg : 0 ≤ holeProbability n := by
            unfold holeProbability
            positivity
          calc
            _ ≤ (n : ℝ) ^ upperThreshold n *
                (2 * holeProbability n * Real.exp
                  (((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ))) := by
              gcongr
            _ ≤ (n : ℝ) ^ upperThreshold n *
                (2 * Real.exp (-((upperThreshold n).choose 3 : ℕ) /
                    colorCount n) * Real.exp
                  (((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ))) := by
              gcongr
            _ = _ := by
              rw [hpowexp]
              calc
                Real.exp ((upperThreshold n : ℝ) * Real.log n) *
                    (2 * Real.exp (-((upperThreshold n).choose 3 : ℕ) /
                      colorCount n) * Real.exp
                      (((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ))) =
                    2 * (Real.exp ((upperThreshold n : ℝ) * Real.log n) *
                      Real.exp (-((upperThreshold n).choose 3 : ℕ) /
                        colorCount n)) * Real.exp
                      (((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ)) := by ring
                _ = 2 * Real.exp
                      ((upperThreshold n : ℝ) * Real.log n +
                        (-((upperThreshold n).choose 3 : ℕ) / colorCount n)) *
                      Real.exp (((upperThreshold n).choose 3 : ℕ) /
                        (576 * n : ℝ)) := by rw [Real.exp_add]
                _ = 2 * Real.exp
                    (((upperThreshold n : ℝ) * Real.log n +
                      (-((upperThreshold n).choose 3 : ℕ) / colorCount n)) +
                      ((upperThreshold n).choose 3 : ℕ) / (576 * n : ℝ)) := by
                    symm
                    rw [Real.exp_add]
                    ring
                _ = 2 * Real.exp ((upperThreshold n : ℝ) * Real.log n -
                    ((upperThreshold n).choose 3 : ℕ) / (192 * n : ℝ)) := by
                    congr 2
                    simp only [colorCount]
                    push_cast
                    field_simp
                    ring
    _ ≤ 2 * Real.exp (-3) := by gcongr
    _ ≤ 1 / 4 := two_mul_exp_neg_three_le_quarter

lemma holeCharge_nonneg {n : ℕ} (S : HoleIndex n (upperThreshold n)) :
    0 ≤ holeCharge n S := by
  unfold holeCharge holeProbability
  positivity

/-- The fully quantified upper construction at the explicit threshold. -/
theorem exists_upper_system (n : ℕ) (hn : 3 ≤ n) :
    ∃ H : Finset (Finset (Fin n)),
      (∀ e ∈ H, e.card = 3) ∧
      (∀ ⦃e⦄, e ∈ H → ∀ ⦃f⦄, f ∈ H → e ≠ f → (e ∩ f).card ≤ 1) ∧
      (∀ S : Finset (Fin n), S.card = upperThreshold n →
        ∃ e ∈ H, e ⊆ S) := by
  have hn0 : 0 < n := by omega
  have hK : 0 < colorCount n := by simp [colorCount, hn0]
  let : NeZero (colorCount n) := ⟨hK.ne'⟩
  let selected : Fin (colorCount n) := ⟨0, hK⟩
  have htotal := total_hole_charge_le hn
  have hxB1 : ∀ S : HoleIndex n (upperThreshold n), holeCharge n S < 1 := by
    intro S
    have hsingle : holeCharge n S ≤
        ∑ T : HoleIndex n (upperThreshold n), holeCharge n T :=
      Finset.single_le_sum (fun T _ ↦ holeCharge_nonneg T) (Finset.mem_univ S)
    linarith
  have hcriterion := twoCharge_criterion
    (n := n) (t := upperThreshold n) (K := colorCount n)
    (overlapCharge n) (holeCharge n)
    rfl (overlapCharge_nonneg n) ((overlapCharge_le_half hn0).trans (by norm_num))
    (fun S ↦ holeCharge_nonneg S) (fun S ↦ (hxB1 S).le)
    htotal (overlap_loss_le hn0) (fun S ↦ by
      simpa [holeProbability, badProbability] using hole_criterion hn0 S)
  exact exists_linear_hitting_system_of_charges selected
    (twoCharge (overlapCharge n) (holeCharge n))
    (fun i ↦ by cases i <;> simp [twoCharge, overlapCharge_nonneg, holeCharge_nonneg])
    (fun i ↦ by
      cases i with
      | inl _ =>
          simp [twoCharge]
          exact (overlapCharge_le_half hn0).trans_lt (by norm_num)
      | inr S => simpa [twoCharge] using hxB1 S)
    hcriterion

end Upper
end Erdos1024
