import ErdosProblems.Erdos88.BinomialLower
import ErdosProblems.Erdos88.QuadraticLemma82
import ErdosProblems.Erdos88.RLCD
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Hypergeometric anticoncentration for the quadratic argument

This file develops the finite hypergeometric estimates used in KSSS
Lemmas 8.4 and 8.3.  We work first with the unnormalised weights: choosing
`ell` points from two classes of size `m`, the weight of intersection size
`j` with the first class is

`choose m j * choose m (ell - j)`.
-/

namespace Erdos88
namespace QuadraticCancellation

open scoped BigOperators
open Finset Finset.Nat

/-- The unnormalised mass function of `Hyp(2m,m,ell)`. -/
def hypergeomWeight (m ell j : ℕ) : ℕ :=
  Nat.choose m j * Nat.choose m (ell - j)

/-- Vandermonde normalization for the symmetric hypergeometric weights. -/
lemma sum_range_hypergeomWeight (m ell : ℕ) :
    ∑ j ∈ Finset.range (ell + 1), hypergeomWeight m ell j =
      Nat.choose (2 * m) ell := by
  rw [show 2 * m = m + m by omega, Nat.add_choose_eq,
    sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

/-- The symmetric hypergeometric weights are invariant under `j ↦ ell-j`. -/
lemma hypergeomWeight_symm (m ell j : ℕ) (hj : j ≤ ell) :
    hypergeomWeight m ell (ell - j) = hypergeomWeight m ell j := by
  simp only [hypergeomWeight, Nat.sub_sub_self hj, mul_comm]

/-- Exact adjacent-weight recurrence.  Its two linear factors make the
unimodality around `ell/2` transparent. -/
lemma hypergeomWeight_succ_recurrence (m ell j : ℕ) (hj : j < ell) :
    hypergeomWeight m ell (j + 1) * (j + 1) * (m - (ell - (j + 1))) =
      hypergeomWeight m ell j * (m - j) * (ell - j) := by
  have hell : ell - j = (ell - (j + 1)) + 1 := by omega
  have hleft := Nat.choose_succ_right_eq m j
  have hright := Nat.choose_succ_right_eq m (ell - (j + 1))
  simp only [hypergeomWeight]
  calc
    (m.choose (j + 1) * m.choose (ell - (j + 1))) * (j + 1) *
        (m - (ell - (j + 1))) =
      (m.choose (j + 1) * (j + 1)) *
        (m.choose (ell - (j + 1)) * (m - (ell - (j + 1)))) := by ring
    _ = (m.choose j * (m - j)) *
        (m.choose (ell - (j + 1) + 1) *
          (ell - (j + 1) + 1)) := by rw [hleft, hright]
    _ = (m.choose j * m.choose (ell - j)) * (m - j) * (ell - j) := by
      rw [← hell]
      ring

/-- Polynomial comparison of the two factors in the adjacent recurrence. -/
lemma hypergeom_step_factor_le (m ell j : ℕ)
    (hell : ell ≤ 2 * m) (hj : 2 * j + 1 ≤ ell)
    (hsupport : ell ≤ m + j + 1) :
    (j + 1) * (m - (ell - (j + 1))) ≤ (m - j) * (ell - j) := by
  rw [mul_comm (m - j)]
  exact Nat.mul_le_mul (by omega) (by omega)

/-- The weights increase on the left half of their support. -/
lemma hypergeomWeight_le_succ_of_left (m ell j : ℕ)
    (hell : ell ≤ 2 * m) (hj : 2 * j + 1 ≤ ell) :
    hypergeomWeight m ell j ≤ hypergeomWeight m ell (j + 1) := by
  have hjell : j < ell := by omega
  by_cases hsupport : ell ≤ m + j
  · have hfactor := hypergeom_step_factor_le m ell j hell hj (by omega)
    have hpos : 0 < (j + 1) * (m - (ell - (j + 1))) := by
      apply Nat.mul_pos
      · omega
      · omega
    apply Nat.le_of_mul_le_mul_right _ hpos
    calc
      hypergeomWeight m ell j *
          ((j + 1) * (m - (ell - (j + 1)))) ≤
        hypergeomWeight m ell j * ((m - j) * (ell - j)) :=
          Nat.mul_le_mul_left _ hfactor
      _ = hypergeomWeight m ell (j + 1) *
          ((j + 1) * (m - (ell - (j + 1)))) := by
            simpa only [mul_assoc] using
              (hypergeomWeight_succ_recurrence m ell j hjell).symm
  · have hzero : Nat.choose m (ell - j) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [hypergeomWeight, hzero]

/-- Monotonicity of the weights up to the central index. -/
lemma hypergeomWeight_mono_left (m ell a b : ℕ)
    (hell : ell ≤ 2 * m) (hab : a ≤ b) (hb : b ≤ ell / 2) :
    hypergeomWeight m ell a ≤ hypergeomWeight m ell b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      exact (ih (by omega)).trans
        (hypergeomWeight_le_succ_of_left m ell b hell (by omega))

/-- The central index `ell/2` maximizes the symmetric hypergeometric mass. -/
lemma hypergeomWeight_le_middle (m ell j : ℕ)
    (hell : ell ≤ 2 * m) (hj : j ≤ ell) :
    hypergeomWeight m ell j ≤ hypergeomWeight m ell (ell / 2) := by
  by_cases hleft : j ≤ ell / 2
  · exact hypergeomWeight_mono_left m ell j (ell / 2) hell hleft le_rfl
  · rw [← hypergeomWeight_symm m ell j hj]
    apply hypergeomWeight_mono_left m ell (ell - j) (ell / 2) hell
    · omega
    · exact le_rfl

/-- Exact size of the gap between the two factors in the adjacent recurrence. -/
lemma hypergeom_step_factor_gap (m ell j : ℕ)
    (hell : ell ≤ 2 * m) (hj : 2 * j + 1 ≤ ell)
    (hsupport : ell ≤ m + j + 1) :
    (j + 1) * (m - (ell - (j + 1))) +
        (m + 1) * (ell - (2 * j + 1)) =
      (m - j) * (ell - j) := by
  have hjm : j ≤ m := by omega
  have htail : ell - (j + 1) ≤ m := by omega
  have h1 : m - (ell - (j + 1)) + (ell - (j + 1)) = m := by omega
  have h2 : m - j + j = m := by omega
  have h3 : ell - j + j = ell := by omega
  have h4 : ell - (2 * j + 1) + (2 * j + 1) = ell := by omega
  have h5 : ell - (j + 1) + (j + 1) = ell := by omega
  nlinarith

/-- A quantitative one-step lower ratio on the increasing half of the
hypergeometric mass function.  The parameters `s` and `G` are respectively
a lower bound for the two denominator factors and an upper bound for their
gap. -/
lemma hypergeomWeight_succ_ratio_lower
    (m ell j s G : ℕ)
    (hell : ell ≤ 2 * m) (hj : 2 * j + 1 ≤ ell)
    (hsupport : ell ≤ m + j + 1)
    (hs : 1 ≤ s) (hsleft : s ≤ m - j) (hsright : s ≤ ell - j)
    (hG : (m + 1) * (ell - (2 * j + 1)) ≤ G) :
    (1 - (G : ℝ) / (s : ℝ) ^ 2) *
        (hypergeomWeight m ell (j + 1) : ℝ) ≤
      hypergeomWeight m ell j := by
  let A : ℕ := (j + 1) * (m - (ell - (j + 1)))
  let B : ℕ := (m - j) * (ell - j)
  let E : ℕ := (m + 1) * (ell - (2 * j + 1))
  have hgap : A + E = B := by
    exact hypergeom_step_factor_gap m ell j hell hj hsupport
  have hB : s ^ 2 ≤ B := by
    dsimp only [B]
    simpa only [pow_two] using Nat.mul_le_mul hsleft hsright
  have hspos : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
  have hBpos : (0 : ℝ) < (B : ℝ) :=
    lt_of_lt_of_le hspos (by exact_mod_cast hB)
  have hfrac : (E : ℝ) / B ≤ (G : ℝ) / (s : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hBpos hspos]
    have hEG : E ≤ G := by exact hG
    have hfirst : (E : ℝ) * (s : ℝ) ^ 2 ≤
        (G : ℝ) * (s : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hEG) (sq_nonneg _)
    have hsecond : (G : ℝ) * (s : ℝ) ^ 2 ≤ (G : ℝ) * B := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hB) (Nat.cast_nonneg _)
    exact hfirst.trans hsecond
  have hrecNat := hypergeomWeight_succ_recurrence m ell j (by omega)
  have hrec :
      (hypergeomWeight m ell (j + 1) : ℝ) * A =
        (hypergeomWeight m ell j : ℝ) * B := by
    simpa only [A, B, Nat.cast_mul, mul_assoc] using
      congrArg (fun z : ℕ ↦ (z : ℝ)) hrecNat
  have hgapReal : (A : ℝ) + E = B := by exact_mod_cast hgap
  calc
    (1 - (G : ℝ) / (s : ℝ) ^ 2) *
        (hypergeomWeight m ell (j + 1) : ℝ) ≤
      (1 - (E : ℝ) / B) *
        (hypergeomWeight m ell (j + 1) : ℝ) := by
          gcongr
    _ = hypergeomWeight m ell j := by
      field_simp
      nlinarith

/-- Iterating the one-step ratio through a left-central window. -/
lemma hypergeomWeight_middle_mul_pow_le
    (m ell D s d : ℕ)
    (hell : ell ≤ 2 * m) (hs : 1 ≤ s)
    (hleftMargin : D + s ≤ ell / 2)
    (hrightMargin : D + s ≤ m - (ell - ell / 2))
    (hbudget : 2 * (m + 1) * D ≤ s ^ 2)
    (hd : d ≤ D) :
    (hypergeomWeight m ell (ell / 2) : ℝ) *
        (1 - ((2 * (m + 1) * D : ℕ) : ℝ) / (s : ℝ) ^ 2) ^ d ≤
      hypergeomWeight m ell (ell / 2 - d) := by
  let c := ell / 2
  let G := 2 * (m + 1) * D
  let b : ℝ := 1 - (G : ℝ) / (s : ℝ) ^ 2
  have hspos : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
  have hGle : G ≤ s ^ 2 := by exact hbudget
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    rw [sub_nonneg, div_le_one hspos]
    exact_mod_cast hGle
  induction d with
  | zero => simp [c, b]
  | succ d ih =>
      have hdD : d < D := by omega
      have hdle : d ≤ D := by omega
      have hdc : d + 1 ≤ c := by
        dsimp only [c]
        omega
      let j := c - (d + 1)
      have hjleft : 2 * j + 1 ≤ ell := by
        dsimp only [j, c]
        omega
      have hjsupport : ell ≤ m + j + 1 := by
        dsimp only [j, c]
        omega
      have hsjleft : s ≤ m - j := by
        dsimp only [j, c]
        omega
      have hsjright : s ≤ ell - j := by
        dsimp only [j, c]
        omega
      have hjgap : (m + 1) * (ell - (2 * j + 1)) ≤ G := by
        have hg : ell - (2 * j + 1) ≤ 2 * D := by
          dsimp only [j, c]
          omega
        dsimp only [G]
        calc
          (m + 1) * (ell - (2 * j + 1)) ≤ (m + 1) * (2 * D) :=
            Nat.mul_le_mul_left _ hg
          _ = 2 * (m + 1) * D := by ring
      have hstep := hypergeomWeight_succ_ratio_lower
        m ell j s G hell hjleft hjsupport hs hsjleft hsjright hjgap
      have hjnext : j + 1 = c - d := by
        dsimp only [j]
        omega
      rw [hjnext] at hstep
      have hih := ih hdle
      change (hypergeomWeight m ell c : ℝ) * b ^ (d + 1) ≤
        hypergeomWeight m ell (c - (d + 1))
      calc
        (hypergeomWeight m ell c : ℝ) * b ^ (d + 1) =
            b * ((hypergeomWeight m ell c : ℝ) * b ^ d) := by
              rw [pow_succ]
              ring
        _ ≤ b * (hypergeomWeight m ell (c - d) : ℝ) :=
          mul_le_mul_of_nonneg_left hih hb0
        _ ≤ hypergeomWeight m ell (c - (d + 1)) := by
          simpa only [b, G, c] using hstep

/-- Every weight in a sufficiently short central window is at least half of
the modal weight.  The quadratic budget is arranged for the later choice
`D ≍ √m`. -/
lemma hypergeomWeight_middle_div_two_le_near
    (m ell D s d : ℕ)
    (hell : ell ≤ 2 * m) (hD : 1 ≤ D) (hs : 1 ≤ s)
    (hleftMargin : D + s ≤ ell / 2)
    (hrightMargin : D + s ≤ m - (ell - ell / 2))
    (hbudget : 4 * (m + 1) * D ^ 2 ≤ s ^ 2)
    (hd : d ≤ D) :
    (hypergeomWeight m ell (ell / 2) : ℝ) / 2 ≤
      hypergeomWeight m ell (ell / 2 - d) := by
  let G : ℕ := 2 * (m + 1) * D
  let x : ℝ := (G : ℝ) / (s : ℝ) ^ 2
  let b : ℝ := 1 - x
  have hspos : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
  have hweak : 2 * (m + 1) * D ≤ s ^ 2 := by
    have : 2 * (m + 1) * D ≤ 4 * (m + 1) * D ^ 2 := by
      calc
        2 * (m + 1) * D = (2 * (m + 1) * D) * 1 := by ring
        _ ≤ (2 * (m + 1) * D) * (2 * D) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = 4 * (m + 1) * D ^ 2 := by ring
    exact this.trans hbudget
  have hx0 : 0 ≤ x := by
    dsimp only [x, G]
    positivity
  have hDx : (D : ℝ) * x ≤ 1 / 2 := by
    dsimp only [x]
    rw [← mul_div_assoc]
    rw [div_le_iff₀ hspos]
    have hreal : ((4 * (m + 1) * D ^ 2 : ℕ) : ℝ) ≤ (s ^ 2 : ℕ) := by
      exact_mod_cast hbudget
    dsimp only [G]
    push_cast at hreal ⊢
    calc
      (D : ℝ) * (2 * ((m : ℝ) + 1) * D) =
          (1 / 2 : ℝ) * (4 * ((m : ℝ) + 1) * D ^ 2) := by ring
      _ ≤ (1 / 2 : ℝ) * (s : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hreal (by norm_num)
  have hb0 : 0 ≤ b := by
    dsimp only [b, x, G]
    rw [sub_nonneg, div_le_one hspos]
    exact_mod_cast hweak
  have hbern := one_add_mul_sub_le_pow (a := b) (by linarith : -1 ≤ b) d
  have hdreal : (d : ℝ) ≤ D := by exact_mod_cast hd
  have hdx : (d : ℝ) * x ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hdreal hx0).trans hDx
  have hhalf : (1 / 2 : ℝ) ≤ b ^ d := by
    dsimp only [b] at hbern ⊢
    nlinarith
  have hiter := hypergeomWeight_middle_mul_pow_le
    m ell D s d hell hs hleftMargin hrightMargin hweak hd
  change (hypergeomWeight m ell (ell / 2) : ℝ) / 2 ≤
    hypergeomWeight m ell (ell / 2 - d)
  calc
    (hypergeomWeight m ell (ell / 2) : ℝ) / 2 =
        (hypergeomWeight m ell (ell / 2) : ℝ) * (1 / 2) := by ring
    _ ≤ (hypergeomWeight m ell (ell / 2) : ℝ) * b ^ d :=
      mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg _)
    _ ≤ hypergeomWeight m ell (ell / 2 - d) := by
      simpa only [b, x, G] using hiter

/-- A central plateau of length `D+1` forces a square-root-scale upper bound
for the normalized modal mass. -/
lemma hypergeomWeight_middle_div_choose_le_two_div
    (m ell D s : ℕ)
    (hell : ell ≤ 2 * m) (hD : 1 ≤ D) (hs : 1 ≤ s)
    (hleftMargin : D + s ≤ ell / 2)
    (hrightMargin : D + s ≤ m - (ell - ell / 2))
    (hbudget : 4 * (m + 1) * D ^ 2 ≤ s ^ 2) :
    (hypergeomWeight m ell (ell / 2) : ℝ) /
        Nat.choose (2 * m) ell ≤ 2 / (D + 1 : ℕ) := by
  let c := ell / 2
  let W : Finset ℕ := (Finset.range (D + 1)).image fun d ↦ c - D + d
  have hDc : D ≤ c := by
    dsimp only [c]
    omega
  have hinj : Function.Injective (fun d : ℕ ↦ c - D + d) := by
    intro a b hab
    exact Nat.add_left_cancel hab
  have hWcard : W.card = D + 1 := by
    dsimp only [W]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hWsub : W ⊆ Finset.range (ell + 1) := by
    intro j hj
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hj
    rw [Finset.mem_range] at hd ⊢
    dsimp only [c]
    omega
  have hpoint : ∀ j ∈ W,
      (hypergeomWeight m ell c : ℝ) / 2 ≤ hypergeomWeight m ell j := by
    intro j hj
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hj
    rw [Finset.mem_range] at hd
    have hnear := hypergeomWeight_middle_div_two_le_near
      m ell D s (D - d) hell hD hs hleftMargin hrightMargin hbudget (by omega)
    have hdD : d ≤ D := by omega
    have hidx : ell / 2 - (D - d) = ell / 2 - D + d := by omega
    simpa only [c, hidx] using hnear
  have hsumLower :
      ((D + 1 : ℕ) : ℝ) *
          ((hypergeomWeight m ell c : ℝ) / 2) ≤
        ∑ j ∈ W, (hypergeomWeight m ell j : ℝ) := by
    calc
      ((D + 1 : ℕ) : ℝ) *
          ((hypergeomWeight m ell c : ℝ) / 2) =
        ∑ j ∈ W, ((hypergeomWeight m ell c : ℝ) / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, hWcard]
      _ ≤ ∑ j ∈ W, (hypergeomWeight m ell j : ℝ) := by
        exact Finset.sum_le_sum fun j hj ↦ hpoint j hj
  have hsumUpper :
      (∑ j ∈ W, (hypergeomWeight m ell j : ℝ)) ≤
        Nat.choose (2 * m) ell := by
    calc
      (∑ j ∈ W, (hypergeomWeight m ell j : ℝ)) ≤
          ∑ j ∈ Finset.range (ell + 1),
            (hypergeomWeight m ell j : ℝ) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hWsub
              intro j _hj _hjW
              positivity
      _ = Nat.choose (2 * m) ell := by
        exact_mod_cast sum_range_hypergeomWeight m ell
  have htotalPos : (0 : ℝ) < Nat.choose (2 * m) ell := by
    exact_mod_cast Nat.choose_pos hell
  have hDpos : (0 : ℝ) < (D + 1 : ℕ) := by positivity
  rw [div_le_div_iff₀ htotalPos hDpos]
  have hmain := hsumLower.trans hsumUpper
  dsimp only [c] at hmain ⊢
  nlinarith

/-- Every hypergeometric point mass obeys the same normalized bound as the
mode. -/
lemma hypergeomWeight_div_choose_le_two_div
    (m ell D s j : ℕ)
    (hell : ell ≤ 2 * m) (hj : j ≤ ell)
    (hD : 1 ≤ D) (hs : 1 ≤ s)
    (hleftMargin : D + s ≤ ell / 2)
    (hrightMargin : D + s ≤ m - (ell - ell / 2))
    (hbudget : 4 * (m + 1) * D ^ 2 ≤ s ^ 2) :
    (hypergeomWeight m ell j : ℝ) / Nat.choose (2 * m) ell ≤
      2 / (D + 1 : ℕ) := by
  have hmax := hypergeomWeight_le_middle m ell j hell hj
  have htotalPos : (0 : ℝ) < Nat.choose (2 * m) ell := by
    exact_mod_cast Nat.choose_pos hell
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hmax) htotalPos.le).trans
    (hypergeomWeight_middle_div_choose_le_two_div
      m ell D s hell hD hs hleftMargin hrightMargin hbudget)

/-- Explicit fixed-density specialization of the modal bound.  The two
size hypotheses are harmless eventual conditions; they will be absorbed into
the `eta`-dependent constant in KSSS Lemma 8.4. -/
lemma hypergeomWeight_div_choose_le_of_density
    (eta : ℝ) (m ell j : ℕ)
    (heta : 0 < eta) (hm : 1 ≤ m)
    (hetaM : 8 ≤ eta * m)
    (hetaSqrt : 64 ≤ eta * Real.sqrt m)
    (hellower : eta * (2 * m : ℕ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * (2 * m : ℕ))
    (hj : j ≤ ell) :
    (hypergeomWeight m ell j : ℝ) / Nat.choose (2 * m) ell ≤
      128 / (eta * Real.sqrt m) := by
  let D : ℕ := Nat.floor (eta * Real.sqrt m / 64)
  let s : ℕ := Nat.floor (eta * m / 4)
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsqrt0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hsqrtPos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hsqrtSq : Real.sqrt (m : ℝ) ^ 2 = m := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrtLe : Real.sqrt (m : ℝ) ≤ m := by
    exact Real.sqrt_le_self_iff.mpr (Or.inr hmreal)
  have hDarg0 : 0 ≤ eta * Real.sqrt m / 64 := by positivity
  have hsarg0 : 0 ≤ eta * (m : ℝ) / 4 := by positivity
  have hDup : (D : ℝ) ≤ eta * Real.sqrt m / 64 := by
    dsimp only [D]
    exact Nat.floor_le hDarg0
  have hDlower : eta * Real.sqrt m / 64 < (D : ℝ) + 1 := by
    dsimp only [D]
    exact Nat.lt_floor_add_one _
  have hsUp : (s : ℝ) ≤ eta * m / 4 := by
    dsimp only [s]
    exact Nat.floor_le hsarg0
  have hsFloor : eta * m / 4 < (s : ℝ) + 1 := by
    dsimp only [s]
    exact Nat.lt_floor_add_one _
  have hsLow : eta * m / 8 ≤ (s : ℝ) := by
    nlinarith
  have hD : 1 ≤ D := by
    apply Nat.le_floor
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 64)]
    simpa using hetaSqrt
  have hs : 1 ≤ s := by
    have : (1 : ℝ) ≤ s := by nlinarith
    exact_mod_cast this
  have hell : ell ≤ 2 * m := by
    have : (ell : ℝ) ≤ 2 * m := by
      calc
        (ell : ℝ) ≤ (1 - eta) * (2 * m : ℕ) := hellupper
        _ ≤ 1 * (2 * m : ℕ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ = 2 * m := by push_cast; ring
    exact_mod_cast this
  have hDS : ((D + s : ℕ) : ℝ) ≤ eta * m / 2 := by
    push_cast
    have hDlinear : (D : ℝ) ≤ eta * m / 64 := by
      calc
        (D : ℝ) ≤ eta * Real.sqrt m / 64 := hDup
        _ ≤ eta * m / 64 := by gcongr
    nlinarith
  have hleftMargin : D + s ≤ ell / 2 := by
    have hellSplit : ell ≤ 2 * (ell / 2) + 1 := by omega
    have hellSplitR : (ell : ℝ) ≤ 2 * (ell / 2 : ℕ) + 1 := by
      exact_mod_cast hellSplit
    have hreal : ((D + s : ℕ) : ℝ) ≤ (ell / 2 : ℕ) := by
      push_cast at hellower
      nlinarith
    exact_mod_cast hreal
  have hrightMargin : D + s ≤ m - (ell - ell / 2) := by
    have huSplit : 2 * (ell - ell / 2) ≤ ell + 1 := by omega
    have huSplitR : ((2 * (ell - ell / 2) : ℕ) : ℝ) ≤ ell + 1 := by
      exact_mod_cast huSplit
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sub (Nat.div_le_self ell 2)] at huSplitR
    have huReal : ((ell - ell / 2 : ℕ) : ℝ) ≤
        (1 - eta) * m + 1 / 2 := by
      rw [Nat.cast_sub (Nat.div_le_self ell 2)]
      push_cast at hellupper
      nlinarith
    have hsum : D + s + (ell - ell / 2) ≤ m := by
      have hreal : (((D + s + (ell - ell / 2) : ℕ) : ℝ)) ≤ m := by
        push_cast
        nlinarith
      exact_mod_cast hreal
    omega
  have hDsq : (D : ℝ) ^ 2 ≤ (eta * Real.sqrt m / 64) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg D) (by positivity)).2 hDup
  have hsSq : (eta * m / 8) ^ 2 ≤ (s : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg s)).2 hsLow
  have hbudgetR :
      ((4 * (m + 1) * D ^ 2 : ℕ) : ℝ) ≤ (s ^ 2 : ℕ) := by
    push_cast
    have hDsq' : (D : ℝ) ^ 2 ≤ eta ^ 2 * m / 4096 := by
      calc
        (D : ℝ) ^ 2 ≤ (eta * Real.sqrt m / 64) ^ 2 := hDsq
        _ = eta ^ 2 * m / 4096 := by rw [div_pow, mul_pow, hsqrtSq]; norm_num
    have hmplus : (4 : ℝ) * (m + 1) ≤ 8 * m := by nlinarith
    have hleft : (4 : ℝ) * (m + 1) * D ^ 2 ≤
        eta ^ 2 * m ^ 2 / 512 := by
      calc
        (4 : ℝ) * (m + 1) * D ^ 2 ≤
            (4 : ℝ) * (m + 1) * (eta ^ 2 * m / 4096) :=
          mul_le_mul_of_nonneg_left hDsq' (by positivity)
        _ ≤ (8 * m) * (eta ^ 2 * m / 4096) :=
          mul_le_mul_of_nonneg_right hmplus (by positivity)
        _ = eta ^ 2 * m ^ 2 / 512 := by ring
    have hright : eta ^ 2 * m ^ 2 / 64 ≤ (s : ℝ) ^ 2 := by
      calc
        eta ^ 2 * m ^ 2 / 64 = (eta * m / 8) ^ 2 := by ring
        _ ≤ (s : ℝ) ^ 2 := hsSq
    exact hleft.trans (by
      apply le_trans (show eta ^ 2 * m ^ 2 / 512 ≤
        eta ^ 2 * m ^ 2 / 64 by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num))
      exact hright)
  have hbudget : 4 * (m + 1) * D ^ 2 ≤ s ^ 2 := by
    exact_mod_cast hbudgetR
  have hlocal := hypergeomWeight_div_choose_le_two_div
    m ell D s j hell hj hD hs hleftMargin hrightMargin hbudget
  have hden : 0 < eta * Real.sqrt m := mul_pos heta hsqrtPos
  have hDden : (0 : ℝ) < (D + 1 : ℕ) := by positivity
  calc
    (hypergeomWeight m ell j : ℝ) / Nat.choose (2 * m) ell ≤
        2 / (D + 1 : ℕ) := hlocal
    _ ≤ 128 / (eta * Real.sqrt m) := by
      have hscaled : eta * Real.sqrt m < 64 * ((D : ℝ) + 1) := by
        have h := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 64)).mp hDlower
        nlinarith
      rw [div_le_div_iff₀ hDden hden]
      push_cast
      nlinarith

section UnimodalBlockSampling

/-- On one side of a mode, a nonnegative antitone sequence cannot put much
mass on a set occupying at most `r` points in every interval of length `L`.
This is the deterministic summation principle behind the periodic residue
bound in KSSS Lemma 8.4. -/
lemma sum_right_of_antitone_of_block_card
    (N c L r : ℕ) (f : ℕ → ℝ) (E : Finset ℕ)
    (hL : 1 ≤ L) (hE : E ⊆ Finset.range N)
    (hf0 : ∀ j, 0 ≤ f j)
    (hanti : ∀ ⦃i j⦄, c ≤ i → i ≤ j → j < N → f j ≤ f i)
    (hblock : ∀ a,
      (E.filter fun j ↦ a ≤ j ∧ j < a + L).card ≤ r) :
    ∑ j ∈ E.filter (c ≤ ·), f j ≤
      (r : ℝ) * f c + (r : ℝ) / L * ∑ j ∈ Finset.range N, f j := by
  classical
  let ER : Finset ℕ := E.filter (c ≤ ·)
  let R : Finset ℕ := (Finset.range N).filter (c ≤ ·)
  let g : ℕ → ℕ := fun j ↦ (j - c) / L
  let A : ℕ → Finset ℕ := fun q ↦ ER.filter fun j ↦ g j = q
  let B : ℕ → Finset ℕ := fun q ↦ R.filter fun j ↦ g j = q
  have hmapsA : ∀ j ∈ ER, g j ∈ Finset.range (N + 1) := by
    intro j hj
    rw [Finset.mem_range]
    have hjE : j ∈ E := (Finset.mem_filter.mp hj).1
    have hjN : j < N := Finset.mem_range.mp (hE hjE)
    dsimp only [g]
    have hdiv : (j - c) / L ≤ j - c := Nat.div_le_self _ _
    omega
  have hmapsB : ∀ j ∈ R, g j ∈ Finset.range N := by
    intro j hj
    rw [Finset.mem_range]
    have hjN : j < N := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    dsimp only [g]
    have hdiv : (j - c) / L ≤ j - c := Nat.div_le_self _ _
    omega
  have hsumA :
      ∑ j ∈ ER, f j = ∑ q ∈ Finset.range (N + 1), ∑ j ∈ A q, f j := by
    simpa only [A] using
      (Finset.sum_fiberwise_of_maps_to hmapsA f).symm
  have hsumB :
      ∑ j ∈ R, f j = ∑ q ∈ Finset.range N, ∑ j ∈ B q, f j := by
    simpa only [B] using
      (Finset.sum_fiberwise_of_maps_to hmapsB f).symm
  have hA0sub : A 0 ⊆ E.filter fun j ↦ c ≤ j ∧ j < c + L := by
    intro j hj
    have hjA := Finset.mem_filter.mp hj
    have hjER := Finset.mem_filter.mp hjA.1
    rw [Finset.mem_filter]
    refine ⟨hjER.1, hjER.2, ?_⟩
    dsimp only [g] at hjA
    rw [Nat.div_eq_zero_iff] at hjA
    have hdiff : j - c < L := hjA.2.resolve_left (by omega)
    omega
  have hA0card : (A 0).card ≤ r :=
    (Finset.card_le_card hA0sub).trans (hblock c)
  have hA0 : ∑ j ∈ A 0, f j ≤ (r : ℝ) * f c := by
    calc
      ∑ j ∈ A 0, f j ≤ ∑ _j ∈ A 0, f c := by
        apply Finset.sum_le_sum
        intro j hj
        have hjER := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
        have hjN := Finset.mem_range.mp (hE
          (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1)
        exact hanti (i := c) (j := j) le_rfl hjER hjN
      _ = ((A 0).card : ℝ) * f c := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (r : ℝ) * f c :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hA0card) (hf0 c)
  have hAsucc : ∀ q < N,
      ∑ j ∈ A (q + 1), f j ≤
        (r : ℝ) / L * ∑ i ∈ B q, f i := by
    intro q hqN
    by_cases hAempty : A (q + 1) = ∅
    · rw [hAempty]
      simp only [Finset.sum_empty, zero_le]
      exact mul_nonneg
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun i _hi ↦ hf0 i)
    · obtain ⟨j, hjA⟩ := Finset.nonempty_iff_ne_empty.mpr hAempty
      have hjAf := Finset.mem_filter.mp hjA
      have hjER := Finset.mem_filter.mp hjAf.1
      have hjE : j ∈ E := hjER.1
      have hcj : c ≤ j := hjER.2
      have hjN : j < N := Finset.mem_range.mp (hE hjE)
      have hgq : g j = q + 1 := hjAf.2
      change (j - c) / L = q + 1 at hgq
      have hLpos : 0 < L := by omega
      have hstartJ : c + (q + 1) * L ≤ j := by
        have hqle : q + 1 ≤ (j - c) / L := by omega
        have : (q + 1) * L ≤ j - c :=
          (Nat.le_div_iff_mul_le hLpos).mp hqle
        omega
      have hendN : c + (q + 1) * L < N := hstartJ.trans_lt hjN
      have hBmem : ∀ i,
          i ∈ B q ↔ c + q * L ≤ i ∧ i < c + (q + 1) * L := by
        intro i
        simp only [B, R, Finset.mem_filter, Finset.mem_range, g]
        constructor
        · rintro ⟨⟨hiN, hci⟩, hdiv⟩
          change (i - c) / L = q at hdiv
          have hlo : q * L ≤ i - c := by
            exact (Nat.le_div_iff_mul_le hLpos).mp hdiv.ge
          have hhi : i - c < (q + 1) * L := by
            exact (Nat.div_lt_iff_lt_mul hLpos).mp (by omega)
          omega
        · rintro ⟨hlo, hhi⟩
          have hiN : i < N := hhi.trans hendN
          have hci : c ≤ i := by omega
          refine ⟨⟨hiN, hci⟩, ?_⟩
          apply Nat.le_antisymm
          · have hdiffhi : i - c < (q + 1) * L := by omega
            exact Nat.lt_succ_iff.mp
              ((Nat.div_lt_iff_lt_mul hLpos).mpr hdiffhi)
          · have hdifflo : q * L ≤ i - c := by omega
            exact (Nat.le_div_iff_mul_le hLpos).mpr hdifflo
      have hBcard : (B q).card = L := by
        have hBeq : B q = Finset.Ico (c + q * L) (c + (q + 1) * L) := by
          ext i
          rw [hBmem, Finset.mem_Ico]
        rw [hBeq, Nat.card_Ico]
        simp [Nat.add_mul, Nat.add_sub_add_left]
      have hAcard : (A (q + 1)).card ≤ r := by
        apply (Finset.card_le_card ?_).trans (hblock (c + (q + 1) * L))
        intro i hi
        have hiAf := Finset.mem_filter.mp hi
        have hiER := Finset.mem_filter.mp hiAf.1
        have hdiv := hiAf.2
        change (i - c) / L = q + 1 at hdiv
        rw [Finset.mem_filter]
        refine ⟨hiER.1, ?_⟩
        have hlo : (q + 1) * L ≤ i - c := by
          exact (Nat.le_div_iff_mul_le hLpos).mp hdiv.ge
        have hhi : i - c < (q + 2) * L := by
          exact (Nat.div_lt_iff_lt_mul hLpos).mp (by omega)
        constructor
        · have hstart : (q + 1) * L + c ≤ i :=
            Nat.add_le_of_le_sub hiER.2 hlo
          simpa [Nat.add_comm] using hstart
        · have hend : i < (q + 2) * L + c :=
            (Nat.sub_lt_iff_lt_add hiER.2).mp hhi
          rw [show q + 2 = (q + 1) + 1 by omega, Nat.add_mul, one_mul] at hend
          omega
      have hApoint : ∀ i ∈ A (q + 1), f i ≤ f (c + (q + 1) * L) := by
        intro i hi
        have hiAf := Finset.mem_filter.mp hi
        have hiER := Finset.mem_filter.mp hiAf.1
        have hiN := Finset.mem_range.mp (hE hiER.1)
        have hdiv := hiAf.2
        change (i - c) / L = q + 1 at hdiv
        have hlo : (q + 1) * L ≤ i - c := by
          exact (Nat.le_div_iff_mul_le hLpos).mp hdiv.ge
        exact hanti (i := c + (q + 1) * L) (j := i)
          (by omega) (by omega) hiN
      have hBpoint : ∀ i ∈ B q, f (c + (q + 1) * L) ≤ f i := by
        intro i hi
        have hiBounds := (hBmem i).mp hi
        exact hanti (i := i) (j := c + (q + 1) * L)
          (by omega) hiBounds.2.le hendN
      have hAsum : ∑ i ∈ A (q + 1), f i ≤
          (r : ℝ) * f (c + (q + 1) * L) := by
        calc
          ∑ i ∈ A (q + 1), f i ≤
              ∑ _i ∈ A (q + 1), f (c + (q + 1) * L) :=
            Finset.sum_le_sum hApoint
          _ = ((A (q + 1)).card : ℝ) * f (c + (q + 1) * L) := by
            rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (r : ℝ) * f (c + (q + 1) * L) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hAcard) (hf0 _)
      have hBsum : (L : ℝ) * f (c + (q + 1) * L) ≤
          ∑ i ∈ B q, f i := by
        calc
          (L : ℝ) * f (c + (q + 1) * L) =
              ∑ _i ∈ B q, f (c + (q + 1) * L) := by
            rw [Finset.sum_const, nsmul_eq_mul, hBcard]
          _ ≤ ∑ i ∈ B q, f i := Finset.sum_le_sum hBpoint
      have hLreal : (0 : ℝ) < L := by exact_mod_cast hLpos
      calc
        ∑ i ∈ A (q + 1), f i ≤
            (r : ℝ) * f (c + (q + 1) * L) := hAsum
        _ = (r : ℝ) / L *
            ((L : ℝ) * f (c + (q + 1) * L)) := by field_simp
        _ ≤ (r : ℝ) / L * ∑ i ∈ B q, f i :=
          mul_le_mul_of_nonneg_left hBsum (by positivity)
  calc
    ∑ j ∈ E.filter (c ≤ ·), f j = ∑ j ∈ ER, f j := rfl
    _ = ∑ q ∈ Finset.range (N + 1), ∑ j ∈ A q, f j := hsumA
    _ = (∑ j ∈ A 0, f j) +
        ∑ q ∈ Finset.range N, ∑ j ∈ A (q + 1), f j := by
          rw [Finset.sum_range_succ']
          ac_rfl
    _ ≤ (r : ℝ) * f c +
        ∑ q ∈ Finset.range N,
          ((r : ℝ) / L * ∑ j ∈ B q, f j) := by
            exact add_le_add hA0 (Finset.sum_le_sum fun q hq ↦
              hAsucc q (Finset.mem_range.mp hq))
    _ = (r : ℝ) * f c + (r : ℝ) / L *
        ∑ q ∈ Finset.range N, ∑ j ∈ B q, f j := by
          rw [Finset.mul_sum]
    _ = (r : ℝ) * f c + (r : ℝ) / L *
        ∑ j ∈ R, f j := by rw [← hsumB]
    _ ≤ (r : ℝ) * f c + (r : ℝ) / L *
        ∑ j ∈ Finset.range N, f j := by
          have hRsum : ∑ j ∈ R, f j ≤ ∑ j ∈ Finset.range N, f j := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro j _hj _hjR
            exact hf0 j
          have hcoef : 0 ≤ (r : ℝ) / L :=
            div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          exact add_le_add_right
            (mul_le_mul_of_nonneg_left hRsum hcoef) _

/-- Two points which are both close to integers and are less than one minus
the two errors apart have the same chosen nearest integer. -/
lemma round_eq_of_distToInt_add_lt_one
    {x y delta : ℝ}
    (hx : RLCD.distToInt x ≤ delta)
    (hy : RLCD.distToInt y ≤ delta)
    (hxy : |x - y| + 2 * delta < 1) :
    round x = round y := by
  have hroundDist :
      |((round x : ℤ) : ℝ) - ((round y : ℤ) : ℝ)| ≤
        RLCD.distToInt x + |x - y| + RLCD.distToInt y := by
    rw [RLCD.distToInt, RLCD.distToInt]
    calc
      |((round x : ℤ) : ℝ) - ((round y : ℤ) : ℝ)| =
          |(((round x : ℤ) : ℝ) - x) + (x - y) +
            (y - ((round y : ℤ) : ℝ))| := by congr 1 <;> ring
      _ ≤ |((round x : ℤ) : ℝ) - x| + |x - y| +
          |y - ((round y : ℤ) : ℝ)| := by
            exact (abs_add_le _ _).trans
              (add_le_add_left (abs_add_le _ _) _)
      _ = |x - ((round x : ℤ) : ℝ)| + |x - y| +
          |y - ((round y : ℤ) : ℝ)| := by rw [abs_sub_comm]
  have hlt :
      |((round x : ℤ) : ℝ) - ((round y : ℤ) : ℝ)| < 1 := by
    exact lt_of_le_of_lt hroundDist (by linarith)
  have hintReal : ((|round x - round y| : ℤ) : ℝ) < 1 := by
    simpa only [Int.cast_abs, Int.cast_sub, Int.cast_one] using hlt
  have hint : |round x - round y| < (1 : ℤ) := by exact_mod_cast hintReal
  exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp hint)

/-- Inside an interval shorter than half a period, a residue event occupies
only `O(delta / |tau| + 1)` integer points.  The factor two comes from using
a fixed event point rather than the two extremal points. -/
lemma card_residue_block_le
    (tau alpha delta : ℝ) (a L : ℕ) (E : Finset ℕ)
    (htau : 0 < |tau|) (hdelta : 0 ≤ delta) (hdeltaSmall : delta < 1 / 8)
    (hscale : (L : ℝ) * |tau| ≤ 1 / 2)
    (hres : ∀ j ∈ E, RLCD.distToInt (tau * j - alpha) ≤ delta) :
    (E.filter fun j ↦ a ≤ j ∧ j < a + L).card ≤
      2 * Nat.floor (2 * delta / |tau|) + 1 := by
  classical
  let S := E.filter fun j ↦ a ≤ j ∧ j < a + L
  let R := Nat.floor (2 * delta / |tau|)
  have hratio0 : 0 ≤ 2 * delta / |tau| := by positivity
  by_cases hSempty : S = ∅
  · simp [S, hSempty]
  · obtain ⟨j₀, hj₀S⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
    have hj₀ := Finset.mem_filter.mp hj₀S
    have hj₀res := hres j₀ hj₀.1
    have hsub : S ⊆ Finset.Icc (j₀ - R) (j₀ + R) := by
      intro i hiS
      have hi := Finset.mem_filter.mp hiS
      have hires := hres i hi.1
      have hijdiff : |(i : ℝ) - j₀| < L := by
        rw [abs_lt]
        constructor
        · have : -(L : ℤ) < (i : ℤ) - j₀ := by omega
          exact_mod_cast this
        · have : (i : ℤ) - j₀ < L := by omega
          exact_mod_cast this
      have hphaseHalf :
          |(tau * i - alpha) - (tau * j₀ - alpha)| < 1 / 2 := by
        rw [show (tau * (i : ℝ) - alpha) - (tau * (j₀ : ℝ) - alpha) =
          tau * ((i : ℝ) - j₀) by ring, abs_mul]
        exact (mul_lt_mul_of_pos_left hijdiff htau).trans_le (by
          simpa only [mul_comm] using hscale)
      have hround : round (tau * i - alpha) = round (tau * j₀ - alpha) := by
        apply round_eq_of_distToInt_add_lt_one hires hj₀res
        nlinarith
      have hphase : |tau| * |(i : ℝ) - j₀| ≤ 2 * delta := by
        calc
          |tau| * |(i : ℝ) - j₀| =
              |(tau * i - alpha) - (tau * j₀ - alpha)| := by
                rw [show (tau * (i : ℝ) - alpha) -
                  (tau * (j₀ : ℝ) - alpha) =
                    tau * ((i : ℝ) - j₀) by ring, abs_mul]
          _ = |((tau * i - alpha) - (round (tau * i - alpha) : ℝ)) -
                ((tau * j₀ - alpha) -
                  (round (tau * j₀ - alpha) : ℝ))| := by
                    rw [hround]
                    congr 1 <;> ring
          _ ≤ RLCD.distToInt (tau * i - alpha) +
                RLCD.distToInt (tau * j₀ - alpha) := by
                  rw [RLCD.distToInt, RLCD.distToInt]
                  calc
                    |((tau * i - alpha) - (round (tau * i - alpha) : ℝ)) -
                        ((tau * j₀ - alpha) -
                          (round (tau * j₀ - alpha) : ℝ))| =
                      |((tau * i - alpha) - (round (tau * i - alpha) : ℝ)) +
                        -((tau * j₀ - alpha) -
                          (round (tau * j₀ - alpha) : ℝ))| := by congr 1 <;> ring
                    _ ≤ |(tau * i - alpha) - (round (tau * i - alpha) : ℝ)| +
                        |-((tau * j₀ - alpha) -
                          (round (tau * j₀ - alpha) : ℝ))| := abs_add_le _ _
                    _ = |(tau * i - alpha) - (round (tau * i - alpha) : ℝ)| +
                        |(tau * j₀ - alpha) -
                          (round (tau * j₀ - alpha) : ℝ)| := by rw [abs_neg]
          _ ≤ 2 * delta := by linarith
      have habs : |(i : ℝ) - j₀| ≤ 2 * delta / |tau| := by
        rw [le_div_iff₀ htau]
        simpa only [mul_comm] using hphase
      rw [Finset.mem_Icc]
      by_cases hij : j₀ ≤ i
      · have hdiffReal : ((i - j₀ : ℕ) : ℝ) ≤ 2 * delta / |tau| := by
          have hcast : (j₀ : ℝ) ≤ i := by exact_mod_cast hij
          simpa only [Nat.cast_sub hij, abs_of_nonneg (sub_nonneg.mpr hcast)] using habs
        have hdiff : i - j₀ ≤ R := by
          dsimp only [R]
          exact Nat.le_floor hdiffReal
        exact ⟨by omega, by omega⟩
      · have hij' : i ≤ j₀ := by omega
        have hdiffReal : ((j₀ - i : ℕ) : ℝ) ≤ 2 * delta / |tau| := by
          rw [abs_sub_comm] at habs
          have hcast : (i : ℝ) ≤ j₀ := by exact_mod_cast hij'
          simpa only [Nat.cast_sub hij', abs_of_nonneg (sub_nonneg.mpr hcast)] using habs
        have hdiff : j₀ - i ≤ R := by
          dsimp only [R]
          exact Nat.le_floor hdiffReal
        exact ⟨by omega, by omega⟩
    calc
      S.card ≤ (Finset.Icc (j₀ - R) (j₀ + R)).card := Finset.card_le_card hsub
      _ = j₀ + R + 1 - (j₀ - R) := by rw [Nat.card_Icc]
      _ ≤ 2 * R + 1 := by omega
      _ = 2 * Nat.floor (2 * delta / |tau|) + 1 := rfl

/-- The support indices whose affine phase is within `delta` of an integer. -/
noncomputable def hypergeomResidueSet
    (ell : ℕ) (tau alpha delta : ℝ) : Finset ℕ :=
  (Finset.range (ell + 1)).filter fun j ↦
    RLCD.distToInt (tau * j - alpha) ≤ delta

/-- Exact two-sided block-sampling estimate for the symmetric
hypergeometric law.  This is the finite combinatorial core of KSSS Lemma
8.4; the remaining specialization only chooses `L` and simplifies the
displayed elementary parameters. -/
lemma sum_hypergeomWeight_residue_le_of_block
    (m ell L : ℕ) (tau alpha delta : ℝ)
    (hell : ell ≤ 2 * m) (hL : 1 ≤ L)
    (htau : 0 < |tau|) (hdelta : 0 ≤ delta)
    (hdeltaSmall : delta < 1 / 8)
    (hscale : (L : ℝ) * |tau| ≤ 1 / 2) :
    ∑ j ∈ hypergeomResidueSet ell tau alpha delta,
        (hypergeomWeight m ell j : ℝ) ≤
      2 * ((2 * Nat.floor (2 * delta / |tau|) + 1 : ℕ) *
          (hypergeomWeight m ell (ell / 2) : ℝ) +
        ((2 * Nat.floor (2 * delta / |tau|) + 1 : ℕ) : ℝ) / L *
          Nat.choose (2 * m) ell) := by
  classical
  let c : ℕ := ell / 2
  let N : ℕ := c + 1
  let r : ℕ := 2 * Nat.floor (2 * delta / |tau|) + 1
  let f : ℕ → ℝ := fun d ↦ hypergeomWeight m ell (c - d)
  let alphaL : ℝ := alpha - tau * c
  let alphaR : ℝ := alpha - tau * (ell - c)
  let DL : Finset ℕ := (Finset.range N).filter fun d ↦
    RLCD.distToInt ((-tau) * d - alphaL) ≤ delta
  let DR : Finset ℕ := (Finset.range N).filter fun d ↦
    c < ell - (c - d) ∧ RLCD.distToInt (tau * d - alphaR) ≤ delta
  let E := hypergeomResidueSet ell tau alpha delta
  let EL := E.filter fun j ↦ j ≤ c
  let ER := E.filter fun j ↦ ¬j ≤ c
  have hcEll : c ≤ ell := by dsimp only [c]; omega
  have hf0 : ∀ d, 0 ≤ f d := fun d ↦ by dsimp only [f]; positivity
  have hanti : ∀ {i j : ℕ}, 0 ≤ i → i ≤ j → j < N → f j ≤ f i := by
    intro i j _hi hij hjN
    have hjc : j ≤ c := by dsimp only [N] at hjN; omega
    have hidx : c - j ≤ c - i := by omega
    have hmono := hypergeomWeight_mono_left m ell (c - j) (c - i)
      hell hidx (by dsimp only [c]; omega)
    dsimp only [f]
    exact_mod_cast hmono
  have hDLsub : DL ⊆ Finset.range N := Finset.filter_subset _ _
  have hDRsub : DR ⊆ Finset.range N := Finset.filter_subset _ _
  have hDLblock : ∀ a,
      (DL.filter fun d ↦ a ≤ d ∧ d < a + L).card ≤ r := by
    intro a
    have hres : ∀ d ∈ DL,
        RLCD.distToInt ((-tau) * d - alphaL) ≤ delta := by
      intro d hd
      exact (Finset.mem_filter.mp hd).2
    simpa only [r, abs_neg] using
      (card_residue_block_le (-tau) alphaL delta a L DL
        (by simpa only [abs_neg] using htau) hdelta hdeltaSmall
        (by simpa only [abs_neg] using hscale) hres)
  have hDRblock : ∀ a,
      (DR.filter fun d ↦ a ≤ d ∧ d < a + L).card ≤ r := by
    intro a
    have hres : ∀ d ∈ DR,
        RLCD.distToInt (tau * d - alphaR) ≤ delta := by
      intro d hd
      exact (Finset.mem_filter.mp hd).2.2
    simpa only [r] using
      (card_residue_block_le tau alphaR delta a L DR htau hdelta
        hdeltaSmall hscale hres)
  have hsampleL : ∑ d ∈ DL, f d ≤
      (r : ℝ) * f 0 + (r : ℝ) / L * ∑ d ∈ Finset.range N, f d := by
    have h := sum_right_of_antitone_of_block_card
      (N := N) (c := 0) (L := L) (r := r) (f := f) (E := DL)
      hL hDLsub hf0 (hanti := by
        intro i j hi hij hjN
        exact hanti hi hij hjN) (hblock := hDLblock)
    simpa only [Finset.filter_true_of_mem (fun _ _ ↦ Nat.zero_le _)] using h
  have hsampleR : ∑ d ∈ DR, f d ≤
      (r : ℝ) * f 0 + (r : ℝ) / L * ∑ d ∈ Finset.range N, f d := by
    have h := sum_right_of_antitone_of_block_card
      (N := N) (c := 0) (L := L) (r := r) (f := f) (E := DR)
      hL hDRsub hf0 (hanti := by
        intro i j hi hij hjN
        exact hanti hi hij hjN) (hblock := hDRblock)
    simpa only [Finset.filter_true_of_mem (fun _ _ ↦ Nat.zero_le _)] using h
  have hsumL : ∑ j ∈ EL, (hypergeomWeight m ell j : ℝ) =
      ∑ d ∈ DL, f d := by
    apply Finset.sum_bij (fun j _ ↦ c - j)
    · intro j hj
      have hjEL := Finset.mem_filter.mp hj
      have hjE := Finset.mem_filter.mp hjEL.1
      have hjc : j ≤ c := hjEL.2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr (by dsimp only [N]; omega), ?_⟩
      dsimp only [alphaL]
      rw [Nat.cast_sub hjc]
      convert hjE.2 using 1 <;> ring_nf
    · intro j₁ hj₁ j₂ hj₂ heq
      have hj₁c := (Finset.mem_filter.mp hj₁).2
      have hj₂c := (Finset.mem_filter.mp hj₂).2
      omega
    · intro d hd
      have hdDL := Finset.mem_filter.mp hd
      have hdc : d ≤ c := by
        have := Finset.mem_range.mp hdDL.1
        dsimp only [N] at this
        omega
      let j := c - d
      have hjc : j ≤ c := by dsimp only [j]; omega
      have hjell : j < ell + 1 := by dsimp only [j]; omega
      have hjres : RLCD.distToInt (tau * j - alpha) ≤ delta := by
        dsimp only [j]
        rw [Nat.cast_sub hdc]
        dsimp only [alphaL] at hdDL
        convert hdDL.2 using 1 <;> ring_nf
      refine ⟨j, ⟨?_, ?_⟩⟩
      · rw [Finset.mem_filter]
        refine ⟨?_, hjc⟩
        change j ∈ hypergeomResidueSet ell tau alpha delta
        rw [hypergeomResidueSet, Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr hjell, hjres⟩
      · dsimp only [j]
        omega
    · intro j hj
      have hjc := (Finset.mem_filter.mp hj).2
      dsimp only [f]
      rw [show c - (c - j) = j by omega]
  have hsumR : ∑ j ∈ ER, (hypergeomWeight m ell j : ℝ) =
      ∑ d ∈ DR, f d := by
    apply Finset.sum_bij (fun j _ ↦ c - (ell - j))
    · intro j hj
      have hjER := Finset.mem_filter.mp hj
      have hjE := Finset.mem_filter.mp hjER.1
      have hjell : j ≤ ell := by
        have := Finset.mem_range.mp hjE.1
        omega
      have hcj : c < j := by omega
      have htail : ell - j ≤ c := by omega
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr (by dsimp only [N]; omega), ?_, ?_⟩
      · omega
      · dsimp only [alphaR]
        rw [Nat.cast_sub htail, Nat.cast_sub hjell]
        convert hjE.2 using 1 <;> ring_nf
    · intro j₁ hj₁ j₂ hj₂ heq
      have hj₁E := Finset.mem_filter.mp (Finset.mem_filter.mp hj₁).1
      have hj₂E := Finset.mem_filter.mp (Finset.mem_filter.mp hj₂).1
      have hj₁ell : j₁ ≤ ell := by
        have := Finset.mem_range.mp hj₁E.1
        omega
      have hj₂ell : j₂ ≤ ell := by
        have := Finset.mem_range.mp hj₂E.1
        omega
      have htail₁ : ell - j₁ ≤ c := by
        have := (Finset.mem_filter.mp hj₁).2
        omega
      have htail₂ : ell - j₂ ≤ c := by
        have := (Finset.mem_filter.mp hj₂).2
        omega
      omega
    · intro d hd
      have hdDR := Finset.mem_filter.mp hd
      have hdc : d ≤ c := by
        have := Finset.mem_range.mp hdDR.1
        dsimp only [N] at this
        omega
      let j := ell - (c - d)
      have hjell : j ≤ ell := by dsimp only [j]; omega
      have hcj : c < j := by exact hdDR.2.1
      have hjres : RLCD.distToInt (tau * j - alpha) ≤ delta := by
        dsimp only [j]
        rw [Nat.cast_sub (by omega : c - d ≤ ell), Nat.cast_sub hdc]
        dsimp only [alphaR] at hdDR
        convert hdDR.2.2 using 1 <;> ring_nf
      refine ⟨j, ⟨?_, ?_⟩⟩
      · rw [Finset.mem_filter]
        refine ⟨?_, by omega⟩
        change j ∈ hypergeomResidueSet ell tau alpha delta
        rw [hypergeomResidueSet, Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr (by omega), hjres⟩
      · dsimp only [j]
        omega
    · intro j hj
      have hjER := Finset.mem_filter.mp hj
      have hjE := Finset.mem_filter.mp hjER.1
      have hjell : j ≤ ell := by
        have := Finset.mem_range.mp hjE.1
        omega
      have htail : ell - j ≤ c := by omega
      dsimp only [f]
      rw [show c - (c - (ell - j)) = ell - j by omega]
      exact_mod_cast (hypergeomWeight_symm m ell j hjell).symm
  have hsplit : ∑ j ∈ E, (hypergeomWeight m ell j : ℝ) =
      (∑ j ∈ EL, (hypergeomWeight m ell j : ℝ)) +
        ∑ j ∈ ER, (hypergeomWeight m ell j : ℝ) := by
    simpa only [EL, ER] using
      (Finset.sum_filter_add_sum_filter_not E (fun j ↦ j ≤ c)
        (fun j ↦ (hypergeomWeight m ell j : ℝ))).symm
  have hdistTotal : ∑ d ∈ Finset.range N, f d ≤
      (Nat.choose (2 * m) ell : ℝ) := by
    have hreindex : ∑ d ∈ Finset.range N, f d =
        ∑ j ∈ Finset.range N, (hypergeomWeight m ell j : ℝ) := by
      apply Finset.sum_bij (fun d _ ↦ c - d)
      · intro d hd
        rw [Finset.mem_range]
        have := Finset.mem_range.mp hd
        dsimp only [N] at this ⊢
        omega
      · intro d₁ hd₁ d₂ hd₂ heq
        have h₁ := Finset.mem_range.mp hd₁
        have h₂ := Finset.mem_range.mp hd₂
        dsimp only [N] at h₁ h₂
        omega
      · intro j hj
        have hjc : j ≤ c := by
          have := Finset.mem_range.mp hj
          dsimp only [N] at this
          omega
        refine ⟨c - j, Finset.mem_range.mpr (by dsimp only [N]; omega), by omega⟩
      · intro d hd
        rfl
    rw [hreindex]
    calc
      ∑ j ∈ Finset.range N, (hypergeomWeight m ell j : ℝ) ≤
          ∑ j ∈ Finset.range (ell + 1), (hypergeomWeight m ell j : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj
              rw [Finset.mem_range] at hj ⊢
              dsimp only [N, c] at hj
              omega
            · intro j _hj _
              positivity
      _ = Nat.choose (2 * m) ell := by
        exact_mod_cast sum_range_hypergeomWeight m ell
  have hboth : (∑ d ∈ DL, f d) + ∑ d ∈ DR, f d ≤
      2 * ((r : ℝ) * f 0 + (r : ℝ) / L *
        Nat.choose (2 * m) ell) := by
    calc
      (∑ d ∈ DL, f d) + ∑ d ∈ DR, f d ≤
          2 * ((r : ℝ) * f 0 + (r : ℝ) / L *
            ∑ d ∈ Finset.range N, f d) := by linarith
      _ ≤ 2 * ((r : ℝ) * f 0 + (r : ℝ) / L *
            Nat.choose (2 * m) ell) := by
              gcongr
  calc
    ∑ j ∈ hypergeomResidueSet ell tau alpha delta,
        (hypergeomWeight m ell j : ℝ) =
      (∑ d ∈ DL, f d) + ∑ d ∈ DR, f d := by
        rw [show hypergeomResidueSet ell tau alpha delta = E by rfl,
          hsplit, hsumL, hsumR]
    _ ≤ 2 * ((r : ℝ) * f 0 + (r : ℝ) / L *
        Nat.choose (2 * m) ell) := hboth
    _ = 2 * ((2 * Nat.floor (2 * delta / |tau|) + 1 : ℕ) *
          (hypergeomWeight m ell (ell / 2) : ℝ) +
        ((2 * Nat.floor (2 * delta / |tau|) + 1 : ℕ) : ℝ) / L *
          Nat.choose (2 * m) ell) := by rfl

/-- The small-parameter form of KSSS Lemma 8.4.  Here `k = 2m`; this
intermediate version keeps the equivalent scale `1 / sqrt m`, which makes
the exact finite hypergeometric normalization transparent. -/
lemma hypergeomResidue_ratio_le_small_of_density
    (eta : ℝ) (m ell : ℕ) (tau alpha delta : ℝ)
    (heta : 0 < eta) (hm : 1 ≤ m)
    (hetaSqrt : 64 ≤ eta * Real.sqrt m)
    (hellower : eta * (2 * m : ℕ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * (2 * m : ℕ))
    (htau : 0 < |tau|) (htauSmall : |tau| < 1 / 8)
    (hdelta : 0 ≤ delta) (hdeltaSmall : delta < 1 / 8) :
    (∑ j ∈ hypergeomResidueSet ell tau alpha delta,
        (hypergeomWeight m ell j : ℝ)) / Nat.choose (2 * m) ell ≤
      2048 / eta *
        ((|tau| + delta) * (|tau| + 1 / Real.sqrt m) / |tau|) := by
  let t : ℝ := |tau|
  let L : ℕ := Nat.floor (1 / (2 * t))
  let R : ℕ := Nat.floor (2 * delta / t)
  let r : ℕ := 2 * R + 1
  have ht : 0 < t := htau
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hmreal
  have hsqrtPos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  have htwoMpos : (0 : ℝ) < (2 * m : ℕ) := by positivity
  have hetaHalf : eta ≤ 1 / 2 := by
    have h := hellower.trans hellupper
    have h' : eta ≤ 1 - eta := le_of_mul_le_mul_right (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h) htwoMpos
    linarith
  have hetaOne : eta ≤ 1 := hetaHalf.trans (by norm_num)
  have hell : ell ≤ 2 * m := by
    have hreal : (ell : ℝ) ≤ (2 * m : ℕ) := by
      calc
        (ell : ℝ) ≤ (1 - eta) * (2 * m : ℕ) := hellupper
        _ ≤ 1 * (2 * m : ℕ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ = (2 * m : ℕ) := one_mul _
    exact_mod_cast hreal
  have hsqrtLe : Real.sqrt (m : ℝ) ≤ m :=
    Real.sqrt_le_self_iff.mpr (Or.inr hmreal)
  have hetaM : 8 ≤ eta * m := by
    calc
      (8 : ℝ) ≤ 64 := by norm_num
      _ ≤ eta * Real.sqrt m := hetaSqrt
      _ ≤ eta * m := mul_le_mul_of_nonneg_left hsqrtLe heta.le
  have harg0 : 0 ≤ 1 / (2 * t) := by positivity
  have hargOne : (1 : ℝ) ≤ 1 / (2 * t) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * t)]
    nlinarith
  have hL : 1 ≤ L := by
    dsimp only [L]
    apply Nat.le_floor
    simpa using hargOne
  have hLupper : (L : ℝ) ≤ 1 / (2 * t) := by
    dsimp only [L]
    exact Nat.floor_le harg0
  have hscale : (L : ℝ) * |tau| ≤ 1 / 2 := by
    dsimp only [t] at hLupper
    calc
      (L : ℝ) * |tau| ≤ (1 / (2 * |tau|)) * |tau| :=
        mul_le_mul_of_nonneg_right hLupper (abs_nonneg _)
      _ = 1 / 2 := by field_simp
  have hLarg : 1 / (2 * t) < (L : ℝ) + 1 := by
    dsimp only [L]
    exact Nat.lt_floor_add_one _
  have hquarter : 1 / (4 * t) ≤ 1 / (2 * t) - 1 := by
    have hmul : (4 * t) * (1 / (4 * t) + 1) ≤
        (4 * t) * (1 / (2 * t)) := by
      field_simp
      nlinarith
    rw [le_sub_iff_add_le]
    exact le_of_mul_le_mul_left hmul (by positivity : (0 : ℝ) < 4 * t)
  have hLlower : 1 / (4 * t) ≤ (L : ℝ) := by linarith
  have hLreal : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hinvL : 1 / (L : ℝ) ≤ 4 * t := by
    have hrecip := one_div_le_one_div_of_le
      (by positivity : (0 : ℝ) < 1 / (4 * t)) hLlower
    simpa only [one_div_div, div_one] using hrecip
  have hratio0 : 0 ≤ 2 * delta / t := by positivity
  have hRupper : (R : ℝ) ≤ 2 * delta / t := by
    dsimp only [R]
    exact Nat.floor_le hratio0
  let A : ℝ := (t + delta) / t
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hrUpper : (r : ℝ) ≤ 4 * A := by
    have hident : 4 * A = 4 + 4 * delta / t := by
      dsimp only [A]
      field_simp
    calc
      (r : ℝ) = 2 * (R : ℝ) + 1 := by dsimp only [r]; push_cast; ring
      _ ≤ 2 * (2 * delta / t) + 1 := by gcongr
      _ = 4 * delta / t + 1 := by ring
      _ ≤ 4 + 4 * delta / t := by linarith
      _ = 4 * A := hident.symm
  have htotalPos : (0 : ℝ) < Nat.choose (2 * m) ell := by
    exact_mod_cast Nat.choose_pos hell
  have hcore := sum_hypergeomWeight_residue_le_of_block
    m ell L tau alpha delta hell hL htau hdelta hdeltaSmall (by
      simpa only [t] using hscale)
  have hnorm :
      (∑ j ∈ hypergeomResidueSet ell tau alpha delta,
          (hypergeomWeight m ell j : ℝ)) / Nat.choose (2 * m) ell ≤
        2 * ((r : ℝ) *
            ((hypergeomWeight m ell (ell / 2) : ℝ) /
              Nat.choose (2 * m) ell) + (r : ℝ) / L) := by
    calc
      (∑ j ∈ hypergeomResidueSet ell tau alpha delta,
          (hypergeomWeight m ell j : ℝ)) / Nat.choose (2 * m) ell ≤
        (2 * ((r : ℝ) * (hypergeomWeight m ell (ell / 2) : ℝ) +
          (r : ℝ) / L * Nat.choose (2 * m) ell)) /
            Nat.choose (2 * m) ell :=
              div_le_div_of_nonneg_right (by simpa only [r, R, t] using hcore)
                htotalPos.le
      _ = 2 * ((r : ℝ) *
            ((hypergeomWeight m ell (ell / 2) : ℝ) /
              Nat.choose (2 * m) ell) + (r : ℝ) / L) := by
              field_simp
  have hmode := hypergeomWeight_div_choose_le_of_density
    eta m ell (ell / 2) heta hm hetaM hetaSqrt hellower hellupper (by omega)
  have hp : (hypergeomWeight m ell (ell / 2) : ℝ) /
        Nat.choose (2 * m) ell ≤
      (128 / eta) * (t + 1 / Real.sqrt m) := by
    calc
      (hypergeomWeight m ell (ell / 2) : ℝ) /
          Nat.choose (2 * m) ell ≤ 128 / (eta * Real.sqrt m) := hmode
      _ = (128 / eta) * (1 / Real.sqrt m) := by field_simp
      _ ≤ (128 / eta) * (t + 1 / Real.sqrt m) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hcoef : (4 : ℝ) ≤ 128 / eta := by
    rw [le_div_iff₀ heta]
    nlinarith
  have hinv : 1 / (L : ℝ) ≤
      (128 / eta) * (t + 1 / Real.sqrt m) := by
    calc
      1 / (L : ℝ) ≤ 4 * t := hinvL
      _ ≤ (128 / eta) * t :=
        mul_le_mul_of_nonneg_right hcoef ht.le
      _ ≤ (128 / eta) * (t + 1 / Real.sqrt m) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (by positivity)) (by positivity)
  have hfirst : (r : ℝ) *
        ((hypergeomWeight m ell (ell / 2) : ℝ) /
          Nat.choose (2 * m) ell) ≤
      (4 * A) * ((128 / eta) * (t + 1 / Real.sqrt m)) := by
    exact mul_le_mul hrUpper hp (by positivity) (mul_nonneg (by norm_num) hA0)
  have hsecond : (r : ℝ) / L ≤
      (4 * A) * ((128 / eta) * (t + 1 / Real.sqrt m)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul hrUpper (by simpa only [one_div] using hinv)
      (by positivity) (mul_nonneg (by norm_num) hA0)
  calc
    (∑ j ∈ hypergeomResidueSet ell tau alpha delta,
        (hypergeomWeight m ell j : ℝ)) / Nat.choose (2 * m) ell ≤
      2 * ((r : ℝ) *
          ((hypergeomWeight m ell (ell / 2) : ℝ) /
            Nat.choose (2 * m) ell) + (r : ℝ) / L) := hnorm
    _ ≤ 2 * ((4 * A) * ((128 / eta) * (t + 1 / Real.sqrt m)) +
        (4 * A) * ((128 / eta) * (t + 1 / Real.sqrt m))) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num)
    _ = 2048 / eta *
        ((|tau| + delta) * (|tau| + 1 / Real.sqrt m) / |tau|) := by
          dsimp only [A, t]
          field_simp
          ring

/-- KSSS Lemma 8.4 in the exact finite hypergeometric model `k = 2m`.
The explicit constant `4096 / eta` witnesses the source notation
`\lesssim_eta`; unlike the paper's proof, this proof uses only exact
unimodality and finite block sampling. -/
lemma hypergeomResidue_ratio_le_of_density
    (eta : ℝ) (m ell : ℕ) (tau alpha delta : ℝ)
    (heta : 0 < eta) (hm : 1 ≤ m)
    (hellower : eta * (2 * m : ℕ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * (2 * m : ℕ))
    (htau : tau ≠ 0) (hdelta : 0 ≤ delta) (hdeltaUpper : delta ≤ 1 / 2) :
    (∑ j ∈ hypergeomResidueSet ell tau alpha delta,
        (hypergeomWeight m ell j : ℝ)) / Nat.choose (2 * m) ell ≤
      4096 / eta *
        ((|tau| + delta) *
          (|tau| + 1 / Real.sqrt (2 * m : ℕ)) / |tau|) := by
  let t : ℝ := |tau|
  let s : ℝ := Real.sqrt (2 * m : ℕ)
  let A : ℝ := (t + delta) / t
  let Q : ℝ := t + 1 / s
  have ht : 0 < t := abs_pos.mpr htau
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hmreal
  have hsqrtMpos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  have htwoMpos : (0 : ℝ) < (2 * m : ℕ) := by positivity
  have hspos : 0 < s := by
    dsimp only [s]
    exact Real.sqrt_pos.mpr htwoMpos
  have hetaHalf : eta ≤ 1 / 2 := by
    have h := hellower.trans hellupper
    have h' : eta ≤ 1 - eta := le_of_mul_le_mul_right (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h) htwoMpos
    linarith
  have hetaOne : eta ≤ 1 := hetaHalf.trans (by norm_num)
  have hell : ell ≤ 2 * m := by
    have hreal : (ell : ℝ) ≤ (2 * m : ℕ) := by
      calc
        (ell : ℝ) ≤ (1 - eta) * (2 * m : ℕ) := hellupper
        _ ≤ 1 * (2 * m : ℕ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ = (2 * m : ℕ) := one_mul _
    exact_mod_cast hreal
  have htotalPos : (0 : ℝ) < Nat.choose (2 * m) ell := by
    exact_mod_cast Nat.choose_pos hell
  have hprob :
      (∑ j ∈ hypergeomResidueSet ell tau alpha delta,
          (hypergeomWeight m ell j : ℝ)) / Nat.choose (2 * m) ell ≤ 1 := by
    rw [div_le_one htotalPos]
    calc
      ∑ j ∈ hypergeomResidueSet ell tau alpha delta,
          (hypergeomWeight m ell j : ℝ) ≤
        ∑ j ∈ Finset.range (ell + 1),
          (hypergeomWeight m ell j : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.filter_subset _ _
            · intro j _hj _
              positivity
      _ = Nat.choose (2 * m) ell := by
        exact_mod_cast sum_range_hypergeomWeight m ell
  have hAOne : 1 ≤ A := by
    dsimp only [A]
    rw [le_div_iff₀ ht]
    linarith
  have hA0 : 0 ≤ A := le_trans zero_le_one hAOne
  have hQ0 : 0 ≤ Q := by dsimp only [Q]; positivity
  have hcoef0 : 0 ≤ 4096 / eta := by positivity
  have hsqrtTwoLe : s ≤ 2 * Real.sqrt m := by
    have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
      rw [Real.sqrt_le_iff]
      norm_num
    dsimp only [s]
    rw [show ((2 * m : ℕ) : ℝ) = (2 : ℝ) * m by push_cast; ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg _)
  have hinvSqrt : 1 / Real.sqrt m ≤ 2 / s := by
    have hrecip := one_div_le_one_div_of_le hspos hsqrtTwoLe
    calc
      1 / Real.sqrt m = 2 * (1 / (2 * Real.sqrt m)) := by field_simp
      _ ≤ 2 * (1 / s) := mul_le_mul_of_nonneg_left hrecip (by norm_num)
      _ = 2 / s := by ring
  by_cases hsize : 64 ≤ eta * Real.sqrt m
  · by_cases htSmall : t < 1 / 8
    · by_cases hdSmall : delta < 1 / 8
      · have hsmall := hypergeomResidue_ratio_le_small_of_density
          eta m ell tau alpha delta heta hm hsize hellower hellupper
          (by simpa only [t] using ht) (by simpa only [t] using htSmall)
          hdelta hdSmall
        have hscaleQ : t + 1 / Real.sqrt m ≤ 2 * Q := by
          dsimp only [Q]
          calc
            t + 1 / Real.sqrt m ≤ t + 2 / s := by
              simpa only [add_comm] using add_le_add_left hinvSqrt t
            _ ≤ 2 * (t + 1 / s) := by
              rw [show 2 * (t + 1 / s) = 2 * t + 2 / s by ring]
              linarith
        calc
          (∑ j ∈ hypergeomResidueSet ell tau alpha delta,
              (hypergeomWeight m ell j : ℝ)) / Nat.choose (2 * m) ell ≤
            2048 / eta *
              ((|tau| + delta) * (|tau| + 1 / Real.sqrt m) / |tau|) := hsmall
          _ = (2048 / eta * A) * (t + 1 / Real.sqrt m) := by
            dsimp only [A, t]
            field_simp
          _ ≤ (2048 / eta * A) * (2 * Q) := by
            exact mul_le_mul_of_nonneg_left hscaleQ (mul_nonneg (by positivity) hA0)
          _ = 4096 / eta *
              ((|tau| + delta) *
                (|tau| + 1 / Real.sqrt (2 * m : ℕ)) / |tau|) := by
            dsimp only [A, Q, s, t]
            field_simp
            ring
      · have hdLarge : 1 / 8 ≤ delta := le_of_not_gt hdSmall
        have hAq : 1 / 8 ≤ A * Q := by
          have hQt : t ≤ Q := by
            dsimp only [Q]
            exact le_add_of_nonneg_right (by positivity)
          have hAt : delta ≤ A * t := by
            have hAtEq : A * t = t + delta := by dsimp only [A]; field_simp
            rw [hAtEq]
            linarith
          exact hdLarge.trans (hAt.trans
            (mul_le_mul_of_nonneg_left hQt hA0))
        have hcoef8 : (8 : ℝ) ≤ 4096 / eta := by
          rw [le_div_iff₀ heta]
          nlinarith
        have hRhs : 1 ≤ (4096 / eta) * (A * Q) := by
          calc
            (1 : ℝ) = 8 * (1 / 8) := by norm_num
            _ ≤ (4096 / eta) * (A * Q) :=
              mul_le_mul hcoef8 hAq (by norm_num) (by positivity)
        exact hprob.trans (hRhs.trans_eq (by
          dsimp only [A, Q, s, t]
          field_simp
          ))
    · have htLarge : 1 / 8 ≤ t := le_of_not_gt htSmall
      have hAq : 1 / 8 ≤ A * Q := by
        have hQt : t ≤ Q := by
          dsimp only [Q]
          exact le_add_of_nonneg_right (by positivity)
        calc
          (1 / 8 : ℝ) ≤ 1 * t := by simpa only [one_mul] using htLarge
          _ ≤ A * Q := mul_le_mul hAOne hQt ht.le hA0
      have hcoef8 : (8 : ℝ) ≤ 4096 / eta := by
        rw [le_div_iff₀ heta]
        nlinarith
      have hRhs : 1 ≤ (4096 / eta) * (A * Q) := by
        calc
          (1 : ℝ) = 8 * (1 / 8) := by norm_num
          _ ≤ (4096 / eta) * (A * Q) :=
            mul_le_mul hcoef8 hAq (by norm_num) (by positivity)
      exact hprob.trans (hRhs.trans_eq (by
        dsimp only [A, Q, s, t]
        field_simp
        ))
  · have hsize' : eta * Real.sqrt m < 64 := lt_of_not_ge hsize
    have hetaS : eta * s < 128 := by
      calc
        eta * s ≤ eta * (2 * Real.sqrt m) :=
          mul_le_mul_of_nonneg_left hsqrtTwoLe heta.le
        _ < 128 := by nlinarith
    have hbase : 1 ≤ (4096 / eta) * (1 / s) := by
      have hden : 0 < eta * s := mul_pos heta hspos
      rw [show (4096 / eta) * (1 / s) = 4096 / (eta * s) by field_simp]
      rw [le_div_iff₀ hden]
      linarith
    have hInvQ : 1 / s ≤ Q := by dsimp only [Q]; linarith
    have hRhs : 1 ≤ (4096 / eta) * (A * Q) := by
      calc
        (1 : ℝ) ≤ (4096 / eta) * (1 / s) := hbase
        _ ≤ (4096 / eta) * Q :=
          mul_le_mul_of_nonneg_left hInvQ hcoef0
        _ ≤ (4096 / eta) * (A * Q) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa only [one_mul] using
              (mul_le_mul_of_nonneg_right hAOne hQ0)) hcoef0
    exact hprob.trans (hRhs.trans_eq (by
      dsimp only [A, Q, s, t]
      field_simp
      ))

/-- Source-shaped KSSS Lemma 8.4, with the affine shift written as `+ x`. -/
theorem ksssLemma84
    (eta : ℝ) (m ell : ℕ) (tau x delta : ℝ)
    (heta : 0 < eta) (hm : 1 ≤ m)
    (hellower : eta * (2 * m : ℕ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * (2 * m : ℕ))
    (htau : tau ≠ 0) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 2) :
    (∑ j ∈ (Finset.range (ell + 1)).filter (fun j : ℕ ↦
        RLCD.distToInt (tau * j + x) ≤ delta),
        (hypergeomWeight m ell j : ℝ)) / Nat.choose (2 * m) ell ≤
      4096 / eta *
        ((|tau| + delta) *
          (|tau| + 1 / Real.sqrt (2 * m : ℕ)) / |tau|) := by
  have h := hypergeomResidue_ratio_le_of_density
    eta m ell tau (-x) delta heta hm hellower hellupper htau hdelta.le hdeltaUpper
  simpa only [hypergeomResidueSet, sub_neg_eq_add] using h

end UnimodalBlockSampling

end QuadraticCancellation
end Erdos88
