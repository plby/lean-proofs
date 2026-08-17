/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.GeneralizedParkingDefs
import ErdosProblems.Erdos896.Ford.ParkingForestBound
import ErdosProblems.Erdos896.Ford.OrderQBound
import ErdosProblems.Erdos896.Ford.QDirect

/-!
# A finite generalized-parking bound

This file isolates the finite occupancy problem behind the upper estimate in
Ford's Lemma 11.1.  There are `k` labelled balls and

`V = k - U + W`

ordered boxes.  A word is good when its first `r` boxes contain at most
`U + r - 1` balls, for `0 ≤ r ≤ k - U`.  On reversing the order of the
boxes this says that the `i`-th smallest letter is at most `W + i - 2`.
-/

namespace Erdos896.Ford

/-- Reverse-bin form of `generalizedParkingGood`.  The parameter `s` is
zero based: it says that at least `s+1` letters occur in the last
`W+s` boxes of the original word.  After reversing the boxes, this is the
usual sorted constraint `q_(s+1) ≤ W+(s+1)-2`. -/
def generalizedParkingReverseGood (k U W : ℕ)
    (f : Fin k → Fin (k - U + W)) : Prop :=
  ∀ s : Fin (k - U + 1),
    s.val + 1 ≤
      ((Finset.univ.filter fun i ↦ k - U - s.val ≤ (f i).val).card)

theorem generalizedParkingGood_iff_reverse
    {k U W : ℕ} (hU : 1 ≤ U) (hUk : U ≤ k)
    (f : Fin k → Fin (k - U + W)) :
    generalizedParkingGood k U W f ↔
      generalizedParkingReverseGood k U W f := by
  classical
  constructor
  · intro hf s
    let r : Fin (k - U + 1) :=
      ⟨k - U - s.val, by omega⟩
    have hr := hf r
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin k)))
      (p := fun i ↦ (f i).val < r.val)
    simp only [Finset.card_univ, Fintype.card_fin] at hpartition
    have hcomp :
        (Finset.univ.filter fun i ↦ ¬(f i).val < r.val) =
          Finset.univ.filter fun i ↦ k - U - s.val ≤ (f i).val := by
      apply Finset.filter_congr
      intro i hi
      simp [r]
    rw [hcomp] at hpartition
    have hsle : s.val ≤ k - U := by omega
    change
      (Finset.univ.filter fun i ↦ (f i).val < k - U - s.val).card ≤
        U + (k - U - s.val) - 1 at hr
    have hthreshold : U + (k - U - s.val) - 1 = k - s.val - 1 := by omega
    rw [hthreshold] at hr
    change
      (Finset.univ.filter fun i ↦ (f i).val < k - U - s.val).card +
        (Finset.univ.filter fun i ↦ k - U - s.val ≤ (f i).val).card = k
      at hpartition
    omega
  · intro hf r
    let s : Fin (k - U + 1) :=
      ⟨k - U - r.val, by omega⟩
    have hs := hf s
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin k)))
      (p := fun i ↦ (f i).val < r.val)
    simp only [Finset.card_univ, Fintype.card_fin] at hpartition
    have hcomp :
        (Finset.univ.filter fun i ↦ ¬(f i).val < r.val) =
          Finset.univ.filter fun i ↦ k - U - s.val ≤ (f i).val := by
      apply Finset.filter_congr
      intro i hi
      have hrle : r.val ≤ k - U := by omega
      have hinv : k - U - (k - U - r.val) = r.val := by omega
      simp [s, hinv]
    rw [hcomp] at hpartition
    have hrle : r.val ≤ k - U := by omega
    have hinv : k - U - (k - U - r.val) = r.val := by omega
    dsimp only [s] at hs
    rw [hinv] at hs
    have hcompThreshold : k - U - s.val = r.val := by
      dsimp [s]
      omega
    rw [hcompThreshold] at hpartition
    change
      (Finset.univ.filter fun i ↦ (f i).val < r.val).card +
        (Finset.univ.filter fun i ↦ r.val ≤ (f i).val).card = k
      at hpartition
    omega

/-- Reverse every box label.  This is the involution which identifies the
upper-tail formulation above with the initial-segment formulation used by
the first-failure enumeration. -/
def reverseParkingWord {k U W : ℕ}
    (f : Fin k → Fin (k - U + W)) : Fin k → Fin (k - U + W) :=
  fun i ↦ (f i).rev

@[simp] theorem reverseParkingWord_reverseParkingWord {k U W : ℕ}
    (f : Fin k → Fin (k - U + W)) :
    reverseParkingWord (reverseParkingWord f) = f := by
  funext i
  simp [reverseParkingWord]

private theorem reverseParkingWord_lt_iff
    {k U W : ℕ}
    (f : Fin k → Fin (k - U + W)) (i : Fin k)
    {s : ℕ} (hs : s < k - U + 1) :
    (reverseParkingWord f i).val < W + s ↔ k - U - s ≤ (f i).val := by
  simp only [reverseParkingWord, Fin.val_rev]
  have hx := (f i).isLt
  omega

theorem generalizedParkingReverseGood_reverseParkingWord_iff
    {k U W : ℕ}
    (f : Fin k → Fin (k - U + W)) :
    generalizedParkingReverseGood k U W f ↔
      confinedParkingGood k U W (reverseParkingWord f) := by
  constructor
  · intro hf s hs
    have h := hf ⟨s, hs⟩
    convert h using 1
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact reverseParkingWord_lt_iff f i hs
  · intro hf s
    have h := hf s.val s.isLt
    convert h using 1
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (reverseParkingWord_lt_iff f i s.isLt).symm

private def generalizedParkingReverseGoodEquivConfinedParkingGood
    (k U W : ℕ) :
    {f : Fin k → Fin (k - U + W) // generalizedParkingReverseGood k U W f} ≃
      {f : Fin k → Fin (k - U + W) // confinedParkingGood k U W f} where
  toFun f := ⟨@reverseParkingWord k U W f,
    (generalizedParkingReverseGood_reverseParkingWord_iff
      (k := k) (U := U) (W := W) f).mp f.property⟩
  invFun f := ⟨@reverseParkingWord k U W f, by
    rw [generalizedParkingReverseGood_reverseParkingWord_iff
      (k := k) (U := U) (W := W),
      reverseParkingWord_reverseParkingWord]
    exact f.property⟩
  left_inv f := by
    ext i
    simp
  right_inv f := by
    ext i
    simp

noncomputable instance (k U W : ℕ) :
    DecidablePred (@generalizedParkingReverseGood k U W) :=
  Classical.decPred _

/-- The cardinality-preserving reversal which puts the finite event in the
form used by the Abel first-failure recurrence. -/
theorem generalizedParkingGood_card_eq_confinedParkingGood
    {k U W : ℕ} (hU : 1 ≤ U) (hUk : U ≤ k) :
    (Finset.univ.filter (@generalizedParkingGood k U W)).card =
      (Finset.univ.filter (@confinedParkingGood k U W)).card := by
  have hforward :
      (Finset.univ.filter (@generalizedParkingGood k U W)).card =
        (Finset.univ.filter (@generalizedParkingReverseGood k U W)).card := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro f hf
    exact generalizedParkingGood_iff_reverse hU hUk f
  rw [hforward]
  have hcard := Fintype.card_congr
    (generalizedParkingReverseGoodEquivConfinedParkingGood k U W)
  simpa [Fintype.card_subtype] using hcard

/-- Exact Abel first-violation enumeration of the generalized parking event.
This is the finite identity to which the analytic tail estimate is applied. -/
theorem generalizedParkingGood_card_eq_abelRemainder
    {k U W : ℕ} (hU : 1 ≤ U) (hUk : U ≤ k) :
    (Finset.univ.filter (@generalizedParkingGood k U W)).card =
      (k - U + W) ^ k -
        ∑ j ∈ Finset.range (k - U + 1),
          k.choose j * parkingAbelP j W *
            (k - U - j) ^ (k - j) := by
  rw [generalizedParkingGood_card_eq_confinedParkingGood hU hUk,
    card_confinedParkingGood_eq_abelRemainder hUk]

/-- At `U = 1` the confined condition is the ordinary `W`-parking
condition, so Pollak--Abel enumeration is already a closed form. -/
theorem generalizedParkingGood_card_eq_parkingAbelP_of_U_one
    (k W : ℕ) (hk : 1 ≤ k) :
    (Finset.univ.filter (@generalizedParkingGood k 1 W)).card =
      parkingAbelP k W := by
  rw [generalizedParkingGood_card_eq_confinedParkingGood (by omega) hk]
  rw [← card_ordinaryParkingGood_eq_parkingAbelP]
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [confinedParkingGood, ordinaryParkingGood]
  have hindex : k - 1 + 1 = k := by omega
  rw [hindex]

/-- First-violation form.  This is the starting point of the Abel
decomposition: at a bad cut `r`, at least `U+r` labels lie in the first `r`
boxes. -/
theorem not_generalizedParkingGood_iff
    {k U W : ℕ} (hU : 1 ≤ U) (f : Fin k → Fin (k - U + W)) :
    ¬ generalizedParkingGood k U W f ↔
      ∃ r : Fin (k - U + 1),
        U + r.val ≤
          (Finset.univ.filter fun i ↦ (f i).val < r.val).card := by
  rw [generalizedParkingGood]
  push Not
  apply exists_congr
  intro r
  omega

/-- The unrestricted count which is used in the short-parameter branch of
the estimate. -/
theorem generalizedParkingGood_card_le_pow (k U W : ℕ) :
    (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
      (k - U + W) ^ k := by
  calc
    (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
        (Finset.univ : Finset (Fin k → Fin (k - U + W))).card :=
      Finset.card_filter_le _ _
    _ = (k - U + W) ^ k := by simp

/-- The elementary branch of the normalized bound.  It is kept separate
because the complementary branch is precisely where the generalized
parking enumeration is needed. -/
theorem generalizedParkingGood_card_bound_of_k_le
    (k U W : ℕ) (hk : k ≤ 64 * U * W ^ 2) :
    k * (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
      64 * U * W ^ 2 * (k - U + W) ^ k := by
  calc
    k * (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
        k * (k - U + W) ^ k :=
      Nat.mul_le_mul_left k (generalizedParkingGood_card_le_pow k U W)
    _ ≤ 64 * U * W ^ 2 * (k - U + W) ^ k :=
      Nat.mul_le_mul_right ((k - U + W) ^ k) hk

/-- A convenient normalization lemma for combinatorial proofs of the hard
branch.  A forest or cycle construction naturally gives the slightly larger
base `V+1`; in the hard branch `U` is small compared with `k`, so the loss is
an absolute constant. -/
private theorem succ_pow_le_nine_mul_pow {V n : ℕ}
    (hV : 1 ≤ V) (hn : n ≤ 2 * V) :
    (V + 1) ^ n ≤ 9 * V ^ n := by
  have hbase : (1 : ℝ) ≤ 1 + (V : ℝ)⁻¹ := by
    exact le_add_of_nonneg_right (inv_nonneg.mpr (by positivity))
  have hpowmono :
      (1 + (V : ℝ)⁻¹) ^ n ≤ (1 + (V : ℝ)⁻¹) ^ (2 * V) := by
    exact pow_le_pow_right₀ hbase (by omega)
  have hVpos : (0 : ℝ) < V := by exact_mod_cast hV
  have hEuler : (1 + (V : ℝ)⁻¹) ^ V ≤ Real.exp 1 :=
    Real.one_add_inv_pow_le_exp
  have hsq : (1 + (V : ℝ)⁻¹) ^ (2 * V) ≤ 9 := by
    calc
      (1 + (V : ℝ)⁻¹) ^ (2 * V) =
          ((1 + (V : ℝ)⁻¹) ^ V) ^ 2 := by
            rw [← pow_mul]
            congr 1
            omega
      _ ≤ (Real.exp 1) ^ 2 := by gcongr
      _ ≤ 3 ^ 2 := by gcongr; exact Real.exp_one_lt_three.le
      _ = 9 := by norm_num
  have hfactor : ((V + 1 : ℕ) : ℝ) =
      (V : ℝ) * (1 + (V : ℝ)⁻¹) := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  have hratio : ((V + 1 : ℕ) : ℝ) ^ n ≤ 9 * (V : ℝ) ^ n := by
    calc
      ((V + 1 : ℕ) : ℝ) ^ n =
          (V : ℝ) ^ n * (1 + (V : ℝ)⁻¹) ^ n := by
        rw [hfactor, mul_pow]
      _ ≤ (V : ℝ) ^ n * (1 + (V : ℝ)⁻¹) ^ (2 * V) := by gcongr
      _ ≤ (V : ℝ) ^ n * 9 := by gcongr
      _ = 9 * (V : ℝ) ^ n := by ring
  exact_mod_cast hratio

theorem generalizedParkingGood_card_bound_of_succ_pow
    (k U W : ℕ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hUk : U ≤ k) (hW : 1 ≤ W)
    (hforest :
      (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
        U * W ^ 2 * (k - U + W + 1) ^ (k - 1)) :
    k * (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
      64 * U * W ^ 2 * (k - U + W) ^ k := by
  by_cases hsmall : k ≤ 64 * U * W ^ 2
  · exact generalizedParkingGood_card_bound_of_k_le k U W hsmall
  · have hWsq : 1 ≤ W ^ 2 := Nat.one_le_pow 2 W hW
    have h2U : 2 * U ≤ k := by
      have : 64 * U < k := by
        calc
          64 * U = 64 * U * 1 := by ring
          _ ≤ 64 * U * W ^ 2 := by gcongr
          _ < k := Nat.lt_of_not_ge hsmall
      omega
    let V := k - U + W
    have hV : 1 ≤ V := by dsimp [V]; omega
    have hkV : k ≤ 2 * V := by dsimp [V]; omega
    have hexp : k - 1 ≤ 2 * V := (Nat.sub_le k 1).trans hkV
    have hsucc := succ_pow_le_nine_mul_pow hV hexp
    have hk64V : 9 * k ≤ 64 * V := by omega
    calc
      k * (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
          k * (U * W ^ 2 * (V + 1) ^ (k - 1)) := by
        simpa [V, add_assoc] using Nat.mul_le_mul_left k hforest
      _ ≤ k * (U * W ^ 2 * (9 * V ^ (k - 1))) := by gcongr
      _ = (9 * k) * U * W ^ 2 * V ^ (k - 1) := by ring
      _ ≤ (64 * V) * U * W ^ 2 * V ^ (k - 1) := by gcongr
      _ = 64 * U * W ^ 2 * V ^ k := by
        have hkpred : k - 1 + 1 = k := by omega
        have hpow : V ^ k = V ^ (k - 1) * V := by
          conv_lhs => rw [← hkpred]
          exact pow_succ V (k - 1)
        rw [hpow]
        ring
      _ = 64 * U * W ^ 2 * (k - U + W) ^ k := by rfl

/-- Closed-form specialization of the normalized bound at `U = 1`. -/
theorem generalizedParkingGood_card_bound_U_one
    (k W : ℕ) (hk : 1 ≤ k) (hW : 1 ≤ W) :
    k * (Finset.univ.filter (@generalizedParkingGood k 1 W)).card ≤
      64 * W ^ 2 * (k - 1 + W) ^ k := by
  have hforest :
      (Finset.univ.filter (@generalizedParkingGood k 1 W)).card ≤
        1 * W ^ 2 * (k - 1 + W + 1) ^ (k - 1) := by
    rw [generalizedParkingGood_card_eq_parkingAbelP_of_U_one k W hk]
    rw [show k = (k - 1) + 1 by omega, parkingAbelP_succ]
    simp only [one_mul]
    have hWW : W ≤ W ^ 2 := by nlinarith
    calc
      W * (W + (k - 1) + 1) ^ (k - 1) ≤
          W ^ 2 * (W + (k - 1) + 1) ^ (k - 1) := by gcongr
      _ = W ^ 2 * (k - 1 + W + 1) ^ (k - 1) := by
        congr 2
        omega
  have hnorm := generalizedParkingGood_card_bound_of_succ_pow
    k 1 W hk (by omega) hk hW hforest
  simpa only [one_mul] using hnorm

/-- The elementary normalization of the Raney/cycle form of the count.
The factor `k - U + 1` is the number of occupancy blocks after the first
`W` boxes have been collapsed to one block. -/
theorem generalizedParkingGood_card_bound_of_cycle
    (k U W : ℕ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hUk : U ≤ k) (hW : 1 ≤ W)
    (hcycle :
      (k - U + 1) *
          (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
        U * W * (k - U + W + 1) ^ k) :
    k * (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
      256 * U * W ^ 2 * (k - U + W) ^ k := by
  have hblocks : 1 ≤ k - U + 1 := by omega
  have hbase : k - U + W + 1 ≤ 2 * W * (k - U + 1) := by
    nlinarith
  have hkpred : k - 1 + 1 = k := by omega
  have hcycle' :
      (k - U + 1) *
          (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
        (k - U + 1) *
          (2 * U * W ^ 2 * (k - U + W + 1) ^ (k - 1)) := by
    calc
      (k - U + 1) *
            (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
          U * W * (k - U + W + 1) ^ k := hcycle
      _ = U * W * ((k - U + W + 1) ^ (k - 1) *
            (k - U + W + 1)) := by
          rw [← pow_succ, hkpred]
      _ ≤ U * W * ((k - U + W + 1) ^ (k - 1) *
            (2 * W * (k - U + 1))) := by gcongr
      _ = (k - U + 1) *
            (2 * U * W ^ 2 * (k - U + W + 1) ^ (k - 1)) := by ring
  have hforest :
      (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
        2 * U * W ^ 2 * (k - U + W + 1) ^ (k - 1) := by
    exact Nat.le_of_mul_le_mul_left hcycle' hblocks
  by_cases hsmall : k ≤ 256 * U * W ^ 2
  · calc
      k * (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
          k * (k - U + W) ^ k :=
        Nat.mul_le_mul_left k (generalizedParkingGood_card_le_pow k U W)
      _ ≤ 256 * U * W ^ 2 * (k - U + W) ^ k :=
        Nat.mul_le_mul_right ((k - U + W) ^ k) hsmall
  · have hWsq : 1 ≤ W ^ 2 := Nat.one_le_pow 2 W hW
    have h2U : 2 * U ≤ k := by
      have : 256 * U < k := by
        calc
          256 * U = 256 * U * 1 := by ring
          _ ≤ 256 * U * W ^ 2 := by gcongr
          _ < k := Nat.lt_of_not_ge hsmall
      omega
    let V := k - U + W
    have hV : 1 ≤ V := by dsimp [V]; omega
    have hkV : k ≤ 2 * V := by dsimp [V]; omega
    have hexp : k - 1 ≤ 2 * V := (Nat.sub_le k 1).trans hkV
    have hsucc := succ_pow_le_nine_mul_pow hV hexp
    have hk256V : 18 * k ≤ 256 * V := by omega
    calc
      k * (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
          k * (2 * U * W ^ 2 * (V + 1) ^ (k - 1)) := by
        simpa [V, add_assoc] using Nat.mul_le_mul_left k hforest
      _ ≤ k * (2 * U * W ^ 2 * (9 * V ^ (k - 1))) := by gcongr
      _ = (18 * k) * U * W ^ 2 * V ^ (k - 1) := by ring
      _ ≤ (256 * V) * U * W ^ 2 * V ^ (k - 1) := by gcongr
      _ = 256 * U * W ^ 2 * V ^ k := by
        have hpow : V ^ k = V ^ (k - 1) * V := by
          conv_lhs => rw [← hkpred]
          exact pow_succ V (k - 1)
        rw [hpow]
        ring
      _ = 256 * U * W ^ 2 * (k - U + W) ^ k := by rfl

/-- The exact grid identity turns any normalized continuous `orderQ` estimate
at integral parameters into the corresponding finite parking-word estimate. -/
theorem generalizedParkingGood_card_bound_of_orderQ
    (A k U W : ℕ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hUk : U ≤ k) (hW : 1 ≤ W)
    (hQ : orderQ k (U : ℝ) (k - U + W : ℕ) ≤
      (A : ℝ) * (U : ℝ) * (W : ℝ) ^ 2 / (k : ℝ)) :
    k * (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
      A * U * W ^ 2 * (k - U + W) ^ k := by
  let V := k - U + W
  let C := (Finset.univ.filter (@generalizedParkingGood k U W)).card
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hV : 1 ≤ V := by dsimp [V]; omega
  have hVR : (0 : ℝ) < V := by exact_mod_cast hV
  have hfrac : (C : ℝ) / (V : ℝ) ^ k ≤
      (A : ℝ) * (U : ℝ) * (W : ℝ) ^ 2 / (k : ℝ) := by
    rw [generalizedParkingGood_div_pow_eq_orderQ k U W hU hUk hW]
    simpa [V] using hQ
  have hscaled := mul_le_mul_of_nonneg_left hfrac
    (mul_nonneg hkR.le (pow_nonneg hVR.le k))
  have hreal : (k : ℝ) * (C : ℝ) ≤
      (A : ℝ) * (U : ℝ) * (W : ℝ) ^ 2 * (V : ℝ) ^ k := by
    calc
      (k : ℝ) * (C : ℝ) =
          ((k : ℝ) * (V : ℝ) ^ k) * ((C : ℝ) / (V : ℝ) ^ k) := by
            field_simp
      _ ≤ ((k : ℝ) * (V : ℝ) ^ k) *
          ((A : ℝ) * (U : ℝ) * (W : ℝ) ^ 2 / (k : ℝ)) := hscaled
      _ = (A : ℝ) * (U : ℝ) * (W : ℝ) ^ 2 * (V : ℝ) ^ k := by
        field_simp
  exact_mod_cast hreal

/-- Uniform finite generalized-parking estimate.  Reversal and the Abel
first-violation identity above identify the event; Ford's direct
first-crossing estimate supplies its normalized tail bound. -/
theorem generalizedParkingGood_card_bound
    (k U W : ℕ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hUk : U ≤ k) (hW : 1 ≤ W) :
    k * (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
      1024 * U * W ^ 2 * (k - U + W) ^ k := by
  have hUshift : U + 1 ≤ 2 * U := by omega
  have hWshift : W + 1 ≤ 2 * W := by omega
  have hshift : 128 * (U + 1) * (W + 1) ^ 2 ≤ 1024 * U * W ^ 2 := by
    calc
      128 * (U + 1) * (W + 1) ^ 2 ≤
          128 * (2 * U) * (2 * W) ^ 2 := by gcongr
      _ = 1024 * U * W ^ 2 := by ring
  have hv : ((k - U + W : ℕ) : ℝ) =
      (k : ℝ) - (U : ℝ) + (W : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub hUk]
  have hexcess : (U : ℝ) + (k - U + W : ℕ) - (k : ℝ) = (W : ℝ) := by
    rw [hv]
    ring
  have hQshift := ford_orderQ_direct_bound k (U : ℝ) (k - U + W : ℕ)
    hk (by positivity) (by rw [hexcess]; positivity)
  rw [hexcess] at hQshift
  have hshiftR :
      128 * ((U : ℝ) + 1) * ((W : ℝ) + 1) ^ 2 ≤
        1024 * (U : ℝ) * (W : ℝ) ^ 2 := by
    exact_mod_cast hshift
  have hkR : (0 : ℝ) ≤ k := by positivity
  have hQ : orderQ k (U : ℝ) (k - U + W : ℕ) ≤
      1024 * (U : ℝ) * (W : ℝ) ^ 2 / (k : ℝ) :=
    hQshift.trans (div_le_div_of_nonneg_right hshiftR hkR)
  exact generalizedParkingGood_card_bound_of_orderQ
    1024 k U W hk hU hUk hW hQ

/-- Abel-remainder form of `generalizedParkingGood_card_bound`.  This is
the explicit first-violation tail estimate, independent of the predicate
presentation of the parking words. -/
theorem parkingAbel_remainder_bound
    (k U W : ℕ) (hk : 1 ≤ k) (hU : 1 ≤ U) (hUk : U ≤ k) (hW : 1 ≤ W) :
    k * ((k - U + W) ^ k -
      ∑ j ∈ Finset.range (k - U + 1),
        k.choose j * parkingAbelP j W * (k - U - j) ^ (k - j)) ≤
      1024 * U * W ^ 2 * (k - U + W) ^ k := by
  rw [← generalizedParkingGood_card_eq_abelRemainder hU hUk]
  exact generalizedParkingGood_card_bound k U W hk hU hUk hW

end Erdos896.Ford
