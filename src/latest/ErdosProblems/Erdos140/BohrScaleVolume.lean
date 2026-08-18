/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos140.BourgainRegular

/-!
# Arbitrary-scale finite Bohr volume comparison

The four-cell argument in BourgainRegular is convenient at the fixed
scales 1 and 1 / 2. Here we record the same finite signature/fibre
argument at an arbitrary positive integral resolution.

For one coordinate of width w, the interval [-w,w] is split into
2m + 1 consecutive cells of diameter at most w / m. Equal signatures
therefore inject into the carrier at scale rho / m. The resulting bound
has no regularity, positivity-of-width, or ambient-size hypothesis:

|B_rho| <= (2m + 1)^rank(B) |B_(rho/m)|.

For later bookkeeping we also expose the cleaner, slightly weaker
(3m)^rank form, together with its real-valued exponential rewriting.
-/

open Finset
open scoped BigOperators NNReal

namespace Erdos140

noncomputable section

namespace BohrData

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Scaled interval cells -/

/-- A total coding of a real coordinate into 2m + 1 cells. On the interval
[-w,w] with 0 < w, the unclamped value is floor ((r+w)m/w); the outer min
only makes the definition total away from that interval. -/
def scaledCell (m : ℕ) (w r : ℝ) : Fin (2 * m + 1) :=
  ⟨min ⌊((r + w) * (m : ℝ)) / w⌋₊ (2 * m),
    Nat.lt_succ_iff.mpr (Nat.min_le_right _ _)⟩

/-- Points of [-w,w] in the same scaled cell are at distance at most
w / m. The case w = 0 is included, so no hidden positivity assumption
on Bohr widths is needed later. -/
lemma abs_sub_le_div_of_scaledCell_eq
    {m : ℕ} (hm : 0 < m) {w r s : ℝ}
    (hw : 0 ≤ w) (hr : |r| ≤ w) (hs : |s| ≤ w)
    (hcell : scaledCell m w r = scaledCell m w s) :
    |r - s| ≤ w / (m : ℝ) := by
  by_cases hw0 : w = 0
  · subst w
    have hr0 : r = 0 := by
      apply abs_eq_zero.mp
      exact le_antisymm hr (abs_nonneg r)
    have hs0 : s = 0 := by
      apply abs_eq_zero.mp
      exact le_antisymm hs (abs_nonneg s)
    simp [hr0, hs0]
  have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let ur : ℝ := ((r + w) * (m : ℝ)) / w
  let us : ℝ := ((s + w) * (m : ℝ)) / w
  have hr_bounds : -w ≤ r ∧ r ≤ w := (abs_le.mp hr)
  have hs_bounds : -w ≤ s ∧ s ≤ w := (abs_le.mp hs)
  have hur0 : 0 ≤ ur := by
    dsimp [ur]
    exact div_nonneg (mul_nonneg (by linarith) hmR.le) hw
  have hus0 : 0 ≤ us := by
    dsimp [us]
    exact div_nonneg (mul_nonneg (by linarith) hmR.le) hw
  have hur_le : ur ≤ (2 * m : ℕ) := by
    dsimp [ur]
    apply (div_le_iff₀ hwpos).2
    push_cast
    nlinarith
  have hus_le : us ≤ (2 * m : ℕ) := by
    dsimp [us]
    apply (div_le_iff₀ hwpos).2
    push_cast
    nlinarith
  have hfloor_r_lt : ⌊ur⌋₊ < 2 * m + 1 := by
    apply (Nat.floor_lt hur0).2
    exact lt_of_le_of_lt hur_le (by exact_mod_cast (Nat.lt_succ_self (2 * m)))
  have hfloor_s_lt : ⌊us⌋₊ < 2 * m + 1 := by
    apply (Nat.floor_lt hus0).2
    exact lt_of_le_of_lt hus_le (by exact_mod_cast (Nat.lt_succ_self (2 * m)))
  have hfloor_r_le : ⌊ur⌋₊ ≤ 2 * m := by omega
  have hfloor_s_le : ⌊us⌋₊ ≤ 2 * m := by omega
  have hfloor : ⌊ur⌋₊ = ⌊us⌋₊ := by
    have hval := congrArg Fin.val hcell
    simpa only [scaledCell, ur, us, Nat.min_eq_left hfloor_r_le,
      Nat.min_eq_left hfloor_s_le] using hval
  have hur_lower : ((⌊ur⌋₊ : ℕ) : ℝ) ≤ ur := Nat.floor_le hur0
  have hur_upper : ur < ((⌊ur⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one ur
  have hus_lower : ((⌊us⌋₊ : ℕ) : ℝ) ≤ us := Nat.floor_le hus0
  have hus_upper : us < ((⌊us⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one us
  have hur_lt_us_add : ur < us + 1 := by
    calc
      ur < ((⌊ur⌋₊ : ℕ) : ℝ) + 1 := hur_upper
      _ = ((⌊us⌋₊ : ℕ) : ℝ) + 1 := by rw [hfloor]
      _ ≤ us + 1 := by gcongr
  have hus_lt_ur_add : us < ur + 1 := by
    calc
      us < ((⌊us⌋₊ : ℕ) : ℝ) + 1 := hus_upper
      _ = ((⌊ur⌋₊ : ℕ) : ℝ) + 1 := by rw [← hfloor]
      _ ≤ ur + 1 := by gcongr
  have hur_sub_us :
      ur - us = ((r - s) * (m : ℝ)) / w := by
    dsimp [ur, us]
    field_simp
    ring
  have hquot_upper : ((r - s) * (m : ℝ)) / w < 1 := by
    rw [← hur_sub_us]
    linarith
  have hquot_lower : (-1 : ℝ) < ((r - s) * (m : ℝ)) / w := by
    rw [← hur_sub_us]
    linarith
  have hmul_upper : (r - s) * (m : ℝ) < w := by
    have h := (div_lt_iff₀ hwpos).mp hquot_upper
    simpa only [one_mul] using h
  have hmul_lower : -w < (r - s) * (m : ℝ) := by
    have h := (lt_div_iff₀ hwpos).mp hquot_lower
    simpa only [neg_one_mul] using h
  have hupper : r - s < w / (m : ℝ) :=
    (lt_div_iff₀ hmR).2 hmul_upper
  have hlower : -(w / (m : ℝ)) < r - s := by
    have h := (div_lt_iff₀ hmR).2 hmul_lower
    simpa only [neg_div] using h
  exact (abs_lt.2 ⟨hlower, hupper⟩).le

/-- The scaled-cell signature of a point in the rho-dilate. -/
def scaledSignature (B : BohrData G) (rho : NNReal) (m : ℕ)
    (x : ↥(B.dilate rho).carrier) : B.freq → Fin (2 * m + 1) :=
  fun γ ↦
    scaledCell m ((rho : ℝ) * (B.width γ.1 : ℝ))
      (circleRep (γ.1 x.1))

private lemma sub_mem_dilate_div_of_scaledSignature_eq
    (B : BohrData G) (rho : NNReal) {m : ℕ} (hm : 0 < m)
    {x y : ↥(B.dilate rho).carrier}
    (hxy : B.scaledSignature rho m x = B.scaledSignature rho m y) :
    x.1 - y.1 ∈ (B.dilate (rho / (m : NNReal))).carrier := by
  rw [mem_carrier]
  intro γ hγ
  have hx := (mem_carrier (B.dilate rho) x.1).mp x.2 γ hγ
  have hy := (mem_carrier (B.dilate rho) y.1).mp y.2 γ hγ
  simp only [width_dilate, NNReal.coe_mul] at hx hy ⊢
  rw [map_sub]
  have hxrep :
      |circleRep (γ x.1)| ≤ (rho : ℝ) * (B.width γ : ℝ) := by
    rwa [← norm_eq_abs_circleRep]
  have hyrep :
      |circleRep (γ y.1)| ≤ (rho : ℝ) * (B.width γ : ℝ) := by
    rwa [← norm_eq_abs_circleRep]
  have hcoord := congrFun hxy ⟨γ, hγ⟩
  have hdiv := abs_sub_le_div_of_scaledCell_eq hm
    (mul_nonneg (by positivity) (by positivity)) hxrep hyrep hcoord
  calc
    ‖γ x.1 - γ y.1‖ ≤
        |circleRep (γ x.1) - circleRep (γ y.1)| :=
      norm_sub_le_abs_circleRep_sub _ _
    _ ≤ ((rho : ℝ) * (B.width γ : ℝ)) / (m : ℝ) := hdiv
    _ = ((rho / (m : NNReal) : NNReal) : ℝ) *
        (B.width γ : ℝ) := by
      push_cast
      field_simp

private lemma card_scaledSignature_fiber_le
    (B : BohrData G) (rho : NNReal) {m : ℕ} (hm : 0 < m)
    (a : B.freq → Fin (2 * m + 1)) :
    Fintype.card
        {x : ↥(B.dilate rho).carrier // B.scaledSignature rho m x = a} ≤
      (B.dilate (rho / (m : NNReal))).carrier.card := by
  classical
  by_cases hfiber : Nonempty
      {x : ↥(B.dilate rho).carrier // B.scaledSignature rho m x = a}
  · let x₀ :
        {x : ↥(B.dilate rho).carrier // B.scaledSignature rho m x = a} :=
      Classical.choice hfiber
    let f :
        {x : ↥(B.dilate rho).carrier // B.scaledSignature rho m x = a} →
          ↥(B.dilate (rho / (m : NNReal))).carrier :=
      fun x ↦
        ⟨x.1.1 - x₀.1.1,
          sub_mem_dilate_div_of_scaledSignature_eq B rho hm
            (x.2.trans x₀.2.symm)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      have hval := congrArg Subtype.val hxy
      dsimp [f] at hval
      exact sub_left_injective hval
    calc
      Fintype.card
          {x : ↥(B.dilate rho).carrier // B.scaledSignature rho m x = a} ≤
          Fintype.card ↥(B.dilate (rho / (m : NNReal))).carrier :=
        Fintype.card_le_of_injective f hf
      _ = (B.dilate (rho / (m : NNReal))).carrier.card :=
        Fintype.card_coe _
  · simp only [not_nonempty_iff] at hfiber
    simp

/-! ## Volume comparison -/

/-- Arbitrary-scale relative volume growth for a finite Bohr carrier.
Shrinking a scale by a positive integer m costs at most
(2m+1)^rank. -/
theorem card_dilate_le_two_mul_add_one_pow_rank_mul_card_div
    (B : BohrData G) (rho : NNReal) {m : ℕ} (hm : 0 < m) :
    (B.dilate rho).carrier.card ≤
      (2 * m + 1) ^ B.rank *
        (B.dilate (rho / (m : NNReal))).carrier.card := by
  classical
  let S := B.freq → Fin (2 * m + 1)
  let q : ↥(B.dilate rho).carrier → S := B.scaledSignature rho m
  have hfiber : ∀ a : S,
      Fintype.card {x : ↥(B.dilate rho).carrier // q x = a} ≤
        (B.dilate (rho / (m : NNReal))).carrier.card := by
    intro a
    exact card_scaledSignature_fiber_le B rho hm a
  have hcardS : Fintype.card S = (2 * m + 1) ^ B.rank := by
    dsimp [S, rank]
    rw [Fintype.card_pi]
    simp
  rw [← Fintype.card_coe (B.dilate rho).carrier, ← hcardS]
  by_contra h
  have hlt :
      Fintype.card S * (B.dilate (rho / (m : NNReal))).carrier.card <
        Fintype.card ↥(B.dilate rho).carrier := by omega
  obtain ⟨a, ha⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := q) hlt
  have hfa : #{x | q x = a} ≤
      (B.dilate (rho / (m : NNReal))).carrier.card := by
    rw [← Fintype.card_subtype]
    exact hfiber a
  exact (not_lt_of_ge hfa) ha

/-- A cleaner bookkeeping form of the arbitrary-scale volume estimate. -/
theorem card_dilate_le_three_mul_pow_rank_mul_card_div
    (B : BohrData G) (rho : NNReal) {m : ℕ} (hm : 0 < m) :
    (B.dilate rho).carrier.card ≤
      (3 * m) ^ B.rank *
        (B.dilate (rho / (m : NNReal))).carrier.card := by
  calc
    (B.dilate rho).carrier.card ≤
        (2 * m + 1) ^ B.rank *
          (B.dilate (rho / (m : NNReal))).carrier.card :=
      card_dilate_le_two_mul_add_one_pow_rank_mul_card_div B rho hm
    _ ≤ (3 * m) ^ B.rank *
          (B.dilate (rho / (m : NNReal))).carrier.card := by
      apply Nat.mul_le_mul_right
      apply Nat.pow_le_pow_left
      omega

/-- Real-valued form of the clean arbitrary-scale comparison. -/
theorem card_dilate_real_le_three_mul_pow_rank_mul_card_div
    (B : BohrData G) (rho : NNReal) {m : ℕ} (hm : 0 < m) :
    ((B.dilate rho).carrier.card : ℝ) ≤
      ((3 * m : ℕ) : ℝ) ^ B.rank *
        ((B.dilate (rho / (m : NNReal))).carrier.card : ℝ) := by
  exact_mod_cast card_dilate_le_three_mul_pow_rank_mul_card_div B rho hm

/-- Exponential rewriting of the real-valued arbitrary-scale comparison. -/
theorem card_dilate_real_le_exp_rank_log_mul_card_div
    (B : BohrData G) (rho : NNReal) {m : ℕ} (hm : 0 < m) :
    ((B.dilate rho).carrier.card : ℝ) ≤
      Real.exp ((B.rank : ℝ) * Real.log ((3 * m : ℕ) : ℝ)) *
        ((B.dilate (rho / (m : NNReal))).carrier.card : ℝ) := by
  have hreal := card_dilate_real_le_three_mul_pow_rank_mul_card_div B rho hm
  have hbase : (0 : ℝ) < ((3 * m : ℕ) : ℝ) := by
    positivity
  have hpow :
      (((3 * m : ℕ) : ℝ) ^ B.rank) =
        Real.exp ((B.rank : ℝ) * Real.log ((3 * m : ℕ) : ℝ)) := by
    conv_lhs =>
      rw [← Real.exp_log hbase, ← Real.exp_nat_mul]
  simpa only [hpow] using hreal

end BohrData

end

end Erdos140

#print axioms Erdos140.BohrData.card_dilate_le_two_mul_add_one_pow_rank_mul_card_div
#print axioms Erdos140.BohrData.card_dilate_le_three_mul_pow_rank_mul_card_div
#print axioms Erdos140.BohrData.card_dilate_real_le_exp_rank_log_mul_card_div
