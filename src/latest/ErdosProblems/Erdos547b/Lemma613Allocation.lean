/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma65
import ErdosProblems.Erdos547b.Lemma613

/-!
# Finite capacity allocation for Zhao's Lemma 6.13

The efficient-subset lemma below is the denominator-sensitive selection
needed in the large-`f_b` argument. It reuses the proved finite allocation
theorem (Fact 6.4). No tree-embedding implication is an assumption here.
See the inequalities (EFF) and (LA) in `tex/547.tex`.
-/

open scoped BigOperators
noncomputable section

namespace Erdos547b.ZhaoLemma613Allocation

open Finset
open Erdos547b.ZhaoLemma65
open Erdos547b.ZhaoStability

/-- A prescribed amount of the second row can be selected at a cost in the
first row at most its proportional share, with one summand of overshoot.
The zero first-row and whole-set cases are included. -/
theorem exists_efficient_subset_univ
    {E : Type*} [Fintype E] [DecidableEq E]
    (a b : E → ℝ) (C q : ℝ)
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e)
    (haC : ∀ e, a e ≤ C) (hbC : ∀ e, b e ≤ C)
    (hC : 0 < C) (hq : 0 < q) (hqB : q ≤ ∑ e, b e) :
    ∃ P : Finset E, q ≤ ∑ e ∈ P, b e ∧
      (∑ e ∈ P, a e) ≤ (∑ e, a e) * (q + C) / (∑ e, b e) := by
  let A : ℝ := ∑ e, a e
  let B : ℝ := ∑ e, b e
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun e _ ↦ ha e
  have hB : 0 < B := hq.trans_le hqB
  by_cases hsmall : B ≤ q + C
  · refine ⟨Finset.univ, hqB, ?_⟩
    change A ≤ A * (q + C) / B
    apply (le_div_iff₀ hB).2
    exact mul_le_mul_of_nonneg_left hsmall hA0
  by_cases hAzero : A = 0
  · refine ⟨Finset.univ, hqB, ?_⟩
    change A ≤ A * (q + C) / B
    simp [hAzero]
  have hA : 0 < A := by
    rcases lt_or_eq_of_le hA0 with h | h
    · exact h
    · exact (hAzero h.symm).elim
  let r : ℝ := q + C
  let u : ℝ := A * (1 - r / B)
  have hr : 0 < r := add_pos hq hC
  have hrB : r < B := lt_of_not_ge hsmall
  have hu : 0 < u :=
    mul_pos hA (sub_pos.mpr ((div_lt_one hB).2 hrB))
  have hratio : r / B + u / A ≤ 1 := by
    dsimp only [u]
    rw [mul_div_cancel_left₀ _ hA.ne']
    linarith
  obtain ⟨P, Q, hPQ, hcover, hlower, _hupper, hQ⟩ :=
    zhaoFact6_4 b a C B A r u hb ha hbC haC rfl rfl hB hA hr hu hratio
  have hsum : (∑ e ∈ P, a e) + (∑ e ∈ Q, a e) = A := by
    rw [← Finset.sum_union hPQ, hcover]
  refine ⟨P, ?_, ?_⟩
  · dsimp only [r] at hlower
    linarith
  · change (∑ e ∈ P, a e) ≤ A * (q + C) / B
    calc
      (∑ e ∈ P, a e) ≤ A - u := by linarith
      _ = A * (q + C) / B := by
        dsimp only [u, r]
        ring

/-- The efficient-subset lemma on an arbitrary finite edge set. -/
theorem exists_efficient_subset
    {E : Type*} [DecidableEq E]
    (M : Finset E) (a b : E → ℝ) (C q : ℝ)
    (ha : ∀ e ∈ M, 0 ≤ a e) (hb : ∀ e ∈ M, 0 ≤ b e)
    (haC : ∀ e ∈ M, a e ≤ C) (hbC : ∀ e ∈ M, b e ≤ C)
    (hC : 0 < C) (hq : 0 < q) (hqB : q ≤ ∑ e ∈ M, b e) :
    ∃ P ⊆ M, q ≤ ∑ e ∈ P, b e ∧
      (∑ e ∈ P, a e) ≤ (∑ e ∈ M, a e) * (q + C) / (∑ e ∈ M, b e) := by
  have hsum (w : E → ℝ) : (∑ e : M, w e) = ∑ e ∈ M, w e := by
    rw [Finset.univ_eq_attach, Finset.sum_attach]
  obtain ⟨P, hPq, hPa⟩ := exists_efficient_subset_univ
    (fun e : M ↦ a e) (fun e : M ↦ b e) C q
    (fun e ↦ ha e e.property) (fun e ↦ hb e e.property)
    (fun e ↦ haC e e.property) (fun e ↦ hbC e e.property)
    hC hq (by simpa only [hsum] using hqB)
  let Q : Finset E := P.image Subtype.val
  have hQ : Q ⊆ M := by
    intro e he
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp he
    exact x.property
  have hQP (w : E → ℝ) : (∑ e ∈ Q, w e) = ∑ e ∈ P, w e := by
    apply Finset.sum_image
    intro x _hx y _hy hxy
    exact Subtype.ext hxy
  refine ⟨Q, hQ, ?_, ?_⟩
  · simpa only [hQP] using hPq
  · simpa only [hQP, hsum] using hPa

/-- An excess on a submatching pays for the deficient total degree and the
two forest reserves. This is the actual finite allocation step in Lemma 6.13,
not a hypothesis asserting that a large excess already embeds the tree. -/
theorem exists_allocation_of_excess_on_subset
    {E : Type*} [DecidableEq E]
    (M S : Finset E) (a b : E → ℝ)
    (n δ t lam fa fb s C : ℝ)
    (hSM : S ⊆ M)
    (ha : ∀ e ∈ S, 0 ≤ a e) (hb : ∀ e ∈ S, 0 ≤ b e)
    (haC : ∀ e ∈ S, a e ≤ C) (hbC : ∀ e ∈ S, b e ≤ C)
    (hC : 0 < C) (hn : 0 ≤ n) (ht : 0 ≤ t) (hlam : 0 ≤ lam)
    (hfb : 0 < fb) (hs : 0 ≤ s)
    (hA : (∑ e ∈ M, a e) = (1 - δ) * n)
    (hB : (∑ e ∈ S, b e) ≤ n)
    (htarget : fb + s ≤ ∑ e ∈ S, b e)
    (hexcess : lam * n ≤ (∑ e ∈ S, b e) - ∑ e ∈ S, a e)
    (hfbLower : t * n ≤ fb) (hforest : fa + fb ≤ n)
    (hbudget : δ * n + 2 * s + C ≤ t * lam * n) :
    ∃ P ⊆ S, fb + s ≤ ∑ e ∈ P, b e ∧
      fa + s ≤ ∑ e ∈ M \ P, a e := by
  have hq : 0 < fb + s := add_pos_of_pos_of_nonneg hfb hs
  have hBpos : 0 < ∑ e ∈ S, b e := hq.trans_le htarget
  obtain ⟨P, hPS, hPq, hPa⟩ :=
    exists_efficient_subset S a b C (fb + s) ha hb haC hbC hC hq htarget
  have hscale : t * (∑ e ∈ S, b e) ≤ fb + s + C := by
    calc
      t * (∑ e ∈ S, b e) ≤ t * n := mul_le_mul_of_nonneg_left hB ht
      _ ≤ fb := hfbLower
      _ ≤ fb + s + C := by linarith
  have hsaving :
      t * lam * n * (∑ e ∈ S, b e) ≤
        ((∑ e ∈ S, b e) - ∑ e ∈ S, a e) * (fb + s + C) := by
    calc
      t * lam * n * (∑ e ∈ S, b e) =
          (lam * n) * (t * (∑ e ∈ S, b e)) := by ring
      _ ≤ (lam * n) * (fb + s + C) :=
        mul_le_mul_of_nonneg_left hscale (mul_nonneg hlam hn)
      _ ≤ ((∑ e ∈ S, b e) - ∑ e ∈ S, a e) * (fb + s + C) :=
        mul_le_mul_of_nonneg_right hexcess (by linarith)
  have hcost : (∑ e ∈ P, a e) ≤ fb + s + C - t * lam * n := by
    apply hPa.trans
    apply (div_le_iff₀ hBpos).2
    nlinarith only [hsaving]
  have hsum := Finset.sum_sdiff (hPS.trans hSM) (f := a)
  rw [hA] at hsum
  refine ⟨P, hPS, hPq, ?_⟩
  nlinarith only [hsum, hcost, hbudget, hforest]

/-- Equal-total rows with a large discrepancy yield the two forest
capacities in one of the two orientations. The submatching carrying the
excess and the allocation itself are both constructed in this proof. -/
theorem exists_allocation_or_swap_of_equal_totals
    {E : Type*} [DecidableEq E]
    (M S : Finset E) (a b : E → ℝ)
    (n δ t lam fa fb s C : ℝ)
    (hSM : S ⊆ M)
    (ha : ∀ e ∈ M, 0 ≤ a e) (hb : ∀ e ∈ M, 0 ≤ b e)
    (haC : ∀ e ∈ M, a e ≤ C) (hbC : ∀ e ∈ M, b e ≤ C)
    (hC : 0 < C) (hn : 0 ≤ n) (hδ : 0 ≤ δ)
    (ht : 0 ≤ t) (hlam : 0 ≤ lam) (hfb : 0 < fb) (hs : 0 ≤ s)
    (hA : (∑ e ∈ M, a e) = (1 - δ) * n)
    (hB : (∑ e ∈ M, b e) = (1 - δ) * n)
    (hdiscrepancy : lam * n ≤ |(∑ e ∈ S, a e) - ∑ e ∈ S, b e|)
    (hfbLower : t * n ≤ fb) (hfbHalf : fb ≤ n / 2)
    (hforest : fa + fb ≤ n)
    (hfirst : δ * n + 2 * s ≤ lam * n)
    (hbudget : δ * n + 2 * s + C ≤ t * lam * n) :
    (∃ P ⊆ M, fb + s ≤ ∑ e ∈ P, b e ∧ fa + s ≤ ∑ e ∈ M \ P, a e) ∨
    (∃ P ⊆ M, fb + s ≤ ∑ e ∈ P, a e ∧ fa + s ≤ ∑ e ∈ M \ P, b e) := by
  let P₀ := matchingPositivePart M a b
  let S₀ := M \ P₀
  have hP₀ : P₀ ⊆ M := matchingPositivePart_subset M a b
  have hS₀ : S₀ ⊆ M := Finset.sdiff_subset
  have hpositive : lam * n ≤ matchingPositiveExcess M a b :=
    hdiscrepancy.trans
      (abs_sum_difference_le_matchingPositiveExcess M S a b hSM (hA.trans hB.symm))
  have hEP : (∑ e ∈ P₀, a e) - (∑ e ∈ P₀, b e) =
      matchingPositiveExcess M a b := matchingPositivePart_attains_excess M a b
  have hsumA : (∑ e ∈ S₀, a e) + (∑ e ∈ P₀, a e) = (1 - δ) * n := by
    simpa only [S₀, hA] using (Finset.sum_sdiff hP₀ (f := a))
  have hsumB : (∑ e ∈ S₀, b e) + (∑ e ∈ P₀, b e) = (1 - δ) * n := by
    simpa only [S₀, hB] using (Finset.sum_sdiff hP₀ (f := b))
  have hES : (∑ e ∈ S₀, b e) - (∑ e ∈ S₀, a e) =
      matchingPositiveExcess M a b := by linarith
  have htotalUpper : (1 - δ) * n ≤ n := by
    nlinarith only [mul_nonneg hδ hn]
  by_cases hchoice : (∑ e ∈ P₀, a e) ≤ ∑ e ∈ S₀, b e
  · have htarget : fb + s ≤ ∑ e ∈ S₀, b e := by
      nlinarith only [hsumA, hES, hpositive, hchoice, hfirst, hfbHalf]
    have hbound : (∑ e ∈ S₀, b e) ≤ n := by
      calc
        (∑ e ∈ S₀, b e) ≤ ∑ e ∈ M, b e :=
          Finset.sum_le_sum_of_subset_of_nonneg hS₀ (fun e he _ ↦ hb e he)
        _ ≤ n := hB.trans_le htotalUpper
    obtain ⟨P, hPS, hPb, hPa⟩ := exists_allocation_of_excess_on_subset
      M S₀ a b n δ t lam fa fb s C hS₀
      (fun e he ↦ ha e (hS₀ he)) (fun e he ↦ hb e (hS₀ he))
      (fun e he ↦ haC e (hS₀ he)) (fun e he ↦ hbC e (hS₀ he))
      hC hn ht hlam hfb hs hA hbound htarget
      (by rw [hES]; exact hpositive) hfbLower hforest hbudget
    exact Or.inl ⟨P, hPS.trans hS₀, hPb, hPa⟩
  · have htarget : fb + s ≤ ∑ e ∈ P₀, a e := by
      have hchoice' := le_of_lt (lt_of_not_ge hchoice)
      nlinarith only [hsumB, hEP, hpositive, hchoice', hfirst, hfbHalf]
    have hbound : (∑ e ∈ P₀, a e) ≤ n := by
      calc
        (∑ e ∈ P₀, a e) ≤ ∑ e ∈ M, a e :=
          Finset.sum_le_sum_of_subset_of_nonneg hP₀ (fun e he _ ↦ ha e he)
        _ ≤ n := hA.trans_le htotalUpper
    obtain ⟨P, hPP, hPa, hPb⟩ := exists_allocation_of_excess_on_subset
      M P₀ b a n δ t lam fa fb s C hP₀
      (fun e he ↦ hb e (hP₀ he)) (fun e he ↦ ha e (hP₀ he))
      (fun e he ↦ hbC e (hP₀ he)) (fun e he ↦ haC e (hP₀ he))
      hC hn ht hlam hfb hs hB hbound htarget
      (by rw [hEP]; exact hpositive) hfbLower hforest hbudget
    exact Or.inr ⟨P, hPP.trans hP₀, hPa, hPb⟩

/-- A row whose total already exceeds the tree order by `t*n` supports the
larger forest. This case is essential before normalizing both raw rows. -/
theorem exists_allocation_of_large_total
    {E : Type*} [DecidableEq E]
    (M : Finset E) (a b : E → ℝ)
    (n δ t fa fb s C : ℝ)
    (ha : ∀ e ∈ M, 0 ≤ a e) (hb : ∀ e ∈ M, 0 ≤ b e)
    (haC : ∀ e ∈ M, a e ≤ C) (hbC : ∀ e ∈ M, b e ≤ C)
    (hC : 0 < C) (hn : 0 < n) (hδ : 0 ≤ δ) (hδone : δ < 1)
    (ht : 0 ≤ t) (hfb : 0 < fb) (hs : 0 ≤ s)
    (hA : (1 + t) * n ≤ ∑ e ∈ M, a e)
    (hB : (1 - δ) * n ≤ ∑ e ∈ M, b e)
    (hfbHalf : fb ≤ n / 2) (hforest : fa + fb ≤ n)
    (hroom : fb + s + C < (1 - δ) * n)
    (hbudget : (2 + t - δ) * s + (1 + t) * C ≤
      (t / 2 - δ / 2 - t * δ) * n) :
    ∃ P ⊆ M, fb + s ≤ ∑ e ∈ P, b e ∧
      fa + s ≤ ∑ e ∈ M \ P, a e := by
  let A : ℝ := ∑ e ∈ M, a e
  let B : ℝ := ∑ e ∈ M, b e
  let D : ℝ := (1 - δ) * n
  let r : ℝ := fb + s + C
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun e he ↦ ha e he
  have hD : 0 < D := mul_pos (sub_pos.mpr hδone) hn
  have hBpos : 0 < B := hD.trans_le hB
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hq : 0 < fb + s := add_pos_of_pos_of_nonneg hfb hs
  have hqB : fb + s ≤ ∑ e ∈ M, b e := by linarith
  obtain ⟨P, hPM, hPq, hPa⟩ :=
    exists_efficient_subset M a b C (fb + s) ha hb haC hbC hC hq hqB
  have hsum : (∑ e ∈ M \ P, a e) + (∑ e ∈ P, a e) = A :=
    Finset.sum_sdiff hPM
  have hratio : r / B ≤ r / D := div_le_div_of_nonneg_left hr hD hB
  have hfactor : 0 ≤ 1 - r / D := by
    have hrD : r / D ≤ 1 := (div_le_one hD).2 hroom.le
    linarith
  have hnum : (n - fb + s) * (1 - δ) ≤
      (1 + t) * ((1 - δ) * n - r) := by
    have hhalf : 0 ≤ (t + δ) * (n / 2 - fb) :=
      mul_nonneg (add_nonneg ht hδ) (sub_nonneg.mpr hfbHalf)
    dsimp only [r]
    nlinarith only [hbudget, hhalf]
  have hscalar : n - fb + s ≤ (1 + t) * n * (1 - r / D) := by
    have heq : (1 + t) * n * (1 - r / D) =
        (1 + t) * ((1 - δ) * n - r) / (1 - δ) := by
      dsimp only [D]
      field_simp [hn.ne', (sub_pos.mpr hδone).ne']
    rw [heq]
    exact (le_div_iff₀ (sub_pos.mpr hδone)).2 hnum
  refine ⟨P, hPM, hPq, ?_⟩
  calc
    fa + s ≤ n - fb + s := by linarith only [hforest]
    _ ≤ (1 + t) * n * (1 - r / D) := hscalar
    _ ≤ A * (1 - r / D) := mul_le_mul_of_nonneg_right hA hfactor
    _ ≤ A * (1 - r / B) := by
      apply mul_le_mul_of_nonneg_left _ hA0
      linarith only [hratio]
    _ ≤ ∑ e ∈ M \ P, a e := by
      change (∑ e ∈ P, a e) ≤ A * r / B at hPa
      have heq : A * (1 - r / B) = A - A * r / B := by ring
      rw [heq]
      linarith only [hsum, hPa]

/-- Reducing each of two quantities by an amount in `[0,u]` changes their
absolute difference by at most `u`, not the weaker bound `2*u`. -/
theorem abs_difference_le_of_bounded_reductions
    {x y x' y' u : ℝ}
    (hx : 0 ≤ x - x') (hy : 0 ≤ y - y')
    (hxu : x - x' ≤ u) (hyu : y - y' ≤ u) :
    |x - y| ≤ |x' - y'| + u := by
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (x' - y')]
  · linarith [le_abs_self (x' - y')]

/-- Real capacity normalization; it does not delete fractional graph edges. -/
def normalizedRow {E : Type*} (M : Finset E) (a : E → ℝ) (D : ℝ) : E → ℝ :=
  fun e ↦ (D / ∑ i ∈ M, a i) * a e

/-- Normalization preserves a positive prescribed total, decreases every
entry, and decreases each submatching sum by at most the total row loss. -/
theorem normalizedRow_spec
    {E : Type*} [DecidableEq E]
    (M : Finset E) (a : E → ℝ) (D : ℝ)
    (ha : ∀ e ∈ M, 0 ≤ a e) (hD : 0 < D) (hDA : D ≤ ∑ e ∈ M, a e) :
    (∀ e ∈ M, 0 ≤ normalizedRow M a D e ∧ normalizedRow M a D e ≤ a e) ∧
    (∑ e ∈ M, normalizedRow M a D e) = D ∧
    ∀ S ⊆ M, 0 ≤ (∑ e ∈ S, a e) - ∑ e ∈ S, normalizedRow M a D e ∧
      (∑ e ∈ S, a e) - (∑ e ∈ S, normalizedRow M a D e) ≤
        (∑ e ∈ M, a e) - D := by
  have hA : 0 < ∑ e ∈ M, a e := hD.trans_le hDA
  have hfactor : D / (∑ e ∈ M, a e) ≤ 1 := (div_le_one hA).2 hDA
  have hentry : ∀ e ∈ M,
      0 ≤ normalizedRow M a D e ∧ normalizedRow M a D e ≤ a e := by
    intro e he
    refine ⟨mul_nonneg (div_nonneg hD.le hA.le) (ha e he), ?_⟩
    calc
      normalizedRow M a D e ≤ 1 * a e :=
        mul_le_mul_of_nonneg_right hfactor (ha e he)
      _ = a e := one_mul _
  have htotal : (∑ e ∈ M, normalizedRow M a D e) = D := by
    simp only [normalizedRow, ← Finset.mul_sum]
    exact div_mul_cancel₀ D hA.ne'
  refine ⟨hentry, htotal, ?_⟩
  intro S hSM
  have hnonneg : ∀ e ∈ M, 0 ≤ a e - normalizedRow M a D e :=
    fun e he ↦ sub_nonneg.mpr (hentry e he).2
  constructor
  · rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun e he ↦ hnonneg e (hSM he)
  · calc
      (∑ e ∈ S, a e) - (∑ e ∈ S, normalizedRow M a D e) =
          ∑ e ∈ S, (a e - normalizedRow M a D e) := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ e ∈ M, (a e - normalizedRow M a D e) :=
        Finset.sum_le_sum_of_subset_of_nonneg hSM (fun e he _ ↦ hnonneg e he)
      _ = (∑ e ∈ M, a e) - D := by rw [Finset.sum_sub_distrib, htotal]

/-- Raw-row version of the large-`f_b` allocation, including the cases in
which one total is too large to normalize without losing its discrepancy.
This proves the finite matching content of Lemma 6.13 from lower bounds on
the original row totals. -/
theorem exists_allocation_or_swap_of_raw_discrepancy
    {E : Type*} [DecidableEq E]
    (M S : Finset E) (a b : E → ℝ)
    (n δ t fa fb s C : ℝ)
    (hSM : S ⊆ M)
    (ha : ∀ e ∈ M, 0 ≤ a e) (hb : ∀ e ∈ M, 0 ≤ b e)
    (haC : ∀ e ∈ M, a e ≤ C) (hbC : ∀ e ∈ M, b e ≤ C)
    (hC : 0 < C) (hn : 0 < n) (hδ : 0 ≤ δ) (hδone : δ < 1)
    (ht : 0 ≤ t) (hδt : δ ≤ t) (hfb : 0 < fb) (hs : 0 ≤ s)
    (hA : (1 - δ) * n ≤ ∑ e ∈ M, a e)
    (hB : (1 - δ) * n ≤ ∑ e ∈ M, b e)
    (hdiscrepancy : 15 * t * n ≤ |(∑ e ∈ S, a e) - ∑ e ∈ S, b e|)
    (hfbLower : t * n ≤ fb) (hfbHalf : fb ≤ n / 2)
    (hforest : fa + fb ≤ n)
    (hfirst : δ * n + 2 * s ≤ (13 * t) * n)
    (hbudget : δ * n + 2 * s + C ≤ t * (13 * t) * n)
    (hroom : fb + s + C < (1 - δ) * n)
    (hlargeBudget : (2 + t - δ) * s + (1 + t) * C ≤
      (t / 2 - δ / 2 - t * δ) * n) :
    (∃ P ⊆ M, fb + s ≤ ∑ e ∈ P, b e ∧ fa + s ≤ ∑ e ∈ M \ P, a e) ∨
    (∃ P ⊆ M, fb + s ≤ ∑ e ∈ P, a e ∧ fa + s ≤ ∑ e ∈ M \ P, b e) := by
  by_cases hlargeA : (1 + t) * n ≤ ∑ e ∈ M, a e
  · exact Or.inl (exists_allocation_of_large_total M a b n δ t fa fb s C
      ha hb haC hbC hC hn hδ hδone ht hfb hs hlargeA hB
      hfbHalf hforest hroom hlargeBudget)
  by_cases hlargeB : (1 + t) * n ≤ ∑ e ∈ M, b e
  · exact Or.inr (exists_allocation_of_large_total M b a n δ t fa fb s C
      hb ha hbC haC hC hn hδ hδone ht hfb hs hlargeB hA
      hfbHalf hforest hroom hlargeBudget)
  let D := (1 - δ) * n
  let a' := normalizedRow M a D
  let b' := normalizedRow M b D
  have hD : 0 < D := mul_pos (sub_pos.mpr hδone) hn
  obtain ⟨ha', htotalA', hlossA⟩ := normalizedRow_spec M a D ha hD hA
  obtain ⟨hb', htotalB', hlossB⟩ := normalizedRow_spec M b D hb hD hB
  have hAtop : (∑ e ∈ M, a e) - D ≤ (t + δ) * n := by
    have h := le_of_lt (lt_of_not_ge hlargeA)
    dsimp only [D]
    nlinarith only [h]
  have hBtop : (∑ e ∈ M, b e) - D ≤ (t + δ) * n := by
    have h := le_of_lt (lt_of_not_ge hlargeB)
    dsimp only [D]
    nlinarith only [h]
  have hperturb := abs_difference_le_of_bounded_reductions
    (hlossA S hSM).1 (hlossB S hSM).1
    ((hlossA S hSM).2.trans hAtop) ((hlossB S hSM).2.trans hBtop)
  have hdiscrepancy' : (13 * t) * n ≤ |(∑ e ∈ S, a' e) - ∑ e ∈ S, b' e| := by
    have hδn := mul_le_mul_of_nonneg_right hδt hn.le
    change |(∑ e ∈ S, a e) - ∑ e ∈ S, b e| ≤
      |(∑ e ∈ S, a' e) - ∑ e ∈ S, b' e| + (t + δ) * n at hperturb
    nlinarith only [hperturb, hdiscrepancy, hδn]
  have halloc := exists_allocation_or_swap_of_equal_totals M S a' b'
    n δ t (13 * t) fa fb s C hSM
    (fun e he ↦ (ha' e he).1) (fun e he ↦ (hb' e he).1)
    (fun e he ↦ (ha' e he).2.trans (haC e he))
    (fun e he ↦ (hb' e he).2.trans (hbC e he))
    hC hn.le hδ ht (by positivity) hfb hs htotalA' htotalB'
    hdiscrepancy' hfbLower hfbHalf hforest hfirst hbudget
  rcases halloc with ⟨P, hPM, hPb, hPa⟩ | ⟨P, hPM, hPa, hPb⟩
  · left
    refine ⟨P, hPM, hPb.trans ?_, hPa.trans ?_⟩
    · exact Finset.sum_le_sum fun e he ↦ (hb' e (hPM he)).2
    · exact Finset.sum_le_sum fun e he ↦ (ha' e (Finset.mem_sdiff.mp he).1).2
  · right
    refine ⟨P, hPM, hPa.trans ?_, hPb.trans ?_⟩
    · exact Finset.sum_le_sum fun e he ↦ (ha' e (hPM he)).2
    · exact Finset.sum_le_sum fun e he ↦ (hb' e (Finset.mem_sdiff.mp he).1).2

end Erdos547b.ZhaoLemma613Allocation

#print axioms Erdos547b.ZhaoLemma613Allocation.exists_efficient_subset_univ
#print axioms Erdos547b.ZhaoLemma613Allocation.exists_efficient_subset
#print axioms Erdos547b.ZhaoLemma613Allocation.exists_allocation_of_excess_on_subset
#print axioms Erdos547b.ZhaoLemma613Allocation.exists_allocation_or_swap_of_equal_totals
#print axioms Erdos547b.ZhaoLemma613Allocation.exists_allocation_of_large_total
#print axioms Erdos547b.ZhaoLemma613Allocation.abs_difference_le_of_bounded_reductions
#print axioms Erdos547b.ZhaoLemma613Allocation.normalizedRow_spec
#print axioms Erdos547b.ZhaoLemma613Allocation.exists_allocation_or_swap_of_raw_discrepancy
