import ErdosProblems.Erdos239.External.Erdos67.Entropy
import Mathlib.Analysis.Convex.Jensen

/-!
# Finite Pinsker inequality

An explicit finite proof of Pinsker's inequality for the probability vectors used by entropy
decrement.  The proof first establishes the sharp Bernoulli inequality by convexity, and then
coarse-grains along the positive part of `p - q`.
-/

open scoped BigOperators ENNReal NNReal
open Finset MeasureTheory

namespace Erdos67
namespace FiniteEntropy

noncomputable section

def binaryKLDivergence (p q : ℝ) : ℝ :=
  -Real.negMulLog p - Real.negMulLog (1 - p) -
    p * Real.log q - (1 - p) * Real.log (1 - q)

theorem binaryKLDivergence_pinsker
    {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ binaryKLDivergence p q := by
  let F : ℝ → ℝ := fun x => binaryKLDivergence x q - 2 * (x - q) ^ 2
  let F' : ℝ → ℝ := fun x =>
    Real.log x - Real.log (1 - x) - Real.log q + Real.log (1 - q) - 4 * (x - q)
  let F'' : ℝ → ℝ := fun x => x⁻¹ + (1 - x)⁻¹ - 4
  have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    unfold F binaryKLDivergence
    fun_prop
  have hF' : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt F (F' x) (interior (Set.Icc (0 : ℝ) 1)) x := by
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hx1 : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
    unfold F F' binaryKLDivergence
    have hA : HasDerivAt (fun y : ℝ => -Real.negMulLog y) (Real.log x + 1) x := by
      convert (Real.hasDerivAt_negMulLog hx0).neg using 1
      all_goals try rfl
      all_goals ring
    have hB : HasDerivAt (fun y : ℝ => Real.negMulLog (1 - y))
        (Real.log (1 - x) + 1) x := by
      convert (Real.hasDerivAt_negMulLog hx1).comp x
        ((hasDerivAt_const x 1).sub (hasDerivAt_id x)) using 1
      all_goals try rfl
      all_goals ring
    have hC : HasDerivAt (fun y : ℝ => y * Real.log q) (Real.log q) x := by
      convert (hasDerivAt_id x).mul_const (Real.log q) using 1
      all_goals try rfl
      all_goals ring
    have hD : HasDerivAt (fun y : ℝ => (1 - y) * Real.log (1 - q))
        (-Real.log (1 - q)) x := by
      convert ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).mul_const
        (Real.log (1 - q)) using 1
      all_goals try rfl
      all_goals ring
    have hSq : HasDerivAt (fun y : ℝ => 2 * (y - q) ^ 2) (4 * (x - q)) x := by
      convert (((hasDerivAt_id x).sub (hasDerivAt_const x q)).pow 2).const_mul 2 using 1
      all_goals try rfl
      all_goals norm_num [Pi.sub_apply, Pi.pow_apply, id_eq]
      all_goals ring
    convert ((((hA.sub hB).sub hC).sub hD).sub hSq).hasDerivWithinAt using 1
    all_goals try rfl
    all_goals ring
  have hF'' : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt F' (F'' x) (interior (Set.Icc (0 : ℝ) 1)) x := by
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hx1 : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
    unfold F' F''
    have hA : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := Real.hasDerivAt_log hx0
    have hB : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-(1 - x)⁻¹) x := by
      convert (Real.hasDerivAt_log hx1).comp x
        ((hasDerivAt_const x 1).sub (hasDerivAt_id x)) using 1
      all_goals try rfl
      all_goals ring
    have hC : HasDerivAt (fun _y : ℝ => Real.log q) 0 x := hasDerivAt_const _ _
    have hD : HasDerivAt (fun _y : ℝ => Real.log (1 - q)) 0 x := hasDerivAt_const _ _
    have hlin : HasDerivAt (fun y : ℝ => 4 * (y - q)) 4 x := by
      convert ((hasDerivAt_id x).sub (hasDerivAt_const x q)).const_mul 4 using 1
      all_goals try rfl
      all_goals norm_num [Pi.sub_apply, id_eq]
    convert ((((hA.sub hB).sub hC).add hD).sub hlin).hasDerivWithinAt using 1
    all_goals try rfl
    all_goals ring
  have hF''nonneg : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1), 0 ≤ F'' x := by
    intro x hx
    rw [interior_Icc] at hx
    have hxpos : 0 < x := hx.1
    have hxlt : x < 1 := hx.2
    unfold F''
    have hden : 0 < x * (1 - x) := mul_pos hxpos (sub_pos.mpr hxlt)
    rw [show x⁻¹ + (1 - x)⁻¹ - 4 = (2 * x - 1) ^ 2 / (x * (1 - x)) by
      field_simp [ne_of_gt hxpos, ne_of_gt (sub_pos.mpr hxlt)]
      ring]
    exact div_nonneg (sq_nonneg _) hden.le
  have hconvex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) F :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) hFcont hF' hF'' hF''nonneg
  have hqmem : q ∈ interior (Set.Icc (0 : ℝ) 1) := by
    rw [interior_Icc]
    exact ⟨hq0, hq1⟩
  have hFq : F q = 0 := by
    unfold F binaryKLDivergence
    rw [Real.negMulLog_eq_neg]
    ring
  have hright : derivWithin F (Set.Ioi q) q = 0 := by
    have hderiv : HasDerivAt F 0 q := by
      have h := hF' q hqmem
      have hopen : interior (Set.Icc (0 : ℝ) 1) ∈ nhds q :=
        IsOpen.mem_nhds isOpen_interior hqmem
      have hat := h.hasDerivAt hopen
      have hzero : F' q = 0 := by
        unfold F'
        ring
      rw [hzero] at hat
      exact hat
    exact hderiv.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi q)
  have hmin := hconvex.isMinOn_of_rightDeriv_eq_zero hqmem hright
  have hp_mem : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp0, hp1⟩
  have := hmin hp_mem
  change F q ≤ F p at this
  rw [hFq] at this
  unfold F at this
  linarith

/-- Corrected finite relative entropy for arbitrary finite probability vectors. -/
def correctedKLSum {α : Type*} [Fintype α] (p q : FinProb α) : ℝ :=
  ∑ a, correctedKLTerm (p a) (q a)

theorem correctedKLTerm_eq_mul_klFun {x y : ℝ} (hy : y ≠ 0) :
    correctedKLTerm x y = y * InformationTheory.klFun (x / y) := by
  rw [correctedKLTerm, InformationTheory.klFun]
  field_simp [hy]
  ring

/-- Finite log-sum inequality, in corrected-KL form. -/
theorem correctedKLTerm_sum_le_sum
    {α : Type*} [Fintype α] (p q : FinProb α) (s : Finset α)
    (hsupport : ∀ a ∈ s, 0 < p a → 0 < q a) :
    correctedKLTerm (∑ a ∈ s, p a) (∑ a ∈ s, q a) ≤
      ∑ a ∈ s, correctedKLTerm (p a) (q a) := by
  classical
  let P : ℝ := ∑ a ∈ s, p a
  let Q : ℝ := ∑ a ∈ s, q a
  have hqnonneg (a : α) : 0 ≤ q a := prob_nonneg q a
  have hpnonneg (a : α) : 0 ≤ p a := prob_nonneg p a
  have hQnonneg : 0 ≤ Q := Finset.sum_nonneg fun a _ => hqnonneg a
  by_cases hQzero : Q = 0
  · have hqzero : ∀ a ∈ s, q a = 0 := by
      intro a ha
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hqnonneg i)).mp hQzero a ha
    have hpzero : ∀ a ∈ s, p a = 0 := by
      intro a ha
      apply le_antisymm
      · by_contra hnot
        have hppos : 0 < p a := lt_of_not_ge hnot
        exact (ne_of_gt (hsupport a ha hppos)) (hqzero a ha)
      · exact hpnonneg a
    have hPzero : P = 0 := by
      unfold P
      exact Finset.sum_eq_zero fun a ha => hpzero a ha
    have hsumzero : ∑ a ∈ s, correctedKLTerm (p a) (q a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [hpzero a ha, hqzero a ha]
      simp [correctedKLTerm]
    change correctedKLTerm P Q ≤ _
    rw [hPzero, hQzero, hsumzero]
    simp [correctedKLTerm]
  have hQpos : 0 < Q := lt_of_le_of_ne hQnonneg (Ne.symm hQzero)
  let w : α → ℝ := fun a => q a / Q
  let r : α → ℝ := fun a => if q a = 0 then 0 else p a / q a
  have hw0 : ∀ a ∈ s, 0 ≤ w a := by
    intro a _
    exact div_nonneg (hqnonneg a) hQnonneg
  have hwsum : ∑ a ∈ s, w a = 1 := by
    simp only [w, ← Finset.sum_div, Q]
    exact div_self hQzero
  have hr0 : ∀ a ∈ s, r a ∈ Set.Ici (0 : ℝ) := by
    intro a _
    simp only [Set.mem_Ici]
    by_cases hqa : q a = 0
    · simp [r, hqa]
    · simp [r, hqa, div_nonneg (hpnonneg a) (hqnonneg a)]
  have hweighted : ∑ a ∈ s, w a • r a = P / Q := by
    rw [show P / Q = ∑ a ∈ s, p a / Q by simp [P, Finset.sum_div]]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hqa : q a = 0
    · have hpa : p a = 0 := by
        apply le_antisymm
        · by_contra hnot
          have hppos : 0 < p a := lt_of_not_ge hnot
          exact (ne_of_gt (hsupport a ha hppos)) hqa
        · exact hpnonneg a
      simp [w, r, hqa, hpa]
    · simp only [w, r, hqa, if_false, smul_eq_mul]
      field_simp
  have hjensen := InformationTheory.convexOn_klFun.map_sum_le
    (t := s) (w := w) (p := r) hw0 hwsum hr0
  rw [hweighted] at hjensen
  have hmul := mul_le_mul_of_nonneg_left hjensen hQnonneg
  rw [← correctedKLTerm_eq_mul_klFun hQzero] at hmul
  calc
    correctedKLTerm P Q ≤ Q * ∑ a ∈ s, w a • InformationTheory.klFun (r a) := hmul
    _ = ∑ a ∈ s, correctedKLTerm (p a) (q a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hqa : q a = 0
      · have hpa : p a = 0 := by
          apply le_antisymm
          · by_contra hnot
            have hppos : 0 < p a := lt_of_not_ge hnot
            exact (ne_of_gt (hsupport a ha hppos)) hqa
          · exact hpnonneg a
        simp [w, r, hqa, hpa, correctedKLTerm]
      · rw [correctedKLTerm_eq_mul_klFun hqa]
        simp only [w, r, hqa, if_false, smul_eq_mul]
        field_simp

theorem l1Dist_eq_two_mul_sum_ge
    {α : Type*} [Fintype α] (p q : FinProb α) :
    l1Dist p q =
      2 * ∑ a ∈ Finset.univ.filter (fun a => q a ≤ p a), (p a - q a) := by
  classical
  have htotal : ∑ a, (p a - q a) = 0 := by
    rw [Finset.sum_sub_distrib, stdSimplex.sum_eq_one, stdSimplex.sum_eq_one, sub_self]
  rw [l1Dist]
  calc
    ∑ a, |p a - q a| =
        ∑ a, (2 * (if q a ≤ p a then p a - q a else 0) - (p a - q a)) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : q a ≤ p a
      · rw [if_pos ha, abs_of_nonneg (sub_nonneg.mpr ha)]
        ring
      · rw [if_neg ha, abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge ha))]
        ring
    _ = 2 * ∑ a, (if q a ≤ p a then p a - q a else 0) -
        ∑ a, (p a - q a) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 2 * ∑ a ∈ Finset.univ.filter (fun a => q a ≤ p a), (p a - q a) := by
      rw [htotal, sub_zero, Finset.sum_filter]

theorem binaryKLDivergence_eq_corrected
    {p q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    binaryKLDivergence p q =
      correctedKLTerm p q + correctedKLTerm (1 - p) (1 - q) := by
  have hqne : q ≠ 0 := ne_of_gt hq0
  have h1qne : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  rw [binaryKLDivergence, Real.negMulLog_eq_neg]
  by_cases hp0 : p = 0
  · simp [hp0, correctedKLTerm]
  by_cases hp1 : 1 - p = 0
  · have hp : p = 1 := by linarith
    simp [hp, correctedKLTerm]
  simp only [neg_neg]
  unfold correctedKLTerm
  rw [Real.log_div hp0 hqne, Real.log_div hp1 h1qne]
  ring

/-- Sharp finite Pinsker inequality, with the conventional natural-log constant. -/
theorem l1Dist_sq_le_two_mul_correctedKLSum
    {α : Type*} [Fintype α] (p q : FinProb α)
    (hsupport : ∀ a, 0 < p a → 0 < q a) :
    l1Dist p q ^ 2 ≤ 2 * correctedKLSum p q := by
  classical
  let A : Finset α := Finset.univ.filter fun a => q a ≤ p a
  let B : Finset α := Finset.univ.filter fun a => ¬q a ≤ p a
  let P : ℝ := ∑ a ∈ A, p a
  let Q : ℝ := ∑ a ∈ A, q a
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun a _ => prob_nonneg p a
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun a _ => prob_nonneg q a
  have hP1 : P ≤ 1 := by
    rw [← stdSimplex.sum_eq_one p]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => prob_nonneg p _)
  have hQ1 : Q ≤ 1 := by
    rw [← stdSimplex.sum_eq_one q]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => prob_nonneg q _)
  have hl1 : l1Dist p q = 2 * (P - Q) := by
    rw [l1Dist_eq_two_mul_sum_ge]
    congr 1
    unfold P Q A
    rw [Finset.sum_sub_distrib]
  by_cases hQzero : Q = 0
  · have hPzero : P = 0 := by
      have hqzero : ∀ a ∈ A, q a = 0 := by
        intro a ha
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => prob_nonneg q i)).mp hQzero a ha
      have hpzero : ∀ a ∈ A, p a = 0 := by
        intro a ha
        apply le_antisymm
        · by_contra hnot
          have hppos : 0 < p a := lt_of_not_ge hnot
          exact (ne_of_gt (hsupport a hppos)) (hqzero a ha)
        · exact prob_nonneg p a
      unfold P
      exact Finset.sum_eq_zero fun a ha => hpzero a ha
    rw [hl1, hPzero, hQzero]
    simpa only [sub_self, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (show 0 ≤ correctedKLSum p q by
          unfold correctedKLSum
          exact Finset.sum_nonneg fun a _ => correctedKLTerm_nonneg
            (prob_nonneg p a) (prob_nonneg q a) (hsupport a))
  by_cases hQone : Q = 1
  · have hPone : P = 1 := by
      have hQP : Q ≤ P := by
        unfold P Q A
        exact Finset.sum_le_sum fun a ha => by
          have haq : q a ≤ p a := by
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
          exact haq
      exact le_antisymm hP1 (by simpa [hQone] using hQP)
    rw [hl1, hPone, hQone]
    simpa only [sub_self, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (show 0 ≤ correctedKLSum p q by
          unfold correctedKLSum
          exact Finset.sum_nonneg fun a _ => correctedKLTerm_nonneg
            (prob_nonneg p a) (prob_nonneg q a) (hsupport a))
  have hQpos : 0 < Q := lt_of_le_of_ne hQ0 (Ne.symm hQzero)
  have hQlt : Q < 1 := lt_of_le_of_ne hQ1 hQone
  have hAcoarse := correctedKLTerm_sum_le_sum p q A
    (fun a _ => hsupport a)
  have hBcoarse := correctedKLTerm_sum_le_sum p q B
    (fun a _ => hsupport a)
  have hBsumP : ∑ a ∈ B, p a = 1 - P := by
    have hsplit : (∑ a ∈ A, p a) + ∑ a ∈ B, p a = ∑ a, p a := by
      simpa [A, B] using
        (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun a => q a ≤ p a) (fun a => p a))
    rw [stdSimplex.sum_eq_one] at hsplit
    unfold P
    linarith
  have hBsumQ : ∑ a ∈ B, q a = 1 - Q := by
    have hsplit : (∑ a ∈ A, q a) + ∑ a ∈ B, q a = ∑ a, q a := by
      simpa [A, B] using
        (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun a => q a ≤ p a) (fun a => q a))
    rw [stdSimplex.sum_eq_one] at hsplit
    unfold Q
    linarith
  rw [hBsumP, hBsumQ] at hBcoarse
  have hpartition :
      (∑ a ∈ A, correctedKLTerm (p a) (q a)) +
          ∑ a ∈ B, correctedKLTerm (p a) (q a) = correctedKLSum p q := by
    unfold correctedKLSum
    simpa [A, B] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun a => q a ≤ p a) (fun a => correctedKLTerm (p a) (q a)))
  have hcoarse : binaryKLDivergence P Q ≤ correctedKLSum p q := by
    rw [binaryKLDivergence_eq_corrected hQpos hQlt]
    calc
      correctedKLTerm P Q + correctedKLTerm (1 - P) (1 - Q) ≤
          (∑ a ∈ A, correctedKLTerm (p a) (q a)) +
            ∑ a ∈ B, correctedKLTerm (p a) (q a) := add_le_add hAcoarse hBcoarse
      _ = correctedKLSum p q := hpartition
  have hbinary := binaryKLDivergence_pinsker hP0 hP1 hQpos hQlt
  rw [hl1]
  nlinarith

/-- Pinsker specialized to a joint law and the product of its marginals. -/
theorem l1Dist_joint_product_sq_le_two_mul_mutualInfo
    {α β : Type*} [Fintype α] [Fintype β] (r : FinProb (α × β)) :
    l1Dist r (product (fstMarginal r) (sndMarginal r)) ^ 2 ≤
      2 * mutualInfo r := by
  have hsupport : ∀ z, 0 < r z →
      0 < product (fstMarginal r) (sndMarginal r) z := by
    rintro ⟨a, b⟩ hab
    exact mul_pos (hab.trans_le (joint_le_fstMarginal r a b))
      (hab.trans_le (joint_le_sndMarginal r a b))
  have h := l1Dist_sq_le_two_mul_correctedKLSum
    r (product (fstMarginal r) (sndMarginal r)) hsupport
  rw [mutualInfo_eq_jointProductKL]
  exact h

/-- Square-root form of finite Pinsker. -/
theorem l1Dist_joint_product_le_sqrt_two_mul_mutualInfo
    {α β : Type*} [Fintype α] [Fintype β] (r : FinProb (α × β)) :
    l1Dist r (product (fstMarginal r) (sndMarginal r)) ≤
      Real.sqrt (2 * mutualInfo r) := by
  apply (Real.le_sqrt (l1Dist_nonneg _ _)
    (mul_nonneg (by norm_num) (mutualInfo_nonneg r))).2
  exact l1Dist_joint_product_sq_le_two_mul_mutualInfo r

/-- Pinsker in the exact random-variable form consumed after entropy decrement. -/
theorem l1Dist_jointLaw_product_le_sqrt_two_mul_of_mutualInfo_le
    {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]
    (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) {η : ℝ}
    (hη : mutualInfo (jointLaw p X Y) ≤ η) :
    l1Dist (jointLaw p X Y) (product (law p X) (law p Y)) ≤
      Real.sqrt (2 * η) := by
  have hη0 : 0 ≤ η := (mutualInfo_nonneg (jointLaw p X Y)).trans hη
  have hsq := l1Dist_joint_product_sq_le_two_mul_mutualInfo (jointLaw p X Y)
  rw [fstMarginal_jointLaw, sndMarginal_jointLaw] at hsq
  apply (Real.le_sqrt (l1Dist_nonneg _ _) (mul_nonneg (by norm_num) hη0)).2
  exact hsq.trans (mul_le_mul_of_nonneg_left hη (by norm_num))

end

end FiniteEntropy
end Erdos67
