/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.TypeII
import ErdosProblems.Erdos175.ReciprocalExpSumRounding
import ErdosProblems.Erdos175.ReciprocalExpSumOneStep

/-!
# Near--far splitting for Type II reciprocal sums

This file supplies the finite combinatorics used in Granville--Ramaré's
Type II estimate.  Pairs of second variables within a prescribed integer
distance are estimated trivially, while the remaining Gram correlations
may be bounded by a reciprocal exponential-sum estimate.
-/

open scoped BigOperators

namespace Erdos175.TypeII

/-- The elements of `s` at integer distance at most `T` from `v`. -/
def nearNeighbors (s : Finset ℕ) (T v : ℕ) : Finset ℕ :=
  s.filter fun w ↦ Nat.dist v w ≤ T

@[simp] lemma mem_nearNeighbors {s : Finset ℕ} {T v w : ℕ} :
    w ∈ nearNeighbors s T v ↔ w ∈ s ∧ Nat.dist v w ≤ T := by
  simp [nearNeighbors]

/-- An integer interval contains at most `2T+1` integers at distance at
most `T` from any fixed integer. -/
lemma card_nearNeighbors_le (s : Finset ℕ) (T v : ℕ) :
    (nearNeighbors s T v).card ≤ 2 * T + 1 := by
  have hsub : nearNeighbors s T v ⊆ Finset.Icc (v - T) (v + T) := by
    intro w hw
    have hd := (mem_nearNeighbors.mp hw).2
    by_cases hvw : v ≤ w
    · rw [Nat.dist_eq_sub_of_le hvw] at hd
      simp only [Finset.mem_Icc]
      omega
    · have hwv : w ≤ v := Nat.le_of_not_ge hvw
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hwv] at hd
      simp only [Finset.mem_Icc]
      omega
  calc
    (nearNeighbors s T v).card ≤ (Finset.Icc (v - T) (v + T)).card :=
      Finset.card_le_card hsub
    _ = v + T + 1 - (v - T) := by simp
    _ ≤ 2 * T + 1 := by omega

/-- Consequently, the number of ordered near pairs in a finite support is
at most `card(s) * (2T+1)`. -/
lemma card_nearPairs_le (s : Finset ℕ) (T : ℕ) :
    ((s ×ˢ s).filter fun p ↦ Nat.dist p.1 p.2 ≤ T).card ≤
      s.card * (2 * T + 1) := by
  rw [Finset.card_filter]
  change (∑ p ∈ s ×ˢ s, if Nat.dist p.1 p.2 ≤ T then 1 else 0) ≤ _
  rw [Finset.sum_product]
  calc
    (∑ v ∈ s, ∑ w ∈ s, if Nat.dist v w ≤ T then 1 else 0) =
        ∑ v ∈ s, (nearNeighbors s T v).card := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [nearNeighbors, Finset.card_filter]
    _ ≤ ∑ _v ∈ s, (2 * T + 1) := by
      apply Finset.sum_le_sum
      intro v hv
      exact card_nearNeighbors_le s T v
    _ = s.card * (2 * T + 1) := by simp

/-- A concrete near--far Gram estimate.  Near correlations cost `D`, but
there are at most `2T+1` near neighbors of each second variable.  Far
correlations cost `Q`.  The factor `2` in the near term comes from the
elementary inequality `ab ≤ a²+b²`; it is harmless for the application.
-/
lemma reciprocalInnerBound_of_natDist_near_far
    (uSupport vSupport : Finset ℕ)
    (beta : ℕ → ℂ) (kernel : ℕ → ℕ → ℂ)
    (T : ℕ) (D Q : ℝ)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hnear : ∀ v ∈ vSupport, ∀ w ∈ vSupport,
      Nat.dist v w ≤ T →
        ‖kernelCorrelation uSupport kernel v w‖ ≤ D)
    (hfar : ∀ v ∈ vSupport, ∀ w ∈ vSupport,
      T < Nat.dist v w →
        ‖kernelCorrelation uSupport kernel v w‖ ≤ Q) :
    ReciprocalInnerBound uSupport vSupport beta kernel
      (2 * D * (2 * T + 1) + Q * (vSupport.card : ℝ)) := by
  classical
  let a : ℕ → ℝ := fun v ↦ ‖beta v‖
  let S : ℝ := ∑ v ∈ vSupport, a v ^ 2
  let L : ℝ := ∑ v ∈ vSupport, ∑ w ∈ vSupport,
    if Nat.dist v w ≤ T then a v ^ 2 else 0
  let R : ℝ := ∑ v ∈ vSupport, ∑ w ∈ vSupport,
    if Nat.dist v w ≤ T then a w ^ 2 else 0
  have hleft : L ≤ (2 * T + 1 : ℕ) * S := by
    dsimp only [L, S]
    calc
      (∑ v ∈ vSupport, ∑ w ∈ vSupport,
          if Nat.dist v w ≤ T then a v ^ 2 else 0) =
          ∑ v ∈ vSupport,
            ((nearNeighbors vSupport T v).card : ℝ) * a v ^ 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [← Finset.sum_filter]
        simp [nearNeighbors]
      _ ≤ ∑ v ∈ vSupport, ((2 * T + 1 : ℕ) : ℝ) * a v ^ 2 := by
        apply Finset.sum_le_sum
        intro v hv
        gcongr
        exact_mod_cast card_nearNeighbors_le vSupport T v
      _ = ((2 * T + 1 : ℕ) : ℝ) *
          ∑ v ∈ vSupport, a v ^ 2 := by rw [Finset.mul_sum]
  have hright : R ≤ (2 * T + 1 : ℕ) * S := by
    have hRL : R = L := by
      dsimp only [R, L]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      rw [Nat.dist_comm]
    rw [hRL]
    exact hleft
  have hnearMass :
      (∑ v ∈ vSupport, ∑ w ∈ vSupport,
        if Nat.dist v w ≤ T then (a v ^ 2 + a w ^ 2) else 0) ≤
        2 * ((2 * T + 1 : ℕ) : ℝ) * S := by
    have hsplit :
        (∑ v ∈ vSupport, ∑ w ∈ vSupport,
          if Nat.dist v w ≤ T then (a v ^ 2 + a w ^ 2) else 0) = L + R := by
      dsimp only [L, R]
      simp only [ite_add_zero, Finset.sum_add_distrib]
    rw [hsplit]
    nlinarith
  have hmass :
      (∑ v ∈ vSupport, ∑ w ∈ vSupport, a v * a w) ≤
        (vSupport.card : ℝ) * S := by
    have hcs :
        (∑ v ∈ vSupport, a v) ^ 2 ≤
          (vSupport.card : ℝ) * S := by
      dsimp only [S]
      simpa using (Finset.sum_mul_sq_le_sq_mul_sq vSupport
        (fun _v ↦ (1 : ℝ)) a)
    calc
      (∑ v ∈ vSupport, ∑ w ∈ vSupport, a v * a w) =
          (∑ v ∈ vSupport, a v) ^ 2 := by
        rw [pow_two, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.mul_sum]
      _ ≤ (vSupport.card : ℝ) * S := hcs
  have hpair (v : ℕ) (hv : v ∈ vSupport)
      (w : ℕ) (hw : w ∈ vSupport) :
      a v * a w * ‖kernelCorrelation uSupport kernel v w‖ ≤
        D * (if Nat.dist v w ≤ T then (a v ^ 2 + a w ^ 2) else 0) +
          Q * (a v * a w) := by
    by_cases hn : Nat.dist v w ≤ T
    · rw [if_pos hn]
      have hab : a v * a w ≤ a v ^ 2 + a w ^ 2 := by
        dsimp only [a]
        nlinarith [sq_nonneg (‖beta v‖ - ‖beta w‖)]
      calc
        a v * a w * ‖kernelCorrelation uSupport kernel v w‖ ≤
            a v * a w * D := by
          exact mul_le_mul_of_nonneg_left (hnear v hv w hw hn)
            (mul_nonneg (by dsimp only [a]; positivity)
              (by dsimp only [a]; positivity))
        _ ≤ D * (a v ^ 2 + a w ^ 2) := by
          rw [mul_comm (a v * a w) D]
          exact mul_le_mul_of_nonneg_left hab hD
        _ ≤ D * (a v ^ 2 + a w ^ 2) + Q * (a v * a w) := by
          exact le_add_of_nonneg_right
            (mul_nonneg hQ (mul_nonneg
              (by dsimp only [a]; positivity) (by dsimp only [a]; positivity)))
    · simp only [if_neg hn, mul_zero, zero_add]
      have hdist : T < Nat.dist v w := Nat.lt_of_not_ge hn
      calc
        a v * a w * ‖kernelCorrelation uSupport kernel v w‖ ≤
            a v * a w * Q := by
          exact mul_le_mul_of_nonneg_left (hfar v hv w hw hdist)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = Q * (a v * a w) := by ring
  unfold ReciprocalInnerBound
  calc
    (∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2) ≤
        ∑ v ∈ vSupport, ∑ w ∈ vSupport,
          a v * a w * ‖kernelCorrelation uSupport kernel v w‖ :=
      innerSum_meanSquare_le_sum_norm_correlation
        uSupport vSupport beta kernel
    _ ≤ ∑ v ∈ vSupport, ∑ w ∈ vSupport,
        (D * (if Nat.dist v w ≤ T then (a v ^ 2 + a w ^ 2) else 0) +
          Q * (a v * a w)) := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro w hw
      exact hpair v hv w hw
    _ = D * (∑ v ∈ vSupport, ∑ w ∈ vSupport,
          if Nat.dist v w ≤ T then (a v ^ 2 + a w ^ 2) else 0) +
        Q * (∑ v ∈ vSupport, ∑ w ∈ vSupport, a v * a w) := by
      simp only [Finset.sum_add_distrib]
      simp only [Finset.mul_sum]
    _ ≤ D * (2 * ((2 * T + 1 : ℕ) : ℝ) * S) +
        Q * ((vSupport.card : ℝ) * S) := by gcongr
    _ = (2 * D * (2 * T + 1) + Q * (vSupport.card : ℝ)) *
        ∑ v ∈ vSupport, ‖beta v‖ ^ 2 := by
      dsimp only [S, a]
      push_cast
      ring

/-- Unsquared bilinear consequence of the concrete near--far split. -/
lemma norm_bilinearSum_le_natDist_near_far
    (uSupport vSupport : Finset ℕ)
    (alpha beta : ℕ → ℂ) (kernel : ℕ → ℕ → ℂ)
    (T : ℕ) (D Q : ℝ)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hnear : ∀ v ∈ vSupport, ∀ w ∈ vSupport,
      Nat.dist v w ≤ T →
        ‖kernelCorrelation uSupport kernel v w‖ ≤ D)
    (hfar : ∀ v ∈ vSupport, ∀ w ∈ vSupport,
      T < Nat.dist v w →
        ‖kernelCorrelation uSupport kernel v w‖ ≤ Q) :
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ≤
      l2Norm uSupport alpha *
        Real.sqrt (2 * D * (2 * T + 1) + Q * (vSupport.card : ℝ)) *
          l2Norm vSupport beta := by
  apply norm_bilinearSum_le_of_reciprocalInnerBound
  · positivity
  · exact reciprocalInnerBound_of_natDist_near_far
      uSupport vSupport beta kernel T D Q hD hQ hnear hfar

/-! ## Restricted reciprocal kernels -/

/-- The completely trivial correlation estimate for the restricted
reciprocal kernel. -/
lemma norm_kernelCorrelation_restrictedReciprocalKernel_le_card
    (I uSupport : Finset ℕ) (x : ℝ) (v w : ℕ) :
    ‖kernelCorrelation uSupport (restrictedReciprocalKernel I x) v w‖ ≤
      (uSupport.card : ℝ) := by
  calc
    ‖kernelCorrelation uSupport (restrictedReciprocalKernel I x) v w‖ ≤
        ∑ _u ∈ uSupport, (1 : ℝ) := by
      unfold kernelCorrelation
      calc
        ‖∑ u ∈ uSupport,
            (starRingEnd ℂ) (restrictedReciprocalKernel I x u v) *
              restrictedReciprocalKernel I x u w‖ ≤
            ∑ u ∈ uSupport,
              ‖(starRingEnd ℂ) (restrictedReciprocalKernel I x u v) *
                restrictedReciprocalKernel I x u w‖ := norm_sum_le _ _
        _ ≤ ∑ _u ∈ uSupport, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro u hu
          rw [norm_mul]
          change ‖star (restrictedReciprocalKernel I x u v)‖ *
              ‖restrictedReciprocalKernel I x u w‖ ≤ 1
          rw [norm_star]
          have hv := norm_restrictedReciprocalKernel_le_one I x u v
          have hw := norm_restrictedReciprocalKernel_le_one I x u w
          nlinarith [norm_nonneg (restrictedReciprocalKernel I x u v),
            norm_nonneg (restrictedReciprocalKernel I x u w)]
    _ = (uSupport.card : ℝ) := by simp

/-- Applying the q-free reciprocal-Ioc theorem to every far Gram entry.
The hypotheses are only the explicit scale inequalities needed by that
theorem; there is no abstract exponential-sum or mean-square premise.

This form is useful while later arithmetic estimates replace `Q` by a
single closed expression in the dyadic block parameters. -/
lemma norm_reciprocalBilinearSum_Ioc_le_near_far_qfree
    (x : ℝ) (y y' A B V T : ℕ) (alpha beta : ℕ → ℂ) (Q : ℝ)
    (hV : 0 < V) (hx : 0 < x) (hdyadic : B - A ≤ A + 1) (hQ : 0 ≤ Q)
    (hscale : ∀ v ∈ Finset.Ioc V (2 * V),
      ∀ w ∈ Finset.Ioc V (2 * V), T < Nat.dist v w →
      let C := max A (max (y / v) (y / w))
      let E := min B (min (y' / v) (y' / w))
      C < E →
        12 * |x * (1 / (w : ℝ) - 1 / (v : ℝ))| ≤
            ((C + 1 : ℕ) : ℝ) ^ 4 ∧
          ((C + 1 : ℕ) : ℝ) ^ 4 <
            12 * |x * (1 / (w : ℝ) - 1 / (v : ℝ))| *
              (Nat.sqrt (E - C) : ℝ) ^ 3)
    (hfarQ : ∀ v ∈ Finset.Ioc V (2 * V),
      ∀ w ∈ Finset.Ioc V (2 * V), T < Nat.dist v w →
      let C := max A (max (y / v) (y / w))
      let E := min B (min (y' / v) (y' / w))
      C < E →
        128 * ((E - C : ℕ) : ℝ) *
          (|x * (1 / (w : ℝ) - 1 / (v : ℝ))| /
              ((C + 1 : ℕ) : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
            Real.sqrt (1 + Real.log ((C + 1 : ℕ) : ℝ)) ≤ Q) :
    ‖reciprocalBilinearSum (Finset.Ioc y y') (Finset.Ioc A B)
        (Finset.Ioc V (2 * V)) x alpha beta‖ ≤
      l2Norm (Finset.Ioc A B) alpha *
        Real.sqrt
          (2 * (B - A : ℕ) * (2 * T + 1) +
            Q * (V : ℝ)) *
          l2Norm (Finset.Ioc V (2 * V)) beta := by
  have hcardAB : (Finset.Ioc A B).card = B - A := by simp
  have hcardV : (Finset.Ioc V (2 * V)).card = V := by simp; omega
  have hnear : ∀ v ∈ Finset.Ioc V (2 * V),
      ∀ w ∈ Finset.Ioc V (2 * V), Nat.dist v w ≤ T →
        ‖kernelCorrelation (Finset.Ioc A B)
          (restrictedReciprocalKernel (Finset.Ioc y y') x) v w‖ ≤
            ((B - A : ℕ) : ℝ) := by
    intro v hv w hw hn
    simpa only [hcardAB] using
      norm_kernelCorrelation_restrictedReciprocalKernel_le_card
        (Finset.Ioc y y') (Finset.Ioc A B) x v w
  have hfar : ∀ v ∈ Finset.Ioc V (2 * V),
      ∀ w ∈ Finset.Ioc V (2 * V), T < Nat.dist v w →
        ‖kernelCorrelation (Finset.Ioc A B)
          (restrictedReciprocalKernel (Finset.Ioc y y') x) v w‖ ≤ Q := by
    intro v hv w hw hdist
    have hvpos : 0 < v := by
      have := (Finset.mem_Ioc.mp hv).1
      omega
    have hwpos : 0 < w := by
      have := (Finset.mem_Ioc.mp hw).1
      omega
    let C := max A (max (y / v) (y / w))
    let E := min B (min (y' / v) (y' / w))
    let t : ℝ := x * (1 / (w : ℝ) - 1 / (v : ℝ))
    rw [kernelCorrelation_restrictedReciprocalKernel_Ioc_eq
      x y y' A B v w hvpos hwpos]
    change ‖reciprocalExpSum t C E‖ ≤ Q
    by_cases hCE : C < E
    · have hsc := hscale v hv w hw hdist hCE
      have ht : 0 < |t| := by
        have hvw : v ≠ w := by
          intro heq
          subst w
          simpa using hdist
        have hdiff : 1 / (w : ℝ) - 1 / (v : ℝ) ≠ 0 := by
          intro hzero
          have hinv : (w : ℝ)⁻¹ = (v : ℝ)⁻¹ := by
            simpa only [one_div] using sub_eq_zero.mp hzero
          have hcast : (w : ℝ) = (v : ℝ) := inv_injective hinv
          apply hvw
          exact_mod_cast hcast.symm
        exact abs_pos.mpr (mul_ne_zero (ne_of_gt hx) hdiff)
      have hbase := norm_reciprocalExpSum_le_dyadic_qfree
        |t| C E ht hCE.le hCE (by
          dsimp only [C, E]
          omega) hsc.1 hsc.2
      have hsign : ‖reciprocalExpSum t C E‖ =
          ‖reciprocalExpSum |t| C E‖ := by
        by_cases htneg : t < 0
        · have habs : |t| = -t := abs_of_neg htneg
          rw [habs, ← norm_reciprocalExpSum_neg t C E]
        · have ht0 : 0 ≤ t := le_of_not_gt htneg
          rw [abs_of_nonneg ht0]
      rw [hsign]
      exact hbase.trans (hfarQ v hv w hw hdist hCE)
    · have hempty : Finset.Ioc C E = ∅ :=
        Finset.Ioc_eq_empty hCE
      rw [reciprocalExpSum, hempty]
      simpa using hQ
  unfold reciprocalBilinearSum
  have hbound := norm_bilinearSum_le_natDist_near_far
    (Finset.Ioc A B) (Finset.Ioc V (2 * V)) alpha beta
    (restrictedReciprocalKernel (Finset.Ioc y y') x)
    T (B - A : ℕ) Q (by positivity) hQ hnear hfar
  simpa only [hcardV] using hbound

/-- The explicit direct/one-step/two-step envelope used for far pairs. -/
noncomputable def reciprocalThreeBranchBound (x : ℝ) (A B : ℕ) : ℝ :=
  ((B + 1 : ℕ) : ℝ) ^ 2 / x +
    24 * ((A + 1 : ℕ) : ℝ) *
      Real.sqrt (x / ((A + 1 : ℕ) : ℝ) ^ 3) *
        Real.sqrt (1 + Real.log ((A + 1 : ℕ) : ℝ)) +
    256 * ((B - A : ℕ) : ℝ) *
      (x / ((A + 1 : ℕ) : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (Real.log ((A + 1 : ℕ) : ℝ))

/-- The unconditional three-branch version of the preceding result.  Only
the common upper-frequency condition remains; the first-derivative,
two-step, and capped one-step alternatives are selected internally by
`TypeI.norm_reciprocalExpSum_le_threeBranch`. -/
lemma norm_reciprocalBilinearSum_Ioc_le_near_far_threeBranch
    (x : ℝ) (y y' A B V₀ V₁ T : ℕ) (alpha beta : ℕ → ℂ) (Q : ℝ)
    (hx : 0 < x) (hdyadic : B - A ≤ A + 1) (hQ : 0 ≤ Q)
    (hone : ∀ v ∈ Finset.Ioc V₀ V₁,
      ∀ w ∈ Finset.Ioc V₀ V₁, T < Nat.dist v w →
      let C := max A (max (y / v) (y / w))
      let E := min B (min (y' / v) (y' / w))
      C < E →
        12 * |x * (1 / (w : ℝ) - 1 / (v : ℝ))| ≤
          ((C + 1 : ℕ) : ℝ) ^ 4)
    (hfarQ : ∀ v ∈ Finset.Ioc V₀ V₁,
      ∀ w ∈ Finset.Ioc V₀ V₁, T < Nat.dist v w →
      let C := max A (max (y / v) (y / w))
      let E := min B (min (y' / v) (y' / w))
      C < E →
        reciprocalThreeBranchBound
          |x * (1 / (w : ℝ) - 1 / (v : ℝ))| C E ≤ Q) :
    ‖reciprocalBilinearSum (Finset.Ioc y y') (Finset.Ioc A B)
        (Finset.Ioc V₀ V₁) x alpha beta‖ ≤
      l2Norm (Finset.Ioc A B) alpha *
        Real.sqrt
          (2 * (B - A : ℕ) * (2 * T + 1) +
            Q * ((V₁ - V₀ : ℕ) : ℝ)) *
          l2Norm (Finset.Ioc V₀ V₁) beta := by
  have hcardAB : (Finset.Ioc A B).card = B - A := by simp
  have hcardV : (Finset.Ioc V₀ V₁).card = V₁ - V₀ := by simp
  have hnear : ∀ v ∈ Finset.Ioc V₀ V₁,
      ∀ w ∈ Finset.Ioc V₀ V₁, Nat.dist v w ≤ T →
        ‖kernelCorrelation (Finset.Ioc A B)
          (restrictedReciprocalKernel (Finset.Ioc y y') x) v w‖ ≤
            ((B - A : ℕ) : ℝ) := by
    intro v hv w hw hn
    simpa only [hcardAB] using
      norm_kernelCorrelation_restrictedReciprocalKernel_le_card
        (Finset.Ioc y y') (Finset.Ioc A B) x v w
  have hfar : ∀ v ∈ Finset.Ioc V₀ V₁,
      ∀ w ∈ Finset.Ioc V₀ V₁, T < Nat.dist v w →
        ‖kernelCorrelation (Finset.Ioc A B)
          (restrictedReciprocalKernel (Finset.Ioc y y') x) v w‖ ≤ Q := by
    intro v hv w hw hdist
    have hvpos : 0 < v := by
      have := (Finset.mem_Ioc.mp hv).1
      omega
    have hwpos : 0 < w := by
      have := (Finset.mem_Ioc.mp hw).1
      omega
    let C := max A (max (y / v) (y / w))
    let E := min B (min (y' / v) (y' / w))
    let t : ℝ := |x * (1 / (w : ℝ) - 1 / (v : ℝ))|
    rw [norm_kernelCorrelation_restrictedReciprocalKernel_Ioc_eq_abs
      x y y' A B v w hvpos hwpos]
    change ‖reciprocalExpSum t C E‖ ≤ Q
    by_cases hCE : C < E
    · have ht : 0 < t := by
        dsimp only [t]
        have hvw : v ≠ w := by
          intro heq
          subst w
          simp at hdist
        have hdiff : 1 / (w : ℝ) - 1 / (v : ℝ) ≠ 0 := by
          intro hzero
          have hinv : (w : ℝ)⁻¹ = (v : ℝ)⁻¹ := by
            simpa only [one_div] using sub_eq_zero.mp hzero
          have hcast : (w : ℝ) = (v : ℝ) := inv_injective hinv
          apply hvw
          exact_mod_cast hcast.symm
        exact abs_pos.mpr (mul_ne_zero (ne_of_gt hx) hdiff)
      have hbase := norm_reciprocalExpSum_le_three_branch
        t C E ht hCE.le (by
          dsimp only [C, E]
          omega) (hone v hv w hw hdist hCE)
      exact hbase.trans (by
        simpa only [reciprocalThreeBranchBound] using hfarQ v hv w hw hdist hCE)
    · have hempty : Finset.Ioc C E = ∅ := Finset.Ioc_eq_empty hCE
      rw [reciprocalExpSum, hempty]
      simpa using hQ
  unfold reciprocalBilinearSum
  have hbound := norm_bilinearSum_le_natDist_near_far
    (Finset.Ioc A B) (Finset.Ioc V₀ V₁) alpha beta
    (restrictedReciprocalKernel (Finset.Ioc y y') x)
    T (B - A : ℕ) Q (by positivity) hQ hnear hfar
  simpa only [hcardV] using hbound

/-! ### A premise-free finite majorant -/

/-- The lower endpoint of a product-restricted Gram correlation. -/
def correlationLower (y A v w : ℕ) : ℕ :=
  max A (max (y / v) (y / w))

/-- The upper endpoint of a product-restricted Gram correlation. -/
def correlationUpper (y' B v w : ℕ) : ℕ :=
  min B (min (y' / v) (y' / w))

/-- A completely explicit bound for one far correlation.  In the frequency
range covered by one of the three analytic branches it selects exactly one
branch; outside those ranges it falls back to the trivial interval length.
In particular, inactive `k = 1` and `k = 2` terms are not added. -/
noncomputable def selectedReciprocalBound (x : ℝ) (A B : ℕ) : ℝ :=
  let C : ℕ := A + 1
  if x / (C : ℝ) ^ 2 ≤ 1 / 2 then
    ((B + 1 : ℕ) : ℝ) ^ 2 / x
  else if 12 * x ≤ (C : ℝ) ^ 4 ∧
      (C : ℝ) ^ 4 <
        12 * x * (Nat.sqrt (B - A) : ℝ) ^ 3 then
    128 * ((B - A : ℕ) : ℝ) *
      (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log (C : ℝ))
  else if 4 * x ≤ (C : ℝ) ^ 3 then
    24 * (C : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
      Real.sqrt (1 + Real.log (C : ℝ))
  else
    (B - A : ℕ)

/-- The direct-frequency branch of `selectedReciprocalBound`. -/
lemma selectedReciprocalBound_eq_direct
    (x : ℝ) (A B : ℕ)
    (h : x / ((A + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 2) :
    selectedReciprocalBound x A B = ((B + 1 : ℕ) : ℝ) ^ 2 / x := by
  simp only [selectedReciprocalBound, if_pos h]

/-- The one-step branch of `selectedReciprocalBound`. -/
lemma selectedReciprocalBound_eq_k1
    (x : ℝ) (A B : ℕ)
    (hdirect : ¬ x / ((A + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 2)
    (hk2 : ¬ (12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4 ∧
      ((A + 1 : ℕ) : ℝ) ^ 4 <
        12 * x * (Nat.sqrt (B - A) : ℝ) ^ 3))
    (hk1 : 4 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 3) :
    selectedReciprocalBound x A B =
      24 * (((A + 1 : ℕ) : ℝ)) *
        Real.sqrt (x / (((A + 1 : ℕ) : ℝ)) ^ 3) *
          Real.sqrt (1 + Real.log (((A + 1 : ℕ) : ℝ))) := by
  simp only [selectedReciprocalBound, if_neg hdirect, if_neg hk2, if_pos hk1]

/-- The two-step branch of `selectedReciprocalBound`. -/
lemma selectedReciprocalBound_eq_k2
    (x : ℝ) (A B : ℕ)
    (hdirect : ¬ x / ((A + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 2)
    (hk2 : 12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4 ∧
      ((A + 1 : ℕ) : ℝ) ^ 4 <
        12 * x * (Nat.sqrt (B - A) : ℝ) ^ 3) :
    selectedReciprocalBound x A B =
      128 * ((B - A : ℕ) : ℝ) *
        (x / (((A + 1 : ℕ) : ℝ)) ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt (1 + Real.log (((A + 1 : ℕ) : ℝ))) := by
  simp only [selectedReciprocalBound, if_neg hdirect, if_pos hk2]

/-- The residual trivial branch of `selectedReciprocalBound`. -/
lemma selectedReciprocalBound_eq_trivial
    (x : ℝ) (A B : ℕ)
    (hdirect : ¬ x / ((A + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 2)
    (hk2 : ¬ (12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4 ∧
      ((A + 1 : ℕ) : ℝ) ^ 4 <
        12 * x * (Nat.sqrt (B - A) : ℝ) ^ 3))
    (hk1 : ¬ 4 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 3) :
    selectedReciprocalBound x A B = (B - A : ℕ) := by
  simp only [selectedReciprocalBound, if_neg hdirect, if_neg hk2, if_neg hk1]

/-- The selected bound controls every nonempty dyadic reciprocal interval.
The proof performs the same direct/one-step/two-step split encoded in the
definition, and uses the trivial estimate only in the residual branch. -/
lemma norm_reciprocalExpSum_le_selected
    (x : ℝ) (A B : ℕ) (hx : 0 < x) (hAB : A < B)
    (hdyadic : B - A ≤ A + 1) :
    ‖reciprocalExpSum x A B‖ ≤ selectedReciprocalBound x A B := by
  let C : ℕ := A + 1
  have hC : 0 < C := by omega
  by_cases hdirect : x / (C : ℝ) ^ 2 ≤ 1 / 2
  · have h := norm_reciprocalExpSum_le_firstDerivative
      x A B hx hAB.le (by simpa only [C] using hdirect)
    simpa only [selectedReciprocalBound, C, if_pos hdirect] using h
  · have hC2 : (C : ℝ) ^ 2 < 2 * x := by
      have hC2pos : 0 < (C : ℝ) ^ 2 := by positivity
      have hlt : 1 / 2 < x / (C : ℝ) ^ 2 := lt_of_not_ge hdirect
      rw [lt_div_iff₀ hC2pos] at hlt
      nlinarith
    have hmiddle : (C : ℝ) ^ 3 < 4 * x * (C : ℝ) := by
      have hCr : 0 < (C : ℝ) := by positivity
      nlinarith [mul_lt_mul_of_pos_right hC2 hCr]
    by_cases hk2 : 12 * x ≤ (C : ℝ) ^ 4 ∧
        (C : ℝ) ^ 4 <
          12 * x * (Nat.sqrt (B - A) : ℝ) ^ 3
    · have h := norm_reciprocalExpSum_le_dyadic_qfree
        x A B hx hAB.le hAB hdyadic
          (by simpa only [C] using hk2.1) (by simpa only [C] using hk2.2)
      simp only [selectedReciprocalBound, C, if_neg hdirect, if_pos hk2]
      exact h
    · by_cases hk1 : 4 * x ≤ (C : ℝ) ^ 3
      · have h := norm_reciprocalExpSum_le_dyadic_qfree_k1
          x A B hx hAB.le hdyadic (by simpa only [C] using hk1)
            (by simpa only [C] using hmiddle)
        simp only [selectedReciprocalBound, C, if_neg hdirect, if_neg hk2,
          if_pos hk1]
        exact h
      · have h := norm_reciprocalExpSum_le x A B
        simpa only [selectedReciprocalBound, C, if_neg hdirect, if_neg hk2,
          if_neg hk1] using h

/-- The effective pointwise majorant is the better of the selected analytic
estimate and the trivial interval-length estimate.  This minimum is crucial
when the two-step high-frequency condition fails: the correlation interval
is then short even if the one-step formula itself is comparatively large. -/
noncomputable def effectiveReciprocalBound (x : ℝ) (A B : ℕ) : ℝ :=
  min (selectedReciprocalBound x A B) (B - A : ℕ)

/-- Every nonempty dyadic reciprocal interval is bounded by the effective
minimum of the analytic and trivial estimates. -/
lemma norm_reciprocalExpSum_le_effective
    (x : ℝ) (A B : ℕ) (hx : 0 < x) (hAB : A < B)
    (hdyadic : B - A ≤ A + 1) :
    ‖reciprocalExpSum x A B‖ ≤ effectiveReciprocalBound x A B := by
  unfold effectiveReciprocalBound
  apply le_min
  · exact norm_reciprocalExpSum_le_selected x A B hx hAB hdyadic
  · exact norm_reciprocalExpSum_le x A B

/-- The effective majorant is nonnegative at positive frequency. -/
lemma effectiveReciprocalBound_nonneg
    (x : ℝ) (A B : ℕ) (hx : 0 < x) :
    0 ≤ effectiveReciprocalBound x A B := by
  unfold effectiveReciprocalBound selectedReciprocalBound
  dsimp only
  split_ifs <;> positivity

/-- Interpolation in the middle/high-failure range.  Write `C=A+1`,
`N=B-A`, and `L=1+log C`.  If the direct branch fails, the two-step upper
condition holds, but its lower-frequency condition fails, then taking the
minimum with the trivial length bound gives the uniform seventh-power
estimate `q⁷ ≤ 147456 C⁶ L²`.  This covers both the one-step branch and
the final trivial branch. -/
lemma effectiveReciprocalBound_seventh_le_of_high_fail
    (t : ℝ) (A B : ℕ) (ht : 0 < t) (hAB : A < B)
    (hdyadic : B - A ≤ A + 1)
    (hdirect : ¬ t / (((A + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / 2)
    (hhone : 12 * t ≤ (((A + 1 : ℕ) : ℝ)) ^ 4)
    (hhigh : ¬ (((A + 1 : ℕ) : ℝ)) ^ 4 <
      12 * t * (Nat.sqrt (B - A) : ℝ) ^ 3) :
    effectiveReciprocalBound t A B ^ 7 ≤
      147456 * (((A + 1 : ℕ) : ℝ)) ^ 6 *
        (1 + Real.log (((A + 1 : ℕ) : ℝ))) ^ 2 := by
  let C : ℕ := A + 1
  let N : ℕ := B - A
  let s : ℕ := Nat.sqrt N
  let L : ℝ := 1 + Real.log (C : ℝ)
  let q : ℝ := effectiveReciprocalBound t A B
  have hC : 0 < C := by omega
  have hN : 0 < N := by dsimp only [N]; omega
  have hq0 : 0 ≤ q := effectiveReciprocalBound_nonneg t A B ht
  have hqN : q ≤ (N : ℝ) := by
    dsimp only [q, effectiveReciprocalBound, N]
    exact min_le_right _ _
  have hLone : 1 ≤ L := by
    dsimp only [L]
    have hlog : 0 ≤ Real.log (C : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ C by omega)
    linarith
  have hL0 : 0 ≤ L := hLone.trans' (by norm_num)
  have hhighFails : 12 * t * (s : ℝ) ^ 3 ≤ (C : ℝ) ^ 4 := by
    have hh : 12 * t * (Nat.sqrt (B - A) : ℝ) ^ 3 ≤
        (((A + 1 : ℕ) : ℝ)) ^ 4 := le_of_not_gt hhigh
    simpa only [C, N, s] using hh
  have hk2 : ¬ (12 * t ≤ (C : ℝ) ^ 4 ∧
      (C : ℝ) ^ 4 < 12 * t * (s : ℝ) ^ 3) := by
    push_neg
    intro _
    exact hhighFails
  by_cases hk1 : 4 * t ≤ (C : ℝ) ^ 3
  · have hqSelected : q ≤ selectedReciprocalBound t A B := by
      dsimp only [q, effectiveReciprocalBound]
      exact min_le_left _ _
    have hqFormula : q ≤
        24 * (C : ℝ) * Real.sqrt (t / (C : ℝ) ^ 3) * Real.sqrt L := by
      rw [selectedReciprocalBound_eq_k1 t A B
        (by simpa only [C] using hdirect)
        (by simpa only [C, N, s] using hk2)
        (by simpa only [C] using hk1)] at hqSelected
      simpa only [C, L] using hqSelected
    have hinterp := effective_k1_highFailure_seventh_le
      C N t L q hC hN ht.le hL0 hq0 hqN hqFormula hhighFails
    simpa only [q, C, L] using hinterp
  · have hmiddle : (C : ℝ) ^ 3 < 4 * t := lt_of_not_ge hk1
    have hN4 : N ^ 4 ≤ 256 * C ^ 3 :=
      residual_interval_length_fourth_le C N t hC hN hmiddle hhighFails
    have hq7N : q ^ 7 ≤ (N : ℝ) ^ 7 := pow_le_pow_left₀ hq0 hqN 7
    have hNleC : N ≤ C := by simpa only [N, C] using hdyadic
    have hpoly : N ^ 7 ≤ 256 * C ^ 6 := by
      calc
        N ^ 7 = N ^ 3 * N ^ 4 := by ring
        _ ≤ C ^ 3 * (256 * C ^ 3) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hNleC 3) hN4
        _ = 256 * C ^ 6 := by ring
    calc
      q ^ 7 ≤ (N : ℝ) ^ 7 := hq7N
      _ ≤ 256 * (C : ℝ) ^ 6 := by exact_mod_cast hpoly
      _ ≤ 147456 * (C : ℝ) ^ 6 * L ^ 2 := by
        have hLsq : 1 ≤ L ^ 2 := by nlinarith
        nlinarith [sq_nonneg ((C : ℝ) ^ 3)]
      _ = 147456 * (((A + 1 : ℕ) : ℝ)) ^ 6 *
          (1 + Real.log (((A + 1 : ℕ) : ℝ))) ^ 2 := by rfl

/-- Effective-bound eliminator in the direct branch. -/
lemma effectiveReciprocalBound_le_direct
    (t : ℝ) (A B : ℕ)
    (hdirect : t / (((A + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / 2) :
    effectiveReciprocalBound t A B ≤ ((B + 1 : ℕ) : ℝ) ^ 2 / t := by
  calc
    effectiveReciprocalBound t A B ≤ selectedReciprocalBound t A B := by
      exact min_le_left _ _
    _ = ((B + 1 : ℕ) : ℝ) ^ 2 / t :=
      selectedReciprocalBound_eq_direct t A B hdirect

/-- Effective-bound eliminator in the two-step branch. -/
lemma effectiveReciprocalBound_le_k2
    (t : ℝ) (A B : ℕ)
    (hdirect : ¬ t / (((A + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / 2)
    (hk2 : 12 * t ≤ (((A + 1 : ℕ) : ℝ)) ^ 4 ∧
      (((A + 1 : ℕ) : ℝ)) ^ 4 <
        12 * t * (Nat.sqrt (B - A) : ℝ) ^ 3) :
    effectiveReciprocalBound t A B ≤
      128 * ((B - A : ℕ) : ℝ) *
        (t / (((A + 1 : ℕ) : ℝ)) ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt (1 + Real.log (((A + 1 : ℕ) : ℝ))) := by
  calc
    effectiveReciprocalBound t A B ≤ selectedReciprocalBound t A B := by
      exact min_le_left _ _
    _ = _ := selectedReciprocalBound_eq_k2 t A B hdirect hk2

/-- Complete branch trichotomy for the effective reciprocal majorant.
Under the two-step upper condition, every nonempty dyadic interval is
controlled either by the direct formula, by the k2 formula, or by the
seventh-power interpolation bound. -/
lemma effectiveReciprocalBound_direct_or_k2_or_seventh
    (t : ℝ) (A B : ℕ) (ht : 0 < t) (hAB : A < B)
    (hdyadic : B - A ≤ A + 1)
    (hhone : 12 * t ≤ (((A + 1 : ℕ) : ℝ)) ^ 4) :
    effectiveReciprocalBound t A B ≤ ((B + 1 : ℕ) : ℝ) ^ 2 / t ∨
      effectiveReciprocalBound t A B ≤
        128 * ((B - A : ℕ) : ℝ) *
          (t / (((A + 1 : ℕ) : ℝ)) ^ 4) ^ (1 / 6 : ℝ) *
            Real.sqrt (1 + Real.log (((A + 1 : ℕ) : ℝ))) ∨
      effectiveReciprocalBound t A B ^ 7 ≤
        147456 * (((A + 1 : ℕ) : ℝ)) ^ 6 *
          (1 + Real.log (((A + 1 : ℕ) : ℝ))) ^ 2 := by
  by_cases hdirect : t / (((A + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / 2
  · exact Or.inl (effectiveReciprocalBound_le_direct t A B hdirect)
  · by_cases hhigh : (((A + 1 : ℕ) : ℝ)) ^ 4 <
        12 * t * (Nat.sqrt (B - A) : ℝ) ^ 3
    · exact Or.inr <| Or.inl <|
        effectiveReciprocalBound_le_k2 t A B hdirect ⟨hhone, hhigh⟩
    · exact Or.inr <| Or.inr <|
        effectiveReciprocalBound_seventh_le_of_high_fail
          t A B ht hAB hdyadic hdirect hhone hhigh

/-! ### Elementary dyadic phase and endpoint bounds -/

/-- Exact absolute reciprocal-difference formula in terms of natural
distance. -/
lemma abs_one_div_sub_one_div_eq_dist_div
    (v w : ℕ) (hv : 0 < v) (hw : 0 < w) :
    |1 / (w : ℝ) - 1 / (v : ℝ)| =
      (Nat.dist v w : ℝ) / ((v : ℝ) * (w : ℝ)) := by
  by_cases hvw : v ≤ w
  · have hinv : 1 / (w : ℝ) ≤ 1 / (v : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hvw)
    rw [abs_of_nonpos (sub_nonpos.mpr hinv), Nat.dist_eq_sub_of_le hvw,
      Nat.cast_sub hvw]
    field_simp <;> ring
  · have hwv : w ≤ v := Nat.le_of_not_ge hvw
    have hinv : 1 / (v : ℝ) ≤ 1 / (w : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hwv)
    rw [abs_of_nonneg (sub_nonneg.mpr hinv), Nat.dist_comm,
      Nat.dist_eq_sub_of_le hwv, Nat.cast_sub hwv]
    field_simp <;> ring

/-- On the power block `V ≤ v,w < 2V`, written as the shifted interval
`(V-1,2V-1]`, a nonzero reciprocal phase difference has the uniform lower
bound used for the direct branch. -/
lemma dyadic_reciprocalPhaseDifference_lower
    (x : ℝ) (V v w : ℕ) (hx : 0 < x) (hV : 0 < V)
    (hv : v ∈ Finset.Ioc (V - 1) (2 * V - 1))
    (hw : w ∈ Finset.Ioc (V - 1) (2 * V - 1))
    (hvw : v ≠ w) :
    x / (4 * (V : ℝ) ^ 2) ≤
      |x * (1 / (w : ℝ) - 1 / (v : ℝ))| := by
  have hvI := Finset.mem_Ioc.mp hv
  have hwI := Finset.mem_Ioc.mp hw
  have hvpos : 0 < v := by omega
  have hwpos : 0 < w := by omega
  have hdist : 1 ≤ Nat.dist v w := by
    unfold Nat.dist
    omega
  have hden : (v : ℝ) * (w : ℝ) ≤
      (2 * (V : ℝ)) * (2 * (V : ℝ)) := by
    have hvR : (v : ℝ) ≤ 2 * (V : ℝ) := by
      exact_mod_cast (show v ≤ 2 * V by omega)
    have hwR : (w : ℝ) ≤ 2 * (V : ℝ) := by
      exact_mod_cast (show w ≤ 2 * V by omega)
    exact mul_le_mul hvR hwR (by positivity) (by positivity)
  have hratio : 1 / (4 * (V : ℝ) ^ 2) ≤
      (Nat.dist v w : ℝ) / ((v : ℝ) * (w : ℝ)) := by
    have hnum : (1 : ℝ) ≤ Nat.dist v w := by exact_mod_cast hdist
    have hdenpos : 0 < (v : ℝ) * (w : ℝ) := by positivity
    have hfourpos : 0 < 4 * (V : ℝ) ^ 2 := by positivity
    rw [div_le_div_iff₀ hfourpos hdenpos]
    nlinarith
  rw [abs_mul, abs_of_pos hx,
    abs_one_div_sub_one_div_eq_dist_div v w hvpos hwpos]
  calc
    x / (4 * (V : ℝ) ^ 2) =
        x * (1 / (4 * (V : ℝ) ^ 2)) := by ring
    _ ≤ x * ((Nat.dist v w : ℝ) / ((v : ℝ) * (w : ℝ))) :=
      mul_le_mul_of_nonneg_left hratio hx.le

/-- A distance-sensitive version of the dyadic lower phase bound.  For a
far pair with `T < dist v w`, the numerator gains the factor `T+1`. -/
lemma dyadic_reciprocalPhaseDifference_lower_of_dist
    (x : ℝ) (V T v w : ℕ) (hx : 0 < x) (hV : 0 < V)
    (hv : v ∈ Finset.Ioc (V - 1) (2 * V - 1))
    (hw : w ∈ Finset.Ioc (V - 1) (2 * V - 1))
    (hdist : T < Nat.dist v w) :
    x * (T + 1 : ℕ) / (4 * (V : ℝ) ^ 2) ≤
      |x * (1 / (w : ℝ) - 1 / (v : ℝ))| := by
  have hvI := Finset.mem_Ioc.mp hv
  have hwI := Finset.mem_Ioc.mp hw
  have hvpos : 0 < v := by omega
  have hwpos : 0 < w := by omega
  have hden : (v : ℝ) * (w : ℝ) ≤
      (2 * (V : ℝ)) * (2 * (V : ℝ)) := by
    have hvR : (v : ℝ) ≤ 2 * (V : ℝ) := by
      exact_mod_cast (show v ≤ 2 * V by omega)
    have hwR : (w : ℝ) ≤ 2 * (V : ℝ) := by
      exact_mod_cast (show w ≤ 2 * V by omega)
    exact mul_le_mul hvR hwR (by positivity) (by positivity)
  have hratio : ((T + 1 : ℕ) : ℝ) / (4 * (V : ℝ) ^ 2) ≤
      (Nat.dist v w : ℝ) / ((v : ℝ) * (w : ℝ)) := by
    have hnum : (((T + 1 : ℕ) : ℝ)) ≤ Nat.dist v w := by
      exact_mod_cast (show T + 1 ≤ Nat.dist v w by omega)
    have hdenpos : 0 < (v : ℝ) * (w : ℝ) := by positivity
    have hfourpos : 0 < 4 * (V : ℝ) ^ 2 := by positivity
    rw [div_le_div_iff₀ hfourpos hdenpos]
    nlinarith
  rw [abs_mul, abs_of_pos hx,
    abs_one_div_sub_one_div_eq_dist_div v w hvpos hwpos]
  calc
    x * (T + 1 : ℕ) / (4 * (V : ℝ) ^ 2) =
        x * (((T + 1 : ℕ) : ℝ) / (4 * (V : ℝ) ^ 2)) := by ring
    _ ≤ x * ((Nat.dist v w : ℝ) / ((v : ℝ) * (w : ℝ))) :=
      mul_le_mul_of_nonneg_left hratio hx.le

/-- On the same dyadic block, every reciprocal phase difference is at most
`x/V`. -/
lemma dyadic_reciprocalPhaseDifference_upper
    (x : ℝ) (V v w : ℕ) (hx : 0 < x) (hV : 0 < V)
    (hv : v ∈ Finset.Ioc (V - 1) (2 * V - 1))
    (hw : w ∈ Finset.Ioc (V - 1) (2 * V - 1)) :
    |x * (1 / (w : ℝ) - 1 / (v : ℝ))| ≤ x / (V : ℝ) := by
  have hvI := Finset.mem_Ioc.mp hv
  have hwI := Finset.mem_Ioc.mp hw
  have hvpos : 0 < v := by omega
  have hwpos : 0 < w := by omega
  have hdist : Nat.dist v w ≤ V := by
    unfold Nat.dist
    omega
  have hden : (V : ℝ) * (V : ℝ) ≤ (v : ℝ) * (w : ℝ) := by
    have hvR : (V : ℝ) ≤ v := by
      exact_mod_cast (show V ≤ v by omega)
    have hwR : (V : ℝ) ≤ w := by
      exact_mod_cast (show V ≤ w by omega)
    exact mul_le_mul hvR hwR (by positivity) (by positivity)
  have hratio : (Nat.dist v w : ℝ) / ((v : ℝ) * (w : ℝ)) ≤
      1 / (V : ℝ) := by
    have hnum : (Nat.dist v w : ℝ) ≤ V := by exact_mod_cast hdist
    have hdenpos : 0 < (v : ℝ) * (w : ℝ) := by positivity
    have hVpos : 0 < (V : ℝ) := by positivity
    rw [div_le_div_iff₀ hdenpos hVpos]
    nlinarith
  rw [abs_mul, abs_of_pos hx,
    abs_one_div_sub_one_div_eq_dist_div v w hvpos hwpos]
  calc
    x * ((Nat.dist v w : ℝ) / ((v : ℝ) * (w : ℝ))) ≤
        x * (1 / (V : ℝ)) := mul_le_mul_of_nonneg_left hratio hx.le
    _ = x / (V : ℝ) := by ring

/-- The lower correlation endpoint for a power block satisfies
`U ≤ C+1`. -/
lemma correlationLower_powerBlock_add_one_ge
    (y U v w : ℕ) (hU : 0 < U) :
    U ≤ correlationLower y (U - 1) v w + 1 := by
  have h := le_max_left (U - 1) (max (y / v) (y / w))
  unfold correlationLower
  omega

/-- The upper correlation endpoint for a power block satisfies
`E+1 ≤ 2U`. -/
lemma correlationUpper_powerBlock_add_one_le
    (y' U v w : ℕ) (hU : 0 < U) :
    correlationUpper y' (2 * U - 1) v w + 1 ≤ 2 * U := by
  have h := min_le_left (2 * U - 1) (min (y' / v) (y' / w))
  unfold correlationUpper
  omega

/-- Every nonempty correlation interval cut out of a power block has length
at most `U`. -/
lemma correlationEndpoints_powerBlock_length_le
    (y y' U v w : ℕ) (hU : 0 < U) :
    correlationUpper y' (2 * U - 1) v w -
        correlationLower y (U - 1) v w ≤ U := by
  have hC := correlationLower_powerBlock_add_one_ge y U v w hU
  have hE := correlationUpper_powerBlock_add_one_le y' U v w hU
  omega

/-- On a nonempty correlation interval, its shifted lower endpoint is at
most the upper edge `2U`; consequently its logarithm is at most
`log(2U)`. -/
lemma log_correlationLower_powerBlock_add_one_le
    (y y' U v w : ℕ) (hU : 0 < U)
    (hCE : correlationLower y (U - 1) v w <
      correlationUpper y' (2 * U - 1) v w) :
    Real.log ((correlationLower y (U - 1) v w + 1 : ℕ) : ℝ) ≤
      Real.log ((2 * U : ℕ) : ℝ) := by
  have hE := correlationUpper_powerBlock_add_one_le y' U v w hU
  have hnat : correlationLower y (U - 1) v w + 1 ≤ 2 * U := by omega
  apply Real.log_le_log
  · positivity
  · exact_mod_cast hnat

/-- Polynomial short-interval consequence of a far-pair phase lower bound
and failure of the two-step high-frequency condition.  The power-block
threshold relation `U³ ≤ 8T⁴` converts the two analytic inequalities into
the rounding-stable estimate `N⁶ ≤ 2³⁹ U⁵`. -/
lemma residual_length_sixth_le_of_threshold
    (U T N : ℕ) (t : ℝ) (hU : 0 < U) (hN : 0 < N)
    (hphase : (U : ℝ) ^ 2 * (T : ℝ) ≤ 16 * t)
    (hhighFails : 12 * t * (Nat.sqrt N : ℝ) ^ 3 ≤
      16 * (U : ℝ) ^ 4)
    (hthreshold : U ^ 3 ≤ 8 * T ^ 4) :
    N ^ 6 ≤ 2 ^ 39 * U ^ 5 := by
  let s := Nat.sqrt N
  have hs : 0 < s := by
    dsimp only [s]
    exact Nat.sqrt_pos.mpr hN
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hscaled :
      3 * (U : ℝ) ^ 2 * (T : ℝ) * (s : ℝ) ^ 3 ≤
        48 * t * (s : ℝ) ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_right hphase
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (by positivity : 0 ≤ (s : ℝ) ^ 3))
    nlinarith
  have hscaled' :
      48 * t * (s : ℝ) ^ 3 ≤ 64 * (U : ℝ) ^ 4 := by
    nlinarith [hhighFails]
  have hTsR : (T : ℝ) * (s : ℝ) ^ 3 ≤
      64 * (U : ℝ) ^ 2 := by
    have hUpos : 0 < (U : ℝ) := by exact_mod_cast hU
    have hboth := hscaled.trans hscaled'
    nlinarith [sq_pos_of_pos hUpos]
  have hTs : T * s ^ 3 ≤ 64 * U ^ 2 := by
    exact_mod_cast hTsR
  have hTs4raw := Nat.pow_le_pow_left hTs 4
  have hTs4 : T ^ 4 * s ^ 12 ≤ 64 ^ 4 * U ^ 8 := by
    calc
      T ^ 4 * s ^ 12 = (T * s ^ 3) ^ 4 := by ring
      _ ≤ (64 * U ^ 2) ^ 4 := hTs4raw
      _ = 64 ^ 4 * U ^ 8 := by ring
  have hUs : U ^ 3 * s ^ 12 ≤ 8 * 64 ^ 4 * U ^ 8 := by
    calc
      U ^ 3 * s ^ 12 ≤ (8 * T ^ 4) * s ^ 12 :=
        Nat.mul_le_mul_right (s ^ 12) hthreshold
      _ = 8 * (T ^ 4 * s ^ 12) := by ring
      _ ≤ 8 * (64 ^ 4 * U ^ 8) := Nat.mul_le_mul_left 8 hTs4
      _ = 8 * 64 ^ 4 * U ^ 8 := by ring
  have hs12 : s ^ 12 ≤ 8 * 64 ^ 4 * U ^ 5 := by
    have hfac : U ^ 3 * s ^ 12 ≤
        U ^ 3 * (8 * 64 ^ 4 * U ^ 5) := by
      calc
        U ^ 3 * s ^ 12 ≤ 8 * 64 ^ 4 * U ^ 8 := hUs
        _ = U ^ 3 * (8 * 64 ^ 4 * U ^ 5) := by ring
    exact Nat.le_of_mul_le_mul_left hfac (pow_pos hU 3)
  have hNsq : N ≤ 4 * s ^ 2 := by
    have hroot := Nat.lt_succ_sqrt N
    dsimp only [s] at hroot ⊢
    nlinarith
  have hN6 := Nat.pow_le_pow_left hNsq 6
  calc
    N ^ 6 ≤ (4 * s ^ 2) ^ 6 := hN6
    _ = 4 ^ 6 * s ^ 12 := by ring
    _ ≤ 4 ^ 6 * (8 * 64 ^ 4 * U ^ 5) := Nat.mul_le_mul_left _ hs12
    _ = 2 ^ 39 * U ^ 5 := by norm_num; ring

/-- Closed T=0 far-correlation majorant for an oriented pair of power
blocks.  The three summands are respectively the direct, two-step, and
interpolated high-failure bounds. -/
noncomputable def orientedPowerBlockFarQ (x : ℝ) (U V : ℕ) : ℝ :=
  16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x +
    128 * (U : ℝ) *
      (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log (2 * (U : ℝ))) +
    128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
      (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ)

noncomputable def farCorrelationMajorant
    (x : ℝ) (y y' A B v w : ℕ) : ℝ :=
  let C := correlationLower y A v w
  let E := correlationUpper y' B v w
  let t := |x * (1 / (w : ℝ) - 1 / (v : ℝ))|
  if C < E then effectiveReciprocalBound t C E else 0

/-- Every nonzero-distance correlation of two oriented power blocks is
bounded by `orientedPowerBlockFarQ`, provided the simple upper-frequency
scale inequality holds. -/
lemma farCorrelationMajorant_powerBlock_zero_le
    (x : ℝ) (y y' U V v w : ℕ)
    (hx : 0 < x) (hU : 0 < U) (hV : 0 < V)
    (hhoneScale : 12 * (x / (V : ℝ)) ≤ (U : ℝ) ^ 4)
    (hv : v ∈ Finset.Ioc (V - 1) (2 * V - 1))
    (hw : w ∈ Finset.Ioc (V - 1) (2 * V - 1))
    (hdist : 0 < Nat.dist v w) :
    farCorrelationMajorant x y y' (U - 1) (2 * U - 1) v w ≤
      orientedPowerBlockFarQ x U V := by
  let C := correlationLower y (U - 1) v w
  let E := correlationUpper y' (2 * U - 1) v w
  let t : ℝ := |x * (1 / (w : ℝ) - 1 / (v : ℝ))|
  have hLU : 0 ≤ 1 + Real.log (2 * (U : ℝ)) := by
    have harg : (1 : ℝ) ≤ 2 * (U : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * U by omega)
    have := Real.log_nonneg harg
    linarith
  have hQ0 : 0 ≤ orientedPowerBlockFarQ x U V := by
    unfold orientedPowerBlockFarQ
    positivity
  by_cases hCE : C < E
  · have hvw : v ≠ w := by
      intro heq
      subst w
      simp at hdist
    have ht : 0 < t := by
      dsimp only [t]
      have hvpos : 0 < v := by
        have := (Finset.mem_Ioc.mp hv).1
        omega
      have hwpos : 0 < w := by
        have := (Finset.mem_Ioc.mp hw).1
        omega
      have hdiff : 1 / (w : ℝ) - 1 / (v : ℝ) ≠ 0 := by
        intro hzero
        have hinv : (w : ℝ)⁻¹ = (v : ℝ)⁻¹ := by
          simpa only [one_div] using sub_eq_zero.mp hzero
        have hcast : (w : ℝ) = (v : ℝ) := inv_injective hinv
        apply hvw
        exact_mod_cast hcast.symm
      exact abs_pos.mpr (mul_ne_zero (ne_of_gt hx) hdiff)
    have htLower : x / (4 * (V : ℝ) ^ 2) ≤ t := by
      simpa only [t] using
        dyadic_reciprocalPhaseDifference_lower x V v w hx hV hv hw hvw
    have htUpper : t ≤ x / (V : ℝ) := by
      simpa only [t] using
        dyadic_reciprocalPhaseDifference_upper x V v w hx hV hv hw
    have hClo : U ≤ C + 1 := by
      simpa only [C] using correlationLower_powerBlock_add_one_ge y U v w hU
    have hEhi : E + 1 ≤ 2 * U := by
      simpa only [E] using correlationUpper_powerBlock_add_one_le y' U v w hU
    have hN : E - C ≤ U := by
      simpa only [C, E] using
        correlationEndpoints_powerBlock_length_le y y' U v w hU
    have hlog : Real.log ((C + 1 : ℕ) : ℝ) ≤
        Real.log (2 * (U : ℝ)) := by
      simpa only [C, Nat.cast_mul, Nat.cast_ofNat] using
        log_correlationLower_powerBlock_add_one_le y y' U v w hU hCE
    have hdyadic : E - C ≤ C + 1 := hN.trans hClo
    have hhone : 12 * t ≤ ((C + 1 : ℕ) : ℝ) ^ 4 := by
      have hU4 : (U : ℝ) ^ 4 ≤ ((C + 1 : ℕ) : ℝ) ^ 4 := by
        gcongr
      exact (mul_le_mul_of_nonneg_left htUpper (by norm_num)).trans
        (hhoneScale.trans hU4)
    have hcases := effectiveReciprocalBound_direct_or_k2_or_seventh
      t C E ht hCE hdyadic hhone
    have hmajor : farCorrelationMajorant x y y' (U - 1) (2 * U - 1) v w =
        effectiveReciprocalBound t C E := by
      unfold farCorrelationMajorant
      change (if C < E then effectiveReciprocalBound t C E else 0) = _
      rw [if_pos hCE]
    rw [hmajor]
    rcases hcases with hdirect | hk2 | hseven
    · have hnum : (((E + 1 : ℕ) : ℝ)) ^ 2 ≤
          4 * (U : ℝ) ^ 2 := by
        have hER : (((E + 1 : ℕ) : ℝ)) ≤ 2 * (U : ℝ) := by
          exact_mod_cast hEhi
        nlinarith [sq_nonneg (((E + 1 : ℕ) : ℝ) - 2 * (U : ℝ))]
      have hphaseCross : x ≤ 4 * (V : ℝ) ^ 2 * t := by
        rw [div_le_iff₀ (by positivity : 0 < 4 * (V : ℝ) ^ 2)] at htLower
        simpa only [mul_comm] using htLower
      have hdirectQ : (((E + 1 : ℕ) : ℝ)) ^ 2 / t ≤
          16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x := by
        rw [div_le_div_iff₀ ht hx]
        calc
          (((E + 1 : ℕ) : ℝ)) ^ 2 * x ≤
              (4 * (U : ℝ) ^ 2) * x :=
            mul_le_mul_of_nonneg_right hnum hx.le
          _ ≤ (4 * (U : ℝ) ^ 2) *
              (4 * (V : ℝ) ^ 2 * t) :=
            mul_le_mul_of_nonneg_left hphaseCross (by positivity)
          _ = 16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 * t := by ring
      exact (hdirect.trans hdirectQ).trans (by
        unfold orientedPowerBlockFarQ
        have htwo : 0 ≤ 128 * (U : ℝ) *
            (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
              Real.sqrt (1 + Real.log (2 * (U : ℝ))) := by positivity
        have hthree : 0 ≤ 128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
            (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ) := by
          exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
            (Real.rpow_nonneg hLU _)
        linarith)
    · have hratio : t / (((C + 1 : ℕ) : ℝ)) ^ 4 ≤
          x / ((V : ℝ) * (U : ℝ) ^ 4) := by
        calc
          t / (((C + 1 : ℕ) : ℝ)) ^ 4 ≤
              (x / (V : ℝ)) / (((C + 1 : ℕ) : ℝ)) ^ 4 :=
            div_le_div_of_nonneg_right htUpper (by positivity)
          _ ≤ (x / (V : ℝ)) / (U : ℝ) ^ 4 := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            gcongr
          _ = x / ((V : ℝ) * (U : ℝ) ^ 4) := by ring
      have hratio0 : 0 ≤ t / (((C + 1 : ℕ) : ℝ)) ^ 4 := by positivity
      have hrpow := Real.rpow_le_rpow hratio0 hratio
        (by norm_num : (0 : ℝ) ≤ 1 / 6)
      have hsqrt : Real.sqrt (1 + Real.log (((C + 1 : ℕ) : ℝ))) ≤
          Real.sqrt (1 + Real.log (2 * (U : ℝ))) := by
        apply Real.sqrt_le_sqrt
        linarith
      have hk2Q :
          128 * (((E - C : ℕ) : ℝ)) *
              (t / (((C + 1 : ℕ) : ℝ)) ^ 4) ^ (1 / 6 : ℝ) *
                Real.sqrt (1 + Real.log (((C + 1 : ℕ) : ℝ))) ≤
            128 * (U : ℝ) *
              (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
                Real.sqrt (1 + Real.log (2 * (U : ℝ))) := by
        gcongr
      exact (hk2.trans hk2Q).trans (by
        unfold orientedPowerBlockFarQ
        have hone : 0 ≤ 16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x := by
          positivity
        have hthree : 0 ≤ 128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
            (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ) := by
          exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
            (Real.rpow_nonneg hLU _)
        linarith)
    · let L : ℝ := 1 + Real.log (((C + 1 : ℕ) : ℝ))
      have hCupper : (((C + 1 : ℕ) : ℝ)) ≤ 2 * (U : ℝ) := by
        have : C + 1 ≤ 2 * U := by omega
        exact_mod_cast this
      have hL0 : 0 ≤ L := by
        dsimp only [L]
        have hCpos : (1 : ℝ) ≤ ((C + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ C + 1 by omega)
        have := Real.log_nonneg hCpos
        linarith
      have hroot := effective_k1_highFailure_le (C + 1) L
        (effectiveReciprocalBound t C E) (by omega) hL0 hseven
      have hLupper : L ≤ 1 + Real.log (2 * (U : ℝ)) := by
        dsimp only [L]
        linarith
      have hCupPow : (((C + 1 : ℕ) : ℝ)) ^ (6 / 7 : ℝ) ≤
          (2 * (U : ℝ)) ^ (6 / 7 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hCupper (by norm_num)
      have hLPow : L ^ (2 / 7 : ℝ) ≤
          (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ) :=
        Real.rpow_le_rpow hL0 hLupper (by norm_num)
      have hroot' : effectiveReciprocalBound t C E ≤
          128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
            (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ) := by
        exact hroot.trans (by gcongr)
      exact hroot'.trans (by
        unfold orientedPowerBlockFarQ
        have hone : 0 ≤ 16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x := by
          positivity
        have htwo : 0 ≤ 128 * (U : ℝ) *
            (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
              Real.sqrt (1 + Real.log (2 * (U : ℝ))) := by positivity
        linarith)
  · unfold farCorrelationMajorant
    change (if C < E then effectiveReciprocalBound t C E else 0) ≤ _
    rw [if_neg hCE]
    exact hQ0

/-- Ordered far pairs in the second-variable support. -/
def farPairs (V₀ V₁ T : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc V₀ V₁ ×ˢ Finset.Ioc V₀ V₁).filter fun p ↦
    T < Nat.dist p.1 p.2

/-- The maximum of the explicit correlation majorants over the finite set
of far pairs.  Inserting zero makes the maximum total and visibly
nonnegative, including when there are no far pairs. -/
noncomputable def threeBranchFarQ
    (x : ℝ) (y y' A B V₀ V₁ T : ℕ) : ℝ :=
  let values := (farPairs V₀ V₁ T).image fun p ↦
    farCorrelationMajorant x y y' A B p.1 p.2
  (insert 0 values).max' (by simp)

lemma threeBranchFarQ_nonneg
    (x : ℝ) (y y' A B V₀ V₁ T : ℕ) :
    0 ≤ threeBranchFarQ x y y' A B V₀ V₁ T := by
  unfold threeBranchFarQ
  dsimp only
  apply Finset.le_max'
  simp

lemma farCorrelationMajorant_le_threeBranchFarQ
    (x : ℝ) (y y' A B V₀ V₁ T v w : ℕ)
    (hv : v ∈ Finset.Ioc V₀ V₁) (hw : w ∈ Finset.Ioc V₀ V₁)
    (hfar : T < Nat.dist v w) :
    farCorrelationMajorant x y y' A B v w ≤
      threeBranchFarQ x y y' A B V₀ V₁ T := by
  unfold threeBranchFarQ
  dsimp only
  apply Finset.le_max'
  simp only [Finset.mem_insert, Finset.mem_image]
  right
  exact ⟨(v, w), by simp [farPairs, hv, hw, hfar], rfl⟩

/-- Eliminate the finite maximum by proving a uniform bound for every far
pair.  This is the main simplification interface used by the dyadic Type II
assembly. -/
lemma threeBranchFarQ_le
    (x : ℝ) (y y' A B V₀ V₁ T : ℕ) (Q : ℝ)
    (hQ : 0 ≤ Q)
    (hmajor : ∀ v ∈ Finset.Ioc V₀ V₁,
      ∀ w ∈ Finset.Ioc V₀ V₁, T < Nat.dist v w →
        farCorrelationMajorant x y y' A B v w ≤ Q) :
    threeBranchFarQ x y y' A B V₀ V₁ T ≤ Q := by
  classical
  unfold threeBranchFarQ
  dsimp only
  let values := (farPairs V₀ V₁ T).image fun p ↦
      farCorrelationMajorant x y y' A B p.1 p.2
  change (insert 0 values).max' (by simp) ≤ Q
  have hne : (insert 0 values).Nonempty := ⟨0, by simp⟩
  have hmem := Finset.max'_mem (insert 0 values) hne
  rcases Finset.mem_insert.mp hmem with hzero | hvalue
  · calc
      (insert 0 values).max' (by simp) = 0 := hzero
      _ ≤ Q := hQ
  · rcases Finset.mem_image.mp hvalue with ⟨p, hp, hpval⟩
    have hp' : (p.1 ∈ Finset.Ioc V₀ V₁ ∧
        p.2 ∈ Finset.Ioc V₀ V₁) ∧ T < Nat.dist p.1 p.2 := by
      simpa only [farPairs, Finset.mem_filter, Finset.mem_product] using hp
    rw [← hpval]
    exact hmajor p.1 hp'.1.1 p.2 hp'.1.2 hp'.2

/-- Finite-max version of the oriented power-block far-correlation bound.
At threshold zero every far pair is covered by
`farCorrelationMajorant_powerBlock_zero_le`. -/
lemma threeBranchFarQ_powerBlock_zero_le
    (x : ℝ) (y y' U V : ℕ)
    (hx : 0 < x) (hU : 0 < U) (hV : 0 < V)
    (hhoneScale : 12 * (x / (V : ℝ)) ≤ (U : ℝ) ^ 4) :
    threeBranchFarQ x y y' (U - 1) (2 * U - 1)
        (V - 1) (2 * V - 1) 0 ≤
      orientedPowerBlockFarQ x U V := by
  apply threeBranchFarQ_le
  · unfold orientedPowerBlockFarQ
    have hLU : 0 ≤ 1 + Real.log (2 * (U : ℝ)) := by
      have harg : (1 : ℝ) ≤ 2 * (U : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * U by omega)
      have := Real.log_nonneg harg
      linarith
    have hthree : 0 ≤ 128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
        (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ) := by
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg hLU _)
    positivity
  · intro v hv w hw hdist
    exact farCorrelationMajorant_powerBlock_zero_le
      x y y' U V v w hx hU hV hhoneScale hv hw hdist

/-- A fully concrete near--far Type II bound.  It has no exponential-sum,
mean-square, `hfarQ`, or high-frequency premise.  Each far pair is handled
by the three-branch reciprocal estimate when its upper-frequency condition
holds and by the trivial cardinality estimate otherwise. -/
lemma norm_reciprocalBilinearSum_Ioc_le_near_far
    (x : ℝ) (y y' A B V₀ V₁ T : ℕ) (alpha beta : ℕ → ℂ)
    (hx : 0 < x) (hdyadic : B - A ≤ A + 1) :
    ‖reciprocalBilinearSum (Finset.Ioc y y') (Finset.Ioc A B)
        (Finset.Ioc V₀ V₁) x alpha beta‖ ≤
      l2Norm (Finset.Ioc A B) alpha *
        Real.sqrt
          (2 * (B - A : ℕ) * (2 * T + 1) +
            threeBranchFarQ x y y' A B V₀ V₁ T *
              ((V₁ - V₀ : ℕ) : ℝ)) *
          l2Norm (Finset.Ioc V₀ V₁) beta := by
  let Q := threeBranchFarQ x y y' A B V₀ V₁ T
  have hQ : 0 ≤ Q := threeBranchFarQ_nonneg x y y' A B V₀ V₁ T
  have hcardAB : (Finset.Ioc A B).card = B - A := by simp
  have hcardV : (Finset.Ioc V₀ V₁).card = V₁ - V₀ := by simp
  have hnear : ∀ v ∈ Finset.Ioc V₀ V₁,
      ∀ w ∈ Finset.Ioc V₀ V₁, Nat.dist v w ≤ T →
        ‖kernelCorrelation (Finset.Ioc A B)
          (restrictedReciprocalKernel (Finset.Ioc y y') x) v w‖ ≤
            ((B - A : ℕ) : ℝ) := by
    intro v hv w hw hn
    simpa only [hcardAB] using
      norm_kernelCorrelation_restrictedReciprocalKernel_le_card
        (Finset.Ioc y y') (Finset.Ioc A B) x v w
  have hfar : ∀ v ∈ Finset.Ioc V₀ V₁,
      ∀ w ∈ Finset.Ioc V₀ V₁, T < Nat.dist v w →
        ‖kernelCorrelation (Finset.Ioc A B)
          (restrictedReciprocalKernel (Finset.Ioc y y') x) v w‖ ≤ Q := by
    intro v hv w hw hdist
    have hvpos : 0 < v := by
      have := (Finset.mem_Ioc.mp hv).1
      omega
    have hwpos : 0 < w := by
      have := (Finset.mem_Ioc.mp hw).1
      omega
    let C := correlationLower y A v w
    let E := correlationUpper y' B v w
    let t : ℝ := |x * (1 / (w : ℝ) - 1 / (v : ℝ))|
    have htoQ : farCorrelationMajorant x y y' A B v w ≤ Q :=
      farCorrelationMajorant_le_threeBranchFarQ
        x y y' A B V₀ V₁ T v w hv hw hdist
    rw [norm_kernelCorrelation_restrictedReciprocalKernel_Ioc_eq_abs
      x y y' A B v w hvpos hwpos]
    change ‖reciprocalExpSum t C E‖ ≤ Q
    by_cases hCE : C < E
    · have ht : 0 < t := by
        dsimp only [t]
        have hvw : v ≠ w := by
          intro heq
          subst w
          simp at hdist
        have hdiff : 1 / (w : ℝ) - 1 / (v : ℝ) ≠ 0 := by
          intro hzero
          have hinv : (w : ℝ)⁻¹ = (v : ℝ)⁻¹ := by
            simpa only [one_div] using sub_eq_zero.mp hzero
          have hcast : (w : ℝ) = (v : ℝ) := inv_injective hinv
          apply hvw
          exact_mod_cast hcast.symm
        exact abs_pos.mpr (mul_ne_zero (ne_of_gt hx) hdiff)
      have hbase := norm_reciprocalExpSum_le_effective
        t C E ht hCE (by
          dsimp only [C, E, correlationLower, correlationUpper]
          omega)
      have hmajor : farCorrelationMajorant x y y' A B v w =
          effectiveReciprocalBound t C E := by
        unfold farCorrelationMajorant
        change (if C < E then effectiveReciprocalBound t C E else 0) = _
        rw [if_pos hCE]
      rw [hmajor] at htoQ
      exact hbase.trans htoQ
    · have hempty : Finset.Ioc C E = ∅ := Finset.Ioc_eq_empty hCE
      simpa [reciprocalExpSum, hempty] using hQ
  unfold reciprocalBilinearSum
  have hbound := norm_bilinearSum_le_natDist_near_far
    (Finset.Ioc A B) (Finset.Ioc V₀ V₁) alpha beta
    (restrictedReciprocalKernel (Finset.Ioc y y') x)
    T (B - A : ℕ) Q (by positivity) hQ hnear hfar
  simpa only [Q, hcardV] using hbound


end Erdos175.TypeII
