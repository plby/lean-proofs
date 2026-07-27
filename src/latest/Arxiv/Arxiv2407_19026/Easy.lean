import Arxiv.Arxiv2407_19026.Basic

/-!
# The elementary candidate argument

This file formalizes Section 2 of arXiv:2407.19026.  The first result is
Lemma `l:FpAvg`, including the sum-of-squares identity underlying it.
-/

open Finset

noncomputable section

namespace Arxiv2407_19026

lemma sum_redEdgesBetween_redNeighborsIn {V : Type*} (G : SimpleGraph V)
    (X Y : Finset V) :
    (∑ v ∈ X, redEdgesBetween G X (redNeighborsIn G v Y)) =
      ∑ y ∈ Y, (redNeighborsIn G y X).card ^ 2 := by
  classical
  calc
    (∑ v ∈ X, redEdgesBetween G X (redNeighborsIn G v Y)) =
        ∑ v ∈ X, ∑ y ∈ redNeighborsIn G v Y,
          (redNeighborsIn G y X).card := by
      apply sum_congr rfl
      intro v hv
      rw [redEdgesBetween_comm, redEdgesBetween_eq_sum_card]
    _ = ∑ y ∈ Y, ∑ v ∈ redNeighborsIn G y X,
          (redNeighborsIn G y X).card := by
      simp only [redNeighborsIn, sum_filter]
      rw [sum_comm]
      simp only [G.adj_comm]
    _ = ∑ y ∈ Y, (redNeighborsIn G y X).card ^ 2 := by
      apply sum_congr rfl
      intro y hy
      simp [pow_two]

lemma sum_card_redNeighborsIn {V : Type*} (G : SimpleGraph V)
    (X Y : Finset V) :
    (∑ v ∈ X, (redNeighborsIn G v Y).card) = redEdgesBetween G X Y := by
  exact (redEdgesBetween_eq_sum_card G X Y).symm

lemma excess_averaging_identity {V : Type*} (G : SimpleGraph V)
    (X Y : Finset V) (p : ℝ) :
    (∑ v ∈ X, excessBetween p G X (redNeighborsIn G v Y)) -
        p * X.card * excessBetween p G X Y =
      ∑ y ∈ Y,
        ((redNeighborsIn G y X).card - p * X.card) ^ 2 := by
  classical
  have hsq :
      (∑ v ∈ X, (redEdgesBetween G X (redNeighborsIn G v Y) : ℝ)) =
        ∑ y ∈ Y, ((redNeighborsIn G y X).card : ℝ) ^ 2 := by
    exact_mod_cast sum_redEdgesBetween_redNeighborsIn G X Y
  have hdegX :
      (∑ v ∈ X, ((redNeighborsIn G v Y).card : ℝ)) =
        redEdgesBetween G X Y := by
    exact_mod_cast sum_card_redNeighborsIn G X Y
  have hdegY :
      (∑ y ∈ Y, ((redNeighborsIn G y X).card : ℝ)) =
        redEdgesBetween G X Y := by
    calc
      (∑ y ∈ Y, ((redNeighborsIn G y X).card : ℝ)) =
          redEdgesBetween G Y X := by
        exact_mod_cast sum_card_redNeighborsIn G Y X
      _ = redEdgesBetween G X Y := by
        exact_mod_cast redEdgesBetween_comm G Y X
  have hlinear :
      (∑ v ∈ X, p * (X.card : ℝ) * (redNeighborsIn G v Y).card) =
        p * X.card * redEdgesBetween G X Y := by
    calc
      (∑ v ∈ X, p * (X.card : ℝ) * (redNeighborsIn G v Y).card) =
          (p * X.card) *
            ∑ v ∈ X, ((redNeighborsIn G v Y).card : ℝ) := by
        rw [mul_sum]
      _ = p * X.card * redEdgesBetween G X Y := by rw [hdegX]
  have hcross :
      (∑ y ∈ Y, 2 * ((redNeighborsIn G y X).card : ℝ) *
          (p * X.card)) =
        2 * (p * X.card) * redEdgesBetween G X Y := by
    calc
      (∑ y ∈ Y, 2 * ((redNeighborsIn G y X).card : ℝ) *
          (p * X.card)) =
          ∑ y ∈ Y, (2 * (p * X.card)) *
            ((redNeighborsIn G y X).card : ℝ) := by
        apply sum_congr rfl
        intro y hy
        ring
      _ = (2 * (p * X.card)) *
          ∑ y ∈ Y, ((redNeighborsIn G y X).card : ℝ) := by
        rw [mul_sum]
      _ = 2 * (p * X.card) * redEdgesBetween G X Y := by
        rw [hdegY]
  simp_rw [excessBetween]
  rw [sum_sub_distrib, hlinear, hsq]
  simp_rw [sub_sq]
  rw [sum_add_distrib, sum_sub_distrib]
  simp only [sum_const, nsmul_eq_mul]
  rw [hcross]
  ring

/-- Lemma `l:FpAvg` of the paper.  The statement is slightly stronger than
the paper's version because nonemptiness and disjointness are not needed. -/
theorem excess_averaging {V : Type*} (G : SimpleGraph V)
    (X Y : Finset V) (p : ℝ) :
    p * X.card * excessBetween p G X Y ≤
      ∑ v ∈ X, excessBetween p G X (redNeighborsIn G v Y) := by
  have hid := excess_averaging_identity G X Y p
  have hnonneg :
      0 ≤ ∑ y ∈ Y,
        ((redNeighborsIn G y X).card - p * X.card) ^ 2 :=
    sum_nonneg fun _ _ ↦ sq_nonneg _
  linarith

namespace Candidate

/-- Candidate-packaged form of Lemma `l:FpAvg`. -/
theorem excess_averaging (C : Candidate G) (p : ℝ) :
    p * C.X.card * C.excess p ≤
      ∑ v ∈ C.X, excessBetween p G C.X (redNeighborsIn G v C.Y) := by
  simpa [Candidate.excess] using
    Arxiv2407_19026.excess_averaging G C.X C.Y p

end Candidate

section MaxCut

/-- Every finite graph has a cut containing at least half of its (unordered)
edges.  Since `redEdgesBetween G S S` counts every internal edge twice, the
denominator appears as `4` in this formulation. -/
theorem exists_partition_redEdgesBetween_le_four_mul {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    ∃ X Y : Finset V, Disjoint X Y ∧ X ∪ Y = S ∧
      redEdgesBetween G S S ≤ 4 * redEdgesBetween G X Y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨∅, ∅, by simp, by simp, by simp [redEdgesBetween]⟩
  | @insert v S hv ih =>
      obtain ⟨X, Y, hXY, hunion, hcut⟩ := ih
      have hXS : X ⊆ S := by
        intro u hu
        rw [← hunion]
        exact mem_union_left Y hu
      have hYS : Y ⊆ S := by
        intro u hu
        rw [← hunion]
        exact mem_union_right X hu
      have hvX : v ∉ X := fun hv' ↦ hv (hXS hv')
      have hvY : v ∉ Y := fun hv' ↦ hv (hYS hv')
      let a := (redNeighborsIn G v X).card
      let b := (redNeighborsIn G v Y).card
      have hdeg : (redNeighborsIn G v S).card = a + b := by
        calc
          (redNeighborsIn G v S).card = redEdgesBetween G {v} S :=
            (redEdgesBetween_singleton_left G v S).symm
          _ = redEdgesBetween G {v} (X ∪ Y) := by rw [hunion]
          _ = redEdgesBetween G {v} X + redEdgesBetween G {v} Y :=
            redEdgesBetween_union_right G {v} hXY
          _ = a + b := by
            rw [redEdgesBetween_singleton_left, redEdgesBetween_singleton_left]
      have htotal :
          redEdgesBetween G (insert v S) (insert v S) =
            redEdgesBetween G S S + 2 * (a + b) := by
        calc
          redEdgesBetween G (insert v S) (insert v S) =
              redEdgesBetween G ({v} ∪ S) ({v} ∪ S) := by
            rw [singleton_union]
          _ = redEdgesBetween G {v} ({v} ∪ S) +
                redEdgesBetween G S ({v} ∪ S) := by
            rw [redEdgesBetween_union_left G (by simpa [Finset.disjoint_left] using hv)]
          _ = (redEdgesBetween G {v} {v} + redEdgesBetween G {v} S) +
                (redEdgesBetween G S {v} + redEdgesBetween G S S) := by
            rw [redEdgesBetween_union_right G {v}
                (by simpa [Finset.disjoint_left] using hv),
              redEdgesBetween_union_right G S
                (by simpa [Finset.disjoint_left] using hv)]
          _ = redEdgesBetween G S S + 2 * (a + b) := by
            rw [redEdgesBetween_singleton_self, redEdgesBetween_comm G S {v},
              redEdgesBetween_singleton_left, hdeg]
            omega
      by_cases hab : a ≤ b
      · refine ⟨insert v X, Y, ?_, ?_, ?_⟩
        · exact Finset.disjoint_left.mpr fun u huX huY ↦ by
            rw [mem_insert] at huX
            rcases huX with rfl | huX
            · exact hvY huY
            · exact Finset.disjoint_left.mp hXY huX huY
        · ext u
          simp only [mem_union, mem_insert]
          have hu := congrArg (fun T : Finset V ↦ u ∈ T) hunion
          simp only [mem_union] at hu
          tauto
        · have hcross :
              redEdgesBetween G (insert v X) Y =
                redEdgesBetween G X Y + b := by
            calc
              redEdgesBetween G (insert v X) Y =
                  redEdgesBetween G ({v} ∪ X) Y := by rw [singleton_union]
              _ = redEdgesBetween G {v} Y + redEdgesBetween G X Y := by
                rw [redEdgesBetween_union_left G
                  (by simpa [Finset.disjoint_left] using hvX)]
              _ = redEdgesBetween G X Y + b := by
                rw [redEdgesBetween_singleton_left]
                omega
          rw [htotal, hcross]
          omega
      · have hba : b ≤ a := Nat.le_of_not_ge hab
        refine ⟨X, insert v Y, ?_, ?_, ?_⟩
        · exact Finset.disjoint_left.mpr fun u huX huY ↦ by
            rw [mem_insert] at huY
            rcases huY with rfl | huY
            · exact hvX huX
            · exact Finset.disjoint_left.mp hXY huX huY
        · ext u
          simp only [mem_union, mem_insert]
          have hu := congrArg (fun T : Finset V ↦ u ∈ T) hunion
          simp only [mem_union] at hu
          tauto
        · have hcross :
              redEdgesBetween G X (insert v Y) =
                redEdgesBetween G X Y + a := by
            calc
              redEdgesBetween G X (insert v Y) =
                  redEdgesBetween G X ({v} ∪ Y) := by rw [singleton_union]
              _ = redEdgesBetween G X {v} + redEdgesBetween G X Y := by
                rw [redEdgesBetween_union_right G X
                  (by simpa [Finset.disjoint_left] using hvY)]
              _ = redEdgesBetween G X Y + a := by
                rw [redEdgesBetween_comm G X {v},
                  redEdgesBetween_singleton_left]
                omega
          rw [htotal, hcross]
          omega

end MaxCut

section ElementaryRamseyBound

/-- Multiplicative form of Observation `o:easybound`.  It is the invariant
which makes the weighted Erdős--Szekeres induction transparent. -/
theorem ramseyNumber_mul_weights_le_one (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    (ramseyNumber k l : ℝ) * x ^ (k - 1) * (1 - x) ^ (l - 1) ≤ 1 := by
  have hy0 : 0 < 1 - x := sub_pos.mpr hx1
  have hxle : x ≤ 1 := le_of_lt hx1
  have hyle : 1 - x ≤ 1 := by linarith
  induction k generalizing l with
  | zero => omega
  | succ u ihu =>
      induction l with
      | zero => omega
      | succ m ihm =>
          by_cases hu : u = 0
          · subst u
            have hR :
                (ramseyNumber 1 (m + 1) : ℝ) ≤ 1 := by
              exact_mod_cast Erdos1014.ramseyNumber_le_of_property
                (Erdos1014.ramseyProperty_one_left (m + 1))
            have hpow : (1 - x) ^ m ≤ 1 :=
              pow_le_one₀ (le_of_lt hy0) hyle
            simpa using
              (mul_le_mul hR hpow (pow_nonneg (le_of_lt hy0) m) zero_le_one)
          · by_cases hm : m = 0
            · subst m
              have hR :
                  (ramseyNumber (u + 1) 1 : ℝ) ≤ 1 := by
                exact_mod_cast Erdos1014.ramseyNumber_le_of_property
                  (Erdos1014.ramseyProperty_one_right (u + 1))
              have hpow : x ^ u ≤ 1 := pow_le_one₀ (le_of_lt hx0) hxle
              simpa [Nat.succ_sub_one] using
                (mul_le_mul hR hpow (pow_nonneg (le_of_lt hx0) u) zero_le_one)
            · have hu1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr hu
              have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
              have hrec :
                  (ramseyNumber (u + 1) (m + 1) : ℝ) ≤
                    ramseyNumber u (m + 1) + ramseyNumber (u + 1) m := by
                exact_mod_cast Erdos1014.ramseyNumber_recurrence u m hu1
              have hleft := ihu (m + 1) hu1 (by omega)
              have hright := ihm (by omega)
              have hxpow : x ^ u = x ^ (u - 1) * x := by
                conv_lhs => rw [show u = (u - 1) + 1 by omega, pow_succ]
              have hypow : (1 - x) ^ m = (1 - x) ^ (m - 1) * (1 - x) := by
                conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
              calc
                (ramseyNumber (u + 1) (m + 1) : ℝ) *
                      x ^ ((u + 1) - 1) * (1 - x) ^ ((m + 1) - 1) ≤
                    ((ramseyNumber u (m + 1) : ℝ) +
                      ramseyNumber (u + 1) m) * x ^ u * (1 - x) ^ m := by
                  simpa only [Nat.succ_sub_one, mul_assoc] using
                    mul_le_mul_of_nonneg_right hrec
                      (mul_nonneg (pow_nonneg (le_of_lt hx0) u)
                        (pow_nonneg (le_of_lt hy0) m))
                _ = x * ((ramseyNumber u (m + 1) : ℝ) *
                      x ^ (u - 1) * (1 - x) ^ m) +
                    (1 - x) * ((ramseyNumber (u + 1) m : ℝ) *
                      x ^ u * (1 - x) ^ (m - 1)) := by
                  rw [hxpow, hypow]
                  ring
                _ ≤ x * 1 + (1 - x) * 1 :=
                  add_le_add
                    (mul_le_mul_of_nonneg_left hleft (le_of_lt hx0))
                    (mul_le_mul_of_nonneg_left hright (le_of_lt hy0))
                _ = 1 := by ring

/-- Observation `o:easybound` in the paper:
`R(k,l) ≤ x⁻ᵏ⁺¹ (1-x)⁻ˡ⁺¹`.  The right side is written as the reciprocal of
the corresponding natural powers. -/
theorem ramseyNumber_le_elementary (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    (ramseyNumber k l : ℝ) ≤
      1 / (x ^ (k - 1) * (1 - x) ^ (l - 1)) := by
  have hden :
      0 < x ^ (k - 1) * (1 - x) ^ (l - 1) :=
    mul_pos (pow_pos hx0 _) (pow_pos (sub_pos.mpr hx1) _)
  apply (le_div_iff₀ hden).2
  simpa only [mul_assoc] using
    ramseyNumber_mul_weights_le_one x hx0 hx1 k l hk hl

end ElementaryRamseyBound

section CandidateInduction

/-- The lower bound on `f_p(X,Y)` in Lemma `l:easy`. -/
def easyThreshold (x p : ℝ) (k l t : ℕ) : ℝ :=
  (k + t : ℝ) /
    (x ^ (k - 1) * (1 - x) ^ (l - 1) * (p - x) ^ (t - 1))

lemma easyThreshold_pos {x p : ℝ} (hx : 0 < x) (hxp : x < p) (hp : p < 1)
    {k l t : ℕ} (hk : 1 ≤ k) (_hl : 1 ≤ l) (ht : 1 ≤ t) :
    0 < easyThreshold x p k l t := by
  apply div_pos
  · positivity
  · exact mul_pos
      (mul_pos (pow_pos hx _) (pow_pos (sub_pos.mpr (hxp.trans hp)) _))
      (pow_pos (sub_pos.mpr hxp) _)

lemma easyThreshold_red_scale {x p : ℝ} (hx : 0 < x) (hxp : x < p)
    (hp : p < 1) {k l t : ℕ} (hk : 2 ≤ k) (_hl : 1 ≤ l) (ht : 1 ≤ t) :
    ((k + t - 1 : ℕ) : ℝ) / (k + t) * x * easyThreshold x p k l t =
      easyThreshold x p (k - 1) l t := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hone_x : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr (hxp.trans hp))
  have hp_x : p - x ≠ 0 := ne_of_gt (sub_pos.mpr hxp)
  have hsum : (k + t : ℝ) ≠ 0 := by positivity
  have hxpow : x ^ (k - 1) = x ^ (k - 2) * x := by
    conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
  have hsum_pred : k + t - 1 = (k - 1) + t := by omega
  have hpred_pred : k - 1 - 1 = k - 2 := by omega
  rw [easyThreshold, easyThreshold, hxpow]
  field_simp
  rw [hsum_pred, hpred_pred]
  push_cast
  ring

lemma easyThreshold_blue_scale {x p : ℝ} (hx : 0 < x) (hxp : x < p)
    (hp : p < 1) {k l t : ℕ} (hk : 1 ≤ k) (_hl : 1 ≤ l) (ht : 2 ≤ t) :
    ((k + t - 1 : ℕ) : ℝ) / (k + t) * (p - x) * easyThreshold x p k l t =
      easyThreshold x p k l (t - 1) := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hone_x : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr (hxp.trans hp))
  have hp_x : p - x ≠ 0 := ne_of_gt (sub_pos.mpr hxp)
  have hsum : (k + t : ℝ) ≠ 0 := by positivity
  have htpow : (p - x) ^ (t - 1) = (p - x) ^ (t - 2) * (p - x) := by
    conv_lhs => rw [show t - 1 = (t - 2) + 1 by omega, pow_succ]
  have hsum_pred : k + t - 1 = k + (t - 1) := by omega
  have hpred_pred : t - 1 - 1 = t - 2 := by omega
  rw [easyThreshold, easyThreshold, htpow]
  field_simp
  rw [hsum_pred, hpred_pred]
  push_cast
  ring

/-- Lemma `l:easy`, the main inductive argument of Section 2.

The terminal calculation retains the factor `p` supplied by
`excess_averaging`; the published prose drops that factor in one displayed
line.  It is enough because `t ≥ 2` and `(p-x)^(t-1) ≤ p`. -/
theorem candidate_good_of_excess {V : Type*} (G : SimpleGraph V)
    (x p : ℝ) (hx : 0 < x) (hxp : x < p) (hp : p < 1)
    (C : Candidate G) (k l t : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (ht : 1 ≤ t)
    (hC : easyThreshold x p k l t ≤ C.excess p) :
    C.Good k l t := by
  classical
  induction k generalizing t C with
  | zero => omega
  | succ k ihk =>
      induction t generalizing C with
      | zero => omega
      | succ t iht =>
          by_cases hk0 : k = 0
          · subst k
            exact C.good_of_k_one l (t + 1)
          · by_cases ht0 : t = 0
            · subst t
              exact C.good_of_t_one (k + 1) l
            · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
              have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
              have hK : 2 ≤ k + 1 := by omega
              have hT : 2 ≤ t + 1 := by omega
              have hfpos : 0 < C.excess p :=
                lt_of_lt_of_le
                  (easyThreshold_pos hx hxp hp (by omega) hl (by omega)) hC
              have havg := C.excess_averaging p
              have hexists :
                  ∃ v ∈ C.X, p * C.excess p ≤
                    excessBetween p G C.X (redNeighborsIn G v C.Y) := by
                by_contra hnone
                push Not at hnone
                have hlt :=
                  sum_lt_sum_of_nonempty C.X_nonempty
                    (fun v hv ↦ hnone v hv)
                have hlt' :
                    (∑ v ∈ C.X,
                        excessBetween p G C.X (redNeighborsIn G v C.Y)) <
                      (C.X.card : ℝ) * (p * C.excess p) := by
                  simpa [sum_const, nsmul_eq_mul] using hlt
                nlinarith
              obtain ⟨v, hvX, hvavg⟩ := hexists
              let Y' := redNeighborsIn G v C.Y
              let XR := redNeighborsIn G v C.X
              let XB := blueNeighborsIn G v C.X
              have hp0 : 0 < p := hx.trans hxp
              have hYpos : 0 < excessBetween p G C.X Y' := by
                exact lt_of_lt_of_le (mul_pos hp0 hfpos) hvavg
              have hY' : Y'.Nonempty :=
                right_nonempty_of_excessBetween_pos hYpos
              let q : ℝ :=
                (((k + 1) + (t + 1) - 1 : ℕ) : ℝ) /
                  ((k + 1) + (t + 1) : ℕ)
              by_cases hred :
                  q * x * C.excess p ≤ excessBetween p G XR Y'
              · have hqxpos : 0 < q * x := by
                  apply mul_pos
                  · dsimp [q]
                    positivity
                  · exact hx
                have hXRpos : 0 < excessBetween p G XR Y' :=
                  lt_of_lt_of_le (mul_pos hqxpos hfpos) hred
                have hXR : XR.Nonempty :=
                  left_nonempty_of_excessBetween_pos hXRpos
                let D := C.redStep v hXR hY'
                have hD :
                    easyThreshold x p k l (t + 1) ≤ D.excess p := by
                  calc
                    easyThreshold x p k l (t + 1) =
                        q * x * easyThreshold x p (k + 1) l (t + 1) := by
                      symm
                      simpa [q] using
                        easyThreshold_red_scale (k := k + 1) (l := l) (t := t + 1)
                          hx hxp hp hK hl (by omega)
                    _ ≤ q * x * C.excess p :=
                      mul_le_mul_of_nonneg_left hC (le_of_lt hqxpos)
                    _ ≤ D.excess p := by
                      simpa [D, Candidate.redStep, Candidate.excess, XR, Y'] using hred
                have hgoodD : D.Good k l (t + 1) :=
                  ihk D (t + 1) hk1 (by omega) hD
                exact C.good_of_redStep_good hvX hXR hY' hgoodD
              · have hnotred :
                    excessBetween p G XR Y' < q * x * C.excess p :=
                  lt_of_not_ge hred
                by_cases hblue :
                    q * (p - x) * C.excess p ≤ excessBetween p G XB Y'
                · have hqzpos : 0 < q * (p - x) := by
                    apply mul_pos
                    · dsimp [q]
                      positivity
                    · exact sub_pos.mpr hxp
                  have hXBpos : 0 < excessBetween p G XB Y' :=
                    lt_of_lt_of_le (mul_pos hqzpos hfpos) hblue
                  have hXB : XB.Nonempty :=
                    left_nonempty_of_excessBetween_pos hXBpos
                  let D := C.blueStep v hXB hY'
                  have hD :
                      easyThreshold x p (k + 1) l t ≤ D.excess p := by
                    calc
                      easyThreshold x p (k + 1) l t =
                          q * (p - x) *
                            easyThreshold x p (k + 1) l (t + 1) := by
                        symm
                        simpa [q] using
                          easyThreshold_blue_scale
                            (k := k + 1) (l := l) (t := t + 1)
                            hx hxp hp (by omega) hl hT
                      _ ≤ q * (p - x) * C.excess p :=
                        mul_le_mul_of_nonneg_left hC (le_of_lt hqzpos)
                      _ ≤ D.excess p := by
                        simpa [D, Candidate.blueStep, Candidate.excess, XB, Y'] using hblue
                  have hgoodD : D.Good (k + 1) l t :=
                    iht D ht1 hD
                  exact C.good_of_blueStep_good hvX hXB hY' hgoodD
                · have hnotblue :
                      excessBetween p G XB Y' <
                        q * (p - x) * C.excess p :=
                    lt_of_not_ge hblue
                  have hsingleton :
                      excessBetween p G {v} Y' ≤ C.Y.card := by
                    exact (excessBetween_singleton_le_card p (le_of_lt hp0) G v Y').trans
                      (by
                        exact_mod_cast card_le_card
                          (redNeighborsIn_subset G v C.Y))
                  have hdecomp :=
                    excessBetween_partition_neighbors p G hvX Y'
                  have hupper :
                      excessBetween p G C.X Y' <
                        q * x * C.excess p +
                          q * (p - x) * C.excess p + C.Y.card := by
                    rw [hdecomp]
                    exact add_lt_add_of_lt_of_le
                      (add_lt_add hnotred hnotblue) hsingleton
                  have hpf :
                      p * C.excess p <
                        q * p * C.excess p + C.Y.card := by
                    calc
                      p * C.excess p ≤ excessBetween p G C.X Y' := hvavg
                      _ < q * x * C.excess p +
                            q * (p - x) * C.excess p + C.Y.card := hupper
                      _ = q * p * C.excess p + C.Y.card := by ring
                  have hspos :
                      0 < (((k + 1) + (t + 1) : ℕ) : ℝ) := by positivity
                  have hq :
                      q = 1 -
                        1 / (((k + 1) + (t + 1) : ℕ) : ℝ) := by
                    dsimp [q]
                    push_cast
                    field_simp
                    ring
                  rw [hq] at hpf
                  have hterminal :
                      p * C.excess p /
                          (((k + 1) + (t + 1) : ℕ) : ℝ) < C.Y.card := by
                    have halg :
                        p * C.excess p *
                            ((((k + 1) + (t + 1) : ℕ) : ℝ))⁻¹ =
                          p * C.excess p -
                            (1 - ((((k + 1) + (t + 1) : ℕ) : ℝ))⁻¹) *
                              p * C.excess p := by ring
                    have hsub :
                        p * C.excess p -
                            (1 - ((((k + 1) + (t + 1) : ℕ) : ℝ))⁻¹) *
                              p * C.excess p < C.Y.card := by
                      apply (sub_lt_iff_lt_add).2
                      simpa only [one_div, add_comm] using hpf
                    rw [div_eq_mul_inv, halg]
                    exact hsub
                  have hscaled :
                      p * easyThreshold x p (k + 1) l (t + 1) /
                          (((k + 1) + (t + 1) : ℕ) : ℝ) <
                        C.Y.card := by
                    exact lt_of_le_of_lt
                      ((div_le_div_iff_of_pos_right hspos).2
                        (mul_le_mul_of_nonneg_left hC (le_of_lt hp0)))
                      hterminal
                  let base :=
                    x ^ ((k + 1) - 1) * (1 - x) ^ (l - 1)
                  let zpow := (p - x) ^ ((t + 1) - 1)
                  have hbase : 0 < base := by
                    dsimp [base]
                    exact mul_pos (pow_pos hx _)
                      (pow_pos (sub_pos.mpr (hxp.trans hp)) _)
                  have hzpow : 0 < zpow := by
                    dsimp [zpow]
                    exact pow_pos (sub_pos.mpr hxp) _
                  have hzpow_le : zpow ≤ p := by
                    have hz0 : 0 ≤ p - x := le_of_lt (sub_pos.mpr hxp)
                    have hz1 : p - x ≤ 1 := by linarith
                    have hpowone : (p - x) ^ (t - 1) ≤ 1 :=
                      pow_le_one₀ hz0 hz1
                    have hpowself : (p - x) ^ t ≤ p - x := by
                      calc
                        (p - x) ^ t = (p - x) ^ (t - 1) * (p - x) := by
                          conv_lhs =>
                            rw [show t = (t - 1) + 1 by omega, pow_succ]
                        _ ≤ 1 * (p - x) :=
                          mul_le_mul_of_nonneg_right hpowone hz0
                        _ = p - x := one_mul _
                    simpa [zpow] using hpowself.trans (by linarith : p - x ≤ p)
                  have hone_div :
                      1 / base ≤ p / (base * zpow) := by
                    apply (div_le_div_iff₀ hbase (mul_pos hbase hzpow)).2
                    simpa [mul_comm, mul_left_comm, mul_assoc] using
                      mul_le_mul_of_nonneg_left hzpow_le (le_of_lt hbase)
                  have hscaled_eq :
                      p * easyThreshold x p (k + 1) l (t + 1) /
                          (((k + 1) + (t + 1) : ℕ) : ℝ) =
                        p / (base * zpow) := by
                    have hcancel (s d : ℝ) (hs : s ≠ 0) :
                        p * (s / d) / s = p / d := by
                      field_simp
                    dsimp only [easyThreshold, base, zpow]
                    push_cast
                    exact hcancel _ _ (by positivity)
                  have hR :
                      (ramseyNumber (k + 1) l : ℝ) ≤ 1 / base := by
                    simpa [base] using
                      ramseyNumber_le_elementary x hx (hxp.trans hp)
                        (k + 1) l (by omega) hl
                  have hRcard :
                      (ramseyNumber (k + 1) l : ℝ) < C.Y.card :=
                    hR.trans_lt (hone_div.trans_lt (hscaled_eq ▸ hscaled))
                  have hRcardNat : ramseyNumber (k + 1) l ≤ C.Y.card := by
                    exact_mod_cast le_of_lt hRcard
                  exact C.good_of_ramsey_right hRcardNat

end CandidateInduction

end Arxiv2407_19026
