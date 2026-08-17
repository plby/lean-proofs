/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos641.Chromatic
import Mathlib.Data.Fin.Rev

/-!
# Counting the chromatic obstruction

This file turns the cylinder estimate from `Chromatic.lean` into an
exponentially small relative-cardinality bound.  The repetition parameter
`20 q²` is the quantitative slack used in the JSS majority-color argument.
-/

open Finset Fintype Filter
open scoped BigOperators Classical

namespace Erdos641

open SimpleGraph
open Erdos182

noncomputable section

/-- Number of later majority layers retained for one color. -/
def chromaticRepetitions (q : ℕ) : ℕ := 20 * q ^ 2

/-- Eventually every strict tail has at most as many vertices as the layer
immediately before it. -/
lemma eventually_card_jssStrictTail_le_layer :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (prsLayerCount n),
      (jssStrictTail n i).card ≤ prsLayerSize n i := by
  filter_upwards [eventually_prsLayer_tail_le,
      eventually_four_thousand_mul_prsLayerSize_succ_le] with n htail hstep
  intro i
  rw [card_jssStrictTail]
  by_cases hi : i.val + 1 < prsLayerCount n
  · exact (htail i).trans <| by
      have hs := hstep i.val hi
      omega
  · simpa only [Finset.Ico_eq_empty hi, Finset.sum_empty] using
      Nat.zero_le (prsLayerSize n i.val)

/-- The relative size of one retained majority-color cylinder is at most
`exp (-20 b)`, where `b` is the size of its first layer. -/
lemma avoidanceSpace_ratio_le_exp_neg_twenty {n q : ℕ}
    (hq : 0 < q) (i : Fin (prsLayerCount n))
    (A T : Finset (JSSVertex n))
    (J : Finset (Fin (prsLayerCount n)))
    (hA : A ⊆ jssLayer n i)
    (hJheavy : J ⊆ heavyLaterLayers n q i T)
    (hAsize : majoritySize (prsLayerSize n i) q ≤ A.card)
    (hJsize : chromaticRepetitions q ≤ J.card)
    (hspace : (jssOutcomeSpace n).Nonempty) :
    ((avoidanceSpace A T).card : ℝ) / (jssOutcomeSpace n).card ≤
      Real.exp (-(20 * (prsLayerSize n i : ℝ))) := by
  let m := A.card * J.card
  have hcount := card_avoidanceSpace_mul_pow_le hq i A T J hA hJheavy
  have hspacepos : (0 : ℝ) < (jssOutcomeSpace n).card := by
    exact_mod_cast Finset.card_pos.mpr hspace
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqpow : (0 : ℝ) < (q : ℝ) ^ m := pow_pos hqR _
  have hcount' : (avoidanceSpace A T).card * q ^ m ≤
      (q - 1) ^ m * (jssOutcomeSpace n).card := by
    calc
      (avoidanceSpace A T).card * q ^ m ≤
          (jssOutcomeSpace n).card * (q - 1) ^ m := by
        simpa only [m] using hcount
      _ = (q - 1) ^ m * (jssOutcomeSpace n).card := Nat.mul_comm _ _
  have hratio :
      ((avoidanceSpace A T).card : ℝ) / (jssOutcomeSpace n).card ≤
        (((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ m := by
    rw [div_pow]
    rw [div_le_div_iff₀ hspacepos hqpow]
    exact_mod_cast hcount'
  have hbase : (((q - 1 : ℕ) : ℝ) / (q : ℝ)) =
      1 - 1 / (q : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    field_simp
    ring
  have hbase0 : (0 : ℝ) ≤ 1 - 1 / (q : ℝ) := by
    rw [sub_nonneg, div_le_one hqR]
    exact_mod_cast hq
  have hexp : 1 - 1 / (q : ℝ) ≤ Real.exp (-(1 / (q : ℝ))) :=
    Real.one_sub_le_exp_neg _
  have hpowexp : (1 - 1 / (q : ℝ)) ^ m ≤
      Real.exp (-(1 / (q : ℝ))) ^ m :=
    pow_le_pow_left₀ hbase0 hexp m
  have hrewrite : Real.exp (-(1 / (q : ℝ))) ^ m =
      Real.exp (-((m : ℝ) / (q : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hbq : prsLayerSize n i ≤ q * A.card :=
    (le_mul_majoritySize hq).trans (Nat.mul_le_mul_left q hAsize)
  have hm : 20 * q * prsLayerSize n i ≤ m := by
    dsimp [m]
    dsimp [chromaticRepetitions] at hJsize
    nlinarith [Nat.mul_le_mul_left A.card hJsize,
      Nat.mul_le_mul_left (20 * q) hbq]
  have hmR : (20 : ℝ) * prsLayerSize n i ≤ (m : ℝ) / (q : ℝ) := by
    have hm' : ((20 * q * prsLayerSize n i : ℕ) : ℝ) ≤ m := by
      exact_mod_cast hm
    norm_num only [Nat.cast_mul] at hm'
    rw [le_div_iff₀ hqR]
    nlinarith
  calc
    ((avoidanceSpace A T).card : ℝ) / (jssOutcomeSpace n).card ≤
        (((q - 1 : ℕ) : ℝ) / (q : ℝ)) ^ m := hratio
    _ = (1 - 1 / (q : ℝ)) ^ m := by rw [hbase]
    _ ≤ Real.exp (-(1 / (q : ℝ))) ^ m := hpowexp
    _ = Real.exp (-((m : ℝ) / (q : ℝ))) := hrewrite
    _ ≤ Real.exp (-(20 * (prsLayerSize n i : ℝ))) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hmR)

/-- One summand in the two powerset unions defining `chromaticBadAt`. -/
def chromaticPiece (n q R : ℕ) (i : Fin (prsLayerCount n))
    (A T : Finset (JSSVertex n)) : Finset (JSSOutcome n) :=
  if majoritySize (prsLayerSize n i) q ≤ A.card ∧
      R ≤ (heavyLaterLayers n q i T).card then
    avoidanceSpace A T
  else ∅

lemma chromaticBadAt_eq_biUnion_piece (n q R : ℕ)
    (i : Fin (prsLayerCount n)) :
    chromaticBadAt n q R i =
      (jssLayer n i).powerset.biUnion fun A ↦
        (jssStrictTail n i).powerset.biUnion fun T ↦
          chromaticPiece n q R i A T := by
  rfl

/-- The cardinality of `chromaticBadAt` is at most the sum of the
cardinalities of all its powerset-indexed pieces. -/
lemma card_chromaticBadAt_le_sum_piece (n q R : ℕ)
    (i : Fin (prsLayerCount n)) :
    (chromaticBadAt n q R i).card ≤
      ∑ A ∈ (jssLayer n i).powerset,
        ∑ T ∈ (jssStrictTail n i).powerset,
          (chromaticPiece n q R i A T).card := by
  classical
  rw [chromaticBadAt_eq_biUnion_piece]
  calc
    ((jssLayer n i).powerset.biUnion fun A ↦
        (jssStrictTail n i).powerset.biUnion fun T ↦
          chromaticPiece n q R i A T).card ≤
        ∑ A ∈ (jssLayer n i).powerset,
          ((jssStrictTail n i).powerset.biUnion fun T ↦
            chromaticPiece n q R i A T).card := Finset.card_biUnion_le
    _ ≤ ∑ A ∈ (jssLayer n i).powerset,
          ∑ T ∈ (jssStrictTail n i).powerset,
            (chromaticPiece n q R i A T).card := by
      apply Finset.sum_le_sum
      intro A _hA
      exact Finset.card_biUnion_le

/-- Every powerset-indexed piece has the fixed-cylinder exponential bound. -/
lemma chromaticPiece_ratio_le {n q : ℕ} (hq : 0 < q)
    (i : Fin (prsLayerCount n)) (A T : Finset (JSSVertex n))
    (hA : A ∈ (jssLayer n i).powerset)
    (hspace : (jssOutcomeSpace n).Nonempty) :
    ((chromaticPiece n q (chromaticRepetitions q) i A T).card : ℝ) /
        (jssOutcomeSpace n).card ≤
      Real.exp (-(20 * (prsLayerSize n i : ℝ))) := by
  classical
  by_cases hgood : majoritySize (prsLayerSize n i) q ≤ A.card ∧
      chromaticRepetitions q ≤ (heavyLaterLayers n q i T).card
  · rw [chromaticPiece, if_pos hgood]
    obtain ⟨J, hJsub, hJcard⟩ :=
      Finset.exists_subset_card_eq hgood.2
    exact avoidanceSpace_ratio_le_exp_neg_twenty hq i A T J
      (Finset.mem_powerset.mp hA) hJsub hgood.1 (by omega) hspace
  · rw [chromaticPiece, if_neg hgood]
    simpa using (Real.exp_pos (-(20 * (prsLayerSize n i : ℝ)))).le

/-- The number of possible pairs `(A,T)` costs at most `exp (2b)` when the
strict tail has cardinality at most the current layer. -/
lemma powerset_pair_card_le_exp_two_mul {n : ℕ}
    (i : Fin (prsLayerCount n))
    (htail : (jssStrictTail n i).card ≤ prsLayerSize n i) :
    (((jssLayer n i).powerset.card : ℕ) : ℝ) *
        (((jssStrictTail n i).powerset.card : ℕ) : ℝ) ≤
      Real.exp (2 * (prsLayerSize n i : ℝ)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
  have hb : (jssLayer n i).card = prsLayerSize n i := card_jssLayer n i
  rw [Finset.card_powerset, Finset.card_powerset, hb]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    (2 : ℝ) ^ prsLayerSize n i *
        2 ^ (jssStrictTail n i).card ≤
      Real.exp 1 ^ prsLayerSize n i *
        Real.exp 1 ^ (jssStrictTail n i).card := by
          gcongr
    _ = Real.exp ((prsLayerSize n i : ℝ) +
        (jssStrictTail n i).card) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          ring
    _ ≤ Real.exp (2 * (prsLayerSize n i : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact_mod_cast (by omega : prsLayerSize n i +
        (jssStrictTail n i).card ≤ 2 * prsLayerSize n i)

/-- A complete layer-level chromatic union bound. -/
lemma chromaticBadAt_ratio_le_exp_neg_eighteen {n q : ℕ}
    (hq : 0 < q) (i : Fin (prsLayerCount n))
    (htail : (jssStrictTail n i).card ≤ prsLayerSize n i)
    (hspace : (jssOutcomeSpace n).Nonempty) :
    ((chromaticBadAt n q (chromaticRepetitions q) i).card : ℝ) /
        (jssOutcomeSpace n).card ≤
      Real.exp (-(18 * (prsLayerSize n i : ℝ))) := by
  classical
  have hspacepos : (0 : ℝ) < (jssOutcomeSpace n).card := by
    exact_mod_cast Finset.card_pos.mpr hspace
  calc
    ((chromaticBadAt n q (chromaticRepetitions q) i).card : ℝ) /
        (jssOutcomeSpace n).card ≤
      (↑(∑ A ∈ (jssLayer n i).powerset,
        ∑ T ∈ (jssStrictTail n i).powerset,
          (chromaticPiece n q (chromaticRepetitions q) i A T).card) : ℝ) /
            (jssOutcomeSpace n).card := by
              apply div_le_div_of_nonneg_right _ hspacepos.le
              exact_mod_cast card_chromaticBadAt_le_sum_piece n q
                (chromaticRepetitions q) i
    _ = ∑ A ∈ (jssLayer n i).powerset,
          ∑ T ∈ (jssStrictTail n i).powerset,
            ((chromaticPiece n q (chromaticRepetitions q) i A T).card : ℝ) /
              (jssOutcomeSpace n).card := by
      norm_num only [Nat.cast_sum]
      simp_rw [Finset.sum_div]
    _ ≤ ∑ _A ∈ (jssLayer n i).powerset,
          ∑ _T ∈ (jssStrictTail n i).powerset,
            Real.exp (-(20 * (prsLayerSize n i : ℝ))) := by
      apply Finset.sum_le_sum
      intro A hA
      apply Finset.sum_le_sum
      intro T _hT
      exact chromaticPiece_ratio_le hq i A T hA hspace
    _ = (((jssLayer n i).powerset.card : ℕ) : ℝ) *
          (((jssStrictTail n i).powerset.card : ℕ) : ℝ) *
            Real.exp (-(20 * (prsLayerSize n i : ℝ))) := by
      simp
      ring
    _ ≤ Real.exp (2 * (prsLayerSize n i : ℝ)) *
          Real.exp (-(20 * (prsLayerSize n i : ℝ))) := by
      gcongr
      exact powerset_pair_card_le_exp_two_mul i htail
    _ = Real.exp (-(18 * (prsLayerSize n i : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Reversing a positive strictly decreasing natural sequence bounds its
`j`-th term below by `j+1`. -/
lemma reverse_lower_of_strict_decrease {L : ℕ} (b : ℕ → ℕ)
    (hpos : ∀ i < L, 0 < b i)
    (hstep : ∀ i, i + 1 < L → b (i + 1) < b i) :
    ∀ j : Fin L, j.val + 1 ≤ b (Fin.rev j).val := by
  intro j
  have haux : ∀ d, d < L → d + 1 ≤ b (L - 1 - d) := by
    intro d
    induction d with
    | zero =>
        intro hL
        have hp := hpos (L - 1) (by omega)
        simpa only [Nat.zero_add, Nat.sub_zero] using
          (show 1 ≤ b (L - 1) by omega)
    | succ d ih =>
        intro hd
        have hi := ih (by omega)
        have hs := hstep (L - 1 - (d + 1)) (by omega)
        have heq : L - 1 - (d + 1) + 1 = L - 1 - d := by omega
        rw [heq] at hs
        omega
  have hj := haux j.val j.isLt
  change j.val + 1 ≤ b (L - (j.val + 1))
  rw [show L - (j.val + 1) = L - 1 - j.val by omega]
  exact hj

/-- Under the PRS separation estimate, the layer sizes are strictly
decreasing throughout the active range. -/
lemma prsLayerSize_strict_decrease {n : ℕ}
    (hlayer : ∀ i < prsLayerCount n, 0 < prsLayerSize n i)
    (hseparate : ∀ i, i + 1 < prsLayerCount n →
      4000 * prsLayerSize n (i + 1) ≤ prsLayerSize n i) :
    ∀ i, i + 1 < prsLayerCount n →
      prsLayerSize n (i + 1) < prsLayerSize n i := by
  intro i hi
  have hp := hlayer (i + 1) hi
  have hs := hseparate i hi
  omega

/-- The union of all chromatic bad layers has relative cardinality less
than one quarter. -/
lemma chromaticBad_ratio_lt_one_quarter {n q : ℕ} (hq : 0 < q)
    (hlayer : ∀ i < prsLayerCount n, 0 < prsLayerSize n i)
    (hseparate : ∀ i, i + 1 < prsLayerCount n →
      4000 * prsLayerSize n (i + 1) ≤ prsLayerSize n i)
    (htail : ∀ i : Fin (prsLayerCount n),
      (jssStrictTail n i).card ≤ prsLayerSize n i)
    (hspace : (jssOutcomeSpace n).Nonempty) :
    ((chromaticBad n q (chromaticRepetitions q)).card : ℝ) /
        (jssOutcomeSpace n).card < 1 / 4 := by
  classical
  let L := prsLayerCount n
  have hspacepos : (0 : ℝ) < (jssOutcomeSpace n).card := by
    exact_mod_cast Finset.card_pos.mpr hspace
  have hcard : (chromaticBad n q (chromaticRepetitions q)).card ≤
      ∑ i : Fin L, (chromaticBadAt n q (chromaticRepetitions q) i).card := by
    simpa [chromaticBad, L] using
      (Finset.card_biUnion_le :
        ((Finset.univ : Finset (Fin L)).biUnion
          (chromaticBadAt n q (chromaticRepetitions q))).card ≤
        ∑ i : Fin L, (chromaticBadAt n q (chromaticRepetitions q) i).card)
  have hreverse : ∀ j : Fin L, j.val + 1 ≤
      prsLayerSize n (Fin.rev j).val :=
    reverse_lower_of_strict_decrease (fun i ↦ prsLayerSize n i)
      hlayer (prsLayerSize_strict_decrease hlayer hseparate)
  have hhalf : Real.exp (-(36 / 2 : ℝ)) ≤ 1 / 2 := by
    calc
      Real.exp (-(36 / 2 : ℝ)) = Real.exp (-18) := by norm_num
      _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ 0.3678794412 := Real.exp_neg_one_lt_d9.le
      _ ≤ 1 / 2 := by norm_num
  have hsmall : 2 * Real.exp (-18) < (1 / 4 : ℝ) := by
    have he : (8 : ℝ) < Real.exp 3 := by
      calc
        (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
        _ < Real.exp 1 ^ (3 : ℕ) := by
          exact pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)
        _ = Real.exp 3 := by
          rw [← Real.exp_nat_mul]
          norm_num
    have heneg : Real.exp (-18) ≤ Real.exp (-3) :=
      Real.exp_le_exp.mpr (by norm_num)
    have heinv : Real.exp (-3) < (1 / 8 : ℝ) := by
      rw [Real.exp_neg]
      simpa [one_div] using
        (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 8) he)
    nlinarith
  calc
    ((chromaticBad n q (chromaticRepetitions q)).card : ℝ) /
        (jssOutcomeSpace n).card ≤
      (↑(∑ i : Fin L,
        (chromaticBadAt n q (chromaticRepetitions q) i).card) : ℝ) /
          (jssOutcomeSpace n).card := by
            apply div_le_div_of_nonneg_right _ hspacepos.le
            exact_mod_cast hcard
    _ = ∑ i : Fin L,
          ((chromaticBadAt n q (chromaticRepetitions q) i).card : ℝ) /
            (jssOutcomeSpace n).card := by
      norm_num only [Nat.cast_sum]
      simp_rw [Finset.sum_div]
    _ ≤ ∑ i : Fin L,
          Real.exp (-(18 * (prsLayerSize n i : ℝ))) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact chromaticBadAt_ratio_le_exp_neg_eighteen hq i (htail i) hspace
    _ = ∑ j : Fin L,
          Real.exp (-(18 * (prsLayerSize n (Fin.rev j) : ℝ))) := by
      exact (Equiv.sum_comp Fin.revPerm
        (fun i : Fin L ↦ Real.exp (-(18 * (prsLayerSize n i : ℝ))))).symm
    _ ≤ ∑ j : Fin L, Real.exp (-(18 * ((j.val + 1 : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro j _hj
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_left
        (by exact_mod_cast hreverse j) (by norm_num))
    _ = ∑ x ∈ Finset.range L,
          Real.exp (-(((x + 1 : ℕ) : ℝ) * 36 / 2)) := by
      calc
        (∑ j : Fin L, Real.exp (-(18 * ((j.val + 1 : ℕ) : ℝ)))) =
            ∑ x ∈ Finset.range L,
              Real.exp (-(18 * ((x + 1 : ℕ) : ℝ))) :=
          Fin.sum_univ_eq_sum_range
            (fun x : ℕ ↦ Real.exp (-(18 * ((x + 1 : ℕ) : ℝ)))) L
        _ = ∑ x ∈ Finset.range L,
              Real.exp (-(((x + 1 : ℕ) : ℝ) * 36 / 2)) := by
          apply Finset.sum_congr rfl
          intro x _hx
          congr 1
          push_cast
          ring
    _ ≤ 2 * Real.exp (-(36 / 2 : ℝ)) :=
      sum_exp_neg_succ_mul_half_le L 36 hhalf
    _ = 2 * Real.exp (-18) := by norm_num
    _ < 1 / 4 := hsmall

end

end Erdos641
