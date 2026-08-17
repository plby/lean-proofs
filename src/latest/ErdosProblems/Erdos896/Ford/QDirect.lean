/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.OrderQ
import ErdosProblems.Erdos896.Ford.OrderedSimplexVolume
import ErdosProblems.Erdos896.Ford.FirstCrossingFubini
import ErdosProblems.Erdos896.Ford.Abel

/-!
# Ford's direct upper bound for uniform order statistics

This is the first-crossing/Fubini proof of the upper half of Ford's
Lemma 11.1.  In particular, it does not pass through the finite parking-word
estimate.  The auxiliary truncation uses Ford's parameters
`a = w + 2` and `A = exp (2*w+2)`.
-/

namespace Erdos896.Ford

open MeasureTheory Set Real
open scoped BigOperators ENNReal Pointwise

/-- Ford's zero-based lower barrier. -/
noncomputable def fordBarrier (u v : ℝ) (i : ℕ) : ℝ :=
  ((i : ℝ) + 1 - u) / v

/-- Tuples whose first strict crossing of Ford's barrier occurs at `p`.
The ambient ordered interval is allowed to have a variable upper endpoint;
this is what lets us compare the unit simplex with Ford's truncation. -/
def fordFirstCrossingCell (k : ℕ) (u v b : ℝ) (p : Fin k) :
    Set (Fin k → ℝ) :=
  {x | x ∈ orderedSimplex k 0 b ∧
    (∀ i : Fin k, i < p → fordBarrier u v i.val ≤ x i) ∧
    x p < fordBarrier u v p.val}

/-- The strict bad set, partitioned according to the first crossing. -/
def fordBadSet (k : ℕ) (u v b : ℝ) : Set (Fin k → ℝ) :=
  ⋃ p : Fin k, fordFirstCrossingCell k u v b p

theorem measurableSet_fordFirstCrossingCell
    (k : ℕ) (u v b : ℝ) (p : Fin k) :
    MeasurableSet (fordFirstCrossingCell k u v b p) := by
  have hprev : MeasurableSet
      (⋂ i : Fin k, {x : Fin k → ℝ |
        i < p → fordBarrier u v i.val ≤ x i}) := by
    apply MeasurableSet.iInter
    intro i
    by_cases hip : i < p
    · have hi : MeasurableSet
          {x : Fin k → ℝ | fordBarrier u v i.val ≤ x i} :=
        measurableSet_le measurable_const (measurable_pi_apply i)
      convert hi using 1
      ext x
      simp only [mem_setOf_eq]
      exact ⟨fun h ↦ h hip, fun h _ ↦ h⟩
    · have hi : MeasurableSet (Set.univ : Set (Fin k → ℝ)) :=
        MeasurableSet.univ
      convert hi using 1
      ext x
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact fun h ↦ (hip h).elim
  have hlast : MeasurableSet
      {x : Fin k → ℝ | x p < fordBarrier u v p.val} :=
    measurableSet_lt (measurable_pi_apply p) measurable_const
  rw [show fordFirstCrossingCell k u v b p =
      (orderedSimplex k 0 b ∩
        (⋂ i : Fin k, {x : Fin k → ℝ |
          i < p → fordBarrier u v i.val ≤ x i})) ∩
        {x : Fin k → ℝ | x p < fordBarrier u v p.val} by
      ext x
      simp only [fordFirstCrossingCell, mem_setOf_eq, mem_inter_iff,
        mem_iInter]
      tauto]
  exact ((measurableSet_orderedSimplex k 0 b).inter hprev).inter hlast

theorem measurableSet_fordBadSet (k : ℕ) (u v b : ℝ) :
    MeasurableSet (fordBadSet k u v b) := by
  unfold fordBadSet
  exact MeasurableSet.iUnion fun p ↦
    measurableSet_fordFirstCrossingCell k u v b p

theorem fordFirstCrossingCell_pairwise_disjoint
    (k : ℕ) (u v b : ℝ) :
    Pairwise (fun p q : Fin k ↦
      Disjoint (fordFirstCrossingCell k u v b p)
        (fordFirstCrossingCell k u v b q)) := by
  intro p q hpq
  rcases lt_or_gt_of_ne hpq with hpq | hqp
  · rw [Set.disjoint_left]
    intro x hp hq
    exact (not_lt_of_ge (hq.2.1 p hpq)) hp.2.2
  · rw [Set.disjoint_left]
    intro x hp hq
    exact (not_lt_of_ge (hp.2.1 q hqp)) hq.2.2

theorem fordFirstCrossingCell_pairwise_aedisjoint
    (k : ℕ) (u v b : ℝ) :
    Pairwise (Function.onFun (AEDisjoint volume)
      (fordFirstCrossingCell k u v b)) := by
  intro p q hpq
  exact (fordFirstCrossingCell_pairwise_disjoint k u v b hpq).aedisjoint

theorem mem_fordBadSet_iff {k : ℕ} {u v b : ℝ} {x : Fin k → ℝ} :
    x ∈ fordBadSet k u v b ↔
      x ∈ orderedSimplex k 0 b ∧
        ∃ i : Fin k, x i < fordBarrier u v i.val := by
  classical
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨p, hp⟩
    exact ⟨hp.1, p, hp.2.2⟩
  · rintro ⟨hord, i, hi⟩
    let P : ℕ → Prop := fun n ↦
      ∃ hn : n < k, x ⟨n, hn⟩ < fordBarrier u v n
    have hP : ∃ n, P n := ⟨i.val, i.isLt, hi⟩
    let m := Nat.find hP
    have hm := Nat.find_spec hP
    let p : Fin k := ⟨m, hm.1⟩
    apply Set.mem_iUnion.mpr
    refine ⟨p, hord, ?_, ?_⟩
    · intro j hjp
      by_contra hj
      have hPlt : P j.val := ⟨j.isLt, lt_of_not_ge hj⟩
      have hmin : m ≤ j.val := Nat.find_min' hP hPlt
      exact (not_le_of_gt hjp) hmin
    · exact hm.2

theorem fordBadSet_eq_diff_orderQSet (k : ℕ) (u v : ℝ) :
    fordBadSet k u v 1 =
      orderedSimplex k 0 1 \ orderQSet k u v := by
  classical
  ext x
  rw [mem_fordBadSet_iff]
  simp only [mem_diff, orderQSet, mem_setOf_eq]
  constructor
  · rintro ⟨hord, i, hi⟩
    refine ⟨hord, ?_⟩
    intro hq
    have := hq.2 i
    exact (not_lt_of_ge (by simpa [fordBarrier] using this)) hi
  · rintro ⟨hord, hq⟩
    refine ⟨hord, ?_⟩
    push_neg at hq
    rcases hq hord with ⟨i, hi⟩
    exact ⟨i, by simpa [fordBarrier] using hi⟩

theorem fordBadSet_eq_orderedSimplex_of_last_crossing
    {k : ℕ} (hk : 1 ≤ k) {u v b : ℝ}
    (hlast : b < fordBarrier u v (k - 1)) :
    fordBadSet k u v b = orderedSimplex k 0 b := by
  ext x
  rw [mem_fordBadSet_iff]
  constructor
  · exact fun hx ↦ hx.1
  · intro hx
    let p : Fin k := ⟨k - 1, by omega⟩
    refine ⟨hx, p, ?_⟩
    exact lt_of_le_of_lt (hx.1 p).2 hlast

theorem volume_fordBadSet_eq_sum (k : ℕ) (u v b : ℝ) :
    volume (fordBadSet k u v b) =
      ∑ p : Fin k, volume (fordFirstCrossingCell k u v b p) := by
  unfold fordBadSet
  rw [measure_iUnion₀
    (fordFirstCrossingCell_pairwise_aedisjoint k u v b)
    (fun p ↦ (measurableSet_fordFirstCrossingCell k u v b p).nullMeasurableSet)]
  exact tsum_fintype _

/-- Sum the fixed-first-crossing section comparisons.  This is the global
form of Ford's cancellation in (11.83). -/
theorem ford_truncation_volume_le_bad
    {k : ℕ} {u v c A : ℝ}
    (htrunc : fordBadSet k u v c = orderedSimplex k 0 c)
    (hcell : ∀ p : Fin k,
      ENNReal.ofReal A * volume (fordFirstCrossingCell k u v c p) ≤
        volume (fordFirstCrossingCell k u v 1 p)) :
    ENNReal.ofReal A * volume (orderedSimplex k 0 c) ≤
      volume (fordBadSet k u v 1) := by
  rw [← htrunc, volume_fordBadSet_eq_sum,
    volume_fordBadSet_eq_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun p _ ↦ hcell p

/-- Convert the global bad-volume comparison back to the normalized
order-statistics probability. -/
theorem orderQ_le_one_sub_of_truncation
    {k : ℕ} {u v c A : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hvol : ENNReal.ofReal A * volume (orderedSimplex k 0 c) ≤
      volume (fordBadSet k u v 1)) :
    orderQ k u v ≤ 1 - A * c ^ k := by
  have hsub : volume (orderQSet k u v) ≤ volume (orderedSimplex k 0 1) :=
    measure_mono (orderQSet_subset_orderedSimplex k u v)
  have hsimplexfinite : volume (orderedSimplex k 0 1) ≠ ⊤ := by
    rw [volume_orderedSimplex k (by norm_num)]
    simp
  have hqfinite : volume (orderQSet k u v) ≠ ⊤ :=
    ne_top_of_le_ne_top hsimplexfinite hsub
  have hdiff : volume (fordBadSet k u v 1) =
      volume (orderedSimplex k 0 1) - volume (orderQSet k u v) := by
    rw [fordBadSet_eq_diff_orderQSet]
    exact measure_diff (orderQSet_subset_orderedSimplex k u v)
      (measurableSet_orderQSet k u v).nullMeasurableSet hqfinite
  have hfinite : volume (fordBadSet k u v 1) ≠ ⊤ := by
    apply ne_of_lt
    calc
      volume (fordBadSet k u v 1) ≤ volume (orderedSimplex k 0 1) := by
        rw [fordBadSet_eq_diff_orderQSet]
        exact measure_mono diff_subset
      _ < ⊤ := by
        rw [volume_orderedSimplex k (by norm_num)]
        simp
  have htoRealDiff :
      (volume (orderedSimplex k 0 1) - volume (orderQSet k u v)).toReal =
        (volume (orderedSimplex k 0 1)).toReal -
          (volume (orderQSet k u v)).toReal :=
    ENNReal.toReal_sub_of_le hsub hsimplexfinite
  have hreal := ENNReal.toReal_mono hfinite hvol
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA,
    volume_orderedSimplex_toReal k hc, hdiff, htoRealDiff,
    volume_orderedSimplex_toReal k (by norm_num)] at hreal
  unfold orderQ
  have hfac : (0 : ℝ) < k.factorial := by positivity
  norm_num at hreal ⊢
  rw [inv_eq_one_div] at hreal
  have hrewrite : A * (c ^ k / (k.factorial : ℝ)) =
      A * c ^ k / (k.factorial : ℝ) := by ring
  rw [hrewrite] at hreal
  have hq : (volume (orderQSet k u v)).toReal ≤
      1 / (k.factorial : ℝ) - A * c ^ k / (k.factorial : ℝ) := by
    nlinarith
  calc
    (k.factorial : ℝ) * (volume (orderQSet k u v)).toReal ≤
        (k.factorial : ℝ) *
          (1 / (k.factorial : ℝ) - A * c ^ k / (k.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hq hfac.le
    _ = 1 - A * c ^ k := by field_simp

/-! ### Ford's pointwise ratio -/

private theorem ford_log_ratio_aux {x y : ℝ}
    (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x < 1) :
    Real.log (1 - x) - Real.log (1 + y) ≤ -(x + y) := by
  have hxabs : |x| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hylt : y < 1 := hyx.trans_lt hx
  have hyabs : |-y| < 1 := by
    rw [abs_neg, abs_of_nonneg hy]
    exact hylt
  have hsumx := (Real.hasSum_pow_div_log_of_abs_lt_one hxabs).mul_left (-1)
  have hsumy := Real.hasSum_pow_div_log_of_abs_lt_one hyabs
  have hsum : HasSum
      (fun n : ℕ ↦
        -(x ^ (n + 1) / (n + 1)) + (-y) ^ (n + 1) / (n + 1))
      (Real.log (1 - x) - Real.log (1 + y)) := by
    simpa [sub_eq_add_neg] using hsumx.add hsumy
  have hmajor : HasSum (fun n : ℕ ↦ if n = 0 then -(x + y) else 0)
      (-(x + y)) := by
    simpa using hasSum_ite_eq 0 (-(x + y))
  apply hasSum_le (fun n ↦ ?_) hsum hmajor
  by_cases hn : n = 0
  · subst n
    norm_num
  · rw [if_neg hn]
    by_cases heven : Even (n + 1)
    · rw [Even.neg_pow heven]
      have hp := pow_le_pow_left₀ hy hyx (n + 1)
      have hden : (0 : ℝ) < n + 1 := by positivity
      convert div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) hden.le using 1 <;>
        ring
    · have hodd : Odd (n + 1) := (Nat.not_even_iff_odd).mp heven
      rw [Odd.neg_pow hodd]
      have hx0 : 0 ≤ x := hy.trans hyx
      exact add_nonpos
        (neg_nonpos.mpr (div_nonneg (pow_nonneg hx0 _) (by positivity)))
        (div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (pow_nonneg hy _)) (by positivity))

/-- The power comparison used in (11.83), with `a=w+2`. -/
theorem ford_ratio_pow_le_exp_neg {n : ℕ} {w lam : ℝ}
    (hn : 0 < n) (hw : 0 ≤ w) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hnum : 0 ≤ (n : ℝ) - w - 2 + lam) :
    (((n : ℝ) - w - 2 + lam) / ((n : ℝ) + w + lam)) ^ n ≤
      Real.exp (-2 * w - 2) := by
  by_cases hz : (n : ℝ) - w - 2 + lam = 0
  · rw [hz, zero_div, zero_pow hn.ne']
    positivity
  · let x := (w + 2 - lam) / (n : ℝ)
    let y := (w + lam) / (n : ℝ)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hnumpos : 0 < (n : ℝ) - w - 2 + lam :=
      lt_of_le_of_ne hnum (Ne.symm hz)
    have hxlt : x < 1 := by
      dsimp [x]
      rw [div_lt_one hnR]
      linarith
    have hy : 0 ≤ y := by dsimp [y]; positivity
    have hyx : y ≤ x := by
      dsimp [x, y]
      apply div_le_div_of_nonneg_right _ hnR.le
      linarith
    have hlog := ford_log_ratio_aux hy hyx hxlt
    have hden : 0 < (n : ℝ) + w + lam := by positivity
    have hratioPos : 0 < ((n : ℝ) - w - 2 + lam) /
        ((n : ℝ) + w + lam) := div_pos hnumpos hden
    have hrewrite : ((n : ℝ) - w - 2 + lam) /
          ((n : ℝ) + w + lam) = (1 - x) / (1 + y) := by
      dsimp [x, y]
      field_simp
      ring
    have hlogratio : Real.log (((n : ℝ) - w - 2 + lam) /
          ((n : ℝ) + w + lam)) ≤ (-2 * w - 2) / (n : ℝ) := by
      rw [hrewrite, Real.log_div (by linarith : 1 - x ≠ 0)
        (by positivity : 1 + y ≠ 0)]
      convert hlog using 1 <;> dsimp [x, y] <;> field_simp <;> ring
    rw [← Real.exp_log hratioPos, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      (n : ℝ) * Real.log (((n : ℝ) - w - 2 + lam) /
          ((n : ℝ) + w + lam)) ≤
          (n : ℝ) * ((-2 * w - 2) / (n : ℝ)) := by gcongr
      _ = -2 * w - 2 := by field_simp

/-! ### The fixed first-crossing section -/

/-- The variables up to and including the first crossing.  We include the
truncation bound `y ≤ c`; on the unit side this selects a subset of the full
first-crossing cell, which is all the comparison needs. -/
def fordPrefixSection (m : ℕ) (u v c : ℝ) :
    Set (ℝ × (Fin m → ℝ)) :=
  {q | 0 ≤ q.1 ∧ q.1 ≤ c ∧ q.1 < fordBarrier u v m ∧
    q.2 ∈ orderedSimplex m 0 q.1 ∧
    ∀ i, fordBarrier u v i.val ≤ q.2 i}

theorem measurableSet_fordPrefixSection (m : ℕ) (u v c : ℝ) :
    MeasurableSet (fordPrefixSection m u v c) := by
  have hy0 : MeasurableSet {q : ℝ × (Fin m → ℝ) | 0 ≤ q.1} :=
    measurableSet_le measurable_const measurable_fst
  have hyc : MeasurableSet {q : ℝ × (Fin m → ℝ) | q.1 ≤ c} :=
    measurableSet_le measurable_fst measurable_const
  have hybar : MeasurableSet
      {q : ℝ × (Fin m → ℝ) | q.1 < fordBarrier u v m} :=
    measurableSet_lt measurable_fst measurable_const
  have hbounds : MeasurableSet
      {q : ℝ × (Fin m → ℝ) | ∀ i, 0 ≤ q.2 i ∧ q.2 i ≤ q.1} := by
    rw [show {q : ℝ × (Fin m → ℝ) | ∀ i, 0 ≤ q.2 i ∧ q.2 i ≤ q.1} =
        ⋂ i, {q | 0 ≤ q.2 i ∧ q.2 i ≤ q.1} by ext; simp]
    exact MeasurableSet.iInter fun i ↦
      (measurableSet_le measurable_const
        ((measurable_pi_apply i).comp measurable_snd)).inter
      (measurableSet_le ((measurable_pi_apply i).comp measurable_snd)
        measurable_fst)
  have hmono : MeasurableSet
      {q : ℝ × (Fin m → ℝ) | Monotone q.2} := by
    rw [show {q : ℝ × (Fin m → ℝ) | Monotone q.2} =
        ⋂ i, ⋂ j, ⋂ (_h : i ≤ j), {q | q.2 i ≤ q.2 j} by
          ext q
          simp only [mem_ofPred_eq, mem_iInter]
          exact Iff.rfl]
    exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun _ ↦
        measurableSet_le ((measurable_pi_apply i).comp measurable_snd)
          ((measurable_pi_apply j).comp measurable_snd)
  have hbars : MeasurableSet
      {q : ℝ × (Fin m → ℝ) | ∀ i, fordBarrier u v i.val ≤ q.2 i} := by
    rw [show {q : ℝ × (Fin m → ℝ) |
        ∀ i, fordBarrier u v i.val ≤ q.2 i} =
        ⋂ i, {q | fordBarrier u v i.val ≤ q.2 i} by ext; simp]
    exact MeasurableSet.iInter fun i ↦
      measurableSet_le measurable_const
        ((measurable_pi_apply i).comp measurable_snd)
  rw [show fordPrefixSection m u v c =
      {q | 0 ≤ q.1} ∩ {q | q.1 ≤ c} ∩
        {q | q.1 < fordBarrier u v m} ∩
        (({q | ∀ i, 0 ≤ q.2 i ∧ q.2 i ≤ q.1} ∩
          {q | Monotone q.2}) ∩
          {q | ∀ i, fordBarrier u v i.val ≤ q.2 i}) by
      ext q
      simp [fordPrefixSection, orderedSimplex, and_assoc]]
  exact ((hy0.inter hyc).inter hybar).inter
    ((hbounds.inter hmono).inter hbars)

/-- Splitting at a prescribed first crossing identifies the crossing cell
with a fixed prefix section and an ordered suffix. -/
theorem fordFirstCrossingCell_eq_splitOrderedCell
    (m n : ℕ) (u v c : ℝ) :
    fordFirstCrossingCell (m + n + 1) u v c ⟨m, by omega⟩ =
      splitOrderedCell m n c (fordPrefixSection m u v c) := by
  ext x
  simp only [fordFirstCrossingCell, mem_setOf_eq, splitOrderedCell, mem_preimage,
    orderedSuffixCell, fordPrefixSection]
  simp only [splitAtFubini_pivot, splitAtFubini_prefix,
    splitAtFubini_suffix, orderedSimplex, mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨(hx.1.1 ⟨m, by omega⟩).1, (hx.1.1 ⟨m, by omega⟩).2,
        hx.2.2, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro i
          exact ⟨(hx.1.1 (Fin.castAdd (n + 1) i)).1,
            hx.1.2 (Fin.mk_le_mk.mpr (by exact i.isLt.le))⟩
        · intro i j hij
          rw [splitAtFubini_prefix, splitAtFubini_prefix]
          exact hx.1.2 (Fin.mk_le_mk.mpr hij)
      · intro i
        exact hx.2.1 (Fin.castAdd (n + 1) i)
          (Fin.mk_lt_mk.mpr (by exact i.isLt))
    · intro i
      exact ⟨hx.1.2 (Fin.mk_le_mk.mpr (by omega)),
        (hx.1.1 ⟨m + 1 + i.val, by omega⟩).2⟩
    · intro i j hij
      rw [splitAtFubini_suffix, splitAtFubini_suffix]
      exact hx.1.2 (Fin.mk_le_mk.mpr (by omega))
  · intro hx
    rcases hx with
      ⟨⟨hy0, hyc, hybar, ⟨hpreBounds, hpreMono⟩, hpreBarrier⟩,
        hsuffixBounds, hsuffixMono⟩
    refine ⟨⟨?_, ?_⟩, ?_, hybar⟩
    · intro i
      by_cases hiPre : i.val < m
      · let a : Fin m := ⟨i.val, hiPre⟩
        have ha := hpreBounds a
        have hai : Fin.castAdd (n + 1) a = i := by
          apply Fin.ext
          rfl
        exact ⟨by simpa only [hai] using ha.1,
          by simpa only [hai] using ha.2.trans hyc⟩
      · by_cases hiCross : i.val = m
        · have hi : i = ⟨m, by omega⟩ := by
            apply Fin.ext
            exact hiCross
          simpa only [hi] using And.intro hy0 hyc
        · have hiSuf : m < i.val := by omega
          let a : Fin n := ⟨i.val - m - 1, by omega⟩
          have ha := hsuffixBounds a
          have hai : (⟨m + 1 + a.val, by omega⟩ : Fin (m + n + 1)) = i := by
            apply Fin.ext
            dsimp [a]
            omega
          exact ⟨hy0.trans (by simpa only [hai] using ha.1),
            by simpa only [hai] using ha.2⟩
    · intro i j hij
      by_cases hjPre : j.val < m
      · have hiPre : i.val < m := lt_of_le_of_lt (Fin.mk_le_mk.mp hij) hjPre
        let a : Fin m := ⟨i.val, hiPre⟩
        let b : Fin m := ⟨j.val, hjPre⟩
        have hab : a ≤ b := Fin.mk_le_mk.mpr (Fin.mk_le_mk.mp hij)
        have h := hpreMono hab
        rw [splitAtFubini_prefix, splitAtFubini_prefix] at h
        have hai : Fin.castAdd (n + 1) a = i := by
          apply Fin.ext
          rfl
        have hbj : Fin.castAdd (n + 1) b = j := by
          apply Fin.ext
          rfl
        simpa only [hai, hbj] using h
      · by_cases hiSuf : m < i.val
        · have hjSuf : m < j.val := lt_of_lt_of_le hiSuf (Fin.mk_le_mk.mp hij)
          let a : Fin n := ⟨i.val - m - 1, by omega⟩
          let b : Fin n := ⟨j.val - m - 1, by omega⟩
          have hab : a ≤ b := by
            apply Fin.mk_le_mk.mpr
            omega
          have h := hsuffixMono hab
          rw [splitAtFubini_suffix, splitAtFubini_suffix] at h
          have hai : (⟨m + 1 + a.val, by omega⟩ : Fin (m + n + 1)) = i := by
            apply Fin.ext
            dsimp [a]
            omega
          have hbj : (⟨m + 1 + b.val, by omega⟩ : Fin (m + n + 1)) = j := by
            apply Fin.ext
            dsimp [b]
            omega
          simpa only [hai, hbj] using h
        · have hiLe : i.val ≤ m := by omega
          have hjGe : m ≤ j.val := by omega
          have hip : x i ≤ x ⟨m, by omega⟩ := by
            by_cases hiCross : i.val = m
            · have hi : i = ⟨m, by omega⟩ := by
                apply Fin.ext
                exact hiCross
              rw [hi]
            · have hiPre : i.val < m := by omega
              let a : Fin m := ⟨i.val, hiPre⟩
              have ha := (hpreBounds a).2
              have hai : Fin.castAdd (n + 1) a = i := by
                apply Fin.ext
                rfl
              simpa only [hai] using ha
          have hpj : x ⟨m, by omega⟩ ≤ x j := by
            by_cases hjCross : j.val = m
            · have hj : j = ⟨m, by omega⟩ := by
                apply Fin.ext
                exact hjCross
              rw [hj]
            · have hjSuf : m < j.val := by omega
              let b : Fin n := ⟨j.val - m - 1, by omega⟩
              have hb := (hsuffixBounds b).1
              have hbj : (⟨m + 1 + b.val, by omega⟩ : Fin (m + n + 1)) = j := by
                apply Fin.ext
                dsimp [b]
                omega
              simpa only [hbj] using hb
          exact hip.trans hpj
    · intro i hi
      let a : Fin m := ⟨i.val, Fin.mk_lt_mk.mp hi⟩
      have ha := hpreBarrier a
      have hai : Fin.castAdd (n + 1) a = i := by
        apply Fin.ext
        rfl
      simpa only [a, hai] using ha

/-- Ford's pointwise comparison of the ordered suffix volumes.  The proof
recovers `λ = m+1-u-vy` from the crossing coordinate `y`; the preceding
barrier gives `λ≤1`, and the truncation gives the nonnegative numerator in
the ratio from (11.83). -/
theorem ford_suffix_section_comparison {m n : ℕ} {u v w c : ℝ}
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hvpos : 0 < v)
    (hv : v = ((m + n + 1 : ℕ) : ℝ) - u + w)
    (hc : c = 1 - (2 * w + 2) / v)
    (q : ℝ × (Fin m → ℝ)) (hq : q ∈ fordPrefixSection m u v c) :
    ENNReal.ofReal (Real.exp (2 * w + 2)) *
        volume (orderedSimplex n q.1 c) ≤
      volume (orderedSimplex n q.1 1) := by
  let y := q.1
  let lam := (m : ℝ) + 1 - u - v * y
  have hy0 : 0 ≤ y := hq.1
  have hyc : y ≤ c := hq.2.1
  have hybar : y < fordBarrier u v m := hq.2.2.1
  have hlam0 : 0 ≤ lam := by
    dsimp [lam, y]
    rw [fordBarrier, lt_div_iff₀ hvpos] at hybar
    linarith
  have hlam1 : lam ≤ 1 := by
    cases m with
    | zero =>
        dsimp [lam]
        simp only [Nat.cast_zero, zero_add]
        have := mul_nonneg hvpos.le hy0
        linarith
    | succ m =>
        let i : Fin (m + 1) := ⟨m, by omega⟩
        have hpre : fordBarrier u v i.val ≤ q.2 i := hq.2.2.2.2 i
        have hupper : q.2 i ≤ y := (hq.2.2.2.1.1 i).2
        rw [fordBarrier] at hpre
        rw [div_le_iff₀ hvpos] at hpre
        change ((m : ℝ) + 1 - u) ≤ q.2 i * v at hpre
        have huppermul : q.2 i * v ≤ y * v :=
          mul_le_mul_of_nonneg_right hupper hvpos.le
        dsimp [lam, y]
        rw [Nat.cast_add, Nat.cast_one]
        linarith
  have hv' : v = (m : ℝ) + (n : ℝ) + 1 - u + w := by
    rw [hv]
    push_cast
    ring
  have hnumEq : (n : ℝ) - w - 2 + lam = v * (c - y) := by
    dsimp [lam, y]
    rw [hc]
    field_simp [hvpos.ne']
    linarith
  have hdenEq : (n : ℝ) + w + lam = v * (1 - y) := by
    dsimp [lam, y]
    linarith
  have hnum : 0 ≤ (n : ℝ) - w - 2 + lam := by
    rw [hnumEq]
    exact mul_nonneg hvpos.le (sub_nonneg.mpr hyc)
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    norm_num at hnum
    linarith
  have hden : 0 < (n : ℝ) + w + lam := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hy1 : y < 1 := by
    rw [hdenEq] at hden
    nlinarith
  have hratio :
      ((n : ℝ) - w - 2 + lam) / ((n : ℝ) + w + lam) =
        (c - y) / (1 - y) := by
    rw [hnumEq, hdenEq]
    field_simp [hvpos.ne']
  have hp := ford_ratio_pow_le_exp_neg hn hw hlam0 hlam1 hnum
  rw [hratio] at hp
  have hprod : Real.exp (2 * w + 2) * (c - y) ^ n ≤ (1 - y) ^ n := by
    have hcancel : Real.exp (2 * w + 2) * Real.exp (-2 * w - 2) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    have hm : Real.exp (2 * w + 2) * ((c - y) / (1 - y)) ^ n ≤
        Real.exp (2 * w + 2) * Real.exp (-2 * w - 2) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_pos (2 * w + 2)).le
    have hm' : Real.exp (2 * w + 2) * ((c - y) / (1 - y)) ^ n ≤ 1 := by
      calc
        Real.exp (2 * w + 2) * ((c - y) / (1 - y)) ^ n ≤
            Real.exp (2 * w + 2) * Real.exp (-2 * w - 2) := hm
        _ = 1 := hcancel
    have hpowpos : 0 < (1 - y) ^ n := pow_pos (sub_pos.mpr hy1) n
    have hm'' := mul_le_mul_of_nonneg_right hm' hpowpos.le
    calc
      Real.exp (2 * w + 2) * (c - y) ^ n =
          (Real.exp (2 * w + 2) * ((c - y) / (1 - y)) ^ n) *
            (1 - y) ^ n := by
        rw [div_pow]
        field_simp [ne_of_gt hpowpos]
      _ ≤ 1 * (1 - y) ^ n := hm''
      _ = (1 - y) ^ n := one_mul _
  rw [volume_orderedSimplex n hyc, volume_orderedSimplex n hy1.le]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have := (div_le_div_iff_of_pos_right hfac).2 hprod
  simpa only [mul_div_assoc] using this

theorem fordPrefixSection_mono {m : ℕ} {u v c d : ℝ} (hcd : c ≤ d) :
    fordPrefixSection m u v c ⊆ fordPrefixSection m u v d := by
  intro q hq
  exact ⟨hq.1, hq.2.1.trans hcd, hq.2.2⟩

theorem splitOrderedCell_fordPrefixSection_mono
    {m n : ℕ} {u v b c d : ℝ} (hcd : c ≤ d) :
    splitOrderedCell m n b (fordPrefixSection m u v c) ⊆
      splitOrderedCell m n b (fordPrefixSection m u v d) := by
  intro x hx
  exact ⟨fordPrefixSection_mono hcd hx.1, hx.2⟩

/-- Ford's estimate in the nontrivial range.  This is (11.83) with
`a=w+2`, so that the truncation endpoint is `1-(2w+2)/v`, and with
`A=exp(2w+2)`. -/
theorem ford_orderQ_hard_estimate {k : ℕ} {u v w : ℝ}
    (hk : 1 ≤ k) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hv : v = (k : ℝ) - u + w)
    (hlarge : 128 * (u + 1) * (w + 1) ^ 2 < (k : ℝ)) :
    orderQ k u v ≤
      1 - Real.exp (2 * w + 2) *
        (1 - (2 * w + 2) / v) ^ k := by
  let c : ℝ := 1 - (2 * w + 2) / v
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hu1 : 1 ≤ u + 1 := by linarith
  have hw1 : 1 ≤ w + 1 := by linarith
  have hwsq : 1 ≤ (w + 1) ^ 2 := one_le_pow₀ hw1
  have huSmall : 128 * (u + 1) < (k : ℝ) := by
    calc
      128 * (u + 1) ≤ 128 * (u + 1) * (w + 1) ^ 2 := by nlinarith
      _ < (k : ℝ) := hlarge
  have hwSmall : 128 * (w + 1) < (k : ℝ) := by
    calc
      128 * (w + 1) ≤ 128 * (u + 1) * (w + 1) ^ 2 := by nlinarith
      _ < (k : ℝ) := hlarge
  have hvpos : 0 < v := by rw [hv]; nlinarith
  have ha_le_v : 2 * w + 2 ≤ v := by rw [hv]; nlinarith
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact sub_nonneg.mpr ((div_le_one hvpos).2 ha_le_v)
  have hc1 : c ≤ 1 := by
    dsimp [c]
    exact sub_le_self _ (div_nonneg (by nlinarith) hvpos.le)
  have hlast : c < fordBarrier u v (k - 1) := by
    rw [fordBarrier]
    have hnum : ((k - 1 : ℕ) : ℝ) + 1 - u = (k : ℝ) - u := by
      rw [Nat.cast_sub hk]
      norm_num
    rw [hnum, lt_div_iff₀ hvpos]
    dsimp [c]
    field_simp [hvpos.ne']
    rw [hv]
    nlinarith
  have htrunc : fordBadSet k u v c = orderedSimplex k 0 c :=
    fordBadSet_eq_orderedSimplex_of_last_crossing hk hlast
  have hcell : ∀ p : Fin k,
      ENNReal.ofReal (Real.exp (2 * w + 2)) *
          volume (fordFirstCrossingCell k u v c p) ≤
        volume (fordFirstCrossingCell k u v 1 p) := by
    rintro ⟨m, hm⟩
    obtain ⟨n, hdim⟩ : ∃ n, k = m + n + 1 :=
      ⟨k - m - 1, by omega⟩
    subst k
    have hsec := mul_volume_splitOrderedCell_le
      (measurableSet_fordPrefixSection m u v c)
      (ENNReal.ofReal (Real.exp (2 * w + 2)))
      (ford_suffix_section_comparison hu hw hvpos hv rfl)
    rw [fordFirstCrossingCell_eq_splitOrderedCell] at ⊢
    calc
      ENNReal.ofReal (Real.exp (2 * w + 2)) *
          volume (splitOrderedCell m n c (fordPrefixSection m u v c)) ≤
        volume (splitOrderedCell m n 1 (fordPrefixSection m u v c)) := hsec
      _ ≤ volume (splitOrderedCell m n 1 (fordPrefixSection m u v 1)) :=
        measure_mono (splitOrderedCell_fordPrefixSection_mono hc1)
      _ = volume (fordFirstCrossingCell (m + n + 1) u v 1 ⟨m, by omega⟩) := by
        rw [fordFirstCrossingCell_eq_splitOrderedCell]
  have hvol := ford_truncation_volume_le_bad htrunc hcell
  have hq := orderQ_le_one_sub_of_truncation hc0
    (Real.exp_pos (2 * w + 2)).le hvol
  simpa [c] using hq

/-! ### The elementary last step -/

/-- The elementary logarithmic estimate converting Ford's hard estimate
into the desired rational bound. -/
theorem orderQ_le_of_ford_hard_estimate {k : ℕ} {u v w : ℝ}
    (hk : 1 ≤ k) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hv : v = (k : ℝ) - u + w)
    (hlarge : 128 * (u + 1) * (w + 1) ^ 2 < (k : ℝ))
    (hq : orderQ k u v ≤
      1 - Real.exp (2 * w + 2) *
        (1 - (2 * w + 2) / v) ^ k) :
    orderQ k u v ≤
      128 * (u + 1) * (w + 1) ^ 2 / (k : ℝ) := by
  let a : ℝ := 2 * (w + 1)
  let X : ℝ := 8 * (u + 1) * (w + 1) ^ 2 / (k : ℝ)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hu1 : 1 ≤ u + 1 := by linarith
  have hw1 : 1 ≤ w + 1 := by linarith
  have hwsq : 1 ≤ (w + 1) ^ 2 := one_le_pow₀ hw1
  have huSmall : 128 * (u + 1) < (k : ℝ) := by
    calc
      128 * (u + 1) ≤ 128 * (u + 1) * (w + 1) ^ 2 := by nlinarith
      _ < (k : ℝ) := hlarge
  have hwSmall : 128 * (w + 1) < (k : ℝ) := by
    calc
      128 * (w + 1) ≤ 128 * (u + 1) * (w + 1) ^ 2 := by nlinarith
      _ < (k : ℝ) := hlarge
  have hden : (k : ℝ) / 2 ≤ v - a := by
    dsimp [a]
    rw [hv]
    nlinarith
  have hdenpos : 0 < v - a := lt_of_lt_of_le (half_pos hkR) hden
  have hvpos : 0 < v := by linarith
  have hbase : 0 < 1 - a / v := by
    rw [sub_pos, div_lt_one hvpos]
    linarith
  have hlog0 := Real.one_sub_inv_le_log_of_pos hbase
  have hinv : 1 - (1 - a / v)⁻¹ = -a / (v - a) := by
    field_simp
    ring
  have hlog : -a / (v - a) ≤ Real.log (1 - a / v) := by
    rw [← hinv]
    exact hlog0
  have hB : a * (u + a) / (v - a) ≤ X := by
    have ha : a = 2 * (w + 1) := rfl
    have hua : u + a ≤ 2 * (u + 1) * (w + 1) := by
      rw [ha]
      nlinarith
    have hnum : a * (u + a) ≤ 4 * (u + 1) * (w + 1) ^ 2 := by
      rw [ha]
      nlinarith
    dsimp [X]
    apply (div_le_div_iff₀ hdenpos hkR).2
    have hnumk := mul_le_mul_of_nonneg_right hnum hkR.le
    have hdenT := mul_le_mul_of_nonneg_left hden
      (by positivity : 0 ≤ 8 * (u + 1) * (w + 1) ^ 2)
    nlinarith
  have hexponent : -X ≤ a + (k : ℝ) * Real.log (1 - a / v) := by
    have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
    have hid : a - (k : ℝ) * a / (v - a) =
        a * (w - u - a) / (v - a) := by
      field_simp [hdenpos.ne']
      rw [hv]
      ring
    have hlower : -a * (u + a) / (v - a) ≤
        a - (k : ℝ) * a / (v - a) := by
      rw [hid]
      apply (div_le_div_iff_of_pos_right hdenpos).2
      have ha0 : 0 ≤ a := by dsimp [a]; positivity
      nlinarith
    calc
      -X ≤ -(a * (u + a) / (v - a)) := by linarith
      _ = -a * (u + a) / (v - a) := by ring
      _ ≤ a - (k : ℝ) * a / (v - a) := hlower
      _ = a + (k : ℝ) * (-a / (v - a)) := by ring
      _ ≤ a + (k : ℝ) * Real.log (1 - a / v) := by
        simpa [add_comm] using add_le_add_left hmul a
  have hprod : 1 - X ≤ Real.exp a * (1 - a / v) ^ k := by
    calc
      1 - X ≤ Real.exp (-X) := by
        simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-X)
      _ ≤ Real.exp (a + (k : ℝ) * Real.log (1 - a / v)) :=
        Real.exp_le_exp.mpr hexponent
      _ = Real.exp a * (1 - a / v) ^ k := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hbase]
  have hqx : orderQ k u v ≤ X := by
    have hq' : orderQ k u v ≤
        1 - Real.exp a * (1 - a / v) ^ k := by
      convert hq using 1 <;> dsimp [a] <;> ring
    exact hq'.trans (by linarith [hprod])
  have hX : X ≤ 128 * (u + 1) * (w + 1) ^ 2 / (k : ℝ) := by
    dsimp [X]
    apply (div_le_div_iff_of_pos_right hkR).2
    have : 0 ≤ (u + 1) * (w + 1) ^ 2 := by positivity
    nlinarith
  exact hqx.trans hX

/-! ### The uniform direct bound -/

/-- Ford's direct upper bound for `orderQ`, with an explicit absolute constant.

The large-parameter case is the first-crossing/Fubini argument above.  In the
complementary case, the defining probability is at most one. -/
theorem ford_orderQ_direct_bound (k : ℕ) (u v : ℝ)
    (hk : 1 ≤ k) (hu : 0 ≤ u) (hw : 0 ≤ u + v - (k : ℝ)) :
    orderQ k u v ≤
      128 * (u + 1) * (u + v - (k : ℝ) + 1) ^ 2 / (k : ℝ) := by
  let w : ℝ := u + v - (k : ℝ)
  have hw0 : 0 ≤ w := by simpa [w] using hw
  have hv : v = (k : ℝ) - u + w := by
    dsimp [w]
    ring
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases hlarge : 128 * (u + 1) * (w + 1) ^ 2 < (k : ℝ)
  · have hhard := ford_orderQ_hard_estimate hk hu hw0 hv hlarge
    have hbound := orderQ_le_of_ford_hard_estimate hk hu hw0 hv hlarge hhard
    simpa [w] using hbound
  · calc
      orderQ k u v ≤ 1 := orderQ_le_one k u v
      _ ≤ 128 * (u + 1) * (w + 1) ^ 2 / (k : ℝ) :=
        (le_div_iff₀ hkR).2 (by simpa using le_of_not_gt hlarge)
      _ = 128 * (u + 1) * (u + v - (k : ℝ) + 1) ^ 2 / (k : ℝ) := by
        rfl

/-- Existential-constant formulation of Ford's direct `orderQ` upper bound. -/
theorem ford_orderQ_upper_direct :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) (u v : ℝ), 1 ≤ k → 0 ≤ u → 0 ≤ u + v - (k : ℝ) →
        orderQ k u v ≤
          C * (u + 1) * (u + v - (k : ℝ) + 1) ^ 2 / (k : ℝ) := by
  refine ⟨128, by norm_num, ?_⟩
  intro k u v hk hu hw
  exact ford_orderQ_direct_bound k u v hk hu hw

end Erdos896.Ford
