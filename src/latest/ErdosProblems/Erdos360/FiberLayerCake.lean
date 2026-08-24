import ErdosProblems.Erdos360.Core

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

lemma sum_card_filter_lt_eq_sum_min (A : Finset ℕ) (f : ℕ → ℕ) (M : ℕ) :
    (∑ t ∈ Finset.range M, (A.filter fun a => t < f a).card) =
      ∑ a ∈ A, min (f a) M := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range M).filter (fun t => t < f a) =
      Finset.range (min (f a) M) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter]
  simp

lemma sum_card_filter_lt_eq_sum (A : Finset ℕ) (f : ℕ → ℕ) (M : ℕ)
    (hf : ∀ a ∈ A, f a ≤ M) :
    (∑ t ∈ Finset.range M, (A.filter fun a => t < f a).card) =
      ∑ a ∈ A, f a := by
  rw [sum_card_filter_lt_eq_sum_min]
  apply Finset.sum_congr rfl
  intro a ha
  rw [min_eq_left (hf a ha)]

lemma relative_interval_arithmetic
    {s r e M G D T : ℕ}
    (hs : 6 ≤ s) (he : 1 ≤ e) (hsplit : s = r + e)
    (hD : D ≤ e * M)
    (hbasic : 3 * G ≤ 2 * r * M + 2 * T)
    (hstrong : 6 * G + (r + 1) * M ≤ 4 * r * M + 4 * T) :
    5 * (G + D) ≤ 2 * ((G + D) + (s + e - 2) * M + T) := by
  have hD3 : 3 * D ≤ 3 * (e * M) := Nat.mul_le_mul_left 3 hD
  by_cases he4 : 4 ≤ e
  · have hcoeff0 : 2 * r + 3 * e ≤ 2 * (s + e - 2) := by omega
    have hcoeff := Nat.mul_le_mul_right M hcoeff0
    have hcore : 3 * (G + D) ≤
        2 * (s + e - 2) * M + 2 * T := by
      ring_nf at hcoeff hD3 hbasic ⊢
      omega
    ring_nf at hcore ⊢
    omega
  · have hr : 3 ≤ r := by omega
    have hcoef0 : 2 * (4 - e) ≤ r + 1 := by omega
    have hcoef := Nat.mul_le_mul_right M hcoef0
    have hdouble : 2 * (3 * G + (4 - e) * M) ≤
        2 * (2 * r * M + 2 * T) := by
      ring_nf at hcoef hstrong ⊢
      omega
    have hboost : 3 * G + (4 - e) * M ≤ 2 * r * M + 2 * T := by
      omega
    have hcoeffEq :
        2 * (s + e - 2) * M + (4 - e) * M =
          2 * r * M + 3 * e * M := by
      have hscoeff : 2 * (s + e - 2) + (4 - e) = 2 * r + 3 * e := by
        omega
      calc
        2 * (s + e - 2) * M + (4 - e) * M =
            (2 * (s + e - 2) + (4 - e)) * M := by ring
        _ = (2 * r + 3 * e) * M := by rw [hscoeff]
        _ = 2 * r * M + 3 * e * M := by ring
    have hcoreAdd : 3 * (G + D) + (4 - e) * M ≤
        2 * (s + e - 2) * M + 2 * T + (4 - e) * M := by
      rw [add_assoc, add_comm (2 * T), ← add_assoc, hcoeffEq]
      ring_nf at hD3 hboost ⊢
      omega
    have hcore : 3 * (G + D) ≤
        2 * (s + e - 2) * M + 2 * T := by omega
    ring_nf at hcore ⊢
    omega

lemma excess_basic {M w : ℕ} (hw : w ≤ M) :
    3 * w ≤ 2 * M + 2 * (2 * w - M) := by
  omega

lemma excess_strong {M w : ℕ} (hw : w ≤ M) :
    6 * w + M ≤ 4 * M + 4 * (2 * w - M) := by
  omega

lemma good_excess_bounds (Good : Finset ℕ) (w : ℕ → ℕ) {base M : ℕ}
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hmax : ∀ a ∈ Good, w a ≤ M) :
    3 * (∑ a ∈ Good, w a) ≤
        2 * Good.card * M + 2 * ∑ a ∈ Good, (2 * w a - M) ∧
      6 * (∑ a ∈ Good, w a) + (Good.card + 1) * M ≤
        4 * Good.card * M + 4 * ∑ a ∈ Good, (2 * w a - M) := by
  classical
  have hbasicSum : (∑ a ∈ Good, 3 * w a) ≤
      ∑ a ∈ Good, (2 * M + 2 * (2 * w a - M)) := by
    apply Finset.sum_le_sum
    intro a ha
    exact excess_basic (hmax a ha)
  have hbasic : 3 * (∑ a ∈ Good, w a) ≤
      2 * Good.card * M + 2 * ∑ a ∈ Good, (2 * w a - M) := by
    calc
      3 * (∑ a ∈ Good, w a) = ∑ a ∈ Good, 3 * w a := by
        rw [Finset.mul_sum]
      _ ≤ ∑ a ∈ Good, (2 * M + 2 * (2 * w a - M)) := hbasicSum
      _ = 2 * Good.card * M +
          2 * ∑ a ∈ Good, (2 * w a - M) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        rw [Finset.mul_sum]
        congr 1
        ac_rfl
  let Rest := Good.erase base
  have hstrongRest : (∑ a ∈ Rest, (6 * w a + M)) ≤
      ∑ a ∈ Rest, (4 * M + 4 * (2 * w a - M)) := by
    apply Finset.sum_le_sum
    intro a ha
    exact excess_strong (hmax a (Finset.mem_of_mem_erase ha))
  have hstrongRest' : 6 * (∑ a ∈ Rest, w a) + Rest.card * M ≤
      4 * Rest.card * M + 4 * ∑ a ∈ Rest, (2 * w a - M) := by
    have hleft : 6 * (∑ a ∈ Rest, w a) + Rest.card * M =
        ∑ a ∈ Rest, (6 * w a + M) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.mul_sum]
      rfl
    have hright : (∑ a ∈ Rest, (4 * M + 4 * (2 * w a - M))) =
        4 * Rest.card * M +
          4 * ∑ a ∈ Rest, (2 * w a - M) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.mul_sum]
      congr 1
      ac_rfl
    rw [hleft, ← hright]
    exact hstrongRest
  have hRestCard : Rest.card = Good.card - 1 := by
    dsimp [Rest]
    rw [Finset.card_erase_of_mem hbase]
  have hRestSum : (∑ a ∈ Good, w a) = M + ∑ a ∈ Rest, w a := by
    dsimp [Rest]
    rw [add_comm, ← hbasew]
    exact (Finset.sum_erase_add Good w hbase).symm
  have hRestExcess : (∑ a ∈ Good, (2 * w a - M)) =
      M + ∑ a ∈ Rest, (2 * w a - M) := by
    dsimp [Rest]
    rw [add_comm, ← Finset.sum_erase_add Good (fun a => 2 * w a - M) hbase]
    rw [hbasew]
    omega
  have hstrong : 6 * (∑ a ∈ Good, w a) + (Good.card + 1) * M ≤
      4 * Good.card * M + 4 * ∑ a ∈ Good, (2 * w a - M) := by
    rw [hRestSum, hRestExcess]
    have hcardpos : 0 < Good.card := Finset.card_pos.mpr ⟨base, hbase⟩
    have hcardEq : Good.card = (Good.card - 1) + 1 := by omega
    have haug := Nat.add_le_add_right hstrongRest' (8 * M)
    rw [hRestCard] at hstrongRest' haug
    rw [hcardEq]
    ring_nf at haug ⊢
    exact haug
  exact ⟨hbasic, hstrong⟩

lemma relative_layerCake_lower
    (s M : ℕ) (w L : ℕ → ℕ) (Good Bad : Finset ℕ)
    (hspos : 0 < s) (hMpos : 0 < M) (hBad : Bad.Nonempty)
    (hpart : Good ∪ Bad = Finset.range s) (hdisj : Disjoint Good Bad)
    (hmax : ∀ i ∈ Finset.range s, w i ≤ M)
    (hLmax : ∀ k ∈ Finset.range (2 * s - 1), L k ≤ 2 * M)
    (hlow : ∀ t ∈ Finset.range M,
      (s + ((Finset.range s).filter (fun i => t < w i)).card - 1) ≤
        ((Finset.range (2 * s - 1)).filter (fun k => t < L k)).card)
    (hhigh : ∀ u ∈ Finset.range M,
      (Good.filter (fun i => M + u < 2 * w i)).card + Bad.card - 1 ≤
        ((Finset.range (2 * s - 1)).filter (fun k => M + u < L k)).card) :
    (∑ i ∈ Finset.range s, w i) +
        (s + Bad.card - 2) * M +
          ∑ i ∈ Good, (2 * w i - M) ≤
      ∑ k ∈ Finset.range (2 * s - 1), L k := by
  classical
  have hBadPos : 1 ≤ Bad.card := Finset.card_pos.mpr hBad
  have hsumw := sum_card_filter_lt_eq_sum (Finset.range s) w M hmax
  have hexcessMax : ∀ i ∈ Good, 2 * w i - M ≤ M := by
    intro i hi
    have hiRange : i ∈ Finset.range s := by
      rw [← hpart]
      exact Finset.mem_union_left _ hi
    have := hmax i hiRange
    omega
  have hsumExcess := sum_card_filter_lt_eq_sum Good
    (fun i => 2 * w i - M) M hexcessMax
  have hsumL := sum_card_filter_lt_eq_sum
    (Finset.range (2 * s - 1)) L (2 * M) hLmax
  have hlowSum :
      ∑ t ∈ Finset.range M,
          (s + ((Finset.range s).filter fun i => t < w i).card - 1) ≤
        ∑ t ∈ Finset.range M,
          ((Finset.range (2 * s - 1)).filter fun k => t < L k).card := by
    exact Finset.sum_le_sum hlow
  have hhighSum :
      ∑ u ∈ Finset.range M,
          ((Good.filter fun i => M + u < 2 * w i).card + Bad.card - 1) ≤
        ∑ u ∈ Finset.range M,
          ((Finset.range (2 * s - 1)).filter fun k => M + u < L k).card := by
    exact Finset.sum_le_sum hhigh
  have hlowEval :
      ∑ t ∈ Finset.range M,
          (s + ((Finset.range s).filter fun i => t < w i).card - 1) =
        (∑ i ∈ Finset.range s, w i) + M * (s - 1) := by
    have hsTerm : ∀ t ∈ Finset.range M,
        s + ((Finset.range s).filter fun i => t < w i).card - 1 =
          ((Finset.range s).filter fun i => t < w i).card + (s - 1) := by
      intro t ht
      omega
    calc
      (∑ t ∈ Finset.range M,
          (s + ((Finset.range s).filter fun i => t < w i).card - 1)) =
          ∑ t ∈ Finset.range M,
            (((Finset.range s).filter fun i => t < w i).card + (s - 1)) := by
        exact Finset.sum_congr rfl hsTerm
      _ = (∑ i ∈ Finset.range s, w i) + M * (s - 1) := by
        rw [Finset.sum_add_distrib, hsumw]
        simp
  have hhighFilter : ∀ u ∈ Finset.range M,
      Good.filter (fun i => M + u < 2 * w i) =
        Good.filter (fun i => u < 2 * w i - M) := by
    intro u hu
    ext i
    simp only [Finset.mem_filter]
    constructor <;> intro hi
    · exact ⟨hi.1, by omega⟩
    · exact ⟨hi.1, by omega⟩
  have hhighEval :
      ∑ u ∈ Finset.range M,
          ((Good.filter fun i => M + u < 2 * w i).card + Bad.card - 1) =
        (∑ i ∈ Good, (2 * w i - M)) + M * (Bad.card - 1) := by
    have heTerm : ∀ u ∈ Finset.range M,
        (Good.filter (fun i => u < 2 * w i - M)).card + Bad.card - 1 =
          (Good.filter (fun i => u < 2 * w i - M)).card +
            (Bad.card - 1) := by
      intro u hu
      omega
    calc
      (∑ u ∈ Finset.range M,
          ((Good.filter fun i => M + u < 2 * w i).card + Bad.card - 1)) =
          ∑ u ∈ Finset.range M,
            ((Good.filter fun i => u < 2 * w i - M).card +
              (Bad.card - 1)) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hhighFilter u hu]
        exact heTerm u hu
      _ = (∑ i ∈ Good, (2 * w i - M)) + M * (Bad.card - 1) := by
        rw [Finset.sum_add_distrib, hsumExcess]
        simp
  have hsplitRange : Finset.range (2 * M) =
      Finset.range M ∪ (Finset.range M).image (fun u => M + u) := by
    ext t
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
    constructor
    · intro ht
      by_cases htm : t < M
      · exact Or.inl htm
      · right
        refine ⟨t - M, by omega, by omega⟩
    · rintro (ht | ⟨u, hu, rfl⟩)
      · omega
      · omega
  have hsplitDisj : Disjoint (Finset.range M)
      ((Finset.range M).image (fun u => M + u)) := by
    rw [Finset.disjoint_left]
    intro t ht hti
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hti
    simp only [Finset.mem_range] at ht hu
    omega
  have hrightSplit :
      (∑ t ∈ Finset.range M,
          ((Finset.range (2 * s - 1)).filter fun k => t < L k).card) +
        ∑ u ∈ Finset.range M,
          ((Finset.range (2 * s - 1)).filter fun k => M + u < L k).card =
        ∑ k ∈ Finset.range (2 * s - 1), L k := by
    rw [← hsumL]
    rw [hsplitRange, Finset.sum_union hsplitDisj]
    congr 1
    rw [Finset.sum_image]
    intro a ha b hb hab
    change M + a = M + b at hab
    omega
  rw [hlowEval] at hlowSum
  rw [hhighEval] at hhighSum
  have hadd := Nat.add_le_add hlowSum hhighSum
  rw [hrightSplit] at hadd
  have hcoeff : M * (s - 1) + M * (Bad.card - 1) =
      (s + Bad.card - 2) * M := by
    rw [← Nat.mul_add]
    have : (s - 1) + (Bad.card - 1) = s + Bad.card - 2 := by omega
    rw [this, Nat.mul_comm]
  rw [← hcoeff]
  omega

def intervalAntidiagonalPairs (s k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range s).product (Finset.range s)).filter fun p => p.1 + p.2 = k

def relativeCosetPairHalf (Good : Finset ℕ) (w : ℕ → ℕ)
    (i j : ℕ) : ℕ :=
  if i ∈ Good then
    if j ∈ Good then max (w i) (w j) else max (2 * w i) (w j)
  else if j ∈ Good then max (w i) (2 * w j) else max (w i) (w j)

def relativeIntervalDiagonalMax (s : ℕ) (Good : Finset ℕ)
    (w : ℕ → ℕ) (k : ℕ) : ℕ :=
  (intervalAntidiagonalPairs s k).sup fun p =>
    relativeCosetPairHalf Good w p.1 p.2

lemma mem_intervalAntidiagonalPairs {s k : ℕ} {p : ℕ × ℕ} :
    p ∈ intervalAntidiagonalPairs s k ↔
      p.1 < s ∧ p.2 < s ∧ p.1 + p.2 = k := by
  simp [intervalAntidiagonalPairs, and_assoc]

lemma relativeCosetPairHalf_le {Good : Finset ℕ} {w : ℕ → ℕ}
    {i j M : ℕ} (hi : w i ≤ M) (hj : w j ≤ M) :
    relativeCosetPairHalf Good w i j ≤ 2 * M := by
  simp only [relativeCosetPairHalf]
  split_ifs <;> simp only [max_le_iff] <;> omega

lemma max_le_relativeCosetPairHalf (Good : Finset ℕ) (w : ℕ → ℕ)
    (i j : ℕ) : max (w i) (w j) ≤ relativeCosetPairHalf Good w i j := by
  simp only [relativeCosetPairHalf]
  split_ifs <;> simp only [max_le_iff, le_max_iff] <;> omega

lemma relativeCosetPairHalf_of_good_bad {Good : Finset ℕ} {w : ℕ → ℕ}
    {i j : ℕ} (hi : i ∈ Good) (hj : j ∉ Good) :
    relativeCosetPairHalf Good w i j = max (2 * w i) (w j) := by
  simp [relativeCosetPairHalf, hi, hj]

lemma pairHalf_le_relativeIntervalDiagonalMax
    {s : ℕ} (Good : Finset ℕ) (w : ℕ → ℕ)
    {i j : ℕ} (hi : i < s) (hj : j < s) :
    relativeCosetPairHalf Good w i j ≤
      relativeIntervalDiagonalMax s Good w (i + j) := by
  unfold relativeIntervalDiagonalMax
  apply Finset.le_sup (s := intervalAntidiagonalPairs s (i + j))
    (f := fun p => relativeCosetPairHalf Good w p.1 p.2) (b := (i, j))
  exact mem_intervalAntidiagonalPairs.mpr ⟨hi, hj, rfl⟩

lemma relativeIntervalDiagonalMax_le
    {s M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ}
    (hmax : ∀ i ∈ Finset.range s, w i ≤ M) (k : ℕ) :
    relativeIntervalDiagonalMax s Good w k ≤ 2 * M := by
  apply Finset.sup_le
  intro p hp
  have hp' := mem_intervalAntidiagonalPairs.mp hp
  exact relativeCosetPairHalf_le
    (hmax p.1 (Finset.mem_range.mpr hp'.1))
    (hmax p.2 (Finset.mem_range.mpr hp'.2.1))

lemma relative_interval_threshold_bounds
    {s M : ℕ} {w : ℕ → ℕ} {Good Bad : Finset ℕ} {base : ℕ}
    (hspos : 0 < s) (hMpos : 0 < M)
    (hpart : Good ∪ Bad = Finset.range s) (hdisj : Disjoint Good Bad)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hmax : ∀ i ∈ Finset.range s, w i ≤ M)
    (hBad : Bad.Nonempty) :
    (∀ t ∈ Finset.range M,
      s + ((Finset.range s).filter (fun i => t < w i)).card - 1 ≤
        ((Finset.range (2 * s - 1)).filter fun k =>
          t < relativeIntervalDiagonalMax s Good w k).card) ∧
    (∀ u ∈ Finset.range M,
      (Good.filter (fun i => M + u < 2 * w i)).card + Bad.card - 1 ≤
        ((Finset.range (2 * s - 1)).filter fun k =>
          M + u < relativeIntervalDiagonalMax s Good w k).card) := by
  classical
  have hGoodSub : Good ⊆ Finset.range s := by
    intro i hi
    rw [← hpart]
    exact Finset.mem_union_left _ hi
  have hBadSub : Bad ⊆ Finset.range s := by
    intro i hi
    rw [← hpart]
    exact Finset.mem_union_right _ hi
  constructor
  · intro t ht
    let S := (Finset.range s).filter fun i => t < w i
    have hbaseRange := hGoodSub hbase
    have hSne : S.Nonempty := by
      refine ⟨base, Finset.mem_filter.mpr ⟨hbaseRange, ?_⟩⟩
      rw [hbasew]
      exact Finset.mem_range.mp ht
    have hrangeNe : (Finset.range s).Nonempty :=
      ⟨0, Finset.mem_range.mpr hspos⟩
    have haddLower : S.card + s - 1 ≤ (S + Finset.range s).card := by
      simpa using cauchy_davenport_add_of_linearOrder_isCancelAdd hSne hrangeNe
    have hsub : S + Finset.range s ⊆
        (Finset.range (2 * s - 1)).filter (fun k =>
          t < relativeIntervalDiagonalMax s Good w k) := by
      intro k hk
      obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp hk
      have hi' := Finset.mem_filter.mp hi
      have hiLt := Finset.mem_range.mp hi'.1
      have hj' := Finset.mem_range.mp hj
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        omega
      · have hpair := pairHalf_le_relativeIntervalDiagonalMax Good w
            (Finset.mem_range.mp hi'.1) hj'
        exact hi'.2.trans_le ((le_max_left _ _).trans
          ((max_le_relativeCosetPairHalf Good w i j).trans hpair))
    simpa [S, add_comm] using haddLower.trans (Finset.card_le_card hsub)
  · intro u hu
    let T := Good.filter fun i => M + u < 2 * w i
    have hTne : T.Nonempty := by
      refine ⟨base, Finset.mem_filter.mpr ⟨hbase, ?_⟩⟩
      rw [hbasew]
      have hu' := Finset.mem_range.mp hu
      omega
    have haddLower : T.card + Bad.card - 1 ≤ (T + Bad).card :=
      cauchy_davenport_add_of_linearOrder_isCancelAdd hTne hBad
    have hsub : T + Bad ⊆
        (Finset.range (2 * s - 1)).filter (fun k =>
          M + u < relativeIntervalDiagonalMax s Good w k) := by
      intro k hk
      obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp hk
      have hi' := Finset.mem_filter.mp hi
      have hiRange := hGoodSub hi'.1
      have hjRange := hBadSub hj
      have hjNotGood : j ∉ Good := by
        intro hjGood
        exact Finset.disjoint_left.mp hdisj hjGood hj
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        have hiLt := Finset.mem_range.mp hiRange
        have hjLt := Finset.mem_range.mp hjRange
        omega
      · have hpair := pairHalf_le_relativeIntervalDiagonalMax Good w
            (Finset.mem_range.mp hiRange) (Finset.mem_range.mp hjRange)
        rw [relativeCosetPairHalf_of_good_bad hi'.1 hjNotGood] at hpair
        exact hi'.2.trans_le ((le_max_left _ _).trans hpair)
    exact haddLower.trans (Finset.card_le_card hsub)

theorem relative_interval_diagonal_weight_bound
    {s M : ℕ} {w : ℕ → ℕ} {Good Bad : Finset ℕ} {base : ℕ}
    (hs : 6 ≤ s) (hMpos : 0 < M)
    (hpart : Good ∪ Bad = Finset.range s) (hdisj : Disjoint Good Bad)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hmax : ∀ i ∈ Finset.range s, w i ≤ M)
    (hBad : Bad.Nonempty) :
    5 * (∑ i ∈ Finset.range s, w i) ≤
      2 * ∑ k ∈ Finset.range (2 * s - 1),
        relativeIntervalDiagonalMax s Good w k := by
  classical
  let L := relativeIntervalDiagonalMax s Good w
  let G := ∑ i ∈ Good, w i
  let D := ∑ i ∈ Bad, w i
  let T := ∑ i ∈ Good, (2 * w i - M)
  have hGoodSub : Good ⊆ Finset.range s := by
    intro i hi
    rw [← hpart]
    exact Finset.mem_union_left _ hi
  have hBadSub : Bad ⊆ Finset.range s := by
    intro i hi
    rw [← hpart]
    exact Finset.mem_union_right _ hi
  have hGoodMax : ∀ i ∈ Good, w i ≤ M := by
    intro i hi
    exact hmax i (hGoodSub hi)
  have hD : D ≤ Bad.card * M := by
    dsimp [D]
    calc
      ∑ i ∈ Bad, w i ≤ ∑ _i ∈ Bad, M := by
        apply Finset.sum_le_sum
        intro i hi
        exact hmax i (hBadSub hi)
      _ = Bad.card * M := by simp
  have hcards : s = Good.card + Bad.card := by
    have := Finset.card_union_of_disjoint hdisj
    rw [hpart] at this
    simpa [add_comm] using this
  obtain ⟨hbasic, hstrong⟩ :=
    good_excess_bounds Good w hbase hbasew hGoodMax
  have harith : 5 * (G + D) ≤
      2 * ((G + D) + (s + Bad.card - 2) * M + T) := by
    apply relative_interval_arithmetic hs (Finset.card_pos.mpr hBad) hcards
      hD hbasic hstrong
  obtain ⟨hlow, hhigh⟩ := relative_interval_threshold_bounds
    (s := s) (M := M) (w := w) (Good := Good) (Bad := Bad) (base := base)
    (by omega) hMpos hpart hdisj hbase hbasew hmax hBad
  have hlayer : (G + D) + (s + Bad.card - 2) * M + T ≤
      ∑ k ∈ Finset.range (2 * s - 1), L k := by
    have hraw := relative_layerCake_lower s M w L Good Bad
      (by omega) hMpos hBad hpart hdisj hmax
      (fun k hk => relativeIntervalDiagonalMax_le hmax k) hlow hhigh
    have hsum : ∑ i ∈ Finset.range s, w i = G + D := by
      rw [← hpart, Finset.sum_union hdisj]
    simpa [G, D, T, L, hsum] using hraw
  have hsum : ∑ i ∈ Finset.range s, w i = G + D := by
    rw [← hpart, Finset.sum_union hdisj]
  rw [hsum]
  exact harith.trans (Nat.mul_le_mul_left 2 hlayer)

lemma intervalAntidiagonalPairs_nonempty {s k : ℕ}
    (hs : 0 < s) (hk : k < 2 * s - 1) :
    (intervalAntidiagonalPairs s k).Nonempty := by
  by_cases hks : k < s
  · refine ⟨(0, k), mem_intervalAntidiagonalPairs.mpr ?_⟩
    exact ⟨hs, hks, by omega⟩
  · refine ⟨(k - (s - 1), s - 1), mem_intervalAntidiagonalPairs.mpr ?_⟩
    constructor
    · omega
    constructor
    · omega
    · omega

noncomputable def relativeIntervalMaxPair
    (s : ℕ) (Good : Finset ℕ) (w : ℕ → ℕ) (hs : 0 < s)
    (k : Fin (2 * s - 1)) : ℕ × ℕ :=
  Classical.choose (Finset.exists_max_image (intervalAntidiagonalPairs s k.1)
    (fun p => relativeCosetPairHalf Good w p.1 p.2)
    (intervalAntidiagonalPairs_nonempty hs k.2))

lemma relativeIntervalMaxPair_mem
    {s : ℕ} (Good : Finset ℕ) (w : ℕ → ℕ) (hs : 0 < s)
    (k : Fin (2 * s - 1)) :
    relativeIntervalMaxPair s Good w hs k ∈ intervalAntidiagonalPairs s k.1 :=
  (Classical.choose_spec (Finset.exists_max_image
    (intervalAntidiagonalPairs s k.1)
    (fun p => relativeCosetPairHalf Good w p.1 p.2)
    (intervalAntidiagonalPairs_nonempty hs k.2))).1

lemma relativeIntervalMaxPair_realizes
    {s : ℕ} (Good : Finset ℕ) (w : ℕ → ℕ) (hs : 0 < s)
    (k : Fin (2 * s - 1)) :
    relativeCosetPairHalf Good w
        (relativeIntervalMaxPair s Good w hs k).1
        (relativeIntervalMaxPair s Good w hs k).2 =
      relativeIntervalDiagonalMax s Good w k.1 := by
  unfold relativeIntervalDiagonalMax
  apply le_antisymm
  · exact Finset.le_sup
      (s := intervalAntidiagonalPairs s k.1)
      (f := fun p => relativeCosetPairHalf Good w p.1 p.2)
      (b := relativeIntervalMaxPair s Good w hs k)
      (relativeIntervalMaxPair_mem Good w hs k)
  · apply Finset.sup_le
    intro p hp
    exact (Classical.choose_spec (Finset.exists_max_image
      (intervalAntidiagonalPairs s k.1)
      (fun p => relativeCosetPairHalf Good w p.1 p.2)
      (intervalAntidiagonalPairs_nonempty hs k.2))).2 p hp

lemma relativeIntervalMaxPair_sum
    {s : ℕ} (Good : Finset ℕ) (w : ℕ → ℕ) (hs : 0 < s)
    (k : Fin (2 * s - 1)) :
    (relativeIntervalMaxPair s Good w hs k).1 +
        (relativeIntervalMaxPair s Good w hs k).2 = k.1 :=
  (mem_intervalAntidiagonalPairs.mp
    (relativeIntervalMaxPair_mem Good w hs k)).2.2

theorem all_fibers_contained_of_interval_support_largest
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) {s base : ℕ}
    (hs : 6 ≤ s)
    (hsupport : firstCoordinateSet X = Finset.range s)
    (hsmall : 2 * (X + X).card < 5 * X.card)
    (hbase : base ∈ firstCoordinateSet X)
    (hbaseMax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X base).card)
    {H : AddSubgroup (ZMod d)}
    (hbaseCos : ContainedInAddCoset H (coordinateFiber X base)) :
    ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a) := by
  classical
  let w : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let M := w base
  let Good := (Finset.range s).filter fun a =>
    ContainedInAddCoset H (coordinateFiber X a)
  let Bad := Finset.range s \ Good
  have hbaseRange : base ∈ Finset.range s := by simpa [← hsupport] using hbase
  have hGoodSub : Good ⊆ Finset.range s := Finset.filter_subset _ _
  have hBadSub : Bad ⊆ Finset.range s := Finset.sdiff_subset
  have hbaseGood : base ∈ Good :=
    Finset.mem_filter.mpr ⟨hbaseRange, hbaseCos⟩
  have hpart : Good ∪ Bad = Finset.range s := by
    dsimp only [Bad]
    exact Finset.union_sdiff_of_subset hGoodSub
  have hdisj : Disjoint Good Bad := Finset.disjoint_sdiff
  have hGood : ∀ a ∈ Good,
      ContainedInAddCoset H (coordinateFiber X a) := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hBadNot : ∀ a ∈ Bad,
      ¬ContainedInAddCoset H (coordinateFiber X a) := by
    intro a ha hcos
    exact (Finset.mem_sdiff.mp ha).2
      (Finset.mem_filter.mpr ⟨hBadSub ha, hcos⟩)
  intro a ha
  by_contra haNot
  have haRange : a ∈ Finset.range s := by simpa [← hsupport] using ha
  have haBad : a ∈ Bad := Finset.mem_sdiff.mpr ⟨haRange, by
    intro haGood
    exact haNot (hGood a haGood)⟩
  have hBadNe : Bad.Nonempty := ⟨a, haBad⟩
  have hMpos : 0 < M := by
    dsimp only [M, w]
    exact Finset.card_pos.mpr (coordinateFiber_nonempty_iff.mpr hbase)
  have hmax : ∀ i ∈ Finset.range s, w i ≤ M := by
    intro i hi
    dsimp only [w, M]
    exact hbaseMax i (by simpa [hsupport] using hi)
  have hweight := relative_interval_diagonal_weight_bound
    (s := s) (M := M) (w := w) (Good := Good) (Bad := Bad) (base := base)
    hs hMpos hpart hdisj hbaseGood rfl hmax hBadNe
  let pair : Fin (2 * s - 1) → ℕ × ℕ :=
    relativeIntervalMaxPair s Good w (by omega)
  let P : Finset (ℕ × ℕ) := Finset.univ.image pair
  have hpairMem : ∀ k, pair k ∈ intervalAntidiagonalPairs s k.1 := by
    intro k
    exact relativeIntervalMaxPair_mem Good w (by omega) k
  have hpairBounds : ∀ k, (pair k).1 < s ∧ (pair k).2 < s := by
    intro k
    have hk := mem_intervalAntidiagonalPairs.mp (hpairMem k)
    exact ⟨hk.1, hk.2.1⟩
  have hpairSum : ∀ k, (pair k).1 + (pair k).2 = k.1 := by
    intro k
    exact (mem_intervalAntidiagonalPairs.mp (hpairMem k)).2.2
  have hpairInj : Function.Injective pair := by
    intro i j hij
    apply Fin.ext
    rw [← hpairSum i, ← hpairSum j, hij]
  have hPmem : ∀ p ∈ P,
      p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X := by
    intro p hp
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
    have hb := hpairBounds k
    rw [hsupport]
    exact ⟨Finset.mem_range.mpr hb.1, Finset.mem_range.mpr hb.2⟩
  have hPinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) P := by
    intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
    have hijVal : i.1 = j.1 := by simpa [hpairSum] using hpq
    have hij : i = j := Fin.ext hijVal
    subst j
    rfl
  have hpoint : ∀ k : Fin (2 * s - 1),
      relativeCosetPairHalf Good w (pair k).1 (pair k).2 ≤
        (coordinateFiber X (pair k).1 + coordinateFiber X (pair k).2).card := by
    intro k
    let i := (pair k).1
    let j := (pair k).2
    have hib := (hpairBounds k).1
    have hjb := (hpairBounds k).2
    have hiX : i ∈ firstCoordinateSet X := by
      rw [hsupport]
      exact Finset.mem_range.mpr hib
    have hjX : j ∈ firstCoordinateSet X := by
      rw [hsupport]
      exact Finset.mem_range.mpr hjb
    have hiNe := coordinateFiber_nonempty_iff.mpr hiX
    have hjNe := coordinateFiber_nonempty_iff.mpr hjX
    change relativeCosetPairHalf Good w i j ≤
      (coordinateFiber X i + coordinateFiber X j).card
    by_cases hiG : i ∈ Good <;> by_cases hjG : j ∈ Good
    · simp only [relativeCosetPairHalf, if_pos hiG, if_pos hjG]
      dsimp only [w]
      exact max_le (Finset.card_le_card_add_right hjNe)
        (Finset.card_le_card_add_left hiNe)
    · rw [relativeCosetPairHalf_of_good_bad hiG hjG]
      dsimp only [w]
      apply max_le
      · exact two_mul_card_le_add_of_coset_and_not_coset hiNe hjNe
          (hGood i hiG) (hBadNot j (Finset.mem_sdiff.mpr
            ⟨Finset.mem_range.mpr hjb, hjG⟩))
      · exact Finset.card_le_card_add_left hiNe
    · have htwo := two_mul_card_le_add_of_coset_and_not_coset
          hjNe hiNe (hGood j hjG) (hBadNot i (Finset.mem_sdiff.mpr
            ⟨Finset.mem_range.mpr hib, hiG⟩))
      simp only [relativeCosetPairHalf, if_neg hiG, if_pos hjG]
      dsimp only [w]
      apply max_le
      · exact Finset.card_le_card_add_right hjNe
      · simpa [add_comm] using htwo
    · simp only [relativeCosetPairHalf, if_neg hiG, if_neg hjG]
      dsimp only [w]
      exact max_le (Finset.card_le_card_add_right hjNe)
        (Finset.card_le_card_add_left hiNe)
  have hdiagToFiber :
      (∑ k : Fin (2 * s - 1),
          relativeIntervalDiagonalMax s Good w k.1) ≤
        ∑ k : Fin (2 * s - 1),
          (coordinateFiber X (pair k).1 + coordinateFiber X (pair k).2).card := by
    apply Finset.sum_le_sum
    intro k hk
    rw [← relativeIntervalMaxPair_realizes Good w (by omega) k]
    exact hpoint k
  have hfinToP : (∑ k : Fin (2 * s - 1),
        (coordinateFiber X (pair k).1 + coordinateFiber X (pair k).2).card) =
      ∑ p ∈ P,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    dsimp only [P]
    rw [Finset.sum_image hpairInj.injOn]
  have hPsum : (∑ p ∈ P,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card) ≤
      (X + X).card :=
    sum_card_coordinateFiber_add_le_card_add_of_pairSelection X P hPmem hPinj
  have hdiag : (∑ k ∈ Finset.range (2 * s - 1),
        relativeIntervalDiagonalMax s Good w k) ≤ (X + X).card := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact hdiagToFiber.trans (hfinToP.le.trans hPsum)
  have hXcard : X.card = ∑ i ∈ Finset.range s, w i := by
    rw [card_eq_sum_card_coordinateFiber X, hsupport]
  have : 5 * X.card ≤ 2 * (X + X).card := by
    rw [hXcard]
    exact hweight.trans (Nat.mul_le_mul_left 2 hdiag)
  omega

end Erdos360
