import ErdosProblems.Erdos360.FiberArithmeticRefined
import ErdosProblems.Erdos360.FiberLayerCake

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

def hybridPairWeight (M : ℕ) (Good : Finset ℕ) (w : ℕ → ℕ)
    (i j : ℕ) : ℕ :=
  max (2 * relativeCosetPairHalf Good w i j)
    (if M < max (w i) (w j) then pairWeight (w i) (w j) else 0)

def hybridIntervalDiagonalMax (s M : ℕ) (Good : Finset ℕ)
    (w : ℕ → ℕ) (k : ℕ) : ℕ :=
  (intervalAntidiagonalPairs s k).sup fun p =>
    hybridPairWeight M Good w p.1 p.2

lemma hybridPairWeight_le {M K : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ}
    {i j : ℕ} (hi : w i ≤ K) (hj : w j ≤ K) :
    hybridPairWeight M Good w i j ≤ 4 * K := by
  apply max_le
  · exact (Nat.mul_le_mul_left 2 (relativeCosetPairHalf_le hi hj)).trans_eq
      (by ring)
  · split_ifs
    · simp only [pairWeight, largestPairWeight, max_def, min_def]
      split_ifs <;> omega
    · omega

lemma hybridIntervalDiagonalMax_le
    {s M K : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ}
    (hmax : ∀ i ∈ Finset.range s, w i ≤ K) (k : ℕ) :
    hybridIntervalDiagonalMax s M Good w k ≤ 4 * K := by
  apply Finset.sup_le
  intro p hp
  have hp' := mem_intervalAntidiagonalPairs.mp hp
  exact hybridPairWeight_le
    (hmax p.1 (Finset.mem_range.mpr hp'.1))
    (hmax p.2 (Finset.mem_range.mpr hp'.2.1))

lemma hybridPairWeight_le_diagonal
    {s M : ℕ} (Good : Finset ℕ) (w : ℕ → ℕ)
    {i j : ℕ} (hi : i < s) (hj : j < s) :
    hybridPairWeight M Good w i j ≤
      hybridIntervalDiagonalMax s M Good w (i + j) := by
  unfold hybridIntervalDiagonalMax
  apply Finset.le_sup (s := intervalAntidiagonalPairs s (i + j))
    (f := fun p => hybridPairWeight M Good w p.1 p.2) (b := (i, j))
  exact mem_intervalAntidiagonalPairs.mpr ⟨hi, hj, rfl⟩

lemma two_max_le_hybridPairWeight
    (M : ℕ) (Good : Finset ℕ) (w : ℕ → ℕ) (i j : ℕ) :
    2 * max (w i) (w j) ≤ hybridPairWeight M Good w i j := by
  exact (Nat.mul_le_mul_left 2 (max_le_relativeCosetPairHalf Good w i j)).trans
    (le_max_left _ _)

lemma four_good_left_le_hybridPairWeight
    {M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i j : ℕ}
    (hi : i ∈ Good) (hj : j ∉ Good) :
    4 * w i ≤ hybridPairWeight M Good w i j := by
  unfold hybridPairWeight
  rw [relativeCosetPairHalf_of_good_bad hi hj]
  calc
    4 * w i = 2 * (2 * w i) := by ring
    _ ≤ 2 * max (2 * w i) (w j) :=
      Nat.mul_le_mul_left 2 (le_max_left _ _)
    _ ≤ _ := le_max_left _ _

lemma pairWeight_le_hybridPairWeight
    {M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {i j : ℕ}
    (hhigh : M < max (w i) (w j)) :
    pairWeight (w i) (w j) ≤ hybridPairWeight M Good w i j := by
  simp only [hybridPairWeight, if_pos hhigh]
  exact le_max_right _ _

lemma baseline_threshold_bound
    {s M K q : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ}
    (hs : 0 < s) (hq : q < 2 * K)
    (hbase : ∃ i ∈ Finset.range s, w i = K) :
    s + ((Finset.range s).filter (fun i => q < 2 * w i)).card - 1 ≤
      ((Finset.range (2 * s - 1)).filter fun k =>
        q < hybridIntervalDiagonalMax s M Good w k).card := by
  classical
  let U := (Finset.range s).filter fun i => q < 2 * w i
  have hUne : U.Nonempty := by
    obtain ⟨i, hi, hiw⟩ := hbase
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
    omega
  have hRangeNe : (Finset.range s).Nonempty :=
    ⟨0, Finset.mem_range.mpr hs⟩
  have hadd := cauchy_davenport_add_of_linearOrder_isCancelAdd hUne hRangeNe
  have hsub : U + Finset.range s ⊆
      (Finset.range (2 * s - 1)).filter (fun k =>
        q < hybridIntervalDiagonalMax s M Good w k) := by
    intro k hk
    obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp hk
    have hi' := Finset.mem_filter.mp hi
    have hiLt := Finset.mem_range.mp hi'.1
    have hjLt := Finset.mem_range.mp hj
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (by omega)
    · have hp := hybridPairWeight_le_diagonal (M := M) Good w hiLt hjLt
      exact hi'.2.trans_le ((Nat.mul_le_mul_left 2 (le_max_left _ _)).trans
        ((two_max_le_hybridPairWeight M Good w i j).trans hp))
  simpa [U, add_comm] using hadd.trans (Finset.card_le_card hsub)

lemma cross_bonus_threshold_bound
    {s M K u : ℕ} {Good Bad : Finset ℕ} {w : ℕ → ℕ} {base : ℕ}
    (hGoodSub : Good ⊆ Finset.range s) (hBadSub : Bad ⊆ Finset.range s)
    (hdisj : Disjoint Good Bad) (hBad : Bad.Nonempty)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hu : u < hybridG K M) :
    (Good.filter (fun i => 2 * K + u < 4 * w i)).card + Bad.card - 1 ≤
      ((Finset.range (2 * s - 1)).filter fun k =>
        2 * K + u < hybridIntervalDiagonalMax s M Good w k).card := by
  classical
  let U := Good.filter fun i => 2 * K + u < 4 * w i
  have hUne : U.Nonempty := by
    refine ⟨base, Finset.mem_filter.mpr ⟨hbase, ?_⟩⟩
    rw [hbasew]
    simp only [hybridG] at hu
    omega
  have hadd := cauchy_davenport_add_of_linearOrder_isCancelAdd hUne hBad
  have hsub : U + Bad ⊆
      (Finset.range (2 * s - 1)).filter (fun k =>
        2 * K + u < hybridIntervalDiagonalMax s M Good w k) := by
    intro k hk
    obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp hk
    have hi' := Finset.mem_filter.mp hi
    have hiRange := hGoodSub hi'.1
    have hjRange := hBadSub hj
    have hjNotGood : j ∉ Good := by
      intro hjG
      exact Finset.disjoint_left.mp hdisj hjG hj
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hiRange
        have := Finset.mem_range.mp hjRange
        omega)
    · have hp := hybridPairWeight_le_diagonal (M := M) Good w
          (Finset.mem_range.mp hiRange) (Finset.mem_range.mp hjRange)
      exact hi'.2.trans_le ((four_good_left_le_hybridPairWeight hi'.1 hjNotGood).trans hp)
  simpa [U] using hadd.trans (Finset.card_le_card hsub)

lemma top_star_threshold_bound
    {s M K u : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {top : ℕ}
    (hMK : M < K) (htop : top ∈ Finset.range s) (htopw : w top = K)
    (hu : u < K) :
    ((Finset.range s).filter (fun i =>
        2 * K + u < pairWeight K (w i))).card ≤
      ((Finset.range (2 * s - 1)).filter fun k =>
        2 * K + u < hybridIntervalDiagonalMax s M Good w k).card := by
  classical
  let U := (Finset.range s).filter fun i =>
    2 * K + u < pairWeight K (w i)
  have hUne : U.Nonempty := by
    refine ⟨top, Finset.mem_filter.mpr ⟨htop, ?_⟩⟩
    rw [htopw, pairWeight_self]
    omega
  have hsingle : ({top} : Finset ℕ).Nonempty := Finset.singleton_nonempty top
  have hadd := cauchy_davenport_add_of_linearOrder_isCancelAdd hsingle hUne
  have hsub : ({top} : Finset ℕ) + U ⊆
      (Finset.range (2 * s - 1)).filter (fun k =>
        2 * K + u < hybridIntervalDiagonalMax s M Good w k) := by
    intro k hk
    obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp hk
    have hiTop : i = top := by simpa using hi
    subst i
    have hj' := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (by
        have := Finset.mem_range.mp htop
        have := Finset.mem_range.mp hj'.1
        omega)
    · have hp := hybridPairWeight_le_diagonal (M := M) Good w
          (Finset.mem_range.mp htop) (Finset.mem_range.mp hj'.1)
      have hhigh : M < max (w top) (w j) := by rw [htopw]; omega
      have hpw := pairWeight_le_hybridPairWeight (Good := Good) hhigh
      rw [htopw] at hpw
      exact hj'.2.trans_le (hpw.trans hp)
  have hc := hadd.trans (Finset.card_le_card hsub)
  simpa [U] using hc

lemma three_min_le_pairWeight (a b : ℕ) :
    3 * min a b ≤ pairWeight a b := by
  have hminmax : min a b ≤ max a b :=
    (min_le_left a b).trans (le_max_left a b)
  exact (show 3 * min a b ≤ max a b + 2 * min a b by omega).trans
    (max_add_two_min_le_pairWeight a b)

lemma high_bonus_threshold_bound
    {s M K u : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {top : ℕ}
    (hGoodSub : Good ⊆ Finset.range s)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M)
    (htop : top ∈ Finset.range s) (htopw : w top = K)
    (hMK : M < K) (hu : u < K) :
    (Good.filter (fun i => 2 * K + u < 4 * w i)).card +
        2 * ((Finset.range s).filter (fun i =>
          M < w i ∧ 2 * K + u < 3 * w i)).card - 1 ≤
      ((Finset.range (2 * s - 1)).filter fun k =>
        2 * K + u < hybridIntervalDiagonalMax s M Good w k).card := by
  classical
  let GU := Good.filter fun i => 2 * K + u < 4 * w i
  let AU := (Finset.range s).filter fun i =>
    M < w i ∧ 2 * K + u < 3 * w i
  let V := GU ∪ AU
  have htopAU : top ∈ AU := by
    refine Finset.mem_filter.mpr ⟨htop, ?_⟩
    rw [htopw]
    exact ⟨hMK, by omega⟩
  have hAUne : AU.Nonempty := ⟨top, htopAU⟩
  have hVne : V.Nonempty := by
    exact ⟨top, Finset.mem_union_right _ htopAU⟩
  have hdisj : Disjoint GU AU := by
    rw [Finset.disjoint_left]
    intro i hiG hiA
    have hiG' := Finset.mem_filter.mp hiG
    have hiA' := Finset.mem_filter.mp hiA
    have := hGoodMax i hiG'.1
    omega
  have hadd := cauchy_davenport_add_of_linearOrder_isCancelAdd hVne hAUne
  have hsub : V + AU ⊆
      (Finset.range (2 * s - 1)).filter (fun k =>
        2 * K + u < hybridIntervalDiagonalMax s M Good w k) := by
    intro k hk
    obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp hk
    have hj' := Finset.mem_filter.mp hj
    have hjRange := hj'.1
    have hjCond := hj'.2
    have hiUnion := Finset.mem_union.mp hi
    have hiRange : i ∈ Finset.range s := by
      rcases hiUnion with hiG | hiA
      · exact hGoodSub (Finset.mem_filter.mp hiG).1
      · exact (Finset.mem_filter.mp hiA).1
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hiRange
        have := Finset.mem_range.mp hjRange
        omega)
    · have hp := hybridPairWeight_le_diagonal (M := M) Good w
          (Finset.mem_range.mp hiRange) (Finset.mem_range.mp hjRange)
      rcases hiUnion with hiG | hiA
      · have hiG' := Finset.mem_filter.mp hiG
        have hjNotGood : j ∉ Good := by
          intro hjG
          have := hGoodMax j hjG
          omega
        exact hiG'.2.trans_le
          ((four_good_left_le_hybridPairWeight hiG'.1 hjNotGood).trans hp)
      · have hiA' := Finset.mem_filter.mp hiA
        have hthreshold : 2 * K + u < pairWeight (w i) (w j) := by
          have hthree := three_min_le_pairWeight (w i) (w j)
          have hmin : 2 * K + u < 3 * min (w i) (w j) := by
            simp only [min_def]
            split_ifs <;> omega
          exact hmin.trans_le hthree
        have hhigh : M < max (w i) (w j) :=
          hjCond.1.trans_le (le_max_right _ _)
        exact hthreshold.trans_le
          ((pairWeight_le_hybridPairWeight (Good := Good) hhigh).trans hp)
  have hc := hadd.trans (Finset.card_le_card hsub)
  have hVcard : V.card = GU.card + AU.card := Finset.card_union_of_disjoint hdisj
  rw [hVcard] at hc
  dsimp only [GU, AU, V] at hc ⊢
  omega

lemma hybridG_le_two_mul {K w : ℕ} (hw : w ≤ K) :
    hybridG K w ≤ 2 * K := by
  simp only [hybridG]
  omega

lemma hybridG_le_of_le {K w M : ℕ} (hw : w ≤ M) :
    hybridG K w ≤ hybridG K M := by
  simp only [hybridG]
  omega

lemma hybridA_le {K w : ℕ} (hw : w ≤ K) : hybridA K w ≤ K := by
  simp only [hybridA]
  omega

lemma hybridT_le {K w : ℕ} (hw : w ≤ K) : hybridT K w ≤ K := by
  simp only [hybridT, pairWeight, largestPairWeight,
    max_eq_left hw, min_eq_right hw, max_def]
  split_ifs <;> omega

lemma baseline_layer_sum_lower
    {s M K : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ}
    (hs : 0 < s) (hmax : ∀ i ∈ Finset.range s, w i ≤ K)
    (hbase : ∃ i ∈ Finset.range s, w i = K) :
    2 * ((∑ i ∈ Finset.range s, w i) + (s - 1) * K) ≤
      ∑ q ∈ Finset.range (2 * K),
        ((Finset.range (2 * s - 1)).filter fun k =>
          q < hybridIntervalDiagonalMax s M Good w k).card := by
  classical
  have hpoint : ∀ q ∈ Finset.range (2 * K),
      s + ((Finset.range s).filter (fun i => q < 2 * w i)).card - 1 ≤
        ((Finset.range (2 * s - 1)).filter fun k =>
          q < hybridIntervalDiagonalMax s M Good w k).card := by
    intro q hq
    exact baseline_threshold_bound
      (M := M) (Good := Good) (w := w) hs (Finset.mem_range.mp hq) hbase
  have hsum := Finset.sum_le_sum hpoint
  have hweights :
      (∑ q ∈ Finset.range (2 * K),
        ((Finset.range s).filter (fun i => q < 2 * w i)).card) =
        2 * ∑ i ∈ Finset.range s, w i := by
    have heq := sum_card_filter_lt_eq_sum (Finset.range s)
      (fun i => 2 * w i) (2 * K) (by
        intro i hi
        exact Nat.mul_le_mul_left 2 (hmax i hi))
    simpa [Finset.mul_sum] using heq
  have heval :
      (∑ q ∈ Finset.range (2 * K),
        (s + ((Finset.range s).filter (fun i => q < 2 * w i)).card - 1)) =
        2 * ((∑ i ∈ Finset.range s, w i) + (s - 1) * K) := by
    have hterm : ∀ q ∈ Finset.range (2 * K),
        s + ((Finset.range s).filter (fun i => q < 2 * w i)).card - 1 =
          ((Finset.range s).filter (fun i => q < 2 * w i)).card + (s - 1) := by
      intro q hq
      omega
    calc
      _ = ∑ q ∈ Finset.range (2 * K),
          (((Finset.range s).filter (fun i => q < 2 * w i)).card +
            (s - 1)) := Finset.sum_congr rfl hterm
      _ = 2 * ∑ i ∈ Finset.range s, w i + (2 * K) * (s - 1) := by
        rw [Finset.sum_add_distrib, hweights]
        simp
      _ = _ := by ring
  rw [heval] at hsum
  exact hsum

lemma cross_bonus_layer_sum_lower
    {s M K : ℕ} {Good Bad : Finset ℕ} {w : ℕ → ℕ} {base : ℕ}
    (hGoodSub : Good ⊆ Finset.range s) (hBadSub : Bad ⊆ Finset.range s)
    (hdisj : Disjoint Good Bad) (hBad : Bad.Nonempty)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M) (hMK : M ≤ K) :
    (∑ i ∈ Good, hybridG K (w i)) +
        (Bad.card - 1) * hybridG K M ≤
      ∑ u ∈ Finset.range (2 * K),
        ((Finset.range (2 * s - 1)).filter fun k =>
          2 * K + u < hybridIntervalDiagonalMax s M Good w k).card := by
  classical
  let gm := hybridG K M
  have hgm : gm ≤ 2 * K := hybridG_le_two_mul hMK
  have hpoint : ∀ u ∈ Finset.range gm,
      (Good.filter (fun i => 2 * K + u < 4 * w i)).card +
          Bad.card - 1 ≤
        ((Finset.range (2 * s - 1)).filter fun k =>
          2 * K + u < hybridIntervalDiagonalMax s M Good w k).card := by
    intro u hu
    exact cross_bonus_threshold_bound hGoodSub hBadSub hdisj hBad
      hbase hbasew (Finset.mem_range.mp hu)
  have hsum := Finset.sum_le_sum hpoint
  have hfilter : ∀ u ∈ Finset.range gm,
      Good.filter (fun i => 2 * K + u < 4 * w i) =
        Good.filter (fun i => u < hybridG K (w i)) := by
    intro u hu
    ext i
    simp only [Finset.mem_filter]
    constructor <;> intro hi
    · refine ⟨hi.1, ?_⟩
      simp only [hybridG]
      omega
    · refine ⟨hi.1, ?_⟩
      simp only [hybridG] at hi
      omega
  have hgBound : ∀ i ∈ Good, hybridG K (w i) ≤ gm := by
    intro i hi
    exact hybridG_le_of_le (hGoodMax i hi)
  have hcardSum :
      (∑ u ∈ Finset.range gm,
        (Good.filter (fun i => 2 * K + u < 4 * w i)).card) =
        ∑ i ∈ Good, hybridG K (w i) := by
    calc
      _ = ∑ u ∈ Finset.range gm,
          (Good.filter (fun i => u < hybridG K (w i))).card := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hfilter u hu]
      _ = _ := sum_card_filter_lt_eq_sum Good (fun i => hybridG K (w i)) gm hgBound
  have hleftEval :
      (∑ u ∈ Finset.range gm,
        ((Good.filter (fun i => 2 * K + u < 4 * w i)).card +
          Bad.card - 1)) =
        (∑ i ∈ Good, hybridG K (w i)) + (Bad.card - 1) * gm := by
    have hBadPos : 1 ≤ Bad.card := Finset.card_pos.mpr hBad
    have hterm : ∀ u ∈ Finset.range gm,
        (Good.filter (fun i => 2 * K + u < 4 * w i)).card + Bad.card - 1 =
          (Good.filter (fun i => 2 * K + u < 4 * w i)).card +
            (Bad.card - 1) := by intro u hu; omega
    calc
      _ = ∑ u ∈ Finset.range gm,
          ((Good.filter (fun i => 2 * K + u < 4 * w i)).card +
            (Bad.card - 1)) := Finset.sum_congr rfl hterm
      _ = _ := by
        rw [Finset.sum_add_distrib, hcardSum]
        simp
        ring
  rw [hleftEval] at hsum
  have hsub : Finset.range gm ⊆ Finset.range (2 * K) := by
    intro u hu
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hu).trans_le hgm)
  have hsumSub :
      (∑ u ∈ Finset.range gm,
        ((Finset.range (2 * s - 1)).filter fun k =>
          2 * K + u < hybridIntervalDiagonalMax s M Good w k).card) ≤
      ∑ u ∈ Finset.range (2 * K),
        ((Finset.range (2 * s - 1)).filter fun k =>
          2 * K + u < hybridIntervalDiagonalMax s M Good w k).card :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro i hi hin
      positivity)
  exact hsum.trans hsumSub

lemma top_star_layer_sum_lower
    {s M K : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {top : ℕ}
    (hMK : M < K) (htop : top ∈ Finset.range s) (htopw : w top = K)
    (hmax : ∀ i ∈ Finset.range s, w i ≤ K) :
    (∑ i ∈ Finset.range s, hybridT K (w i)) ≤
      ∑ u ∈ Finset.range (2 * K),
        ((Finset.range (2 * s - 1)).filter fun k =>
          2 * K + u < hybridIntervalDiagonalMax s M Good w k).card := by
  classical
  have hpoint : ∀ u ∈ Finset.range K,
      ((Finset.range s).filter (fun i =>
          2 * K + u < pairWeight K (w i))).card ≤
        ((Finset.range (2 * s - 1)).filter fun k =>
          2 * K + u < hybridIntervalDiagonalMax s M Good w k).card := by
    intro u hu
    exact top_star_threshold_bound hMK htop htopw (Finset.mem_range.mp hu)
  have hsum := Finset.sum_le_sum hpoint
  have hfilter : ∀ u ∈ Finset.range K,
      (Finset.range s).filter (fun i => 2 * K + u < pairWeight K (w i)) =
        (Finset.range s).filter (fun i => u < hybridT K (w i)) := by
    intro u hu
    ext i
    simp only [Finset.mem_filter]
    constructor <;> intro hi
    · refine ⟨hi.1, ?_⟩
      simp only [hybridT]
      omega
    · refine ⟨hi.1, ?_⟩
      simp only [hybridT] at hi
      omega
  have hbound : ∀ i ∈ Finset.range s, hybridT K (w i) ≤ K := by
    intro i hi
    exact hybridT_le (hmax i hi)
  have heval :
      (∑ u ∈ Finset.range K,
        ((Finset.range s).filter (fun i =>
          2 * K + u < pairWeight K (w i))).card) =
        ∑ i ∈ Finset.range s, hybridT K (w i) := by
    calc
      _ = ∑ u ∈ Finset.range K,
          ((Finset.range s).filter (fun i => u < hybridT K (w i))).card := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hfilter u hu]
      _ = _ := sum_card_filter_lt_eq_sum (Finset.range s)
        (fun i => hybridT K (w i)) K hbound
  rw [heval] at hsum
  have hsub : Finset.range K ⊆ Finset.range (2 * K) := by
    intro u hu
    exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hu; omega)
  exact hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (by
    intro i hi hin
    positivity))

lemma sum_two_mul_sub_one (A : Finset ℕ) (f : ℕ → ℕ)
    (hpos : ∀ i ∈ A, 1 ≤ f i) :
    (∑ i ∈ A, (2 * f i - 1)) = 2 * (∑ i ∈ A, f i) - A.card := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
      have hfa := hpos a (Finset.mem_insert_self a A)
      have hrest : ∀ i ∈ A, 1 ≤ f i := by
        intro i hi
        exact hpos i (Finset.mem_insert_of_mem hi)
      have hi := ih hrest
      have hcardle : A.card ≤ ∑ i ∈ A, f i := by
        calc
          A.card = ∑ _i ∈ A, 1 := by simp
          _ ≤ ∑ i ∈ A, f i := by
            apply Finset.sum_le_sum
            intro i hi
            exact hrest i hi
      simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      omega

lemma high_bonus_layer_sum_lower
    {s M K : ℕ} {Good Bad : Finset ℕ} {w : ℕ → ℕ} {base top : ℕ}
    (hGoodSub : Good ⊆ Finset.range s) (hBadSub : Bad ⊆ Finset.range s)
    (hdisj : Disjoint Good Bad) (hBad : Bad.Nonempty)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M)
    (htop : top ∈ Finset.range s) (htopw : w top = K)
    (hMK : M < K) (hmax : ∀ i ∈ Finset.range s, w i ≤ K) :
    (∑ i ∈ Good, hybridG K (w i)) +
        (Bad.card - 1) * (hybridG K M - K) +
        (2 * (∑ i ∈ (Finset.range s).filter (fun i => M < w i),
          hybridA K (w i)) - K) ≤
      ∑ u ∈ Finset.range (2 * K),
        ((Finset.range (2 * s - 1)).filter fun k =>
          2 * K + u < hybridIntervalDiagonalMax s M Good w k).card := by
  classical
  let gm := hybridG K M
  let tail := gm - K
  let AS := (Finset.range s).filter fun i => M < w i
  let F : ℕ → ℕ := fun u =>
    ((Finset.range (2 * s - 1)).filter fun k =>
      2 * K + u < hybridIntervalDiagonalMax s M Good w k).card
  have hgm : gm ≤ 2 * K := hybridG_le_two_mul hMK.le
  have htail : tail ≤ K := by dsimp only [tail]; omega
  have htopAS : top ∈ AS := Finset.mem_filter.mpr ⟨htop, by rw [htopw]; exact hMK⟩
  have hmainPoint : ∀ u ∈ Finset.range K,
      (Good.filter (fun i => 2 * K + u < 4 * w i)).card +
          2 * ((Finset.range s).filter (fun i =>
            M < w i ∧ 2 * K + u < 3 * w i)).card - 1 ≤ F u := by
    intro u hu
    exact high_bonus_threshold_bound hGoodSub hGoodMax htop htopw hMK
      (Finset.mem_range.mp hu)
  have hmain := Finset.sum_le_sum hmainPoint
  have hGoodFilter : ∀ u ∈ Finset.range K,
      Good.filter (fun i => 2 * K + u < 4 * w i) =
        Good.filter (fun i => u < hybridG K (w i)) := by
    intro u hu
    ext i
    simp only [Finset.mem_filter]
    constructor <;> intro hi
    · refine ⟨hi.1, ?_⟩
      simp only [hybridG]
      omega
    · refine ⟨hi.1, ?_⟩
      simp only [hybridG] at hi
      omega
  have hAFilter : ∀ u ∈ Finset.range K,
      (Finset.range s).filter (fun i => M < w i ∧ 2 * K + u < 3 * w i) =
        AS.filter (fun i => u < hybridA K (w i)) := by
    intro u hu
    dsimp only [AS]
    ext i
    simp only [Finset.mem_filter]
    constructor <;> intro hi
    · refine ⟨⟨hi.1, hi.2.1⟩, ?_⟩
      simp only [hybridA]
      omega
    · refine ⟨hi.1.1, hi.1.2, ?_⟩
      simp only [hybridA] at hi
      omega
  have hgTrunc :
      (∑ u ∈ Finset.range K,
        (Good.filter (fun i => 2 * K + u < 4 * w i)).card) =
        ∑ i ∈ Good, min (hybridG K (w i)) K := by
    calc
      _ = ∑ u ∈ Finset.range K,
          (Good.filter (fun i => u < hybridG K (w i))).card := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hGoodFilter u hu]
      _ = _ := sum_card_filter_lt_eq_sum_min Good
        (fun i => hybridG K (w i)) K
  have haBound : ∀ i ∈ AS, hybridA K (w i) ≤ K := by
    intro i hi
    exact hybridA_le (hmax i (Finset.mem_filter.mp hi).1)
  have haSum :
      (∑ u ∈ Finset.range K,
        ((Finset.range s).filter (fun i =>
          M < w i ∧ 2 * K + u < 3 * w i)).card) =
        ∑ i ∈ AS, hybridA K (w i) := by
    calc
      _ = ∑ u ∈ Finset.range K,
          (AS.filter (fun i => u < hybridA K (w i))).card := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hAFilter u hu]
      _ = _ := sum_card_filter_lt_eq_sum AS (fun i => hybridA K (w i)) K haBound
  have hmainEval :
      (∑ u ∈ Finset.range K,
        ((Good.filter (fun i => 2 * K + u < 4 * w i)).card +
          2 * ((Finset.range s).filter (fun i =>
            M < w i ∧ 2 * K + u < 3 * w i)).card - 1)) =
        (∑ i ∈ Good, min (hybridG K (w i)) K) +
          (2 * (∑ i ∈ AS, hybridA K (w i)) - K) := by
    have hANe : ∀ u ∈ Finset.range K,
        1 ≤ ((Finset.range s).filter (fun i =>
          M < w i ∧ 2 * K + u < 3 * w i)).card := by
      intro u hu
      apply Finset.card_pos.mpr
      refine ⟨top, Finset.mem_filter.mpr ⟨htop, ?_⟩⟩
      rw [htopw]
      exact ⟨hMK, by have := Finset.mem_range.mp hu; omega⟩
    have hterm : ∀ u ∈ Finset.range K,
        (Good.filter (fun i => 2 * K + u < 4 * w i)).card +
            2 * ((Finset.range s).filter (fun i =>
              M < w i ∧ 2 * K + u < 3 * w i)).card - 1 =
          (Good.filter (fun i => 2 * K + u < 4 * w i)).card +
            (2 * ((Finset.range s).filter (fun i =>
              M < w i ∧ 2 * K + u < 3 * w i)).card - 1) := by
      intro u hu
      have := hANe u hu
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hgTrunc]
    have htwice :
        (∑ u ∈ Finset.range K,
          (2 * ((Finset.range s).filter (fun i =>
            M < w i ∧ 2 * K + u < 3 * w i)).card - 1)) =
          2 * (∑ i ∈ AS, hybridA K (w i)) - K := by
      have hh := sum_two_mul_sub_one (Finset.range K)
        (fun u => ((Finset.range s).filter (fun i =>
          M < w i ∧ 2 * K + u < 3 * w i)).card) hANe
      simpa [haSum] using hh
    rw [htwice]
  rw [hmainEval] at hmain
  have htailPoint : ∀ v ∈ Finset.range tail,
      (Good.filter (fun i => 2 * K + (K + v) < 4 * w i)).card +
          Bad.card - 1 ≤ F (K + v) := by
    intro v hv
    have huv : K + v < gm := by
      dsimp only [tail] at hv
      have := Finset.mem_range.mp hv
      omega
    exact cross_bonus_threshold_bound hGoodSub hBadSub hdisj hBad
      hbase hbasew huv
  have htailSum := Finset.sum_le_sum htailPoint
  have hTailFilter : ∀ v ∈ Finset.range tail,
      Good.filter (fun i => 2 * K + (K + v) < 4 * w i) =
        Good.filter (fun i => v < hybridG K (w i) - K) := by
    intro v hv
    ext i
    simp only [Finset.mem_filter]
    constructor <;> intro hi
    · refine ⟨hi.1, ?_⟩
      simp only [hybridG]
      omega
    · refine ⟨hi.1, ?_⟩
      simp only [hybridG] at hi
      omega
  have htailBound : ∀ i ∈ Good, hybridG K (w i) - K ≤ tail := by
    intro i hi
    dsimp only [tail, gm]
    exact Nat.sub_le_sub_right (hybridG_le_of_le (hGoodMax i hi)) K
  have htailGood :
      (∑ v ∈ Finset.range tail,
        (Good.filter (fun i => 2 * K + (K + v) < 4 * w i)).card) =
        ∑ i ∈ Good, (hybridG K (w i) - K) := by
    calc
      _ = ∑ v ∈ Finset.range tail,
          (Good.filter (fun i => v < hybridG K (w i) - K)).card := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [hTailFilter v hv]
      _ = _ := sum_card_filter_lt_eq_sum Good
        (fun i => hybridG K (w i) - K) tail htailBound
  have htailEval :
      (∑ v ∈ Finset.range tail,
        ((Good.filter (fun i => 2 * K + (K + v) < 4 * w i)).card +
          Bad.card - 1)) =
        (∑ i ∈ Good, (hybridG K (w i) - K)) +
          (Bad.card - 1) * tail := by
    have hBadPos : 1 ≤ Bad.card := Finset.card_pos.mpr hBad
    have hterm : ∀ v ∈ Finset.range tail,
        (Good.filter (fun i => 2 * K + (K + v) < 4 * w i)).card + Bad.card - 1 =
          (Good.filter (fun i => 2 * K + (K + v) < 4 * w i)).card +
            (Bad.card - 1) := by intros; omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, htailGood]
    simp
    ring
  rw [htailEval] at htailSum
  have hgoodSplit :
      (∑ i ∈ Good, min (hybridG K (w i)) K) +
        ∑ i ∈ Good, (hybridG K (w i) - K) =
        ∑ i ∈ Good, hybridG K (w i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    omega
  have hbonusToTwo :
      (∑ i ∈ Good, hybridG K (w i)) + (Bad.card - 1) * tail +
          (2 * (∑ i ∈ AS, hybridA K (w i)) - K) ≤
        (∑ u ∈ Finset.range K, F u) +
          ∑ v ∈ Finset.range tail, F (K + v) := by
    calc
      _ = ((∑ i ∈ Good, min (hybridG K (w i)) K) +
            (2 * (∑ i ∈ AS, hybridA K (w i)) - K)) +
          ((∑ i ∈ Good, (hybridG K (w i) - K)) +
            (Bad.card - 1) * tail) := by omega
      _ ≤ _ := Nat.add_le_add hmain htailSum
  let TailRange := (Finset.range tail).image fun v => K + v
  have hinj : Set.InjOn (fun v : ℕ => K + v) (Finset.range tail) := by
    intro a ha b hb hab
    exact Nat.add_left_cancel hab
  have htailImage : (∑ v ∈ Finset.range tail, F (K + v)) =
      ∑ u ∈ TailRange, F u := by
    dsimp only [TailRange]
    rw [Finset.sum_image hinj]
  have hdisjRange : Disjoint (Finset.range K) TailRange := by
    rw [Finset.disjoint_left]
    intro u hu huT
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp huT
    have := Finset.mem_range.mp hu
    omega
  have hQsub : Finset.range K ∪ TailRange ⊆ Finset.range (2 * K) := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hu; omega)
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hv
        omega)
  rw [htailImage] at hbonusToTwo
  rw [← Finset.sum_union hdisjRange] at hbonusToTwo
  have hfull : (∑ u ∈ Finset.range K ∪ TailRange, F u) ≤
      ∑ u ∈ Finset.range (2 * K), F u :=
    Finset.sum_le_sum_of_subset_of_nonneg hQsub (by
    intro i hi hin
    exact Nat.zero_le _)
  dsimp only [F, tail, gm, AS] at hbonusToTwo ⊢
  exact hbonusToTwo.trans hfull

lemma hybrid_layer_sum_split
    {s M K : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ}
    (hmax : ∀ i ∈ Finset.range s, w i ≤ K) :
    (∑ q ∈ Finset.range (2 * K),
        ((Finset.range (2 * s - 1)).filter fun k =>
          q < hybridIntervalDiagonalMax s M Good w k).card) +
      (∑ u ∈ Finset.range (2 * K),
        ((Finset.range (2 * s - 1)).filter fun k =>
          2 * K + u < hybridIntervalDiagonalMax s M Good w k).card) =
      ∑ k ∈ Finset.range (2 * s - 1),
        hybridIntervalDiagonalMax s M Good w k := by
  classical
  let L := hybridIntervalDiagonalMax s M Good w
  have hLmax : ∀ k ∈ Finset.range (2 * s - 1), L k ≤ 4 * K := by
    intro k hk
    exact hybridIntervalDiagonalMax_le hmax k
  have hsumL := sum_card_filter_lt_eq_sum
    (Finset.range (2 * s - 1)) L (4 * K) hLmax
  have hsplitRange : Finset.range (4 * K) =
      Finset.range (2 * K) ∪
        (Finset.range (2 * K)).image (fun u => 2 * K + u) := by
    ext q
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
    constructor
    · intro hq
      by_cases hlow : q < 2 * K
      · exact Or.inl hlow
      · exact Or.inr ⟨q - 2 * K, by omega, by omega⟩
    · rintro (hq | ⟨u, hu, rfl⟩)
      · omega
      · omega
  have hdisj : Disjoint (Finset.range (2 * K))
      ((Finset.range (2 * K)).image (fun u => 2 * K + u)) := by
    rw [Finset.disjoint_left]
    intro q hq hqi
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hqi
    have := Finset.mem_range.mp hq
    omega
  rw [← hsumL, hsplitRange, Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact Nat.add_left_cancel hab

theorem hybrid_interval_diagonal_weight_bound
    {s M K : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ} {base top : ℕ}
    (hs : 6 ≤ s) (hGoodSub : Good ⊆ Finset.range s)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (htop : top ∈ Finset.range s) (htopw : w top = K)
    (hMK : M < K) (hmax : ∀ i ∈ Finset.range s, w i ≤ K)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M)
    (hBad : (Finset.range s \ Good).Nonempty) :
    5 * (∑ i ∈ Finset.range s, w i) ≤
      ∑ k ∈ Finset.range (2 * s - 1),
        hybridIntervalDiagonalMax s M Good w k := by
  classical
  let A := Finset.range s
  let Bad := A \ Good
  let G := ∑ i ∈ Good, hybridG K (w i)
  let AH := ∑ i ∈ A.filter (fun i => M < w i), hybridA K (w i)
  let T := ∑ i ∈ A, hybridT K (w i)
  let C := G + (Bad.card - 1) * hybridG K M
  let AA := G + (Bad.card - 1) * (hybridG K M - K) + (2 * AH - K)
  let B := max C (max AA T)
  let LowSum := ∑ q ∈ Finset.range (2 * K),
    ((Finset.range (2 * s - 1)).filter fun k =>
      q < hybridIntervalDiagonalMax s M Good w k).card
  let HighSum := ∑ u ∈ Finset.range (2 * K),
    ((Finset.range (2 * s - 1)).filter fun k =>
      2 * K + u < hybridIntervalDiagonalMax s M Good w k).card
  have hBadSub : Bad ⊆ A := Finset.sdiff_subset
  have hdisj : Disjoint Good Bad := Finset.disjoint_sdiff
  have htopBase : ∃ i ∈ A, w i = K := ⟨top, htop, htopw⟩
  have hlow : 2 * ((∑ i ∈ A, w i) + (s - 1) * K) ≤ LowSum := by
    exact baseline_layer_sum_lower (M := M) (Good := Good)
      (by omega) hmax htopBase
  have hcross : C ≤ HighSum := by
    dsimp only [C, G, Bad, HighSum, A]
    exact cross_bonus_layer_sum_lower hGoodSub hBadSub hdisj hBad
      hbase hbasew hGoodMax hMK.le
  have hhigh : AA ≤ HighSum := by
    dsimp only [AA, G, AH, Bad, HighSum, A]
    exact high_bonus_layer_sum_lower hGoodSub hBadSub hdisj hBad
      hbase hbasew hGoodMax htop htopw hMK hmax
  have hstar : T ≤ HighSum := by
    dsimp only [T, HighSum, A]
    exact top_star_layer_sum_lower hMK htop htopw hmax
  have hbonus : B ≤ HighSum := by
    dsimp only [B]
    exact max_le hcross (max_le hhigh hstar)
  have harith : 5 * (∑ i ∈ A, w i) ≤
      2 * ((∑ i ∈ A, w i) + (A.card - 1) * K) + B := by
    dsimp only [B, C, AA, G, AH, T, Bad]
    exact hybrid_three_branch_arithmetic A Good w
      (by simpa [A] using hs) hGoodSub (hGoodSub hbase) htop hbase hbasew htopw
      hMK hmax hGoodMax
  have htoSums : 5 * (∑ i ∈ A, w i) ≤ LowSum + HighSum := by
    have := Nat.add_le_add hlow hbonus
    have hAcard : A.card = s := by simp [A]
    rw [hAcard] at harith
    exact harith.trans (by omega)
  have hsplit := hybrid_layer_sum_split (M := M) (Good := Good) hmax
  dsimp only [A, LowSum, HighSum] at htoSums ⊢
  rw [hsplit] at htoSums
  exact htoSums

noncomputable def hybridIntervalMaxPair
    (s M : ℕ) (Good : Finset ℕ) (w : ℕ → ℕ) (hs : 0 < s)
    (k : Fin (2 * s - 1)) : ℕ × ℕ :=
  Classical.choose (Finset.exists_max_image (intervalAntidiagonalPairs s k.1)
    (fun p => hybridPairWeight M Good w p.1 p.2)
    (intervalAntidiagonalPairs_nonempty hs k.2))

lemma hybridIntervalMaxPair_mem
    {s M : ℕ} (Good : Finset ℕ) (w : ℕ → ℕ) (hs : 0 < s)
    (k : Fin (2 * s - 1)) :
    hybridIntervalMaxPair s M Good w hs k ∈ intervalAntidiagonalPairs s k.1 :=
  (Classical.choose_spec (Finset.exists_max_image
    (intervalAntidiagonalPairs s k.1)
    (fun p => hybridPairWeight M Good w p.1 p.2)
    (intervalAntidiagonalPairs_nonempty hs k.2))).1

lemma hybridIntervalMaxPair_realizes
    {s M : ℕ} (Good : Finset ℕ) (w : ℕ → ℕ) (hs : 0 < s)
    (k : Fin (2 * s - 1)) :
    hybridPairWeight M Good w
        (hybridIntervalMaxPair s M Good w hs k).1
        (hybridIntervalMaxPair s M Good w hs k).2 =
      hybridIntervalDiagonalMax s M Good w k.1 := by
  unfold hybridIntervalDiagonalMax
  apply le_antisymm
  · exact Finset.le_sup
      (s := intervalAntidiagonalPairs s k.1)
      (f := fun p => hybridPairWeight M Good w p.1 p.2)
      (b := hybridIntervalMaxPair s M Good w hs k)
      (hybridIntervalMaxPair_mem Good w hs k)
  · apply Finset.sup_le
    intro p hp
    exact (Classical.choose_spec (Finset.exists_max_image
      (intervalAntidiagonalPairs s k.1)
      (fun p => hybridPairWeight M Good w p.1 p.2)
      (intervalAntidiagonalPairs_nonempty hs k.2))).2 p hp

theorem all_fibers_contained_of_interval_support_maximal_dense
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) {s base top : ℕ}
    (hs : 6 ≤ s) (hsupport : firstCoordinateSet X = Finset.range s)
    (hsmall : 2 * (X + X).card < 5 * X.card)
    (hbase : base ∈ firstCoordinateSet X) (htop : top ∈ firstCoordinateSet X)
    (hbaseTop : (coordinateFiber X base).card < (coordinateFiber X top).card)
    (htopMax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X top).card)
    {H : AddSubgroup (ZMod d)}
    (hbaseCos : ContainedInAddCoset H (coordinateFiber X base))
    (hGoodMax : ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a) →
        (coordinateFiber X a).card ≤ (coordinateFiber X base).card)
    (hpairHigh : ∀ i ∈ firstCoordinateSet X, ∀ j ∈ firstCoordinateSet X,
      (coordinateFiber X base).card <
        max (coordinateFiber X i).card (coordinateFiber X j).card →
      pairWeight (coordinateFiber X i).card (coordinateFiber X j).card ≤
        2 * (coordinateFiber X i + coordinateFiber X j).card) :
    ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a) := by
  classical
  let w : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let M := w base
  let K := w top
  let Good := (Finset.range s).filter fun a =>
    ContainedInAddCoset H (coordinateFiber X a)
  let Bad := Finset.range s \ Good
  have hbaseRange : base ∈ Finset.range s := by simpa [← hsupport] using hbase
  have htopRange : top ∈ Finset.range s := by simpa [← hsupport] using htop
  have hGoodSub : Good ⊆ Finset.range s := Finset.filter_subset _ _
  have hBadSub : Bad ⊆ Finset.range s := Finset.sdiff_subset
  have hbaseGood : base ∈ Good :=
    Finset.mem_filter.mpr ⟨hbaseRange, hbaseCos⟩
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
  have hMK : M < K := hbaseTop
  have hmax : ∀ i ∈ Finset.range s, w i ≤ K := by
    intro i hi
    exact htopMax i (by simpa [hsupport] using hi)
  have hGoodMax' : ∀ i ∈ Good, w i ≤ M := by
    intro i hi
    exact hGoodMax i (by simpa [hsupport] using hGoodSub hi) (hGood i hi)
  have hweight := hybrid_interval_diagonal_weight_bound
    (s := s) (M := M) (K := K) (Good := Good) (w := w)
    (base := base) (top := top) hs hGoodSub hbaseGood rfl htopRange rfl
    hMK hmax hGoodMax' hBadNe
  let pair : Fin (2 * s - 1) → ℕ × ℕ :=
    hybridIntervalMaxPair s M Good w (by omega)
  let P : Finset (ℕ × ℕ) := Finset.univ.image pair
  have hpairMem : ∀ k, pair k ∈ intervalAntidiagonalPairs s k.1 := by
    intro k
    exact hybridIntervalMaxPair_mem Good w (by omega) k
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
      hybridPairWeight M Good w (pair k).1 (pair k).2 ≤
        2 * (coordinateFiber X (pair k).1 +
          coordinateFiber X (pair k).2).card := by
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
    change hybridPairWeight M Good w i j ≤
      2 * (coordinateFiber X i + coordinateFiber X j).card
    unfold hybridPairWeight
    apply max_le
    · apply Nat.mul_le_mul_left 2
      by_cases hiG : i ∈ Good <;> by_cases hjG : j ∈ Good
      · simp only [relativeCosetPairHalf, if_pos hiG, if_pos hjG]
        exact max_le (Finset.card_le_card_add_right hjNe)
          (Finset.card_le_card_add_left hiNe)
      · rw [relativeCosetPairHalf_of_good_bad hiG hjG]
        apply max_le
        · exact two_mul_card_le_add_of_coset_and_not_coset hiNe hjNe
            (hGood i hiG) (hBadNot j (Finset.mem_sdiff.mpr
              ⟨Finset.mem_range.mpr hjb, hjG⟩))
        · exact Finset.card_le_card_add_left hiNe
      · have htwo := two_mul_card_le_add_of_coset_and_not_coset
            hjNe hiNe (hGood j hjG) (hBadNot i (Finset.mem_sdiff.mpr
              ⟨Finset.mem_range.mpr hib, hiG⟩))
        simp only [relativeCosetPairHalf, if_neg hiG, if_pos hjG]
        apply max_le
        · exact Finset.card_le_card_add_right hjNe
        · simpa [add_comm] using htwo
      · simp only [relativeCosetPairHalf, if_neg hiG, if_neg hjG]
        exact max_le (Finset.card_le_card_add_right hjNe)
          (Finset.card_le_card_add_left hiNe)
    · split_ifs with hhigh
      · exact hpairHigh i hiX j hjX hhigh
      · omega
  have hdiagToFiber :
      (∑ k : Fin (2 * s - 1),
          hybridIntervalDiagonalMax s M Good w k.1) ≤
        ∑ k : Fin (2 * s - 1),
          2 * (coordinateFiber X (pair k).1 +
            coordinateFiber X (pair k).2).card := by
    apply Finset.sum_le_sum
    intro k hk
    rw [← hybridIntervalMaxPair_realizes Good w (by omega) k]
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
        hybridIntervalDiagonalMax s M Good w k) ≤ 2 * (X + X).card := by
    rw [← Fin.sum_univ_eq_sum_range]
    rw [← Finset.mul_sum] at hdiagToFiber
    rw [hfinToP] at hdiagToFiber
    exact hdiagToFiber.trans (Nat.mul_le_mul_left 2 hPsum)
  have hXcard : X.card = ∑ i ∈ Finset.range s, w i := by
    rw [card_eq_sum_card_coordinateFiber X, hsupport]
  have : 5 * X.card ≤ 2 * (X + X).card := by
    rw [hXcard]
    exact hweight.trans hdiag
  omega

/-- In the interval-support regime, maximality among all dense fibres turns
the local Deshouillers--Freiman alternative into a single subgroup which
contains every fibre. -/
theorem exists_common_dense_coset_of_interval_support
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) {s : ℕ}
    (hs : 6 ≤ s)
    (hsupport : firstCoordinateSet X = Finset.range s)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ base ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X base) ∧
        2 * Nat.card H < 3 * (coordinateFiber X base).card ∧
        ∀ a ∈ firstCoordinateSet X,
          ContainedInAddCoset H (coordinateFiber X a) := by
  classical
  let A := firstCoordinateSet X
  let F : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let Dense := A.filter fun a => ∃ H : AddSubgroup (ZMod d),
    ContainedInAddCoset H (coordinateFiber X a) ∧
      2 * Nat.card H < 3 * (coordinateFiber X a).card
  obtain ⟨a, ha, H₀, haCos, hH₀card⟩ :=
    exists_dense_fiber_coset_of_interval_support X (by omega) hsupport hsmall
  have haDense : a ∈ Dense :=
    Finset.mem_filter.mpr ⟨ha, ⟨H₀, haCos, hH₀card⟩⟩
  have hDenseNe : Dense.Nonempty := ⟨a, haDense⟩
  obtain ⟨base, hbaseDense, hbaseMaxDense⟩ :=
    Finset.exists_max_image Dense F hDenseNe
  have hbase : base ∈ firstCoordinateSet X :=
    (Finset.mem_filter.mp hbaseDense).1
  obtain ⟨H, hbaseCos, hHcard⟩ :=
    (Finset.mem_filter.mp hbaseDense).2
  have hANe : (firstCoordinateSet X).Nonempty := ⟨base, hbase⟩
  obtain ⟨top, htop, htopMax⟩ := Finset.exists_max_image
    (firstCoordinateSet X) F hANe
  have hbaseLeTop : F base ≤ F top := htopMax base hbase
  by_cases hEq : F base = F top
  · have hbaseMax : ∀ z ∈ firstCoordinateSet X, F z ≤ F base := by
      intro z hz
      exact (htopMax z hz).trans_eq hEq.symm
    refine ⟨base, hbase, H, hbaseCos, hHcard, ?_⟩
    exact all_fibers_contained_of_interval_support_largest X hs hsupport
      hsmall hbase hbaseMax hbaseCos
  · have hbaseTop : F base < F top := by omega
    have hGoodMax : ∀ z ∈ firstCoordinateSet X,
        ContainedInAddCoset H (coordinateFiber X z) → F z ≤ F base := by
      intro z hz hzCos
      by_contra hzNot
      have hbaseZ : F base < F z := Nat.lt_of_not_ge hzNot
      have hzDense : z ∈ Dense := Finset.mem_filter.mpr ⟨hz, ⟨H, hzCos, by
        have := hHcard
        dsimp only [F] at hbaseZ ⊢
        omega⟩⟩
      exact (Nat.not_lt_of_ge (hbaseMaxDense z hzDense)) hbaseZ
    have hpairHigh : ∀ i ∈ firstCoordinateSet X,
        ∀ j ∈ firstCoordinateSet X,
          F base < max (F i) (F j) →
            pairWeight (F i) (F j) ≤
              2 * (coordinateFiber X i + coordinateFiber X j).card := by
      intro i hi j hj hhigh
      have hiNe := coordinateFiber_nonempty_iff.mpr hi
      have hjNe := coordinateFiber_nonempty_iff.mpr hj
      rcases le_total (F j) (F i) with hji | hij
      · rcases small_coset_or_largestPairWeight_le hiNe hjNe hji with
          hdense | hsum
        · obtain ⟨H', hiCos, hH'card⟩ := hdense
          have hiDense : i ∈ Dense :=
            Finset.mem_filter.mpr ⟨hi, ⟨H', hiCos, by simpa [F] using hH'card⟩⟩
          have hiLe := hbaseMaxDense i hiDense
          rw [max_eq_left hji] at hhigh
          omega
        · simpa [pairWeight, max_eq_left hji, min_eq_right hji, F] using hsum
      · rcases small_coset_or_largestPairWeight_le hjNe hiNe hij with
          hdense | hsum
        · obtain ⟨H', hjCos, hH'card⟩ := hdense
          have hjDense : j ∈ Dense :=
            Finset.mem_filter.mpr ⟨hj, ⟨H', hjCos, by simpa [F] using hH'card⟩⟩
          have hjLe := hbaseMaxDense j hjDense
          rw [max_eq_right hij] at hhigh
          omega
        · simpa [pairWeight, max_eq_right hij, min_eq_left hij, F,
            add_comm] using hsum
    refine ⟨base, hbase, H, hbaseCos, hHcard, ?_⟩
    apply all_fibers_contained_of_interval_support_maximal_dense X hs
      hsupport hsmall hbase htop
    · simpa [F] using hbaseTop
    · intro z hz
      simpa [F] using htopMax z hz
    · exact hbaseCos
    · intro z hz hzCos
      simpa [F] using hGoodMax z hz hzCos
    · intro i hi j hj hhigh
      simpa [F] using hpairHigh i hi j hj (by simpa [F] using hhigh)

end Erdos360
