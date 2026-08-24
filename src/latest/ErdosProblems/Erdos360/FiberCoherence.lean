import ErdosProblems.Erdos360.FiberIntervalCoherence

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

def supportAntidiagonalPairs (A : Finset ℕ) (k : ℕ) : Finset (ℕ × ℕ) :=
  (A.product A).filter fun p => p.1 + p.2 = k

lemma mem_supportAntidiagonalPairs {A : Finset ℕ} {k : ℕ} {p : ℕ × ℕ} :
    p ∈ supportAntidiagonalPairs A k ↔
      p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = k := by
  simp [supportAntidiagonalPairs, and_assoc]

lemma supportAntidiagonalPairs_nonempty {A : Finset ℕ} {k : ℕ}
    (hk : k ∈ A + A) : (supportAntidiagonalPairs A k).Nonempty := by
  obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp hk
  exact ⟨(i, j), mem_supportAntidiagonalPairs.mpr ⟨hi, hj, rfl⟩⟩

def hybridSupportDiagonalMax (A : Finset ℕ) (M : ℕ) (Good : Finset ℕ)
    (w : ℕ → ℕ) (k : ℕ) : ℕ :=
  (supportAntidiagonalPairs A k).sup fun p =>
    hybridPairWeight M Good w p.1 p.2

lemma hybridPairWeight_le_support_diagonal
    {A : Finset ℕ} {M : ℕ} (Good : Finset ℕ) (w : ℕ → ℕ)
    {i j : ℕ} (hi : i ∈ A) (hj : j ∈ A) :
    hybridPairWeight M Good w i j ≤
      hybridSupportDiagonalMax A M Good w (i + j) := by
  unfold hybridSupportDiagonalMax
  apply Finset.le_sup (s := supportAntidiagonalPairs A (i + j))
    (f := fun p => hybridPairWeight M Good w p.1 p.2) (b := (i, j))
  exact mem_supportAntidiagonalPairs.mpr ⟨hi, hj, rfl⟩

lemma hybridSupportDiagonalMax_le
    {A : Finset ℕ} {M K : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ}
    (hmax : ∀ i ∈ A, w i ≤ K) (k : ℕ) :
    hybridSupportDiagonalMax A M Good w k ≤ 4 * K := by
  apply Finset.sup_le
  intro p hp
  have hp' := mem_supportAntidiagonalPairs.mp hp
  exact hybridPairWeight_le (hmax p.1 hp'.1) (hmax p.2 hp'.2.1)

lemma support_baseline_threshold_bound
    {A : Finset ℕ} {M K q : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ}
    (hA : A.Nonempty) (hq : q < 2 * K) (hbase : ∃ i ∈ A, w i = K) :
    A.card + (A.filter (fun i => q < 2 * w i)).card - 1 ≤
      ((A + A).filter fun k =>
        q < hybridSupportDiagonalMax A M Good w k).card := by
  classical
  let U := A.filter fun i => q < 2 * w i
  have hUne : U.Nonempty := by
    obtain ⟨i, hi, hiw⟩ := hbase
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, by omega⟩⟩
  have hadd := cauchy_davenport_add_of_linearOrder_isCancelAdd hUne hA
  have hsub : U + A ⊆ (A + A).filter (fun k =>
      q < hybridSupportDiagonalMax A M Good w k) := by
    intro k hk
    obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp hk
    have hi' := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_add.mpr ⟨i, hi'.1, j, hj, rfl⟩
    · have hp := hybridPairWeight_le_support_diagonal
          (M := M) Good w hi'.1 hj
      exact hi'.2.trans_le ((Nat.mul_le_mul_left 2 (le_max_left _ _)).trans
        ((two_max_le_hybridPairWeight M Good w i j).trans hp))
  simpa [U, add_comm] using hadd.trans (Finset.card_le_card hsub)

lemma support_cross_bonus_threshold_bound
    {A : Finset ℕ} {M K u : ℕ} {Good Bad : Finset ℕ}
    {w : ℕ → ℕ} {base : ℕ}
    (hGoodSub : Good ⊆ A) (hBadSub : Bad ⊆ A)
    (hdisj : Disjoint Good Bad) (hBad : Bad.Nonempty)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hu : u < hybridG K M) :
    (Good.filter (fun i => 2 * K + u < 4 * w i)).card + Bad.card - 1 ≤
      ((A + A).filter fun k =>
        2 * K + u < hybridSupportDiagonalMax A M Good w k).card := by
  classical
  let U := Good.filter fun i => 2 * K + u < 4 * w i
  have hUne : U.Nonempty := by
    refine ⟨base, Finset.mem_filter.mpr ⟨hbase, ?_⟩⟩
    rw [hbasew]
    simp only [hybridG] at hu
    omega
  have hadd := cauchy_davenport_add_of_linearOrder_isCancelAdd hUne hBad
  have hsub : U + Bad ⊆ (A + A).filter (fun k =>
      2 * K + u < hybridSupportDiagonalMax A M Good w k) := by
    intro k hk
    obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp hk
    have hi' := Finset.mem_filter.mp hi
    have hiA := hGoodSub hi'.1
    have hjA := hBadSub hj
    have hjNotGood : j ∉ Good := fun hjG =>
      Finset.disjoint_left.mp hdisj hjG hj
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_add.mpr ⟨i, hiA, j, hjA, rfl⟩
    · have hp := hybridPairWeight_le_support_diagonal
          (M := M) Good w hiA hjA
      exact hi'.2.trans_le
        ((four_good_left_le_hybridPairWeight hi'.1 hjNotGood).trans hp)
  simpa [U] using hadd.trans (Finset.card_le_card hsub)

lemma support_top_star_threshold_bound
    {A : Finset ℕ} {M K u : ℕ} {Good : Finset ℕ}
    {w : ℕ → ℕ} {top : ℕ}
    (hMK : M < K) (htop : top ∈ A) (htopw : w top = K) (hu : u < K) :
    (A.filter (fun i => 2 * K + u < pairWeight K (w i))).card ≤
      ((A + A).filter fun k =>
        2 * K + u < hybridSupportDiagonalMax A M Good w k).card := by
  classical
  let U := A.filter fun i => 2 * K + u < pairWeight K (w i)
  have hUne : U.Nonempty := by
    refine ⟨top, Finset.mem_filter.mpr ⟨htop, ?_⟩⟩
    rw [htopw, pairWeight_self]
    omega
  have hsingle : ({top} : Finset ℕ).Nonempty := Finset.singleton_nonempty top
  have hadd := cauchy_davenport_add_of_linearOrder_isCancelAdd hsingle hUne
  have hsub : ({top} : Finset ℕ) + U ⊆ (A + A).filter (fun k =>
      2 * K + u < hybridSupportDiagonalMax A M Good w k) := by
    intro k hk
    obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp hk
    have hiTop : i = top := by simpa using hi
    subst i
    have hj' := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_add.mpr ⟨top, htop, j, hj'.1, rfl⟩
    · have hp := hybridPairWeight_le_support_diagonal
          (M := M) Good w htop hj'.1
      have hhigh : M < max (w top) (w j) := by rw [htopw]; omega
      have hpw := pairWeight_le_hybridPairWeight (Good := Good) hhigh
      rw [htopw] at hpw
      exact hj'.2.trans_le (hpw.trans hp)
  have hc := hadd.trans (Finset.card_le_card hsub)
  simpa [U] using hc

lemma support_high_bonus_threshold_bound
    {A : Finset ℕ} {M K u : ℕ} {Good : Finset ℕ}
    {w : ℕ → ℕ} {top : ℕ}
    (hGoodSub : Good ⊆ A) (hGoodMax : ∀ i ∈ Good, w i ≤ M)
    (htop : top ∈ A) (htopw : w top = K)
    (hMK : M < K) (hu : u < K) :
    (Good.filter (fun i => 2 * K + u < 4 * w i)).card +
        2 * (A.filter (fun i => M < w i ∧ 2 * K + u < 3 * w i)).card - 1 ≤
      ((A + A).filter fun k =>
        2 * K + u < hybridSupportDiagonalMax A M Good w k).card := by
  classical
  let GU := Good.filter fun i => 2 * K + u < 4 * w i
  let AU := A.filter fun i => M < w i ∧ 2 * K + u < 3 * w i
  let V := GU ∪ AU
  have htopAU : top ∈ AU := by
    exact Finset.mem_filter.mpr ⟨htop, by rw [htopw]; exact ⟨hMK, by omega⟩⟩
  have hAUne : AU.Nonempty := ⟨top, htopAU⟩
  have hVne : V.Nonempty := ⟨top, Finset.mem_union_right _ htopAU⟩
  have hdisj : Disjoint GU AU := by
    rw [Finset.disjoint_left]
    intro i hiG hiA
    have hiG' := Finset.mem_filter.mp hiG
    have hiA' := Finset.mem_filter.mp hiA
    have := hGoodMax i hiG'.1
    omega
  have hadd := cauchy_davenport_add_of_linearOrder_isCancelAdd hVne hAUne
  have hsub : V + AU ⊆ (A + A).filter (fun k =>
      2 * K + u < hybridSupportDiagonalMax A M Good w k) := by
    intro k hk
    obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp hk
    have hj' := Finset.mem_filter.mp hj
    have hiUnion := Finset.mem_union.mp hi
    have hiA : i ∈ A := by
      rcases hiUnion with hiG | hiAU
      · exact hGoodSub (Finset.mem_filter.mp hiG).1
      · exact (Finset.mem_filter.mp hiAU).1
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_add.mpr ⟨i, hiA, j, hj'.1, rfl⟩
    · have hp := hybridPairWeight_le_support_diagonal
          (M := M) Good w hiA hj'.1
      rcases hiUnion with hiG | hiAU
      · have hiG' := Finset.mem_filter.mp hiG
        have hjNotGood : j ∉ Good := by
          intro hjG
          have := hGoodMax j hjG
          omega
        exact hiG'.2.trans_le
          ((four_good_left_le_hybridPairWeight hiG'.1 hjNotGood).trans hp)
      · have hiAU' := Finset.mem_filter.mp hiAU
        have hthreshold : 2 * K + u < pairWeight (w i) (w j) := by
          have hthree := three_min_le_pairWeight (w i) (w j)
          have hmin : 2 * K + u < 3 * min (w i) (w j) := by
            simp only [min_def]
            split_ifs <;> omega
          exact hmin.trans_le hthree
        have hhigh : M < max (w i) (w j) :=
          hj'.2.1.trans_le (le_max_right _ _)
        exact hthreshold.trans_le
          ((pairWeight_le_hybridPairWeight (Good := Good) hhigh).trans hp)
  have hc := hadd.trans (Finset.card_le_card hsub)
  have hVcard : V.card = GU.card + AU.card := Finset.card_union_of_disjoint hdisj
  rw [hVcard] at hc
  dsimp only [GU, AU, V] at hc ⊢
  omega

lemma support_baseline_layer_sum_lower
    {A : Finset ℕ} {M K : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ}
    (hA : A.Nonempty) (hmax : ∀ i ∈ A, w i ≤ K)
    (hbase : ∃ i ∈ A, w i = K) :
    2 * ((∑ i ∈ A, w i) + (A.card - 1) * K) ≤
      ∑ q ∈ Finset.range (2 * K),
        ((A + A).filter fun k =>
          q < hybridSupportDiagonalMax A M Good w k).card := by
  classical
  have hpoint : ∀ q ∈ Finset.range (2 * K),
      A.card + (A.filter (fun i => q < 2 * w i)).card - 1 ≤
        ((A + A).filter fun k =>
          q < hybridSupportDiagonalMax A M Good w k).card := by
    intro q hq
    exact support_baseline_threshold_bound hA (Finset.mem_range.mp hq) hbase
  have hsum := Finset.sum_le_sum hpoint
  have hweights :
      (∑ q ∈ Finset.range (2 * K),
        (A.filter (fun i => q < 2 * w i)).card) =
        2 * ∑ i ∈ A, w i := by
    have heq := sum_card_filter_lt_eq_sum A (fun i => 2 * w i) (2 * K) (by
      intro i hi
      exact Nat.mul_le_mul_left 2 (hmax i hi))
    simpa [Finset.mul_sum] using heq
  have heval :
      (∑ q ∈ Finset.range (2 * K),
        (A.card + (A.filter (fun i => q < 2 * w i)).card - 1)) =
        2 * ((∑ i ∈ A, w i) + (A.card - 1) * K) := by
    have hterm : ∀ q ∈ Finset.range (2 * K),
        A.card + (A.filter (fun i => q < 2 * w i)).card - 1 =
          (A.filter (fun i => q < 2 * w i)).card + (A.card - 1) := by
      intro q hq
      have : 1 ≤ A.card := Finset.card_pos.mpr hA
      omega
    calc
      _ = ∑ q ∈ Finset.range (2 * K),
          ((A.filter (fun i => q < 2 * w i)).card + (A.card - 1)) :=
            Finset.sum_congr rfl hterm
      _ = 2 * ∑ i ∈ A, w i + (2 * K) * (A.card - 1) := by
        rw [Finset.sum_add_distrib, hweights]
        simp
      _ = _ := by ring
  rw [heval] at hsum
  exact hsum

lemma support_cross_bonus_layer_sum_lower
    {A : Finset ℕ} {M K : ℕ} {Good Bad : Finset ℕ}
    {w : ℕ → ℕ} {base : ℕ}
    (hGoodSub : Good ⊆ A) (hBadSub : Bad ⊆ A)
    (hdisj : Disjoint Good Bad) (hBad : Bad.Nonempty)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M) (hMK : M ≤ K) :
    (∑ i ∈ Good, hybridG K (w i)) +
        (Bad.card - 1) * hybridG K M ≤
      ∑ u ∈ Finset.range (2 * K),
        ((A + A).filter fun k =>
          2 * K + u < hybridSupportDiagonalMax A M Good w k).card := by
  classical
  let gm := hybridG K M
  have hgm : gm ≤ 2 * K := hybridG_le_two_mul hMK
  have hpoint : ∀ u ∈ Finset.range gm,
      (Good.filter (fun i => 2 * K + u < 4 * w i)).card + Bad.card - 1 ≤
        ((A + A).filter fun k =>
          2 * K + u < hybridSupportDiagonalMax A M Good w k).card := by
    intro u hu
    exact support_cross_bonus_threshold_bound hGoodSub hBadSub hdisj hBad
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
      _ = _ := sum_card_filter_lt_eq_sum Good
        (fun i => hybridG K (w i)) gm hgBound
  have hleftEval :
      (∑ u ∈ Finset.range gm,
        ((Good.filter (fun i => 2 * K + u < 4 * w i)).card +
          Bad.card - 1)) =
        (∑ i ∈ Good, hybridG K (w i)) + (Bad.card - 1) * gm := by
    have hBadPos : 1 ≤ Bad.card := Finset.card_pos.mpr hBad
    have hterm : ∀ u ∈ Finset.range gm,
        (Good.filter (fun i => 2 * K + u < 4 * w i)).card + Bad.card - 1 =
          (Good.filter (fun i => 2 * K + u < 4 * w i)).card +
            (Bad.card - 1) := by intros; omega
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
  exact hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (by
    intro i hi hin
    positivity))

lemma support_top_star_layer_sum_lower
    {A : Finset ℕ} {M K : ℕ} {Good : Finset ℕ}
    {w : ℕ → ℕ} {top : ℕ}
    (hMK : M < K) (htop : top ∈ A) (htopw : w top = K)
    (hmax : ∀ i ∈ A, w i ≤ K) :
    (∑ i ∈ A, hybridT K (w i)) ≤
      ∑ u ∈ Finset.range (2 * K),
        ((A + A).filter fun k =>
          2 * K + u < hybridSupportDiagonalMax A M Good w k).card := by
  classical
  have hpoint : ∀ u ∈ Finset.range K,
      (A.filter (fun i => 2 * K + u < pairWeight K (w i))).card ≤
        ((A + A).filter fun k =>
          2 * K + u < hybridSupportDiagonalMax A M Good w k).card := by
    intro u hu
    exact support_top_star_threshold_bound hMK htop htopw
      (Finset.mem_range.mp hu)
  have hsum := Finset.sum_le_sum hpoint
  have hfilter : ∀ u ∈ Finset.range K,
      A.filter (fun i => 2 * K + u < pairWeight K (w i)) =
        A.filter (fun i => u < hybridT K (w i)) := by
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
  have hbound : ∀ i ∈ A, hybridT K (w i) ≤ K := by
    intro i hi
    exact hybridT_le (hmax i hi)
  have heval :
      (∑ u ∈ Finset.range K,
        (A.filter (fun i => 2 * K + u < pairWeight K (w i))).card) =
        ∑ i ∈ A, hybridT K (w i) := by
    calc
      _ = ∑ u ∈ Finset.range K,
          (A.filter (fun i => u < hybridT K (w i))).card := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hfilter u hu]
      _ = _ := sum_card_filter_lt_eq_sum A (fun i => hybridT K (w i)) K hbound
  rw [heval] at hsum
  have hsub : Finset.range K ⊆ Finset.range (2 * K) := by
    intro u hu
    exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hu; omega)
  exact hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (by
    intro i hi hin
    positivity))

lemma support_high_bonus_layer_sum_lower
    {A : Finset ℕ} {M K : ℕ} {Good Bad : Finset ℕ}
    {w : ℕ → ℕ} {base top : ℕ}
    (hGoodSub : Good ⊆ A) (hBadSub : Bad ⊆ A)
    (hdisj : Disjoint Good Bad) (hBad : Bad.Nonempty)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M)
    (htop : top ∈ A) (htopw : w top = K)
    (hMK : M < K) (hmax : ∀ i ∈ A, w i ≤ K) :
    (∑ i ∈ Good, hybridG K (w i)) +
        (Bad.card - 1) * (hybridG K M - K) +
        (2 * (∑ i ∈ A.filter (fun i => M < w i),
          hybridA K (w i)) - K) ≤
      ∑ u ∈ Finset.range (2 * K),
        ((A + A).filter fun k =>
          2 * K + u < hybridSupportDiagonalMax A M Good w k).card := by
  classical
  let gm := hybridG K M
  let tail := gm - K
  let AS := A.filter fun i => M < w i
  let F : ℕ → ℕ := fun u =>
    ((A + A).filter fun k =>
      2 * K + u < hybridSupportDiagonalMax A M Good w k).card
  have hgm : gm ≤ 2 * K := hybridG_le_two_mul hMK.le
  have htail : tail ≤ K := by dsimp only [tail]; omega
  have htopAS : top ∈ AS :=
    Finset.mem_filter.mpr ⟨htop, by rw [htopw]; exact hMK⟩
  have hmainPoint : ∀ u ∈ Finset.range K,
      (Good.filter (fun i => 2 * K + u < 4 * w i)).card +
          2 * (A.filter (fun i =>
            M < w i ∧ 2 * K + u < 3 * w i)).card - 1 ≤ F u := by
    intro u hu
    exact support_high_bonus_threshold_bound hGoodSub hGoodMax htop htopw hMK
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
      A.filter (fun i => M < w i ∧ 2 * K + u < 3 * w i) =
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
        (A.filter (fun i =>
          M < w i ∧ 2 * K + u < 3 * w i)).card) =
        ∑ i ∈ AS, hybridA K (w i) := by
    calc
      _ = ∑ u ∈ Finset.range K,
          (AS.filter (fun i => u < hybridA K (w i))).card := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hAFilter u hu]
      _ = _ := sum_card_filter_lt_eq_sum AS
        (fun i => hybridA K (w i)) K haBound
  have hmainEval :
      (∑ u ∈ Finset.range K,
        ((Good.filter (fun i => 2 * K + u < 4 * w i)).card +
          2 * (A.filter (fun i =>
            M < w i ∧ 2 * K + u < 3 * w i)).card - 1)) =
        (∑ i ∈ Good, min (hybridG K (w i)) K) +
          (2 * (∑ i ∈ AS, hybridA K (w i)) - K) := by
    have hANe : ∀ u ∈ Finset.range K,
        1 ≤ (A.filter (fun i =>
          M < w i ∧ 2 * K + u < 3 * w i)).card := by
      intro u hu
      apply Finset.card_pos.mpr
      refine ⟨top, Finset.mem_filter.mpr ⟨htop, ?_⟩⟩
      rw [htopw]
      exact ⟨hMK, by have := Finset.mem_range.mp hu; omega⟩
    have hterm : ∀ u ∈ Finset.range K,
        (Good.filter (fun i => 2 * K + u < 4 * w i)).card +
            2 * (A.filter (fun i =>
              M < w i ∧ 2 * K + u < 3 * w i)).card - 1 =
          (Good.filter (fun i => 2 * K + u < 4 * w i)).card +
            (2 * (A.filter (fun i =>
              M < w i ∧ 2 * K + u < 3 * w i)).card - 1) := by
      intro u hu
      have := hANe u hu
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hgTrunc]
    have htwice :
        (∑ u ∈ Finset.range K,
          (2 * (A.filter (fun i =>
            M < w i ∧ 2 * K + u < 3 * w i)).card - 1)) =
          2 * (∑ i ∈ AS, hybridA K (w i)) - K := by
      have hh := sum_two_mul_sub_one (Finset.range K)
        (fun u => (A.filter (fun i =>
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
    exact support_cross_bonus_threshold_bound hGoodSub hBadSub hdisj hBad
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
        (Good.filter (fun i => 2 * K + (K + v) < 4 * w i)).card +
            Bad.card - 1 =
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
      exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hv; omega)
  rw [htailImage] at hbonusToTwo
  rw [← Finset.sum_union hdisjRange] at hbonusToTwo
  have hfull : (∑ u ∈ Finset.range K ∪ TailRange, F u) ≤
      ∑ u ∈ Finset.range (2 * K), F u :=
    Finset.sum_le_sum_of_subset_of_nonneg hQsub (by
      intro i hi hin
      exact Nat.zero_le _)
  dsimp only [F, tail, gm, AS] at hbonusToTwo ⊢
  exact hbonusToTwo.trans hfull

lemma support_hybrid_layer_sum_split
    {A : Finset ℕ} {M K : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ}
    (hmax : ∀ i ∈ A, w i ≤ K) :
    (∑ q ∈ Finset.range (2 * K),
        ((A + A).filter fun k =>
          q < hybridSupportDiagonalMax A M Good w k).card) +
      (∑ u ∈ Finset.range (2 * K),
        ((A + A).filter fun k =>
          2 * K + u < hybridSupportDiagonalMax A M Good w k).card) =
      ∑ k ∈ A + A, hybridSupportDiagonalMax A M Good w k := by
  classical
  let L := hybridSupportDiagonalMax A M Good w
  have hLmax : ∀ k ∈ A + A, L k ≤ 4 * K := by
    intro k hk
    exact hybridSupportDiagonalMax_le hmax k
  have hsumL := sum_card_filter_lt_eq_sum (A + A) L (4 * K) hLmax
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

theorem hybrid_support_diagonal_weight_bound
    {A : Finset ℕ} {M K : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ}
    {base top : ℕ}
    (hAcard : 6 ≤ A.card) (hGoodSub : Good ⊆ A)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (htop : top ∈ A) (htopw : w top = K)
    (hMK : M < K) (hmax : ∀ i ∈ A, w i ≤ K)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M)
    (hBad : (A \ Good).Nonempty) :
    5 * (∑ i ∈ A, w i) ≤
      ∑ k ∈ A + A, hybridSupportDiagonalMax A M Good w k := by
  classical
  let Bad := A \ Good
  let G := ∑ i ∈ Good, hybridG K (w i)
  let AH := ∑ i ∈ A.filter (fun i => M < w i), hybridA K (w i)
  let T := ∑ i ∈ A, hybridT K (w i)
  let C := G + (Bad.card - 1) * hybridG K M
  let AA := G + (Bad.card - 1) * (hybridG K M - K) + (2 * AH - K)
  let B := max C (max AA T)
  let LowSum := ∑ q ∈ Finset.range (2 * K),
    ((A + A).filter fun k =>
      q < hybridSupportDiagonalMax A M Good w k).card
  let HighSum := ∑ u ∈ Finset.range (2 * K),
    ((A + A).filter fun k =>
      2 * K + u < hybridSupportDiagonalMax A M Good w k).card
  have hBadSub : Bad ⊆ A := Finset.sdiff_subset
  have hdisj : Disjoint Good Bad := Finset.disjoint_sdiff
  have hANe : A.Nonempty := by
    exact ⟨top, htop⟩
  have htopBase : ∃ i ∈ A, w i = K := ⟨top, htop, htopw⟩
  have hlow : 2 * ((∑ i ∈ A, w i) + (A.card - 1) * K) ≤ LowSum := by
    exact support_baseline_layer_sum_lower (M := M) (Good := Good)
      hANe hmax htopBase
  have hcross : C ≤ HighSum := by
    dsimp only [C, G, Bad, HighSum]
    exact support_cross_bonus_layer_sum_lower hGoodSub hBadSub hdisj hBad
      hbase hbasew hGoodMax hMK.le
  have hhigh : AA ≤ HighSum := by
    dsimp only [AA, G, AH, Bad, HighSum]
    exact support_high_bonus_layer_sum_lower hGoodSub hBadSub hdisj hBad
      hbase hbasew hGoodMax htop htopw hMK hmax
  have hstar : T ≤ HighSum := by
    dsimp only [T, HighSum]
    exact support_top_star_layer_sum_lower hMK htop htopw hmax
  have hbonus : B ≤ HighSum := by
    dsimp only [B]
    exact max_le hcross (max_le hhigh hstar)
  have harith : 5 * (∑ i ∈ A, w i) ≤
      2 * ((∑ i ∈ A, w i) + (A.card - 1) * K) + B := by
    dsimp only [B, C, AA, G, AH, T, Bad]
    exact hybrid_three_branch_arithmetic A Good w hAcard hGoodSub
      (hGoodSub hbase) htop hbase hbasew htopw hMK hmax hGoodMax
  have htoSums : 5 * (∑ i ∈ A, w i) ≤ LowSum + HighSum := by
    exact harith.trans (Nat.add_le_add hlow hbonus)
  have hsplit := support_hybrid_layer_sum_split
    (A := A) (M := M) (Good := Good) hmax
  dsimp only [LowSum, HighSum] at htoSums
  rw [hsplit] at htoSums
  exact htoSums

noncomputable def hybridSupportMaxPair
    (A : Finset ℕ) (M : ℕ) (Good : Finset ℕ) (w : ℕ → ℕ)
    (k : {k // k ∈ A + A}) : ℕ × ℕ :=
  Classical.choose (Finset.exists_max_image (supportAntidiagonalPairs A k.1)
    (fun p => hybridPairWeight M Good w p.1 p.2)
    (supportAntidiagonalPairs_nonempty k.2))

lemma hybridSupportMaxPair_mem
    (A : Finset ℕ) (M : ℕ) (Good : Finset ℕ) (w : ℕ → ℕ)
    (k : {k // k ∈ A + A}) :
    hybridSupportMaxPair A M Good w k ∈ supportAntidiagonalPairs A k.1 :=
  (Classical.choose_spec (Finset.exists_max_image
    (supportAntidiagonalPairs A k.1)
    (fun p => hybridPairWeight M Good w p.1 p.2)
    (supportAntidiagonalPairs_nonempty k.2))).1

lemma hybridSupportMaxPair_realizes
    (A : Finset ℕ) (M : ℕ) (Good : Finset ℕ) (w : ℕ → ℕ)
    (k : {k // k ∈ A + A}) :
    hybridPairWeight M Good w
        (hybridSupportMaxPair A M Good w k).1
        (hybridSupportMaxPair A M Good w k).2 =
      hybridSupportDiagonalMax A M Good w k.1 := by
  unfold hybridSupportDiagonalMax
  apply le_antisymm
  · exact Finset.le_sup
      (s := supportAntidiagonalPairs A k.1)
      (f := fun p => hybridPairWeight M Good w p.1 p.2)
      (b := hybridSupportMaxPair A M Good w k)
      (hybridSupportMaxPair_mem A M Good w k)
  · apply Finset.sup_le
    intro p hp
    exact (Classical.choose_spec (Finset.exists_max_image
      (supportAntidiagonalPairs A k.1)
      (fun p => hybridPairWeight M Good w p.1 p.2)
      (supportAntidiagonalPairs_nonempty k.2))).2 p hp

theorem all_fibers_contained_of_support_maximal_dense
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) {base top : ℕ}
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hsmall : 2 * (X + X).card < 5 * X.card)
    (hbase : base ∈ firstCoordinateSet X)
    (htop : top ∈ firstCoordinateSet X)
    (hbaseTop : (coordinateFiber X base).card < (coordinateFiber X top).card)
    (htopMax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X top).card)
    {H : AddSubgroup (ZMod d)}
    (hbaseCos : ContainedInAddCoset H (coordinateFiber X base))
    (hGoodMax : ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a) →
        (coordinateFiber X a).card ≤ (coordinateFiber X base).card)
    (hpairHigh : ∀ i ∈ firstCoordinateSet X,
      ∀ j ∈ firstCoordinateSet X,
        (coordinateFiber X base).card <
          max (coordinateFiber X i).card (coordinateFiber X j).card →
        pairWeight (coordinateFiber X i).card (coordinateFiber X j).card ≤
          2 * (coordinateFiber X i + coordinateFiber X j).card) :
    ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a) := by
  classical
  let A := firstCoordinateSet X
  let w : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let M := w base
  let K := w top
  let Good := A.filter fun a =>
    ContainedInAddCoset H (coordinateFiber X a)
  let Bad := A \ Good
  have hGoodSub : Good ⊆ A := Finset.filter_subset _ _
  have hBadSub : Bad ⊆ A := Finset.sdiff_subset
  have hbaseGood : base ∈ Good :=
    Finset.mem_filter.mpr ⟨hbase, hbaseCos⟩
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
  have haBad : a ∈ Bad := Finset.mem_sdiff.mpr ⟨ha, by
    intro haGood
    exact haNot (hGood a haGood)⟩
  have hBadNe : Bad.Nonempty := ⟨a, haBad⟩
  have hMK : M < K := hbaseTop
  have hmax : ∀ i ∈ A, w i ≤ K := by
    intro i hi
    exact htopMax i hi
  have hGoodMax' : ∀ i ∈ Good, w i ≤ M := by
    intro i hi
    exact hGoodMax i (hGoodSub hi) (hGood i hi)
  have hweight := hybrid_support_diagonal_weight_bound
    (A := A) (M := M) (K := K) (Good := Good) (w := w)
    (base := base) (top := top) hAcard hGoodSub hbaseGood rfl htop rfl
    hMK hmax hGoodMax' hBadNe
  let pair : {k // k ∈ A + A} → ℕ × ℕ :=
    hybridSupportMaxPair A M Good w
  let P : Finset (ℕ × ℕ) := Finset.univ.image pair
  have hpairMem : ∀ k, pair k ∈ supportAntidiagonalPairs A k.1 := by
    intro k
    exact hybridSupportMaxPair_mem A M Good w k
  have hpairInA : ∀ k, (pair k).1 ∈ A ∧ (pair k).2 ∈ A := by
    intro k
    have hk := mem_supportAntidiagonalPairs.mp (hpairMem k)
    exact ⟨hk.1, hk.2.1⟩
  have hpairSum : ∀ k, (pair k).1 + (pair k).2 = k.1 := by
    intro k
    exact (mem_supportAntidiagonalPairs.mp (hpairMem k)).2.2
  have hpairInj : Function.Injective pair := by
    intro i j hij
    apply Subtype.ext
    rw [← hpairSum i, ← hpairSum j, hij]
  have hPmem : ∀ p ∈ P,
      p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X := by
    intro p hp
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
    exact hpairInA k
  have hPinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) P := by
    intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
    have hijVal : i.1 = j.1 := by simpa [hpairSum] using hpq
    have hij : i = j := Subtype.ext hijVal
    subst j
    rfl
  have hpoint : ∀ k : {k // k ∈ A + A},
      hybridPairWeight M Good w (pair k).1 (pair k).2 ≤
        2 * (coordinateFiber X (pair k).1 +
          coordinateFiber X (pair k).2).card := by
    intro k
    let i := (pair k).1
    let j := (pair k).2
    have hiA := (hpairInA k).1
    have hjA := (hpairInA k).2
    have hiNe := coordinateFiber_nonempty_iff.mpr hiA
    have hjNe := coordinateFiber_nonempty_iff.mpr hjA
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
            (hGood i hiG) (hBadNot j (Finset.mem_sdiff.mpr ⟨hjA, hjG⟩))
        · exact Finset.card_le_card_add_left hiNe
      · have htwo := two_mul_card_le_add_of_coset_and_not_coset
            hjNe hiNe (hGood j hjG)
              (hBadNot i (Finset.mem_sdiff.mpr ⟨hiA, hiG⟩))
        simp only [relativeCosetPairHalf, if_neg hiG, if_pos hjG]
        apply max_le
        · exact Finset.card_le_card_add_right hjNe
        · simpa [add_comm] using htwo
      · simp only [relativeCosetPairHalf, if_neg hiG, if_neg hjG]
        exact max_le (Finset.card_le_card_add_right hjNe)
          (Finset.card_le_card_add_left hiNe)
    · split_ifs with hhigh
      · exact hpairHigh i hiA j hjA hhigh
      · omega
  have hdiagToFiber :
      (∑ k : {k // k ∈ A + A},
          hybridSupportDiagonalMax A M Good w k.1) ≤
        ∑ k : {k // k ∈ A + A},
          2 * (coordinateFiber X (pair k).1 +
            coordinateFiber X (pair k).2).card := by
    apply Finset.sum_le_sum
    intro k hk
    rw [← hybridSupportMaxPair_realizes A M Good w k]
    exact hpoint k
  have hfinToP : (∑ k : {k // k ∈ A + A},
        (coordinateFiber X (pair k).1 + coordinateFiber X (pair k).2).card) =
      ∑ p ∈ P, (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    dsimp only [P]
    rw [Finset.sum_image hpairInj.injOn]
  have hPsum : (∑ p ∈ P,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card) ≤
      (X + X).card :=
    sum_card_coordinateFiber_add_le_card_add_of_pairSelection X P hPmem hPinj
  have hdiag : (∑ k ∈ A + A,
        hybridSupportDiagonalMax A M Good w k) ≤ 2 * (X + X).card := by
    rw [Finset.sum_subtype (p := fun k => k ∈ A + A)
      (s := A + A) (by simp)]
    rw [← Finset.mul_sum] at hdiagToFiber
    rw [hfinToP] at hdiagToFiber
    exact hdiagToFiber.trans (Nat.mul_le_mul_left 2 hPsum)
  have hXcard : X.card = ∑ i ∈ A, w i := by
    exact card_eq_sum_card_coordinateFiber X
  have : 5 * X.card ≤ 2 * (X + X).card := by
    rw [hXcard]
    exact hweight.trans hdiag
  omega

def relativeSupportDiagonalMax (A : Finset ℕ) (Good : Finset ℕ)
    (w : ℕ → ℕ) (k : ℕ) : ℕ :=
  (supportAntidiagonalPairs A k).sup fun p =>
    relativeCosetPairHalf Good w p.1 p.2

lemma relativePairHalf_le_support_diagonal
    {A : Finset ℕ} (Good : Finset ℕ) (w : ℕ → ℕ)
    {i j : ℕ} (hi : i ∈ A) (hj : j ∈ A) :
    relativeCosetPairHalf Good w i j ≤
      relativeSupportDiagonalMax A Good w (i + j) := by
  unfold relativeSupportDiagonalMax
  apply Finset.le_sup (s := supportAntidiagonalPairs A (i + j))
    (f := fun p => relativeCosetPairHalf Good w p.1 p.2) (b := (i, j))
  exact mem_supportAntidiagonalPairs.mpr ⟨hi, hj, rfl⟩

lemma relativeSupportDiagonalMax_le
    {A : Finset ℕ} {M : ℕ} {Good : Finset ℕ} {w : ℕ → ℕ}
    (hmax : ∀ i ∈ A, w i ≤ M) (k : ℕ) :
    relativeSupportDiagonalMax A Good w k ≤ 2 * M := by
  apply Finset.sup_le
  intro p hp
  have hp' := mem_supportAntidiagonalPairs.mp hp
  exact relativeCosetPairHalf_le (hmax p.1 hp'.1) (hmax p.2 hp'.2.1)

lemma relative_support_threshold_bounds
    {A : Finset ℕ} {M : ℕ} {w : ℕ → ℕ}
    {Good Bad : Finset ℕ} {base : ℕ}
    (hMpos : 0 < M) (hpart : Good ∪ Bad = A)
    (hdisj : Disjoint Good Bad)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hmax : ∀ i ∈ A, w i ≤ M) (hBad : Bad.Nonempty) :
    (∀ t ∈ Finset.range M,
      A.card + (A.filter (fun i => t < w i)).card - 1 ≤
        ((A + A).filter fun k =>
          t < relativeSupportDiagonalMax A Good w k).card) ∧
    (∀ u ∈ Finset.range M,
      (Good.filter (fun i => M + u < 2 * w i)).card + Bad.card - 1 ≤
        ((A + A).filter fun k =>
          M + u < relativeSupportDiagonalMax A Good w k).card) := by
  classical
  have hGoodSub : Good ⊆ A := by
    intro i hi
    rw [← hpart]
    exact Finset.mem_union_left _ hi
  have hBadSub : Bad ⊆ A := by
    intro i hi
    rw [← hpart]
    exact Finset.mem_union_right _ hi
  constructor
  · intro t ht
    let S := A.filter fun i => t < w i
    have hSne : S.Nonempty := by
      refine ⟨base, Finset.mem_filter.mpr ⟨hGoodSub hbase, ?_⟩⟩
      rw [hbasew]
      exact Finset.mem_range.mp ht
    have hANe : A.Nonempty := ⟨base, hGoodSub hbase⟩
    have haddLower := cauchy_davenport_add_of_linearOrder_isCancelAdd hSne hANe
    have hsub : S + A ⊆ (A + A).filter (fun k =>
        t < relativeSupportDiagonalMax A Good w k) := by
      intro k hk
      obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp hk
      have hi' := Finset.mem_filter.mp hi
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_add.mpr ⟨i, hi'.1, j, hj, rfl⟩
      · have hpair := relativePairHalf_le_support_diagonal Good w hi'.1 hj
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
    have haddLower := cauchy_davenport_add_of_linearOrder_isCancelAdd hTne hBad
    have hsub : T + Bad ⊆ (A + A).filter (fun k =>
        M + u < relativeSupportDiagonalMax A Good w k) := by
      intro k hk
      obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp hk
      have hi' := Finset.mem_filter.mp hi
      have hiA := hGoodSub hi'.1
      have hjA := hBadSub hj
      have hjNotGood : j ∉ Good := fun hjGood =>
        Finset.disjoint_left.mp hdisj hjGood hj
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_add.mpr ⟨i, hiA, j, hjA, rfl⟩
      · have hpair := relativePairHalf_le_support_diagonal Good w hiA hjA
        rw [relativeCosetPairHalf_of_good_bad hi'.1 hjNotGood] at hpair
        exact hi'.2.trans_le ((le_max_left _ _).trans hpair)
    exact haddLower.trans (Finset.card_le_card hsub)

lemma relative_support_layerCake_lower
    (A : Finset ℕ) (M : ℕ) (w L : ℕ → ℕ)
    (Good Bad : Finset ℕ)
    (hMpos : 0 < M) (hBad : Bad.Nonempty)
    (hpart : Good ∪ Bad = A) (hdisj : Disjoint Good Bad)
    (hmax : ∀ i ∈ A, w i ≤ M)
    (hLmax : ∀ k ∈ A + A, L k ≤ 2 * M)
    (hlow : ∀ t ∈ Finset.range M,
      A.card + (A.filter (fun i => t < w i)).card - 1 ≤
        ((A + A).filter fun k => t < L k).card)
    (hhigh : ∀ u ∈ Finset.range M,
      (Good.filter (fun i => M + u < 2 * w i)).card + Bad.card - 1 ≤
        ((A + A).filter fun k => M + u < L k).card) :
    (∑ i ∈ A, w i) + (A.card + Bad.card - 2) * M +
        ∑ i ∈ Good, (2 * w i - M) ≤
      ∑ k ∈ A + A, L k := by
  classical
  have hBadPos : 1 ≤ Bad.card := Finset.card_pos.mpr hBad
  have hApos : 1 ≤ A.card := by
    obtain ⟨b, hb⟩ := hBad
    apply Finset.card_pos.mpr
    refine ⟨b, ?_⟩
    rw [← hpart]
    exact Finset.mem_union_right _ hb
  have hsumw := sum_card_filter_lt_eq_sum A w M hmax
  have hexcessMax : ∀ i ∈ Good, 2 * w i - M ≤ M := by
    intro i hi
    have hiA : i ∈ A := by
      rw [← hpart]
      exact Finset.mem_union_left _ hi
    have := hmax i hiA
    omega
  have hsumExcess := sum_card_filter_lt_eq_sum Good
    (fun i => 2 * w i - M) M hexcessMax
  have hsumL := sum_card_filter_lt_eq_sum (A + A) L (2 * M) hLmax
  have hlowSum :
      ∑ t ∈ Finset.range M,
          (A.card + (A.filter fun i => t < w i).card - 1) ≤
        ∑ t ∈ Finset.range M,
          ((A + A).filter fun k => t < L k).card :=
    Finset.sum_le_sum hlow
  have hhighSum :
      ∑ u ∈ Finset.range M,
          ((Good.filter fun i => M + u < 2 * w i).card + Bad.card - 1) ≤
        ∑ u ∈ Finset.range M,
          ((A + A).filter fun k => M + u < L k).card :=
    Finset.sum_le_sum hhigh
  have hlowEval :
      ∑ t ∈ Finset.range M,
          (A.card + (A.filter fun i => t < w i).card - 1) =
        (∑ i ∈ A, w i) + M * (A.card - 1) := by
    have hsTerm : ∀ t ∈ Finset.range M,
        A.card + (A.filter fun i => t < w i).card - 1 =
          (A.filter fun i => t < w i).card + (A.card - 1) := by
      intro t ht
      omega
    calc
      _ = ∑ t ∈ Finset.range M,
          ((A.filter fun i => t < w i).card + (A.card - 1)) :=
            Finset.sum_congr rfl hsTerm
      _ = (∑ i ∈ A, w i) + M * (A.card - 1) := by
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
            (Bad.card - 1) := by intros; omega
    calc
      _ = ∑ u ∈ Finset.range M,
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
      · exact Or.inr ⟨t - M, by omega, by omega⟩
    · rintro (ht | ⟨u, hu, rfl⟩) <;> omega
  have hsplitDisj : Disjoint (Finset.range M)
      ((Finset.range M).image (fun u => M + u)) := by
    rw [Finset.disjoint_left]
    intro t ht hti
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hti
    simp only [Finset.mem_range] at ht hu
    omega
  have hrightSplit :
      (∑ t ∈ Finset.range M, ((A + A).filter fun k => t < L k).card) +
        ∑ u ∈ Finset.range M,
          ((A + A).filter fun k => M + u < L k).card =
        ∑ k ∈ A + A, L k := by
    rw [← hsumL, hsplitRange, Finset.sum_union hsplitDisj]
    congr 1
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact Nat.add_left_cancel hab
  rw [hlowEval] at hlowSum
  rw [hhighEval] at hhighSum
  have hadd := Nat.add_le_add hlowSum hhighSum
  rw [hrightSplit] at hadd
  have hcoeff : M * (A.card - 1) + M * (Bad.card - 1) =
      (A.card + Bad.card - 2) * M := by
    rw [← Nat.mul_add]
    have : (A.card - 1) + (Bad.card - 1) =
        A.card + Bad.card - 2 := by omega
    rw [this, Nat.mul_comm]
  rw [← hcoeff]
  omega

theorem relative_support_diagonal_weight_bound
    {A : Finset ℕ} {M : ℕ} {w : ℕ → ℕ}
    {Good Bad : Finset ℕ} {base : ℕ}
    (hAcard : 6 ≤ A.card) (hMpos : 0 < M)
    (hpart : Good ∪ Bad = A) (hdisj : Disjoint Good Bad)
    (hbase : base ∈ Good) (hbasew : w base = M)
    (hmax : ∀ i ∈ A, w i ≤ M) (hBad : Bad.Nonempty) :
    5 * (∑ i ∈ A, w i) ≤
      2 * ∑ k ∈ A + A, relativeSupportDiagonalMax A Good w k := by
  classical
  let L := relativeSupportDiagonalMax A Good w
  let G := ∑ i ∈ Good, w i
  let D := ∑ i ∈ Bad, w i
  let T := ∑ i ∈ Good, (2 * w i - M)
  have hGoodSub : Good ⊆ A := by
    intro i hi
    rw [← hpart]
    exact Finset.mem_union_left _ hi
  have hBadSub : Bad ⊆ A := by
    intro i hi
    rw [← hpart]
    exact Finset.mem_union_right _ hi
  have hGoodMax : ∀ i ∈ Good, w i ≤ M := by
    intro i hi
    exact hmax i (hGoodSub hi)
  have hD : D ≤ Bad.card * M := by
    dsimp only [D]
    calc
      ∑ i ∈ Bad, w i ≤ ∑ _i ∈ Bad, M := by
        apply Finset.sum_le_sum
        intro i hi
        exact hmax i (hBadSub hi)
      _ = Bad.card * M := by simp
  have hcards : A.card = Good.card + Bad.card := by
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hpart] at hc
    exact hc
  obtain ⟨hbasic, hstrong⟩ :=
    good_excess_bounds Good w hbase hbasew hGoodMax
  have harith : 5 * (G + D) ≤
      2 * ((G + D) + (A.card + Bad.card - 2) * M + T) := by
    apply relative_interval_arithmetic hAcard (Finset.card_pos.mpr hBad)
      hcards hD hbasic hstrong
  obtain ⟨hlow, hhigh⟩ := relative_support_threshold_bounds
    (A := A) (M := M) (w := w) (Good := Good) (Bad := Bad) (base := base)
    hMpos hpart hdisj hbase hbasew hmax hBad
  have hlayer : (G + D) + (A.card + Bad.card - 2) * M + T ≤
      ∑ k ∈ A + A, L k := by
    have hraw := relative_support_layerCake_lower A M w L Good Bad
      hMpos hBad hpart hdisj hmax
      (fun k hk => relativeSupportDiagonalMax_le hmax k) hlow hhigh
    have hsum : ∑ i ∈ A, w i = G + D := by
      rw [← hpart, Finset.sum_union hdisj]
    simpa [G, D, T, L, hsum] using hraw
  have hsum : ∑ i ∈ A, w i = G + D := by
    rw [← hpart, Finset.sum_union hdisj]
  rw [hsum]
  exact harith.trans (Nat.mul_le_mul_left 2 hlayer)

noncomputable def relativeSupportMaxPair
    (A Good : Finset ℕ) (w : ℕ → ℕ) (k : {k // k ∈ A + A}) : ℕ × ℕ :=
  Classical.choose (Finset.exists_max_image (supportAntidiagonalPairs A k.1)
    (fun p => relativeCosetPairHalf Good w p.1 p.2)
    (supportAntidiagonalPairs_nonempty k.2))

lemma relativeSupportMaxPair_mem
    (A Good : Finset ℕ) (w : ℕ → ℕ) (k : {k // k ∈ A + A}) :
    relativeSupportMaxPair A Good w k ∈ supportAntidiagonalPairs A k.1 :=
  (Classical.choose_spec (Finset.exists_max_image
    (supportAntidiagonalPairs A k.1)
    (fun p => relativeCosetPairHalf Good w p.1 p.2)
    (supportAntidiagonalPairs_nonempty k.2))).1

lemma relativeSupportMaxPair_realizes
    (A Good : Finset ℕ) (w : ℕ → ℕ) (k : {k // k ∈ A + A}) :
    relativeCosetPairHalf Good w
        (relativeSupportMaxPair A Good w k).1
        (relativeSupportMaxPair A Good w k).2 =
      relativeSupportDiagonalMax A Good w k.1 := by
  unfold relativeSupportDiagonalMax
  apply le_antisymm
  · exact Finset.le_sup
      (s := supportAntidiagonalPairs A k.1)
      (f := fun p => relativeCosetPairHalf Good w p.1 p.2)
      (b := relativeSupportMaxPair A Good w k)
      (relativeSupportMaxPair_mem A Good w k)
  · apply Finset.sup_le
    intro p hp
    exact (Classical.choose_spec (Finset.exists_max_image
      (supportAntidiagonalPairs A k.1)
      (fun p => relativeCosetPairHalf Good w p.1 p.2)
      (supportAntidiagonalPairs_nonempty k.2))).2 p hp

theorem all_fibers_contained_of_support_largest
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d)) {base : ℕ}
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hsmall : 2 * (X + X).card < 5 * X.card)
    (hbase : base ∈ firstCoordinateSet X)
    (hbaseMax : ∀ a ∈ firstCoordinateSet X,
      (coordinateFiber X a).card ≤ (coordinateFiber X base).card)
    {H : AddSubgroup (ZMod d)}
    (hbaseCos : ContainedInAddCoset H (coordinateFiber X base)) :
    ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a) := by
  classical
  let A := firstCoordinateSet X
  let w : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let M := w base
  let Good := A.filter fun a =>
    ContainedInAddCoset H (coordinateFiber X a)
  let Bad := A \ Good
  have hGoodSub : Good ⊆ A := Finset.filter_subset _ _
  have hBadSub : Bad ⊆ A := Finset.sdiff_subset
  have hbaseGood : base ∈ Good :=
    Finset.mem_filter.mpr ⟨hbase, hbaseCos⟩
  have hpart : Good ∪ Bad = A := Finset.union_sdiff_of_subset hGoodSub
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
  have haBad : a ∈ Bad := Finset.mem_sdiff.mpr ⟨ha, by
    intro haGood
    exact haNot (hGood a haGood)⟩
  have hBadNe : Bad.Nonempty := ⟨a, haBad⟩
  have hMpos : 0 < M := by
    dsimp only [M, w]
    exact Finset.card_pos.mpr (coordinateFiber_nonempty_iff.mpr hbase)
  have hmax : ∀ i ∈ A, w i ≤ M := by
    intro i hi
    exact hbaseMax i hi
  have hweight := relative_support_diagonal_weight_bound
    (A := A) (M := M) (w := w) (Good := Good) (Bad := Bad) (base := base)
    hAcard hMpos hpart hdisj hbaseGood rfl hmax hBadNe
  let pair : {k // k ∈ A + A} → ℕ × ℕ := relativeSupportMaxPair A Good w
  let P : Finset (ℕ × ℕ) := Finset.univ.image pair
  have hpairMem : ∀ k, pair k ∈ supportAntidiagonalPairs A k.1 := by
    intro k
    exact relativeSupportMaxPair_mem A Good w k
  have hpairInA : ∀ k, (pair k).1 ∈ A ∧ (pair k).2 ∈ A := by
    intro k
    have hk := mem_supportAntidiagonalPairs.mp (hpairMem k)
    exact ⟨hk.1, hk.2.1⟩
  have hpairSum : ∀ k, (pair k).1 + (pair k).2 = k.1 := by
    intro k
    exact (mem_supportAntidiagonalPairs.mp (hpairMem k)).2.2
  have hpairInj : Function.Injective pair := by
    intro i j hij
    apply Subtype.ext
    rw [← hpairSum i, ← hpairSum j, hij]
  have hPmem : ∀ p ∈ P,
      p.1 ∈ firstCoordinateSet X ∧ p.2 ∈ firstCoordinateSet X := by
    intro p hp
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
    exact hpairInA k
  have hPinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) P := by
    intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
    have hijVal : i.1 = j.1 := by simpa [hpairSum] using hpq
    have hij : i = j := Subtype.ext hijVal
    subst j
    rfl
  have hpoint : ∀ k : {k // k ∈ A + A},
      relativeCosetPairHalf Good w (pair k).1 (pair k).2 ≤
        (coordinateFiber X (pair k).1 + coordinateFiber X (pair k).2).card := by
    intro k
    let i := (pair k).1
    let j := (pair k).2
    have hiA := (hpairInA k).1
    have hjA := (hpairInA k).2
    have hiNe := coordinateFiber_nonempty_iff.mpr hiA
    have hjNe := coordinateFiber_nonempty_iff.mpr hjA
    change relativeCosetPairHalf Good w i j ≤
      (coordinateFiber X i + coordinateFiber X j).card
    by_cases hiG : i ∈ Good <;> by_cases hjG : j ∈ Good
    · simp only [relativeCosetPairHalf, if_pos hiG, if_pos hjG]
      exact max_le (Finset.card_le_card_add_right hjNe)
        (Finset.card_le_card_add_left hiNe)
    · rw [relativeCosetPairHalf_of_good_bad hiG hjG]
      apply max_le
      · exact two_mul_card_le_add_of_coset_and_not_coset hiNe hjNe
          (hGood i hiG) (hBadNot j (Finset.mem_sdiff.mpr ⟨hjA, hjG⟩))
      · exact Finset.card_le_card_add_left hiNe
    · have htwo := two_mul_card_le_add_of_coset_and_not_coset
          hjNe hiNe (hGood j hjG)
            (hBadNot i (Finset.mem_sdiff.mpr ⟨hiA, hiG⟩))
      simp only [relativeCosetPairHalf, if_neg hiG, if_pos hjG]
      apply max_le
      · exact Finset.card_le_card_add_right hjNe
      · simpa [add_comm] using htwo
    · simp only [relativeCosetPairHalf, if_neg hiG, if_neg hjG]
      exact max_le (Finset.card_le_card_add_right hjNe)
        (Finset.card_le_card_add_left hiNe)
  have hdiagToFiber :
      (∑ k : {k // k ∈ A + A},
          relativeSupportDiagonalMax A Good w k.1) ≤
        ∑ k : {k // k ∈ A + A},
          (coordinateFiber X (pair k).1 + coordinateFiber X (pair k).2).card := by
    apply Finset.sum_le_sum
    intro k hk
    rw [← relativeSupportMaxPair_realizes A Good w k]
    exact hpoint k
  have hfinToP : (∑ k : {k // k ∈ A + A},
        (coordinateFiber X (pair k).1 + coordinateFiber X (pair k).2).card) =
      ∑ p ∈ P, (coordinateFiber X p.1 + coordinateFiber X p.2).card := by
    dsimp only [P]
    rw [Finset.sum_image hpairInj.injOn]
  have hPsum : (∑ p ∈ P,
        (coordinateFiber X p.1 + coordinateFiber X p.2).card) ≤
      (X + X).card :=
    sum_card_coordinateFiber_add_le_card_add_of_pairSelection X P hPmem hPinj
  have hdiag : (∑ k ∈ A + A,
        relativeSupportDiagonalMax A Good w k) ≤ (X + X).card := by
    rw [Finset.sum_subtype (p := fun k => k ∈ A + A)
      (s := A + A) (by simp)]
    exact hdiagToFiber.trans (hfinToP.le.trans hPsum)
  have hXcard : X.card = ∑ i ∈ A, w i := card_eq_sum_card_coordinateFiber X
  have : 5 * X.card ≤ 2 * (X + X).card := by
    rw [hXcard]
    exact hweight.trans (Nat.mul_le_mul_left 2 hdiag)
  omega

/-- Complete finite-fibre coherence theorem.  Under the normalized support
hypotheses and strict `5/2` small doubling, one subgroup coset contains every
fibre, and the subgroup is smaller than three halves of a distinguished
fibre. -/
theorem exists_common_dense_coset_of_small_doubling
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ base ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X base) ∧
        2 * Nat.card H < 3 * (coordinateFiber X base).card ∧
        (∀ a ∈ firstCoordinateSet X,
          (coordinateFiber X a).card ≤ (coordinateFiber X base).card) ∧
        ∀ a ∈ firstCoordinateSet X,
          ContainedInAddCoset H (coordinateFiber X a) := by
  classical
  let A := firstCoordinateSet X
  let F : ℕ → ℕ := fun a => (coordinateFiber X a).card
  let Dense := A.filter fun a => ∃ H : AddSubgroup (ZMod d),
    ContainedInAddCoset H (coordinateFiber X a) ∧
      2 * Nat.card H < 3 * (coordinateFiber X a).card
  obtain ⟨a, ha, H₀, haCos, hH₀card⟩ :=
    exists_dense_fiber_coset_of_small_doubling X hA hAzero hAcard hgcd hsmall
  have haDense : a ∈ Dense :=
    Finset.mem_filter.mpr ⟨ha, ⟨H₀, haCos, hH₀card⟩⟩
  have hDenseNe : Dense.Nonempty := ⟨a, haDense⟩
  obtain ⟨base, hbaseDense, hbaseMaxDense⟩ :=
    Finset.exists_max_image Dense F hDenseNe
  have hbase : base ∈ firstCoordinateSet X :=
    (Finset.mem_filter.mp hbaseDense).1
  obtain ⟨H, hbaseCos, hHcard⟩ :=
    (Finset.mem_filter.mp hbaseDense).2
  obtain ⟨top, htop, htopMax⟩ :=
    Finset.exists_max_image (firstCoordinateSet X) F hA
  have hbaseLeTop : F base ≤ F top := htopMax base hbase
  by_cases hEq : F base = F top
  · have hbaseMax : ∀ z ∈ firstCoordinateSet X, F z ≤ F base := by
      intro z hz
      exact (htopMax z hz).trans_eq hEq.symm
    refine ⟨base, hbase, H, hbaseCos, hHcard, hbaseMax, ?_⟩
    exact all_fibers_contained_of_support_largest X hAcard hsmall
      hbase hbaseMax hbaseCos
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
    have hAll : ∀ z ∈ firstCoordinateSet X,
        ContainedInAddCoset H (coordinateFiber X z) := by
      apply all_fibers_contained_of_support_maximal_dense X hAcard hsmall
        hbase htop
      · simpa [F] using hbaseTop
      · intro z hz
        simpa [F] using htopMax z hz
      · exact hbaseCos
      · intro z hz hzCos
        simpa [F] using hGoodMax z hz hzCos
      · intro i hi j hj hhigh
        simpa [F] using hpairHigh i hi j hj (by simpa [F] using hhigh)
    have htopLe : F top ≤ F base := hGoodMax top htop (hAll top htop)
    omega

/-- The common subgroup supplied by fibre coherence has controlled total
mass even without using affine alignment of its individual cosets.  The
factor `4` is deliberately coarse: density gives `|H| ≤ 2M`, while the
anchored Hall estimate gives `(s - 2)M ≤ |X + X| - |X|`. -/
theorem exists_common_dense_coset_with_mass_bound
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet X)
    (hAcard : 6 ≤ (firstCoordinateSet X).card)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hsmall : 2 * (X + X).card < 5 * X.card) :
    ∃ base ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ContainedInAddCoset H (coordinateFiber X base) ∧
        2 * Nat.card H < 3 * (coordinateFiber X base).card ∧
        (∀ a ∈ firstCoordinateSet X,
          (coordinateFiber X a).card ≤ (coordinateFiber X base).card) ∧
        (∀ a ∈ firstCoordinateSet X,
          ContainedInAddCoset H (coordinateFiber X a)) ∧
        (firstCoordinateSet X).card * Nat.card H ≤
          4 * ((X + X).card - X.card) := by
  classical
  obtain ⟨base, hbase, H, hbaseCos, hHcard, hbaseMax, hAll⟩ :=
    exists_common_dense_coset_of_small_doubling X hA hAzero hAcard hgcd hsmall
  have hHall := layerHall_weighted_fiber_lower X hA hAzero
    (by omega : 3 ≤ (firstCoordinateSet X).card) hgcd hbase
    (D := ∅) (by simp) (by simp) (by simp)
  have hdiff :
      ((firstCoordinateSet X).card - 2) *
          (coordinateFiber X base).card ≤ (X + X).card - X.card := by
    simpa only [Finset.sum_empty, zero_add, add_zero] using
      (Nat.le_sub_of_add_le hHall)
  have hHle : Nat.card H ≤ 2 * (coordinateFiber X base).card := by
    omega
  have hs : (firstCoordinateSet X).card ≤
      2 * ((firstCoordinateSet X).card - 2) := by
    omega
  have hmass : (firstCoordinateSet X).card * Nat.card H ≤
      4 * ((X + X).card - X.card) := by
    calc
      (firstCoordinateSet X).card * Nat.card H ≤
          (firstCoordinateSet X).card *
            (2 * (coordinateFiber X base).card) :=
        Nat.mul_le_mul_left _ hHle
      _ ≤ 4 * (((firstCoordinateSet X).card - 2) *
            (coordinateFiber X base).card) := by
        nlinarith
      _ ≤ 4 * ((X + X).card - X.card) :=
        Nat.mul_le_mul_left 4 hdiff
  exact ⟨base, hbase, H, hbaseCos, hHcard, hbaseMax, hAll, hmass⟩

end Erdos360
