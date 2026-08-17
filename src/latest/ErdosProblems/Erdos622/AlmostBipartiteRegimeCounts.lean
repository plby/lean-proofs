import ErdosProblems.Erdos622.AlmostBipartite
import ErdosProblems.Erdos622.MatchingDeleteTransfer
import ErdosProblems.Erdos622.OneSmallGaussian

/-!
# Counting lemmas for the cover regimes in the almost-bipartite case

This file is deliberately separate from `AlmostBipartite.lean`.  It supplies
the exact symmetric-difference transport from subsets of an arbitrary cut to
the fair-binomial count, and packages the subtraction of the exceptional
Hall-matching family.  No graph-theoretic Hamiltonicity input is used here.
-/

open Filter Finset Real
open scoped BigOperators Topology SimpleGraph symmDiff

namespace Erdos622.AlmostBipartiteRegimeCounts

noncomputable section

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma mem_left_iff_not_mem_right {A B : Finset V}
    (hcut : IsCut A B) (v : V) : v ∈ A ↔ v ∉ B := by
  constructor
  · intro hvA hvB
    exact Finset.disjoint_left.mp hcut.1 hvA hvB
  · intro hvB
    have hv : v ∈ A ∪ B := by
      rw [hcut.2]
      exact Finset.mem_univ v
    rcases Finset.mem_union.mp hv with hvA | hvB'
    · exact hvA
    · exact (hvB hvB').elim

/-- Toggling all coordinates in the right side of a cut changes cardinality
into the complemented two-block difference statistic. -/
lemma card_symmDiff_right {A B S : Finset V} (hcut : IsCut A B) :
    (S ∆ B).card = (S ∩ A).card + (B.card - (S ∩ B).card) := by
  have heq : S ∆ B = (S ∩ A) ∪ (B \ S) := by
    ext v
    rw [Finset.mem_symmDiff]
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    rw [mem_left_iff_not_mem_right hcut v]
  rw [heq, Finset.card_union_of_disjoint]
  · have hdiff : B \ S = B \ (B ∩ S) := by
      ext v
      simp
    rw [hdiff, Finset.card_sdiff_of_subset Finset.inter_subset_left]
    rw [Finset.inter_comm B S]
  · rw [Finset.disjoint_left]
    intro v hvSA hvBS
    exact (Finset.mem_sdiff.mp hvBS).2 (Finset.mem_inter.mp hvSA).1

/-- Exact fair-binomial law for the signed cardinality difference across an
arbitrary finite cut.  The proof is the involution `S ↦ S ∆ B`. -/
theorem cut_difference_count_eq_binomialCount {A B : Finset V}
    (hcut : IsCut A B) (P : ℕ → Prop) :
    almostBipartiteCount (Finset.univ : Finset V)
        (fun S ↦ P ((S ∩ A).card + (B.card - (S ∩ B).card))) =
      Counting.binomialCount (Fintype.card V) P := by
  classical
  have hinvol (T : Finset V) : (T ∆ B) ∆ B = T := by
    ext v
    simp only [Finset.mem_symmDiff]
    tauto
  have htoggle :
      almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ P ((S ∩ A).card + (B.card - (S ∩ B).card))) =
        almostBipartiteCount (Finset.univ : Finset V) (fun S ↦ P S.card) := by
    unfold almostBipartiteCount almostBipartiteEvent
    refine Finset.card_bij' (fun S _ ↦ S ∆ B) (fun T _ ↦ T ∆ B) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [card_symmDiff_right hcut]
      exact hS.2
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [← card_symmDiff_right hcut, hinvol]
      exact hT.2
    · intro S _hS
      exact hinvol S
    · intro T _hT
      exact hinvol T
  rw [htoggle]
  unfold almostBipartiteCount almostBipartiteEvent
  change Counting.countEvent (Finset.univ : Finset V) (fun S ↦ P S.card) = _
  calc
    Counting.countEvent (Finset.univ : Finset V) (fun S ↦ P S.card) =
        ∑ k ∈ Finset.range ((Finset.univ : Finset V).card + 1),
          if P k then (Finset.univ : Finset V).card.choose k else 0 :=
      Counting.countEvent_card_eq_sum _ P
    _ = ∑ k ∈ Finset.range (Fintype.card V + 1),
          if P k then (Fintype.card V).choose k else 0 := by simp
    _ = Counting.binomialCount (Fintype.card V) P :=
      (Counting.binomialCount_eq_sum _ P).symm

/-- The preceding transport specialized to a standardized binomial window. -/
theorem cut_difference_window_count {A B : Finset V}
    (hcut : IsCut A B) (a b : ℝ) :
    almostBipartiteCount (Finset.univ : Finset V)
        (fun S ↦ BinomialCLT.standardizedBinomialPoint (Fintype.card V)
          ((S ∩ A).card + (B.card - (S ∩ B).card)) ∈ Set.Icc a b) =
      BinomialCLT.fairBinomialWindowCount (Fintype.card V) a b := by
  have h := cut_difference_count_eq_binomialCount hcut
    (fun k ↦ BinomialCLT.standardizedBinomialPoint (Fintype.card V) k ∈ Set.Icc a b)
  rw [h, Counting.binomialCount_eq_sum]
  unfold BinomialCLT.fairBinomialWindowCount
  rw [← Nat.range_succ_eq_Iic]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hmem : BinomialCLT.standardizedBinomialPoint (Fintype.card V) k ∈ Set.Icc a b
  · simp only [hmem, ↓reduceIte]
  · simp only [hmem, ↓reduceIte]

lemma card_restrictedPart_eq_inter (S A : Finset V) :
    (restrictedPart S A).card = (S ∩ A).card := by
  classical
  apply Finset.card_bij (fun v _ ↦ v.1)
  · intro v hv
    exact Finset.mem_inter.mpr ⟨v.property, mem_restrictedPart.mp hv⟩
  · intro v hv w hw hvw
    exact Subtype.ext hvw
  · intro v hv
    exact ⟨⟨v, (Finset.mem_inter.mp hv).1⟩,
      mem_restrictedPart.mpr (Finset.mem_inter.mp hv).2, rfl⟩

/-- Finite subtraction principle: a signed-difference window is good whenever
the left internal graph has a sufficiently large sampled matching. -/
theorem goodSample_count_of_left_window
    (G : SimpleGraph V) {A B : Finset V}
    (_hcut : IsCut A B) (P : Finset V → Prop) (threshold R : ℝ)
    (hwindowGood : ∀ S : Finset V, S ⊆ Finset.univ → P S →
      RandomCover.HasMatchingAtLeast (internalGraph G A) S threshold →
        IsKGoodSample G A B S 0)
    (hwindow : R ≤
      (almostBipartiteCount (Finset.univ : Finset V) P : ℝ))
    {δ : ℝ}
    (hfailure :
      ((((Finset.univ : Finset V).powerset.filter fun S ↦
          ¬ RandomCover.HasMatchingAtLeast (internalGraph G A) S threshold).card : ℝ)) ≤
        δ * (2 : ℝ) ^ Fintype.card V) :
    R - δ * (2 : ℝ) ^ Fintype.card V ≤
      (almostBipartiteCount (Finset.univ : Finset V)
        (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  have hnat : almostBipartiteCount (Finset.univ : Finset V) P ≤
      almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ IsKGoodSample G A B S 0) +
        ((Finset.univ : Finset V).powerset.filter fun S ↦
          ¬ RandomCover.HasMatchingAtLeast (internalGraph G A) S threshold).card := by
    unfold almostBipartiteCount almostBipartiteEvent
    calc
      ((Finset.univ : Finset V).powerset.filter P).card ≤
          (((Finset.univ : Finset V).powerset.filter fun S ↦
              IsKGoodSample G A B S 0) ∪
            ((Finset.univ : Finset V).powerset.filter fun S ↦
              ¬ RandomCover.HasMatchingAtLeast (internalGraph G A) S threshold)).card := by
        apply Finset.card_le_card
        intro S hS
        simp only [Finset.mem_filter, Finset.mem_powerset,
          Finset.mem_union] at hS ⊢
        by_cases hm : RandomCover.HasMatchingAtLeast (internalGraph G A) S threshold
        · exact Or.inl ⟨hS.1, hwindowGood S hS.1 hS.2 hm⟩
        · exact Or.inr ⟨hS.1, hm⟩
      _ ≤ _ := Finset.card_union_le _ _
  have hreal : (almostBipartiteCount (Finset.univ : Finset V) P : ℝ) ≤
      (almostBipartiteCount (Finset.univ : Finset V)
        (fun S ↦ IsKGoodSample G A B S 0) : ℝ) +
      (((Finset.univ : Finset V).powerset.filter fun S ↦
        ¬ RandomCover.HasMatchingAtLeast (internalGraph G A) S threshold).card : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- Generic finite union-bound subtraction, used when the Hall matching is
constructed on an auxiliary transferred side rather than directly on `A`. -/
theorem goodSample_count_of_window_failure
    (G : SimpleGraph V) {A B : Finset V}
    (P Failure : Finset V → Prop) (R δ : ℝ)
    (hgood : ∀ S : Finset V, S ⊆ Finset.univ → P S → ¬ Failure S →
      IsKGoodSample G A B S 0)
    (hwindow : R ≤
      (almostBipartiteCount (Finset.univ : Finset V) P : ℝ))
    (hfailure :
      (almostBipartiteCount (Finset.univ : Finset V) Failure : ℝ) ≤
        δ * (2 : ℝ) ^ Fintype.card V) :
    R - δ * (2 : ℝ) ^ Fintype.card V ≤
      (almostBipartiteCount (Finset.univ : Finset V)
        (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  have hnat : almostBipartiteCount (Finset.univ : Finset V) P ≤
      almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ IsKGoodSample G A B S 0) +
        almostBipartiteCount (Finset.univ : Finset V) Failure := by
    unfold almostBipartiteCount almostBipartiteEvent
    calc
      ((Finset.univ : Finset V).powerset.filter P).card ≤
          (((Finset.univ : Finset V).powerset.filter fun S ↦
              IsKGoodSample G A B S 0) ∪
            ((Finset.univ : Finset V).powerset.filter Failure)).card := by
        apply Finset.card_le_card
        intro S hS
        simp only [Finset.mem_filter, Finset.mem_powerset,
          Finset.mem_union] at hS ⊢
        by_cases hF : Failure S
        · exact Or.inr ⟨hS.1, hF⟩
        · exact Or.inl ⟨hS.1, hgood S hS.1 hS.2 hF⟩
      _ ≤ _ := Finset.card_union_le _ _
  have hreal : (almostBipartiteCount (Finset.univ : Finset V) P : ℝ) ≤
      (almostBipartiteCount (Finset.univ : Finset V)
        (fun S ↦ IsKGoodSample G A B S 0) : ℝ) +
      (almostBipartiteCount (Finset.univ : Finset V) Failure : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- The fixed window used in the large-imbalance regime has the correct
orientation, and its signed difference is at most twice the cut excess. -/
lemma largeImbalance_window_bounds
    {n a b x y : ℕ}
    (hsum : a + b = 2 * n) (hna : n ≤ a)
    (hx : x ≤ a) (hy : y ≤ b)
    (hlarge : Nat.sqrt n < a - n)
    (hwindow : BinomialCLT.standardizedBinomialPoint (2 * n)
        (x + (b - y)) ∈
      Set.Icc (-(Real.sqrt 2)) (Real.sqrt 2 / 4)) :
    y ≤ x ∧ 2 * (x - y) ≤ 3 * (a - n) := by
  let d := a - n
  have ha : a = n + d := by omega
  have ha2n : a ≤ 2 * n := by omega
  have hdle : d ≤ n := by omega
  have hb : b = n - d := by omega
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp at hsum hlarge
    omega
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtmul : Real.sqrt (2 * n : ℝ) = Real.sqrt 2 * Real.sqrt n := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hden : 0 < Real.sqrt (2 * n : ℝ) := by positivity
  have hnum :
      (2 * (x + (b - y)) : ℝ) - (2 * n : ℝ) =
        2 * ((x : ℝ) - y - d) := by
    push_cast [Nat.cast_sub hy, Nat.cast_sub hdle, hb]
    ring
  have hnltSq : n < d ^ 2 := Nat.sqrt_lt'.mp hlarge
  have hnltSqReal : (n : ℝ) < (d : ℝ) ^ 2 := by exact_mod_cast hnltSq
  have hsqrtnSq : (Real.sqrt n) ^ 2 = n := by
    rw [sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
  have hdreal : Real.sqrt n < d := by
    have hdnonneg : (0 : ℝ) ≤ d := by positivity
    nlinarith
  constructor
  · by_contra hxy
    have hxy' : x < y := Nat.lt_of_not_ge hxy
    have hnumlt :
        (2 * (x + (b - y)) : ℝ) - (2 * n : ℝ) <
          -(Real.sqrt 2) * Real.sqrt (2 * n : ℝ) := by
      rw [hnum, hsqrtmul]
      have hxyreal : (x : ℝ) < y := by exact_mod_cast hxy'
      nlinarith
    have hratio :
        BinomialCLT.standardizedBinomialPoint (2 * n) (x + (b - y)) <
          -(Real.sqrt 2) := by
      unfold BinomialCLT.standardizedBinomialPoint
      norm_num
      rw [Nat.cast_sub hy]
      rw [div_lt_iff₀ (mul_pos hsqrt2 hsqrtn)]
      rw [← hsqrtmul]
      exact hnumlt
    exact (not_lt_of_ge hwindow.1) hratio
  · by_contra hdiff
    have hdiff' : 3 * d < 2 * (x - y) := Nat.lt_of_not_ge hdiff
    have hyx : y ≤ x := by omega
    have hnumgt :
        (Real.sqrt 2 / 2) * Real.sqrt (2 * n : ℝ) <
          (2 * (x + (b - y)) : ℝ) - (2 * n : ℝ) := by
      rw [hnum, hsqrtmul]
      have hdiffreal' : (3 * d : ℝ) < (2 * (x - y) : ℕ) := by
        exact_mod_cast hdiff'
      norm_num at hdiffreal'
      rw [Nat.cast_sub hyx] at hdiffreal'
      nlinarith
    have hratio : Real.sqrt 2 / 2 <
        BinomialCLT.standardizedBinomialPoint (2 * n) (x + (b - y)) := by
      unfold BinomialCLT.standardizedBinomialPoint
      norm_num
      rw [Nat.cast_sub hy]
      rw [lt_div_iff₀ (mul_pos hsqrt2 hsqrtn)]
      rw [← hsqrtmul]
      exact hnumgt
    have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hquarter : Real.sqrt 2 / 4 < Real.sqrt 2 / 2 := by nlinarith
    exact (not_lt_of_ge hwindow.2) (hquarter.trans hratio)

/-- Uniform large-imbalance regime.  The constants are chosen with ample
integer slack: the random-cover theorem is used at Hall loss `1/64`, while
the tailored cover bound `8(d+1) ≤ |C|` makes its Hall threshold exceed
`2d`.  A fixed normal window has mass strictly greater than one half. -/
theorem eventually_largeImbalance_goodSample_count
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B C : Finset (Fin (2 * n))),
        G.IsRegularOfDegree (n + 1) →
        IsAlmostBipartiteCut G A B →
        IsMinimumVertexCoverOn G A C →
        Nat.sqrt n < A.card - n →
        ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
          (almostBipartiteCount
            (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  obtain ⟨margin, hmargin, hnormal⟩ :=
    Erdos622.eventually_uniform_normal_window_above_half
      (η := (1 : ℝ)) (M := 4) (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnormal
  have hwindow : ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 2 : ℝ) + margin / 2 <
        (BinomialCLT.fairBinomialWindowCount (2 * n)
          (-(Real.sqrt 2)) (Real.sqrt 2 / 4) : ℝ) /
          (2 : ℝ) ^ (2 * n) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    have h2n : N ≤ 2 * n := by omega
    simpa using hN (2 * n) h2n (4 : ℝ)
      (by constructor <;> norm_num)
  have hhall := eventually_minimumCoverOn_ambient_randomMatching_count_le
    (L := 1) (eps := (1 / 64 : ℝ)) (delta := ε)
      (by omega) (by norm_num) (by norm_num) hε
  filter_upwards [hwindow, hhall, Filter.eventually_ge_atTop 16] with
      n hnWindow hnHall hn16
  intro G A B C hreg hAB hC hlarge
  have hsum : A.card + B.card = 2 * n := by
    simpa using hAB.1.card_add_card
  have hnA : n ≤ A.card := by exact_mod_cast hAB.2.1
  have hcoverStrong : 8 * (A.card - n + 1) ≤ C.card :=
    hAB.minimumCover_largeImbalance hreg hC hn16 (by omega)
  have hcoverSqrt : sqrtCoverThreshold 1 n ≤ C.card := by
    have := hAB.minimumCover_sqrtThreshold_of_largeImbalance
      hreg hC hn16 (L := 1)
    exact this (by simpa [sqrtCoverThreshold] using hlarge)
  have hfailure := hnHall (Fin (2 * n)) G A C hC hcoverSqrt
  let P : Finset (Fin (2 * n)) → Prop := fun S ↦
    BinomialCLT.standardizedBinomialPoint (2 * n)
      ((S ∩ A).card + (B.card - (S ∩ B).card)) ∈
        Set.Icc (-(Real.sqrt 2)) (Real.sqrt 2 / 4)
  have hcountEq :
      almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) P =
        BinomialCLT.fairBinomialWindowCount (2 * n)
          (-(Real.sqrt 2)) (Real.sqrt 2 / 4) := by
    simpa [P] using cut_difference_window_count hAB.1
      (-(Real.sqrt 2)) (Real.sqrt 2 / 4)
  have hwindowRaw :
      ((1 / 2 : ℝ) + margin / 2) * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n))) P : ℝ) := by
    rw [hcountEq]
    exact (le_of_lt ((lt_div_iff₀ (by positivity)).mp hnWindow))
  have hwindowGood : ∀ S : Finset (Fin (2 * n)), S ⊆ Finset.univ → P S →
      RandomCover.HasMatchingAtLeast (internalGraph G A) S
        ((1 / 4 - 1 / 64 : ℝ) * C.card) →
      IsKGoodSample G A B S 0 := by
    intro S hSuniv hSP hmatching
    have hx : (S ∩ A).card ≤ A.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hy : (S ∩ B).card ≤ B.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hb := largeImbalance_window_bounds hsum hnA hx hy hlarge hSP
    have hpartCard : (restrictedPart S B).card ≤ (restrictedPart S A).card := by
      simpa only [card_restrictedPart_eq_inter] using hb.1
    have hdiff :
        2 * ((restrictedPart S A).card - (restrictedPart S B).card) ≤
          3 * (A.card - n) := by
      simpa only [card_restrictedPart_eq_inter] using hb.2
    have hthreshold :
        (3 / 2 : ℝ) * ((A.card - n : ℕ) : ℝ) ≤
          (1 / 4 - 1 / 64 : ℝ) * C.card := by
      have hcoverStrongReal :
          ((8 * (A.card - n + 1) : ℕ) : ℝ) ≤ C.card := by
        exact_mod_cast hcoverStrong
      norm_num at hcoverStrongReal ⊢
      nlinarith
    obtain ⟨M, hMmatching, hMsupport, hMcard⟩ := hmatching
    have hdiffReal :
        (((restrictedPart S A).card - (restrictedPart S B).card : ℕ) : ℝ) ≤
          (3 / 2 : ℝ) * ((A.card - n : ℕ) : ℝ) := by
      have hdiffReal' :
          ((2 * ((restrictedPart S A).card -
            (restrictedPart S B).card) : ℕ) : ℝ) ≤
            ((3 * (A.card - n) : ℕ) : ℝ) := by
        exact_mod_cast hdiff
      norm_num at hdiffReal'
      linarith
    have htarget :
        (((restrictedPart S A).card - (restrictedPart S B).card : ℕ) : ℝ) ≤
          (1 / 4 - 1 / 64 : ℝ) * C.card := by
      exact hdiffReal.trans hthreshold
    apply IsKGoodSample.of_ambient_matching_left hAB.1 hpartCard
    simpa using (show RandomCover.HasMatchingAtLeast (internalGraph G A) S
        (((restrictedPart S A).card - (restrictedPart S B).card : ℕ) : ℝ)
      from ⟨M, hMmatching, hMsupport, htarget.trans hMcard⟩)
  have hgood := goodSample_count_of_left_window G hAB.1 P
    ((1 / 4 - 1 / 64 : ℝ) * C.card)
    (((1 / 2 : ℝ) + margin / 2) * (2 : ℝ) ^ (2 * n))
    hwindowGood hwindowRaw hfailure
  have hgood' :
      ((1 / 2 : ℝ) + margin / 2) * (2 : ℝ) ^ (2 * n) -
          ε * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
    simpa using hgood
  calc
    ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
        ((1 / 2 : ℝ) + margin / 2) * (2 : ℝ) ^ (2 * n) -
          ε * (2 : ℝ) ^ (2 * n) := by
      have hp : 0 ≤ (2 : ℝ) ^ (2 * n) := by positivity
      nlinarith
    _ ≤ (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := hgood'

/-- The cover-product arm gives a linear-in-`sqrt n` lower bound for the
opposite cover.  This cancellation lemma is purely integral and avoids all
rounding losses: if `r = floor(sqrt n / K)` and `K > H`, then
`n+1 ≤ r(D+1)` forces `H floor(sqrt n) ≤ D`. -/
lemma coverProductArm_forces_sqrtCover
    {n K H D : ℕ} (hHK : H < K)
    (hprod : n + 1 ≤ sqrtCoverThreshold K n * (D + 1)) :
    H * Nat.sqrt n ≤ D := by
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [sqrtCoverThreshold] at hprod
  by_contra hD
  have hD' : D + 1 ≤ H * Nat.sqrt n := by omega
  have hKpos : 0 < K := lt_of_le_of_lt (Nat.zero_le H) hHK
  have hrK : sqrtCoverThreshold K n * K ≤ Nat.sqrt n := by
    simpa [sqrtCoverThreshold, Nat.mul_comm] using
      Nat.div_mul_le_self (Nat.sqrt n) K
  have hchain : K * (n + 1) ≤ H * n := by
    calc
      K * (n + 1) ≤ K * (sqrtCoverThreshold K n * (D + 1)) :=
        Nat.mul_le_mul_left K hprod
      _ = (sqrtCoverThreshold K n * K) * (D + 1) := by ring
      _ ≤ Nat.sqrt n * (D + 1) := Nat.mul_le_mul_right (D + 1) hrK
      _ ≤ Nat.sqrt n * (H * Nat.sqrt n) :=
        Nat.mul_le_mul_left (Nat.sqrt n) hD'
      _ = H * (Nat.sqrt n) ^ 2 := by ring
      _ ≤ H * n := Nat.mul_le_mul_left H (Nat.sqrt_le' n)
  have hstrict : H * n < K * (n + 1) := by
    have hmul : H * n < K * n := Nat.mul_lt_mul_of_pos_right hHK hnpos
    have hnext : K * n < K * (n + 1) :=
      Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self n) hKpos
    exact hmul.trans hnext
  exact (not_lt_of_ge hchain) hstrict

/-- Arithmetic of the negative original-cut window used when the balanced
right cover is the large one.  The upper endpoint fixes the original
orientation; the lower endpoint budgets both the required right forest and
the loss of at most `d` matching edges at transferred vertices. -/
lemma oneSmall_negative_window_bounds
    {n K M a b x y : ℕ}
    (hK : 0 < K) (hM : 0 < M)
    (hsum : a + b = 2 * n) (hna : n ≤ a)
    (hy : y ≤ b) (hsmall : a - n ≤ sqrtCoverThreshold K n)
    (hwindow : BinomialCLT.standardizedBinomialPoint (2 * n)
        (x + (b - y)) ∈
      Set.Icc (-(M * Real.sqrt 2)) (-(Real.sqrt 2 / K))) :
    x ≤ y ∧ y - x + (a - n) ≤ 2 * M * Nat.sqrt n := by
  let d := a - n
  have ha : a = n + d := by omega
  have ha2n : a ≤ 2 * n := by omega
  have hdle : d ≤ n := by omega
  have hb : b = n - d := by omega
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    have hy0 : y = 0 := by omega
    simp [ha0, hb0, hy0, BinomialCLT.standardizedBinomialPoint] at hwindow
    have hKReal : (0 : ℝ) < K := by exact_mod_cast hK
    have hpos : 0 < Real.sqrt 2 / (K : ℝ) := div_pos (by positivity) hKReal
    linarith
  have hspos : 0 < Nat.sqrt n := Nat.sqrt_pos.2 hnpos
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtmul : Real.sqrt (2 * n : ℝ) = Real.sqrt 2 * Real.sqrt n := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hnum :
      (2 * (x + (b - y)) : ℝ) - (2 * n : ℝ) =
        2 * ((x : ℝ) - y - d) := by
    push_cast [Nat.cast_sub hy, Nat.cast_sub hdle, hb]
    ring
  have hdK : d * K ≤ Nat.sqrt n := by
    change d ≤ sqrtCoverThreshold K n at hsmall
    exact (Nat.le_div_iff_mul_le hK).mp (by simpa [sqrtCoverThreshold] using hsmall)
  have hsSq : ((Nat.sqrt n : ℕ) : ℝ) ^ 2 ≤ n := by
    exact_mod_cast Nat.sqrt_le' n
  have hsleReal : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
    have hsnonneg : (0 : ℝ) ≤ Nat.sqrt n := by positivity
    have hsqrtSq : (Real.sqrt n) ^ 2 = n := by
      rw [sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
    nlinarith
  have hdReal : (d : ℝ) ≤ Real.sqrt n / K := by
    have hdKReal : (d : ℝ) * K ≤ Nat.sqrt n := by exact_mod_cast hdK
    rw [le_div_iff₀ (by exact_mod_cast hK)]
    exact hdKReal.trans hsleReal
  have hxy : x ≤ y := by
    by_contra h
    have hyx : y < x := Nat.lt_of_not_ge h
    have hyxReal : (y : ℝ) < x := by exact_mod_cast hyx
    have hdKReal : (d : ℝ) * K ≤ Real.sqrt n := by
      have hcast : (d : ℝ) * K ≤ Nat.sqrt n := by exact_mod_cast hdK
      exact hcast.trans hsleReal
    have hupper := hwindow.2
    unfold BinomialCLT.standardizedBinomialPoint at hupper
    norm_num at hupper
    rw [Nat.cast_sub hy] at hupper
    rw [div_le_iff₀ (mul_pos hsqrt2 hsqrtn)] at hupper
    rw [hnum] at hupper
    have hKReal : (0 : ℝ) < K := by exact_mod_cast hK
    field_simp at hupper
    nlinarith
  refine ⟨hxy, ?_⟩
  have hlower := hwindow.1
  unfold BinomialCLT.standardizedBinomialPoint at hlower
  norm_num at hlower
  rw [Nat.cast_sub hy] at hlower
  rw [le_div_iff₀ (mul_pos hsqrt2 hsqrtn)] at hlower
  rw [hnum] at hlower
  have hboundReal : ((y - x + d : ℕ) : ℝ) ≤ M * Real.sqrt n := by
    rw [Nat.cast_add, Nat.cast_sub hxy]
    nlinarith
  have hslt : Real.sqrt n < Nat.sqrt n + 1 := by
    exact Real.real_sqrt_lt_nat_sqrt_succ
  have hsone : Nat.sqrt n + 1 ≤ 2 * Nat.sqrt n := by omega
  have hcoarse : M * Real.sqrt n < ((2 * M * Nat.sqrt n : ℕ) : ℝ) := by
    have hsoneReal : (Nat.sqrt n : ℝ) + 1 ≤ 2 * Nat.sqrt n := by exact_mod_cast hsone
    have hMReal : (0 : ℝ) < M := by exact_mod_cast hM
    push_cast
    nlinarith
  have hfinal := (hboundReal.trans_lt hcoarse).le
  exact_mod_cast hfinal

/-- The one-small-cover arm in which the balanced right cover is forced
large.  The statement keeps the original tailored cut `(A,B)` and records
the transfer set explicitly; the matching in `B₀ = B ∪ T` is pruned before
it is used as a forest on the original sampled right part. -/
theorem eventually_oneSmallCover_right_goodSample_count
    {ε : ℝ} (hε : 0 < ε) {K M : ℕ}
    (hM : 0 < M) (hKM : 16 * M < K)
    (hgauss : (1 / 2 : ℝ) - ε / 2 <
      BinomialCLT.gaussianWindowMass (-(M * Real.sqrt 2))
        (-(Real.sqrt 2 / K))) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B T B₀ D : Finset (Fin (2 * n))),
        IsCut A B → n ≤ A.card →
        A.card - n ≤ sqrtCoverThreshold K n →
        T.card = A.card - n → Disjoint B T → B₀ = B ∪ T →
        IsMinimumVertexCoverOn G B₀ D →
        n + 1 ≤ sqrtCoverThreshold K n * (D.card + 1) →
        ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
          (almostBipartiteCount
            (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le (16 * M)) hKM
  have hab : -(M * Real.sqrt 2) ≤ -(Real.sqrt 2 / K) := by
    have hKReal : (0 : ℝ) < K := by exact_mod_cast hK
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hdiv : Real.sqrt 2 / K ≤ M * Real.sqrt 2 := by
      have : (1 : ℝ) / K ≤ M := by
        have honeK : (1 : ℝ) / K ≤ 1 := (div_le_one hKReal).2 hKone
        exact honeK.trans hMReal
      have hmul := mul_le_mul_of_nonneg_right this hsqrt
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    linarith
  have hclt := BinomialCLT.eventually_lt_fairBinomialWindowCount_ratio hab hgauss
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hclt
  have hclt2 : ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 2 : ℝ) - ε / 2 <
        (BinomialCLT.fairBinomialWindowCount (2 * n)
          (-(M * Real.sqrt 2)) (-(Real.sqrt 2 / K)) : ℝ) /
          (2 : ℝ) ^ (2 * n) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    exact hN (2 * n) (by omega)
  have hhall := eventually_minimumCoverOn_ambient_randomMatching_count_le
    (L := 1) (eps := (1 / 64 : ℝ)) (delta := ε / 2)
      (by omega) (by norm_num) (by norm_num) (by positivity)
  filter_upwards [hclt2, hhall] with n hnWindow hnHall
  intro G A B T B₀ D hcut hnA hsmall hTcard hBT hB₀ hD hprod
  have hsum : A.card + B.card = 2 * n := by
    simpa using hcut.card_add_card
  have hDlarge : 16 * M * Nat.sqrt n ≤ D.card :=
    coverProductArm_forces_sqrtCover hKM hprod
  have hDsqrt : sqrtCoverThreshold 1 n ≤ D.card := by
    simp only [sqrtCoverThreshold, Nat.div_one]
    have hMone : 1 ≤ M := hM
    calc
      Nat.sqrt n ≤ 16 * M * Nat.sqrt n := by
        have : 1 ≤ 16 * M := by omega
        simpa using Nat.mul_le_mul_right (Nat.sqrt n) this
      _ ≤ D.card := hDlarge
  let threshold : ℝ := (1 / 4 - 1 / 64 : ℝ) * D.card
  let P : Finset (Fin (2 * n)) → Prop := fun S ↦
    BinomialCLT.standardizedBinomialPoint (2 * n)
      ((S ∩ A).card + (B.card - (S ∩ B).card)) ∈
        Set.Icc (-(M * Real.sqrt 2)) (-(Real.sqrt 2 / K))
  let Failure : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ RandomCover.HasMatchingAtLeast (internalGraph G B₀) S threshold
  have hfailure :
      (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) Failure : ℝ) ≤
        (ε / 2) * (2 : ℝ) ^ (2 * n) := by
    have h := hnHall (Fin (2 * n)) G B₀ D hD hDsqrt
    simpa [Failure, threshold, almostBipartiteCount, almostBipartiteEvent] using h
  have hcountEq :
      almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) P =
        BinomialCLT.fairBinomialWindowCount (2 * n)
          (-(M * Real.sqrt 2)) (-(Real.sqrt 2 / K)) := by
    simpa [P] using cut_difference_window_count hcut
      (-(M * Real.sqrt 2)) (-(Real.sqrt 2 / K))
  have hwindowRaw :
      ((1 / 2 : ℝ) - ε / 2) * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n))) P : ℝ) := by
    rw [hcountEq]
    exact (le_of_lt ((lt_div_iff₀ (by positivity)).mp hnWindow))
  have hgoodWindow : ∀ S : Finset (Fin (2 * n)), S ⊆ Finset.univ →
      P S → ¬ Failure S → IsKGoodSample G A B S 0 := by
    intro S hSuniv hSP hnotFailure
    have hy : (S ∩ B).card ≤ B.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hb := oneSmall_negative_window_bounds hK hM hsum hnA hy hsmall hSP
    have hpartCard : (restrictedPart S A).card ≤ (restrictedPart S B).card := by
      simpa only [card_restrictedPart_eq_inter] using hb.1
    have hloss : (S ∩ T).card ≤ A.card - n := by
      calc
        (S ∩ T).card ≤ T.card := Finset.card_le_card Finset.inter_subset_right
        _ = A.card - n := hTcard
    have hbudget :
        (restrictedPart S B).card - (restrictedPart S A).card +
            (S ∩ T).card ≤ 2 * M * Nat.sqrt n := by
      rw [card_restrictedPart_eq_inter, card_restrictedPart_eq_inter]
      omega
    have hthreshold :
        (((restrictedPart S B).card - (restrictedPart S A).card +
            (S ∩ T).card : ℕ) : ℝ) ≤ threshold := by
      have hbudgetReal :
          (((restrictedPart S B).card - (restrictedPart S A).card +
              (S ∩ T).card : ℕ) : ℝ) ≤
            ((2 * M * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hbudget
      have hDlargeReal :
          ((16 * M * Nat.sqrt n : ℕ) : ℝ) ≤ D.card := by exact_mod_cast hDlarge
      dsimp [threshold]
      norm_num at hbudgetReal hDlargeReal ⊢
      have hfactor :
          2 * (M : ℝ) * Nat.sqrt n ≤
            (15 / 64 : ℝ) * (16 * (M : ℝ) * Nat.sqrt n) := by
        have hz : 0 ≤ (M : ℝ) * Nat.sqrt n := by positivity
        nlinarith
      exact hbudgetReal.trans (hfactor.trans
        (mul_le_mul_of_nonneg_left hDlargeReal (by norm_num)))
    have hmatching : RandomCover.HasMatchingAtLeast
        (internalGraph G B₀) S threshold := by
      simpa [Failure] using hnotFailure
    have hforest := hmatching.induce_internalGraph_union_delete
      hB₀ hBT hthreshold
    refine ⟨restrictedParts_isCut hcut, Or.inr ⟨hpartCard, ?_⟩⟩
    simpa using hforest
  have hgood := goodSample_count_of_window_failure G P Failure
    (((1 / 2 : ℝ) - ε / 2) * (2 : ℝ) ^ (2 * n)) (ε / 2)
    hgoodWindow hwindowRaw (by simpa using hfailure)
  convert hgood using 1 <;> simp <;> ring

/-- Parameter-free form of the right one-small-cover count.  The Gaussian
window lemma chooses a single integer scale `K`; the resulting eventual
statement has no analytic side condition and still counts good samples for
the original tailored cut `(A,B)`. -/
theorem exists_scale_eventually_oneSmallCover_right_goodSample_count
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 16 ≤ K ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin (2 * n)))
          (A B T B₀ D : Finset (Fin (2 * n))),
          IsCut A B → n ≤ A.card →
          A.card - n ≤ sqrtCoverThreshold K n →
          T.card = A.card - n → Disjoint B T → B₀ = B ∪ T →
          IsMinimumVertexCoverOn G B₀ D →
          n + 1 ≤ sqrtCoverThreshold K n * (D.card + 1) →
          ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
            (almostBipartiteCount
              (Finset.univ : Finset (Fin (2 * n)))
              (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  obtain ⟨K, M, hM, hKM, hgauss⟩ :=
    OneSmallGaussian.exists_oneSmallCover_gaussian_parameters hε
  refine ⟨K, ?_, eventually_oneSmallCover_right_goodSample_count
    hε hM hKM hgauss⟩
  omega

end

end Erdos622.AlmostBipartiteRegimeCounts
