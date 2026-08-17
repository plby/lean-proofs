import ErdosProblems.Erdos622.AlmostBipartiteRegimeCounts
import ErdosProblems.Erdos622.IntermediateImbalance

/-!
# The intermediate-imbalance, one-small-cover regime

When the original cut excess is between `sqrt n / K` and `sqrt n`, neither
one side alone supplies half of all samples.  The large balanced-right cover
handles samples with at least as many right vertices.  The minimum cover of
the original left side handles the complementary orientation.  Their two
windows meet, so the fixed negative Gaussian window used in the small-
imbalance proof is contained in the resulting good window.
-/

open Filter Finset Real
open scoped BigOperators Topology SimpleGraph

namespace Erdos622.AlmostBipartiteRegimeCounts

noncomputable section

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Arithmetic for the window joining the two matching orientations. -/
lemma intermediate_window_bounds
    {n M a b x y : ℕ}
    (hM : 0 < M) (hsum : a + b = 2 * n) (hna : n ≤ a)
    (hx : x ≤ a) (hy : y ≤ b) (hupper : a - n ≤ Nat.sqrt n)
  (hwindow : BinomialCLT.standardizedBinomialPoint (2 * n)
        (x + (b - y)) ∈
      Set.Icc (-(M * Real.sqrt 2))
        ((7 / 8 : ℝ) * ((a - n : ℕ) : ℝ) *
          Real.sqrt 2 / Real.sqrt n)) :
    (x ≤ y → y - x + (a - n) ≤ 2 * M * Nat.sqrt n) ∧
      (y ≤ x → ((x - y : ℕ) : ℝ) ≤
        (15 / 8 : ℝ) * ((a - n : ℕ) : ℝ)) := by
  by_cases hn0 : n = 0
  · subst n
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    subst a
    subst b
    subst x
    subst y
    simp
  let d := a - n
  have ha : a = n + d := by omega
  have ha2n : a ≤ 2 * n := by omega
  have hdle : d ≤ n := by omega
  have hb : b = n - d := by omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
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
  constructor
  · intro hxy
    have hlower := hwindow.1
    unfold BinomialCLT.standardizedBinomialPoint at hlower
    norm_num at hlower
    rw [Nat.cast_sub hy] at hlower
    rw [le_div_iff₀ (mul_pos hsqrt2 hsqrtn)] at hlower
    rw [hnum] at hlower
    have hboundReal : ((y - x + d : ℕ) : ℝ) ≤ M * Real.sqrt n := by
      rw [Nat.cast_add, Nat.cast_sub hxy]
      nlinarith
    have hslt : Real.sqrt n < Nat.sqrt n + 1 :=
      Real.real_sqrt_lt_nat_sqrt_succ
    have hsone : Nat.sqrt n + 1 ≤ 2 * Nat.sqrt n := by omega
    have hcoarse : M * Real.sqrt n < ((2 * M * Nat.sqrt n : ℕ) : ℝ) := by
      have hsoneReal : (Nat.sqrt n : ℝ) + 1 ≤ 2 * Nat.sqrt n := by
        exact_mod_cast hsone
      have hMReal : (0 : ℝ) < M := by exact_mod_cast hM
      push_cast
      nlinarith
    have hfinal := (hboundReal.trans_lt hcoarse).le
    exact_mod_cast hfinal
  · intro hyx
    have hupperWindow := hwindow.2
    unfold BinomialCLT.standardizedBinomialPoint at hupperWindow
    norm_num at hupperWindow
    rw [Nat.cast_sub hy] at hupperWindow
    rw [div_le_iff₀ (mul_pos hsqrt2 hsqrtn)] at hupperWindow
    rw [hnum] at hupperWindow
    change 2 * ((x : ℝ) - y - d) ≤
      (7 / 8 : ℝ) * d * Real.sqrt 2 / Real.sqrt n *
        (Real.sqrt 2 * Real.sqrt n) at hupperWindow
    have hdiff : (x : ℝ) - y ≤ (15 / 8 : ℝ) * d := by
      field_simp at hupperWindow
      nlinarith [hsqrt2sq]
    simpa [Nat.cast_sub hyx, d] using hdiff

/-- A union of two exceptional sample families has at most the sum of their
counts. -/
lemma almostBipartiteCount_or_le
    (P Q : Finset V → Prop) :
    almostBipartiteCount (Finset.univ : Finset V) (fun S ↦ P S ∨ Q S) ≤
      almostBipartiteCount (Finset.univ : Finset V) P +
        almostBipartiteCount (Finset.univ : Finset V) Q := by
  exact Erdos622.almostBipartiteCount_or_le
    (Finset.univ : Finset V) P Q

/-- The forced-right one-small-cover estimate in the intermediate imbalance
range.  The original left cover handles the `A`-majority samples, while the
product-forced balanced-right cover handles the `B`-majority samples after
deleting matching edges incident with the transfer set. -/
theorem eventually_intermediate_oneSmallCover_right_goodSample_count
    {ε : ℝ} (hε : 0 < ε) {K M : ℕ}
    (hM : 0 < M) (hKM : 16 * M < K)
    (hgauss : (1 / 2 : ℝ) - ε / 4 <
      BinomialCLT.gaussianWindowMass (-(M * Real.sqrt 2))
        (-(Real.sqrt 2 / K))) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B E T B₀ D : Finset (Fin (2 * n))),
        G.IsRegularOfDegree (n + 1) →
        IsAlmostBipartiteCut G A B →
        IsMinimumVertexCoverOn G A E →
        sqrtCoverThreshold K n < A.card - n →
        A.card - n ≤ Nat.sqrt n →
        T.card = A.card - n → Disjoint B T → B₀ = B ∪ T →
        IsMinimumVertexCoverOn G B₀ D →
        n + 1 ≤ sqrtCoverThreshold K n * (D.card + 1) →
        ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
          (almostBipartiteCount
            (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  have hK : 0 < K := by omega
  have hab : -(M * Real.sqrt 2) ≤ -(Real.sqrt 2 / K) := by
    have hKReal : (0 : ℝ) < K := by exact_mod_cast hK
    have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hdiv : Real.sqrt 2 / K ≤ M * Real.sqrt 2 := by
      have hone : (1 : ℝ) / K ≤ M :=
        ((div_le_one hKReal).2 hKone).trans hMReal
      have hmul := mul_le_mul_of_nonneg_right hone hsqrt
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    linarith
  have hclt :=
    BinomialCLT.eventually_lt_fairBinomialWindowCount_ratio hab hgauss
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hclt
  have hclt2 : ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 2 : ℝ) - ε / 4 <
        (BinomialCLT.fairBinomialWindowCount (2 * n)
          (-(M * Real.sqrt 2)) (-(Real.sqrt 2 / K)) : ℝ) /
          (2 : ℝ) ^ (2 * n) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    exact hN (2 * n) (by omega)
  have hhallE := eventually_minimumCoverOn_ambient_randomMatching_count_le
    (L := K) (eps := (1 / 64 : ℝ)) (delta := ε / 4)
      hK (by norm_num) (by norm_num) (by positivity)
  have hhallD := eventually_minimumCoverOn_ambient_randomMatching_count_le
    (L := 1) (eps := (1 / 64 : ℝ)) (delta := ε / 4)
      (by omega) (by norm_num) (by norm_num) (by positivity)
  filter_upwards [hclt2, hhallE, hhallD,
      Filter.eventually_ge_atTop 16] with n hnWindow hnHallE hnHallD hn16
  intro G A B E T B₀ D hreg hAB hE hinter hupper hTcard hBT hB₀ hD hprod
  let d := A.card - n
  have hsum : A.card + B.card = 2 * n := by
    simpa using hAB.1.card_add_card
  have hnA : n ≤ A.card := by exact_mod_cast hAB.2.1
  have hEStrong : 8 * (d + 1) ≤ E.card := by
    apply hAB.minimumCover_largeImbalance hreg hE hn16
    simpa [d] using (show 0 < A.card - n by omega)
  have hEsqrt : sqrtCoverThreshold K n ≤ E.card := by
    exact hAB.minimumCover_sqrtThreshold_of_largeImbalance
      hreg hE hn16 (by simpa [d] using hinter)
  have hDlarge : 16 * M * Nat.sqrt n ≤ D.card :=
    coverProductArm_forces_sqrtCover hKM hprod
  have hDsqrt : sqrtCoverThreshold 1 n ≤ D.card := by
    simp only [sqrtCoverThreshold, Nat.div_one]
    calc
      Nat.sqrt n ≤ 16 * M * Nat.sqrt n := by
        have : 1 ≤ 16 * M := by omega
        simpa using Nat.mul_le_mul_right (Nat.sqrt n) this
      _ ≤ D.card := hDlarge
  let thresholdE : ℝ := (1 / 4 - 1 / 64 : ℝ) * E.card
  let thresholdD : ℝ := (1 / 4 - 1 / 64 : ℝ) * D.card
  let P : Finset (Fin (2 * n)) → Prop := fun S ↦
    BinomialCLT.standardizedBinomialPoint (2 * n)
      ((S ∩ A).card + (B.card - (S ∩ B).card)) ∈
        Set.Icc (-(M * Real.sqrt 2)) (-(Real.sqrt 2 / K))
  let FailureE : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ RandomCover.HasMatchingAtLeast (internalGraph G A) S thresholdE
  let FailureD : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ RandomCover.HasMatchingAtLeast (internalGraph G B₀) S thresholdD
  let Failure : Finset (Fin (2 * n)) → Prop := fun S ↦ FailureE S ∨ FailureD S
  have hfailureE :
      (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n))) FailureE : ℝ) ≤
        (ε / 4) * (2 : ℝ) ^ (2 * n) := by
    have h := hnHallE (Fin (2 * n)) G A E hE hEsqrt
    simpa [FailureE, thresholdE, almostBipartiteCount,
      almostBipartiteEvent] using h
  have hfailureD :
      (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n))) FailureD : ℝ) ≤
        (ε / 4) * (2 : ℝ) ^ (2 * n) := by
    have h := hnHallD (Fin (2 * n)) G B₀ D hD hDsqrt
    simpa [FailureD, thresholdD, almostBipartiteCount,
      almostBipartiteEvent] using h
  have hfailure :
      (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n))) Failure : ℝ) ≤
        (ε / 2) * (2 : ℝ) ^ (2 * n) := by
    have hNat := almostBipartiteCount_or_le
      (V := Fin (2 * n)) FailureE FailureD
    have hReal :
        (almostBipartiteCount
            (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ FailureE S ∨ FailureD S) : ℝ) ≤
          (almostBipartiteCount
              (Finset.univ : Finset (Fin (2 * n))) FailureE : ℝ) +
            (almostBipartiteCount
              (Finset.univ : Finset (Fin (2 * n))) FailureD : ℝ) := by
      exact_mod_cast hNat
    dsimp [Failure]
    nlinarith
  have hcountEq :
      almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) P =
        BinomialCLT.fairBinomialWindowCount (2 * n)
          (-(M * Real.sqrt 2)) (-(Real.sqrt 2 / K)) := by
    simpa [P] using cut_difference_window_count hAB.1
      (-(M * Real.sqrt 2)) (-(Real.sqrt 2 / K))
  have hwindowRaw :
      ((1 / 2 : ℝ) - ε / 4) * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n))) P : ℝ) := by
    rw [hcountEq]
    exact le_of_lt ((lt_div_iff₀ (by positivity)).mp hnWindow)
  have hgoodWindow : ∀ S : Finset (Fin (2 * n)), S ⊆ Finset.univ →
      P S → ¬ Failure S → IsKGoodSample G A B S 0 := by
    intro S hSuniv hSP hnotFailure
    have hx : (S ∩ A).card ≤ A.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hy : (S ∩ B).card ≤ B.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hwide : BinomialCLT.standardizedBinomialPoint (2 * n)
        ((S ∩ A).card + (B.card - (S ∩ B).card)) ∈
      Set.Icc (-(M * Real.sqrt 2))
        ((7 / 8 : ℝ) * d * Real.sqrt 2 / Real.sqrt n) := by
      refine ⟨hSP.1, hSP.2.trans ?_⟩
      have hKReal : (0 : ℝ) < K := by exact_mod_cast hK
      have hdnonneg : (0 : ℝ) ≤ d := by positivity
      have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      have hright : 0 ≤ (7 / 8 : ℝ) * d * Real.sqrt 2 / Real.sqrt n := by
        positivity
      have hquot : 0 ≤ Real.sqrt 2 / (K : ℝ) :=
        div_nonneg (Real.sqrt_nonneg _) (by positivity)
      have hleft : -(Real.sqrt 2 / K) ≤ 0 := by linarith
      exact hleft.trans hright
    have hbnds := intermediate_window_bounds hM hsum hnA hx hy
      (by simpa [d] using hupper) (by simpa [d] using hwide)
    have hnotE : ¬ FailureE S := fun h ↦ hnotFailure (Or.inl h)
    have hnotD : ¬ FailureD S := fun h ↦ hnotFailure (Or.inr h)
    rcases le_total (S ∩ A).card (S ∩ B).card with hxy | hyx
    · have hpartCard :
          (restrictedPart S A).card ≤ (restrictedPart S B).card := by
        simpa only [card_restrictedPart_eq_inter] using hxy
      have hloss : (S ∩ T).card ≤ d := by
        calc
          (S ∩ T).card ≤ T.card :=
            Finset.card_le_card Finset.inter_subset_right
          _ = d := by simpa [d] using hTcard
      have hbudget :
          (restrictedPart S B).card - (restrictedPart S A).card +
              (S ∩ T).card ≤ 2 * M * Nat.sqrt n := by
        rw [card_restrictedPart_eq_inter, card_restrictedPart_eq_inter]
        have := hbnds.1 hxy
        omega
      have hthreshold :
          (((restrictedPart S B).card - (restrictedPart S A).card +
              (S ∩ T).card : ℕ) : ℝ) ≤ thresholdD := by
        have hbudgetReal :
            (((restrictedPart S B).card - (restrictedPart S A).card +
              (S ∩ T).card : ℕ) : ℝ) ≤
                ((2 * M * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hbudget
        have hDlargeReal :
            ((16 * M * Nat.sqrt n : ℕ) : ℝ) ≤ D.card := by
          exact_mod_cast hDlarge
        dsimp [thresholdD]
        norm_num at hbudgetReal hDlargeReal ⊢
        have hz : 0 ≤ (M : ℝ) * Nat.sqrt n := by positivity
        have hfactor :
            2 * (M : ℝ) * Nat.sqrt n ≤
              (15 / 64 : ℝ) * (16 * (M : ℝ) * Nat.sqrt n) := by
          nlinarith
        exact hbudgetReal.trans (hfactor.trans
          (mul_le_mul_of_nonneg_left hDlargeReal (by norm_num)))
      have hmatchingD : RandomCover.HasMatchingAtLeast
          (internalGraph G B₀) S thresholdD := by
        simpa [FailureD] using hnotD
      have hforest := hmatchingD.induce_internalGraph_union_delete
        hB₀ hBT hthreshold
      refine ⟨restrictedParts_isCut hAB.1, Or.inr ⟨hpartCard, ?_⟩⟩
      simpa using hforest
    · have hpartCard :
          (restrictedPart S B).card ≤ (restrictedPart S A).card := by
        simpa only [card_restrictedPart_eq_inter] using hyx
      have htarget :
          (((restrictedPart S A).card - (restrictedPart S B).card : ℕ) : ℝ) ≤
            thresholdE := by
        have hb := hbnds.2 hyx
        have hEStrongReal : ((8 * (d + 1) : ℕ) : ℝ) ≤ E.card := by
          exact_mod_cast hEStrong
        dsimp [thresholdE]
        norm_num at hb hEStrongReal ⊢
        have hb' :
            (((restrictedPart S A).card -
              (restrictedPart S B).card : ℕ) : ℝ) ≤
              (15 / 8 : ℝ) * d := by
          simpa only [card_restrictedPart_eq_inter] using hb
        have hdnonneg : (0 : ℝ) ≤ d := by positivity
        exact hb'.trans (by nlinarith)
      have hmatchingE : RandomCover.HasMatchingAtLeast
          (internalGraph G A) S thresholdE := by
        simpa [FailureE] using hnotE
      obtain ⟨F, hFmatching, hFsupport, hFcard⟩ := hmatchingE
      have hmatchingTarget : RandomCover.HasMatchingAtLeast
          (internalGraph G A) S
            (((restrictedPart S A).card -
              (restrictedPart S B).card : ℕ) : ℝ) :=
        ⟨F, hFmatching, hFsupport, htarget.trans hFcard⟩
      refine IsKGoodSample.of_ambient_matching_left hAB.1 hpartCard ?_
      simpa using hmatchingTarget
  have hgood := goodSample_count_of_window_failure G P Failure
    (((1 / 2 : ℝ) - ε / 4) * (2 : ℝ) ^ (2 * n)) (ε / 2)
    hgoodWindow hwindowRaw (by simpa using hfailure)
  have hgood' :
      ((1 / 2 : ℝ) - ε / 4) * (2 : ℝ) ^ (2 * n) -
          (ε / 2) * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
    simpa using hgood
  calc
    ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
        ((1 / 2 : ℝ) - ε / 4) * (2 : ℝ) ^ (2 * n) -
          (ε / 2) * (2 : ℝ) ^ (2 * n) := by
      have hp : 0 ≤ (2 : ℝ) ^ (2 * n) := by positivity
      nlinarith
    _ ≤ (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := hgood'

/-- The complete forced-right product arm for every excess at most
`floor(sqrt n)`.  Below `floor(sqrt n / K)` it uses the one-sided matching
argument; above that cutoff it uses both the original-left and transferred-
right matchings. -/
theorem eventually_sqrtImbalance_oneSmallCover_right_goodSample_count
    {ε : ℝ} (hε : 0 < ε) {K M : ℕ}
    (hM : 0 < M) (hKM : 16 * M < K)
    (hgauss : (1 / 2 : ℝ) - ε / 4 <
      BinomialCLT.gaussianWindowMass (-(M * Real.sqrt 2))
        (-(Real.sqrt 2 / K))) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B E T B₀ D : Finset (Fin (2 * n))),
        G.IsRegularOfDegree (n + 1) →
        IsAlmostBipartiteCut G A B →
        IsMinimumVertexCoverOn G A E →
        A.card - n ≤ Nat.sqrt n →
        T.card = A.card - n → Disjoint B T → B₀ = B ∪ T →
        IsMinimumVertexCoverOn G B₀ D →
        n + 1 ≤ sqrtCoverThreshold K n * (D.card + 1) →
        ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
          (almostBipartiteCount
            (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  have hgaussSmall : (1 / 2 : ℝ) - ε / 2 <
      BinomialCLT.gaussianWindowMass (-(M * Real.sqrt 2))
        (-(Real.sqrt 2 / K)) := by linarith
  have hsmall := eventually_oneSmallCover_right_goodSample_count
    hε hM hKM hgaussSmall
  have hintermediate :=
    eventually_intermediate_oneSmallCover_right_goodSample_count
      hε hM hKM hgauss
  filter_upwards [hsmall, hintermediate] with n hnSmall hnIntermediate
  intro G A B E T B₀ D hreg hAB hE hupper hTcard hBT hB₀ hD hprod
  have hnA : n ≤ A.card := by exact_mod_cast hAB.2.1
  by_cases hd : A.card - n ≤ sqrtCoverThreshold K n
  · exact hnSmall G A B T B₀ D hAB.1 hnA hd hTcard hBT hB₀ hD hprod
  · exact hnIntermediate G A B E T B₀ D hreg hAB hE (by omega)
      hupper hTcard hBT hB₀ hD hprod

/-- A common integer scale for both one-small-cover product arms throughout
the entire transferred range `A.card - n ≤ floor(sqrt n)`. -/
theorem exists_common_scale_eventually_sqrtImbalance_oneSmallCover_counts
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 16 ≤ K ∧
      (∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin (2 * n)))
          (A B E T B₀ D : Finset (Fin (2 * n))),
          G.IsRegularOfDegree (n + 1) →
          IsAlmostBipartiteCut G A B →
          IsMinimumVertexCoverOn G A E →
          A.card - n ≤ Nat.sqrt n →
          T.card = A.card - n → Disjoint B T → B₀ = B ∪ T →
          IsMinimumVertexCoverOn G B₀ D →
          n + 1 ≤ sqrtCoverThreshold K n * (D.card + 1) →
          ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
            (almostBipartiteCount
              (Finset.univ : Finset (Fin (2 * n)))
              (fun S ↦ IsKGoodSample G A B S 0) : ℝ)) ∧
      (∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin (2 * n)))
          (A B T A₀ C : Finset (Fin (2 * n))),
          IsCut A B → n ≤ A.card →
          A.card - n ≤ Nat.sqrt n →
          A₀ = A \ T →
          IsMinimumVertexCoverOn G A₀ C →
          n + 1 ≤ sqrtCoverThreshold K n * (C.card + 1) →
          ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) ≤
            (almostBipartiteCount
              (Finset.univ : Finset (Fin (2 * n)))
              (fun S ↦ IsKGoodSample G A B S 0) : ℝ)) := by
  have hεhalf : 0 < ε / 2 := by positivity
  obtain ⟨K, M, hM, hKM, hnegative⟩ :=
    OneSmallGaussian.exists_oneSmallCover_gaussian_parameters hεhalf
  have hnegative' : (1 / 2 : ℝ) - ε / 4 <
      BinomialCLT.gaussianWindowMass (-(M * Real.sqrt 2))
        (-(Real.sqrt 2 / K)) := by
    nlinarith [hnegative]
  have hK : 16 ≤ K := by omega
  have hpositiveStrong : (1 / 2 : ℝ) - ε / 4 <
      BinomialCLT.gaussianWindowMass 0
        ((K : ℝ) * Real.sqrt 2 / 16) := by
    have hp := positive_gaussianWindow_of_negative hM hKM hnegative
    nlinarith
  have hpositive : (1 / 2 : ℝ) - ε / 2 <
      BinomialCLT.gaussianWindowMass 0
        ((K : ℝ) * Real.sqrt 2 / 16) := by linarith
  exact ⟨K, hK,
    eventually_sqrtImbalance_oneSmallCover_right_goodSample_count
      hε hM hKM hnegative',
    eventually_intermediate_oneSmallCover_left_goodSample_count
      hε hK hpositive⟩

end

end Erdos622.AlmostBipartiteRegimeCounts
