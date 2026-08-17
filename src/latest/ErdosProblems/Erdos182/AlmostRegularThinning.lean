import ErdosProblems.Erdos182.AlmostRegular

/-!
# Random thinning of an almost-biregular graph

This file proves the finite alteration argument of Janzer--Sudakov,
Lemma 3.7.  All expectations are literal finite weighted sums.
-/

namespace Erdos182

open Finset
open scoped BigOperators NNReal

noncomputable section

namespace BipartiteGraph

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Janzer--Sudakov Lemma 3.7, in an integer form: the returned graph has
average degree at least `d / 2`, and maximum degree at most `4 * L * d`.
-/
theorem exists_randomly_thinned {G : BipartiteGraph A B}
    {A₀ : Finset A} {B₀ : Finset B} {L d : ℕ}
    (hG : G.IsAlmostBiregularOn A₀ B₀ L d) (hL : 0 < L) (hd : 0 < d) :
    ∃ H : BipartiteGraph A B,
      H ≤ G ∧ 0 < H.edgeCount ∧ H.HasAverageDegreeAtLeastHalf d ∧
        ∀ v : A ⊕ B, H.vertexDegree v ≤ 4 * L * d := by
  classical
  rcases hG with ⟨hsupp, hA₀, hB₀, hreg, hdense, hmax⟩
  have hAcard : 0 < A₀.card := Finset.card_pos.mpr hA₀
  have hBcard : 0 < B₀.card := Finset.card_pos.mpr hB₀
  have hedge : G.edgeCount = B₀.card * d :=
    edgeCount_eq_card_mul_of_rightRegularOn hsupp hreg
  have hcards : A₀.card ≤ B₀.card := by
    rw [hedge] at hdense
    exact Nat.le_of_mul_le_mul_left (by simpa [mul_comm] using hdense) hd
  let p : ℝ≥0 := (A₀.card : ℝ≥0) / B₀.card
  have hp : p ≤ 1 := by
    dsimp [p]
    exact (div_le_one (by positivity)).2 (by exact_mod_cast hcards)
  have hpB : p * (B₀.card : ℝ≥0) = A₀.card := by
    dsimp [p]
    exact div_mul_cancel₀ _ (by positivity)
  have hpedge : p * (G.edgeCount : ℝ≥0) = d * A₀.card := by
    rw [hedge]
    push_cast
    calc
      p * ((B₀.card : ℝ≥0) * d) =
          (p * (B₀.card : ℝ≥0)) * d := by ring
      _ = (A₀.card : ℝ≥0) * d := by rw [hpB]
      _ = (d : ℝ≥0) * A₀.card := by ring
  have hdegree (a : A) : p * G.leftDegree a ≤ L * d := by
    by_cases ha : a ∈ A₀
    · dsimp [p]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ≥0) < B₀.card)]
      norm_cast
      simpa [hedge, mul_assoc, mul_left_comm, mul_comm] using hmax a ha
    · have hzero : G.leftDegree a = 0 := by
        rw [leftDegree, Finset.card_eq_zero]
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨b, hb⟩
        exact ha (hsupp ((mem_rightNeighbors G a b).mp hb)).1
      simp [hzero]
  have hLd : 1 ≤ L * d := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hL.ne' hd.ne')
  let M := 4 * L * d
  let w : Finset ↑B₀ → ℝ≥0 := bernoulliWeight p
  let sample : Finset ↑B₀ → ℝ≥0 :=
    fun S => sampledEdgeCount G B₀ S
  let removed : Finset ↑B₀ → ℝ≥0 :=
    fun S => removedEdgeCount G B₀ M S
  let altered : Finset ↑B₀ → ℝ≥0 :=
    fun S => alteredEdgeCount G B₀ M S
  have hw : ∑ S : Finset ↑B₀, w S = 1 := by
    simpa [w] using sum_bernoulliWeight p hp
  have hsample : weightedExpectation w sample = d * A₀.card := by
    rw [show weightedExpectation w sample = p * G.edgeCount by
      simpa [w, sample] using bernoulli_expect_sampledEdgeCount G B₀ hsupp p hp]
    exact hpedge
  have hsecond (a : A) :
      weightedExpectation w
          (fun S : Finset ↑B₀ => (sampledLeftDegree G B₀ a S : ℝ≥0) ^ 2) ≤
        2 * (L * d : ℝ≥0) * (p * G.leftDegree a) := by
    rw [show weightedExpectation w
          (fun S : Finset ↑B₀ => (sampledLeftDegree G B₀ a S : ℝ≥0) ^ 2) =
        p * G.leftDegree a + p ^ 2 * G.leftDegree a * (G.leftDegree a - 1) by
      simpa [w] using bernoulli_expect_sampledLeftDegree_sq G B₀ hsupp p hp a]
    have hsub : (G.leftDegree a - 1 : ℝ≥0) ≤ G.leftDegree a := tsub_le_self
    have hsquare : p ^ 2 * G.leftDegree a * (G.leftDegree a - 1) ≤
        (p * G.leftDegree a) ^ 2 := by
      calc
        p ^ 2 * G.leftDegree a * (G.leftDegree a - 1) ≤
            p ^ 2 * G.leftDegree a * G.leftDegree a := by gcongr
        _ = (p * G.leftDegree a) ^ 2 := by ring
    have hx := hdegree a
    have hLd' : (1 : ℝ≥0) ≤ L * d := by exact_mod_cast hLd
    calc
      p * G.leftDegree a + p ^ 2 * G.leftDegree a * (G.leftDegree a - 1) ≤
          p * G.leftDegree a + (p * G.leftDegree a) ^ 2 :=
        add_le_add (le_refl _) hsquare
      _ ≤ 2 * (L * d : ℝ≥0) * (p * G.leftDegree a) := by
        have hsquare' : (p * G.leftDegree a) ^ 2 ≤
            (L * d : ℝ≥0) * (p * G.leftDegree a) := by
          simpa [pow_two] using
            mul_le_mul_of_nonneg_right hx (by positivity)
        have hlinear : p * G.leftDegree a ≤
            (L * d : ℝ≥0) * (p * G.leftDegree a) := by
          simpa [one_mul] using
            mul_le_mul_of_nonneg_right hLd' (by positivity)
        calc
          p * G.leftDegree a + (p * G.leftDegree a) ^ 2 ≤
              (L * d : ℝ≥0) * (p * G.leftDegree a) +
                (L * d : ℝ≥0) * (p * G.leftDegree a) :=
            add_le_add hlinear hsquare'
          _ = 2 * (L * d : ℝ≥0) * (p * G.leftDegree a) := by ring
  have hsquares :
      ∑ a : A, weightedExpectation w
          (fun S : Finset ↑B₀ => (sampledLeftDegree G B₀ a S : ℝ≥0) ^ 2) ≤
        2 * (L * d : ℝ≥0) * weightedExpectation w sample := by
    calc
      ∑ a : A, weightedExpectation w
          (fun S : Finset ↑B₀ => (sampledLeftDegree G B₀ a S : ℝ≥0) ^ 2) ≤
          ∑ a : A, 2 * (L * d : ℝ≥0) * (p * G.leftDegree a) := by
            exact Finset.sum_le_sum fun a _ => hsecond a
      _ = 2 * (L * d : ℝ≥0) * (p * G.edgeCount) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Finset.mul_sum]
        congr 1
        norm_cast
        exact (edgeCount_eq_sum_leftDegree G).symm
      _ = 2 * (L * d : ℝ≥0) * weightedExpectation w sample := by
        rw [show weightedExpectation w sample = p * G.edgeCount by
          simpa [w, sample] using bernoulli_expect_sampledEdgeCount G B₀ hsupp p hp]
  have hthreshold :
      (M : ℝ≥0) * weightedExpectation w removed ≤
        ∑ a : A, weightedExpectation w
          (fun S : Finset ↑B₀ => (sampledLeftDegree G B₀ a S : ℝ≥0) ^ 2) := by
    simpa [w, removed] using threshold_mul_expect_removed_le_expect_sq_sum G B₀ p M
  have hremoved :
      2 * weightedExpectation w removed ≤ weightedExpectation w sample := by
    have hfac : (0 : ℝ≥0) < 2 * (L * d : ℝ≥0) := by positivity
    have hscaled :
        2 * (L * d : ℝ≥0) * (2 * weightedExpectation w removed) ≤
          2 * (L * d : ℝ≥0) * weightedExpectation w sample := by
      calc
      2 * (L * d : ℝ≥0) * (2 * weightedExpectation w removed) =
          (M : ℝ≥0) * weightedExpectation w removed := by
            simp [M]
            ring
      _ ≤ ∑ a : A, weightedExpectation w
          (fun S : Finset ↑B₀ => (sampledLeftDegree G B₀ a S : ℝ≥0) ^ 2) := hthreshold
      _ ≤ 2 * (L * d : ℝ≥0) * weightedExpectation w sample := hsquares
    by_contra hn
    have hlt : weightedExpectation w sample < 2 * weightedExpectation w removed :=
      lt_of_not_ge hn
    exact (not_lt_of_ge hscaled) (mul_lt_mul_of_pos_left hlt hfac)
  have hdecomp : weightedExpectation w sample =
      weightedExpectation w altered + weightedExpectation w removed := by
    rw [← weightedExpectation_add]
    apply congrArg (weightedExpectation w)
    funext S
    simp only [sample, altered, removed]
    norm_cast
    exact sampledEdgeCount_eq_altered_add_removed G B₀ M S
  have hsample_altered :
      weightedExpectation w sample ≤ 2 * weightedExpectation w altered := by
    rw [hdecomp] at hremoved ⊢
    nlinarith
  have hcard : weightedExpectation w (fun S : Finset ↑B₀ => (S.card : ℝ≥0)) = A₀.card := by
    rw [show weightedExpectation w (fun S : Finset ↑B₀ => (S.card : ℝ≥0)) =
        p * B₀.card by
          simpa [w] using bernoulli_expect_card (α := ↑B₀) p hp]
    exact hpB
  let score : Finset ↑B₀ → ℝ := fun S =>
    4 * alteredEdgeCount G B₀ M S - d * (A₀.card + S.card)
  have hscore : 0 ≤ realWeightedExpectation w score := by
    have hmain : (2 : ℝ≥0) * (d * A₀.card) ≤
        4 * weightedExpectation w altered := by
      calc
        (2 : ℝ≥0) * (d * A₀.card) = 2 * weightedExpectation w sample := by rw [hsample]
        _ ≤ 2 * (2 * weightedExpectation w altered) := by gcongr
        _ = 4 * weightedExpectation w altered := by ring
    have hmainR : (2 : ℝ) * (d * A₀.card) ≤
        4 * (weightedExpectation w altered : ℝ) := by exact_mod_cast hmain
    have heq : realWeightedExpectation w score =
        4 * (weightedExpectation w altered : ℝ) -
          (d : ℝ) * ((A₀.card : ℝ) + (A₀.card : ℝ)) := by
      have hwR : ∑ S : Finset ↑B₀, (w S : ℝ) = 1 := by exact_mod_cast hw
      have halteredR :
          (∑ S : Finset ↑B₀, (w S : ℝ) * alteredEdgeCount G B₀ M S) =
            (weightedExpectation w altered : ℝ) := by
        exact_mod_cast (show weightedExpectation w altered = weightedExpectation w altered from rfl)
      have hcardR :
          (∑ S : Finset ↑B₀, (w S : ℝ) * (S.card : ℝ)) = A₀.card := by
        exact_mod_cast hcard
      have hfirst :
          (∑ S : Finset ↑B₀,
              (w S : ℝ) * 4 * alteredEdgeCount G B₀ M S) =
            4 * (weightedExpectation w altered : ℝ) := by
        calc
          (∑ S : Finset ↑B₀,
              (w S : ℝ) * 4 * alteredEdgeCount G B₀ M S) =
              4 * ∑ S : Finset ↑B₀,
                (w S : ℝ) * alteredEdgeCount G B₀ M S := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro S _
                  ring
          _ = 4 * (weightedExpectation w altered : ℝ) := by rw [halteredR]
      have hfixed :
          (∑ S : Finset ↑B₀, (w S : ℝ) * (d : ℝ) * A₀.card) =
            (d : ℝ) * A₀.card := by
        calc
          (∑ S : Finset ↑B₀, (w S : ℝ) * (d : ℝ) * A₀.card) =
              ((d : ℝ) * A₀.card) * ∑ S : Finset ↑B₀, (w S : ℝ) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro S _
                ring
          _ = (d : ℝ) * A₀.card := by rw [hwR, mul_one]
      have hvariable :
          (∑ S : Finset ↑B₀, (w S : ℝ) * (d : ℝ) * S.card) =
            (d : ℝ) * A₀.card := by
        calc
          (∑ S : Finset ↑B₀, (w S : ℝ) * (d : ℝ) * S.card) =
              (d : ℝ) * ∑ S : Finset ↑B₀, (w S : ℝ) * S.card := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro S _
                ring
          _ = (d : ℝ) * A₀.card := by rw [hcardR]
      unfold realWeightedExpectation score
      simp_rw [mul_sub, mul_add]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have hfirst' :
          (∑ S : Finset ↑B₀,
              (w S : ℝ) * (4 * alteredEdgeCount G B₀ M S)) =
            4 * (weightedExpectation w altered : ℝ) := by
        simpa only [mul_assoc] using hfirst
      have hfixed' :
          (∑ S : Finset ↑B₀,
              (w S : ℝ) * ((d : ℝ) * A₀.card)) =
            (d : ℝ) * A₀.card := by
        simpa only [mul_assoc] using hfixed
      have hvariable' :
          (∑ S : Finset ↑B₀,
              (w S : ℝ) * ((d : ℝ) * S.card)) =
            (d : ℝ) * A₀.card := by
        simpa only [mul_assoc] using hvariable
      rw [hfirst', hfixed', hvariable']
    rw [heq]
    norm_num at hmainR ⊢
    nlinarith
  obtain ⟨S, hS⟩ := exists_realWeightedExpectation_le w hw score
  have hscoreS : 0 ≤ score S := hscore.trans hS
  let H := G.alteredGraph B₀ M S
  refine ⟨H, alteredGraph_le G B₀ M S, ?_, ?_, ?_⟩
  · rw [edgeCount_alteredGraph]
    dsimp [score] at hscoreS
    have hcost : (0 : ℝ) < (d : ℝ) * ((A₀.card : ℝ) + S.card) := by
      positivity
    have hpositive : (0 : ℝ) < alteredEdgeCount G B₀ M S := by
      nlinarith
    exact_mod_cast hpositive
  · unfold HasAverageDegreeAtLeastHalf
    have hsupport := supportCard_le_card_add_card_of_supportedOn
      (alteredGraph_supportedOn G B₀ hsupp M S)
    rw [card_selectedRightVertices] at hsupport
    rw [edgeCount_alteredGraph]
    dsimp [score] at hscoreS
    have hbound : d * (A₀.card + S.card) ≤
        4 * alteredEdgeCount G B₀ M S := by
      exact_mod_cast (sub_nonneg.mp hscoreS)
    exact (Nat.mul_le_mul_left d hsupport).trans hbound
  · intro v
    cases v with
    | inl a =>
        simpa [H, vertexDegree, M] using alteredGraph_leftDegree_le G B₀ M S a
    | inr b =>
        have hb := alteredGraph_rightDegree_le G B₀ M S b
        have hbG : G.rightDegree b ≤ d := by
          by_cases hb₀ : b ∈ B₀
          · exact (hreg b hb₀).le
          · have hz : G.rightDegree b = 0 := by
              rw [rightDegree, Finset.card_eq_zero]
              apply Finset.not_nonempty_iff_eq_empty.mp
              rintro ⟨a, ha⟩
              exact hb₀ (hsupp ((mem_leftNeighbors G a b).mp ha)).2
            simp [hz]
        calc
          H.vertexDegree (Sum.inr b) = H.rightDegree b := rfl
          _ ≤ G.rightDegree b := hb
          _ ≤ d := hbG
          _ = 1 * d := by rw [one_mul]
          _ ≤ (4 * L) * d := Nat.mul_le_mul_right d (by omega)
          _ = 4 * L * d := rfl

end BipartiteGraph

end

end Erdos182
