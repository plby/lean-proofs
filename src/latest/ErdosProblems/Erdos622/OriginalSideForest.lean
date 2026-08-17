/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.TwoLargeForest

/-!
# A sampled linear forest on the original large side

This file supplies the extra forest used in the intermediate-imbalance
subcase of the almost-bipartite argument.  The important point is that the
forest lives on the original side `A`, not on the balanced side obtained by
moving vertices across the cut.
-/

namespace Erdos622.OriginalSideForest

open Filter Finset Real
open scoped BigOperators Topology SimpleGraph

attribute [local instance] Classical.propDecidable

/-- A graph-independent upper bound for the two exceptional proportions in
the original-side sampled Alon argument. -/
noncomputable def failureMajorant (K n : ℕ) : ℝ :=
  4 * (n : ℝ) * exp (-(1 / 16384 : ℝ) * n) +
    2 * exp (-((1 / (K : ℝ)) * Real.sqrt n))

theorem failureMajorant_tendsto_zero {K : ℕ} (hK : 0 < K) :
    Tendsto (failureMajorant K) atTop (nhds 0) := by
  have hfirst := Concentration.tendsto_linear_mul_exp_neg
    (1 / 16384 : ℝ) (by norm_num)
  have hsecond := TwoLargeForest.tendsto_exp_neg_sqrt
    (1 / (K : ℝ)) (by positivity)
  unfold failureMajorant
  convert (hfirst.const_mul 4).add (hsecond.const_mul 2) using 1
  · ext n
    ring
  · norm_num

/-- Uniform sampled-forest estimate on the original larger side of the
almost-bipartite cut.  Once its excess over `n` is larger than the chosen
square-root threshold, all but an arbitrarily small proportion of samples
contain a linear forest with twenty times that excess many edges.

The hypotheses and conclusion deliberately use the original cut `(A,B)`;
this is the form consumed by the final three-forest transfer lemma. -/
theorem eventually_originalSide_linearForest_count
    {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B : Finset (Fin (2 * n))),
        G.IsRegularOfDegree (n + 1) →
        IsAlmostBipartiteCut G A B →
        A.card - n ≤ Nat.sqrt n →
        sqrtCoverThreshold K n < A.card - n →
        ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter
            fun S : Finset (Fin (2 * n)) ↦
              ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
                (restrictedPart S A) (20 * (A.card - n))).card : ℝ)) ≤
          δ * (2 : ℝ) ^ (2 * n) := by
  obtain ⟨D₀, hAlon⟩ :=
    TwoLargeForest.eventually_not_containsLinearForestWith_induce_count_le_of_edge_slack
      (epsilon := (1 / 8 : ℝ)) (by norm_num)
  have hmajor := failureMajorant_tendsto_zero hK
  have hmajorEventually : ∀ᶠ n : ℕ in atTop, failureMajorant K n < δ := by
    rcases Metric.tendsto_atTop.1 hmajor δ hδ with ⟨N, hN⟩
    exact eventually_atTop.2 ⟨N, fun n hn ↦ by
      simpa [Real.dist_eq, abs_of_nonneg (show 0 ≤ failureMajorant K n by
        unfold failureMajorant
        positivity)] using hN n hn⟩
  filter_upwards [hmajorEventually,
      eventually_ge_atTop (max (200 * D₀) 4096)] with n hnmajor hnlarge
  intro G A B hreg hAB _hdUpper hdLower
  let d := A.card - n
  let J := internalGraph G A
  let q := n / 128
  let D := n / 200
  let tDegree : ℝ := (n : ℝ) / 2048
  have hn : 4096 ≤ n := (le_max_right _ _).trans hnlarge
  have hnpos : 0 < n := by omega
  have hnA : n ≤ A.card := by exact_mod_cast hAB.2.1
  have hdpos : 0 < d := by
    dsimp [d]
    omega
  have hmaxReal : Trichotomy.InternalMaxDegree G A
      (TailoredTrichotomy.gamma0 * (2 * n : ℝ)) := by
    rcases hAB.2.2.2.2.2 with hbalanced | hmax
    · dsimp [d] at hdpos
      omega
    · exact hmax
  have hmax : ∀ v, J.degree v ≤ q := by
    dsimp only [J, q]
    exact TwoLargeForest.internalGraph_degree_le_oneTwentyEighth_of_tailored
      G hmaxReal
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.div_pos (by omega) (by norm_num)
  have htDegree : 0 < tDegree := by
    dsimp [tDegree]
    positivity
  have hD₀ : D₀ ≤ D := by
    dsimp [D]
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 200)).2
    simpa [Nat.mul_comm] using (le_max_left (200 * D₀) 4096).trans hnlarge
  have hedgeLower : A.card * (d + 1) ≤ 2 * J.edgeFinset.card := by
    dsimp only [d, J]
    exact TwoLargeForest.large_side_internal_edge_lower G hreg hAB.1 hnA
  have hedge : 0 < J.edgeFinset.card := by
    have hApos : 0 < A.card := hnpos.trans_le hnA
    by_contra hnot
    have hzero : J.edgeFinset.card = 0 := Nat.eq_zero_of_not_pos hnot
    have hlezero : A.card * (d + 1) ≤ 0 := by
      simpa [hzero] using hedgeLower
    have hpositive : 0 < A.card * (d + 1) :=
      Nat.mul_pos hApos (Nat.succ_pos d)
    omega
  have hdegreeMargin : ∀ v,
      (J.degree v : ℝ) / 2 + tDegree ≤ D := by
    intro v
    have hv : (J.degree v : ℝ) ≤ q := by exact_mod_cast hmax v
    have hqcast : (q : ℝ) ≤ (n : ℝ) / 128 := by
      dsimp [q]
      exact Nat.cast_div_le
    have hDlower : (n : ℝ) / 200 - 1 < D := by
      have hlt : n < (D + 1) * 200 := by
        dsimp [D]
        omega
      have hltR : (n : ℝ) < (D + 1) * 200 := by exact_mod_cast hlt
      linarith
    dsimp only [tDegree]
    have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    have hscalar :
        (1 : ℝ) ≤ (31 / 51200 : ℝ) * (n : ℝ) := by
      calc
        (1 : ℝ) ≤ (31 / 51200 : ℝ) * 4096 := by norm_num
        _ ≤ (31 / 51200 : ℝ) * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hnR (by norm_num)
    calc
      (J.degree v : ℝ) / 2 + (n : ℝ) / 2048 ≤
          ((n : ℝ) / 128) / 2 + (n : ℝ) / 2048 := by
        gcongr
        exact hv.trans hqcast
      _ ≤ (n : ℝ) / 200 - 1 := by
        linarith
      _ ≤ (D : ℝ) := le_of_lt hDlower
  have hcapacity :
      ((20 * d : ℕ) : ℝ) *
          ((1 + (1 / 8 : ℝ)) * (D : ℝ) / 2) ≤
        (J.edgeFinset.card : ℝ) / 8 := by
    have hedgeLowerR : (A.card : ℝ) * ((d : ℝ) + 1) ≤
        2 * (J.edgeFinset.card : ℝ) := by exact_mod_cast hedgeLower
    have hnAR : (n : ℝ) ≤ A.card := by exact_mod_cast hnA
    have hDcast : (D : ℝ) ≤ (n : ℝ) / 200 := by
      dsimp [D]
      exact Nat.cast_div_le
    have hdR : (0 : ℝ) ≤ d := by positivity
    push_cast
    nlinarith
  have hraw := hAlon (Fin (2 * n)) J q D (20 * d) tDegree
    hD₀ hq htDegree hedge hmax hdegreeMargin hcapacity
  have hrawAmbient :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter
          fun S : Finset (Fin (2 * n)) ↦
            ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
              (restrictedPart S A) (20 * d)).card : ℝ)) ≤
        ((2 * n : ℝ) * 2 * exp (-2 * tDegree ^ 2 / q) +
          2 * exp (-(J.edgeFinset.card : ℝ) / (64 * q))) *
            (2 : ℝ) ^ (2 * n) := by
    have hsub : (Finset.univ : Finset (Fin (2 * n))).powerset.filter
        (fun S : Finset (Fin (2 * n)) ↦
          ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
            (restrictedPart S A) (20 * d)) ⊆
        (Finset.univ : Finset (Fin (2 * n))).powerset.filter
          (fun S : Finset (Fin (2 * n)) ↦
            ¬ ContainsLinearForestWith (J.induce (S : Set (Fin (2 * n))))
              Finset.univ (20 * d)) := by
      intro S hS
      have hm := Finset.mem_filter.mp hS
      apply Finset.mem_filter.mpr
      refine ⟨hm.1, ?_⟩
      intro hforest
      exact hm.2 (TwoLargeForest.ContainsLinearForestWith.mono_induce_internalGraph
        (G := G) (A := A) (S := S) (r := 20 * d) (by rfl) hforest)
    have hcard := Finset.card_le_card hsub
    have hcardR :
        ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter
            fun S : Finset (Fin (2 * n)) ↦
              ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
                (restrictedPart S A) (20 * d)).card : ℝ)) ≤
          (((Finset.univ : Finset (Fin (2 * n))).powerset.filter
            fun S : Finset (Fin (2 * n)) ↦
              ¬ ContainsLinearForestWith (J.induce (S : Set (Fin (2 * n))))
                Finset.univ (20 * d)).card : ℝ) := by
      exact_mod_cast hcard
    simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using
      hcardR.trans hraw
  have hdegreeExp :
      -2 * tDegree ^ 2 / (q : ℝ) ≤
        -(1 / 16384 : ℝ) * n := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hqNat : q * 128 ≤ n := by
      dsimp [q]
      exact Nat.div_mul_le_self n 128
    have hqBound : (q : ℝ) * 128 ≤ n := by exact_mod_cast hqNat
    dsimp [tDegree]
    field_simp
    nlinarith
  have hedgeExp :
      -(J.edgeFinset.card : ℝ) / (64 * q) ≤
        -((1 / (K : ℝ)) * Real.sqrt n) := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hKReal : (0 : ℝ) < K := by exact_mod_cast hK
    have hqNat : q * 128 ≤ n := by
      dsimp [q]
      exact Nat.div_mul_le_self n 128
    have hqBound : (q : ℝ) * 128 ≤ n := by exact_mod_cast hqNat
    have hedgeLowerR : (A.card : ℝ) * ((d : ℝ) + 1) ≤
        2 * (J.edgeFinset.card : ℝ) := by exact_mod_cast hedgeLower
    have hnAR : (n : ℝ) ≤ A.card := by exact_mod_cast hnA
    have hthresholdReal : Real.sqrt n / K < d := by
      have hsqrtLt : Real.sqrt n < (Nat.sqrt n : ℝ) + 1 := by
        have hs := Nat.lt_succ_sqrt n
        have hsR : (n : ℝ) <
            ((Nat.sqrt n : ℝ) + 1) * ((Nat.sqrt n : ℝ) + 1) := by
          exact_mod_cast hs
        nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n),
          Real.sqrt_nonneg (n : ℝ)]
      have hfloorNat : Nat.sqrt n < d * K := by
        apply (Nat.div_lt_iff_lt_mul hK).mp
        simpa only [sqrtCoverThreshold] using hdLower
      rw [div_lt_iff₀ hKReal]
      have hfloorPlus : (Nat.sqrt n : ℝ) + 1 ≤ d * K := by
        exact_mod_cast hfloorNat
      exact hsqrtLt.trans_le hfloorPlus
    have htarget : (64 * (q : ℝ)) * (Real.sqrt n / K) ≤
        (J.edgeFinset.card : ℝ) := by
      have hdplus : Real.sqrt n / K < (d : ℝ) + 1 := by linarith
      have hnnonneg : (0 : ℝ) ≤ n := by positivity
      have hqtarget : 64 * (q : ℝ) ≤ (n : ℝ) / 2 := by
        nlinarith
      calc
        (64 * (q : ℝ)) * (Real.sqrt n / K) ≤
            ((n : ℝ) / 2) * (Real.sqrt n / K) := by
              apply mul_le_mul_of_nonneg_right hqtarget
              positivity
        _ ≤ ((n : ℝ) / 2) * ((d : ℝ) + 1) := by
              apply mul_le_mul_of_nonneg_left
              · exact hthresholdReal.le.trans (by linarith)
              · positivity
        _ ≤ (J.edgeFinset.card : ℝ) := by nlinarith
    rw [neg_div, neg_le_neg_iff]
    apply (le_div_iff₀
      (mul_pos (by norm_num : (0 : ℝ) < 64) hqR)).2
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htarget
  have hcoef :
      (2 * n : ℝ) * 2 * exp (-2 * tDegree ^ 2 / q) +
          2 * exp (-(J.edgeFinset.card : ℝ) / (64 * q)) ≤
        failureMajorant K n := by
    unfold failureMajorant
    have hdegree := Real.exp_le_exp.mpr hdegreeExp
    have hedge' := Real.exp_le_exp.mpr hedgeExp
    apply add_le_add
    · calc
        (2 * n : ℝ) * 2 * exp (-2 * tDegree ^ 2 / q) =
            4 * (n : ℝ) * exp (-2 * tDegree ^ 2 / q) := by ring
        _ ≤ 4 * (n : ℝ) * exp (-(1 / 16384 : ℝ) * n) :=
          mul_le_mul_of_nonneg_left hdegree (by positivity)
    · exact mul_le_mul_of_nonneg_left hedge' (by norm_num)
  calc
    _ ≤ ((2 * n : ℝ) * 2 * exp (-2 * tDegree ^ 2 / q) +
          2 * exp (-(J.edgeFinset.card : ℝ) / (64 * q))) *
            (2 : ℝ) ^ (2 * n) := by simpa [d] using hrawAmbient
    _ ≤ failureMajorant K n * (2 : ℝ) ^ (2 * n) := by
      exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ δ * (2 : ℝ) ^ (2 * n) := by
      exact mul_le_mul_of_nonneg_right hnmajor.le (by positivity)

end Erdos622.OriginalSideForest
