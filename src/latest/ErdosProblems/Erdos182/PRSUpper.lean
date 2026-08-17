import ErdosProblems.Erdos182.PRSEntry
import ErdosProblems.Erdos182.PRSRatio
import ErdosProblems.Erdos182.PRSRegularization
import ErdosProblems.Erdos182.PRSBalancing
import ErdosProblems.Erdos182.PRSFactor
import ErdosProblems.Erdos182.PRSParameters

/-!
# The bounded-maximum-degree theorem of Pyber--Rődl--Szemerédi

This file assembles the finite entry, ratio-amplification, roof, balancing,
and factor lemmas.  The numerical constants are intentionally disposable;
their only role is to turn the logarithmic density hypothesis into the
integer degree inequalities required by those finite lemmas.
-/

namespace Erdos182

open PRSEntry

namespace PRSUpper

/-- A rounding-safe multiplier for the entry and ratio-amplification steps. -/
def coreConstant {k : ℕ} {η : ℝ} (P : PRSParameters k η) (M : ℕ) : ℕ :=
  16 * P.alpha * ((P.gamma - 1) * M + 8)

lemma coreConstant_pos {k : ℕ} {η : ℝ} (P : PRSParameters k η)
    {M : ℕ} (hM : 0 < M) : 0 < coreConstant P M := by
  have ha : 0 < P.alpha := Nat.zero_lt_of_lt P.alpha_gt_one
  have _hM := hM
  simp only [coreConstant]
  positivity

/-- The chosen multiplier is large enough for the `32 * alpha` threshold in
the ratio-amplification lemma, after the factor four lost in the entry step. -/
lemma ratio_threshold_le_coreConstant {k : ℕ} {η : ℝ}
    (P : PRSParameters k η) (M : ℕ) :
    128 * P.alpha ≤ coreConstant P M := by
  simp only [coreConstant]
  have h : 8 ≤ (P.gamma - 1) * M + 8 := Nat.le_add_left 8 _
  calc
    128 * P.alpha = 16 * P.alpha * 8 := by ring
    _ ≤ 16 * P.alpha * ((P.gamma - 1) * M + 8) :=
      Nat.mul_le_mul_left _ h

/-- The same multiplier dominates the degree needed to put the prescribed
power exponent below the roof-block exponent. -/
lemma exponent_target_le_coreDegree {k ℓ : ℕ} {η : ℝ}
    (P : PRSParameters k η) (M : ℕ) :
    16 * P.alpha * ((P.gamma - 1) * (M * (ℓ + 1)) + 1) ≤
      coreConstant P M * (ℓ + 1) := by
  have hone : 1 ≤ 8 * (ℓ + 1) := by omega
  have hinner :
      (P.gamma - 1) * (M * (ℓ + 1)) + 1 ≤
        ((P.gamma - 1) * M + 8) * (ℓ + 1) := by
    calc
      (P.gamma - 1) * (M * (ℓ + 1)) + 1
          ≤ (P.gamma - 1) * (M * (ℓ + 1)) + 8 * (ℓ + 1) :=
        Nat.add_le_add_left hone _
      _ = ((P.gamma - 1) * M + 8) * (ℓ + 1) := by ring
  simpa [coreConstant, Nat.mul_assoc] using
    Nat.mul_le_mul_left (16 * P.alpha) hinner

/-- Passing through an entry degree `delta₁` and then the floor division by
`4 * alpha` still leaves the entire roof exponent target. -/
lemma target_le_ratioDegree {k ℓ d δ₁ : ℕ} {η : ℝ}
    (P : PRSParameters k η) (M : ℕ)
    (hd : coreConstant P M * (ℓ + 1) ≤ d)
    (hentry : d ≤ 4 * δ₁) :
    (P.gamma - 1) * (M * (ℓ + 1)) + 1 ≤ δ₁ / (4 * P.alpha) := by
  have ha : 0 < P.alpha := Nat.zero_lt_of_lt P.alpha_gt_one
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 4 * P.alpha)).2
  have htarget := exponent_target_le_coreDegree (P := P) (M := M) (ℓ := ℓ)
  have hscaled :
      4 * P.alpha * ((P.gamma - 1) * (M * (ℓ + 1)) + 1) ≤ δ₁ := by
    have h16 :
        16 * P.alpha * ((P.gamma - 1) * (M * (ℓ + 1)) + 1) ≤
          4 * δ₁ := htarget.trans (hd.trans hentry)
    have h4 :
        4 * (4 * P.alpha * ((P.gamma - 1) * (M * (ℓ + 1)) + 1)) ≤
          4 * δ₁ := by
      convert h16 using 1 <;> ring
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hscaled

/-- The cardinal-ratio estimate which turns the switching inequality into
the near-regularity inequality used by the final factor argument. -/
lemma degree_ratio_lt_of_balancing {k a b D : ℕ} {η : ℝ}
    (hk : 1 ≤ k) (hη : 0 < η) (P : PRSParameters k η)
    (ha : 0 < a) (hab : P.alpha * a ≤ b) (hD : P.lambda ≤ D)
    (hbal :
      (((D - 1 : ℕ) : ℝ) * ((P.gamma - P.lambda : ℕ) : ℝ) *
          ((b - a : ℕ) : ℝ)) ≤
        (P.gamma : ℝ) * b *
          (P.beta * (1 + 1 / (P.alpha : ℝ))) * P.lambda) :
    (D : ℝ) / P.lambda < 1 + η := by
  have hαposN : 0 < P.alpha := Nat.zero_lt_of_lt P.alpha_gt_one
  have hlambdaPosN : 0 < P.lambda := by
    exact lt_of_lt_of_le (by omega) P.lambda_ge
  have hγposN : 0 < P.gamma := lt_trans hlambdaPosN P.gamma_gt_lambda
  have hDpos : 0 < D := lt_of_lt_of_le hlambdaPosN hD
  have habStrict : a < b := by
    have haa : a < P.alpha * a := by
      have halphaGt : 1 < P.alpha := P.alpha_gt_one
      have halphaTwo : 2 ≤ P.alpha := by omega
      calc
        a < 2 * a := by omega
        _ ≤ P.alpha * a := Nat.mul_le_mul_right a halphaTwo
    exact haa.trans_le hab
  have hbaNat : 0 < b - a := Nat.sub_pos_of_lt habStrict
  have hgammaLambdaNat : 0 < P.gamma - P.lambda :=
    Nat.sub_pos_of_lt P.gamma_gt_lambda
  have hlambda : (0 : ℝ) < P.lambda := by exact_mod_cast hlambdaPosN
  have hγ : (0 : ℝ) < P.gamma := by exact_mod_cast hγposN
  have hα : (0 : ℝ) < P.alpha := by exact_mod_cast hαposN
  have hαden : (0 : ℝ) < P.alpha - 1 := P.alpha_den_pos
  have hgammaLambda : (0 : ℝ) < (P.gamma - P.lambda : ℕ) := by
    exact_mod_cast hgammaLambdaNat
  have hba : (0 : ℝ) < (b - a : ℕ) := by exact_mod_cast hbaNat
  have hden : (0 : ℝ) <
      ((P.gamma - P.lambda : ℕ) : ℝ) * (b - a : ℕ) :=
    mul_pos hgammaLambda hba
  have hcardRatio :
      (b : ℝ) / ((b - a : ℕ) : ℝ) ≤
        (P.alpha : ℝ) / ((P.alpha : ℝ) - 1) := by
    rw [div_le_div_iff₀ hba hαden]
    have habR : (P.alpha : ℝ) * a ≤ b := by exact_mod_cast hab
    have hsub : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := by
      rw [Nat.cast_sub habStrict.le]
    rw [hsub]
    nlinarith
  have hswitch :
      (((D - 1 : ℕ) : ℝ) / P.lambda) ≤
        ((P.gamma : ℝ) * b *
            (P.beta * (1 + 1 / (P.alpha : ℝ)))) /
          (((P.gamma - P.lambda : ℕ) : ℝ) * (b - a : ℕ)) := by
    rw [div_le_div_iff₀ hlambda hden]
    nlinarith [hbal]
  have hgammaSub :
      (((P.gamma - P.lambda : ℕ) : ℝ)) =
        (P.gamma : ℝ) - P.lambda := by
    rw [Nat.cast_sub P.gamma_gt_lambda.le]
  have hscaleEq :
      ((P.gamma : ℝ) * b *
            (P.beta * (1 + 1 / (P.alpha : ℝ)))) /
          (((P.gamma - P.lambda : ℕ) : ℝ) * (b - a : ℕ)) =
        (P.beta * (1 + 1 / (P.alpha : ℝ))) *
          ((P.gamma : ℝ) / ((P.gamma : ℝ) - P.lambda)) *
          ((b : ℝ) / ((b - a : ℕ) : ℝ)) := by
    rw [hgammaSub]
    field_simp
  have hscaleLe :
      (((D - 1 : ℕ) : ℝ) / P.lambda) ≤
        (P.beta * (((P.alpha : ℝ) + 1) / ((P.alpha : ℝ) - 1))) /
          (1 - (P.lambda : ℝ) / (P.gamma : ℝ)) := by
    rw [hscaleEq] at hswitch
    have hLpos : 0 < P.beta * (1 + 1 / (P.alpha : ℝ)) := by
      have hbpos : 0 < P.beta := lt_trans (by norm_num) P.beta_gt_one
      positivity
    have hgammaFrac :
        (P.gamma : ℝ) / ((P.gamma : ℝ) - P.lambda) =
          1 / (1 - (P.lambda : ℝ) / P.gamma) := by
      field_simp
    have hratioStep :
        (P.beta * (1 + 1 / (P.alpha : ℝ))) *
              ((P.gamma : ℝ) / ((P.gamma : ℝ) - P.lambda)) *
              ((b : ℝ) / ((b - a : ℕ) : ℝ)) ≤
          (P.beta * (1 + 1 / (P.alpha : ℝ))) *
              ((P.gamma : ℝ) / ((P.gamma : ℝ) - P.lambda)) *
              ((P.alpha : ℝ) / ((P.alpha : ℝ) - 1)) := by
      have hgammaPos :
          0 < (P.gamma : ℝ) / ((P.gamma : ℝ) - P.lambda) := by
        rw [hgammaSub.symm]
        positivity
      exact mul_le_mul_of_nonneg_left hcardRatio (mul_nonneg hLpos.le hgammaPos.le)
    refine hswitch.trans (hratioStep.trans_eq ?_)
    rw [hgammaFrac]
    field_simp
  have hDcast : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ D)]
    norm_num
  have hratioDecomp :
      (D : ℝ) / P.lambda =
        1 / (P.lambda : ℝ) + ((D - 1 : ℕ) : ℝ) / P.lambda := by
    rw [hDcast]
    field_simp
    ring
  rw [hratioDecomp]
  have hsum := add_le_add_left hscaleLe (1 / (P.lambda : ℝ))
  exact lt_of_le_of_lt (by simpa [add_comm] using hsum) (P.assembled_ratio_lt hη)

/-- A real ratio within the tolerance selected for `K` is precisely the
integer cross-multiplied inequality needed by the factor theorem. -/
lemma cross_mul_close_of_ratio {K d D : ℕ} (hK : 2 ≤ K) (hd : 0 < d)
    (h : (D : ℝ) / d < 1 + PRSParameters.eta K) :
    (4 * K - 4) * D < (4 * K - 3) * d := by
  have hmNat : 4 ≤ 4 * K := by omega
  have hmPosNat : 0 < 4 * K - 4 := Nat.sub_pos_of_lt (by omega)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < (4 * K - 4 : ℕ) := by exact_mod_cast hmPosNat
  have heta : PRSParameters.eta K = 1 / ((4 * K - 4 : ℕ) : ℝ) := by
    dsimp [PRSParameters.eta]
    rw [Nat.cast_sub hmNat]
    norm_num
  rw [heta] at h
  have hone :
      1 + 1 / ((4 * K - 4 : ℕ) : ℝ) =
        (((4 * K - 4 : ℕ) : ℝ) + 1) / (4 * K - 4 : ℕ) := by
    field_simp
  have hmSucc :
      (((4 * K - 4 : ℕ) : ℝ) + 1) = ((4 * K - 3 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : (4 * K - 4) + 1 = 4 * K - 3)
  rw [hone, hmSucc] at h
  have hcloseR := (div_lt_div_iff₀ hdR hmR).1 h
  have hcloseNat : D * (4 * K - 4) < (4 * K - 3) * d := by
    exact_mod_cast hcloseR
  simpa [Nat.mul_comm] using hcloseNat

/-- Structural form of the PRS theorem.  It retains the final two-sorted
witness, which is useful to downstream arguments that already work with a
bipartite core. -/
theorem prs_upper_bipartite_nat (k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 0 < C ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
        (G : SimpleGraph V) (Delta : ℕ),
        2 ≤ Delta → maximumDegreeNumber G ≤ Delta →
        C * (Nat.log2 Delta + 1) * Fintype.card V ≤ 2 * edgeNumber G →
        ∃ A B : Finset V,
          Disjoint (A : Set V) (B : Set V) ∧
          ∃ H : BipartiteGraph A B,
            H ≤ fromSimpleGraph G A B ∧
            H.ContainsRegularBipartiteSubgraph k := by
  classical
  let K := max 3 k
  have hKthree : 3 ≤ K := by simp [K]
  have hKtwo : 2 ≤ K := by omega
  obtain ⟨P⟩ := PRSParameters.exists_for_degree K hKtwo
  obtain ⟨M, hM, hpow⟩ := exists_pow_mul_log2_add_one_bound P.beta_gt_one
  refine ⟨coreConstant P M, coreConstant_pos P hM, ?_⟩
  intro V instV instDecV instNonemptyV G Delta hDelta hmax hdensity
  let ell := Nat.log2 Delta
  let d := coreConstant P M * (ell + 1)
  have hdpos : 0 < d := mul_pos (coreConstant_pos P hM) (by omega)
  obtain ⟨A, B, hA, hB, hABcard, hAB, H₁, delta₁, hH₁, _hdelta₁eq,
      hdDelta, _hdelta₁d, hdelta₁Delta, hdelta₁pos, hleft₁, _hedges, _hdense⟩ :=
    exists_initial_halfRegular_core G d Delta hdpos hdensity hmax
  have hratioThreshold : 32 * P.alpha ≤ delta₁ := by
    have hC := ratio_threshold_le_coreConstant P M
    have hCd : 128 * P.alpha ≤ d := by
      calc
        128 * P.alpha ≤ coreConstant P M := hC
        _ ≤ coreConstant P M * (ell + 1) := by
          exact Nat.le_mul_of_pos_right _ (by omega)
    have hfour : 4 * (32 * P.alpha) ≤ 4 * delta₁ := by
      calc
        4 * (32 * P.alpha) = 128 * P.alpha := by ring
        _ ≤ d := hCd
        _ ≤ 4 * delta₁ := hdDelta
    exact Nat.le_of_mul_le_mul_left hfour (by omega)
  obtain ⟨A₂, B₂, H₂, hA₂sub, hB₂sub, hH₂, hratio₂⟩ :=
    BipartiteGraph.exists_ratioAmplified_halfRegularSubgraph
      H₁ (Finset.univ : Finset A) (Finset.univ : Finset B)
      delta₁ P.alpha hH₁.2.1 hH₁.2.2.1 hH₁.2.2.2
      (by simpa using hABcard) P.alpha_gt_one.le hratioThreshold
  let delta₂ := delta₁ / (4 * P.alpha)
  have htarget :
      (P.gamma - 1) * (M * (ell + 1)) + 1 ≤ delta₂ := by
    exact target_le_ratioDegree P M (by rfl) hdDelta
  have hgammaPos : 0 < P.gamma := by
    have hlambdaPos : 0 < P.lambda :=
      lt_of_lt_of_le (by omega) P.lambda_ge
    exact lt_trans hlambdaPos P.gamma_gt_lambda
  have hqpos : 1 ≤ M * (ell + 1) := by
    exact Nat.mul_pos hM (by omega)
  have hgammaTarget :
      P.gamma ≤ (P.gamma - 1) * (M * (ell + 1)) + 1 := by
    calc
      P.gamma = (P.gamma - 1) + 1 := by omega
      _ ≤ (P.gamma - 1) * (M * (ell + 1)) + 1 := by
        exact Nat.add_le_add_right
          (Nat.le_mul_of_pos_right (P.gamma - 1) hqpos) 1
  have hgammaDelta₂ : P.gamma ≤ delta₂ := hgammaTarget.trans htarget
  have hdelta₂pos : 0 < delta₂ := lt_of_lt_of_le hgammaPos hgammaDelta₂
  have hA₂ : A₂.Nonempty := by
    obtain ⟨b, hb⟩ := hH₂.2.2.1
    have hdegpos : 0 < H₂.rightDegree b := by
      rw [hH₂.2.2.2 b hb]
      exact hdelta₂pos
    rw [BipartiteGraph.rightDegree, Finset.card_pos] at hdegpos
    obtain ⟨a, ha⟩ := hdegpos
    exact ⟨a, (hH₂.2.1 ((BipartiteGraph.mem_leftNeighbors H₂ a b).mp ha)).1⟩
  have hleft₂ : ∀ a ∈ A₂, H₂.leftDegree a ≤ Delta := by
    intro a _ha
    exact (BipartiteGraph.leftDegree_mono hH₂.1 a).trans (hleft₁ a)
  have hgammaTwo : 2 ≤ P.gamma := by
    calc
      2 ≤ 4 * K - 3 := by omega
      _ ≤ P.lambda := P.lambda_ge
      _ ≤ P.gamma := P.gamma_gt_lambda.le
  have hexponent :
      M * (ell + 1) ≤ (delta₂ - 1) / (P.gamma - 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < P.gamma - 1)).2
    have hmul : (P.gamma - 1) * (M * (ell + 1)) ≤ delta₂ - 1 := by
      omega
    simpa [Nat.mul_comm] using hmul
  have hDeltaPow :
      (Delta : ℝ) ≤ P.beta ^ ((delta₂ - 1) / (P.gamma - 1)) := by
    calc
      (Delta : ℝ) ≤ P.beta ^ (M * (Nat.log2 Delta + 1)) := hpow Delta
      _ ≤ P.beta ^ ((delta₂ - 1) / (P.gamma - 1)) := by
        exact pow_le_pow_right₀ (by linarith [P.beta_gt_one]) hexponent
  have halphaOne : 1 ≤ P.alpha := P.alpha_gt_one.le
  obtain ⟨A₃, B₃, H₃, hH₃H₂, _hA₃sub, _hB₃sub, hH₃supp,
      hA₃, hB₃, hH₃reg, hratio₃, _hratioMono, hleft₃⟩ :=
    hH₂.exists_multiplicativeBlock_regularization hA₂ hgammaTwo
      hgammaDelta₂ halphaOne P.beta_gt_one.le hratio₂ hleft₂ hDeltaPow
  have hcard₃ : A₃.card < B₃.card := by
    have halphaTwo : 2 ≤ P.alpha := P.alpha_gt_one
    have haPos := hA₃.card_pos
    have haa : A₃.card < P.alpha * A₃.card := by
      calc
        A₃.card < 2 * A₃.card := by omega
        _ ≤ P.alpha * A₃.card := Nat.mul_le_mul_right _ halphaTwo
    exact haa.trans_le hratio₃
  have hlambdaPos : 1 ≤ P.lambda := by
    exact (lt_of_lt_of_le (by omega) P.lambda_ge)
  obtain ⟨H₄, B₄, D, hH₄H₃, hH₄supp, hB₄sub, hB₄card,
      hH₄reg, hleft₄, hlambdaD, hbalance⟩ :=
    BipartiteGraph.prs_balancing_real H₃ A₃ B₃ P.gamma P.lambda
      (P.beta * (1 + 1 / (P.alpha : ℝ))) hA₃ hcard₃ hH₃supp
      hH₃reg hlambdaPos P.gamma_gt_lambda hleft₃
  have hbalance' :
      (((D - 1 : ℕ) : ℝ) * ((P.gamma - P.lambda : ℕ) : ℝ) *
          ((B₃.card - A₃.card : ℕ) : ℝ)) ≤
        (P.gamma : ℝ) * B₃.card *
          (P.beta * (1 + 1 / (P.alpha : ℝ))) * P.lambda := by
    simpa only [Nat.cast_mul] using hbalance
  have hnear : (D : ℝ) / P.lambda < 1 + PRSParameters.eta K :=
    degree_ratio_lt_of_balancing (by omega) (PRSParameters.eta_pos hKtwo)
      P hA₃.card_pos hratio₃ hlambdaD hbalance'
  have hclose :
      (4 * K - 4) * D < (4 * K - 3) * P.lambda :=
    cross_mul_close_of_ratio hKtwo (by omega) hnear
  have hDlarge : 4 * max 3 k - 3 ≤ D := by
    change 4 * K - 3 ≤ D
    exact P.lambda_ge.trans hlambdaD
  have hB₄ : B₄.Nonempty := by
    apply Finset.card_pos.mp
    rw [hB₄card]
    exact hA₃.card_pos
  have hregular : H₄.ContainsRegularBipartiteSubgraph k :=
    BipartiteGraph.finalFactorOnPositive H₄ A₃ B₄ hk hH₄supp hA₃
      hB₄ hB₄card.symm hH₄reg hleft₄ hlambdaD
      hDlarge hclose
  refine ⟨A, B, hAB, H₄, ?_, hregular⟩
  exact hH₄H₃.trans (hH₃H₂.trans (hH₂.1.trans hH₁.1))

/-- The Pyber--Rődl--Szemerédi upper bound in a fully discrete form.

The parameter `Delta` is any upper bound for the maximum degree.  Thus the
hypothesis says that the average degree is at least a constant (depending
only on `k`) times `log₂ Delta + 1`.  The conclusion is the literal
`ContainsRegularSubgraph` predicate from `Foundations.lean`. -/
theorem prs_upper_nat (k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 0 < C ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
        (G : SimpleGraph V) (Delta : ℕ),
        2 ≤ Delta → maximumDegreeNumber G ≤ Delta →
        C * (Nat.log2 Delta + 1) * Fintype.card V ≤ 2 * edgeNumber G →
        ContainsRegularSubgraph G k := by
  obtain ⟨C, hC, hmain⟩ := prs_upper_bipartite_nat k hk
  refine ⟨C, hC, ?_⟩
  intro V _instV _instDecV _instNonemptyV G Delta hDelta hmax hdensity
  obtain ⟨A, B, hAB, H, hHG, hH⟩ :=
    hmain G Delta hDelta hmax hdensity
  exact BipartiteGraph.containsRegularSubgraph_of_containsRegularBipartiteSubgraph
    hAB hHG hH

/-- Specialization of `prs_upper_nat` where the degree parameter is the
actual maximum degree of the graph. -/
theorem prs_upper_maximumDegree_nat (k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 0 < C ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
        (G : SimpleGraph V),
        2 ≤ maximumDegreeNumber G →
        C * (Nat.log2 (maximumDegreeNumber G) + 1) * Fintype.card V ≤
            2 * edgeNumber G →
        ContainsRegularSubgraph G k := by
  obtain ⟨C, hC, hmain⟩ := prs_upper_nat k hk
  refine ⟨C, hC, ?_⟩
  intro V _instV _instDecV _instNonemptyV G hDelta hdensity
  exact hmain G (maximumDegreeNumber G) hDelta le_rfl hdensity

end PRSUpper

end Erdos182
