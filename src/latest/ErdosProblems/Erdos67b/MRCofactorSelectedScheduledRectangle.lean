import ErdosProblems.Erdos67b.MRCofactorSelectedAmbient
import ErdosProblems.Erdos67b.MRCofactorSelectedGeometry
import ErdosProblems.Erdos67b.MRSelectedPrimeShiftedCost
import ErdosProblems.Erdos67b.MRCofactorRectangleIdentity
import ErdosProblems.Erdos67b.MRCofactorIntervalAbel

/-!
# Fixed-power selected cofactors on the actual scheduled rectangle

The lower complementary scale, prime disjointness, contour window, and
source block conditions are all discharged before finite Abel summation.
The exponential selected-factor tail is retained explicitly.
-/

open Filter
open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrEventually_selected_scheduled_scale {c delta : ℝ}
    (hc : 0 < c) (hdelta : 0 < delta) (Y₀ : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      Y₀ ^ 2 ≤ X ∧ 1024 ≤ Real.log (X : ℝ) ∧
      4 ≤ delta ^ 2 * Real.log (X : ℝ) ∧ 4 ≤ c * Real.log (X : ℝ) ∧
      Real.sqrt (Real.log (X : ℝ)) < c * Real.log (X : ℝ) ∧
      Real.log (X : ℝ) ^ 2 ≤ (X : ℝ) / 2 := by
  filter_upwards [eventually_ge_atTop (Y₀ ^ 2), eventually_ge_atTop 1,
    EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1024),
    EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop (4 / delta ^ 2)),
    EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop (4 / c)),
    EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop (4 / c ^ 2)),
    MRHalaszBands.eventually_log_pow_div_self_le 2 (by norm_num : (0 : ℝ) < 1 / 2)]
    with X hY hX hlog hd hcL hcSq hheight
  have hLpos : 0 < Real.log (X : ℝ) := by linarith
  have hD := (div_le_iff₀ (sq_pos_of_pos hdelta)).1 hd
  have hC := (div_le_iff₀ hc).1 hcL
  have hCSq := (div_le_iff₀ (sq_pos_of_pos hc)).1 hcSq
  refine ⟨hY, hlog, by nlinarith, by nlinarith, ?_, ?_⟩
  · apply (Real.sqrt_lt' (mul_pos hc hLpos)).2
    have hh := mul_le_mul_of_nonneg_left hCSq hLpos.le
    nlinarith
  · have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hh := (div_le_iff₀ hXR).1 hheight
    nlinarith

theorem mrExists_selected_scheduled_cofactor_rectangle_shifted
    {r shift tau theta epsilon : ℝ} (hr : 0 < r) (hrOne : r ≤ 1)
    (hshift : 0 ≤ shift) (htau : 0 ≤ tau) (htheta : 0 < theta)
    (hpower : (tau + 1) * theta ≤ 1 / 4) (hepsilon : 0 < epsilon) :
    ∃ M₀ X₀ : ℕ, 0 < M₀ ∧ 1 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∀ {eta p₁ q₁ : ℝ}, eta ≤ 1 / 12 → 2 ≤ p₁ → 1 ≤ q₁ →
        2 * p₁ ≤ q₁ → 1 ≤ Real.log q₁ →
        4096 * Real.log q₁ ≤ eta * p₁ →
        Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁ →
      ∀ J : ℕ, mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) →
      ∀ (I : ℕ × ℕ) (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
        (∀ p ∈ A, r * (theta * Real.log (X : ℝ)) ≤ Real.log (p : ℝ)) →
        (∀ p ∈ A, Real.log (p : ℝ) ≤ theta * Real.log (X : ℝ)) →
      ∀ {P Q : ℕ}, 4 ≤ P → P ≤ Q → Q ≤ 2 * P →
        (Q : ℝ) ≤ Real.exp (theta * Real.log (X : ℝ) + 1) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| ≤ (X : ℝ) / 2 →
        ‖logarithmicDirichletPolynomial
          (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I (P, Q) X)
          (mrFiniteCofactorLineCoefficient A f) (-t)‖ ≤
            9 * mrSelectedPrimeShiftedRatioCost r shift * (epsilon + Real.exp (-shift * tau)) := by
  obtain ⟨delta, hdelta, _, M₀, Y₀, hM₀, hY₀, hprefix⟩ :=
    mrExists_ambient_selected_cofactor_prefix_bound hepsilon
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1
    (mrEventually_selected_scheduled_scale (mul_pos hr htheta) hdelta Y₀)
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually
      (eventually_ge_atTop (2 * shift / theta)))
  refine ⟨M₀, max X₁ (max X₂ 1), hM₀,
    (le_max_right X₂ 1).trans (le_max_right X₁ _), ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hbudget hmertens J hupper
    I A hA hlower hAupper P Q hP hPQ hQP hQ f hmul hbound hnonpret t ht
  obtain ⟨hYsquare, hlog, hdeltaLog, ha, hgap, hheight⟩ :=
    hX₁ X ((le_max_left _ _).trans hX)
  have hXtwo : X₂ ≤ X := (le_max_left X₂ 1).trans ((le_max_right X₁ _).trans hX)
  have hXpos : 0 < X := by
    have := (le_max_right X₂ 1).trans ((le_max_right X₁ _).trans hX)
    omega
  have hLpos : 0 < Real.log (X : ℝ) := by linarith
  let b := theta * Real.log (X : ℝ)
  let Y := mrSelectedCofactorLowerScale X
  let K := mrSelectedCofactorFactorCutoff tau b
  have hb : 0 < b := mul_pos htheta hLpos
  have ha' : 4 ≤ r * b := by simpa only [b, mul_assoc] using ha
  have hgap' : Real.sqrt (Real.log (X : ℝ)) < r * b := by
    simpa only [b, mul_assoc] using hgap
  have hY : Y₀ ≤ Y := mrSelectedCofactorLowerScale_ge hYsquare
  have hYpos : 0 < Y := mrSelectedCofactorLowerScale_pos hXpos
  have hYX : Y ≤ X := mrSelectedCofactorLowerScale_le (by omega)
  have hXY := mrSelectedCofactorLowerScale_log hXpos
  have hKpos : 0 < K := mrSelectedCofactorFactorCutoff_pos tau b
  have hPpos : 0 < P := by omega
  have hQpos : 0 < Q := hPpos.trans_le hPQ
  have hpowerX : (tau + 1) * b ≤ Real.log (X : ℝ) / 4 := by
    have hh := mul_le_mul_of_nonneg_right hpower hLpos.le
    dsimp only [b]
    nlinarith
  have hKY : K * Y ≤ X / Q := mrSelectedCofactor_cutoffs_le_rectangle_lower hXpos
    hQpos htau hb.le (by linarith) hpowerX hQ
  have hVpos : 0 < X / Q := (Nat.mul_pos hKpos hYpos).trans_le hKY
  have hQX : Q ≤ X := (Nat.div_pos_iff.mp hVpos).2
  have hU : (2 * X) / P ≤ X := by
    have hh := mrCofactor_rectangle_upper_twice_le (X := X) hP
    omega
  obtain ⟨hB, hdisj, hsmall, hmass, hcutoff, hlarge⟩ :=
    mrScheduledBlocks_cofactor_conditions heta hp hq hpq hlogq hbudget hmertens
      hdelta (hY₀.trans hY) hlog hXY hdeltaLog hupper
  have hAB : ∀ j ∈ Finset.Icc 1 J,
      Disjoint A (primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) := by
    intro j hj
    apply Finset.disjoint_left.mpr
    intro p hpA hpB
    have hpLow := hlower p hpA
    have hpHigh := mrScheduledPrime_log_le_sqrt heta hp hq (by linarith) hlogq
      hbudget hupper hj hpB
    linarith
  let J' := mrScheduledRemainingIndices p₁ q₁ J I
  have hJ' : J' ⊆ Finset.Icc 1 J := mrScheduledRemainingIndices_subset p₁ q₁ J I
  have hwindow : |t| + Real.log (X : ℝ) ^ 2 ≤ X := by linarith
  have hbs : 2 * shift ≤ b := by
    have hh := (div_le_iff₀ htheta).1 (hX₂ X hXtwo)
    dsimp only [b]
    nlinarith
  have hratio : shift / b ≤ 1 / 2 := (div_le_iff₀ hb).2 (by linarith)
  have hsigma : 0 < 1 - shift / b := by linarith
  have hsigmaOne : 1 - shift / b ≤ 1 := by linarith [div_nonneg hshift hb.le]
  have hcost := mrSelected_shifted_euler_rankin_le_ratio A hA hr hrOne hb hshift hbs ha'
    hlower hAupper hepsilon.le (show Real.exp (tau * b) ≤ (K : ℝ) from Nat.le_ceil _)
  have hpref : ∀ Z ∈ Finset.Icc (X / Q) ((2 * X) / P),
      ‖positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J'
        (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) (archimedeanUntwist f t)) Z‖ /
        (Z : ℝ) ≤ mrSelectedPrimeShiftedRatioCost r shift *
          (epsilon + Real.exp (-shift * tau)) := by
    intro Z hZ
    have hZrange := Finset.mem_Icc.mp hZ
    have hh := hprefix hM hY hYX hXY A hA J'
      (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j))
      (fun j hj ↦ (Finset.mem_Icc.mp (hJ' hj)).1)
      (fun j hj ↦ hB j (hJ' hj))
      (fun i hi j hj hij ↦ hdisj (hJ' hi) (hJ' hj) hij)
      (fun j hj ↦ hsmall j (hJ' hj)) (fun j hj ↦ hmass j (hJ' hj))
      (fun j hj ↦ hcutoff j (hJ' hj)) (fun j hj ↦ hlarge j (hJ' hj))
      (fun j hj ↦ hAB j (hJ' hj)) hmul hbound hnonpret t hwindow
      (hZrange.2.trans hU) hKpos (hKY.trans hZrange.1) hsigma hsigmaOne
    rw [mrPositivePrefix_typicalCofactor_untwist_eq]
    exact hh.trans hcost
  rw [mrTypicalCofactorRectangle_polynomial_eq_indexed]
  have hh := mrNorm_cofactor_intervalPolynomial_le_of_untwistedPrefixes A J'
    (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f hVpos
    (mrCofactor_rectangle_endpoints_order hPpos hPQ)
    (mrCofactor_rectangle_upper_le_eight_lower hPpos hPQ hQP hQX) t
    (show 0 ≤ mrSelectedPrimeShiftedRatioCost r shift * (epsilon + Real.exp (-shift * tau)) by
      exact mul_nonneg (mrSelectedPrimeShiftedRatioCost_pos r shift).le (by positivity)) hpref
  simpa only [mrDyadicCofactorRectangle, J', Nat.cast_ofNat, show (8 : ℝ) + 1 = 9 by norm_num,
    mul_assoc] using hh


theorem mrExists_selected_scheduled_cofactor_rectangle
    {r tau theta epsilon : ℝ} (hr : 0 < r) (hrOne : r ≤ 1)
    (htau : 0 ≤ tau) (htheta : 0 < theta)
    (hpower : (tau + 1) * theta ≤ 1 / 4) (hepsilon : 0 < epsilon) :
    ∃ M₀ X₀ : ℕ, 0 < M₀ ∧ 1 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∀ {eta p₁ q₁ : ℝ}, eta ≤ 1 / 12 → 2 ≤ p₁ → 1 ≤ q₁ →
        2 * p₁ ≤ q₁ → 1 ≤ Real.log q₁ →
        4096 * Real.log q₁ ≤ eta * p₁ →
        Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁ →
      ∀ J : ℕ, mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) →
      ∀ (I : ℕ × ℕ) (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
        (∀ p ∈ A, r * (theta * Real.log (X : ℝ)) ≤ Real.log (p : ℝ)) →
        (∀ p ∈ A, Real.log (p : ℝ) ≤ theta * Real.log (X : ℝ)) →
      ∀ {P Q : ℕ}, 4 ≤ P → P ≤ Q → Q ≤ 2 * P →
        (Q : ℝ) ≤ Real.exp (theta * Real.log (X : ℝ) + 1) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t : ℝ, |t| ≤ (X : ℝ) / 2 →
        ‖logarithmicDirichletPolynomial
          (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I (P, Q) X)
          (mrFiniteCofactorLineCoefficient A f) (-t)‖ ≤
            9 * mrSelectedPrimeRatioCost r * (epsilon + Real.exp (-tau)) := by
  simpa only [mrSelectedPrimeShiftedRatioCost, mrSelectedPrimeRatioCost, neg_mul, one_mul] using
    (mrExists_selected_scheduled_cofactor_rectangle_shifted (shift := 1)
      hr hrOne (by norm_num) htau htheta hpower hepsilon)

end

end Erdos67b
