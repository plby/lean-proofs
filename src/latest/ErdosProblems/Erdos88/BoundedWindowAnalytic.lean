import ErdosProblems.Erdos88.BoundedWindowFin
import ErdosProblems.Erdos88.Esseen
import ErdosProblems.Erdos88.GraphLinearNormalization
import ErdosProblems.Erdos88.QuadraticLemma81
import ErdosProblems.Erdos88.Unstructured

open MeasureTheory
open scoped BigOperators

namespace Erdos88
namespace BoundedWindowAnalytic

open Classical

/-- The finite characteristic function used by the Boolean-slice modules is
the normalized finite characteristic function used by the Fourier modules. -/
lemma booleanFiniteCharacteristic_eq_finCharFun
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (t : ℝ) :
    BooleanSlices.finiteCharacteristic X t = Fourier.finCharFun Ω X t := by
  unfold BooleanSlices.finiteCharacteristic Fourier.finCharFun
    Fourier.finExpectation
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  apply Finset.sum_congr rfl
  intro ω hω
  congr 1
  push_cast
  ring

/-- On the Boolean cube, normalized finite counting probability agrees with
the unbiased Bernoulli product probability. -/
lemma finProbability_finset_eq_eventProbability_half
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset V → Prop) :
    Fourier.finProbability (Finset V) P =
      Probability.eventProbability (1 / 2 : ℝ) P := by
  rw [BoundedWindow.eventProbability_half_eq_card_div]
  unfold Fourier.finProbability
  rw [Fintype.card_finset]
  rw [Nat.cast_pow]
  norm_num

/-- The law of the centered perturbed induced-edge polynomial under the
uniform Boolean-cube measure. -/
noncomputable def graphCenteredLaw {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ) : Measure ℝ :=
  Esseen.finiteUniformLaw (Finset (Fin n)) (fun U ↦
    Probability.perturbedEdgePolynomial G e₀ c U -
      Probability.expectation (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G e₀ c))

/-- The characteristic function of `graphCenteredLaw` is the graph-centered
characteristic function used in the KSSS frequency estimates. -/
lemma charFun_graphCenteredLaw {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ) (t : ℝ) :
    charFun (graphCenteredLaw G e₀ c) t =
      GraphQuadratic.centeredGraphCharacteristic G e₀ c t := by
  rw [graphCenteredLaw, Esseen.charFun_finiteUniformLaw_sub_const]
  unfold GraphQuadratic.centeredGraphCharacteristic
  rw [booleanFiniteCharacteristic_eq_finCharFun]

/-- Closed windows for `graphCenteredLaw` are exactly the corresponding
unbiased Boolean-cube events for the uncentered polynomial. -/
lemma smallBall_graphCenteredLaw {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (eps x : ℝ) :
    Esseen.smallBall (graphCenteredLaw G e₀ c) eps
        (x - Probability.expectation (1 / 2 : ℝ)
          (Probability.perturbedEdgePolynomial G e₀ c)) =
      Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
        |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ eps) := by
  rw [graphCenteredLaw, Esseen.smallBall_finiteUniformLaw_sub_const]
  exact finProbability_finset_eq_eventProbability_half _

/-- The cardinality of a subset, packaged in the finite range `0,...,n`. -/
def subsetCardStatistic (n : ℕ) (U : Finset (Fin n)) : Fin (n + 1) :=
  ⟨U.card, by
    apply Nat.lt_succ_of_le
    simpa using Finset.card_le_card (Finset.subset_univ U)⟩

/-- A cardinality fiber of the Boolean cube is exactly a Boolean slice. -/
def subsetCardFiberEquiv (n : ℕ) (k : Fin (n + 1)) :
    {U : Finset (Fin n) // subsetCardStatistic n U = k} ≃
      BooleanSlices.BooleanSlicePoint (Finset.univ : Finset (Fin n)) k.1 where
  toFun U := ⟨U.1, BooleanSlices.mem_booleanSlice.mpr ⟨Finset.subset_univ _, by
    exact congrArg Fin.val U.2⟩⟩
  invFun U := ⟨U.1, by
    apply Fin.ext
    exact (BooleanSlices.mem_booleanSlice.mp U.2).2⟩
  left_inv U := by cases U; rfl
  right_inv U := by cases U; rfl

/-- Conditioning the uniform Boolean cube by its cardinality transports the
conditional characteristic functions to the corresponding Boolean slices.
Bad cardinalities contribute only their total probability. -/
theorem norm_finCharFun_sq_le_of_card_slices_except {n : ℕ}
    (X : Finset (Fin n) → ℝ) (t : ℝ)
    (Bad : Fin (n + 1) → Prop) [DecidablePred Bad]
    (B eps : ℝ) (hB : 0 ≤ B)
    (hgood : ∀ (k : Fin (n + 1))
      (hk : Nonempty (BooleanSlices.BooleanSlicePoint
        (Finset.univ : Finset (Fin n)) k.1)), ¬Bad k →
      ‖@Fourier.finCharFun
          (BooleanSlices.BooleanSlicePoint
            (Finset.univ : Finset (Fin n)) k.1)
          inferInstance hk (fun U ↦ X U.1) t‖ ^ 2 ≤ B)
    (hbad : Fourier.finProbability (Finset (Fin n))
      (fun U ↦ Bad (subsetCardStatistic n U)) ≤ eps) :
    ‖Fourier.finCharFun (Finset (Fin n)) X t‖ ^ 2 ≤ B + eps := by
  classical
  unfold Fourier.finCharFun
  apply QuadraticCancellation.norm_finExpectation_sq_le_of_fiberwise_except
    _ (subsetCardStatistic n) Bad B eps hB
  · intro U
    rw [Complex.norm_exp]
    simp
  · intro k hk hnot
    let Fiber := {U : Finset (Fin n) // subsetCardStatistic n U = k}
    let Slice := BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) k.1
    let e : Fiber ≃ Slice := subsetCardFiberEquiv n k
    letI : Nonempty Slice := Nonempty.map e hk
    let g : Slice → ℂ := fun U ↦
      Complex.exp ((t * X U.1 : ℝ) * Complex.I)
    have heq :
        Fourier.finExpectation Fiber
            (fun U ↦ Complex.exp ((t * X U.1 : ℝ) * Complex.I)) =
          Fourier.finExpectation Slice g := by
      have hfun :
          (fun U : Fiber ↦ Complex.exp ((t * X U.1 : ℝ) * Complex.I)) =
            fun U ↦ g (e U) := by
        funext U
        rfl
      rw [hfun]
      exact QuadraticCancellation.finExpectation_equiv Fiber Slice e g
    rw [heq]
    have hkGood := hgood k inferInstance hnot
    simpa only [Fourier.finCharFun, Slice, g] using hkGood
  · exact hbad

lemma finProbability_eq_uniformProbability
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    Fourier.finProbability Ω P = Concentration.uniformProbability P := by
  unfold Fourier.finProbability Concentration.uniformProbability
  congr 1

/-- The central cardinality range used to pass from the Boolean cube to the
fixed-size slices in Lemma 8.1. -/
def centralCardinality (n : ℕ) (k : Fin (n + 1)) : Prop :=
  3 * (n : ℝ) / 8 ≤ (k.1 : ℝ) ∧ (k.1 : ℝ) ≤ 5 * n / 8

lemma not_centralCardinality_implies_deviation {n : ℕ}
    (k : Fin (n + 1)) (hk : ¬centralCardinality n k) :
    (n : ℝ) / 8 < |(k.1 : ℝ) - (n : ℝ) / 2| := by
  rw [lt_abs]
  unfold centralCardinality at hk
  by_cases hlow : 3 * (n : ℝ) / 8 ≤ (k.1 : ℝ)
  · left
    have hupp : 5 * (n : ℝ) / 8 < (k.1 : ℝ) := by
      exact lt_of_not_ge (fun h ↦ hk ⟨hlow, h⟩)
    linarith
  · right
    have hlow' : (k.1 : ℝ) < 3 * (n : ℝ) / 8 := lt_of_not_ge hlow
    linarith

/-- A uniform random subset has non-central cardinality with exponentially
small probability. -/
lemma finProbability_not_centralCardinality_le {n : ℕ} (hn : 1 ≤ n) :
    Fourier.finProbability (Finset (Fin n))
        (fun U ↦ ¬centralCardinality n (subsetCardStatistic n U)) ≤
      2 * Real.exp (-(n : ℝ) / 32) := by
  let E : Finset (Fin n) → Prop := fun U ↦
    (n : ℝ) / 8 < |((U ∩ Finset.univ).card : ℝ) -
      ((Finset.univ : Finset (Fin n)).card : ℝ) / 2|
  have hmono :
      Fourier.finProbability (Finset (Fin n))
          (fun U ↦ ¬centralCardinality n (subsetCardStatistic n U)) ≤
        Fourier.finProbability (Finset (Fin n)) E := by
    apply Fourier.finProbability_mono
    intro U hU
    simpa only [E, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      subsetCardStatistic] using
      not_centralCardinality_implies_deviation
        (subsetCardStatistic n U) hU
  have htail := BooleanSlices.uniformProbability_card_inter_two_sided
    (Finset.univ : Finset (Fin n)) ((n : ℝ) / 8) (by positivity)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  calc
    Fourier.finProbability (Finset (Fin n))
        (fun U ↦ ¬centralCardinality n (subsetCardStatistic n U)) ≤
        Fourier.finProbability (Finset (Fin n)) E := hmono
    _ = Concentration.uniformProbability E :=
      finProbability_eq_uniformProbability E
    _ ≤ 2 * Real.exp
        (-2 * ((n : ℝ) / 8) ^ 2 /
          ((Finset.univ : Finset (Fin n)).card : ℝ)) := by
      simpa only [E] using htail
    _ = 2 * Real.exp (-(n : ℝ) / 32) := by
      congr 2
      simp only [Finset.card_univ, Fintype.card_fin]
      field_simp
      ring

/-- Lemma 8.1 averaged over the cardinality of a uniform Boolean-cube
subset.  The exponentially unlikely non-central cardinalities cost only a
fixed factor in the final `n⁻⁵` estimate. -/
theorem ksssLemma81_booleanCube
    (C eta : ℝ) (hC : 0 < C) (heta : 0 < eta)
    (hetaUpper : eta ≤ 3 / 8) :
    ∃ nu : ℝ, 0 < nu ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        RamseyFree C G →
        ∀ (e₀ : ℝ) (coeff : Fin n → ℝ) (t : ℝ),
          (n : ℝ) ^ (-1 + eta) ≤ |t| → |t| ≤ nu →
          ‖Fourier.finCharFun (Finset (Fin n))
              (Probability.perturbedEdgePolynomial G e₀ coeff) t‖ ≤
            2 * (n : ℝ) ^ (-5 : ℝ) := by
  have hetaHalf : eta < 1 / 2 := lt_of_le_of_lt hetaUpper (by norm_num)
  obtain ⟨nu, hnu, Nslice, hslice⟩ :=
    QuadraticCancellation.ksssLemma81 C eta hC heta hetaHalf
  have htailEvent :=
    QuadraticCancellation.eventually_const_mul_exp_neg_const_rpow_le_rpow
      2 (1 / 32) 1 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Ntail, hNtail⟩ := Filter.eventually_atTop.mp htailEvent
  refine ⟨nu, hnu, max (max Nslice Ntail) 1, ?_⟩
  intro n hn G _instAdj hG e₀ coeff t htLower htUpper
  have hnSlice : Nslice ≤ n := (le_max_left Nslice Ntail).trans
    ((le_max_left (max Nslice Ntail) 1).trans hn)
  have hnTail : Ntail ≤ n := (le_max_right Nslice Ntail).trans
    ((le_max_left (max Nslice Ntail) 1).trans hn)
  have hnOne : 1 ≤ n := (le_max_right (max Nslice Ntail) 1).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let X : Finset (Fin n) → ℝ :=
    Probability.perturbedEdgePolynomial G e₀ coeff
  let Bad : Fin (n + 1) → Prop := fun k ↦ ¬centralCardinality n k
  have hbad : Fourier.finProbability (Finset (Fin n))
      (fun U ↦ Bad (subsetCardStatistic n U)) ≤ (n : ℝ) ^ (-10 : ℝ) := by
    have hbinomial := finProbability_not_centralCardinality_le hnOne
    have hdecay := hNtail n hnTail
    have hdecay' : 2 * Real.exp (-(n : ℝ) / 32) ≤
        (n : ℝ) ^ (-10 : ℝ) := by
      convert hdecay using 1 <;> simp only [Real.rpow_one] <;> ring
    have hbinomial' : Fourier.finProbability (Finset (Fin n))
        (fun U ↦ Bad (subsetCardStatistic n U)) ≤
          2 * Real.exp (-(n : ℝ) / 32) := by
      simpa only [Bad] using hbinomial
    exact hbinomial'.trans hdecay'
  have hsq : ‖Fourier.finCharFun (Finset (Fin n)) X t‖ ^ 2 ≤
      (n : ℝ) ^ (-10 : ℝ) + (n : ℝ) ^ (-10 : ℝ) := by
    apply norm_finCharFun_sq_le_of_card_slices_except X t Bad
      ((n : ℝ) ^ (-10 : ℝ)) ((n : ℝ) ^ (-10 : ℝ))
      (Real.rpow_nonneg hnpos.le _)
    · intro k hk hnot
      have hkCentral : centralCardinality n k := Classical.not_not.mp hnot
      have hkLower : eta * (n : ℝ) ≤ (k.1 : ℝ) := by
        calc
          eta * (n : ℝ) ≤ (3 / 8 : ℝ) * n :=
            mul_le_mul_of_nonneg_right hetaUpper hnpos.le
          _ = 3 * (n : ℝ) / 8 := by ring
          _ ≤ (k.1 : ℝ) := hkCentral.1
      have hkUpper : (k.1 : ℝ) ≤ (1 - eta) * n := by
        calc
          (k.1 : ℝ) ≤ 5 * (n : ℝ) / 8 := hkCentral.2
          _ = (1 - (3 / 8 : ℝ)) * n := by ring
          _ ≤ (1 - eta) * n := by
            apply mul_le_mul_of_nonneg_right _ hnpos.le
            linarith
      have hs := hslice n hnSlice G hG k e₀ coeff t
        hkLower hkUpper htLower htUpper
      have hsSq :
          ‖@Fourier.finCharFun
              (BooleanSlices.BooleanSlicePoint
                (Finset.univ : Finset (Fin n)) k.1)
              inferInstance hk
              (fun U ↦ X U.1) t‖ ^ 2 ≤
            ((n : ℝ) ^ (-5 : ℝ)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (Real.rpow_nonneg hnpos.le _)).2 (by simpa only [X] using hs)
      calc
        ‖@Fourier.finCharFun
            (BooleanSlices.BooleanSlicePoint
              (Finset.univ : Finset (Fin n)) k.1)
            inferInstance hk (fun U ↦ X U.1) t‖ ^ 2 ≤
            ((n : ℝ) ^ (-5 : ℝ)) ^ 2 := hsSq
        _ = (n : ℝ) ^ (-10 : ℝ) := by
          rw [pow_two, ← Real.rpow_add hnpos]
          norm_num
    · exact hbad
  have hpow : ((n : ℝ) ^ (-5 : ℝ)) ^ 2 =
      (n : ℝ) ^ (-10 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hnpos]
    norm_num
  have htargetSq : ‖Fourier.finCharFun (Finset (Fin n)) X t‖ ^ 2 ≤
      (2 * (n : ℝ) ^ (-5 : ℝ)) ^ 2 := by
    rw [mul_pow, hpow]
    nlinarith [Real.rpow_nonneg hnpos.le (-10 : ℝ)]
  have htarget := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hnpos.le _))).mp htargetSq
  simpa only [X] using htarget

lemma norm_centeredGraphCharacteristic_eq_finCharFun {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (coeff : Fin n → ℝ) (t : ℝ) :
    ‖GraphQuadratic.centeredGraphCharacteristic G e₀ coeff t‖ =
      ‖Fourier.finCharFun (Finset (Fin n))
        (Probability.perturbedEdgePolynomial G e₀ coeff) t‖ := by
  rw [GraphQuadratic.centeredGraphCharacteristic,
    booleanFiniteCharacteristic_eq_finCharFun, norm_mul, Complex.norm_exp]
  simp

/-- Lemma 8.1 in the exact centered graph-characteristic form consumed by
the unstructured frequency-band assembly. -/
theorem ksssLemma81_centeredGraphCharacteristic
    (C eta : ℝ) (hC : 0 < C) (heta : 0 < eta)
    (hetaUpper : eta ≤ 3 / 8) :
    ∃ nu : ℝ, 0 < nu ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        RamseyFree C G →
        ∀ (e₀ : ℝ) (coeff : Fin n → ℝ) (t : ℝ),
          (n : ℝ) ^ (-1 + eta) ≤ |t| → |t| ≤ nu →
          ‖GraphQuadratic.centeredGraphCharacteristic G e₀ coeff t‖ ≤
            2 * (n : ℝ) ^ (-5 : ℝ) := by
  obtain ⟨nu, hnu, N, hN⟩ :=
    ksssLemma81_booleanCube C eta hC heta hetaUpper
  refine ⟨nu, hnu, N, ?_⟩
  intro n hn G _instAdj hG e₀ coeff t htLower htUpper
  rw [norm_centeredGraphCharacteristic_eq_finCharFun]
  exact @hN n hn G (fun a b ↦ Classical.propDecidable (G.Adj a b))
    hG e₀ coeff t htLower htUpper

end BoundedWindowAnalytic
end Erdos88
