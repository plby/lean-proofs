import ErdosProblems.Erdos88.UnstructuredWindow
import ErdosProblems.Erdos88.StructuredUpperAsymptotic
import ErdosProblems.Erdos88.StructuredLowerAsymptotic

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos88
namespace BoundedWindowAnalytic

/-- The upper bounded-window statement in the complementary low-RLCD branch,
at a prescribed radius. -/
def KSSSBoundedWindowFinStructuredUpperAt (C : ℝ) (B : ℕ) : Prop :=
  ∀ H : ℝ, 0 < H →
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        N ≤ n → RamseyFree C G →
        ∀ (e₀ : ℝ) (c : Fin n → ℝ),
          (∀ v, 0 ≤ c v ∧ c v ≤ H * n) →
          RLCD.regularizedLCD
              (Nat.ceil (100 / unstructuredGamma) : ℕ)
              unstructuredGamma
              (GraphQuadratic.graphEffectiveLinear G c) <
            BooleanSlices.scale n (1 / 2) →
          ∀ x : ℤ,
            Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) ≤
              K * (n : ℝ) ^ (-(3 / 2 : ℝ))

/-- The lower bounded-window statement in the complementary low-RLCD branch,
at a prescribed radius. -/
def KSSSBoundedWindowFinStructuredLowerAt (C : ℝ) (B : ℕ) : Prop :=
  ∀ H A : ℝ, 0 < H → 0 < A →
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ N : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        N ≤ n → RamseyFree C G →
        ∀ (e₀ : ℝ) (c : Fin n → ℝ),
          (∀ v, 0 ≤ c v ∧ c v ≤ H * n) →
          RLCD.regularizedLCD
              (Nat.ceil (100 / unstructuredGamma) : ℕ)
              unstructuredGamma
              (GraphQuadratic.graphEffectiveLinear G c) <
            BooleanSlices.scale n (1 / 2) →
          ∀ x : ℤ,
            |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
                (Probability.perturbedEdgePolynomial G e₀ c)| ≤
                A * (n : ℝ) ^ (3 / 2 : ℝ) →
            kappa * (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
              Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B)

/-- The structured upper estimate can be placed at an integer radius which
also dominates the canonical radius needed by the high-RLCD branch.  The
radius is chosen before `H`, as required by the bounded-window statement. -/
theorem exists_structuredUpperAt_with_unstructuredWindow_le
    (C : ℝ) (hC : 0 < C) :
    ∃ B : ℕ, unstructuredWindowNat C hC ≤ B ∧
      KSSSBoundedWindowFinStructuredUpperAt C B := by
  let gamma : ℝ := unstructuredGamma
  let L : ℝ := (Nat.ceil (100 / unstructuredGamma) : ℕ)
  have hgamma : 0 < gamma := by
    simpa only [gamma] using unstructuredGamma_pos
  have hgammaSmall : gamma < 3 / 800 := by
    norm_num [gamma, unstructuredGamma]
  have hL : 1 ≤ L := by
    have hquot : (1 : ℝ) ≤ 100 / unstructuredGamma := by
      rw [le_div_iff₀ unstructuredGamma_pos]
      norm_num [unstructuredGamma]
    exact hquot.trans (by
      simpa only [L] using Nat.le_ceil (100 / unstructuredGamma))
  obtain ⟨B0, hB0, hupper⟩ :=
    GaussianQuadratic.exists_eventual_graphEffective_smallRLCD_window_upper_threshold
      C gamma L hC hgamma hgammaSmall hL
  let B : ℕ := max (unstructuredWindowNat C hC) (Nat.ceil B0)
  have hcanonical : unstructuredWindowNat C hC ≤ B := by
    exact le_max_left _ _
  refine ⟨B, hcanonical, ?_⟩
  intro H hH
  have hB0B : B0 ≤ (B : ℝ) := by
    exact (Nat.le_ceil B0).trans (by
      exact_mod_cast (le_max_right (unstructuredWindowNat C hC) (Nat.ceil B0)))
  obtain ⟨K, hK, hmain⟩ := hupper (B : ℝ) hB0B H hH
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hmain
  refine ⟨K, hK, N, ?_⟩
  intro n G _instAdj hn hG e₀ c hc hsmall x
  have hsqrtScale : Real.sqrt (n : ℝ) = BooleanSlices.scale n (1 / 2) := by
    rw [Real.sqrt_eq_rpow]
    rfl
  have hsmall' : RLCD.regularizedLCD L gamma
      (GraphQuadratic.graphEffectiveLinear G c) ≤ Real.sqrt n := by
    rw [hsqrtScale]
    exact hsmall.le
  have hbound := hN n hn G c hG hc hsmall' e₀ (x : ℝ)
  calc
    Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
        |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) ≤
        K * BooleanSlices.scale n (-(3 : ℝ) / 2) := by
      simpa only [gamma, L] using hbound
    _ = K * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      unfold BooleanSlices.scale
      congr 2
      ring

/-- Exact remaining bounded-window proposition after the high-RLCD branch:
the low-RLCD estimates must hold at the same canonical radius. -/
def KSSSBoundedWindowFinStructured : Prop :=
  ∀ C : ℝ, ∀ hC : 0 < C,
    ∃ B : ℕ, unstructuredWindowNat C hC ≤ B ∧
      KSSSBoundedWindowFinStructuredUpperAt C B ∧
      KSSSBoundedWindowFinStructuredLowerAt C B

/-- Both structured estimates hold at one integer radius which also
dominates the canonical radius used by the complementary high-RLCD branch. -/
theorem ksssBoundedWindowFinStructured_proof :
    KSSSBoundedWindowFinStructured := by
  intro C hC
  let gamma : ℝ := unstructuredGamma
  let L : ℝ := (Nat.ceil (100 / unstructuredGamma) : ℕ)
  have hgamma : 0 < gamma := by
    simpa only [gamma] using unstructuredGamma_pos
  have hgammaSmall : gamma < 3 / 800 := by
    norm_num [gamma, unstructuredGamma]
  have hL : 1 ≤ L := by
    have hquot : (1 : ℝ) ≤ 100 / unstructuredGamma := by
      rw [le_div_iff₀ unstructuredGamma_pos]
      norm_num [unstructuredGamma]
    exact hquot.trans (by
      simpa only [L] using Nat.le_ceil (100 / unstructuredGamma))
  obtain ⟨Bupper, hBupper, hupper⟩ :=
    GaussianQuadratic.exists_eventual_graphEffective_smallRLCD_window_upper_threshold
      C gamma L hC hgamma hgammaSmall hL
  obtain ⟨Blower, hBlower, hlower⟩ :=
    GaussianQuadratic.exists_eventual_graphEffective_smallRLCD_window_lower_threshold
      C gamma L hC hgamma hgammaSmall hL
  let B : ℕ := max (unstructuredWindowNat C hC)
    (max (Nat.ceil Bupper) (Nat.ceil Blower))
  have hcanonical : unstructuredWindowNat C hC ≤ B := le_max_left _ _
  have hBupperB : Bupper ≤ (B : ℝ) := by
    exact (Nat.le_ceil Bupper).trans (by
      exact_mod_cast ((le_max_left (Nat.ceil Bupper) (Nat.ceil Blower)).trans
        (le_max_right (unstructuredWindowNat C hC)
          (max (Nat.ceil Bupper) (Nat.ceil Blower)))))
  have hBlowerB : Blower ≤ (B : ℝ) := by
    exact (Nat.le_ceil Blower).trans (by
      exact_mod_cast ((le_max_right (Nat.ceil Bupper) (Nat.ceil Blower)).trans
        (le_max_right (unstructuredWindowNat C hC)
          (max (Nat.ceil Bupper) (Nat.ceil Blower)))))
  refine ⟨B, hcanonical, ?_, ?_⟩
  · intro H hH
    obtain ⟨K, hK, hmain⟩ := hupper (B : ℝ) hBupperB H hH
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hmain
    refine ⟨K, hK, N, ?_⟩
    intro n G _instAdj hn hG e₀ c hc hsmall x
    have hsqrtScale : Real.sqrt (n : ℝ) =
        BooleanSlices.scale n (1 / 2) := by
      rw [Real.sqrt_eq_rpow]
      rfl
    have hsmall' : RLCD.regularizedLCD L gamma
        (GraphQuadratic.graphEffectiveLinear G c) ≤ Real.sqrt n := by
      rw [hsqrtScale]
      exact hsmall.le
    have hbound := hN n hn G c hG hc hsmall' e₀ (x : ℝ)
    calc
      Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
          |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) ≤
          K * BooleanSlices.scale n (-(3 : ℝ) / 2) := by
        simpa only [gamma, L] using hbound
      _ = K * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
        unfold BooleanSlices.scale
        congr 2
        ring
  · intro H A hH hA
    obtain ⟨kappa, hkappa, hmain⟩ :=
      hlower (B : ℝ) hBlowerB H A hH hA
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hmain
    refine ⟨kappa, hkappa, N, ?_⟩
    intro n G _instAdj hn hG e₀ c hc hsmall x hx
    have hsqrtScale : Real.sqrt (n : ℝ) =
        BooleanSlices.scale n (1 / 2) := by
      rw [Real.sqrt_eq_rpow]
      rfl
    have hsmall' : RLCD.regularizedLCD L gamma
        (GraphQuadratic.graphEffectiveLinear G c) ≤ Real.sqrt n := by
      rw [hsqrtScale]
      exact hsmall.le
    have hx' : |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G e₀ c)| ≤
          A * BooleanSlices.scale n (3 / 2 : ℝ) := by
      simpa only [BooleanSlices.scale, Real.rpow_eq_pow] using hx
    have hbound := hN n hn G c hG hc hsmall' e₀ (x : ℝ) hx'
    calc
      kappa * (n : ℝ) ^ (-(3 / 2 : ℝ)) =
          kappa * BooleanSlices.scale n (-(3 : ℝ) / 2) := by
        unfold BooleanSlices.scale
        congr 2
        ring
      _ ≤ Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
          |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) := by
        simpa only [gamma, L] using hbound

/-- The high/low regularized-LCD dichotomy assembles the complete finite
bounded-window theorem once the structured branch is supplied. -/
theorem ksssBoundedWindowFin_of_structured
    (hstructured : KSSSBoundedWindowFinStructured) :
    KSSSBoundedWindowFin := by
  intro C hC
  obtain ⟨B, hBcanonical, hlowUpper, hlowLower⟩ := hstructured C hC
  have hB : 0 < B := by
    have hcanonicalPos : 0 < unstructuredWindowNat C hC := by
      dsimp only [unstructuredWindowNat]
      omega
    exact hcanonicalPos.trans_le hBcanonical
  have hhighUpper : KSSSBoundedWindowFinUnstructuredUpperAt C B := by
    exact ksssBoundedWindowFinUnstructuredUpperAt_of_canonical_le
      C hC B hBcanonical
  have hhighLower : KSSSBoundedWindowFinUnstructuredLowerAt C B := by
    exact ksssBoundedWindowFinUnstructuredLowerAt_of_canonical_le
      C hC B hBcanonical
  refine ⟨B, hB, ?_, ?_⟩
  · intro H hH
    obtain ⟨Khigh, hKhigh, Nhigh, hUpperHigh⟩ := hhighUpper H hH
    obtain ⟨Klow, hKlow, Nlow, hUpperLow⟩ := hlowUpper H hH
    let K := Khigh + Klow
    have hK : 0 < K := by dsimp only [K]; positivity
    refine ⟨K, hK, max Nhigh Nlow, ?_⟩
    intro n G _instAdj hn hG e₀ c hc x
    by_cases hLCD : BooleanSlices.scale n (1 / 2) ≤
        RLCD.regularizedLCD
          (Nat.ceil (100 / unstructuredGamma) : ℕ)
          unstructuredGamma
          (GraphQuadratic.graphEffectiveLinear G c)
    · have hbound := hUpperHigh n G (le_max_left _ _ |>.trans hn)
        hG e₀ c hc hLCD x
      have hpow : 0 ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_nonneg (Nat.cast_nonneg n) _
      calc
        Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
            |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) ≤
            Khigh * (n : ℝ) ^ (-(3 / 2 : ℝ)) := hbound
        _ ≤ K * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ hpow
          dsimp only [K]
          linarith
    · have hbound := hUpperLow n G (le_max_right _ _ |>.trans hn)
        hG e₀ c hc (lt_of_not_ge hLCD) x
      have hpow : 0 ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_nonneg (Nat.cast_nonneg n) _
      calc
        Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
            |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) ≤
            Klow * (n : ℝ) ^ (-(3 / 2 : ℝ)) := hbound
        _ ≤ K * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ hpow
          dsimp only [K]
          linarith
  · intro H A hH hA
    obtain ⟨kHigh, hkHigh, Nhigh, hLowerHigh⟩ := hhighLower H A hH hA
    obtain ⟨kLow, hkLow, Nlow, hLowerLow⟩ := hlowLower H A hH hA
    let kappa := min kHigh kLow
    have hkappa : 0 < kappa := by
      dsimp only [kappa]
      exact lt_min hkHigh hkLow
    refine ⟨kappa, hkappa, max Nhigh Nlow, ?_⟩
    intro n G _instAdj hn hG e₀ c hc x hx
    have hpow : 0 ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    by_cases hLCD : BooleanSlices.scale n (1 / 2) ≤
        RLCD.regularizedLCD
          (Nat.ceil (100 / unstructuredGamma) : ℕ)
          unstructuredGamma
          (GraphQuadratic.graphEffectiveLinear G c)
    · have hbound := hLowerHigh n G (le_max_left _ _ |>.trans hn)
        hG e₀ c hc hLCD x hx
      calc
        kappa * (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
            kHigh * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (min_le_left _ _) hpow
        _ ≤ Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
            |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) := hbound
    · have hbound := hLowerLow n G (le_max_right _ _ |>.trans hn)
        hG e₀ c hc (lt_of_not_ge hLCD) x hx
      calc
        kappa * (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
            kLow * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (min_le_right _ _) hpow
        _ ≤ Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
            |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) := hbound

/-- The completed high/low regularized-LCD dichotomy in canonical finite
vertex types. -/
theorem ksssBoundedWindowFin_proof : KSSSBoundedWindowFin :=
  ksssBoundedWindowFin_of_structured ksssBoundedWindowFinStructured_proof

end BoundedWindowAnalytic
end Erdos88
