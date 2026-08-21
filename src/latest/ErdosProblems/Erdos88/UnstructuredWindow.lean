import ErdosProblems.Erdos88.GaussianWindow

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos88
namespace BoundedWindowAnalytic

/-- A canonical cutoff supplied by the unstructured frequency package. -/
noncomputable def unstructuredCutoff (C : ℝ) (hC : 0 < C) : ℝ :=
  Classical.choose (exists_cutoff_eventually_frequencyBands_unstructured C hC)

/-- The fixed integer window associated to the canonical cutoff. -/
noncomputable def unstructuredWindowNat (C : ℝ) (hC : 0 < C) : ℕ :=
  Nat.ceil (max 1 (60000 / unstructuredCutoff C hC)) + 1

/-- The upper unstructured conclusion at a prescribed integer radius. -/
def KSSSBoundedWindowFinUnstructuredUpperAt (C : ℝ) (B : ℕ) : Prop :=
  ∀ H : ℝ, 0 < H →
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        N ≤ n → RamseyFree C G →
        ∀ (e₀ : ℝ) (c : Fin n → ℝ),
          (∀ v, 0 ≤ c v ∧ c v ≤ H * n) →
          BooleanSlices.scale n (1 / 2) ≤
            RLCD.regularizedLCD
              (Nat.ceil (100 / unstructuredGamma) : ℕ)
              unstructuredGamma
              (GraphQuadratic.graphEffectiveLinear G c) →
          ∀ x : ℤ,
            Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) ≤
              K * (n : ℝ) ^ (-(3 / 2 : ℝ))

/-- The bounded-window conclusion in the additively unstructured
(`regularizedLCD ≥ √n`) branch. -/
def KSSSBoundedWindowFinUnstructuredUpper : Prop :=
  ∀ C : ℝ, 0 < C →
    ∃ B : ℕ, 0 < B ∧
      KSSSBoundedWindowFinUnstructuredUpperAt C B

/-- The unstructured upper argument only requires the integer radius to be
at least the canonical Fourier cutoff radius. -/
theorem ksssBoundedWindowFinUnstructuredUpperAt_of_canonical_le
    (C : ℝ) (hC : 0 < C) (B : ℕ)
    (hBcanonical : unstructuredWindowNat C hC ≤ B) :
    KSSSBoundedWindowFinUnstructuredUpperAt C B := by
  let nu : ℝ := unstructuredCutoff C hC
  have hspec := Classical.choose_spec
    (exists_cutoff_eventually_frequencyBands_unstructured C hC)
  have hnu : 0 < nu := by
    simpa only [nu, unstructuredCutoff] using hspec.1
  have hpackage := hspec.2
  have hBformula : Nat.ceil (max 1 (60000 / nu)) + 1 ≤ B := by
    simpa only [unstructuredWindowNat, nu] using hBcanonical
  have hB : 0 < B := by omega
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  have hBcast : 60000 / nu ≤ (B : ℝ) := by
    calc
      60000 / nu ≤ max 1 (60000 / nu) := le_max_right _ _
      _ ≤ (Nat.ceil (max 1 (60000 / nu)) : ℕ) := Nat.le_ceil _
      _ ≤ (B : ℕ) := by
        exact_mod_cast (show Nat.ceil (max 1 (60000 / nu)) ≤ B by omega)
  have hcut : 60000 / (B : ℝ) ≤ nu := by
    apply (div_le_iff₀ hBreal).2
    have hscaled := (div_le_iff₀ hnu).mp hBcast
    nlinarith
  change KSSSBoundedWindowFinUnstructuredUpperAt C B
  · intro H hH
    have hpkg := hpackage H hH.le
    dsimp only at hpkg
    obtain ⟨a, alpha, scaleUpper, cLinear, cTail, ha, halpha,
      hscaleUpper, hcLinear, hcTail, hbands⟩ := hpkg
    let scaleLower : ℝ := a / 2
    let Alinear : ℝ := 2 * cLinear / scaleLower
    let Dtail : ℝ := 4 * nu * cTail
    have hscaleLower : 0 < scaleLower := by dsimp only [scaleLower]; positivity
    have hAlinear : 0 ≤ Alinear := by dsimp only [Alinear]; positivity
    have hDtail : 0 ≤ Dtail := by dsimp only [Dtail]; positivity
    have habsorbEvent := eventually_sigma_mul_band_bound_le
      unstructuredGamma scaleUpper Alinear Dtail 1 hscaleUpper.le
      hAlinear hDtail (by norm_num) (by norm_num [unstructuredGamma])
    have hmain : ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          RamseyFree C G →
          ∀ (e₀ : ℝ) (c : Fin n → ℝ),
            (∀ v, 0 ≤ c v ∧ c v ≤ H * n) →
            BooleanSlices.scale n (1 / 2) ≤
              RLCD.regularizedLCD
                (Nat.ceil (100 / unstructuredGamma) : ℕ)
                unstructuredGamma
                (GraphQuadratic.graphEffectiveLinear G c) →
            ∀ x : ℤ,
              Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                  |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) ≤
                ((∑' k : ℤ, Esseen.kernelCellWeight k) *
                    (3 * (B : ℝ)) / scaleLower) *
                  (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      filter_upwards [hbands, habsorbEvent] with n hbandN habsorbN
      intro G _instAdj hG e₀ c hc hLCD x
      have hdec : _instAdj = Classical.decRel G.Adj := Subsingleton.elim _ _
      cases hdec
      letI : DecidableRel G.Adj := Classical.decRel G.Adj
      have hpair := hbandN G e₀ c hG hc hLCD
      let sigma := GraphQuadratic.graphPerturbedSigma G e₀ c
      have hband := hpair.1
      have hsigmaLower : scaleLower * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ sigma := by
        simpa only [scaleLower, sigma] using hpair.2
      have habsorb : sigma *
          ((2 * cLinear / scaleLower) *
              (n : ℝ) ^ (4 * unstructuredGamma - 2) +
            4 * nu * cTail * (n : ℝ) ^ (-5 : ℝ)) ≤ 1 := by
        exact habsorbN sigma hband.sigma_pos.le hband.sigma_upper
      have hFourier := fourierL1Error_le_div_of_scaled_bound
        hband hscaleLower hsigmaLower habsorb
      have hcutUpper : 2 / (B : ℝ) ≤ nu := by
        exact (div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 60000)
          hBreal.le).trans hcut
      have hsmall := smallBall_graphCenteredLaw_le_of_fourierL1
        G e₀ c hband hFourier hBreal hcutUpper
        ((x : ℝ) - Probability.expectation (1 / 2 : ℝ)
          (Probability.perturbedEdgePolynomial G e₀ c))
      have hinv := one_div_sigma_le_rpow
        (lt_trans (by norm_num) hband.one_lt_n) hband.sigma_pos
        hscaleLower hsigmaLower
      calc
        Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
            |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) =
            Esseen.smallBall (graphCenteredLaw G e₀ c) (B : ℝ)
              ((x : ℝ) - Probability.expectation (1 / 2 : ℝ)
                (Probability.perturbedEdgePolynomial G e₀ c)) := by
          symm
          exact smallBall_graphCenteredLaw G e₀ c (B : ℝ) (x : ℝ)
        _ ≤
            (∑' k : ℤ, Esseen.kernelCellWeight k) *
              (2 * (B : ℝ) + (B : ℝ) * 1) / sigma := by
          simpa only [Int.cast_id, Nat.cast_ofNat] using hsmall
        _ = ((∑' k : ℤ, Esseen.kernelCellWeight k) *
              (3 * (B : ℝ))) * (1 / sigma) := by ring
        _ ≤ ((∑' k : ℤ, Esseen.kernelCellWeight k) *
              (3 * (B : ℝ))) *
              ((1 / scaleLower) * (n : ℝ) ^ (-(3 : ℝ) / 2)) := by
          apply mul_le_mul_of_nonneg_left hinv
          exact mul_nonneg (tsum_nonneg Esseen.kernelCellWeight_nonneg) (by positivity)
        _ = ((∑' k : ℤ, Esseen.kernelCellWeight k) *
              (3 * (B : ℝ)) / scaleLower) *
                (n : ℝ) ^ (-(3 / 2 : ℝ)) := by ring
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hmain
    let K : ℝ := (∑' k : ℤ, Esseen.kernelCellWeight k) *
      (3 * (B : ℝ)) / scaleLower
    have hK : 0 < K := by
      dsimp only [K]
      have hmass := Esseen.two_le_kernelCellWeightSum
      positivity
    refine ⟨K, hK, N, ?_⟩
    intro n G _instAdj hn hG e₀ c hc hLCD x
    exact hN n hn G hG e₀ c hc hLCD x

theorem ksssBoundedWindowFinUnstructuredUpperAtCanonical
    (C : ℝ) (hC : 0 < C) :
    KSSSBoundedWindowFinUnstructuredUpperAt C
      (unstructuredWindowNat C hC) :=
  ksssBoundedWindowFinUnstructuredUpperAt_of_canonical_le
    C hC (unstructuredWindowNat C hC) le_rfl

theorem ksssBoundedWindowFinUnstructuredUpper :
    KSSSBoundedWindowFinUnstructuredUpper := by
  intro C hC
  let B := unstructuredWindowNat C hC
  have hB : 0 < B := by
    dsimp only [B, unstructuredWindowNat]
    omega
  exact ⟨B, hB, ksssBoundedWindowFinUnstructuredUpperAtCanonical C hC⟩

/-- The matching lower bounded-window conclusion in the additively
unstructured branch.  The radius is chosen by the same cutoff formula as
in `ksssBoundedWindowFinUnstructuredUpper`. -/
def KSSSBoundedWindowFinUnstructuredLowerAt (C : ℝ) (B : ℕ) : Prop :=
  ∀ H A : ℝ, 0 < H → 0 < A →
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ N : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        N ≤ n → RamseyFree C G →
        ∀ (e₀ : ℝ) (c : Fin n → ℝ),
          (∀ v, 0 ≤ c v ∧ c v ≤ H * n) →
          BooleanSlices.scale n (1 / 2) ≤
            RLCD.regularizedLCD
              (Nat.ceil (100 / unstructuredGamma) : ℕ)
              unstructuredGamma
              (GraphQuadratic.graphEffectiveLinear G c) →
          ∀ x : ℤ,
            |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
                (Probability.perturbedEdgePolynomial G e₀ c)| ≤
                A * (n : ℝ) ^ (3 / 2 : ℝ) →
            kappa * (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
              Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B)

def KSSSBoundedWindowFinUnstructuredLower : Prop :=
  ∀ C : ℝ, 0 < C →
    ∃ B : ℕ, 0 < B ∧
      KSSSBoundedWindowFinUnstructuredLowerAt C B

theorem ksssBoundedWindowFinUnstructuredLowerAtCanonical
    (C : ℝ) (hC : 0 < C) :
    KSSSBoundedWindowFinUnstructuredLowerAt C
      (unstructuredWindowNat C hC) := by
  let nu : ℝ := unstructuredCutoff C hC
  have hspec := Classical.choose_spec
    (exists_cutoff_eventually_frequencyBands_unstructured C hC)
  have hnu : 0 < nu := by
    simpa only [nu, unstructuredCutoff] using hspec.1
  have hpackage := hspec.2
  let B : ℕ := Nat.ceil (max 1 (60000 / nu)) + 1
  have hB : 0 < B := by dsimp only [B]; omega
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  have hBcast : 60000 / nu ≤ (B : ℝ) := by
    calc
      60000 / nu ≤ max 1 (60000 / nu) := le_max_right _ _
      _ ≤ (Nat.ceil (max 1 (60000 / nu)) : ℕ) := Nat.le_ceil _
      _ ≤ (B : ℕ) := by dsimp only [B]; exact_mod_cast Nat.le_add_right _ 1
  have hcut : 60000 / (B : ℝ) ≤ nu := by
    apply (div_le_iff₀ hBreal).2
    have hscaled := (div_le_iff₀ hnu).mp hBcast
    nlinarith
  change KSSSBoundedWindowFinUnstructuredLowerAt C B
  intro H A hH hA
  have hpkg := hpackage H hH.le
  dsimp only at hpkg
  obtain ⟨a, alpha, scaleUpper, cLinear, cTail, ha, halpha,
    hscaleUpper, hcLinear, hcTail, hbands⟩ := hpkg
  let scaleLower : ℝ := a / 2
  let M : ℝ := A / scaleLower
  let base : ℝ := Real.exp (-((M + 1) ^ 2) / 2) / 12
  let cE : ℝ := Esseen.relativeEsseenConstant
  let eta : ℝ := base / (16 * (cE + 1))
  let R : ℝ := max 4 (16 * (cE + 1) / base)
  let eps : ℝ := (B : ℝ) / 30000
  have hscaleLower : 0 < scaleLower := by dsimp only [scaleLower]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hbase : 0 < base := by dsimp only [base]; positivity
  have hcE : 0 ≤ cE := by
    dsimp only [cE]
    exact Esseen.relativeEsseenConstant_nonneg
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hR : 4 ≤ R := by dsimp only [R]; exact le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hcutEps : 2 / eps ≤ nu := by
    dsimp only [eps]
    convert hcut using 1 <;> field_simp <;> norm_num
  have hRbound : 16 * (cE + 1) / base ≤ R := by
    dsimp only [R]
    exact le_max_right _ _
  have hnoiseR : cE * (2 / R) ≤ base / 8 := by
    rw [show cE * (2 / R) = (2 * cE) / R by ring]
    apply (div_le_iff₀ hRpos).2
    have hscaled := mul_le_mul_of_nonneg_left hRbound hbase.le
    have hnorm : base * (16 * (cE + 1) / base) = 16 * (cE + 1) := by
      field_simp [hbase.ne']
    rw [hnorm] at hscaled
    nlinarith
  have hnoiseEta : cE * eta ≤ base / 16 := by
    have hcE1 : 0 < cE + 1 := by linarith
    have hratio : cE / (cE + 1) ≤ 1 := (div_le_one hcE1).2 (by linarith)
    calc
      cE * eta = (base / 16) * (cE / (cE + 1)) := by
        dsimp only [eta]
        field_simp [hcE1.ne']
        <;> ring
      _ ≤ (base / 16) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = base / 16 := mul_one _
  let margin : ℝ := base - cE * (2 / R + eta)
  have hmargin : 0 < margin := by
    dsimp only [margin]
    nlinarith
  let Alinear : ℝ := 2 * cLinear / scaleLower
  let Dtail : ℝ := 4 * nu * cTail
  have hAlinear : 0 ≤ Alinear := by dsimp only [Alinear]; positivity
  have hDtail : 0 ≤ Dtail := by dsimp only [Dtail]; positivity
  have habsorbEvent := eventually_sigma_mul_band_bound_le
    unstructuredGamma scaleUpper Alinear Dtail eta hscaleUpper.le
    hAlinear hDtail heta (by norm_num [unstructuredGamma])
  let sigmaFloor : ℝ := max eps (2 * R * eps * (M + R))
  have hsigmaFloor : 0 ≤ sigmaFloor := by
    dsimp only [sigmaFloor]
    exact le_max_of_le_left heps.le
  have hgrowth := QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    (sigmaFloor / scaleLower) 0 ((3 : ℝ) / 2)
    (div_nonneg hsigmaFloor hscaleLower.le) (by norm_num)
  have hmain : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        RamseyFree C G →
        ∀ (e₀ : ℝ) (c : Fin n → ℝ),
          (∀ v, 0 ≤ c v ∧ c v ≤ H * n) →
          BooleanSlices.scale n (1 / 2) ≤
            RLCD.regularizedLCD
              (Nat.ceil (100 / unstructuredGamma) : ℕ)
              unstructuredGamma
              (GraphQuadratic.graphEffectiveLinear G c) →
          ∀ x : ℤ,
            |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
                (Probability.perturbedEdgePolynomial G e₀ c)| ≤
                A * (n : ℝ) ^ (3 / 2 : ℝ) →
            ((eps * margin) / scaleUpper) *
                (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
              Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) := by
    filter_upwards [hbands, habsorbEvent, hgrowth,
      Filter.eventually_ge_atTop 1] with n hbandN habsorbN hgrowthN hn
    intro G _instAdj hG e₀ c hc hLCD x hx
    have hdec : _instAdj = Classical.decRel G.Adj := Subsingleton.elim _ _
    cases hdec
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    have hpair := hbandN G e₀ c hG hc hLCD
    let sigma := GraphQuadratic.graphPerturbedSigma G e₀ c
    have hband := hpair.1
    have hsigmaLower : scaleLower * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ sigma := by
      simpa only [scaleLower, sigma] using hpair.2
    have habsorb : sigma *
        ((2 * cLinear / scaleLower) *
            (n : ℝ) ^ (4 * unstructuredGamma - 2) +
          4 * nu * cTail * (n : ℝ) ^ (-5 : ℝ)) ≤ eta := by
      exact habsorbN sigma hband.sigma_pos.le hband.sigma_upper
    have hFourier := fourierL1Error_le_div_of_scaled_bound
      hband hscaleLower hsigmaLower habsorb
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsigmaFloorLe : sigmaFloor ≤ sigma := by
      have hgrowthN' : sigmaFloor / scaleLower ≤
          (n : ℝ) ^ ((3 : ℝ) / 2) := by
        simpa only [Real.rpow_zero, mul_one] using hgrowthN
      calc
        sigmaFloor = scaleLower * (sigmaFloor / scaleLower) := by
          field_simp [hscaleLower.ne']
        _ ≤ scaleLower * (n : ℝ) ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hgrowthN' hscaleLower.le
        _ ≤ sigma := hsigmaLower
    have hepssigma : eps ≤ sigma :=
      (le_max_left eps (2 * R * eps * (M + R))).trans hsigmaFloorLe
    have hlarge : 2 * R * eps * (M + R) ≤ sigma :=
      (le_max_right eps (2 * R * eps * (M + R))).trans hsigmaFloorLe
    let center : ℝ := (x : ℝ) - Probability.expectation (1 / 2 : ℝ)
      (Probability.perturbedEdgePolynomial G e₀ c)
    have hcenter : |center| ≤ M * sigma := by
      have hscaled := mul_le_mul_of_nonneg_left hsigmaLower hM
      have hnorm : M * (scaleLower * (n : ℝ) ^ ((3 : ℝ) / 2)) =
          A * (n : ℝ) ^ ((3 : ℝ) / 2) := by
        dsimp only [M]
        field_simp [hscaleLower.ne']
      rw [hnorm] at hscaled
      exact hx.trans hscaled
    have hratioScale :
        2 * (R * eps) * (|center| + R * eps) ≤ sigma ^ 2 := by
      have hReps : R * eps ≤ R * sigma :=
        mul_le_mul_of_nonneg_left hepssigma hRpos.le
      have hsum : |center| + R * eps ≤ (M + R) * sigma := by
        calc
          |center| + R * eps ≤ M * sigma + R * sigma :=
            add_le_add hcenter hReps
          _ = (M + R) * sigma := by ring
      calc
        2 * (R * eps) * (|center| + R * eps) ≤
            (2 * (R * eps)) * ((M + R) * sigma) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (2 * R * eps * (M + R)) * sigma := by ring
        _ ≤ sigma * sigma :=
          mul_le_mul_of_nonneg_right hlarge hband.sigma_pos.le
        _ = sigma ^ 2 := by ring
    have hratio := densityRatioOn_centeredGaussian_three
      hband.sigma_pos heps.le ((by norm_num : (0 : ℝ) ≤ 4).trans hR) hratioScale
    have hsmall := smallBall_graphCenteredLaw_lower_of_fourierL1
      G e₀ c hband hFourier heps hcutEps hepssigma hM hcenter hR hratio
    have hinv := rpow_le_one_div_sigma hnpos hband.sigma_pos
      hscaleUpper hband.sigma_upper
    have hinv' : (1 / scaleUpper) * (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
        1 / sigma := by
      simpa only [sigma, show (-(3 / 2 : ℝ)) = (-(3 : ℝ) / 2) by ring]
        using hinv
    have hcoef : 0 ≤ eps * margin := (mul_pos heps hmargin).le
    have hradius : 30000 * eps = (B : ℝ) := by
      dsimp only [eps]
      field_simp
    calc
      ((eps * margin) / scaleUpper) *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) =
          (eps * margin) *
            ((1 / scaleUpper) * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by ring
      _ ≤ (eps * margin) * (1 / sigma) :=
        mul_le_mul_of_nonneg_left hinv' hcoef
      _ = (eps / sigma) * margin := by ring
      _ ≤ Esseen.smallBall (graphCenteredLaw G e₀ c)
          (30000 * eps) center := by
        simpa only [margin, base, cE] using hsmall
      _ = Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
          |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) := by
        rw [hradius]
        exact smallBall_graphCenteredLaw G e₀ c (B : ℝ) (x : ℝ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hmain
  let kappa : ℝ := (eps * margin) / scaleUpper
  have hkappa : 0 < kappa := by dsimp only [kappa]; positivity
  refine ⟨kappa, hkappa, N, ?_⟩
  intro n G _instAdj hn hG e₀ c hc hLCD x hx
  exact hN n hn G hG e₀ c hc hLCD x hx

/-- Enlarging the canonical integer window preserves the unstructured lower
bound by monotonicity of Bernoulli event probability. -/
theorem ksssBoundedWindowFinUnstructuredLowerAt_of_canonical_le
    (C : ℝ) (hC : 0 < C) (B : ℕ)
    (hBcanonical : unstructuredWindowNat C hC ≤ B) :
    KSSSBoundedWindowFinUnstructuredLowerAt C B := by
  intro H A hH hA
  obtain ⟨kappa, hkappa, N, hcanonical⟩ :=
    ksssBoundedWindowFinUnstructuredLowerAtCanonical C hC H A hH hA
  refine ⟨kappa, hkappa, N, ?_⟩
  intro n G _instAdj hn hG e₀ c hc hLCD x hx
  have hbase := hcanonical n G hn hG e₀ c hc hLCD x hx
  exact hbase.trans (Probability.eventProbability_mono
    (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (fun U hU ↦
      hU.trans (by exact_mod_cast hBcanonical)))

theorem ksssBoundedWindowFinUnstructuredLower :
    KSSSBoundedWindowFinUnstructuredLower := by
  intro C hC
  let B := unstructuredWindowNat C hC
  have hB : 0 < B := by
    dsimp only [B, unstructuredWindowNat]
    omega
  exact ⟨B, hB, ksssBoundedWindowFinUnstructuredLowerAtCanonical C hC⟩

/-- The complete bounded-window theorem in the high-regularized-LCD branch,
with one radius serving both the upper and lower estimates. -/
def KSSSBoundedWindowFinUnstructured : Prop :=
  ∀ C : ℝ, 0 < C →
    ∃ B : ℕ, 0 < B ∧
      KSSSBoundedWindowFinUnstructuredUpperAt C B ∧
      KSSSBoundedWindowFinUnstructuredLowerAt C B

theorem ksssBoundedWindowFinUnstructured :
    KSSSBoundedWindowFinUnstructured := by
  intro C hC
  let B := unstructuredWindowNat C hC
  have hB : 0 < B := by
    dsimp only [B, unstructuredWindowNat]
    omega
  exact ⟨B, hB,
    ksssBoundedWindowFinUnstructuredUpperAtCanonical C hC,
    ksssBoundedWindowFinUnstructuredLowerAtCanonical C hC⟩

end BoundedWindowAnalytic
end Erdos88
