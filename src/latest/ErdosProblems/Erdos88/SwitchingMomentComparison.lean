import ErdosProblems.Erdos88.SwitchingMomentUpper
import ErdosProblems.Erdos88.BoundedWindowFin

open Classical
open scoped BigOperators

namespace Erdos88.Switching

/-- Full KSSS Lemma 13.4 from the fixed-radius bounded-window input. -/
theorem ksssUnbiasedSwitchingMoments_of_boundedWindow
    (hBW : KSSSBoundedWindow) : KSSSUnbiasedSwitchingMoments := by
  intro C A hC hA
  obtain ⟨B, hB, hupperData, hlowerData⟩ :=
    hBW (2 * C) (mul_pos (by norm_num) hC)
  let d := 4 * B + 2
  let D := 2 * d
  have hD : 0 < D := by dsimp only [D, d]; omega
  obtain ⟨rho, delta, hrho, hrho1, hdelta, hdeltaBound,
      Nrich, hrichData⟩ :=
    ksssLemma131 C 1 hC (by norm_num) D hD
  have hdeltaRho : delta ≤ rho :=
    delta_le_rho_of_lemma131_bound hrho hrho1 hdeltaBound
  let base := delta ^ (1 / rho)
  let etaPrivate := rho * delta * base
  have hbase : 0 < base := by dsimp only [base]; positivity
  have hetaPrivate : 0 < etaPrivate := by
    dsimp only [etaPrivate]
    positivity
  obtain ⟨kappa, hkappa, Nstate, hstateData⟩ :=
    exists_uniform_richTupleClass_state_lower_of_data
      C B hlowerData delta base rho A d
      hC hdelta hbase hrho hA
  obtain ⟨Npair, hpairData⟩ := Filter.eventually_atTop.1
    eventually_switchingPairs_large_from_lemma131_sizes
  obtain ⟨Nsmall, hsmallData⟩ := Filter.eventually_atTop.1
    (eventually_switchingTuple_good_smallness D)
  let CPrivate := canonicalPrivateQuadraticConstant etaPrivate B d
  let c₀ := 1 / 2 * canonicalFirstExposureRate d * kappa
  let z := Real.exp (-8 * CPrivate) / 8
  let lower := c₀ / 2 * z ^ d
  have hCPrivate : 0 < CPrivate := by
    dsimp only [CPrivate]
    exact canonicalPrivateQuadraticConstant_pos hetaPrivate B d
  have hc₀ : 0 < c₀ := by
    dsimp only [c₀]
    exact mul_pos (mul_pos (by norm_num) (canonicalFirstExposureRate_pos d))
      hkappa
  have hz : 0 < z := by dsimp only [z]; positivity
  have hz1 : z ≤ 1 := by
    have hexp : Real.exp (-8 * CPrivate) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    dsimp only [z]
    linarith [Real.exp_pos (-8 * CPrivate)]
  have hlower : 0 < lower := by dsimp only [lower]; positivity
  let gamma := canonicalUpperFiberRate d rho delta base
  have hgamma : 0 < gamma :=
    canonicalUpperFiberRate_pos d hrho hdelta hbase
  have hdeltaBound' : delta <
      rho ^ 3 / (3 : ℝ) ^ (2 * d + 1) := by
    simpa only [D] using hdeltaBound
  have hgaps := canonicalUpperFiberRate_gaps d hrho hrho1 hdelta hbase
    hdeltaBound'
  obtain ⟨K₀, hK₀, Nwindow, hwindowData⟩ :=
    exists_uniform_switchingConditional_window_upper_of_data
      (B := B) C delta base hupperData hC hdelta hbase
  obtain ⟨Nparam, hparamData⟩ := Filter.eventually_atTop.1
    (eventually_switchingUpper_parameter_bounds d rho delta base gamma
      hrho hdelta hbase hgamma hgaps.1 hgaps.2)
  obtain ⟨Nratio, hratioData⟩ := Filter.eventually_atTop.1
    (eventually_switchingDegeneracy_ratio d)
  let fiberRate := gamma / 2
  let R := max 1 (2 / Real.sqrt fiberRate)
  let upper := ((d + 1 : ℕ) : ℝ) * K₀ * R ^ d
  have hfiberRate : 0 < fiberRate := by dsimp only [fiberRate]; positivity
  have hR : 1 ≤ R := le_max_left _ _
  have hupper : 0 < upper := by
    dsimp only [upper]
    positivity
  refine ⟨B, lower, upper, hlower, hupper,
    max 1 (max Nrich (max Nstate (max Npair (max Nsmall
      (max Nwindow (max Nparam Nratio)))))), ?_⟩
  intro n G hn hG x hx
  have hn1 : 1 ≤ n := by omega
  have hnRich : Nrich ≤ n := by omega
  have hnState : Nstate ≤ n := by omega
  have hnPair : Npair ≤ n := by omega
  have hnSmall : Nsmall ≤ n := by omega
  have hnWindow : Nwindow ≤ n := by omega
  have hnParam : Nparam ≤ n := by omega
  have hnRatio : Nratio ≤ n := by omega
  obtain ⟨S, S₀, hSS₀, hS, hS₀, hrich, hcommon, hdegree⟩ :=
    hrichData n hnRich G hG (fun _ ↦ 0) (by
      intro v
      constructor <;> norm_num)
  let q := switchingThreshold rho S₀
  let T := switchingPairs G S S₀ q
  have hTlarge : (S.card : ℝ) * (n : ℝ) ^ (12 / 25 : ℝ) / 2 ≤
      (T.card : ℝ) := by
    simpa only [T, q] using
      hpairData n hnPair G S S₀ delta rho hSS₀ hS hrich
        hrho hrho1.le hdeltaRho
  have hTambient : (n : ℝ) ^ (24 / 25 : ℝ) / 4 ≤
      (T.card : ℝ) :=
    ambient_switchingPairs_lower_of_source_bounds (by omega) hS hTlarge
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hSp : 0 < (S.card : ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hS
  have hTp : 0 < (T.card : ℝ) := by
    have hleft : 0 < (S.card : ℝ) *
        (n : ℝ) ^ (12 / 25 : ℝ) / 2 := by positivity
    exact hleft.trans_le hTlarge
  have hS₀n : (S₀.card : ℝ) ≤ n := by
    exact_mod_cast (show S₀.card ≤ n by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ S₀))
  let codeBound := ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊
  have hcode : (S₀.card : ℝ) ^ (1 / 5 : ℝ) ≤ codeBound := by
    calc
      (S₀.card : ℝ) ^ (1 / 5 : ℝ) ≤
          (n : ℝ) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hS₀n (by norm_num)
      _ ≤ codeBound := by
        dsimp only [codeBound]
        exact_mod_cast Nat.le_ceil _
  let richFiberSize := Nat.ceil (delta * (S₀.card : ℝ))
  let halaszFiberSize := Nat.floor (gamma * (n : ℝ))
  let deletionBudget := 3 ^ d * halaszFiberSize
  have hparams := hparamData n hnParam S₀.card
    (by simpa only [base] using hS₀)
  change 0 < richFiberSize ∧ 0 < halaszFiberSize ∧
      fiberRate * n ≤ halaszFiberSize ∧
      ((deletionBudget + 2 : ℕ) : ℝ) ≤ rho * richFiberSize ∧
      delta * S₀.card ≤ richFiberSize ∧
      ∀ s : ℕ, s ≤ d →
        3 ^ s * (halaszFiberSize - 1) ≤ deletionBudget ∧
        ∀ k : ℕ, k ≤ s →
          3 ^ (s - k) * richFiberSize + deletionBudget + 2 ≤ q at hparams
  have hroot : 2 * Real.sqrt n / Real.sqrt halaszFiberSize ≤ R := by
    exact (two_mul_sqrt_div_sqrt_le fiberRate (by omega) hfiberRate
      hparams.2.2.1).trans (le_max_right _ _)
  have hlowerAll : ∀ a : ℤ → ℕ,
      (∀ i ∈ switchingLabels B, a i ≤ 2) →
      lower * ((T.card : ℝ) / Real.sqrt n) ^
          (∑ i ∈ switchingLabels B, a i) /
          (n : ℝ) ^ (3 / 2 : ℝ) ≤
        rawMomentExpectation (Finset.univ : Finset (Finset (Fin n)))
          (fun U ↦ |edgeScore G U - (x : ℤ)| ≤ (B : ℤ))
          (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ))
          a (switchingLabels B) := by
    dsimp only [lower]
    exact rawMomentExpectation_lower_of_tupleFamily
      (d := d) G T (switchingLabels B)
      (fun a ↦ ∑ i ∈ switchingLabels B, a i)
      (fun a ↦ ∀ i ∈ switchingLabels B, a i ≤ 2)
      (fun a ↦ richSwitchingTupleClass
        (I := RawTupleIndex (switchingLabels B) a)
        T G S₀ (rho * delta * S₀.card))
      c₀ z hn1
      (by
        intro a _ha
        simpa only [Nat.card_eq_fintype_card] using
          (card_rawTupleIndex (switchingLabels B) a).symm)
      (by
        intro a ha
        dsimp only [d]
        simpa only [Nat.card_eq_fintype_card] using
          switchingTuple_dimension_le a ha)
      (by
        intro a ha
        have hsd : Fintype.card
            (RawTupleIndex (switchingLabels B) a) ≤ d := by
          dsimp only [d]
          simpa only [Nat.card_eq_fintype_card] using
            switchingTuple_dimension_le a ha
        have hID : 2 * Fintype.card
            (RawTupleIndex (switchingLabels B) a) ≤ D := by
          dsimp only [D]
          omega
        simpa only [T] using
          rawTuple_richSwitchingTupleClass_half_of_smallness
            (B := B) (D := D) G S S₀ delta rho a
            (⟨⟨0, hn1⟩, ⟨0, hn1⟩⟩ : Fin n × Fin n)
            hrich hSS₀ hrho.le hcommon hID hcode
            (by simpa only [T] using hTlarge)
            (fun s SCard TCard ↦ hsmallData n hnSmall s SCard TCard))
      (fun U ↦ |edgeScore G U - (x : ℤ)| ≤ (B : ℤ))
      (by
        intro a ha
        have hsd : Fintype.card
            (RawTupleIndex (switchingLabels B) a) ≤ d := by
          dsimp only [d]
          simpa only [Nat.card_eq_fintype_card] using
            switchingTuple_dimension_le a ha
        have hID : 2 * Fintype.card
            (RawTupleIndex (switchingLabels B) a) ≤ D := by
          dsimp only [D]
          omega
        have hstateCore := hstateData n hnState G hG a hsd
          S S₀ q D hcommon hID (by simpa only [base] using hS₀)
        simpa only [c₀, z, CPrivate, etaPrivate, T] using
          rawTuple_stateLower_of_edgeCountCenter
            (B := B) (d := d) (q := q)
            A delta base rho kappa G S S₀ a
            hstateCore hdegree x hx)
      hc₀.le hz.le hz1
  refine ⟨T, switchingPairs_isSymmetric G S S₀ q, ?_⟩
  refine ⟨div_pos hTp (Real.sqrt_pos.2 hnpos),
    Real.rpow_pos_of_pos hnpos _, hlower, hupper, ?_⟩
  intro a ha
  refine ⟨hlowerAll a ha, ?_⟩
  let s := Fintype.card (RawTupleIndex (switchingLabels B) a)
  have hsd : s ≤ d := by
    dsimp only [s, d]
    simpa only [Nat.card_eq_fintype_card] using
      switchingTuple_dimension_le a ha
  have hID : 2 * s ≤ D := by dsimp only [D]; omega
  have hnum := hparams.2.2.2.2.2 s hsd
  have hraw := rawMoment_switchingCount_le_of_lemma1310_and_conditional_window
    (n := n) (by omega) G S S₀ delta rho (1 / 5 : ℝ)
      q deletionBudget richFiberSize halaszFiberSize codeBound
      (switchingLabels B) a
      (fun U ↦ |edgeScore G U - (x : ℤ)| ≤ (B : ℤ))
      (K₀ * (n : ℝ) ^ (-(3 / 2 : ℝ))) (by positivity)
      hparams.1 hparams.2.1 hrho.le hrich hSS₀
      hparams.2.2.2.1 hparams.2.2.2.2.1 hcode hnum.1
      (by
        intro k hkpos hks
        exact hnum.2 k hks)
      (by
        intro k hkpos hks
        exact (hratioData n hnRatio s k T.card hsd hkpos hks hTambient).1)
      (by
        intro k hkpos hks
        exact (hratioData n hnRatio s k T.card hsd hkpos hks hTambient).2)
      (by
        intro p hpT O hO
        have hpS : ∀ j, p j ∈ S ×ˢ S := by
          intro j
          have hj := (mem_switchingPairs_iff G S S₀ q
            (p j).1 (p j).2).mp (by simpa only [T] using hpT j)
          exact Finset.mem_product.mpr ⟨hj.1, hj.2.1⟩
        have hw := hwindowData n hnWindow G hG
          (RawTupleIndex (switchingLabels B) a) S S₀ p D hcommon
          (by simpa only [s] using hID) hpS (by simpa only [base] using hS₀)
          O hO (x : ℤ)
        convert hw using 1
        apply congrArg (fun z : ℕ ↦ (z : ℝ))
        apply congrArg Finset.card
        ext Rset
        simp only [Finset.mem_filter, Finset.mem_powerset])
  dsimp only [upper]
  rw [show (∑ i ∈ switchingLabels B, a i) = s by
    simpa only [s, Nat.card_eq_fintype_card] using
      (card_rawTupleIndex (switchingLabels B) a).symm]
  exact rawMomentExpectation_upper_of_degeneracySum
    K₀ R
      (fun U ↦ |edgeScore G U - (x : ℤ)| ≤ (B : ℤ))
      (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ))
      (switchingLabels B) a (by omega) hparams.2.1 hK₀.le hR hsd hroot
      (by simpa only [T, s] using hraw)

/-- The graph-level bounded-window theorem is the sole remaining input in
the switching route to Erdős Problem 88. -/
theorem erdos_88_of_boundedWindow
    (hBW : KSSSBoundedWindow) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          HomogeneousFree epsilon G →
            ∀ m : ℕ, (m : ℝ) ≤ delta * (n : ℝ) ^ 2 →
              ∃ S : Finset (Fin n), inducedEdges G S = m :=
  erdos_88_of_switchingMoments
    (ksssUnbiasedSwitchingMoments_of_boundedWindow hBW)

/-- The canonical `Fin n` bounded-window theorem supplies the full switching
moment comparison. -/
theorem ksssUnbiasedSwitchingMoments_of_boundedWindowFin
    (hBW : KSSSBoundedWindowFin) : KSSSUnbiasedSwitchingMoments :=
  ksssUnbiasedSwitchingMoments_of_boundedWindow
    (BoundedWindow.ksssBoundedWindow_of_fin hBW)

/-- Canonical finite-order form of the sole remaining input to Erdős
Problem 88. -/
theorem erdos_88_of_boundedWindowFin
    (hBW : KSSSBoundedWindowFin) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          HomogeneousFree epsilon G →
            ∀ m : ℕ, (m : ℝ) ≤ delta * (n : ℝ) ^ 2 →
              ∃ S : Finset (Fin n), inducedEdges G S = m :=
  erdos_88_of_boundedWindow
    (BoundedWindow.ksssBoundedWindow_of_fin hBW)

end Erdos88.Switching
