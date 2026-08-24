/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.PrimeRandomControlledLedger
import ErdosProblems.Erdos360.PrimeCountSharp
import ErdosProblems.Erdos360.PrimePoolOrdinary
import ErdosProblems.Erdos360.PrimeStructuredDivisorBound
import ErdosProblems.Erdos360.GeneralRandomLedger
import ErdosProblems.Erdos360.ControlledCapTwelve

/-!
# Eventual controlled parameters for Erdos 360

This file chooses the two cardinal scales which repair the unbalanced-colour
case.  The pre-extraction cap is `7n/(4y)` and the guaranteed post-loss size
is `3n/(2y)`.  The canonical parameter identity gives a test set large
enough for the first scale, while the gap of order `n/y` pays all extraction
and exact-multiple losses.  The second scale still leaves a factor `21/16`
in the terminal unused-mass estimate.

The additive ordinary-growth theorem is intentionally not imported here.
The eventual source theorem at the end accepts it in the local extraction
context used by `controlledRandomPreLevInput`.
-/

namespace Erdos360

open Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

/-- Number of elements retained from the pigeonhole colour class before
divisor extraction. -/
def controlledPrimeClassCap (n y : ℕ) : ℕ :=
  controlledPrimeClassCapTwelve n y

/-- Uniform lower size demanded after divisor extraction. -/
def controlledPrimeExtractedFloor (n y : ℕ) : ℕ :=
  controlledPrimeExtractedFloorTwelve n y

/-- The canonical initial-prime window has enough counted test elements to
choose the controlled class cap.  This exact lemma is the point where the
constant `15` in the definition of `initialLowerY` is spent: `14 < 15`.
-/
lemma controlledPrimeClassCap_mul_le_primeStructured_card
    {n colors y U : ℕ} (hn : 0 < n) (hcolors : 0 < colors)
    (hy : y = initialLowerY n colors)
    (hcount : initialMissingEulerProduct n colors * (y : ℝ) / 12 ≤
      ((primeStructuredTestSet n y U).card : ℝ)) :
    colors * controlledPrimeClassCap n y ≤
      (primeStructuredTestSet n y U).card := by
  simpa [controlledPrimeClassCap] using
    controlledPrimeClassCapTwelve_mul_le_primeStructured_card
      hn hcolors hy hcount

/-- The endpoint reserve is a purely integral consequence of the chosen
post-extraction floor, once `n/y` is beyond a fixed rounding threshold. -/
lemma controlledPrime_unused_numeric
    {n y : ℕ} (hy : 0 < y) (hlarge : 140 * y ≤ n) :
    n ≤ 7 * y * (controlledPrimeExtractedFloor n y / 8) := by
  simpa [controlledPrimeExtractedFloor] using
    controlledPrimeTwelve_unused_reserve hy hlarge

/-- One global exponential inequality (with `d = 1` and the full cap `M`)
discharges every stage and every admissible extraction divisor. -/
lemma controlledPrime_probability_ledger
    {y M L ell d : ℕ} (hell : 0 < ell) (hd : 0 < d)
    (hk : 12 * ell ^ 2 ≤ L - (8 * ell - 1))
    (hsmall : (4 : ℝ) * (M + 1) * (2 * y + 1) *
      Real.exp (- ((L - (8 * ell - 1) : ℕ) : ℝ) /
        (1024 * (ell : ℝ) ^ 2)) < 1) :
    ∀ j < ell,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (M / (8 * ell)) (8 * ell - j)
        (RandomDiversity.residualDiversity
          (L - (8 * ell - 1)) (8 * ell) j) < 1 := by
  apply exactSplitFailureMass_eight_mul_ledger hell hk
  apply (show (4 : ℝ) *
      (8 * (ell : ℝ) * ((M / (8 * ell) : ℕ) : ℝ) + 1) *
        (((2 * y / d : ℕ) : ℝ) + 1) *
        Real.exp (- ((L - (8 * ell - 1) : ℕ) : ℝ) /
          (1024 * (ell : ℝ) ^ 2)) ≤
      (4 : ℝ) * (M + 1) * (2 * y + 1) *
        Real.exp (- ((L - (8 * ell - 1) : ℕ) : ℝ) /
          (1024 * (ell : ℝ) ^ 2)) by
    have hcard : 8 * ell * (M / (8 * ell)) ≤ M :=
      by simpa [mul_comm] using Nat.div_mul_le_self M (8 * ell)
    have hN : 2 * y / d ≤ 2 * y := Nat.div_le_self _ _
    have hcardR : (8 : ℝ) * ell * ((M / (8 * ell) : ℕ) : ℝ) ≤ M := by
      exact_mod_cast hcard
    have hNR : ((2 * y / d : ℕ) : ℝ) ≤ 2 * y := by
      exact_mod_cast hN
    gcongr).trans_lt hsmall

/-- A single lower bound for the starting diversity supplies the entire
piece-diversity ledger. -/
lemma controlledPrime_diversity_ledger
    {y L ell : ℕ} (hell : 0 < ell)
    (hk : 12 * ell ^ 2 ≤ L - (8 * ell - 1))
    (hK : primeRandomPoolDiversity y ell ≤
      ((L - (8 * ell - 1)) / 2) / (16 * ell)) :
    ∀ j < ell,
      primeRandomPoolDiversity y ell ≤
        RandomDiversity.residualDiversity
          (L - (8 * ell - 1)) (8 * ell) j /
            (2 * (8 * ell - j)) := by
  intro j hj
  have hres := residualDiversity_eight_mul_half hell hj hk
  have hden : 2 * (8 * ell - j) ≤ 16 * ell := by omega
  exact hK.trans (Nat.div_le_div hres hden (by omega))

/-- The sum/diameter field in the local ordinary ledger follows directly
from the definitions; it consumes no asymptotic estimate. -/
lemma primeRandomPoolSize_mul_range_le_diameter
    {y z ell d : ℕ} (hell : 0 < ell) (hd : 0 < d) :
    primeRandomPoolSize z ell * (2 * y / d) ≤
      primeRandomDiameter y z ell d := by
  let s := primeRandomPoolSize z ell
  let N := 2 * y / d
  have hcell : 8 * ell * s ≤ z := by
    dsimp [s, primeRandomPoolSize]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      Nat.div_mul_le_self z (8 * ell)
  have hscale : d * N ≤ 2 * y := by
    dsimp [N]
    simpa [mul_comm] using Nat.div_mul_le_self (2 * y) d
  have hcross : (s * N) * (4 * ell * d) ≤ y * z := by
    have hmul := Nat.mul_le_mul hcell hscale
    nlinarith
  unfold primeRandomDiameter
  have hden : 0 < 4 * ell * d := by positivity
  have hfloor : s * N ≤ y * z / (4 * ell * d) :=
    (Nat.le_div_iff_mul_le hden).2 hcross
  exact hfloor.trans (by
    simpa only [Nat.floorDiv_eq_div] using
      (floorDiv_le_ceilDiv :
        y * z ⌊/⌋ (4 * ell * d) ≤ y * z ⌈/⌉ (4 * ell * d)))

/-- Source-parameter specialization of the general controlled constructor.
The pre-extraction cap `M` replaces every dangerous upper occurrence of
`Z.card`; the post-loss floor `Q` replaces every lower occurrence. -/
noncomputable def controlledPrimeRandomPreLevInput_of_parameter_ledger
    {n colors y B L M Q ell : ℕ} {Y : Finset (BelowTarget n)}
    {c : BelowTarget n → Fin colors} {i : Fin colors}
    {W Z : Finset ℕ} {d : ℕ}
    (hell : 0 < ell)
    (hk : 12 * ell ^ 2 ≤ L - (8 * ell - 1))
    (hY : ∀ x ∈ Y, y < x.1 ∧ x.1 ≤ 2 * y)
    (hW : W ⊆ integerColorClass Y c i) (hWcard : W.card = M)
    (hd : 0 < d) (hdB : d ≤ B)
    (hscale : ∀ z ∈ Z, d * z ∈ W)
    (hloss : W.card - Z.card ≤ L * Nat.log 2 B)
    (hdiverse : ∀ e : ℕ, 1 < e → d * e ≤ B →
      L ≤ (Z.filter fun z ↦ ¬e ∣ z).card)
    (hlossRoom : Q + L * Nat.log 2 B ≤ M)
    (hlarge : (L - (8 * ell - 1)) +
      (2 * y / d) / (B / d + 1) + (8 * ell - 1) ≤ Q)
    (hprobability : ∀ j < ell,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (M / (8 * ell)) (8 * ell - j)
        (RandomDiversity.residualDiversity
          (L - (8 * ell - 1)) (8 * ell) j) < 1)
    (hdiversity : ∀ j < ell,
      primeRandomPoolDiversity y ell ≤
        RandomDiversity.residualDiversity
          (L - (8 * ell - 1)) (8 * ell) j /
            (2 * (8 * ell - j)))
    (hordinaryNumerics : CFPPrimePoolOrdinaryNumerics ell y Z.card d)
    (hnzero : 3 ≤ primeRandomNzero y Z.card ell d)
    (hlev : 2 * ((primeRandomDiameter y Z.card ell d - 1) ⌈/⌉
      (primeRandomNzero y Z.card ell d - 2)) ≤ ell)
    (hwidth : 2 * y ≤
      ell * (primeRandomNzero y Z.card ell d - 1) + 1)
    (hsum : ell * (M / (8 * ell)) * (2 * y / d) < n / d)
    (hunused : n / d ≤
      (y / d + 1) * (Q - ell * (M / (8 * ell)))) :
    CFPRandomPreLevInput n d y Z := by
  have hscaleClass : ∀ z ∈ Z,
      d * z ∈ integerColorClass Y c i := fun z hz ↦ hW (hscale z hz)
  have hZrange : Z ⊆ Finset.Icc (y / d + 1) (2 * y / d) :=
    extracted_dyadic_quotient_exact_Icc hY hd hscaleClass
  have hresidualPos : 0 < L - (8 * ell - 1) :=
    (by positivity : 0 < 12 * ell ^ 2).trans_le hk
  have hreserve : 8 * ell - 1 ≤ L :=
    (Nat.sub_pos_iff_lt.mp hresidualPos).le
  have hkL : (L - (8 * ell - 1)) + (8 * ell - 1) ≤ L := by
    rw [Nat.sub_add_cancel hreserve]
  have hcellCount : ell + 2 ≤ 8 * ell := by omega
  apply controlledRandomPreLevInput
    (K := 0)
    (h := 8 * ell) (ell := ell)
    (k := L - (8 * ell - 1))
    (diversity := primeRandomPoolDiversity y ell)
    (nzero := primeRandomNzero y Z.card ell d)
    (diameter := primeRandomDiameter y Z.card ell d)
    hY hW hWcard hd hdB (by positivity) hscale
    (by simpa using hloss) (by simpa using hdiverse)
    (by simpa using hlossRoom) hkL hlarge hcellCount
    hprobability hdiversity
  · intro P hP hPcard hPdiverse
    apply cfpPrimePoolOrdinaryGrowthPrinciple ell y Z.card d P
      hordinaryNumerics
    · simpa [primeRandomPoolSize] using hPcard
    · intro p hp
      exact hZrange (lowerPart_subset Z _ (hP hp))
    · exact hPdiverse
  · exact hnzero
  · exact hlev
  · exact hwidth
  · exact hsum
  · exact hunused

/-- Complete finite numerical ledger after controlled extraction.  Its
quantifiers use the genuine bound `d <= U` forced by the prime-structured
factorization, rather than the much larger sieve cutoff `B`. -/
structure CFPControlledPrimeParameterLedger
    (n y U B L M Q ell : ℕ) : Prop where
  ell_pos : 0 < ell
  residual_large : 12 * ell ^ 2 ≤ L - (8 * ell - 1)
  U_pos : 0 < U
  B_pos : 0 < B
  B_cut : B ≤ y / U
  Q_pos : 0 < Q
  loss_room : Q + L * Nat.log 2 B ≤ M
  post : ∀ d z : ℕ, 0 < d → d ≤ U → Q ≤ z → z ≤ M →
    (L - (8 * ell - 1)) +
        (2 * y / d) / (B / d + 1) + (8 * ell - 1) ≤ Q ∧
    (∀ j < ell,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (M / (8 * ell)) (8 * ell - j)
        (RandomDiversity.residualDiversity
          (L - (8 * ell - 1)) (8 * ell) j) < 1) ∧
    (∀ j < ell,
      primeRandomPoolDiversity y ell ≤
        RandomDiversity.residualDiversity
          (L - (8 * ell - 1)) (8 * ell) j /
            (2 * (8 * ell - j))) ∧
    CFPPrimePoolOrdinaryNumerics ell y z d ∧
    3 ≤ primeRandomNzero y z ell d ∧
    2 * ((primeRandomDiameter y z ell d - 1) ⌈/⌉
      (primeRandomNzero y z ell d - 2)) ≤ ell ∧
    2 * y ≤ ell * (primeRandomNzero y z ell d - 1) + 1 ∧
    ell * (M / (8 * ell)) * (2 * y / d) < n / d ∧
    n / d ≤ (y / d + 1) * (Q - ell * (M / (8 * ell)))

/-- Exact finite source interface after the pigeonhole class has been
trimmed to cardinality `M`.  Unlike the older source interface, the loss is
measured from `W`, not from the whole (possibly much larger) colour class.
-/
def CFPControlledRandomTestSetSourceCompletion
    (n colors y U B L M : ℕ) (Y : Finset (BelowTarget n)) : Prop :=
  ∀ (c : BelowTarget n → Fin colors) (i : Fin colors)
      (W : Finset ℕ) (d : ℕ) (Z : Finset ℕ),
    W ⊆ integerColorClass Y c i → W.card = M →
    0 < d → d ≤ B →
    (∀ z ∈ Z, d * z ∈ W) →
    W.card - Z.card ≤ L * Nat.log 2 B →
    (∀ e : ℕ, 1 < e → d * e ≤ B →
      L ≤ (Z.filter fun z ↦ ¬e ∣ z).card) →
    d ∣ n ∧ Nonempty (CFPRandomPreLevInput n d y Z)

/-- The finite ledger produces the exact controlled source completion on
the canonical prime-structured test set. -/
theorem controlledRandomTestSetSource_of_parameterLedger
    {n colors y U B L M Q ell : ℕ} {hy : 2 * y < n}
    (hnum : CFPControlledPrimeParameterLedger n y U B L M Q ell) :
    CFPControlledRandomTestSetSourceCompletion n colors y U B L M
      (primeStructuredBelowTarget n y U hy) := by
  intro c i W d Z hW hWcard hd hdB hscale hloss hdiverse
  have hZupper : Z.card ≤ M := by
    simpa [hWcard] using card_le_of_positive_scale_subset hd hscale
  have hZlower : Q ≤ Z.card :=
    extracted_card_lower_of_controlled_loss hd hWcard hscale hloss
      hnum.loss_room
  have hZnonempty : Z.Nonempty :=
    Finset.card_pos.mp (hnum.Q_pos.trans_le hZlower)
  have hdData := extracted_scale_dvd_target_and_le_cutoff
    hnum.B_cut hd hdB hW hscale hZnonempty
  have hp := hnum.post d Z.card hd hdData.2 hZlower hZupper
  rcases hp with ⟨hlarge, hprobability, hdiversity,
    hordinary, hnzero, hlev, hwidth, hsum, hunused⟩
  refine ⟨hdData.1, ⟨?_⟩⟩
  exact controlledPrimeRandomPreLevInput_of_parameter_ledger
    hnum.ell_pos hnum.residual_large
    (fun x hx ↦ primeStructuredBelowTarget_dyadic hx)
    hW hWcard hd hdB hscale hloss hdiverse hnum.loss_room
    hlarge hprobability hdiversity hordinary hnzero hlev hwidth hsum hunused

/-! ## Controlled eventual lower-bound assembly -/

/-- Controlled extraction, random selection, and Lev imply the exact
monochromatic forcing statement.  All quotient range estimates are still
derived from membership in the actual dyadic test set. -/
theorem forcesTarget_of_controlledRandomTestSetSource
    {n colors y U B L M : ℕ} {Y : Finset (BelowTarget n)}
    (hcolors : 0 < colors) (hB : 0 < B)
    (hY : ∀ x ∈ Y, y < x.1 ∧ x.1 ≤ 2 * y)
    (hM : colors * M ≤ Y.card)
    (hsource : CFPControlledRandomTestSetSourceCompletion
      n colors y U B L M Y)
    (hlev : CFPLevHighMultiplicityPrinciple) :
    ForcesTarget n colors := by
  apply forcesTarget_of_controlled_extracted_colorClass_completion (K := 0)
    hcolors hB Y hM
  intro c i W d Z hW hWcard hd hdB hscale hloss hdiverse
  have hloss' : W.card - Z.card ≤ L * Nat.log 2 B := by
    simpa using hloss
  have hdiverse' : ∀ e : ℕ, 1 < e → d * e ≤ B →
      L ≤ (Z.filter fun z ↦ ¬e ∣ z).card := by
    intro e he heB
    simpa using hdiverse e he heB
  obtain ⟨hdn, hinput⟩ :=
    hsource c i W d Z hW hWcard hd hdB hscale hloss' hdiverse'
  obtain ⟨input⟩ := hinput
  have hscaleClass : ∀ z ∈ Z,
      d * z ∈ integerColorClass Y c i := fun z hz ↦ hW (hscale z hz)
  have hbounds := extracted_dyadic_quotient_bounds hY hd hscaleClass
  let raw := input.toPreLevSourceData.toRawSourceData hlev
  exact ⟨hdn, raw.toSourceData.quotient_mem_of_bounds hbounds⟩

/-- Eventual prime-structured controlled source package.  The test-set
cardinality inequality is explicit, so the eventual analytic module can
discharge it directly using `PrimeCountSharp`. -/
def EventuallyCFPControlledPrimeRandomTheorem (c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    let colors := lowerColorCount c n
    let y := initialLowerY n colors
    ∃ U B L M : ℕ, ∃ hy : 2 * y < n,
      0 < B ∧
      colors * M ≤
        (primeStructuredBelowTarget n y U hy).card ∧
      CFPControlledRandomTestSetSourceCompletion n colors y U B L M
        (primeStructuredBelowTarget n y U hy)

/-- Eventual controlled source data imply the canonical forcing floor. -/
theorem eventuallyForcesResolutionFloor_of_controlledPrimeRandom
    {c : ℝ} (hc : 0 < c)
    (hlev : CFPLevHighMultiplicityPrinciple)
    (hsource : EventuallyCFPControlledPrimeRandomTheorem c) :
    EventuallyForcesResolutionFloor c := by
  filter_upwards [eventually_three_le_lowerColorCount hc, hsource] with
      n hcolors hdata
  dsimp only at hdata
  obtain ⟨U, B, L, M, hy, hB, hM, hfinite⟩ := hdata
  simpa [lowerColorCount] using
    forcesTarget_of_controlledRandomTestSetSource
      (Y := primeStructuredBelowTarget n
        (initialLowerY n (lowerColorCount c n)) U hy)
      (by omega) hB (by
        intro x hx
        exact primeStructuredBelowTarget_dyadic hx) hM hfinite hlev

/-- Final exact resolution connector for the controlled source route. -/
theorem resolution_of_controlledPrimeRandom
    {c : ℝ} (hc : 0 < c)
    (hlev : CFPLevHighMultiplicityPrinciple)
    (hsource : EventuallyCFPControlledPrimeRandomTheorem c) :
    Resolution := by
  apply resolution_of_exists_eventually_forces_floor
  exact ⟨c, hc,
    eventuallyForcesResolutionFloor_of_controlledPrimeRandom
      hc hlev hsource⟩

end Erdos360

#print axioms Erdos360.controlledPrimeClassCap_mul_le_primeStructured_card
#print axioms Erdos360.controlledPrime_unused_numeric
#print axioms Erdos360.resolution_of_controlledPrimeRandom
