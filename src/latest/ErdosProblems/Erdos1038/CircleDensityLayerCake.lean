import ErdosProblems.Erdos1038.CircleTerminalShell
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Two-density layer cake for circle rearrangement

This file supplies the reusable Tonelli bridge needed for the normalized
mixed circle energy.  A nonnegative kernel weighted by two nonnegative
densities is written as an iterated integral of the kernel over both strict
superlevel sets.  Consequently, any pointwise comparison of superlevel-set
cross-energies lifts immediately to the full density cross-energy.
-/

set_option warningAsError false

open Set MeasureTheory
open scoped ENNReal

namespace Erdos1038

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

local notation "AngleCircle" => AddCircle (2 * Real.pi)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Nonnegative mixed kernel energy of two real densities. -/
def densityKernelEnergy
    (mu : Measure X) (nu : Measure Y)
    (f : X → ℝ) (g : Y → ℝ) (kernel : X → Y → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y,
    ENNReal.ofReal (f x) * ENNReal.ofReal (g y) * kernel x y ∂nu ∂mu

/-- Kernel energy between the strict `t`- and `s`-superlevel sets. -/
def superlevelKernelEnergy
    (mu : Measure X) (nu : Measure Y)
    (f : X → ℝ) (g : Y → ℝ) (kernel : X → Y → ℝ≥0∞)
    (t s : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in ({x | t < f x} ×ˢ {y | s < g y}), kernel p.1 p.2 ∂(mu.prod nu)

/-- Two-variable layer-cake identity.  This is the exact Tonelli step that
turns a density rearrangement problem into a comparison for pairs of
superlevel sets. -/
theorem densityKernelEnergy_eq_lintegral_superlevels
    (mu : Measure X) (nu : Measure Y) [SFinite mu] [SFinite nu]
    {f : X → ℝ} {g : Y → ℝ} {kernel : X → Y → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y)
    (hkernel : Measurable (Function.uncurry kernel)) :
    densityKernelEnergy mu nu f g kernel =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
        superlevelKernelEnergy mu nu f g kernel t s := by
  let base : Measure (X × Y) := mu.prod nu
  let kappa : X × Y → ℝ≥0∞ := Function.uncurry kernel
  let F : X × Y → ℝ := fun p ↦ f p.1
  let G : X × Y → ℝ := fun p ↦ g p.2
  let weighted : Measure (X × Y) := base.withDensity kappa
  let weightedG : Measure (X × Y) :=
    weighted.withDensity (fun p ↦ ENNReal.ofReal (G p))
  have hkappa : Measurable kappa := by
    simpa only [kappa] using! hkernel
  have hF : Measurable F := hf.comp measurable_fst
  have hG : Measurable G := hg.comp measurable_snd
  have hOfRealF : Measurable (fun p ↦ ENNReal.ofReal (F p)) :=
    hF.ennreal_ofReal
  have hOfRealG : Measurable (fun p ↦ ENNReal.ofReal (G p)) :=
    hG.ennreal_ofReal
  have hprodIntegrand : Measurable (fun p : X × Y ↦
      kappa p * (ENNReal.ofReal (G p) * ENNReal.ofReal (F p))) :=
    hkappa.mul (hOfRealG.mul hOfRealF)
  have hweighted :
      densityKernelEnergy mu nu f g kernel =
        ∫⁻ p, ENNReal.ofReal (F p) ∂weightedG := by
    calc
      densityKernelEnergy mu nu f g kernel =
          ∫⁻ p : X × Y,
            kappa p *
              (ENNReal.ofReal (G p) * ENNReal.ofReal (F p)) ∂base := by
        unfold densityKernelEnergy base kappa F G
        rw [lintegral_prod _ hprodIntegrand.aemeasurable]
        apply lintegral_congr
        intro x
        apply lintegral_congr
        intro y
        dsimp only [kappa, F, G, Function.uncurry_apply_pair]
        ac_rfl
      _ = ∫⁻ p, ENNReal.ofReal (G p) * ENNReal.ofReal (F p)
          ∂weighted := by
        dsimp only [weighted]
        simpa only [Pi.mul_apply] using!
          (lintegral_withDensity_eq_lintegral_mul
            base hkappa (hOfRealG.mul hOfRealF)).symm
      _ = ∫⁻ p, ENNReal.ofReal (F p) ∂weightedG := by
        dsimp only [weightedG]
        simpa only [Pi.mul_apply] using!
          (lintegral_withDensity_eq_lintegral_mul
            weighted hOfRealG hOfRealF).symm
  have houter := lintegral_eq_lintegral_meas_lt weightedG
    (Filter.Eventually.of_forall fun p ↦ hf0 p.1)
    hF.aemeasurable
  rw [hweighted, houter]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  let Ft : Set (X × Y) := {p | t < F p}
  have hFt : MeasurableSet Ft :=
    measurableSet_lt measurable_const hF
  dsimp only [weightedG]
  rw [withDensity_apply _ hFt]
  have hinner := lintegral_eq_lintegral_meas_lt
    (weighted.restrict Ft)
    (Filter.Eventually.of_forall fun p ↦ hg0 p.2)
    hG.aemeasurable
  rw [hinner]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  let Gs : Set (X × Y) := {p | s < G p}
  have hGs : MeasurableSet Gs :=
    measurableSet_lt measurable_const hG
  change (weighted.restrict Ft) Gs = _
  rw [Measure.restrict_apply hGs]
  have hproduct : Gs ∩ Ft = {x | t < f x} ×ˢ {y | s < g y} := by
    ext p
    simp only [Gs, Ft, G, F, mem_inter_iff, mem_ofPred_eq,
      mem_prod, and_comm]
  rw [hproduct]
  unfold superlevelKernelEnergy
  dsimp only [weighted, base, kappa]
  have hlevels : MeasurableSet
      ({x | t < f x} ×ˢ {y | s < g y}) :=
    (measurableSet_lt measurable_const hf).prod
      (measurableSet_lt measurable_const hg)
  rw [withDensity_apply _ hlevels]
  rfl

/-- Pointwise superlevel-set comparison lifted through both layer-cake
variables. -/
theorem densityKernelEnergy_le_of_superlevelEnergy_le
    (mu : Measure X) (nu : Measure Y) [SFinite mu] [SFinite nu]
    {f : X → ℝ} {g : Y → ℝ} {kernel : X → Y → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y)
    (hkernel : Measurable (Function.uncurry kernel))
    (comparison : ℝ → ℝ → ℝ≥0∞)
    (hcomparison : ∀ t ∈ Ioi (0 : ℝ), ∀ s ∈ Ioi (0 : ℝ),
      superlevelKernelEnergy mu nu f g kernel t s ≤ comparison t s) :
    densityKernelEnergy mu nu f g kernel ≤
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ), comparison t s := by
  rw [densityKernelEnergy_eq_lintegral_superlevels
    mu nu hf hg hf0 hg0 hkernel]
  apply setLIntegral_mono' measurableSet_Ioi
  intro t ht
  apply setLIntegral_mono' measurableSet_Ioi
  intro s hs
  exact hcomparison t ht s hs

/-! ## The logarithmic circle kernel -/

/-- Mixed nonnegative logarithmic deficit of two arbitrary circle
densities. -/
def circleDensityLogDeficit
    (f g : AngleCircle → ℝ) : ℝ≥0∞ :=
  densityKernelEnergy volume volume f g
    (fun x y ↦ ENNReal.ofReal (circleLogDeficitAt x y))

/-- Logarithmic deficit between a pair of strict superlevel sets. -/
def circleSuperlevelLogDeficit
    (f g : AngleCircle → ℝ) (t s : ℝ) : ℝ≥0∞ :=
  superlevelKernelEnergy volume volume f g
    (fun x y ↦ ENNReal.ofReal (circleLogDeficitAt x y)) t s

lemma measurable_uncurry_circleLogDeficitAt_ofReal :
    Measurable (Function.uncurry
      (fun x y : AngleCircle ↦
        ENNReal.ofReal (circleLogDeficitAt x y))) := by
  unfold circleLogDeficitAt
  fun_prop

/-- Exact two-variable layer cake for the mixed logarithmic deficit.  This
is the nonnegative form of the density integral occurring in manuscript
equation `(5.3)`. -/
theorem circleDensityLogDeficit_eq_lintegral_superlevels
    {f g : AngleCircle → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y) :
    circleDensityLogDeficit f g =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
        circleSuperlevelLogDeficit f g t s := by
  exact densityKernelEnergy_eq_lintegral_superlevels
    volume volume hf hg hf0 hg0
      measurable_uncurry_circleLogDeficitAt_ofReal

/-! ## Terminal-shell specialization -/

/-- Separation of the two positive (equivalently, two negative)
components of terminal shells with lower endpoints `lower₁, lower₂`. -/
def terminalShellSameSignSeparation (lower₁ lower₂ : ℝ) : ℝ :=
  |lower₁ - lower₂| / 2

/-- Four-component logarithmic deficit between two terminal shells. -/
def terminalShellCrossDeficit (lower₁ upper lower₂ : ℝ) : ℝ≥0∞ :=
  2 * circleLogTwoArcEnergy
      (terminalShellComponentRadius lower₁ upper)
      (terminalShellComponentRadius lower₂ upper)
      (terminalShellSameSignSeparation lower₁ lower₂) +
    2 * circleLogTwoArcEnergy
      (terminalShellComponentRadius lower₁ upper)
      (terminalShellComponentRadius lower₂ upper)
      (terminalShellOppositeSeparation lower₁ upper lower₂)

/-- The same four pieces after both shells have been joined into centered
arcs. -/
def centeredTerminalShellCrossDeficit
    (lower₁ upper lower₂ : ℝ) : ℝ≥0∞ :=
  2 * circleLogTwoArcEnergy
      (terminalShellComponentRadius lower₁ upper)
      (terminalShellComponentRadius lower₂ upper)
      (terminalShellSameSignSeparation lower₁ lower₂) +
    2 * circleLogTwoArcEnergy
      (terminalShellComponentRadius lower₁ upper)
      (terminalShellComponentRadius lower₂ upper)
      (centeredCompressionOppositeSeparation lower₁ upper lower₂)

theorem terminalShellCrossDeficit_le_centered
    {lower₁ upper lower₂ : ℝ}
    (hlower₁ : 0 ≤ lower₁) (hlower₂ : 0 ≤ lower₂)
    (hlower₁Upper : lower₁ ≤ upper)
    (hlower₂Upper : lower₂ ≤ upper)
    (hupper : upper ≤ Real.pi) :
    terminalShellCrossDeficit lower₁ upper lower₂ ≤
      centeredTerminalShellCrossDeficit lower₁ upper lower₂ := by
  exact circleLogTerminalShell_crossDeficit_le_compressed
    hlower₁ hlower₂ hlower₁Upper hlower₂Upper hupper

/-- The mixed deficit obtained after applying layer cake to both density
variables of a pair of terminal-shell densities. -/
def terminalShellLayerCakeDeficit
    (lowerF lowerG : ℝ → ℝ) (upper : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
    terminalShellCrossDeficit (lowerF t) upper (lowerG s)

/-- Double layer-cake deficit after centered compression of every pair of
terminal shells. -/
def centeredTerminalShellLayerCakeDeficit
    (lowerF lowerG : ℝ → ℝ) (upper : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
    centeredTerminalShellCrossDeficit (lowerF t) upper (lowerG s)

/-- `CircleTerminalShell` lifted pointwise through both layer-cake
variables.  No integrability hypothesis is needed because all terms take
values in `ℝ≥0∞`. -/
theorem terminalShellLayerCakeDeficit_le_centered
    (lowerF lowerG : ℝ → ℝ) (upper : ℝ)
    (hlowerF0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ lowerF t)
    (hlowerG0 : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ lowerG s)
    (hlowerFUpper : ∀ t ∈ Ioi (0 : ℝ), lowerF t ≤ upper)
    (hlowerGUpper : ∀ s ∈ Ioi (0 : ℝ), lowerG s ≤ upper)
    (hupper : upper ≤ Real.pi) :
    terminalShellLayerCakeDeficit lowerF lowerG upper ≤
      centeredTerminalShellLayerCakeDeficit lowerF lowerG upper := by
  unfold terminalShellLayerCakeDeficit
    centeredTerminalShellLayerCakeDeficit
  apply setLIntegral_mono' measurableSet_Ioi
  intro t ht
  apply setLIntegral_mono' measurableSet_Ioi
  intro s hs
  exact terminalShellCrossDeficit_le_centered
    (hlowerF0 t ht) (hlowerG0 s hs)
    (hlowerFUpper t ht) (hlowerGUpper s hs) hupper

/-- Reusable end-to-end rearrangement bridge: identify each pair of strict
superlevel sets with (or bound it by) the corresponding terminal-shell
cross-deficit, and the two-density energy is bounded by the double
layer-cake of the centered compressions. -/
theorem densityKernelEnergy_le_centeredTerminalShellLayerCake
    (mu : Measure X) (nu : Measure Y) [SFinite mu] [SFinite nu]
    {f : X → ℝ} {g : Y → ℝ} {kernel : X → Y → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y)
    (hkernel : Measurable (Function.uncurry kernel))
    (lowerF lowerG : ℝ → ℝ) (upper : ℝ)
    (hlowerF0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ lowerF t)
    (hlowerG0 : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ lowerG s)
    (hlowerFUpper : ∀ t ∈ Ioi (0 : ℝ), lowerF t ≤ upper)
    (hlowerGUpper : ∀ s ∈ Ioi (0 : ℝ), lowerG s ≤ upper)
    (hupper : upper ≤ Real.pi)
    (hsuperlevel : ∀ t ∈ Ioi (0 : ℝ), ∀ s ∈ Ioi (0 : ℝ),
      superlevelKernelEnergy mu nu f g kernel t s ≤
        terminalShellCrossDeficit (lowerF t) upper (lowerG s)) :
    densityKernelEnergy mu nu f g kernel ≤
      centeredTerminalShellLayerCakeDeficit lowerF lowerG upper := by
  calc
    densityKernelEnergy mu nu f g kernel ≤
        terminalShellLayerCakeDeficit lowerF lowerG upper :=
      densityKernelEnergy_le_of_superlevelEnergy_le
        mu nu hf hg hf0 hg0 hkernel
        (fun t s ↦ terminalShellCrossDeficit (lowerF t) upper (lowerG s))
        hsuperlevel
    _ ≤ centeredTerminalShellLayerCakeDeficit lowerF lowerG upper :=
      terminalShellLayerCakeDeficit_le_centered
        lowerF lowerG upper hlowerF0 hlowerG0
        hlowerFUpper hlowerGUpper hupper

/-- Circle-logarithmic specialization of the end-to-end terminal-shell
bridge.  The sole geometric input left to a concrete density is the exact
description of each positive superlevel set as a terminal shell. -/
theorem circleDensityLogDeficit_le_centeredTerminalShellLayerCake
    {f g : AngleCircle → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y)
    (lowerF lowerG : ℝ → ℝ) (upper : ℝ)
    (hlowerF0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ lowerF t)
    (hlowerG0 : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ lowerG s)
    (hlowerFUpper : ∀ t ∈ Ioi (0 : ℝ), lowerF t ≤ upper)
    (hlowerGUpper : ∀ s ∈ Ioi (0 : ℝ), lowerG s ≤ upper)
    (hupper : upper ≤ Real.pi)
    (hsuperlevel : ∀ t ∈ Ioi (0 : ℝ), ∀ s ∈ Ioi (0 : ℝ),
      circleSuperlevelLogDeficit f g t s ≤
        terminalShellCrossDeficit (lowerF t) upper (lowerG s)) :
    circleDensityLogDeficit f g ≤
      centeredTerminalShellLayerCakeDeficit lowerF lowerG upper := by
  exact densityKernelEnergy_le_centeredTerminalShellLayerCake
    volume volume hf hg hf0 hg0
    measurable_uncurry_circleLogDeficitAt_ofReal
    lowerF lowerG upper hlowerF0 hlowerG0
    hlowerFUpper hlowerGUpper hupper hsuperlevel

/-- Fixed-mass sign reversal: an upper bound for a finite logarithmic
deficit gives the corresponding lower bound for the log-kernel energy. -/
theorem deficit_toReal_le_of_deficit_le
    {deficit centeredDeficit : ℝ≥0∞}
    (hdeficit : deficit ≤ centeredDeficit)
    (hcenteredFinite : centeredDeficit ≠ ∞) :
    deficit.toReal ≤ centeredDeficit.toReal := by
  exact ENNReal.toReal_mono hcenteredFinite hdeficit

theorem fixedMass_sub_deficit_ge_of_deficit_le
    {mass : ℝ} {deficit centeredDeficit : ℝ≥0∞}
    (hdeficit : deficit ≤ centeredDeficit)
    (hcenteredFinite : centeredDeficit ≠ ∞) :
    mass - centeredDeficit.toReal ≤ mass - deficit.toReal := by
  have hreal := ENNReal.toReal_mono hcenteredFinite hdeficit
  linarith

/-- Normalized real log-energy form used in equation `(5.3)`: the fixed
`2 * log 2` mass term is unchanged, so increasing the logarithmic deficit
decreases the log-kernel energy. -/
theorem normalized_log_energy_ge_of_deficit_le
    {H Q R : ℝ} {deficit centeredDeficit : ℝ≥0∞}
    (hQ : 0 < Q) (hR : 0 < R)
    (hdeficit : deficit ≤ centeredDeficit)
    (hcenteredFinite : centeredDeficit ≠ ∞) :
    Real.log H + 2 * Real.log 2 -
          centeredDeficit.toReal / (2 * Q * R) ≤
      Real.log H + 2 * Real.log 2 -
          deficit.toReal / (2 * Q * R) := by
  have hreal : deficit.toReal ≤ centeredDeficit.toReal :=
    ENNReal.toReal_mono hcenteredFinite hdeficit
  have hden : 0 ≤ 2 * Q * R := (by positivity)
  have hquotient := div_le_div_of_nonneg_right hreal hden
  linarith

end

end Erdos1038
