import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothCoordinates
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierSymbol

/-!
# Joint real smoothness of the genuine varying Dolbeault symbol

The symbol is evaluated through the original inverse period coordinates.
Its real smoothness in both the base and the frequency follows from the
original holomorphic period functions, without a symbol-regularity premise.
All native statements retain the original open-base product charts.
-/

noncomputable section

open TopologicalSpace
open scoped BigOperators ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth

open PeriodTorusLineBundleClassification

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The actual frequency functional expressed in the ambient original base chart. -/
def frequencyValue (x : ℂ × RealPlane₄) (z : ComplexPlane₂) : ℝ :=
  ∑ j : Fin 4, x.2 j * inversePeriodCoordinates P (x.1, z) j

@[simp] theorem frequencyValue_apply (b : U) (v : RealPlane₄) (z : ComplexPlane₂) :
    frequencyValue P ((b : ℂ), v) z = frequencyFunctional (P.point b) v z := by
  simp only [frequencyValue, inversePeriodCoordinates_apply, frequencyFunctional_apply]
  rfl

/-- Frequency evaluation is jointly real smooth in the base and the real frequency. -/
theorem frequencyValue_contDiffOn (z : ComplexPlane₂) :
    ContDiffOn ℝ ∞ (fun x => frequencyValue P x z) (baseProductDomain U RealPlane₄) := by
  have hcoord : ContDiffOn ℝ ∞
      (fun x : ℂ × RealPlane₄ => inversePeriodCoordinates P (x.1, z))
      (baseProductDomain U RealPlane₄) :=
    (inversePeriodCoordinates_contDiffOn P).comp
      (f := fun x : ℂ × RealPlane₄ => (x.1, z))
      (contDiffOn_fst.prodMk contDiffOn_const) (fun _ hx => hx)
  apply ContDiffOn.sum
  intro j _
  exact ((contDiff_apply ℝ ℝ j).comp contDiff_snd).contDiffOn.mul
    ((contDiff_apply ℝ ℝ j).comp_contDiffOn hcoord)

/-- Ambient expression for the genuine symbol in its fixed complex-coordinate frame. -/
def symbolValue (x : ℂ × RealPlane₄) : ComplexPlane₂ :=
  fun i => (Real.pi : ℂ) *
    (Complex.I * (frequencyValue P x (Pi.single i 1) : ℂ) -
      (frequencyValue P x (Complex.I • Pi.single i 1) : ℂ))

@[simp] theorem symbolValue_apply (b : U) (v : RealPlane₄) :
    symbolValue P ((b : ℂ), v) = dolbeaultSymbol (P.point b) v := by
  ext i
  simp only [symbolValue, frequencyValue_apply, dolbeaultSymbol_apply]

/-- The original symbol is jointly real smooth, including the zero real frequency. -/
theorem symbolValue_contDiffOn :
    ContDiffOn ℝ ∞ (symbolValue P) (baseProductDomain U RealPlane₄) := by
  apply contDiffOn_pi.mpr
  intro i
  exact contDiffOn_const.mul
    ((contDiffOn_const.mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (frequencyValue_contDiffOn P (Pi.single i 1)))).sub
      (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (frequencyValue_contDiffOn P (Complex.I • Pi.single i 1))))

local instance smoothSymbolProductChartedSpace :
    ChartedSpace (ℂ × RealPlane₄) (U × RealPlane₄) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ RealPlane₄) (U × RealPlane₄))

/-- Joint real smoothness of the actual symbol in the original native charts. -/
theorem symbol_native_contMDiff :
    ContMDiff (modelWithCornersSelf ℝ (ℂ × RealPlane₄))
      (modelWithCornersSelf ℝ ComplexPlane₂) ∞
      (fun x : U × RealPlane₄ => dolbeaultSymbol (P.point x.1) x.2) := by
  have h := contMDiff_productOpen_of_contDiffOn (symbolValue_contDiffOn P)
  exact h.congr (fun x => (symbolValue_apply P x.1 x.2).symm)

@[simp] theorem symbolValue_zero_frequency (z : ℂ) :
    symbolValue P (z, 0) = 0 := by
  ext i
  simp [symbolValue, frequencyValue]

/-- The symbol of one fixed integer Fourier mode in the original open base chart. -/
def integerSymbolValue (k : Fin 4 → ℤ) (z : ℂ) : ComplexPlane₂ :=
  symbolValue P (z, integerFrequency k)

@[simp] theorem integerSymbolValue_apply (k : Fin 4 → ℤ) (b : U) :
    integerSymbolValue P k (b : ℂ) =
      dolbeaultSymbol (P.point b) (integerFrequency k) :=
  symbolValue_apply P b (integerFrequency k)

theorem integerSymbolValue_contDiffOn (k : Fin 4 → ℤ) :
    ContDiffOn ℝ ∞ (integerSymbolValue P k) U :=
  (symbolValue_contDiffOn P).comp
    (f := fun z : ℂ => (z, integerFrequency k))
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => hz)

@[simp] theorem integerSymbolValue_zero (z : ℂ) :
    integerSymbolValue P 0 z = 0 := by
  simp [integerSymbolValue]

/-- Nonzero modes remain nonzero by the actual period-symbol injectivity theorem. -/
theorem integerSymbolValue_ne_zero (k : Fin 4 → ℤ) (hk : k ≠ 0)
    (z : ℂ) (hz : z ∈ U) : integerSymbolValue P k z ≠ 0 := by
  rw [integerSymbolValue_apply P k ⟨z, hz⟩]
  exact dolbeaultSymbol_integer_ne_zero (P.point ⟨z, hz⟩) hk

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth
