import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothSymbol
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierModes

/-!
# Actual Hermitian Fourier multipliers are real smooth in the original family

For every fixed integer frequency, both genuine Hermitian mode inverses are
jointly real smooth in the base and their coefficient input. The period map
is the original holomorphic map on an open subset of the complex line.
The zero mode is handled by its exact zero formula; at every other mode the
denominator is nonzero by the proved injectivity of the actual symbol.

These are finite-mode smoothness statements, not assertions about convergence
of an infinite Fourier sum or about holomorphic base change.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The genuine scalar mode inverse written in the ambient original base chart. -/
def modePotentialValue (k : Fin 4 → ℤ) (x : ℂ × ComplexPlane₂) : ℂ :=
  FourierHermitian.potential (integerSymbolValue P k x.1) x.2

/-- The genuine top-degree mode inverse in the ambient original base chart. -/
def modeTopInverseValue (k : Fin 4 → ℤ) (x : ℂ × ℂ) : ComplexPlane₂ :=
  FourierHermitian.topInverse (integerSymbolValue P k x.1) x.2

@[simp] theorem modePotentialValue_apply (k : Fin 4 → ℤ) (b : U) (a : ComplexPlane₂) :
    modePotentialValue P k ((b : ℂ), a) = Fourier.modePotential (P.point b) k a := by
  simp only [modePotentialValue, integerSymbolValue_apply, Fourier.modePotential]

@[simp] theorem modeTopInverseValue_apply (k : Fin 4 → ℤ) (b : U) (h : ℂ) :
    modeTopInverseValue P k ((b : ℂ), h) = Fourier.modeTopInverse (P.point b) k h := by
  simp only [modeTopInverseValue, integerSymbolValue_apply, Fourier.modeTopInverse]

@[simp] theorem modePotentialValue_zero_frequency (x : ℂ × ComplexPlane₂) :
    modePotentialValue P 0 x = 0 := by
  simp only [modePotentialValue, integerSymbolValue_zero, FourierHermitian.potential_zero_symbol]

@[simp] theorem modeTopInverseValue_zero_frequency (x : ℂ × ℂ) :
    modeTopInverseValue P 0 x = 0 := by
  simp only [modeTopInverseValue, integerSymbolValue_zero, FourierHermitian.topInverse_zero_symbol]

/-- Real smoothness of each actual scalar multiplier, jointly with its input. -/
theorem modePotentialValue_contDiffOn (k : Fin 4 → ℤ) :
    ContDiffOn ℝ ∞ (modePotentialValue P k) (baseProductDomain U ComplexPlane₂) := by
  by_cases hk : k = 0
  · subst k
    exact (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℂ × ComplexPlane₂ => (0 : ℂ))
      (baseProductDomain U ComplexPlane₂)).congr
        (fun x _ => modePotentialValue_zero_frequency P x)
  · exact FourierHermitian.potential_contDiffOn_comp
      ((integerSymbolValue_contDiffOn P k).comp
        (f := fun x : ℂ × ComplexPlane₂ => x.1) contDiffOn_fst (fun _ hx => hx))
      contDiffOn_snd (fun x hx => integerSymbolValue_ne_zero P k hk x.1 hx)

/-- Real smoothness of each actual top-degree multiplier, jointly with its input. -/
theorem modeTopInverseValue_contDiffOn (k : Fin 4 → ℤ) :
    ContDiffOn ℝ ∞ (modeTopInverseValue P k) (baseProductDomain U ℂ) := by
  by_cases hk : k = 0
  · subst k
    exact (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℂ × ℂ => (0 : ComplexPlane₂))
      (baseProductDomain U ℂ)).congr
        (fun x _ => modeTopInverseValue_zero_frequency P x)
  · exact FourierHermitian.topInverse_contDiffOn_comp
      ((integerSymbolValue_contDiffOn P k).comp
        (f := fun x : ℂ × ℂ => x.1) contDiffOn_fst (fun _ hx => hx))
      contDiffOn_snd (fun x hx => integerSymbolValue_ne_zero P k hk x.1 hx)

local instance smoothModesProductChartedSpace {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] : ChartedSpace (ℂ × F) (U × F) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ F) (U × F))

/-- The original scalar Hermitian multiplier is real smooth in the unchanged charts. -/
theorem modePotential_native_contMDiff (k : Fin 4 → ℤ) :
    ContMDiff (modelWithCornersSelf ℝ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun x : U × ComplexPlane₂ => Fourier.modePotential (P.point x.1) k x.2) := by
  have h := contMDiff_productOpen_of_contDiffOn (modePotentialValue_contDiffOn P k)
  exact h.congr (fun x => (modePotentialValue_apply P k x.1 x.2).symm)

/-- The original top-degree Hermitian multiplier is real smooth in the unchanged charts. -/
theorem modeTopInverse_native_contMDiff (k : Fin 4 → ℤ) :
    ContMDiff (modelWithCornersSelf ℝ (ℂ × ℂ))
      (modelWithCornersSelf ℝ ComplexPlane₂) ∞
      (fun x : U × ℂ => Fourier.modeTopInverse (P.point x.1) k x.2) := by
  have h := contMDiff_productOpen_of_contDiffOn (modeTopInverseValue_contDiffOn P k)
  exact h.congr (fun x => (modeTopInverseValue_apply P k x.1 x.2).symm)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Smooth
