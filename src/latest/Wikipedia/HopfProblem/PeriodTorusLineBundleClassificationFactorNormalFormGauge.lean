import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorNormalFormDatum
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationAdditiveNormalFormBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCharacterGauge

/-!
# The actual entire gauge to the unitary Appell--Humbert factor

The constant antilinear increments form a genuine lattice character.
Its proved unitary normalization is combined with the actual entire
logarithmic correction. The resulting nowhere-zero entire gauge has the
exact factor-intertwining relation required for a native bundle isomorphism.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex PeriodTorusAppellHumbert
open scoped ContDiff

def normalizingCharacter {p : PeriodDomain} (c : Fin 2 → ℂ) : LatticeCharacter p :=
  realLinearExponentialCharacter (antiholomorphicLinear c).toLinearMap

@[simp]
theorem normalizingCharacter_value {p : PeriodDomain} (c : Fin 2 → ℂ) (l : p.lattice) :
    characterValue (normalizingCharacter c) l = Complex.exp (antiholomorphicLinear c l) := rfl

def normalizingGauge {p : PeriodDomain} (c : Fin 2 → ℂ)
    (g : ComplexPlane₂ → ℂ) (z : ComplexPlane₂) : ℂ :=
  Complex.exp (g z) * characterGauge (p := p) (normalizingCharacter c) z

theorem normalizingGauge_holomorphic {p : PeriodDomain} (c : Fin 2 → ℂ)
    {g : ComplexPlane₂ → ℂ} (hg : ContDiff ℂ ω g) :
    ContDiff ℂ ω (normalizingGauge (p := p) c g) :=
  hg.cexp.mul (characterGauge_holomorphic (normalizingCharacter c))

theorem normalizingGauge_ne_zero {p : PeriodDomain} (c : Fin 2 → ℂ)
    (g : ComplexPlane₂ → ℂ) (z : ComplexPlane₂) : normalizingGauge (p := p) c g z ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (characterGauge_ne_zero _ _)

theorem factorComparison_normal_form_relation {p : PeriodDomain} (F : FactorOfAutomorphy p)
    (c : Fin 2 → ℂ) (g : ComplexPlane₂ → ℂ)
    (hk : ∀ l : p.lattice, ∀ z, factorComparisonLog F l z =
      g (z + l) - g z + antiholomorphicLinear c l)
    (l : p.lattice) (z : ComplexPlane₂) :
    Complex.exp (g (z + l)) * characterValue (normalizingCharacter c) l *
        ((factorReference F).factor l z : ℂ) =
      (F.factor l z : ℂ) * Complex.exp (g z) := by
  have he := factorComparisonLog_exp F l z
  rw [hk l z, Complex.exp_add, Complex.exp_sub, ← normalizingCharacter_value c l] at he
  field_simp [(factorReference F).factor_ne_zero l z, Complex.exp_ne_zero (g z)] at he
  linear_combination he

/-- The positive-translation relation intertwines the actual normalized
unitary factor with the original factor. -/
theorem normalizedFactorDatum_gauge_relation {p : PeriodDomain} (F : FactorOfAutomorphy p)
    (c : Fin 2 → ℂ) (g : ComplexPlane₂ → ℂ)
    (hk : ∀ l : p.lattice, ∀ z, factorComparisonLog F l z =
      g (z + l) - g z + antiholomorphicLinear c l)
    (l : p.lattice) (z : ComplexPlane₂) :
    normalizingGauge (p := p) c g (z + l) *
        ((normalizedFactorDatum F (normalizingCharacter c)).factor.factor l z : ℂ) =
      (F.factor l z : ℂ) * normalizingGauge (p := p) c g z := by
  have hc := characterGauge_factor_relation (normalizingCharacter (p := p) c) l z
  simp only [constantCharacterFactor_coe] at hc
  have hk' := factorComparison_normal_form_relation F c g hk l z
  dsimp only [normalizingGauge]
  rw [normalizedFactorDatum_factor_coe]
  linear_combination
    (Complex.exp (g (z + l)) * ((factorReference F).factor l z : ℂ)) * hc +
      characterGauge (normalizingCharacter c) z * hk'

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
