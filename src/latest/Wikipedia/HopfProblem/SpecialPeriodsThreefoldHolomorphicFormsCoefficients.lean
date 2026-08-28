import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsRegularCover

/-!
# Literal coefficients of global forms in the regular period coordinates

These are evaluations of the genuine derivative pullback, not a
replacement definition of a differential form. Restriction to the zero
fibre vector records candidate base coefficients; fibre independence is
proved separately from the actual lattice invariance.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open HolomorphicDifferentialForms (Form)

attribute [local instance] chartedSpace coverChartedSpace cover_isManifold space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

/-- The coefficient of dz in the actual pulled-back one-form. -/
def oneBase (θ : Form Model Threefold.Space 1) (x : Cover) : ℂ :=
  HolomorphicDifferentialForms.Coordinates.oneBaseCoefficient (nativeCoefficients θ x)

/-- Both vertical coefficients of the actual pulled-back one-form. -/
def oneFibre (θ : Form Model Threefold.Space 1) (x : Cover) : ComplexPlane₂ :=
  HolomorphicDifferentialForms.Coordinates.oneFibreCoefficient (nativeCoefficients θ x)

/-- The purely vertical coefficient of the actual pulled-back two-form. -/
def twoVertical (θ : Form Model Threefold.Space 2) (x : Cover) : ℂ :=
  HolomorphicDifferentialForms.Coordinates.twoVerticalCoefficient (nativeCoefficients θ x)

/-- Both mixed coefficients of the actual pulled-back two-form. -/
def twoMixed (θ : Form Model Threefold.Space 2) (x : Cover) : ComplexPlane₂ :=
  HolomorphicDifferentialForms.Coordinates.twoMixedCoefficient (nativeCoefficients θ x)

/-- The coefficient of the original ordered three-dimensional volume. -/
def top (θ : Form Model Threefold.Space 3) (x : Cover) : ℂ :=
  HolomorphicDifferentialForms.Coordinates.topCoefficient (nativeCoefficients θ x)

theorem oneBase_holomorphic (θ : Form Model Threefold.Space 1) :
    ContMDiff IF I₁ ω (oneBase θ) :=
  HolomorphicDifferentialForms.Coordinates.oneBaseCoefficient.contMDiff.comp
    (nativeCoefficients_holomorphic θ)

theorem oneFibre_holomorphic (θ : Form Model Threefold.Space 1) :
    ContMDiff IF I₂ ω (oneFibre θ) :=
  HolomorphicDifferentialForms.Coordinates.oneFibreCoefficient.contMDiff.comp
    (nativeCoefficients_holomorphic θ)

theorem twoVertical_holomorphic (θ : Form Model Threefold.Space 2) :
    ContMDiff IF I₁ ω (twoVertical θ) :=
  HolomorphicDifferentialForms.Coordinates.twoVerticalCoefficient.contMDiff.comp
    (nativeCoefficients_holomorphic θ)

theorem twoMixed_holomorphic (θ : Form Model Threefold.Space 2) :
    ContMDiff IF I₂ ω (twoMixed θ) :=
  HolomorphicDifferentialForms.Coordinates.twoMixedCoefficient.contMDiff.comp
    (nativeCoefficients_holomorphic θ)

theorem top_holomorphic (θ : Form Model Threefold.Space 3) :
    ContMDiff IF I₁ ω (top θ) :=
  HolomorphicDifferentialForms.Coordinates.topCoefficient.contMDiff.comp
    (nativeCoefficients_holomorphic θ)

/-- The literal zero period-vector section before either quotient. -/
def zeroSection (z : TriangleRegularPoint) : Cover := (z, 0)

theorem zeroSection_holomorphic : ContMDiff I₁ IF ω zeroSection := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_id.prodMk contMDiff_const

def baseOne (θ : Form Model Threefold.Space 1) (z : TriangleRegularPoint) : ℂ :=
  oneBase θ (zeroSection z)

def fibreOne (θ : Form Model Threefold.Space 1) (z : TriangleRegularPoint) : ComplexPlane₂ :=
  oneFibre θ (zeroSection z)

def verticalTwo (θ : Form Model Threefold.Space 2) (z : TriangleRegularPoint) : ℂ :=
  twoVertical θ (zeroSection z)

def mixedTwo (θ : Form Model Threefold.Space 2) (z : TriangleRegularPoint) : ComplexPlane₂ :=
  twoMixed θ (zeroSection z)

def baseTop (θ : Form Model Threefold.Space 3) (z : TriangleRegularPoint) : ℂ :=
  top θ (zeroSection z)

theorem baseOne_holomorphic (θ : Form Model Threefold.Space 1) :
    ContMDiff I₁ I₁ ω (baseOne θ) :=
  (oneBase_holomorphic θ).comp zeroSection_holomorphic

theorem fibreOne_holomorphic (θ : Form Model Threefold.Space 1) :
    ContMDiff I₁ I₂ ω (fibreOne θ) :=
  (oneFibre_holomorphic θ).comp zeroSection_holomorphic

theorem verticalTwo_holomorphic (θ : Form Model Threefold.Space 2) :
    ContMDiff I₁ I₁ ω (verticalTwo θ) :=
  (twoVertical_holomorphic θ).comp zeroSection_holomorphic

theorem mixedTwo_holomorphic (θ : Form Model Threefold.Space 2) :
    ContMDiff I₁ I₂ ω (mixedTwo θ) :=
  (twoMixed_holomorphic θ).comp zeroSection_holomorphic

theorem baseTop_holomorphic (θ : Form Model Threefold.Space 3) :
    ContMDiff I₁ I₁ ω (baseTop θ) :=
  (top_holomorphic θ).comp zeroSection_holomorphic

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
