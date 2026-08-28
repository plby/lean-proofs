import Wikipedia.HopfProblem.PeriodTorusLineBundleChernFrames
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreIdentification
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLogCocycle

/-!
# Actual frame logarithms and their integral Čech defect

The native Appell--Humbert bundle uses its original quotient charts and
coordinate transitions.  Their constructed entire logarithms give actual
frame logarithms, with the inverse convention verified on fibre vectors.
The Čech coboundary of these logarithms is an integer multiple of `2π I`;
the integers are locally constant and satisfy the actual four-chart
cocycle identity.  No comparison with singular cohomology is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open Set Filter Topology PeriodTorusAppellHumbert PeriodTorusLineBundleClassification
open scoped ContDiff

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- A logarithm of the actual scalar change from the first native coordinate to the second. -/
def coordinateLog (i j x : p.Torus) : ℂ :=
  factorLog F (Core.deck p i j x) (Core.lift p i x)

theorem coordinateLog_exp (i j x : p.Torus) :
    Complex.exp (coordinateLog F i j x) = ((Core.data F).transition i j x : ℂ) :=
  factorLog_exp F _ _

/-- A logarithm of the multiplier expressing the second native frame in the first. -/
def frameLog (i j x : p.Torus) : ℂ := -coordinateLog F i j x

theorem frameLog_exp (i j x : p.Torus) :
    Complex.exp (frameLog F i j x) = (frameTransition (Core.data F) i j x : ℂ) := by
  rw [frameLog, Complex.exp_neg, coordinateLog_exp]
  simp only [frameTransition, Units.val_inv_eq_inv_val]

/-- The exponentiated logarithm is the actual native fibre-frame multiplier. -/
theorem localFrame_change_exp (i j : p.Torus) {x : p.Torus}
    (hx : x ∈ Core.baseSet p i ∩ Core.baseSet p j) :
    localFrame (Core.data F) j x =
      Complex.exp (frameLog F i j x) • localFrame (Core.data F) i x := by
  rw [frameLog_exp]
  exact localFrame_change (Core.data F) i j hx

theorem coordinateLog_locally_eq (i j : p.Torus) {x : p.Torus}
    (hx : x ∈ Core.baseSet p i ∩ Core.baseSet p j) :
    coordinateLog F i j =ᶠ[𝓝 x]
      (fun y => factorLog F (Core.deck p i j x) (Core.lift p i y)) := by
  filter_upwards [Core.deck_locally_constant p i j hx] with y hy
  simp only [coordinateLog, hy]

/-- These are genuine holomorphic logarithms on the original chart overlaps. -/
theorem coordinateLog_holomorphic (i j : p.Torus) :
    ContMDiffOn (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ℂ) ω
      (coordinateLog F i j) (Core.baseSet p i ∩ Core.baseSet p j) := by
  intro x hx
  have hi := (Core.lift_holomorphic p i).contMDiffAt
    ((Core.isOpen_baseSet p i).mem_nhds hx.1)
  have hb := (factorLog_holomorphic F (Core.deck p i j x)).contMDiff.contMDiffAt
    (x := Core.lift p i x)
  exact ((hb.comp x hi).congr_of_eventuallyEq
    (coordinateLog_locally_eq F i j hx)).contMDiffWithinAt

theorem frameLog_holomorphic (i j : p.Torus) :
    ContMDiffOn (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ℂ) ω
      (frameLog F i j) (Core.baseSet p i ∩ Core.baseSet p j) :=
  (coordinateLog_holomorphic F i j).neg

/-- The integer is obtained from the actual entire transition logarithms and actual deck changes. -/
def frameIntegerCocycle (i j k x : p.Torus) : ℤ :=
  factorLogIntegerCocycle F (Core.deck p j k x) (Core.deck p i j x)

/-- The precise exponential-sequence integer, in the proved native frame convention. -/
theorem frameLog_cech_defect (i j k : p.Torus) {x : p.Torus}
    (hx : x ∈ Core.baseSet p i ∩ Core.baseSet p j ∩ Core.baseSet p k) :
    frameLog F j k x - frameLog F i k x + frameLog F i j x =
      (frameIntegerCocycle F i j k x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  have h := factorLogIntegerCocycle_spec F (Core.deck p j k x)
    (Core.deck p i j x) (Core.lift p i x)
  rw [factorLogDefect, Core.deck_comp p i j k hx, Core.deck_spec p i j hx.1] at h
  dsimp only [frameLog, coordinateLog, frameIntegerCocycle]
  linear_combination h

/-- The coordinate-log coboundary has the opposite sign, derived rather than chosen. -/
theorem coordinateLog_cech_defect (i j k : p.Torus) {x : p.Torus}
    (hx : x ∈ Core.baseSet p i ∩ Core.baseSet p j ∩ Core.baseSet p k) :
    coordinateLog F j k x - coordinateLog F i k x + coordinateLog F i j x =
      -(frameIntegerCocycle F i j k x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  have h := frameLog_cech_defect F i j k hx
  dsimp only [frameLog] at h
  linear_combination -h

/-- The actual integer transition defect is locally constant on every triple overlap. -/
theorem frameIntegerCocycle_locally_constant (i j k : p.Torus) {x : p.Torus}
    (hx : x ∈ Core.baseSet p i ∩ Core.baseSet p j ∩ Core.baseSet p k) :
    frameIntegerCocycle F i j k =ᶠ[𝓝 x] fun _ => frameIntegerCocycle F i j k x := by
  filter_upwards [Core.deck_locally_constant p j k ⟨hx.1.2, hx.2⟩,
    Core.deck_locally_constant p i j hx.1] with y hy hj
  exact congrArg₂ (factorLogIntegerCocycle F) hy hj

/-- The integral Čech differential vanishes on each actual four-fold overlap. -/
theorem frameIntegerCocycle_closed (i j k l : p.Torus) {x : p.Torus}
    (hx : x ∈ Core.baseSet p i ∩ Core.baseSet p j ∩ Core.baseSet p k ∩ Core.baseSet p l) :
    frameIntegerCocycle F j k l x - frameIntegerCocycle F i k l x +
      frameIntegerCocycle F i j l x - frameIntegerCocycle F i j k x = 0 := by
  have h := factorLogIntegerCocycle_cocycle F (Core.deck p k l x)
    (Core.deck p j k x) (Core.deck p i j x)
  dsimp only [frameIntegerCocycle]
  rw [← Core.deck_comp p i j k hx.1,
    ← Core.deck_comp p j k l ⟨⟨hx.1.1.2, hx.1.2⟩, hx.2⟩]
  omega

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
