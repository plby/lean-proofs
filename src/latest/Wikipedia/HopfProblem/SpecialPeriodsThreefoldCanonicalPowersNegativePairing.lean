import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersNegativeCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleDual

/-!
# The genuine dual-section pairing for negative pulled-back powers

The positive dual section has the original ideal-frame coefficients
`1` and `w ^ n`.  It is constructed as a holomorphic section of the
actual dual of the native power bundle.  Pairing with a section of the
negative power is evaluation of its full continuous complex-linear
fibre dual, and is globally holomorphic by the native chart formulas.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersNegative

open HolomorphicCharacterBundle CanonicalGlobalLineBundle

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

instance data_isHolomorphic : data.IsHolomorphic IF := GlobalBasePullback.cartier.isHolomorphic

/-- The actual power cocycle of the pulled-back ideal line, on its unchanged cover. -/
abbrev powerData (n : ℕ) := data.power n

abbrev bundle (n : ℕ) := (powerData n).core

/-- Genuine holomorphic sections for the original total-space manifold structure. -/
abbrev Section (n : ℕ) := ContMDiffSection IF ℂ ω (bundle n).Fiber

/-- The inverse transition cocycle, with fibres identified with full continuous duals. -/
abbrev dualData (n : ℕ) := CanonicalGlobalLineBundle.dual (powerData n)

abbrev DualSection (n : ℕ) := ContMDiffSection IF ℂ ω (dualData n).core.Fiber

/-- The actual reciprocal ideal-frame coefficients satisfy the dual power cocycle. -/
theorem positiveLocal_compatible (n : ℕ) :
    (dualData n).IsCompatible (fun i x => dualCoefficient i x ^ n) := by
  intro i j x hx
  have he := dualCoefficient_transition i j x hx
  simp only [dualData, dual_transition, powerData, TransitionData.power_transition,
    Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  change ((data.transition i j x : ℂ) ^ n)⁻¹ * dualCoefficient i x ^ n =
    dualCoefficient j x ^ n
  rw [← he, mul_pow, mul_comm (dualCoefficient j x ^ n) ((data.transition i j x : ℂ) ^ n)]
  exact inv_mul_cancel_left₀ (pow_ne_zero n (data.transition_ne_zero i j x)) _

theorem positiveLocal_holomorphic (n : ℕ) (i : Bool) :
    ContMDiffOn IF 𝓘(ℂ) ω (fun x => dualCoefficient i x ^ n) ((dualData n).baseSet i) :=
  (dualCoefficient_holomorphicOn i).pow n

/-- The actual positive section dual to the negative pulled-back power. -/
def positiveSection (n : ℕ) : DualSection n :=
  (dualData n).holomorphicSectionFromLocal IF (fun i x => dualCoefficient i x ^ n)
    (positiveLocal_compatible n) (positiveLocal_holomorphic n)

@[simp] theorem positiveSection_apply (n : ℕ) (x : Threefold.Space) :
    id (α := ℂ) (positiveSection n x) = dualCoefficient (data.indexAt x) x ^ n := rfl

/-- Every valid original chart reads the prescribed actual power coefficient. -/
theorem positiveSection_localCoefficient (n : ℕ) (i : Bool) (x : Threefold.Space)
    (hx : x ∈ data.baseSet i) :
    (dualData n).localCoefficient (positiveSection n) i x = dualCoefficient i x ^ n :=
  (dualData n).localCoefficient_sectionFromLocal (fun i x => dualCoefficient i x ^ n)
    (positiveLocal_compatible n) i hx

/-- Evaluation in the full continuous complex-linear dual of the actual fibre. -/
def pairing (n : ℕ) (s : Section n) (x : Threefold.Space) : ℂ :=
  dualFiberEquiv (powerData n) x (positiveSection n x) (s x)

theorem pairing_apply (n : ℕ) (s : Section n) (x : Threefold.Space) :
    pairing n s x = dualCoefficient (data.indexAt x) x ^ n * id (α := ℂ) (s x) := by
  rw [pairing, dualFiberEquiv_apply, positiveSection_apply]

/-- The pairing has its literal product formula in every native pair of dual charts. -/
theorem pairing_localCoefficient (n : ℕ) (s : Section n) (i : Bool)
    (x : Threefold.Space) (hx : x ∈ data.baseSet i) :
    pairing n s x = dualCoefficient i x ^ n * (powerData n).localCoefficient s i x :=
  (dualFiberEquiv_localTriv (powerData n) i x (positiveSection n x) (s x)).trans
    (congrArg (fun c : ℂ => c * (powerData n).localCoefficient s i x)
      (positiveSection_localCoefficient n i x hx))

/-- Holomorphicity is proved using the actual two bundle sections in their
original local trivializations, not by assuming a preferred scalar is holomorphic. -/
theorem pairing_holomorphic (n : ℕ) (s : Section n) :
    ContMDiff IF 𝓘(ℂ) ω (pairing n s) := by
  intro x
  let i := data.indexAt x
  have hi : data.baseSet i ∈ 𝓝 x :=
    (data.isOpen_baseSet i).mem_nhds (data.mem_baseSet_at x)
  have hd := ((dualData n).localCoefficient_holomorphic IF
    (positiveSection n) (positiveSection n).contMDiff i).contMDiffAt hi
  have hs := ((powerData n).localCoefficient_holomorphic IF s s.contMDiff i).contMDiffAt hi
  apply (hd.mul hs).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y =>
    dualFiberEquiv_localTriv (powerData n) i y (positiveSection n y) (s y)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersNegative
