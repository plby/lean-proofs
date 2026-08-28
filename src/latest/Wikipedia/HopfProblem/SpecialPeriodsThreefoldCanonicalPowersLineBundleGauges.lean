import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleRefinementGauge
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleTensor

/-!
# Native holomorphic comparisons of line-bundle powers

Power, iteration, and tensor-product identities are implemented by
holomorphic gauges of the actual cocycles.  Their associated maps are
therefore fibrewise-linear biholomorphisms for the original native
bundle atlases, not just equalities between names for line bundles.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M ι κ : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] {I : ModelWithCorners ℂ E H}

local notation "I₁" => modelWithCornersSelf ℂ ℂ

namespace CrossGauge

variable {A : TransitionData M ι} {B : TransitionData M κ} (G : CrossGauge I A B)

/-- Raising the actual chart comparison units to a natural power gives
a genuine comparison of the native power bundles on the same two covers. -/
def power (n : ℕ) : CrossGauge I (A.power n) (B.power n) where
  value i x := G.value i x ^ n
  compatible i j x hx := by
    change B.transition i.2 j.2 x ^ n * G.value i x ^ n =
      G.value j x ^ n * A.transition i.1 j.1 x ^ n
    rw [← mul_pow, ← mul_pow, G.compatible i j x hx]
  holomorphicOn i := by
    simpa only [Units.val_pow_eq_pow_val, TransitionData.power_baseSet] using
      (G.holomorphicOn i).pow n

@[simp] theorem power_value (n : ℕ) (i : ι × κ) (x : M) :
    (G.power n).value i x = G.value i x ^ n := rfl

/-- Exact action on the actual preferred scalar fibre. -/
theorem power_fiberEquiv_apply (n : ℕ) (x : M) (v : (A.power n).core.Fiber x) :
    (G.power n).fiberEquiv x v =
      (G.value (A.indexAt x, B.indexAt x) x : ℂ) ^ n * id (α := ℂ) v := by
  rw [fiberEquiv_apply]
  rfl

/-- Powering a genuine fibre vector commutes with the induced comparison. -/
theorem power_fiberEquiv_pow (n : ℕ) (x : M) (v : A.core.Fiber x) :
    (G.power n).fiberEquiv x (id (α := ℂ) v ^ n) =
      id (α := ℂ) (G.fiberEquiv x v) ^ n := by
  have hv : id (α := ℂ) (G.fiberEquiv x v) =
      (G.value (A.indexAt x, B.indexAt x) x : ℂ) * id (α := ℂ) v :=
    G.fiberEquiv_apply x v
  have hp : id (α := ℂ) ((G.power n).fiberEquiv x (id (α := ℂ) v ^ n)) =
      (G.value (A.indexAt x, B.indexAt x) x : ℂ) ^ n * (id (α := ℂ) v ^ n) :=
    G.power_fiberEquiv_apply n x (id (α := ℂ) v ^ n)
  exact hp.trans ((mul_pow (G.value (A.indexAt x, B.indexAt x) x : ℂ)
    (id (α := ℂ) v) n).symm.trans (congrArg (fun c : ℂ => c ^ n) hv.symm))

end CrossGauge

namespace Powers

variable (I) (A : TransitionData M ι) (B : TransitionData M κ)

/-- The first-power bundle is compared with the original bundle by
identity coefficients in every original chart. -/
def onePowerGauge : Gauge I (A.power 1) A where
  baseSet_eq := rfl
  value _ _ := 1
  compatible i j x _ := by simp only [TransitionData.power_transition, pow_one, mul_one, one_mul]
  holomorphicOn _ := contMDiffOn_const

/-- Iterated native power bundles are compared without identifying
their total-space topologies by fiat. -/
def iteratePowerGauge (m n : ℕ) : Gauge I ((A.power m).power n) (A.power (m * n)) where
  baseSet_eq := rfl
  value _ _ := 1
  compatible i j x _ := by
    simp only [TransitionData.power_transition, mul_one, one_mul, pow_mul]
  holomorphicOn _ := contMDiffOn_const

/-- Exchanging two successive powers gives a genuine native comparison,
avoiding dependent casts when relating squares of pluricanonical sections. -/
def powerSwapGauge (m n : ℕ) : Gauge I ((A.power m).power n) ((A.power n).power m) where
  baseSet_eq := rfl
  value _ _ := 1
  compatible i j x _ := by
    simp only [TransitionData.power_transition, mul_one, one_mul, ← pow_mul, Nat.mul_comm]
  holomorphicOn _ := contMDiffOn_const

/-- A tensor power distributes over the two actual cocycles, on their
literal paired intersection cover. -/
def tensorPowerGauge (n : ℕ) :
    Gauge I ((tensor A B).power n) (tensor (A.power n) (B.power n)) where
  baseSet_eq := rfl
  value _ _ := 1
  compatible i j x _ := by
    simp only [TransitionData.power_transition, tensor_transition, mul_one, one_mul, mul_pow]
  holomorphicOn _ := contMDiffOn_const

theorem onePowerGauge_preferredMultiplier (x : M) :
    (onePowerGauge I A).preferredMultiplier x = 1 := by
  change A.transition (A.indexAt x) (A.indexAt x) x * 1 = 1
  rw [A.transition_self _ _ (A.mem_baseSet_at x), mul_one]

theorem iteratePowerGauge_preferredMultiplier (m n : ℕ) (x : M) :
    (iteratePowerGauge I A m n).preferredMultiplier x = 1 := by
  change A.transition (A.indexAt x) (A.indexAt x) x ^ (m * n) * 1 = 1
  rw [A.transition_self _ _ (A.mem_baseSet_at x), one_pow, mul_one]

theorem powerSwapGauge_preferredMultiplier (m n : ℕ) (x : M) :
    (powerSwapGauge I A m n).preferredMultiplier x = 1 := by
  change (A.transition (A.indexAt x) (A.indexAt x) x ^ n) ^ m * 1 = 1
  rw [A.transition_self _ _ (A.mem_baseSet_at x), one_pow, one_pow, mul_one]

theorem tensorPowerGauge_preferredMultiplier (n : ℕ) (x : M) :
    (tensorPowerGauge I A B n).preferredMultiplier x = 1 := by
  change (A.transition (A.indexAt x) (A.indexAt x) x ^ n *
    B.transition (B.indexAt x) (B.indexAt x) x ^ n) * 1 = 1
  simp only [A.transition_self _ _ (A.mem_baseSet_at x),
    B.transition_self _ _ (B.mem_baseSet_at x), one_pow, mul_one]

theorem onePowerGauge_fiberEquiv_apply (x : M) (v : (A.power 1).core.Fiber x) :
    (onePowerGauge I A).fiberEquiv x v = id (α := ℂ) v := by
  change ((onePowerGauge I A).preferredMultiplier x : ℂ) * id (α := ℂ) v = _
  rw [onePowerGauge_preferredMultiplier]
  exact one_mul _

theorem iteratePowerGauge_fiberEquiv_apply (m n : ℕ) (x : M)
    (v : ((A.power m).power n).core.Fiber x) :
    (iteratePowerGauge I A m n).fiberEquiv x v = id (α := ℂ) v := by
  change ((iteratePowerGauge I A m n).preferredMultiplier x : ℂ) * id (α := ℂ) v = _
  rw [iteratePowerGauge_preferredMultiplier]
  exact one_mul _

theorem powerSwapGauge_fiberEquiv_apply (m n : ℕ) (x : M)
    (v : ((A.power m).power n).core.Fiber x) :
    (powerSwapGauge I A m n).fiberEquiv x v = id (α := ℂ) v := by
  change ((powerSwapGauge I A m n).preferredMultiplier x : ℂ) * id (α := ℂ) v = _
  rw [powerSwapGauge_preferredMultiplier]
  exact one_mul _

theorem tensorPowerGauge_fiberEquiv_apply (n : ℕ) (x : M)
    (v : ((tensor A B).power n).core.Fiber x) :
    (tensorPowerGauge I A B n).fiberEquiv x v = id (α := ℂ) v := by
  change ((tensorPowerGauge I A B n).preferredMultiplier x : ℂ) * id (α := ℂ) v = _
  rw [tensorPowerGauge_preferredMultiplier]
  exact one_mul _

end Powers

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle
