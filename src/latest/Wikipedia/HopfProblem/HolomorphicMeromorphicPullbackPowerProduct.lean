import Wikipedia.HopfProblem.HolomorphicMeromorphicValueCongr
import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackPower
import Wikipedia.HopfProblem.HolomorphicMeromorphicProductRegularity

/-!
# Canonical values for the actual power of a product projection

The map `(z, v) ↦ zⁿ` is the literal composition of the native product
projection with the positive complex power map. The proved composition
law for genuine meromorphic pullback, projection regularity reflection,
and the power-map value formula give its canonical scalar values away
from the ramification divisor, including at poles.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IP" => modelWithCornersSelf ℂ (ℂ × E)

/-- The actual holomorphic map from the native product space to the
standard complex plane given by the positive power of its first coordinate. -/
def powerFstMap (n : ℕ) : ContMDiffMap IP I₁ (ℂ × E) ℂ ω :=
  (powerMap n).comp ProductDescent.fstMap

@[simp] theorem powerFstMap_apply (n : ℕ) (x : ℂ × E) :
    powerFstMap n x = x.1 ^ n := rfl

theorem powerFstMap_isOpenMap (n : ℕ) (hn : 0 < n) :
    IsOpenMap (powerFstMap (E := E) n) :=
  (powerMap_isOpenMap n hn).comp ProductDescent.fstMap_isOpenMap

/-- The pullback by the actual power-projection map is the genuine
iterated pullback, by the already proved native composition law. -/
theorem pullbackSection_powerFst (n : ℕ) (hn : 0 < n) (U : Opens ℂ)
    (s : Section I₁ ℂ U) :
    pullbackSection IP I₁ (powerFstMap n) (powerFstMap_isOpenMap n hn) U s =
      pullbackSection IP I₁ ProductDescent.fstMap ProductDescent.fstMap_isOpenMap
        (pullbackOpen I₁ I₁ (powerMap n) U)
        (pullbackSection I₁ I₁ (powerMap n) (powerMap_isOpenMap n hn) U s) :=
  (pullbackSection_comp IP I₁ I₁ ProductDescent.fstMap ProductDescent.fstMap_isOpenMap
    (powerMap n) (powerMap_isOpenMap n hn) U s).symm

/-- Away from the zero first-coordinate divisor, the actual power-projection
pullback preserves and reflects regularity of the native base germ. -/
theorem regularAt_powerFst_pullback_iff (n : ℕ) (hn : 0 < n)
    {U : Opens ℂ} (s : Section I₁ ℂ U)
    (x : pullbackOpen IP I₁ (powerFstMap n) U) (hx : x.val.1 ≠ 0) :
    RegularAt IP (ℂ × E)
        (pullbackSection IP I₁ (powerFstMap n) (powerFstMap_isOpenMap n hn) U s) x ↔
      RegularAt I₁ ℂ s (pullbackPoint IP I₁ (powerFstMap n) U x) := by
  have he := congrArg
    (fun a : Section IP (ℂ × E) (pullbackOpen IP I₁ (powerFstMap n) U) =>
      RegularAt IP (ℂ × E) a x) (pullbackSection_powerFst n hn U s)
  exact (Iff.of_eq he).trans
    ((ProductDescent.regularAt_fst_pullback_iff
      (pullbackSection I₁ I₁ (powerMap n) (powerMap_isOpenMap n hn) U s) x).trans
      (regularAt_power_pullback_iff n hn s
        (pullbackPoint IP I₁ ProductDescent.fstMap (pullbackOpen I₁ I₁ (powerMap n) U) x) hx))

/-- Canonical values of the actual power-projection pullback are exactly
the base scalar values at the powered first coordinate. No regularity
assumption is imposed on either germ. -/
theorem value_powerFst_pullback (n : ℕ) (hn : 0 < n)
    {U : Opens ℂ} (s : Section I₁ ℂ U)
    (x : pullbackOpen IP I₁ (powerFstMap n) U) (hx : x.val.1 ≠ 0) :
    value IP (ℂ × E)
      (pullbackSection IP I₁ (powerFstMap n) (powerFstMap_isOpenMap n hn) U s) x =
      scalarValue s (x.val.1 ^ n) := by
  let sp := pullbackSection I₁ I₁ (powerMap n) (powerMap_isOpenMap n hn) U s
  have he := congrArg
    (fun a : Section IP (ℂ × E) (pullbackOpen IP I₁ (powerFstMap n) U) =>
      value IP (ℂ × E) a x) (pullbackSection_powerFst n hn U s)
  exact he.trans ((ProductDescent.value_fst_pullback sp x).trans
    ((scalarValue_apply sp x.val.1 x.property).symm.trans
      (scalarValue_power_pullback n hn s x.val.1 hx)))

end Wikipedia.HopfProblem.HolomorphicMeromorphic
