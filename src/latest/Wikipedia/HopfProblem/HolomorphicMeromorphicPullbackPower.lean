import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackLocalDiffeomorph
import Wikipedia.HopfProblem.RiemannMappingBiholomorph
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Canonical meromorphic values under actual positive power maps

The complex power map is genuinely open and is a native local
biholomorphism away from zero. Its meromorphic pullback therefore
commutes with canonical ordinary scalar values away from zero, including
at poles of the target section.
-/

noncomputable section

open Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

/-- The actual ambient holomorphic power map on the standard complex plane. -/
def powerMap (n : ℕ) : ContMDiffMap 𝓘(ℂ) 𝓘(ℂ) ℂ ℂ ω :=
  ⟨fun z => z ^ n, (contDiff_id.pow n).contMDiff⟩

@[simp] theorem powerMap_apply (n : ℕ) (z : ℂ) : powerMap n z = z ^ n := rfl

theorem powerMap_isOpenMap (n : ℕ) (hn : 0 < n) : IsOpenMap (powerMap n) := by
  let _ : NeZero n := ⟨hn.ne'⟩
  exact (Complex.isOpenQuotientMap_pow n).isOpenMap

/-- Away from zero, the nonzero power derivative supplies a true local
analytic inverse in the original standard plane atlas. -/
theorem powerMap_isLocalDiffeomorphAt (n : ℕ) (hn : 0 < n) (z : ℂ) (hz : z ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (powerMap n) z := by
  let U : Opens ℂ := ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩
  change IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w : ℂ => w ^ n) z
  apply RiemannMapping.isLocalDiffeomorphAt_of_deriv_ne_zero U
    (differentiable_id.pow n).differentiableOn _ hz
  intro w hw
  change deriv (fun v : ℂ => v ^ n) w ≠ 0
  rw [deriv_pow_field]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (pow_ne_zero _ hw)

theorem regularAt_power_pullback_iff (n : ℕ) (hn : 0 < n)
    {U : Opens ℂ} (s : Section 𝓘(ℂ) ℂ U)
    (z : pullbackOpen 𝓘(ℂ) 𝓘(ℂ) (powerMap n) U) (hz : z.val ≠ 0) :
    RegularAt 𝓘(ℂ) ℂ (pullbackSection 𝓘(ℂ) 𝓘(ℂ) (powerMap n)
      (powerMap_isOpenMap n hn) U s) z ↔
      RegularAt 𝓘(ℂ) ℂ s (pullbackPoint 𝓘(ℂ) 𝓘(ℂ) (powerMap n) U z) :=
  regularAt_pullbackSection_iff_of_isLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) (powerMap n)
    (powerMap_isOpenMap n hn) s z (powerMap_isLocalDiffeomorphAt n hn z.val hz)

theorem value_power_pullback (n : ℕ) (hn : 0 < n)
    {U : Opens ℂ} (s : Section 𝓘(ℂ) ℂ U)
    (z : pullbackOpen 𝓘(ℂ) 𝓘(ℂ) (powerMap n) U) (hz : z.val ≠ 0) :
    value 𝓘(ℂ) ℂ (pullbackSection 𝓘(ℂ) 𝓘(ℂ) (powerMap n)
      (powerMap_isOpenMap n hn) U s) z =
      value 𝓘(ℂ) ℂ s (pullbackPoint 𝓘(ℂ) 𝓘(ℂ) (powerMap n) U z) :=
  value_pullbackSection_of_isLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) (powerMap n)
    (powerMap_isOpenMap n hn) s z (powerMap_isLocalDiffeomorphAt n hn z.val hz)

theorem scalarValue_power_pullback (n : ℕ) (hn : 0 < n)
    {U : Opens ℂ} (s : Section 𝓘(ℂ) ℂ U) (z : ℂ) (hz : z ≠ 0) :
    scalarValue (pullbackSection 𝓘(ℂ) 𝓘(ℂ) (powerMap n)
      (powerMap_isOpenMap n hn) U s) z = scalarValue s (z ^ n) :=
  scalarValue_pullbackSection_of_isLocalDiffeomorphAt (powerMap n)
    (powerMap_isOpenMap n hn) s z (powerMap_isLocalDiffeomorphAt n hn z hz)

/-- The exact scalar composition law holds on the full punctured plane,
and hence on a punctured neighborhood of the ramification point. -/
theorem scalarValue_power_pullback_eventuallyEq_zero (n : ℕ) (hn : 0 < n)
    {U : Opens ℂ} (s : Section 𝓘(ℂ) ℂ U) :
    scalarValue (pullbackSection 𝓘(ℂ) 𝓘(ℂ) (powerMap n)
      (powerMap_isOpenMap n hn) U s) =ᶠ[𝓝[≠] 0] fun z => scalarValue s (z ^ n) := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact scalarValue_power_pullback n hn s z hz

end Wikipedia.HopfProblem.HolomorphicMeromorphic
