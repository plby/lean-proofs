import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionExponentialCore
import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyBase
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# Actual analytic local sections of the normalized exponential

The nonzero complex numbers have Mathlib's existing manifold structure
on `ℂˣ`, given by their open embedding into `ℂ`. The inverse-function
charts of the literal normalized exponential give local logarithms in
these charts, including both inverse identities.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Exponential

open CuspUniformization

theorem normalizedExponential_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω normalizedExponential := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  exact exponential_holomorphic.contMDiff

/-- An actual inverse-function chart of the normalized exponential,
with the inherited nonzero-complex target atlas. -/
def unitsExponentialChart (s : ℂ) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℂˣ ω where
  toFun := normalizedExponential
  invFun := (CuspFamily.scalarExponentialChart s).symm ∘ Units.val
  source := (CuspFamily.scalarExponentialChart s).source
  target := Units.val ⁻¹' (CuspFamily.scalarExponentialChart s).target
  map_source' := by
    intro t ht
    exact (CuspFamily.scalarExponentialChart s).map_source ht
  map_target' := by
    intro t ht
    exact (CuspFamily.scalarExponentialChart s).map_target ht
  left_inv' := by
    intro t ht
    exact (CuspFamily.scalarExponentialChart s).left_inv ht
  right_inv' := by
    intro t ht
    apply Units.ext
    exact (CuspFamily.scalarExponentialChart s).right_inv ht
  open_source := (CuspFamily.scalarExponentialChart s).open_source
  open_target := (CuspFamily.scalarExponentialChart s).open_target.preimage
    Units.continuous_val
  contMDiffOn_toFun := normalizedExponential_holomorphic.contMDiffOn
  contMDiffOn_invFun :=
    (CuspFamily.scalarExponentialChart_symm_holomorphic s).contMDiffOn.comp
      Units.contMDiff_val.contMDiffOn (fun _ ht => ht)

theorem normalizedExponential_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω normalizedExponential := by
  intro s
  exact ⟨unitsExponentialChart s, CuspFamily.scalarExponentialChart_mem_source s,
    fun _ _ => rfl⟩

theorem normalizedExponential_isOpenMap : IsOpenMap normalizedExponential :=
  normalizedExponential_isLocalDiffeomorph.isOpenMap

theorem normalizedExponential_continuous : Continuous normalizedExponential :=
  normalizedExponential_holomorphic.continuous

/-- The local logarithm through the specified lift `s`, obtained from
the actual scalar exponential chart. -/
def localLogarithm (s : ℂ) : ℂˣ → ℂ :=
  (CuspFamily.scalarExponentialChart s).symm ∘ Units.val

theorem localLogarithm_holomorphicOn (s : ℂ) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localLogarithm s)
      (Units.val ⁻¹' (CuspFamily.scalarExponentialChart s).target) :=
  (unitsExponentialChart s).contMDiffOn_invFun

theorem localLogarithm_holomorphicAt (s : ℂ) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (localLogarithm s) (normalizedExponential s) := by
  apply (localLogarithm_holomorphicOn s).contMDiffAt
  exact (unitsExponentialChart s).open_target.mem_nhds
    ((unitsExponentialChart s).map_source (CuspFamily.scalarExponentialChart_mem_source s))

theorem localLogarithm_left_inv (s t : ℂ)
    (ht : t ∈ (CuspFamily.scalarExponentialChart s).source) :
    localLogarithm s (normalizedExponential t) = t :=
  (unitsExponentialChart s).left_inv ht

theorem localLogarithm_right_inv (s : ℂ) (t : ℂˣ)
    (ht : (t : ℂ) ∈ (CuspFamily.scalarExponentialChart s).target) :
    normalizedExponential (localLogarithm s t) = t :=
  (unitsExponentialChart s).right_inv ht

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Exponential
