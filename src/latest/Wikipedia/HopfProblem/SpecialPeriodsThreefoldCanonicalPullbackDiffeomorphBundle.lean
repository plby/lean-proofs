import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackDiffeomorph
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackBundle

/-!
# Biholomorphic canonical bundle pullback

The canonical total-space equivalence associated to an actual analytic
diffeomorphism is holomorphic in both directions for the original canonical
bundle atlases.  This follows from the already established local coefficient
formula for inverse derivative pullback.  No topology or atlas is transported
along the total-space equivalence.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]
  [TopologicalSpace N] [ChartedSpace Model N] [IsManifold I ω N]

/-- The covariant total-space map is the already constructed holomorphic
inverse-pullback map of the local biholomorphism. -/
theorem diffeomorphTotalPushforward_eq_forwardMap (e : Diffeomorph I I M N ω) :
    diffeomorphTotalPushforward e = forwardMap e.isLocalDiffeomorph := rfl

/-- Contravariant pullback is the forward map of the actual inverse
diffeomorphism, by the previously proved fibre inverse identities. -/
theorem diffeomorphTotalPullback_eq_forwardMap_symm (e : Diffeomorph I I M N ω) :
    diffeomorphTotalPullback e = forwardMap e.symm.isLocalDiffeomorph := by
  funext p
  exact (diffeomorphTotalPushforward_eq_pullback_symm e.symm p).symm

theorem diffeomorphTotalPushforward_holomorphic (e : Diffeomorph I I M N ω) :
    ContMDiff ((I).prod I₁) ((I).prod I₁) ω (diffeomorphTotalPushforward e) :=
  forwardMap_holomorphic e.isLocalDiffeomorph

/-- Pullback is holomorphic for the existing total-space structures. -/
theorem diffeomorphTotalPullback_holomorphic (e : Diffeomorph I I M N ω) :
    ContMDiff ((I).prod I₁) ((I).prod I₁) ω (diffeomorphTotalPullback e) := by
  rw [diffeomorphTotalPullback_eq_forwardMap_symm]
  exact forwardMap_holomorphic e.symm.isLocalDiffeomorph

/-- The actual canonical total spaces are biholomorphic over `e.symm`,
with the previously constructed complex-linear maps on each fibre. -/
def diffeomorphTotalBiholomorph (e : Diffeomorph I I M N ω) :
    Diffeomorph ((I).prod I₁) ((I).prod I₁)
      (Atlas.core N).TotalSpace (Atlas.core M).TotalSpace ω where
  toEquiv := diffeomorphTotalEquiv e
  contMDiff_toFun := diffeomorphTotalPullback_holomorphic e
  contMDiff_invFun := diffeomorphTotalPushforward_holomorphic e

@[simp] theorem diffeomorphTotalBiholomorph_toEquiv (e : Diffeomorph I I M N ω) :
    (diffeomorphTotalBiholomorph e).toEquiv = diffeomorphTotalEquiv e := rfl

@[simp] theorem diffeomorphTotalBiholomorph_apply (e : Diffeomorph I I M N ω)
    (p : (Atlas.core N).TotalSpace) :
    diffeomorphTotalBiholomorph e p = diffeomorphTotalPullback e p := rfl

@[simp] theorem diffeomorphTotalBiholomorph_symm_apply (e : Diffeomorph I I M N ω)
    (p : (Atlas.core M).TotalSpace) :
    (diffeomorphTotalBiholomorph e).symm p = diffeomorphTotalPushforward e p := rfl

@[simp] theorem diffeomorphTotalBiholomorph_proj (e : Diffeomorph I I M N ω)
    (p : (Atlas.core N).TotalSpace) :
    (diffeomorphTotalBiholomorph e p).proj = e.symm p.proj := rfl

@[simp] theorem diffeomorphTotalBiholomorph_symm_proj (e : Diffeomorph I I M N ω)
    (p : (Atlas.core M).TotalSpace) :
    ((diffeomorphTotalBiholomorph e).symm p).proj = e p.proj := rfl

/-- The restriction of the biholomorphism to a fibre is exactly the
equality-transported continuous linear pullback equivalence. -/
theorem diffeomorphTotalBiholomorph_mk (e : Diffeomorph I I M N ω)
    (y : N) (v : (Atlas.core N).Fiber y) :
    diffeomorphTotalBiholomorph e ⟨y, v⟩ =
      ⟨e.symm y, diffeomorphFiberPullback e y v⟩ := rfl

theorem diffeomorphTotalBiholomorph_symm_mk (e : Diffeomorph I I M N ω)
    (x : M) (v : (Atlas.core M).Fiber x) :
    (diffeomorphTotalBiholomorph e).symm ⟨x, v⟩ =
      ⟨e x, (diffeomorphPullback e x).symm v⟩ := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback
