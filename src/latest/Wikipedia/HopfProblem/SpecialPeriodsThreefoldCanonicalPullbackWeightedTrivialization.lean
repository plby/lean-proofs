import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackWeighted

/-!
# Actual canonical-bundle trivializations as local biholomorphisms

The canonical bundle's existing local trivializations have holomorphic
forward and inverse maps in the original total-space and product atlases.
They therefore supply genuine partial diffeomorphisms without changing
either topology or manifold structure.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]

/-- The actual canonical local trivialization, bundled with its original
open sets and both holomorphicity proofs. -/
def localTrivPartialDiffeomorph (i : atlas Model M) :
    PartialDiffeomorph ((I).prod I₁) ((I).prod I₁)
      (Atlas.core M).TotalSpace (M × ℂ) ω where
  __ := ((Atlas.core M).localTriv i).toOpenPartialHomeomorph
  contMDiffOn_toFun := ((Atlas.core M).localTriv i).contMDiffOn
  contMDiffOn_invFun := ((Atlas.core M).localTriv i).contMDiffOn_symm

@[simp] theorem localTrivPartialDiffeomorph_source (i : atlas Model M) :
    (localTrivPartialDiffeomorph i).source = ((Atlas.core M).localTriv i).source := rfl

@[simp] theorem localTrivPartialDiffeomorph_target (i : atlas Model M) :
    (localTrivPartialDiffeomorph i).target = ((Atlas.core M).localTriv i).target := rfl

@[simp] theorem localTrivPartialDiffeomorph_apply (i : atlas Model M)
    (p : (Atlas.core M).TotalSpace) :
    localTrivPartialDiffeomorph i p = (Atlas.core M).localTriv i p := rfl

@[simp] theorem localTrivPartialDiffeomorph_symm_apply (i : atlas Model M) (p : M × ℂ) :
    (localTrivPartialDiffeomorph i).symm p =
      ((Atlas.core M).localTriv i).toOpenPartialHomeomorph.symm p := rfl

/-- The original local trivialization is locally biholomorphic at every
point whose base lies in the chart source. -/
theorem localTriv_isLocalDiffeomorphAt (i : atlas Model M)
    {p : (Atlas.core M).TotalSpace} (hp : p.proj ∈ i.val.source) :
    IsLocalDiffeomorphAt ((I).prod I₁) ((I).prod I₁) ω
      ((Atlas.core M).localTriv i) p :=
  (localTrivPartialDiffeomorph i).isLocalDiffeomorphAt _ _ _ hp

/-- The inverse original local trivialization is locally biholomorphic
throughout the ordinary product chart target. -/
theorem localTriv_symm_isLocalDiffeomorphAt (i : atlas Model M)
    {p : M × ℂ} (hp : p.1 ∈ i.val.source) :
    IsLocalDiffeomorphAt ((I).prod I₁) ((I).prod I₁) ω
      ((Atlas.core M).localTriv i).toOpenPartialHomeomorph.symm p :=
  (localTrivPartialDiffeomorph i).symm.isLocalDiffeomorphAt _ _ _ ⟨hp, mem_univ _⟩

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback
