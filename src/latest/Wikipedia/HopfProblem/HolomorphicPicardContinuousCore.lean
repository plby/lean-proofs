import Wikipedia.HopfProblem.HolomorphicPicardContinuousCoreBasic
import Wikipedia.HopfProblem.HolomorphicPicardContinuousCoreContinuity

/-!
# An actual continuous fibre-linear trivialization of the native cocycle bundle

Compatible continuous nonzero coordinates on the original cover give a
homeomorphism from the original cocycle core's total space to the ordinary
product with the complex line. Its maps on the original fibres are genuine
complex-linear equivalences. The continuity proofs use the original native
local trivializations, rather than changing the total-space topology.
-/

noncomputable section

open Bundle TopologicalSpace

namespace Wikipedia.HopfProblem.HolomorphicPicard.ContinuousCore

open HolomorphicPicardNative HolomorphicExponentialSheaf
open HolomorphicFunctionSheaf.SphereH1

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type} (U : ι → Opens M) (hU : ∀ x : M, ∃ i : ι, x ∈ U i)
  (c : CechOneCocycle (unitsSheaf I M) U)
  (a : ∀ i : ι, C(U i, ℂ))
  (hne : ∀ i (x : U i), a i x ≠ 0)
  (hcompat : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
    unitSectionEval (c.value i j) ⟨x, hi, hj⟩ * a i ⟨x, hi⟩ = a j ⟨x, hj⟩)

local notation "Z" => cocycleCore I M U hU c

include hne in
/-- Division by the actual preferred section coordinate is complex-linear on each native fibre. -/
def fiberEquiv (x : M) : (Z).Fiber x ≃ₗ[ℂ] ℂ where
  toFun v := id (α := ℂ) v / preferredCoordinate I M U hU c a x
  invFun z := preferredCoordinate I M U hU c a x * z
  left_inv v := by
    change preferredCoordinate I M U hU c a x *
      (id (α := ℂ) v / preferredCoordinate I M U hU c a x) = v
    field_simp [preferredCoordinate_ne_zero I M U hU c a hne x]
    rfl
  right_inv z := by
    change (preferredCoordinate I M U hU c a x * z) /
      preferredCoordinate I M U hU c a x = z
    exact mul_div_cancel_left₀ z (preferredCoordinate_ne_zero I M U hU c a hne x)
  map_add' v w := by
    change (id (α := ℂ) v + id (α := ℂ) w) / preferredCoordinate I M U hU c a x =
      id (α := ℂ) v / preferredCoordinate I M U hU c a x +
        id (α := ℂ) w / preferredCoordinate I M U hU c a x
    exact add_div _ _ _
  map_smul' r v := by
    change (r * id (α := ℂ) v) / preferredCoordinate I M U hU c a x =
      r * (id (α := ℂ) v / preferredCoordinate I M U hU c a x)
    exact mul_div_assoc _ _ _

@[simp] theorem fiberEquiv_apply (x : M) (v : (Z).Fiber x) :
    fiberEquiv I M U hU c a hne x v =
      id (α := ℂ) v / preferredCoordinate I M U hU c a x := rfl

@[simp] theorem fiberEquiv_symm_apply (x : M) (z : ℂ) :
    (fiberEquiv I M U hU c a hne x).symm z =
      preferredCoordinate I M U hU c a x * z := rfl

include hne hcompat in
/-- The homeomorphism is between the original native total space and the standard product. -/
def productHomeomorph : (Z).TotalSpace ≃ₜ M × ℂ where
  toFun := toProduct I M U hU c a
  invFun := fromProduct I M U hU c a
  left_inv := fromProduct_toProduct I M U hU c a hne
  right_inv := toProduct_fromProduct I M U hU c a hne
  continuous_toFun := toProduct_continuous I M U hU c a hne hcompat
  continuous_invFun := fromProduct_continuous I M U hU c a hcompat

@[simp] theorem productHomeomorph_apply (p : (Z).TotalSpace) :
    productHomeomorph I M U hU c a hne hcompat p =
      (p.proj, id (α := ℂ) p.2 / preferredCoordinate I M U hU c a p.proj) := rfl

@[simp] theorem productHomeomorph_symm_apply (p : M × ℂ) :
    (productHomeomorph I M U hU c a hne hcompat).symm p =
      ⟨p.1, preferredCoordinate I M U hU c a p.1 * p.2⟩ := rfl

include hne hcompat in
/-- A compatible actual continuous nonzero section trivializes the original native bundle. -/
def trivialization : ContinuousTrivialization (Z).Fiber where
  homeomorph := productHomeomorph I M U hU c a hne hcompat
  fiberEquiv := fiberEquiv I M U hU c a hne
  map_fiber _ _ := rfl

@[simp] theorem trivialization_homeomorph_apply (p : (Z).TotalSpace) :
    (trivialization I M U hU c a hne hcompat).homeomorph p =
      (p.proj, id (α := ℂ) p.2 / preferredCoordinate I M U hU c a p.proj) := rfl

@[simp] theorem trivialization_fiberEquiv_apply (x : M) (v : (Z).Fiber x) :
    (trivialization I M U hU c a hne hcompat).fiberEquiv x v =
      id (α := ℂ) v / preferredCoordinate I M U hU c a x := rfl

end Wikipedia.HopfProblem.HolomorphicPicard.ContinuousCore
