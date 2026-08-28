import Wikipedia.NoExoticSixSphere.SupportedModTwoCohomology
import Mathlib.Topology.Sets.Compacts
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# The directed limit of genuine compact-supported cohomology groups

The components are the original relative cohomology groups of compact
support complements. Transition maps are the proved identity-pair
precomposition maps. This constructs compact-support cohomology from
those actual maps, without assigning any expected cohomology groups.
-/

noncomputable section

open TopologicalSpace
open Wikipedia.HopfProblem

namespace NoExoticSixSphere.CompactSupportCohomology

variable (X : Type) [TopologicalSpace X] (p : ℕ)

/-- The original relative cohomology at this compact support. -/
abbrev Component (K : Compacts X) : Type :=
  SupportedModTwoCohomology.Cohomology (K : Set X) p

/-- The original support-extension map in the compact-support diagram. -/
def transition (K L : Compacts X) (h : K ≤ L) : Component X p K →ₗ[ℤ] Component X p L :=
  SupportedModTwoCohomology.extend h p

instance directedSystem : DirectedSystem (Component X p) (transition X p · · ·) where
  map_self {K} a := LinearMap.congr_fun
    (SupportedModTwoCohomology.extend_refl (K : Set X) p) a
  map_map {_N _L _K} hKL hLN a :=
    (LinearMap.congr_fun (SupportedModTwoCohomology.extend_trans hKL hLN p) a).symm

/-- Compact-support cohomology is the directed limit of these actual relative groups. -/
abbrev Cohomology : Type := DirectLimit (Component X p) (transition X p)

/-- The original map from a compact-supported relative class to the direct limit. -/
def of (K : Compacts X) : Component X p K →ₗ[ℤ] Cohomology X p :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    (DirectLimit.Module.of ℤ (Compacts X) (Component X p) (transition X p) K).toAddMonoidHom

theorem of_transition {K L : Compacts X} (h : K ≤ L) (a : Component X p K) :
    of X p L (transition X p K L h a) = of X p K a :=
  DirectLimit.Module.of_f (R := ℤ) (f := transition X p) (i := K) (j := L) (hij := h) (x := a)

/-- Every direct-limit class has an actual compact-supported relative representative. -/
theorem exists_representative (a : Cohomology X p) :
    ∃ (K : Compacts X) (b : Component X p K), of X p K b = a := by
  induction a using DirectLimit.induction with
  | _ K a => exact ⟨K, a, rfl⟩

/-- Equality means actual agreement after extending to a common compact support. -/
theorem of_eq_iff (K L : Compacts X) (a : Component X p K) (b : Component X p L) :
    of X p K a = of X p L b ↔
      ∃ (N : Compacts X) (hK : K ≤ N) (hL : L ≤ N),
        transition X p K N hK a = transition X p L N hL b :=
  Quotient.eq

/-- The universal linear map for a compatible family on the original components. -/
def lift {P : Type} [AddCommGroup P] [Module ℤ P]
    (f : ∀ K : Compacts X, Component X p K →ₗ[ℤ] P)
    (hf : ∀ (K L : Compacts X) (h : K ≤ L) (a : Component X p K),
      f L (transition X p K L h a) = f K a) : Cohomology X p →ₗ[ℤ] P :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    (DirectLimit.Module.lift ℤ (Compacts X) (Component X p) (transition X p) f hf).toAddMonoidHom

theorem lift_of {P : Type} [AddCommGroup P] [Module ℤ P]
    (f : ∀ K : Compacts X, Component X p K →ₗ[ℤ] P)
    (hf : ∀ (K L : Compacts X) (h : K ≤ L) (a : Component X p K),
      f L (transition X p K L h a) = f K a) (K : Compacts X) (a : Component X p K) :
    lift X p f hf (of X p K a) = f K a := rfl

end NoExoticSixSphere.CompactSupportCohomology
