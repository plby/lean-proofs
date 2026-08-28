import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleRefinementNativeData
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleRefinementNativeComparison

/-!
# Actual native bundle isomorphisms for the common-cover refinements

The paired cover refines both original covers.  Keeping each original
cocycle on that paired cover gives a genuine holomorphic line bundle
biholomorphic to the original, by the identity in preferred fibre
coordinates.  The biholomorphisms commute exactly with the original
and refined local trivializations, even as total functions outside the
chart domains.  No atlas or topology is transported or replaced.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M ι κ : Type*} [TopologicalSpace M]
  (A : TransitionData M ι) (B : TransitionData M κ)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

section Left

variable [A.IsHolomorphic I]

/-- Refining the left bundle's cover preserves its actual holomorphic
bundle, via the identity in preferred fibre coordinates. -/
def leftRefinementDiffeomorph : Diffeomorph (I.prod I₁) (I.prod I₁)
    A.core.TotalSpace (leftRefinement A B).core.TotalSpace ω :=
  RefinementNative.diffeomorph A (leftRefinement A B) I Prod.fst
    (fun _ _ hp => hp.1) (fun _ _ => rfl)

@[simp] theorem leftRefinementDiffeomorph_apply (p : A.core.TotalSpace) :
    leftRefinementDiffeomorph A B I p = ⟨p.proj, id (α := ℂ) p.2⟩ := rfl

@[simp] theorem leftRefinementDiffeomorph_symm_apply
    (p : (leftRefinement A B).core.TotalSpace) :
    (leftRefinementDiffeomorph A B I).symm p = ⟨p.proj, id (α := ℂ) p.2⟩ := rfl

@[simp] theorem leftRefinementDiffeomorph_proj (p : A.core.TotalSpace) :
    (leftRefinementDiffeomorph A B I p).proj = p.proj := rfl

@[simp] theorem leftRefinementDiffeomorph_symm_proj
    (p : (leftRefinement A B).core.TotalSpace) :
    ((leftRefinementDiffeomorph A B I).symm p).proj = p.proj := rfl

/-- The native biholomorphism restricts to the identity continuous
complex-linear equivalence of the original and refined fibres. -/
theorem leftRefinementDiffeomorph_mk (x : M) (v : A.core.Fiber x) :
    leftRefinementDiffeomorph A B I ⟨x, v⟩ =
      ⟨x, leftRefinementFiberEquiv A B x v⟩ := rfl

theorem leftRefinementDiffeomorph_symm_mk (x : M)
    (v : (leftRefinement A B).core.Fiber x) :
    (leftRefinementDiffeomorph A B I).symm ⟨x, v⟩ =
      ⟨x, (leftRefinementFiberEquiv A B x).symm v⟩ := rfl

/-- Exact native trivialization comparison on every paired chart. -/
theorem leftRefinementDiffeomorph_localTriv (i : ι × κ) (p : A.core.TotalSpace) :
    (leftRefinement A B).core.localTriv i (leftRefinementDiffeomorph A B I p) =
      A.core.localTriv i.1 p := rfl

theorem leftRefinementDiffeomorph_symm_localTriv (i : ι × κ)
    (p : (leftRefinement A B).core.TotalSpace) :
    A.core.localTriv i.1 ((leftRefinementDiffeomorph A B I).symm p) =
      (leftRefinement A B).core.localTriv i p := rfl

end Left

section Right

variable [B.IsHolomorphic I]

/-- Refining the right bundle's cover preserves its actual holomorphic
bundle, via the identity in preferred fibre coordinates. -/
def rightRefinementDiffeomorph : Diffeomorph (I.prod I₁) (I.prod I₁)
    B.core.TotalSpace (rightRefinement A B).core.TotalSpace ω :=
  RefinementNative.diffeomorph B (rightRefinement A B) I Prod.snd
    (fun _ _ hp => hp.2) (fun _ _ => rfl)

@[simp] theorem rightRefinementDiffeomorph_apply (p : B.core.TotalSpace) :
    rightRefinementDiffeomorph A B I p = ⟨p.proj, id (α := ℂ) p.2⟩ := rfl

@[simp] theorem rightRefinementDiffeomorph_symm_apply
    (p : (rightRefinement A B).core.TotalSpace) :
    (rightRefinementDiffeomorph A B I).symm p = ⟨p.proj, id (α := ℂ) p.2⟩ := rfl

@[simp] theorem rightRefinementDiffeomorph_proj (p : B.core.TotalSpace) :
    (rightRefinementDiffeomorph A B I p).proj = p.proj := rfl

@[simp] theorem rightRefinementDiffeomorph_symm_proj
    (p : (rightRefinement A B).core.TotalSpace) :
    ((rightRefinementDiffeomorph A B I).symm p).proj = p.proj := rfl

/-- The native biholomorphism restricts to the identity continuous
complex-linear equivalence of the original and refined fibres. -/
theorem rightRefinementDiffeomorph_mk (x : M) (v : B.core.Fiber x) :
    rightRefinementDiffeomorph A B I ⟨x, v⟩ =
      ⟨x, rightRefinementFiberEquiv A B x v⟩ := rfl

theorem rightRefinementDiffeomorph_symm_mk (x : M)
    (v : (rightRefinement A B).core.Fiber x) :
    (rightRefinementDiffeomorph A B I).symm ⟨x, v⟩ =
      ⟨x, (rightRefinementFiberEquiv A B x).symm v⟩ := rfl

/-- Exact native trivialization comparison on every paired chart. -/
theorem rightRefinementDiffeomorph_localTriv (i : ι × κ) (p : B.core.TotalSpace) :
    (rightRefinement A B).core.localTriv i (rightRefinementDiffeomorph A B I p) =
      B.core.localTriv i.2 p := rfl

theorem rightRefinementDiffeomorph_symm_localTriv (i : ι × κ)
    (p : (rightRefinement A B).core.TotalSpace) :
    B.core.localTriv i.2 ((rightRefinementDiffeomorph A B I).symm p) =
      (rightRefinement A B).core.localTriv i p := rfl

end Right

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle
