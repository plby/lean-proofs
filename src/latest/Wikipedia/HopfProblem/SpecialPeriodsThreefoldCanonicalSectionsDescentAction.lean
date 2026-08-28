import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsDescentAnalytic

/-!
# Descent from differential invariance under an actual group action

For a quotient whose fibres are the actual group orbits, invariance of a
canonical section under derivative pullback implies fibre compatibility.
The proof uses the native manifold-derivative chain rule for `q ∘ g = q`,
with equality transport between the literal quotient fibres.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsDescent

open _root_.Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

local notation "I" => modelWithCornersSelf ℂ Model

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]
  [TopologicalSpace N] [ChartedSpace Model N] [IsManifold I ω N]

/-- Equality of base maps gives the same intrinsic pullback, with literal
equality transport on the source canonical fibre. -/
theorem pullbackLinear_congr_transport {f g : M → N} (h : f = g) (x : M)
    (v : (Atlas.core N).Fiber (f x)) :
    pullbackLinear f x v = pullbackLinear g x (fiberTransport (congrFun h x) v) := by
  subst g
  rfl

/-- The derivative pullback identity for an actual local biholomorphism
which preserves the quotient map. -/
theorem pullback_quotient_preserving_map {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) {a : M → M}
    (ha : IsLocalDiffeomorph I I ω a) (hqa : ∀ x, q (a x) = q x)
    (x : M) (v : (Atlas.core N).Fiber (q x)) :
    pullbackEquiv ha x
      (pullbackEquiv hq (a x) (fiberTransport (hqa x).symm v)) =
        pullbackEquiv hq x v := by
  have hfun : q ∘ a = q := funext hqa
  have hcomp := pullbackLinear_comp ((ha x).mdifferentiableAt (by simp))
    ((hq (a x)).mdifferentiableAt (by simp))
  have htransport : fiberTransport (congrFun hfun x) (fiberTransport (hqa x).symm v) = v :=
    (fiberTransport_apply (congrFun hfun x) _).trans
      (fiberTransport_apply (hqa x).symm v)
  calc
    _ = pullbackLinear (q ∘ a) x (fiberTransport (hqa x).symm v) :=
      (congrArg (fun A => A (fiberTransport (hqa x).symm v)) hcomp).symm
    _ = pullbackLinear q x
        (fiberTransport (congrFun hfun x) (fiberTransport (hqa x).symm v)) :=
      pullbackLinear_congr_transport hfun x (fiberTransport (hqa x).symm v)
    _ = pullbackEquiv hq x v := congrArg (pullbackLinear q x) htransport

variable {G : Type*} [Group G] [MulAction G M]

/-- Differential invariance under the actual action implies precisely the
fibre compatibility needed for genuine canonical-section descent. -/
theorem compatible_of_action_invariant {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q)
    (hA : ∀ g : G, IsLocalDiffeomorph I I ω (fun x : M => g • x))
    (hqA : ∀ (g : G) (x : M), q (g • x) = q x)
    (hOrbits : ∀ x y : M, q x = q y → ∃ g : G, g • x = y)
    (s : Section M)
    (hs : ∀ (g : G) (x : M), pullbackEquiv (hA g) x (s (g • x)) = s x) :
    Compatible hq s := by
  apply (compatible_iff_fiberTransport hq s).mpr
  intro x y hxy
  obtain ⟨g, rfl⟩ := hOrbits x y hxy
  change fiberTransport (hqA g x).symm ((pullbackEquiv hq x).symm (s x)) =
    (pullbackEquiv hq (g • x)).symm (s (g • x))
  apply (pullbackEquiv hq (g • x)).injective
  apply (pullbackEquiv (hA g) x).injective
  calc
    _ = pullbackEquiv hq x ((pullbackEquiv hq x).symm (s x)) :=
      pullback_quotient_preserving_map hq (hA g) (hqA g) x
        ((pullbackEquiv hq x).symm (s x))
    _ = s x := (pullbackEquiv hq x).apply_symm_apply (s x)
    _ = pullbackEquiv (hA g) x (s (g • x)) := (hs g x).symm
    _ = _ := congrArg (pullbackEquiv (hA g) x)
      ((pullbackEquiv hq (g • x)).apply_symm_apply (s (g • x))).symm

/-- Invariant holomorphic canonical sections descend uniquely through a
surjective quotient by the actual action, without a finiteness assumption. -/
theorem existsUnique_holomorphic_descent_of_action_invariant {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (hA : ∀ g : G, IsLocalDiffeomorph I I ω (fun x : M => g • x))
    (hqA : ∀ (g : G) (x : M), q (g • x) = q x)
    (hOrbits : ∀ x y : M, q x = q y → ∃ g : G, g • x = y)
    (s : ContMDiffSection I ℂ ω (Atlas.core M).Fiber)
    (hs : ∀ (g : G) (x : M), pullbackEquiv (hA g) x (s (g • x)) = s x) :
    ∃! t : ContMDiffSection I ℂ ω (Atlas.core N).Fiber,
      ∀ x, pullbackEquiv hq x (t (q x)) = s x :=
  existsUnique_holomorphic_descent hq hsurj s
    (compatible_of_action_invariant hq hA hqA hOrbits s hs)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsDescent
