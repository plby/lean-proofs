import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullback
import Wikipedia.HopfProblem.EllipticCyclicAction

/-!
# Differential invariance under the entire cyclic action

Invariance of a genuine canonical section under one holomorphic map
implies invariance under all its iterates, by the actual manifold chain
rule.  For a finite-order permutation this applies to every element of
the original cyclic action.  No character action on a formal line is used.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsIterates

local notation "I" => modelWithCornersSelf ℂ Model

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]

/-- Genuine differential invariance propagates to all iterates. -/
theorem pullbackLinear_iterate_invariant {f : M → M} (hf : ContMDiff I I ω f)
    (s : ∀ x : M, (Atlas.core M).Fiber x)
    (hs : ∀ x, Pullback.pullbackLinear f x (s (f x)) = s x) :
    ∀ (n : ℕ) (x : M), Pullback.pullbackLinear (f^[n]) x (s (f^[n] x)) = s x := by
  intro n
  induction n with
  | zero =>
    intro x
    rw [Function.iterate_zero, Pullback.pullbackLinear_id]
    rfl
  | succ n ih =>
    intro x
    change id (α := ℂ) (Pullback.pullbackLinear ((f^[n]) ∘ f) x (s (f^[n] (f x)))) =
      id (α := ℂ) (s x)
    have hcomp := congrArg (fun A => id (α := ℂ) (A (s (f^[n] (f x)))))
      (Pullback.pullbackLinear_comp ((hf.mdifferentiable (by simp)) x)
        (((hf.iterate n).mdifferentiable (by simp)) (f x)))
    change id (α := ℂ) (Pullback.pullbackLinear ((f^[n]) ∘ f) x (s (f^[n] (f x)))) =
      id (α := ℂ) (Pullback.pullbackLinear f x
        (Pullback.pullbackLinear (f^[n]) (f x) (s (f^[n] (f x))))) at hcomp
    have hinner := congrArg (fun v => id (α := ℂ) (Pullback.pullbackLinear f x v))
      (ih (f x))
    exact hcomp.trans (hinner.trans (hs x))

/-- All elements of the actual cyclic action preserve a section once
its generator preserves it by native derivative pullback. -/
theorem cyclic_pullbackLinear_invariant {m : ℕ} [NeZero m]
    (σ : Equiv.Perm M) (hσ : σ ^ m = 1) (hhol : ContMDiff I I ω σ)
    (s : ∀ x : M, (Atlas.core M).Fiber x)
    (hs : ∀ x, Pullback.pullbackLinear σ x (s (σ x)) = s x)
    (g : Multiplicative (ZMod m)) (x : M) :
    letI := Elliptic.CyclicAction.action σ hσ
    Pullback.pullbackLinear (fun y : M => g • y) x (s (g • x)) = s x := by
  let := Elliptic.CyclicAction.action σ hσ
  have hact : (fun y : M => g • y) = (σ : M → M)^[g.toAdd.val] :=
    funext (Elliptic.CyclicAction.smul_eq_iterate σ hσ g)
  have h := pullbackLinear_iterate_invariant hhol s hs g.toAdd.val x
  change id (α := ℂ) (Pullback.pullbackLinear (fun y : M => g • y) x (s (g • x))) =
    id (α := ℂ) (s x)
  have h' : id (α := ℂ)
      (Pullback.pullbackLinear (fun y : M => g • y) x (s ((fun y : M => g • y) x))) =
      id (α := ℂ)
        (Pullback.pullbackLinear ((σ : M → M)^[g.toAdd.val]) x
          (s (((σ : M → M)^[g.toAdd.val]) x))) :=
    congrArg (fun f : M → M => id (α := ℂ) (Pullback.pullbackLinear f x (s (f x)))) hact
  exact h'.trans h

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsIterates
