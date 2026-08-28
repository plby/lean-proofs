import Wikipedia.HopfProblem.OrbitPairNativeSpatialReparametrization
import Wikipedia.HopfProblem.OrbitPairFiniteProjectedCollisionFibers

/-!
# Globally exact fibers under spatial source reparametrization

Any time-dependent spatial equivalence preserves globally exact projected
collision fibers, transporting their two source points by the same source
equivalence. If every old collision source is fixed, the synchronized
collision set is literally unchanged.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.SpatialReparametrization

open FamilyDoublePoints SynchronizedPairs

variable {M N : Type*}

theorem pairEquiv_fixed_at_collision {F : ℝ × M → N} (e : ℝ → M ≃ M)
    (hfixed : ∀ q ∈ collisionSources F, sourceEquiv e q = q)
    {p : ℝ × (M × M)} (hp : p ∈ doublePoints F) : pairEquiv e p = p := by
  have h₁ := hfixed (first p) (first_mem_collisionSources hp)
  have h₂ := hfixed (second p) (second_mem_collisionSources hp)
  have hx : e p.1 p.2.1 = p.2.1 := congrArg (fun q : ℝ × M => q.2) h₁
  have hy : e p.1 p.2.2 = p.2.2 := congrArg (fun q : ℝ × M => q.2) h₂
  change (p.1, (e p.1 p.2.1, e p.1 p.2.2)) = p
  exact Prod.ext rfl (Prod.ext hx hy)

theorem doublePoints_eq_of_fixed_collisionSources {F : ℝ × M → N} (e : ℝ → M ≃ M)
    (hfixed : ∀ q ∈ collisionSources F, sourceEquiv e q = q) :
    doublePoints (changedFamily F e) = doublePoints F := by
  ext p
  rw [mem_doublePoints_iff]
  constructor
  · intro hp
    have heq : pairEquiv e p = p := (pairEquiv e).injective
      (pairEquiv_fixed_at_collision e hfixed hp)
    exact heq ▸ hp
  · intro hp
    rw [pairEquiv_fixed_at_collision e hfixed hp]
    exact hp

theorem global_projected_collision_fibers {F : ℝ × M → N} (e : ℝ → M ≃ M)
    (hglobal : ∀ p ∈ doublePoints F, NativeFamily.HasGlobalProjectedCollisionFiber F p) :
    ∀ p ∈ doublePoints (changedFamily F e),
      NativeFamily.HasGlobalProjectedCollisionFiber (changedFamily F e) p := by
  intro p hp z
  have hold := hglobal (pairEquiv e p) ((mem_doublePoints_iff F e p).mp hp)
  constructor
  · intro hz
    have heq : F (sourceEquiv e z) = F (first (pairEquiv e p)) := hz
    rcases (hold (sourceEquiv e z)).mp heq with h | h
    · exact Or.inl ((sourceEquiv e).injective h)
    · exact Or.inr ((sourceEquiv e).injective h)
  · rintro (rfl | rfl)
    · rfl
    · exact hp.2.symm

end Wikipedia.HopfProblem.OrbitPair.SpatialReparametrization
