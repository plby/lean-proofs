import Wikipedia.HopfProblem.EllipticCyclicAction
import Wikipedia.HopfProblem.EllipticLogGaugeQuotientCore

/-!
# Conjugate cyclic actions have homeomorphic actual orbit quotients

A homeomorphism intertwining two finite-order generators intertwines
their selected cyclic actions.  The resulting homeomorphism is defined
on the actual orbit quotients, with their quotient topologies, and sends
the class of a point to the class of its given homeomorphic image.
No freeness, compactness, or continuity hypothesis on the actions is
needed for this quotient-conjugacy construction.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology.MappingTorusQuotient

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  {m : ℕ} [NeZero m]

/-- Intertwining the actual generators intertwines every residue-class
action, because the selected actions are the corresponding iterates. -/
theorem cyclicConjugacy_smul (σ : Equiv.Perm M) (hσ : σ ^ m = 1)
    (τ : Equiv.Perm N) (hτ : τ ^ m = 1) (e : M ≃ₜ N)
    (he : ∀ x, e (σ x) = τ (e x)) (g : Multiplicative (ZMod m)) (x : M) :
    letI := CyclicAction.action σ hσ
    letI := CyclicAction.action τ hτ
    e (g • x) = g • e x := by
  let := CyclicAction.action σ hσ
  let := CyclicAction.action τ hτ
  rw [CyclicAction.smul_eq_iterate σ hσ, CyclicAction.smul_eq_iterate τ hτ]
  exact Function.Semiconj.iterate_right he g.toAdd.val x

/-- The inverse homeomorphism intertwines the inverse-direction action
on the same cyclic-group element, not merely the quotient classes. -/
theorem cyclicConjugacy_symm_smul (σ : Equiv.Perm M) (hσ : σ ^ m = 1)
    (τ : Equiv.Perm N) (hτ : τ ^ m = 1) (e : M ≃ₜ N)
    (he : ∀ x, e (σ x) = τ (e x)) (g : Multiplicative (ZMod m)) (y : N) :
    letI := CyclicAction.action σ hσ
    letI := CyclicAction.action τ hτ
    e.symm (g • y) = g • e.symm y := by
  let := CyclicAction.action σ hσ
  let := CyclicAction.action τ hτ
  apply e.injective
  rw [e.apply_symm_apply, cyclicConjugacy_smul σ hσ τ hτ e he, e.apply_symm_apply]

/-- A generator conjugacy descends to a homeomorphism of the actual
finite cyclic orbit spaces with their original quotient topologies. -/
def cyclicQuotientCongr (σ : Equiv.Perm M) (hσ : σ ^ m = 1)
    (τ : Equiv.Perm N) (hτ : τ ^ m = 1) (e : M ≃ₜ N)
    (he : ∀ x, e (σ x) = τ (e x)) :
    letI := CyclicAction.action σ hσ
    letI := CyclicAction.action τ hτ
    FiniteQuotient.Space (Multiplicative (ZMod m)) M ≃ₜ
      FiniteQuotient.Space (Multiplicative (ZMod m)) N := by
  let := CyclicAction.action σ hσ
  let := CyclicAction.action τ hτ
  refine
    { toEquiv := LogGauge.quotientEquiv (Multiplicative (ZMod m)) e.toEquiv
        (cyclicConjugacy_smul σ hσ τ hτ e he)
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply (FiniteQuotient.project_isQuotientMap (Multiplicative (ZMod m)) M).continuous_iff.mpr
    exact (FiniteQuotient.project_continuous (Multiplicative (ZMod m)) N).comp e.continuous
  · apply (FiniteQuotient.project_isQuotientMap (Multiplicative (ZMod m)) N).continuous_iff.mpr
    exact (FiniteQuotient.project_continuous (Multiplicative (ZMod m)) M).comp e.symm.continuous

/-- The descended map has the literal expected value on representatives. -/
@[simp] theorem cyclicQuotientCongr_project (σ : Equiv.Perm M) (hσ : σ ^ m = 1)
    (τ : Equiv.Perm N) (hτ : τ ^ m = 1) (e : M ≃ₜ N)
    (he : ∀ x, e (σ x) = τ (e x)) (x : M) :
    letI := CyclicAction.action σ hσ
    letI := CyclicAction.action τ hτ
    cyclicQuotientCongr σ hσ τ hτ e he
        (FiniteQuotient.project (Multiplicative (ZMod m)) M x) =
      FiniteQuotient.project (Multiplicative (ZMod m)) N (e x) := by
  let := CyclicAction.action σ hσ
  let := CyclicAction.action τ hτ
  rfl

/-- The inverse also has the literal representative formula. -/
@[simp] theorem cyclicQuotientCongr_symm_project (σ : Equiv.Perm M) (hσ : σ ^ m = 1)
    (τ : Equiv.Perm N) (hτ : τ ^ m = 1) (e : M ≃ₜ N)
    (he : ∀ x, e (σ x) = τ (e x)) (y : N) :
    letI := CyclicAction.action σ hσ
    letI := CyclicAction.action τ hτ
    (cyclicQuotientCongr σ hσ τ hτ e he).symm
        (FiniteQuotient.project (Multiplicative (ZMod m)) N y) =
      FiniteQuotient.project (Multiplicative (ZMod m)) M (e.symm y) := by
  let := CyclicAction.action σ hσ
  let := CyclicAction.action τ hτ
  rfl

end Wikipedia.HopfProblem.Elliptic.HigherHomology.MappingTorusQuotient
