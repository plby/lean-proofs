import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# A local orbit trivialization from an equivariant phase

An equivariant map to the acting group gives an explicit product
homeomorphism. The slice is the actual fibre over the identity, and the
inverse is the original action. This general lemma will be applied to
the normalized local character on an invariant open part of the actual
threefold.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair

variable {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace M] [MulAction G M] [ContinuousSMul G M]

/-- The actual identity fibre of the equivariant phase. -/
abbrev PhaseSlice (φ : M → G) := {x : M // φ x = 1}

/-- Splitting off the phase gives a literal product with the identity fibre. -/
def phaseTrivialization (φ : M → G) (hφ : Continuous φ)
    (heq : ∀ g x, φ (g • x) = g * φ x) : M ≃ₜ G × PhaseSlice φ := by
  refine
    { toFun := fun x => (φ x, ⟨(φ x)⁻¹ • x, ?_⟩)
      invFun := fun p => p.1 • p.2.val
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · rw [heq, inv_mul_cancel]
  · intro x
    exact smul_inv_smul (φ x) x
  · intro p
    apply Prod.ext
    · exact (heq p.1 p.2.val).trans (by rw [p.2.property, mul_one])
    · apply Subtype.ext
      change (φ (p.1 • p.2.val))⁻¹ • (p.1 • p.2.val) = p.2.val
      rw [heq, p.2.property, mul_one, inv_smul_smul]
  · exact hφ.prodMk ((hφ.inv.smul continuous_id).subtype_mk _)
  · exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)

@[simp] theorem phaseTrivialization_fst (φ : M → G) (hφ : Continuous φ)
    (heq : ∀ g x, φ (g • x) = g * φ x) (x : M) :
    (phaseTrivialization φ hφ heq x).1 = φ x := rfl

@[simp] theorem phaseTrivialization_symm (φ : M → G) (hφ : Continuous φ)
    (heq : ∀ g x, φ (g • x) = g * φ x) (g : G) (x : PhaseSlice φ) :
    (phaseTrivialization φ hφ heq).symm (g, x) = g • x.val := rfl

end Wikipedia.HopfProblem.OrbitPair
