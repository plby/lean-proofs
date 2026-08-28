import Wikipedia.HopfProblem.FundamentalGroupVanKampenTransport

/-!
# A homotopy-invariant path value induces an actual group homomorphism

The quotient here is the native fundamental group, namely actual based
paths modulo endpoint-preserving homotopy.  Taking the inverse of the
path value accounts for mathlib's reverse-concatenation multiplication.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen.PathValue

variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]
variable (V : PathValue X G) (hV : V.HomotopyInvariant) (o : X)

/-- Descend the actual homotopy-invariant path value to the native fundamental group. -/
def fundamentalGroupHom : FundamentalGroup X o →* G where
  toFun := _root_.Quotient.lift (fun p : Path o o => (V.value p)⁻¹)
    (fun p q h => congrArg (fun a : G => a⁻¹) (hV p q h))
  map_one' := by
    change (V.value (Path.refl o))⁻¹ = 1
    rw [V.refl, inv_one]
  map_mul' := by
    intro a b
    obtain ⟨p⟩ := a
    obtain ⟨q⟩ := b
    change (V.value (q.trans p))⁻¹ = (V.value p)⁻¹ * (V.value q)⁻¹
    rw [V.trans, mul_inv_rev]

@[simp] theorem fundamentalGroupHom_mk (p : Path o o) :
    V.fundamentalGroupHom hV o (Path.Homotopic.Quotient.mk p) = (V.value p)⁻¹ := rfl

end Wikipedia.HopfProblem.FundamentalGroupVanKampen.PathValue
