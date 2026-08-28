import Wikipedia.NoExoticSixSphere.UnorderedSphereDoublePoints

/-!
# Source reparametrization preserves the actual unordered double points

A bijection of the original source sphere induces an equivariant bijection
of distinct equal-image pairs and hence a bijection of their sheet-swap
orbits. No immersion, finiteness, orientation, or smoothness assumption is
needed for this set-theoretic statement.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.SphereSelfIntersections

open GLOrthonormalization InvolutionQuotient

variable {M : Type*} (f : Sphere 3 → M) (e : Sphere 3 ≃ Sphere 3)

def sourcePairEquiv : pairs (f ∘ e) ≃ pairs f where
  toFun p := ⟨(e p.val.1, e p.val.2), e.injective.ne p.property.1, p.property.2⟩
  invFun p := ⟨(e.symm p.val.1, e.symm p.val.2), e.symm.injective.ne p.property.1,
    by simpa only [comp_apply, e.apply_symm_apply] using p.property.2⟩
  left_inv p := by
    apply Subtype.ext
    simp only [e.symm_apply_apply]
  right_inv p := by
    apply Subtype.ext
    simp only [e.apply_symm_apply]

theorem sourcePairEquiv_swap (p : pairs (f ∘ e)) :
    sourcePairEquiv f e (swap (f ∘ e) p) = swap f (sourcePairEquiv f e p) := rfl

def sourceUnorderedEquiv : Unordered (f ∘ e) ≃ Unordered f :=
  Quotient.congr (sourcePairEquiv f e) (by
    intro p q
    change (p = q ∨ swap (f ∘ e) p = q) ↔
      (sourcePairEquiv f e p = sourcePairEquiv f e q ∨
        swap f (sourcePairEquiv f e p) = sourcePairEquiv f e q)
    rw [← sourcePairEquiv_swap, Equiv.apply_eq_iff_eq, Equiv.apply_eq_iff_eq])

theorem sourceUnorderedEquiv_proj (p : pairs (f ∘ e)) :
    sourceUnorderedEquiv f e (unorderedProj (f ∘ e) p) =
      unorderedProj f (sourcePairEquiv f e p) := rfl

theorem unorderedParity_precomp_equiv : unorderedParity (f ∘ e) = unorderedParity f := by
  unfold unorderedParity
  rw [Nat.card_congr (sourceUnorderedEquiv f e)]

end NoExoticSixSphere.SphereSelfIntersections
