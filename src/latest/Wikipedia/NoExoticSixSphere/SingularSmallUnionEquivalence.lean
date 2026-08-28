import Wikipedia.NoExoticSixSphere.SingularSubcomplexRestriction
import Wikipedia.NoExoticSixSphere.SingularSmallChainComparison

/-!
# Small chains compute the actual open union

The original small-simplex map into the singular set of the union is a
quasi-isomorphism when both subsets are open, without requiring them to
cover the original ambient space. The proof restricts to the actual union
and uses the proved subdivision equivalence there.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.SingularSubcomplex

variable {X : Type} [TopologicalSpace X] (U V : Set X)

omit [TopologicalSpace X] in
theorem union_subspace_cover :
    (Subtype.val ⁻¹' U : Set (U ∪ V : Set X)) ∪ Subtype.val ⁻¹' V = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact x.property

/-- The integral map into the actual open union is a quasi-isomorphism. -/
theorem smallToUnion_integral_quasiIso (hU : IsOpen U) (hV : IsOpen V) :
    QuasiIso ((SimplicialCoefficients.chains (ModuleCat.of ℤ ℤ)).map (smallToUnion U V)) := by
  let F := SimplicialCoefficients.chains (ModuleCat.of ℤ ℤ)
  have h : QuasiIso (F.map (smallUnionIso U V).hom ≫ F.map (smallToUnion U V)) := by
    rw [← F.map_comp, smallUnionIso_toUnion]
    exact smallInclusion_integral_quasiIso
      (Subtype.val ⁻¹' U : Set (U ∪ V : Set X)) (Subtype.val ⁻¹' V)
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
      (union_subspace_cover U V)
  exact quasiIso_of_comp_left (F.map (smallUnionIso U V).hom) (F.map (smallToUnion U V))

/-- Native finite-cyclic coefficients preserve the actual open-union comparison. -/
theorem smallToUnion_mod_quasiIso (p : ℕ) (hp : p ≠ 0) (hU : IsOpen U) (hV : IsOpen V) :
    QuasiIso ((SimplicialCoefficients.chains (ModuleCat.of ℤ (ZMod p))).map (smallToUnion U V)) :=
  SimplicialCoefficients.map_mod_quasiIso_of_integral p hp (smallToUnion U V)
    (smallToUnion_integral_quasiIso U V hU hV)

end NoExoticSixSphere.SingularSubcomplex
