import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitarySpecialComparison

/-!
# The determinant-one inclusion on native higher homotopy groups

The original inclusion is injective in positive degree and an isomorphism
in every degree at least two. Both statements concern Mathlib's native
cubical groups with the identity matrix as base point.
-/

noncomputable section

open scoped Topology unitInterval ContinuousMap

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

def specialInclusionHom (n d : ℕ) [NeZero d] :
    π_ d (SpecialSpace (Fin (n + 1))) specialIdentity →*
      π_ d (Space (Fin (n + 1))) identity :=
  pointedMap (specialInclusion _) specialIdentity identity rfl

theorem specialInclusionHom_mk (n d : ℕ) [NeZero d]
    (p : GenLoop (Fin d) (SpecialSpace (Fin (n + 1))) specialIdentity) :
    specialInclusionHom n d (Quotient.mk' p) =
      Quotient.mk' (pointedMapGenLoop (specialInclusion _) specialIdentity identity rfl p) :=
  pointedMap_mk _ _ _ _ p

theorem specialInclusionHom_injective (n d : ℕ) [NeZero d] :
    Function.Injective (specialInclusionHom n d) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      have he := (specialInclusionHom_mk n d p).symm.trans
        (hab.trans (specialInclusionHom_mk n d q))
      have hS : (Cube.boundary (Fin d)).Nonempty := ⟨0, ⟨0, Or.inl rfl⟩⟩
      apply Quotient.sound
      exact (special_homotopicRel_iff n hS p.val q.val).mpr (Quotient.exact he)

theorem specialInclusionHom_surjective (n d : ℕ) :
    Function.Surjective (specialInclusionHom n (d + 2)) := by
  intro a
  induction a using Quotient.inductionOn with
  | h p =>
    obtain ⟨q, hq⟩ := exists_special_cube_representative n d p
    refine ⟨Quotient.mk' q, ?_⟩
    rw [specialInclusionHom_mk]
    exact Quotient.sound hq.symm

/-- The actual determinant-one inclusion induces this higher group isomorphism. -/
def specialInclusionMulEquiv (n d : ℕ) :
    π_ (d + 2) (SpecialSpace (Fin (n + 1))) specialIdentity ≃*
      π_ (d + 2) (Space (Fin (n + 1))) identity :=
  MulEquiv.ofBijective (specialInclusionHom n (d + 2))
    ⟨specialInclusionHom_injective n (d + 2), specialInclusionHom_surjective n d⟩

theorem specialInclusionMulEquiv_mk (n d : ℕ)
    (p : GenLoop (Fin (d + 2)) (SpecialSpace (Fin (n + 1))) specialIdentity) :
    specialInclusionMulEquiv n d (Quotient.mk' p) =
      Quotient.mk' (pointedMapGenLoop (specialInclusion _) specialIdentity identity rfl p) :=
  specialInclusionHom_mk n (d + 2) p

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
