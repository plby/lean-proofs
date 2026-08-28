import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitarySpecialHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryBlocks

/-! # The actual determinant-one inclusion in arbitrary finite index coordinates -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

variable {N : Type} [Fintype N] [DecidableEq N] {n : ℕ}

def specialInclusionReindexMulEquiv (e : N ≃ Fin (n + 1)) (d : ℕ) :
    π_ (d + 2) (SpecialSpace N) specialIdentity ≃* π_ (d + 2) (Space N) identity :=
  ((specialReindexHomotopyMulEquiv e (d + 2)).trans (specialInclusionMulEquiv n d)).trans
    (pointedHomeomorphMulEquiv (reindexHomeomorph e.symm) identity identity
      (reindexHomeomorph_identity e.symm))

theorem specialInclusionReindexMulEquiv_mk (e : N ≃ Fin (n + 1)) (d : ℕ)
    (p : GenLoop (Fin (d + 2)) (SpecialSpace N) specialIdentity) :
    specialInclusionReindexMulEquiv e d (⟦p⟧ : π_ (d + 2) (SpecialSpace N) specialIdentity) =
      (⟦pointedMapGenLoop (specialInclusion N) specialIdentity identity rfl p⟧ :
        π_ (d + 2) (Space N) identity) := by
  let G := specialReindexHomotopyMulEquiv e (d + 2)
  let F := specialInclusionMulEquiv n d
  let E := pointedHomeomorphMulEquiv (N := Fin (d + 2)) (reindexHomeomorph e.symm)
    identity identity (reindexHomeomorph_identity e.symm)
  let p' := pointedMapGenLoop
    (specialReindexHomeomorph e : C(SpecialSpace N, SpecialSpace (Fin (n + 1))))
    specialIdentity specialIdentity (specialReindexHomeomorph_identity e) p
  let q := pointedMapGenLoop (specialInclusion (Fin (n + 1))) specialIdentity identity rfl p'
  let r := pointedMapGenLoop (reindexHomeomorph e.symm : C(Space (Fin (n + 1)), Space N))
    identity identity (reindexHomeomorph_identity e.symm) q
  have hG : G (⟦p⟧ : π_ (d + 2) (SpecialSpace N) specialIdentity) = ⟦p'⟧ :=
    pointedHomeomorphMulEquiv_mk (specialReindexHomeomorph e)
      specialIdentity specialIdentity (specialReindexHomeomorph_identity e) p
  have hF : F (⟦p'⟧ : π_ (d + 2) (SpecialSpace (Fin (n + 1))) specialIdentity) = ⟦q⟧ :=
    specialInclusionMulEquiv_mk n d p'
  have hE : E (⟦q⟧ : π_ (d + 2) (Space (Fin (n + 1))) identity) = ⟦r⟧ :=
    pointedHomeomorphMulEquiv_mk (reindexHomeomorph e.symm)
      identity identity (reindexHomeomorph_identity e.symm) q
  have hr : r = pointedMapGenLoop (specialInclusion N) specialIdentity identity rfl p := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    exact reindex_symm_reindex e (p t).val
  change E (F (G (⟦p⟧ : π_ (d + 2) (SpecialSpace N) specialIdentity))) = _
  exact (congrArg (fun a ↦ E (F a)) hG).trans ((congrArg E hF).trans
    (hE.trans (congrArg (fun s : GenLoop (Fin (d + 2)) (Space N) identity ↦
      (⟦s⟧ : π_ (d + 2) (Space N) identity)) hr)))

theorem specialInclusionReindexMulEquiv_apply (e : N ≃ Fin (n + 1)) (d : ℕ)
    (a : π_ (d + 2) (SpecialSpace N) specialIdentity) :
    specialInclusionReindexMulEquiv e d a =
      pointedMap (specialInclusion N) specialIdentity identity rfl a := by
  refine Quotient.inductionOn a fun p ↦ ?_
  exact (specialInclusionReindexMulEquiv_mk e d p).trans
    (pointedMap_mk (specialInclusion N) specialIdentity identity rfl p).symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
