import ErdosProblems.Erdos587.HooleyLatticeModel
import ErdosProblems.Erdos587.HooleyCoordinateTransfer

/-! # Evaluation and real-coordinate maps for the adapted generated lattice -/

namespace Erdos587.GeneralizedAP

namespace DeltaLatticeModel

variable {X : ConvexProgression} {Γ : AddSubgroup (Fin X.rank → ℤ)}

noncomputable def basis (D : DeltaLatticeModel X Γ) :
    Module.Basis (Fin X.rank) ℤ Γ.toIntSubmodule :=
  (Pi.basisFun ℤ (Fin X.rank)).map D.coordinates.symm

lemma basis_equivFun (D : DeltaLatticeModel X Γ) : D.basis.equivFun = D.coordinates := by
  rw [basis, Module.Basis.map_equivFun, LinearEquiv.symm_symm, Pi.basisFun_equivFun]
  rfl

noncomputable def realCoordinates [Γ.FiniteIndex] (D : DeltaLatticeModel X Γ) :
    (Fin X.rank → ℝ) ≃ₗ[ℝ] (Fin X.rank → ℝ) :=
  (deltaLatticeRealEquiv Γ D.basis).symm

lemma realCoordinates_intCast [Γ.FiniteIndex] (D : DeltaLatticeModel X Γ)
    (v : Γ.toIntSubmodule) :
    D.realCoordinates (intCastVec v.val) = intCastVec (D.coordinates v) := by
  apply (deltaLatticeRealEquiv Γ D.basis).injective
  rw [show deltaLatticeRealEquiv Γ D.basis
      (D.realCoordinates (intCastVec v.val)) = intCastVec v.val from
    (deltaLatticeRealEquiv Γ D.basis).apply_symm_apply _]
  change intCastVec v.val =
    intLinearMapRealExtension (deltaLatticeEmbedding Γ D.basis) (intCastVec (D.coordinates v))
  rw [intLinearMapRealExtension_intCastVec]
  congr 1
  change v.val = (D.basis.equivFun.symm (D.coordinates v)).val
  rw [D.basis_equivFun, D.coordinates.symm_apply_apply]

open scoped Classical in
noncomputable def coordinateMap (D : DeltaLatticeModel X Γ) (v : Fin X.rank → ℤ) :
    Fin X.rank → ℤ := if hv : v ∈ Γ then D.coordinates ⟨v, hv⟩ else 0

lemma coordinateMap_mem (D : DeltaLatticeModel X Γ) {v : Fin X.rank → ℤ} (hv : v ∈ Γ) :
    D.coordinateMap v = D.coordinates ⟨v, hv⟩ := by rw [coordinateMap, dif_pos hv]

def coordinateEval (D : DeltaLatticeModel X Γ) (f : (Fin X.rank → ℤ) →+ ℤ) :
    (Fin X.rank → ℤ) →+ ℤ :=
  f.comp (Γ.toIntSubmodule.subtype.toAddMonoidHom.comp D.coordinates.symm.toAddMonoidHom)

lemma coordinateEval_map (D : DeltaLatticeModel X Γ) (f : (Fin X.rank → ℤ) →+ ℤ)
    {v : Fin X.rank → ℤ} (hv : v ∈ Γ) : D.coordinateEval f (D.coordinateMap v) = f v := by
  rw [D.coordinateMap_mem hv]
  change f (D.coordinates.symm (D.coordinates ⟨v, hv⟩)).val = f v
  rw [D.coordinates.symm_apply_apply]

lemma coordinateMap_real [Γ.FiniteIndex] (D : DeltaLatticeModel X Γ)
    {v : Fin X.rank → ℤ} (hv : v ∈ Γ) :
    intCastVec (D.coordinateMap v) = D.realCoordinates (intCastVec v) := by
  rw [D.coordinateMap_mem hv]
  exact (D.realCoordinates_intCast ⟨v, hv⟩).symm

lemma coordinateMap_bound (D : DeltaLatticeModel X Γ) {v : Fin X.rank → ℤ}
    (hv : v ∈ Γ) (hbody : intCastVec v ∈ X.body) (i : Fin X.rank) :
    |(D.coordinateMap v i : ℝ)| ≤ D.bound i := by
  rw [D.coordinateMap_mem hv]
  exact D.cover ⟨v, hv⟩ hbody i

theorem robust_spanning_image [Γ.FiniteIndex] (D : DeltaLatticeModel X Γ)
    (U : Finset (Fin X.rank → ℤ)) (hU : ∀ u ∈ U, u ∈ Γ) (k : ℕ)
    (hspan : ∀ V ⊆ U, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin X.rank → ℤ))) = ⊤) :
    ∀ V ⊆ U.image D.coordinateMap, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin X.rank → ℤ))) = ⊤ :=
  delta_robust_span_coordinate_image U k hspan D.coordinateMap D.realCoordinates.toLinearMap
    D.realCoordinates.surjective (fun u hu => D.coordinateMap_real (hU u hu))

lemma coordinateMap_injOn (D : DeltaLatticeModel X Γ) (f : (Fin X.rank → ℤ) →+ ℤ)
    (U : Finset (Fin X.rank → ℤ)) (hU : ∀ u ∈ U, u ∈ Γ) (hinj : Set.InjOn f U) :
    Set.InjOn D.coordinateMap U :=
  delta_injOn_of_evaluation D.coordinateMap f (D.coordinateEval f) hinj
    (fun u hu => D.coordinateEval_map f (hU u hu))

end DeltaLatticeModel

end Erdos587.GeneralizedAP
