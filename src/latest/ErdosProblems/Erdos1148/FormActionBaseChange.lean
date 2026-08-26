import ErdosProblems.Erdos1148.BaseChange

/-! # Base change for the special-linear action on forms -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma mapCoeffs_transform {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Matrix (Fin 2) (Fin 2) R) (t : R × R × R) :
    mapCoeffs φ (transform M t) = transform (M.map φ) (mapCoeffs φ t) := by
  ext <;> simp [mapCoeffs, transform, map_ofNat]

lemma mapCoeffs_formAction {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : SL(2, R)) (t : R × R × R) :
    mapCoeffs φ (formAction g t) =
      formAction (Matrix.SpecialLinearGroup.map φ g) (mapCoeffs φ t) := by
  simp only [formAction, ← map_inv (Matrix.SpecialLinearGroup.map φ),
    Matrix.SpecialLinearGroup.map_apply_coe, mapCoeffs_transform]
  rfl

lemma formAction_smul {R : Type*} [CommRing R] (g : SL(2, R)) (c : R) (t : R × R × R) :
    formAction g (c • t) = c • formAction g t :=
  (formActionEquiv g).map_smul c t

end Erdos1148.DukeArithmetic
