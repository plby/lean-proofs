import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricUnitaryModel

/-! # Inverse coordinate formulas without expanding the concrete matrix model -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.AnticommutingStructures

theorem symmetricUnitaryHomeomorph_symm_apply (n : ℕ)
    (B : QuaternionicSymmetricMatrices.Space (Fin (n + 1))) :
    (symmetricUnitaryHomeomorph n).symm B = ofSymmetricUnitary B := rfl

theorem symmetricUnitaryHomeomorph_symm_identity (n : ℕ) :
    (symmetricUnitaryHomeomorph n).symm QuaternionicSymmetricMatrices.identity = standard n :=
  ofSymmetricUnitary_identity n

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.AnticommutingStructures
