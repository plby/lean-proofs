import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexComponents

/-! # Multiplication and squared norm in two complex quaternion coordinates -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexPlane

local notation "ℍ" => Quaternion ℝ

theorem complexPart_neg (q : ℍ) : complexPart (-q) = -complexPart q := rfl
theorem coordinate_neg (q : ℍ) : coordinate (-q) = -coordinate q := rfl

theorem complexPart_mul (q r : ℍ) :
    complexPart (q * r) = complexPart q * complexPart r - coordinate q * star (coordinate r) := by
  apply Complex.ext
  · change (q * r).re = _
    rw [Quaternion.re_mul]
    simp [complexPart, coordinate]
    ring
  · change (q * r).imI = _
    rw [Quaternion.imI_mul]
    simp [complexPart, coordinate]
    ring

theorem coordinate_mul (q r : ℍ) :
    coordinate (q * r) = complexPart q * coordinate r + coordinate q * star (complexPart r) := by
  apply Complex.ext
  · change (q * r).imJ = _
    rw [Quaternion.imJ_mul]
    simp [complexPart, coordinate]
    ring
  · change (q * r).imK = _
    rw [Quaternion.imK_mul]
    simp [complexPart, coordinate]
    ring

theorem normSq_complex_pair (q : ℍ) :
    Quaternion.normSq q = Complex.normSq (complexPart q) + Complex.normSq (coordinate q) := by
  rw [Quaternion.normSq_def']
  simp [complexPart, coordinate, Complex.normSq_apply]
  ring

theorem coeComplex_mk (a b : ℝ) : ((⟨a, b⟩ : ℂ) : ℍ) =
    a • (1 : ℍ) + b • QuaternionicScalars.i := by
  apply Quaternion.ext
  · change a = a * 1 + b * 0
    ring
  · change b = a * 0 + b * 1
    ring
  · change (0 : ℝ) = a * 0 + b * 0
    ring
  · change (0 : ℝ) = a * 0 + b * 0
    ring

theorem embed_ofReal (c : ℝ) : embed (c : ℂ) = c • QuaternionicScalars.j := by
  rw [embed_eq_mk]
  apply Quaternion.ext
  · change (0 : ℝ) = c * 0
    ring
  · change (0 : ℝ) = c * 0
    ring
  · change c = c * 1
    ring
  · change (0 : ℝ) = c * 0
    ring

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexPlane
