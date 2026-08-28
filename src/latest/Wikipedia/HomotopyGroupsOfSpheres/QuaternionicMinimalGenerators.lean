import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructures
import Wikipedia.NoExoticSixSphere.SkewAntipodalMinimum

/-! # Minimum antipodal generators are scaled quaternionic complex structures -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt

variable {n : ℕ}

theorem squareNorm_eq_iff_complexStructure (K : SkewSpace n)
    (hexp : (Exponential.exp K).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    squareNorm K.val = ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 ↔
      ∃ J : ComplexStructures.Space n, Real.pi • J.val = K := by
  have hbase := NoExoticSixSphere.SkewAntipodalSpectrum.squareNorm_eq_iff_complexStructure
    (toOrthogonalSkew n K) hexp
  constructor
  · intro he
    obtain ⟨J, hJ⟩ := hbase.mp he
    have hscaled := congrArg
      (fun L : NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4) =>
        Real.pi⁻¹ • L.val) hJ
    change Real.pi⁻¹ • (Real.pi • J.val.val) = Real.pi⁻¹ • K.val at hscaled
    have hJeq : J.val.val = Real.pi⁻¹ • K.val := by
      simpa only [smul_smul, inv_mul_cancel₀ Real.pi_ne_zero, one_smul] using hscaled
    have hcomm : J.val.val ∈ commutant n := by
      rw [hJeq]
      exact (commutant n).smul_mem K.property.2 Real.pi⁻¹
    let Q : ComplexStructures.Space n :=
      ⟨⟨J.val.val, ⟨J.val.property, hcomm⟩⟩, J.property⟩
    refine ⟨Q, Subtype.ext ?_⟩
    exact congrArg
      (fun L : NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4) => L.val) hJ
  · rintro ⟨J, hJ⟩
    apply hbase.mpr
    refine ⟨ComplexStructures.toOrthogonal J, ?_⟩
    rw [← hJ, map_smul]
    rfl

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
