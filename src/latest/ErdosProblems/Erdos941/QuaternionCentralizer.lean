import ErdosProblems.Erdos941.HurwitzSpheres

/-! # The centralizer of a nonzero pure quaternion -/

namespace Erdos941

open scoped Quaternion

private theorem exists_common_ratio {A B C x y z : ℚ}
    (hbase : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0)
    (hAB : x * B = y * A) (hAC : x * C = z * A) (hBC : y * C = z * B) :
    ∃ t : ℚ, x = t * A ∧ y = t * B ∧ z = t * C := by
  rcases hbase with hA | hB | hC
  · refine ⟨x / A, (div_mul_cancel₀ x hA).symm, ?_, ?_⟩
    · field_simp; exact hAB.symm
    · field_simp; exact hAC.symm
  · refine ⟨y / B, ?_, (div_mul_cancel₀ y hB).symm, ?_⟩
    · field_simp; exact hAB
    · field_simp; exact hBC.symm
  · refine ⟨z / C, ?_, ?_, (div_mul_cancel₀ z hC).symm⟩
    · field_simp; exact hAC
    · field_simp; exact hBC

theorem pureQuaternion_commutes_iff {v : Triple} (hv : v ≠ 0) (q : ℍ[ℚ]) :
    q * pureQuaternion v = pureQuaternion v * q ↔
      ∃ a b : ℚ, q = a • (1 : ℍ[ℚ]) + b • pureQuaternion v := by
  constructor
  · intro h
    have hi := congrArg (fun z : ℍ[ℚ] => z.imI) h
    have hj := congrArg (fun z : ℍ[ℚ] => z.imJ) h
    have hk := congrArg (fun z : ℍ[ℚ] => z.imK) h
    rw [Quaternion.imI_mul, Quaternion.imI_mul] at hi
    rw [Quaternion.imJ_mul, Quaternion.imJ_mul] at hj
    rw [Quaternion.imK_mul, Quaternion.imK_mul] at hk
    dsimp [pureQuaternion] at hi hj hk
    have hbase : (v.1 : ℚ) ≠ 0 ∨ (v.2.1 : ℚ) ≠ 0 ∨ (v.2.2 : ℚ) ≠ 0 := by
      by_contra! hh
      apply hv
      apply Prod.ext
      · exact_mod_cast hh.1
      · apply Prod.ext
        · exact_mod_cast hh.2.1
        · exact_mod_cast hh.2.2
    obtain ⟨b, hbI, hbJ, hbK⟩ := exists_common_ratio hbase
      (show q.imI * (v.2.1 : ℚ) = q.imJ * (v.1 : ℚ) by nlinarith [hk])
      (show q.imI * (v.2.2 : ℚ) = q.imK * (v.1 : ℚ) by nlinarith [hj])
      (show q.imJ * (v.2.2 : ℚ) = q.imK * (v.2.1 : ℚ) by nlinarith [hi])
    refine ⟨q.re, b, ?_⟩
    apply Quaternion.ext
    · rw [Quaternion.re_add, Quaternion.re_smul, Quaternion.re_smul]
      simp [pureQuaternion]
    · rw [Quaternion.imI_add, Quaternion.imI_smul, Quaternion.imI_smul]
      simpa [pureQuaternion] using hbI
    · rw [Quaternion.imJ_add, Quaternion.imJ_smul, Quaternion.imJ_smul]
      simpa [pureQuaternion] using hbJ
    · rw [Quaternion.imK_add, Quaternion.imK_smul, Quaternion.imK_smul]
      simpa [pureQuaternion] using hbK
  · rintro ⟨a, b, rfl⟩
    rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

end Erdos941
