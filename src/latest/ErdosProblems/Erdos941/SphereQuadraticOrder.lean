import ErdosProblems.Erdos941.SphereQuadraticField
import ErdosProblems.Erdos941.HurwitzParity
import ErdosProblems.Erdos941.PrimitiveTriples

/-! # Coordinates of the quadratic order inside the Hurwitz order -/

namespace Erdos941

open scoped Quaternion

theorem sphereQuadraticOrder_coordinates {v : Triple} {n : ℕ}
    (hv : tripleNorm v = n) (hp : PrimitiveTriple v) (z : SphereQuadraticField n) :
    z ∈ sphereQuadraticOrder hv ↔ ∃ r s : ℤ,
      z.re = (r : ℚ) / 2 ∧ z.im = (s : ℚ) / 2 ∧
      r % 2 = (s * v.1) % 2 ∧ r % 2 = (s * v.2.1) % 2 ∧
      r % 2 = (s * v.2.2) % 2 := by
  change sphereFieldEmbedding hv z ∈ hurwitzOrder ↔ _
  constructor
  · intro hz
    obtain ⟨r, i, j, k, heq, hr, hi, hj⟩ :=
      (hurwitz_mem_iff_half_coordinates _).mp hz
    have hR := congrArg (fun q : ℍ[ℚ] => q.re) heq
    have hI := congrArg (fun q : ℍ[ℚ] => q.imI) heq
    have hJ := congrArg (fun q : ℍ[ℚ] => q.imJ) heq
    have hK := congrArg (fun q : ℍ[ℚ] => q.imK) heq
    simp only [sphereFieldEmbedding_re] at hR
    simp only [sphereFieldEmbedding_imI] at hI
    simp only [sphereFieldEmbedding_imJ] at hJ
    simp only [sphereFieldEmbedding_imK] at hK
    obtain ⟨a, b, c, hbez⟩ := hp
    have hbezQ : (a : ℚ) * v.1 + (b : ℚ) * v.2.1 + (c : ℚ) * v.2.2 = 1 := by
      exact_mod_cast hbez
    let s : ℤ := a * i + b * j + c * k
    have hs : z.im = (s : ℚ) / 2 := by
      dsimp [s]
      push_cast
      linear_combination -z.im * hbezQ + (a : ℚ) * hI + (b : ℚ) * hJ + (c : ℚ) * hK
    have hsi : s * v.1 = i := by
      have h : (s : ℚ) * v.1 = i := by rw [hs] at hI; linarith
      exact_mod_cast h
    have hsj : s * v.2.1 = j := by
      have h : (s : ℚ) * v.2.1 = j := by rw [hs] at hJ; linarith
      exact_mod_cast h
    have hsk : s * v.2.2 = k := by
      have h : (s : ℚ) * v.2.2 = k := by rw [hs] at hK; linarith
      exact_mod_cast h
    refine ⟨r, s, hR, hs, ?_, ?_, ?_⟩
    · rw [hsi]; omega
    · rw [hsj]; omega
    · rw [hsk]; exact hr
  · rintro ⟨r, s, hre, him, hA, hB, hC⟩
    apply (hurwitz_mem_iff_half_coordinates _).mpr
    refine ⟨r, s * v.1, s * v.2.1, s * v.2.2, ?_, hC, hA.symm.trans hC,
      hB.symm.trans hC⟩
    apply Quaternion.ext
    · simpa only [sphereFieldEmbedding_re] using hre
    · rw [sphereFieldEmbedding_imI, him]
      push_cast
      ring
    · rw [sphereFieldEmbedding_imJ, him]
      push_cast
      ring
    · rw [sphereFieldEmbedding_imK, him]
      push_cast
      ring

theorem sphereQuadraticOrder_of_mixed_parity {v : Triple} {n : ℕ}
    (hv : tripleNorm v = n) (hp : PrimitiveTriple v)
    (heven : v.1 % 2 = 0 ∨ v.2.1 % 2 = 0 ∨ v.2.2 % 2 = 0)
    (z : SphereQuadraticField n) :
    z ∈ sphereQuadraticOrder hv ↔ ∃ a b : ℤ, z = ⟨(a : ℚ), (b : ℚ)⟩ := by
  constructor
  · intro hz
    obtain ⟨r, s, hre, him, hA, hB, hC⟩ :=
      (sphereQuadraticOrder_coordinates hv hp z).mp hz
    have hr : r % 2 = 0 := by
      rcases heven with he | he | he
      · simpa only [Int.mul_emod, he, mul_zero, Int.zero_emod] using hA
      · simpa only [Int.mul_emod, he, mul_zero, Int.zero_emod] using hB
      · simpa only [Int.mul_emod, he, mul_zero, Int.zero_emod] using hC
    have hs : s % 2 = 0 := by
      obtain ⟨a, b, c, hbez⟩ := hp
      have hsbez : s = a * (s * v.1) + b * (s * v.2.1) + c * (s * v.2.2) := by
        linear_combination -s * hbez
      rw [hsbez]
      simp only [Int.add_emod, Int.mul_emod a, Int.mul_emod b, Int.mul_emod c,
        ← hA, ← hB, ← hC, hr, mul_zero, Int.zero_emod, zero_add]
    obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero hr
    obtain ⟨b, hb⟩ := Int.dvd_of_emod_eq_zero hs
    refine ⟨a, b, ?_⟩
    apply QuadraticAlgebra.ext
    · rw [hre, ha]; push_cast; ring
    · rw [him, hb]; push_cast; ring
  · rintro ⟨a, b, rfl⟩
    apply (sphereQuadraticOrder_coordinates hv hp _).mpr
    refine ⟨2 * a, 2 * b, ?_, ?_, ?_, ?_, ?_⟩
    · push_cast; ring
    · push_cast; ring
    all_goals simp [Int.mul_emod]

theorem sphereQuadraticOrder_of_all_odd {v : Triple} {n : ℕ}
    (hv : tripleNorm v = n) (hp : PrimitiveTriple v)
    (hodd : v.1 % 2 = 1 ∧ v.2.1 % 2 = 1 ∧ v.2.2 % 2 = 1)
    (z : SphereQuadraticField n) :
    z ∈ sphereQuadraticOrder hv ↔
      ∃ a b : ℤ, z = ⟨(a : ℚ) + (b : ℚ) / 2, (b : ℚ) / 2⟩ := by
  constructor
  · intro hz
    obtain ⟨r, s, hre, him, hA, hB, hC⟩ :=
      (sphereQuadraticOrder_coordinates hv hp z).mp hz
    have hrs : r % 2 = s % 2 := by simpa [Int.mul_emod, hodd.1] using hA
    have hd : 2 ∣ r - s := by omega
    obtain ⟨a, ha⟩ := hd
    have haQ : (r : ℚ) - s = 2 * a := by exact_mod_cast ha
    refine ⟨a, s, ?_⟩
    apply QuadraticAlgebra.ext
    · rw [hre]; dsimp; linarith
    · exact him
  · rintro ⟨a, b, rfl⟩
    apply (sphereQuadraticOrder_coordinates hv hp _).mpr
    refine ⟨2 * a + b, b, ?_, rfl, ?_, ?_, ?_⟩
    · dsimp; push_cast; ring
    all_goals simp [Int.add_emod, Int.mul_emod, hodd.1, hodd.2.1, hodd.2.2]

end Erdos941
