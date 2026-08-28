import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimumGenerators
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMinimalGenerators

/-! # The equality case for anticommuting antipodal generators -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.AnticommutingStructures

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt
open ComplexStructures

variable {n : ℕ} {a : ComplexStructures.Space n}

private theorem anticommute_of_real_smul {A : Type*} [Ring A] [Algebra ℝ A]
    (J K : A) (c : ℝ) (hc : c ≠ 0) (h : J * (c • K) = -((c • K) * J)) :
    J * K = -(K * J) := by
  apply smul_right_injective (M := A) hc
  simpa only [mul_smul_comm, smul_mul_assoc, smul_neg] using h

theorem squareNorm_eq_iff_minimumSpeed (K : AntiSkewSpace a)
    (hexp : (Exponential.exp (antiSkewToSkew a K)).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    squareNorm K.val = ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 ↔ ∃ P : Space a, speed P = K := by
  constructor
  · intro he
    obtain ⟨Q, hQ⟩ := (QuaternionicColumns.squareNorm_eq_iff_complexStructure
      (antiSkewToSkew a K) hexp).mp he
    have hscaled : a.val.val * (Real.pi • Q.val.val) = -((Real.pi • Q.val.val) * a.val.val) := by
      have hop := congrArg (fun L : SkewSpace n ↦ L.val) hQ
      change Real.pi • Q.val.val = K.val at hop
      rw [hop]
      exact K.property.2
    let Q' : Space a := ⟨Q, anticommute_of_real_smul a.val.val Q.val.val
      Real.pi Real.pi_ne_zero hscaled⟩
    refine ⟨midpointParameter Q', ?_⟩
    have hs : antiSkewToSkew a (speed (midpointParameter Q')) = antiSkewToSkew a K := by
      rw [speed_toSkew, generator_midpoint]
      exact hQ
    exact Subtype.ext (congrArg (fun L : SkewSpace n ↦ L.val) hs)
  · rintro ⟨P, hP⟩
    apply (QuaternionicColumns.squareNorm_eq_iff_complexStructure (antiSkewToSkew a K) hexp).mpr
    refine ⟨(generatorParameter P).val, ?_⟩
    rw [← hP, speed_toSkew]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.AnticommutingStructures
