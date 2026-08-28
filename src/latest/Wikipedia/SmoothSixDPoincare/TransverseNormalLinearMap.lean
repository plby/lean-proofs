import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Normal derivatives of complementary transverse linear maps

A surjective normal projection annihilating the first tangent map sends the
complementary transverse tangent map onto the whole normal space. In equal
finite dimensions this normal map is bijective.
-/

noncomputable section

open Function

namespace Wikipedia.SmoothSixDPoincare.TransverseCoordinates

variable {D Z E B : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Reversing the order of two transverse tangent maps preserves surjectivity. -/
theorem surjective_coprod_swap (A : D →L[ℝ] E) (C : Z →L[ℝ] E)
    (h : Surjective (A.coprod C)) : Surjective (C.coprod A) := by
  intro w
  obtain ⟨⟨u, v⟩, huv⟩ := h w
  refine ⟨(v, u), ?_⟩
  change C v + A u = w
  rw [add_comm]
  exact huv

/-- Projecting a transverse tangent sum onto the normal space preserves surjectivity. -/
theorem surjective_normal_comp (Q : E →L[ℝ] B) (A : D →L[ℝ] E) (C : Z →L[ℝ] E)
    (hQ : Surjective Q) (hAC : Surjective (A.coprod C)) (hQA : Q.comp A = 0) :
    Surjective (Q.comp C) := by
  intro w
  obtain ⟨z, hz⟩ := hQ w
  obtain ⟨⟨u, v⟩, huv⟩ := hAC z
  have hAu : Q (A u) = 0 := congrArg (fun T : D →L[ℝ] B => T u) hQA
  refine ⟨v, ?_⟩
  change Q (C v) = w
  have hsum : Q (A u + C v) = w := (congrArg Q huv).trans hz
  simpa only [map_add, hAu, zero_add] using hsum

/-- A complementary transverse sheet has an invertible derivative in normal coordinates. -/
theorem bijective_normal_comp [FiniteDimensional ℝ Z] [FiniteDimensional ℝ B]
    (Q : E →L[ℝ] B) (A : D →L[ℝ] E) (C : Z →L[ℝ] E)
    (hQ : Surjective Q) (hAC : Surjective (A.coprod C)) (hQA : Q.comp A = 0)
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) : Bijective (Q.comp C) := by
  have hs := surjective_normal_comp Q A C hQ hAC hQA
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hs, hs⟩

end Wikipedia.SmoothSixDPoincare.TransverseCoordinates
