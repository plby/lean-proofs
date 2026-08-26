/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The rational-certificate count after exchanging the two positive sextic coordinates.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CertificatePointBound

namespace Erdos477.Counting

open Erdos477.Geometry

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem exists_swapped_certificate_bound (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℤ, c ∉ PowerValues 6 →
      ∀ G N D : MvPolynomial (Fin 2) K, G ≠ 0 → G.totalDegree ≤ d →
      G ∣ sexticRationalCertificate 0 (c : K) N D →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, IntegerDiagonalPoint c z ∧ 1 ≤ z 1) →
      (∀ z ∈ S, MvPolynomial.eval ![(z 0 : K), (z 2 : K)] G = 0) →
      (∀ z ∈ S, MvPolynomial.eval ![(z 0 : K), (z 2 : K)] D ≠ 0) →
      (∀ z ∈ S, MvPolynomial.eval ![(z 0 : K), (z 2 : K)] N =
        (z 1 : K) * MvPolynomial.eval ![(z 0 : K), (z 2 : K)] D) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ ((1 : ℝ) / 3 + ε) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_certificate_point_bound (K := K) d ε hε
  refine ⟨C, hC, ?_⟩
  intro c hc G N D hG hdegree hdiv B hB S hS hroot hden hinverse hheight
  have hproj (z : Fin 3 → ℤ) :
      projectedFieldPoint (K := K) 0 (swapPositiveCoordinates z) = ![(z 0 : K), (z 2 : K)] := by
    funext i
    fin_cases i <;> simp [projectedFieldPoint, projectedIntegerPoint, swapPositiveCoordinates]
  have h := hbound c hc 0 (by decide) G N D hG hdegree (by simpa using hdiv)
    B hB (S.image swapPositiveCoordinates) (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      exact (hS z hz).1.swap (hS z hz).2) (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      rw [hproj]
      exact hroot z hz) (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      rw [hproj]
      exact hden z hz) (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      rw [hproj]
      exact hinverse z hz) (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      exact height_swapPositiveCoordinates z B (hheight z hz))
  rwa [Finset.card_image_of_injective _ swapPositiveCoordinates_injective] at h

#print axioms exists_swapped_certificate_bound
-- 'Erdos477.Counting.exists_swapped_certificate_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
