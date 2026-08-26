/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Counting the low-degree factors of an explicit rational lift certificate.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.IntegerDiagonal
import ErdosProblems.Erdos477.Geometry.RationalLiftCertificate
import ErdosProblems.Erdos477.Geometry.CurveSingularPoints
import ErdosProblems.Erdos477.Geometry.PlaneFactors

namespace Erdos477.Geometry

def projectedIntegerPoint (a : ℕ) (z : Fin 3 → ℤ) : Fin 2 → ℤ := ![z 1 + a * z 0, z 2]

variable {K : Type*} [Field K] [CharZero K]

def projectedFieldPoint (a : ℕ) (z : Fin 3 → ℤ) : Fin 2 → K :=
  fun i => (projectedIntegerPoint a z i : K)

lemma projectedIntegerPoint_injOn_of_inverse (a : ℕ) (N D : MvPolynomial (Fin 2) K)
    (S : Finset (Fin 3 → ℤ))
    (hden : ∀ z ∈ S, MvPolynomial.eval (projectedFieldPoint a z) D ≠ 0)
    (hinverse : ∀ z ∈ S, MvPolynomial.eval (projectedFieldPoint a z) N =
      (z 0 : K) * MvPolynomial.eval (projectedFieldPoint a z) D) :
    Set.InjOn (projectedIntegerPoint a) S := by
  intro z hz w hw heq
  have hfield : projectedFieldPoint (K := K) a z = projectedFieldPoint a w := by
    funext i
    exact congrArg (Int.cast : ℤ → K) (congrFun heq i)
  have hN := hinverse z hz
  rw [hfield] at hN
  have h0 : z 0 = w 0 := Int.cast_injective
    (mul_right_cancel₀ (hden w hw) (hN.symm.trans (hinverse w hw)))
  have h1 : z 1 + a * z 0 = w 1 + a * w 0 := congrFun heq 0
  have h2 : z 2 = w 2 := congrFun heq 1
  rw [h0] at h1
  funext i
  fin_cases i
  · exact h0
  · exact add_right_cancel h1
  · exact h2

lemma height_projectedIntegerPoint (a : ℕ) (ha : a ≤ 1) (z : Fin 3 → ℤ)
    (B : ℝ) (hB : 0 ≤ B) (hz : ∀ i, |(z i : ℝ)| ≤ B) :
    ∀ i, |(projectedIntegerPoint a z i : ℝ)| ≤ 2 * B := by
  intro i
  fin_cases i
  · change |((z 1 + (a : ℤ) * z 0 : ℤ) : ℝ)| ≤ _
    push_cast
    calc
      _ ≤ |(z 1 : ℝ)| + |(a : ℝ) * (z 0 : ℝ)| := abs_add_le _ _
      _ = |(z 1 : ℝ)| + (a : ℝ) * |(z 0 : ℝ)| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
      _ ≤ B + 1 * B := by gcongr <;> first | exact hz _ | exact_mod_cast ha
      _ = _ := by ring
  · change |(z 2 : ℝ)| ≤ _
    exact (hz 2).trans (by linarith)

variable [IsAlgClosed K]

theorem no_smooth_selected_integer_point_of_rational_certificate
    (c : ℤ) (hc : c ∉ PowerValues 6) (z : Fin 3 → ℤ) (hz : IntegerDiagonalPoint c z) (a : ℕ)
    (P N D : MvPolynomial (Fin 2) K) (hP : Irreducible P) (hdegree : P.totalDegree ≤ 2)
    (hdiv : P ∣ sexticRationalCertificate (a : K) (c : K) N D)
    (hroot : MvPolynomial.eval (projectedFieldPoint a z) P = 0)
    (hgradient : ∃ i, MvPolynomial.eval (projectedFieldPoint a z) (MvPolynomial.pderiv i P) ≠ 0)
    (hden : MvPolynomial.eval (projectedFieldPoint a z) D ≠ 0)
    (hinverse : MvPolynomial.eval (projectedFieldPoint a z) N =
      (z 0 : K) * MvPolynomial.eval (projectedFieldPoint a z) D) : False := by
  have hcast (i : Fin 3) : ((z i).toNat : K) = (z i : K) := by exact_mod_cast hz.cast_toNat i
  have hproj : ![((z 1).toNat : K) + (a : K) * (z 0).toNat, ((z 2).toNat : K)] =
      projectedFieldPoint a z := by
    funext i
    fin_cases i <;> simp [projectedFieldPoint, projectedIntegerPoint, hcast]
  apply no_smooth_selected_point_of_rational_certificate c hc
    (z 0).toNat (z 2).toNat (z 1).toNat hz.first_positive hz.toNat a P N D hP hdegree hdiv
  · rwa [hproj]
  · rwa [hproj]
  · rwa [hproj]
  · rwa [hproj, hcast 0]

theorem card_low_degree_certificate_points_le
    (c : ℤ) (hc : c ∉ PowerValues 6) (a : ℕ) (P N D : MvPolynomial (Fin 2) K)
    (hP : Irreducible P) (hdegree : P.totalDegree ≤ 2)
    (hdiv : P ∣ sexticRationalCertificate (a : K) (c : K) N D)
    (S : Finset (Fin 3 → ℤ)) (hS : ∀ z ∈ S, IntegerDiagonalPoint c z)
    (hroot : ∀ z ∈ S, MvPolynomial.eval (projectedFieldPoint a z) P = 0)
    (hden : ∀ z ∈ S, MvPolynomial.eval (projectedFieldPoint a z) D ≠ 0)
    (hinverse : ∀ z ∈ S, MvPolynomial.eval (projectedFieldPoint a z) N =
      (z 0 : K) * MvPolynomial.eval (projectedFieldPoint a z) D) : S.card ≤ 4 := by
  classical
  have hsingular (z) (hz : z ∈ S) (i) :
      MvPolynomial.eval (projectedFieldPoint a z) (MvPolynomial.pderiv i P) = 0 := by
    by_contra h
    exact no_smooth_selected_integer_point_of_rational_certificate c hc z (hS z hz) a P N D
      hP hdegree hdiv (hroot z hz) ⟨i, h⟩ (hden z hz) (hinverse z hz)
  let T := S.image (projectedIntegerPoint a)
  have h := card_integer_curve_singular_points_le P hP (totalDegree_pos_of_irreducible P hP) T
    (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      exact hroot z hz) (by
      intro w hw i
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      exact hsingular z hz i)
  rw [show T.card = S.card from Finset.card_image_of_injOn
    (projectedIntegerPoint_injOn_of_inverse a N D S hden hinverse)] at h
  exact h.trans (Nat.mul_le_mul hdegree ((Nat.sub_le _ _).trans hdegree))

#print axioms card_low_degree_certificate_points_le
-- 'Erdos477.Geometry.card_low_degree_certificate_points_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
