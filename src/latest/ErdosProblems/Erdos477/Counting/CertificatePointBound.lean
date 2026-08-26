/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A uniform count from a bounded-degree plane equation and an explicit rational lift certificate.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.IntegerLiftCertificate
import ErdosProblems.Erdos477.Counting.BoundedDegreeCurves

namespace Erdos477.Counting

open Erdos477.Geometry
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem exists_certificate_point_bound (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℤ, c ∉ PowerValues 6 → ∀ a : ℕ, a ≤ 1 →
      ∀ G N D : MvPolynomial (Fin 2) K, G ≠ 0 → G.totalDegree ≤ d →
      G ∣ sexticRationalCertificate (a : K) (c : K) N D →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, IntegerDiagonalPoint c z) →
      (∀ z ∈ S, MvPolynomial.eval (projectedFieldPoint a z) G = 0) →
      (∀ z ∈ S, MvPolynomial.eval (projectedFieldPoint a z) D ≠ 0) →
      (∀ z ∈ S, MvPolynomial.eval (projectedFieldPoint a z) N =
        (z 0 : K) * MvPolynomial.eval (projectedFieldPoint a z) D) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ ((1 : ℝ) / 3 + ε) := by
  classical
  obtain ⟨L, hL, hcurve⟩ := exists_bounded_degree_curve_bound (K := K) 3 d (by decide) ε hε
  let A : ℝ := 4 + L * 2 ^ ((1 : ℝ) / 3 + ε)
  have hA : 0 < A := by dsimp only [A]; positivity
  let C : ℝ := d * A + 1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro c hc a ha G N D hG hdegree hdiv B hB S hS hroot hden hinverse hheight
  have hB0 : 0 ≤ B := by linarith
  have hpower : 1 ≤ B ^ ((1 : ℝ) / 3 + ε) := Real.one_le_rpow hB (by positivity)
  obtain ⟨F, hF, _, _, hFcard, hcover⟩ := exists_distinct_factor_cover G hG
  let U := fun P : MvPolynomial (Fin 2) K =>
    S.filter (fun z => MvPolynomial.eval (projectedFieldPoint a z) P = 0)
  have heach (P) (hPF : P ∈ F) : ((U P).card : ℝ) ≤ A * B ^ ((1 : ℝ) / 3 + ε) := by
    have hP := (hF P hPF).1
    have hPd := (MvPolynomial.totalDegree_le_of_dvd_of_isDomain (hF P hPF).2 hG).trans hdegree
    have hUS : U P ⊆ S := Finset.filter_subset _ _
    by_cases hsmall : P.totalDegree ≤ 2
    · have hcount := card_low_degree_certificate_points_le c hc a P N D hP hsmall
        ((hF P hPF).2.trans hdiv) (U P) (fun z hz => hS z (hUS hz))
        (fun _ hz => (Finset.mem_filter.mp hz).2)
        (fun z hz => hden z (hUS hz)) (fun z hz => hinverse z (hUS hz))
      have hcountR : ((U P).card : ℝ) ≤ 4 := by exact_mod_cast hcount
      have h4A : (4 : ℝ) ≤ A := by
        dsimp only [A]
        have hnonneg : 0 ≤ L * 2 ^ ((1 : ℝ) / 3 + ε) := by positivity
        linarith
      exact (hcountR.trans h4A).trans (le_mul_of_one_le_right hA.le hpower)
    · let T := (U P).image (projectedIntegerPoint a)
      have hT := hcurve (2 * B) (by linarith) P hP (by omega) hPd T (by
        intro w hw
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp hz).2) (by
        intro w hw
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
        exact height_projectedIntegerPoint a ha z B hB0 (hheight z (hUS hz)))
      rw [show T.card = (U P).card from Finset.card_image_of_injOn
        (projectedIntegerPoint_injOn_of_inverse a N D (U P)
          (fun z hz => hden z (hUS hz)) (fun z hz => hinverse z (hUS hz))),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hB0, ← mul_assoc] at hT
      apply hT.trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hB0 _)
      dsimp only [A]
      linarith
  have hsub : S ⊆ F.biUnion U := by
    intro z hz
    obtain ⟨P, hPF, hzero⟩ := hcover (projectedFieldPoint a z) (hroot z hz)
    exact Finset.mem_biUnion.mpr ⟨P, hPF, Finset.mem_filter.mpr ⟨hz, hzero⟩⟩
  have hnat : S.card ≤ ∑ P ∈ F, (U P).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hreal : (S.card : ℝ) ≤ ∑ P ∈ F, ((U P).card : ℝ) := by exact_mod_cast hnat
  have hFd : (F.card : ℝ) ≤ d := by exact_mod_cast hFcard.trans hdegree
  calc
    _ ≤ ∑ P ∈ F, ((U P).card : ℝ) := hreal
    _ ≤ ∑ _P ∈ F, A * B ^ ((1 : ℝ) / 3 + ε) := Finset.sum_le_sum heach
    _ = (F.card : ℝ) * (A * B ^ ((1 : ℝ) / 3 + ε)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d : ℝ) * (A * B ^ ((1 : ℝ) / 3 + ε)) :=
      mul_le_mul_of_nonneg_right hFd (by positivity)
    _ ≤ C * B ^ ((1 : ℝ) / 3 + ε) := by
      dsimp only [C]
      nlinarith [Real.rpow_nonneg hB0 ((1 : ℝ) / 3 + ε)]

#print axioms exists_certificate_point_bound
-- 'Erdos477.Counting.exists_certificate_point_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
