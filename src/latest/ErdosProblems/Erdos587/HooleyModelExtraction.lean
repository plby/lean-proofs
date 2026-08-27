import ErdosProblems.Erdos587.HooleyCoefficientModel
import ErdosProblems.Erdos587.HooleyStableSeed

/-! # Full-width extraction from a robust interval coordinate model -/

open scoped BigOperators Pointwise
open Erdos587.GeneralizedAP

namespace Erdos587.CFP

theorem delta_full_width_GAP_of_integer_model (P : GeneralizedAP) (A : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hA : A ⊆ P.carrier) (hL : ∀ i, 0 < P.length i)
    (hpositive : ∀ a ∈ A, 0 < a) (h M k : ℕ) (hh : 0 < h) (hM : 1 ≤ M)
    (hfinite : (generatedSubgroup P.centeredCoordinates A).FiniteIndex)
    (hindex : (generatedSubgroup P.centeredCoordinates A).index ≤ M ^ P.rank)
    (hdense : ∀ B ⊆ A, A.card ≤ B.card + h ^ 2 →
      2 * (P.dilate h).boxCard < M * (h • insert 0 B).card)
    (hstable : ∀ B ⊆ A, A.card ≤ B.card + h ^ 2 →
      generatedSubgroup P.centeredCoordinates B = generatedSubgroup P.centeredCoordinates A)
    (hspan : ∀ B ⊆ A, k ≤ B.card →
      Submodule.span ℝ ((intCastVec ∘ P.centeredCoordinates) '' (B : Set ℤ)) = ⊤)
    (hreserve : ∀ B ⊆ A, B.card ≤ h ^ 2 → ∑ a ∈ B, a ≤ ∑ a ∈ A \ B, a)
    (hcard : 2 * k + h ^ 2 + 1 ≤ A.card)
    (hlarge : 16 * ((4 ^ P.rank : ℕ) : ℝ) ≤
      (1 / ((4 ^ (P.rank + 1) : ℕ) : ℝ)) * ((A.card - h ^ 2 : ℕ) : ℝ)) :
    let c := 2 * (Nat.log 2 (nvCoordBox (fun i => 2 * (h * P.length i))).card + 1)
    let D := (2 ^ P.rank * M) * c ^ P.rank
    deltaSeedCostConstant P.rank * D ^ deltaSeedPower P.rank ≤ h →
    let K := ⌈32 * ((4 ^ P.rank : ℕ) : ℝ) / (1 / ((4 ^ (P.rank + 1) : ℕ) : ℝ))⌉₊
    let F := 9 * P.rank * K
    let m := A.card - h ^ 2
    0 < F ∧ ∃ Q : GeneralizedAP, 0 < Q.rank ∧ Q.rank ≤ P.rank ∧ Q.Proper ∧ Q.HasHomogeneousBase ∧
      (Q.carrier : Set ℤ) ⊆ (A.subsetSum : Set ℤ) ∧
      (∀ i, m ≤ F * Q.length i) ∧ m ^ (Q.rank + 1) ≤ 2 * F ^ Q.rank * Q.carrier.card ∧
      (Q.upperEndpoint : ℝ) ≤ (((3 : ℝ) / 2) * K + 1) * Q.coefficientSpan := by
  classical
  let U := A.image P.centeredCoordinates
  have hinj := delta_centeredCoordinates_injOn P A hzero hA
  have hUcard : U.card = A.card := Finset.card_image_of_injOn hinj
  have hΓ : generatedSubgroup id U = generatedSubgroup P.centeredCoordinates A :=
    delta_generatedSubgroup_image P.centeredCoordinates A
  let _ : (generatedSubgroup id U).FiniteIndex := by rw [hΓ]; exact hfinite
  let c := 2 * (Nat.log 2 (nvCoordBox (fun i => 2 * (h * P.length i))).card + 1)
  let D := (2 ^ P.rank * M) * c ^ P.rank
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hrank : 0 < P.rank :=
    delta_model_rank_pos P A hA (by nlinarith [Nat.one_le_iff_ne_zero.mpr hh.ne'])
  have hc : c ≤ D := by
    calc
      c = c ^ 1 := (pow_one _).symm
      _ ≤ c ^ P.rank := Nat.pow_le_pow_right hcpos hrank
      _ ≤ D := Nat.le_mul_of_pos_left _ (by positivity)
  have hMD : M ≤ D :=
    (Nat.le_mul_of_pos_left M (by positivity : 0 < 2 ^ P.rank)).trans
      (Nat.le_mul_of_pos_right _ (pow_pos hcpos _))
  have hI : (generatedSubgroup id U).index ≤ D ^ P.rank := by
    rw [hΓ]
    exact hindex.trans (Nat.pow_le_pow_left hMD _)
  dsimp only
  intro hpower
  have hpositiveU : ∀ u ∈ U, 0 < P.nvLinearEvalHom u := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    rw [P.linearEval_centeredCoordinates hzero (hA ha)]
    exact hpositive a ha
  obtain ⟨hF, Q, hQpos, hQrank, hQproper, hQhom, hQsub, hside, hsize, hheight⟩ :=
    delta_full_width_GAP_of_stable_coefficients U P.length P.nvLinearEvalHom hL
      (by intro u hu i; obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
          exact delta_centeredCoordinates_abs_bound P a i)
      (delta_eval_injOn_centered_image P A hzero hA) hpositiveU h (2 ^ P.rank * M) k hh
      (by
        have hmul : 0 < 2 ^ P.rank * M := by positivity
        omega)
      (delta_centered_image_density P A hzero hA h M (h ^ 2) hdense)
      (delta_centered_image_stability P A hzero hA (h ^ 2) hstable)
      (delta_centered_image_robust_spanning P A hzero hA k hspan)
      (delta_centered_image_reserve_mass P A hzero hA (h ^ 2) hreserve)
      (by rwa [hUcard]) (by rwa [hUcard]) hc hI hpower
  have heval : U.image P.nvLinearEvalHom = A := delta_eval_centered_image P A hzero hA
  rw [heval] at hQsub
  rw [hUcard] at hside hsize
  exact ⟨hF, Q, hQpos, hQrank, hQproper, hQhom, hQsub, hside, hsize, hheight⟩

end Erdos587.CFP
