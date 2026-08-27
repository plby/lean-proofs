import ErdosProblems.Erdos587.HooleyModelExtraction
import ErdosProblems.Erdos587.HooleyPreprocessingBudgets

/-! # Preprocessing and extraction retain a constant fraction of a robust model -/

open scoped BigOperators Pointwise
open Erdos587.GeneralizedAP

namespace Erdos587.CFP

theorem delta_full_width_GAP_of_robust_model (P : GeneralizedAP) (A : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hA : A ⊆ P.carrier) (hL : ∀ i, 0 < P.length i)
    (hpositive : ∀ a ∈ A, 0 < a) (L h M : ℕ) (hh : 2 ≤ h) (hM : 1 ≤ M)
    (hsum : ∑ a ∈ A, a ≤ (2 : ℤ) ^ (2 * L + 1))
    (hweak : ∀ B ⊆ A, A.card ≤ 3 * B.card →
      2 * (P.dilate h).boxCard < M * (h • insert 0 B).card ∧
      (generatedSubgroup P.centeredCoordinates B).FiniteIndex ∧
      (generatedSubgroup P.centeredCoordinates B).index ≤ M ^ P.rank ∧
      Submodule.span ℝ ((intCastVec ∘ P.centeredCoordinates) '' (B : Set ℤ)) = ⊤)
    (hindex : M ^ P.rank ≤ h) (hlinear : 8 * (L + 1) + 1 ≤ h)
    (hcard : 6 * h ^ 5 + 6 ≤ A.card)
    (hlarge : 16 * ((4 ^ P.rank : ℕ) : ℝ) ≤
      (1 / ((4 ^ (P.rank + 1) : ℕ) : ℝ)) * ((A.card / 2 : ℕ) : ℝ)) :
    let c := 2 * (Nat.log 2 (nvCoordBox (fun i => 2 * (h * P.length i))).card + 1)
    let D := (2 ^ P.rank * M) * c ^ P.rank
    deltaSeedCostConstant P.rank * D ^ deltaSeedPower P.rank ≤ h →
    let K := ⌈32 * ((4 ^ P.rank : ℕ) : ℝ) / (1 / ((4 ^ (P.rank + 1) : ℕ) : ℝ))⌉₊
    let F := 9 * P.rank * K
    let m := A.card / 2
    0 < F ∧ ∃ Q : GeneralizedAP, 0 < Q.rank ∧ Q.rank ≤ P.rank ∧ Q.Proper ∧ Q.HasHomogeneousBase ∧
      (Q.carrier : Set ℤ) ⊆ (A.subsetSum : Set ℤ) ∧
      (∀ i, m ≤ F * Q.length i) ∧ m ^ (Q.rank + 1) ≤ 2 * F ^ Q.rank * Q.carrier.card ∧
      (Q.upperEndpoint : ℝ) ≤ (((3 : ℝ) / 2) * K + 1) * Q.coefficientSpan := by
  classical
  let I := M ^ P.rank
  let T := 4 * h ^ 4 * (2 * L + 2) + I * h ^ 2
  have htotal : T + h ^ 2 ≤ h ^ 5 := by
    have hh' := delta_preprocessing_cost_le h L I hh hindex hlinear
    dsimp only [T]
    nlinarith
  have hbudget : 3 * (4 * h ^ 4 * (2 * L + 1 + 1) + (I + 1) * h ^ 2) ≤ 2 * A.card := by
    calc
      _ = 3 * (T + h ^ 2) := by dsimp only [T]; ring
      _ ≤ 3 * h ^ 5 := Nat.mul_le_mul_left 3 htotal
      _ ≤ 2 * A.card := by omega
  obtain ⟨C, hCA, hcost, hfinite, hCindex, hstable, hreserve⟩ :=
    delta_exists_balanced_stable_subset P.centeredCoordinates A (2 * L + 1) (h ^ 4) (h ^ 2) I
      (by positivity) (fun a ha => (hpositive a ha).le) hsum
      (fun B hBA hBcard => ⟨(hweak B hBA hBcard).2.1, (hweak B hBA hBcard).2.2.1⟩)
      hbudget (delta_preprocessing_reserve_budget h I hh hindex)
  have hcost' : A.card ≤ C.card + T := by simpa only [Nat.add_assoc] using hcost
  obtain ⟨hhalf, hkeep, hthreshold⟩ :=
    delta_preprocessing_retained_budgets A.card C.card T (h ^ 2) (h ^ 5) hcost' htotal hcard
  have hmlower : A.card / 2 ≤ C.card - h ^ 2 := by omega
  have hdense : ∀ B ⊆ C, C.card ≤ B.card + h ^ 2 →
      2 * (P.dilate h).boxCard < M * (h • insert 0 B).card := by
    intro B hBC hBcard
    exact (hweak B (hBC.trans hCA) (by omega)).1
  have hspan : ∀ B ⊆ C, (A.card + 2) / 3 ≤ B.card →
      Submodule.span ℝ ((intCastVec ∘ P.centeredCoordinates) '' (B : Set ℤ)) = ⊤ := by
    intro B hBC hBcard
    exact (hweak B (hBC.trans hCA) (by omega)).2.2.2
  have hlarge' : 16 * ((4 ^ P.rank : ℕ) : ℝ) ≤
      (1 / ((4 ^ (P.rank + 1) : ℕ) : ℝ)) * ((C.card - h ^ 2 : ℕ) : ℝ) := hlarge.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hmlower) (by positivity))
  dsimp only
  intro hpower
  obtain ⟨hF, Q, hQpos, hQrank, hQproper, hQhom, hQsub, hside, hsize, hheight⟩ :=
    delta_full_width_GAP_of_integer_model P C hzero (hCA.trans hA) hL
      (fun a ha => hpositive a (hCA ha)) h M ((A.card + 2) / 3) (by omega) hM hfinite hCindex
      hdense hstable hspan hreserve hhalf hlarge' hpower
  exact ⟨hF, Q, hQpos, hQrank, hQproper, hQhom,
    hQsub.trans (Finset.subsetSum_mono hCA), (fun i => hmlower.trans (hside i)),
    (Nat.pow_le_pow_left hmlower _).trans hsize, hheight⟩

end Erdos587.CFP
