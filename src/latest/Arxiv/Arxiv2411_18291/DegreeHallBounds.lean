import Arxiv.Arxiv2411_18291.PartialHall
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! # A Hall defect bound from lower and upper degrees -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem hall_defect_of_degree_bounds {I X : Type*} [Fintype I] [DecidableEq X]
    (t : I → Finset X) {δ Δ : ℝ} (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ)
    (hmin : ∀ i, δ ≤ ((t i).card : ℝ))
    (hmax : ∀ x, ((univ.filter fun i => x ∈ t i).card : ℝ) ≤ Δ)
    (d : ℕ) (hdefect : (Δ - δ) * Fintype.card I ≤ Δ * d) :
    ∀ s : Finset I, s.card ≤ (s.biUnion t).card + d := by
  classical
  intro s
  let U := s.biUnion t
  have habove (i : I) (hi : i ∈ s) : U.bipartiteAbove (fun i x => x ∈ t i) i = t i := by
    ext x
    simp only [mem_bipartiteAbove]
    exact ⟨And.right, fun hx => ⟨mem_biUnion.mpr ⟨i, hi, hx⟩, hx⟩⟩
  have hbelow (x : X) : s.bipartiteBelow (fun i x => x ∈ t i) x ⊆
      univ.filter (fun i => x ∈ t i) := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩
  have hcounts : (s.card : ℝ) * δ ≤ (U.card : ℝ) * Δ := by
    have h := card_nsmul_le_card_nsmul (fun i x => x ∈ t i) (s := s) (t := U)
      (m := δ) (n := Δ)
      (fun i hi => by simpa only [habove i hi] using hmin i)
      (fun x _ => (by exact_mod_cast card_le_card (hbelow x) :
        ((s.bipartiteBelow (fun i x => x ∈ t i) x).card : ℝ) ≤
          ((univ.filter fun i => x ∈ t i).card : ℝ)).trans (hmax x))
    simpa only [nsmul_eq_mul] using h
  have hscard : (s.card : ℝ) ≤ Fintype.card I := by
    exact_mod_cast card_le_univ s
  have hscale := mul_le_mul_of_nonneg_left hscard (sub_nonneg.mpr hδΔ)
  have hreal : (s.card : ℝ) ≤ (U.card : ℝ) + d := by
    apply (mul_le_mul_iff_right₀ hΔ).mp
    nlinarith only [hcounts, hscale, hdefect]
  exact_mod_cast hreal

theorem exists_partial_transversal_of_degree_bounds {I X : Type*} [Fintype I] [DecidableEq X]
    (t : I → Finset X) {δ Δ : ℝ} (hΔ : 0 < Δ) (hδΔ : δ ≤ Δ)
    (hmin : ∀ i, δ ≤ ((t i).card : ℝ))
    (hmax : ∀ x, ((univ.filter fun i => x ∈ t i).card : ℝ) ≤ Δ)
    (d : ℕ) (hdefect : (Δ - δ) * Fintype.card I ≤ Δ * d) :
    ∃ S : Finset I, Fintype.card I ≤ S.card + d ∧
      ∃ g : S → X, Function.Injective g ∧ ∀ i : S, g i ∈ t i.val :=
  exists_partial_transversal t d (hall_defect_of_degree_bounds t hΔ hδΔ hmin hmax d hdefect)

end Arxiv2411_18291
