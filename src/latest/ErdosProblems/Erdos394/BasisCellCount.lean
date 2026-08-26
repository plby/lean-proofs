import ErdosProblems.Erdos394.FundamentalCellCount
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Counting lattice points by expanded basis cells in dimension two
-/

open Set MeasureTheory Module Submodule
open scoped ENNReal Pointwise

namespace Erdos394

/-- If all lattice points in `A` lie in the square `[0,Y]²` and the fundamental
basis cell lies in `[-ρ,ρ]²`, then expanded-cell packing gives the sharp-leading
bound `|A| |det b| ≤ (Y+2ρ)²`. -/
theorem basis_lattice_card_mul_det_le
    (b : Basis (Fin 2) ℝ (Fin 2 → ℝ))
    (A : Finset (span ℤ (Set.range b))) {Y ρ : ℝ}
    (hY : 0 ≤ Y) (hρ : 0 ≤ ρ)
    (hpoint : ∀ g ∈ A, ∀ i, 0 ≤ (g : Fin 2 → ℝ) i ∧ (g : Fin 2 → ℝ) i ≤ Y)
    (hcell : ∀ x ∈ ZSpan.fundamentalDomain b, ∀ i, -ρ ≤ x i ∧ x i ≤ ρ) :
    (A.card : ℝ) * |(Pi.basisFun ℝ (Fin 2)).det b| ≤ (Y + 2 * ρ) ^ 2 := by
  let E : Set (Fin 2 → ℝ) :=
    Set.Icc (fun _ ↦ -ρ) (fun _ ↦ Y + ρ)
  have hsub :
      (⋃ g ∈ A, g +ᵥ ZSpan.fundamentalDomain b) ⊆ E := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨g, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hg, hx⟩
    rcases Set.mem_vadd_set.mp hx with ⟨f, hf, rfl⟩
    change (fun _ ↦ -ρ) ≤ g +ᵥ f ∧ g +ᵥ f ≤ (fun _ ↦ Y + ρ)
    constructor <;> intro i
    · change -ρ ≤ (g : Fin 2 → ℝ) i + f i
      have hgbox := hpoint g hg i
      have hfbox := hcell f hf i
      linarith
    · change (g : Fin 2 → ℝ) i + f i ≤ Y + ρ
      have hgbox := hpoint g hg i
      have hfbox := hcell f hf i
      linarith
  have hEfin : volume E ≠ ∞ := by
    simp [E, Real.volume_Icc_pi]
  letI : VAddInvariantMeasure (span ℤ (Set.range b))
      (Fin 2 → ℝ) volume :=
    ⟨fun c s _ ↦ measure_preimage_add volume (c : Fin 2 → ℝ) s⟩
  have hpack := fundamentalDomain_finset_card_mul_measureReal_le
    (ZSpan.isAddFundamentalDomain b volume) A hsub hEfin
  have hfund : volume.real (ZSpan.fundamentalDomain b) =
      |(Pi.basisFun ℝ (Fin 2)).det b| := by
    rw [ZSpan.measureReal_fundamentalDomain b volume (Pi.basisFun ℝ (Fin 2))]
    rw [ZSpan.fundamentalDomain_pi_basisFun]
    simp only [measureReal_def]
    rw [Real.volume_pi_Ico_toReal (by intro i; norm_num)]
    simp
  have hEmeasure : volume.real E = (Y + 2 * ρ) ^ 2 := by
    rw [show E = Set.Icc (fun _ ↦ -ρ) (fun _ ↦ Y + ρ) by rfl]
    simp only [measureReal_def]
    rw [Real.volume_Icc_pi_toReal]
    · simp [Fin.prod_univ_two]
      ring
    · intro i
      linarith
  rw [hfund, hEmeasure] at hpack
  exact hpack

end Erdos394
