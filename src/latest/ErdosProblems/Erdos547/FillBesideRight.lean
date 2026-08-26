import ErdosProblems.Erdos547.PieceCombination
import ErdosProblems.Erdos547.FractionalSaturation

/-!
# Filling the fractional remainder beside a fixed right allocation
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {δ : ℝ}

theorem fill_beside_right (F P : FractionalMatching G) (hP : ∀ u v, P.weight u v ≤ F.weight u v)
    (w : EdgeWeights G) {c d : V} (hcd : G.Adj c d) (β : SkewMatching G δ)
    (hβ : β.DominatedByFractional P) (hfitβ : β.Fits w d)
    (hbudget : w.saturation P.load c ≤ β.total) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ α : SkewMatching G γ, AnchoredPair α β w c d ∧ PairDominated α β F ∧
      w.saturation F.load c ≤ α.total + β.total := by
  let R := F.sub P hP
  let r := (w.truncate P.load P.load_nonneg).saturation R.load c
  have hr : 0 ≤ r := (w.truncate P.load P.load_nonneg).saturation_nonneg R.load R.load_nonneg c
  obtain ⟨α, hα, hfitα, htotal⟩ := exists_skew_of_saturation_exact R
    (w.truncate P.load P.load_nonneg) c γ hγ r hr le_rfl
  have hdom : PairDominated α β F := by
    intro u v
    have h₁ := hα u v
    have h₂ := hβ u v
    change α.endpointWeight u v ≤ F.weight u v - P.weight u v at h₁
    linarith
  refine ⟨α, ⟨hcd, fun u ↦ (hdom.load_le u).trans (F.load_le_one u), ?_, hfitβ, ?_⟩,
    hdom, ?_⟩
  · intro u
    exact (hfitα u).trans (w.truncate_weight_le P.load P.load_nonneg c u)
  · intro u
    have htail : β.outLoad u ≤ P.load u := (β.outLoad_le_load u).trans (hβ.load_le u)
    have hother : α.outLoad u ≤ max 0 (max (w.weight c u) (w.weight d u) - P.load u) :=
      (hfitα u).trans (max_le_max_left _ (sub_le_sub_right (le_max_left _ _) _))
    have hh := add_le_of_le_truncated ((hfitβ u).trans (le_max_right _ _)) htail hother
    linarith
  · have he := F.saturation_sub P hP w c
    change w.saturation P.load c + r = w.saturation F.load c at he
    rw [htotal]
    linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.fill_beside_right
