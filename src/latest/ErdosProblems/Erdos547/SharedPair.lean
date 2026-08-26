import ErdosProblems.Erdos547.ResidualBudgets
import ErdosProblems.Erdos547.PieceCombination
import ErdosProblems.Erdos547.FractionalSaturation
import ErdosProblems.Erdos547.CappingLoss

/-!
# Allocating a shared piece while preserving the anchor order
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_shared_pair (C : FractionalMatching G) (U : Finset V) (hcross : C.Crosses U)
    (w : EdgeWeights G) {c d : V} (hcd : G.Adj c d)
    (hfitC : ∀ u, C.load u ≤ w.weight c u) (hfitD : ∀ u ∈ U, C.load u ≤ w.weight d u)
    (γ δ r s : ℝ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hs : 0 < s)
    (hbound : 0 < r → max (r / (1 + γ)) (γ * (r / (1 + γ))) +
      min (s / (1 + δ)) (δ * (s / (1 + δ))) ≤ C.total) :
    ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ,
      AnchoredPair σ τ w d c ∧ PairDominated σ τ C ∧ σ.total = r ∧
      (s ≤ τ.total ∨ w.saturation C.load c - σ.total ≤ τ.total) := by
  classical
  by_cases hr0 : r = 0
  · let τ := C.toSkew δ hδ
    have hτ : τ.DominatedByFractional C := C.toSkew_dominated δ hδ
    have hfit : τ.Fits w c := fun u ↦
      ((τ.outLoad_le_load u).trans (hτ.load_le u)).trans (hfitC u)
    have hp := AnchoredPair.single_left τ γ hγ w hcd hfit
    have hd := PairDominated.single_left τ γ hγ hτ
    refine ⟨SkewMatching.zero G γ hγ, τ, hp.swap, hd.swap, ?_, Or.inr ?_⟩
    · simp only [SkewMatching.total, SkewMatching.zero, Finset.sum_const_zero, hr0]
    · have he : τ.total = 2 * C.total := C.toSkew_total δ hδ
      rw [C.saturation_eq_twice_total w c hfitC, he]
      simp only [SkewMatching.total, SkewMatching.zero, Finset.sum_const_zero, sub_zero, le_refl]
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hbound := hbound hrpos
  obtain ⟨ha₁, ha₂, hsumA, hratioA⟩ := positive_skew_parts r γ hrpos hγ
  obtain ⟨hb₁, hb₂, hsumB, hratioB⟩ := positive_skew_parts s δ hs hδ
  by_cases hsum : r + s ≤ 2 * C.total
  · have hex := exists_improved_balancing_le C U Uᶜ disjoint_compl_right hcross.runsBetween
      (r / (1 + γ)) (γ * (r / (1 + γ))) (s / (1 + δ)) (δ * (s / (1 + δ)))
      ha₁ ha₂ hb₁ hb₂ (by linarith) hbound
    rw [hratioA, hratioB] at hex
    obtain ⟨σ, τ, hdom, hσ, hτ, hout, _⟩ := hex
    have hfit : τ.Fits w c := fun u ↦
      ((τ.outLoad_le_load u).trans (hdom.right.load_le u)).trans (hfitC u)
    exact ⟨σ, τ, anchoredPair_of_one_side hcd.symm hdom U hout hfit hfitD,
      hdom, hσ.trans hsumA, Or.inl (hτ.trans hsumB).ge⟩
  · have hhi : C.total ≤ min (r / (1 + γ)) (γ * (r / (1 + γ))) +
        max (s / (1 + δ)) (δ * (s / (1 + δ))) := by
      linarith [min_add_max (r / (1 + γ)) (γ * (r / (1 + γ))),
        min_add_max (s / (1 + δ)) (δ * (s / (1 + δ)))]
    obtain ⟨σ, τ, hdom, hσ, hlower, hout, hfit⟩ := exists_completion_of_totals
      C U Uᶜ disjoint_compl_right hcross.runsBetween w c (fun u _ ↦ hfitC u)
      γ δ r s hγ hδ hrpos hs hbound hhi
    exact ⟨σ, τ, anchoredPair_of_one_side hcd.symm hdom U hout hfit hfitD,
      hdom, hσ, Or.inr ((le_max_right _ _).trans hlower)⟩

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_shared_pair
