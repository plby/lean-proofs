import ErdosProblems.Erdos547.GESelectedPiece
import ErdosProblems.Erdos547.GEGreedyFinish
import ErdosProblems.Erdos547.MonotonePieceFilling
import ErdosProblems.Erdos547.MatchingCompletion

/-!
# The easy-skew case of the degree structure theorem

All four part budgets are positive, as supplied by tree coating. The first
skew is at most one in this case, allowing the completion lemma to cover the
whole reachable side of the selected piece.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

theorem IsMaxSaturation.anchoredTotals_of_easy_skew {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c d : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) (hd : d ∈ D.reachableVertices w c μ) (hcd : G.Adj c d)
    (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hlarge : a₁ + a₂ + b₁ + b₂ ≤ w.degree c)
    (hdeg : ∀ v, (a₁ + a₂ + b₁ + b₂) / 2 ≤ w.degree v)
    (hsmall : a₂ + b₁ ≤ (a₁ + a₂ + b₁ + b₂) / 2)
    (hbig : (a₁ + a₂ + b₁ + b₂) / 2 ≤ a₁ + b₁) :
    HasAnchoredTotals w (a₂ / a₁) (b₂ / b₁) (a₁ + a₂) (b₁ + b₂) := by
  classical
  let R := D.reachableVertices w c μ
  let M := (a₁ + a₂ + b₁ + b₂) / 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hdis : Disjoint D.separator R := Finset.disjoint_left.mpr fun _ hu hv ↦
    D.singleton_not_separator (h.reachable_singleton hv) hu
  obtain ⟨P, hP, hbetween, htotalP, hfitD, hfitC⟩ := h.exists_selected_piece hd M hM (hdeg d)
  have ha21 : a₂ ≤ a₁ := by linarith
  have hγ : a₂ / a₁ ≤ 1 := (div_le_one ha₁).mpr ha21
  have hlo : max b₁ b₂ + min a₁ a₂ ≤ P.total := by
    rw [htotalP, min_eq_right ha21]
    rcases le_total b₁ b₂ with hb | hb
    · rw [max_eq_right hb]
      dsimp [M]
      linarith
    · rw [max_eq_left hb]
      simpa only [M, add_comm b₁ a₂] using hsmall
  have hhi : P.total ≤ min b₁ b₂ + max a₁ a₂ := by
    rw [htotalP, max_eq_left ha21]
    rcases le_total b₁ b₂ with hb | hb
    · rw [min_eq_left hb]
      dsimp [M]
      linarith
    · rw [min_eq_right hb]
      dsimp [M]
      linarith
  obtain ⟨τ, σ, hdom, hτ, hlower, hout, hfit, hfull⟩ := exists_matching_completion
    P D.separator R hdis hbetween w c hfitC b₁ b₂ a₁ a₂
    hb₁ hb₂.le ha₁ ha₂.le hlo hhi
  have hp : AnchoredPair σ τ w c d :=
    (anchoredPair_of_one_side hcd.symm hdom D.separator hout hfit hfitD).swap
  have hlow : w.saturation P.load c ≤ σ.total + τ.total := by
    have hh := (le_max_right _ _).trans hlower
    linarith
  obtain ⟨σ', τ', hp', hd', hsat', hτ', hload⟩ :=
    hp.fill_fractional_remainder hdom.swap hP hlow
  have hR : M ≤ ∑ u ∈ R, (σ'.load u + τ'.load u) := by
    calc
      M = P.total := htotalP.symm
      _ = ∑ u ∈ R, P.load u := ((hbetween.swap.crosses hdis.symm).sum_load_side).symm
      _ = ∑ u ∈ R, (σ.load u + τ.load u) := Finset.sum_congr rfl fun u hu ↦ by
        have he := hfull hγ u hu
        linarith
      _ ≤ _ := Finset.sum_le_sum fun u _ ↦ hload u
  apply h.finish_from_reachable_load hp' hd' (div_pos ha₂ ha₁)
    (a₁ + a₂) (b₁ + b₂) (by positivity) (by positivity) (hτ'.trans hτ)
  · linarith
  · intro v
    linarith [hdeg v]
  · exact hsat'
  · simpa only [M, add_assoc] using hR

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.anchoredTotals_of_easy_skew
