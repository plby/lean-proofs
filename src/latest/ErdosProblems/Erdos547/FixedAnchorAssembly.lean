import ErdosProblems.Erdos547.PieceCombination
import ErdosProblems.Erdos547.FractionalSaturation

/-!
# Combining a shared allocation, a private allocation, and the remainder
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

theorem assemble_fixed_anchor {μ C Q : FractionalMatching G} {w : EdgeWeights G} {c d : V}
    {σ : SkewMatching G γ} {τ : SkewMatching G δ} {ρ : SkewMatching G γ}
    (hp : AnchoredPair σ τ w d c) (hdom : PairDominated σ τ C)
    (hρ : ρ.DominatedByFractional Q) (hfit : ρ.Fits (w.truncate C.load C.load_nonneg) d)
    (hpieces : ∀ u v, C.weight u v + Q.weight u v ≤ μ.weight u v)
    (hloss : (w.truncate C.load C.load_nonneg).saturation Q.load c ≤ ρ.total)
    (b : ℝ) (hshared : b ≤ τ.total ∨ w.saturation C.load c - σ.total ≤ τ.total)
    (hsat : σ.total + ρ.total + b ≤ w.saturation μ.load c) :
    ∃ σ' : SkewMatching G γ, ∃ τ' : SkewMatching G δ,
      AnchoredPair σ' τ' w d c ∧ PairDominated σ' τ' μ ∧
      σ'.total = σ.total + ρ.total ∧ b ≤ τ'.total := by
  have hcap (u : V) : C.load u + Q.load u ≤ 1 := by
    have hh : C.load u + Q.load u ≤ μ.load u := by
      rw [FractionalMatching.load, FractionalMatching.load, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun v _ ↦ hpieces u v
    exact hh.trans (μ.load_le_one u)
  let H := C.add Q hcap
  have hH (u v : V) : H.weight u v ≤ μ.weight u v := hpieces u v
  have hpρ := AnchoredPair.single_left ρ δ τ.skew_nonneg _ hp.adjacent hfit
  have hdρ := PairDominated.single_left ρ δ τ.skew_nonneg hρ
  obtain ⟨σ₁, τ₁, hp₁, hd₁, htσ₁, htτ₁⟩ :=
    hp.combine_pieces hpρ hdom hdρ (show ∀ u v, C.weight u v + Q.weight u v ≤ H.weight u v
      from fun _ _ ↦ le_rfl)
  have htτ : τ₁.total = τ.total := by
    simpa only [SkewMatching.total, SkewMatching.zero, Finset.sum_const_zero, add_zero] using htτ₁
  let R := μ.sub H hH
  let r := (w.truncate H.load H.load_nonneg).saturation R.load c
  have hr : 0 ≤ r := (w.truncate H.load H.load_nonneg).saturation_nonneg R.load R.load_nonneg c
  have hR (u v : V) : H.weight u v + R.weight u v ≤ μ.weight u v := by
    change H.weight u v + (μ.weight u v - H.weight u v) ≤ _
    linarith
  obtain ⟨σ', τ', hp', hd', htσ', htτ'⟩ := hp₁.extend_right_piece hd₁ hR r hr le_rfl
  refine ⟨σ', τ', hp', hd', htσ'.trans htσ₁, ?_⟩
  rw [htτ', htτ]
  rcases hshared with hb | hb
  · linarith
  · have he₁ := C.saturation_add Q hcap w c
    have he₂ := μ.saturation_sub H hH w c
    change w.saturation C.load c +
      (w.truncate C.load C.load_nonneg).saturation Q.load c = w.saturation H.load c at he₁
    change w.saturation H.load c + r = w.saturation μ.load c at he₂
    linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.assemble_fixed_anchor
