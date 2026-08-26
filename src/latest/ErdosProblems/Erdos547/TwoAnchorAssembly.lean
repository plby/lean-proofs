import ErdosProblems.Erdos547.PrivatePieceSaturation
import ErdosProblems.Erdos547.PieceCombination

/-!
# Assembling the two-anchor allocation

The same assembly handles both a partial private piece and the entire
private piece. This avoids separate gluing arguments in the easy and hard
cases of the two-anchor lemma.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ δ : ℝ}

namespace SaturationDecomposition

theorem assemble_private_piece {μ : FractionalMatching G} {w : EdgeWeights G} {c d : V}
    (D : SaturationDecomposition μ w d)
    (E : CrossAnchorSplit D.cross D.active (w.truncate D.full.load D.full.load_nonneg) c)
    (hcd : G.Adj c d) (Q : FractionalMatching G)
    (hQ : ∀ u v, Q.weight u v ≤ E.privatePart.weight u v)
    (σs : SkewMatching G γ) (τs : SkewMatching G δ) (hdoms : PairDominated σs τs E.shared)
    (hout : ∀ u ∉ D.active, σs.outLoad u = 0)
    (hfit : τs.Fits (w.truncate D.full.load D.full.load_nonneg) c)
    (hlower : (w.truncate D.full.load D.full.load_nonneg).saturation E.shared.load c -
      σs.total ≤ τs.total) :
    ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ,
      AnchoredPair σ τ w d c ∧ PairDominated σ τ μ ∧
      σ.total = 2 * D.full.total + σs.total + Q.total ∧
      w.saturation μ.load c - σ.total ≤ τ.total := by
  let σI := D.full.toSkew γ σs.skew_nonneg
  have hσI : σI.DominatedByFractional D.full := D.full.toSkew_dominated γ σs.skew_nonneg
  have hIfit : σI.Fits w d := fun u ↦
    ((σI.outLoad_le_load u).trans (hσI.load_le u)).trans (D.full_fits u)
  have hI := AnchoredPair.single_left σI δ τs.skew_nonneg w hcd.symm hIfit
  have hIdom := PairDominated.single_left σI δ τs.skew_nonneg hσI
  have hs := anchoredPair_of_one_side hcd.symm hdoms D.active hout hfit (fun u hu ↦
    (E.shared.load_le_of_weight_le D.cross E.shared_le u).trans
      ((D.active_cross_fits hu).trans (le_max_right _ _)))
  let H₁ := D.sharedUsed E
  have hpieces₁ (u v : V) : D.full.weight u v + E.shared.weight u v ≤ H₁.weight u v := le_rfl
  obtain ⟨σ₁, τ₁, hp₁, hd₁, htσ₁, htτ₁⟩ := hI.combine_pieces hs hIdom hdoms hpieces₁
  have htI : σI.total = 2 * D.full.total := D.full.toSkew_total γ σs.skew_nonneg
  have ht₁ : σ₁.total = 2 * D.full.total + σs.total := by rwa [htI] at htσ₁
  have ht₁' : τ₁.total = τs.total := by
    simpa only [SkewMatching.total, SkewMatching.zero, Finset.sum_const_zero, zero_add] using htτ₁
  have hcap₂ (u : V) : H₁.load u + Q.load u ≤ 1 := by
    have hh : H₁.load u + Q.load u ≤ μ.load u := by
      rw [FractionalMatching.load, FractionalMatching.load, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun v _ ↦ D.sharedUsed_add_private_piece_le E Q hQ u v
    exact hh.trans (μ.load_le_one u)
  let H₂ := H₁.add Q hcap₂
  have hH₂ (u v : V) : H₂.weight u v ≤ μ.weight u v := D.sharedUsed_add_private_piece_le E Q hQ u v
  have hpieces₂ (u v : V) : H₁.weight u v + Q.weight u v ≤ H₂.weight u v := le_rfl
  have hsatQ : Q.total ≤ (w.truncate H₁.load H₁.load_nonneg).saturation Q.load d :=
    (D.private_piece_saturation_eq E Q hQ).ge
  obtain ⟨σ₂, τ₂, hp₂, hd₂, htσ₂, htτ₂⟩ := hp₁.extend_left_piece hd₁ hpieces₂
    Q.total Q.total_nonneg hsatQ
  let R := μ.sub H₂ hH₂
  let r := (w.truncate H₂.load H₂.load_nonneg).saturation R.load c
  have hr : 0 ≤ r := (w.truncate H₂.load H₂.load_nonneg).saturation_nonneg R.load R.load_nonneg c
  have hpieces₃ (u v : V) : H₂.weight u v + R.weight u v ≤ μ.weight u v := by
    change H₂.weight u v + (μ.weight u v - H₂.weight u v) ≤ _
    linarith
  obtain ⟨σ, τ, hp, hd, htσ, htτ⟩ := hp₂.extend_right_piece hd₂ hpieces₃ r hr le_rfl
  have htotal : σ.total = 2 * D.full.total + σs.total + Q.total := by
    rw [htσ, htσ₂, ht₁]
  refine ⟨σ, τ, hp, hd, htotal, ?_⟩
  have hsat₁ := D.full.saturation_add E.shared
    (fun u ↦ (add_le_add le_rfl (E.shared.load_le_of_weight_le D.cross E.shared_le u)).trans
      ((D.combined_load_le u).trans (μ.load_le_one u))) w c
  change w.saturation D.full.load c +
    (w.truncate D.full.load D.full.load_nonneg).saturation E.shared.load c =
      w.saturation H₁.load c at hsat₁
  have hsat₂ := H₁.saturation_add Q hcap₂ w c
  change w.saturation H₁.load c + (w.truncate H₁.load H₁.load_nonneg).saturation Q.load c =
    w.saturation H₂.load c at hsat₂
  have hsat₃ := μ.saturation_sub H₂ hH₂ w c
  change w.saturation H₂.load c + r = w.saturation μ.load c at hsat₃
  have hIbound := D.full.saturation_le_twice_total w c
  have hQbound := D.private_piece_saturation_other_le E Q hQ
  change (w.truncate H₁.load H₁.load_nonneg).saturation Q.load c ≤ Q.total at hQbound
  rw [htτ₂, ht₁'] at htτ
  linarith

end SaturationDecomposition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SaturationDecomposition.assemble_private_piece
