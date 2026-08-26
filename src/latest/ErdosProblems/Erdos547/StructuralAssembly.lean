import ErdosProblems.Erdos547.StructuralEasySkew
import ErdosProblems.Erdos547.StructuralBalancedOptimal
import ErdosProblems.Erdos547.StructuralSmallOverlap
import ErdosProblems.Erdos547.StructuralAvoiding

/-!
# The weighted degree structure theorem

This assembles every structural case. The integer budgets in the final
statement allow the finite tail-set selection used in the flabellum case.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_anchored_totals_normalized (w : EdgeWeights G) (c : V)
    (a₁ a₂ b₁ : ℝ) (m : ℕ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁)
    (hm : 0 < (m : ℝ))
    (hlarge : a₁ + a₂ + b₁ + m ≤ w.degree c)
    (hdeg : ∀ v, (a₁ + a₂ + b₁ + m) / 2 ≤ w.degree v)
    (hnorm : a₂ + b₁ ≤ (a₁ + a₂ + b₁ + m) / 2) :
    HasAnchoredTotals w (a₂ / a₁) ((m : ℝ) / b₁) (a₁ + a₂) (b₁ + m) := by
  classical
  by_contra hn
  obtain ⟨D⟩ := exists_gallaiEdmonds_partition G
  have hγ : 0 ≤ a₂ / a₁ := (div_pos ha₂ ha₁).le
  have hδ : 0 ≤ (m : ℝ) / b₁ := (div_pos hm hb₁).le
  obtain ⟨_hc, μ, hμ, _hsat, d, hd, hcd, _hdef⟩ :=
    D.initial_obstruction w (a₂ / a₁) ((m : ℝ) / b₁) (a₁ + a₂) (b₁ + m)
      hγ hδ (add_pos ha₁ ha₂) (add_pos hb₁ hm)
      (by simpa only [add_assoc] using hdeg) (by simpa only [add_assoc] using hlarge) hn
  by_cases heasy : (a₁ + a₂ + b₁ + m) / 2 ≤ a₁ + b₁
  · exact hn (hμ.anchoredTotals_of_easy_skew hd hcd a₁ a₂ b₁ m ha₁ ha₂ hb₁ hm
      hlarge hdeg hnorm heasy)
  have hskew : b₁ < (m : ℝ) := by linarith
  have hsmall : max a₁ a₂ + b₁ ≤ (a₁ + a₂ + b₁ + m) / 2 := by
    have hh : max a₁ a₂ ≤ (a₁ + a₂ + b₁ + m) / 2 - b₁ :=
      max_le (by linarith) (by linarith)
    linarith
  obtain ⟨σ, ν, hpair, hopt⟩ := D.exists_optimal_gePair w c μ hμ ((m : ℝ) / b₁) hδ
  have h : D.IsOptimalGEPair w c μ σ ν := ⟨hpair, hopt⟩
  have hR : (D.reachableVertices w c μ).Nonempty := ⟨d, hd⟩
  by_cases hbigσ : b₁ + m ≤ σ.total
  · exact hn (hpair.anchoredTotals_of_skew_cover a₁ a₂ b₁ m hμ ha₁ ha₂.le hb₁
      hskew.le hR hbigσ hdeg hsmall)
  have hσ : σ.total ≤ b₁ + m := (lt_of_not_ge hbigσ).le
  by_cases hmixed : a₁ + a₂ + b₁ + m ≤ w.saturation (fun u ↦ σ.load u + ν.load u) c
  · exact hn (hpair.anchoredTotals_of_mixed_saturation a₁ a₂ b₁ m hμ ha₁ ha₂.le hb₁
      hskew.le hR hdeg hsmall hmixed)
  by_cases hbalanced : (m : ℝ) ≤ (a₁ + a₂ + b₁ + m) / 2
  · exact hn (h.anchoredTotals_of_balanced a₁ a₂ b₁ m hμ ha₁ ha₂ hb₁ hskew
      hR hlarge hdeg hsmall hbalanced)
  have hhalf : (a₁ + a₂ + b₁ + m) / 2 ≤ (m : ℝ) := (lt_of_not_ge hbalanced).le
  obtain ⟨e, hdef⟩ := w.exists_deficient_of_saturation_lt_degree
    (fun u ↦ σ.load u + ν.load u) c ((lt_of_not_ge hmixed).trans_le hlarge)
  have he : e ∈ D.reachableVertices w c μ := by
    by_contra he
    exact (not_lt_of_ge (hpair.outside_lower e he)) hdef
  by_cases hoverlap : ∀ y ∈ D.reachableVertices w c μ,
      b₁ ≤ w.degreeOn (Finset.univ.filter (G.Adj y)) e
  · by_cases hsize : (m : ℝ) ≤ ((D.reachableVertices w c μ ∪
        D.fullFlabellumExtra w c μ e b₁).card : ℝ)
    · exact hn (h.anchoredTotals_of_full_flabellum a₁ a₂ b₁ m ha₁ ha₂ hb₁ hμ he hdef
        hσ hhalf hlarge hdeg hoverlap hsize)
    · exact hn (h.anchoredTotals_of_avoiding (a₁ + a₂) b₁ m (a₂ / a₁)
        (add_pos ha₁ ha₂) hb₁ hskew hγ hμ he hdef hσ hlarge hdeg (lt_of_not_ge hsize))
  · push Not at hoverlap
    obtain ⟨y, hy, hoverlap⟩ := hoverlap
    exact hn (hμ.anchoredTotals_of_small_overlap he hy a₁ a₂ b₁ m ha₁ ha₂.le hb₁
      hskew.le hdeg hhalf hoverlap.le)

/-- One vertex of degree at least the total budget, and minimum degree at
least half that budget, supply an adjacent pair of compatible allocations. -/
theorem exists_anchored_totals_of_degree (w : EdgeWeights G) (c : V)
    (a₁ a₂ b₁ b₂ : ℕ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hlarge : (a₁ : ℝ) + a₂ + b₁ + b₂ ≤ w.degree c)
    (hdeg : ∀ v, ((a₁ : ℝ) + a₂ + b₁ + b₂) / 2 ≤ w.degree v) :
    HasAnchoredTotals w ((a₂ : ℝ) / a₁) ((b₂ : ℝ) / b₁)
      ((a₁ : ℝ) + a₂) ((b₁ : ℝ) + b₂) := by
  have ha₁' : 0 < (a₁ : ℝ) := by exact_mod_cast ha₁
  have ha₂' : 0 < (a₂ : ℝ) := by exact_mod_cast ha₂
  have hb₁' : 0 < (b₁ : ℝ) := by exact_mod_cast hb₁
  have hb₂' : 0 < (b₂ : ℝ) := by exact_mod_cast hb₂
  by_cases hnorm : (a₂ : ℝ) + b₁ ≤ ((a₁ : ℝ) + a₂ + b₁ + b₂) / 2
  · exact exists_anchored_totals_normalized w c a₁ a₂ b₁ b₂ ha₁' ha₂' hb₁' hb₂'
      hlarge hdeg hnorm
  · have hh := exists_anchored_totals_normalized w c b₁ b₂ a₁ a₂ hb₁' hb₂' ha₁' ha₂'
      (by linarith) (fun v ↦ by linarith [hdeg v]) (by linarith)
    exact hh.swap

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_anchored_totals_of_degree
