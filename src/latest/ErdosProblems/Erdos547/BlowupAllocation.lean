import ErdosProblems.Erdos547.StructuralCover
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Averaging anchored allocations from a uniform graph blow-up
-/

noncomputable section

namespace Erdos547.DPRS.Blowup

open Finset SimpleGraph
open scoped BigOperators

variable {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V} {γ δ : ℝ}

def graph (G : SimpleGraph V) (I : Type*) : SimpleGraph (V × I) := G.comap Prod.fst

def weights (w : EdgeWeights G) : EdgeWeights (graph G I) where
  weight u v := w.weight u.1 v.1
  nonnegative u v := w.nonnegative u.1 v.1
  at_most_one u v := w.at_most_one u.1 v.1
  supported u v h := w.supported u.1 v.1 h

theorem degree_weights (w : EdgeWeights G) (u : V × I) :
    (weights w).degree u = (Fintype.card I : ℝ) * w.degree u.1 := by
  simp only [EdgeWeights.degree, weights, Fintype.sum_prod_type, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ, ← Finset.mul_sum]

def meanWeight (f : (V × I) → (V × I) → ℝ) (u v : V) : ℝ :=
  (∑ i, ∑ j, f (u, i) (v, j)) / Fintype.card I

theorem meanWeight_row (f : (V × I) → (V × I) → ℝ) (u : V) :
    (∑ v, meanWeight f u v) = (∑ i, ∑ x, f (u, i) x) / Fintype.card I := by
  simp only [meanWeight]
  rw [← Finset.sum_div]
  congr 1
  simp only [Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem meanWeight_col (f : (V × I) → (V × I) → ℝ) (u : V) :
    (∑ v, meanWeight f v u) = (∑ i, ∑ x, f x (u, i)) / Fintype.card I := by
  simp only [meanWeight]
  rw [← Finset.sum_div]
  congr 1
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ v, ∑ j, ∑ i, f (v, i) (u, j) :=
      Finset.sum_congr rfl fun v _ ↦ Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem mean_le_const (f : I → ℝ) (b : ℝ) (hI : 0 < Fintype.card I)
    (hf : ∀ i, f i ≤ b) : (∑ i, f i) / Fintype.card I ≤ b := by
  have hIp : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hI
  apply (div_le_iff₀ hIp).mpr
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hf i)
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_comm] using hh

def collapse (σ : SkewMatching (graph G I) γ) (hI : 0 < Fintype.card I) :
    SkewMatching G γ where
  skew_nonneg := σ.skew_nonneg
  weight := meanWeight σ.weight
  nonnegative u v := div_nonneg (Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦ σ.nonnegative (u, i) (v, j)) (Nat.cast_nonneg _)
  supported u v huv := by
    dsimp [meanWeight]
    have hz (i j : I) : σ.weight (u, i) (v, j) = 0 := σ.supported _ _ huv
    simp only [hz, Finset.sum_const_zero, zero_div]
  capacity u := by
    rw [meanWeight_row, meanWeight_col]
    have he : (∑ i, ∑ x, σ.weight (u, i) x) / (Fintype.card I : ℝ) +
        γ * ((∑ i, ∑ x, σ.weight x (u, i)) / Fintype.card I) =
        (∑ i, ((∑ x, σ.weight (u, i) x) + γ * (∑ x, σ.weight x (u, i)))) /
          Fintype.card I := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    rw [he]
    exact mean_le_const _ _ hI (fun i ↦ σ.capacity (u, i))

theorem collapse_outLoad (σ : SkewMatching (graph G I) γ) (hI : 0 < Fintype.card I)
    (u : V) : (collapse σ hI).outLoad u = (∑ i, σ.outLoad (u, i)) / Fintype.card I := by
  change (∑ v, meanWeight σ.weight u v) / (1 + γ) = _
  rw [meanWeight_row]
  simp only [SkewMatching.outLoad, ← Finset.sum_div]
  ring

theorem collapse_inLoad (σ : SkewMatching (graph G I) γ) (hI : 0 < Fintype.card I)
    (u : V) : (collapse σ hI).inLoad u = (∑ i, σ.inLoad (u, i)) / Fintype.card I := by
  change γ * (∑ v, meanWeight σ.weight v u) / (1 + γ) = _
  rw [meanWeight_col]
  simp only [SkewMatching.inLoad, ← Finset.sum_div, ← Finset.mul_sum]
  ring

theorem collapse_load (σ : SkewMatching (graph G I) γ) (hI : 0 < Fintype.card I)
    (u : V) : (collapse σ hI).load u = (∑ i, σ.load (u, i)) / Fintype.card I := by
  simp only [SkewMatching.load, collapse_outLoad, collapse_inLoad,
    Finset.sum_add_distrib, add_div]

theorem collapse_total (σ : SkewMatching (graph G I) γ) (hI : 0 < Fintype.card I) :
    (collapse σ hI).total = σ.total / Fintype.card I := by
  rw [← (collapse σ hI).sum_load]
  simp only [collapse_load, ← Finset.sum_div]
  rw [← Fintype.sum_prod_type, σ.sum_load]

theorem collapse_anchoredPair {σ : SkewMatching (graph G I) γ}
    {τ : SkewMatching (graph G I) δ} {w : EdgeWeights G} {c d : V × I}
    (hp : AnchoredPair σ τ (weights w) c d) (hI : 0 < Fintype.card I) :
    AnchoredPair (collapse σ hI) (collapse τ hI) w c.1 d.1 := by
  refine ⟨hp.adjacent, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [collapse_load, collapse_load, ← add_div, ← Finset.sum_add_distrib]
    exact mean_le_const _ _ hI (fun i ↦ hp.capacity (u, i))
  · intro u
    rw [collapse_outLoad]
    exact mean_le_const _ _ hI (fun i ↦ hp.fits_left (u, i))
  · intro u
    rw [collapse_outLoad]
    exact mean_le_const _ _ hI (fun i ↦ hp.fits_right (u, i))
  · intro u
    rw [collapse_outLoad, collapse_outLoad, ← add_div, ← Finset.sum_add_distrib]
    exact mean_le_const _ _ hI (fun i ↦ hp.joint (u, i))

theorem collapse_anchoredTotals {w : EdgeWeights G} {a b : ℝ}
    (h : HasAnchoredTotals (weights (I := I) w) γ δ a b) (hI : 0 < Fintype.card I) :
    HasAnchoredTotals w γ δ (a / Fintype.card I) (b / Fintype.card I) := by
  obtain ⟨c, d, σ, τ, hp, hσ, hτ⟩ := h
  refine ⟨c.1, d.1, collapse σ hI, collapse τ hI, collapse_anchoredPair hp hI, ?_, ?_⟩
  · rw [collapse_total, hσ]
  · rw [collapse_total, hτ]

end Erdos547.DPRS.Blowup

#print axioms Erdos547.DPRS.Blowup.collapse_anchoredTotals
