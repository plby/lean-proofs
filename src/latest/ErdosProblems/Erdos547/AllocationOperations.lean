import ErdosProblems.Erdos547.AllocationComparison
import ErdosProblems.Erdos547.WeightedHost

/-!
# Compatible sums and anchored allocations

All sums below include an explicit proof that the combined vertex loads
respect capacity. The truncation lemma proves the anchor constraints for
such sums, including the joint constraint at the two anchors.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

namespace FractionalMatching

def zero (G : SimpleGraph V) : FractionalMatching G where
  weight _ _ := 0
  symmetric _ _ := rfl
  nonnegative _ _ := le_rfl
  supported _ _ _ := rfl
  capacity _ := by simp

def add (μ ν : FractionalMatching G) (h : ∀ u, μ.load u + ν.load u ≤ 1) :
    FractionalMatching G where
  weight u v := μ.weight u v + ν.weight u v
  symmetric u v := by rw [μ.symmetric u v, ν.symmetric u v]
  nonnegative u v := add_nonneg (μ.nonnegative u v) (ν.nonnegative u v)
  supported u v huv := by rw [μ.supported u v huv, ν.supported u v huv, add_zero]
  capacity u := by simpa only [load, Finset.sum_add_distrib] using h u

@[simp] theorem add_load (μ ν : FractionalMatching G) (h : ∀ u, μ.load u + ν.load u ≤ 1)
    (u : V) : (μ.add ν h).load u = μ.load u + ν.load u := by
  simp only [load, add, Finset.sum_add_distrib]

@[simp] theorem add_total (μ ν : FractionalMatching G) (h : ∀ u, μ.load u + ν.load u ≤ 1) :
    (μ.add ν h).total = μ.total + ν.total := by
  simp only [total, add, Finset.sum_add_distrib, add_div]

def sub (μ ν : FractionalMatching G) (h : ∀ u v, ν.weight u v ≤ μ.weight u v) :
    FractionalMatching G where
  weight u v := μ.weight u v - ν.weight u v
  symmetric u v := by rw [μ.symmetric u v, ν.symmetric u v]
  nonnegative u v := sub_nonneg.mpr (h u v)
  supported u v huv := by rw [μ.supported u v huv, ν.supported u v huv, sub_self]
  capacity u := by
    rw [Finset.sum_sub_distrib]
    exact (sub_le_self _ (ν.load_nonneg u)).trans (μ.capacity u)

@[simp] theorem sub_load (μ ν : FractionalMatching G)
    (h : ∀ u v, ν.weight u v ≤ μ.weight u v) (u : V) :
    (μ.sub ν h).load u = μ.load u - ν.load u := by
  simp only [load, sub, Finset.sum_sub_distrib]

@[simp] theorem sub_total (μ ν : FractionalMatching G)
    (h : ∀ u v, ν.weight u v ≤ μ.weight u v) :
    (μ.sub ν h).total = μ.total - ν.total := by
  simp only [total, sub, Finset.sum_sub_distrib, sub_div]

theorem load_le_of_weight_le (μ ν : FractionalMatching G)
    (h : ∀ u v, μ.weight u v ≤ ν.weight u v) (u : V) : μ.load u ≤ ν.load u :=
  Finset.sum_le_sum fun v _ ↦ h u v

end FractionalMatching

namespace SkewMatching

def zero (G : SimpleGraph V) (γ : ℝ) (hγ : 0 ≤ γ) : SkewMatching G γ where
  skew_nonneg := hγ
  weight _ _ := 0
  nonnegative _ _ := le_rfl
  supported _ _ _ := rfl
  capacity _ := by simp only [Finset.sum_const_zero, mul_zero, add_zero]; linarith

def add (σ τ : SkewMatching G γ) (h : ∀ u, σ.load u + τ.load u ≤ 1) :
    SkewMatching G γ where
  skew_nonneg := σ.skew_nonneg
  weight u v := σ.weight u v + τ.weight u v
  nonnegative u v := add_nonneg (σ.nonnegative u v) (τ.nonnegative u v)
  supported u v huv := by rw [σ.supported u v huv, τ.supported u v huv, add_zero]
  capacity u := by
    have hu := (div_le_one σ.denominator_pos).mp (show
        ((∑ v, σ.weight u v) + γ * (∑ v, σ.weight v u) +
          ((∑ v, τ.weight u v) + γ * (∑ v, τ.weight v u))) / (1 + γ) ≤ 1 from by
      simpa only [load, outLoad, inLoad, add_div, add_assoc] using h u)
    simpa only [Finset.sum_add_distrib, mul_add, add_assoc, add_left_comm, add_comm] using hu

@[simp] theorem add_outLoad (σ τ : SkewMatching G γ)
    (h : ∀ u, σ.load u + τ.load u ≤ 1) (u : V) :
    (σ.add τ h).outLoad u = σ.outLoad u + τ.outLoad u := by
  simp only [outLoad, add, Finset.sum_add_distrib, add_div]

@[simp] theorem add_inLoad (σ τ : SkewMatching G γ)
    (h : ∀ u, σ.load u + τ.load u ≤ 1) (u : V) :
    (σ.add τ h).inLoad u = σ.inLoad u + τ.inLoad u := by
  simp only [inLoad, add, Finset.sum_add_distrib, mul_add, add_div]

@[simp] theorem add_load (σ τ : SkewMatching G γ)
    (h : ∀ u, σ.load u + τ.load u ≤ 1) (u : V) :
    (σ.add τ h).load u = σ.load u + τ.load u := by
  simp only [load, add_outLoad, add_inLoad]
  ring

@[simp] theorem add_total (σ τ : SkewMatching G γ)
    (h : ∀ u, σ.load u + τ.load u ≤ 1) : (σ.add τ h).total = σ.total + τ.total := by
  simp only [total, add, Finset.sum_add_distrib]

@[simp] theorem add_endpointWeight (σ τ : SkewMatching G γ)
    (h : ∀ u, σ.load u + τ.load u ≤ 1) (u v : V) :
    (σ.add τ h).endpointWeight u v = σ.endpointWeight u v + τ.endpointWeight u v := by
  simp only [endpointWeight, add]
  ring

theorem outLoad_le_load (σ : SkewMatching G γ) (u : V) : σ.outLoad u ≤ σ.load u :=
  le_add_of_nonneg_right (σ.inLoad_nonneg u)

def Fits (σ : SkewMatching G γ) (w : EdgeWeights G) (c : V) : Prop :=
  ∀ u, σ.outLoad u ≤ w.weight c u

theorem add_dominated {σ τ : SkewMatching G γ} {μ ν : FractionalMatching G}
    (hσ : σ.DominatedByFractional μ) (hτ : τ.DominatedByFractional ν)
    (h : ∀ u, μ.load u + ν.load u ≤ 1)
    (hs : ∀ u, σ.load u + τ.load u ≤ 1) :
    (σ.add τ hs).DominatedByFractional (μ.add ν h) := by
  intro u v
  rw [add_endpointWeight]
  exact add_le_add (hσ u v) (hτ u v)

end SkewMatching

theorem add_le_of_le_truncated {a b c l : ℝ}
    (ha : a ≤ c) (hal : a ≤ l) (hb : b ≤ max 0 (c - l)) : a + b ≤ c := by
  by_cases hcl : c ≤ l
  · rw [max_eq_left (sub_nonpos.mpr hcl)] at hb
    linarith
  · rw [max_eq_right (by linarith)] at hb
    linarith

namespace SkewMatching

theorem fits_add_truncated {σ τ : SkewMatching G γ} {μ : FractionalMatching G}
    {w : EdgeWeights G} {c : V} (hσ : σ.Fits w c)
    (hτ : τ.Fits (w.truncate μ.load μ.load_nonneg) c)
    (hμ : σ.DominatedByFractional μ) (h : ∀ u, σ.load u + τ.load u ≤ 1) :
    (σ.add τ h).Fits w c := by
  intro u
  rw [add_outLoad]
  exact add_le_of_le_truncated (hσ u) ((σ.outLoad_le_load u).trans (hμ.load_le u)) (hτ u)

end SkewMatching

/-- The constraints of an edge-anchored pair. The joint anchor bound is
stated at every vertex; outside a common neighbourhood the separate bounds
already imply it, since nonedges have weight zero. -/
structure AnchoredPair (σ : SkewMatching G γ) (τ : SkewMatching G δ)
    (w : EdgeWeights G) (c d : V) : Prop where
  adjacent : G.Adj c d
  capacity : ∀ u, σ.load u + τ.load u ≤ 1
  fits_left : σ.Fits w c
  fits_right : τ.Fits w d
  joint : ∀ u, σ.outLoad u + τ.outLoad u ≤ max (w.weight c u) (w.weight d u)

def PairDominated (σ : SkewMatching G γ) (τ : SkewMatching G δ)
    (μ : FractionalMatching G) : Prop :=
  ∀ u v, σ.endpointWeight u v + τ.endpointWeight u v ≤ μ.weight u v

theorem PairDominated.load_le {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {μ : FractionalMatching G} (h : PairDominated σ τ μ) (u : V) :
    σ.load u + τ.load u ≤ μ.load u := by
  rw [← σ.sum_endpointWeight, ← τ.sum_endpointWeight, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun v _ ↦ h u v

theorem PairDominated.left {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {μ : FractionalMatching G} (h : PairDominated σ τ μ) : σ.DominatedByFractional μ :=
  fun u v ↦ (le_add_of_nonneg_right (τ.endpointWeight_nonneg u v)).trans (h u v)

theorem PairDominated.right {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {μ : FractionalMatching G} (h : PairDominated σ τ μ) : τ.DominatedByFractional μ :=
  fun u v ↦ (le_add_of_nonneg_left (σ.endpointWeight_nonneg u v)).trans (h u v)

theorem max_truncated (a b l : ℝ) :
    max (max 0 (a - l)) (max 0 (b - l)) = max 0 (max a b - l) := by
  by_cases hab : a ≤ b
  · rw [max_eq_right hab, max_eq_right (max_le_max_left _ (sub_le_sub_right hab _))]
  · have hba := le_of_not_ge hab
    rw [max_eq_left hba, max_eq_left (max_le_max_left _ (sub_le_sub_right hba _))]

/-- Adding pairs fitted to an initial weight and its truncation preserves
all anchor inequalities and the domination by the sum of the matchings. -/
theorem AnchoredPair.add_truncated
    {σ₁ σ₂ : SkewMatching G γ} {τ₁ τ₂ : SkewMatching G δ}
    {μ ν : FractionalMatching G} {w : EdgeWeights G} {c d : V}
    (h₁ : AnchoredPair σ₁ τ₁ w c d)
    (h₂ : AnchoredPair σ₂ τ₂ (w.truncate μ.load μ.load_nonneg) c d)
    (hμ : PairDominated σ₁ τ₁ μ) (hν : PairDominated σ₂ τ₂ ν)
    (h : ∀ u, μ.load u + ν.load u ≤ 1) :
    ∃ (hs : ∀ u, σ₁.load u + σ₂.load u ≤ 1)
      (ht : ∀ u, τ₁.load u + τ₂.load u ≤ 1),
      AnchoredPair (σ₁.add σ₂ hs) (τ₁.add τ₂ ht) w c d ∧
      PairDominated (σ₁.add σ₂ hs) (τ₁.add τ₂ ht) (μ.add ν h) := by
  have hs : ∀ u, σ₁.load u + σ₂.load u ≤ 1 := fun u ↦
    (add_le_add (hμ.left.load_le u) (hν.left.load_le u)).trans (h u)
  have ht : ∀ u, τ₁.load u + τ₂.load u ≤ 1 := fun u ↦
    (add_le_add (hμ.right.load_le u) (hν.right.load_le u)).trans (h u)
  refine ⟨hs, ht, ⟨h₁.adjacent, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u
    simp only [SkewMatching.add_load]
    have := add_le_add (hμ.load_le u) (hν.load_le u)
    linarith [h u]
  · exact SkewMatching.fits_add_truncated h₁.fits_left h₂.fits_left hμ.left hs
  · exact SkewMatching.fits_add_truncated h₁.fits_right h₂.fits_right hμ.right ht
  · intro u
    simp only [SkewMatching.add_outLoad]
    have hload : σ₁.outLoad u + τ₁.outLoad u ≤ μ.load u :=
      (add_le_add (σ₁.outLoad_le_load u) (τ₁.outLoad_le_load u)).trans (hμ.load_le u)
    have htr := h₂.joint u
    change σ₂.outLoad u + τ₂.outLoad u ≤
      max (max 0 (w.weight c u - μ.load u)) (max 0 (w.weight d u - μ.load u)) at htr
    rw [max_truncated] at htr
    have := add_le_of_le_truncated (h₁.joint u) hload htr
    linarith
  · intro u v
    simp only [SkewMatching.add_endpointWeight]
    change _ ≤ μ.weight u v + ν.weight u v
    linarith [hμ u v, hν u v]

end Erdos547.DPRS

#print axioms Erdos547.DPRS.AnchoredPair.add_truncated
