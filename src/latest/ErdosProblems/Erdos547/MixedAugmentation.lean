import ErdosProblems.Erdos547.LocalAllocationChanges

/-!
# Increasing one load in a compatible mixed allocation

Two oriented arc increments balance a decrease on one fractional edge.
The formula also covers coincident terminal vertices without a separate
construction.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ : ℝ}

open scoped Classical in
theorem exists_mixed_augmentation (σ : SkewMatching G γ) (ν : FractionalMatching G)
    (hcap : ∀ u, σ.load u + ν.load u ≤ 1) {x y d : V}
    (hxy : G.Adj x y) (hxd : G.Adj x d) (b q : ℝ) (hb : 0 ≤ b) (hq : 0 ≤ q)
    (hbalance : γ * q = b + q) (he : b + q ≤ ν.weight x y)
    (hd : σ.load d + ν.load d + γ * b ≤ 1) :
    ∃ σ' : SkewMatching G γ, ∃ ν' : FractionalMatching G,
      (∀ u, σ'.load u + ν'.load u = σ.load u + ν.load u + if u = d then γ * b else 0) ∧
      (∀ u, σ'.outLoad u = σ.outLoad u + if u = x then b + q else 0) ∧
      (∀ u v, σ'.weight u v = σ.weight u v + arcIncrement x d ((1 + γ) * b) u v +
        arcIncrement x y ((1 + γ) * q) u v) ∧
      (∀ u v, ν'.weight u v = ν.weight u v - edgeIncrement x y (b + q) u v) := by
  classical
  let ν' := ν.decreaseEdge x y (b + q) (add_nonneg hb hq) he
  let f := fun u v ↦ σ.weight u v + arcIncrement x d ((1 + γ) * b) u v +
    arcIncrement x y ((1 + γ) * q) u v
  have hnonneg : ∀ u v, 0 ≤ f u v := by
    intro u v
    exact add_nonneg (add_nonneg (σ.nonnegative u v)
      (arcIncrement_nonneg x d (mul_nonneg σ.denominator_pos.le hb) u v))
      (arcIncrement_nonneg x y (mul_nonneg σ.denominator_pos.le hq) u v)
  have hsupp : ∀ u v, ¬ G.Adj u v → f u v = 0 := by
    intro u v huv
    dsimp [f]
    rw [σ.supported u v huv, arcIncrement_supported hxd _ huv,
      arcIncrement_supported hxy _ huv]
    ring
  have hload (u : V) : SkewMatching.vertexLoadOf γ f u + ν'.load u =
      σ.load u + ν.load u + if u = d then γ * b else 0 := by
    dsimp [f]
    rw [SkewMatching.vertexLoadOf_add, SkewMatching.vertexLoadOf_add,
      SkewMatching.vertexLoadOf_weight,
      SkewMatching.vertexLoadOf_normalized_arc σ.skew_nonneg,
      SkewMatching.vertexLoadOf_normalized_arc σ.skew_nonneg]
    change _ + (ν.decreaseEdge x y (b + q) (add_nonneg hb hq) he).load u = _
    rw [FractionalMatching.decreaseEdge_load ν x y hxy.ne]
    split_ifs <;> linarith
  have hnewcap (u : V) : SkewMatching.vertexLoadOf γ f u + ν'.load u ≤ 1 := by
    rw [hload]
    by_cases hud : u = d
    · simpa only [hud, ite_true] using hd
    · simpa only [if_neg hud, add_zero] using hcap u
  have hσcap : ∀ u, SkewMatching.vertexLoadOf γ f u ≤ 1 := fun u ↦
    (le_add_of_nonneg_right (ν'.load_nonneg u)).trans (hnewcap u)
  let σ' := SkewMatching.ofVertexLoad σ.skew_nonneg f hnonneg hsupp hσcap
  refine ⟨σ', ν', hload, ?_, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  intro u
  change (∑ v, f u v) / (1 + γ) = _
  simp only [f, Finset.sum_add_distrib, sum_arcIncrement]
  by_cases hux : u = x
  · simp only [if_pos hux]
    change ((∑ v, σ.weight u v) + (1 + γ) * b + (1 + γ) * q) / (1 + γ) =
      (∑ v, σ.weight u v) / (1 + γ) + (b + q)
    field_simp [σ.denominator_pos.ne']
    ring
  · simp only [if_neg hux, add_zero]
    rfl

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_mixed_augmentation
