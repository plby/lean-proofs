import ErdosProblems.Erdos547.LocalAllocationChanges

/-!
# Conserving saturation and redirecting an oriented allocation
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem saturation_eq_of_load_transfer (w : EdgeWeights G) (c : V) (a b : V → ℝ)
    {x z : V} (hxz : x ≠ z) (t : ℝ) (ht : 0 ≤ t)
    (hb : ∀ u, b u = a u + (if u = x then t else 0) - (if u = z then t else 0))
    (hx : a x + t ≤ w.weight c x) (hz : a z ≤ w.weight c z) :
    w.saturation b c = w.saturation a c := by
  classical
  have hp (u : V) : min (w.weight c u) (b u) =
      min (w.weight c u) (a u) + (if u = x then t else 0) - (if u = z then t else 0) := by
    rw [hb]
    by_cases hux : u = x
    · subst u
      simp only [ite_true, if_neg hxz, sub_zero]
      rw [min_eq_right hx, min_eq_right (by linarith)]
    · by_cases huz : u = z
      · subst u
        simp only [if_neg (Ne.symm hxz), ite_true, add_zero]
        rw [min_eq_right hz, min_eq_right (by linarith)]
      · simp only [if_neg hux, if_neg huz, add_zero, sub_zero]
  simp only [EdgeWeights.saturation, hp, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

namespace SkewMatching

omit [DecidableEq V] in
theorem vertexLoadOf_sub (γ : ℝ) (f g : V → V → ℝ) (u : V) :
    vertexLoadOf γ (fun x y ↦ f x y - g x y) u = vertexLoadOf γ f u - vertexLoadOf γ g u := by
  simp only [vertexLoadOf, Finset.sum_sub_distrib]
  ring

theorem exists_redirect {γ : ℝ} (σ : SkewMatching G γ) {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : y ≠ z) (t : ℝ) (ht : 0 ≤ t)
    (he : (1 + γ) * t ≤ σ.weight x y) (hz : σ.load z + γ * t ≤ 1) :
    ∃ τ : SkewMatching G γ,
      (∀ u, τ.load u = σ.load u + (if u = z then γ * t else 0) -
        (if u = y then γ * t else 0)) ∧
      (∀ u, τ.outLoad u = σ.outLoad u) ∧
      ∀ u v, τ.weight u v = σ.weight u v + arcIncrement x z ((1 + γ) * t) u v -
        arcIncrement x y ((1 + γ) * t) u v := by
  classical
  let f := fun u v ↦ σ.weight u v + arcIncrement x z ((1 + γ) * t) u v -
    arcIncrement x y ((1 + γ) * t) u v
  have hval (u : V) : vertexLoadOf γ f u = σ.load u +
      (if u = z then γ * t else 0) - (if u = y then γ * t else 0) := by
    rw [show f = _ from rfl, vertexLoadOf_sub, vertexLoadOf_add,
      vertexLoadOf_weight, vertexLoadOf_normalized_arc σ.skew_nonneg,
      vertexLoadOf_normalized_arc σ.skew_nonneg]
    ring
  have hgt : 0 ≤ γ * t := mul_nonneg σ.skew_nonneg ht
  have hsz : ∀ u v, 0 ≤ f u v := by
    intro u v
    have hi := arcIncrement_nonneg x z (mul_nonneg σ.denominator_pos.le ht) u v
    have hd : arcIncrement x y ((1 + γ) * t) u v ≤ σ.weight u v := by
      rw [arcIncrement]
      split_ifs with huv
      · rcases huv with ⟨rfl, rfl⟩
        exact he
      · exact σ.nonnegative u v
    dsimp [f]
    linarith
  have hs : ∀ u v, ¬ G.Adj u v → f u v = 0 := by
    intro u v huv
    dsimp [f]
    rw [σ.supported u v huv, arcIncrement_supported hxz _ huv,
      arcIncrement_supported hxy _ huv]
    ring
  have hc (u : V) : vertexLoadOf γ f u ≤ 1 := by
    rw [hval]
    by_cases huz : u = z
    · subst u
      simpa only [ite_true, if_neg (Ne.symm hyz), sub_zero] using hz
    · rw [if_neg huz, add_zero]
      split_ifs <;> linarith [σ.load_le_one u]
  let τ := ofVertexLoad σ.skew_nonneg f hsz hs hc
  refine ⟨τ, hval, ?_, fun _ _ ↦ rfl⟩
  intro u
  change (∑ v, f u v) / (1 + γ) = _
  simp only [f, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_arcIncrement]
  congr 1
  ring

end SkewMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.saturation_eq_of_load_transfer
#print axioms Erdos547.DPRS.SkewMatching.exists_redirect
