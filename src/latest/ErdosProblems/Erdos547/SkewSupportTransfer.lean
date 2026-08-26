import ErdosProblems.Erdos547.SkewBipartiteSupport
import ErdosProblems.Erdos547.BipartiteFractional

/-!
# Support consequences of fractional domination
-/

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ : ℝ}

namespace SkewMatching

theorem DominatedByFractional.weight_eq_zero {σ : SkewMatching G γ}
    {P : FractionalMatching G} (h : σ.DominatedByFractional P) {u v : V}
    (hz : P.weight u v = 0) : σ.weight u v = 0 := by
  have hh := (div_le_iff₀ σ.denominator_pos).mp (h u v)
  rw [hz, zero_mul] at hh
  exact le_antisymm (by linarith [mul_nonneg σ.skew_nonneg (σ.nonnegative v u)])
    (σ.nonnegative u v)

theorem outLoad_pos_of_weight_pos (σ : SkewMatching G γ) {u v : V}
    (h : 0 < σ.weight u v) : 0 < σ.outLoad u := by
  apply div_pos _ σ.denominator_pos
  exact h.trans_le (Finset.single_le_sum (fun x _ ↦ σ.nonnegative u x) (Finset.mem_univ v))

theorem DominatedByFractional.runsFrom_of_crosses {σ : SkewMatching G γ}
    {P : FractionalMatching G} (h : σ.DominatedByFractional P) (U : Finset V)
    (hcross : P.Crosses U) (hout : ∀ u ∉ U, σ.outLoad u = 0) : σ.RunsFrom U := by
  intro u v hp
  have hu : u ∈ U := by
    by_contra hn
    have hh := σ.outLoad_pos_of_weight_pos hp
    rw [hout u hn] at hh
    exact lt_irrefl 0 hh
  have hP : 0 < P.weight u v := by
    by_contra hn
    rw [h.weight_eq_zero (le_antisymm (le_of_not_gt hn) (P.nonnegative u v))] at hp
    exact lt_irrefl 0 hp
  exact ⟨hu, (hcross u v hP).mp hu⟩

theorem RunsFrom.add {σ τ : SkewMatching G γ} {U : Finset V}
    (hσ : σ.RunsFrom U) (hτ : τ.RunsFrom U) (hc : ∀ u, σ.load u + τ.load u ≤ 1) :
    (σ.add τ hc).RunsFrom U := by
  intro u v hp
  by_contra hn
  change 0 < σ.weight u v + τ.weight u v at hp
  rw [hσ.weight_eq_zero hn, hτ.weight_eq_zero hn, add_zero] at hp
  exact lt_irrefl 0 hp

end SkewMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SkewMatching.DominatedByFractional.runsFrom_of_crosses
