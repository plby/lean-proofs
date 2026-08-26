import ErdosProblems.Erdos547.DisjointFilling
import ErdosProblems.Erdos547.FractionalSaturation

/-!
# The full-piece case of the two-anchor matching lemma
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_pair_of_full_piece (μ ν : FractionalMatching G)
    (hν : ∀ u v, ν.weight u v ≤ μ.weight u v) (w : EdgeWeights G) {c d : V}
    (hcd : G.Adj c d) (hfit : ∀ u, ν.load u ≤ w.weight d u)
    (γ δ : ℝ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsat : a + b ≤ w.saturation μ.load c) (hsize : a ≤ 2 * ν.total) :
    ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ,
      AnchoredPair σ τ w d c ∧ PairDominated σ τ μ ∧ σ.total = a ∧ τ.total = b := by
  obtain ⟨ν', hν', htotal⟩ := ν.exists_submatching_total (a / 2) (by linarith) (by linarith)
  have hν'μ (u v : V) : ν'.weight u v ≤ μ.weight u v := (hν' u v).trans (hν u v)
  have hfit' (u : V) : ν'.load u ≤ w.weight d u :=
    (ν'.load_le_of_weight_le ν hν' u).trans (hfit u)
  have hd : w.saturation ν'.load d = a := by
    rw [ν'.saturation_eq_twice_total w d hfit', htotal]
    ring
  let R := μ.sub ν' hν'μ
  have hrc : b ≤ (w.truncate ν'.load ν'.load_nonneg).saturation R.load c := by
    have hid := μ.saturation_sub ν' hν'μ w c
    have hbound := ν'.saturation_le_twice_total w c
    rw [htotal] at hbound
    change w.saturation ν'.load c +
      (w.truncate ν'.load ν'.load_nonneg).saturation R.load c = _ at hid
    linarith
  have hpieces (u v : V) : ν'.weight u v + R.weight u v ≤ μ.weight u v := by
    change ν'.weight u v + (μ.weight u v - ν'.weight u v) ≤ _
    linarith
  exact exists_filling_disjoint ν' R μ hpieces w hcd.symm γ δ hγ hδ a b ha hb hd.ge hrc

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_pair_of_full_piece
