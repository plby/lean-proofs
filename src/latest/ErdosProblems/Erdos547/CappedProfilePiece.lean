import ErdosProblems.Erdos547.GECappedProfile
import ErdosProblems.Erdos547.ResidualNeighbourPiece
import ErdosProblems.Erdos547.ZeroSideSaturation
import ErdosProblems.Erdos547.FractionalSaturation

/-!
# A private fractional budget after capping a GE skew allocation
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {δ : ℝ}

theorem CappedProfile.exists_private_piece {σ : SkewMatching G δ}
    {ν : FractionalMatching G} {w : EdgeWeights G} {c d : V} {R S : Finset V}
    (K : CappedProfile σ ν w c d R S) (hσ : σ.RunsFrom S)
    (hN : ∀ u, G.Adj d u → u ∈ S)
    (hsep : ∀ u, G.Adj d u → σ.outLoad u = w.weight c u)
    (q : ℝ) (hq : 0 ≤ q)
    (hsize : q ≤ (w.truncate K.kept.load K.kept.load_nonneg).degree d) :
    ∃ P : FractionalMatching G, (∀ u v, P.weight u v ≤ ν.weight u v) ∧
      P.RunsBetween S Sᶜ ∧ P.total = q ∧
      (∀ u ∈ S, P.load u ≤ (w.truncate K.kept.load K.kept.load_nonneg).weight d u) ∧
      (w.truncate K.kept.load K.kept.load_nonneg).saturation P.load c ≤ P.total := by
  let w' := w.truncate K.kept.load K.kept.load_nonneg
  have hνzero (u : V) (hu : u ∈ S) (v : V) (hv : v ∈ S) : ν.weight u v = 0 :=
    le_antisymm ((K.fractional_le u v).trans_eq (K.separator_zero u hu v hv)) (ν.nonnegative u v)
  obtain ⟨J, hJ, hcross, hload, htotal⟩ := ν.exists_neighbour_piece S hνzero w' d hN
    K.residual_available
  obtain ⟨P, hP, htP⟩ := J.exists_submatching_total q hq (by rwa [htotal])
  have hfit (u : V) (hu : u ∈ S) : P.load u ≤ w'.weight d u :=
    (P.load_le_of_weight_le J hP u).trans_eq (hload u hu)
  refine ⟨P, fun u v ↦ (hP u v).trans (hJ u v), hcross.mono hP, htP, hfit, ?_⟩
  apply P.saturation_le_total_of_zero_side S ((hcross.mono hP).crosses disjoint_compl_right)
    w' c
  intro u hu
  by_cases hz : P.load u = 0
  · rw [hz, min_eq_right (w'.nonnegative c u)]
  have hp : 0 < P.load u := lt_of_le_of_ne (P.load_nonneg u) (Ne.symm hz)
  have hwpos : 0 < w.weight d u := (hp.trans_le (hfit u hu)).trans_le
    (w.truncate_weight_le K.kept.load K.kept.load_nonneg d u)
  have hdu : G.Adj d u := by
    by_contra hn
    rw [w.supported d u hn] at hwpos
    exact lt_irrefl 0 hwpos
  have hlt : σ.load u < w.weight d u := by
    by_contra hn
    have hh := hfit u hu
    change P.load u ≤ max 0 (w.weight d u - K.kept.load u) at hh
    rw [K.kept_load u hu, min_eq_left (le_of_not_gt hn), sub_self, max_self] at hh
    linarith
  have hkept : K.kept.load u = w.weight c u := by
    rw [K.kept_load u hu, min_eq_right hlt.le, hσ.load_eq_outLoad hu, hsep u hdu]
  have hwzero : w'.weight c u = 0 := by
    change max 0 (w.weight c u - K.kept.load u) = 0
    rw [hkept, sub_self, max_self]
  rw [hwzero, min_eq_left (P.load_nonneg u)]

end Erdos547.DPRS

#print axioms Erdos547.DPRS.CappedProfile.exists_private_piece
