import ErdosProblems.Erdos547.CrossAnchorSplit

/-!
# Saturation of a subpiece private to the first anchor
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem max_zero_sub_twice (a b c : ℝ) (hc : 0 ≤ c) :
    max 0 (max 0 (a - b) - c) = max 0 (a - (b + c)) := by
  by_cases hab : a ≤ b
  · rw [max_eq_left (sub_nonpos.mpr hab), max_eq_left (by linarith), max_eq_left (by linarith)]
  · rw [show max 0 (a - b) = a - b from max_eq_right (by linarith)]
    congr 1
    ring

namespace CrossAnchorSplit

variable {J : FractionalMatching G} {U : Finset V} {w : EdgeWeights G} {c : V}

theorem private_piece_saturation_le (E : CrossAnchorSplit J U w c) (Q : FractionalMatching G)
    (hQ : ∀ u v, Q.weight u v ≤ E.privatePart.weight u v) :
    (w.truncate E.shared.load E.shared.load_nonneg).saturation Q.load c ≤ Q.total := by
  classical
  let w' := w.truncate E.shared.load E.shared.load_nonneg
  have hcross := (E.private_between.mono hQ).crosses (disjoint_compl_right)
  have hout (u : V) (hu : u ∉ U) : min (w'.weight c u) (Q.load u) = 0 := by
    by_cases hzero : Q.load u = 0
    · rw [hzero, min_eq_right (w'.nonnegative c u)]
    · have hp : 0 < Q.load u := lt_of_le_of_ne (Q.load_nonneg u) (Ne.symm hzero)
      have hex : ∃ v, 0 < Q.weight u v := by
        by_contra hn
        push Not at hn
        have hh : Q.load u ≤ 0 := Finset.sum_nonpos fun v _ ↦ hn v
        linarith
      obtain ⟨v, hv⟩ := hex
      have hw : w'.weight c u = 0 := E.private_truncate_zero (Finset.mem_compl.mpr hu)
        (hv.trans_le (hQ u v))
      rw [hw, min_eq_left (Q.load_nonneg u)]
  calc
    _ = ∑ u ∈ U, min (w'.weight c u) (Q.load u) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      exact fun u _ hu ↦ hout u hu
    _ ≤ ∑ u ∈ U, Q.load u := Finset.sum_le_sum fun _ _ ↦ min_le_right _ _
    _ = _ := hcross.sum_load_side

end CrossAnchorSplit

namespace SaturationDecomposition

variable {μ : FractionalMatching G} {w : EdgeWeights G} {c d : V}

def sharedUsed (D : SaturationDecomposition μ w d)
    (E : CrossAnchorSplit D.cross D.active (w.truncate D.full.load D.full.load_nonneg) c) :
    FractionalMatching G := D.full.add E.shared (fun u ↦
      (add_le_add le_rfl (E.shared.load_le_of_weight_le D.cross E.shared_le u)).trans
        ((D.combined_load_le u).trans (μ.load_le_one u)))

theorem sharedUsed_load (D : SaturationDecomposition μ w d)
    (E : CrossAnchorSplit D.cross D.active (w.truncate D.full.load D.full.load_nonneg) c) (u : V) :
    (D.sharedUsed E).load u = D.full.load u + E.shared.load u :=
  FractionalMatching.add_load _ _ _ _

theorem sharedUsed_weight_le (D : SaturationDecomposition μ w d)
    (E : CrossAnchorSplit D.cross D.active
      (w.truncate D.full.load D.full.load_nonneg) c) (u v : V) :
    (D.sharedUsed E).weight u v ≤ μ.weight u v :=
  (add_le_add le_rfl (E.shared_le u v)).trans (D.combined_le u v)

theorem sharedUsed_add_private_piece_le (D : SaturationDecomposition μ w d)
    (E : CrossAnchorSplit D.cross D.active (w.truncate D.full.load D.full.load_nonneg) c)
    (Q : FractionalMatching G) (hQ : ∀ u v, Q.weight u v ≤ E.privatePart.weight u v) (u v : V) :
    (D.sharedUsed E).weight u v + Q.weight u v ≤ μ.weight u v := by
  have he := E.split_eq u v
  have hb := D.combined_le u v
  change D.full.weight u v + E.shared.weight u v + Q.weight u v ≤ _
  linarith [hQ u v]

theorem sharedUsed_truncate_weight (D : SaturationDecomposition μ w d)
    (E : CrossAnchorSplit D.cross D.active
      (w.truncate D.full.load D.full.load_nonneg) c) (x u : V) :
    (w.truncate (D.sharedUsed E).load (D.sharedUsed E).load_nonneg).weight x u =
      ((w.truncate D.full.load D.full.load_nonneg).truncate
        E.shared.load E.shared.load_nonneg).weight x u := by
  change max 0 (w.weight x u - (D.sharedUsed E).load u) =
    max 0 (max 0 (w.weight x u - D.full.load u) - E.shared.load u)
  rw [D.sharedUsed_load]
  exact (max_zero_sub_twice _ _ _ (E.shared.load_nonneg u)).symm

theorem private_piece_saturation_other_le (D : SaturationDecomposition μ w d)
    (E : CrossAnchorSplit D.cross D.active (w.truncate D.full.load D.full.load_nonneg) c)
    (Q : FractionalMatching G) (hQ : ∀ u v, Q.weight u v ≤ E.privatePart.weight u v) :
    (w.truncate (D.sharedUsed E).load (D.sharedUsed E).load_nonneg).saturation Q.load c ≤
      Q.total := by
  have he : (w.truncate (D.sharedUsed E).load (D.sharedUsed E).load_nonneg).saturation Q.load c =
      ((w.truncate D.full.load D.full.load_nonneg).truncate
        E.shared.load E.shared.load_nonneg).saturation Q.load c := by
    apply Finset.sum_congr rfl
    intro u _
    rw [D.sharedUsed_truncate_weight E c u]
  rw [he]
  exact E.private_piece_saturation_le Q hQ

theorem private_piece_saturation_eq (D : SaturationDecomposition μ w d)
    (E : CrossAnchorSplit D.cross D.active (w.truncate D.full.load D.full.load_nonneg) c)
    (Q : FractionalMatching G) (hQ : ∀ u v, Q.weight u v ≤ E.privatePart.weight u v) :
    (w.truncate (D.sharedUsed E).load (D.sharedUsed E).load_nonneg).saturation Q.load d =
      Q.total := by
  classical
  let w' := w.truncate (D.sharedUsed E).load (D.sharedUsed E).load_nonneg
  have hcross := (E.private_between.mono hQ).crosses (disjoint_compl_right)
  have hpoint (u : V) : min (w'.weight d u) (Q.load u) =
      if u ∈ D.active then Q.load u else 0 := by
    by_cases hu : u ∈ D.active
    · rw [if_pos hu]
      apply min_eq_right
      have hQload := Q.load_le_of_weight_le E.privatePart hQ u
      have hcrossload := E.load_eq u
      have hd := D.active_cross_fits hu
      change Q.load u ≤ max 0 (w.weight d u - (D.sharedUsed E).load u)
      apply le_trans _ (le_max_right _ _)
      rw [D.sharedUsed_load]
      linarith
    · rw [if_neg hu]
      have hz : w'.weight d u = 0 := by
        change max 0 (w.weight d u - (D.sharedUsed E).load u) = 0
        rw [D.sharedUsed_load, D.outside_full_load hu]
        apply max_eq_left
        linarith [E.shared.load_nonneg u]
      rw [hz, min_eq_left (Q.load_nonneg u)]
  change (∑ u, min (w'.weight d u) (Q.load u)) = _
  simp only [hpoint, Finset.sum_ite_mem_eq]
  exact hcross.sum_load_side

end SaturationDecomposition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SaturationDecomposition.private_piece_saturation_eq
#print axioms Erdos547.DPRS.SaturationDecomposition.private_piece_saturation_other_le
