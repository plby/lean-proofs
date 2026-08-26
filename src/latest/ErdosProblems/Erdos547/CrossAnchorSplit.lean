import ErdosProblems.Erdos547.CappingLoss
import ErdosProblems.Erdos547.SaturationRemainder

/-!
# Splitting the cross piece according to a second anchor
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

structure CrossAnchorSplit (J : FractionalMatching G) (U : Finset V)
    (w : EdgeWeights G) (c : V) where
  shared : FractionalMatching G
  privatePart : FractionalMatching G
  shared_le : ∀ u v, shared.weight u v ≤ J.weight u v
  split_eq : ∀ u v, J.weight u v = shared.weight u v + privatePart.weight u v
  shared_between : shared.RunsBetween U Uᶜ
  private_between : privatePart.RunsBetween U Uᶜ
  shared_load : ∀ u ∈ Uᶜ, shared.load u = min (w.weight c u) (J.load u)
  saturation_loss : w.saturation J.load c ≤ w.saturation shared.load c + privatePart.total
  private_saturates : ∀ u ∈ Uᶜ, ∀ v, 0 < privatePart.weight u v → shared.load u = w.weight c u

theorem exists_cross_anchor_split (J : FractionalMatching G) (U : Finset V)
    (hU : J.Crosses U) (w : EdgeWeights G) (c : V) : Nonempty (CrossAnchorSplit J U w c) := by
  let hzero := fun u (hu : u ∈ Uᶜ) v (hv : v ∈ Uᶜ) ↦ hU.swap.weight_zero_same hu hv
  let S := J.capIndependent Uᶜ hzero (w.weight c) (w.nonnegative c)
  have hS (u v : V) : S.weight u v ≤ J.weight u v :=
    J.capIndependent_weight_le Uᶜ hzero (w.weight c) (w.nonnegative c) u v
  let P := J.sub S hS
  have hP (u v : V) : P.weight u v ≤ J.weight u v := sub_le_self _ (S.nonnegative u v)
  refine ⟨⟨S, P, hS, ?_, (hU.mono hS).runsBetween, (hU.mono hP).runsBetween, ?_, ?_, ?_⟩⟩
  · intro u v
    change J.weight u v = S.weight u v + (J.weight u v - S.weight u v)
    ring
  · intro u hu
    exact J.capIndependent_load Uᶜ hzero (w.weight c) (w.nonnegative c) hu
  · exact J.capIndependent_saturation_loss Uᶜ hU.swap w c
  · intro u hu v hp
    exact J.capIndependent_residual_saturated Uᶜ hzero (w.weight c) (w.nonnegative c) hu hp

namespace CrossAnchorSplit

variable {J : FractionalMatching G} {U : Finset V} {w : EdgeWeights G} {c : V}

theorem load_eq (E : CrossAnchorSplit J U w c) (u : V) :
    J.load u = E.shared.load u + E.privatePart.load u := by
  change (∑ v, J.weight u v) = _
  simp_rw [E.split_eq]
  exact Finset.sum_add_distrib

theorem total_eq (E : CrossAnchorSplit J U w c) :
    J.total = E.shared.total + E.privatePart.total := by
  have hh := J.sum_load
  simp_rw [E.load_eq] at hh
  rw [Finset.sum_add_distrib, E.shared.sum_load, E.privatePart.sum_load] at hh
  linarith

theorem shared_fits_inactive (E : CrossAnchorSplit J U w c) {u : V} (hu : u ∈ Uᶜ) :
    E.shared.load u ≤ w.weight c u := by
  rw [E.shared_load u hu]
  exact min_le_left _ _

theorem private_truncate_zero (E : CrossAnchorSplit J U w c) {u v : V}
    (hu : u ∈ Uᶜ) (hp : 0 < E.privatePart.weight u v) :
    (w.truncate E.shared.load E.shared.load_nonneg).weight c u = 0 := by
  change max 0 (w.weight c u - E.shared.load u) = 0
  rw [E.private_saturates u hu v hp, sub_self, max_self]

end CrossAnchorSplit

namespace SaturationDecomposition

variable {μ : FractionalMatching G} {w : EdgeWeights G} {d : V}

theorem remainder_saturation_lower (D : SaturationDecomposition μ w d) (c : V)
    (E : CrossAnchorSplit D.cross D.active (w.truncate D.full.load D.full.load_nonneg) c)
    (hdeg : 2 * w.saturation μ.load d ≤ w.saturation μ.load c) :
    2 * D.full.total + E.privatePart.total ≤
      (w.truncate D.used.load D.used.load_nonneg).saturation D.remainder.load c := by
  have hrem := D.remainder_saturation_identity c
  have hsplit := D.full.saturation_add D.cross
    (fun u ↦ (D.combined_load_le u).trans (μ.load_le_one u)) w c
  change w.saturation D.full.load c +
    (w.truncate D.full.load D.full.load_nonneg).saturation D.cross.load c =
      w.saturation D.used.load c at hsplit
  have hfull := D.full.saturation_le_twice_total w c
  have hshared := E.shared.saturation_le_twice_total
    (w.truncate D.full.load D.full.load_nonneg) c
  have hloss := E.saturation_loss
  have htotal := E.total_eq
  rw [D.saturation_eq] at hdeg
  linarith

end SaturationDecomposition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_cross_anchor_split
#print axioms Erdos547.DPRS.SaturationDecomposition.remainder_saturation_lower
