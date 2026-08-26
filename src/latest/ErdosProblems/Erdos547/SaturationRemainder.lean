import ErdosProblems.Erdos547.SaturationDecomposition
import ErdosProblems.Erdos547.FractionalSaturation

/-!
# The used and remaining pieces of an anchor decomposition
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace SaturationDecomposition

variable {μ : FractionalMatching G} {w : EdgeWeights G} {c : V}

def used (D : SaturationDecomposition μ w c) : FractionalMatching G :=
  D.full.add D.cross (fun u ↦ (D.combined_load_le u).trans (μ.load_le_one u))

theorem used_weight_le (D : SaturationDecomposition μ w c) (u v : V) :
    D.used.weight u v ≤ μ.weight u v := D.combined_le u v

def remainder (D : SaturationDecomposition μ w c) : FractionalMatching G :=
  μ.sub D.used D.used_weight_le

theorem used_load (D : SaturationDecomposition μ w c) (u : V) :
    D.used.load u = D.full.load u + D.cross.load u := FractionalMatching.add_load _ _ _ _

theorem used_total (D : SaturationDecomposition μ w c) :
    D.used.total = D.full.total + D.cross.total := FractionalMatching.add_total _ _ _

theorem remainder_load (D : SaturationDecomposition μ w c) (u : V) :
    D.remainder.load u = μ.load u - D.used.load u := FractionalMatching.sub_load _ _ _ _

theorem remainder_total (D : SaturationDecomposition μ w c) :
    D.remainder.total = μ.total - D.used.total := FractionalMatching.sub_total _ _ _

theorem used_saturation (D : SaturationDecomposition μ w c) :
    w.saturation D.used.load c = w.saturation μ.load c := by
  apply Finset.sum_congr rfl
  intro u _
  rw [D.used_load]
  exact D.captures_saturation u

theorem cross_saturation (D : SaturationDecomposition μ w c) :
    (w.truncate D.full.load D.full.load_nonneg).saturation D.cross.load c = D.cross.total := by
  have hh := D.full.saturation_add D.cross
    (fun u ↦ (D.combined_load_le u).trans (μ.load_le_one u)) w c
  change w.saturation D.full.load c +
    (w.truncate D.full.load D.full.load_nonneg).saturation D.cross.load c =
      w.saturation D.used.load c at hh
  rw [D.used_saturation, D.saturation_eq,
    D.full.saturation_eq_twice_total w c D.full_fits] at hh
  linarith

theorem inactive_truncate_zero (D : SaturationDecomposition μ w c) {u : V} (hu : u ∉ D.active) :
    (w.truncate D.full.load D.full.load_nonneg).weight c u = 0 := by
  change max 0 (w.weight c u - D.full.load u) = 0
  rw [D.outside_full_load hu, sub_self, max_self]

theorem remainder_saturation_identity (D : SaturationDecomposition μ w c) (d : V) :
    w.saturation D.used.load d + (w.truncate D.used.load D.used.load_nonneg).saturation
      D.remainder.load d = w.saturation μ.load d :=
  μ.saturation_sub D.used D.used_weight_le w d

theorem remainder_anchor_saturation_zero (D : SaturationDecomposition μ w c) :
    (w.truncate D.used.load D.used.load_nonneg).saturation D.remainder.load c = 0 := by
  have hh := D.remainder_saturation_identity c
  rw [D.used_saturation] at hh
  linarith

end SaturationDecomposition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SaturationDecomposition.cross_saturation
#print axioms Erdos547.DPRS.SaturationDecomposition.remainder_anchor_saturation_zero
