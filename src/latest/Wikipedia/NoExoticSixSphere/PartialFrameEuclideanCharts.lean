import Wikipedia.NoExoticSixSphere.PartialFrameColumnBundle
import Wikipedia.NoExoticSixSphere.PartialFrameOneColumn
import Wikipedia.NoExoticSixSphere.Definitions

/-!
# Euclidean base charts for the actual partial-frame bundle

Stereographic projection identifies each antipode-complement base chart with
Euclidean space. Combining this with the column trivialization identifies
the actual open total-space patch with Euclidean space times the smaller
frame space. In the two-column case the latter factor is the actual unit
sphere, with its original topology.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnBundle

open GLOrthonormalization Set

variable {n r : ℕ}

local instance targetDimension : Fact (Module.finrank ℝ (Vector (n + 1)) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def baseHomeomorph (c : UnitSphere (Vector (n + 1))) : baseSet c ≃ₜ Vector n :=
  (Homeomorph.setCongr (stereographic'_source (n := n) (antipode c)).symm).trans
    ((stereographic' n (antipode c)).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target (n := n) (antipode c))).trans
        (Homeomorph.Set.univ (Vector n))))

theorem baseHomeomorph_apply (c : UnitSphere (Vector (n + 1))) (x : baseSet c) :
    baseHomeomorph c x = stereographic' n (antipode c) x.val := rfl

def sourceEuclideanHomeomorph (v : UnitSphere (Vector (r + 1)))
    (c : UnitSphere (Vector (n + 1))) :
    ((column v) ⁻¹' baseSet c) ≃ₜ Vector n × Space n r :=
  (sourceHomeomorph v c).trans ((baseHomeomorph c).prodCongr (Homeomorph.refl _))

theorem sourceEuclideanHomeomorph_fst (v : UnitSphere (Vector (r + 1)))
    (c : UnitSphere (Vector (n + 1))) (a : (column v) ⁻¹' baseSet c) :
    (sourceEuclideanHomeomorph v c a).1 = stereographic' n (antipode c) (column v a.val) :=
  rfl

def twoColumnSourceHomeomorph (v : UnitSphere (Vector 2))
    (c : UnitSphere (Vector (n + 1))) (w : UnitSphere (Vector 1)) :
    ((column v) ⁻¹' baseSet c) ≃ₜ Vector n × UnitSphere (Vector n) :=
  (sourceEuclideanHomeomorph v c).trans
    ((Homeomorph.refl (Vector n)).prodCongr (OneColumn.homeomorph w))

end NoExoticSixSphere.Stiefel.ColumnBundle
