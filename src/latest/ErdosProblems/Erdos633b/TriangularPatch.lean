import ErdosProblems.Erdos633b.PatchAssembly

/-! Rigid transport of patches between triangles with equal ordered side lengths. -/

namespace Erdos633b.Patch

noncomputable def transportSides {R S : Triangle} {n : ℕ} (d : Patch R S.support n)
    (T : Triangle) (hs : ∀ i, S.side i = T.side i) : Patch R T.support n := by
  have hdist := S.distances_of_sides T hs
  let g := S.vertexIsometry T hdist
  have hg : g '' S.support = T.support := by
    rw [← S.support_move g, S.move_vertexIsometry T hdist]
  have result := d.move g
  rwa [hg] at result

/-- Change the reference by a proved rigid congruence; every placed piece is unchanged. -/
noncomputable def changeTileBySides {R : Triangle} {S : Set Plane} {n : ℕ}
    (d : Patch R S n) (T : Triangle) (hs : ∀ i, T.side i = R.side i) : Patch T S n := by
  have hdist := T.distances_of_sides R hs
  let g := T.vertexIsometry R hdist
  have hg : g '' T.support = R.support := by
    rw [← T.support_move g, T.move_vertexIsometry R hdist]
  exact { place := fun i => g.trans (d.place i)
          covers := by
            simpa only [AffineIsometryEquiv.coe_trans, Set.image_comp, hg] using d.covers
          disjoint_interiors := by
            simpa only [AffineIsometryEquiv.coe_trans, Set.image_comp, hg]
              using d.disjoint_interiors }

end Erdos633b.Patch
