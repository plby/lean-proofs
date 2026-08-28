import Wikipedia.NoExoticSixSphere.StabilizedSpanningDisk
import Wikipedia.NoExoticSixSphere.PartialFrames
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Inner products in the actual stabilized Euclidean coordinates

The coordinate identifications use the ordinary product topology, whose norm
is not Euclidean. Their exact inner-product formulas are obtained through
the genuine `L²` product isometry, not by declaring those product norms equal.
-/

noncomputable section

namespace NoExoticSixSphere

open GLOrthonormalization

theorem inner_finAdd_split {n m : ℕ} (u v : Vector (n + m)) :
    inner ℝ u v =
      inner ℝ (EuclideanSpace.finAddEquivProd u).1 (EuclideanSpace.finAddEquivProd v).1 +
      inner ℝ (EuclideanSpace.finAddEquivProd u).2 (EuclideanSpace.finAddEquivProd v).2 := by
  let L : Vector (n + m) ≃ₗᵢ[ℝ] WithLp 2 (Vector n × Vector m) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
      (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m ↦ ℝ))
  exact (L.inner_map_map u v).symm

theorem inner_finAdd_symm {n m : ℕ} (u v : Vector n × Vector m) :
    inner ℝ (EuclideanSpace.finAddEquivProd.symm u)
      (EuclideanSpace.finAddEquivProd.symm v) = inner ℝ u.1 v.1 + inner ℝ u.2 v.2 := by
  rw [inner_finAdd_split, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]

theorem inner_appendZeroMap (N k : ℕ) (u v : Vector N) :
    inner ℝ (appendZeroMap N k u) (appendZeroMap N k v) = inner ℝ u v := by
  change inner ℝ (EuclideanSpace.finAddEquivProd.symm (u, (0 : Vector k)))
    (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector k))) = _
  rw [inner_finAdd_symm]
  simp

namespace DiskGraph

theorem inner_scalarCoordinates (u v : ℝ) :
    inner ℝ (scalarCoordinates u) (scalarCoordinates v) = inner ℝ u v := by
  rw [PiLp.inner_apply, Fin.sum_univ_one]
  rfl

theorem inner_extraCoordinates (d : ℕ) (u v : ℝ × Vector d) :
    inner ℝ (extraCoordinates d u) (extraCoordinates d v) =
      inner ℝ u.1 v.1 + inner ℝ u.2 v.2 := by
  change inner ℝ (EuclideanSpace.finAddEquivProd.symm (scalarCoordinates u.1, u.2))
    (EuclideanSpace.finAddEquivProd.symm (scalarCoordinates v.1, v.2)) = _
  rw [inner_finAdd_symm, inner_scalarCoordinates]

theorem inner_coordinateEquiv (N d : ℕ) (u v : Vector N × (ℝ × Vector d)) :
    inner ℝ (coordinateEquiv N d u) (coordinateEquiv N d v) =
      inner ℝ u.1 v.1 + (inner ℝ u.2.1 v.2.1 + inner ℝ u.2.2 v.2.2) := by
  change inner ℝ (EuclideanSpace.finAddEquivProd.symm (u.1, extraCoordinates d u.2))
    (EuclideanSpace.finAddEquivProd.symm (v.1, extraCoordinates d v.2)) = _
  rw [inner_finAdd_symm, inner_extraCoordinates]

end DiskGraph

namespace StabilizedSpanningDisk

theorem inner_coordinates (N d : ℕ) (u v : (Vector N × ℝ) × (ℝ × Vector d)) :
    inner ℝ (coordinates N d u) (coordinates N d v) =
      inner ℝ u.1.1 v.1.1 +
        (inner ℝ u.1.2 v.1.2 + (inner ℝ u.2.1 v.2.1 + inner ℝ u.2.2 v.2.2)) := by
  change inner ℝ
    (DiskGraph.coordinateEquiv N (1 + d) (u.1.1, (u.1.2, DiskGraph.extraCoordinates d u.2)))
    (DiskGraph.coordinateEquiv N (1 + d) (v.1.1, (v.1.2, DiskGraph.extraCoordinates d v.2))) = _
  rw [DiskGraph.inner_coordinateEquiv, DiskGraph.inner_extraCoordinates]

end StabilizedSpanningDisk

end NoExoticSixSphere
