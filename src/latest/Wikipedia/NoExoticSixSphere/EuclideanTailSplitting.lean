import Wikipedia.NoExoticSixSphere.EuclideanBlockInner

/-!
# Isometric coordinates splitting off the last Euclidean coordinate

These splittings use the actual `Fin` coordinate blocks. The scalar and
the remaining coordinates are arranged as an `L²` product, so that block
reconstruction is the ordinary operation of appending an identity column.
-/

noncomputable section

namespace NoExoticSixSphere.EuclideanTailCoordinates

open GLOrthonormalization

def scalar : ℝ ≃ₗᵢ[ℝ] Vector 1 where
  toLinearEquiv := DiskGraph.scalarCoordinates.toLinearEquiv
  norm_map' x := by
    change ‖DiskGraph.scalarCoordinates x‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [real_inner_self_eq_norm_sq] using DiskGraph.inner_scalarCoordinates x x

def finAdd (n m : ℕ) : Vector (n + m) ≃ₗᵢ[ℝ] WithLp 2 (Vector n × Vector m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m ↦ ℝ))

theorem finAdd_apply (n m : ℕ) (x : Vector (n + m)) :
    WithLp.ofLp (finAdd n m x) = EuclideanSpace.finAddEquivProd x := rfl

def split (n : ℕ) : Vector (n + 1) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Vector n) :=
  ((finAdd n 1).trans
    (LinearIsometryEquiv.withLpProdCongr 2
      (LinearIsometryEquiv.refl ℝ (Vector n)) scalar.symm)).trans
        (LinearIsometryEquiv.withLpProdComm 2 ℝ (Vector n) ℝ)

theorem split_apply (n : ℕ) (w : Vector (n + 1)) :
  split n w = WithLp.toLp 2
      (scalar.symm (EuclideanSpace.finAddEquivProd w).2,
        (EuclideanSpace.finAddEquivProd w).1) := rfl

theorem split_symm_apply (n : ℕ) (z : WithLp 2 (ℝ × Vector n)) :
    (split n).symm z = EuclideanSpace.finAddEquivProd.symm (z.snd, scalar z.fst) := rfl

end NoExoticSixSphere.EuclideanTailCoordinates
