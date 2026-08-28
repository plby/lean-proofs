import Wikipedia.NoExoticSixSphere.CanonicalRightInverse
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Canonical normal frames and genuine Hilbert products

The orthogonal right inverse of a block differential is the block map of
the original orthogonal right inverses. The ambient and equation products
carry their L2 inner products; the ordinary product norm is not used as
an inner-product norm.
-/

noncomputable section

namespace NoExoticSixSphere.HilbertProduct

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def map (D : E →L[ℝ] F) (A : G →L[ℝ] H) :
    WithLp 2 (E × G) →L[ℝ] WithLp 2 (F × H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F H).symm.toContinuousLinearMap.comp
    ((D.prodMap A).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E G).toContinuousLinearMap)

theorem map_apply (D : E →L[ℝ] F) (A : G →L[ℝ] H) (v : WithLp 2 (E × G)) :
    map D A v = WithLp.toLp 2 (D v.fst, A v.snd) := rfl

theorem map_surjective (D : E →L[ℝ] F) (A : G →L[ℝ] H)
    (hD : Function.Surjective D) (hA : Function.Surjective A) :
    Function.Surjective (map D A) := by
  intro v
  obtain ⟨x, hx⟩ := hD v.fst
  obtain ⟨y, hy⟩ := hA v.snd
  refine ⟨WithLp.toLp 2 (x, y), ?_⟩
  rw [map_apply]
  change WithLp.toLp 2 (D x, A y) = v
  rw [hx, hy]
  rfl

theorem map_kernel (D : E →L[ℝ] F) (A : G →L[ℝ] H) (v : WithLp 2 (E × G)) :
    v ∈ (map D A).ker ↔ D v.fst = 0 ∧ A v.snd = 0 := by
  change WithLp.toLp 2 (D v.fst, A v.snd) = WithLp.toLp 2 (0, 0) ↔ _
  rw [(WithLp.toLp_injective 2).eq_iff]
  simp only [Prod.mk.injEq]

end NoExoticSixSphere.HilbertProduct

namespace NoExoticSixSphere

variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem orthogonalRightInverse_product (D : E →L[ℝ] F) (A : G →L[ℝ] H)
    (hD : Function.Surjective D) (hA : Function.Surjective A) :
    orthogonalRightInverse (HilbertProduct.map D A) =
      HilbertProduct.map (orthogonalRightInverse D) (orthogonalRightInverse A) := by
  apply orthogonalRightInverse_eq_of_rightInverse _ (HilbertProduct.map_surjective D A hD hA)
  · intro v
    rw [HilbertProduct.map_apply, HilbertProduct.map_apply]
    change WithLp.toLp 2 (D (orthogonalRightInverse D v.fst),
      A (orthogonalRightInverse A v.snd)) = v
    rw [apply_orthogonalRightInverse D hD, apply_orthogonalRightInverse A hA]
    rfl
  · rintro _ ⟨w, rfl⟩
    rw [Submodule.mem_orthogonal']
    intro v hv
    obtain ⟨hvD, hvA⟩ := (HilbertProduct.map_kernel D A v).mp hv
    have hRD : orthogonalRightInverse D w.fst ∈ D.kerᗮ := by
      rw [← range_orthogonalRightInverse D hD]
      exact ⟨w.fst, rfl⟩
    have hRA : orthogonalRightInverse A w.snd ∈ A.kerᗮ := by
      rw [← range_orthogonalRightInverse A hA]
      exact ⟨w.snd, rfl⟩
    change inner ℝ (orthogonalRightInverse D w.fst) v.fst +
      inner ℝ (orthogonalRightInverse A w.snd) v.snd = 0
    rw [Submodule.mem_orthogonal'] at hRD hRA
    rw [hRD v.fst hvD, hRA v.snd hvA, add_zero]

end NoExoticSixSphere
