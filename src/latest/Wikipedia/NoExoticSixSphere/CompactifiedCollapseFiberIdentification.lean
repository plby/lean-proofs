import Wikipedia.NoExoticSixSphere.CompactifiedEmbeddingDifferential
import Wikipedia.NoExoticSixSphere.RegularFiberIdentification

/-!
# The native fiber identification of a compactified embedded manifold

The fiber parametrization is the original compactified embedding. Its
smooth immersion and exact fiber identity give a diffeomorphism retaining
the independently supplied source atlas and the native regular-fiber atlas.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (e : EuclideanEmbedding n M)
  (g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - n)))
  (hg : ContMDiff (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n)) ∞ g)
  (hreg : ∀ y, g y = sphereZero (e.ambientDimension - n) →
    Function.Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - n)) g y))
  (hd : e.ambientDimension = (e.ambientDimension - n) + n)
  (hfiber : ∀ y, g y = sphereZero (e.ambientDimension - n) ↔ ∃ x, e.compactifiedEmbedding x = y)

def diffeomorphToCompactifiedFiber :
    letI := regularFiberAtlas g hg (sphereZero (e.ambientDimension - n)) hreg n
      (by simpa using hd);
    M ≃ₘ⟮𝓡 n, 𝓡 n⟯
      {y : Sphere e.ambientDimension // g y = sphereZero (e.ambientDimension - n)} :=
  diffeomorphToRegularFiber g hg (sphereZero (e.ambientDimension - n)) hreg n
    (by simpa using hd) e.compactifiedEmbedding e.contMDiff_compactifiedEmbedding
      e.compactifiedEmbedding_isEmbedding.injective e.injective_mfderiv_compactifiedEmbedding hfiber

theorem diffeomorphToCompactifiedFiber_val (x : M) :
    letI := regularFiberAtlas g hg (sphereZero (e.ambientDimension - n)) hreg n
      (by simpa using hd);
    (e.diffeomorphToCompactifiedFiber g hg hreg hd hfiber x).val = e.compactifiedEmbedding x := rfl

end NoExoticSixSphere.EuclideanEmbedding
