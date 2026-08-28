import Wikipedia.NoExoticSixSphere.SpherePoleCompactification
import Wikipedia.NoExoticSixSphere.RegularSphereFiberEmbedding

/-!
# Embed the original regular fiber in any dimension in one source chart

A source point mapped to the antipode of the regular value lies outside
the fiber. Its stereographic chart gives a genuine closed Euclidean
embedding of the compact fiber, without adding an ambient coordinate.
The fiber retains its original regular-fiber atlas.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StereographicFiber

open SpherePoleCompactification

variable {n k : ℕ} (f : C(Sphere (n + k), Sphere n))
  (hf : ContMDiff (𝓡 (n + k)) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 (n + k)) (𝓡 n) f x))
  (a : Sphere (n + k)) (ha : f a = -b)

include ha in
theorem fiber_ne_pole (x : {x : Sphere (n + k) // f x = b}) : x.val ≠ a := by
  intro h
  have he := x.property
  rw [h, ha] at he
  exact ne_neg b he.symm

def inclusion : {x : Sphere (n + k) // f x = b} → EuclideanSpace ℝ (Fin (n + k)) :=
  fun x ↦ chart a x.val

include ha in
theorem contMDiff_inclusion :
    letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin]);
    ContMDiff (𝓡 k) (𝓡 (n + k)) ∞ (inclusion f b a) := by
  let := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  intro x
  exact (chart_localDiffeomorph a (fiber_ne_pole f b a ha x)).contMDiffAt.comp x
    (regularFiber_contMDiff_subtype_val f hf b hreg k
      (by simp only [finrank_euclideanSpace_fin]) x)

include ha in
theorem inclusion_injective : Injective (inclusion f b a) := by
  intro x y h
  apply Subtype.ext
  apply (chart a).injOn ?_ ?_ h
  · simpa only [chart_source, mem_compl_iff, mem_singleton_iff] using fiber_ne_pole f b a ha x
  · simpa only [chart_source, mem_compl_iff, mem_singleton_iff] using fiber_ne_pole f b a ha y

include ha in
theorem inclusion_differential_injective (x : {x : Sphere (n + k) // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin]);
    Injective (mfderiv (𝓡 k) (𝓡 (n + k)) (inclusion f b a) x) := by
  let := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  have hc := chart_localDiffeomorph a (fiber_ne_pole f b a ha x)
  have hi := (regularFiber_contMDiff_subtype_val f hf b hreg k
    (by simp only [finrank_euclideanSpace_fin])).mdifferentiable (by simp) x
  change Injective (mfderiv (𝓡 k) (𝓡 (n + k))
    ((chart a) ∘ (Subtype.val : {x : Sphere (n + k) // f x = b} → Sphere (n + k))) x)
  rw [mfderiv_comp x (hc.mdifferentiableAt (by simp)) hi]
  exact (hc.mfderivToContinuousLinearEquiv (by simp)).injective.comp
    (regularFiber_injective_mfderiv_subtype_val f hf b hreg k
      (by simp only [finrank_euclideanSpace_fin]) x)

def embedding :
    letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin]);
    EuclideanEmbedding k {x : Sphere (n + k) // f x = b} := by
  let := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  let := RegularSphereFiber.fiber_compact f b
  exact {
    ambientDimension := n + k
    toFun := inclusion f b a
    smooth := contMDiff_inclusion f hf b hreg a ha
    closedEmbedding := (contMDiff_inclusion f hf b hreg a ha).continuous.isClosedEmbedding
      (inclusion_injective f b a ha)
    injective_mfderiv := inclusion_differential_injective f hf b hreg a ha }

end NoExoticSixSphere.StereographicFiber
