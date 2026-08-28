import Wikipedia.NoExoticSixSphere.StereographicFiberEmbedding
import Wikipedia.NoExoticSixSphere.RegularPointNeighborhood

/-!
# The original map supplies regular Euclidean equations for its fiber

Both stereographic charts are from the existing sphere atlases. Their
composition is smooth and submersive on the actual open regular-point
domain. On the fiber's actual embedding it vanishes exactly as required
to construct the induced normal frame.
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

def finiteMap : EuclideanSpace ℝ (Fin (n + k)) → Sphere n := f ∘ (chart a).symm

def coordinates : EuclideanSpace ℝ (Fin (n + k)) → EuclideanSpace ℝ (Fin n) :=
  (chart (-b)) ∘ finiteMap f a

def neighborhood : Set (EuclideanSpace ℝ (Fin (n + k))) :=
  (chart a).symm ⁻¹' (f ⁻¹' {-b}ᶜ ∩
    {x | Surjective (mfderiv (𝓡 (n + k)) (𝓡 n) f x)})

include hf in
theorem isOpen_neighborhood : IsOpen (neighborhood f b a) :=
  ((isClosed_singleton.isOpen_compl.preimage f.continuous).inter
    (isOpen_regularPoints hf)).preimage (contMDiff_chart_symm a).continuous

include ha in
theorem finiteMap_inclusion (x : {x : Sphere (n + k) // f x = b}) :
    finiteMap f a (inclusion f b a x) = b := by
  change f ((chart a).symm (chart a x.val)) = b
  rw [(chart a).left_inv (by
    simpa only [chart_source, mem_compl_iff, mem_singleton_iff] using fiber_ne_pole f b a ha x)]
  exact x.property

include ha in
theorem coordinates_inclusion (x : {x : Sphere (n + k) // f x = b}) :
    coordinates f b a (inclusion f b a x) = 0 := by
  change chart (-b) (finiteMap f a (inclusion f b a x)) = 0
  rw [finiteMap_inclusion f b a ha]
  simpa only [neg_neg] using chart_antipode (-b)

include hreg ha in
theorem inclusion_mem_neighborhood (x : {x : Sphere (n + k) // f x = b}) :
    inclusion f b a x ∈ neighborhood f b a := by
  change f ((chart a).symm (chart a x.val)) ≠ -b ∧
    Surjective (mfderiv (𝓡 (n + k)) (𝓡 n) f ((chart a).symm (chart a x.val)))
  rw [(chart a).left_inv (by
    simpa only [chart_source, mem_compl_iff, mem_singleton_iff] using fiber_ne_pole f b a ha x)]
  exact ⟨by simpa only [x.property, mem_compl_iff, mem_singleton_iff] using ne_neg b,
    hreg x.val x.property⟩

include hf in
theorem contDiffOn_coordinates : ContDiffOn ℝ ∞ (coordinates f b a) (neighborhood f b a) := by
  intro y hy
  have hi := (hf ((chart a).symm y)).comp y (contMDiff_chart_symm a y)
  have ho := (chart_localDiffeomorph (-b) hy.1).contMDiffAt.comp y hi
  exact ho.contDiffAt.contDiffWithinAt

include hf in
theorem surjective_fderiv_coordinates {y : EuclideanSpace ℝ (Fin (n + k))}
    (hy : y ∈ neighborhood f b a) : Surjective (fderiv ℝ (coordinates f b a) y) := by
  have hs := chart_symm_localDiffeomorph a y
  have ht := chart_localDiffeomorph (-b) hy.1
  have hds := hs.mdifferentiableAt (by simp)
  have hdf := (hf ((chart a).symm y)).mdifferentiableAt (by simp)
  have hdt := ht.mdifferentiableAt (by simp)
  rw [← mfderiv_eq_fderiv]
  change Surjective (mfderiv (𝓡 (n + k)) (𝓡 n) ((chart (-b)) ∘ (f ∘ (chart a).symm)) y)
  rw [mfderiv_comp y hdt (hdf.comp y hds), mfderiv_comp y hdf hds]
  exact (ht.mfderivToContinuousLinearEquiv (by simp)).surjective.comp
    (hy.2.comp (hs.mfderivToContinuousLinearEquiv (by simp)).surjective)

end NoExoticSixSphere.StereographicFiber
