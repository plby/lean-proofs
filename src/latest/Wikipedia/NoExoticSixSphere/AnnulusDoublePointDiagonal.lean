import Wikipedia.NoExoticSixSphere.AnnulusDoublePointTopology
import Wikipedia.NoExoticSixSphere.FourAnnulusSingularities
import Wikipedia.NoExoticSixSphere.CompactCoreImmersion

/-!
# Diagonal annulus double-point limits are original singularities

Local injectivity of the actual embedded map at an injective native
differential excludes every diagonal double-point limit. The first
source coordinate injects the actual diagonal locus into the intrinsic
singular set. Finiteness follows when that singular set is finite, without
yet asserting the converse or a boundary chart through a singularity.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.AnnulusDoublePoints

open GLOrthonormalization SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (g : Vector 4 → M)

include e

theorem diagonal_not_mem_closure_of_injective_derivative (x : Vector 4)
    (hg : ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (hi : Injective (mfderiv (𝓡 4) (𝓡 7) g x)) : (x, x) ∉ closure (points g) := by
  have hgi := (GenericFourDisk.injective_embedded_derivative_iff e g x
    (hg.mdifferentiableAt (by simp))).mpr hi
  have hgs : ContDiffAt ℝ ∞ (e.toFun ∘ g) x :=
    (e.smooth.contMDiffAt.comp x hg).contDiffAt
  obtain ⟨V, hV, hxV, hVi⟩ := CompactCoreImmersion.exists_open_injOn_at hgs hgi
  intro hcl
  obtain ⟨q, hqV, hq⟩ := (_root_.mem_closure_iff.mp hcl) (V ×ˢ V) (hV.prod hV) ⟨hxV, hxV⟩
  exact hq.2.2.1 (hVi hqV.1 hqV.2 (congrArg e.toFun hq.2.2.2))

theorem singular_of_diagonal_mem_closure
    (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (v : ClosedPoints g) (hv : v.val.1 = v.val.2) :
    ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g v.val.1) := by
  intro hi
  have hK := closure_subset_domain g v.property
  have hdiag : v.val = (v.val.1, v.val.1) := Prod.ext rfl hv.symm
  apply diagonal_not_mem_closure_of_injective_derivative e g v.val.1 (hg _ hK.1) hi
  rw [← hdiag]
  exact v.property

theorem finite_diagonal_points
    (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (hs : (domain 3 ∩ {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}).Finite) :
    {v : ClosedPoints g | v.val.1 = v.val.2}.Finite := by
  have hmap : MapsTo (fun v : ClosedPoints g ↦ v.val.1)
      {v | v.val.1 = v.val.2}
      (domain 3 ∩ {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}) := by
    intro v hv
    exact ⟨(closure_subset_domain g v.property).1,
      singular_of_diagonal_mem_closure e g hg v hv⟩
  have hi : InjOn (fun v : ClosedPoints g ↦ v.val.1) {v | v.val.1 = v.val.2} := by
    intro v hv w hw he
    apply Subtype.ext
    exact Prod.ext he (hv.symm.trans (he.trans hw))
  exact Set.Finite.of_injOn hmap hi hs

theorem finite_diagonalOrbits
    (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (hs : (domain 3 ∩ {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}).Finite) :
    (diagonalOrbits g).Finite := (finite_diagonal_points e g hg hs).image (unorderedProj g)

end NoExoticSixSphere.AnnulusDoublePoints
