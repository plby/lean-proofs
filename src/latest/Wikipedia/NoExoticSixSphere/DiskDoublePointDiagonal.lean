import Wikipedia.NoExoticSixSphere.DiskDoublePointTopology
import Wikipedia.NoExoticSixSphere.FourDiskSingularities
import Wikipedia.NoExoticSixSphere.CompactCoreImmersion

/-!
# Diagonal limits are original singularities, and there are finitely many

At an injective native differential, the original embedding followed by
a left-inverse projection has a local inverse. Its local injectivity
excludes any diagonal limit of actual double points. The first source
coordinate therefore injects the actual fixed-point set into the native
singular set. This proves finiteness, but not the reverse inclusion of
singularities or a local chart through them.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DiskDoublePoints

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (g : Vector 4 → M)

include e

theorem diagonal_not_mem_closure_of_injective_derivative (x : Vector 4)
    (hg : ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (hi : Injective (mfderiv (𝓡 4) (𝓡 7) g x)) :
    (x, x) ∉ closure (points g) := by
  have hgi := (GenericFourDisk.injective_embedded_derivative_iff e g x
    (hg.mdifferentiableAt (by simp))).mpr hi
  have hgs : ContDiffAt ℝ ∞ (e.toFun ∘ g) x :=
    (e.smooth.contMDiffAt.comp x hg).contDiffAt
  obtain ⟨V, hV, hxV, hVi⟩ := CompactCoreImmersion.exists_open_injOn_at hgs hgi
  intro hcl
  obtain ⟨q, hqV, hq⟩ := (_root_.mem_closure_iff.mp hcl) (V ×ˢ V) (hV.prod hV) ⟨hxV, hxV⟩
  exact hq.2.2.1 (hVi hqV.1 hqV.2 (congrArg e.toFun hq.2.2.2))

theorem singular_of_diagonal_mem_closure
    (hg : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (p : ClosedPoints g) (hp : p.val.1 = p.val.2) :
    ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g p.val.1) := by
  intro hi
  have hK := closure_subset_closedBall g p.property
  have hdiag : p.val = (p.val.1, p.val.1) := Prod.ext rfl hp.symm
  apply diagonal_not_mem_closure_of_injective_derivative e g p.val.1 (hg _ hK.1) hi
  rw [← hdiag]
  exact p.property

theorem finite_diagonal_points
    (hg : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (hs : (closedBall (0 : Vector 4) 1 ∩
      {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}).Finite) :
    {p : ClosedPoints g | p.val.1 = p.val.2}.Finite := by
  have hmap : MapsTo (fun p : ClosedPoints g ↦ p.val.1)
      {p | p.val.1 = p.val.2}
      (closedBall 0 1 ∩ {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}) := by
    intro p hp
    exact ⟨(closure_subset_closedBall g p.property).1,
      singular_of_diagonal_mem_closure e g hg p hp⟩
  have hi : InjOn (fun p : ClosedPoints g ↦ p.val.1) {p | p.val.1 = p.val.2} := by
    intro p hp q hq he
    apply Subtype.ext
    exact Prod.ext he (hp.symm.trans (he.trans hq))
  exact Set.Finite.of_injOn hmap hi hs

theorem finite_diagonalOrbits
    (hg : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (hs : (closedBall (0 : Vector 4) 1 ∩
      {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}).Finite) :
    (diagonalOrbits g).Finite :=
  (finite_diagonal_points e g hg hs).image (unorderedProj g)

end NoExoticSixSphere.DiskDoublePoints
