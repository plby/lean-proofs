import Wikipedia.NoExoticSixSphere.TransverseSpherePairRepresentative

/-!
# A choice-independent geometric intersection number for sphere maps

Choose the actual smooth transverse representatives already constructed and
count their actual source-pair intersections modulo two. The ordinary-
homotopy invariance theorem proves independence of every representative,
embedding, and tubular-retraction choice used in this definition.

The resulting function is symmetric and homotopy invariant. Bilinearity and
descent to the native middle homology group are not asserted in this file.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization MapIntersections

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

/-- The count of the constructed finite transverse pair, not an assigned algebraic form. -/
def sphereIntersectionNumber (f g : C(Sphere 3, M)) : ZMod 2 :=
  parity (e.intersectionRepresentative r f g).left (e.intersectionRepresentative r f g).right

theorem sphereIntersectionNumber_eq_representative (f g : C(Sphere 3, M))
    (D : Representative f g) : sphereIntersectionNumber e r f g = parity D.left D.right := by
  let R := e.intersectionRepresentative r f g
  change parity R.left R.right = parity D.left D.right
  exact e.intersectionParity_homotopic r R.left D.left R.right D.right
    R.smooth_left D.smooth_left R.smooth_right D.smooth_right R.transverse D.transverse
    (R.homotopic_left.symm.trans D.homotopic_left)
    (R.homotopic_right.symm.trans D.homotopic_right)

theorem sphereIntersectionNumber_eq_parity (f g : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (ht : ∀ x y, f x = g y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) :
    sphereIntersectionNumber e r f g = parity f g := by
  let R := e.intersectionRepresentative r f g
  change parity R.left R.right = parity f g
  exact e.intersectionParity_homotopic r R.left f R.right g
    R.smooth_left hf R.smooth_right hg R.transverse ht
    R.homotopic_left.symm R.homotopic_right.symm

theorem sphereIntersectionNumber_homotopic (f f' g g' : C(Sphere 3, M))
    (Hf : f.Homotopic f') (Hg : g.Homotopic g') :
    sphereIntersectionNumber e r f g = sphereIntersectionNumber e r f' g' := by
  let R := e.intersectionRepresentative r f g
  let S := e.intersectionRepresentative r f' g'
  change parity R.left R.right = parity S.left S.right
  exact e.intersectionParity_homotopic r R.left S.left R.right S.right
    R.smooth_left S.smooth_left R.smooth_right S.smooth_right R.transverse S.transverse
    (R.homotopic_left.symm.trans (Hf.trans S.homotopic_left))
    (R.homotopic_right.symm.trans (Hg.trans S.homotopic_right))

theorem sphereIntersectionNumber_comm (f g : C(Sphere 3, M)) :
    sphereIntersectionNumber e r f g = sphereIntersectionNumber e r g f := by
  let R := e.intersectionRepresentative r f g
  have h := sphereIntersectionNumber_eq_representative e r g f R.swap
  change sphereIntersectionNumber e r g f = parity R.right R.left at h
  exact (parity_comm R.left R.right).trans h.symm

theorem sphereIntersectionNumber_independent (e' : EuclideanEmbedding 6 M)
    (r' : TubularRetraction e') (f g : C(Sphere 3, M)) :
    sphereIntersectionNumber e r f g = sphereIntersectionNumber e' r' f g :=
  sphereIntersectionNumber_eq_representative e r f g (e'.intersectionRepresentative r' f g)

theorem sphereIntersectionNumber_zero_of_disjoint (f g : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hdis : Disjoint (range f) (range g)) : sphereIntersectionNumber e r f g = 0 := by
  have hne (x y : Sphere 3) : f x ≠ g y := by
    intro h
    exact disjoint_left.mp hdis (mem_range_self x) ⟨y, h.symm⟩
  have ht : ∀ x y, f x = g y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) g y)) :=
    fun x y h ↦ (hne x y h).elim
  rw [sphereIntersectionNumber_eq_parity e r f g hf hg ht]
  have he : pairs f g = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    exact fun p hp ↦ hne p.1 p.2 hp
  simp only [parity, he, ncard_empty, Nat.cast_zero]

end NoExoticSixSphere.EuclideanEmbedding
