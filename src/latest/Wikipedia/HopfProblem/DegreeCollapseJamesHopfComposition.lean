import Wikipedia.HopfProblem.DegreeCollapseSphereCoadjunction
import Wikipedia.HopfProblem.DegreeCollapseJamesRetractionComposition

/-!
# The original James--Hopf projection under suspended precomposition

Use actual word representatives and the ordered loop comparison.
The continuous James--Hopf word map commutes with precomposition;
uncurrying retains the prescribed product suspension. The resulting
formula is for the original EHP homomorphism on native sphere groups.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.JamesHopfComposition

open NoExoticSixSphere SmoothCube SphereLiftFamily CubicalSphereSuspension JamesSphere
open SphereCoadjunction JamesRetractionComposition

variable {m n : ℕ} [NeZero m] [NeZero n]

def orderedLoopRepresentative (r : ℕ) (q : BasedMap n (WordHomology.Words r) 1) :
    BasedMap n (Path (spherePole (r + 1)) (spherePole (r + 1))) (Path.refl (spherePole (r + 1))) :=
  ⟨(AttachingSquare.orderedLoopComparison r).comp q.val,
    (congrArg (AttachingSquare.orderedLoopComparison r) q.property).trans
      (AttachingSquare.orderedLoopComparison_one r)⟩

def orderedSphereRepresentative (r : ℕ) (q : BasedMap n (WordHomology.Words r) 1) :
    SphereComposition.Based (n + 1) (r + 1) :=
  unadjoint (orderedLoopRepresentative r q)

theorem orderedSphereRepresentative_class (r : ℕ) (hr : 2 ≤ r)
    (q : BasedMap n (WordHomology.Words r) 1) :
    sphereClass (orderedSphereRepresentative r q) =
      InclusionRange.orderedComparison r hr n (sphereClass q) := by
  rw [AttachingSquare.orderedComparison_loopMap]
  exact unadjoint_native (orderedLoopRepresentative r q)

theorem orderedComparison_precomposition (r : ℕ) (hr : 2 ≤ r)
    (q : BasedMap n (WordHomology.Words r) 1) (g : SphereComposition.Based m n) :
    InclusionRange.orderedComparison r hr m (sphereClass (compose q g)) =
      sphereClass (compose (orderedSphereRepresentative r q) (productBasedMap g)) := by
  rw [← orderedSphereRepresentative_class]
  exact unadjoint_precomposition (orderedLoopRepresentative r q) g

theorem ordered_hopf_comparison (r : ℕ) (hr : 2 ≤ r)
    (c : π_ n (WordHomology.Words r) 1) :
    SuspensionComparison.orderedHopfHom r hr n
      (InclusionRange.orderedComparison r hr n c) =
      InclusionRange.orderedComparison (r + r) (by omega) n
        (HigherHomotopy.map (hopf r) (hopf_one r) c) := by
  change SuspensionComparison.coordinateEquiv (r + r) (n + 1)
    (NativeHopf.hopfHom r hr n ((SuspensionComparison.coordinateEquiv r (n + 1)).symm
      (SuspensionComparison.coordinateEquiv r (n + 1) (NativeHopf.spherePiEquiv r hr n c)))) = _
  rw [MulEquiv.symm_apply_apply, NativeHopf.hopfHom_comparison]
  rfl

def hopfWord (f : SphereComposition.Based (n + 1) 4) : BasedMap n (WordHomology.Words 6) 1 :=
  ⟨(hopf 3).comp (wordRepresentative f).val,
    (congrArg (hopf 3) (wordRepresentative f).property).trans (hopf_one 3)⟩

def hopfRepresentative (f : SphereComposition.Based (n + 1) 4) :
    SphereComposition.Based (n + 1) 7 := orderedSphereRepresentative 6 (hopfWord f)

theorem hopfRepresentative_class (f : SphereComposition.Based (n + 1) 4) :
    sphereClass (hopfRepresentative f) =
      SuspensionComparison.orderedHopfHom 3 (by decide) n (sphereClass f) := by
  rw [hopfRepresentative, orderedSphereRepresentative_class 6 (by decide)]
  change InclusionRange.orderedComparison 6 (by decide) n
    (HigherHomotopy.map (hopf 3) (hopf_one 3) (sphereClass (wordRepresentative f))) = _
  rw [← ordered_hopf_comparison 3 (by decide), wordRepresentative_class,
    MulEquiv.apply_symm_apply]

theorem hopf_precomposition (f : SphereComposition.Based (n + 1) 4)
    (g : SphereComposition.Based m n) :
    SuspensionComparison.orderedHopfHom 3 (by decide) m
      (sphereClass (compose f (productBasedMap g))) =
        sphereClass (compose (hopfRepresentative f) (productBasedMap g)) := by
  rw [← word_precomposition f g, ordered_hopf_comparison 3 (by decide)]
  exact orderedComparison_precomposition 6 (by decide) (hopfWord f) g

end Wikipedia.HopfProblem.DegreeCollapse.JamesHopfComposition
