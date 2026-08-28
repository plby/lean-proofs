import Wikipedia.NoExoticSixSphere.JamesPairFiber
import Wikipedia.NoExoticSixSphere.RelativeTwoSkeletonNormalization

/-!
# Coherent relative simplex normalization for the actual James cylinder pair

The required second-homotopy surjectivity is proved for the original
source-image inclusion using the checked homology comparison and second
Hurewicz isomorphism. Thus all normalization inputs are discharged here.
Every endpoint triangle lies in the original source image, and each
endpoint tetrahedron has its entire boundary there. Higher relative
Hurewicz detection is still not asserted.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.JamesSphere.PairNormalization

open ComparisonCylinder

local instance cylinderSimplyConnected (n : ℕ) : SimplyConnectedSpace (Cylinder (n + 2)) :=
  cylinder_simplyConnected n

local instance sourceSimplyConnected (n : ℕ) : SimplyConnectedSpace (sourceImage (n + 2)) :=
  sourceImage_simplyConnected n

theorem inclusion_piTwo_surjective (n : ℕ) (a : sourceImage (n + 2)) :
    Function.Surjective
      (HigherHomotopy.map (N := Fin 2) (subtypeInclusion (sourceImage (n + 2))) (y := a) rfl) := by
  let f := subtypeInclusion (sourceImage (n + 2))
  have he : HigherHomotopy.map (N := Fin 2) f (y := a) rfl =
      SecondHurewicz.homotopyMap f a := by
    funext c
    refine Quotient.inductionOn c fun p ↦ ?_
    rfl
  change Function.Surjective (HigherHomotopy.map (N := Fin 2) f (y := a) rfl)
  rw [he]
  exact (HomologyEquivalence.piTwo_bijective f
    (source_inclusion_homology_bijective (n + 2) 2 (by omega)) a).surjective

def homotopy (n d : ℕ) (a : sourceImage (n + 2)) (smp : C(Simplex d, Cylinder (n + 2))) :
    C(I × Simplex d, Cylinder (n + 2)) :=
  RelativeTwoSkeletonNormalization.homotopy (sourceImage (n + 2)) a
    (inclusion_piTwo_surjective n a) d smp

theorem homotopy_zero (n d : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex d, Cylinder (n + 2))) (s : Simplex d) :
    homotopy n d a smp (0, s) = smp s :=
  RelativeTwoSkeletonNormalization.homotopy_zero _ _ _ d smp s

theorem homotopy_face (n d : ℕ) (a : sourceImage (n + 2)) :
    FaceCompatibleHomotopies d (homotopy n d a) (homotopy n (d + 1) a) :=
  RelativeTwoSkeletonNormalization.homotopy_face _ _ _ d

theorem homotopy_mem (n d : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex d, Cylinder (n + 2))) (hs : ∀ s, smp s ∈ sourceImage (n + 2))
    (p : I × Simplex d) : homotopy n d a smp p ∈ sourceImage (n + 2) :=
  RelativeTwoSkeletonNormalization.homotopy_mem _ _ _ d smp hs p

def endpoint (n d : ℕ) (a : sourceImage (n + 2)) (smp : C(Simplex d, Cylinder (n + 2))) :
    C(Simplex d, Cylinder (n + 2)) :=
  SecondHurewicz.SimplyConnected.timeSlice (homotopy n d a smp) 1

theorem endpoint_face (n d : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex (d + 1), Cylinder (n + 2))) (i : Fin (d + 2)) :
    (endpoint n (d + 1) a smp).comp (simplexFace d i) =
      endpoint n d a (smp.comp (simplexFace d i)) :=
  timeSlice_face (homotopy_face n d a) smp i 1

theorem endpoint_triangle_mem (n : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex 2, Cylinder (n + 2))) (s : Simplex 2) :
    endpoint n 2 a smp s ∈ sourceImage (n + 2) :=
  RelativeTwoSkeletonNormalization.endpoint_triangle_mem (sourceImage (n + 2)) a
    (inclusion_piTwo_surjective n a) smp s

theorem endpoint_tetrahedron_boundary (n : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex 3, Cylinder (n + 2))) (s : Simplex 3) (hs : s ∈ simplexBoundary 3) :
    endpoint n 3 a smp s ∈ sourceImage (n + 2) :=
  RelativeTwoSkeletonNormalization.endpoint_tetrahedron_boundary (sourceImage (n + 2)) a
    (inclusion_piTwo_surjective n a) smp s hs

end NoExoticSixSphere.JamesSphere.PairNormalization
