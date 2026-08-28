import Wikipedia.NoExoticSixSphere.FiberQuotientComparison
import Wikipedia.NoExoticSixSphere.JamesSphereQuotientNativeHopf

/-!
# The actual James inclusion-fiber to quotient comparison

The source is the genuine homotopy fiber of the one-letter inclusion,
at the image of the actual sphere pole. Composing its paths with the
full first-stage quotient gives the based comparison homomorphism.
The boundary formula is proved; its metastable bijectivity is not.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.FiberQuotient

abbrev Fiber (n : ℕ) := HomotopyFiber.Space (inclusion n) (inclusion n (spherePole n))

def basepoint (n : ℕ) : Fiber n := HomotopyFiber.basepoint (inclusion n) (spherePole n)

theorem quotient_inclusion (n : ℕ) (x : Sphere n) :
    FirstStageQuotient.quotientMap n (inclusion n x) = FirstStageQuotient.basepoint n :=
  FirstStageQuotient.quotientMap_firstStage n (inclusion n x)
    (James.size_letter_le (spherePole n) x)

def toLoops (n : ℕ) : C(Fiber n,
    Path (FirstStageQuotient.basepoint n) (FirstStageQuotient.basepoint n)) :=
  FiberQuotientComparison.toLoops (inclusion n) (FirstStageQuotient.quotientMap n)
    (FirstStageQuotient.basepoint n) (quotient_inclusion n) (spherePole n)

def hom (n d : ℕ) [NeZero d] :
    π_ d (Fiber n) (basepoint n) →*
      π_ (d + 1) (FirstStageQuotient.Space n) (FirstStageQuotient.basepoint n) :=
  FiberQuotientComparison.hom (inclusion n) (FirstStageQuotient.quotientMap n)
    (FirstStageQuotient.basepoint n) (quotient_inclusion n) (spherePole n) d

theorem hom_boundary (n d : ℕ) [NeZero d]
    (c : π_ (d + 1) (WordHomology.Words n) (inclusion n (spherePole n))) :
    hom n d (HomotopyFiber.boundaryHom d (inclusion n) (spherePole n) c) =
      HigherHomotopy.map (N := Fin (d + 1)) (FirstStageQuotient.quotientMap n)
        (quotient_inclusion n (spherePole n)) c :=
  FiberQuotientComparison.hom_boundary (inclusion n) (FirstStageQuotient.quotientMap n)
    (FirstStageQuotient.basepoint n) (quotient_inclusion n) (spherePole n) d c

end NoExoticSixSphere.JamesSphere.FiberQuotient
