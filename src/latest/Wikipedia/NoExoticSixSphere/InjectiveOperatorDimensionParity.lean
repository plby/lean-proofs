import Wikipedia.NoExoticSixSphere.PartialFrameParityComplete
import Wikipedia.NoExoticSixSphere.PartialFrameDimensionCoordinates

/-!
# Frame parity with explicit dimension equalities

Normalize the actual injective operators and transport only the proved
dimension equalities. The resulting obstruction still detects extension of
the original map and completely classifies its ordinary homotopy class.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.Monomorphism

open GLOrthonormalization DiskBoundary

variable {N n : ℕ} (r : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2)

def sphereParityOfDimension (f : C(Sphere 3, Space N n)) : ZMod 2 :=
  sphereThirdObstruction r ((Stiefel.dimensionHomeomorph hN hn :
    C(Stiefel.Space N n, Stiefel.Space (3 + (r + 2)) (r + 2))).comp
      ((normalize N n).comp f))

theorem sphereParityOfDimension_zero_iff (f : C(Sphere 3, Space N n)) :
    sphereParityOfDimension r hN hn f = 0 ↔ Extends f := by
  rw [sphereParityOfDimension, sphereThirdObstruction_zero_iff_extension]
  exact (extends_dimensionHomeomorph_iff hN hn ((normalize N n).comp f)).trans
    (extends_normalize_iff f)

theorem sphereParityOfDimension_eq_iff (f g : C(Sphere 3, Space N n)) :
    sphereParityOfDimension r hN hn f = sphereParityOfDimension r hN hn g ↔
      f.Homotopic g := by
  rw [sphereParityOfDimension, sphereParityOfDimension,
    sphereThirdObstruction_eq_iff_homotopic]
  exact (homotopic_dimensionHomeomorph_iff hN hn
    ((normalize N n).comp f) ((normalize N n).comp g)).trans (normalize_homotopic_iff f g)

theorem sphereParityOfDimension_homotopic {f g : C(Sphere 3, Space N n)}
    (H : f.Homotopic g) :
    sphereParityOfDimension r hN hn f = sphereParityOfDimension r hN hn g :=
  (sphereParityOfDimension_eq_iff r hN hn f g).mpr H

end NoExoticSixSphere.Stiefel.Monomorphism
