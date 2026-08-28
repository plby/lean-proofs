import Wikipedia.NoExoticSixSphere.JamesSphereCellContractionComparison

/-!
# The original James-cell quotient homomorphism is an isomorphism in range

The constructed boundary and target homeomorphisms identify the original
cell quotient homomorphism with the actual cubical suspension. The based
contraction comparison discharges the coordinate-change input. Inverting
the original boundary homeomorphism transfers suspension bijectivity to
the original max-norm cell-boundary homomorphism itself.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.RoundCell

def boundaryPiEquiv (n : ℕ) (hn : 0 < n) (d : ℕ) [NeZero d] :
    π_ d (Sphere (sphereDimension n)) (spherePole (sphereDimension n)) ≃*
      π_ d (CellBoundary.Boundary n) (CellBoundary.corner n hn) :=
  (HigherHomotopyCoordinates.homeomorphMulEquiv (Fin d)
    (boundaryHomeomorph n hn) (spherePole (sphereDimension n))).trans
      (NativeHomotopyTargetEquality.equiv d (boundaryHomeomorph_pole n hn))

theorem boundaryPiEquiv_apply (n : ℕ) (hn : 0 < n) (d : ℕ) [NeZero d]
    (c : π_ d (Sphere (sphereDimension n)) (spherePole (sphereDimension n))) :
    boundaryPiEquiv n hn d c = HigherHomotopy.map (N := Fin d)
      (boundaryHomeomorph n hn : C(Sphere (sphereDimension n), CellBoundary.Boundary n))
      (boundaryHomeomorph_pole n hn) c :=
  NativeHomotopyTargetEquality.equiv_map d
    (boundaryHomeomorph n hn : C(Sphere (sphereDimension n), CellBoundary.Boundary n))
    (boundaryHomeomorph_pole n hn) c

def targetHomeomorph (n : ℕ) (hn : 0 < n) : Sphere (sphereDimension n + 1) ≃ₜ Sphere (n + n) :=
  RoundDiskCubicalSuspension.homeomorph (quotient n hn) (spherePole (n + n))
    (quotient_base n hn) (quotient_fiber n hn) (quotient_surjective n hn) (parameterHomeomorph n hn)

theorem targetHomeomorph_pole (n : ℕ) (hn : 0 < n) :
    targetHomeomorph n hn (spherePole (sphereDimension n + 1)) = spherePole (n + n) :=
  RoundDiskCubicalSuspension.homeomorph_pole (quotient n hn) (spherePole (n + n))
    (quotient_base n hn) (quotient_fiber n hn) (quotient_surjective n hn) (parameterHomeomorph n hn)

theorem quotientHom_eq_suspension (n : ℕ) (hn : 0 < n) (d : ℕ) [NeZero d]
    (c : π_ d (Sphere (sphereDimension n)) (spherePole (sphereDimension n))) :
    CellBoundary.quotientHom n hn d (boundaryPiEquiv n hn d c) =
      HigherHomotopy.map (N := Fin (d + 1))
        (targetHomeomorph n hn : C(Sphere (sphereDimension n + 1), Sphere (n + n)))
        (targetHomeomorph_pole n hn) (CubicalSphereSuspension.hom d (sphereDimension n) c) := by
  rw [boundaryPiEquiv_apply]
  exact (quotientHom_comparison n hn d c).trans
    (RoundDiskCubicalSuspension.hom_eq_postcompose (quotient n hn) (spherePole (n + n))
      (quotient_base n hn) (parameterHomeomorph n hn) (quotient_fiber n hn)
      (quotient_surjective n hn) d c)

theorem quotientHom_bijective (n : ℕ) (hn : 0 < n) (d : ℕ) [NeZero d]
    (hd : d + 3 < 4 * n) : Function.Bijective (CellBoundary.quotientHom n hn d) := by
  have hr := RoundDiskCubicalSuspension.hom_bijective (quotient n hn) (spherePole (n + n))
    (quotient_base n hn) (parameterHomeomorph n hn) (quotient_fiber n hn)
    (quotient_surjective n hn) d (by unfold sphereDimension; omega)
  have hf : (CellBoundary.quotientHom n hn d : _ → _) ∘ boundaryPiEquiv n hn d =
      RoundDiskCubicalSuspension.hom (quotient n hn) (spherePole (n + n))
        (quotient_base n hn) (parameterHomeomorph n hn) d := by
    funext c
    rw [Function.comp_apply, boundaryPiEquiv_apply]
    exact quotientHom_comparison n hn d c
  rw [← hf] at hr
  exact (Function.Bijective.of_comp_iff _ (boundaryPiEquiv n hn d).bijective).mp hr

end NoExoticSixSphere.JamesSphere.RoundCell
