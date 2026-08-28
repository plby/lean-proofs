import Wikipedia.NoExoticSixSphere.JamesSphereEHPCellFormula

/-!
# The literal cubical representative in the second-cell EHP formula

The first cube coordinate runs along a straight segment from the
boundary point to the selected corner. The remaining coordinates carry
the original boundary representative. Applying the characteristic map
and collapsing the first James stage gives the exact quotient class
used by the connecting-map formula, including the original sphere
pairing and the order of its two coordinate blocks.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem.DegreeCollapse

namespace NoExoticSixSphere.JamesSphere.CellBoundary

theorem collapse_attaching (n : ℕ) (x : Sphere n) :
    SecondStage.collapse n (SecondStageCone.attaching n x) = spherePole (n + n) :=
  (SecondStage.collapse_eq_pole_iff n _).mpr (James.size_letter_le (spherePole n) x)

theorem collapse_characteristic (n : ℕ) (x : DiskCylinder.Disk (E := Coordinates n)) :
    SecondStage.collapse n (Cell.closedPresentation n 2 x) =
      pairing n (Cell.array n 2 x.val 0, Cell.array n 2 x.val 1) :=
  SecondStage.collapse_presentation n (Cell.array n 2 x.val)

def sphereLoops (n : ℕ) (hn : 0 < n) :
    C(Boundary n, Path (spherePole (n + n)) (spherePole (n + n))) :=
  DiskBoundaryFiberLift.quotientLoops (SecondStageCone.attaching n) (attaching n)
    (Cell.closedPresentation n 2) (characteristic_boundary n) (corner n hn)
      (spherePole n) (attaching_corner n hn) (SecondStage.collapse n)
        (spherePole (n + n)) (collapse_attaching n)

theorem sphereLoops_apply (n : ℕ) (hn : 0 < n) (s : Boundary n) (t : unitInterval) :
    sphereLoops n hn s t = SecondStage.collapse n (Cell.closedPresentation n 2
      (DiskBoundary.segment (cornerDisk n) (t, DiskCylinder.boundaryToDisk s))) := rfl

theorem sphereLoops_corner (n : ℕ) (hn : 0 < n) :
    sphereLoops n hn (corner n hn) = Path.refl (spherePole (n + n)) :=
  DiskBoundaryFiberLift.quotientLoops_basepoint (SecondStageCone.attaching n) (attaching n)
    (Cell.closedPresentation n 2) (characteristic_boundary n) (corner n hn)
      (spherePole n) (attaching_corner n hn) (SecondStage.collapse n)
        (spherePole (n + n)) (collapse_attaching n)

def quotientGenLoop (n : ℕ) (hn : 0 < n) {d : ℕ}
    (p : GenLoop (Fin d) (Boundary n) (corner n hn)) :
    GenLoop (Fin (d + 1)) (Sphere (n + n)) (spherePole (n + n)) :=
  GeneralizedLoopCurrying.uncurry
    (HigherHomotopy.genLoopMap (sphereLoops n hn) (sphereLoops_corner n hn) p)

theorem quotientGenLoop_apply (n : ℕ) (hn : 0 < n) {d : ℕ}
    (p : GenLoop (Fin d) (Boundary n) (corner n hn)) (u : Fin (d + 1) → unitInterval) :
    (quotientGenLoop n hn p).val u =
      SecondStage.collapse n (Cell.closedPresentation n 2
        (DiskBoundary.segment (cornerDisk n)
          (u 0, DiskCylinder.boundaryToDisk (p.val (Fin.tail u))))) := rfl

theorem quotientGenLoop_pairing (n : ℕ) (hn : 0 < n) {d : ℕ}
    (p : GenLoop (Fin d) (Boundary n) (corner n hn)) (u : Fin (d + 1) → unitInterval) :
    (quotientGenLoop n hn p).val u =
      pairing n
        (Cell.array n 2 (DiskBoundary.segment (cornerDisk n)
          (u 0, DiskCylinder.boundaryToDisk (p.val (Fin.tail u)))).val 0,
        Cell.array n 2 (DiskBoundary.segment (cornerDisk n)
          (u 0, DiskCylinder.boundaryToDisk (p.val (Fin.tail u)))).val 1) := by
  rw [quotientGenLoop_apply, collapse_characteristic]

theorem quotientHom_mk (n : ℕ) (hn : 0 < n) (d : ℕ) [NeZero d]
    (p : GenLoop (Fin d) (Boundary n) (corner n hn)) :
    quotientHom n hn d (Quotient.mk _ p) = Quotient.mk _ (quotientGenLoop n hn p) := rfl

theorem quotientHom_eq_currying (n : ℕ) (hn : 0 < n) (d : ℕ) [NeZero d]
    (c : π_ d (Boundary n) (corner n hn)) :
    quotientHom n hn d c = GeneralizedLoopCurrying.homotopyMulEquiv d (spherePole (n + n))
      (HigherHomotopy.map (N := Fin d) (sphereLoops n hn) (sphereLoops_corner n hn) c) := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

theorem connecting_quotientGenLoop (n d : ℕ) [NeZero d]
    (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n)
    (p : GenLoop (Fin d) (Boundary n) (corner n (by omega))) :
    EHP.connectingHomMetastable n d hn hdn
      (CubicalSphereSuspension.hom (d + 1) (n + n)
        (Quotient.mk _ (quotientGenLoop n (by omega) p))) =
      Quotient.mk _ (HigherHomotopy.genLoopMap (attaching n)
        (attaching_corner n (by omega)) p) := by
  rw [← quotientHom_mk n (by omega) d p]
  exact connecting_quotientHom n d hn hdn (Quotient.mk _ p)

end NoExoticSixSphere.JamesSphere.CellBoundary
