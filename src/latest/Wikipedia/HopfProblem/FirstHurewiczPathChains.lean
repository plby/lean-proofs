import Wikipedia.HopfProblem.FirstHurewiczChains
import Wikipedia.HopfProblem.FirstHurewiczHomotopySimplex

/-!
# Paths and homotopies in the actual singular chain complex

A path gives an actual singular one-chain. Its boundary is the difference
of its endpoint generators. The two triangles in a path-homotopy square
give the explicit singular two-chain comparing the two paths.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FirstHurewicz

variable {X : Type} [TopologicalSpace X] {x y z : X}

def pointChain (x : X) : Chains X 0 :=
  simplexChain X 0 (ContinuousMap.const (Simplex 0) x)

/-- The actual singular one-chain associated to a path. -/
def pathChain (p : Path x y) : Chains X 1 := simplexChain X 1 (pathSimplex p)

theorem boundaryOne_pathChain (p : Path x y) :
    boundaryOne X (pathChain p) = pointChain y - pointChain x := by
  rw [pathChain, boundaryOne_simplex, pathSimplex_face_zero, pathSimplex_face_one]
  rfl

/-- In particular, a based loop is an actual singular one-cycle. -/
theorem boundaryOne_loop (p : Path x x) : boundaryOne X (pathChain p) = 0 := by
  rw [boundaryOne_pathChain, sub_self]

/-- The actual singular two-chain encoding path concatenation. -/
def concatChain (p : Path x y) (q : Path y z) : Chains X 2 :=
  simplexChain X 2 (concatSimplex p q)

theorem boundaryTwo_concatChain (p : Path x y) (q : Path y z) :
    boundaryTwo X (concatChain p q) = pathChain q - pathChain (p.trans q) + pathChain p := by
  rw [concatChain, boundaryTwo_simplex, concatSimplex_face_zero,
    concatSimplex_face_one, concatSimplex_face_two]
  rfl

def constantEdgeChain (x : X) : Chains X 1 :=
  simplexChain X 1 (ContinuousMap.const (Simplex 1) x)

def constantTriangleChain (x : X) : Chains X 2 :=
  simplexChain X 2 (ContinuousMap.const (Simplex 2) x)

/-- A constant edge is the boundary of the constant triangle. -/
theorem boundaryTwo_constantTriangleChain (x : X) :
    boundaryTwo X (constantTriangleChain x) = constantEdgeChain x := by
  rw [constantTriangleChain, boundaryTwo_simplex]
  change constantEdgeChain x - constantEdgeChain x + constantEdgeChain x = _
  abel

@[simp] theorem pathChain_refl (x : X) : pathChain (Path.refl x) = constantEdgeChain x := rfl

/-- The signed pair of actual singular triangles in the homotopy square. -/
def homotopyChain {p q : Path x y} (H : p.Homotopy q) : Chains X 2 :=
  simplexChain X 2 (homotopyLowerSimplex H) - simplexChain X 2 (homotopyUpperSimplex H)

/-- The shared diagonal cancels. The remaining endpoint terms are the
constant edges appearing on the two horizontal sides of the square. -/
theorem boundaryTwo_homotopyChain {p q : Path x y} (H : p.Homotopy q) :
    boundaryTwo X (homotopyChain H) =
      pathChain p - pathChain q + constantEdgeChain y - constantEdgeChain x := by
  rw [homotopyChain, map_sub, boundaryTwo_simplex, boundaryTwo_simplex,
    homotopyLowerSimplex_face_zero, homotopyLowerSimplex_face_one,
    homotopyLowerSimplex_face_two, homotopyUpperSimplex_face_zero,
    homotopyUpperSimplex_face_one, homotopyUpperSimplex_face_two]
  change constantEdgeChain y - simplexChain X 1 (homotopyDiagonalSimplex H) + pathChain p -
      (pathChain q - simplexChain X 1 (homotopyDiagonalSimplex H) + constantEdgeChain x) = _
  abel

/-- An explicit boundary witness for path-homotopy invariance, with no
relative-cycle or homology comparison assumption. -/
def correctedHomotopyChain {p q : Path x y} (H : p.Homotopy q) : Chains X 2 :=
  homotopyChain H - constantTriangleChain y + constantTriangleChain x

theorem boundaryTwo_correctedHomotopyChain {p q : Path x y} (H : p.Homotopy q) :
    boundaryTwo X (correctedHomotopyChain H) = pathChain p - pathChain q := by
  rw [correctedHomotopyChain, map_add, map_sub, boundaryTwo_homotopyChain,
    boundaryTwo_constantTriangleChain, boundaryTwo_constantTriangleChain]
  abel

/-- For based loops the endpoint terms already cancel before correction. -/
theorem boundaryTwo_loopHomotopy {p q : Path x x} (H : p.Homotopy q) :
    boundaryTwo X (homotopyChain H) = pathChain p - pathChain q := by
  rw [boundaryTwo_homotopyChain]
  abel

end Wikipedia.HopfProblem.FirstHurewicz
