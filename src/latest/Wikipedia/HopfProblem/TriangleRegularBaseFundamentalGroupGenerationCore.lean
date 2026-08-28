import Wikipedia.HopfProblem.SimplyConnectedCover
import Mathlib.Topology.Sets.Opens

/-!
# Loop classes associated to a two-set simply connected cover

The loops below are actual paths modulo endpoint-preserving homotopy.
Their constancy along a connected overlap uses homotopies inside the
two given open sets.  No presentation of the ambient fundamental group
is part of the input.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroup

variable {X : Type*} [TopologicalSpace X]

open Path.Homotopic.Quotient

theorem quotient_symm_trans_cancel {x y z : X}
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) :
    p.symm.trans (p.trans q) = q := by
  rw [← trans_assoc, symm_trans, refl_trans]

theorem quotient_trans_symm_cancel {x y z : X}
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient x z) :
    p.trans (p.symm.trans q) = q := by
  rw [← trans_assoc, trans_symm, refl_trans]

theorem quotient_trans_right_cancel {x y z : X}
    {p q : Path.Homotopic.Quotient x y} (r : Path.Homotopic.Quotient y z)
    (h : p.trans r = q.trans r) : p = q := by
  have h' := congrArg (fun a : Path.Homotopic.Quotient x z => a.trans r.symm) h
  simpa only [trans_assoc, trans_symm, trans_refl] using h'

/-- Close a path by a chosen family of paths from a common basepoint. -/
def basedLoop {o : X} (F : ∀ x, Path.Homotopic.Quotient o x)
    {x y : X} (p : Path.Homotopic.Quotient x y) : FundamentalGroup X o :=
  ((F x).trans p).trans (F y).symm

/-- Compare two paths from the same basepoint to the same endpoint. -/
def pathDifference {o x : X}
    (p q : Path.Homotopic.Quotient o x) : FundamentalGroup X o :=
  p.trans q.symm

@[simp] theorem basedLoop_refl {o : X} (F : ∀ x, Path.Homotopic.Quotient o x) (x : X) :
    basedLoop F (refl x) = 1 := by
  simp only [basedLoop, trans_refl, trans_symm, FundamentalGroup.one_def]

/-- Fundamental-group multiplication is reverse path concatenation. -/
theorem basedLoop_trans {o x y z : X} (F : ∀ x, Path.Homotopic.Quotient o x)
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) :
    basedLoop F (p.trans q) = basedLoop F q * basedLoop F p := by
  simp only [basedLoop, FundamentalGroup.mul_def, trans_assoc,
    quotient_symm_trans_cancel]

/-- Comparison with paths chosen in one simply connected chart. -/
theorem basedLoop_comparison {o x y : X} (F : ∀ z, Path.Homotopic.Quotient o z)
    (a : Path.Homotopic.Quotient o x) (b : Path.Homotopic.Quotient o y)
    (p : Path.Homotopic.Quotient x y) (h : a.trans p = b) :
    basedLoop F p = (pathDifference (F y) b)⁻¹ * pathDifference (F x) a := by
  apply (@eq_inv_mul_iff_mul_eq (FundamentalGroup X o) _
    (basedLoop F p) (pathDifference (F y) b) (pathDifference (F x) a)).2
  apply quotient_trans_right_cancel b
  simp only [basedLoop, pathDifference, FundamentalGroup.mul_def, trans_assoc,
    quotient_symm_trans_cancel, symm_trans, trans_refl]
  rw [← h, quotient_symm_trans_cancel]

/-- Actual simply connected open sets with a common basepoint. -/
structure TwoSimplyConnectedCover (X : Type*) [TopologicalSpace X] where
  U : TopologicalSpace.Opens X
  V : TopologicalSpace.Opens X
  cover : (U : Set X) ∪ V = univ
  simplyU : IsSimplyConnected (U : Set X)
  simplyV : IsSimplyConnected (V : Set X)
  base : X
  baseU : base ∈ U
  baseV : base ∈ V

namespace TwoSimplyConnectedCover

variable (D : TwoSimplyConnectedCover X)

def pathU (x : X) (hx : x ∈ D.U) : Path D.base x :=
  (D.simplyU.isPathConnected.joinedIn D.base D.baseU x hx).somePath

def pathV (x : X) (hx : x ∈ D.V) : Path D.base x :=
  (D.simplyV.isPathConnected.joinedIn D.base D.baseV x hx).somePath

theorem pathU_mem (x : X) (hx : x ∈ D.U) (t : I) : D.pathU x hx t ∈ D.U :=
  JoinedIn.somePath_mem _ t

theorem pathV_mem (x : X) (hx : x ∈ D.V) (t : I) : D.pathV x hx t ∈ D.V :=
  JoinedIn.somePath_mem _ t

theorem pathU_trans {x y : X} (hx : x ∈ D.U) (hy : y ∈ D.U)
    (p : Path x y) (hp : ∀ t, p t ∈ D.U) :
    (Path.Homotopic.Quotient.mk (D.pathU x hx)).trans (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk (D.pathU y hy) := by
  rw [← mk_trans, eq]
  exact SimplyConnectedCover.homotopic_of_mem D.simplyU _ _
    (SimplyConnectedCover.trans_mem _ _ (D.pathU_mem x hx) hp) (D.pathU_mem y hy)

theorem pathV_trans {x y : X} (hx : x ∈ D.V) (hy : y ∈ D.V)
    (p : Path x y) (hp : ∀ t, p t ∈ D.V) :
    (Path.Homotopic.Quotient.mk (D.pathV x hx)).trans (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk (D.pathV y hy) := by
  rw [← mk_trans, eq]
  exact SimplyConnectedCover.homotopic_of_mem D.simplyV _ _
    (SimplyConnectedCover.trans_mem _ _ (D.pathV_mem x hx) hp) (D.pathV_mem y hy)

/-- Go to an overlap point through `U` and return through `V`. -/
def switchClass (x : X) (hxU : x ∈ D.U) (hxV : x ∈ D.V) :
    FundamentalGroup X D.base :=
  (Path.Homotopic.Quotient.mk (D.pathU x hxU)).trans
    (Path.Homotopic.Quotient.mk (D.pathV x hxV)).symm

/-- The two-chart loop is constant on every path component of the overlap. -/
theorem switchClass_eq_of_joinedIn {x y : X}
    (hxU : x ∈ D.U) (hxV : x ∈ D.V) (hyU : y ∈ D.U) (hyV : y ∈ D.V)
    (hxy : JoinedIn ((D.U : Set X) ∩ D.V) x y) :
    D.switchClass x hxU hxV = D.switchClass y hyU hyV := by
  let p := hxy.somePath
  have hU := D.pathU_trans hxU hyU p (fun t => (hxy.somePath_mem t).1)
  have hV := D.pathV_trans hxV hyV p (fun t => (hxy.somePath_mem t).2)
  apply quotient_trans_right_cancel (Path.Homotopic.Quotient.mk (D.pathV y hyV))
  change ((Path.Homotopic.Quotient.mk (D.pathU x hxU)).trans
      (Path.Homotopic.Quotient.mk (D.pathV x hxV)).symm).trans
      (Path.Homotopic.Quotient.mk (D.pathV y hyV)) =
    ((Path.Homotopic.Quotient.mk (D.pathU y hyU)).trans
      (Path.Homotopic.Quotient.mk (D.pathV y hyV)).symm).trans
      (Path.Homotopic.Quotient.mk (D.pathV y hyV))
  rw [trans_assoc, ← hV, quotient_symm_trans_cancel, hU]
  simp only [trans_assoc, symm_trans, trans_refl]

/-- The switch loop through the basepoint is null-homotopic. -/
@[simp] theorem switchClass_base : D.switchClass D.base D.baseU D.baseV = 1 := by
  have hU : Path.Homotopic.Quotient.mk (D.pathU D.base D.baseU) =
      Path.Homotopic.Quotient.refl D.base := by
    apply eq.mpr
    exact SimplyConnectedCover.homotopic_of_mem D.simplyU _ _
      (D.pathU_mem _ _) (fun _ => D.baseU)
  have hV : Path.Homotopic.Quotient.mk (D.pathV D.base D.baseV) =
      Path.Homotopic.Quotient.refl D.base := by
    apply eq.mpr
    exact SimplyConnectedCover.homotopic_of_mem D.simplyV _ _
      (D.pathV_mem _ _) (fun _ => D.baseV)
  simp only [switchClass, hU, hV, trans_symm, FundamentalGroup.one_def]

end TwoSimplyConnectedCover

end Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroup
