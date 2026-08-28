import Wikipedia.HopfProblem.FundamentalGroupVanKampenLocal

/-!
# Agreement of the local path values on the actual overlap

The coherent based paths restrict to paths in the intersection.  Closing
an intersection path and including the resulting loop in either open
set gives exactly the two local closed loops.  Thus the standard
fundamental-group compatibility hypothesis gives the full local path
compatibility required by interval subdivision.
-/

noncomputable section

open Set Path.Homotopic.Quotient
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen

open TriangleRegularBaseFundamentalGroup

variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]

namespace TwoOpenCover

variable (D : TwoOpenCover X)

def overlapPath (x : D.overlap) : Path D.baseOverlapPoint x :=
  pathIn (S := (D.overlap : Set X)) (D.pathTo x.val) ⟨D.baseU, D.baseV⟩ x.property
    (fun t => ⟨D.pathTo_mem false x.val x.property.1 t,
      D.pathTo_mem true x.val x.property.2 t⟩)

theorem overlapPath_map_U (x : D.overlap) :
    (D.overlapPath x).map D.overlapToU.continuous =
      D.chartPath false (D.overlapToU x) := by
  ext t
  rfl

theorem overlapPath_map_V (x : D.overlap) :
    (D.overlapPath x).map D.overlapToV.continuous =
      D.chartPath true (D.overlapToV x) := by
  ext t
  rfl

def overlapClose {x y : D.overlap} (p : Path x y) : D.OverlapGroup :=
  basedLoop (fun x => Path.Homotopic.Quotient.mk (D.overlapPath x))
    (Path.Homotopic.Quotient.mk p)

theorem overlapHomU_close {x y : D.overlap} (p : Path x y) :
    D.overlapHomU (D.overlapClose p) =
      D.closePath false (p.map D.overlapToU.continuous) := by
  change Path.Homotopic.Quotient.mk
      ((((D.overlapPath x).trans p).trans (D.overlapPath y).symm).map
        D.overlapToU.continuous) =
    Path.Homotopic.Quotient.mk
      (((D.chartPath false (D.overlapToU x)).trans (p.map D.overlapToU.continuous)).trans
        (D.chartPath false (D.overlapToU y)).symm)
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm,
    D.overlapPath_map_U, D.overlapPath_map_U]
  rfl

theorem overlapHomV_close {x y : D.overlap} (p : Path x y) :
    D.overlapHomV (D.overlapClose p) =
      D.closePath true (p.map D.overlapToV.continuous) := by
  change Path.Homotopic.Quotient.mk
      ((((D.overlapPath x).trans p).trans (D.overlapPath y).symm).map
        D.overlapToV.continuous) =
    Path.Homotopic.Quotient.mk
      (((D.chartPath true (D.overlapToV x)).trans (p.map D.overlapToV.continuous)).trans
        (D.chartPath true (D.overlapToV y)).symm)
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm,
    D.overlapPath_map_V, D.overlapPath_map_V]
  rfl

theorem localValue_compatible_UV (fU : D.UGroup →* G) (fV : D.VGroup →* G)
    (hf : D.Compatible fU fV) {x y : X} (p : Path x y)
    (hU : ∀ t, p t ∈ D.U) (hV : ∀ t, p t ∈ D.V) :
    D.localValue fU fV false p hU = D.localValue fU fV true p hV := by
  have hxU : x ∈ D.U := by simpa using hU 0
  have hxV : x ∈ D.V := by simpa using hV 0
  have hyU : y ∈ D.U := by simpa using hU 1
  have hyV : y ∈ D.V := by simpa using hV 1
  let pI := pathIn (S := (D.overlap : Set X)) p ⟨hxU, hxV⟩ ⟨hyU, hyV⟩
    (fun t => ⟨hU t, hV t⟩)
  have hpU : pI.map D.overlapToU.continuous = pathIn p hxU hyU hU := by
    ext t
    rfl
  have hpV : pI.map D.overlapToV.continuous = pathIn p hxV hyV hV := by
    ext t
    rfl
  have h := DFunLike.congr_fun hf (D.overlapClose pI)
  change fU (D.overlapHomU (D.overlapClose pI)) =
    fV (D.overlapHomV (D.overlapClose pI)) at h
  have hU' := congrArg fU ((D.overlapHomU_close pI).trans
    (congrArg (D.closePath false) hpU))
  have hV' := congrArg fV ((D.overlapHomV_close pI).trans
    (congrArg (D.closePath true) hpV))
  exact congrArg (fun a : G => a⁻¹) (hU'.symm.trans (h.trans hV'))

theorem localValue_compatible (fU : D.UGroup →* G) (fV : D.VGroup →* G)
    (hf : D.Compatible fU fV) (i j : Bool) {x y : X} (p : Path x y)
    (hi : ∀ t, p t ∈ D.chart i) (hj : ∀ t, p t ∈ D.chart j) :
    D.localValue fU fV i p hi = D.localValue fU fV j p hj := by
  cases i <;> cases j
  · rfl
  · exact D.localValue_compatible_UV fU fV hf p hi hj
  · exact (D.localValue_compatible_UV fU fV hf p hj hi).symm
  · rfl

/-- The complete local transport data are constructed from the actual
compatible homomorphisms, rather than being assumed. -/
def localPathValue (fU : D.UGroup →* G) (fV : D.VGroup →* G)
    (hf : D.Compatible fU fV) : LocalPathValue (fun i => (D.chart i : Set X)) G where
  value := D.localValue fU fV
  refl := D.localValue_refl fU fV
  trans := D.localValue_trans fU fV
  subpath_mul := D.localValue_subpath_mul fU fV
  compatible := D.localValue_compatible fU fV hf

theorem localPathValue_homotopyInvariant (fU : D.UGroup →* G) (fV : D.VGroup →* G)
    (hf : D.Compatible fU fV) : (D.localPathValue fU fV hf).HomotopyInvariant :=
  D.localValue_homotopy fU fV

/-- On an actual based local loop the closing paths are constant, so the
local transport is exactly the inverse of the original group map. -/
theorem localValue_map_loop (fU : D.UGroup →* G) (fV : D.VGroup →* G)
    (i : Bool) (p : Path (D.baseChart i) (D.baseChart i)) :
    D.localValue fU fV i (p.map continuous_subtype_val) (fun t => (p t).property) =
      (D.chartHom fU fV i (Path.Homotopic.Quotient.mk p))⁻¹ := by
  unfold localValue
  apply congrArg (fun a : FundamentalGroup (D.chart i) (D.baseChart i) =>
    (D.chartHom fU fV i a)⁻¹)
  rw [D.closePath_loop]
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

end TwoOpenCover

end Wikipedia.HopfProblem.FundamentalGroupVanKampen
