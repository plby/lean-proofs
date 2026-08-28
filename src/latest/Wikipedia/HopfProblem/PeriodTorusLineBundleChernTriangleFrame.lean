import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCoverLifts
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniquenessCoordinates

/-!
# A genuine native frame on every lifted singular simplex

The actual covering lift of a singular simplex gives a continuous scalar
coordinate map into the original native Appell--Humbert bundle. Its restriction
to each fibre is the already proved covering-coordinate linear equivalence.
The scalar-one vector is a nonzero frame on the whole simplex, and the scalar
coordinate is literal multiplication of this native frame. All topologies and
linear structures here are the existing native ones.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationUniqueness
open ChernCover FirstHurewicz Bundle Topology

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- Scalar coordinates along the genuine simplex lift, in the original native total space. -/
def nativeSimplexCoordinateMap {n : ℕ} (σ : SingularSimplex p.Torus n) :
    C(Simplex n × ℂ, (Core.data F).core.TotalSpace) where
  toFun u := Core.fromAssociated F (associatedMap F (simplexLift p σ u.1, u.2))
  continuous_toFun := (Core.fromAssociated_comp_holomorphic F).continuous.comp
    (((simplexLift p σ).continuous.comp continuous_fst).prodMk continuous_snd)

@[simp] theorem nativeSimplexCoordinateMap_apply {n : ℕ}
    (σ : SingularSimplex p.Torus n) (s : Simplex n) (c : ℂ) :
    nativeSimplexCoordinateMap F σ (s, c) =
      Core.fromAssociated F (associatedMap F (simplexLift p σ s, c)) := rfl

/-- This is a map over the original singular simplex, not over an assigned base. -/
@[simp] theorem nativeSimplexCoordinateMap_proj {n : ℕ}
    (σ : SingularSimplex p.Torus n) (s : Simplex n) (c : ℂ) :
    (nativeSimplexCoordinateMap F σ (s, c)).proj = σ s :=
  simplexLift_projection p σ s

/-- The original fibre's complex-linear equivalence supplied by its covering coordinates. -/
def nativeSimplexFiberEquiv {n : ℕ} (σ : SingularSimplex p.Torus n) (s : Simplex n) :
    ℂ ≃ₗ[ℂ] (Core.data F).core.Fiber (σ s) :=
  coverFiberEquiv F (simplexLift p σ s)

/-- The fibre equivalence is exactly the previously defined native total-space map. -/
theorem nativeSimplexCoordinateMap_eq {n : ℕ}
    (σ : SingularSimplex p.Torus n) (s : Simplex n) (c : ℂ) :
    nativeSimplexCoordinateMap F σ (s, c) =
      ⟨σ s, nativeSimplexFiberEquiv F σ s c⟩ := by
  rw [nativeSimplexCoordinateMap_apply, fromAssociated_map]
  exact Bundle.TotalSpace.ext (simplexLift_projection p σ s) HEq.rfl

@[simp] theorem nativeSimplexCoordinateMap_fiber {n : ℕ}
    (σ : SingularSimplex p.Torus n) (s : Simplex n) (c : ℂ) :
    (nativeSimplexCoordinateMap F σ (s, c)).2 = nativeSimplexFiberEquiv F σ s c := by
  rw [nativeSimplexCoordinateMap_eq]

/-- The quotient comparison identifies this linear equivalence with the actual scalar `c`. -/
theorem nativeSimplexFiberEquiv_toAssociated {n : ℕ}
    (σ : SingularSimplex p.Torus n) (s : Simplex n) (c : ℂ) :
    Core.toAssociated F ⟨σ s, nativeSimplexFiberEquiv F σ s c⟩ =
      associatedMap F (simplexLift p σ s, c) := by
  rw [← nativeSimplexCoordinateMap_eq, nativeSimplexCoordinateMap_apply,
    Core.toAssociated_fromAssociated]

/-- Inverse fibre coordinates are the original quotient's proved scalar coordinates. -/
theorem nativeSimplexFiberEquiv_symm_eq_fibreCoordinate {n : ℕ}
    (σ : SingularSimplex p.Torus n) (s : Simplex n)
    (v : (Core.data F).core.Fiber (σ s)) :
    (nativeSimplexFiberEquiv F σ s).symm v =
      fibreCoordinate F (simplexLift p σ s) (Core.toAssociated F ⟨σ s, v⟩)
        ((Core.projection_toAssociated F _).trans (simplexLift_projection p σ s).symm) := by
  apply associatedMap_fibre_injective F (simplexLift p σ s)
  dsimp only
  rw [associatedMap_fibreCoordinate]
  simpa only [LinearEquiv.apply_symm_apply] using
    (nativeSimplexFiberEquiv_toAssociated F σ s ((nativeSimplexFiberEquiv F σ s).symm v)).symm

/-- The actual scalar-one vector in the original native fibre over the simplex point. -/
def nativeSimplexFrame {n : ℕ} (σ : SingularSimplex p.Torus n) (s : Simplex n) :
    (Core.data F).core.Fiber (σ s) :=
  nativeSimplexFiberEquiv F σ s 1

/-- This whole-simplex frame is nonzero at every point, including the boundary. -/
theorem nativeSimplexFrame_ne_zero {n : ℕ}
    (σ : SingularSimplex p.Torus n) (s : Simplex n) : nativeSimplexFrame F σ s ≠ 0 := by
  intro h
  apply one_ne_zero (α := ℂ)
  apply (nativeSimplexFiberEquiv F σ s).injective
  simpa only [map_zero, nativeSimplexFrame] using h

/-- The native frame is a continuous section over the entire actual simplex. -/
theorem nativeSimplexFrame_continuous {n : ℕ} (σ : SingularSimplex p.Torus n) :
    Continuous (fun s : Simplex n =>
      (⟨σ s, nativeSimplexFrame F σ s⟩ : (Core.data F).core.TotalSpace)) := by
  have h := (nativeSimplexCoordinateMap F σ).continuous.comp
    (continuous_id.prodMk (continuous_const (y := (1 : ℂ))))
  exact h.congr fun s => nativeSimplexCoordinateMap_eq F σ s 1

/-- A bundled version of the actual continuous native simplex frame. -/
def nativeSimplexFrameSection {n : ℕ} (σ : SingularSimplex p.Torus n) :
    C(Simplex n, (Core.data F).core.TotalSpace) :=
  ⟨fun s => ⟨σ s, nativeSimplexFrame F σ s⟩, nativeSimplexFrame_continuous F σ⟩

@[simp] theorem nativeSimplexFrameSection_proj {n : ℕ}
    (σ : SingularSimplex p.Torus n) (s : Simplex n) :
    (nativeSimplexFrameSection F σ s).proj = σ s := rfl

/-- The linear equivalence acts by genuine scalar multiplication of the native frame. -/
theorem nativeSimplexFiberEquiv_eq_smul_frame {n : ℕ}
    (σ : SingularSimplex p.Torus n) (s : Simplex n) (c : ℂ) :
    nativeSimplexFiberEquiv F σ s c = c • nativeSimplexFrame F σ s := by
  simpa only [smul_eq_mul, mul_one, nativeSimplexFrame] using
    (nativeSimplexFiberEquiv F σ s).map_smul c (1 : ℂ)

/-- The whole scalar map is exactly scalar multiplication of the actual native frame. -/
theorem nativeSimplexCoordinateMap_eq_smul_frame {n : ℕ}
    (σ : SingularSimplex p.Torus n) (s : Simplex n) (c : ℂ) :
    nativeSimplexCoordinateMap F σ (s, c) =
      ⟨σ s, c • nativeSimplexFrame F σ s⟩ := by
  rw [nativeSimplexCoordinateMap_eq, nativeSimplexFiberEquiv_eq_smul_frame]

/-- The scalar-one coordinate map is nonzero as an original native vector. -/
theorem nativeSimplexCoordinateMap_one_ne_zero {n : ℕ}
    (σ : SingularSimplex p.Torus n) (s : Simplex n) :
    (nativeSimplexCoordinateMap F σ (s, 1)).2 ≠ 0 := by
  rw [nativeSimplexCoordinateMap_fiber]
  exact nativeSimplexFrame_ne_zero F σ s

/-- Every original fibre vector has one unique scalar in this whole-simplex frame. -/
theorem nativeSimplexCoordinateMap_existsUnique {n : ℕ}
    (σ : SingularSimplex p.Torus n) (s : Simplex n)
    (v : (Core.data F).core.Fiber (σ s)) :
    ∃! c : ℂ, nativeSimplexCoordinateMap F σ (s, c) = ⟨σ s, v⟩ := by
  refine ⟨(nativeSimplexFiberEquiv F σ s).symm v, ?_, ?_⟩
  · dsimp only
    rw [nativeSimplexCoordinateMap_eq, LinearEquiv.apply_symm_apply]
  · intro c hc
    apply (nativeSimplexFiberEquiv F σ s).injective
    rw [LinearEquiv.apply_symm_apply]
    exact Bundle.TotalSpace.mk_injective (σ s)
      ((nativeSimplexCoordinateMap_eq F σ s c).symm.trans hc)

/-- In an original local trivialization the scalar map has the actual factor multiplier. -/
theorem nativeSimplexCoordinateMap_localTriv {n : ℕ}
    (σ : SingularSimplex p.Torus n) (i : p.Torus) (s : Simplex n) (c : ℂ) (l : p.lattice)
    (hs : σ s ∈ Core.baseSet p i)
    (hl : Core.lift p i (σ s) = simplexLift p σ s + l) :
    (Core.data F).core.localTriv i (nativeSimplexCoordinateMap F σ (s, c)) =
      (σ s, (F.factor l (simplexLift p σ s) : ℂ) * c) := by
  have hs' : p.lattice.mkQ (simplexLift p σ s) ∈ Core.baseSet p i := by
    simpa only [simplexLift_projection] using hs
  have hl' : Core.lift p i (p.lattice.mkQ (simplexLift p σ s)) =
      simplexLift p σ s + l := by
    simpa only [simplexLift_projection] using hl
  simpa only [nativeSimplexCoordinateMap_apply, simplexLift_projection] using
    Core.localTriv_fromAssociated_map F i (simplexLift p σ s) c l hs' hl'

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
