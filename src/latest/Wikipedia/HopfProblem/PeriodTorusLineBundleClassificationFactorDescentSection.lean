import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopologicalCover
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Native coordinates of a section on the universal-cover pullback

An actual analytic section of the native pullback gives an analytic map to
the original bundle's total space.  Its coefficients in the original native
charts are analytic, transform by the native scalar transitions, and are
nonzero when the section is nowhere zero.  Scalar multiplication of this
section gives the analytic map used for descent to a factor bundle.
-/

noncomputable section

open Bundle Filter Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent

open PeriodTorusLineBundleClassificationNative
open PeriodTorusLineBundleClassificationTopological

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable (p : PeriodDomain) (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC]

/-- An actual analytic section of the native universal-cover pullback. -/
abbrev CoverSection := ContMDiffSection IC ℂ ω (universalCoverPullback p V)

variable {p V}

@[simp]
theorem quotient_add_lattice (z : ComplexPlane₂) (l : p.lattice) :
    p.lattice.mkQ (z + l) = p.lattice.mkQ z := by
  have hl : p.lattice.mkQ (l : ComplexPlane₂) = 0 :=
    (Submodule.Quotient.mk_eq_zero p.lattice).mpr l.property
  rw [map_add, hl, add_zero]

/-- Forget only the pullback base coordinate, retaining the actual section
value in the original bundle fibre. -/
def sectionMap (s : CoverSection p V) (z : ComplexPlane₂) : TotalSpace ℂ V :=
  ⟨p.lattice.mkQ z, s z⟩

omit [∀ x, Module ℂ (V x)] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC] in
@[simp]
theorem sectionMap_proj (s : CoverSection p V) (z : ComplexPlane₂) :
    (sectionMap s z).proj = p.lattice.mkQ z := rfl

omit [∀ x, Module ℂ (V x)] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC] in
/-- The pullback's native fibre chart is definitionally the original native
chart composed with the actual pullback projection. -/
theorem sectionMap_contMDiff (s : CoverSection p V) :
    ContMDiff IC ((IC).prod I₁) ω (sectionMap s) := by
  intro z
  refine Bundle.contMDiffAt_totalSpace.mpr
    ⟨p.torus_projection_holomorphic.contMDiffAt, ?_⟩
  exact (Bundle.contMDiffAt_section z).mp (s.contMDiff z)

/-- The section's scalar coefficient in the original native chart. -/
def coefficient (s : CoverSection p V) (i : p.Torus) (z : ComplexPlane₂) : ℂ :=
  (nativeTriv V i (sectionMap s z)).2

omit [ContMDiffVectorBundle ω ℂ V IC] in
theorem coefficient_eq_linearEquivAt (s : CoverSection p V)
    (i : p.Torus) (z : ComplexPlane₂)
    (hi : p.lattice.mkQ z ∈ (nativeTriv V i).baseSet) :
    coefficient s i z = (nativeTriv V i).linearEquivAt ℂ (p.lattice.mkQ z) hi (s z) :=
  rfl

omit [∀ x, Module ℂ (V x)] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC] in
theorem sectionMap_localTriv (s : CoverSection p V) (i : p.Torus)
    (z : ComplexPlane₂) (hi : p.lattice.mkQ z ∈ (nativeTriv V i).baseSet) :
    nativeTriv V i (sectionMap s z) = (p.lattice.mkQ z, coefficient s i z) :=
  Prod.ext ((nativeTriv V i).coe_fst' hi) rfl

theorem coefficient_contMDiffAt (s : CoverSection p V) (i : p.Torus)
    (z : ComplexPlane₂) (hi : p.lattice.mkQ z ∈ (nativeTriv V i).baseSet) :
    ContMDiffAt IC I₁ ω (coefficient s i) z :=
  (((nativeTriv V i).contMDiffAt_iff ((nativeTriv V i).mem_source.mpr hi)).mp
    (sectionMap_contMDiff s z)).2

omit [ContMDiffVectorBundle ω ℂ V IC] in
theorem coefficient_ne_zero (s : CoverSection p V) (hne : ∀ z, s z ≠ 0)
    (i : p.Torus) (z : ComplexPlane₂)
    (hi : p.lattice.mkQ z ∈ (nativeTriv V i).baseSet) :
    coefficient s i z ≠ 0 := by
  rw [coefficient_eq_linearEquivAt s i z hi]
  intro h
  apply hne z
  exact ((nativeTriv V i).linearEquivAt ℂ (p.lattice.mkQ z) hi).injective
    (h.trans (map_zero _).symm)

omit [ContMDiffVectorBundle ω ℂ V IC] in
/-- The coefficient transforms by the original native transition scalar. -/
theorem coefficient_change (s : CoverSection p V) (i j : p.Torus)
    (z : ComplexPlane₂)
    (hi : p.lattice.mkQ z ∈ (nativeTriv V i).baseSet)
    (hj : p.lattice.mkQ z ∈ (nativeTriv V j).baseSet) :
    (scalarTransition V i j (p.lattice.mkQ z) : ℂ) * coefficient s i z =
      coefficient s j z := by
  rw [scalarTransition_coe, ← coordChange_apply V,
    (nativeTriv V i).coordChangeL_apply (nativeTriv V j) ⟨hi, hj⟩]
  change (nativeTriv V j
    ⟨p.lattice.mkQ z, (nativeTriv V i).symm (p.lattice.mkQ z)
      ((nativeTriv V i ⟨p.lattice.mkQ z, s z⟩).2)⟩).2 =
    (nativeTriv V j ⟨p.lattice.mkQ z, s z⟩).2
  exact congrArg (fun v : V (p.lattice.mkQ z) =>
    (nativeTriv V j ⟨p.lattice.mkQ z, v⟩).2)
      ((nativeTriv V i).symm_apply_apply_mk hi (s z))

/-- Multiply the actual pullback section by a complex scalar and regard
the resulting vector as an element of the original total space. -/
def coverScalarMap (s : CoverSection p V) (u : ComplexPlane₂ × ℂ) : TotalSpace ℂ V :=
  ⟨p.lattice.mkQ u.1, u.2 • s u.1⟩

omit [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC] in
@[simp]
theorem coverScalarMap_proj (s : CoverSection p V) (u : ComplexPlane₂ × ℂ) :
    (coverScalarMap s u).proj = p.lattice.mkQ u.1 := rfl

omit [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC] in
@[simp]
theorem coverScalarMap_zero (s : CoverSection p V) (z : ComplexPlane₂) :
    coverScalarMap s (z, 0) = ⟨p.lattice.mkQ z, (0 : V (p.lattice.mkQ z))⟩ := by
  exact congrArg (fun v : V (p.lattice.mkQ z) =>
    (⟨p.lattice.mkQ z, v⟩ : TotalSpace ℂ V)) (zero_smul ℂ (s z))

omit [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC] in
@[simp]
theorem coverScalarMap_one (s : CoverSection p V) (z : ComplexPlane₂) :
    coverScalarMap s (z, 1) = sectionMap s z := by
  simp [coverScalarMap, sectionMap]

omit [ContMDiffVectorBundle ω ℂ V IC] in
theorem coverScalarMap_localTriv (s : CoverSection p V) (i : p.Torus)
    (u : ComplexPlane₂ × ℂ)
    (hi : p.lattice.mkQ u.1 ∈ (nativeTriv V i).baseSet) :
    nativeTriv V i (coverScalarMap s u) =
      (p.lattice.mkQ u.1, u.2 * coefficient s i u.1) := by
  refine Prod.ext ((nativeTriv V i).coe_fst' hi) ?_
  change (nativeTriv V i).linearEquivAt ℂ (p.lattice.mkQ u.1) hi (u.2 • s u.1) =
    u.2 * (nativeTriv V i).linearEquivAt ℂ (p.lattice.mkQ u.1) hi (s u.1)
  exact ((nativeTriv V i).linearEquivAt ℂ (p.lattice.mkQ u.1) hi).map_smul u.2 (s u.1)

/-- Analyticity is proved in the original native charts; no holomorphic
projection from the pullback total space is assumed. -/
theorem coverScalarMap_contMDiff (s : CoverSection p V) :
    ContMDiff (modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)) ((IC).prod I₁) ω
      (coverScalarMap s) := by
  intro u
  have hfst : ContMDiffAt (modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)) IC ω
      (Prod.fst : ComplexPlane₂ × ℂ → ComplexPlane₂) u :=
    contDiff_fst.contMDiff.contMDiffAt
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨p.torus_projection_holomorphic.contMDiffAt.comp u hfst, ?_⟩
  let i := p.lattice.mkQ u.1
  have hi : p.lattice.mkQ u.1 ∈ (nativeTriv V i).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt ℂ V i
  change ContMDiffAt (modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)) I₁ ω
    (fun v => (nativeTriv V i (coverScalarMap s v)).2) u
  have hc := coefficient_contMDiffAt s i u.1 hi
  have hmul : ContMDiffAt (modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)) I₁ ω
      (fun v : ComplexPlane₂ × ℂ => v.2 * coefficient s i v.1) u :=
    (contDiffAt_snd.mul (hc.contDiffAt.comp u contDiffAt_fst)).contMDiffAt
  apply hmul.congr_of_eventuallyEq
  have hq : ContinuousAt (fun v : ComplexPlane₂ × ℂ => p.lattice.mkQ v.1) u :=
    p.lattice.continuous_mkQ.continuousAt.comp continuous_fst.continuousAt
  filter_upwards [hq ((nativeTriv V i).open_baseSet.mem_nhds hi)] with v hv
  exact congrArg Prod.snd (coverScalarMap_localTriv s i v hv)

omit [ContMDiffVectorBundle ω ℂ V IC] in
theorem coverScalarMap_fiber_injective (s : CoverSection p V)
    (hne : ∀ z, s z ≠ 0) (z : ComplexPlane₂) :
    Function.Injective (fun c : ℂ => coverScalarMap s (z, c)) := by
  intro c d h
  let i := p.lattice.mkQ z
  have hi : p.lattice.mkQ z ∈ (nativeTriv V i).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt ℂ V i
  have hc := congrArg (fun v : TotalSpace ℂ V => (nativeTriv V i v).2) h
  rw [coverScalarMap_localTriv s i (z, c) hi,
    coverScalarMap_localTriv s i (z, d) hi] at hc
  exact mul_right_cancel₀ (coefficient_ne_zero s hne i z hi) hc

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent
