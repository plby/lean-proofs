import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupData
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupBaseChangeSquare

/-!
# Basepoint change preserves the actual fibre lattice column

An actual path in the original base parameter space gives the product
homotopy `(s, f) ↦ quotient (p s, f)`. Basepoint change along its constant
fibre-coordinate trajectory takes each included fibre loop to the same
loop at the other endpoint. For the period family this preserves the
original integral column exactly, with no deck correction or new marking.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F]

/-- Move the original fibre inclusion along an actual upstairs base path. -/
def fibreBasepointHomotopy {b₀ b₁ : B} (p : Path b₀ b₁) :
    ContinuousMap.Homotopy
      (⟨fibreInclusion G B F b₀, fibreInclusion_continuous G B F b₀⟩ :
        C(F, Space G B F))
      ⟨fibreInclusion G B F b₁, fibreInclusion_continuous G B F b₁⟩ where
  toFun x := quotient G B F (p x.1, x.2)
  continuous_toFun := (quotient_continuous G B F).comp
    ((p.continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left f := by
    change quotient G B F (p 0, f) = quotient G B F (b₀, f)
    rw [p.source]
  map_one_left f := by
    change quotient G B F (p 1, f) = quotient G B F (b₁, f)
    rw [p.target]

/-- The literal constant-fibre-coordinate path in the actual diagonal quotient. -/
def fibreBasepointPath (c : F) {b₀ b₁ : B} (p : Path b₀ b₁) :
    Path (fibreInclusion G B F b₀ c) (fibreInclusion G B F b₁ c) :=
  (fibreBasepointHomotopy (G := G) (F := F) p).evalAt c

@[simp] theorem fibreBasepointPath_apply (c : F) {b₀ b₁ : B} (p : Path b₀ b₁)
    (t : unitInterval) :
    fibreBasepointPath (G := G) c p t = quotient G B F (p t, c) := rfl

/-- Actual basepoint change along the product trajectory preserves the
same fibre homotopy class. No covering or fixed-point assumption is needed. -/
theorem fibreFundamentalGroupHom_baseChange (c : F) {b₀ b₁ : B} (p : Path b₀ b₁)
    (v : FundamentalGroup F c) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (fibreBasepointPath (G := G) c p)
        (fibreFundamentalGroupHom (G := G) b₀ c v) =
      fibreFundamentalGroupHom (G := G) b₁ c v :=
  fundamentalGroup_basepointChange_of_homotopy _ _
    (fibreBasepointHomotopy (G := G) (F := F) p) c v

end Wikipedia.HopfProblem.DiagonalQuotient

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

/-- The actual zero-section trajectory along an upstairs base path. -/
def zeroSectionPath {b₀ b₁ : B} (p : Path b₀ b₁) :
    Path (D.fundamentalGroupBasepoint b₀) (D.fundamentalGroupBasepoint b₁) :=
  DiagonalQuotient.fibreBasepointPath (G := TriangleGroup) (0 : RealTorus₄) p

@[simp] theorem zeroSectionPath_apply {b₀ b₁ : B} (p : Path b₀ b₁)
    (t : unitInterval) : D.zeroSectionPath p t = D.quotient (p t, 0) := rfl

/-- This trajectory is also the literal zero-section image of the projected path. -/
theorem zeroSectionPath_eq_sectionMap {b₀ b₁ : B} (p : Path b₀ b₁) :
    D.zeroSectionPath p =
      (p.map D.baseQuotient_continuous).map D.zeroSection_continuous := by
  ext t
  rfl

theorem flatFibreFundamentalGroupHom_baseChange {b₀ b₁ : B} (p : Path b₀ b₁)
    (v : FundamentalGroup RealTorus₄ 0) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (D.zeroSectionPath p)
        (D.flatFibreFundamentalGroupHom b₀ v) =
      D.flatFibreFundamentalGroupHom b₁ v :=
  DiagonalQuotient.fibreFundamentalGroupHom_baseChange
    (G := TriangleGroup) (0 : RealTorus₄) p v

/-- Moving the actual family basepoint along an upstairs path preserves
the original integral column `v` exactly. -/
theorem latticeFundamentalGroupHom_baseChange {b₀ b₁ : B} (p : Path b₀ b₁)
    (v : Multiplicative Lattice) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (D.zeroSectionPath p)
        (D.latticeFundamentalGroupHom b₀ v) =
      D.latticeFundamentalGroupHom b₁ v :=
  D.flatFibreFundamentalGroupHom_baseChange p (FlatTorus.fundamentalGroupEquiv.symm v)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
