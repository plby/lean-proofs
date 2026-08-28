import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCoordinates
import Wikipedia.HopfProblem.RiemannSphere
import Wikipedia.HopfProblem.ComplexRealManifold

/-!
# Native real-analytic charts for the normal-neighborhood construction

The real structures here use the unchanged toric and Riemann-sphere
atlases. Their original complex analytic transitions are real analytic.
The displayed partial diffeomorphisms retain the literal original affine
maps and coordinate inverses, with no replacement smooth structure.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open ToricCharts ToricFan

local notation "I₃" => 𝓘(ℝ, CoordinateSpace 3)
local notation "I₁" => 𝓘(ℝ, ℂ)
local notation "IP" => 𝓘(ℝ, Model)

/-- The unchanged native product atlas, with its transparent model-space spelling. -/
instance productChartedSpace : ChartedSpace Model (RiemannSphere × Fibre) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ Fibre) (RiemannSphere × Fibre))

local instance toricRealManifold : IsManifold I₃ ω ToricSpace.Space :=
  complexManifold_isRealManifold ToricSpace.Space ω

local instance sphereRealManifold : IsManifold I₁ ω RiemannSphere :=
  complexManifold_isRealManifold RiemannSphere ω

/-- The literal native toric parametrization as a real-analytic partial diffeomorphism. -/
def toricChartPartialDiffeomorph (a : Triangle) :
    PartialDiffeomorph I₃ I₃ (CoordinateSpace 3) ToricSpace.Space ω := by
  have he : (ToricSpace.parametrization a).symm ∈
      IsManifold.maximalAtlas I₃ ω ToricSpace.Space :=
    IsManifold.subset_maximalAtlas (mem_range_self a)
  exact {
    toPartialEquiv := (ToricSpace.parametrization a).toPartialEquiv
    open_source := (ToricSpace.parametrization a).open_source
    open_target := (ToricSpace.parametrization a).open_target
    contMDiffOn_toFun := contMDiffOn_symm_of_mem_maximalAtlas he
    contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas he }

@[simp] theorem toricChartPartialDiffeomorph_apply (a : Triangle) (z : CoordinateSpace 3) :
    toricChartPartialDiffeomorph a z = ToricSpace.inclusion a z := rfl

@[simp] theorem toricChartPartialDiffeomorph_source (a : Triangle) :
    (toricChartPartialDiffeomorph a).source = univ := rfl

/-- The original affine sphere chart, with its genuine inverse, over the real field. -/
def sphereChartPartialDiffeomorph (b : Bool) :
    PartialDiffeomorph I₁ I₁ ℂ RiemannSphere ω := by
  have he : (RiemannSphere.standardCharts.parametrization b).symm ∈
      IsManifold.maximalAtlas I₁ ω RiemannSphere :=
    IsManifold.subset_maximalAtlas (mem_range_self b)
  exact {
    toPartialEquiv := (RiemannSphere.standardCharts.parametrization b).toPartialEquiv
    open_source := (RiemannSphere.standardCharts.parametrization b).open_source
    open_target := (RiemannSphere.standardCharts.parametrization b).open_target
    contMDiffOn_toFun := contMDiffOn_symm_of_mem_maximalAtlas he
    contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas he }

/-- The original base affine chart times the unchanged normal fibre. -/
def baseProductParametrization (b : Bool) :
    PartialDiffeomorph IP IP Model (RiemannSphere × Fibre) ω := by
  let e := (RiemannSphere.standardCharts.parametrization b).prod
    (OpenPartialHomeomorph.refl Fibre)
  refine {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := ?_ }
  · have hf : ContMDiffOn IP I₁ ω (fun q : Model => q.1) e.source :=
      (ContinuousLinearMap.fst ℝ ℂ Fibre).contDiff.contMDiff.contMDiffOn
    have hs : ContMDiffOn IP 𝓘(ℝ, Fibre) ω (fun q : Model => q.2) e.source :=
      (ContinuousLinearMap.snd ℝ ℂ Fibre).contDiff.contMDiff.contMDiffOn
    have hbase := (sphereChartPartialDiffeomorph b).contMDiffOn_toFun.comp hf
      (fun _ hx => hx.1)
    conv =>
      arg 2
      rw [modelWithCornersSelf_prod]
    change ContMDiffOn IP ((I₁).prod 𝓘(ℝ, Fibre)) ω
      (fun q : Model => (sphereChartPartialDiffeomorph b q.1, q.2)) e.source
    exact hbase.prodMk hs
  · have hf : ContMDiffOn IP I₁ ω (fun q : RiemannSphere × Fibre => q.1) e.target := by
      simpa only [← modelWithCornersSelf_prod] using
        (contMDiffOn_fst (I := I₁) (J := 𝓘(ℝ, Fibre)) (n := ω) (s := e.target))
    have hs : ContMDiffOn IP 𝓘(ℝ, Fibre) ω
        (fun q : RiemannSphere × Fibre => q.2) e.target := by
      simpa only [← modelWithCornersSelf_prod] using
        (contMDiffOn_snd (I := I₁) (J := 𝓘(ℝ, Fibre)) (n := ω) (s := e.target))
    apply (contMDiffOn_prod_module_iff _).mpr
    exact ⟨(sphereChartPartialDiffeomorph b).contMDiffOn_invFun.comp hf
      (fun _ hx => hx.1), hs⟩

@[simp] theorem baseProductParametrization_apply (b : Bool) (q : Model) :
    baseProductParametrization b q =
      (RiemannSphere.standardCharts.affineMap b q.1, q.2) := rfl

@[simp] theorem baseProductParametrization_source (b : Bool) :
    (baseProductParametrization b).source = univ := by
  ext q
  change (q.1 ∈ (univ : Set ℂ) ∧ q.2 ∈ (univ : Set Fibre)) ↔ q ∈ univ
  simp only [mem_univ, and_self]

@[simp] theorem baseProductParametrization_target (b : Bool) :
    (baseProductParametrization b).target =
      range (RiemannSphere.standardCharts.affineMap b) ×ˢ (univ : Set Fibre) := by
  change (RiemannSphere.standardCharts.parametrization b).target ×ˢ (univ : Set Fibre) = _
  rw [TwoAffineCharts.parametrization_target]

/-- The actual toric parametrization after the explicit normal-coordinate inverse. -/
def normalChartParametrization (b : Bool) :
    PartialDiffeomorph IP I₃ Model ToricSpace.Space ω :=
  (chartCoordinates b).symm.toPartialDiffeomorph.trans
    (toricChartPartialDiffeomorph (chartTriangle b))

@[simp] theorem normalChartParametrization_apply (b : Bool) (q : Model) :
    normalChartParametrization b q =
      ToricSpace.inclusion (chartTriangle b) ((chartCoordinates b).symm q) := rfl

@[simp] theorem normalChartParametrization_source (b : Bool) :
    (normalChartParametrization b).source = univ := by
  ext q
  change (q ∈ (univ : Set Model) ∧
    (chartCoordinates b).symm q ∈ (toricChartPartialDiffeomorph (chartTriangle b)).source) ↔
      q ∈ univ
  rw [toricChartPartialDiffeomorph_source]
  simp only [mem_univ, and_self]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
