import Wikipedia.HopfProblem.NormalCrossing
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Normal-crossing charts through an actual open parametrization

An existing maximal-atlas chart is an analytic partial diffeomorphism.
Composing it with the inverse of an actual analytic parametrization
preserves its centered product equation.  The new chart is analytic for
the already supplied target atlas, and its source lies in the actual
target of the parametrization.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspNormalForms

open ToricCharts

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃

section NativeChart

variable {X : Type*} [TopologicalSpace X] [ChartedSpace E₃ X]

/-- A native normal-crossing atlas member, with its proved analytic
forward and inverse maps retained as a partial diffeomorphism. -/
def nativePartialChart (e : OpenPartialHomeomorph X E₃)
    (he : e ∈ IsManifold.maximalAtlas I₃ ω X) :
    PartialDiffeomorph I₃ I₃ X E₃ ω where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he

@[simp] theorem nativePartialChart_apply (e : OpenPartialHomeomorph X E₃)
    (he : e ∈ IsManifold.maximalAtlas I₃ ω X) (x : X) :
    nativePartialChart e he x = e x := rfl

@[simp] theorem nativePartialChart_symm_apply (e : OpenPartialHomeomorph X E₃)
    (he : e ∈ IsManifold.maximalAtlas I₃ ω X) (w : E₃) :
    (nativePartialChart e he).symm w = e.symm w := rfl

@[simp] theorem nativePartialChart_source (e : OpenPartialHomeomorph X E₃)
    (he : e ∈ IsManifold.maximalAtlas I₃ ω X) :
    (nativePartialChart e he).source = e.source := rfl

@[simp] theorem nativePartialChart_target (e : OpenPartialHomeomorph X E₃)
    (he : e ∈ IsManifold.maximalAtlas I₃ ω X) :
    (nativePartialChart e he).target = e.target := rfl

end NativeChart

section Transport

variable {X Y F H : Type*}
    [TopologicalSpace X] [ChartedSpace E₃ X]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace Y] [ChartedSpace H Y]
    {I : ModelWithCorners ℂ F H}

/-- Compose the original normal-crossing chart with the inverse of the
actual parametrization.  In particular, no new atlas is put on `Y`. -/
theorem exists_transported_normalCrossingChart
    (p : PartialDiffeomorph I₃ I X Y ω) {f : X → ℂ} {q : Y → ℂ}
    {J : Finset (Fin 3)} {x : X} (hx : x ∈ p.source)
    (hcoord : ∀ z ∈ p.source, q (p z) = f z)
    (h : NormalCrossingChartAt J f x) :
    ∃ e : PartialDiffeomorph I I₃ Y E₃ ω,
      p x ∈ e.source ∧ e (p x) = 0 ∧ e.source ⊆ p.target ∧
      ∀ w ∈ e.target, q (e.symm w) = ∏ j ∈ J, w j := by
  obtain ⟨d, hd, hxd, hzero, hprod⟩ := h
  let e := p.symm.trans (nativePartialChart d hd)
  have hleft : p.symm (p x) = x := p.left_inv' hx
  refine ⟨e, ?_, ?_, fun _ hy => hy.1, ?_⟩
  · refine ⟨p.map_source' hx, ?_⟩
    change p.symm (p x) ∈ d.source
    rw [hleft]
    exact hxd
  · change d (p.symm (p x)) = 0
    rw [hleft, hzero]
  · intro w hw
    change q (p (d.symm w)) = ∏ j ∈ J, w j
    exact (hcoord (d.symm w) hw.2).trans (hprod w hw.1)

end Transport

section Reindex

variable {Y F H : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace Y] [ChartedSpace H Y]
    {I : ModelWithCorners ℂ F H}

/-- A genuine linear change of the three target coordinates preserves
the original global atlas and the containment of the chart source. -/
theorem exists_reindexed_normalForm
    (e : PartialDiffeomorph I I₃ Y E₃ ω) {y : Y} {S : Set Y}
    {q : Y → ℂ} {P Q : E₃ → ℂ}
    (hy : y ∈ e.source) (hzero : e y = 0) (hsource : e.source ⊆ S)
    (hprod : ∀ w ∈ e.target, q (e.symm w) = P w)
    (d : Diffeomorph I₃ I₃ E₃ E₃ ω) (hdzero : d 0 = 0)
    (hdprod : ∀ w, P (d.symm w) = Q w) :
    ∃ e' : PartialDiffeomorph I I₃ Y E₃ ω,
      y ∈ e'.source ∧ e' y = 0 ∧ e'.source ⊆ S ∧
      ∀ w ∈ e'.target, q (e'.symm w) = Q w := by
  refine ⟨e.trans d.toPartialDiffeomorph, ⟨hy, mem_univ _⟩, ?_,
    fun _ hz => hsource hz.1, ?_⟩
  · change d (e y) = 0
    rw [hzero, hdzero]
  · intro w hw
    change q (e.symm (d.symm w)) = Q w
    exact (hprod (d.symm w) hw.2).trans (hdprod w)

end Reindex

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspNormalForms
