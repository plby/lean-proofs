import Wikipedia.HopfProblem.DegreeCollapseImmersedSourceArc
import Wikipedia.NoExoticSixSphere.TransverseSphereResolution

/-!
# A full-source native sphere chart centered at an actual unique fiber

The finite original double-source set has finite preimage in the injective
reference sphere chart. Choose a point outside it and translate that chart
so its parameter zero has a unique global image preimage. The chart and
all original immersion derivatives are retained, not assumed anew.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization SphereSumNeck

def sourceTranslation (a : Vector 3) : Vector 3 ≃ₘ[ℝ] Vector 3 where
  toEquiv := Equiv.addRight a
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

def shiftedSourceChart (a : Vector 3) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (Vector 3) (Sphere 3) ∞ :=
  (sourceTranslation a).toPartialDiffeomorph.trans sourceChart

theorem shiftedSourceChart_apply (a x : Vector 3) :
    shiftedSourceChart a x = sourceChart (x + a) := rfl

theorem shiftedSourceChart_source (a : Vector 3) : (shiftedSourceChart a).source = univ := by
  ext x
  change (x ∈ (univ : Set (Vector 3)) ∧ sourceTranslation a x ∈ sourceChart.source) ↔ x ∈ univ
  rw [sourceChart_source]
  simp

theorem contMDiff_shiftedSourceChart (a : Vector 3) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (shiftedSourceChart a) := by
  have h := (shiftedSourceChart a).contMDiffOn_toFun
  rw [shiftedSourceChart_source, contMDiffOn_univ] at h
  exact h

theorem injective_shiftedSourceChart (a : Vector 3) : Injective (shiftedSourceChart a) := by
  intro x y hxy
  exact (shiftedSourceChart a).injOn
    (by rw [shiftedSourceChart_source]; trivial) (by rw [shiftedSourceChart_source]; trivial) hxy

theorem exists_shifted_unique_fiber {M : Type*} (f : Sphere 3 → M)
    (hfin : (SphereSelfIntersections.pairs f).Finite) :
    ∃ a : Vector 3, ∀ z, f z = f (shiftedSourceChart a 0) → z = shiftedSourceChart a 0 := by
  have hi : Injective sourceChart := by
    intro x y hxy
    exact sourceChart.injOn (by rw [sourceChart_source]; trivial)
      (by rw [sourceChart_source]; trivial) hxy
  have hpre : (sourceChart ⁻¹' doubleSources f).Finite :=
    (hfin.image Prod.fst).preimage hi.injOn
  obtain ⟨a, ha⟩ := hpre.exists_notMem
  refine ⟨a, fun z hz ↦ ?_⟩
  have ha' : sourceChart a ∉ doubleSources f := ha
  have he : shiftedSourceChart a 0 = sourceChart a := by rw [shiftedSourceChart_apply, zero_add]
  rw [he] at hz ⊢
  exact (eq_of_not_mem_doubleSources ha' hz.symm).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]

theorem injective_mfderiv_shifted_branch {f : Sphere 3 → M}
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x)) (a x : Vector 3) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (f ∘ shiftedSourceChart a) x) := by
  have hx : x ∈ (shiftedSourceChart a).source := by rw [shiftedSourceChart_source]; trivial
  have hlocal := (shiftedSourceChart a).isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hx
  rw [mfderiv_comp x (hf.mdifferentiable (by simp) _) (hlocal.mdifferentiableAt (by simp))]
  exact (hi _).comp ((hlocal.mfderivToContinuousLinearEquiv (by simp)).injective)

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
