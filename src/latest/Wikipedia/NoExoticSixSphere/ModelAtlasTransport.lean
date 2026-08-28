import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Atlas transport for models with boundary

Pull back an atlas along a homeomorphism without changing the source topology.
The model need not be boundaryless. This constructs the smooth structure on
newly defined slab neighborhoods; it does not identify independently specified
smooth structures on a candidate sphere.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.ModelAtlasTransport

variable {H M N : Type*} [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H N] (e : M ≃ₜ N)

@[instance_reducible]
def atlas : ChartedSpace H M where
  atlas := e.transOpenPartialHomeomorph '' _root_.atlas H N
  chartAt x := e.transOpenPartialHomeomorph (chartAt H (e x))
  mem_chart_source x := mem_chart_source H (e x)
  chart_mem_atlas x := ⟨_, chart_mem_atlas H (e x), rfl⟩

omit [ChartedSpace H N] in
theorem transition (f g : OpenPartialHomeomorph N H) :
    (e.transOpenPartialHomeomorph f).symm.trans (e.transOpenPartialHomeomorph g) =
      f.symm.trans g := by
  simp only [Homeomorph.transOpenPartialHomeomorph_eq_trans,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← Homeomorph.symm_toOpenPartialHomeomorph]
  rw [← OpenPartialHomeomorph.trans_assoc e.symm.toOpenPartialHomeomorph
    e.toOpenPartialHomeomorph g, ← Homeomorph.trans_toOpenPartialHomeomorph]
  simp

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  (I : ModelWithCorners ℝ B H)

theorem isManifold [IsManifold I ∞ N] : letI := atlas (H := H) e; IsManifold I ∞ M := by
  let := atlas (H := H) e
  refine { compatible := ?_ }
  rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
  rw [transition]
  exact (contDiffGroupoid ∞ I).compatible hf hg

theorem extChartAt_apply (x y : M) : letI := atlas (H := H) e;
    extChartAt I x y = extChartAt I (e x) (e y) := rfl

theorem extChartAt_symm_apply (x : M) (y : B) : letI := atlas (H := H) e;
    (extChartAt I x).symm y = e.symm ((extChartAt I (e x)).symm y) := rfl

theorem contMDiff : letI := atlas (H := H) e; ContMDiff I I ∞ e := by
  let := atlas (H := H) e
  intro x
  refine contMDiffAt_iff.mpr ⟨e.continuous.continuousAt, ?_⟩
  have h := (contMDiffAt_iff.mp
    ((contMDiff_id : ContMDiff I I ∞ (id : N → N)) (e x))).2
  simpa only [Function.comp_def, extChartAt_symm_apply, extChartAt_apply,
    Homeomorph.apply_symm_apply, id_eq] using h

theorem contMDiff_symm : letI := atlas (H := H) e; ContMDiff I I ∞ e.symm := by
  let := atlas (H := H) e
  intro y
  refine contMDiffAt_iff.mpr ⟨e.symm.continuous.continuousAt, ?_⟩
  have h := (contMDiffAt_iff.mp
    ((contMDiff_id : ContMDiff I I ∞ (id : N → N)) y)).2
  simpa only [Function.comp_def, extChartAt_symm_apply, extChartAt_apply,
    Homeomorph.apply_symm_apply, id_eq] using h

def diffeomorph : letI := atlas (H := H) e; M ≃ₘ⟮I, I⟯ N := by
  let := atlas (H := H) e
  exact { toEquiv := e.toEquiv
          contMDiff_toFun := contMDiff e I
          contMDiff_invFun := contMDiff_symm e I }

end NoExoticSixSphere.ModelAtlasTransport
