import Wikipedia.NoExoticSixSphere.ChartFiber
import Wikipedia.NoExoticSixSphere.RegularLevelDifferential
import Wikipedia.NoExoticSixSphere.Transport

/-!
# The embedded smooth structure on a chart fiber

The chart-coordinate level atlas transfers to the original fiber, with its
original subtype topology. Smoothness into this atlas is equivalent to
smoothness of the ambient-valued map. Its inclusion has injective differential.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.ChartFiber

variable {B H M C H' N F : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : ContinuousMap M N) (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
  (b : N) (hb : b ∈ c.source) {k : ℕ}
  (A : RegularLevelAtlas (K := EuclideanSpace ℝ (Fin k)) I (coordinates f c b))

@[instance_reducible]
noncomputable def atlas : ChartedSpace (EuclideanSpace ℝ (Fin k)) {x : M // f x = b} :=
  letI := A.chartedSpace
  pullbackAtlas (n := k) (homeomorph f c b hb)

theorem isManifold : letI := atlas f c b hb A;
    IsManifold (𝓡 k) ∞ {x : M // f x = b} := by
  let := A.chartedSpace
  let := A.isManifold
  exact pullback_isManifold (n := k) (homeomorph f c b hb)

theorem contMDiff_homeomorph : letI := A.chartedSpace; letI := atlas f c b hb A;
    ContMDiff (𝓡 k) (𝓡 k) ∞ (homeomorph f c b hb) := by
  let := A.chartedSpace
  exact pullback_contMDiff (n := k) (homeomorph f c b hb)

theorem contMDiff_homeomorph_symm : letI := A.chartedSpace; letI := atlas f c b hb A;
    ContMDiff (𝓡 k) (𝓡 k) ∞ (homeomorph f c b hb).symm := by
  let := A.chartedSpace
  exact pullback_symm_contMDiff (n := k) (homeomorph f c b hb)

theorem contMDiff_subtype_val : letI := atlas f c b hb A;
    ContMDiff (𝓡 k) I ∞ (Subtype.val : {x : M // f x = b} → M) := by
  let := A.chartedSpace
  let := atlas f c b hb A
  have hv : ContMDiff I I ∞ (Subtype.val : domain f c → M) :=
    _root_.contMDiff_subtype_val
  exact hv.comp (A.contMDiff_subtype_val.comp (contMDiff_homeomorph f c b hb A))

variable {B' H'' P : Type*} [NormedAddCommGroup B'] [NormedSpace ℝ B']
  [TopologicalSpace H''] {L : ModelWithCorners ℝ B' H''}
  [TopologicalSpace P] [ChartedSpace H'' P]

theorem contMDiffAt_iff_ambient (g : P → {x : M // f x = b}) (x : P) :
    letI := atlas f c b hb A;
    ContMDiffAt L (𝓡 k) ∞ g x ↔ ContMDiffAt L I ∞ (fun y ↦ (g y).val) x := by
  let := A.chartedSpace
  let := atlas f c b hb A
  constructor
  · intro hg
    exact (contMDiff_subtype_val f c b hb A).contMDiffAt.comp x hg
  · intro hg
    let g' := homeomorph f c b hb ∘ g
    have hg' : ContMDiffAt L I ∞ (fun y ↦ (g' y).val) x :=
      (ContMDiffAt.subtypeVal_comp_iff (domain f c) (fun y ↦ (g' y).val) x).mp hg
    have hz := (A.contMDiffAt_iff_ambient g' x).mpr hg'
    have h := (contMDiff_homeomorph_symm f c b hb A).contMDiffAt.comp x hz
    simpa only [g', Function.comp_def, Homeomorph.symm_apply_apply] using h

theorem contMDiff_iff_ambient (g : P → {x : M // f x = b}) :
    letI := atlas f c b hb A;
    ContMDiff L (𝓡 k) ∞ g ↔ ContMDiff L I ∞ (fun y ↦ (g y).val) := by
  let := atlas f c b hb A
  exact forall_congr' (fun x ↦ contMDiffAt_iff_ambient f c b hb A g x)

theorem injective_mfderiv_subtype_val (x : {x : M // f x = b}) :
    letI := atlas f c b hb A;
    Function.Injective (mfderiv (𝓡 k) I (Subtype.val : {x : M // f x = b} → M) x) := by
  let := A.chartedSpace
  let := atlas f c b hb A
  let e := homeomorph f c b hb
  let d := pullbackDiffeomorph (n := k) e
  have he : Function.Injective (mfderiv (𝓡 k) (𝓡 k) e x) :=
    (d.mfderivToContinuousLinearEquiv (by simp) x).injective
  have hl := A.injective_mfderiv_subtype_val (e x)
  have hv := (mfderiv_openSubset_val_bijective (I := I) (domain f c) (e x).val).injective
  have hde := (contMDiff_homeomorph f c b hb A).mdifferentiable (by simp) x
  have hdl := A.contMDiff_subtype_val.mdifferentiable (by simp) (e x)
  have hdv := (_root_.contMDiff_subtype_val (I := I) (U := domain f c) (n := ∞)).mdifferentiable
    (by simp) (e x).val
  change Function.Injective (mfderiv (𝓡 k) I
    ((Subtype.val : domain f c → M) ∘
      ((Subtype.val : {x : domain f c // coordinates f c b x = 0} → domain f c) ∘ e)) x)
  rw [mfderiv_comp x hdv (hdl.comp x hde), mfderiv_comp x hdl hde]
  exact hv.comp (hl.comp he)

end NoExoticSixSphere.ChartFiber
