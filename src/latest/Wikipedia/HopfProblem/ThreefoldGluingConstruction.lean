import Wikipedia.HopfProblem.ThreefoldGluingProper
import Wikipedia.HopfProblem.ThreefoldGluingDescent
import Wikipedia.HopfProblem.ThreefoldGluingManifold
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Compact holomorphic spaces constructed by gluing over the base

This packages the actual topological and analytic constructions: each
piece is biholomorphic to the full inverse image of its base patch, and
proper local maps over a compact Hausdorff base give a compact Hausdorff
complex manifold with a proper holomorphic projection.

This is a construction theorem from actual local gluing data.  It does
not assert that the source's still-unconstructed global special periods
and overlap identifications instantiate that data.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff

universe u

namespace Wikipedia.HopfProblem.ThreefoldGluing.Data

variable {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)

/-- The full open inverse image of a base patch in the actual gluing. -/
def liftedPatch (i : D.J) : Opens D.Space :=
  ⟨D.projection ⁻¹' (D.patch i : Set B), (D.patch i).isOpen.preimage D.projection_continuous⟩

variable [∀ i, Nonempty (D.piece i)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [∀ i, ChartedSpace E (D.piece i)]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)]

theorem patchHomeomorph_symm_eq_parametrization (i : D.J) (x : D.liftedPatch i) :
    (D.patchHomeomorph i).symm x = (D.parametrization i).symm x.val := by
  have hx : D.inclusion i ((D.patchHomeomorph i).symm x) = x.val :=
    congrArg Subtype.val ((D.patchHomeomorph i).apply_symm_apply x)
  rw [← hx, D.parametrization_symm_inclusion]

variable (hhol : ∀ i j, ContMDiffOn (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ E) ω (D.transition i j) (D.transition i j).source)

include hhol in
/-- Each original piece is genuinely biholomorphic to the full inverse
image of its base patch in the constructed complex manifold. -/
def patchBiholomorph (i : D.J) :
    letI := D.chartedSpace (E := E)
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
      (D.piece i) (D.liftedPatch i) ω := by
  letI := D.chartedSpace (E := E)
  let e : D.piece i ≃ₜ D.liftedPatch i := D.patchHomeomorph i
  refine {
    toEquiv := e.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · intro x
    have he : ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
        (fun z : D.piece i => ((e z).val : D.Space)) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
        e x :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
    exact he.mp ((D.inclusion_holomorphic hhol i) x)
  · intro x
    have hx : x.val ∈ (D.parametrization i).target := by
      rw [D.parametrization_target, D.inclusion_range]
      exact x.property
    have h := ((D.parametrization_symm_holomorphic hhol i).contMDiffAt
      ((D.parametrization i).open_target.mem_nhds hx)).comp x
        contMDiff_subtype_val.contMDiffAt
    convert h using 1
    funext y
    exact D.patchHomeomorph_symm_eq_parametrization i y

section Descent

variable {F H Y : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace Y] [ChartedSpace H Y]

/-- Compatible holomorphic local maps yield a holomorphic actual descent. -/
theorem descend_holomorphic (I : ModelWithCorners ℂ F H)
    (f : ∀ i, D.piece i → Y) (hf : D.Compatible f)
    (hh : ∀ i, ContMDiff (modelWithCornersSelf ℂ E) I ω (f i)) :
    letI := D.chartedSpace (E := E)
    ContMDiff (modelWithCornersSelf ℂ E) I ω (D.descend f hf) := by
  apply D.contMDiff_of_comp_inclusion I (D.descend f hf)
  intro i
  rw [D.descend_comp_inclusion]
  exact hh i

/-- The universal property holds in the analytic category as well. -/
theorem existsUnique_holomorphic_descend (I : ModelWithCorners ℂ F H)
    (f : ∀ i, D.piece i → Y) (hf : D.Compatible f)
    (hh : ∀ i, ContMDiff (modelWithCornersSelf ℂ E) I ω (f i)) :
    letI := D.chartedSpace (E := E)
    ∃! g : D.Space → Y, ContMDiff (modelWithCornersSelf ℂ E) I ω g ∧
      ∀ i x, g (D.inclusion i x) = f i x := by
  let := D.chartedSpace (E := E)
  refine ⟨D.descend f hf, ⟨D.descend_holomorphic I f hf hh, D.descend_inclusion f hf⟩, ?_⟩
  intro g hg
  exact D.descend_unique f hf g hg.2

end Descent

include hhol in
/-- Compact complex gluing from the actual local data, with no assumed
global manifold, global proper map, or global compactness field. -/
theorem compact_holomorphic_gluing
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace F B]
    [CompactSpace B] [T2Space B] [∀ i, T2Space (D.piece i)]
    [∀ i, SecondCountableTopology (D.piece i)]
    (hproper : ∀ i, IsProperMap (D.localProjection i))
    (hsurj : ∀ i, Function.Surjective (D.localProjection i))
    (hbase : ∀ i, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) ω
      (D.toBase i)) :
    letI := D.chartedSpace (E := E)
    CompactSpace D.Space ∧ T2Space D.Space ∧ SecondCountableTopology D.Space ∧
      IsManifold (modelWithCornersSelf ℂ E) ω D.Space ∧
      IsProperMap D.projection ∧ Function.Surjective D.projection ∧
      ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) ω D.projection := by
  let := D.chartedSpace (E := E)
  exact ⟨D.compactSpace hproper, D.spaceT2, D.secondCountableSpace_of_compactBase,
    D.isManifold hhol, D.projection_proper hproper, D.projection_surjective hsurj,
    D.projection_holomorphic hbase⟩

end Wikipedia.HopfProblem.ThreefoldGluing.Data
