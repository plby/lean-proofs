import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

/-!
# Complex manifolds obtained by discrete translations

The period tori in §3 of `tex/s6.tex` use the quotient complex structure.
This file constructs that structure from local inverses of the quotient map.
Chart transitions differ from the identity by a locally constant lattice
vector, and are therefore complex analytic.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A continuous map differing from the identity by a vector in a discrete
subgroup is locally a translation, hence analytic. -/
theorem contDiffOn_of_sub_mem_discrete (L : Submodule ℤ E) [DiscreteTopology L]
    {f : E → E} {s : Set E} (hf : ContinuousOn f s)
    (hL : ∀ x ∈ s, f x - x ∈ L) (n : ℕ∞ω) : ContDiffOn ℂ n f s := by
  let g : s → L := fun x => ⟨f x - x, hL x x.property⟩
  have hg : Continuous g :=
    (hf.domRestrict.sub continuous_subtype_val).subtype_mk _
  have hg' : IsLocallyConstant g := (IsLocallyConstant.iff_continuous g).mpr hg
  intro x hx
  have heq : ∀ᶠ y in 𝓝[s] x, f y - y = f x - x := by
    apply (eventually_nhds_subtype_iff s ⟨x, hx⟩ _).mp
    exact (hg'.eventually_eq ⟨x, hx⟩).mono fun y hy => congrArg Subtype.val hy
  apply (contDiff_id.add contDiff_const).contDiffWithinAt.congr_of_eventuallyEq_of_mem
    (s := s) (f := fun y => y + (f x - x)) ?_ hx
  exact heq.mono fun y hy => (sub_eq_iff_eq_add.mp hy).trans (add_comm _ _)

namespace DiscreteQuotient

variable (L : Submodule ℤ E) [DiscreteTopology L]

omit [NormedSpace ℂ E] in
theorem quotient_localHomeomorph : IsLocalHomeomorph (L.mkQ : E → E ⧸ L) := by
  have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  exact (AddSubgroup.isAddQuotientCoveringMap_of_comm L.toAddSubgroup
    DiscreteTopology.isDiscrete).isCoveringMap.isLocalHomeomorph

/-- Choose a lift only to specify a preferred chart at each quotient point. -/
def representative (x : E ⧸ L) : E := (L.mkQ_surjective x).choose

omit [NormedSpace ℂ E] [DiscreteTopology L] in
@[simp] theorem mkQ_representative (x : E ⧸ L) : L.mkQ (representative L x) = x :=
  (L.mkQ_surjective x).choose_spec

def chart (x : E ⧸ L) : OpenPartialHomeomorph (E ⧸ L) E :=
  (quotient_localHomeomorph L).localInverseAt (representative L x)

instance chartedSpace : ChartedSpace E (E ⧸ L) where
  atlas := Set.range (chart L)
  chartAt := chart L
  mem_chart_source x := by
    have h := (quotient_localHomeomorph L).apply_self_mem_localInverseAt_source
      (x := representative L x)
    simpa only [chart, mkQ_representative] using h
  chart_mem_atlas x := Set.mem_range_self x

omit [NormedSpace ℂ E] in
@[simp] theorem chart_symm (x : E ⧸ L) : (chart L x).symm = (L.mkQ : E → E ⧸ L) :=
  (quotient_localHomeomorph L).localInverseAt_symm (representative L x)

omit [NormedSpace ℂ E] in
theorem mkQ_chart (x y : E ⧸ L) (hy : y ∈ (chart L x).source) :
    L.mkQ (chart L x y) = y :=
  (quotient_localHomeomorph L).apply_localInverseAt_of_mem hy

omit [NormedSpace ℂ E] in
theorem transition_sub_mem (x y : E ⧸ L) (z : E)
    (hz : z ∈ ((chart L x).symm.trans (chart L y)).source) :
    ((chart L x).symm.trans (chart L y)) z - z ∈ L := by
  apply (Submodule.Quotient.eq L).mp
  change L.mkQ (((chart L x).symm.trans (chart L y)) z) = L.mkQ z
  rw [OpenPartialHomeomorph.trans_apply, chart_symm]
  apply mkQ_chart
  simpa only [OpenPartialHomeomorph.symm_symm, chart_symm, Set.mem_preimage] using hz.2

/-- A vector space modulo a discrete lattice has an analytic complex atlas. -/
instance isManifold (n : ℕ∞ω) : IsManifold (modelWithCornersSelf ℂ E) n (E ⧸ L) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  have h := contDiffOn_of_sub_mem_discrete L
    ((chart L x).symm.trans (chart L y)).continuousOn (transition_sub_mem L x y) n
  simpa using h

/-- The quotient projection is holomorphic for the constructed complex atlas. -/
theorem contMDiff_mkQ (n : ℕ∞ω) :
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (L.mkQ : E → E ⧸ L) := by
  apply contMDiff_iff.mpr
  refine ⟨L.continuous_mkQ, ?_⟩
  intro x y
  have h : ContDiffOn ℂ n (chart L y ∘ L.mkQ) (L.mkQ ⁻¹' (chart L y).source) := by
    apply contDiffOn_of_sub_mem_discrete L
    · exact (chart L y).continuousOn.comp L.continuous_mkQ.continuousOn
        (fun z hz => hz)
    · intro z hz
      exact (Submodule.Quotient.eq L).mp (mkQ_chart L y (L.mkQ z) hz)
  have hchart : chartAt E y = chart L y := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chartAt_self_eq] using h

/-- Holomorphicity can be tested after pulling a map back to the covering
vector space. This includes analytic descent without choosing a global lift. -/
theorem contMDiff_of_comp_mkQ {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℂ F H) (n : ℕ∞ω) {f : E ⧸ L → M}
    (hf : ContMDiff (modelWithCornersSelf ℂ E) I n (f ∘ L.mkQ)) :
    ContMDiff (modelWithCornersSelf ℂ E) I n f := by
  intro x
  rw [contMDiffAt_iff_source]
  have hchart : chartAt E x = chart L x := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chart_symm] using
    (hf.contMDiffAt.contMDiffWithinAt (s := Set.univ) (x := chart L x x))

/-- The quotient group operations are analytic, not only continuous. -/
instance lieAddGroup (n : ℕ∞ω) : LieAddGroup (modelWithCornersSelf ℂ E) n (E ⧸ L) where
  contMDiff_add := by
    have h : ContMDiff (modelWithCornersSelf ℂ (E × E)) (modelWithCornersSelf ℂ E) n
        (fun z : E × E => L.mkQ (z.1 + z.2)) :=
      (contMDiff_mkQ L n).comp (contDiff_fst.add contDiff_snd).contMDiff
    intro x
    rw [contMDiffAt_iff_source]
    have hchart : ∀ y : E ⧸ L, chartAt E y = chart L y := fun _ => rfl
    have hs : ((extChartAt ((modelWithCornersSelf ℂ E).prod
        (modelWithCornersSelf ℂ E)) x).symm : E × E → (E ⧸ L) × (E ⧸ L)) =
        fun z => (L.mkQ z.1, L.mkQ z.2) := by
      rw [extChartAt_prod, PartialEquiv.prod_coe_symm]
      simp only [extChartAt_coe_symm, hchart, chart_symm, modelWithCornersSelf_coe_symm,
        Function.comp_def, id_eq]
    have ht : extChartAt ((modelWithCornersSelf ℂ E).prod (modelWithCornersSelf ℂ E)) x x =
        (chart L x.1 x.1, chart L x.2 x.2) := rfl
    have hr : Set.range ((modelWithCornersSelf ℂ E).prod (modelWithCornersSelf ℂ E)) =
        Set.univ := Set.range_eq_univ.mpr fun z => ⟨z, rfl⟩
    rw [hs, ht, hr]
    simpa only [Function.comp_def, map_add] using
      (h.contMDiffAt.contMDiffWithinAt (s := Set.univ)
        (x := (chart L x.1 x.1, chart L x.2 x.2)))
  contMDiff_neg := by
    apply contMDiff_of_comp_mkQ L (modelWithCornersSelf ℂ E) n
    simpa [Function.comp_def, map_neg] using
      (contMDiff_mkQ L n).comp (contDiff_neg : ContDiff ℂ n (fun z : E => -z)).contMDiff

end DiscreteQuotient

end Wikipedia.HopfProblem
