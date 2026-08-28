import Wikipedia.HopfProblem.QuotientManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Complex structures on covering quotients

The torus family and the local fillings in §§3–5 are quotients by holomorphic
covering actions. This file proves the compatibility of the quotient charts,
rather than assuming a complex structure on the quotient.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem

/-- Two continuous local lifts through a local homeomorphism that agree at
one point agree near that point whenever their projections agree there. -/
theorem eventuallyEq_of_localHomeomorph_comp_eq
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {q : X → Y} (hq : IsLocalHomeomorph q) {f g : Z → X} {z : Z}
    (hf : ContinuousAt f z) (hg : ContinuousAt g z) (hz : f z = g z)
    (he : ∀ᶠ w in 𝓝 z, q (f w) = q (g w)) : f =ᶠ[𝓝 z] g := by
  let e := hq.localInverseAt (f z)
  have hU : e.target ∈ 𝓝 (f z) := e.open_target.mem_nhds hq.self_mem_localInverseAt_target
  have hfU : ∀ᶠ w in 𝓝 z, f w ∈ e.target := hf hU
  have hgU : ∀ᶠ w in 𝓝 z, g w ∈ e.target := hg (hz ▸ hU)
  filter_upwards [hfU, hgU, he] with w hfw hgw hw
  exact hq.injOn_localInverseAt_target hfw hgw hw

/-- A surjective local homeomorphism whose fibres are the orbits of a free
continuous action is a quotient covering map. -/
theorem quotientCoveringMap_of_localHomeomorph
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Group G] [MulAction G X] [ContinuousConstSMul G X] [IsCancelSMul G X]
    {q : X → Y} (hq : IsLocalHomeomorph q) (hs : Function.Surjective q)
    (ho : ∀ x y, q x = q y ↔ x ∈ MulAction.orbit G y) : IsQuotientCoveringMap q G where
  toIsQuotientMap := hq.isOpenMap.isQuotientMap hq.continuous hs
  continuous_const_smul := continuous_const_smul
  apply_eq_iff_mem_orbit := ho _ _
  disjoint x := by
    let e := hq.localInverseAt x
    refine ⟨e.target, e.open_target.mem_nhds hq.self_mem_localInverseAt_target, ?_⟩
    rintro g ⟨z, ⟨w, hw, rfl⟩, hgw⟩
    have heq : q (g • w) = q w := (ho _ _).mpr ⟨g, rfl⟩
    have heq' : g • w = (1 : G) • w := by
      simpa only [one_smul] using hq.injOn_localInverseAt_target hgw hw heq
    exact IsCancelSMul.right_cancel _ _ w heq'

/-- Products with an unchanged base preserve local homeomorphisms. -/
theorem localHomeomorph_prod_id
    {B X Y : Type*} [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]
    {q : X → Y} (hq : IsLocalHomeomorph q) :
    IsLocalHomeomorph (fun z : B × X => (z.1, q z.2)) := by
  intro x
  obtain ⟨e, he, hqe⟩ := hq x.2
  refine ⟨(OpenPartialHomeomorph.refl B).prod e, ⟨Set.mem_univ _, he⟩, ?_⟩
  funext y
  exact congrArg (Prod.mk y.1) (congrFun hqe y.2)

namespace CoveringQuotient

variable {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q]
    [Group G] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G)

def representative (x : Q) : M := (hq.surjective x).choose

theorem project_representative (x : Q) : q (representative hq x) = x :=
  (hq.surjective x).choose_spec

def localInverse (x : M) : OpenPartialHomeomorph Q M :=
  hq.isCoveringMap.isLocalHomeomorph.localInverseAt x

@[simp] theorem localInverse_symm (x : M) : (localInverse hq x).symm = q :=
  hq.isCoveringMap.isLocalHomeomorph.localInverseAt_symm x

theorem project_localInverse (x : M) {y : Q} (hy : y ∈ (localInverse hq x).source) :
    q (localInverse hq x y) = y :=
  hq.isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem hy

/-- The change between two local lifts is locally a fixed deck transformation,
so is holomorphic whenever every deck transformation is holomorphic. -/
theorem contMDiffOn_lift (n : ℕ∞ω) (hG : ∀ g : G,
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n (fun x : M => g • x))
    (a : M) :
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (localInverse hq a ∘ q) (q ⁻¹' (localInverse hq a).source) := by
  intro x hx
  have hcont : ContinuousAt (localInverse hq a ∘ q) x :=
    ((localInverse hq a).continuousAt hx).comp hq.continuous.continuousAt
  obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp (project_localInverse hq a hx)
  have hsource : ∀ᶠ y in 𝓝 x, q y ∈ (localInverse hq a).source :=
    hq.continuous.continuousAt ((localInverse hq a).open_source.mem_nhds hx)
  have heq : (localInverse hq a ∘ q) =ᶠ[𝓝 x] (fun y => g • y) := by
    apply eventuallyEq_of_localHomeomorph_comp_eq hq.isCoveringMap.isLocalHomeomorph
      hcont (hG g).continuous.continuousAt hg.symm
    exact hsource.mono fun y hy => (project_localInverse hq a hy).trans (hq.map_smul g).symm
  exact ((hG g).contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt

/-- A quotient chart is a local lift followed by an original complex chart. -/
def chart (x : Q) : OpenPartialHomeomorph Q E :=
  (localInverse hq (representative hq x)).trans (chartAt E (representative hq x))

@[instance_reducible] def chartedSpace : ChartedSpace E Q where
  atlas := Set.range (chart (E := E) hq)
  chartAt := chart (E := E) hq
  mem_chart_source x := by
    change x ∈ (localInverse hq (representative hq x)).source ∧
      localInverse hq (representative hq x) x ∈ (chartAt E (representative hq x)).source
    constructor
    · have h := hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
        (x := representative hq x)
      simpa only [localInverse, project_representative] using h
    · have h : localInverse hq (representative hq x) x = representative hq x := by
        simpa only [localInverse, project_representative] using
          hq.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self (x := representative hq x)
      rw [h]
      exact mem_chart_source E (representative hq x)
  chart_mem_atlas x := Set.mem_range_self x

omit [NormedSpace ℂ E] in
theorem chart_symm (x : Q) :
    ((chart (E := E) hq x).symm : E → Q) = q ∘ (chartAt E (representative hq x)).symm := by
  funext z
  change (localInverse hq (representative hq x)).symm
    ((chartAt E (representative hq x)).symm z) = _
  rw [localInverse_symm]
  rfl

omit [NormedSpace ℂ E] in
theorem transition_eq (x y : Q) :
    (((chart (E := E) hq x).symm.trans (chart (E := E) hq y)) : E → E) =
      chartAt E (representative hq y) ∘ (localInverse hq (representative hq y) ∘ q) ∘
        (chartAt E (representative hq x)).symm := by
  funext z
  simp only [OpenPartialHomeomorph.trans_apply, chart_symm, Function.comp_apply]
  rfl

theorem contDiffOn_transition (n : ℕ∞ω) [IsManifold (modelWithCornersSelf ℂ E) n M]
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (fun x : M => g • x)) (x y : Q) :
    ContDiffOn ℂ n ((chart (E := E) hq x).symm.trans (chart (E := E) hq y))
      ((chart (E := E) hq x).symm.trans (chart (E := E) hq y)).source := by
  intro z hz
  have hza : z ∈ (chartAt E (representative hq x)).target := hz.1.1
  have hy : q ((chartAt E (representative hq x)).symm z) ∈ (chart (E := E) hq y).source := by
    simpa only [OpenPartialHomeomorph.symm_symm, chart_symm, Function.comp_apply,
      Set.mem_preimage] using hz.2
  have ha := (chartAt E (representative hq x)).map_target hza
  have hb : localInverse hq (representative hq y)
      (q ((chartAt E (representative hq x)).symm z)) ∈
      (chartAt E (representative hq y)).source := hy.2
  have hmid := (contMDiffOn_lift hq n hG (representative hq y)).contMDiffAt
    (((localInverse hq (representative hq y)).open_source.preimage hq.continuous).mem_nhds hy.1)
  have hc := ((contMDiffAt_iff_of_mem_source ha hb).mp hmid).2
  have hc' : ContDiffAt ℂ n
      (chartAt E (representative hq y) ∘ (localInverse hq (representative hq y) ∘ q) ∘
        (chartAt E (representative hq x)).symm) z := by
    simpa [extChartAt, OpenPartialHomeomorph.extend, contDiffWithinAt_univ,
      (chartAt E (representative hq x)).right_inv hza] using hc
  rw [transition_eq]
  exact hc'.contDiffWithinAt

/-- The quotient chart structure is an analytic complex manifold when the
original manifold and all deck transformations are analytic. -/
theorem isManifold (n : ℕ∞ω) [IsManifold (modelWithCornersSelf ℂ E) n M]
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (fun x : M => g • x)) :
    letI := chartedSpace (E := E) hq
    IsManifold (modelWithCornersSelf ℂ E) n Q := by
  let := chartedSpace (E := E) hq
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  simpa using contDiffOn_transition hq n hG x y

/-- The quotient projection is holomorphic in the constructed complex atlas. -/
theorem contMDiff_project (n : ℕ∞ω) [IsManifold (modelWithCornersSelf ℂ E) n M]
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (fun x : M => g • x)) :
    letI := chartedSpace (E := E) hq
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n q := by
  let := chartedSpace (E := E) hq
  let := isManifold hq n hG
  intro x
  have hy : q x ∈ (chart (E := E) hq (q x)).source := mem_chart_source E (q x)
  have hmid := (contMDiffOn_lift hq n hG (representative hq (q x))).contMDiffAt
    (((localInverse hq (representative hq (q x))).open_source.preimage hq.continuous).mem_nhds hy.1)
  have hc : ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (chartAt E (representative hq (q x)))
      (localInverse hq (representative hq (q x)) (q x)) := by
    simpa [extChartAt, OpenPartialHomeomorph.extend] using
      (contMDiffAt_extChartAt' (I := modelWithCornersSelf ℂ E) (n := n) hy.2)
  apply (contMDiffAt_iff_target_of_mem_source (I := modelWithCornersSelf ℂ E)
    (I' := modelWithCornersSelf ℂ E) (mem_chart_source E (q x))).mpr
  refine ⟨hq.continuous.continuousAt, ?_⟩
  have hchart : chartAt E (q x) = chart (E := E) hq (q x) := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chart,
    Function.comp_def] using hc.comp x hmid

/-- A map out of the quotient is holomorphic if its pullback to the covering
manifold is holomorphic. -/
theorem contMDiff_of_comp {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ F H) (n : ℕ∞ω) [IsManifold (modelWithCornersSelf ℂ E) n M]
    {f : Q → N} (hf : ContMDiff (modelWithCornersSelf ℂ E) I n (f ∘ q)) :
    letI := chartedSpace (E := E) hq
    ContMDiff (modelWithCornersSelf ℂ E) I n f := by
  let := chartedSpace (E := E) hq
  intro x
  rw [contMDiffAt_iff_source]
  have hx : x ∈ (chart (E := E) hq x).source := mem_chart_source E x
  have hsrc := (contMDiffAt_iff_source_of_mem_source (I := modelWithCornersSelf ℂ E)
    (I' := I) hx.2).mp (hf.contMDiffAt (x := localInverse hq (representative hq x) x))
  have hchart : chartAt E x = chart (E := E) hq x := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chart,
    Function.comp_def] using hsrc

/-- The same descent criterion on an open subset of the quotient. -/
theorem contMDiffOn_of_comp {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ F H) (n : ℕ∞ω) [IsManifold (modelWithCornersSelf ℂ E) n M]
    {f : Q → N} {U : Set Q} (hU : IsOpen U)
    (hf : ContMDiffOn (modelWithCornersSelf ℂ E) I n (f ∘ q) (q ⁻¹' U)) :
    letI := chartedSpace (E := E) hq
    ContMDiffOn (modelWithCornersSelf ℂ E) I n f U := by
  let := chartedSpace (E := E) hq
  intro x hxU
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  have hx : x ∈ (chart (E := E) hq x).source := mem_chart_source E x
  have hpre : localInverse hq (representative hq x) x ∈ q ⁻¹' U := by
    change q (localInverse hq (representative hq x) x) ∈ U
    rw [project_localInverse hq _ hx.1]
    exact hxU
  have hf' := hf.contMDiffAt ((hU.preimage hq.continuous).mem_nhds hpre)
  have hsrc := (contMDiffAt_iff_source_of_mem_source (I := modelWithCornersSelf ℂ E)
    (I' := I) hx.2).mp hf'
  have hchart : chartAt E x = chart (E := E) hq x := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, chart,
    Function.comp_def] using hsrc

theorem localInverse_holomorphic (n : ℕ∞ω) [IsManifold (modelWithCornersSelf ℂ E) n M]
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (fun x : M => g • x)) (a : M) :
    letI := chartedSpace (E := E) hq
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) n
      (localInverse hq a) (localInverse hq a).source :=
  contMDiffOn_of_comp hq (modelWithCornersSelf ℂ E) n (localInverse hq a).open_source
    (contMDiffOn_lift hq n hG a)

end CoveringQuotient

end Wikipedia.HopfProblem
