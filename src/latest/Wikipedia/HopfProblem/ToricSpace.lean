import Wikipedia.HopfProblem.ToricFan
import Mathlib.Topology.Gluing
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Gluing the cusp charts

This constructs the space obtained by gluing the explicit affine charts in
§4.2 of `tex/s6.tex`. The overlap data and cocycle are proved from the integral
monomial substitutions. Hausdorffness and the compact quotient are not assumed.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

abbrev gluingCore : TopCat.GlueData.MkCore where
  J := Triangle
  U := fun _ => TopCat.of (CoordinateSpace 3)
  V s t := ⟨(chartChange s t).source, (chartChange s t).open_source⟩
  t s t := TopCat.ofHom {
    toFun := fun z => ⟨chartChange s t z, (chartChange s t).map_source z.2⟩
    continuous_toFun := (chartChange s t).continuousOn.domRestrict.subtype_mk _ }
  V_id s := by
    apply Opens.ext
    exact chartChange_self_source s
  t_id s := by
    funext z
    exact Subtype.ext (chartChange_self_apply s z.1)
  t_inter := by
    intro r s t z hz
    exact chartChange_inter r s t z.2 hz
  cocycle r s t z hz :=
    (chartChange_cocycle r s t z.2 (chartChange_inter r s t z.2 hz)).2

abbrev gluing : TopCat.GlueData := TopCat.GlueData.mk' gluingCore

/-- The actual glued topological space, before taking the cusp lattice quotient. -/
abbrev Space := gluing.toGlueData.glued

def inclusion (s : Triangle) : CoordinateSpace 3 → Space := gluing.toGlueData.ι s

theorem inclusion_openEmbedding (s : Triangle) : IsOpenEmbedding (inclusion s) :=
  gluing.ι_isOpenEmbedding s

theorem inclusion_jointly_surjective (x : Space) :
    ∃ s z, inclusion s z = x := gluing.ι_jointly_surjective x

theorem inclusion_eq_iff (s t : Triangle) (z w : CoordinateSpace 3) :
    inclusion s z = inclusion t w ↔
      z ∈ (chartChange s t).source ∧ chartChange s t z = w := by
  refine (gluing.ι_eq_iff_rel s t z w).trans ?_
  constructor
  · rintro ⟨⟨v, hv⟩, h1, h2⟩
    change v = z at h1
    change chartChange s t v = w at h2
    subst v
    exact ⟨hv, h2⟩
  · rintro ⟨hz, he⟩
    exact ⟨⟨z, hz⟩, rfl, he⟩

/-- Each copy of complex three-space is an actual open chart of the gluing. -/
def parametrization (s : Triangle) : OpenPartialHomeomorph (CoordinateSpace 3) Space :=
  (inclusion_openEmbedding s).toOpenPartialHomeomorph (inclusion s)

@[simp] theorem parametrization_apply (s : Triangle) (z : CoordinateSpace 3) :
    parametrization s z = inclusion s z := rfl

@[simp] theorem parametrization_source (s : Triangle) :
    (parametrization s).source = univ := rfl

@[simp] theorem parametrization_target (s : Triangle) :
    (parametrization s).target = range (inclusion s) := by
  simp [parametrization]

theorem parametrization_transition (s t : Triangle) {z : CoordinateSpace 3}
    (hz : inclusion s z ∈ range (inclusion t)) :
    z ∈ (chartChange s t).source ∧
      (parametrization t).symm (inclusion s z) = chartChange s t z := by
  obtain ⟨w, hw⟩ := hz
  have he := (inclusion_eq_iff s t z w).mp hw.symm
  refine ⟨he.1, ?_⟩
  rw [← hw]
  exact ((inclusion_openEmbedding t).toOpenPartialHomeomorph_left_inv).trans he.2.symm

def preferredTriangle (x : Space) : Triangle := (inclusion_jointly_surjective x).choose

theorem preferred_mem (x : Space) : x ∈ range (inclusion (preferredTriangle x)) :=
  (inclusion_jointly_surjective x).choose_spec

instance chartedSpace : ChartedSpace (CoordinateSpace 3) Space where
  atlas := range (fun s : Triangle => (parametrization s).symm)
  chartAt x := (parametrization (preferredTriangle x)).symm
  mem_chart_source x := by
    change x ∈ (parametrization (preferredTriangle x)).target
    rw [parametrization_target]
    exact preferred_mem x
  chart_mem_atlas x := mem_range_self _

theorem transition_holomorphic (s t : Triangle) :
    ContDiffOn ℂ ω ((parametrization s).trans (parametrization t).symm)
      ((parametrization s).trans (parametrization t).symm).source := by
  have h : ∀ z ∈ ((parametrization s).trans (parametrization t).symm).source,
      z ∈ (chartChange s t).source ∧
      ((parametrization s).trans (parametrization t).symm) z = chartChange s t z := by
    intro z hz
    exact parametrization_transition s t (by simpa using hz.2)
  exact ((chartChange_holomorphic s t).mono (fun z hz => (h z hz).1)).congr
    (fun z hz => (h z hz).2)

instance isManifold : IsManifold (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω Space := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨s, rfl⟩ := he
  obtain ⟨t, rfl⟩ := he'
  simpa using transition_holomorphic s t

instance secondCountableTopology : SecondCountableTopology Space := by
  let U : Triangle → Set Space := fun s => range (inclusion s)
  let (s : Triangle) : SecondCountableTopology (U s) :=
    (inclusion_openEmbedding s).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply secondCountableTopology_of_countable_cover
    (U := U) (fun s => (inclusion_openEmbedding s).isOpen_range)
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  exact mem_iUnion.mpr ⟨s, mem_range_self z⟩

/-- The local normal-crossings equations glue to a single complex-valued map. -/
def time (x : Space) : ℂ :=
  Triangle.time ((parametrization (preferredTriangle x)).symm x)

@[simp] theorem time_inclusion (s : Triangle) (z : CoordinateSpace 3) :
    time (inclusion s z) = Triangle.time z := by
  change Triangle.time ((parametrization (preferredTriangle (inclusion s z))).symm
    (inclusion s z)) = Triangle.time z
  have h := parametrization_transition s (preferredTriangle (inclusion s z))
    (preferred_mem (inclusion s z))
  rw [h.2]
  exact chartChange_preserves_time _ _ h.1

theorem time_comp_parametrization (s : Triangle) :
    time ∘ parametrization s = Triangle.time := by
  funext z
  exact time_inclusion s z

theorem time_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ ℂ) ω time := by
  intro x
  rw [contMDiffAt_iff_source]
  have hchart : chartAt (CoordinateSpace 3) x =
      (parametrization (preferredTriangle x)).symm := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, time_comp_parametrization]
    using Triangle.time_holomorphic.contMDiff.contMDiffAt.contMDiffWithinAt
      (s := univ) (x := (parametrization (preferredTriangle x)).symm x)

def referenceTriangle : Triangle := ⟨0, 0, false⟩

instance : Nonempty Space := ⟨inclusion referenceTriangle 0⟩

theorem inclusion_one (s t : Triangle) :
    inclusion s (fun _ => 1) = inclusion t (fun _ => 1) := by
  apply (inclusion_eq_iff s t _ _).mpr
  constructor
  · exact torus_subset_overlap _ _ (by intro i; exact one_ne_zero)
  · funext i
    change (∏ j, (1 : ℂ) ^ transition s t i j) = 1
    simp

instance preconnectedSpace : PreconnectedSpace Space := by
  have hcover : (⋃ s, range (inclusion s)) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
    exact mem_iUnion.mpr ⟨s, mem_range_self z⟩
  constructor
  rw [← hcover]
  apply isPreconnected_iUnion
  · refine ⟨inclusion referenceTriangle (fun _ => 1), mem_iInter.mpr fun s => ?_⟩
    exact ⟨fun _ => 1, inclusion_one s referenceTriangle⟩
  · intro s
    exact isPreconnected_range (inclusion_openEmbedding s).continuous

instance connectedSpace : ConnectedSpace Space :=
  { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }

theorem time_surjective : Function.Surjective time := by
  intro t
  refine ⟨inclusion referenceTriangle ![t, 1, 1], ?_⟩
  simp [Triangle.time]

/-- The dense torus is represented in a single reference chart. -/
def openTorus : Set Space := inclusion referenceTriangle '' torus

theorem inclusion_torus_subset (s : Triangle) : inclusion s '' torus ⊆ openTorus := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨chartChange s referenceTriangle z, monomial_mapsTo_torus _ hz, ?_⟩
  exact ((inclusion_eq_iff s referenceTriangle z _).mpr
    ⟨torus_subset_overlap _ _ hz, rfl⟩).symm

theorem mem_openTorus_iff (x : Space) : x ∈ openTorus ↔ time x ≠ 0 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [time_inclusion]
    exact mul_ne_zero (mul_ne_zero (hz 0) (hz 1)) (hz 2)
  · intro hx
    obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
    have hz : z ∈ torus := by
      have h : (z 0 ≠ 0 ∧ z 1 ≠ 0) ∧ z 2 ≠ 0 := by
        simpa only [time_inclusion, Triangle.time, mul_ne_zero_iff] using hx
      intro i
      fin_cases i
      · exact h.1.1
      · exact h.1.2
      · exact h.2
    exact inclusion_torus_subset s ⟨z, hz, rfl⟩

theorem openTorus_isOpen : IsOpen openTorus := by
  have he : openTorus = {x | time x ≠ 0} := Set.ext mem_openTorus_iff
  rw [he]
  exact isOpen_ne_fun time_holomorphic.continuous continuous_const

theorem openTorus_dense : Dense openTorus := by
  intro x
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  apply closure_mono (inclusion_torus_subset s)
  exact mem_closure_image (inclusion_openEmbedding s).continuous.continuousAt (torus_dense z)

theorem inclusion_holomorphic (s : Triangle) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (inclusion s) := by
  have he : (parametrization s).symm ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω Space :=
    IsManifold.subset_maximalAtlas (mem_range_self s)
  have h := contMDiffOn_symm_of_mem_maximalAtlas he
  change ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 3))
    (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (inclusion s) univ at h
  exact contMDiffOn_univ.mp h

/-- Descent of a compatible family of maps, using the already constructed
gluing. This does not assert compatibility or regularity as extra axioms. -/
def descend {Y : Type*} (f : Triangle → CoordinateSpace 3 → Y) (x : Space) : Y :=
  f (preferredTriangle x) ((parametrization (preferredTriangle x)).symm x)

theorem descend_inclusion {Y : Type*} (f : Triangle → CoordinateSpace 3 → Y)
    (h : ∀ s t z, z ∈ (chartChange s t).source → f t (chartChange s t z) = f s z)
    (s : Triangle) (z : CoordinateSpace 3) : descend f (inclusion s z) = f s z := by
  change f (preferredTriangle (inclusion s z))
    ((parametrization (preferredTriangle (inclusion s z))).symm (inclusion s z)) = f s z
  have he := parametrization_transition s (preferredTriangle (inclusion s z))
    (preferred_mem (inclusion s z))
  rw [he.2]
  exact h _ _ _ he.1

theorem descend_holomorphic {F H Y : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace Y] [ChartedSpace H Y]
    (I : ModelWithCorners ℂ F H) (f : Triangle → CoordinateSpace 3 → Y)
    (h : ∀ s t z, z ∈ (chartChange s t).source → f t (chartChange s t z) = f s z)
    (hf : ∀ s, ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3)) I ω (f s)) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3)) I ω (descend f) := by
  have hcomp (s : Triangle) : descend f ∘ parametrization s = f s := by
    funext z
    exact descend_inclusion f h s z
  intro x
  rw [contMDiffAt_iff_source]
  have hchart : chartAt (CoordinateSpace 3) x =
      (parametrization (preferredTriangle x)).symm := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, hcomp] using
    (hf (preferredTriangle x)).contMDiffAt.contMDiffWithinAt
      (s := univ) (x := (parametrization (preferredTriangle x)).symm x)

/-- Holomorphicity on an open set can be checked on all the explicit affine
charts, even when they are not the chosen preferred chart at a point. -/
theorem contMDiffOn_of_comp_inclusion {F H Y : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace Y] [ChartedSpace H Y]
    (I : ModelWithCorners ℂ F H) (f : Space → Y) {U : Set Space} (hU : IsOpen U)
    (hf : ∀ s, ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 3)) I ω
      (f ∘ inclusion s) (inclusion s ⁻¹' U)) :
    ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 3)) I ω f U := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  have he : inclusion (preferredTriangle x)
      ((parametrization (preferredTriangle x)).symm x) = x :=
    IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
      (inclusion (preferredTriangle x)) (inclusion_openEmbedding _) (preferred_mem x)
  have hm : (parametrization (preferredTriangle x)).symm x ∈
      inclusion (preferredTriangle x) ⁻¹' U := by
    change inclusion _ _ ∈ U
    rwa [he]
  have hlocal := (hf (preferredTriangle x)).contMDiffAt
    ((hU.preimage (inclusion_openEmbedding _).continuous).mem_nhds hm)
  have hchart : chartAt (CoordinateSpace 3) x =
      (parametrization (preferredTriangle x)).symm := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, Function.comp_def] using
    hlocal.contMDiffWithinAt (s := univ)

end Wikipedia.HopfProblem.ToricSpace
