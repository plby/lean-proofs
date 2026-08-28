import Wikipedia.HopfProblem.CoveringManifold

/-!
# Finite free quotient coverings without local compactness

The actual orbit quotient of a finite continuous free action on a Hausdorff
space is a quotient covering.  A finite intersection of separating
neighbourhoods proves the required disjointness directly; no local compactness
assumption is needed.  The finite orbit quotient is Hausdorff even without
freeness, because the orbit relation is a finite union of closed graphs.

For holomorphic actions on a complex manifold, the covering's actual local
lifts give its complex atlas and a holomorphic quotient projection.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle.FiniteQuotient

variable (G A : Type*) [Group G] [MulAction G A]

/-- The actual orbit quotient, with the standard quotient topology. -/
abbrev Space := MulAction.orbitRel.Quotient G A

/-- The actual orbit projection. -/
def project : A → Space G A := Quotient.mk (MulAction.orbitRel G A)

theorem project_surjective : Function.Surjective (project G A) := Quotient.mk_surjective

theorem project_eq_iff_mem_orbit (x y : A) :
    project G A x = project G A y ↔ x ∈ MulAction.orbit G y := Quotient.eq''

@[simp] theorem project_smul (g : G) (x : A) :
    project G A (g • x) = project G A x :=
  (project_eq_iff_mem_orbit G A _ _).mpr ⟨g, rfl⟩

section Topology

variable [TopologicalSpace A]

theorem project_isQuotientMap : IsQuotientMap (project G A) :=
  isQuotientMap_quotient_mk'

theorem project_continuous : Continuous (project G A) :=
  (project_isQuotientMap G A).continuous

theorem project_isOpenQuotientMap [ContinuousConstSMul G A] :
    IsOpenQuotientMap (project G A) := MulAction.isOpenQuotientMap_quotientMk

theorem spaceCompactSpace [CompactSpace A] : CompactSpace (Space G A) := inferInstance

theorem spaceConnectedSpace [ConnectedSpace A] : ConnectedSpace (Space G A) :=
  (project_surjective G A).connectedSpace (project_continuous G A)

theorem spaceSecondCountableTopology [SecondCountableTopology A] [ContinuousConstSMul G A] :
    SecondCountableTopology (Space G A) :=
  (project_isQuotientMap G A).secondCountableTopology
    (project_isOpenQuotientMap G A).isOpenMap

/-- Finiteness makes the orbit relation closed; the open quotient therefore
is Hausdorff, without any local compactness or freeness assumption. -/
theorem spaceT2Space [Finite G] [T2Space A] [ContinuousConstSMul G A] :
    T2Space (Space G A) := by
  rw [t2_iff_isClosed_diagonal]
  have hq : IsOpenQuotientMap (Prod.map (project G A) (project G A)) :=
    (project_isOpenQuotientMap G A).prodMap (project_isOpenQuotientMap G A)
  rw [← hq.isQuotientMap.isClosed_preimage]
  have hc : IsClosed (⋃ g : G, {p : A × A | g • p.2 = p.1}) :=
    isClosed_iUnion_of_finite fun g =>
      isClosed_eq ((continuous_const_smul g).comp continuous_snd) continuous_fst
  convert hc using 1
  ext p
  simp only [Set.mem_preimage, Set.mem_diagonal_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
  exact project_eq_iff_mem_orbit G A p.1 p.2

variable [Finite G] [T2Space A] [ContinuousConstSMul G A] [IsCancelSMul G A]

/-- A finite free continuous action has a neighbourhood disjoint from every
nonidentity translate.  This uses only the Hausdorff separation axiom. -/
theorem exists_nhds_disjoint_translate (x : A) :
    ∃ U ∈ 𝓝 x, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  have hs : ∀ g : G, ∃ U ∈ 𝓝 x, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
    intro g
    by_cases hg : g = 1
    · exact ⟨univ, univ_mem, fun _ => hg⟩
    have hne : g • x ≠ x := by
      intro h
      apply hg
      apply IsCancelSMul.right_cancel g 1 x
      simpa only [one_smul] using h
    obtain ⟨V, W, hV, hW, hd⟩ := t2_separation_nhds hne
    refine ⟨(fun y : A => g • y) ⁻¹' V ∩ W,
      inter_mem ((continuous_const_smul g).continuousAt hV) hW, ?_⟩
    rintro ⟨z, ⟨y, hy, rfl⟩, hz⟩
    exact False.elim (Set.disjoint_left.mp hd hy.1 hz.2)
  choose U hU hdisj using hs
  refine ⟨⋂ g : G, U g, Filter.iInter_mem.mpr hU, ?_⟩
  intro g hg
  apply hdisj g
  obtain ⟨z, ⟨y, hy, rfl⟩, hz⟩ := hg
  exact ⟨g • y, ⟨y, Set.mem_iInter.mp hy g, rfl⟩, Set.mem_iInter.mp hz g⟩

/-- The quotient-covering structure on the actual finite orbit projection. -/
theorem project_isQuotientCoveringMap : IsQuotientCoveringMap (project G A) G where
  toIsQuotientMap := project_isQuotientMap G A
  continuous_const_smul := continuous_const_smul
  apply_eq_iff_mem_orbit := project_eq_iff_mem_orbit G A _ _
  disjoint := exists_nhds_disjoint_translate G A

theorem project_isCoveringMap : IsCoveringMap (project G A) :=
  (project_isQuotientCoveringMap G A).isCoveringMap

theorem project_isLocalHomeomorph : IsLocalHomeomorph (project G A) :=
  (project_isCoveringMap G A).isLocalHomeomorph

/-- A selected genuine local inverse of the quotient projection. -/
def localInverse (a : A) : OpenPartialHomeomorph (Space G A) A :=
  CoveringQuotient.localInverse (project_isQuotientCoveringMap G A) a

@[simp] theorem localInverse_symm (a : A) :
    (localInverse G A a).symm = project G A :=
  CoveringQuotient.localInverse_symm (project_isQuotientCoveringMap G A) a

theorem project_localInverse (a : A) {x : Space G A}
    (hx : x ∈ (localInverse G A a).source) : project G A (localInverse G A a x) = x :=
  CoveringQuotient.project_localInverse (project_isQuotientCoveringMap G A) a hx

/-- Every quotient fibre has exactly as many points as the acting group. -/
theorem fibre_card (x : Space G A) : Nat.card (project G A ⁻¹' {x}) = Nat.card G :=
  Nat.card_congr ((project_isQuotientCoveringMap G A).fiberEquivGroup
    ⟨(project_surjective G A x).choose, (project_surjective G A x).choose_spec⟩)

end Topology

section ComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace A] [ChartedSpace E A]

theorem continuousConstSMul_of_holomorphic
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) ω (fun a : A => g • a)) : ContinuousConstSMul G A where
  continuous_const_smul g := (hG g).continuous

variable [Finite G] [T2Space A] [ContinuousConstSMul G A] [IsCancelSMul G A]

/-- The complex quotient atlas constructed using local lifts of its covering. -/
@[instance_reducible] def chartedSpace : ChartedSpace E (Space G A) :=
  CoveringQuotient.chartedSpace (E := E) (project_isQuotientCoveringMap G A)

variable [IsManifold (modelWithCornersSelf ℂ E) ω A]
  (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ E) ω (fun a : A => g • a))

include hG

theorem isManifold :
    letI := chartedSpace (E := E) G A
    IsManifold (modelWithCornersSelf ℂ E) ω (Space G A) :=
  CoveringQuotient.isManifold (project_isQuotientCoveringMap G A) ω hG

theorem project_holomorphic :
    letI := chartedSpace (E := E) G A
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (project G A) :=
  CoveringQuotient.contMDiff_project (project_isQuotientCoveringMap G A) ω hG

theorem localInverse_holomorphic (a : A) :
    letI := chartedSpace (E := E) G A
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (localInverse G A a) (localInverse G A a).source :=
  CoveringQuotient.localInverse_holomorphic (project_isQuotientCoveringMap G A) ω hG a

end ComplexStructure

end Wikipedia.HopfProblem.HolomorphicCharacterBundle.FiniteQuotient
