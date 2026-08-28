import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySectionTransition

/-!
# Constant section transitions on connected overlaps

Uniqueness of continuous lifts through the actual covering propagates a
deck transformation from one point throughout a preconnected section
domain. Freeness of the covering action makes this element unique.
-/

noncomputable section

open Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F]

omit [TopologicalSpace F] in
/-- A deck relation at one point determines two sections on a preconnected domain. -/
theorem baseSection_eq_smul_of_eq
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : Opens (BaseSpace G B)) [PreconnectedSpace U] (s t : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x)
    (ht : ∀ x : U, baseQuotient G B (t x) = x)
    (x : U) (g : G) (hg : t x = g • s x) (y : U) : t y = g • s y := by
  have he : baseQuotient G B ∘ (t : U → B) =
      baseQuotient G B ∘ (fun z : U => g • s z) := by
    funext z
    exact (ht z).trans ((hq.map_smul g).trans (hs z)).symm
  exact congrFun (hq.isCoveringMap.eq_of_comp_eq t.continuous
    ((hq.continuous_const_smul g).comp s.continuous) he x hg) y

omit [TopologicalSpace F] in
/-- Two sections on a pointed preconnected domain differ by a unique deck element. -/
theorem baseSection_existsUnique_smul
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : Opens (BaseSpace G B)) [PreconnectedSpace U] (s t : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x)
    (ht : ∀ x : U, baseQuotient G B (t x) = x) (x : U) :
    ∃! g : G, ∀ y : U, t y = g • s y := by
  obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp ((ht x).trans (hs x).symm)
  refine ⟨g, baseSection_eq_smul_of_eq hq U s t hs ht x g hg.symm, ?_⟩
  intro g' hg'
  let := hq.isCancelSMul
  exact IsCancelSMul.right_cancel _ _ (s x) ((hg' x).symm.trans hg.symm)

/-- On a preconnected overlap, one known deck relation determines the full chart transition. -/
theorem sectionHomeomorph_transition_of_eq [ContinuousConstSMul G F]
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : Opens (BaseSpace G B)) [PreconnectedSpace U] (s t : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x)
    (ht : ∀ x : U, baseQuotient G B (t x) = x)
    (x : U) (g : G) (hg : t x = g • s x) :
    (sectionHomeomorph (F := F) hq U s hs).symm.trans
        (sectionHomeomorph hq U t ht) = sectionTransitionHomeomorph U g :=
  sectionHomeomorph_transition hq U s t hs ht g
    (baseSection_eq_smul_of_eq hq U s t hs ht x g hg)

end Wikipedia.HopfProblem.DiagonalQuotient
