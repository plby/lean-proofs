import Wikipedia.HopfProblem.TrianglePeriodFamilyTopology

/-!
# Actual product charts from continuous sections of a covering quotient

A continuous section on an open set is an open embedding because the base
quotient is a local homeomorphism. Inserting this section in the diagonal
quotient gives a homeomorphism from the full inverse image of the open set
to its product with the original fibre.
-/

noncomputable section

open Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F]

/-- Insert a specified continuous base lift in the actual diagonal quotient. -/
def sectionMap (U : Opens (BaseSpace G B)) (s : C(U, B))
    (x : U × F) : Space G B F :=
  quotient G B F (s x.1, x.2)

theorem sectionMap_continuous (U : Opens (BaseSpace G B)) (s : C(U, B)) :
    Continuous (sectionMap (F := F) U s) :=
  (quotient_continuous G B F).comp (s.continuous.prodMap continuous_id)

/-- A continuous section of the quotient covering over an open set is open. -/
theorem baseSection_openEmbedding
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) : IsOpenEmbedding s := by
  apply hq.isCoveringMap.isLocalHomeomorph.isOpenEmbedding_of_comp _ s.continuous
  have hcomp : baseQuotient G B ∘ s = (Subtype.val : U → BaseSpace G B) :=
    funext hs
  rw [hcomp]
  exact U.isOpenEmbedding'

omit [TopologicalSpace F] in
@[simp] theorem projection_sectionMap (U : Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) (x : U × F) :
    projection G B F (sectionMap U s x) = (x.1 : BaseSpace G B) :=
  hs x.1

omit [TopologicalSpace F] in
theorem sectionMap_injective
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) :
    Function.Injective (sectionMap (F := F) U s) := by
  intro x y hxy
  have hbase : x.1 = y.1 := Subtype.ext (by
    simpa only [projection_sectionMap U s hs] using
      congrArg (projection G B F) hxy)
  apply Prod.ext hbase
  apply fibreInclusion_injective hq (s y.1)
  simpa only [sectionMap, fibreInclusion, hbase] using hxy

omit [TopologicalSpace F] in
theorem sectionMap_range
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) :
    range (sectionMap (F := F) U s) = projection G B F ⁻¹' (U : Set _) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [mem_preimage, projection_sectionMap U s hs]
    exact x.1.property
  · intro hy
    obtain ⟨⟨z, f⟩, rfl⟩ := quotient_surjective G B F y
    change baseQuotient G B z ∈ U at hy
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp
      (hs ⟨baseQuotient G B z, hy⟩)
    refine ⟨(⟨baseQuotient G B z, hy⟩, g • f), ?_⟩
    exact (quotient_eq_iff G B F _ _).mpr ⟨g, Prod.ext hg rfl⟩

variable [ContinuousConstSMul G F]

/-- The actual section parametrization is an open embedding, not merely a bijection. -/
theorem sectionMap_openEmbedding
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) :
    IsOpenEmbedding (sectionMap (F := F) U s) :=
  .of_continuous_injective_isOpenMap (sectionMap_continuous U s)
    (sectionMap_injective hq U s hs)
    ((quotient_isOpenQuotientMap (F := F) hq).isOpenMap.comp
      ((baseSection_openEmbedding hq U s hs).isOpenMap.prodMap IsOpenMap.id))

/-- The product chart on the entire inverse image of the domain of a section. -/
def sectionHomeomorph
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) :
    (projection G B F ⁻¹' (U : Set _)) ≃ₜ (U × F) :=
  ((sectionMap_openEmbedding (F := F) hq U s hs).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (sectionMap_range hq U s hs))).symm

@[simp] theorem sectionHomeomorph_symm_coe
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) (x : U × F) :
    ((sectionHomeomorph hq U s hs).symm x : Space G B F) = sectionMap U s x := rfl

/-- The section chart retains the actual base projection in its first coordinate. -/
theorem sectionHomeomorph_projection
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x)
    (x : projection G B F ⁻¹' (U : Set _)) :
    ((sectionHomeomorph hq U s hs x).1 : BaseSpace G B) = projection G B F x.val := by
  have hp := projection_sectionMap U s hs (sectionHomeomorph hq U s hs x)
  have he : sectionMap U s (sectionHomeomorph hq U s hs x) = x.val :=
    congrArg Subtype.val ((sectionHomeomorph hq U s hs).symm_apply_apply x)
  rw [he] at hp
  exact hp.symm

/-- Evaluation on the actual representative inserted by the section. -/
@[simp] theorem sectionHomeomorph_apply_quotient
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (U : Opens (BaseSpace G B)) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) (x : U) (f : F) :
    sectionHomeomorph hq U s hs
      ⟨quotient G B F (s x, f), by
        change baseQuotient G B (s x) ∈ U
        rw [hs x]
        exact x.property⟩ = (x, f) :=
  (sectionHomeomorph hq U s hs).apply_symm_apply (x, f)

end Wikipedia.HopfProblem.DiagonalQuotient
