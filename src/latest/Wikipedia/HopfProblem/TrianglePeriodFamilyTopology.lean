import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.OpenCover
import Wikipedia.HopfProblem.TrianglePeriodFamilyTopologyProper

/-!
# The actual diagonal quotient of a covering base and a fibre

A covering action on the base makes the diagonal action on a product a
covering action as well.  The resulting orbit quotient is locally a
product over the base quotient, with the full inverse image of each base
patch homeomorphic to that patch times the original fibre.
-/

noncomputable section

open Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable (G B F : Type*) [Group G] [MulAction G B] [MulAction G F]

/-- The actual base orbit quotient. -/
abbrev BaseSpace := MulAction.orbitRel.Quotient G B

/-- The actual orbit quotient for the diagonal product action. -/
abbrev Space := MulAction.orbitRel.Quotient G (B × F)

def baseQuotient : B → BaseSpace G B := Quotient.mk (MulAction.orbitRel G B)

def quotient : B × F → Space G B F := Quotient.mk (MulAction.orbitRel G (B × F))

theorem baseQuotient_surjective : Function.Surjective (baseQuotient G B) := Quotient.mk_surjective

theorem quotient_surjective : Function.Surjective (quotient G B F) := Quotient.mk_surjective

theorem quotient_eq_iff (x y : B × F) :
    quotient G B F x = quotient G B F y ↔ ∃ g : G, g • y = x := Quotient.eq''

@[simp] theorem quotient_smul (g : G) (x : B × F) :
    quotient G B F (g • x) = quotient G B F x :=
  (quotient_eq_iff G B F _ _).mpr ⟨g, rfl⟩

/-- The actual quotient of the product projection. -/
def projection : Space G B F → BaseSpace G B :=
  Quotient.lift (fun x : B × F => baseQuotient G B x.1) (by
    rintro x y ⟨g, hg⟩
    exact Quotient.sound ⟨g, congrArg Prod.fst hg⟩)

@[simp] theorem projection_quotient (x : B × F) :
    projection G B F (quotient G B F x) = baseQuotient G B x.1 := rfl

/-- The actual inclusion of a fibre represented over a chosen base lift. -/
def fibreInclusion (b : B) (f : F) : Space G B F := quotient G B F (b, f)

@[simp] theorem projection_fibreInclusion (b : B) (f : F) :
    projection G B F (fibreInclusion G B F b f) = baseQuotient G B b := rfl

theorem projection_surjective [Nonempty F] : Function.Surjective (projection G B F) := by
  intro b
  obtain ⟨x, rfl⟩ := baseQuotient_surjective G B b
  exact ⟨quotient G B F (x, Classical.choice ‹Nonempty F›), rfl⟩

variable [TopologicalSpace B] [TopologicalSpace F]

theorem baseQuotient_continuous : Continuous (baseQuotient G B) := continuous_quot_mk

theorem quotient_continuous : Continuous (quotient G B F) := continuous_quot_mk

theorem quotient_isQuotientMap : IsQuotientMap (quotient G B F) :=
  isQuotientMap_quotient_mk'

theorem projection_continuous : Continuous (projection G B F) :=
  (quotient_isQuotientMap G B F).continuous_iff.mpr
    ((baseQuotient_continuous G B).comp continuous_fst)

theorem fibreInclusion_continuous (b : B) : Continuous (fibreInclusion G B F b) :=
  (quotient_continuous G B F).comp (continuous_const.prodMk continuous_id)

variable {G B F}
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)

/-- The actual local inverse chosen from the base covering. -/
def baseLocalInverse (b : B) : OpenPartialHomeomorph (BaseSpace G B) B :=
  hq.isCoveringMap.isLocalHomeomorph.localInverseAt b

@[simp] theorem baseLocalInverse_symm (b : B) :
    (baseLocalInverse hq b).symm = baseQuotient G B :=
  hq.isCoveringMap.isLocalHomeomorph.localInverseAt_symm b

@[simp] theorem baseLocalInverse_baseQuotient (b : B) :
    baseLocalInverse hq b (baseQuotient G B b) = b :=
  hq.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self

theorem baseQuotient_localInverse (b : B) {x : BaseSpace G B}
    (hx : x ∈ (baseLocalInverse hq b).source) :
    baseQuotient G B (baseLocalInverse hq b x) = x :=
  hq.isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem hx

/-- An actual local-inverse patch in the base quotient. -/
def patch (b : B) : Opens (BaseSpace G B) :=
  ⟨(baseLocalInverse hq b).source, (baseLocalInverse hq b).open_source⟩

theorem baseQuotient_mem_patch (b : B) : baseQuotient G B b ∈ patch hq b :=
  hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source

theorem patch_cover : IsOpenCover (patch hq) := by
  apply IsOpenCover.of_sets (fun b => (baseLocalInverse hq b).open_source)
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨b, rfl⟩ := hq.surjective x
  exact mem_iUnion.mpr ⟨b, baseQuotient_mem_patch hq b⟩

include hq

omit [TopologicalSpace F] in
theorem fibreInclusion_injective (b : B) :
    Function.Injective (fibreInclusion G B F b) := by
  let := hq.isCancelSMul
  intro x y hxy
  obtain ⟨g, hg⟩ := (quotient_eq_iff G B F _ _).mp hxy
  have hb : g • b = b := congrArg Prod.fst hg
  have hg1 : g = 1 := IsCancelSMul.right_cancel _ _ b (hb.trans (one_smul G b).symm)
  simpa only [hg1, one_smul] using (congrArg Prod.snd hg).symm

omit [TopologicalSpace F] in
theorem fibreInclusion_range (b : B) :
    range (fibreInclusion G B F b) = projection G B F ⁻¹' {baseQuotient G B b} := by
  ext y
  constructor
  · rintro ⟨f, rfl⟩
    exact projection_fibreInclusion G B F b f
  · intro hy
    obtain ⟨⟨z, f⟩, rfl⟩ := quotient_surjective G B F y
    change baseQuotient G B z = baseQuotient G B b at hy
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp hy.symm
    refine ⟨g • f, ?_⟩
    exact (quotient_eq_iff G B F _ _).mpr ⟨g, Prod.ext hg rfl⟩

variable [ContinuousConstSMul G F]

/-- The same disjoint base neighborhoods prove that the diagonal action
on the whole product is a genuine quotient covering action. -/
theorem quotientCoveringMap : IsQuotientCoveringMap (quotient G B F) G where
  toIsQuotientMap := quotient_isQuotientMap G B F
  continuous_const_smul g := (hq.continuous_const_smul g).prodMap (continuous_const_smul g)
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint x := by
    obtain ⟨U, hU, hd⟩ := hq.disjoint x.1
    refine ⟨Prod.fst ⁻¹' U, continuous_fst.continuousAt hU, ?_⟩
    rintro g ⟨z, ⟨w, hw, rfl⟩, hz⟩
    exact hd g ⟨g • w.1, ⟨w.1, hw, rfl⟩, hz⟩

theorem quotient_isCoveringMap : IsCoveringMap (quotient G B F) :=
  (quotientCoveringMap (F := F) hq).isCoveringMap

theorem quotient_isOpenQuotientMap : IsOpenQuotientMap (quotient G B F) := by
  let := hq.toContinuousConstSMul
  exact MulAction.isOpenQuotientMap_quotientMk

/-- Inserting the chosen base lift defines the actual local product parametrization. -/
def patchMap (b : B) (x : patch hq b × F) : Space G B F :=
  quotient G B F (baseLocalInverse hq b x.1, x.2)

omit [TopologicalSpace F] [ContinuousConstSMul G F] in
@[simp] theorem projection_patchMap (b : B) (x : patch hq b × F) :
    projection G B F (patchMap hq b x) = (x.1 : BaseSpace G B) :=
  baseQuotient_localInverse hq b x.1.property

omit [TopologicalSpace F] [ContinuousConstSMul G F] in
theorem patchMap_injective (b : B) : Function.Injective (patchMap (F := F) hq b) := by
  let := hq.isCancelSMul
  intro x y hxy
  have hbase : x.1 = y.1 := Subtype.ext (by
    simpa only [projection_patchMap] using congrArg (projection G B F) hxy)
  obtain ⟨g, hg⟩ := (quotient_eq_iff G B F _ _).mp hxy
  have hgbase : g • baseLocalInverse hq b y.1 = baseLocalInverse hq b y.1 := by
    have he := congrArg Prod.fst hg
    change g • baseLocalInverse hq b y.1 = baseLocalInverse hq b x.1 at he
    simpa only [hbase] using he
  have hg1 : g = 1 := IsCancelSMul.right_cancel _ _ (baseLocalInverse hq b y.1)
    (hgbase.trans (one_smul G (baseLocalInverse hq b y.1)).symm)
  apply Prod.ext hbase
  simpa only [hg1, one_smul] using (congrArg Prod.snd hg).symm

omit [ContinuousConstSMul G F] in
theorem patchMap_continuous (b : B) : Continuous (patchMap (F := F) hq b) :=
  (quotient_continuous G B F).comp
    ((baseLocalInverse hq b).isOpenEmbedding_restrict.continuous.prodMap continuous_id)

theorem patchMap_openEmbedding (b : B) : IsOpenEmbedding (patchMap (F := F) hq b) :=
  .of_continuous_injective_isOpenMap (patchMap_continuous hq b) (patchMap_injective hq b)
    ((quotient_isOpenQuotientMap (F := F) hq).isOpenMap.comp
      ((baseLocalInverse hq b).isOpenEmbedding_restrict.isOpenMap.prodMap IsOpenMap.id))

omit [TopologicalSpace F] [ContinuousConstSMul G F] in
theorem patchMap_range (b : B) :
    range (patchMap (F := F) hq b) = projection G B F ⁻¹' (patch hq b : Set _) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [mem_preimage, projection_patchMap]
    exact x.1.property
  · intro hy
    obtain ⟨⟨z, f⟩, rfl⟩ := quotient_surjective G B F y
    change baseQuotient G B z ∈ patch hq b at hy
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp (baseQuotient_localInverse hq b hy)
    refine ⟨(⟨baseQuotient G B z, hy⟩, g • f), ?_⟩
    apply (quotient_eq_iff G B F _ _).mpr
    exact ⟨g, Prod.ext hg rfl⟩

/-- The full inverse image of a base patch is homeomorphic to the actual
product of that patch and the original fibre. -/
def patchHomeomorph (b : B) :
    (projection G B F ⁻¹' (patch hq b : Set _)) ≃ₜ (patch hq b × F) :=
  ((patchMap_openEmbedding (F := F) hq b).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (patchMap_range hq b))).symm

@[simp] theorem patchHomeomorph_symm_coe (b : B) (x : patch hq b × F) :
    ((patchHomeomorph hq b).symm x : Space G B F) = patchMap hq b x := rfl

/-- The local product homeomorphism preserves the actual base projection. -/
theorem patchHomeomorph_projection (b : B)
    (x : projection G B F ⁻¹' (patch hq b : Set _)) :
    ((patchHomeomorph hq b x).1 : BaseSpace G B) = projection G B F x.val := by
  have hp := projection_patchMap hq b (patchHomeomorph hq b x)
  have he : patchMap hq b (patchHomeomorph hq b x) = x.val :=
    congrArg Subtype.val ((patchHomeomorph hq b).symm_apply_apply x)
  rw [he] at hp
  exact hp.symm

/-- Every actual fibre of the descended projection is homeomorphic to
the original fibre, using one of the constructed local products. -/
def fibreHomeomorph (y : BaseSpace G B) : (projection G B F ⁻¹' {y}) ≃ₜ F :=
  fibreHomeomorphOfLocalTrivializations (projection G B F) (patch hq)
    (patchHomeomorph hq) (patchHomeomorph_projection hq)
    ((patch_cover hq).exists_mem y).choose y ((patch_cover hq).exists_mem y).choose_spec

/-- The fibre identification over a specified lift uses that lift's local inverse. -/
def fibreHomeomorphOver (b : B) :
    (projection G B F ⁻¹' {baseQuotient G B b}) ≃ₜ F :=
  fibreHomeomorphOfLocalTrivializations (projection G B F) (patch hq)
    (patchHomeomorph hq) (patchHomeomorph_projection hq)
    b (baseQuotient G B b) (baseQuotient_mem_patch hq b)

/-- The inverse of the actual fibre homeomorphism is the original fibre
inclusion followed by the diagonal orbit quotient. -/
@[simp] theorem fibreHomeomorphOver_symm_coe (b : B) (f : F) :
    ((fibreHomeomorphOver hq b).symm f : Space G B F) = fibreInclusion G B F b f := by
  change patchMap hq b (⟨baseQuotient G B b, baseQuotient_mem_patch hq b⟩, f) = _
  change quotient G B F (baseLocalInverse hq b (baseQuotient G B b), f) = _
  rw [baseLocalInverse_baseQuotient]
  rfl

theorem fibreInclusion_isEmbedding (b : B) : IsEmbedding (fibreInclusion G B F b) := by
  have h := IsEmbedding.subtypeVal.comp (fibreHomeomorphOver (F := F) hq b).symm.isEmbedding
  simpa only [Function.comp_def, fibreHomeomorphOver_symm_coe] using h

/-- Compact fibres and the constructed local products make the actual
diagonal-quotient projection proper. -/
theorem projection_proper [CompactSpace F] : IsProperMap (projection G B F) :=
  proper_of_localTrivializations (projection G B F) (projection_continuous G B F)
    (patch hq) (patch_cover hq) (patchHomeomorph hq) (patchHomeomorph_projection hq)

/-- Hausdorffness is proved from the base quotient and local fibre, not
assumed for the total diagonal quotient. -/
theorem spaceT2Space [T2Space (BaseSpace G B)] [T2Space F] : T2Space (Space G B F) :=
  t2Space_of_localTrivializations (projection G B F) (projection_continuous G B F)
    (patch hq) (patch_cover hq) (patchHomeomorph hq) (patchHomeomorph_projection hq)

omit [TopologicalSpace F] [ContinuousConstSMul G F] in
/-- A properly discontinuous action on a locally compact Hausdorff base
also supplies Hausdorffness of its actual quotient. -/
theorem baseT2Space [T2Space B] [LocallyCompactSpace B] [ProperlyDiscontinuousSMul G B] :
    T2Space (BaseSpace G B) := by
  let := hq.toContinuousConstSMul
  infer_instance

/-- A convenient version requiring only separation upstairs and proper
discontinuity of the base action. -/
theorem spaceT2Space_of_properlyDiscontinuous [T2Space B] [LocallyCompactSpace B]
    [ProperlyDiscontinuousSMul G B] [T2Space F] : T2Space (Space G B F) := by
  let := baseT2Space hq
  exact spaceT2Space (F := F) hq

theorem spaceSecondCountable [SecondCountableTopology B] [SecondCountableTopology F] :
    SecondCountableTopology (Space G B F) :=
  (quotient_isQuotientMap G B F).secondCountableTopology
    (quotient_isOpenQuotientMap (F := F) hq).isOpenMap

theorem spaceLocallyCompact [LocallyCompactSpace B] [LocallyCompactSpace F] :
    LocallyCompactSpace (Space G B F) :=
  (quotient_isOpenQuotientMap (F := F) hq).locallyCompactSpace

end Wikipedia.HopfProblem.DiagonalQuotient
