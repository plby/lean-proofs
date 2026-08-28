import Wikipedia.HopfProblem.HolomorphicMeromorphicLocalDiffeomorph

/-!
# Genuine meromorphic germs under partial biholomorphisms

The source of a partial biholomorphism has its original inherited manifold
structure. Restricting the map to this open source gives a global holomorphic
open map, and the original open inclusion induces an equivalence on germs.
Their actual stalk pullbacks therefore give the meromorphic coordinate change.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H'] (J : ModelWithCorners ℂ E' H')
  [TopologicalSpace N] [ChartedSpace H' N]

/-- The codomain restriction lemma also holds for analytic regularity,
directly in the original inherited charts of the open subset. -/
theorem analyticWithinAt_subtypeVal_comp_iff (U : Opens N) (f : M → U)
    (s : Set M) (x : M) :
    ContMDiffWithinAt I J ω (Subtype.val ∘ f) s x ↔
      ContMDiffWithinAt I J ω f s x :=
  ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..

/-- The actual inclusion of an original open subset. -/
def openInclusionMap (U : Opens M) : ContMDiffMap I I U M ω :=
  ⟨Subtype.val, contMDiff_subtype_val⟩

@[simp] theorem openInclusionMap_apply (U : Opens M) (x : U) :
    openInclusionMap I U x = x.val := rfl

theorem openInclusionMap_isOpenMap (U : Opens M) : IsOpenMap (openInclusionMap I U) :=
  U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap

/-- Open inclusions are local biholomorphisms for the inherited charts. -/
theorem openInclusionMap_isLocalDiffeomorph (U : Opens M) :
    IsLocalDiffeomorph I I ω (openInclusionMap I U) := by
  intro x
  let c := U.openPartialHomeomorphSubtypeCoe ⟨x⟩
  let d : PartialDiffeomorph I I U M ω :=
    { c.toPartialEquiv with
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        apply (analyticWithinAt_subtypeVal_comp_iff I I U c.symm c.target y).mp
        apply contMDiffWithinAt_id.congr_of_mem _ hy
        intro z hz
        exact c.right_inv hz }
  exact ⟨d, by trivial, fun _ _ => rfl⟩

namespace PartialBiholomorph

variable (e : PartialDiffeomorph I J M N ω)

/-- The genuine source open set, with its inherited manifold structure. -/
def sourceOpen : Opens M := ⟨e.source, e.open_source⟩

/-- The genuine target open set, with its inherited manifold structure. -/
def targetOpen : Opens N := ⟨e.target, e.open_target⟩

/-- The partial map restricted to its actual source is globally holomorphic. -/
def sourceMap : ContMDiffMap I J (sourceOpen I J e) N ω :=
  ⟨fun x => e x.val, fun x =>
    contMDiffAt_subtype_iff.mpr
      (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds x.property))⟩

@[simp] theorem sourceMap_apply (x : sourceOpen I J e) :
    sourceMap I J e x = e x.val := rfl

theorem sourceMap_isLocalDiffeomorph :
    IsLocalDiffeomorph I J ω (sourceMap I J e) := by
  intro x
  exact (openInclusionMap_isLocalDiffeomorph I (sourceOpen I J e) x).comp J N
    (e.isLocalDiffeomorphAt I J ω x.property)

theorem sourceMap_isOpenMap : IsOpenMap (sourceMap I J e) :=
  (sourceMap_isLocalDiffeomorph I J e).isOpenMap

variable [I.Boundaryless] [IsManifold I ω M]
  [J.Boundaryless] [IsManifold J ω N]

/-- The native source-open inclusion identifies the actual germs on that
open subset with the original ambient germs. -/
def inclusionGermEquiv (U : Opens M) (x : U) :
    Germ I M x.val ≃+* Germ I U x :=
  germPullbackEquivOfIsLocalDiffeomorphAt I I (openInclusionMap I U)
    (openInclusionMap_isOpenMap I U) x (openInclusionMap_isLocalDiffeomorph I U x)

/-- Coordinate change for genuine meromorphic germs under an actual
partial biholomorphism, without replacing either manifold's atlas. -/
def germEquiv (x : M) (hx : x ∈ e.source) :
    Germ J N (e x) ≃+* Germ I M x :=
  (germPullbackEquivOfIsLocalDiffeomorphAt I J (sourceMap I J e)
    (sourceMap_isOpenMap I J e) ⟨x, hx⟩
    (sourceMap_isLocalDiffeomorph I J e ⟨x, hx⟩)).trans
      (inclusionGermEquiv I (sourceOpen I J e) ⟨x, hx⟩).symm

/-- Its defining compatibility is equality of the actual native pullbacks
into the source-open germ ring. -/
theorem inclusion_pullback_germEquiv (x : M) (hx : x ∈ e.source)
    (a : Germ J N (e x)) :
    germPullback I I (openInclusionMap I (sourceOpen I J e))
      (openInclusionMap_isOpenMap I (sourceOpen I J e)) ⟨x, hx⟩
      (germEquiv I J e x hx a) =
    germPullback I J (sourceMap I J e) (sourceMap_isOpenMap I J e) ⟨x, hx⟩ a :=
  (inclusionGermEquiv I (sourceOpen I J e) ⟨x, hx⟩).apply_symm_apply _

end PartialBiholomorph

end Wikipedia.HopfProblem.HolomorphicMeromorphic
