import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackFunctor
import Wikipedia.HopfProblem.HolomorphicMeromorphicRegular

/-!
# Regularity and actual values under meromorphic pullback

The categorical holomorphic stalk pullback preserves the original stalk
evaluation, as is checked on genuine local holomorphic representatives.
It therefore sends regular meromorphic germs to regular germs and
preserves their actual complex values. Local holomorphic representative
agreement also pulls back on the literal inverse-image neighborhoods.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  (I : ModelWithCorners ℂ E H) [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℂ E' H') [TopologicalSpace N] [ChartedSpace H' N]

/-- Pullback of the actual holomorphic local ring preserves its original
evaluation, because local composition preserves the value at the base point. -/
@[simp] theorem stalkEval_holomorphicPullbackStalk (f : ContMDiffMap I J M N ω)
    (x : M) (a : HolomorphicStalk J N (f x)) :
    HolomorphicFunctionSheaf.stalkEval I M x (holomorphicPullbackStalk I J f x a) =
      HolomorphicFunctionSheaf.stalkEval J N (f x) a := by
  obtain ⟨U, hxU, s, rfl⟩ := (HolomorphicFunctionSheaf.presheaf J N).exists_germ_eq a
  exact (congrArg (HolomorphicFunctionSheaf.stalkEval I M x)
    (holomorphicPullbackStalk_germ I J f U x hxU s)).trans
      ((HolomorphicFunctionSheaf.stalkEval_germ I M (pullbackOpen I J f U) x hxU
        (holomorphicPullback I J f U s)).trans
          (HolomorphicFunctionSheaf.stalkEval_germ J N U (f x) hxU s).symm)

theorem stalkEval_comp_holomorphicPullbackStalk (f : ContMDiffMap I J M N ω) (x : M) :
    (HolomorphicFunctionSheaf.stalkEval I M x).comp (holomorphicPullbackStalk I J f x) =
      HolomorphicFunctionSheaf.stalkEval J N (f x) := by
  apply RingHom.ext
  intro a
  exact stalkEval_holomorphicPullbackStalk I J f x a

variable [I.Boundaryless] [IsManifold I ω M] [J.Boundaryless] [IsManifold J ω N]

/-- A regular target germ pulls back to the actual image of its holomorphic
representative in the source local ring. -/
theorem regularAt_pullbackSection (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    {U : Opens N} (s : Section J N U) (x : pullbackOpen I J f U)
    (hx : RegularAt J N s (pullbackPoint I J f U x)) :
    RegularAt I M (pullbackSection I J f hf U s) x := by
  obtain ⟨p, hp⟩ := hx
  refine ⟨holomorphicPullbackStalk I J f x.val p, ?_⟩
  exact (germPullback_ofHolomorphicGerm I J f hf x.val p).symm.trans
    (congrArg (germPullback I J f hf x.val) hp)

/-- At regular target germs, the canonical ordinary value is preserved
by the genuine meromorphic pullback. -/
theorem value_pullbackSection_of_regularAt (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    {U : Opens N} (s : Section J N U) (x : pullbackOpen I J f U)
    (hx : RegularAt J N s (pullbackPoint I J f U x)) :
    value I M (pullbackSection I J f hf U s) x =
      value J N s (pullbackPoint I J f U x) := by
  obtain ⟨p, hp⟩ := hx
  have hpull : ofHolomorphicGerm I M x.val (holomorphicPullbackStalk I J f x.val p) =
      pullbackSection I J f hf U s x :=
    (germPullback_ofHolomorphicGerm I J f hf x.val p).symm.trans
      (congrArg (germPullback I J f hf x.val) hp)
  exact (value_eq_of_holomorphicGerm I M (pullbackSection I J f hf U s) x _ hpull).trans
    ((stalkEval_holomorphicPullbackStalk I J f x.val p).trans
      (value_eq_of_holomorphicGerm J N s (pullbackPoint I J f U x) p hp).symm)

/-- An actual local holomorphic representative pulls back to a local
holomorphic representative with agreement as full meromorphic germs. -/
theorem pullbackSection_holomorphic_representation (f : ContMDiffMap I J M N ω)
    (hf : IsOpenMap f) {U V : Opens N} (hVU : V ≤ U) (s : Section J N U)
    (p : HolomorphicFunctionSheaf.Section J N V)
    (hp : ∀ y : V, s (Set.inclusion hVU y) = sectionGerm J N V y p)
    (x : pullbackOpen I J f V) :
    pullbackSection I J f hf U s (Set.inclusion (pullbackOpen_mono I J f hVU) x) =
      sectionGerm I M (pullbackOpen I J f V) x (holomorphicPullback I J f V p) :=
  (congrArg (germPullback I J f hf x.val) (hp (pullbackPoint I J f V x))).trans
    (germPullback_sectionGerm I J f hf V p x)

/-- The target's actual regular representative gives, on a genuine
inverse-image neighborhood, a simultaneously compatible source representative. -/
theorem local_holomorphic_representation_pullback (f : ContMDiffMap I J M N ω)
    (hf : IsOpenMap f) {U : Opens N} (s : Section J N U) (x : pullbackOpen I J f U)
    (hx : RegularAt J N s (pullbackPoint I J f U x)) :
    ∃ (V : Opens N) (hVU : V ≤ U) (_hxV : f x.val ∈ V)
      (p : HolomorphicFunctionSheaf.Section J N V),
      (∀ y : V, s (Set.inclusion hVU y) = sectionGerm J N V y p) ∧
      ∀ y : pullbackOpen I J f V,
        pullbackSection I J f hf U s (Set.inclusion (pullbackOpen_mono I J f hVU) y) =
          sectionGerm I M (pullbackOpen I J f V) y (holomorphicPullback I J f V p) := by
  obtain ⟨V, hVU, hxV, p, hp⟩ :=
    local_holomorphic_representation J N s (pullbackPoint I J f U x) hx
  exact ⟨V, hVU, hxV, p, hp, pullbackSection_holomorphic_representation I J f hf hVU s p hp⟩

/-- Pointwise values on a pulled-back local holomorphic representative
are the literal compositions of the original representative's values. -/
theorem value_pullbackSection_eq_of_holomorphic_representation
    (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    {U V : Opens N} (hVU : V ≤ U) (s : Section J N U)
    (p : HolomorphicFunctionSheaf.Section J N V)
    (hp : ∀ y : V, s (Set.inclusion hVU y) = sectionGerm J N V y p)
    (x : pullbackOpen I J f V) :
    value I M (pullbackSection I J f hf U s)
        (Set.inclusion (pullbackOpen_mono I J f hVU) x) = p (pullbackPoint I J f V x) := by
  have he := pullbackSection_holomorphic_representation I J f hf hVU s p hp x
  exact (value_eq_of_holomorphicGerm I M (pullbackSection I J f hf U s)
    (Set.inclusion (pullbackOpen_mono I J f hVU) x)
    (holomorphicGerm I M (pullbackOpen I J f V) x (holomorphicPullback I J f V p))
    he.symm).trans
      (HolomorphicFunctionSheaf.stalkEval_germ I M (pullbackOpen I J f V) x.val x.property
        (holomorphicPullback I J f V p))

end Wikipedia.HopfProblem.HolomorphicMeromorphic
