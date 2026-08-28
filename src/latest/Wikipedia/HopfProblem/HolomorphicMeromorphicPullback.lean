import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackHolomorphic

/-!
# Pullback of genuine meromorphic sections along holomorphic open maps

The injective map of actual holomorphic stalks extends to their fraction
fields. The pointwise maps of meromorphic germs preserve local fraction
representations on actual inverse-image neighborhoods. They therefore
give genuine ring homomorphisms on meromorphic sections, compatible with
restriction and with the original holomorphic functions.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H E' H' M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] [IsManifold I ω M]
  [J.Boundaryless] [IsManifold J ω N]

/-- The genuine meromorphic germ pullback, obtained by extending the proved
injective pullback of the actual holomorphic local rings. -/
def germPullback (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f) (x : M) :
    Germ J N (f x) →+* Germ I M x :=
  IsFractionRing.lift
    (g := (ofHolomorphicGerm I M x).comp (holomorphicPullbackStalk I J f x))
    ((ofHolomorphicGerm_injective I M x).comp
      (holomorphicPullbackStalk_injective I J f hf x))

theorem germPullback_injective (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f) (x : M) :
    Function.Injective (germPullback I J f hf x) :=
  (germPullback I J f hf x).injective

@[simp] theorem germPullback_ofHolomorphicGerm (f : ContMDiffMap I J M N ω)
    (hf : IsOpenMap f) (x : M) (a : HolomorphicStalk J N (f x)) :
    germPullback I J f hf x (ofHolomorphicGerm J N (f x) a) =
      ofHolomorphicGerm I M x (holomorphicPullbackStalk I J f x a) :=
  IsFractionRing.lift_algebraMap _ a

@[simp] theorem germPullback_sectionGerm (f : ContMDiffMap I J M N ω)
    (hf : IsOpenMap f) (U : Opens N) (s : HolomorphicFunctionSheaf.Section J N U)
    (x : pullbackOpen I J f U) :
    germPullback I J f hf x.val (sectionGerm J N U (pullbackPoint I J f U x) s) =
      sectionGerm I M (pullbackOpen I J f U) x (holomorphicPullback I J f U s) := by
  change germPullback I J f hf x.val
      (ofHolomorphicGerm J N (f x.val) (holomorphicGerm J N U ⟨f x.val, x.property⟩ s)) =
    ofHolomorphicGerm I M x.val
      (holomorphicGerm I M (pullbackOpen I J f U) x (holomorphicPullback I J f U s))
  exact (germPullback_ofHolomorphicGerm I J f hf x.val
    (holomorphicGerm J N U ⟨f x.val, x.property⟩ s)).trans
      (congrArg (ofHolomorphicGerm I M x.val)
        (holomorphicPullbackStalk_germ I J f U x.val x.property s))

@[simp] theorem germPullback_fraction (f : ContMDiffMap I J M N ω)
    (hf : IsOpenMap f) (U : Opens N) (p q : HolomorphicFunctionSheaf.Section J N U)
    (x : pullbackOpen I J f U) :
    germPullback I J f hf x.val (fraction J N U p q (pullbackPoint I J f U x)) =
      fraction I M (pullbackOpen I J f U)
        (holomorphicPullback I J f U p) (holomorphicPullback I J f U q) x := by
  change germPullback I J f hf x.val
      (sectionGerm J N U ⟨f x.val, x.property⟩ p /
        sectionGerm J N U ⟨f x.val, x.property⟩ q) =
    sectionGerm I M (pullbackOpen I J f U) x (holomorphicPullback I J f U p) /
      sectionGerm I M (pullbackOpen I J f U) x (holomorphicPullback I J f U q)
  rw [map_div₀]
  exact congrArg₂ (fun a b : Germ I M x.val => a / b)
    (germPullback_sectionGerm I J f hf U p x) (germPullback_sectionGerm I J f hf U q x)

omit [I.Boundaryless] [IsManifold I ω M] [J.Boundaryless] [IsManifold J ω N] in
/-- An actual target denominator with nonzero germs stays a valid denominator
after pullback along an open holomorphic map. -/
theorem holomorphicPullback_nonzero_germs (f : ContMDiffMap I J M N ω)
    (hf : IsOpenMap f) (U : Opens N) (q : HolomorphicFunctionSheaf.Section J N U)
    (hq : ∀ y : U, holomorphicGerm J N U y q ≠ 0) :
    ∀ x : pullbackOpen I J f U, holomorphicGerm I M (pullbackOpen I J f U) x
      (holomorphicPullback I J f U q) ≠ 0 := by
  intro x hx
  apply hq (pullbackPoint I J f U x)
  exact holomorphicPullbackStalk_injective I J f hf x.val
    ((holomorphicPullbackStalk_germ I J f U x.val x.property q).trans
      (hx.trans (map_zero (holomorphicPullbackStalk I J f x.val)).symm))

/-- Literal pointwise pullback of meromorphic germ-valued sections, with its
local representability proved using the actual inverse-image neighborhoods. -/
def pullbackSection (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (U : Opens N) (s : Section J N U) : Section I M (pullbackOpen I J f U) :=
  ⟨fun x => germPullback I J f hf x.val (s (pullbackPoint I J f U x)), by
    intro x
    obtain ⟨V, hVU, hxV, p, q, hq, hs⟩ :=
      local_representation J N s (pullbackPoint I J f U x)
    refine ⟨pullbackOpen I J f V, hxV, homOfLE (pullbackOpen_mono I J f hVU),
      holomorphicPullback I J f V p, holomorphicPullback I J f V q,
      holomorphicPullback_nonzero_germs I J f hf V q hq, ?_⟩
    intro y
    change germPullback I J f hf y.val
        (s (Set.inclusion hVU (pullbackPoint I J f V y))) = _
    rw [hs (pullbackPoint I J f V y)]
    exact germPullback_fraction I J f hf V p q y⟩

@[simp] theorem pullbackSection_apply (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (U : Opens N) (s : Section J N U) (x : pullbackOpen I J f U) :
    pullbackSection I J f hf U s x =
      germPullback I J f hf x.val (s (pullbackPoint I J f U x)) := rfl

/-- Pullback is a homomorphism of the actual meromorphic section rings. -/
def pullbackRingHom (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f) (U : Opens N) :
    Section J N U →+* Section I M (pullbackOpen I J f U) where
  toFun := pullbackSection I J f hf U
  map_zero' := by
    ext x
    exact map_zero (germPullback I J f hf x.val)
  map_one' := by
    ext x
    exact map_one (germPullback I J f hf x.val)
  map_add' s t := by
    ext x
    exact map_add (germPullback I J f hf x.val) _ _
  map_mul' s t := by
    ext x
    exact map_mul (germPullback I J f hf x.val) _ _

@[simp] theorem pullbackRingHom_apply (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (U : Opens N) (s : Section J N U) :
    pullbackRingHom I J f hf U s = pullbackSection I J f hf U s := rfl

@[simp] theorem pullbackSection_restrict (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    {U V : Opens N} (h : U ≤ V) (s : Section J N V) :
    pullbackSection I J f hf U (restrict J N h s) =
      restrict I M (pullbackOpen_mono I J f h) (pullbackSection I J f hf V s) := by
  ext x
  rfl

theorem pullbackRingHom_restriction (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    {U V : Opens N} (h : U ≤ V) :
    (pullbackRingHom I J f hf U).comp (restrictionRingHom J N h) =
      (restrictionRingHom I M (pullbackOpen_mono I J f h)).comp
        (pullbackRingHom I J f hf V) := by
  apply RingHom.ext
  intro s
  exact pullbackSection_restrict I J f hf h s

@[simp] theorem pullbackSection_ofHolomorphic (f : ContMDiffMap I J M N ω)
    (hf : IsOpenMap f) (U : Opens N) (s : HolomorphicFunctionSheaf.Section J N U) :
    pullbackSection I J f hf U (ofHolomorphic J N U s) =
      ofHolomorphic I M (pullbackOpen I J f U) (holomorphicPullback I J f U s) := by
  ext x
  simp only [pullbackSection_apply, ofHolomorphic_apply, germPullback_sectionGerm]

@[simp] theorem pullbackSection_ofFraction (f : ContMDiffMap I J M N ω)
    (hf : IsOpenMap f) (U : Opens N) (p q : HolomorphicFunctionSheaf.Section J N U)
    (hq : ∀ y : U, holomorphicGerm J N U y q ≠ 0) :
    pullbackSection I J f hf U (ofFraction J N U p q hq) =
      ofFraction I M (pullbackOpen I J f U) (holomorphicPullback I J f U p)
        (holomorphicPullback I J f U q)
        (holomorphicPullback_nonzero_germs I J f hf U q hq) := by
  ext x
  simp only [pullbackSection_apply, ofFraction_apply, germPullback_fraction]

/-- Surjectivity of the original map makes actual meromorphic pullback injective. -/
theorem pullbackRingHom_injective (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (hsurj : Function.Surjective f) (U : Opens N) :
    Function.Injective (pullbackRingHom I J f hf U) := by
  intro s t hst
  apply section_ext
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hsurj y
  apply germPullback_injective I J f hf x
  exact congrArg (fun a : Section I M (pullbackOpen I J f U) => a ⟨x, hy⟩) hst

end Wikipedia.HopfProblem.HolomorphicMeromorphic
