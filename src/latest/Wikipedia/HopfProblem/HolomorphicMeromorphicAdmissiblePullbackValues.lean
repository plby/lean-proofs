import Wikipedia.HopfProblem.HolomorphicMeromorphicAdmissiblePullback
import Wikipedia.HopfProblem.HolomorphicMeromorphicRegular

/-!
# Regular values under individually admissible meromorphic pullback

At a regular target point, the actual holomorphic local representative
has denominator one and pulls back along any holomorphic map. Admissible
pullback therefore preserves regularity and its ordinary complex value.
An admissible denominator also supplies a nearby source point whose image
is regular for the original target section.
-/

open Set Topology TopologicalSpace
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

/-- An actual local holomorphic representative, written with denominator
one, pulls back correctly along an arbitrary holomorphic map. -/
theorem admissiblePullbackSection_holomorphic_representation
    (f : ContMDiffMap I J M N ω) {U V : Opens N} (hVU : V ≤ U)
    (s : Section J N U) (hs : PullbackAdmissible I J f U s)
    (p : HolomorphicFunctionSheaf.Section J N V)
    (hp : ∀ y : V, s (Set.inclusion hVU y) = sectionGerm J N V y p)
    (x : pullbackOpen I J f V) :
    admissiblePullbackSection I J f U s hs
        (Set.inclusion (pullbackOpen_mono I J f hVU) x) =
      sectionGerm I M (pullbackOpen I J f V) x (holomorphicPullback I J f V p) := by
  have hq : ∀ y : V, holomorphicGerm J N V y (1 : HolomorphicFunctionSheaf.Section J N V) ≠ 0 :=
    fun y => by rw [map_one]; exact one_ne_zero
  have hrep : ∀ y : V, s (Set.inclusion hVU y) = fraction J N V p 1 y := by
    intro y
    simpa only [fraction, map_one, div_one] using hp y
  have hxq : holomorphicGerm I M (pullbackOpen I J f V) x
      (holomorphicPullback I J f V (1 : HolomorphicFunctionSheaf.Section J N V)) ≠ 0 := by
    rw [map_one, map_one]
    exact one_ne_zero
  simpa only [fraction, map_one, div_one] using
    admissiblePullbackSection_eq_fraction I J f U s hs V hVU p 1 hq hrep x hxq

/-- A regular target germ remains regular under the sectionwise pullback;
no openness or injectivity hypothesis is imposed on the map. -/
theorem regularAt_admissiblePullbackSection (f : ContMDiffMap I J M N ω)
    {U : Opens N} (s : Section J N U) (hs : PullbackAdmissible I J f U s)
    (x : pullbackOpen I J f U) (hx : RegularAt J N s (pullbackPoint I J f U x)) :
    RegularAt I M (admissiblePullbackSection I J f U s hs) x := by
  obtain ⟨V, hVU, hxV, p, hp⟩ :=
    local_holomorphic_representation J N s (pullbackPoint I J f U x) hx
  refine ⟨holomorphicGerm I M (pullbackOpen I J f V) ⟨x.val, hxV⟩
    (holomorphicPullback I J f V p), ?_⟩
  exact (admissiblePullbackSection_holomorphic_representation I J f hVU s hs p hp
    ⟨x.val, hxV⟩).symm

/-- The actual ordinary value is preserved at every regular target point. -/
theorem value_admissiblePullbackSection_of_regularAt (f : ContMDiffMap I J M N ω)
    {U : Opens N} (s : Section J N U) (hs : PullbackAdmissible I J f U s)
    (x : pullbackOpen I J f U) (hx : RegularAt J N s (pullbackPoint I J f U x)) :
    value I M (admissiblePullbackSection I J f U s hs) x =
      value J N s (pullbackPoint I J f U x) := by
  obtain ⟨V, hVU, hxV, p, hp⟩ :=
    local_holomorphic_representation J N s (pullbackPoint I J f U x) hx
  have hpull := admissiblePullbackSection_holomorphic_representation I J f hVU s hs p hp
    ⟨x.val, hxV⟩
  have hsource := (value_eq_of_holomorphicGerm I M
    (admissiblePullbackSection I J f U s hs) x
    (holomorphicGerm I M (pullbackOpen I J f V) ⟨x.val, hxV⟩
      (holomorphicPullback I J f V p)) hpull.symm).trans
        (HolomorphicFunctionSheaf.stalkEval_germ I M (pullbackOpen I J f V) x.val hxV
          (holomorphicPullback I J f V p))
  have htarget := (value_eq_of_holomorphicGerm J N s (pullbackPoint I J f U x)
    (holomorphicGerm J N V ⟨f x.val, hxV⟩ p) (hp ⟨f x.val, hxV⟩).symm).trans
      (HolomorphicFunctionSheaf.stalkEval_germ J N V (f x.val) hxV p)
  exact hsource.trans htarget.symm

/-- A source point with an admissible denominator gives an actual source
point whose image is regular for the target section. Nonzero denominator
germs persist on a smaller open set, where their cozero locus is dense. -/
theorem exists_regular_image_of_admissible_pullback (f : ContMDiffMap I J M N ω)
    {U : Opens N} (s : Section J N U) (hs : PullbackAdmissible I J f U s)
    (x : pullbackOpen I J f U) :
    ∃ y : pullbackOpen I J f U, RegularAt J N s (pullbackPoint I J f U y) := by
  obtain ⟨P⟩ := hs x
  let q := holomorphicPullback I J f P.domain P.denominator
  obtain ⟨W, hWV, hxW, hWq⟩ :=
    HolomorphicFunctionSheaf.exists_open_restriction_germs_ne_zero I
      (pullbackOpen I J f P.domain) q x.val P.mem_domain P.pullback_denominator_ne_zero
  let qW := HolomorphicFunctionSheaf.restrictionAlgHom I M hWV q
  have hqd : Dense {y : W | qW y ≠ 0} :=
    HolomorphicFunctionSheaf.dense_cozero_of_germs_ne_zero I W qW hWq
  let : Nonempty W := ⟨⟨x.val, hxW⟩⟩
  obtain ⟨y, hyq⟩ := hqd.nonempty
  let hWU : W ≤ pullbackOpen I J f U :=
    hWV.trans (pullbackOpen_mono I J f P.le_domain)
  refine ⟨Set.inclusion hWU y, ?_⟩
  exact regularAt_of_local_fraction J N s P.numerator P.denominator (f y.val)
    (hWU y.property) (hWV y.property) (P.represents ⟨f y.val, hWV y.property⟩) hyq

end Wikipedia.HopfProblem.HolomorphicMeromorphic
