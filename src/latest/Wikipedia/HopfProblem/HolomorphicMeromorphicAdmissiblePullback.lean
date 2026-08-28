import Wikipedia.HopfProblem.HolomorphicMeromorphicAdmissiblePullbackBasic

/-!
# Pullback of an admissible individual meromorphic section

Choose an admissible local fraction at each source point. The holomorphic
cross-product identity makes its pulled-back value independent of that
choice. Nonzero denominator germs persist on smaller source neighborhoods,
so the chosen values form a genuine locally represented meromorphic section.
-/

open TopologicalSpace CategoryTheory
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

/-- The value determined by an admissible local fraction of one section.
This is not a map on the full target meromorphic fraction field. -/
noncomputable def admissiblePullbackGerm (f : ContMDiffMap I J M N ω)
    (U : Opens N) (s : Section J N U) (hs : PullbackAdmissible I J f U s)
    (x : pullbackOpen I J f U) : Germ I M x.val :=
  (Classical.choice (hs x)).value I J

/-- Any admissible presentation computes the same source value. -/
theorem admissiblePullbackGerm_eq_presentation (f : ContMDiffMap I J M N ω)
    (U : Opens N) (s : Section J N U) (hs : PullbackAdmissible I J f U s)
    (x : pullbackOpen I J f U) (P : AdmissiblePullbackPresentation I J f U s x) :
    admissiblePullbackGerm I J f U s hs x = P.value I J :=
  AdmissiblePullbackPresentation.value_eq I J (Classical.choice (hs x)) P

/-- Individually admissible local fractions give an actual meromorphic
section on the full inverse image, for an arbitrary holomorphic map. -/
noncomputable def admissiblePullbackSection (f : ContMDiffMap I J M N ω)
    (U : Opens N) (s : Section J N U) (hs : PullbackAdmissible I J f U s) :
    Section I M (pullbackOpen I J f U) :=
  ⟨admissiblePullbackGerm I J f U s hs, by
    intro x
    let P := Classical.choice (hs x)
    obtain ⟨W, hWV, hxW, hWq⟩ :=
      HolomorphicFunctionSheaf.exists_open_nonzero_germ_neighborhood I
        (pullbackOpen I J f P.domain) (holomorphicPullback I J f P.domain P.denominator)
        x.val P.mem_domain P.pullback_denominator_ne_zero
    let hWU : W ≤ pullbackOpen I J f U :=
      hWV.trans (pullbackOpen_mono I J f P.le_domain)
    refine ⟨W, hxW, homOfLE hWU,
      HolomorphicFunctionSheaf.restrictionAlgHom I M hWV
        (holomorphicPullback I J f P.domain P.numerator),
      HolomorphicFunctionSheaf.restrictionAlgHom I M hWV
        (holomorphicPullback I J f P.domain P.denominator), ?_, ?_⟩
    · intro y hz
      exact hWq y.val y.property
        ((holomorphicGerm_restrict I M hWV y
          (holomorphicPullback I J f P.domain P.denominator)).symm.trans hz)
    · intro y
      let Q : AdmissiblePullbackPresentation I J f U s (Set.inclusion hWU y) :=
        { domain := P.domain
          le_domain := P.le_domain
          mem_domain := hWV y.property
          numerator := P.numerator
          denominator := P.denominator
          denominator_ne_zero := P.denominator_ne_zero
          represents := P.represents
          pullback_denominator_ne_zero := hWq y.val y.property }
      exact (admissiblePullbackGerm_eq_presentation I J f U s hs
        (Set.inclusion hWU y) Q).trans
          (fraction_restrict I M hWV (holomorphicPullback I J f P.domain P.numerator)
            (holomorphicPullback I J f P.domain P.denominator) y).symm⟩

/-- The constructed section agrees with every individually admissible
local numerator and denominator, not merely with the chosen presentations. -/
theorem admissiblePullbackSection_eq_fraction (f : ContMDiffMap I J M N ω)
    (U : Opens N) (s : Section J N U) (hs : PullbackAdmissible I J f U s)
    (V : Opens N) (hVU : V ≤ U) (p q : HolomorphicFunctionSheaf.Section J N V)
    (hq : ∀ y : V, holomorphicGerm J N V y q ≠ 0)
    (he : ∀ y : V, s (Set.inclusion hVU y) = fraction J N V p q y)
    (x : pullbackOpen I J f V)
    (hxq : holomorphicGerm I M (pullbackOpen I J f V) x
      (holomorphicPullback I J f V q) ≠ 0) :
    admissiblePullbackSection I J f U s hs
        (Set.inclusion (pullbackOpen_mono I J f hVU) x) =
      fraction I M (pullbackOpen I J f V)
        (holomorphicPullback I J f V p) (holomorphicPullback I J f V q) x := by
  let P : AdmissiblePullbackPresentation I J f U s
      (Set.inclusion (pullbackOpen_mono I J f hVU) x) :=
    { domain := V
      le_domain := hVU
      mem_domain := x.property
      numerator := p
      denominator := q
      denominator_ne_zero := hq
      represents := he
      pullback_denominator_ne_zero := hxq }
  exact admissiblePullbackGerm_eq_presentation I J f U s hs _ P

/-- The intrinsic specification of sectionwise admissible pullback is
agreement with every actual admissible local fraction presentation. -/
def IsAdmissiblePullback (f : ContMDiffMap I J M N ω) (U : Opens N)
    (s : Section J N U) (t : Section I M (pullbackOpen I J f U)) : Prop :=
  ∀ (x : pullbackOpen I J f U) (P : AdmissiblePullbackPresentation I J f U s x),
    t x = P.value I J

theorem admissiblePullbackSection_spec (f : ContMDiffMap I J M N ω)
    (U : Opens N) (s : Section J N U) (hs : PullbackAdmissible I J f U s) :
    IsAdmissiblePullback I J f U s (admissiblePullbackSection I J f U s hs) := by
  intro x P
  exact admissiblePullbackGerm_eq_presentation I J f U s hs x P

/-- Under admissibility, agreement with actual local pulled-back fractions
uniquely determines the genuine source meromorphic section. -/
theorem admissiblePullbackSection_unique (f : ContMDiffMap I J M N ω)
    (U : Opens N) (s : Section J N U) (hs : PullbackAdmissible I J f U s)
    (t : Section I M (pullbackOpen I J f U)) (ht : IsAdmissiblePullback I J f U s t) :
    t = admissiblePullbackSection I J f U s hs := by
  apply section_ext
  intro x
  let P := Classical.choice (hs x)
  exact (ht x P).trans (admissiblePullbackGerm_eq_presentation I J f U s hs x P).symm

/-- Existence and uniqueness of the meromorphic pullback of an individually
admissible section, with no openness hypothesis on the holomorphic map. -/
theorem existsUnique_admissiblePullbackSection (f : ContMDiffMap I J M N ω)
    (U : Opens N) (s : Section J N U) (hs : PullbackAdmissible I J f U s) :
    ∃! t : Section I M (pullbackOpen I J f U), IsAdmissiblePullback I J f U s t :=
  ⟨admissiblePullbackSection I J f U s hs,
    admissiblePullbackSection_spec I J f U s hs,
    fun t ht => admissiblePullbackSection_unique I J f U s hs t ht⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphic
