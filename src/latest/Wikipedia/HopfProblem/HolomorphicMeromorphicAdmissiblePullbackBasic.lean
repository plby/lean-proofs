import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackHolomorphic
import Wikipedia.HopfProblem.HolomorphicMeromorphicIdentity

/-!
# Pullback of individually admissible local meromorphic fractions

A holomorphic map need not induce a homomorphism on the full meromorphic
fraction fields. Nevertheless two representations of one fraction give the
same pulled-back fraction whenever both pulled-back denominator germs are
nonzero. This follows by mapping their holomorphic cross-product identity.
-/

open TopologicalSpace
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

/-- An equality of fractions survives an arbitrary holomorphic stalk map
provided the two individual denominator images are nonzero. -/
theorem admissible_stalk_fraction_eq (f : ContMDiffMap I J M N ω) (x : M)
    (p q r t : HolomorphicStalk J N (f x))
    (hq : holomorphicPullbackStalk I J f x q ≠ 0)
    (ht : holomorphicPullbackStalk I J f x t ≠ 0)
    (he : ofHolomorphicGerm J N (f x) p / ofHolomorphicGerm J N (f x) q =
      ofHolomorphicGerm J N (f x) r / ofHolomorphicGerm J N (f x) t) :
    ofHolomorphicGerm I M x (holomorphicPullbackStalk I J f x p) /
        ofHolomorphicGerm I M x (holomorphicPullbackStalk I J f x q) =
      ofHolomorphicGerm I M x (holomorphicPullbackStalk I J f x r) /
        ofHolomorphicGerm I M x (holomorphicPullbackStalk I J f x t) := by
  have hq₀ : q ≠ 0 := by
    intro hz
    apply hq
    rw [hz, map_zero]
  have ht₀ : t ≠ 0 := by
    intro hz
    apply ht
    rw [hz, map_zero]
  have hq₁ : ofHolomorphicGerm J N (f x) q ≠ 0 :=
    fun hz => hq₀ ((ofHolomorphicGerm_eq_zero_iff J N (f x) q).mp hz)
  have ht₁ : ofHolomorphicGerm J N (f x) t ≠ 0 :=
    fun hz => ht₀ ((ofHolomorphicGerm_eq_zero_iff J N (f x) t).mp hz)
  have hc : p * t = r * q := by
    apply ofHolomorphicGerm_injective J N (f x)
    simpa only [map_mul] using (div_eq_div_iff hq₁ ht₁).mp he
  have hq₂ : ofHolomorphicGerm I M x (holomorphicPullbackStalk I J f x q) ≠ 0 :=
    fun hz => hq ((ofHolomorphicGerm_eq_zero_iff I M x _).mp hz)
  have ht₂ : ofHolomorphicGerm I M x (holomorphicPullbackStalk I J f x t) ≠ 0 :=
    fun hz => ht ((ofHolomorphicGerm_eq_zero_iff I M x _).mp hz)
  apply (div_eq_div_iff hq₂ ht₂).mpr
  simpa only [RingHom.comp_apply, map_mul] using
    congrArg ((ofHolomorphicGerm I M x).comp (holomorphicPullbackStalk I J f x)) hc

omit [J.Boundaryless] [IsManifold J ω N] in
/-- Pulling back a local numerator and denominator agrees with applying
the actual holomorphic stalk map to those two germs separately. -/
theorem pullback_fraction_eq_stalk_fraction (f : ContMDiffMap I J M N ω)
    (U : Opens N) (p q : HolomorphicFunctionSheaf.Section J N U)
    (x : pullbackOpen I J f U) :
    fraction I M (pullbackOpen I J f U)
        (holomorphicPullback I J f U p) (holomorphicPullback I J f U q) x =
      ofHolomorphicGerm I M x.val
          (holomorphicPullbackStalk I J f x.val
            (holomorphicGerm J N U (pullbackPoint I J f U x) p)) /
        ofHolomorphicGerm I M x.val
          (holomorphicPullbackStalk I J f x.val
            (holomorphicGerm J N U (pullbackPoint I J f U x) q)) := by
  exact congrArg₂ (fun a b : HolomorphicStalk I M x.val =>
      ofHolomorphicGerm I M x.val a / ofHolomorphicGerm I M x.val b)
    (holomorphicPullbackStalk_germ I J f U x.val x.property p).symm
    (holomorphicPullbackStalk_germ I J f U x.val x.property q).symm

/-- Two actual local presentations, even on different target neighborhoods,
pull back equally at a point where both denominator pullbacks are nonzero. -/
theorem admissible_fraction_pullback_eq (f : ContMDiffMap I J M N ω)
    (U V : Opens N) (p q : HolomorphicFunctionSheaf.Section J N U)
    (r t : HolomorphicFunctionSheaf.Section J N V)
    (x : M) (hxU : f x ∈ U) (hxV : f x ∈ V)
    (hq : holomorphicGerm I M (pullbackOpen I J f U) ⟨x, hxU⟩
      (holomorphicPullback I J f U q) ≠ 0)
    (ht : holomorphicGerm I M (pullbackOpen I J f V) ⟨x, hxV⟩
      (holomorphicPullback I J f V t) ≠ 0)
    (he : fraction J N U p q ⟨f x, hxU⟩ = fraction J N V r t ⟨f x, hxV⟩) :
    fraction I M (pullbackOpen I J f U)
        (holomorphicPullback I J f U p) (holomorphicPullback I J f U q) ⟨x, hxU⟩ =
      fraction I M (pullbackOpen I J f V)
        (holomorphicPullback I J f V r) (holomorphicPullback I J f V t) ⟨x, hxV⟩ := by
  rw [pullback_fraction_eq_stalk_fraction, pullback_fraction_eq_stalk_fraction]
  apply admissible_stalk_fraction_eq I J f x
  · intro hz
    exact hq ((holomorphicPullbackStalk_germ I J f U x hxU q).symm.trans hz)
  · intro hz
    exact ht ((holomorphicPullbackStalk_germ I J f V x hxV t).symm.trans hz)
  · exact he

/-- A genuine local fraction presentation of one target section whose
denominator remains a nonzero holomorphic germ at the given source point. -/
structure AdmissiblePullbackPresentation (f : ContMDiffMap I J M N ω)
    (U : Opens N) (s : Section J N U) (x : pullbackOpen I J f U) where
  domain : Opens N
  le_domain : domain ≤ U
  mem_domain : f x.val ∈ domain
  numerator : HolomorphicFunctionSheaf.Section J N domain
  denominator : HolomorphicFunctionSheaf.Section J N domain
  denominator_ne_zero : ∀ y : domain, holomorphicGerm J N domain y denominator ≠ 0
  represents : ∀ y : domain,
    s (Set.inclusion le_domain y) = fraction J N domain numerator denominator y
  pullback_denominator_ne_zero :
    holomorphicGerm I M (pullbackOpen I J f domain) ⟨x.val, mem_domain⟩
      (holomorphicPullback I J f domain denominator) ≠ 0

/-- The source fraction supplied by an individually admissible presentation. -/
noncomputable def AdmissiblePullbackPresentation.value
    {f : ContMDiffMap I J M N ω} {U : Opens N} {s : Section J N U}
    {x : pullbackOpen I J f U} (P : AdmissiblePullbackPresentation I J f U s x) :
    Germ I M x.val :=
  fraction I M (pullbackOpen I J f P.domain)
    (holomorphicPullback I J f P.domain P.numerator)
    (holomorphicPullback I J f P.domain P.denominator) ⟨x.val, P.mem_domain⟩

/-- The pulled-back fraction does not depend on the chosen admissible
presentation. No injectivity or openness of the original map is assumed. -/
theorem AdmissiblePullbackPresentation.value_eq
    {f : ContMDiffMap I J M N ω} {U : Opens N} {s : Section J N U}
    {x : pullbackOpen I J f U} (P Q : AdmissiblePullbackPresentation I J f U s x) :
    P.value I J = Q.value I J := by
  apply admissible_fraction_pullback_eq I J f P.domain Q.domain
    P.numerator P.denominator Q.numerator Q.denominator x.val P.mem_domain Q.mem_domain
    P.pullback_denominator_ne_zero Q.pullback_denominator_ne_zero
  exact (P.represents ⟨f x.val, P.mem_domain⟩).symm.trans
    (Q.represents ⟨f x.val, Q.mem_domain⟩)

/-- Admissibility for an individual section: every source point has an
actual target fraction presentation with nonzero pulled-back denominator germ. -/
def PullbackAdmissible (f : ContMDiffMap I J M N ω) (U : Opens N)
    (s : Section J N U) : Prop :=
  ∀ x : pullbackOpen I J f U, Nonempty (AdmissiblePullbackPresentation I J f U s x)

end Wikipedia.HopfProblem.HolomorphicMeromorphic
