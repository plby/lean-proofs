import Wikipedia.HopfProblem.HolomorphicMeromorphicPartialDiffeomorphFractions
import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackLocalDiffeomorph
import Wikipedia.HopfProblem.HolomorphicMeromorphicValueCongr

/-!
# Arbitrary native meromorphic sections in partial biholomorphic coordinates

The inverse partial map acts on every original fraction stalk. Actual local
fraction presentations prove that this pointwise operation is a meromorphic
section on the genuine target domain. Both the full germs and their canonical
ordinary values are preserved, including the value convention at poles.
-/

noncomputable section

open Set Filter Topology TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H'] (J : ModelWithCorners ℂ E' H')
  [TopologicalSpace N] [ChartedSpace H' N]

namespace PartialBiholomorph

variable (e : PartialDiffeomorph I J M N ω)

/-- Smaller actual source neighborhoods give smaller transport domains. -/
theorem transportOpen_mono {U V : Opens M} (h : U ≤ V) :
    transportOpen I J e U ≤ transportOpen I J e V :=
  fun _ hy => ⟨hy.1, h hy.2⟩

/-- Pullback by the original inverse agrees with literal transported
holomorphic functions on true source-open stalks. -/
theorem inverse_source_stalk_transportHolomorphic (U : Opens M)
    (p : HolomorphicFunctionSheaf.Section I M U) (y : transportOpen I J e U) :
    holomorphicPullbackStalk J I (sourceMap J I e.symm) ⟨y.val, y.property.1⟩
      (holomorphicGerm I M U (inversePoint I J e U y) p) =
    holomorphicPullbackStalk J J (openInclusionMap J (sourceOpen J I e.symm))
      ⟨y.val, y.property.1⟩
      (holomorphicGerm J N (transportOpen I J e U) y (transportHolomorphic I J e U p)) := by
  refine (holomorphicPullbackStalk_germ J I (sourceMap J I e.symm)
    U ⟨y.val, y.property.1⟩ y.property.2 p).trans (Eq.trans ?_
      (holomorphicPullbackStalk_germ J J (openInclusionMap J (sourceOpen J I e.symm))
        (transportOpen I J e U) ⟨y.val, y.property.1⟩ y.property
        (transportHolomorphic I J e U p)).symm)
  refine holomorphicGerm_eq_of_eventuallyEq J (M := sourceOpen J I e.symm)
    ⟨y.val, y.property.1⟩ y.property.2 y.property
    (holomorphicPullback J I (sourceMap J I e.symm) U p)
    (holomorphicPullback J J (openInclusionMap J (sourceOpen J I e.symm))
      (transportOpen I J e U) (transportHolomorphic I J e U p)) ?_
  filter_upwards [
    (pullbackOpen J I (sourceMap J I e.symm) U).isOpen.mem_nhds y.property.2,
    (pullbackOpen J J (openInclusionMap J (sourceOpen J I e.symm))
      (transportOpen I J e U)).isOpen.mem_nhds y.property] with z hzU hzT
  exact (HolomorphicFunctionSheaf.extendManifoldSection_apply J
    (pullbackOpen J I (sourceMap J I e.symm) U)
    (holomorphicPullback J I (sourceMap J I e.symm) U p) z hzU).trans
      (HolomorphicFunctionSheaf.extendManifoldSection_apply J
        (pullbackOpen J J (openInclusionMap J (sourceOpen J I e.symm))
          (transportOpen I J e U))
        (holomorphicPullback J J (openInclusionMap J (sourceOpen J I e.symm))
          (transportOpen I J e U) (transportHolomorphic I J e U p)) z hzT).symm

variable [I.Boundaryless] [IsManifold I ω M]
  [J.Boundaryless] [IsManifold J ω N]

/-- The actual inverse germ equivalence sends a true holomorphic section
germ to its literal inverse-composed section germ. -/
theorem inverse_germEquiv_sectionGerm (U : Opens M)
    (p : HolomorphicFunctionSheaf.Section I M U) (y : transportOpen I J e U) :
    germEquiv J I e.symm y.val y.property.1
      (sectionGerm I M U (inversePoint I J e U y) p) =
    sectionGerm J N (transportOpen I J e U) y (transportHolomorphic I J e U p) := by
  apply (germPullback J J (openInclusionMap J (sourceOpen J I e.symm))
    (openInclusionMap_isOpenMap J (sourceOpen J I e.symm)) ⟨y.val, y.property.1⟩).injective
  refine (inclusion_pullback_germEquiv J I e.symm y.val y.property.1 _).trans ?_
  exact (germPullback_ofHolomorphicGerm J I (sourceMap J I e.symm)
    (sourceMap_isOpenMap J I e.symm) ⟨y.val, y.property.1⟩ _).trans
      ((congrArg (ofHolomorphicGerm J (sourceOpen J I e.symm) ⟨y.val, y.property.1⟩)
        (inverse_source_stalk_transportHolomorphic I J e U p y)).trans
          (germPullback_ofHolomorphicGerm J J (openInclusionMap J (sourceOpen J I e.symm))
            (openInclusionMap_isOpenMap J (sourceOpen J I e.symm))
            ⟨y.val, y.property.1⟩ _).symm)

/-- The inverse acts on actual local fraction germs, independently of
whether the denominator's scalar value is zero. -/
theorem inverse_germEquiv_fraction (U : Opens M)
    (p q : HolomorphicFunctionSheaf.Section I M U) (y : transportOpen I J e U) :
    germEquiv J I e.symm y.val y.property.1
      (fraction I M U p q (inversePoint I J e U y)) =
    fraction J N (transportOpen I J e U)
      (transportHolomorphic I J e U p) (transportHolomorphic I J e U q) y := by
  exact (map_div₀ (germEquiv J I e.symm y.val y.property.1) _ _).trans
    (congrArg₂ (fun a b : Germ J N y.val => a / b)
      (inverse_germEquiv_sectionGerm I J e U p y)
      (inverse_germEquiv_sectionGerm I J e U q y))

/-- Transport of an arbitrary locally represented meromorphic section,
not just a single globally presented fraction. -/
def transportSection (U : Opens M) (s : Section I M U) :
    Section J N (transportOpen I J e U) :=
  ⟨fun y => germEquiv J I e.symm y.val y.property.1 (s (inversePoint I J e U y)), by
    intro y
    obtain ⟨V, hVU, hyV, p, q, hq, hs⟩ := local_representation I M s (inversePoint I J e U y)
    refine ⟨transportOpen I J e V, ⟨y.property.1, hyV⟩,
      homOfLE (transportOpen_mono I J e hVU),
      transportHolomorphic I J e V p, transportHolomorphic I J e V q,
      transportHolomorphic_nonzero_germs I J e V q hq, ?_⟩
    intro z
    exact (congrArg (germEquiv J I e.symm z.val z.property.1)
      (hs (inversePoint I J e V z))).trans (inverse_germEquiv_fraction I J e V p q z)⟩

@[simp] theorem transportSection_apply (U : Opens M) (s : Section I M U)
    (y : transportOpen I J e U) :
    transportSection I J e U s y =
      germEquiv J I e.symm y.val y.property.1 (s (inversePoint I J e U y)) := rfl

/-- The local fraction chosen for the source section is transported to
an actual local fraction for its target section on the exact image domain. -/
theorem transportSection_local_fraction {U V : Opens M} (hVU : V ≤ U)
    (s : Section I M U) (p q : HolomorphicFunctionSheaf.Section I M V)
    (hs : ∀ x : V, s (Set.inclusion hVU x) = fraction I M V p q x)
    (y : transportOpen I J e V) :
    transportSection I J e U s (Set.inclusion (transportOpen_mono I J e hVU) y) =
      fraction J N (transportOpen I J e V)
        (transportHolomorphic I J e V p) (transportHolomorphic I J e V q) y :=
  (congrArg (germEquiv J I e.symm y.val y.property.1)
    (hs (inversePoint I J e V y))).trans (inverse_germEquiv_fraction I J e V p q y)

/-- Full native germ compatibility of arbitrary section transport. -/
theorem germEquiv_transportSection (U : Opens M) (s : Section I M U)
    (x : U) (hx : x.val ∈ e.source) :
    germEquiv I J e x.val hx
      (transportSection I J e U s (transportPoint I J e U x hx)) = s x := by
  obtain ⟨V, hVU, hxV, p, q, hq, hs⟩ := local_representation I M s x
  have he := transportSection_local_fraction I J e hVU s p q hs
    (transportPoint I J e V ⟨x.val, hxV⟩ hx)
  exact (congrArg (germEquiv I J e x.val hx) he).trans
    ((germEquiv_transportFraction I J e V p q hq ⟨x.val, hxV⟩ hx).trans
      (hs ⟨x.val, hxV⟩).symm)

/-- Transport specializes to the already constructed native fraction section. -/
theorem transportSection_ofFraction (U : Opens M)
    (p q : HolomorphicFunctionSheaf.Section I M U)
    (hq : ∀ x : U, holomorphicGerm I M U x q ≠ 0) :
    transportSection I J e U (ofFraction I M U p q hq) =
      transportFraction I J e U p q hq := by
  apply section_ext
  intro y
  exact inverse_germEquiv_fraction I J e U p q y

/-- The actual source-map and inclusion pullbacks of the two sections
have the same original meromorphic germ on the source open subset. -/
theorem source_pullback_transportSection (U : Opens M) (s : Section I M U)
    (x : U) (hx : x.val ∈ e.source) :
    pullbackSection I J (sourceMap I J e) (sourceMap_isOpenMap I J e)
        (transportOpen I J e U) (transportSection I J e U s)
        ⟨⟨x.val, hx⟩, (transportPoint I J e U x hx).property⟩ =
      pullbackSection I I (openInclusionMap I (sourceOpen I J e))
        (openInclusionMap_isOpenMap I (sourceOpen I J e)) U s ⟨⟨x.val, hx⟩, x.property⟩ :=
  (inclusion_pullback_germEquiv I J e x.val hx _).symm.trans
    (congrArg (germPullback I I (openInclusionMap I (sourceOpen I J e))
      (openInclusionMap_isOpenMap I (sourceOpen I J e)) ⟨x.val, hx⟩)
      (germEquiv_transportSection I J e U s x hx))

/-- Canonical ordinary values commute with the genuine partial coordinate
change at every point, including nonregular germs. -/
theorem value_transportSection (U : Opens M) (s : Section I M U)
    (x : U) (hx : x.val ∈ e.source) :
    value J N (transportSection I J e U s) (transportPoint I J e U x hx) =
      value I M s x := by
  have hsame := value_eq_of_germ_eq I
    (pullbackSection I J (sourceMap I J e) (sourceMap_isOpenMap I J e)
      (transportOpen I J e U) (transportSection I J e U s))
    (pullbackSection I I (openInclusionMap I (sourceOpen I J e))
      (openInclusionMap_isOpenMap I (sourceOpen I J e)) U s)
    ⟨x.val, hx⟩ (transportPoint I J e U x hx).property x.property
    (source_pullback_transportSection I J e U s x hx)
  exact (value_pullbackSection_of_isLocalDiffeomorphAt I J
    (sourceMap I J e) (sourceMap_isOpenMap I J e)
    (transportSection I J e U s)
    ⟨⟨x.val, hx⟩, (transportPoint I J e U x hx).property⟩
    (sourceMap_isLocalDiffeomorph I J e ⟨x.val, hx⟩)).symm.trans
      (hsame.trans (value_pullbackSection_of_isLocalDiffeomorphAt I I
        (openInclusionMap I (sourceOpen I J e))
        (openInclusionMap_isOpenMap I (sourceOpen I J e)) s ⟨⟨x.val, hx⟩, x.property⟩
        (openInclusionMap_isLocalDiffeomorph I (sourceOpen I J e) ⟨x.val, hx⟩)))

end PartialBiholomorph

end Wikipedia.HopfProblem.HolomorphicMeromorphic
