import Wikipedia.HopfProblem.HolomorphicMeromorphicPartialDiffeomorph

/-!
# Transport of actual holomorphic fractions through partial biholomorphisms

A local numerator and denominator are composed with the genuine local inverse
on the actual target domain. Equality of original holomorphic stalks proves
compatibility with the native meromorphic germ equivalence, including at zeros
of the denominator's scalar value.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PartialBiholomorph

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H'] (J : ModelWithCorners ℂ E' H')
  [TopologicalSpace N] [ChartedSpace H' N]
  (e : PartialDiffeomorph I J M N ω)

/-- The exact domain on which the inverse coordinate change lands in `U`. -/
def transportOpen (U : Opens M) : Opens N :=
  ⟨e.target ∩ e.symm ⁻¹' U,
    e.toOpenPartialHomeomorph.isOpen_inter_preimage_symm U.isOpen⟩

/-- The original inverse map takes every valid target point into `U`. -/
def inversePoint (U : Opens M) (y : transportOpen I J e U) : U :=
  ⟨e.symm y.val, y.property.2⟩

/-- A source point in `U` maps to the exact transport domain. -/
def transportPoint (U : Opens M) (x : U) (hx : x.val ∈ e.source) :
    transportOpen I J e U :=
  ⟨e x.val, e.map_source hx, by
    exact (congrArg (fun z : M => z ∈ U) (e.left_inv hx)).mpr x.property⟩

theorem exists_transportPoint (U : Opens M) (y : transportOpen I J e U) :
    ∃ (x : U) (hx : x.val ∈ e.source), transportPoint I J e U x hx = y := by
  refine ⟨inversePoint I J e U y, e.map_target y.property.1, ?_⟩
  exact Subtype.ext (e.right_inv y.property.1)

/-- Literal composition with the original partial inverse is holomorphic
in the original inherited charts of its valid target domain. -/
def transportHolomorphic (U : Opens M)
    (p : HolomorphicFunctionSheaf.Section I M U) :
    HolomorphicFunctionSheaf.Section J N (transportOpen I J e U) :=
  ⟨fun y => p (inversePoint I J e U y), by
    have hc : ContMDiff J 𝓘(ℂ) ω
        (fun y : transportOpen I J e U =>
          HolomorphicFunctionSheaf.extendManifoldSection I U p (e.symm y.val)) := by
      intro y
      exact (contMDiffAt_subtype_iff
        (f := fun z : N => HolomorphicFunctionSheaf.extendManifoldSection I U p (e.symm z))
        (x := y)).mpr
          ((HolomorphicFunctionSheaf.extendManifoldSection_contMDiffAt I U p
            (e.symm y.val) y.property.2).comp y.val
              (e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds y.property.1)))
    exact hc.congr fun y =>
      (HolomorphicFunctionSheaf.extendManifoldSection_apply I U p
        (e.symm y.val) y.property.2).symm⟩

@[simp] theorem transportHolomorphic_apply (U : Opens M)
    (p : HolomorphicFunctionSheaf.Section I M U) (y : transportOpen I J e U) :
    transportHolomorphic I J e U p y = p (inversePoint I J e U y) := rfl

@[simp] theorem transportHolomorphic_transportPoint (U : Opens M)
    (p : HolomorphicFunctionSheaf.Section I M U) (x : U) (hx : x.val ∈ e.source) :
    transportHolomorphic I J e U p (transportPoint I J e U x hx) = p x := by
  apply congrArg p
  exact Subtype.ext (e.left_inv hx)

/-- The equality is first checked on true holomorphic stalks, by equality
of the actual local holomorphic functions on a source neighborhood. -/
theorem source_stalk_transportHolomorphic (U : Opens M)
    (p : HolomorphicFunctionSheaf.Section I M U) (x : U) (hx : x.val ∈ e.source) :
    holomorphicPullbackStalk I J (sourceMap I J e) ⟨x.val, hx⟩
      (holomorphicGerm J N (transportOpen I J e U) (transportPoint I J e U x hx)
        (transportHolomorphic I J e U p)) =
    holomorphicPullbackStalk I I (openInclusionMap I (sourceOpen I J e)) ⟨x.val, hx⟩
      (holomorphicGerm I M U x p) := by
  refine (holomorphicPullbackStalk_germ I J (sourceMap I J e)
    (transportOpen I J e U) ⟨x.val, hx⟩ (transportPoint I J e U x hx).property
      (transportHolomorphic I J e U p)).trans (Eq.trans ?_
        (holomorphicPullbackStalk_germ I I (openInclusionMap I (sourceOpen I J e))
          U ⟨x.val, hx⟩ x.property p).symm)
  refine holomorphicGerm_eq_of_eventuallyEq I (M := sourceOpen I J e) ⟨x.val, hx⟩
    (transportPoint I J e U x hx).property x.property
    (holomorphicPullback I J (sourceMap I J e) (transportOpen I J e U)
      (transportHolomorphic I J e U p))
    (holomorphicPullback I I (openInclusionMap I (sourceOpen I J e)) U p) ?_
  filter_upwards [
    (pullbackOpen I J (sourceMap I J e) (transportOpen I J e U)).isOpen.mem_nhds
      (transportPoint I J e U x hx).property,
    (pullbackOpen I I (openInclusionMap I (sourceOpen I J e)) U).isOpen.mem_nhds
      x.property] with z hzT hzU
  rw [HolomorphicFunctionSheaf.extendManifoldSection_apply,
    HolomorphicFunctionSheaf.extendManifoldSection_apply]
  · change p ⟨e.symm (e z.val), hzT.2⟩ = p ⟨z.val, hzU⟩
    apply congrArg p
    exact Subtype.ext (e.left_inv z.property)
  · exact hzU
  · exact hzT

/-- Nonzero denominator germs remain nonzero after the genuine inverse
coordinate change. No claim of pointwise nonvanishing is needed. -/
theorem transportHolomorphic_nonzero_germs (U : Opens M)
    (q : HolomorphicFunctionSheaf.Section I M U)
    (hq : ∀ x : U, holomorphicGerm I M U x q ≠ 0) :
    ∀ y : transportOpen I J e U,
      holomorphicGerm J N (transportOpen I J e U) y (transportHolomorphic I J e U q) ≠ 0 := by
  intro y
  obtain ⟨x, hx, rfl⟩ := exists_transportPoint I J e U y
  intro hzero
  apply hq x
  apply holomorphicPullbackStalk_injective I I (openInclusionMap I (sourceOpen I J e))
    (openInclusionMap_isOpenMap I (sourceOpen I J e)) ⟨x.val, hx⟩
  exact (source_stalk_transportHolomorphic I J e U q x hx).symm.trans
    ((congrArg (holomorphicPullbackStalk I J (sourceMap I J e) ⟨x.val, hx⟩) hzero).trans
      ((map_zero _).trans (map_zero _).symm))

variable [I.Boundaryless] [IsManifold I ω M]
  [J.Boundaryless] [IsManifold J ω N]

/-- Holomorphic-section compatibility of the actual partial-biholomorphic
meromorphic germ equivalence. -/
theorem germEquiv_transportHolomorphic (U : Opens M)
    (p : HolomorphicFunctionSheaf.Section I M U) (x : U) (hx : x.val ∈ e.source) :
    germEquiv I J e x.val hx
      (sectionGerm J N (transportOpen I J e U) (transportPoint I J e U x hx)
        (transportHolomorphic I J e U p)) = sectionGerm I M U x p := by
  apply (germPullback I I (openInclusionMap I (sourceOpen I J e))
    (openInclusionMap_isOpenMap I (sourceOpen I J e)) ⟨x.val, hx⟩).injective
  refine (inclusion_pullback_germEquiv I J e x.val hx _).trans ?_
  exact (germPullback_ofHolomorphicGerm I J (sourceMap I J e)
    (sourceMap_isOpenMap I J e) ⟨x.val, hx⟩ _).trans
      ((congrArg (ofHolomorphicGerm I (sourceOpen I J e) ⟨x.val, hx⟩)
        (source_stalk_transportHolomorphic I J e U p x hx)).trans
          (germPullback_ofHolomorphicGerm I I (openInclusionMap I (sourceOpen I J e))
            (openInclusionMap_isOpenMap I (sourceOpen I J e)) ⟨x.val, hx⟩ _).symm)

/-- The transported fraction is an honest locally represented meromorphic
section on the actual target domain. -/
def transportFraction (U : Opens M) (p q : HolomorphicFunctionSheaf.Section I M U)
    (hq : ∀ x : U, holomorphicGerm I M U x q ≠ 0) :
    Section J N (transportOpen I J e U) :=
  ofFraction J N (transportOpen I J e U) (transportHolomorphic I J e U p)
    (transportHolomorphic I J e U q) (transportHolomorphic_nonzero_germs I J e U q hq)

/-- Exact native meromorphic germ compatibility, including denominator zeros. -/
theorem germEquiv_transportFraction (U : Opens M)
    (p q : HolomorphicFunctionSheaf.Section I M U)
    (hq : ∀ x : U, holomorphicGerm I M U x q ≠ 0)
    (x : U) (hx : x.val ∈ e.source) :
    germEquiv I J e x.val hx
      (transportFraction I J e U p q hq (transportPoint I J e U x hx)) =
    fraction I M U p q x := by
  change germEquiv I J e x.val hx
      (sectionGerm J N (transportOpen I J e U) (transportPoint I J e U x hx)
          (transportHolomorphic I J e U p) /
        sectionGerm J N (transportOpen I J e U) (transportPoint I J e U x hx)
          (transportHolomorphic I J e U q)) =
    sectionGerm I M U x p / sectionGerm I M U x q
  exact (map_div₀ (germEquiv I J e x.val hx) _ _).trans
    (congrArg₂ (fun a b : Germ I M x.val => a / b)
      (germEquiv_transportHolomorphic I J e U p x hx)
      (germEquiv_transportHolomorphic I J e U q x hx))

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PartialBiholomorph
