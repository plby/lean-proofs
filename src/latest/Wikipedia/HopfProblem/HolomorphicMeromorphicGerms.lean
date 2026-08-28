import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkChart
import Wikipedia.HopfProblem.CuspNormalizationGermsBasicDomain
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Meromorphic germs in the original complex-manifold atlas

The local meromorphic field is the fraction field of the actual
categorical stalk of holomorphic functions. Its integral-domain
property follows from the proved comparison with analytic neighborhood
germs in the original extended chart. Thus the fractions below are
genuine local fractions, not quotients of global holomorphic functions.

Every element has a representative by two holomorphic sections on one
actual neighborhood. Equality of fractions is exactly the ordinary
cross-multiplication identity of holomorphic germs.
-/

noncomputable section

open Set Filter Topology TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The actual holomorphic stalk, defined by the open-neighborhood colimit. -/
abbrev HolomorphicStalk (x : M) := (HolomorphicFunctionSheaf.presheaf I M).stalk x

/-- The original holomorphic stalk is an integral domain by the actual
chart comparison and the analytic identity principle. -/
instance holomorphicStalk_isDomain [I.Boundaryless] [IsManifold I ω M]
    (x : M) : IsDomain (HolomorphicStalk I M x) :=
  Function.Injective.isDomain (HolomorphicFunctionSheaf.chartStalkEquiv I x)
    (HolomorphicFunctionSheaf.chartStalkEquiv I x).injective

/-- The genuine field of meromorphic germs at a point of the manifold. -/
abbrev Germ (x : M) := FractionRing (HolomorphicStalk I M x)

/-- The canonical inclusion of a holomorphic germ into its fraction field. -/
def ofHolomorphicGerm (x : M) : HolomorphicStalk I M x →+* Germ I M x :=
  algebraMap _ _

theorem ofHolomorphicGerm_injective (x : M) :
    Function.Injective (ofHolomorphicGerm I M x) :=
  IsFractionRing.injective _ _

@[simp] theorem ofHolomorphicGerm_eq_zero_iff (x : M) (a : HolomorphicStalk I M x) :
    ofHolomorphicGerm I M x a = 0 ↔ a = 0 :=
  map_eq_zero_iff _ (ofHolomorphicGerm_injective I M x)

/-- The original categorical germ of an actual local holomorphic section. -/
def holomorphicGerm (U : Opens M) (x : U) :
    HolomorphicFunctionSheaf.Section I M U →+* HolomorphicStalk I M x.val :=
  ((HolomorphicFunctionSheaf.presheaf I M).germ U x.val x.property).hom

/-- A local holomorphic section, viewed in the genuine meromorphic field. -/
def sectionGerm (U : Opens M) (x : U) :
    HolomorphicFunctionSheaf.Section I M U →+* Germ I M x.val :=
  (ofHolomorphicGerm I M x.val).comp (holomorphicGerm I M U x)

@[simp] theorem sectionGerm_apply (U : Opens M) (x : U)
    (f : HolomorphicFunctionSheaf.Section I M U) :
    sectionGerm I M U x f = ofHolomorphicGerm I M x.val (holomorphicGerm I M U x f) := rfl

@[simp] theorem sectionGerm_eq_zero_iff (U : Opens M) (x : U)
    (f : HolomorphicFunctionSheaf.Section I M U) :
    sectionGerm I M U x f = 0 ↔ holomorphicGerm I M U x f = 0 :=
  ofHolomorphicGerm_eq_zero_iff I M x.val _

/-- Literal restriction leaves the original holomorphic germ unchanged. -/
@[simp] theorem holomorphicGerm_restrict {U V : Opens M} (h : U ≤ V) (x : U)
    (f : HolomorphicFunctionSheaf.Section I M V) :
    holomorphicGerm I M U x (HolomorphicFunctionSheaf.restrictionAlgHom I M h f) =
      holomorphicGerm I M V (Set.inclusion h x) f :=
  (HolomorphicFunctionSheaf.presheaf I M).germ_res_apply (homOfLE h) x.val x.property f

@[simp] theorem sectionGerm_restrict {U V : Opens M} (h : U ≤ V) (x : U)
    (f : HolomorphicFunctionSheaf.Section I M V) :
    sectionGerm I M U x (HolomorphicFunctionSheaf.restrictionAlgHom I M h f) =
      sectionGerm I M V (Set.inclusion h x) f := by
  simp only [sectionGerm_apply, holomorphicGerm_restrict]

/-- A nonzero value is sufficient, but not required, for a nonzero germ. -/
theorem holomorphicGerm_ne_zero_of_value_ne_zero (U : Opens M) (x : U)
    (f : HolomorphicFunctionSheaf.Section I M U) (hf : f x ≠ 0) :
    holomorphicGerm I M U x f ≠ 0 := by
  intro h
  apply hf
  have he := congrArg (HolomorphicFunctionSheaf.stalkEval I M x.val) h
  have hv : HolomorphicFunctionSheaf.stalkEval I M x.val
      (holomorphicGerm I M U x f) = f x :=
    HolomorphicFunctionSheaf.stalkEval_germ I M U x.val x.property f
  exact hv.symm.trans (he.trans (map_zero _))

variable [I.Boundaryless] [IsManifold I ω M]

/-- The meromorphic germ represented by an actual local numerator and denominator. -/
def fraction (U : Opens M) (p q : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    Germ I M x.val := sectionGerm I M U x p / sectionGerm I M U x q

@[simp] theorem fraction_restrict {U V : Opens M} (h : U ≤ V)
    (p q : HolomorphicFunctionSheaf.Section I M V) (x : U) :
    fraction I M U (HolomorphicFunctionSheaf.restrictionAlgHom I M h p)
        (HolomorphicFunctionSheaf.restrictionAlgHom I M h q) x =
      fraction I M V p q (Set.inclusion h x) := by
  simp only [fraction, sectionGerm_restrict]

/-- With genuine nonzero denominator germs, equality is precisely
cross multiplication in the actual holomorphic local ring. -/
theorem fraction_eq_iff (U : Opens M) (p q r s : HolomorphicFunctionSheaf.Section I M U)
    (x : U) (hq : holomorphicGerm I M U x q ≠ 0)
    (hs : holomorphicGerm I M U x s ≠ 0) :
    fraction I M U p q x = fraction I M U r s x ↔
      holomorphicGerm I M U x (p * s) = holomorphicGerm I M U x (r * q) := by
  have hq' : sectionGerm I M U x q ≠ 0 :=
    fun h => hq ((sectionGerm_eq_zero_iff I M U x q).mp h)
  have hs' : sectionGerm I M U x s ≠ 0 :=
    fun h => hs ((sectionGerm_eq_zero_iff I M U x s).mp h)
  rw [fraction, fraction, div_eq_div_iff hq' hs']
  rw [← map_mul, ← map_mul]
  exact (ofHolomorphicGerm_injective I M x.val).eq_iff

/-- Every meromorphic germ has a genuine local fraction representative
on a single actual open neighborhood. -/
theorem exists_fraction_representative (x : M) (a : Germ I M x) :
    ∃ (U : Opens M) (hx : x ∈ U) (p q : HolomorphicFunctionSheaf.Section I M U),
      holomorphicGerm I M U ⟨x, hx⟩ q ≠ 0 ∧ fraction I M U p q ⟨x, hx⟩ = a := by
  obtain ⟨p₀, q₀, hq₀, rfl⟩ := IsFractionRing.div_surjective (HolomorphicStalk I M x) a
  obtain ⟨U, hxU, p, hp⟩ := (HolomorphicFunctionSheaf.presheaf I M).exists_germ_eq p₀
  obtain ⟨V, hVU, hxV, q, hq⟩ :=
    (HolomorphicFunctionSheaf.presheaf I M).exists_le_germ_eq q₀ hxU
  let pV := HolomorphicFunctionSheaf.restrictionAlgHom I M hVU p
  have hpV : holomorphicGerm I M V ⟨x, hxV⟩ pV = p₀ :=
    (holomorphicGerm_restrict I M hVU ⟨x, hxV⟩ p).trans hp
  have hqV : holomorphicGerm I M V ⟨x, hxV⟩ q = q₀ := hq
  refine ⟨V, hxV, pV, q, ?_, ?_⟩
  · rw [hqV]
    exact mem_nonZeroDivisors_iff_ne_zero.mp hq₀
  · change ofHolomorphicGerm I M x (holomorphicGerm I M V ⟨x, hxV⟩ pV) /
      ofHolomorphicGerm I M x (holomorphicGerm I M V ⟨x, hxV⟩ q) = _
    rw [hpV, hqV]
    rfl

end Wikipedia.HopfProblem.HolomorphicMeromorphic
