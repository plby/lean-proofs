import Wikipedia.HopfProblem.HolomorphicMeromorphicGerms
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# The sheaf of genuine local meromorphic functions

A meromorphic section assigns a fraction of the actual holomorphic
local ring to each point and is locally represented by two holomorphic
functions with nonzero denominator germ. The numerator and denominator
may vary from neighborhood to neighborhood. Mathlib's local-predicate
construction proves the sheaf condition from this actual local
representability condition.

In particular this definition is neither a field of global holomorphic
fractions nor a field of functions assumed to descend to another space.
-/

noncomputable section

open Set Topology TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- A local fraction presentation on one open set. Nonvanishing refers
to denominator germs, so denominators are permitted to vanish at points. -/
def IsFraction {U : Opens M} (f : ∀ x : U, Germ I M x.val) : Prop :=
  ∃ p q : HolomorphicFunctionSheaf.Section I M U,
    (∀ x : U, holomorphicGerm I M U x q ≠ 0) ∧
      ∀ x : U, f x = fraction I M U p q x

/-- Local fractions are preserved by literal restriction. -/
def fractionPrelocal : TopCat.PrelocalPredicate (fun x : TopCat.of M => Germ I M x) where
  pred := IsFraction I M
  res {U V} i f hf := by
    obtain ⟨p, q, hq, he⟩ := hf
    refine ⟨HolomorphicFunctionSheaf.restrictionAlgHom I M i.le p,
      HolomorphicFunctionSheaf.restrictionAlgHom I M i.le q, ?_, ?_⟩
    · intro x
      rw [holomorphicGerm_restrict]
      exact hq (Set.inclusion i.le x)
    · intro x
      exact (he (Set.inclusion i.le x)).trans (fraction_restrict I M i.le p q x).symm

/-- The genuine local meromorphy condition, not a global fraction condition. -/
def localPredicate : TopCat.LocalPredicate (fun x : TopCat.of M => Germ I M x) :=
  (fractionPrelocal I M).sheafify

/-- The actual sheaf of locally represented meromorphic functions, as a sheaf of types. -/
def typeSheaf : TopCat.Sheaf (Type) (TopCat.of M) :=
  TopCat.subsheafToTypes (localPredicate I M)

/-- A meromorphic function on an actual open subset of the original manifold. -/
abbrev Section (U : Opens M) := (typeSheaf I M).presheaf.obj (op U)

instance section_coeFun (U : Opens M) :
    CoeFun (Section I M U) (fun _ => ∀ x : U, Germ I M x.val) where
  coe s := s.val

@[ext] theorem section_ext {U : Opens M} {s t : Section I M U}
    (h : ∀ x : U, s x = t x) : s = t :=
  Subtype.ext (funext h)

/-- Restriction is actual restriction of the germ-valued section. -/
def restrict {U V : Opens M} (h : U ≤ V) (s : Section I M V) : Section I M U :=
  (typeSheaf I M).presheaf.map (homOfLE h).op s

@[simp] theorem restrict_apply {U V : Opens M} (h : U ≤ V)
    (s : Section I M V) (x : U) :
    restrict I M h s x = s (Set.inclusion h x) := rfl

@[simp] theorem restrict_refl {U : Opens M} (s : Section I M U) :
    restrict I M le_rfl s = s := rfl

@[simp] theorem restrict_trans {U V W : Opens M} (hUV : U ≤ V) (hVW : V ≤ W)
    (s : Section I M W) :
    restrict I M hUV (restrict I M hVW s) = restrict I M (hUV.trans hVW) s := rfl

/-- A genuine fraction presentation defines a meromorphic section. -/
def ofFraction (U : Opens M) (p q : HolomorphicFunctionSheaf.Section I M U)
    (hq : ∀ x : U, holomorphicGerm I M U x q ≠ 0) : Section I M U :=
  ⟨fraction I M U p q, (fractionPrelocal I M).sheafifyOf ⟨p, q, hq, fun _ => rfl⟩⟩

@[simp] theorem ofFraction_apply (U : Opens M)
    (p q : HolomorphicFunctionSheaf.Section I M U)
    (hq : ∀ x : U, holomorphicGerm I M U x q ≠ 0) (x : U) :
    ofFraction I M U p q hq x = fraction I M U p q x := rfl

/-- Every meromorphic section has a genuine numerator and denominator
on a neighborhood of each point, with agreement as actual fraction germs. -/
theorem local_representation {U : Opens M} (s : Section I M U) (x : U) :
    ∃ (V : Opens M) (hVU : V ≤ U) (_hxV : x.val ∈ V)
      (p q : HolomorphicFunctionSheaf.Section I M V),
      (∀ y : V, holomorphicGerm I M V y q ≠ 0) ∧
        ∀ y : V, s (Set.inclusion hVU y) = fraction I M V p q y := by
  obtain ⟨V, hxV, i, p, q, hq, he⟩ := s.property x
  exact ⟨V, i.le, hxV, p, q, hq, he⟩

/-- Actual holomorphic functions embed by their original holomorphic germs. -/
def ofHolomorphic (U : Opens M) (f : HolomorphicFunctionSheaf.Section I M U) :
    Section I M U := ofFraction I M U f 1 (fun x => by rw [map_one]; exact one_ne_zero)

@[simp] theorem ofHolomorphic_apply (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    ofHolomorphic I M U f x = sectionGerm I M U x f := by
  change sectionGerm I M U x f / sectionGerm I M U x 1 = _
  rw [map_one, div_one]

theorem ofHolomorphic_injective (U : Opens M) :
    Function.Injective (ofHolomorphic I M U) := by
  intro f g h
  apply ContMDiffMap.ext
  intro x
  have hx := congrArg (fun s : Section I M U => s x) h
  rw [ofHolomorphic_apply, ofHolomorphic_apply] at hx
  have hfg : holomorphicGerm I M U x f = holomorphicGerm I M U x g :=
    ofHolomorphicGerm_injective I M x.val hx
  have he := congrArg (HolomorphicFunctionSheaf.stalkEval I M x.val) hfg
  have hf := HolomorphicFunctionSheaf.stalkEval_germ I M U x.val x.property f
  have hg := HolomorphicFunctionSheaf.stalkEval_germ I M U x.val x.property g
  exact hf.symm.trans (he.trans hg)

end Wikipedia.HopfProblem.HolomorphicMeromorphic
