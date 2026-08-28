import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardPositiveSection
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsSheaf

/-!
# The positive infinity section in the actual native section sheaf

The global positive section restricts literally in the original dual
bundle fibres.  These restrictions are elements of the existing sheaf
of holomorphic native bundle sections, with no replacement scalar sheaf.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Positive

open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

/-- Actual holomorphic sections of the original positive line on a base open set. -/
abbrev Section (U : Opens RiemannSphere) :=
  NativeBundleSections.Section bundle 𝓘(ℂ) U

/-- Literal restriction of the constructed global section in the original bundle fibres. -/
def sectionOn (U : Opens RiemannSphere) : Section U where
  toFun x := sectionValue (x : RiemannSphere)
  contMDiff_toFun := sectionMap_holomorphic.comp contMDiff_subtype_val

@[simp] theorem sectionOn_apply (U : Opens RiemannSphere) (x : U) :
    sectionOn U x = sectionValue (x : RiemannSphere) := rfl

/-- The local coefficient is the same literal `1` or `w` after restriction. -/
theorem sectionOn_localCoefficient (b : Bool) (U : Opens RiemannSphere)
    (hU : ∀ p ∈ U, p ∈ data.baseSet b) (x : U) :
    (bundle.localTriv b ⟨(x : RiemannSphere), sectionOn U x⟩).2 =
      coefficient b (x : RiemannSphere) :=
  section_localCoefficient b (hU x x.property)

theorem sectionOn_eq_zero_iff (U : Opens RiemannSphere) (x : U) :
    sectionOn U x = 0 ↔ (x : RiemannSphere) = (∞ : RiemannSphere) :=
  section_eq_zero_iff x

/-- Restrictions agree literally, including at the infinity zero. -/
theorem sectionOn_restrict {U V : Opens RiemannSphere} (h : U ≤ V) :
    NativeBundleSections.Section.restrict bundle 𝓘(ℂ) h (sectionOn V) = sectionOn U := by
  apply NativeBundleSections.Section.ext
  intro x
  rfl

/-- The actual native holomorphic section sheaf of the positive line. -/
def sheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of RiemannSphere) :=
  NativeBundleSections.sheaf bundle 𝓘(ℂ)

theorem sheaf_obj_eq (U : Opens RiemannSphere) :
    sheaf.obj.obj (op U) = AddCommGrpCat.of (Section U) := rfl

/-- The section as an element of the actual sheaf object, on every open set. -/
def sheafSection (U : Opens RiemannSphere) : sheaf.obj.obj (op U) := sectionOn U

theorem sheafSection_restrict {U V : Opens RiemannSphere} (h : U ≤ V) :
    sheaf.obj.map (homOfLE h).op (sheafSection V) = sheafSection U :=
  sectionOn_restrict h

/-- The global native section used in the geometric identification of `O(+∞)`. -/
def globalSection : Section ⊤ := sectionOn ⊤

/-- The same global section in the genuine sheaf object. -/
def sheafGlobalSection : sheaf.obj.obj (op ⊤) := globalSection

@[simp] theorem globalSection_apply (x : (⊤ : Opens RiemannSphere)) :
    globalSection x = sectionValue (x : RiemannSphere) := rfl

theorem globalSection_ne_zero : globalSection ≠ 0 := by
  intro h
  have hz := congrArg
    (fun s : Section ⊤ => s ⟨((0 : ℂ) : RiemannSphere), trivial⟩) h
  have hz' : sectionValue (((0 : ℂ)) : RiemannSphere) = 0 := hz
  exact OnePoint.coe_ne_infty (0 : ℂ) ((section_eq_zero_iff _).mp hz')

/-- On the full finite chart the section is the native unit coefficient. -/
theorem sectionOn_finiteChart_coefficient (p : finiteChart) :
    (bundle.localTriv false ⟨(p : RiemannSphere), sectionOn finiteChart p⟩).2 = 1 :=
  section_localCoefficient false p.property

/-- On the full infinity chart the section is the actual reciprocal coordinate. -/
theorem sectionOn_infinityChart_coefficient (p : infinityChart) :
    (bundle.localTriv true ⟨(p : RiemannSphere), sectionOn infinityChart p⟩).2 =
      CanonicalGlobal.BaseTwist.infinityCoordinate p :=
  section_localCoefficient true p.property

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Positive
