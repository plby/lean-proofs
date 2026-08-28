import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsBundle
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeBasic

/-!
# Actual smooth antiholomorphic cotangent sections on open sets

A section takes values in the original real cotangent Hom-bundle fibres.
Its map into that original total space is real smooth, and each fibre
covector is anti-linear for the original complex structure.  Both
requirements are local predicates.  No differential equation or local
primitive is included in the definition.
-/

noncomputable section

open Bundle TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Forms

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original anti-complex-linearity condition is pointwise and local. -/
def antiLocalPredicate :
    TopCat.LocalPredicate (fun x : TopCat.of M => Covector E M x) where
  pred {U} a := ∀ x : U, covectorAsModel E M (a x) ∈ antiCovectors (E := E)
  res {U V} i a ha := fun x => ha ⟨(x : M), (leOfHom i) x.property⟩
  locality {U} a ha := by
    intro x
    obtain ⟨V, hV, i, h⟩ := ha x
    exact h ⟨(x : M), hV⟩

/-- Smoothness into the native bundle and actual fibre anti-linearity
jointly form a genuine local predicate. -/
def formLocalPredicate :
    TopCat.LocalPredicate (fun x : TopCat.of M => Covector E M x) :=
  (smoothLocalPredicate E M).and (antiLocalPredicate E M)

/-- Actual smooth antiholomorphic one-form sections on an original open
set, valued in the original native real tangent covectors. -/
abbrev FormSection (U : Opens M) :=
  {a : ∀ x : U, Covector E M (x : M) // (formLocalPredicate E M).pred a}

instance formSectionCoeFun (U : Opens M) :
    CoeFun (FormSection E M U) (fun _ => ∀ x : U, Covector E M (x : M)) where
  coe s := s.val

namespace FormSection

/-- Native form sections are determined by their actual fibre values. -/
@[ext] theorem ext {U : Opens M} {s t : FormSection E M U}
    (h : ∀ x : U, s x = t x) : s = t := Subtype.ext (funext h)

/-- The smoothness is that of the actual map to the native Hom bundle. -/
theorem smooth {U : Opens M} (s : FormSection E M U) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (sectionMap E M s.val) := s.property.1

/-- Every section value is the original actual antiholomorphic covector. -/
theorem anti {U : Opens M} (s : FormSection E M U) (x : U) :
    covectorAsModel E M (s x) ∈ antiCovectors (E := E) := s.property.2 x

/-- The pointwise anti-linearity identity is the original complex
structure identity on the real tangent covector. -/
theorem anti_I {U : Opens M} (s : FormSection E M U) (x : U) (v : E) :
    covectorAsModel E M (s x) (Complex.I • v) =
      -Complex.I * covectorAsModel E M (s x) v := anti E M s x v

/-- Each coefficient covector is smooth in the actual native bundle
coordinates at the selected original chart centre. -/
theorem inCoordinates_smoothAt {U : Opens M} (s : FormSection E M U) (x : U) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] ℂ) ∞
      (inCoordinates E M s.val (x : M)) x :=
  (smoothSectionAt_iff E M s.val x).mp (smooth E M s x)

end FormSection

/-- Construct a native form from its genuine smooth section map and
its actual pointwise anti-linearity, with no closedness requirement. -/
def sectionMk (U : Opens M) (a : ∀ x : U, Covector E M (x : M))
    (hs : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (sectionMap E M a))
    (ha : ∀ x : U, covectorAsModel E M (a x) ∈ antiCovectors (E := E)) :
    FormSection E M U := ⟨a, hs, ha⟩

@[simp] theorem sectionMk_apply (U : Opens M)
    (a : ∀ x : U, Covector E M (x : M))
    (hs : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (sectionMap E M a))
    (ha : ∀ x : U, covectorAsModel E M (a x) ∈ antiCovectors (E := E)) (x : U) :
    sectionMk E M U a hs ha x = a x := rfl

/-- Literal restriction of native covectors to the smaller original
open set preserves their genuine smoothness and anti-linearity. -/
def restriction {U V : Opens M} (h : U ≤ V) (s : FormSection E M V) :
    FormSection E M U :=
  ⟨fun x => s ⟨(x : M), h x.property⟩,
    (formLocalPredicate E M).res (homOfLE h) s.val s.property⟩

@[simp] theorem restriction_apply {U V : Opens M} (h : U ≤ V)
    (s : FormSection E M V) (x : U) :
    restriction E M h s x = s ⟨(x : M), h x.property⟩ := rfl

@[simp] theorem restriction_refl {U : Opens M} (s : FormSection E M U) :
    restriction E M le_rfl s = s := FormSection.ext E M fun _ => rfl

@[simp] theorem restriction_comp {U V W : Opens M} (hUV : U ≤ V) (hVW : V ≤ W)
    (s : FormSection E M W) :
    restriction E M hUV (restriction E M hVW s) = restriction E M (hUV.trans hVW) s :=
  FormSection.ext E M fun _ => rfl

/-- The sheaf of types has exactly the actual native form sections and
their original restrictions. -/
def typeSheaf : TopCat.Sheaf (Type) (TopCat.of M) :=
  TopCat.subsheafToTypes (formLocalPredicate E M)

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Forms
