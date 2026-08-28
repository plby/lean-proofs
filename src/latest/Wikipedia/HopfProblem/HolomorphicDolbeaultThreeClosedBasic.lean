import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeClosedCoordinates
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsBasic

/-!
# The actual closed-form equation in every native chart

Closedness is the symmetry of the actual antiholomorphic derivatives of
the scalar covector coefficients, in every original preferred chart and
at every point of its genuine coordinate domain.  Restriction preserves
the coefficient germs.  This proves locality of the differential
equation itself, independently of any existence of local primitives.
-/

noncomputable section

open Bundle TopologicalSpace CategoryTheory
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.ClosedForms

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual antiholomorphic coefficient equation in all original
preferred charts, on each chart's entire genuine coordinate domain. -/
def IsClosed (U : Opens M) (a : ∀ x : U, Forms.Covector E M (x : M)) : Prop :=
  ∀ (x₀ : M) (z : E), z ∈ coordinateDomain E M U x₀ → ∀ v w : E,
    dbar (fun y => coordinateForm E M U a x₀ y w) z v =
      dbar (fun y => coordinateForm E M U a x₀ y v) z w

/-- Actual antiholomorphic derivatives of scalar coefficient functions
are unchanged by literal restriction, because the entire germs agree. -/
theorem dbar_coordinateForm_restriction {U V : Opens M} (h : U ≤ V)
    (a : ∀ x : V, Forms.Covector E M (x : M)) (x₀ : M) (z w : E)
    (hz : z ∈ coordinateDomain E M U x₀) :
    dbar (fun y => coordinateForm E M U (fun x => a ⟨(x : M), h x.property⟩) x₀ y w) z =
      dbar (fun y => coordinateForm E M V a x₀ y w) z :=
  dbar_congr ((coordinateForm_restriction_germ E M h a x₀ z hz).fun_comp
    (fun L : E →L[ℝ] ℂ => L w))

/-- Restriction preserves the actual native differential equation. -/
theorem IsClosed.restriction {U V : Opens M} (h : U ≤ V)
    (a : ∀ x : V, Forms.Covector E M (x : M)) (ha : IsClosed E M V a) :
    IsClosed E M U (fun x => a ⟨(x : M), h x.property⟩) := by
  intro x₀ z hz v w
  rw [dbar_coordinateForm_restriction E M h a x₀ z w hz,
    dbar_coordinateForm_restriction E M h a x₀ z v hz]
  exact ha x₀ z (coordinateDomain_mono E M h x₀ hz) v w

/-- The differential equation, in every original chart, is a genuine
local predicate on the original dependent real cotangent covectors. -/
def equationLocalPredicate :
    TopCat.LocalPredicate (fun x : TopCat.of M => Forms.Covector E M x) where
  pred {U} a := IsClosed E M U a
  res {U V} i a ha := IsClosed.restriction E M (leOfHom i) a ha
  locality {U} a ha := by
    intro x₀ z hz v w
    let x : U := ⟨(chartAt E x₀).symm z, hz.2⟩
    obtain ⟨V, hV, i, hclosed⟩ := ha x
    let hVU : V ≤ U := leOfHom i
    have hzV : z ∈ coordinateDomain E M V x₀ := ⟨hz.1, hV⟩
    change IsClosed E M V (fun y => a ⟨(y : M), hVU y.property⟩) at hclosed
    have hc := hclosed x₀ z hzV v w
    rw [dbar_coordinateForm_restriction E M hVU a x₀ z w hzV,
      dbar_coordinateForm_restriction E M hVU a x₀ z v hzV] at hc
    exact hc

/-- Native smooth anti-linear sections satisfying the actual coefficient
PDE form a local predicate, without a local-exactness requirement. -/
def closedLocalPredicate :
    TopCat.LocalPredicate (fun x : TopCat.of M => Forms.Covector E M x) :=
  (Forms.formLocalPredicate E M).and (equationLocalPredicate E M)

/-- Original native smooth anti-linear covector sections satisfying the
actual closed-form PDE in every native preferred chart. -/
abbrev ClosedFormSection (U : Opens M) :=
  {a : ∀ x : U, Forms.Covector E M (x : M) // (closedLocalPredicate E M).pred a}

instance closedFormSectionCoeFun (U : Opens M) :
    CoeFun (ClosedFormSection E M U) (fun _ => ∀ x : U, Forms.Covector E M (x : M)) where
  coe s := s.val

namespace ClosedFormSection

@[ext] theorem ext {U : Opens M} {s t : ClosedFormSection E M U}
    (h : ∀ x : U, s x = t x) : s = t := Subtype.ext (funext h)

/-- Forget only the actual differential equation, retaining the
original smooth covectors and their genuine native smoothness. -/
def toForm {U : Opens M} (s : ClosedFormSection E M U) : Forms.FormSection E M U :=
  ⟨s.val, s.property.1⟩

@[simp] theorem toForm_apply {U : Opens M} (s : ClosedFormSection E M U) (x : U) :
    toForm E M s x = s x := rfl

/-- The section satisfies exactly the original coefficient equation. -/
theorem isClosed {U : Opens M} (s : ClosedFormSection E M U) :
    IsClosed E M U s.val := s.property.2

/-- The native total-space section map is genuinely smooth. -/
theorem smooth {U : Opens M} (s : ClosedFormSection E M U) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (Forms.sectionMap E M s.val) := Forms.FormSection.smooth E M (toForm E M s)

/-- The values remain actual anti-complex-linear real covectors. -/
theorem anti {U : Opens M} (s : ClosedFormSection E M U) (x : U) :
    Forms.covectorAsModel E M (s x) ∈ antiCovectors (E := E) :=
  Forms.FormSection.anti E M (toForm E M s) x

end ClosedFormSection

/-- Construct a closed native form by proving the actual PDE for a
given genuine smooth anti-linear covector section. -/
def sectionMk (U : Opens M) (s : Forms.FormSection E M U)
    (hs : IsClosed E M U s.val) : ClosedFormSection E M U :=
  ⟨s.val, s.property, hs⟩

@[simp] theorem sectionMk_apply (U : Opens M) (s : Forms.FormSection E M U)
    (hs : IsClosed E M U s.val) (x : U) : sectionMk E M U s hs x = s x := rfl

@[simp] theorem toForm_sectionMk (U : Opens M) (s : Forms.FormSection E M U)
    (hs : IsClosed E M U s.val) :
    ClosedFormSection.toForm E M (sectionMk E M U s hs) = s := rfl

/-- Literal restriction preserves native smoothness, anti-linearity,
and the actual closed coefficient equation. -/
def restriction {U V : Opens M} (h : U ≤ V) (s : ClosedFormSection E M V) :
    ClosedFormSection E M U :=
  ⟨fun x => s ⟨(x : M), h x.property⟩,
    (closedLocalPredicate E M).res (homOfLE h) s.val s.property⟩

@[simp] theorem restriction_apply {U V : Opens M} (h : U ≤ V)
    (s : ClosedFormSection E M V) (x : U) :
    restriction E M h s x = s ⟨(x : M), h x.property⟩ := rfl

@[simp] theorem toForm_restriction {U V : Opens M} (h : U ≤ V)
    (s : ClosedFormSection E M V) :
    ClosedFormSection.toForm E M (restriction E M h s) =
      Forms.restriction E M h (ClosedFormSection.toForm E M s) := rfl

/-- The type-valued sheaf has precisely the actual closed native forms. -/
def typeSheaf : TopCat.Sheaf (Type) (TopCat.of M) :=
  TopCat.subsheafToTypes (closedLocalPredicate E M)

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.ClosedForms
