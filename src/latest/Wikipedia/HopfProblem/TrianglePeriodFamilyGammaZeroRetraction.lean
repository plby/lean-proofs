import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroCharts
import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroMayerVietoris
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyMeridianTransitionsLifting
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# The actual slit overlap retracts onto its zero-γ part

The original upper section chart covers the whole overlap, including all
three components.  Setting its first fibre coordinate to zero preserves
the base point, so restricts to a genuine retraction of the whole overlap.
Consequently its literal subfamily inclusion is injective on actual
singular homology in every degree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology Set Topology

variable (D : Data ℂ TriangleRegularPoint)

abbrev upperFamily := familyOpen D Homology.upperBase

abbrev lowerFamily := familyOpen D Homology.lowerBase

/-- The original two base slits cover the literal subfamily. -/
theorem upperFamily_union_lowerFamily :
    (upperFamily D : Set (Space D)) ∪ lowerFamily D = univ := by
  apply Set.eq_univ_of_forall
  intro x
  have h : x.val ∈ (Homology.upperFamily D : Set D.Space) ∪ Homology.lowerFamily D := by
    rw [Homology.upperFamily_union_lowerFamily]
    trivial
  exact h

theorem inclusion_mapsTo_upper :
    MapsTo (inclusion D) (upperFamily D : Set (Space D)) (Homology.upperFamily D) :=
  fun _ hx => hx

theorem inclusion_mapsTo_lower :
    MapsTo (inclusion D) (lowerFamily D : Set (Space D)) (Homology.lowerFamily D) :=
  fun _ hx => hx

/-- The literal overlap of the two open subsets in the zero-coordinate subfamily. -/
abbrev intersectionFamily : Set (Space D) :=
  (upperFamily D : Set (Space D)) ∩ lowerFamily D

/-- The original regular-family overlap, without replacing its topology. -/
abbrev originalIntersection : Set D.Space :=
  (Homology.upperFamily D : Set D.Space) ∩ Homology.lowerFamily D

/-- Exactly the intersection map occurring in actual Mayer--Vietoris naturality. -/
def intersectionInclusion : C(intersectionFamily D, originalIntersection D) :=
  intersectionRestriction (inclusion D)
    (upperFamily D) (lowerFamily D) (Homology.upperFamily D) (Homology.lowerFamily D)
    (inclusion_mapsTo_upper D) (inclusion_mapsTo_lower D)

@[simp] theorem intersectionInclusion_val (x : intersectionFamily D) :
    (intersectionInclusion D x).val = x.val.val := rfl

/-- The original overlap sits literally in the original upper slit member. -/
def intersectionToUpper : C(originalIntersection D, Homology.upperFamily D) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The fixed actual upper-lift chart gives a retraction on the whole upper member. -/
def upperRetraction : C(Homology.upperFamily D, upperFamily D) :=
  sectionRetraction D Homology.upperBase
    (Homology.upperLift Homology.normalizedSlitBaseLift)
    (Homology.upperLift_project Homology.normalizedSlitBaseLift)

@[simp] theorem upperRetraction_projection (x : Homology.upperFamily D) :
    projection D (upperRetraction D x).val = D.projection x.val :=
  sectionRetraction_projection D Homology.upperBase
    (Homology.upperLift Homology.normalizedSlitBaseLift)
    (Homology.upperLift_project Homology.normalizedSlitBaseLift) x

/-- Base preservation keeps the retracted overlap point in the lower member too. -/
theorem upperRetraction_intersection_mem_lower (x : originalIntersection D) :
    (upperRetraction D (intersectionToUpper D x)).val ∈ lowerFamily D := by
  change projection D (upperRetraction D (intersectionToUpper D x)).val ∈ Homology.lowerBase
  rw [upperRetraction_projection]
  exact x.property.2

/-- The genuine continuous retraction from the entire original overlap. -/
def intersectionRetraction : C(originalIntersection D, intersectionFamily D) where
  toFun x := ⟨(upperRetraction D (intersectionToUpper D x)).val,
    (upperRetraction D (intersectionToUpper D x)).property,
    upperRetraction_intersection_mem_lower D x⟩
  continuous_toFun := (continuous_subtype_val.comp
    ((upperRetraction D).continuous.comp (intersectionToUpper D).continuous)).subtype_mk _

/-- The retraction fixes every point of the literal zero-γ overlap. -/
@[simp] theorem intersectionRetraction_inclusion (x : intersectionFamily D) :
    intersectionRetraction D (intersectionInclusion D x) = x := by
  have h := sectionRetraction_inclusionOnOpen D Homology.upperBase
    (Homology.upperLift Homology.normalizedSlitBaseLift)
    (Homology.upperLift_project Homology.normalizedSlitBaseLift)
    ⟨x.val, x.property.1⟩
  have hv := congrArg (fun z : upperFamily D => z.val) h
  exact Subtype.ext hv

theorem intersectionRetraction_comp_inclusion :
    (intersectionRetraction D).comp (intersectionInclusion D) =
      ContinuousMap.id (intersectionFamily D) :=
  ContinuousMap.ext (intersectionRetraction_inclusion D)

/-- Actual functoriality gives a left inverse on integral singular homology. -/
theorem intersectionHomologyRetraction_comp_inclusion (n : ℕ) :
    (singularHomologyMap (intersectionRetraction D) n).comp
      (singularHomologyMap (intersectionInclusion D) n) = LinearMap.id := by
  rw [← singularHomologyMap_comp, intersectionRetraction_comp_inclusion,
    singularHomologyMap_id]

/-- The actual overlap inclusion is injective in every homological degree. -/
theorem intersectionHomologyInclusion_injective (n : ℕ) :
    Function.Injective (singularHomologyMap (intersectionInclusion D) n) := by
  apply Function.LeftInverse.injective
    (g := singularHomologyMap (intersectionRetraction D) n)
  intro a
  exact LinearMap.congr_fun (intersectionHomologyRetraction_comp_inclusion D n) a

end Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero
