import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereFormsBasic
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The genuine sheaf of smooth antiholomorphic one-forms on the sphere

Compatible actual form sections give compatible smooth functions on
each pulled-back cover.  Those functions glue in the actual smooth
function sheaf.  The derivative overlap law is local, so the glued
coefficients satisfy the original law.  This proves the full sheaf
condition, without assuming gluing or a separately chosen form sheaf.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereForms

variable {ι : Type} (U : ι → Opens RiemannSphere) (s : ∀ i, Section (U i))
  (hs : TopCat.Presheaf.IsCompatible presheaf U s)

include hs in
/-- Literal compatible form restrictions give compatible smooth
coefficient restrictions on each actual coordinate cover. -/
theorem coefficient_compatible (b : Bool) :
    TopCat.Presheaf.IsCompatible (SmoothFunctions.additiveSheaf 𝓘(ℝ, ℂ) ℂ).obj
      (fun i => coordinateOpen (U i) b) (fun i => coefficient (s i) b) := by
  intro i j
  exact congrArg (fun t : Section (U i ⊓ U j) => coefficient t b) (hs i j)

include hs in
/-- The actual smooth function sheaf glues each coefficient on the
coordinate preimage of the original union. -/
theorem exists_coordinate_gluing (b : Bool) :
    ∃ a : SmoothFunctions.Section 𝓘(ℝ, ℂ) ℂ (coordinateOpen (iSup U) b),
      ∀ i, ContMDiffMap.restrictRingHom 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ
        (coordinateOpen_mono (le_iSup U i) b) a = coefficient (s i) b := by
  let F := SmoothFunctions.additiveSheaf 𝓘(ℝ, ℂ) ℂ
  obtain ⟨a, ha, _⟩ := F.existsUnique_gluing' (fun i => coordinateOpen (U i) b)
    (coordinateOpen (iSup U) b)
    (fun i => homOfLE (coordinateOpen_mono (le_iSup U i) b))
    (le_of_eq (coordinateOpen_iSup U b)) (fun i => coefficient (s i) b)
    (coefficient_compatible U s hs b)
  exact ⟨a, ha⟩

/-- Literal restrictions to an actual open cover determine form sections. -/
theorem section_eq_of_restrictions {a b : Section (iSup U)}
    (h : ∀ i, restriction (le_iSup U i) a = restriction (le_iSup U i) b) : a = b := by
  apply section_ext
  intro c z
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show RiemannSphere.standardCharts.affineMap c z ∈ iSup U from z.property)
  exact congrArg (fun t : Section (U i) => coefficient t c ⟨z, hi⟩) (h i)

/-- The actual chart-coefficient presheaf satisfies the genuine sheaf
condition, including its fixed derivative transformation law. -/
theorem presheaf_isSheaf : presheaf.IsSheaf := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing presheaf).mpr
  intro ι U s hs
  choose a ha using fun b => exists_coordinate_gluing U s hs b
  have hc : a ∈ compatibilitySubmodule (iSup U) := by
    intro z hz h₀ hInf
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
      (show RiemannSphere.standardCharts.affineMap false z ∈ iSup U from h₀)
    have hiInf : z⁻¹ ∈ coordinateOpen (U i) true :=
      (mem_coordinateOpen_inv false hz).mpr hi
    have hfalse := congrArg
      (fun f : SmoothFunctions.Section 𝓘(ℝ, ℂ) ℂ (coordinateOpen (U i) false) => f ⟨z, hi⟩)
      (ha false i)
    have htrue := congrArg
      (fun f : SmoothFunctions.Section 𝓘(ℝ, ℂ) ℂ (coordinateOpen (U i) true) => f ⟨z⁻¹, hiInf⟩)
      (ha true i)
    exact hfalse.trans ((condition (s i) z hz hi hiInf).trans
      (congrArg (transition z * ·) htrue.symm))
  let q : Section (iSup U) := sectionMk (iSup U) a hc
  have hq : TopCat.Presheaf.IsGluing presheaf U s q := by
    intro i
    apply Subtype.ext
    funext b
    exact ha b i
  refine ⟨q, hq, ?_⟩
  intro r hr
  apply section_eq_of_restrictions U
  intro i
  exact (hr i).trans (hq i).symm

/-- The genuine additive sheaf of actual smooth `(0,1)`-forms on the
constructed Riemann sphere. -/
def sheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of RiemannSphere) where
  obj := presheaf
  property := presheaf_isSheaf

/-- Its section groups are the actual derivative-compatible coefficients. -/
theorem sheaf_obj_eq (U : Opens RiemannSphere) :
    sheaf.obj.obj (op U) = AddCommGrpCat.of (Section U) := rfl

instance sheaf_obj_module (U : (Opens (TopCat.of RiemannSphere))ᵒᵖ) :
    Module ℂ (sheaf.obj.obj U) := inferInstanceAs (Module ℂ (Section U.unop))

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereForms
