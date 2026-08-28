import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cover
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Actual smooth antiholomorphic one-form coefficients on the sphere

The two coefficient functions are genuine smooth functions on the
preimages of an open set under the sphere's actual affine charts.  On
their overlap they transform by the conjugate of the actual derivative
of inversion.  This is precisely the coordinate transformation of an
antiholomorphic covector, with no independent transition or gluing data
assumed.  Restrictions are literal restrictions of these coefficients.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereForms

/-- The actual coordinate preimage of a sphere open set. -/
def coordinateOpen (U : Opens RiemannSphere) (b : Bool) : Opens ℂ :=
  ⟨RiemannSphere.standardCharts.affineMap b ⁻¹' (U : Set RiemannSphere),
    U.isOpen.preimage (RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).continuous⟩

@[simp] theorem mem_coordinateOpen (U : Opens RiemannSphere) (b : Bool) (z : ℂ) :
    z ∈ coordinateOpen U b ↔ RiemannSphere.standardCharts.affineMap b z ∈ U := Iff.rfl

@[simp] theorem coordinateOpen_false (U : Opens RiemannSphere) :
    coordinateOpen U false = HolomorphicFunctionSheaf.SphereH1.finiteOpen U := rfl

@[simp] theorem coordinateOpen_true (U : Opens RiemannSphere) :
    coordinateOpen U true = HolomorphicFunctionSheaf.SphereH1.infinityOpen U := rfl

theorem coordinateOpen_mono {U V : Opens RiemannSphere} (h : U ≤ V) (b : Bool) :
    coordinateOpen U b ≤ coordinateOpen V b := fun _ hz => h hz

@[simp] theorem coordinateOpen_inf (U V : Opens RiemannSphere) (b : Bool) :
    coordinateOpen (U ⊓ V) b = coordinateOpen U b ⊓ coordinateOpen V b := rfl

@[simp] theorem coordinateOpen_iSup {ι : Type*} (U : ι → Opens RiemannSphere) (b : Bool) :
    coordinateOpen (iSup U) b = ⨆ i, coordinateOpen (U i) b := by
  apply le_antisymm
  · intro z hz
    change RiemannSphere.standardCharts.affineMap b z ∈ iSup U at hz
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hz
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro z hz
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hz
    change RiemannSphere.standardCharts.affineMap b z ∈ iSup U
    exact Opens.mem_iSup.mpr ⟨i, hi⟩

/-- Actual reciprocal coordinates represent the same sphere point. -/
theorem mem_coordinateOpen_inv {U : Opens RiemannSphere} (b : Bool)
    {z : ℂ} (hz : z ≠ 0) :
    z⁻¹ ∈ coordinateOpen U (!b) ↔ z ∈ coordinateOpen U b := by
  change RiemannSphere.standardCharts.affineMap (!b) z⁻¹ ∈ U ↔
    RiemannSphere.standardCharts.affineMap b z ∈ U
  rw [← RiemannSphere.standardCharts.affineMap_inversion b z hz]

/-- The antiholomorphic covector transition of the actual inversion chart. -/
def transition (z : ℂ) : ℂ := starRingEnd ℂ (-(z ^ 2)⁻¹)

/-- The coefficient is the conjugate of the literal complex derivative
of inversion, rather than an independently chosen transition function. -/
theorem transition_eq_conj_deriv (z : ℂ) :
    transition z = starRingEnd ℂ (deriv (fun w : ℂ => w⁻¹) z) := by
  rw [deriv_inv]
  rfl

/-- The actual smooth coefficient spaces in the two affine charts. -/
abbrev CoefficientSpace (U : Opens RiemannSphere) :=
  ∀ b : Bool, SmoothFunctions.Section 𝓘(ℝ, ℂ) ℂ (coordinateOpen U b)

/-- The complex submodule defined by the actual covector overlap law. -/
def compatibilitySubmodule (U : Opens RiemannSphere) : Submodule ℂ (CoefficientSpace U) where
  carrier := {a | ∀ (z : ℂ) (_hz : z ≠ 0)
    (h₀ : z ∈ coordinateOpen U false) (hInf : z⁻¹ ∈ coordinateOpen U true),
      a false ⟨z, h₀⟩ = transition z * a true ⟨z⁻¹, hInf⟩}
  zero_mem' := by
    intro z _ h₀ hInf
    exact (mul_zero (transition z)).symm
  add_mem' := by
    intro a b ha hb z hz h₀ hInf
    change a false ⟨z, h₀⟩ + b false ⟨z, h₀⟩ =
      transition z * (a true ⟨z⁻¹, hInf⟩ + b true ⟨z⁻¹, hInf⟩)
    rw [ha z hz h₀ hInf, hb z hz h₀ hInf, mul_add]
  smul_mem' := by
    intro c a ha z hz h₀ hInf
    change c * a false ⟨z, h₀⟩ = transition z * (c * a true ⟨z⁻¹, hInf⟩)
    rw [ha z hz h₀ hInf]
    exact mul_left_comm c (transition z) (a true ⟨z⁻¹, hInf⟩)

/-- Genuine smooth `(0,1)`-form sections expressed in the actual two
sphere charts, with their required derivative overlap identity. -/
abbrev Section (U : Opens RiemannSphere) := ↥(compatibilitySubmodule U)

/-- The literal smooth coefficient of an actual form section. -/
def coefficient {U : Opens RiemannSphere} (s : Section U) (b : Bool) :
    SmoothFunctions.Section 𝓘(ℝ, ℂ) ℂ (coordinateOpen U b) := s.val b

/-- The defining actual coordinate transformation of a form section. -/
theorem condition {U : Opens RiemannSphere} (s : Section U)
    (z : ℂ) (hz : z ≠ 0) (h₀ : z ∈ coordinateOpen U false)
    (hInf : z⁻¹ ∈ coordinateOpen U true) :
    coefficient s false ⟨z, h₀⟩ = transition z * coefficient s true ⟨z⁻¹, hInf⟩ :=
  s.property z hz h₀ hInf

/-- Construct an actual form section from its actual smooth coefficients
and the literal overlap identity. -/
def sectionMk (U : Opens RiemannSphere) (a : CoefficientSpace U)
    (ha : ∀ (z : ℂ) (_hz : z ≠ 0)
      (h₀ : z ∈ coordinateOpen U false) (hInf : z⁻¹ ∈ coordinateOpen U true),
        a false ⟨z, h₀⟩ = transition z * a true ⟨z⁻¹, hInf⟩) : Section U := ⟨a, ha⟩

@[simp] theorem coefficient_sectionMk (U : Opens RiemannSphere) (a : CoefficientSpace U)
    (ha : a ∈ compatibilitySubmodule U) (b : Bool) :
    coefficient (sectionMk U a ha) b = a b := rfl

/-- Actual sections are determined pointwise by their two coefficient functions. -/
theorem section_ext {U : Opens RiemannSphere} {s t : Section U}
    (h : ∀ (b : Bool) (z : coordinateOpen U b), coefficient s b z = coefficient t b z) :
    s = t :=
  Subtype.ext (funext fun b => ContMDiffMap.ext (h b))

@[simp] theorem coefficient_zero (U : Opens RiemannSphere) (b : Bool) :
    coefficient (0 : Section U) b = 0 := rfl

@[simp] theorem coefficient_add {U : Opens RiemannSphere} (s t : Section U) (b : Bool) :
    coefficient (s + t) b = coefficient s b + coefficient t b := rfl

@[simp] theorem coefficient_smul {U : Opens RiemannSphere} (c : ℂ) (s : Section U) (b : Bool) :
    coefficient (c • s) b = c • coefficient s b := rfl

/-- Literal coefficient restrictions, including their actual complex linearity. -/
def restriction {U V : Opens RiemannSphere} (h : U ≤ V) : Section V →ₗ[ℂ] Section U where
  toFun s :=
    ⟨fun b => ContMDiffMap.restrictRingHom 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ
      (coordinateOpen_mono h b) (coefficient s b),
      fun z hz h₀ hInf => condition s z hz (h h₀) (h hInf)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coefficient_restriction_apply {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : Section V) (b : Bool) (z : coordinateOpen U b) :
    coefficient (restriction h s) b z =
      coefficient s b ⟨z, coordinateOpen_mono h b z.property⟩ := rfl

/-- The actual additive presheaf of smooth antiholomorphic one-forms. -/
def presheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of RiemannSphere) where
  obj U := AddCommGrpCat.of (Section U.unop)
  map h := AddCommGrpCat.ofHom (restriction (leOfHom h.unop)).toAddMonoidHom
  map_id _ := rfl
  map_comp _ _ := rfl

instance presheaf_obj_module (U : (Opens (TopCat.of RiemannSphere))ᵒᵖ) :
    Module ℂ (presheaf.obj U) := inferInstanceAs (Module ℂ (Section U.unop))

@[simp] theorem presheaf_map_apply {U V : Opens RiemannSphere} (h : U ≤ V) (s : Section V) :
    presheaf.map (homOfLE h).op s = restriction h s := rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereForms
