import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativeBundles
import Wikipedia.HopfProblem.PeriodTorusNeronSeveriForms

/-!
# The actual native Chern image and the integral type `(1,1)` subgroup

The carrier is the image of the winding-defined first Chern map on all
original native holomorphic line bundles. The actual analytic descent
and the signed factor comparison prove that this image is exactly the
integral classes whose real period form has type `(1,1)`. The subgroup
is not defined by its desired coefficient or type description.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative

open SingularCohomologyFree PeriodTorusCohomology PeriodTorusTypeOneOne
open PeriodTorusAppellHumbert

/-- The actual image of the native first Chern map on original holomorphic line bundles. -/
def neronSeveriSet (p : PeriodDomain) : Set (SingularCohomology p.Torus 2) :=
  Set.range (NativeLineBundle.chernClass (p := p) : NativeLineBundle.{0} p → _)

/-- The image/type identification uses genuine factor descent in one direction
and the explicitly constructed negative-form native bundle in the other. -/
theorem mem_neronSeveriSet_iff_typeOneOne (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) :
    a ∈ neronSeveriSet p ↔ IsTypeOneOne (cohomologyRealForm p a) := by
  constructor
  · rintro ⟨V, rfl⟩
    exact firstChernClass_isTypeOneOne p V.Fiber
  · intro ha
    obtain ⟨V, hV⟩ := (exists_native_isFirstChernClass_iff_typeOneOne p a).mpr ha
    exact ⟨V, ((isFirstChernClass_iff p V.Fiber a).mp hV).symm⟩

/-- The native-bundle Chern image is an additive subgroup of actual integral cohomology. -/
def neronSeveri (p : PeriodDomain) : AddSubgroup (SingularCohomology p.Torus 2) where
  carrier := neronSeveriSet p
  zero_mem' := (mem_neronSeveriSet_iff_typeOneOne p 0).mpr
    (integralTypeOneOneSubgroup p).zero_mem
  add_mem' := fun ha hb => (mem_neronSeveriSet_iff_typeOneOne p _).mpr
    ((integralTypeOneOneSubgroup p).add_mem
      ((mem_neronSeveriSet_iff_typeOneOne p _).mp ha)
      ((mem_neronSeveriSet_iff_typeOneOne p _).mp hb))
  neg_mem' := fun ha => (mem_neronSeveriSet_iff_typeOneOne p _).mpr
    ((integralTypeOneOneSubgroup p).neg_mem
      ((mem_neronSeveriSet_iff_typeOneOne p _).mp ha))

@[simp] theorem mem_neronSeveri_iff (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) :
    a ∈ neronSeveri p ↔ IsTypeOneOne (cohomologyRealForm p a) :=
  mem_neronSeveriSet_iff_typeOneOne p a

/-- Equality is proved in native integral cohomology, not imposed by the definition. -/
theorem neronSeveri_eq_integralTypeOneOneSubgroup (p : PeriodDomain) :
    neronSeveri p = integralTypeOneOneSubgroup p := by
  ext a
  exact mem_neronSeveri_iff p a

/-- Every class in the subgroup is the class of an actual original native line bundle. -/
theorem mem_neronSeveri_iff_exists_native (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) :
    a ∈ neronSeveri p ↔ ∃ V : NativeLineBundle.{0} p, V.chernClass = a := Iff.rfl

/-- The same image is computed on actual analytic isomorphism classes of native bundles. -/
theorem coe_neronSeveri_eq_range_isoClassChernClass (p : PeriodDomain) :
    (neronSeveri p : Set (SingularCohomology p.Torus 2)) =
      Set.range (NativeLineBundle.isoClassChernClass.{0} p) :=
  (NativeLineBundle.range_isoClassChernClass p).symm

/-- Factors compute the entire native image because native presentation was proved. -/
theorem mem_neronSeveri_iff_exists_factor (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) :
    a ∈ neronSeveri p ↔ ∃ F : FactorOfAutomorphy p, Chern.firstChernClass F = a :=
  (mem_neronSeveri_iff p a).trans
    (Chern.exists_factor_firstChernClass_iff_typeOneOne p a).symm

/-- All original native bundles, in any fibre universe, have classes in this image. -/
theorem firstChernClass_mem_neronSeveri (p : PeriodDomain) (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
    [ContMDiffVectorBundle ω ℂ V (modelWithCornersSelf ℂ ComplexPlane₂)] :
    firstChernClass p V ∈ neronSeveri p :=
  (mem_neronSeveri_iff p _).mpr (firstChernClass_isTypeOneOne p V)

/-- The exact original integral-period coefficient criterion for the genuine native image. -/
theorem coefficientClass_mem_neronSeveri_iff (p : PeriodDomain) (E : Fin 6 → ℤ) :
    coefficientClass p E ∈ neronSeveri p ↔ IsTypeOneOne (tangentForm p E) := by
  rw [mem_neronSeveri_iff, cohomologyRealForm_coefficientClass]

/-- The source period polynomial cuts out exactly the actual native Chern image. -/
theorem coefficientClass_mem_neronSeveri_iff_periodPolynomial
    (p : PeriodDomain) (E : Fin 6 → ℤ) :
    coefficientClass p E ∈ neronSeveri p ↔ periodPolynomial p.val E = 0 := by
  rw [coefficientClass_mem_neronSeveri_iff, tangentForm_isTypeOneOne_iff]

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernNative
