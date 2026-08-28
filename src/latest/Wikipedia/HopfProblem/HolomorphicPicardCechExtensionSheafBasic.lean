import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionMaps
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# The native sheafified Čech extension and its original endpoints

The middle sheaf is the genuine abelian sheafification of the concrete
compatible-data presheaf. The first endpoint is the given sheaf itself,
and the last endpoint is the native constant sheaf on `ULift ℤ` used by
sheaf cohomology. The maps are the actual induced sheaf maps.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

/-- Genuine sheafification of the actual compatible-data presheaf. -/
def extensionSheaf : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
    (presheaf c)

/-- The actual sheafification unit for the extension presheaf. -/
def unit : presheaf c ⟶ (extensionSheaf c).obj :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X) (presheaf c)

/-- The native constant lifted-integer sheaf, with the exact endpoint
used in the existing definition of sheaf cohomology. -/
def degreeSheaf (X : TopCat.{0}) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of (ULift.{0} ℤ))

/-- The actual unit of the lifted-integer constant presheaf. -/
def degreeUnit (X : TopCat.{0}) : degreePresheaf X ⟶ (degreeSheaf X).obj :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X) (degreePresheaf X)

/-- The first endpoint remains the given sheaf, not its replacement. -/
def inclusion : F ⟶ extensionSheaf c where
  hom := inclusionPre c ≫ unit c

/-- The actual sheafified degree projection. -/
def projection : extensionSheaf c ⟶ degreeSheaf X where
  hom := CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) (projectionPre c)

@[simp] theorem inclusion_app (V : Opens X) (a : Section F V) :
    (inclusion c).hom.app (op V) a = (unit c).app (op V) (includeHom c V a) := rfl

theorem unit_projection :
    unit c ≫ (projection c).hom = projectionPre c ≫ degreeUnit X :=
  (CategoryTheory.toSheafify_naturality
    (Opens.grothendieckTopology X) (projectionPre c)).symm

@[simp] theorem projection_app_unit (V : Opens X) (s : ExtensionSection c V) :
    (projection c).hom.app (op V) ((unit c).app (op V) s) =
      (degreeUnit X).app (op V) (degreeHom c V s) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (unit_projection c) (op V)) s

theorem inclusion_projection : inclusion c ≫ projection c = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  change (inclusionPre c ≫ unit c) ≫ (projection c).hom = 0
  rw [Category.assoc, unit_projection, ← Category.assoc,
    inclusionPre_projectionPre, Limits.zero_comp]

/-- The actual extension complex, with its original sheaf as kernel
endpoint and the literal native integer constant sheaf as quotient. -/
def complex : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  ShortComplex.mk (inclusion c) (projection c) (inclusion_projection c)

/-- Equality of actual maps from the extension sheaf is tested on its
genuine presheaf-unit representatives. -/
theorem extensionHom_ext {G : TopCat.Sheaf AddCommGrpCat.{0} X}
    {f g : extensionSheaf c ⟶ G}
    (h : unit c ≫ f.hom = unit c ≫ g.hom) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  exact CategoryTheory.sheafify_hom_ext (Opens.grothendieckTopology X)
    f.hom g.hom G.property h

theorem unit_restrict {V W : Opens X} (hWV : W ≤ V) (s : ExtensionSection c V) :
    (extensionSheaf c).obj.map (homOfLE hWV).op ((unit c).app (op V) s) =
      (unit c).app (op W) (restrict c hWV s) :=
  (ConcreteCategory.congr_hom ((unit c).naturality (homOfLE hWV).op) s).symm

/-- Every actual extension-sheaf section locally has constructed
compatible-data representatives. -/
theorem exists_unit_restriction (V : Opens X)
    (s : Section (extensionSheaf c) V) (x : X) (hx : x ∈ V) :
    ∃ (W : Opens X) (hWV : W ≤ V) (t : ExtensionSection c W), x ∈ W ∧
      (unit c).app (op W) t = (extensionSheaf c).obj.map (homOfLE hWV).op s := by
  have hloc : TopCat.Presheaf.IsLocallySurjective (unit c) := by
    change CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (presheaf c))
    infer_instance
  obtain ⟨W, hWV, ⟨t, ht⟩, hxW⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (unit c)).mp hloc V s x hx
  exact ⟨W, hWV, t, hxW, ht⟩

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
