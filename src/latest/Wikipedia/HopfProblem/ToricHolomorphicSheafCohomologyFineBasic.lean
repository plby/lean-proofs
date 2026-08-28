import Wikipedia.HopfProblem.CuspNormalizationSheafBiproduct
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cech

/-!
# Local vanishing and finite fine decompositions of actual sheaves

Local vanishing means that an actual morphism is zero on every open
subset of the specified open set. It is equivalent to vanishing of the
actual stalk maps there. A fine decomposition consists of actual sheaf
endomorphisms with closed supports subordinate to a finite open cover,
whose literal sum is the identity.

This records the geometric partition-of-unity data. It does not define
cohomology, and no analytic sheaf is assumed to have such decompositions.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped AlgebraicGeometry BigOperators

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology

variable {X : TopCat.{0}}

/-- An actual sheaf morphism is zero on every smaller open set. -/
def IsZeroOn {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G) (U : Opens X) : Prop :=
  ∀ V : Opens X, V ≤ U → f.hom.app (op V) = 0

/-- Local vanishing implies that each actual stalk map in that open set is zero. -/
theorem IsZeroOn.stalkMap_eq_zero {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    {f : F ⟶ G} {U : Opens X} (hf : IsZeroOn f U) (x : X) (hx : x ∈ U) :
    (CuspNormalization.SheafBiproduct.stalkFunctor X x).map f = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  obtain ⟨V, hVU, hxV, s, rfl⟩ := F.presheaf.exists_le_germ_eq a hx
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.hom
    (F.presheaf.germ V x hxV s) = 0
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hf V hVU]
  exact (G.presheaf.germ V x hxV).hom.map_zero

/-- Vanishing of the actual stalk maps gives zero on every smaller open set. -/
theorem isZeroOn_of_stalkMap_eq_zero {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    {f : F ⟶ G} {U : Opens X}
    (hf : ∀ x ∈ U, (CuspNormalization.SheafBiproduct.stalkFunctor X x).map f = 0) :
    IsZeroOn f U := by
  intro V hVU
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply TopCat.Presheaf.section_ext G V
  intro x hx
  have h := ConcreteCategory.congr_hom (hf x (hVU hx)) (F.presheaf.germ V x hx s)
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.hom
    (F.presheaf.germ V x hx s) = 0 at h
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at h
  exact h.trans (G.presheaf.germ V x hx).hom.map_zero.symm

/-- Local zero morphisms are characterized by their actual stalk maps. -/
theorem isZeroOn_iff_stalkMap_eq_zero {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : F ⟶ G) (U : Opens X) :
    IsZeroOn f U ↔
      ∀ x ∈ U, (CuspNormalization.SheafBiproduct.stalkFunctor X x).map f = 0 :=
  ⟨fun h => h.stalkMap_eq_zero, isZeroOn_of_stalkMap_eq_zero⟩

/-- A functor is local here when it preserves actual zero morphisms on
every open subset, not merely global zero morphisms. -/
def IsLocalFunctor
    (K : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X) : Prop :=
  ∀ {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G) (U : Opens X),
    IsZeroOn f U → IsZeroOn (K.map f) U

/-- Actual endomorphisms with closed subordinate supports whose sum is
the identity. This is finite partition-of-unity data for the sheaf. -/
structure FiniteDecomposition (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {ι : Type} [Fintype ι] (U : ι → Opens X) where
  operator : ι → (F ⟶ F)
  support : ι → Set X
  support_closed : ∀ i, IsClosed (support i)
  subordinate : ∀ i, support i ⊆ U i
  zeroOutside : ∀ i, IsZeroOn (operator i) ⟨(support i)ᶜ, (support_closed i).isOpen_compl⟩
  total : ∑ i, operator i = 𝟙 F

/-- Fineness for finite covers of the actual topological space. On a
compact space these covers suffice for arbitrary-cover cocycle lifting. -/
def FiniteFine (F : TopCat.Sheaf AddCommGrpCat.{0} X) : Prop :=
  ∀ (ι : Type) [Fintype ι] (U : ι → Opens X), (∀ x : X, ∃ i : ι, x ∈ U i) →
    Nonempty (FiniteDecomposition F U)

/-- A local additive functor carries an actual fine decomposition to
an actual fine decomposition with the same closed supports. -/
def FiniteDecomposition.map {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι : Type} [Fintype ι] {U : ι → Opens X} (d : FiniteDecomposition F U)
    (K : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X)
    [K.Additive] (hK : IsLocalFunctor K) : FiniteDecomposition (K.obj F) U where
  operator i := K.map (d.operator i)
  support := d.support
  support_closed := d.support_closed
  subordinate := d.subordinate
  zeroOutside i := hK (d.operator i) _ (d.zeroOutside i)
  total := by rw [← K.map_sum, d.total, K.map_id]

/-- Fineness is retained by an actual local additive functor. -/
theorem FiniteFine.map {F : TopCat.Sheaf AddCommGrpCat.{0} X} (hF : FiniteFine F)
    (K : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X)
    [K.Additive] (hK : IsLocalFunctor K) : FiniteFine (K.obj F) := by
  intro ι _ U hU
  obtain ⟨d⟩ := hF ι U hU
  exact ⟨d.map K hK⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology
