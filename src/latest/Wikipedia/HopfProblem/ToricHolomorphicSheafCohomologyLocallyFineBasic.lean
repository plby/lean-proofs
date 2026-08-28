import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyFineBasic
import Mathlib.Topology.LocallyFinite

/-!
# Actual locally finite fine decompositions without compactness

The data consist of actual sheaf endomorphisms with closed locally
finite supports subordinate to an open cover.  Wherever only finitely
many supports can occur, the literal finite sum of the endomorphisms is
the identity.  This is local partition data, not an assumed vanishing
theorem.  Local additive functors retain all of these actual properties.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology

variable {X : TopCat.{0}}

/-- A locally finite partition of the identity by actual supported
endomorphisms of an actual additive sheaf. -/
structure LocallyFiniteDecomposition (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {ι : Type} (U : ι → Opens X) where
  operator : ι → (F ⟶ F)
  support : ι → Set X
  support_closed : ∀ i, IsClosed (support i)
  subordinate : ∀ i, support i ⊆ U i
  zeroOutside : ∀ i, IsZeroOn (operator i) ⟨(support i)ᶜ, (support_closed i).isOpen_compl⟩
  locallyFinite : LocallyFinite support
  localTotal : ∀ (V : Opens X) (s : Finset ι),
    (∀ i ∉ s, Disjoint (V : Set X) (support i)) →
      IsZeroOn (s.sum operator - 𝟙 F) V

/-- Genuine local fineness on arbitrary open covers, with no compactness
assumption on the underlying space. -/
def LocallyFine (F : TopCat.Sheaf AddCommGrpCat.{0} X) : Prop :=
  ∀ (ι : Type) (U : ι → Opens X), (∀ x : X, ∃ i, x ∈ U i) →
    Nonempty (LocallyFiniteDecomposition F U)

/-- Actual local additive functors preserve the supported local identity. -/
def LocallyFiniteDecomposition.map {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι : Type} {U : ι → Opens X} (d : LocallyFiniteDecomposition F U)
    (K : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X)
    [K.Additive] (hK : IsLocalFunctor K) : LocallyFiniteDecomposition (K.obj F) U where
  operator i := K.map (d.operator i)
  support := d.support
  support_closed := d.support_closed
  subordinate := d.subordinate
  zeroOutside i := hK (d.operator i) _ (d.zeroOutside i)
  locallyFinite := d.locallyFinite
  localTotal V s hs := by
    have h := hK (s.sum d.operator - 𝟙 F) V (d.localTotal V s hs)
    have hid : K.map (𝟙 F) = 𝟙 (K.obj F) := K.map_id F
    simpa only [Functor.map_sub, Functor.map_sum, hid] using h

/-- The actual locally fine property passes through local additive functors. -/
theorem LocallyFine.map {F : TopCat.Sheaf AddCommGrpCat.{0} X} (hF : LocallyFine F)
    (K : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X)
    [K.Additive] (hK : IsLocalFunctor K) : LocallyFine (K.obj F) := by
  intro ι U hU
  obtain ⟨d⟩ := hF ι U hU
  exact ⟨d.map K hK⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology
