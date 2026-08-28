import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicCover
import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackRegular

/-!
# Constant genuine meromorphic restrictions on regular fibres

Constancy is stated using the original fraction-germ meromorphic
function: its actual regular values agree on the fibre, and at least
one point of that fibre is regular for the function.  Poles and
indeterminacy elsewhere are allowed.  Pulling the native holomorphic
representative back to the actual regular cover gives the analytic
function to which the uncountability argument applies.
-/

noncomputable section

open Set Filter Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover

open HolomorphicForms.RegularCover

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  coverChartedSpace cover_isManifold

/-- A genuine meromorphic restriction has one finite regular point and
one common value at all its regular points in the literal fibre. -/
def ConstantOnFibre (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (b : RiemannSphere) : Prop :=
  ∃ c : ℂ,
    (∃ x : Threefold.Space, projectionSphere x = b ∧
      HolomorphicMeromorphic.RegularAt IF Threefold.Space g ⟨x, by trivial⟩) ∧
    ∀ x : Threefold.Space, projectionSphere x = b →
      HolomorphicMeromorphic.RegularAt IF Threefold.Space g ⟨x, by trivial⟩ →
      HolomorphicMeromorphic.value IF Threefold.Space g ⟨x, by trivial⟩ = c

/-- The actual regular base values with constant meromorphic restriction. -/
def constantRegularFibres (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    Set RiemannSphere := {b | b ∈ sphereRegularPatch ∧ ConstantOnFibre g b}

/-- The inverse image of the original function's genuine holomorphic locus. -/
def holomorphicCoverDomain (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    Opens Cover :=
  HolomorphicMeromorphic.pullbackOpen IF IF toThreefold
    (HolomorphicMeromorphic.regularDomain IF Threefold.Space g)

theorem mem_holomorphicCoverDomain_iff
    (g : HolomorphicMeromorphic.Function IF Threefold.Space) (x : Cover) :
    x ∈ holomorphicCoverDomain g ↔
      HolomorphicMeromorphic.RegularAt IF Threefold.Space g ⟨toThreefold x, by trivial⟩ := by
  change toThreefold x ∈ HolomorphicMeromorphic.regularDomain IF Threefold.Space g ↔ _
  constructor
  · intro hx
    exact HolomorphicMeromorphic.regularAt_of_mem_regularDomain IF Threefold.Space g
      ⟨toThreefold x, hx⟩
  · intro hx
    exact ⟨⟨toThreefold x, by trivial⟩, hx, rfl⟩

/-- This is the original holomorphic representative, composed with the
actual quotient map, on its literal inverse-image domain. -/
def coverRepresentative (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    HolomorphicFunctionSheaf.Section IF Cover (holomorphicCoverDomain g) :=
  HolomorphicMeromorphic.holomorphicPullback IF IF toThreefold
    (HolomorphicMeromorphic.regularDomain IF Threefold.Space g)
    (HolomorphicMeromorphic.regularRepresentative IF Threefold.Space g)

@[simp] theorem coverRepresentative_apply
    (g : HolomorphicMeromorphic.Function IF Threefold.Space) (x : holomorphicCoverDomain g) :
    coverRepresentative g x =
      HolomorphicMeromorphic.value IF Threefold.Space g ⟨toThreefold x.val, by trivial⟩ := rfl

/-- The representative agrees as full meromorphic germs on the actual cover. -/
theorem coverRepresentative_germ
    (g : HolomorphicMeromorphic.Function IF Threefold.Space) (x : holomorphicCoverDomain g) :
    coverPullback g ⟨x.val, by trivial⟩ =
      HolomorphicMeromorphic.sectionGerm IF Cover (holomorphicCoverDomain g) x
        (coverRepresentative g) := by
  apply HolomorphicMeromorphic.pullbackSection_holomorphic_representation IF IF
    toThreefold toThreefold_isOpenMap
    (HolomorphicMeromorphic.regularDomain_le IF Threefold.Space g) g
    (HolomorphicMeromorphic.regularRepresentative IF Threefold.Space g)
  intro y
  exact (HolomorphicMeromorphic.regularRepresentative_germ IF Threefold.Space g y).symm

/-- Original free base points with a regular lift on a constant fibre. -/
def constantSourceParameters (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    Set TriangleRegularPoint :=
  {z | ConstantOnFibre g (sourceBase z) ∧ ∃ v : ComplexPlane₂, (z, v) ∈ holomorphicCoverDomain g}

theorem constantRegularFibres_subset_sourceBase_image
    (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    constantRegularFibres g ⊆ sourceBase '' constantSourceParameters g := by
  rintro b ⟨hb, hc⟩
  obtain ⟨c, ⟨x, hxb, hxg⟩, hconst⟩ := hc
  have hxr : x ∈ regularLocus :=
    (mem_regularLocus_iff_sphere x).mpr (hxb.symm ▸ hb)
  obtain ⟨u, hu⟩ := exists_toThreefold_eq x hxr
  have hub : sourceBase u.1 = b :=
    (projectionSphere_toThreefold u.1 u.2).symm.trans ((congrArg projectionSphere hu).trans hxb)
  refine ⟨u.1, ⟨?_, u.2, ?_⟩, hub⟩
  · rw [hub]
    exact ⟨c, ⟨x, hxb, hxg⟩, hconst⟩
  · apply (mem_holomorphicCoverDomain_iff g u).mpr
    simpa only [hu] using hxg

/-- Uncountability of genuine constant regular fibres survives passage
to original free base parameters; no choice of a preferred lift is assumed. -/
theorem constantSourceParameters_uncountable
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (constantRegularFibres g).Countable) :
    ¬ (constantSourceParameters g).Countable := by
  intro hs
  exact hg ((hs.image sourceBase).mono (constantRegularFibres_subset_sourceBase_image g))

/-- In the original complex coordinate the relevant base parameters
are still uncountable, since the inherited coordinate is injective. -/
theorem complex_constantSourceParameters_uncountable
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (constantRegularFibres g).Countable) :
    ¬ ((fun z : TriangleRegularPoint => (z.val : ℂ)) '' constantSourceParameters g).Countable := by
  intro hs
  apply constantSourceParameters_uncountable g hg
  apply Set.MapsTo.countable_of_injOn
    (f := fun z : TriangleRegularPoint => (z.val : ℂ)) (mapsTo_image _ _) ?_ hs
  exact (UpperHalfPlane.coe_injective.comp Subtype.val_injective).injOn

/-- On every relevant source fibre, the actual holomorphic cover
representative has one common value wherever it is defined. -/
theorem coverRepresentative_fibre_constant
    (g : HolomorphicMeromorphic.Function IF Threefold.Space) (z : TriangleRegularPoint)
    (hz : z ∈ constantSourceParameters g) (v w : ComplexPlane₂)
    (hv : (z, v) ∈ holomorphicCoverDomain g) (hw : (z, w) ∈ holomorphicCoverDomain g) :
    coverRepresentative g ⟨(z, v), hv⟩ = coverRepresentative g ⟨(z, w), hw⟩ := by
  obtain ⟨c, _, hc⟩ := hz.1
  exact (hc (toThreefold (z, v)) (projectionSphere_toThreefold z v)
    ((mem_holomorphicCoverDomain_iff g (z, v)).mp hv)).trans
      (hc (toThreefold (z, w)) (projectionSphere_toThreefold z w)
        ((mem_holomorphicCoverDomain_iff g (z, w)).mp hw)).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover
