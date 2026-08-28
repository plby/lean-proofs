import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyFineExtensionLinear
import Mathlib.Topology.LocallyFinite

/-!
# Locally finite support neighborhoods for actual sheaf sections

A locally finite family of supports has an actual open neighborhood
meeting only finitely many of them.  An actual section which vanishes
off one closed support restricts to zero on every disjoint open set.
These elementary support statements provide the finite local sums used
to glue a genuine locally finite sum in an arbitrary abelian sheaf.
-/

noncomputable section

open Set Filter TopologicalSpace Opposite CategoryTheory
open scoped Topology BigOperators

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {ι : Type}

/-- An actual open neighborhood meeting only the listed finitely many supports. -/
structure SummationNeighborhood (K : ι → Set X) (x : X) where
  openSet : Opens X
  indices : Finset ι
  mem_openSet : x ∈ openSet
  avoids : ∀ i ∉ indices, Disjoint (openSet : Set X) (K i)

/-- Actual local finiteness supplies such an open finite-support neighborhood. -/
theorem exists_summationNeighborhood {K : ι → Set X} (hK : LocallyFinite K) (x : X) :
    Nonempty (SummationNeighborhood K x) := by
  classical
  obtain ⟨T, hT, hfin⟩ := hK x
  obtain ⟨V, hVT, hV, hxV⟩ := mem_nhds_iff.mp hT
  refine ⟨⟨⟨V, hV⟩, hfin.toFinset, hxV, ?_⟩⟩
  intro i hi
  apply Set.disjoint_left.mpr
  intro y hy hyK
  exact hi (hfin.mem_toFinset.mpr ⟨y, hyK, hVT hy⟩)

/-- Equalities on an actual neighborhood of each point give equality of
actual sections, directly by the sheaf gluing uniqueness theorem. -/
theorem section_ext_of_local (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {U : Opens X} {a b : Section F U}
    (h : ∀ x ∈ U, ∃ (V : Opens X) (hVU : V ≤ U),
      x ∈ V ∧ res F hVU a = res F hVU b) : a = b := by
  classical
  choose V hVU hxV heq using fun x : U => h x x.property
  apply F.eq_of_locally_eq' V U (fun x => homOfLE (hVU x))
  · intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  · exact heq

/-- Finite sums agree whenever both lists contain every possibly nonzero term. -/
theorem finiteSum_eq_of_vanishing {A : Type*} [AddCommMonoid A]
    (a : ι → A) (s t : Finset ι)
    (hs : ∀ i ∉ s, a i = 0) (ht : ∀ i ∉ t, a i = 0) : s.sum a = t.sum a := by
  classical
  have hs' : s.sum a = (s ∪ t).sum a :=
    Finset.sum_subset Finset.subset_union_left (fun i _ hi => hs i hi)
  have ht' : t.sum a = (s ∪ t).sum a :=
    Finset.sum_subset Finset.subset_union_right (fun i _ hi => ht i hi)
  exact hs'.trans ht'.symm

/-- Actual sections on one open set, with a proved locally finite family
of closed supports and actual zero restrictions off those supports. -/
structure SupportedSectionFamily (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (U : Opens X) (ι : Type) where
  value : ι → Section F U
  support : ι → Set X
  support_closed : ∀ i, IsClosed (support i)
  locallyFinite : LocallyFinite support
  zeroOutside : ∀ i,
    res F (V := U ⊓ outsideSupport (support i) (support_closed i)) inf_le_left (value i) = 0

namespace SupportedSectionFamily

variable {F : TopCat.Sheaf AddCommGrpCat.{0} X} {U : Opens X}
  (a : SupportedSectionFamily F U ι)

/-- A supported actual section is zero after restriction to any disjoint open. -/
theorem res_zero_of_disjoint {V : Opens X} (hVU : V ≤ U) (i : ι)
    (hV : Disjoint (V : Set X) (a.support i)) : res F hVU (a.value i) = 0 := by
  have hVK : V ≤ U ⊓ outsideSupport (a.support i) (a.support_closed i) := by
    intro x hx
    exact ⟨hVU hx, fun hxK => Set.disjoint_left.mp hV hx hxK⟩
  have h := congrArg (res F hVK) (a.zeroOutside i)
  simpa only [res_trans, map_zero] using h

/-- Choose an actual finite-support neighborhood, using proved local finiteness. -/
def neighborhood (x : X) : SummationNeighborhood a.support x :=
  Classical.choice (exists_summationNeighborhood a.locallyFinite x)

/-- The chosen neighborhoods restricted to the original section domain. -/
def patch (x : U) : Opens X := U ⊓ (a.neighborhood x).openSet

theorem patch_le (x : U) : a.patch x ≤ U := inf_le_left

theorem mem_patch (x : U) : (x : X) ∈ a.patch x :=
  ⟨x.property, (a.neighborhood x).mem_openSet⟩

theorem patch_cover : U ≤ iSup a.patch := by
  intro x hx
  exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, a.mem_patch ⟨x, hx⟩⟩

theorem patch_avoids (x : U) (i : ι) (hi : i ∉ (a.neighborhood x).indices) :
    Disjoint (a.patch x : Set X) (a.support i) :=
  ((a.neighborhood x).avoids i hi).mono_left (fun _ h => h.2)

/-- The literal finite sum on an actual chosen neighborhood. -/
def patchValue (x : U) : Section F (a.patch x) :=
  res F (a.patch_le x) ((a.neighborhood x).indices.sum a.value)

/-- These literal finite local sums are compatible on their actual overlaps. -/
theorem patchValue_compatible : TopCat.Presheaf.IsCompatible F.obj a.patch a.patchValue := by
  intro x y
  change res F inf_le_left (a.patchValue x) = res F inf_le_right (a.patchValue y)
  simp only [patchValue, res_trans, map_sum]
  apply finiteSum_eq_of_vanishing
  · intro i hi
    exact a.res_zero_of_disjoint (inf_le_left.trans (a.patch_le x)) i
      ((a.patch_avoids x i hi).mono_left (fun _ h => h.1))
  · intro i hi
    exact a.res_zero_of_disjoint (inf_le_right.trans (a.patch_le y)) i
      ((a.patch_avoids y i hi).mono_left (fun _ h => h.2))

end SupportedSectionFamily

end Wikipedia.HopfProblem.HolomorphicSheafCohomology
