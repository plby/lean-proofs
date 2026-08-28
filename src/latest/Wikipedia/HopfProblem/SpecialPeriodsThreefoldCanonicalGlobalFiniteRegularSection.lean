import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalFiniteRegularSectionGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonCompatibility

/-!
# The actual canonical form off the cusp and the second elliptic fibre

The genuine regular canonical form and its first elliptic extension agree
on their entire actual overlap.  They therefore define a nowhere-zero
holomorphic section of the original global canonical bundle on exactly
the generic open of the prescribed Cartier divisor.  The resulting
section also agrees with the second elliptic extension wherever that
patch meets the generic open.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalFiniteRegularSection

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The first elliptic patch contains every point of the actual generic
open which is not in the original regular locus. -/
theorem mem_threePatch_of_not_regular (y : domain) (hy : y.val ∉ regularLocus) :
    y.val ∈ Threefold.liftedPatch (some (some .three)) :=
  (mem_regular_or_threePatch_of_mem_domain y.property).resolve_left hy

/-- The actual canonical vector, glued in the literal fibre over the original point. -/
def genericSection (y : domain) : Threefold.Canonical.bundle.Fiber y.val := by
  classical
  exact if hy : y.val ∈ regularLocus then GlobalRegular.globalSection ⟨y.val, hy⟩
    else GlobalEllipticComparison.extendedSection .three
      ⟨y.val, mem_threePatch_of_not_regular y hy⟩

def genericSectionMap (y : domain) : Threefold.Canonical.bundle.TotalSpace :=
  ⟨y.val, genericSection y⟩

@[simp] theorem genericSectionMap_proj (y : domain) : (genericSectionMap y).proj = y.val := rfl

/-- Exact recovery of the original regular form. -/
theorem genericSection_eq_regular (y : domain) (hy : y.val ∈ regularLocus) :
    genericSection y = GlobalRegular.globalSection ⟨y.val, hy⟩ := by
  classical
  exact dif_pos hy

/-- Exact agreement with the first elliptic extension on its full patch. -/
theorem genericSection_eq_three (y : domain)
    (hy : y.val ∈ Threefold.liftedPatch (some (some .three))) :
    genericSection y = GlobalEllipticComparison.extendedSection .three ⟨y.val, hy⟩ := by
  classical
  by_cases hr : y.val ∈ regularLocus
  · exact (genericSection_eq_regular y hr).trans
      (GlobalEllipticComparison.globalSection_eq_extendedSection .three ⟨y.val, hy⟩ hr)
  · exact dif_neg hr

/-- The generic open meets the second elliptic patch only in its actual
regular part, where the already proved whole-overlap identity applies. -/
theorem genericSection_eq_four (y : domain)
    (hy : y.val ∈ Threefold.liftedPatch (some (some .four))) :
    genericSection y = GlobalEllipticComparison.extendedSection .four ⟨y.val, hy⟩ := by
  have hr : y.val ∈ regularLocus := domain_inf_fourPatch_le_regularLocus ⟨y.property, hy⟩
  exact (genericSection_eq_regular y hr).trans
    (GlobalEllipticComparison.globalSection_eq_extendedSection .four ⟨y.val, hy⟩ hr)

theorem genericSection_ne_zero (y : domain) : genericSection y ≠ 0 := by
  by_cases hy : y.val ∈ regularLocus
  · rw [genericSection_eq_regular y hy]
    exact GlobalRegular.globalSection_ne_zero ⟨y.val, hy⟩
  · rw [genericSection_eq_three y (mem_threePatch_of_not_regular y hy)]
    exact GlobalEllipticComparison.extendedSection_three_ne_zero _

/-- The original regular open embeds into exactly the prescribed generic open. -/
def regularInclusion (y : regularLocus) : domain := ⟨y.val, regularLocus_le_domain y.property⟩

/-- The entire first elliptic patch embeds into the same original open. -/
def threeInclusion (y : Threefold.liftedPatch (some (some .three))) : domain :=
  ⟨y.val, threePatch_le_domain y.property⟩

theorem regularInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph IF IF ω regularInclusion :=
  isLocalDiffeomorph_codRestrictOpens IF IF
    (isLocalDiffeomorph_subtypeVal IF regularLocus) domain
      (fun y => regularLocus_le_domain y.property)

theorem threeInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph IF IF ω threeInclusion :=
  isLocalDiffeomorph_codRestrictOpens IF IF
    (isLocalDiffeomorph_subtypeVal IF (Threefold.liftedPatch (some (some .three)))) domain
      (fun y => threePatch_le_domain y.property)

@[simp] theorem genericSectionMap_regularInclusion (y : regularLocus) :
    genericSectionMap (regularInclusion y) = GlobalRegular.globalSectionMap y :=
  congrArg (fun v : Threefold.Canonical.bundle.Fiber y.val =>
    (⟨y.val, v⟩ : Threefold.Canonical.bundle.TotalSpace))
      (genericSection_eq_regular (regularInclusion y) y.property)

@[simp] theorem genericSectionMap_threeInclusion
    (y : Threefold.liftedPatch (some (some .three))) :
    genericSectionMap (threeInclusion y) =
      GlobalEllipticComparison.extendedSectionMap .three y :=
  congrArg (fun v : Threefold.Canonical.bundle.Fiber y.val =>
    (⟨y.val, v⟩ : Threefold.Canonical.bundle.TotalSpace))
      (genericSection_eq_three (threeInclusion y) y.property)

private theorem holomorphicAt_of_local_cover
    {M : Type*} [TopologicalSpace M] [ChartedSpace Model M]
    {f : M → domain} (hf : IsLocalDiffeomorph IF IF ω f) (x : M)
    (hh : ContMDiff IF Iᴷ ω (genericSectionMap ∘ f)) :
    ContMDiffAt IF Iᴷ ω genericSectionMap (f x) := by
  have h := hh.contMDiffAt.comp (f x) (hf x).localInverse_contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [(hf x).localInverse_eventuallyEq_right] with y hy
  change genericSectionMap y = genericSectionMap (f ((hf x).localInverse y))
  exact congrArg genericSectionMap hy.symm

/-- Holomorphicity is obtained from the two genuine local sections and
the local inverses of the original open inclusions. -/
theorem genericSectionMap_holomorphic : ContMDiff IF Iᴷ ω genericSectionMap := by
  intro y
  rcases mem_regular_or_threePatch_of_mem_domain y.property with hy | hy
  · let x : regularLocus := ⟨y.val, hy⟩
    have he : genericSectionMap ∘ regularInclusion = GlobalRegular.globalSectionMap :=
      funext genericSectionMap_regularInclusion
    have hh : ContMDiff IF Iᴷ ω (genericSectionMap ∘ regularInclusion) := by
      rw [he]
      exact GlobalRegular.globalSectionMap_holomorphic
    exact holomorphicAt_of_local_cover regularInclusion_isLocalDiffeomorph x hh
  · let x : Threefold.liftedPatch (some (some .three)) := ⟨y.val, hy⟩
    have he : genericSectionMap ∘ threeInclusion =
        GlobalEllipticComparison.extendedSectionMap .three :=
      funext genericSectionMap_threeInclusion
    have hh : ContMDiff IF Iᴷ ω (genericSectionMap ∘ threeInclusion) := by
      rw [he]
      exact GlobalEllipticComparison.extendedSectionMap_holomorphic .three
    exact holomorphicAt_of_local_cover threeInclusion_isLocalDiffeomorph x hh

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalFiniteRegularSection
