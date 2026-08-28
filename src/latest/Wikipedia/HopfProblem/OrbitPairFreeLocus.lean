import Wikipedia.HopfProblem.OrbitPairMeridianPullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRealManifold

/-!
# The actual free loci and the restricted orbit projection

Both spaces below are open subspaces of the original spaces. The
restricted projection is an open quotient map, and its fibres have
unique original circle parameters. The previously constructed meridian
and its normal sphere take values in these genuine free loci.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold CuspCircleNormalTrivialization

attribute [local instance] Threefold.chartedSpace Threefold.space_isSmoothRealManifold

local notation "Circle" => AddCircle (1 : ℝ)

def freeLocus : TopologicalSpace.Opens Threefold.Space :=
  ⟨VerticalAction.D₀ᶜ, VerticalAction.D₀_isClosed.isOpen_compl⟩

def freeOrbitLocus : TopologicalSpace.Opens CircleOrbitSpace.OrbitSpace :=
  ⟨(range CircleOrbitSpace.fixedCurveMap)ᶜ,
    CircleOrbitSpace.fixedCurveRange_isClosed.isOpen_compl⟩

theorem freeLocus_isSmoothManifold : IsManifold 𝓘(ℝ, ℂ × ComplexPlane₂) ∞ freeLocus :=
  inferInstance

theorem quotientMap_mem_freeOrbitLocus (x : freeLocus) :
    CircleOrbitSpace.quotientMap x ∈ freeOrbitLocus := by
  change x.val ∉ CircleOrbitSpace.quotientMap ⁻¹' range CircleOrbitSpace.fixedCurveMap
  rw [CircleOrbitSpace.quotientMap_preimage_fixedCurveRange]
  exact x.property

/-- The literal original projection with its domain and codomain restricted. -/
def freeOrbitProjection (x : freeLocus) : freeOrbitLocus :=
  ⟨CircleOrbitSpace.quotientMap x, quotientMap_mem_freeOrbitLocus x⟩

@[simp] theorem freeOrbitProjection_coe (x : freeLocus) :
    (freeOrbitProjection x : CircleOrbitSpace.OrbitSpace) = CircleOrbitSpace.quotientMap x := rfl

theorem freeOrbitProjection_surjective : Function.Surjective freeOrbitProjection := by
  intro y
  obtain ⟨x, hx⟩ := CircleOrbitSpace.quotientMap_surjective y.val
  have hxf : x ∈ freeLocus := by
    change x ∉ VerticalAction.D₀
    rw [← CircleOrbitSpace.quotientMap_preimage_fixedCurveRange]
    change CircleOrbitSpace.quotientMap x ∉ range CircleOrbitSpace.fixedCurveMap
    rw [hx]
    exact y.property
  exact ⟨⟨x, hxf⟩, Subtype.ext hx⟩

theorem freeOrbitProjection_continuous : Continuous freeOrbitProjection :=
  (CircleOrbitSpace.quotientMap_continuous.comp continuous_subtype_val).subtype_mk _

theorem freeOrbitProjection_isOpenMap : IsOpenMap freeOrbitProjection := by
  have h := CircleOrbitSpace.quotientMap_isOpenQuotientMap.isOpenMap.domRestrict freeLocus.isOpen
  exact h.subtype_mk _

theorem freeOrbitProjection_isOpenQuotientMap : IsOpenQuotientMap freeOrbitProjection :=
  ⟨freeOrbitProjection_surjective, freeOrbitProjection_continuous, freeOrbitProjection_isOpenMap⟩

/-- Each fibre is one free orbit, with the actual additive circle parameter. -/
theorem freeOrbitProjection_eq_iff (x y : freeLocus) :
    freeOrbitProjection x = freeOrbitProjection y ↔
      ∃! t : Circle, Homology.DeltaSweep.actionMap (t, y.val) = x.val := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := (CircleOrbitSpace.quotientMap_eq_iff x.val y.val).mp
      (congrArg Subtype.val h)
    refine ⟨t, ht, ?_⟩
    intro s hs
    exact CircleActionSemifree.orbitMap_injective y.val y.property (hs.trans ht.symm)
  · rintro ⟨t, ht, _⟩
    exact Subtype.ext ((CircleOrbitSpace.quotientMap_eq_iff _ _).mpr ⟨t, ht⟩)

/-- The actual meridian, now with its codomain in the free quotient. -/
def freeMeridian (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r)
    (hr : r < injectiveRadius) : C(MeridianSphere r, freeOrbitLocus) where
  toFun y := ⟨meridian b r hr y, meridian_not_mem_fixed b r hr₀ hr y⟩
  continuous_toFun := (meridian b r hr).continuous.subtype_mk _

theorem normalSphereMap_mem_freeLocus (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r)
    (hr : r < injectiveRadius) (v : NormalSphere r) :
    normalSphereMap b r hr₀ hr v ∈ freeLocus := by
  change normalSphereMap b r hr₀ hr v ∉ VerticalAction.D₀
  rw [← CircleOrbitSpace.quotientMap_preimage_fixedCurveRange]
  change CircleOrbitSpace.quotientMap (normalSphereMap b r hr₀ hr v) ∉
    range CircleOrbitSpace.fixedCurveMap
  rw [quotientMap_normalSphereMap]
  exact meridian_not_mem_fixed b r hr₀ hr _

/-- The actual normal Hopf sphere, now in the complement of the fixed set. -/
def freeNormalSphereMap (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r)
    (hr : r < injectiveRadius) : C(NormalSphere r, freeLocus) where
  toFun v := ⟨normalSphereMap b r hr₀ hr v, normalSphereMap_mem_freeLocus b r hr₀ hr v⟩
  continuous_toFun := (normalSphereMap b r hr₀ hr).continuous.subtype_mk _

theorem freeOrbitProjection_freeNormalSphereMap (b : RiemannSphere) (r : ℝ)
    (hr₀ : 0 < r) (hr : r < injectiveRadius) (v : NormalSphere r) :
    freeOrbitProjection (freeNormalSphereMap b r hr₀ hr v) =
      freeMeridian b r hr₀ hr (sphereHopfMap r v) :=
  Subtype.ext (quotientMap_normalSphereMap b r hr₀ hr v)

end Wikipedia.HopfProblem.OrbitPair
