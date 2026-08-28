import Wikipedia.HopfProblem.OrbitPairMeridian

/-!
# The actual meridian pullback is the normal Hopf sphere

This identifies the whole inverse image of a meridian, not just one
chosen family of orbits. The resulting homeomorphism is over the
meridian and the original threefold simultaneously. Thus the local
Hopf diagram is a pullback diagram for the actual global orbit map.
-/

noncomputable section

open Set Topology Metric

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold CuspCircleNormalTrivialization

attribute [local instance] Threefold.space_t2Space

/-- Every point of the threefold over this meridian lies on the chosen normal sphere. -/
theorem exists_normalSphereMap_of_quotientMap_eq_meridian
    (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r) (hr : r < injectiveRadius)
    {x : Threefold.Space} (y : MeridianSphere r)
    (h : CircleOrbitSpace.quotientMap x = meridian b r hr y) :
    ∃ v : NormalSphere r, normalSphereMap b r hr₀ hr v = x := by
  have hx : x ∈ fixedCurveNeighborhood := by
    change x ∈ (fixedCurveNeighborhood : Set Threefold.Space)
    rw [← quotientMap_preimage_normalOrbitImage]
    exact ⟨meridianTubePoint b r hr y, h.symm⟩
  obtain ⟨p, rfl⟩ := hx
  have hp : normalTubeProjection p = meridianTubePoint b r hr y :=
    normalOrbitTubeMap_injective ((normalOrbitTubeMap_projection p).trans h)
  have hb : p.val.1 = b := congrArg (fun q : normalOrbitTube => q.val.1) hp
  have hs : scalarHopfMap p.val.2 = (y : Transverse) :=
    congrArg (fun q : normalOrbitTube => q.val.2) hp
  have hn : ‖scalarCoordinates p.val.2‖ = r := by
    rw [← norm_radialHopfMap]
    change ‖scalarHopfMap p.val.2‖ = r
    rw [hs]
    exact meridianSphere_norm y
  refine ⟨⟨scalarCoordinates p.val.2,
    by simpa only [mem_sphere, dist_zero_right] using hn⟩, ?_⟩
  apply congrArg roundProductMap
  apply Subtype.ext
  change (b, scalarCoordinates.symm (scalarCoordinates p.val.2)) = p.val
  rw [scalarCoordinates.symm_apply_apply]
  exact Prod.ext hb.symm rfl

/-- An equality of subsets of the original threefold, with no local-image assumption. -/
theorem quotientMap_preimage_meridian_range
    (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r) (hr : r < injectiveRadius) :
    CircleOrbitSpace.quotientMap ⁻¹' range (meridian b r hr) =
      range (normalSphereMap b r hr₀ hr) := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact exists_normalSphereMap_of_quotientMap_eq_meridian b r hr₀ hr y hy.symm
  · rintro ⟨v, rfl⟩
    exact ⟨sphereHopfMap r v, (quotientMap_normalSphereMap b r hr₀ hr v).symm⟩

/-- The literal topological pullback of the global orbit projection along the meridian. -/
abbrev MeridianPullback (b : RiemannSphere) (r : ℝ) (hr : r < injectiveRadius) :=
  {p : MeridianSphere r × Threefold.Space //
    meridian b r hr p.1 = CircleOrbitSpace.quotientMap p.2}

/-- The Hopf diagram gives a continuous map into the actual pullback. -/
def meridianPullbackMap (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r)
    (hr : r < injectiveRadius) : C(NormalSphere r, MeridianPullback b r hr) where
  toFun v := ⟨(sphereHopfMap r v, normalSphereMap b r hr₀ hr v),
    (quotientMap_normalSphereMap b r hr₀ hr v).symm⟩
  continuous_toFun :=
    ((sphereHopfMap r).continuous.prodMk (normalSphereMap b r hr₀ hr).continuous).subtype_mk _

theorem meridianPullbackMap_injective (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r)
    (hr : r < injectiveRadius) : Function.Injective (meridianPullbackMap b r hr₀ hr) := by
  intro v w he
  exact normalSphereMap_injective b r hr₀ hr
    (congrArg (fun p : MeridianPullback b r hr => p.val.2) he)

theorem meridianPullbackMap_surjective (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r)
    (hr : r < injectiveRadius) : Function.Surjective (meridianPullbackMap b r hr₀ hr) := by
  intro p
  obtain ⟨v, hv⟩ := exists_normalSphereMap_of_quotientMap_eq_meridian
    b r hr₀ hr p.val.1 p.property.symm
  have hy : sphereHopfMap r v = p.val.1 := by
    apply meridian_injective b r hr
    rw [← quotientMap_normalSphereMap b r hr₀ hr v, hv]
    exact p.property.symm
  exact ⟨v, Subtype.ext (Prod.ext hy hv)⟩

/-- The pullback of the actual global orbit map along the actual meridian is the normal sphere. -/
def meridianPullbackHomeomorph (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r)
    (hr : r < injectiveRadius) : NormalSphere r ≃ₜ MeridianPullback b r hr :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (meridianPullbackMap b r hr₀ hr)
      ⟨meridianPullbackMap_injective b r hr₀ hr, meridianPullbackMap_surjective b r hr₀ hr⟩)
    (meridianPullbackMap b r hr₀ hr).continuous
    (meridianPullbackMap b r hr₀ hr).continuous.isClosedMap

/-- The identification is over the Hopf base, rather than an unrelated sphere homeomorphism. -/
@[simp] theorem meridianPullbackHomeomorph_fst (b : RiemannSphere) (r : ℝ)
    (hr₀ : 0 < r) (hr : r < injectiveRadius) (v : NormalSphere r) :
    (meridianPullbackHomeomorph b r hr₀ hr v).val.1 = sphereHopfMap r v := rfl

@[simp] theorem meridianPullbackHomeomorph_snd (b : RiemannSphere) (r : ℝ)
    (hr₀ : 0 < r) (hr : r < injectiveRadius) (v : NormalSphere r) :
    (meridianPullbackHomeomorph b r hr₀ hr v).val.2 = normalSphereMap b r hr₀ hr v := rfl

end Wikipedia.HopfProblem.OrbitPair
