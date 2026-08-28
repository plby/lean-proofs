import Wikipedia.HopfProblem.HolomorphicPicardContinuousCoreCoordinates

/-!
# Continuity of the original cocycle bundle's product coordinates

Near each point, the quotient coordinate is the original local bundle
coordinate divided by the supplied continuous nonzero section coordinate.
The inverse has local coordinate given by multiplication by that same
section. These local formulas prove continuity in the original native
total-space topology; no topology is transported from the product.
-/

noncomputable section

open Bundle Set Filter Topology TopologicalSpace

namespace Wikipedia.HopfProblem.HolomorphicPicard.ContinuousCore

open HolomorphicPicardNative HolomorphicExponentialSheaf
open HolomorphicFunctionSheaf.SphereH1

open Classical in
private def extendedCoordinate {M : Type} [TopologicalSpace M] {ι : Type}
    (U : ι → Opens M) (a : ∀ i : ι, C(U i, ℂ)) (i : ι) (x : M) : ℂ :=
  if hx : x ∈ U i then a i ⟨x, hx⟩ else 0

private theorem extendedCoordinate_continuousAt {M : Type} [TopologicalSpace M] {ι : Type}
    (U : ι → Opens M) (a : ∀ i : ι, C(U i, ℂ)) (i : ι) (x : M) (hx : x ∈ U i) :
    ContinuousAt (extendedCoordinate U a i) x := by
  have h : ContinuousOn (extendedCoordinate U a i) (U i : Set M) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun y : U i => extendedCoordinate U a i y)
    have he : (fun y : U i => extendedCoordinate U a i y) = a i := by
      funext y
      simp only [extendedCoordinate, dif_pos y.property]
    rw [he]
    exact (a i).continuous
  exact h.continuousAt ((U i).isOpen.mem_nhds hx)

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type} (U : ι → Opens M) (hU : ∀ x : M, ∃ i : ι, x ∈ U i)
  (c : CechOneCocycle (unitsSheaf I M) U)
  (a : ∀ i : ι, C(U i, ℂ))
  (hne : ∀ i (x : U i), a i x ≠ 0)
  (hcompat : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
    unitSectionEval (c.value i j) ⟨x, hi, hj⟩ * a i ⟨x, hi⟩ = a j ⟨x, hj⟩)

local notation "D" => cocycleTransitionData I M U hU c
local notation "Z" => cocycleCore I M U hU c

include hne hcompat in
/-- The original native total-space map to the ordinary product is continuous. -/
theorem toProduct_continuous : Continuous (toProduct I M U hU c a) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let i : ι := (D).indexAt p.proj
  have hi : p.proj ∈ U i := (D).mem_baseSet_at p.proj
  have htr : ContinuousAt ((Z).localTriv i) p :=
    ((Z).localTriv i).toOpenPartialHomeomorph.continuousAt
      (((Z).localTriv i).mem_source.mpr hi)
  have hden : ContinuousAt
      (fun q : (Z).TotalSpace => extendedCoordinate U a i q.proj) p :=
    (extendedCoordinate_continuousAt U a i p.proj hi).comp
      (Z).continuous_proj.continuousAt
  have hn : extendedCoordinate U a i p.proj ≠ 0 := by
    simpa only [extendedCoordinate, dif_pos hi] using hne i ⟨p.proj, hi⟩
  have hquot : ContinuousAt
      (fun q : (Z).TotalSpace => ((Z).localTriv i q).2 /
        extendedCoordinate U a i q.proj) p := htr.snd.div hden hn
  have he : (fun q : (Z).TotalSpace => (toProduct I M U hU c a q).2) =ᶠ[𝓝 p]
      (fun q : (Z).TotalSpace => ((Z).localTriv i q).2 /
        extendedCoordinate U a i q.proj) := by
    filter_upwards [((U i).isOpen.preimage (Z).continuous_proj).mem_nhds hi] with q hq
    change q.proj ∈ U i at hq
    rw [toProduct_snd_localTriv I M U hU c a hne hcompat i q hq,
      extendedCoordinate, dif_pos hq]
  exact (Z).continuous_proj.continuousAt.prodMk (hquot.congr_of_eventuallyEq he)

include hcompat in
/-- The inverse product map is continuous into the unchanged native bundle topology. -/
theorem fromProduct_continuous : Continuous (fromProduct I M U hU c a) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply (FiberBundle.continuousAt_totalSpace ℂ (fromProduct I M U hU c a)).mpr
  refine ⟨continuousAt_fst, ?_⟩
  let i : ι := (D).indexAt p.1
  have hi : p.1 ∈ U i := (D).mem_baseSet_at p.1
  change ContinuousAt
    (fun q : M × ℂ => ((Z).localTriv i (fromProduct I M U hU c a q)).2) p
  have hcoord : ContinuousAt
      (fun q : M × ℂ => extendedCoordinate U a i q.1 * q.2) p :=
    ((extendedCoordinate_continuousAt U a i p.1 hi).comp continuousAt_fst).mul
      continuousAt_snd
  have he : (fun q : M × ℂ => ((Z).localTriv i (fromProduct I M U hU c a q)).2) =ᶠ[𝓝 p]
      (fun q : M × ℂ => extendedCoordinate U a i q.1 * q.2) := by
    filter_upwards [((U i).isOpen.preimage continuous_fst).mem_nhds hi] with q hq
    change q.1 ∈ U i at hq
    rw [fromProduct_localTriv I M U hU c a hcompat i q hq,
      extendedCoordinate, dif_pos hq]
  exact hcoord.congr_of_eventuallyEq he

end Wikipedia.HopfProblem.HolomorphicPicard.ContinuousCore
