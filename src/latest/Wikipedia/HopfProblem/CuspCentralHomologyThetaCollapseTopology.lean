import Wikipedia.HopfProblem.CuspCentralHomologySuspension
import Wikipedia.HopfProblem.CuspCentralHomologyEdgeCharacters
import Mathlib.Topology.CompactOpen

/-!
# The actual character collapse on the three-edge suspension

The theta graph is the literal suspension of the discrete three-element set.
On each of its three edges, the compact phase torus is mapped to the matching
circle by the determinant character of the corresponding hexagon ray. At the
two poles all phase values are collapsed. Joint continuity descends through
the actual suspension quotient, using local compactness of the phase torus.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace ToricComponent

/-- The three-edge graph with its actual suspension quotient topology.
The topology on `Fin 3` is Mathlib's existing discrete topology. -/
abbrev Theta := Suspension (Fin 3)

/-- The first three actual hexagon edges, without changing their labels. -/
def thetaEdgeIndex (j : Fin 3) : Fin 6 := j.castLE (by decide)

@[simp] theorem thetaEdgeIndex_zero : thetaEdgeIndex 0 = 0 := rfl
@[simp] theorem thetaEdgeIndex_one : thetaEdgeIndex 1 = 1 := rfl
@[simp] theorem thetaEdgeIndex_two : thetaEdgeIndex 2 = 2 := rfl

theorem thetaEdgeIndex_ray (j : Fin 3) :
    hexagonRay (thetaEdgeIndex j) = ![![1, 0], ![0, 1], ![-1, 1]] j := by
  fin_cases j <;> rfl

/-- Include the circle belonging to the indicated actual edge. -/
def thetaCircleInclusion (j : Fin 3) (z : Circle) : ThreeCircles :=
  ![Sum.inl z, Sum.inr (Sum.inl z), Sum.inr (Sum.inr z)] j

@[simp] theorem thetaCircleInclusion_zero (z : Circle) :
    thetaCircleInclusion 0 z = Sum.inl z := rfl

@[simp] theorem thetaCircleInclusion_one (z : Circle) :
    thetaCircleInclusion 1 z = Sum.inr (Sum.inl z) := rfl

@[simp] theorem thetaCircleInclusion_two (z : Circle) :
    thetaCircleInclusion 2 z = Sum.inr (Sum.inr z) := rfl

theorem thetaCircleInclusion_continuous (j : Fin 3) :
    Continuous (thetaCircleInclusion j) := by
  fin_cases j
  · exact continuous_inl
  · exact continuous_inr.comp continuous_inl
  · exact continuous_inr.comp continuous_inr

/-- The three literal edge characters, as one continuous map on the disjoint
union of three phase tori. -/
def thetaCharacterMap : C(CompactFibreTorus × Fin 3, ThreeCircles) where
  toFun p := thetaCircleInclusion p.2 (hexagonCharacter (thetaEdgeIndex p.2) p.1)
  continuous_toFun := continuous_prod_of_discrete_right.mpr fun j =>
    (thetaCircleInclusion_continuous j).comp
      (edgeCharacter_continuous (hexagonRay (thetaEdgeIndex j)))

@[simp] theorem thetaCharacterMap_apply (u : CompactFibreTorus) (j : Fin 3) :
    thetaCharacterMap (u, j) =
      thetaCircleInclusion j (hexagonCharacter (thetaEdgeIndex j) u) := rfl

private def thetaCharacterCollapseFun (p : CompactFibreTorus × Theta) :
    ThreeCircleSuspension :=
  Quotient.lift (s := suspensionSetoid (Fin 3))
    (fun q => Suspension.mk q.1 (thetaCharacterMap (p.1, q.2)))
    (fun a b hab => by
      apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
      rcases hab with ⟨ht, hzero | hone | hj⟩
      · exact ⟨ht, Or.inl hzero⟩
      · exact ⟨ht, Or.inr (Or.inl hone)⟩
      · exact ⟨ht, Or.inr (Or.inr (by rw [hj]))⟩) p.2

private theorem thetaCharacterCollapseFun_continuous :
    Continuous thetaCharacterCollapseFun := by
  apply (Suspension.isQuotientMap_mk (X := Fin 3)).continuous_lift_prod_right
  change Continuous (fun p : CompactFibreTorus × (unitInterval × Fin 3) =>
    Suspension.mk p.2.1 (thetaCharacterMap (p.1, p.2.2)))
  exact Suspension.continuous_mk.comp
    ((continuous_fst.comp continuous_snd).prodMk
      (thetaCharacterMap.continuous.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))

/-- The actual phase-character collapse, descended through the theta quotient. -/
def thetaCharacterCollapse : C(CompactFibreTorus × Theta, ThreeCircleSuspension) :=
  ⟨thetaCharacterCollapseFun, thetaCharacterCollapseFun_continuous⟩

@[simp] theorem thetaCharacterCollapse_mk (u : CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    thetaCharacterCollapse (u, Suspension.mk t j) =
      Suspension.mk t (thetaCircleInclusion j (hexagonCharacter (thetaEdgeIndex j) u)) := rfl

theorem thetaCharacterCollapse_continuous : Continuous thetaCharacterCollapse :=
  thetaCharacterCollapse.continuous

@[simp] theorem thetaCharacterCollapse_north (u : CompactFibreTorus) :
    thetaCharacterCollapse (u, Suspension.north) = Suspension.north := by
  simpa only [Suspension.mk_zero] using thetaCharacterCollapse_mk u 0 0

@[simp] theorem thetaCharacterCollapse_south (u : CompactFibreTorus) :
    thetaCharacterCollapse (u, Suspension.south) = Suspension.south := by
  simpa only [Suspension.mk_one] using thetaCharacterCollapse_mk u 1 0

/-- The collapse keeps the literal suspension height unchanged. -/
@[simp] theorem thetaCharacterCollapse_height (p : CompactFibreTorus × Theta) :
    Suspension.height (thetaCharacterCollapse p) = Suspension.height p.2 := by
  rcases p with ⟨u, q⟩
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rfl

/-- The actual northern open set in the product with the theta graph. -/
def thetaNorth : Set (CompactFibreTorus × Theta) := Prod.snd ⁻¹' Suspension.northOpen

/-- The actual southern open set in the product with the theta graph. -/
def thetaSouth : Set (CompactFibreTorus × Theta) := Prod.snd ⁻¹' Suspension.southOpen

@[simp] theorem mem_thetaNorth (p : CompactFibreTorus × Theta) :
    p ∈ thetaNorth ↔ (Suspension.height p.2 : ℝ) < 3 / 4 := Iff.rfl

@[simp] theorem mem_thetaSouth (p : CompactFibreTorus × Theta) :
    p ∈ thetaSouth ↔ 1 / 4 < (Suspension.height p.2 : ℝ) := Iff.rfl

theorem thetaNorth_isOpen : IsOpen thetaNorth :=
  Suspension.northOpen_isOpen.preimage continuous_snd

theorem thetaSouth_isOpen : IsOpen thetaSouth :=
  Suspension.southOpen_isOpen.preimage continuous_snd

theorem theta_open_cover : thetaNorth ∪ thetaSouth = univ := by
  rw [thetaNorth, thetaSouth, ← preimage_union, Suspension.open_cover, preimage_univ]

theorem thetaCharacterCollapse_preimage_north :
    thetaCharacterCollapse ⁻¹' Suspension.northOpen = thetaNorth := by
  ext p
  simp only [mem_preimage, Suspension.mem_northOpen, mem_thetaNorth,
    thetaCharacterCollapse_height]

theorem thetaCharacterCollapse_preimage_south :
    thetaCharacterCollapse ⁻¹' Suspension.southOpen = thetaSouth := by
  ext p
  simp only [mem_preimage, Suspension.mem_southOpen, mem_thetaSouth,
    thetaCharacterCollapse_height]

theorem thetaCharacterCollapse_mapsTo_north :
    MapsTo thetaCharacterCollapse thetaNorth Suspension.northOpen := by
  intro p hp
  rw [← thetaCharacterCollapse_preimage_north] at hp
  exact hp

theorem thetaCharacterCollapse_mapsTo_south :
    MapsTo thetaCharacterCollapse thetaSouth Suspension.southOpen := by
  intro p hp
  rw [← thetaCharacterCollapse_preimage_south] at hp
  exact hp

end Wikipedia.HopfProblem.CuspCentralHomology
