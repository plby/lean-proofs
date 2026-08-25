import StackExchange.Puzzling139335.JordanFixedPoint
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Path

/-!
# Contractions of closed Jordan regions

The existing Schoenflies square chart transports a straight-line contraction
back to the given region.  The contraction fixes its chosen base point.  In
particular, a loop lying in a closed Jordan region contracts, with its endpoints
fixed, in the complement of any point outside that region.
-/

open Set unitInterval

namespace Puzzling139335.CentralRotation.BoundaryOrientation

noncomputable section

private abbrev ModelSquare := Schoenflies.Plane.closedSquare 0 1

/-- The straight-line contraction of the closed model square to a chosen point. -/
private def squareContraction (b : ModelSquare) :
    ContinuousMap.Homotopy (ContinuousMap.id ModelSquare) (ContinuousMap.const _ b) where
  toFun p := ⟨(1 - (p.1 : ℝ)) • (p.2 : Plane) + (p.1 : ℝ) • (b : Plane),
    (Schoenflies.Plane.convex_closedSquare 0 1) p.2.property b.property
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel _ _)⟩
  continuous_toFun := by fun_prop
  map_zero_left p := by apply Subtype.ext; simp
  map_one_left p := by apply Subtype.ext; simp

private theorem squareContraction_stationary (b : ModelSquare) (t : I) :
    squareContraction b (t, b) = b := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • (b : Plane) + (t : ℝ) • (b : Plane) = (b : Plane)
  rw [← add_smul, sub_add_cancel, one_smul]

/-- A concrete contraction of a closed Jordan region to any chosen point in it. -/
def jordanContraction {P : Set Plane} (hP : IsJordanRegion P) (b : P) :
    ContinuousMap.Homotopy (ContinuousMap.id P) (ContinuousMap.const _ b) := by
  let e := Classical.choice hP.nonempty_homeomorph_closedSquare
  exact {
    toFun := fun p => e.symm (squareContraction (e b) (p.1, e p.2))
    continuous_toFun := by fun_prop
    map_zero_left := fun p => by simp
    map_one_left := fun p => by simp }

/-- The chosen base point remains fixed throughout the contraction. -/
theorem jordanContraction_stationary {P : Set Plane} (hP : IsJordanRegion P)
    (b : P) (t : I) : jordanContraction hP b (t, b) = b := by
  let e := Classical.choice hP.nonempty_homeomorph_closedSquare
  change e.symm (squareContraction (e b) (t, e b)) = b
  rw [squareContraction_stationary, Homeomorph.symm_apply_apply]

/-- The subtype of a closed Jordan region is a contractible topological space. -/
theorem jordan_contractibleSpace {P : Set Plane} (hP : IsJordanRegion P) :
    ContractibleSpace P := by
  obtain ⟨b, hb⟩ := hP.nonempty
  exact (contractible_iff_id_nullhomotopic P).mpr
    ⟨⟨b, hb⟩, ⟨jordanContraction hP ⟨b, hb⟩⟩⟩

/-- A region omitting `x` includes continuously into the complement of `x`. -/
def regionToPointComplement {P : Set Plane} {x : Plane} (hx : x ∉ P) :
    C(P, ({x}ᶜ : Set Plane)) :=
  ContinuousMap.inclusion (Set.subset_compl_singleton_iff.mpr hx)

/-- Restrict the codomain of a continuous map to a region containing its range. -/
def regionMap {X : Type*} [TopologicalSpace X] {P : Set Plane}
    (f : C(X, Plane)) (hf : ∀ t, f t ∈ P) : C(X, P) :=
  ⟨fun t => ⟨f t, hf t⟩, f.continuous.subtype_mk _⟩

/-- Regard a map into a region as a map avoiding a specified exterior point. -/
def mapInPointComplement {X : Type*} [TopologicalSpace X] {P : Set Plane}
    (f : C(X, Plane)) (hf : ∀ t, f t ∈ P) {x : Plane} (hx : x ∉ P) :
    C(X, ({x}ᶜ : Set Plane)) :=
  (regionToPointComplement hx).comp (regionMap f hf)

@[simp] theorem mapInPointComplement_coe {X : Type*} [TopologicalSpace X]
    {P : Set Plane} (f : C(X, Plane)) (hf : ∀ t, f t ∈ P)
    {x : Plane} (hx : x ∉ P) (t : X) :
    (mapInPointComplement f hf hx t : Plane) = f t := rfl

/-- A map into a closed Jordan region contracts in the complement of every
point outside the region. -/
def mapNullhomotopy {X : Type*} [TopologicalSpace X] {P : Set Plane}
    (hP : IsJordanRegion P) (b : P) (f : C(X, Plane)) (hf : ∀ t, f t ∈ P)
    {x : Plane} (hx : x ∉ P) :
    ContinuousMap.Homotopy (mapInPointComplement f hf hx)
      (ContinuousMap.const X (regionToPointComplement hx b)) where
  toFun p := regionToPointComplement hx
    (jordanContraction hP b (p.1, regionMap f hf p.2))
  continuous_toFun := by fun_prop
  map_zero_left t := by simp [mapInPointComplement]
  map_one_left t := by simp

/-- Every continuous map into a closed Jordan region is nullhomotopic in the
complement of any point outside the region. -/
theorem map_nullhomotopic_complement {X : Type*} [TopologicalSpace X]
    {P : Set Plane} (hP : IsJordanRegion P) (f : C(X, Plane))
    (hf : ∀ t, f t ∈ P) {x : Plane} (hx : x ∉ P) :
    (mapInPointComplement f hf hx).Nullhomotopic := by
  obtain ⟨b, hb⟩ := hP.nonempty
  exact ⟨regionToPointComplement hx ⟨b, hb⟩, ⟨mapNullhomotopy hP ⟨b, hb⟩ f hf hx⟩⟩

/-- A loop in a Jordan region has an endpoint-fixing nullhomotopy which avoids
any exterior point.  The result uses the literal complement subtype so that it
can be composed directly with a direction map. -/
def loopNullhomotopy {P : Set Plane} (hP : IsJordanRegion P)
    (f : C(I, Plane)) (hf : ∀ t, f t ∈ P) (hloop : f 0 = f 1)
    {x : Plane} (hx : x ∉ P) :
    ContinuousMap.HomotopyRel (mapInPointComplement f hf hx)
      (ContinuousMap.const I (mapInPointComplement f hf hx 0)) {0, 1} where
  toHomotopy := mapNullhomotopy hP ⟨f 0, hf 0⟩ f hf hx
  prop' t s hs := by
    have hs0 : regionMap f hf s = (⟨f 0, hf 0⟩ : P) := by
      apply Subtype.ext
      change f s = f 0
      rcases Set.mem_insert_iff.mp hs with rfl | hs
      · rfl
      · have hs1 : s = 1 := Set.mem_singleton_iff.mp hs
        simpa only [hs1] using hloop.symm
    change regionToPointComplement hx
      (jordanContraction hP ⟨f 0, hf 0⟩ (t, regionMap f hf s)) =
        regionToPointComplement hx (regionMap f hf s)
    rw [hs0, jordanContraction_stationary]

/-- The proposition-level version of the endpoint-fixing loop contraction. -/
theorem loop_homotopic_const_complement {P : Set Plane} (hP : IsJordanRegion P)
    (f : C(I, Plane)) (hf : ∀ t, f t ∈ P) (hloop : f 0 = f 1)
    {x : Plane} (hx : x ∉ P) :
    ContinuousMap.HomotopicRel (mapInPointComplement f hf hx)
      (ContinuousMap.const I (mapInPointComplement f hf hx 0)) {0, 1} :=
  ⟨loopNullhomotopy hP f hf hloop hx⟩

end

end Puzzling139335.CentralRotation.BoundaryOrientation
