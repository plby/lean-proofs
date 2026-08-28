import Wikipedia.SmoothSixDPoincare.OpenPointMoving
import Mathlib.Topology.Connected.PathConnected

/-!
# Supported point transport along a native path

The orbit of global diffeomorphisms fixed outside an open set is relatively
open and relatively closed there, by the constructed local point motions.
A connected set or path inside that open set therefore lies in one orbit.
This supplies global point transport without imposing a dimension-three
general-position condition on curves.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] [T2Space M]

def pointOrbit (J : ModelWithCorners ℝ E H) (U : Set M) (x : M) : Set M :=
  {y | y ∈ U ∧ ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z}

theorem isOpen_pointOrbit {U : Set M} (hU : IsOpen U) (x : M) :
    IsOpen (pointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, d, hd, hdfix⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_pointMoving (J := J) hU hyU
  apply mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  obtain ⟨e, he, hefix⟩ := hmove z hz
  refine ⟨hVU hz, d.trans e, ?_, ?_⟩
  · change e (d x) = z
    rw [hd, he]
  · intro w hw
    change e (d w) = w
    rw [hdfix w hw, hefix w hw]

theorem isOpen_sdiff_pointOrbit {U : Set M} (hU : IsOpen U) (x : M) :
    IsOpen (U \ pointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, hyOrbit⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_pointMoving (J := J) hU hyU
  apply mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  refine ⟨hVU hz, ?_⟩
  rintro ⟨_, d, hd, hdfix⟩
  obtain ⟨e, he, hefix⟩ := hmove z hz
  apply hyOrbit
  refine ⟨hyU, d.trans e.symm, ?_, ?_⟩
  · change e.symm (d x) = y
    rw [hd, ← he]
    exact e.toEquiv.symm_apply_apply y
  · intro w hw
    change e.symm (d w) = w
    rw [hdfix w hw]
    exact inverse_fixed_outside e.toEquiv hefix w hw

/-- Connectedness assembles the local constructions into an actual global diffeomorphism. -/
theorem exists_pointMoving_of_preconnected {U S : Set M} (hU : IsOpen U)
    (hS : IsPreconnected S) (hSU : S ⊆ U) {x y : M} (hx : x ∈ S) (hy : y ∈ S) :
    ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z := by
  have hxOrbit : x ∈ pointOrbit J U x :=
    ⟨hSU hx, Diffeomorph.refl J M ∞, rfl, fun _ _ => rfl⟩
  have hcover : S ⊆ pointOrbit J U x ∪ (U \ pointOrbit J U x) := by
    intro z hz
    by_cases h : z ∈ pointOrbit J U x
    · exact Or.inl h
    · exact Or.inr ⟨hSU hz, h⟩
  have hdisjoint : Disjoint (pointOrbit J U x) (U \ pointOrbit J U x) := by
    rw [Set.disjoint_left]
    exact fun _ hz hw => hw.2 hz
  have hsub := hS.subset_left_of_subset_union (isOpen_pointOrbit hU x)
    (isOpen_sdiff_pointOrbit hU x) hdisjoint hcover ⟨x, hx, hxOrbit⟩
  exact (hsub hy).2

/-- Path transport fixes every point outside the prescribed open region. -/
theorem exists_pointMoving_of_path {U : Set M} (hU : IsOpen U) {x y : M}
    (γ : Path x y) (hγ : ∀ t, γ t ∈ U) :
    ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z := by
  apply exists_pointMoving_of_preconnected (J := J) hU
    (isConnected_range γ.continuous).isPreconnected
    (show range γ ⊆ U from by rintro _ ⟨t, rfl⟩; exact hγ t)
  · exact ⟨0, γ.source⟩
  · exact ⟨1, γ.target⟩

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
