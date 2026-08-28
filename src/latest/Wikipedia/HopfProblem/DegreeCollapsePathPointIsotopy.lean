import Wikipedia.HopfProblem.DegreeCollapseDensePointIsotopies
import Wikipedia.SmoothSixDPoincare.AmbientIsotopyInverse

/-!
# Point transport along paths with the native smooth isotopy retained

The orbit of diffeomorphisms isotopic to the identity is both relatively
open and closed in the prescribed open region. This upgrades local supported
point motions to a path transport without dropping the isotopy witness.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] [T2Space M]

def isotopicPointOrbit (J : ModelWithCorners ℝ E H) (U : Set M) (x : M) : Set M :=
  {y | y ∈ U ∧ ∃ d : Diffeomorph J J M M ∞,
    IsotopicToIdentity d ∧ d x = y ∧ ∀ z ∉ U, d z = z}

theorem isOpen_isotopicPointOrbit {U : Set M} (hU : IsOpen U) (x : M) :
    IsOpen (isotopicPointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, d, hd, hdx, hdfix⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_isotopic_pointMoving (J := J) hU hyU
  apply mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  obtain ⟨e, he, hey, hefix⟩ := hmove z hz
  refine ⟨hVU hz, d.trans e, hd.trans he, ?_, ?_⟩
  · change e (d x) = z
    rw [hdx, hey]
  · intro w hw
    change e (d w) = w
    rw [hdfix w hw, hefix w hw]

theorem isOpen_sdiff_isotopicPointOrbit {U : Set M} (hU : IsOpen U) (x : M) :
    IsOpen (U \ isotopicPointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, hyOrbit⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ := exists_open_isotopic_pointMoving (J := J) hU hyU
  apply mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  refine ⟨hVU hz, ?_⟩
  rintro ⟨_, d, hd, hdx, hdfix⟩
  obtain ⟨e, he, hey, hefix⟩ := hmove z hz
  apply hyOrbit
  refine ⟨hyU, d.trans e.symm, hd.trans he.symm, ?_, ?_⟩
  · change e.symm (d x) = y
    rw [hdx, ← hey, e.symm_apply_apply]
  · intro w hw
    change e.symm (d w) = w
    rw [hdfix w hw]
    exact inverse_fixed_outside e.toEquiv hefix w hw

theorem exists_isotopic_pointMoving_of_preconnected {U A : Set M} (hU : IsOpen U)
    (hA : IsPreconnected A) (hAU : A ⊆ U) {x y : M} (hx : x ∈ A) (hy : y ∈ A) :
    ∃ d : Diffeomorph J J M M ∞, IsotopicToIdentity d ∧ d x = y ∧
      ∀ z ∉ U, d z = z := by
  have hxOrbit : x ∈ isotopicPointOrbit J U x :=
    ⟨hAU hx, Diffeomorph.refl J M ∞, isotopicToIdentity_refl, rfl, fun _ _ => rfl⟩
  have hcover : A ⊆ isotopicPointOrbit J U x ∪ (U \ isotopicPointOrbit J U x) := by
    intro z hz
    by_cases hh : z ∈ isotopicPointOrbit J U x
    · exact Or.inl hh
    · exact Or.inr ⟨hAU hz, hh⟩
  have hdisjoint : Disjoint (isotopicPointOrbit J U x) (U \ isotopicPointOrbit J U x) := by
    rw [Set.disjoint_left]
    exact fun _ hz hw => hw.2 hz
  have hsub := hA.subset_left_of_subset_union (isOpen_isotopicPointOrbit hU x)
    (isOpen_sdiff_isotopicPointOrbit hU x) hdisjoint hcover ⟨x, hx, hxOrbit⟩
  exact (hsub hy).2

theorem exists_isotopic_pointMoving_of_path {U : Set M} (hU : IsOpen U) {x y : M}
    (γ : Path x y) (hγ : ∀ t, γ t ∈ U) :
    ∃ d : Diffeomorph J J M M ∞, IsotopicToIdentity d ∧ d x = y ∧
      ∀ z ∉ U, d z = z := by
  apply exists_isotopic_pointMoving_of_preconnected (J := J) hU
    (isConnected_range γ.continuous).isPreconnected
    (show range γ ⊆ U from by rintro _ ⟨t, rfl⟩; exact hγ t)
  · exact ⟨0, γ.source⟩
  · exact ⟨1, γ.target⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
