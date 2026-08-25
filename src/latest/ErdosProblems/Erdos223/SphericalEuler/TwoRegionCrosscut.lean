import Wikipedia.SchoenfliesTheorem.FaceCyclesLand

open Metric Set unitInterval

namespace Schoenflies

/-- A finite-bookkeeping form of `crosscutSplitsRegion`.  The separating hypotheses for the
two closed-up arcs are explicit, which is exactly what a plane graph supplies from its two
spliced cycles.  This version needs only the `FaceCyclesLand` dependency closure. -/
theorem crosscut_two_regions
    {J A₁ A₂ P Ω : Set Plane} {p q : Plane}
    (hJsep : IsSeparating J)
    (hJ1sep : IsSeparating (A₁ ∪ P)) (hJ2sep : IsSeparating (A₂ ∪ P))
    (hJpoly : IsPolygonal J) (hPpoly : IsPolygonal P)
    (hA1 : IsArcBetween A₁ p q) (hA2 : IsArcBetween A₂ p q)
    (hunion : A₁ ∪ A₂ = J) (hinter : A₁ ∩ A₂ = {p, q})
    (hParc : IsArcBetween P p q) (hPJ : P ∩ J = {p, q})
    (hΩ : IsRegionOf J Ω) (hPsub : P \ {p, q} ⊆ Ω) :
    ∃ U V : Set Plane,
      Ω \ P = U ∪ V ∧ Disjoint U V ∧ U.Nonempty ∧ V.Nonempty ∧
      IsOpen U ∧ IsOpen V ∧ IsPreconnected U ∧ IsPreconnected V ∧
      ((IsRegionOf (A₁ ∪ P) U ∧ IsRegionOf (A₂ ∪ P) V) ∨
       (IsRegionOf (A₁ ∪ P) V ∧ IsRegionOf (A₂ ∪ P) U)) := by
  have hpJ : p ∈ J := by rw [← hunion]; exact Or.inl hA1.left_mem
  have hqJ : q ∈ J := by rw [← hunion]; exact Or.inl hA1.right_mem
  have hA1J : A₁ ⊆ J := by intro x hx; rw [← hunion]; exact Or.inl hx
  have hA2J : A₂ ⊆ J := by intro x hx; rw [← hunion]; exact Or.inr hx
  have hpqA1 : ({p, q} : Set Plane) ⊆ A₁ := by
    rw [← hinter]
    exact Set.inter_subset_left
  have hpqA2 : ({p, q} : Set Plane) ⊆ A₂ := by
    rw [← hinter]
    exact Set.inter_subset_right
  have hAne : A₁ ≠ A₂ := arcs_ne (le_of_eq hinter) (by
    intro hsub
    obtain ⟨-, w, hw⟩ := hA1.preconnected_diff
    exact hw.2 (hsub hw.1))
  obtain ⟨Ω', hΩpair⟩ : ∃ Ω' : Set Plane, IsRegionPair J Ω Ω' := by
    rcases hΩ with h | h
    · exact ⟨outside J, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨inside J, Or.inr ⟨h, rfl⟩⟩
  obtain ⟨y, hy⟩ := (hΩpair.right.isConnected hJsep).nonempty
  have hyNotΩ : y ∉ Ω := fun hyΩ => Set.disjoint_left.1 hΩpair.disjoint hyΩ hy
  have hnotP : ∀ w ∈ Ω', w ∉ P := by
    intro w hw hwP
    have hwJ : w ∉ J := hΩpair.right.subset_compl hw
    have hwpq : w ∉ ({p, q} : Set Plane) := by
      rintro (rfl | rfl)
      exacts [hwJ hpJ, hwJ hqJ]
    exact Set.disjoint_left.1 hΩpair.disjoint (hPsub ⟨hwP, hwpq⟩) hw
  have hΩ'sub : ∀ A : Set Plane, A ⊆ J → Ω' ⊆ (A ∪ P)ᶜ := by
    intro A hAJ w hw
    rintro (h | h)
    · exact hΩpair.right.subset_compl hw (hAJ h)
    · exact hnotP w hw h
  have hyJ1 : y ∉ A₁ ∪ P := hΩ'sub A₁ hA1J hy
  have hyJ2 : y ∉ A₂ ∪ P := hΩ'sub A₂ hA2J hy
  have hΩW1 : Ω' ⊆ connectedComponentIn (A₁ ∪ P)ᶜ y :=
    (hΩpair.right.isConnected hJsep).isPreconnected.subset_connectedComponentIn hy
      (hΩ'sub A₁ hA1J)
  have hΩW2 : Ω' ⊆ connectedComponentIn (A₂ ∪ P)ᶜ y :=
    (hΩpair.right.isConnected hJsep).isPreconnected.subset_connectedComponentIn hy
      (hΩ'sub A₂ hA2J)
  let U := farRegion (A₁ ∪ P) y
  let V := farRegion (A₂ ∪ P) y
  have hWV1 : IsRegionPair (A₁ ∪ P) (connectedComponentIn (A₁ ∪ P)ᶜ y) U :=
    hJ1sep.isRegionPair_farRegion hyJ1
  have hWV2 : IsRegionPair (A₂ ∪ P) (connectedComponentIn (A₂ ∪ P)ᶜ y) V :=
    hJ2sep.isRegionPair_farRegion hyJ2
  obtain ⟨⟨hUsub, hUcomp⟩, ⟨hVsub, hVcomp⟩, hUneV, -, -⟩ :=
    crosscut_cells hJsep hJ1sep hJ2sep hA1J hA2J
      (by rw [hPJ]; exact hpqA1) (by rw [hPJ]; exact hpqA2) hAne hΩpair
      hWV1 hΩW1 hWV2 hΩW2
  have hUreg : IsRegionOf (A₁ ∪ P) U := hJ1sep.isRegionOf_farRegion hyJ1
  have hVreg : IsRegionOf (A₂ ∪ P) V := hJ2sep.isRegionOf_farRegion hyJ2
  have hUne : U.Nonempty := hWV1.right.isConnected hJ1sep |>.nonempty
  have hVne : V.Nonempty := hWV2.right.isConnected hJ2sep |>.nonempty
  obtain ⟨u₀, hu₀⟩ := hUne
  obtain ⟨v₀, hv₀⟩ := hVne
  have hdis : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    exact hUneV ((hUcomp x hxU).symm.trans (hVcomp x hxV))
  have region_eq_far {S W R X : Set Plane}
      (hpair : IsRegionPair S W R) (hreg : IsRegionOf S X)
      (hyW : y ∈ W) (hXsub : X ⊆ Ω \ P) : X = R := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hreg with rfl | rfl
      · exact (hyNotΩ (hXsub hyW).1).elim
      · rfl
    · rcases hreg with rfl | rfl
      · rfl
      · exact (hyNotΩ (hXsub hyW).1).elim
  have hcover : Ω \ P = U ∪ V := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxcomp : x ∈ connectedComponentIn (Ω \ P) x := mem_connectedComponentIn hx
      have hcompsub : connectedComponentIn (Ω \ P) x ⊆ Ω \ P :=
        connectedComponentIn_subset _ _
      rcases crosscutSplitsRegion J A₁ A₂ P Ω p q hJsep hJpoly hPpoly hA1 hA2
          hunion hinter hParc hPJ hΩ hPsub x hx with hreg | hreg
      · exact Or.inl ((region_eq_far hWV1 hreg (mem_connectedComponentIn hyJ1)
          hcompsub) ▸ hxcomp)
      · exact Or.inr ((region_eq_far hWV2 hreg (mem_connectedComponentIn hyJ2)
          hcompsub) ▸ hxcomp)
    · exact Set.union_subset hUsub hVsub
  refine ⟨U, V, hcover, hdis, ⟨u₀, hu₀⟩, ⟨v₀, hv₀⟩,
    hUreg.isOpen hJ1sep, hVreg.isOpen hJ2sep,
    (hUreg.isConnected hJ1sep).isPreconnected,
    (hVreg.isConnected hJ2sep).isPreconnected, Or.inl ⟨hUreg, hVreg⟩⟩

#print axioms Schoenflies.crosscut_two_regions

end Schoenflies
