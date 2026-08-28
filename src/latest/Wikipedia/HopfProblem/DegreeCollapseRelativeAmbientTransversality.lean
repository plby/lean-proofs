import Wikipedia.HopfProblem.DegreeCollapseRelativeAmbientPatchStep

/-!
# Construct relative ambient general position with one compact support

The finite patch induction retains the whole smooth isotopy and the finite
union of its compact supports. Every support lies in the prescribed open
set, so every intermediate diffeomorphism fixes its entire complement.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare NativeTransversality SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

section Isotopy

variable {G K N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
  [TopologicalSpace N] [ChartedSpace K N]

def compose_supported_ambient_isotopies
    {e d : Diffeomorph J J N N ∞} {K₁ K₂ C : Set N}
    (A : SupportedRelativeIsotopy e K₁ C) (B : SupportedRelativeIsotopy d K₂ C) :
    SupportedRelativeIsotopy (e.trans d) (K₁ ∪ K₂) C where
  family := fun p => B.family (p.1, A.family p)
  smooth := B.smooth.comp (contMDiff_fst.prodMk A.smooth)
  zero := fun x => by rw [A.zero, B.zero]
  one := fun x => by change B.family (1, A.family (1, x)) = d (e x); rw [A.one, B.one]
  slices := by
    intro t
    obtain ⟨d₁, hd₁⟩ := A.slices t
    obtain ⟨d₂, hd₂⟩ := B.slices t
    refine ⟨d₁.trans d₂, ?_⟩
    intro x
    change d₂ (d₁ x) = B.family (t, A.family (t, x))
    rw [hd₁, hd₂]
  fixedOutside := by
    intro t x hx
    rw [A.fixedOutside t x (fun h => hx (Or.inl h)),
      B.fixedOutside t x (fun h => hx (Or.inr h))]
  fixedOn := by
    intro t x hx
    rw [A.fixedOn t x hx, B.fixedOn t x hx]

end Isotopy

variable {D Z G H H' K X Y N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
  {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
  [LindelofSpace (X × Y)]

theorem exists_finite_relative_patch_diffeomorph {ι : Type*} [Finite ι]
    (p : ι → Patch J X (N := N)) {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G)
    {U : Set N} (hsupport : ∀ j, (p j).chart.symm '' tsupport (p j).cutoff ⊆ U)
    (s : Finset ι) :
    ∃ (e : Diffeomorph J J N N ∞) (C : Set N),
      IsCompact C ∧ C ⊆ U ∧ Nonempty (SupportedRelativeIsotopy e C Uᶜ) ∧
      (∀ j, (p j).Compatible (e ∘ f)) ∧
      ∀ j ∈ s, ∀ x ∈ (p j).core, ∀ y, At I I' J (e ∘ f) g x y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    let A : SupportedRelativeIsotopy (Diffeomorph.refl J N ∞) ∅ Uᶜ := {
      family := Prod.snd
      smooth := contMDiff_snd
      zero := fun _ => rfl
      one := fun _ => rfl
      slices := fun _ => ⟨Diffeomorph.refl J N ∞, fun _ => rfl⟩
      fixedOutside := fun _ _ _ => rfl
      fixedOn := fun _ _ _ => rfl }
    refine ⟨Diffeomorph.refl J N ∞, ∅, isCompact_empty, empty_subset _, ⟨A⟩,
      hcompatible, ?_⟩
    intro j hj
    simp at hj
  | @insert i s _ ih =>
    obtain ⟨e₁, C₁, hC₁, hC₁U, ⟨A₁⟩, hc₁, ht₁⟩ := ih
    let B : Set X := ⋃ j ∈ s, (p j).core
    have hB : IsCompact B := s.isCompact_biUnion (fun j _ => (p j).core_compact)
    have htrans : ∀ x ∈ B, ∀ y, At I I' J (e₁ ∘ f) g x y := by
      intro x hx y
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      exact ht₁ j hj x hxj y
    obtain ⟨e₂, hc₂, ht₂, ⟨A₂⟩⟩ := exists_relative_ambient_patch_step (C := Uᶜ) p i
      (e₁.contMDiff.comp hf) hg hc₁ hdim hB htrans
      (fun y hy hys => hy (hsupport i hys))
    refine ⟨e₁.trans e₂, C₁ ∪ ((p i).chart.symm '' tsupport (p i).cutoff),
      hC₁.union (ambient_patch_support_compact (p i)), union_subset hC₁U (hsupport i),
      ⟨compose_supported_ambient_isotopies A₁ A₂⟩, hc₂, ?_⟩
    intro j hj x hx y
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact ht₂ x (Or.inr hx) y
    · exact ht₂ x (Or.inl (mem_iUnion₂.mpr ⟨j, hjs, hx⟩)) y

variable [CompactSpace X] [T2Space X]

omit [LindelofSpace (X × Y)] in
theorem exists_supported_ambient_transverse_in_open {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G)
    {U : Set N} (hU : IsOpen U) (hfU : range f ⊆ U) :
    ∃ (e : Diffeomorph J J N N ∞) (C : Set N),
      IsCompact C ∧ C ⊆ U ∧ Nonempty (SupportedRelativeIsotopy e C Uᶜ) ∧
      ∀ x y, At I I' J (e ∘ f) g x y := by
  classical
  choose p hp hx hs using fun x : X =>
    exists_ambient_patch_in_open (J := J) hf.continuous hU x (hfU (mem_range_self x))
  have hcover : (univ : Set X) ⊆ ⋃ x : X, interior (p x).core := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hscover⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => interior (p x).core) (fun _ => isOpen_interior) hcover
  obtain ⟨e, C, hC, hCU, hIso, -, ht⟩ := exists_finite_relative_patch_diffeomorph
    (fun i : s => p i.1) hf hg (fun i => hp i.1) hdim (fun i => hs i.1) Finset.univ
  refine ⟨e, C, hC, hCU, hIso, ?_⟩
  intro x y
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hscover (mem_univ x))
  exact ht ⟨i, hi⟩ (Finset.mem_univ _) x (interior_subset hxi) y

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
