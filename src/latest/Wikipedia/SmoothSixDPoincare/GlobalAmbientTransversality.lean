import Wikipedia.SmoothSixDPoincare.AmbientTransverseStep

/-!
# Global transversality by constructed ambient diffeomorphisms

A finite family of compact source cores is treated one at a time. Each
ambient step retains the already transverse cores and every future plateau
condition. The cores themselves are constructed from the original smooth
map and cover its entire compact source.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.NativeTransversality

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

/-- The finite induction composes actual ambient diffeomorphisms of the same manifold. -/
theorem exists_finite_patch_diffeomorph {ι : Type*} [Finite ι]
    (p : ι → Patch J X (N := N)) {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G)
    (s : Finset ι) :
    ∃ e : Diffeomorph J J N N ∞,
      SupportedDiffeomorph.IsotopicToIdentity e ∧
      (∀ j, (p j).Compatible (e ∘ f)) ∧
      ∀ j ∈ s, ∀ x ∈ (p j).core, ∀ y, At I I' J (e ∘ f) g x y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Diffeomorph.refl J N ∞, SupportedDiffeomorph.isotopicToIdentity_refl,
      hcompatible, ?_⟩
    intro j hj
    simp at hj
  | @insert i s _ ih =>
    obtain ⟨e₁, hiso₁, hc₁, ht₁⟩ := ih
    let C : Set X := ⋃ j ∈ s, (p j).core
    have hC : IsCompact C := s.isCompact_biUnion (fun j _ => (p j).core_compact)
    have htrans : ∀ x ∈ C, ∀ y, At I I' J (e₁ ∘ f) g x y := by
      intro x hx y
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      exact ht₁ j hj x hxj y
    obtain ⟨e₂, hc₂, ht₂, -, hiso₂⟩ :=
      exists_patch_step p i (e₁.contMDiff.comp hf) hg hc₁ hdim hC htrans
    refine ⟨e₁.trans e₂, hiso₁.trans hiso₂, hc₂, ?_⟩
    intro j hj x hx y
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact ht₂ x (Or.inr hx) y
    · exact ht₂ x (Or.inl (mem_iUnion₂.mpr ⟨j, hjs, hx⟩)) y

variable [CompactSpace X] [T2Space X]

omit [LindelofSpace (X × Y)] in
/-- Compact smooth sheets of complementary dimensions can be made transverse by an actual
ambient diffeomorphism. No initial transversality, chart cover, or perturbation is assumed. -/
theorem exists_ambient_transverse_diffeomorph {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) :
    ∃ e : Diffeomorph J J N N ∞, SupportedDiffeomorph.IsotopicToIdentity e ∧
      ∀ x y, At I I' J (e ∘ f) g x y := by
  classical
  choose p hp hx using fun x : X => exists_patch_at (J := J) hf.continuous x
  have hcover : (univ : Set X) ⊆ ⋃ x : X, interior (p x).core := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => interior (p x).core) (fun _ => isOpen_interior) hcover
  obtain ⟨e, hisotopy, -, ht⟩ := exists_finite_patch_diffeomorph (fun i : s => p i.1) hf hg
    (fun i => hp i.1) hdim Finset.univ
  refine ⟨e, hisotopy, ?_⟩
  intro x y
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  exact ht ⟨i, hi⟩ (Finset.mem_univ _) x (interior_subset hxi) y

end Wikipedia.SmoothSixDPoincare.NativeTransversality
