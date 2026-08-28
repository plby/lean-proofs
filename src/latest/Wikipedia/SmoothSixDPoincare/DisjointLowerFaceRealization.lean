import Wikipedia.SmoothSixDPoincare.CompactBeltTubeAvoidance
import Wikipedia.SmoothSixDPoincare.ShrunkExteriorFace
import Wikipedia.SmoothSixDPoincare.SphereLinearDiffeomorph

/-!
# A belt-avoiding whole face in the common exterior of a smaller first handle

Shrink the first surgery's new piece to a closed belt tube disjoint from the
given compact face. The entire face then lies in the common exterior. Its
old-level transport misses the whole original attaching piece, and the same
whole-sublevel realization sends it exactly back to the given face.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace A]
  {f : M → ℝ} {p : M} {d : MorseSurgeryData E f p} {s : ℝ}

namespace ShrunkSurgeryRealization

variable (R : d.ShrunkSurgeryRealization s)

open Classical in
theorem exists_disjoint_lowerExteriorFace (g : C(A, d.UpperLevel))
    (hg : IsClosedEmbedding g) (havoid : Disjoint (range g) (d.closedBeltTube s)) :
    ∃ L : C(A, d.LowerLevel), IsClosedEmbedding L ∧
      Disjoint (range L) (range d.surgery.oldPiece) ∧
      (∀ z, ∃ r, R.surgery.newExterior r = g z ∧ R.surgery.oldExterior r = L z) ∧
      ∀ z, (R.attachmentHomeomorph ⟨(L z).val, Or.inl (L z).property.le⟩).val = (g z).val := by
  have hge (z) : g z ∈ range R.surgery.newExterior :=
    R.mem_newExterior_of_tube_boundary
      (fun hz => (disjoint_left.mp havoid ⟨z, rfl⟩ hz).elim)
  let L := R.surgery.transportExterior g hge
  have hlinks (z) : ∃ r, R.surgery.newExterior r = g z ∧ R.surgery.oldExterior r = L z :=
    ⟨R.surgery.exteriorCoordinates g hge z,
      R.surgery.newExterior_exteriorCoordinates g hge z, rfl⟩
  refine ⟨L, R.surgery.transportExterior_isClosedEmbedding g hge hg,
    disjoint_left.mpr ?_, hlinks, ?_⟩
  · rintro _ ⟨z, rfl⟩ ⟨u, hu⟩
    have hpoint : L z = R.surgery.oldPiece u := hu.symm
    obtain ⟨q, hq, -⟩ := (R.surgery.transportExterior_oldPiece_iff g hge z u).mp hpoint
    apply disjoint_left.mp havoid ⟨z, rfl⟩
    rw [← R.newPiece_range, hq]
    exact mem_range_self _
  · exact R.attachmentHomeomorph_lowerExteriorMap L g hlinks

end ShrunkSurgeryRealization

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [CompactSpace A] (d)

open Classical in
theorem exists_shrunk_disjoint_lowerFace
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (g : C(A, d.UpperLevel)) (hinj : Injective g)
    (havoid : Disjoint (range g) (range d.surgery.beltSphere)) :
    ∃ (s : ℝ), 0 < s ∧ s < 1 ∧ ∃ R : d.ShrunkSurgeryRealization s,
      ∃ L : C(A, d.LowerLevel), IsClosedEmbedding L ∧
        Disjoint (range L) (range d.surgery.oldPiece) ∧
        ∀ z, (R.attachmentHomeomorph ⟨(L z).val, Or.inl (L z).property.le⟩).val = (g z).val := by
  obtain ⟨s, hs, hs₁, htube⟩ :=
    d.exists_closedBeltTube_avoiding_compact (isCompact_range g.continuous) havoid
  let v₀ := SphereCoordinates.standardParametrization d.chart.PositiveCoordinates n
    (Hemisphere.point true ⟨0, by simp⟩)
  obtain ⟨R⟩ := d.nonempty_shrunkSurgeryRealization hf n v₀ hs hs₁
  obtain ⟨L, hL, hdisjoint, -, hmap⟩ :=
    R.exists_disjoint_lowerExteriorFace g (g.continuous.isClosedEmbedding hinj) htube
  exact ⟨s, hs, hs₁, R, L, hL, hdisjoint, hmap⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
