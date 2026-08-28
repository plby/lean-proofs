import Wikipedia.NoExoticSixSphere.ManifoldParityBall

/-!
# Finite systems of disjoint actual parity balls

The indexing set is the intrinsic singular set of the original family. Every
singularity is the center of its own ball. Finiteness and arbitrarily small
local constructions suffice to choose pairwise disjoint closed balls.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]

structure ParityBallSystem (g : ℝ → Sphere 3 → M) where
  finite_singular : (singularParameters (n := 6) g).Finite
  ball : ∀ q : singularParameters (n := 6) g, ParityBall g q.val
  pairwise_disjoint : Pairwise (fun q w ↦ Disjoint (ball q).closedRegion (ball w).closedRegion)

namespace ParityBallSystem

theorem exists_of_small_balls (g : ℝ → Sphere 3 → M)
    (hfin : (singularParameters (n := 6) g).Finite)
    (hlocal : ∀ q ∈ singularParameters (n := 6) g,
      ∀ N : Set (ℝ × Sphere 3), IsOpen N → q ∈ N →
        ∃ B : ParityBall g q, B.closedRegion ⊆ N) :
    Nonempty (ParityBallSystem g) := by
  obtain ⟨U, hU, hdisj⟩ := hfin.t2_separation
  choose B hB using fun q : singularParameters (n := 6) g ↦
    hlocal q.val q.property (U q.val) (hU q.val).2 (hU q.val).1
  refine ⟨⟨hfin, B, ?_⟩⟩
  intro q w hne
  exact (hdisj q.property w.property (fun he ↦ hne (Subtype.ext he))).mono (hB q) (hB w)

variable {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

def openHoles : Set (ℝ × Sphere 3) := ⋃ q, (P.ball q).openRegion

def closedHoles : Set (ℝ × Sphere 3) := ⋃ q, (P.ball q).closedRegion

def linkingBoundary : Set (ℝ × Sphere 3) := ⋃ q, (P.ball q).boundaryRegion

theorem isOpen_openHoles : IsOpen P.openHoles :=
  isOpen_iUnion (fun q ↦ (P.ball q).isOpen_openRegion)

theorem isCompact_closedHoles : IsCompact P.closedHoles := by
  let := P.finite_singular.to_subtype
  exact isCompact_iUnion (fun q ↦ (P.ball q).isCompact_closedRegion)

theorem openHoles_subset_closedHoles : P.openHoles ⊆ P.closedHoles :=
  iUnion_mono (fun q ↦ (P.ball q).openRegion_subset_closedRegion)

theorem closedHoles_subset_interiorTime :
    P.closedHoles ⊆ Ioo (0 : ℝ) 1 ×ˢ (univ : Set (Sphere 3)) :=
  iUnion_subset (fun q ↦ (P.ball q).closedRegion_subset_interiorTime)

theorem singular_subset_openHoles : singularParameters (n := 6) g ⊆ P.openHoles := by
  intro q hq
  exact mem_iUnion.mpr ⟨⟨q, hq⟩, (P.ball ⟨q, hq⟩).center_mem_openRegion⟩

theorem linkingBoundary_disjoint_singular :
    Disjoint P.linkingBoundary (singularParameters (n := 6) g) := by
  apply disjoint_iUnion_left.mpr
  exact fun q ↦ (P.ball q).boundaryRegion_disjoint_singular

theorem closedHoles_sdiff_openHoles : P.closedHoles \ P.openHoles = P.linkingBoundary := by
  ext x
  constructor
  · rintro ⟨hx, hxnot⟩
    obtain ⟨q, hq⟩ := mem_iUnion.mp hx
    apply mem_iUnion.mpr
    refine ⟨q, ?_⟩
    rw [← (P.ball q).closedRegion_sdiff_openRegion]
    exact ⟨hq, fun ho ↦ hxnot (mem_iUnion.mpr ⟨q, ho⟩)⟩
  · intro hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp hx
    rw [← (P.ball q).closedRegion_sdiff_openRegion] at hq
    refine ⟨mem_iUnion.mpr ⟨q, hq.1⟩, ?_⟩
    intro ho
    obtain ⟨w, hw⟩ := mem_iUnion.mp ho
    by_cases he : q = w
    · subst w
      exact hq.2 hw
    · exact disjoint_left.mp (P.pairwise_disjoint he) hq.1
        ((P.ball w).openRegion_subset_closedRegion hw)

theorem closure_openHoles : closure P.openHoles = P.closedHoles := by
  apply le_antisymm
  · exact closure_minimal P.openHoles_subset_closedHoles P.isCompact_closedHoles.isClosed
  · apply iUnion_subset
    intro q
    rw [← (P.ball q).closure_openRegion]
    exact closure_mono (subset_iUnion (fun w ↦ (P.ball w).openRegion) q)

theorem frontier_openHoles : frontier P.openHoles = P.linkingBoundary := by
  rw [frontier, P.closure_openHoles, P.isOpen_openHoles.interior_eq,
    P.closedHoles_sdiff_openHoles]

end ParityBallSystem
end NoExoticSixSphere.SphereFamily
