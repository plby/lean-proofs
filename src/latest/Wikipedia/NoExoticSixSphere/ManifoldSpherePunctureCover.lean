import Wikipedia.NoExoticSixSphere.SphereCylinderPunctures
import Wikipedia.NoExoticSixSphere.SphereCylinderCaps
import Wikipedia.NoExoticSixSphere.ManifoldPuncturedRetraction

/-!
# The actual four-sphere finite-puncture cover for the manifold family

The punctures are the two genuine poles and the images of the actual intrinsic
singularities. The open cover consists of their complement and the disjoint
union of the two endpoint caps and actual ball interiors. Each one-point
comparison cover retains this same union of neighborhoods.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]

def spherePunctures (g : ℝ → Sphere 3 → M) : Set (Sphere 4) :=
  SphereCylinder.punctures 3 (singularParameters (n := 6) g)

def sphereRegularSet (g : ℝ → Sphere 3 → M) : Set (Sphere 4) := (spherePunctures g)ᶜ

def sphereRegularHomeomorph (g : ℝ → Sphere 3 → M) :
    sphereRegularSet g ≃ₜ RegularParameters g :=
  SphereCylinder.puncturedHomeomorph 3 (singularParameters (n := 6) g)

def spherePuncture (g : ℝ → Sphere 3 → M) : ParityBallSystem.BoundaryIndex g → Sphere 4
  | .inl b => SphereCylinder.endPole 3 b
  | .inr q => SphereCylinder.point 3 q.val

theorem range_spherePuncture (g : ℝ → Sphere 3 → M) :
    range (spherePuncture g) = spherePunctures g := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with b | q
    · cases b
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨q.val, q.property, rfl⟩
  · rintro (hpole | himage)
    · rcases hpole with rfl | rfl
      · exact ⟨.inl false, rfl⟩
      · exact ⟨.inl true, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := himage
      exact ⟨.inr ⟨q, hq⟩, rfl⟩

def singlePunctureRegularSet (g : ℝ → Sphere 3 → M)
    (i : ParityBallSystem.BoundaryIndex g) : Set (Sphere 4) := {spherePuncture g i}ᶜ

theorem isOpen_singlePunctureRegularSet (g : ℝ → Sphere 3 → M)
    (i : ParityBallSystem.BoundaryIndex g) : IsOpen (singlePunctureRegularSet g i) :=
  isClosed_singleton.isOpen_compl

theorem sphereRegular_subset_single (g : ℝ → Sphere 3 → M)
    (i : ParityBallSystem.BoundaryIndex g) : sphereRegularSet g ⊆ singlePunctureRegularSet g i := by
  intro y hy he
  apply hy
  rw [← range_spherePuncture]
  exact ⟨i, he.symm⟩

namespace ParityBallSystem

variable {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

include P in
theorem finite_spherePunctures : (spherePunctures g).Finite :=
  SphereCylinder.finite_punctures 3 P.finite_singular

include P in
theorem isOpen_sphereRegularSet : IsOpen (sphereRegularSet g) :=
  P.finite_spherePunctures.isClosed.isOpen_compl

def coverPiece : BoundaryIndex g → Set (Sphere 4)
  | .inl b => SphereCylinder.capRegion 3 b
  | .inr q => SphereCylinder.point 3 '' (P.ball q).openRegion

def coverRegion : Set (Sphere 4) := ⋃ i, P.coverPiece i

theorem isOpen_coverPiece (i : BoundaryIndex g) : IsOpen (P.coverPiece i) := by
  rcases i with b | q
  · exact SphereCylinder.isOpen_capRegion 3 b
  · exact (SphereCylinder.isOpenEmbedding_point 3).isOpenMap _ (P.ball q).isOpen_openRegion

theorem isOpen_coverRegion : IsOpen P.coverRegion := isOpen_iUnion P.isOpen_coverPiece

theorem image_ball_subset_middle (q : singularParameters (n := 6) g) :
    SphereCylinder.point 3 '' (P.ball q).openRegion ⊆
      SphereCylinder.point 3 '' (Icc (0 : ℝ) 1 ×ˢ (univ : Set (Sphere 3))) := by
  apply image_mono
  intro y hy
  have ht := (P.ball q).closedRegion_subset_interiorTime
    ((P.ball q).openRegion_subset_closedRegion hy)
  exact ⟨⟨ht.1.1.le, ht.1.2.le⟩, ht.2⟩

theorem pairwise_disjoint_coverPiece : Pairwise (Disjoint on P.coverPiece) := by
  intro i j hne
  rcases i with a | q <;> rcases j with b | w
  · exact SphereCylinder.pairwise_disjoint_capRegion 3
      (fun he ↦ hne (congrArg Sum.inl he))
  · exact (SphereCylinder.capRegion_disjoint_middle 3 a).mono_right
      (P.image_ball_subset_middle w)
  · exact ((SphereCylinder.capRegion_disjoint_middle 3 b).mono_right
      (P.image_ball_subset_middle q)).symm
  · apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, he⟩
    have hzx := SphereCylinder.injective_point 3 he
    exact disjoint_left.mp (P.pairwise_disjoint (fun he ↦ hne (congrArg Sum.inr he)))
      ((P.ball q).openRegion_subset_closedRegion hx)
      ((P.ball w).openRegion_subset_closedRegion (hzx ▸ hz))

theorem spherePuncture_mem_coverPiece (i : BoundaryIndex g) :
    spherePuncture g i ∈ P.coverPiece i := by
  rcases i with b | q
  · exact SphereCylinder.endPole_mem_capRegion 3 b
  · exact ⟨q.val, (P.ball q).center_mem_openRegion, rfl⟩

theorem spherePunctures_subset_coverRegion : spherePunctures g ⊆ P.coverRegion := by
  rw [← range_spherePuncture]
  rintro y ⟨i, rfl⟩
  exact mem_iUnion.mpr ⟨i, P.spherePuncture_mem_coverPiece i⟩

theorem sphere_regular_cover : sphereRegularSet g ∪ P.coverRegion = univ := by
  apply eq_univ_of_forall
  intro y
  by_cases hy : y ∈ spherePunctures g
  · exact Or.inr (P.spherePunctures_subset_coverRegion hy)
  · exact Or.inl hy

theorem single_puncture_cover (i : BoundaryIndex g) :
    singlePunctureRegularSet g i ∪ P.coverRegion = univ := by
  apply eq_univ_of_forall
  intro y
  by_cases hy : y = spherePuncture g i
  · subst y
    exact Or.inr (mem_iUnion.mpr ⟨i, P.spherePuncture_mem_coverPiece i⟩)
  · exact Or.inl hy

end ParityBallSystem
end NoExoticSixSphere.SphereFamily
