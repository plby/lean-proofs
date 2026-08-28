import Wikipedia.NoExoticSixSphere.SphereExteriorCapImage

/-!
# The removed source disks contain no old double points except the chosen crossing

The globally clean chart proves uniqueness of each input map's fibers on
its removed disk. A mutual coincidence touching either removed disk must
be exactly the pair of reference centers. These statements use the entire
original sphere maps, not restrictions to local patches.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) {ε : ℝ} (hε : 0 < ε)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hclean : ∀ z ∈ Φ.source,
    (∀ x, F x = Φ z ↔ z.2 = 0 ∧ x = sourceChart z.1) ∧
    (∀ x, G x = Φ z ↔ z.1 = 0 ∧ x = sourceChart z.2))

include hε hprod hclean

theorem removedDisk_unique_left {x : Sphere 3} (hx : x ∈ removedSourceDisk ε)
    (y : Sphere 3) (he : F x = F y) : x = y := by
  rcases hx with ⟨v, hv, rfl⟩
  have hs : (v, 0) ∈ Φ.source := hprod
    ⟨ball_subset_closedBall hv, mem_closedBall_self (by positivity)⟩
  have hvF : F (sourceChart v) = Φ (v, 0) :=
    ((hclean _ hs).1 _).mpr ⟨rfl, rfl⟩
  exact (((hclean _ hs).1 y).mp (he.symm.trans hvF)).2.symm

theorem removedDisk_unique_right {x : Sphere 3} (hx : x ∈ removedSourceDisk ε)
    (y : Sphere 3) (he : G x = G y) : x = y := by
  rcases hx with ⟨v, hv, rfl⟩
  have hs : (0, v) ∈ Φ.source := hprod
    ⟨mem_closedBall_self (by positivity), ball_subset_closedBall hv⟩
  have hvG : G (sourceChart v) = Φ (0, v) :=
    ((hclean _ hs).2 _).mpr ⟨rfl, rfl⟩
  exact (((hclean _ hs).2 y).mp (he.symm.trans hvG)).2.symm

theorem removedDisk_mutual_left {x y : Sphere 3} (hx : x ∈ removedSourceDisk ε)
    (he : F x = G y) : x = sourceChart 0 ∧ y = sourceChart 0 := by
  rcases hx with ⟨v, hv, rfl⟩
  have hs : (v, 0) ∈ Φ.source := hprod
    ⟨ball_subset_closedBall hv, mem_closedBall_self (by positivity)⟩
  have hvF : F (sourceChart v) = Φ (v, 0) :=
    ((hclean _ hs).1 _).mpr ⟨rfl, rfl⟩
  obtain ⟨hv0, hy⟩ := ((hclean _ hs).2 y).mp (he.symm.trans hvF)
  exact ⟨congrArg sourceChart hv0, hy⟩

theorem removedDisk_mutual_right {x y : Sphere 3} (hy : y ∈ removedSourceDisk ε)
    (he : F x = G y) : x = sourceChart 0 ∧ y = sourceChart 0 := by
  rcases hy with ⟨v, hv, rfl⟩
  have hs : (0, v) ∈ Φ.source := hprod
    ⟨mem_closedBall_self (by positivity), ball_subset_closedBall hv⟩
  have hvG : G (sourceChart v) = Φ (0, v) :=
    ((hclean _ hs).2 _).mpr ⟨rfl, rfl⟩
  obtain ⟨hv0, hx⟩ := ((hclean _ hs).1 x).mp (he.trans hvG)
  exact ⟨hx, congrArg sourceChart hv0⟩

theorem doublePoints_left_outside_removed {x y : Sphere 3} (hne : x ≠ y) (he : F x = F y) :
    x ∉ removedSourceDisk ε ∧ y ∉ removedSourceDisk ε := by
  exact ⟨fun hx ↦ hne (removedDisk_unique_left Φ F G hε hprod hclean hx y he),
    fun hy ↦ hne (removedDisk_unique_left Φ F G hε hprod hclean hy x he.symm).symm⟩

theorem doublePoints_right_outside_removed {x y : Sphere 3} (hne : x ≠ y) (he : G x = G y) :
    x ∉ removedSourceDisk ε ∧ y ∉ removedSourceDisk ε := by
  exact ⟨fun hx ↦ hne (removedDisk_unique_right Φ F G hε hprod hclean hx y he),
    fun hy ↦ hne (removedDisk_unique_right Φ F G hε hprod hclean hy x he.symm).symm⟩

theorem mutualPairs_outside_removed {x y : Sphere 3} (he : F x = G y)
    (hne : ¬ (x = sourceChart 0 ∧ y = sourceChart 0)) :
    x ∉ removedSourceDisk ε ∧ y ∉ removedSourceDisk ε := by
  exact ⟨fun hx ↦ hne (removedDisk_mutual_left Φ F G hε hprod hclean hx he),
    fun hy ↦ hne (removedDisk_mutual_right Φ F G hε hprod hclean hy he)⟩

end NoExoticSixSphere.SphereSumNeck
