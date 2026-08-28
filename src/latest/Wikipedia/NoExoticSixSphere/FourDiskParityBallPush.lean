import Wikipedia.NoExoticSixSphere.FourDiskParityBallRadial
import Wikipedia.NoExoticSixSphere.FourDiskPuncturedDomain

/-!
# Simultaneous pushing away from the original four-disk singularity balls

The domain excludes exactly the native singular set on the closed disk.
No assertion about derivative injectivity outside that disk is needed.
Finite composition of the original chart pushes removes every open hole,
fixes their common complement, and preserves the original closed disk.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk

open GLOrthonormalization DiskDoublePoints

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

abbrev SingularComplement (g : Vector 4 → M) := {y : Vector 4 // y ∉ singularSet g}

namespace ParityBallSystem

variable {g : Vector 4 → M} (P : ParityBallSystem g)

include P in
theorem singular_subset_interior : singularSet g ⊆ Metric.ball 0 1 :=
  P.singular_subset_openHoles.trans
    (P.openHoles_subset_closedHoles.trans P.closedHoles_subset_interior)

def pushComplement (x : singularSet g) : C(SingularComplement g, SingularComplement g) where
  toFun y := ⟨(P.ball x).push y.val, by
    have hne : y.val ≠ x.val := fun he ↦ y.property (he.symm ▸ x.property)
    by_cases hy : y.val ∈ (P.ball x).closedRegion
    · intro hs
      exact disjoint_left.mp (P.ball x).boundaryRegion_disjoint_singular
        ((P.ball x).push_mem_boundary_of_mem hy hne) hs.2
    · change (P.ball x).push y.val ∉ singularSet g
      rw [ParityBall.push, if_neg hy]
      exact y.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hsub : (singularSet g)ᶜ ⊆ ({x.val} : Set (Vector 4))ᶜ :=
      fun y hy he ↦ hy (he.symm ▸ x.property)
    exact ((P.ball x).continuousOn_push.mono hsub).domRestrict

theorem pushComplement_apply (x : singularSet g) (y : SingularComplement g) :
    (P.pushComplement x y).val = (P.ball x).push y.val := rfl

theorem pushComplement_fixed (x : singularSet g) (y : SingularComplement g)
    (hy : y.val ∉ (P.ball x).openRegion) : P.pushComplement x y = y :=
  Subtype.ext ((P.ball x).push_eq_of_notMem_openRegion hy)

theorem pushComplement_avoids_self (x : singularSet g) (y : SingularComplement g) :
    (P.pushComplement x y).val ∉ (P.ball x).openRegion :=
  (P.ball x).push_notMem_openRegion (fun he ↦ y.property (he.symm ▸ x.property))

theorem pushComplement_preserves_avoidance (x z : singularSet g)
    (y : SingularComplement g) (hy : y.val ∉ (P.ball z).openRegion) :
    (P.pushComplement x y).val ∉ (P.ball z).openRegion := by
  by_cases he : x = z
  · subst z
    exact P.pushComplement_avoids_self x y
  · by_cases hc : y.val ∈ (P.ball x).closedRegion
    · have hb := (P.ball x).push_mem_boundary_of_mem hc
        (fun he ↦ y.property (he.symm ▸ x.property))
      intro hz
      exact disjoint_left.mp (P.pairwise_disjoint he)
        ((P.ball x).boundaryRegion_subset_closedRegion hb)
        ((P.ball z).openRegion_subset_closedRegion hz)
    · change (P.ball x).push y.val ∉ (P.ball z).openRegion
      rw [ParityBall.push, if_neg hc]
      exact hy

theorem pushComplement_preserves_disk (x : singularSet g) (y : SingularComplement g)
    (hy : y.val ∈ closedBall 0 1) : (P.pushComplement x y).val ∈ closedBall 0 1 := by
  by_cases hc : y.val ∈ (P.ball x).closedRegion
  · have hb := (P.ball x).push_mem_boundary_of_mem hc
      (fun he ↦ y.property (he.symm ▸ x.property))
    exact ball_subset_closedBall ((P.ball x).closedRegion_subset_interior
      ((P.ball x).boundaryRegion_subset_closedRegion hb))
  · change (P.ball x).push y.val ∈ closedBall 0 1
    rw [ParityBall.push, if_neg hc]
    exact hy

theorem exists_finite_push (s : Finset (singularSet g)) :
    ∃ R : C(SingularComplement g, SingularComplement g),
      (∀ y, y.val ∉ P.openHoles → R y = y) ∧
      (∀ x ∈ s, ∀ y, (R y).val ∉ (P.ball x).openRegion) ∧
      (∀ y, y.val ∈ closedBall 0 1 → (R y).val ∈ closedBall 0 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨ContinuousMap.id _, fun _ _ ↦ rfl, by simp, fun _ hy ↦ hy⟩
  | @insert x s hx ih =>
    obtain ⟨R, hfix, havoid, hdisk⟩ := ih
    refine ⟨(P.pushComplement x).comp R, ?_, ?_, ?_⟩
    · intro y hy
      change P.pushComplement x (R y) = y
      rw [hfix y hy]
      apply P.pushComplement_fixed
      exact fun ho ↦ hy (mem_iUnion.mpr ⟨x, ho⟩)
    · intro z hz y
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact P.pushComplement_avoids_self z (R y)
      · exact P.pushComplement_preserves_avoidance x z (R y) (havoid z hz y)
    · intro y hy
      exact P.pushComplement_preserves_disk x (R y) (hdisk y hy)

theorem exists_push_all : ∃ R : C(SingularComplement g, SingularComplement g),
    (∀ y, y.val ∉ P.openHoles → R y = y) ∧
    (∀ y, (R y).val ∉ P.openHoles) ∧
    (∀ y, y.val ∈ closedBall 0 1 → (R y).val ∈ closedBall 0 1) := by
  let := P.finite_singular.to_subtype
  let := Fintype.ofFinite (singularSet g)
  obtain ⟨R, hfix, havoid, hdisk⟩ := P.exists_finite_push Finset.univ
  refine ⟨R, hfix, ?_, hdisk⟩
  intro y hy
  obtain ⟨x, hx⟩ := mem_iUnion.mp hy
  exact havoid x (Finset.mem_univ x) y hx

end ParityBallSystem
end NoExoticSixSphere.GenericFourDisk
