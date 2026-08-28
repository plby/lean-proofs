import Wikipedia.NoExoticSixSphere.ManifoldParityBallRadial
import Wikipedia.NoExoticSixSphere.ManifoldParityBallSystem

/-!
# Simultaneously pushing away from all actual singular balls

Each chartwise push preserves the complement of every other open ball because
the closed balls are disjoint. Finite composition therefore removes all open
holes, fixes their common complement, and preserves the closed time cylinder.
The input space excludes exactly the actual intrinsic singularities.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]

abbrev RegularParameters (g : ℝ → Sphere 3 → M) :=
  {y : ℝ × Sphere 3 // y ∉ singularParameters (n := 6) g}

namespace ParityBallSystem

variable {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

def pushRegular (q : singularParameters (n := 6) g) :
    C(RegularParameters g, RegularParameters g) where
  toFun y := ⟨(P.ball q).push y.val, by
    have hne : y.val ≠ q.val := fun he ↦ y.property (he.symm ▸ q.property)
    by_cases hy : y.val ∈ (P.ball q).closedRegion
    · exact disjoint_left.mp (P.ball q).boundaryRegion_disjoint_singular
        ((P.ball q).push_mem_boundary_of_mem hy hne)
    · change (P.ball q).push y.val ∉ singularParameters (n := 6) g
      rw [ParityBall.push, if_neg hy]
      exact y.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hsub : (singularParameters (n := 6) g)ᶜ ⊆ ({q.val} : Set (ℝ × Sphere 3))ᶜ :=
      fun y hy he ↦ hy (he.symm ▸ q.property)
    exact ((P.ball q).continuousOn_push.mono hsub).domRestrict

theorem pushRegular_apply (q : singularParameters (n := 6) g) (y : RegularParameters g) :
    (P.pushRegular q y).val = (P.ball q).push y.val := rfl

theorem pushRegular_fixed (q : singularParameters (n := 6) g) (y : RegularParameters g)
    (hy : y.val ∉ (P.ball q).openRegion) : P.pushRegular q y = y :=
  Subtype.ext ((P.ball q).push_eq_of_notMem_openRegion hy)

theorem pushRegular_avoids_self (q : singularParameters (n := 6) g)
    (y : RegularParameters g) : (P.pushRegular q y).val ∉ (P.ball q).openRegion :=
  (P.ball q).push_notMem_openRegion (fun he ↦ y.property (he.symm ▸ q.property))

theorem pushRegular_preserves_avoidance (q w : singularParameters (n := 6) g)
    (y : RegularParameters g) (hy : y.val ∉ (P.ball w).openRegion) :
    (P.pushRegular q y).val ∉ (P.ball w).openRegion := by
  by_cases he : q = w
  · subst w
    exact P.pushRegular_avoids_self q y
  · by_cases hc : y.val ∈ (P.ball q).closedRegion
    · have hb := (P.ball q).push_mem_boundary_of_mem hc
        (fun he ↦ y.property (he.symm ▸ q.property))
      intro hw
      exact disjoint_left.mp (P.pairwise_disjoint he)
        ((P.ball q).boundaryRegion_subset_closedRegion hb)
        ((P.ball w).openRegion_subset_closedRegion hw)
    · change (P.ball q).push y.val ∉ (P.ball w).openRegion
      rw [ParityBall.push, if_neg hc]
      exact hy

theorem pushRegular_preserves_time (q : singularParameters (n := 6) g)
    (y : RegularParameters g) (hy : y.val.1 ∈ Icc (0 : ℝ) 1) :
    (P.pushRegular q y).val.1 ∈ Icc (0 : ℝ) 1 := by
  by_cases hc : y.val ∈ (P.ball q).closedRegion
  · have hb := (P.ball q).push_mem_boundary_of_mem hc
      (fun he ↦ y.property (he.symm ▸ q.property))
    have ht := ((P.ball q).closedRegion_subset_interiorTime
      ((P.ball q).boundaryRegion_subset_closedRegion hb)).1
    exact ⟨ht.1.le, ht.2.le⟩
  · change ((P.ball q).push y.val).1 ∈ Icc (0 : ℝ) 1
    rw [ParityBall.push, if_neg hc]
    exact hy

theorem exists_finite_push (s : Finset (singularParameters (n := 6) g)) :
    ∃ R : C(RegularParameters g, RegularParameters g),
      (∀ y, y.val ∉ P.openHoles → R y = y) ∧
      (∀ q ∈ s, ∀ y, (R y).val ∉ (P.ball q).openRegion) ∧
      (∀ y, y.val.1 ∈ Icc (0 : ℝ) 1 → (R y).val.1 ∈ Icc (0 : ℝ) 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨ContinuousMap.id _, fun _ _ ↦ rfl, by simp, fun _ hy ↦ hy⟩
  | @insert q s hq ih =>
    obtain ⟨R, hfix, havoid, htime⟩ := ih
    refine ⟨(P.pushRegular q).comp R, ?_, ?_, ?_⟩
    · intro y hy
      change P.pushRegular q (R y) = y
      rw [hfix y hy]
      apply P.pushRegular_fixed
      exact fun ho ↦ hy (mem_iUnion.mpr ⟨q, ho⟩)
    · intro w hw y
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact P.pushRegular_avoids_self w (R y)
      · exact P.pushRegular_preserves_avoidance q w (R y) (havoid w hw y)
    · intro y hy
      exact P.pushRegular_preserves_time q (R y) (htime y hy)

theorem exists_push_all : ∃ R : C(RegularParameters g, RegularParameters g),
    (∀ y, y.val ∉ P.openHoles → R y = y) ∧
    (∀ y, (R y).val ∉ P.openHoles) ∧
    (∀ y, y.val.1 ∈ Icc (0 : ℝ) 1 → (R y).val.1 ∈ Icc (0 : ℝ) 1) := by
  let := P.finite_singular.to_subtype
  let := Fintype.ofFinite (singularParameters (n := 6) g)
  obtain ⟨R, hfix, havoid, htime⟩ := P.exists_finite_push Finset.univ
  refine ⟨R, hfix, ?_, htime⟩
  intro y hy
  obtain ⟨q, hq⟩ := mem_iUnion.mp hy
  exact havoid q (Finset.mem_univ q) y hq

end ParityBallSystem
end NoExoticSixSphere.SphereFamily
