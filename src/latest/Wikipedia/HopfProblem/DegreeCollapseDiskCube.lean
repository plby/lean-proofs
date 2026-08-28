import Wikipedia.HopfProblem.DegreeCollapseDiskHomotopyExtension
import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopyHomeomorph

/-!
# A boundary-preserving homeomorphism of a native disk and cube

Convex gauge rescaling is applied to the actual norm ball and the inverse
image of the coordinate cube. The dimension comparison is a genuine real
linear equivalence, and both boundaries retain their original predicates.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskCube

open DiskCylinder HigherHurewicz

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ))

def target : Set V := L ⁻¹' realCubeSet n

omit [FiniteDimensional ℝ V] in
theorem target_compact : IsCompact (target L) :=
  L.toHomeomorph.isCompact_preimage.mpr (isCompact_realCubeSet n)

omit [FiniteDimensional ℝ V] in
theorem target_convex : Convex ℝ (target L) :=
  (convex_realCubeSet n).linear_preimage L.toLinearMap

omit [FiniteDimensional ℝ V] in
theorem target_interior_nonempty : (interior (target L)).Nonempty := by
  obtain ⟨v, hv⟩ := interior_realCubeSet_nonempty n
  refine ⟨L.symm v, ?_⟩
  change L.symm v ∈ interior (L.toHomeomorph ⁻¹' realCubeSet n)
  rw [← L.toHomeomorph.preimage_interior]
  change L (L.symm v) ∈ interior (realCubeSet n)
  rwa [L.apply_symm_apply]

theorem exists_ambient : ∃ e : V ≃ₜ V,
    e '' closedBall (0 : V) 1 = target L ∧
    e '' frontier (closedBall (0 : V) 1) = frontier (target L) := by
  obtain ⟨e, _, he, hb⟩ := exists_homeomorph_image_eq
    (convex_closedBall (0 : V) 1)
    (show (interior (closedBall (0 : V) 1)).Nonempty from
      ⟨0, ball_subset_interior_closedBall (by simp)⟩)
    ((isCompact_closedBall (0 : V) 1).isVonNBounded ℝ)
    (target_convex L) (target_interior_nonempty L) ((target_compact L).isVonNBounded ℝ)
  exact ⟨e, by simpa only [isClosed_closedBall.closure_eq,
    (target_compact L).isClosed.closure_eq] using he, hb⟩

def ambient : V ≃ₜ V := Classical.choose (exists_ambient L)

theorem ambient_image : ambient L '' closedBall (0 : V) 1 = target L :=
  (Classical.choose_spec (exists_ambient L)).1

theorem ambient_frontier :
    ambient L '' frontier (closedBall (0 : V) 1) = frontier (target L) :=
  (Classical.choose_spec (exists_ambient L)).2

theorem ambient_mem_iff (v : V) :
    v ∈ closedBall (0 : V) 1 ↔ L (ambient L v) ∈ realCubeSet n := by
  change v ∈ closedBall (0 : V) 1 ↔ ambient L v ∈ target L
  rw [← ambient_image]
  exact ((ambient L).injective.mem_set_image).symm

def homeomorph : Disk (E := V) ≃ₜ (Fin n → I) :=
  (((ambient L).trans L.toHomeomorph).subtype (ambient_mem_iff L)).trans (realCubeHomeomorph n)

theorem boundary_iff (z : Disk (E := V)) :
    homeomorph L z ∈ Cube.boundary (Fin n) ↔ ‖(z : V)‖ = 1 := by
  change realCubeHomeomorph n _ ∈ Cube.boundary (Fin n) ↔ _
  rw [realCubeHomeomorph_mem_boundary_iff]
  change L (ambient L z.val) ∈ frontier (realCubeSet n) ↔ _
  have hpre : L (ambient L z.val) ∈ frontier (realCubeSet n) ↔
      ambient L z.val ∈ frontier (target L) := by
    change ambient L z.val ∈ L.toHomeomorph ⁻¹' frontier (realCubeSet n) ↔ _
    rw [L.toHomeomorph.preimage_frontier]
    rfl
  rw [hpre, ← ambient_frontier]
  rw [(ambient L).injective.mem_set_image]
  rw [frontier_closedBall (0 : V) (one_ne_zero), mem_sphere_zero_iff_norm]

theorem symm_boundary_iff (z : Fin n → I) :
    ‖((homeomorph L).symm z : V)‖ = 1 ↔ z ∈ Cube.boundary (Fin n) := by
  rw [← boundary_iff, Homeomorph.apply_symm_apply]

end Wikipedia.HopfProblem.DegreeCollapse.DiskCube
