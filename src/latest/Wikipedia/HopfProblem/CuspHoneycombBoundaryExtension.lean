import Wikipedia.HopfProblem.CuspHoneycombRadialExtension
import Mathlib.Analysis.Convex.GaugeRescale

/-!
# Extending a convex body's boundary homeomorphism

The gauge-rescaling theorem takes the closed convex body and its boundary
to the unit closed ball and unit sphere.  Conjugating the explicitly
constructed radial extension then gives a homeomorphism of the original
ambient space, preserving the original body and extending its prescribed
boundary map exactly.
-/

noncomputable section

open Set Metric Topology Bornology

namespace Wikipedia.HopfProblem.CuspHoneycombRadial

variable {E : Type*} [NormedAddCommGroup E]

private theorem homeomorph_mem_image_iff (H : E ≃ₜ E) {S T : Set E}
    (hST : H '' S = T) (x : E) : x ∈ S ↔ H x ∈ T := by
  rw [← hST]
  exact H.injective.mem_set_image.symm

private theorem homeomorph_image_eq_of_mem_iff (F : E ≃ₜ E) {K : Set E}
    (hmem : ∀ x, F x ∈ K ↔ x ∈ K) : F '' K = K := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro y hy
    refine ⟨F.symm y, ?_, F.apply_symm_apply y⟩
    apply (hmem (F.symm y)).mp
    rwa [F.apply_symm_apply]

variable [NormedSpace ℝ E]

/-- Every boundary homeomorphism of a bounded closed convex body with
nonempty interior extends to a homeomorphism of the actual ambient space. -/
theorem exists_homeomorph_extending_frontier {K : Set E}
    (hconv : Convex ℝ K) (hclosed : IsClosed K) (hbounded : IsBounded K)
    (hne : (interior K).Nonempty) (e : frontier K ≃ₜ frontier K) :
    ∃ F : E ≃ₜ E, F '' K = K ∧ ∀ x : frontier K, F (x : E) = (e x : E) := by
  obtain ⟨H, _hinterior, hclosure, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hbounded
  have hK : H '' K = closedBall (0 : E) 1 := by
    simpa only [hclosed.closure_eq] using hclosure
  let HB : frontier K ≃ₜ UnitSphere E :=
    H.subtype (homeomorph_mem_image_iff H hfrontier)
  let eS : UnitSphere E ≃ₜ UnitSphere E := HB.symm.trans (e.trans HB)
  let F : E ≃ₜ E := H.trans ((radialHomeomorph eS).trans H.symm)
  have hmemF (x : E) : F x ∈ K ↔ x ∈ K := by
    rw [homeomorph_mem_image_iff H hK (F x), homeomorph_mem_image_iff H hK x]
    change H (H.symm (radialHomeomorph eS (H x))) ∈ closedBall (0 : E) 1 ↔
      H x ∈ closedBall (0 : E) 1
    rw [H.apply_symm_apply]
    simp only [mem_closedBall, dist_zero_right, radialHomeomorph_norm]
  refine ⟨F, homeomorph_image_eq_of_mem_iff F hmemF, ?_⟩
  intro x
  change H.symm (radialHomeomorph eS (HB x : E)) = (e x : E)
  rw [radialHomeomorph_sphere]
  change H.symm (HB (e (HB.symm (HB x))) : E) = (e x : E)
  rw [HB.symm_apply_apply]
  exact H.symm_apply_apply (e x : E)

variable {K : Set E}
variable (hconv : Convex ℝ K) (hclosed : IsClosed K) (hbounded : IsBounded K)
variable (hne : (interior K).Nonempty) (e : frontier K ≃ₜ frontier K)

/-- The ambient extension chosen from the explicit radial construction. -/
def boundaryExtension : E ≃ₜ E :=
  (exists_homeomorph_extending_frontier hconv hclosed hbounded hne e).choose

theorem boundaryExtension_image : boundaryExtension hconv hclosed hbounded hne e '' K = K :=
  (exists_homeomorph_extending_frontier hconv hclosed hbounded hne e).choose_spec.1

theorem boundaryExtension_frontier (x : frontier K) :
    boundaryExtension hconv hclosed hbounded hne e (x : E) = (e x : E) :=
  (exists_homeomorph_extending_frontier hconv hclosed hbounded hne e).choose_spec.2 x

/-- The restriction to the original convex body, with its inherited topology. -/
def boundarySetExtension : K ≃ₜ K :=
  (boundaryExtension hconv hclosed hbounded hne e).subtype
    (homeomorph_mem_image_iff _ (boundaryExtension_image hconv hclosed hbounded hne e))

@[simp] theorem boundarySetExtension_coe (x : K) :
    (boundarySetExtension hconv hclosed hbounded hne e x : E) =
      boundaryExtension hconv hclosed hbounded hne e (x : E) := rfl

theorem boundarySetExtension_frontier (x : frontier K) :
    (boundarySetExtension hconv hclosed hbounded hne e
      ⟨(x : E), hclosed.frontier_subset x.2⟩ : E) = (e x : E) :=
  boundaryExtension_frontier hconv hclosed hbounded hne e x

end Wikipedia.HopfProblem.CuspHoneycombRadial
