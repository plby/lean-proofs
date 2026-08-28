import Wikipedia.SmoothSixDPoincare.PlaneCollisionParameters
import Wikipedia.SmoothSixDPoincare.PlaneImmersionPerturbation

/-!
# Affine perturbations without self-intersections in codimension at least three

In target dimension at least five, the two collision images and the two
singular-derivative images together still have lower dimension than the
parameter space. A single arbitrarily small parameter therefore avoids all
of them. Restrictions to compact sets are genuine closed embeddings.
-/

noncomputable section

open Set
open scoped ContDiff Manifold ENNReal

namespace Wikipedia.SmoothSixDPoincare.PlaneImmersion

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem dimH_collision_parameters_le {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    dimH (firstCollision f '' firstCollisionDomain ∪
      secondCollision f '' secondCollisionDomain) ≤
        (Module.finrank ℝ (Plane × (Plane × F)) : ℝ≥0∞) := by
  have hfirst := GeneralPosition.dimH_image_manifold_le
    (isOpen_firstCollisionDomain (F := F)) (contDiffOn_firstCollision hf).contMDiffOn
  have hsecond := GeneralPosition.dimH_image_manifold_le
    (isOpen_secondCollisionDomain (F := F)) (contDiffOn_secondCollision hf).contMDiffOn
  rw [dimH_union]
  exact max_le hfirst hsecond

/-- Small parameters simultaneously avoid all collisions and all singular differentials. -/
theorem dense_injective_immersive_parameters {f : Plane → F} (hf : ContDiff ℝ ∞ f)
    (hdim : 5 ≤ Module.finrank ℝ F) :
    Dense ((range (badFirst f) ∪ range (badSecond f)) ∪
      (firstCollision f '' firstCollisionDomain ∪
        secondCollision f '' secondCollisionDomain))ᶜ := by
  have hd₁ : Module.finrank ℝ (Plane × (ℝ × F)) < Module.finrank ℝ (F × F) := by
    change Module.finrank ℝ ((ℝ × ℝ) × (ℝ × F)) < Module.finrank ℝ (F × F)
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  have hd₂ : Module.finrank ℝ (Plane × (Plane × F)) < Module.finrank ℝ (F × F) := by
    change Module.finrank ℝ ((ℝ × ℝ) × ((ℝ × ℝ) × F)) < Module.finrank ℝ (F × F)
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  apply dense_compl_of_dimH_lt_finrank
  rw [dimH_union]
  exact max_lt ((dimH_bad_parameters_le hf).trans_lt (Nat.cast_lt.mpr hd₁))
    ((dimH_collision_parameters_le hf).trans_lt (Nat.cast_lt.mpr hd₂))

/-- Every smooth plane map into dimension at least five has an arbitrarily small affine
perturbation that is injective and has injective derivatives everywhere. -/
theorem exists_small_affine_injective_immersion {f : Plane → F} (hf : ContDiff ℝ ∞ f)
    (hdim : 5 ≤ Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : F × F, ‖A‖ < ε ∧ ContDiff ℝ ∞ (perturb f A) ∧
      Function.Injective (perturb f A) ∧
        ∀ x, Function.Injective (fderiv ℝ (perturb f A) x) := by
  obtain ⟨A, hA, hnorm⟩ := (dense_injective_immersive_parameters hf hdim).exists_dist_lt 0 hε
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · simpa only [dist_zero_left] using hnorm
  · exact (contDiff_perturb_family hf).comp (contDiff_const.prodMk contDiff_id)
  · exact injective_perturb_of_not_collision f (fun h => hA (Or.inr h))
  · intro x
    rw [fderiv_perturb hf]
    exact injective_add_linearMap_of_not_bad f (fun h => hA (Or.inl h)) x

/-- The same parameter gives a genuine closed embedding on any prescribed compact source set. -/
theorem exists_small_affine_compact_embedding {f : Plane → F} (hf : ContDiff ℝ ∞ f)
    (hdim : 5 ≤ Module.finrank ℝ F) {K : Set Plane} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : F × F, ‖A‖ < ε ∧ ContDiff ℝ ∞ (perturb f A) ∧
      Topology.IsClosedEmbedding (fun x : K => perturb f A x) ∧
        ∀ x, Function.Injective (fderiv ℝ (perturb f A) x) := by
  obtain ⟨A, hA, hsmooth, hinj, hderiv⟩ := exists_small_affine_injective_immersion hf hdim hε
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact ⟨A, hA, hsmooth,
    (hsmooth.continuous.comp continuous_subtype_val).isClosedEmbedding
      (hinj.comp Subtype.val_injective), hderiv⟩

end Wikipedia.SmoothSixDPoincare.PlaneImmersion
