import Wikipedia.HopfProblem.CuspComponentProjection

/-!
# The dense one-branch part of the central component

The part of `E₀` meeting no other ray component is open and dense. The actual
component projection is injective there. Density is proved in the affine
coordinate hyperplanes, not assumed as a toric irreducibility theorem.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricCharts

theorem zeroCount_ge_two_iff (z : CoordinateSpace 3) : 2 ≤ zeroCount z ↔
    ∃ j k : Fin 3, j ≠ k ∧ z j = 0 ∧ z k = 0 := by
  have h := Set.one_lt_ncard (Set.toFinite {j : Fin 3 | z j = 0})
  change (1 < zeroCount z ↔ _) at h
  rw [show (2 ≤ zeroCount z) ↔ 1 < zeroCount z by omega, h]
  constructor
  · rintro ⟨j, hj, k, hk, hne⟩
    exact ⟨j, k, hne, hj, hk⟩
  · rintro ⟨j, k, hne, hj, hk⟩
    exact ⟨j, hj, k, hk, hne⟩

theorem zeroCount_update_zero_of_torus {z : CoordinateSpace 3} (hz : z ∈ torus) (j : Fin 3) :
    zeroCount (Function.update z j 0) = 1 := by
  classical
  rw [← vanishingIndices_card]
  have he : vanishingIndices (Function.update z j 0) = {j} := by
    ext k
    rw [mem_vanishingIndices, Finset.mem_singleton]
    by_cases hk : k = j
    · subst k
      simp
    · simp [hk, hz k]
  rw [he]
  exact Finset.card_singleton j

end Wikipedia.HopfProblem.ToricCharts

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

theorem branchCount_ge_two_isClosed : IsClosed {x : Space | 2 ≤ branchCount x} := by
  rw [← isOpen_compl_iff, gluing.isOpen_iff]
  change ∀ s : Triangle, IsOpen (inclusion s ⁻¹' {x : Space | 2 ≤ branchCount x}ᶜ)
  intro s
  rw [Set.preimage_compl, isOpen_compl_iff]
  have he : inclusion s ⁻¹' {x : Space | 2 ≤ branchCount x} =
      ⋃ j : Fin 3, ⋃ k : Fin 3, {z | j ≠ k ∧ z j = 0 ∧ z k = 0} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, branchCount_inclusion,
      zeroCount_ge_two_iff, Set.mem_iUnion]
  rw [he]
  apply isClosed_iUnion_of_finite
  intro j
  apply isClosed_iUnion_of_finite
  intro k
  exact isClosed_const.inter
    ((isClosed_eq (continuous_apply j) continuous_const).inter
      (isClosed_eq (continuous_apply k) continuous_const))

def componentInterior : Set (rayDivisor 0) := {x | branchCount (x : Space) = 1}

theorem componentInterior_isOpen : IsOpen componentInterior := by
  have he : componentInterior =
      (Subtype.val : rayDivisor 0 → Space) ⁻¹' {x : Space | 2 ≤ branchCount x}ᶜ := by
    ext x
    have hp : 0 < branchCount (x : Space) :=
      (branchCount_pos_iff (x : Space)).mpr (time_eq_zero_of_mem_rayDivisor x.2)
    change branchCount (x : Space) = 1 ↔ ¬2 ≤ branchCount (x : Space)
    omega
  rw [he]
  exact branchCount_ge_two_isClosed.isOpen_compl.preimage continuous_subtype_val

theorem componentInterior_dense : Dense componentInterior := by
  intro x
  obtain ⟨s, z, hz⟩ := inclusion_jointly_surjective (x : Space)
  have hx : inclusion s z ∈ rayDivisor 0 := by rw [hz]; exact x.2
  obtain ⟨j, hj, hv⟩ := (mem_rayDivisor_inclusion 0 s z).mp hx
  let f : CoordinateSpace 3 → rayDivisor 0 := fun w =>
    ⟨inclusion s (Function.update w j 0), by
      rw [← hv, mem_rayDivisor_vertex]
      simp⟩
  have hf : Continuous f :=
    ((inclusion_openEmbedding s).continuous.comp
      (continuous_id.update j continuous_const)).subtype_mk _
  have hfz : f z = x := by
    apply Subtype.ext
    change inclusion s (Function.update z j 0) = (x : Space)
    rw [(Function.update_eq_self_iff).mpr hj.symm]
    exact hz
  have hsub : f '' torus ⊆ componentInterior := by
    rintro _ ⟨w, hw, rfl⟩
    change branchCount (inclusion s (Function.update w j 0)) = 1
    rw [branchCount_inclusion]
    exact zeroCount_update_zero_of_torus hw j
  rw [← hfz]
  exact closure_mono hsub (mem_closure_image hf.continuousAt (torus_dense z))

end Wikipedia.HopfProblem.ToricSpace

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

include hε1 hC hR in
theorem componentProjection_injective_on_interior :
    Set.InjOn (componentProjection C ε hε) componentInterior := by
  intro x hx y _ he
  have hc : (componentProjection C ε hε ⁻¹' {componentProjection C ε hε x}).ncard ≤ 1 := by
    rw [componentProjection_fibre_card C ε hε hε1 hC hR]
    change ToricSpace.branchCount (x : Space) ≤ 1
    exact le_of_eq hx
  have hs := (Set.ncard_le_one (componentProjection_fibre_finite C ε hε hε1 hC hR
    (componentProjection C ε hε x))).mp hc
  exact hs x rfl y he.symm

end Wikipedia.HopfProblem.CuspQuotient
