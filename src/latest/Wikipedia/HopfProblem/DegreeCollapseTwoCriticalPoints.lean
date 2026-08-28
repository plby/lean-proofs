import Wikipedia.HopfProblem.DegreeCollapseMiddleBlocksExhausted
import Wikipedia.SmoothSixDPoincare.TwoCriticalPointSphere

/-!
# Two actual critical points and topological sphere recognition

The constructed ordered minimal function has no middle indices. Its two
chronological critical points supply the exact input of the checked Reeb
recognition theorem. The conclusion is a homeomorphism of the unchanged
manifold, not yet a diffeomorphism of its original smooth atlas.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem critical_pair_of_surgery_count_two (S : SurgeryWindows E f) (hcount : S.count = 2) :
    ∃ p q : M, f p < f q ∧ criticalPoints E f = {p, q} := by
  let p := S.point ⟨0, by omega⟩
  let q := S.point ⟨1, by omega⟩
  refine ⟨p.val, q.val, S.point_strictMono (by change (0 : ℕ) < 1; omega), ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := S.point.surjective ⟨z, hz⟩
    have hib := i.isLt
    have hcases : i.val = 0 ∨ i.val = 1 := by omega
    rcases hcases with hzero | hone
    · have he : i = ⟨0, by omega⟩ := Fin.ext hzero
      have hv := congrArg (fun x : criticalPoints E f => x.val) hi
      rw [he] at hv
      exact mem_insert_iff.mpr (Or.inl hv.symm)
    · have he : i = ⟨1, by omega⟩ := Fin.ext hone
      have hv := congrArg (fun x : criticalPoints E f => x.val) hi
      rw [he] at hv
      exact mem_insert_iff.mpr (Or.inr (mem_singleton_iff.mpr hv.symm))
  · intro hz
    rcases mem_insert_iff.mp hz with hp | hq
    · exact hp ▸ p.property
    · exact (mem_singleton_iff.mp hq) ▸ q.property

variable (E M) in
theorem exists_two_critical_point_morse_of_homotopySixSphere
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere) :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      ∃ p q : M, f p < f q ∧ criticalPoints E f = {p, q} := by
  let _ := pathConnectedSpace_of_homotopySixSphere e
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal⟩ :=
    exists_minimal_ordered_morse_system_without_outer_indices E M e hdim
  have htwo := minimal_ordered_index_two_count_zero S hf hm hdim e horder hzero hone hminimal
  have hfour := minimal_ordered_index_four_count_zero S hf hm hdim e horder hsix hfive hminimal
  obtain ⟨-, hcount⟩ := ordered_no_middle_indices_count_two S.toSurgeryWindows hf hdim e
    horder hzero hsix hone htwo hfour hfive
  exact ⟨f, hf, hm, critical_pair_of_surgery_count_two S.toSurgeryWindows hcount⟩

variable (E M) in
theorem nonempty_homeomorph_of_homotopySixSphere
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere) : Nonempty (M ≃ₜ SixSphere) := by
  obtain ⟨f, hf, hm, p, q, hpq, hcrit⟩ :=
    exists_two_critical_point_morse_of_homotopySixSphere E M hdim e
  have hh := nonempty_homeomorphSphere_of_two_critical_points hf hm hpq hcrit
  change Nonempty (M ≃ₜ Hemisphere.Sphere (Module.finrank ℝ E)) at hh
  rw [hdim] at hh
  exact hh

theorem six_dimensional_smale_assertion : Wikipedia.SmoothSixDPoincare.Assertion := by
  intro E _ _ _ M _ _ _ _ _ _ hdim e
  exact nonempty_homeomorph_of_homotopySixSphere E M hdim e

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
