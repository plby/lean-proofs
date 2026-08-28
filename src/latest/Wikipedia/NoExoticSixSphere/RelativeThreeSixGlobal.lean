import Wikipedia.NoExoticSixSphere.RelativeThreeSixFamily

/-!
# Global genericity when the unchanged exterior slices are already embeddings

Interior relative genericity extends to the full parameter space when every
unchanged exterior slice is injective and immersive. These hypotheses are
explicit: the perturbation does not manufacture regularity at the endpoints.
-/

noncomputable section

open Set Function Module
open scoped ContDiff

namespace NoExoticSixSphere.RelativeDoublePointPerturbation

variable {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem baseDifference_perturb (f : ℝ → V → W) (A : V →L[ℝ] W) :
    DoublePointPerturbation.baseDifference (perturb f A) = difference f A := by
  funext q
  exact (difference_eq f A q).symm

theorem exists_small_global_generic_family (f : ℝ → V → W)
    (hf : ContDiff ℝ ∞ (uncurry f)) (hv : finrank ℝ V = 3) (hw : finrank ℝ W = 6)
    (hext : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t) ∧
      ∀ x, Injective (fderiv ℝ (f t) x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : V →L[ℝ] W, ‖A‖ < ε ∧ ContDiff ℝ ∞ (uncurry (perturb f A)) ∧
      (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, perturb f A t x = f t x) ∧
      OperatorRank.RegularThreeSix (fun q : ℝ × V ↦ fderiv ℝ (perturb f A q.1) q.2) ∧
      ∀ q : ℝ × (V × V), q.2.1 ≠ q.2.2 →
        DoublePointPerturbation.baseDifference (perturb f A) q = 0 →
          Surjective (fderiv ℝ (DoublePointPerturbation.baseDifference (perturb f A)) q) := by
  obtain ⟨A, hsmall, hsmooth, hfixed, hjets, hdouble⟩ :=
    exists_small_generic_family f hf hv hw hε
  have houtside (t : ℝ) (ht : t ∉ Ioo (0 : ℝ) 1) : t ≤ 0 ∨ 1 ≤ t := by
    simpa only [mem_Ioo, not_and_or, not_lt] using ht
  refine ⟨A, hsmall, hsmooth, hfixed, ?_, ?_⟩
  · apply hjets.global_of_injective_off hv
    intro q hq
    have ht := houtside q.1 hq
    rw [fderiv_perturb f hf, cutoff_zero ht, zero_smul, add_zero]
    exact (hext q.1 ht).2 q.2
  · rw [baseDifference_perturb]
    intro q hq hz
    by_cases ht : q.1 ∈ Ioo (0 : ℝ) 1
    · exact hdouble q hq ht hz
    · have he := difference_eq f A q
      rw [hfixed q.1 (houtside q.1 ht), hfixed q.1 (houtside q.1 ht)] at he
      have hsame : f q.1 q.2.1 = f q.1 q.2.2 := sub_eq_zero.mp (he.symm.trans hz)
      exact (hq ((hext q.1 (houtside q.1 ht)).1 hsame)).elim

end NoExoticSixSphere.RelativeDoublePointPerturbation
