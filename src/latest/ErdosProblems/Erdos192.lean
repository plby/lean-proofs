import ErdosProblems.Erdos192.Infinite
import ErdosProblems.Erdos192.Ternary
import ErdosProblems.Erdos192.Geometry

/-!
# Erdős problem 192

The full classification for positive standard-coordinate unit walks in real
space, with arbitrary starting points. The finite Keränen obligations are
kernel checked using prefix-count, streaming, and bitset certificates.

The mathematical construction and parts of the noncomputational infrastructure
are adapted from Lorenzo Luccioli's Aristotle formalization, revision
`dae4202b1a2fac70ebf3c311e9f822bebbb60769` of
https://github.com/LorenzoLuccioli/KE92ErdosProblems.
The reference files are not imports of this development.
-/

namespace Erdos192

theorem exists_parikhAPFree_of_ge_four {d : ℕ} (hd : 4 ≤ d) :
    ∃ f : ℕ → Fin d, parikhAPFree f := by
  obtain ⟨f, hf⟩ := exists_inf_abelianSquareFree_four
  exact ⟨fun n => Fin.castLE hd (f n),
    (infAbelianSquareFree_iff_parikhAPFree _).mp
      (inf_asf_comp_inj f (Fin.castLE hd) (Fin.castLE_injective hd) hf)⟩

theorem erdos_problem_192_classification (d : ℕ) :
    (∀ f : ℕ → Fin d, hasParikhAP f) ↔ d ≤ 3 := by
  constructor
  · intro h
    by_contra hd
    obtain ⟨f, hf⟩ := exists_parikhAPFree_of_ge_four (by omega : 4 ≤ d)
    exact hf (h f)
  · exact fun hd f => hasParikhAP_of_le_three hd f

/-- Every positive unit walk has a nontrivial progression in its visited set
exactly in dimensions at most three. At dimension zero there are no such walks. -/
theorem erdos_192 (d : ℕ) :
    (∀ p : ℕ → Fin d → ℝ, PositiveUnitWalk p →
      ∃ x y z : Fin d → ℝ, x ∈ Set.range p ∧ y ∈ Set.range p ∧ z ∈ Set.range p ∧
        x ≠ y ∧ ∀ j, x j + z j = 2 * y j) ↔ d ≤ 3 := by
  rw [← erdos_problem_192_classification d, ← geometric_classification_iff_words d]
  exact forall_congr' fun p => imp_congr_right fun hp => positiveUnitWalk_setAP_iff p hp

/-- Counterexamples exist from every prescribed starting point, not merely the origin. -/
theorem exists_avoiding_walk {d : ℕ} (hd : 4 ≤ d) (x : Fin d → ℝ) :
    ∃ p : ℕ → Fin d → ℝ, p 0 = x ∧ PositiveUnitWalk p ∧ ¬ContainsThreeTermAP p := by
  obtain ⟨f, hf⟩ := exists_parikhAPFree_of_ge_four hd
  refine ⟨realWalk x f, ?_, realWalk_positive x f, ?_⟩
  · ext j
    simp [realWalk, parikhCount]
  · intro h
    exact hf ((realWalk_hasAP_iff x f).mp ((realWalk_setAP_iff x f).mp h))

end Erdos192
