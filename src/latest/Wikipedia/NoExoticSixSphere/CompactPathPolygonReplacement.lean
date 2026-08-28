import Wikipedia.NoExoticSixSphere.OrthogonalUniformPathReplacement
import Wikipedia.NoExoticSixSphere.UniformExponentialPrefixControl
import Wikipedia.NoExoticSixSphere.OrthogonalComplexStructures

/-!
# Compact continuous path families admit bounded-energy polygon replacements

The uniform partition controls the original family and all protected bounded
exponentials simultaneously. The finite polygon energy is bounded only after
the replacement has been constructed. In particular, the original continuous
paths need not have finite energy.
-/

open Set unitInterval

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace
  UniformTimePartition

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem exists_bounded_polygon_replacement
    (H : C(I × X, OrthogonalOperators n)) (a b : OrthogonalOperators n)
    (ha : ∀ x, H (0, x) = a) (hb : ∀ x, H (1, x) = b)
    (S : Set X) (B : ℝ)
    (hS : ∀ x ∈ S, ∃ K : SkewOperators n, ‖K‖ ≤ B ∧
      ∀ u : I, H (u, x) = a * exp ((u : ℝ) • K)) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∃ p : C(X, Space n m), ∃ hp : ∀ x, p x ∈ admissible a b m,
      ∃ E : ℝ, 0 ≤ E ∧ (∀ x, energy a b (time m) (p x) ≤ E) ∧
        Nonempty (H.HomotopyRel (realizedFamily a b (time m) p hp)
          {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 ∈ S}) := by
  obtain ⟨N₀, hN₀⟩ := exists_uniform_prefix_target_bound n B
  obtain ⟨m, hm, hsmall⟩ := exists_uniform_increment_partition H (logarithmChart n).source
    ((logarithmChart n).open_source.mem_nhds (one_mem_logarithmChart_source n)) (max N N₀)
  let p := sampleUniform H m
  have hp : ∀ x, p x ∈ admissible a b m := sampleUniform_admissible H a b m ha hb hsmall
  obtain ⟨E, hE0, hE⟩ := exists_family_energy_bound a b (time m) p hp
  refine ⟨m, (le_max_left _ _).trans hm, p, hp, E, hE0, hE, ⟨?_⟩⟩
  apply uniformReplacementHomotopy H a b m ha hb hsmall S
  intro x hx
  obtain ⟨K, hK, hpath⟩ := hS x hx
  refine ⟨K, ?_, hN₀ m ((le_max_right _ _).trans hm) K hK⟩
  intro u
  rw [ha x]
  exact hpath u

/-- The protected paths can be all minimum exponentials at once; no choice of
a continuous complex structure on the protected parameter set is required. -/
theorem exists_bounded_polygon_replacement_fixing_minima
    (H : C(I × X, OrthogonalOperators n)) (a b : OrthogonalOperators n)
    (ha : ∀ x, H (0, x) = a) (hb : ∀ x, H (1, x) = b) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∃ p : C(X, Space n m), ∃ hp : ∀ x, p x ∈ admissible a b m,
      ∃ E : ℝ, 0 ≤ E ∧ (∀ x, energy a b (time m) (p x) ≤ E) ∧
        Nonempty (H.HomotopyRel (realizedFamily a b (time m) p hp)
          {q | q.1 = 0 ∨ q.1 = 1 ∨ ∃ J : OrthogonalComplexStructures.Space n,
            ∀ u : I, H (u, q.2) = a * exp ((u : ℝ) • (Real.pi • J.1))}) := by
  apply exists_bounded_polygon_replacement H a b ha hb
    {x | ∃ J : OrthogonalComplexStructures.Space n,
      ∀ u : I, H (u, x) = a * exp ((u : ℝ) • (Real.pi • J.1))} Real.pi _ N
  intro x hx
  obtain ⟨J, hJ⟩ := hx
  refine ⟨Real.pi • J.1, ?_, hJ⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact mul_le_of_le_one_right Real.pi_pos.le (OrthogonalComplexStructures.norm_le_one J)

end NoExoticSixSphere.OrthogonalPolygon
