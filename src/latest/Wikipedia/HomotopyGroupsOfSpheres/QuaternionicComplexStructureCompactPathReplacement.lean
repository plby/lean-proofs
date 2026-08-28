import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureUniformPathReplacement
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicUniformPrefixControl
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimumGenerators

/-!
# Compact continuous path families admit bounded-energy polygon replacement

Uniform subdivision controls the original complex-structure family and the
protected exponential paths simultaneously. The finite energy bound is obtained
only for the resulting polygons. All original minimum rotations can be fixed
without choosing their parameters continuously on the protected set.
-/

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open ComplexStructures ComplexStructureVertices Exponential
open NoExoticSixSphere.UniformTimePartition

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]

private theorem real_norm_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : ℝ) (v : V) : ‖r • v‖ = |r| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]

theorem exists_bounded_polygon_replacement (H : C(I × X, ComplexStructures.Space n))
    (a b : ComplexStructures.Space n) (ha : ∀ x, H (0, x) = a) (hb : ∀ x, H (1, x) = b)
    (S : Set X) (B : ℝ)
    (hS : ∀ x ∈ S, ∃ K : SkewSpace n, ‖K‖ ≤ B ∧
      ∀ u : I, toSymplectic (H (u, x)) = toSymplectic a * exp ((u : ℝ) • K)) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∃ p : C(X, ComplexStructureVertices.Space n m),
      ∃ hp : ∀ x, p x ∈ admissible a b m,
        ∃ E : ℝ, 0 ≤ E ∧ (∀ x, energy a b (time m) (p x) ≤ E) ∧
          Nonempty (H.HomotopyRel (realizedFamily a b (time m) (strictMono_time m) p hp)
            {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 ∈ S}) := by
  obtain ⟨N₀, hN₀⟩ := exists_uniform_prefix_target_bound n B
  obtain ⟨m, hm, hsmall⟩ := ShortLog.exists_uniform_partition H (max N N₀)
  let p := sampleUniform H m
  have hp : ∀ x, p x ∈ admissible a b m := sampleUniform_admissible H a b m ha hb hsmall
  obtain ⟨E, hE0, hE⟩ := exists_family_energy_bound a b (time m) p hp
  refine ⟨m, (le_max_left _ _).trans hm, p, hp, E, hE0, hE, ⟨?_⟩⟩
  apply uniformReplacementHomotopy H a b m ha hb hsmall S
  intro x hx
  obtain ⟨K, hK, hpath⟩ := hS x hx
  refine ⟨K, ?_, hN₀ m ((le_max_right _ _).trans hm) K hK⟩
  intro u
  change toSymplectic (H (u, x)) = toSymplectic (H (0, x)) * exp ((u : ℝ) • K)
  rw [ha x]
  exact hpath u

theorem exists_bounded_polygon_replacement_fixing_minima
    (H : C(I × X, ComplexStructures.Space n)) (a b : ComplexStructures.Space n)
    (ha : ∀ x, H (0, x) = a) (hb : ∀ x, H (1, x) = b) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∃ p : C(X, ComplexStructureVertices.Space n m),
      ∃ hp : ∀ x, p x ∈ admissible a b m,
        ∃ E : ℝ, 0 ≤ E ∧ (∀ x, energy a b (time m) (p x) ≤ E) ∧
          Nonempty (H.HomotopyRel (realizedFamily a b (time m) (strictMono_time m) p hp)
            {q | q.1 = 0 ∨ q.1 = 1 ∨ ∃ P : AnticommutingStructures.Space a,
              ∀ u : I, H (u, q.2) = AnticommutingStructures.rotation P ((u : ℝ) * Real.pi)}) := by
  apply exists_bounded_polygon_replacement H a b ha hb
    {x | ∃ P : AnticommutingStructures.Space a,
      ∀ u : I, H (u, x) = AnticommutingStructures.rotation P ((u : ℝ) * Real.pi)} Real.pi _ N
  intro x hx
  obtain ⟨P, hP⟩ := hx
  refine ⟨Real.pi • (AnticommutingStructures.generatorParameter P).val.val, ?_, ?_⟩
  · rw [real_norm_smul (V := SkewSpace n), abs_of_pos Real.pi_pos]
    exact mul_le_of_le_one_right Real.pi_pos.le
      (ComplexStructures.norm_le_one (AnticommutingStructures.generatorParameter P).val)
  · intro u
    rw [hP u, AnticommutingStructures.rotation_toSymplectic, smul_smul]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
