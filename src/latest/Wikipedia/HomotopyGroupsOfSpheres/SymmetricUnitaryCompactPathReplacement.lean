import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryUniformPathReplacement
import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumGenerators
import Wikipedia.NoExoticSixSphere.UniformExponentialPrefixControl

/-!
# Bounded polygon replacement for compact continuous path families

Subdivision controls both the original continuous family and the protected
exponential paths. Only the resulting polygons need an energy bound.
All original balanced minimum rotations can be fixed simultaneously.
-/

open Set unitInterval
open scoped Matrix.Norms.Frobenius

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open ComplexMatrixRealRepresentation VertexSpace BalancedRealInvolutions
open NoExoticSixSphere.UniformTimePartition NoExoticSixSphere.CayleyTransform

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem exists_bounded_polygon_replacement (H : C(I × X, SpecialSpace ι))
    (a b : SpecialSpace ι) (ha : ∀ x, H (0, x) = a) (hb : ∀ x, H (1, x) = b)
    (S : Set X) (B : ℝ)
    (hS : ∀ x ∈ S, ∃ K : SkewOperators (2 * Fintype.card ι), ‖K‖ ≤ B ∧
      ∀ u : I, specialOrthogonal (H (u, x)) = specialOrthogonal a *
        NoExoticSixSphere.OrthogonalExponential.exp ((u : ℝ) • K)) (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ ∃ p : C(X, VertexSpace.Space ι m),
      ∃ hp : ∀ x, p x ∈ admissible a b m,
        ∃ E : ℝ, 0 ≤ E ∧ (∀ x, energy a b (time m) (p x) ≤ E) ∧
          Nonempty (H.HomotopyRel (realizedFamily a b (time m) (strictMono_time m) p hp)
            {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 ∈ S}) := by
  obtain ⟨N₀, hN₀⟩ := NoExoticSixSphere.OrthogonalExponential.exists_uniform_prefix_target_bound
    (2 * Fintype.card ι) B
  obtain ⟨m, hm, hsmall⟩ := ShortLog.exists_uniform_partition H (max lower N₀)
  let p := sampleUniform H m
  have hp : ∀ x, p x ∈ admissible a b m := sampleUniform_admissible H a b m ha hb hsmall
  obtain ⟨E, hE0, hE⟩ := exists_family_energy_bound a b (time m) p hp
  refine ⟨m, (le_max_left _ _).trans hm, p, hp, E, hE0, hE, ⟨?_⟩⟩
  apply uniformReplacementHomotopy H a b m ha hb hsmall S
  intro x hx
  obtain ⟨K, hK, hpath⟩ := hS x hx
  refine ⟨K, ?_, hN₀ m ((le_max_right _ _).trans hm) K hK⟩
  intro u
  change specialOrthogonal (H (u, x)) = specialOrthogonal (H (0, x)) *
    NoExoticSixSphere.OrthogonalExponential.exp ((u : ℝ) • K)
  rw [ha x]
  exact hpath u

theorem exists_bounded_polygon_replacement_fixing_minima (n : ℕ)
    (H : C(I × X, SpecialSpace (Index n)))
    (ha : ∀ x, H (0, x) = specialIdentity) (hb : ∀ x, H (1, x) = antipode n) (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ ∃ p : C(X, VertexSpace.Space (Index n) m),
      ∃ hp : ∀ x, p x ∈ admissible specialIdentity (antipode n) m,
        ∃ E : ℝ, 0 ≤ E ∧ (∀ x, energy specialIdentity (antipode n) (time m) (p x) ≤ E) ∧
          Nonempty (H.HomotopyRel
            (realizedFamily specialIdentity (antipode n) (time m) (strictMono_time m) p hp)
            {q | q.1 = 0 ∨ q.1 = 1 ∨ ∃ J : BalancedRealInvolutions.Space n,
              ∀ u : I, H (u, q.2) = rotation J ((u : ℝ) * Real.pi)}) := by
  obtain ⟨B, hB⟩ := exists_orthogonalMinimumGenerator_bound n
  apply exists_bounded_polygon_replacement H specialIdentity (antipode n) ha hb
    {x | ∃ J : BalancedRealInvolutions.Space n,
      ∀ u : I, H (u, x) = rotation J ((u : ℝ) * Real.pi)} B _ lower
  intro x hx
  obtain ⟨J, hJ⟩ := hx
  refine ⟨skewMap (minimumGenerator J), hB J, ?_⟩
  intro u
  rw [hJ u, rotation_toOrthogonal]
  have hid : specialOrthogonal (specialIdentity : SpecialSpace (Index n)) = 1 :=
    orthogonal.map_one
  rw [hid, one_mul]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
