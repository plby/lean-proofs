import ErdosProblems.Erdos76.PippengerSpencerAllOrderZero
import ErdosProblems.Erdos76.PippengerSpencerOuterIteration

/-!
# Approximate hypergraph edge coloring

The complete Pippenger–Spencer development is imported from the existing
Erdős 76 development. No probabilistic coloring theorem is introduced as an
axiom or an assumption here.
-/

namespace Erdos19

/-- The proved near-regular, bounded-uniformity Pippenger–Spencer theorem. -/
theorem nearRegularPippengerSpencerEdgeColoring :
    Erdos76.NearRegularPippengerSpencerEdgeColoring :=
  Erdos76.FiniteHypergraph.sharpExactRegularTwoSidedFixedLengthInnerMarginal_to_nearRegular
    Erdos76.FiniteHypergraph.sharpExactRegularTwoSidedFixedLengthInnerMarginal

open Erdos76 Erdos76.FiniteHypergraph
open Erdos76.PippengerSpencerEdgeColoring

/-- The maximum-degree form of approximate edge coloring, without a minimum
degree assumption. The private affine completion preserves the original
edges and has exactly degree `D`; its new pair degrees are at most one. -/
theorem uniform_approximate_edgeColoring (k : ℕ) (hk : 0 < k)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ D₀ : ℕ,
      ∀ (V E : Type) [DecidableEq V] [Fintype E] [DecidableEq E],
        ∀ (H : FiniteHypergraph V E) (D : ℕ),
          D₀ ≤ D → H.IsUniform k →
          (∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) →
          (∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
            (H.edgePairDegree u v : ℝ) < delta * (D : ℝ)) →
          ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ (1 + epsilon) * (D : ℝ) ∧
            Nonempty (H.EdgeColoring q) := by
  classical
  obtain ⟨delta, hdelta, D₀, hround⟩ :=
    nearRegularPippengerSpencerEdgeColoring k hk epsilon hepsilon
  obtain ⟨D₁, hD₁⟩ := exists_nat_gt (1 / delta)
  refine ⟨delta / 2, div_pos hdelta (by norm_num), max D₀ D₁, ?_⟩
  intro V E _ _ _ H D hDlarge hunif hdeg hpair
  have hD₀ : D₀ ≤ D := (le_max_left _ _).trans hDlarge
  have hD₁le : D₁ ≤ D := (le_max_right _ _).trans hDlarge
  have hratio : 1 / delta < (D : ℝ) := hD₁.trans_le (by exact_mod_cast hD₁le)
  have hdeltaD : 1 < delta * (D : ℝ) := by
    have h := (div_lt_iff₀ hdelta).mp hratio
    nlinarith
  have hDposR : (0 : ℝ) < D := by nlinarith
  obtain ⟨q, hqge, hqprime⟩ := Nat.exists_infinite_primes (max k D)
  letI : Fact q.Prime := ⟨hqprime⟩
  letI : NeZero q := ⟨hqprime.ne_zero⟩
  have hkq : k ≤ q := (le_max_left _ _).trans hqge
  have hDq : D ≤ q := (le_max_right _ _).trans hqge
  let HC := regularCompletion H D k q hdeg
  obtain ⟨r, hrpos, hrle, ⟨c⟩⟩ := hround
    (PrivateVertex H k q) (CompletionEdge H D k q hdeg) HC D hD₀
    (regularCompletion_isUniform hdeg hunif)
    (by
      intro z hz
      rw [edgeDegree_regularCompletion hdeg]
      nlinarith [mul_nonneg (le_of_lt hdelta) (Nat.cast_nonneg D)])
    (by
      intro z hz
      exact (edgeDegree_regularCompletion hdeg z).le)
    (by
      intro z hz z' hz' hzz'
      by_cases howner : z.1 = z'.1
      · have hle := edgePairDegree_regularCompletion_le_one_same_owner
          hkq hDq hdeg hzz' howner
        have hleR : ((HC.edgePairDegree z z' : ℕ) : ℝ) ≤ (1 : ℝ) := by
          exact_mod_cast hle
        exact hleR.trans_lt hdeltaD
      · have hle := edgePairDegree_regularCompletion_le_of_owner_ne hdeg howner
        have howners : z.1.1 ≠ z'.1.1 := by
          intro hv
          exact howner (Subtype.ext hv)
        have horiginal := hpair z.1.1 z.1.2 z'.1.1 z'.1.2 howners
        have hsmall : (delta / 2) * (D : ℝ) < delta * (D : ℝ) := by
          nlinarith
        exact (Nat.cast_le.mpr hle).trans_lt (horiginal.trans hsmall))
  exact ⟨r, hrpos, hrle, ⟨restrict_originalEdgeColoring hk hdeg c⟩⟩

#print axioms nearRegularPippengerSpencerEdgeColoring
#print axioms uniform_approximate_edgeColoring

end Erdos19
