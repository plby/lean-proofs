import Mathlib
import ErdosProblems.Erdos550.ClusterDegreeAccounting
import ErdosProblems.Erdos550.OffTuranParams

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# From cleaned host degree to average normalized cluster degree

The direct off--Turán proof normalizes the degree of a cluster by the common
upper bound `scale = ⌊N/ℓ⌋ + 1`.  Thus `ℓ * scale ≤ N + ℓ`.  The lemmas below
record, with deliberately generous constants, that the linear margin surviving
regularity also pays for this final rounding of the cluster size.
-/

namespace Erdos550

/-- The tight regularity loss is far below the available `50ηN` average-degree
budget once `ε ≤ η`, `ℓ ≤ ηN`, and `η` is small. -/
lemma offTuran_cleaning_loss_lt_fifty
    (ε η N ell loss : ℝ)
    (hε : 0 ≤ ε) (hεη : ε ≤ η)
    (hη : 0 < η) (hηsmall : η ≤ 1 / 100)
    (hN : 0 ≤ N) (hell : 0 ≤ ell) (hellN : ell ≤ η * N)
    (hloss :
      loss <
        4 * ε * N ^ 2 + ε / 2 * N ^ 2 +
          η * (N + ell) ^ 2) :
    loss < 50 * η * N ^ 2 := by
  have hηN : 0 ≤ η * N := mul_nonneg hη.le hN
  have hηone : η ≤ 1 := by linarith
  have hsum : N + ell ≤ 2 * N := by
    nlinarith
  have hsq :
      (N + ell) ^ 2 ≤ 4 * N ^ 2 := by
    nlinarith [sq_nonneg (N + ell), sq_nonneg (2 * N)]
  have hεN :
      ε * N ^ 2 ≤ η * N ^ 2 :=
    mul_le_mul_of_nonneg_right hεη (sq_nonneg N)
  have hηsq :
      η * (N + ell) ^ 2 ≤
        η * (4 * N ^ 2) :=
    mul_le_mul_of_nonneg_left hsq hη.le
  nlinarith [mul_nonneg hη.le (sq_nonneg N),
    mul_nonneg hε (sq_nonneg N)]

/-- Raw average degree `base+200ηN`, after a loss below `50ηN`, leaves the
cleaned average degree `base+150ηN`. -/
lemma offTuran_cleaned_average_150
    (base η N e e' loss : ℝ)
    (hraw : (base + 200 * η * N) * N ≤ 2 * e)
    (hlossDef : loss = 2 * (e - e') / N)
    (hN : 0 < N)
    (hloss : loss < 50 * η * N) :
    (base + 150 * η * N) * N ≤ 2 * e' := by
  rw [hlossDef, div_lt_iff₀ hN] at hloss
  nlinarith

/-- The cluster-size rounding `ℓ*scale ≤ N+ℓ` consumes less than the spare
`50ηN` margin. -/
lemma normalized_cluster_average_arith
    (base η N ell scale twoE : ℝ)
    (hbase0 : 0 ≤ base) (hbaseN : base ≤ N)
    (hη : 0 < η) (hηsmall : η ≤ 1 / 100)
    (hN : 0 < N) (hell : 0 ≤ ell) (hscale : 0 < scale)
    (hellN : ell ≤ η * N)
    (hellscale : ell * scale ≤ N + ell)
    (hclean : (base + 150 * η * N) * N ≤ twoE) :
    (base + 100 * η * N) * ell ≤ twoE / scale := by
  rw [le_div_iff₀ hscale]
  have hcoef : 0 ≤ base + 100 * η * N := by positivity
  have hround :
      (base + 100 * η * N) * (ell * scale) ≤
        (base + 100 * η * N) * (N + ell) :=
    mul_le_mul_of_nonneg_left hellscale hcoef
  have hmargin :
      (base + 100 * η * N) * (N + ell) ≤
        (base + 150 * η * N) * N := by
    nlinarith [mul_le_mul_of_nonneg_left hellN hbase0,
      mul_le_mul_of_nonneg_left hbaseN hell,
      mul_nonneg hη.le (sq_nonneg N)]
  calc
    (base + 100 * η * N) * ell * scale =
        (base + 100 * η * N) * (ell * scale) := by ring
    _ ≤ (base + 100 * η * N) * (N + ell) := hround
    _ ≤ (base + 150 * η * N) * N := hmargin
    _ ≤ twoE := hclean

/-- Partition-level form of `normalized_cluster_average_arith`. -/
lemma normalized_cluster_average_of_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (scale : ℕ)
    (base η : ℝ)
    (hbase0 : 0 ≤ base)
    (hbaseN : base ≤ Fintype.card V)
    (hη : 0 < η) (hηsmall : η ≤ 1 / 100)
    (hN : 0 < Fintype.card V)
    (hscale : 0 < scale)
    (hellN : (P.parts.card : ℝ) ≤ η * Fintype.card V)
    (hellscale :
      (P.parts.card : ℝ) * scale ≤
        Fintype.card V + P.parts.card)
    (hclean :
      (base + 150 * η * Fintype.card V) * Fintype.card V ≤
        2 * (G.edgeFinset.card : ℝ)) :
    (base + 100 * η * Fintype.card V) *
        (P.parts.card : ℝ) ≤
      ∑ i, clusterNormalizedDegree G P scale i := by
  rw [sum_clusterNormalizedDegree G P scale]
  apply normalized_cluster_average_arith base η
    (Fintype.card V) P.parts.card scale
    (2 * (G.edgeFinset.card : ℝ))
  · exact hbase0
  · exact hbaseN
  · exact hη
  · exact hηsmall
  · exact_mod_cast hN
  · positivity
  · exact_mod_cast hscale
  · exact hellN
  · exact hellscale
  · exact hclean

end Erdos550
