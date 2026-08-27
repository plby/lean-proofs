import Arxiv.Arxiv2411_18291.NibbleGoodTrend
import Arxiv.Arxiv2411_18291.NibbleEdgeVariance

/-! # Fixed step and variance scales for the finite family of nibble tracks -/

open Finset

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] {r : ℕ}

def nibbleCountStepBound (k : ℕ) (D : ℝ) : ℝ := (k : ℝ) * (2 * D) + 130 * (k : ℝ) ^ 3 * D

def nibbleStepBound (q : ℕ) (G : Hypergraph V (r + 1)) (D : ℝ) (t : NibbleTrack V r) : ℝ :=
  let k := q.choose (r + 1)
  match t with
  | .inl _ => nibbleCountStepBound k D
  | .inr (.inl _) => nibbleEdgeStepBound k G.card D
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1))
  | .inr (.inr _) => ((q - r : ℕ) : ℝ) + (k : ℝ) * Fintype.card V / G.card

def nibbleVarianceRate (q : ℕ) (G : Hypergraph V (r + 1)) (D : ℝ) (t : NibbleTrack V r) : ℝ :=
  let k := q.choose (r + 1)
  match t with
  | .inl _ => nibbleCountStepBound k D ^ 2
  | .inr (.inl _) => nibbleEdgeStepBound k G.card D
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)) * (10 * (k : ℝ) ^ 2 * D / G.card)
  | .inr (.inr _) => 4 * ((q - r : ℕ) : ℝ) * (1 + 128 * (k : ℝ)) * k *
      Fintype.card V / G.card

theorem nibbleStepBound_pos {q : ℕ} (hqr : r + 1 < q) (G : Hypergraph V (r + 1))
    {D : ℝ} (hg : 0 < (G.card : ℝ)) (hD : 0 < D) (t : NibbleTrack V r) :
    0 < nibbleStepBound q G D t := by
  have hk : (0 : ℝ) < q.choose (r + 1) := by exact_mod_cast Nat.choose_pos hqr.le
  have hdiff : (0 : ℝ) < (q - r : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt (by omega : r < q)
  rcases t with b | (⟨e, b⟩ | f) <;>
    dsimp only [nibbleStepBound, nibbleCountStepBound, nibbleEdgeStepBound] <;> positivity

theorem nibbleVarianceRate_nonneg (q : ℕ) (G : Hypergraph V (r + 1))
    {D : ℝ} (hD : 0 ≤ D) (t : NibbleTrack V r) :
    0 ≤ nibbleVarianceRate q G D t := by
  rcases t with b | (⟨e, b⟩ | f) <;>
    dsimp only [nibbleVarianceRate, nibbleCountStepBound, nibbleEdgeStepBound] <;> positivity

end Arxiv2411_18291.CliqueRemovalProcess
