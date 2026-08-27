import Arxiv.Arxiv2411_18291.DenseNibbleParameters
import Arxiv.Arxiv2411_18291.NibbleUniformExponent
import Arxiv.Arxiv2411_18291.NibbleTailDecay

/-! # The eventual nibble in every positive rank at constant graph density -/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

open CliqueRemovalProcess

theorem eventually_exists_dense_nibble (q r : ℕ) (hqr : r + 1 < q)
    (hk : 3 ≤ q.choose (r + 1)) {ε θ : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
      (τ : ℝ), θ * (n.choose (r + 1) : ℝ) ≤ G.card →
      (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ →
      (∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) →
      (∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - (r + 1)) : ℝ)| ≤
          (n : ℝ) ^ (-ε) * (τ * (n.choose (q - (r + 1)) : ℝ))) →
      ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
        IsDecomposition (cliqueSupport (r + 1) C) C ∧
          IsGraphBounded (G \ cliqueSupport (r + 1) C)
            (3 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) := by
  let η := 1 / 2 - ε
  have hη : 0 < η := by dsimp only [η]; linarith only [hεhalf]
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_dense_nibble_parameters q r hqr hk hε hεhalf hθ,
    eventually_nibble_tail_lt_one r hη] with n hn hparams htail
  intro G H τ hG hτ hHG hd
  let k := q.choose (r + 1)
  let a := (n : ℝ) ^ (-(ε / 3))
  let D := τ * (n.choose (q - (r + 1)) : ℝ)
  let p₀ := (n : ℝ) ^ (-(ε / (3 * (k : ℝ))))
  let cg := θ / (2 * ((r + 1).factorial : ℝ))
  let N := nibbleHorizon k (G.card : ℝ) p₀
  obtain ⟨hP, hQ, hR, hS⟩ := hparams G.card τ hG hτ
  have P : NibbleComparisonParameters k a G.card D p₀
      ((Fintype.card (Fin n) : ℝ) ^ (q - (r + 1) - 1)) := by
    simpa only [Fintype.card_fin, k, a, D, p₀] using hP
  have Q : NibbleCountConditions k a G.card D p₀
      ((Fintype.card (Fin n) : ℝ) ^ (q - (r + 1) - 1)) := by
    simpa only [Fintype.card_fin, k, a, D, p₀] using hQ
  have R : NibbleEndConditions k a G.card (Fintype.card (Fin n)) p₀ (q - r) := by
    simpa only [Fintype.card_fin, k, a, p₀] using hR
  have S : NibbleExponentConditions k (q - r) a G.card D (Fintype.card (Fin n))
      ((Fintype.card (Fin n) : ℝ) ^ (q - (r + 1) - 1)) ((n : ℝ) ^ η) cg := by
    simpa only [Fintype.card_fin, k, a, D, η, cg] using hS
  have hkpos : 0 < k := by dsimp only [k]; omega
  have hN : (N : ℝ) ≤ G.card :=
    nibbleHorizon_le_graph hkpos P.graph_pos.le P.floor_pos.le P.floor_le_one
  have hfailure := nibbleFailureBound_le_of_margins hqr G P R S N hN
  have hsmall : nibbleFailureBound q G a D N < 1 := by
    apply hfailure.trans_lt
    simpa only [Fintype.card_fin] using htail
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha3 : a ^ 3 = (n : ℝ) ^ (-ε) := by
    dsimp only [a]
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    ring
  rw [← ha3] at hd
  obtain ⟨C, hsub, _, hdec, hbounded⟩ :=
    exists_packing_at_nibble_horizon hqr G H hHG P Q R hd hsmall
  exact ⟨C, hsub, hdec, hbounded⟩

end Arxiv2411_18291
