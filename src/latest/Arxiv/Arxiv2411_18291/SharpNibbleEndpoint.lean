import Arxiv.Arxiv2411_18291.NibbleEndConditions

/-! # Retaining the stopping density and face error separately -/

noncomputable section

namespace Arxiv2411_18291

theorem NibbleComparisonParameters.step_le_error {k : ℕ} {a g D p₀ L : ℝ}
    (P : NibbleComparisonParameters k a g D p₀ L) : (k : ℝ) / g ≤ a := by
  have hk : (3 : ℝ) ≤ k := by exact_mod_cast P.rank
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk]
  have hk3 := mul_le_mul_of_nonneg_right hk2 (Nat.cast_nonneg k)
  have hk3n : (0 : ℝ) ≤ (k : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg _) _
  have hkg : (k : ℝ) ≤ a ^ 2 * g := by
    have h := P.many_edges
    nlinarith only [hk3, hk3n, h]
  have ha1 : a ≤ 1 := P.error_half.trans (by norm_num)
  have ha2 : a ^ 2 ≤ a := by
    have h := mul_le_mul_of_nonneg_left ha1 P.error_pos.le
    nlinarith only [h]
  exact (div_le_iff₀ P.graph_pos).mpr
    (hkg.trans (mul_le_mul_of_nonneg_right ha2 P.graph_pos.le))

theorem NibbleComparisonParameters.horizon_face_density_lt_error
    {k : ℕ} {a g D p₀ L : ℝ} (P : NibbleComparisonParameters k a g D p₀ L) :
    removalDensity k g (nibbleHorizon k g p₀) + 128 * (k : ℝ) * a <
      p₀ + (128 * (k : ℝ) + 1) * a := by
  have hk : 0 < k := by have h := P.rank; omega
  have h := nibbleHorizon_density_lt hk (p₀ := p₀) P.graph_pos
  have hs := P.step_le_error
  linarith only [h, hs]

namespace CliqueRemovalProcess

theorem exists_packing_at_nibble_horizon_sharp
    {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ} (hqr : r + 1 < q)
    (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) {a D p₀ : ℝ}
    (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (Q : NibbleCountConditions (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (R : NibbleEndConditions (q.choose (r + 1)) a G.card (Fintype.card V) p₀ (q - r))
    (hd : ∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - D| ≤ a ^ 3 * D)
    (hsmall : nibbleFailureBound q G a D (nibbleHorizon (q.choose (r + 1)) G.card p₀) < 1) :
    ∃ C : Finset (Block V q), C ⊆ H ∧ C.card = nibbleHorizon (q.choose (r + 1)) G.card p₀ ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          (p₀ + (128 * (q.choose (r + 1) : ℝ) + 1) * a) := by
  have hk : 0 < q.choose (r + 1) := by have h := P.rank; omega
  exact exists_regular_nibble_packing hqr G H hHG P Q hd _
    (nibbleHorizon_density_ge hk P.graph_pos P.floor_le_one)
    (nibble_all_width_gaps hqr G P R) hsmall P.horizon_face_density_lt_error.le

end CliqueRemovalProcess

end Arxiv2411_18291
