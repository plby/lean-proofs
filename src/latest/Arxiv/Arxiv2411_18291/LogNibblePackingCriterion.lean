import Arxiv.Arxiv2411_18291.LogNibbleCriticalControl

/-!
# An explicit numerical criterion for an actual packing with bounded leave

The logarithmic tracking route supplies the actual packing once its
initial, gap, failure, and final-density inequalities are verified.
-/

open Finset MeasureTheory ProbabilityTheory Preorder

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem logNibbleGood_graphBounded (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    {a D θ : ℝ} (i : ℕ) (ω : ℕ → State V q)
    (hp : 0 ≤ removalDensity (q.choose (r + 1)) G.card i)
    (hgood : ω ∈ logNibbleGood G H a D i)
    (hθ : removalDensity (q.choose (r + 1)) G.card i + 2 * a ≤ θ) :
    IsGraphBounded (G \ cliqueSupport (r + 1) (trajectoryCliques ω i)) θ := by
  intro f
  have hf := hgood (.inr (.inr f))
  change _ - logNibbleFaceUpper _ _ _ _ < 0 at hf
  have hF : ((G.filter fun e => f.val ⊆ e.val).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast face_degree_le_card G f
  apply (sub_lt_zero.mp hf).trans_le
  unfold logNibbleFaceUpper
  calc
    _ ≤ removalDensity (q.choose (r + 1)) G.card i * Fintype.card V +
        2 * a * Fintype.card V :=
      add_le_add (mul_le_mul_of_nonneg_left hF hp) le_rfl
    _ = (removalDensity (q.choose (r + 1)) G.card i + 2 * a) *
        Fintype.card V := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _)

variable (hqr : r + 1 < q) (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
variable (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) {a D p₀ : ℝ}
variable (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
  ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
variable (hd : ∀ e : Block V (r + 1), ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ 2 * D)
variable (N : ℕ) (hfloor : p₀ ≤ removalDensity (q.choose (r + 1)) G.card N)
variable (hgap : ∀ t, nibbleStepBound q G D t < nibbleCriticalWidth G a D t)
variable (hinit : ∀ t ω, logNibbleTrackedProcess G H a D t 0 ω < -nibbleCriticalWidth G a D t)

include hqr hHG P hd hfloor hgap hinit

theorem exists_supported_log_nibble_path (hsmall : nibbleFailureBound q G a D N < 1) :
    ∃ ω : ℕ → State V q,
      (∀ i, ω (i + 1) ∈ (step (r + 1) H i (frestrictLe i ω)).support) ∧
        ∀ j ≤ N, ω ∈ logNibbleGood G H a D j := by
  have hbad := (log_nibble_failure_probability_le hqr G H hHG P hd N hfloor hgap hinit).trans_lt
    hsmall
  apply FiniteHistoryProcess.exists_supported_path (aborted V q) (step (r + 1) H)
    (fun ω => ∀ j ≤ N, ω ∈ logNibbleGood G H a D j)
  change (probability (r + 1) H).real {ω | ¬∀ j ≤ N, ω ∈ logNibbleGood G H a D j} < 1
  simpa only [not_forall, Classical.not_imp, exists_prop] using hbad

theorem exists_packing_of_log_nibble_bounds (hsmall : nibbleFailureBound q G a D N < 1)
    {θ : ℝ}
    (hθ : removalDensity (q.choose (r + 1)) G.card N + 2 * a ≤ θ) :
    ∃ C : Finset (Block V q), C ⊆ H ∧ C.card = N ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C) θ := by
  obtain ⟨ω, hsupp, hgood⟩ :=
    exists_supported_log_nibble_path hqr G H hHG P hd N hfloor hgap hinit hsmall
  have hlast := hgood N le_rfl
  refine ⟨trajectoryCliques ω N, (trajectory_packing H ω hsupp N).1, ?_,
    trajectory_decomposition H ω hsupp N, ?_⟩
  · exact trajectory_card_of_remaining_nonempty H ω hsupp hqr.le N
      (logNibbleGood_remaining_nonempty P hfloor hlast)
  · exact logNibbleGood_graphBounded G H N ω (P.floor_pos.le.trans hfloor) hlast hθ

end Arxiv2411_18291.CliqueRemovalProcess
