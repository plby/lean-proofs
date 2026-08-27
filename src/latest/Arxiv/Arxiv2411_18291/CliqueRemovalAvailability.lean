import Arxiv.Arxiv2411_18291.FrozenEdgeValue
import Arxiv.Arxiv2411_18291.CliqueRemovalPacking
import Arxiv.Arxiv2411_18291.RemovalDensity

/-!
# Current availability implies no earlier abort on a supported trajectory

This lets a current lower bound on the clique count justify the exact
remaining-edge density and the live values of all frozen edge processes.
-/

open Finset MeasureTheory ProbabilityTheory Preorder

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem remainingCliques_antitone (H : Finset (Block V q)) {D D' : Finset (Block V q)}
    (hD : D ⊆ D') : remainingCliques r H D' ⊆ remainingCliques r H D := by
  intro Q hQ
  obtain ⟨hQH, hdis⟩ := mem_remainingCliques.mp hQ
  exact mem_remainingCliques.mpr ⟨hQH, fun P hP => hdis P (hD hP)⟩

theorem trajectory_remainingCliques_antitone (H : Finset (Block V q)) (ω : ℕ → State V q) :
    Antitone (fun n => remainingCliques r H (trajectoryCliques ω n)) := by
  intro i j hij
  exact remainingCliques_antitone H (trajectoryCliques_mono ω hij)

theorem trajectory_support_ae (H : Finset (Block V q)) :
    ∀ᵐ (ω : ℕ → State V q) ∂probability r H,
      ∀ i : ℕ, ω (i + 1) ∈ (step r H i (frestrictLe i ω)).support :=
  ae_all_iff.mpr (fun i => FiniteHistoryProcess.next_mem_support (aborted V q) (step r H) i)

variable (H : Finset (Block V q)) (ω : ℕ → State V q)
variable (hsupport : ∀ i, ω (i + 1) ∈ (step r H i (frestrictLe i ω)).support)

include hsupport

theorem trajectory_choices_of_remaining_nonempty (n : ℕ)
    (hR : (remainingCliques r H (trajectoryCliques ω n)).Nonempty) :
    ∀ i < n, ∃ Q, ω (i + 1) = some Q := by
  intro i hi
  have hav : (remainingCliques r H (trajectoryCliques ω i)).Nonempty :=
    hR.mono (trajectory_remainingCliques_antitone H ω hi.le)
  have hav' : (remainingCliques r H (historyCliques (frestrictLe i ω))).Nonempty := by
    simpa only [historyCliques_prefix] using hav
  obtain ⟨Q, hQ, _⟩ := step_choose_of_nonempty H (frestrictLe i ω) hav' _ (hsupport i)
  exact ⟨Q, hQ⟩

theorem trajectory_card_of_remaining_nonempty (hqr : r ≤ q) (n : ℕ)
    (hR : (remainingCliques r H (trajectoryCliques ω n)).Nonempty) :
    (trajectoryCliques ω n).card = n :=
  trajectory_card H ω hsupport hqr n
    (fun _ hi => hR.mono (trajectory_remainingCliques_antitone H ω hi.le))

theorem trajectory_leave_density (hqr : r ≤ q) (G : Hypergraph V r) (hG : G.Nonempty)
    (hH : ∀ Q ∈ H, cliqueEdges r Q ⊆ G) (n : ℕ)
    (hR : (remainingCliques r H (trajectoryCliques ω n)).Nonempty) :
    ((G \ cliqueSupport r (trajectoryCliques ω n)).card : ℝ) =
      removalDensity (q.choose r) G.card n * G.card := by
  have hg : (0 : ℝ) < G.card := by exact_mod_cast hG.card_pos
  have h : ((G \ cliqueSupport r (trajectoryCliques ω n)).card : ℝ) +
      (n : ℝ) * q.choose r = G.card := by
    exact_mod_cast trajectory_leave_card H ω hsupport hqr G hH n
      (fun i hi => hR.mono (trajectory_remainingCliques_antitone H ω hi.le))
  rw [removalDensity_mul _ hg.ne']
  nlinarith only [h]

theorem frozenEdgeProcess_eq_of_remaining_nonempty (e : Block V r) (c : ℕ → ℝ) (n : ℕ)
    (hR : (remainingCliques r H (trajectoryCliques ω n)).Nonempty)
    (he : e ∉ cliqueSupport r (trajectoryCliques ω n)) :
    frozenEdgeProcess H e c n ω =
      (((remainingCliques r H (trajectoryCliques ω n)).filter
        fun Q => e.val ⊆ Q.val).card : ℝ) - c n :=
  frozenEdgeProcess_eq_of_alive H e c ω n
    (trajectory_choices_of_remaining_nonempty H ω hsupport n hR) he

end Arxiv2411_18291.CliqueRemovalProcess
