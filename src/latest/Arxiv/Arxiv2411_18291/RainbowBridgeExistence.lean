import Arxiv.Arxiv2411_18291.RootedCliqueBridge
import Arxiv.Arxiv2411_18291.RainbowAvoidingExtensions
import Arxiv.Arxiv2411_18291.ColouredFocusingCounts
import Arxiv.Arxiv2411_18291.FrameCountNumerics

/-!
# Rainbow bridge cliques with prescribed colour avoidance

The rainbow punctured-clique count exceeds the loss from avoiding the
vertices of two fixed cliques. The bridge meets each of them precisely in
the prescribed root edge, and its other edges avoid all requested labels.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {I W : Type*} [Fintype W] [DecidableEq W] {q r t : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q}

theorem eventually_exists_avoiding_rainbow_bridge (hqr : r + 1 < q)
    {b α : ℝ} (hb : 0 < b) (hgap : α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      b * (n : ℝ) ^ (-α) ≤ density G → ∀ σ : I → Equiv.Perm (Fin n),
      RainbowAvoidingExtensionProperties S N σ G t →
      ∀ C : Finset I, C.card ≤ t → ∀ P Q : Block (Fin n) q,
      ∀ e : Block (Fin n) (r + 1), e.val ⊆ P.val → e.val ⊆ Q.val →
      ∃ R : Block (Fin n) q, e.val ⊆ R.val ∧ R.val ∩ P.val = e.val ∧
        R.val ∩ Q.val = e.val ∧
        IsRainbowAvoiding (fun i => mapGraph (σ i).toEmbedding G)
          ((cliqueEdges (r + 1) R).erase e) C := by
  classical
  let a := (1 + α * ((q.choose (r + 1) - 1 : ℕ) : ℝ)) / 2
  have ha : α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) < a := by
    dsimp only [a]
    linarith only [hgap]
  have ha1 : a < 1 := by dsimp only [a]; linarith only [hgap]
  filter_upwards [eventually_rainbow_clique_mainTerm_lower q r hb ha,
    eventually_frame_collision_bound (2 * q) (q - (r + 1)) (by omega)
      (c := 1) (by norm_num) ha1,
    eventually_ge_atTop (1 : ℕ)] with n hcount hbudget hn
  intro G hd σ hE C hC P Q e heP heQ
  let D := rainbowAvoidingPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q C
  have hD : ∀ R ∈ D, e.val ⊆ R.val := fun _ hR => (mem_filter.mp hR).2.1
  have hsize : (n : ℝ) ^ (-a) * (n : ℝ) ^ (q - (r + 1)) ≤ (D.card : ℝ) :=
    (hcount (density G) hd).trans
      (by simpa only [D, Fintype.card_fin] using (hE.punctured C hC e).le)
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have hsmall : ((2 * q : ℕ) : ℝ) * (Fintype.card (Fin n) : ℝ) ^ (q - (r + 1) - 1) ≤
      ((n : ℝ) ^ (-a) * (n : ℝ) ^ (q - (r + 1))) / 2 := by
    simpa only [Fintype.card_fin, one_mul] using hbudget
  obtain ⟨R, hR, hRP, hRQ⟩ := exists_rooted_clique_bridge D e hqr hD P Q heP heQ
    (by positivity) hsize hsmall
  exact ⟨R, hD R hR, hRP, hRQ, (mem_filter.mp hR).2.2⟩

end Arxiv2411_18291
