import Arxiv.Arxiv2411_18291.RainbowCliqueCounts
import Arxiv.Arxiv2411_18291.ColouredGenerators
import Arxiv.Arxiv2411_18291.ColourProbabilityNumerics

/-!
# Polynomial candidate density for focusing

Every rainbow punctured clique lies in the union of the colour graphs.
A fixed positive coefficient and the factorial divisor can be absorbed
by an arbitrarily small loss in the density exponent.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] {q r : ℕ}

theorem rainbowPuncturedCliques_subset_permutedUnion (σ : I → Equiv.Perm V)
    (G : Hypergraph V (r + 1)) (e : Block V (r + 1)) :
    rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q ⊆
      puncturedCliques (permutedUnion σ G) e q := by
  classical
  intro Q hQ
  obtain ⟨_, heQ, c, hc⟩ := mem_filter.mp hQ
  apply (mem_puncturedCliques _ _ _).mpr
  apply (isPuncturedClique_iff _ _ _).mpr
  refine ⟨heQ, fun d hd => ?_⟩
  exact mapGraph_subset_permutedUnion σ G (c ⟨d, hd⟩) (hc ⟨d, hd⟩)

omit [Fintype I] [Fintype V] [DecidableEq V] in
theorem eventually_rainbow_clique_mainTerm_lower (q r : ℕ) {b α a : ℝ}
    (hb : 0 < b) (hgap : α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) < a) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℝ, b * (n : ℝ) ^ (-α) ≤ d →
      (n : ℝ) ^ (-a) * (n : ℝ) ^ (q - (r + 1)) ≤
        ((3 / 8 : ℝ) * d ^ (q.choose (r + 1) - 1) *
          (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial := by
  let c : ℝ := (3 / 8 : ℝ) * b ^ (q.choose (r + 1) - 1) / (q - (r + 1)).factorial
  have hc : 0 < c := by dsimp only [c]; positivity
  filter_upwards [eventually_const_mul_rpow_le (1 / c) hgap] with n hn
  intro d hd
  have hscale : (n : ℝ) ^ (-a) ≤
      c * (n : ℝ) ^ (-(α * ((q.choose (r + 1) - 1 : ℕ) : ℝ))) := by
    calc
      _ = c * ((1 / c) * (n : ℝ) ^ (-a)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hn hc.le
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ b * (n : ℝ) ^ (-α)) hd
    (q.choose (r + 1) - 1)
  have hmain : c * (n : ℝ) ^ (-(α * ((q.choose (r + 1) - 1 : ℕ) : ℝ))) *
      (n : ℝ) ^ (q - (r + 1)) ≤
      ((3 / 8 : ℝ) * d ^ (q.choose (r + 1) - 1) *
        (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial := by
    calc
      _ = ((3 / 8 : ℝ) * (b * (n : ℝ) ^ (-α)) ^ (q.choose (r + 1) - 1) *
          (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial := by
        rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n), neg_mul]
        dsimp only [c]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)) (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_right hscale (by positivity)).trans hmain

omit [Fintype V] [DecidableEq V] in
theorem eventually_coloured_punctured_clique_count (q r : ℕ) {b α a : ℝ}
    (hb : 0 < b) (hgap : α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) < a) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      b * (n : ℝ) ^ (-α) ≤ density G → ∀ σ : I → Equiv.Perm (Fin n),
      (∀ e : Block (Fin n) (r + 1),
        ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
          (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial ≤
            (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card) →
      ∀ e : Block (Fin n) (r + 1), (n : ℝ) ^ (-a) * (n : ℝ) ^ (q - (r + 1)) ≤
        (puncturedCliques (permutedUnion σ G) e q).card := by
  filter_upwards [eventually_rainbow_clique_mainTerm_lower q r hb hgap] with n hn
  intro G hd σ hcount e
  exact (hn (density G) hd).trans
    ((hcount e).trans (Nat.cast_le.mpr
      (card_le_card (rainbowPuncturedCliques_subset_permutedUnion σ G e))))

end Arxiv2411_18291
