import ErdosProblems.Erdos547.DegreeSurplusNumbers

/-!
# Constants chosen before applying the regularity lemma
-/

namespace Erdos547

structure EmbeddingConstants (a : ℝ) where
  treeEta : ℝ
  slack : ℝ
  density : ℝ
  theta : ℝ
  delta : ℝ
  beta : ℝ
  epsilon : ℝ
  treeEta_pos : 0 < treeEta
  treeEta_le : treeEta ≤ 1 / 10
  treeEta_surplus : treeEta ≤ a / 10000
  slack_pos : 0 < slack
  slack_le : slack ≤ 1 / 100
  slack_surplus : slack ≤ a / 1000
  density_pos : 0 < density
  theta_pos : 0 < theta
  delta_pos : 0 < delta
  beta_pos : 0 < beta
  beta_slack : beta ≤ slack / 100
  beta_le : beta ≤ 1 / 4
  epsilon_pos : 0 < epsilon
  epsilon_le : epsilon ≤ 1 / 2
  epsilon_delta : epsilon ≤ delta ^ 2
  clean : epsilon + 2 * delta < 1
  high_fraction : epsilon + delta < a
  degree_margin : 2 * epsilon ≤ density
  embedding_margin : 8 * epsilon ≤ density ^ 2 * (beta / 4)
  private_margin : epsilon ≤ slack * theta
  buffer_margin : epsilon ≤ beta / 4
  theta_margin : epsilon ≤ theta / 2
  root_margin : 48 * epsilon ≤ theta * beta
  seed_margin : 3 * epsilon + 2 * delta ≤ density
  exception_margin : theta + 4 * delta ≤ slack * treeEta / 4
  degree_loss : 8 * epsilon + 4 * density + 2 * delta ≤ a / 8

theorem nonempty_embedding_constants (a : ℝ) (ha : 0 < a) (haone : a ≤ 1) :
    Nonempty (EmbeddingConstants a) := by
  let s := a / 1000
  let η := a / 10000
  let θ := s * η / 1000
  let δ := θ / 100
  let ε := min (δ ^ 2) (min (s * θ) (min (θ * δ) (s ^ 2 * δ))) / 1000
  have hs : 0 < s := by dsimp [s]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsle : s ≤ 1 / 1000 := by dsimp only [s]; linarith only [haone]
  have hηle : η ≤ 1 / 10000 := by dsimp only [η]; linarith only [haone]
  have hθle : θ ≤ s / 1000 := by
    have hh := mul_le_mul_of_nonneg_left (show η ≤ 1 by linarith only [hηle]) hs.le
    dsimp only [θ]
    nlinarith only [hh]
  have hδle : δ ≤ s / 100000 := by dsimp only [δ]; linarith only [hθle]
  have hδone : δ ≤ 1 := by linarith only [hδle, hsle]
  have heδ : ε ≤ δ ^ 2 / 1000 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hesθ : ε ≤ s * θ / 1000 :=
    div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  have heθδ : ε ≤ θ * δ / 1000 :=
    div_le_div_of_nonneg_right
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) (by norm_num)
  have hesδ : ε ≤ s ^ 2 * δ / 1000 :=
    div_le_div_of_nonneg_right
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) (by norm_num)
  have hed : ε ≤ δ / 1000 := by
    have hh : δ ^ 2 ≤ δ := by nlinarith only [hδone, hδ.le]
    linarith only [heδ, hh]
  have heδweak : ε ≤ δ := by linarith only [hed, hδ.le]
  have hsδ : 3 * ε + 2 * δ ≤ s := by linarith only [heδweak, hδle, hs.le]
  have heprivate : ε ≤ s * θ := by
    have hh := mul_pos hs hθ
    linarith only [hesθ, hh]
  have heembed : 8 * ε ≤ s ^ 2 * (δ / 4) := by
    have hh := mul_nonneg (sq_nonneg s) hδ.le
    nlinarith only [hesδ, hh]
  have heroot : 48 * ε ≤ θ * δ := by
    have hh := mul_pos hθ hδ
    linarith only [heθδ, hh]
  have hclean : ε + 2 * δ < 1 := by linarith only [heδweak, hδle, hsle]
  have hhigh : ε + δ < a := by
    have hsa : 1000 * s = a := by dsimp only [s]; ring
    linarith only [heδweak, hδle, hsa, ha]
  have hexception : θ + 4 * δ ≤ s * η / 4 := by
    have ht : 1000 * θ = s * η := by dsimp only [θ]; ring
    have hd : 100 * δ = θ := by dsimp only [δ]; ring
    linarith only [ht, hd, hθ.le]
  have hloss : 8 * ε + 4 * s + 2 * δ ≤ a / 8 := by
    have hsa : 1000 * s = a := by dsimp only [s]; ring
    linarith only [heδweak, hδle, hsa, ha.le]
  refine ⟨{
    treeEta := η
    slack := s
    density := s
    theta := θ
    delta := δ
    beta := δ
    epsilon := ε
    treeEta_pos := hη
    treeEta_le := by linarith only [hηle]
    treeEta_surplus := le_rfl
    slack_pos := hs
    slack_le := by linarith only [hsle]
    slack_surplus := le_rfl
    density_pos := hs
    theta_pos := hθ
    delta_pos := hδ
    beta_pos := hδ
    beta_slack := by linarith only [hδle, hs.le]
    beta_le := by linarith only [hδle, hsle]
    epsilon_pos := hε
    epsilon_le := by linarith only [heδweak, hδle, hsle]
    epsilon_delta := by nlinarith only [heδ, sq_nonneg δ]
    clean := hclean
    high_fraction := hhigh
    degree_margin := by linarith only [hsδ, hε.le, hδ.le]
    embedding_margin := heembed
    private_margin := heprivate
    buffer_margin := by linarith only [hed, hδ.le]
    theta_margin := by dsimp only [δ] at hed; linarith only [hed, hθ.le]
    root_margin := heroot
    seed_margin := hsδ
    exception_margin := hexception
    degree_loss := hloss
  }⟩

end Erdos547

#print axioms Erdos547.nonempty_embedding_constants
