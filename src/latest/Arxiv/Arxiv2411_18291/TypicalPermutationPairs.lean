import Arxiv.Arxiv2411_18291.PairProbabilityBounds
import Arxiv.Arxiv2411_18291.ShiftedChooseBounds
import Arxiv.Arxiv2411_18291.CliqueCountEstimates

/-!
# Joint clique probabilities from typicality

When two cliques intersect in fewer vertices than the edge size, their
joint probability under one random permutation is at most
`(1+16*ε)*d^(2*choose(q,r))`. The proof keeps both the clique-counting
error and the finite binomial-denominator error explicit.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem count_le_relative_upper {x y μ ζ ε : ℝ} (hxy : x ≤ y)
    (hy : |y - μ| ≤ ζ * μ) (hμ : 0 ≤ μ) (hζ : ζ ≤ ε) : x ≤ (1 + ε) * μ := by
  have h := (abs_le.mp hy).2
  have he := mul_le_mul_of_nonneg_right hζ hμ
  linarith

theorem count_ratio_upper {x M D ε p : ℝ} (hM : 0 < M) (hε : 0 ≤ ε)
    (hεhalf : ε ≤ 1 / 2) (hp : 0 ≤ p) (hx : x ≤ (1 + ε) * M * p)
    (hD : (1 - ε) * M ≤ D) : x / D ≤ (1 + 4 * ε) * p := by
  have hDpos : 0 < D := (mul_pos (by linarith) hM).trans_le hD
  have hcoef : 1 + ε ≤ (1 + 4 * ε) * (1 - ε) := by nlinarith
  apply (div_le_iff₀ hDpos).mpr
  calc
    x ≤ (1 + ε) * M * p := hx
    _ ≤ ((1 + 4 * ε) * (1 - ε)) * M * p :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hM.le) hp
    _ = ((1 + 4 * ε) * p) * ((1 - ε) * M) := by ring
    _ ≤ ((1 + 4 * ε) * p) * D := mul_le_mul_of_nonneg_left hD (by positivity)

theorem cliqueMainTerm_small_root (n d : ℝ) (q r s : ℕ) (hsr : s < r) :
    cliqueMainTerm n d q r s = (n ^ (q - s) / (q - s).factorial) * d ^ q.choose r := by
  simp only [cliqueMainTerm, Nat.choose_eq_zero_of_lt hsr, Nat.sub_zero]
  ring

variable {V : Type*} [Fintype V] [DecidableEq V] {q r h s : ℕ}
variable [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)]

theorem IsTypical.permuted_clique_pair_probability_le
    {K : Hypergraph V (r + 1)} {c η ε : ℝ} (hT : IsTypical K c h)
    (hqh : q.choose (r + 1) ≤ h) (hcη : c ≤ η) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hsize : (q : ℝ) ≤ (η - c) * (Fintype.card V * density K ^ q.choose (r + 1)))
    (hn : 0 < Fintype.card V) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (herror : η * q * 2 ^ q ≤ ε)
    (hchoose : ∀ a ≤ q, ∀ b ≤ q,
      (1 - ε) * (Fintype.card V : ℝ) ^ b / b.factorial ≤
        ((Fintype.card V - a).choose b : ℝ))
    (P : IntersectingBlockPair V q q s) (hsr : s < r + 1)
    (D E : Finset (Block V q)) (hD : D ⊆ cliqueFamily K q) (hE : E ⊆ cliqueFamily K q) :
    (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real
      {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding E} ≤
      (1 + 16 * ε) * density K ^ (2 * q.choose (r + 1)) := by
  let p := density K ^ q.choose (r + 1)
  let M0 := (Fintype.card V : ℝ) ^ q / q.factorial
  let Ms := (Fintype.card V : ℝ) ^ (q - s) / (q - s).factorial
  let L := (1 + ε) * Ms * p
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hp : 0 ≤ p := pow_nonneg (density_nonneg K) _
  have hM0 : 0 < M0 := by dsimp [M0]; positivity
  have hMs : 0 < Ms := by dsimp [Ms]; positivity
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hsq := P.parameters.1
  have htotal : (D.card : ℝ) ≤ (1 + ε) * M0 * p := by
    have hc := count_le_relative_upper (x := (D.card : ℝ)) (by exact_mod_cast card_le_card hD)
      (hT.cliqueFamily_relative hqh hcη hη hη1 hsize)
      (cliqueMainTerm_nonneg hnR.le (density_nonneg K) q (r + 1) 0) herror
    rw [cliqueMainTerm_small_root _ _ _ _ _ (Nat.succ_pos r), Nat.sub_zero] at hc
    simpa only [mul_assoc] using hc
  have hroot (I : Block V s) : ((E.filter fun Q => I.val ⊆ Q.val).card : ℝ) ≤ L := by
    have hsub : ((E.filter fun Q => I.val ⊆ Q.val).card : ℝ) ≤
        (((cliqueFamily K q).filter fun Q => I.val ⊆ Q.val).card : ℝ) := by
      exact_mod_cast card_le_card (filter_subset_filter (fun Q : Block V q => I.val ⊆ Q.val) hE)
    have hc := count_le_relative_upper hsub
      (hT.cliqueFamily_small_root_relative hqh hcη hη hη1 hsize I hsq hsr)
      (cliqueMainTerm_nonneg hnR.le (density_nonneg K) q (r + 1) s) herror
    rw [cliqueMainTerm_small_root _ _ _ _ _ hsr] at hc
    simpa only [L, mul_assoc] using hc
  have hden0 : (1 - ε) * M0 ≤ ((Fintype.card V).choose q : ℝ) := by
    simpa only [M0, Nat.sub_zero, mul_div_assoc] using hchoose 0 (Nat.zero_le q) q le_rfl
  have hdens : (1 - ε) * Ms ≤ ((Fintype.card V - q).choose (q - s) : ℝ) := by
    simpa only [Ms, mul_div_assoc] using hchoose q le_rfl (q - s) (Nat.sub_le _ _)
  have hratio0 := count_ratio_upper hM0 hε hεhalf hp htotal hden0
  have hratios := count_ratio_upper hMs hε hεhalf hp (show L ≤ (1 + ε) * Ms * p from le_rfl) hdens
  calc
    _ ≤ (D.card / ((Fintype.card V).choose q : ℝ)) *
        (L / ((Fintype.card V - q).choose (q - s) : ℝ)) :=
      uniform_permuted_pair_probability_le P D E hroot
    _ ≤ ((1 + 4 * ε) * p) * ((1 + 4 * ε) * p) :=
      mul_le_mul hratio0 hratios (div_nonneg hL0 (Nat.cast_nonneg _)) (by positivity)
    _ ≤ (1 + 16 * ε) * p ^ 2 := by
      have hcoef : (1 + 4 * ε) ^ 2 ≤ 1 + 16 * ε := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg p)
      nlinarith only [hm]
    _ = _ := by
      dsimp only [p]
      rw [← pow_mul, Nat.mul_comm (q.choose (r + 1)) 2]

end Arxiv2411_18291
