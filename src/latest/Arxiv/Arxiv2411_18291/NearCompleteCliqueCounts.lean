import Arxiv.Arxiv2411_18291.NearCompleteCliqueExtensions

/-!
# Quantitative rooted clique counts with a bounded complement

Iterate the extension bound and retain the exact factorial normalization.
A finite numerical condition yields any desired relative error against
`n^(q-a)/(q-a)!`, uniformly over all roots of size `a`.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r a : ℕ}

omit [DecidableEq V] in
theorem rootedCliques_card_upper (G : Hypergraph V (r + 1)) (I : Block V a) (haq : a ≤ q) :
    ((rootedCliques G I q).card : ℝ) ≤
      (Fintype.card V : ℝ) ^ (q - a) / (q - a).factorial := by
  classical
  have hsub : rootedCliques G I q ⊆ univ.filter (fun Q : Block V q => I.val ⊆ Q.val) := by
    intro Q hQ
    exact mem_filter.mpr ⟨mem_univ _, ((mem_rootedCliques _ _ _).mp hQ).1⟩
  have hcard : (univ.filter fun Q : Block V q => I.val ⊆ Q.val).card =
      (Fintype.card V - a).choose (q - a) := by
    have h := card_blocks_between (r := q) I.val univ (subset_univ _)
      (by simpa only [I.property] using haq)
    simpa only [subset_univ, and_true, card_univ, I.property] using h
  have hcount : ((rootedCliques G I q).card : ℝ) ≤
      ((Fintype.card V - a).choose (q - a) : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans_eq hcard
  exact hcount.trans (shifted_choose_upper (Fintype.card V) a (q - a))

theorem rootedCliques_card_lower_of_complement_bounded {G : Hypergraph V (r + 1)}
    {θ ε : ℝ} (hG : IsGraphBounded (complete V (r + 1) \ G) θ)
    (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (I : Block V a) (haq : a ≤ q)
    (hsize : (q : ℝ) + (q.choose r : ℝ) * θ * Fintype.card V ≤ Fintype.card V)
    (herror : (q - a : ℕ) * ((q : ℝ) + (q.choose r : ℝ) * θ * Fintype.card V) ≤
      ε * Fintype.card V) :
    (1 - ε) * (Fintype.card V : ℝ) ^ (q - a) / (q - a).factorial ≤
      (rootedCliques G I q).card := by
  let M : ℝ := q + (q.choose r : ℝ) * θ * Fintype.card V
  let L : ℝ := Fintype.card V - M
  have hL : 0 ≤ L := sub_nonneg.mpr hsize
  have hstep (k : ℕ) (_ : a ≤ k) (hk : k < q)
      (U : Block V k) (_ : U ∈ rootedCliques G I k) :
      L * (1 : ℝ) ^ k.choose r ≤ (cliqueNextVertices G U).card := by
    rw [one_pow, mul_one]
    have h := cliqueNextVertices_lower_of_complement_bounded hG U
    have hk' : (k : ℝ) ≤ q := by exact_mod_cast hk.le
    have hchoose : (k.choose r : ℝ) ≤ q.choose r := by
      exact_mod_cast Nat.choose_le_choose r hk.le
    have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hchoose hθ)
      (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ _)
    dsimp only [L, M]
    linarith only [h, hk', hp]
  have hcount := rootedCliques_factorial_lower G I q hL (by norm_num : (0 : ℝ) ≤ 1)
    hstep (q - a) (by omega)
  rw [Nat.add_sub_of_le haq, one_pow, mul_one] at hcount
  have hp := pow_sub_relative_lower (N := (Fintype.card V : ℝ)) (M := M)
    (by dsimp only [M]; positivity) hsize hε (q - a) herror
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos (q - a)))).mpr
  exact (hp.trans hcount).trans_eq (mul_comm _ _)

theorem rootedCliques_relative_error_of_complement_bounded {G : Hypergraph V (r + 1)}
    {θ ε : ℝ} (hG : IsGraphBounded (complete V (r + 1) \ G) θ)
    (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (I : Block V a) (haq : a ≤ q)
    (hsize : (q : ℝ) + (q.choose r : ℝ) * θ * Fintype.card V ≤ Fintype.card V)
    (herror : (q - a : ℕ) * ((q : ℝ) + (q.choose r : ℝ) * θ * Fintype.card V) ≤
      ε * Fintype.card V) :
    |((rootedCliques G I q).card : ℝ) -
        (Fintype.card V : ℝ) ^ (q - a) / (q - a).factorial| ≤
      ε * ((Fintype.card V : ℝ) ^ (q - a) / (q - a).factorial) := by
  have hlo := rootedCliques_card_lower_of_complement_bounded hG hθ hε I haq hsize herror
  have hhi := rootedCliques_card_upper G I haq
  have hnonneg : 0 ≤ ε * ((Fintype.card V : ℝ) ^ (q - a) / (q - a).factorial) := by positivity
  have hlo' : (Fintype.card V : ℝ) ^ (q - a) / (q - a).factorial -
      ε * ((Fintype.card V : ℝ) ^ (q - a) / (q - a).factorial) ≤
        (rootedCliques G I q).card := by
    convert hlo using 1
    ring
  rw [abs_le]
  constructor <;> linarith only [hlo', hhi, hnonneg]

end Arxiv2411_18291
