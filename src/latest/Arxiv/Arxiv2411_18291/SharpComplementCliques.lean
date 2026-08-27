import Arxiv.Arxiv2411_18291.RootedCliqueAdditiveLoss
import Arxiv.Arxiv2411_18291.NearCompleteCliqueCounts
import Mathlib.Topology.Instances.Nat

/-! # Rooted clique counts with the summed complement loss -/

open Finset Filter
open scoped BigOperators Topology

noncomputable section

namespace Arxiv2411_18291

theorem rootedCliques_relative_error_of_complement_sum {V : Type*} [Fintype V]
    [DecidableEq V] {q r a : ℕ} {G : Hypergraph V (r + 1)} {θ ε : ℝ}
    (hG : IsGraphBounded (complete V (r + 1) \ G) θ) (hθ : 0 ≤ θ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hn : 0 < Fintype.card V) (I : Block V a) (haq : a ≤ q)
    (herror : (q : ℝ) * (q - a : ℕ) + (q.choose (r + 1) : ℝ) * θ * Fintype.card V ≤
      ε * Fintype.card V) :
    |((rootedCliques G I q).card : ℝ) -
        (Fintype.card V : ℝ) ^ (q - a) / (q - a).factorial| ≤
      ε * ((Fintype.card V : ℝ) ^ (q - a) / (q - a).factorial) := by
  let N : ℝ := Fintype.card V
  let b : ℕ → ℝ := fun t => q + ((a + t).choose r : ℝ) * θ * N
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast hn
  have hb : ∀ t, 0 ≤ b t := by intro t; dsimp only [b]; positivity
  have hsumformula (t : ℕ) : (∑ i ∈ range t, b i) =
      (t : ℝ) * q + ((∑ i ∈ range t, (a + i).choose r : ℕ) : ℝ) * θ * N := by
    simp only [b, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_mul,
      Nat.cast_sum]
  have hsum : ∑ i ∈ range (q - a), b i ≤ ε * N := by
    rw [hsumformula, sum_choose_extension, Nat.add_sub_of_le haq]
    have hc : ((q.choose (r + 1) - a.choose (r + 1) : ℕ) : ℝ) ≤ q.choose (r + 1) := by
      exact_mod_cast Nat.sub_le (q.choose (r + 1)) (a.choose (r + 1))
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hθ) hN.le
    change (q : ℝ) * (q - a : ℕ) + (q.choose (r + 1) : ℝ) * θ * N ≤ ε * N at herror
    linarith only [hm, herror]
  have htotal : ∑ i ∈ range (q - a), b i ≤ N :=
    hsum.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hε1 hN.le)
  have hstep (t : ℕ) (ht : a + t < q) (U : Block V (a + t))
      (_ : U ∈ rootedCliques G I (a + t)) : N - b t ≤ (cliqueNextVertices G U).card := by
    have hh := cliqueNextVertices_lower_of_complement_bounded hG U
    have hk : (a + t : ℕ) ≤ (q : ℝ) := by exact_mod_cast ht.le
    dsimp only [b, N]
    linarith only [hh, hk]
  have hcount := rootedCliques_factorial_lower_additive G I q hN b hb htotal hstep
    (q - a) (by omega)
  rw [Nat.add_sub_of_le haq] at hcount
  have hratio : (∑ i ∈ range (q - a), b i) / N ≤ ε := (div_le_iff₀ hN).mpr hsum
  have hlower : (1 - ε) * N ^ (q - a) ≤
      ((q - a).factorial : ℝ) * (rootedCliques G I q).card :=
    (mul_le_mul_of_nonneg_right (sub_le_sub_left hratio 1) (pow_nonneg hN.le _)).trans hcount
  have hfact : (0 : ℝ) < (q - a).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hlo : (1 - ε) * N ^ (q - a) / (q - a).factorial ≤ (rootedCliques G I q).card :=
    (div_le_iff₀ hfact).mpr (hlower.trans_eq (mul_comm _ _))
  have hhi := rootedCliques_card_upper G I haq
  change ((rootedCliques G I q).card : ℝ) ≤ N ^ (q - a) / (q - a).factorial at hhi
  change |((rootedCliques G I q).card : ℝ) - N ^ (q - a) / (q - a).factorial| ≤ _
  have hlo' : N ^ (q - a) / (q - a).factorial -
      ε * (N ^ (q - a) / (q - a).factorial) ≤ (rootedCliques G I q).card := by
    convert hlo using 1
    ring
  have hnonneg : 0 ≤ ε * (N ^ (q - a) / (q - a).factorial) := by positivity
  rw [abs_le]
  constructor <;> linarith only [hlo', hhi, hnonneg]

theorem eventually_rootedClique_count_of_complement_margin (q r a : ℕ) (haq : a ≤ q)
    {θ ε : ℝ} (hθ : 0 ≤ θ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmargin : (q.choose (r + 1) : ℝ) * θ < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      IsGraphBounded (complete (Fin n) (r + 1) \ G) θ →
      ∀ I : Block (Fin n) a,
        |((rootedCliques G I q).card : ℝ) - (n : ℝ) ^ (q - a) / (q - a).factorial| ≤
          ε * ((n : ℝ) ^ (q - a) / (q - a).factorial) := by
  have hgap : 0 < ε - (q.choose (r + 1) : ℝ) * θ := sub_pos.mpr hmargin
  have hlarge := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop ((q : ℝ) * (q - a : ℕ) / (ε - (q.choose (r + 1) : ℝ) * θ)))
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hlinear := (div_le_iff₀ hgap).mp hn
  intro G hG I
  have hnum : (q : ℝ) * (q - a : ℕ) +
      (q.choose (r + 1) : ℝ) * θ * Fintype.card (Fin n) ≤ ε * Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]
    nlinarith only [hlinear]
  simpa only [Fintype.card_fin] using rootedCliques_relative_error_of_complement_sum
    hG hθ hε.le hε1 (by simpa only [Fintype.card_fin] using (show 0 < n by omega)) I haq hnum

end Arxiv2411_18291
