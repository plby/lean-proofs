import Mathlib
import ErdosProblems.Erdos550.Basic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Kővári–Sós–Turán theorem (usable quantitative form)

This file proves the Kővári–Sós–Turán theorem in the form used by the paper
*A Resolution of Erdős Problem 550* (E. Li): for fixed `a, b ≥ 1`,
`ex(N, K_{a,b}) = o(N²)`.

The proof is elementary:

* `Erdos550.commonNbrs G S` — the set of common neighbours of a vertex set `S`.
* `Erdos550.commonNbrs_card_le` — in a `K_{a,b}`-free graph, every `a`-set has
  at most `b - 1` common neighbours (otherwise we build a copy of `K_{a,b}`).
* `Erdos550.kst_double_count` — the double-counting inequality
  `∑_v C(d(v), a) ≤ (b-1)·C(N, a)`.
* `Erdos550.kst_star_maxDegree` — the `a = 1` special case: a `K_{1,b}`-free
  graph has maximum degree at most `b - 1`.
* `Erdos550.kovari_sos_turan` — the asymptotic `o(N²)` edge bound.
-/

open SimpleGraph Finset

namespace Erdos550

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The set of common neighbours of a vertex set `S`: vertices adjacent to every
member of `S`. -/
def commonNbrs (S : Finset V) : Finset V :=
  Finset.univ.filter (fun v => ∀ u ∈ S, G.Adj u v)

@[simp] lemma mem_commonNbrs {S : Finset V} {v : V} :
    v ∈ commonNbrs G S ↔ ∀ u ∈ S, G.Adj u v := by
  simp [commonNbrs]

/-- `S ⊆ N(v)` exactly says `v` is a common neighbour of `S`. -/
lemma subset_neighborFinset_iff_mem_commonNbrs {S : Finset V} {v : V} :
    S ⊆ G.neighborFinset v ↔ v ∈ commonNbrs G S := by
  simp only [mem_commonNbrs, Finset.subset_iff, mem_neighborFinset]
  constructor
  · intro h u hu; exact (h hu).symm
  · intro h u hu; exact (h u hu).symm

/-
In a `K_{a,b}`-free graph, every `a`-set has at most `b - 1` common
neighbours: otherwise the `a`-set together with `b` of its common neighbours
forms a copy of `K_{a,b}`.
-/
theorem commonNbrs_card_le {a b : ℕ} (hb : 1 ≤ b)
    (hfree : (Kbip a b).Free G) {S : Finset V} (hS : S.card = a) :
    (commonNbrs G S).card ≤ b - 1 := by
  contrapose! hfree;
  obtain ⟨T, hT⟩ : ∃ T : Finset V, T ⊆ commonNbrs G S ∧ T.card = b := by
    exact Finset.exists_subset_card_eq ( by omega );
  have h_complete_bipartite : G.IsCompleteBetween (S : Set V) (T : Set V) := by
    intro v hv w hw; have := hT.1 hw; simp_all +decide [ commonNbrs ] ;
  have h_disjoint : Disjoint (S : Set V) (T : Set V) := by
    simp_all +decide only [disjoint_coe];
    exact Finset.disjoint_left.mpr fun x hxS hxT => by
      have hxx : G.Adj x x := (mem_commonNbrs (G := G)).mp (hT.1 hxT) x hxS
      exact hxx.ne rfl
  have := @SimpleGraph.Copy.completeBipartiteGraph V;
  exact ⟨ this S T ( by simp +decide [ hS ] ) ( by simp +decide [ hT.2 ] ) h_complete_bipartite ⟩

/-
**Kővári–Sós–Turán double counting.**  In a `K_{a,b}`-free graph on `N`
vertices, `∑_v C(d(v), a) ≤ (b-1)·C(N, a)`.
-/
theorem kst_double_count {a b : ℕ} (hb : 1 ≤ b)
    (hfree : (Kbip a b).Free G) :
    ∑ v, (G.degree v).choose a ≤ (b - 1) * (Fintype.card V).choose a := by
  -- Apply the lemma that allows us to rewrite the sum as a double sum.
  have h_double_sum : ∑ v : V, (G.degree v).choose a = ∑ S ∈ Finset.powersetCard a (Finset.univ : Finset V), (Finset.filter (fun v => S ⊆ G.neighborFinset v) (Finset.univ : Finset V)).card := by
    simp +decide only [card_filter];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro v hv
    have h_card : (Finset.powersetCard a (G.neighborFinset v)).card = (G.degree v).choose a := by
      simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
    rw [ ← h_card, ← Finset.card_filter ];
    congr 1 with x ; aesop;
  -- By the lemma `commonNbrs_card_le`, each term in the sum is at most `b - 1`.
  have h_term_le : ∀ S ∈ Finset.powersetCard a (Finset.univ : Finset V), (Finset.filter (fun v => S ⊆ G.neighborFinset v) (Finset.univ : Finset V)).card ≤ b - 1 := by
    intro S hS;
    convert! commonNbrs_card_le G hb hfree ( Finset.mem_powersetCard.mp hS |>.2 ) using 1;
    exact congr_arg Finset.card ( Finset.ext fun x => by simp +decide [ subset_neighborFinset_iff_mem_commonNbrs ] );
  exact h_double_sum.symm ▸ le_trans ( Finset.sum_le_sum h_term_le ) ( by simp +decide [ mul_comm, Finset.card_univ ] )

/-
The `a = 1` special case: a `K_{1,b}`-free graph has maximum degree at most
`b - 1`.
-/
theorem kst_star_maxDegree {b : ℕ} (hb : 1 ≤ b)
    (hfree : (Kbip 1 b).Free G) (v : V) :
    G.degree v ≤ b - 1 := by
  convert! commonNbrs_card_le G hb hfree _;
  rotate_left;
  exact { v };
  · simp +decide;
  · exact congr_arg Finset.card ( by ext; simp +decide [ commonNbrs ] )

end Erdos550

namespace Erdos550

/-
Analytic core of the Kővári–Sós–Turán asymptotic: the choose-ratio that
bounds the number of high-degree vertices is eventually `≤ ε' N`, so multiplied by
`N` it is `≤ ε' N²`.  Here `t = ⌈ε' N⌉` is the degree threshold.
-/
lemma kst_ratio_aux (a b : ℕ) (ha : 1 ≤ a) (ε' : ℝ) (hε' : 0 < ε') :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      (b - 1 : ℝ) * (N.choose a : ℝ) / ((⌈ε' * (N : ℝ)⌉₊).choose a : ℝ) * (N : ℝ)
        ≤ ε' * (N : ℝ) ^ 2 := by
  by_contra! h_contra;
  -- Choose $N$ large enough such that for all $N \geq N₁$:
  -- (i) $\epsilon' N - a \geq \epsilon' N / 2$ (holds when $N \geq 2a / \epsilon'$);
  -- (ii) $a \leq t$ (holds when $\epsilon' N \geq a$, i.e., $N \geq a / \epsilon'$), so that $t.choose a > 0$;
  -- (iii) $(b - 1) * (2 / \epsilon')^a \leq \epsilon' N$ (holds when $N \geq (b-1)*(2 / \epsilon')^a / \epsilon'$).
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ N ≥ N₁, ε' * (N : ℝ) - a ≥ ε' * (N : ℝ) / 2 ∧ a ≤ ⌈ε' * (N : ℝ)⌉₊ ∧ (b - 1) * (2 / ε')^a ≤ ε' * (N : ℝ) := by
    refine' ⟨ ⌈ ( 2 * a ) / ε'⌉₊ + ⌈ ( a : ℝ ) / ε'⌉₊ + ⌈ ( ( b - 1 ) * ( 2 / ε' ) ^ a ) / ε'⌉₊ + 1, fun N hN => ⟨ _, _, _ ⟩ ⟩;
    · nlinarith [ Nat.le_ceil ( 2 * a / ε' ), mul_div_cancel₀ ( 2 * a : ℝ ) hε'.ne', show ( N : ℝ ) ≥ ⌈2 * a / ε'⌉₊ + ⌈a / ε'⌉₊ + ⌈ ( b - 1 ) * ( 2 / ε' ) ^ a / ε'⌉₊ + 1 by exact_mod_cast hN ];
    · exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ Nat.le_ceil ( ε' * N ), Nat.le_ceil ( ( a : ℝ ) / ε' ), mul_div_cancel₀ ( a : ℝ ) hε'.ne', show ( N : ℝ ) ≥ ⌈ ( a : ℝ ) / ε'⌉₊ + 1 by norm_cast; linarith ] ;
    · nlinarith [ Nat.le_ceil ( ( ( b - 1 ) * ( 2 / ε' ) ^ a ) / ε' ), mul_div_cancel₀ ( ( b - 1 : ℝ ) * ( 2 / ε' ) ^ a ) hε'.ne', show ( N : ℝ ) ≥ ⌈ ( ( b - 1 ) * ( 2 / ε' ) ^ a ) / ε'⌉₊ + 1 by exact_mod_cast by linarith ];
  -- Therefore, the ratio $\frac{N.choose a}{t.choose a} \leq \left(\frac{N}{\epsilon' N - a}\right)^a \leq \left(\frac{N}{\epsilon' N / 2}\right)^a = \left(\frac{2}{\epsilon'}\right)^a$.
  have h_ratio : ∀ N ≥ N₁, ((N.choose a : ℝ) / ((Nat.ceil (ε' * (N : ℝ))).choose a)) ≤ (2 / ε')^a := by
    -- Using the bounds from `hN₁`, we can derive the inequality for the ratio.
    intros N hN
    have h_ratio_bound : ((N.choose a : ℝ) / ((Nat.ceil (ε' * (N : ℝ))).choose a)) ≤ ((N : ℝ) ^ a / (Nat.factorial a)) / (((ε' * (N : ℝ) - a) ^ a / (Nat.factorial a))) := by
      gcongr;
      · exact div_pos ( pow_pos ( by nlinarith [ hN₁ N hN, show ( a : ℝ ) ≥ 1 by norm_cast ] ) _ ) ( by positivity );
      · rw [ le_div_iff₀ ( by positivity ) ];
        rw_mod_cast [ Nat.mul_comm ];
        rw [ ← Nat.descFactorial_eq_factorial_mul_choose ] ; exact Nat.descFactorial_le_pow _ _;
      · have h_ratio_bound : ((Nat.ceil (ε' * (N : ℝ))).descFactorial a : ℝ) ≥ ((ε' * (N : ℝ) - a) ^ a) := by
          have h_ratio_bound : ((Nat.ceil (ε' * (N : ℝ))).descFactorial a : ℝ) ≥ (∏ i ∈ Finset.range a, (ε' * (N : ℝ) - i)) := by
            rw [ Nat.descFactorial_eq_prod_range ];
            push_cast;
            exact Finset.prod_le_prod ( fun _ _ => sub_nonneg_of_le <| by nlinarith [ hN₁ N hN, show ( ↑‹ℕ› : ℝ ) + 1 ≤ a by norm_cast; linarith [ Finset.mem_range.mp ‹_› ] ] ) fun i hi => by rw [ Nat.cast_sub <| by linarith [ Finset.mem_range.mp hi, hN₁ N hN ] ] ; exact sub_le_sub_right ( Nat.le_ceil _ ) _;
          refine le_trans ?_ h_ratio_bound;
          exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => sub_nonneg.mpr <| by nlinarith [ hN₁ N hN, show ( a : ℝ ) ≥ 1 by norm_cast ] ) fun i hi => show ( ε' * N - i : ℝ ) ≥ ε' * N - a by linarith [ show ( i : ℝ ) + 1 ≤ a by norm_cast; linarith [ Finset.mem_range.mp hi ] ] );
        convert! div_le_div_of_nonneg_right h_ratio_bound ( Nat.cast_nonneg ( a.factorial ) ) using 1;
        rw [ Nat.descFactorial_eq_factorial_mul_choose ] ; norm_num [ Nat.factorial_ne_zero ];
    refine le_trans h_ratio_bound ?_;
    field_simp;
    rw [ ← div_pow ];
    exact pow_le_pow_left₀ ( div_nonneg ( Nat.cast_nonneg _ ) ( by nlinarith [ hN₁ N hN ] ) ) ( by rw [ div_le_div_iff₀ ] <;> nlinarith [ hN₁ N hN, show ( a : ℝ ) ≥ 1 by norm_cast ] ) _;
  obtain ⟨ N, hN₁, hN₂ ⟩ := h_contra N₁ ; specialize h_ratio N hN₁ ; specialize hN₁ ; specialize hN₂ ; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
  rename_i h; specialize h N hN₁; rcases b with ( _ | _ | b ) <;> norm_num at *;
  · nlinarith [ show ( 0 : ℝ ) ≤ N * ( N.choose a * ( ⌈ε' * N⌉₊.choose a : ℝ ) ⁻¹ ) by positivity ];
  · exact hN₂.not_ge ( by positivity );
  · nlinarith [ mul_inv_cancel₀ ( ne_of_gt hε' ), mul_le_mul_of_nonneg_left h_ratio ( Nat.cast_nonneg N ) ]

/-
**Kővári–Sós–Turán, asymptotic form.**  For fixed `a, b ≥ 1` and every
`ε > 0`, every sufficiently large `K_{a,b}`-free graph has at most `ε N²` edges,
i.e. `ex(N, K_{a,b}) = o(N²)`.
-/
theorem kovari_sos_turan (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      (Kbip a b).Free G → N₀ ≤ Fintype.card V →
      (G.edgeFinset.card : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  -- Set `ε' = ε/4`.
  set ε' : ℝ := ε / 4 with hε'_def;
  -- Set `N₀ = N₁ + ⌈a/ε'⌉₊ + ⌈2/(3*ε)⌉₊ + 1` (large enough).
  obtain ⟨N₁, hN₁⟩ := kst_ratio_aux a b ha ε' (by
  positivity)
  use N₁ + Nat.ceil (a / ε') + Nat.ceil (2 / (3 * ε)) + 1;
  intro V _ _ G _ hfree hN₀
  set N := Fintype.card V
  set t := Nat.ceil (ε' * (N : ℝ))
  set m := (Finset.univ.filter (fun v => t ≤ G.degree v)).card
  have ht : a ≤ t := by
    refine Nat.le_of_lt_succ ?_;
    exact Nat.lt_succ_of_le ( Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ Nat.le_ceil ( ( a : ℝ ) / ε' ), Nat.le_ceil ( 2 / ( 3 * ε ) ), mul_div_cancel₀ ( a : ℝ ) ( show ( ε' : ℝ ) ≠ 0 by positivity ), mul_div_cancel₀ ( 2 : ℝ ) ( show ( 3 * ε : ℝ ) ≠ 0 by positivity ), show ( N : ℝ ) ≥ N₁ + ⌈ ( a : ℝ ) / ε'⌉₊ + ⌈2 / ( 3 * ε ) ⌉₊ + 1 by exact_mod_cast hN₀, mul_div_cancel₀ ( ε' * ( N : ℝ ) ) ( show ( 1 : ℝ ) ≠ 0 by positivity ), Nat.le_ceil ( ε' * ( N : ℝ ) ) ] )
  have hm : m * (t.choose a : ℝ) ≤ (b - 1 : ℝ) * (N.choose a : ℝ) := by
    have hm : ∑ v ∈ Finset.univ.filter (fun v => t ≤ G.degree v), (G.degree v).choose a ≤ (b - 1 : ℕ) * (N.choose a : ℕ) := by
      exact le_trans ( Finset.sum_le_sum_of_subset ( Finset.filter_subset _ _ ) ) ( by simpa using! kst_double_count G hb hfree );
    norm_cast;
    exact le_trans ( by simpa using! Finset.sum_le_sum fun x ( hx : x ∈ Finset.filter ( fun v => t ≤ G.degree v ) Finset.univ ) => Nat.choose_le_choose a <| Finset.mem_filter.mp hx |>.2 ) hm
  have h_sum : ∑ v, G.degree v ≤ N * t + m * N := by
    have h_sum : ∑ v, G.degree v ≤ ∑ v ∈ Finset.univ.filter (fun v => G.degree v < t), t + ∑ v ∈ Finset.univ.filter (fun v => t ≤ G.degree v), N := by
      rw [ Finset.sum_filter, Finset.sum_filter ];
      simpa only [ ← Finset.sum_add_distrib ] using! Finset.sum_le_sum fun v _ => by split_ifs <;> linarith [ show G.degree v < N from G.degree_lt_card_verts v ] ;
    simp +zetaDelta only [ge_iff_le] at *;
    refine le_trans h_sum ?_;
    exact add_le_add (by
      simpa using Nat.mul_le_mul_right t
        (Finset.card_le_univ (Finset.univ.filter (fun v => G.degree v < t)))) (by simp)
  have h_final : 2 * G.edgeFinset.card ≤ N * t + m * N := by
    have := SimpleGraph.sum_degrees_eq_twice_card_edges G; aesop;
  have h_final' : 2 * G.edgeFinset.card ≤ 2 * ε' * (N : ℝ) ^ 2 + N := by
    have h_final' : (N : ℝ) * t + m * N ≤ (N : ℝ) * (ε' * (N : ℝ) + 1) + (b - 1 : ℝ) * (N.choose a : ℝ) / ((⌈ε' * (N : ℝ)⌉₊).choose a : ℝ) * (N : ℝ) := by
      gcongr;
      · exact Nat.ceil_lt_add_one ( by positivity ) |> le_of_lt;
      · rwa [ le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.choose_pos ht ) ];
    have := hN₁ N ( by linarith ) ; norm_num at * ; nlinarith [ show ( 2 * G.edgeFinset.card : ℝ ) ≤ N * t + m * N by exact_mod_cast h_final ] ;
  have h_final'' : G.edgeFinset.card ≤ ε * (N : ℝ) ^ 2 := by
    have h_final'' : (N : ℝ) ≥ 2 / (3 * ε) := by
      exact le_trans ( Nat.le_ceil _ ) ( mod_cast by linarith );
    rw [ ge_iff_le, div_le_iff₀ ] at h_final'' <;> nlinarith [ mul_div_cancel₀ ( 2 : ℝ ) ( by positivity : ( 3 * ε ) ≠ 0 ) ]
  exact h_final''

end Erdos550
