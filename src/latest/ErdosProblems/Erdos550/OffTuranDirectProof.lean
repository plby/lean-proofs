import Mathlib
import ErdosProblems.Erdos550.OffTuranDirectArithmetic
import ErdosProblems.Erdos550.OffTuranConstants
import ErdosProblems.Erdos550.OffTuranDirectInstantiation
import ErdosProblems.Erdos550.OffTuranDirectMatching
import ErdosProblems.Erdos550.OffTuranRegularityData
import ErdosProblems.Erdos550.EFRS

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Direct off--Turán embedding

The theorem `off_turan_embedding_direct` combines the following ingredients.

1. Exact edge surplus, bipartite Ramsey scaling, and decoupled regularity give
   cleaned equitable clusters of average reduced degree at least
   `n + 100ηN`.
2. Complement regularity and the red multipartite embedding theorem imply
   that every family of at least `ηℓ` clusters spans a blue reduced edge.
3. Threshold counting gives adjacent heavy head clusters `X,Y`.  A maximal
   matching outside the heads leaves fewer than `ηℓ` unmatched clusters and
   transfers at least `n + 78ηN` head degree to matching endpoints.
4. A parity-refined separator gives rooted components whose boundary seeds
   have a common tree colour.  Complete matching edges are assigned to the two
   head colours by a two-coordinate Bernoulli second-moment argument.
5. Rooted components are embedded in dependency order.  The invariant
   `HPPacked` supplies an orientation with fresh capacity on both sides of a
   selected matching edge, while retained endpoint sets preserve adjacency to
   the head core needed by later seeds.

The resulting embedding lies in the cleaned blue graph and hence in the
original host.
-/

namespace Erdos550

open Classical

open SimpleGraph Finset Finpartition SzemerediRegularity

set_option maxHeartbeats 6000000 in
/-- **Direct off--Turán embedding theorem.**  Its proof uses the exact reduced
graph, the red multipartite blow-up lemma, a maximal matching, whole-edge
allocation, and the stateful parity embedding. -/
theorem off_turan_embedding_direct
    (q : ℕ) (hq : 2 ≤ q) (m : Fin (q + 1) → ℕ)
    (hmono : Monotone m) (hpos : 1 ≤ m 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
      T.IsTree → n₀ ≤ Fintype.card V →
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        Fintype.card W
            = q * (ramsey T (Kbip (m 0) (m 1)) - 1) + m 0 →
        ¬ (Kmult (q + 1) m ⊑ Gᶜ) →
        ((Fintype.card W).choose 2 -
            (turanEdges q (Fintype.card W) : ℝ) +
            δ * (Fintype.card W) ^ 2 ≤ G.edgeFinset.card) →
        T ⊑ G := by
  let F := Kmult (q + 1) m
  let d₀ : ℝ := min (δ / 200) (1 / 10000)
  have hd₀0 : 0 < d₀ := by
    dsimp [d₀]
    positivity
  have hd₀1 : d₀ < 1 := by
    dsimp [d₀]
    exact (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨εCap, hεCap, mReg, hcap₀⟩ :=
    exists_offTuran_reduced_family_edge_cap
      F q (Kmult_colorable q m) (by omega) d₀ hd₀1
  let m₀ : ℕ := max 1 mReg
  have hm₀ : 1 ≤ m₀ := le_max_left _ _
  obtain ⟨c⟩ :=
    offTuranConstants_exists q
      (Fintype.card (Σ i, Fin (m i))) m₀ hq hm₀ δ εCap hδ hεCap
  have hηd₀ : c.η ≤ d₀ := by
    dsimp [d₀]
    exact le_min c.eta_delta.le c.eta_small.le
  have hcap :
      ∀ {U : Type} [Fintype U] [DecidableEq U]
        (H : SimpleGraph U) [DecidableRel H.Adj], ¬ (F ⊑ Hᶜ) →
        ∀ (ε : ℝ), 0 ≤ ε → ε ≤ εCap →
        ∀ (P : Finpartition (univ : Finset U)), P.IsUniform H ε →
        ∀ (A : Finset {C // C ∈ P.parts}),
          4 * q ^ 2 ≤ A.card →
          ((P.parts.card : ℝ) ^ 2 * ε <
            (A.card : ℝ) ^ 2 / (4 * q)) →
          (∀ C ∈ A, m₀ ≤ C.1.card) →
          ∃ C ∈ A, ∃ E ∈ A, C ≠ E ∧
            H.IsUniform ε C.1 E.1 ∧
            c.η ≤ (H.edgeDensity C.1 E.1 : ℝ) := by
    intro U instU decU H decAdj hF ε hε0 hεcap P hP A
      hAbig hAirr hAsize
    obtain ⟨C, hCA, E, hEA, hCE⟩ :=
      hcap₀ H hF ε hε0 hεcap P hP A hAbig hAirr
        (fun C hC => (le_max_right 1 mReg).trans (hAsize C hC))
    exact ⟨C, hCA, E, hEA, hCE.1, hCE.2.1,
      hηd₀.trans hCE.2.2⟩
  let L : ℕ :=
    SzemerediRegularity.bound c.ε ⌈4 / c.ε⌉₊
  let τsep : ℝ := c.η ^ 2 / (128 * (L : ℝ))
  have hLpos : 0 < L := by
    dsimp [L]
    exact SzemerediRegularity.bound_pos _ _
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hτsep0 : 0 < τsep := by
    dsimp [τsep]
    exact div_pos (sq_pos_of_pos c.eta_pos)
      (mul_pos (by norm_num) hL0)
  let capNeed : ℕ :=
    max m₀ (max ⌈1 / c.η⌉₊
      (⌈4 * (16 / τsep + 9) / c.ε⌉₊ + 1))
  have hcapNeed1 : 1 ≤ capNeed :=
    hm₀.trans (le_max_left _ _)
  have hmcap : m₀ ≤ capNeed := le_max_left _ _
  have hηcap :
      ⌈1 / c.η⌉₊ ≤ capNeed :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hhugeCap :
      ⌈4 * (16 / τsep + 9) / c.ε⌉₊ + 1 ≤ capNeed :=
    (le_max_right _ _).trans (le_max_right _ _)
  set θ := c.η / 2 with hθ
  have hθ0 : 0 < θ := by
    simpa [θ] using! div_pos c.eta_pos (show (0 : ℝ) < 2 by norm_num)
  obtain ⟨nEFRS, hEFRS⟩ :=
    efrs_bipartite (m 0) (m 1) hpos
      (hpos.trans (hmono (Fin.zero_le 1))) θ hθ0
  let n₀ : ℕ :=
    max nEFRS
      (max (L * capNeed)
        (max (⌈1 / τsep⌉₊ + 1)
          (max
            (⌈(((q : ℝ) ^ 2 + 1) /
                (25 * c.η))⌉₊ + 1) 10)))
  refine ⟨n₀, ?_⟩
  intro V instV T hT hn W instW decW G decAdj hW hF hE
  have hnEFRS : nEFRS ≤ Fintype.card V := by
    exact (le_max_left _ _).trans hn
  have hnTail :
      max (L * capNeed)
        (max (⌈1 / τsep⌉₊ + 1)
          (max
            (⌈(((q : ℝ) ^ 2 + 1) /
                (25 * c.η))⌉₊ + 1) 10)) ≤
        Fintype.card V :=
    (le_max_right _ _).trans hn
  have hnLC : L * capNeed ≤ Fintype.card V :=
    (le_max_left _ _).trans hnTail
  have hnSep :
      ⌈1 / τsep⌉₊ + 1 ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hnTail)
  have hnLarge :
      ⌈(((q : ℝ) ^ 2 + 1) / (25 * c.η))⌉₊ + 1 ≤
        Fintype.card V :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans hnTail))
  have hn10 : 10 ≤ Fintype.card V :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans hnTail))
  let n : ℕ := Fintype.card V
  let r : ℕ := ramsey T (Kbip (m 0) (m 1))
  let N : ℕ := Fintype.card W
  have hEF := hEFRS n (by simpa [n] using! hnEFRS) T hT rfl
  rw [abs_le] at hEF
  have hrlo :
      (1 - c.η / 2) * (n : ℝ) ≤ (r : ℝ) := by
    dsimp [r, n]
    rw [← hθ]
    nlinarith [hEF.1]
  have hnReal : (10 : ℝ) ≤ n := by
    exact_mod_cast (show 10 ≤ n by simpa [n] using! hn10)
  have hr1Real : (1 : ℝ) ≤ r := by
    nlinarith [c.eta_small, c.eta_pos]
  have hr1 : 1 ≤ r := by exact_mod_cast hr1Real
  have hNformula :
      N = q * (r - 1) + m 0 := by
    simpa [N, r] using! hW
  have hNcast :
      (N : ℝ) =
        (q : ℝ) * ((r : ℝ) - 1) + (m 0 : ℝ) := by
    rw [hNformula, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub hr1]
    norm_num
  have hnNReal : (n : ℝ) ≤ N := by
    have hqReal : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have ha : (1 : ℝ) ≤ m 0 := by exact_mod_cast hpos
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hetaN :
        c.η * (n : ℝ) ≤ (n : ℝ) / 10000 :=
      by
        have ht := mul_le_mul_of_nonneg_right c.eta_small.le hn0
        nlinarith
    rw [hNcast]
    nlinarith
  have hnN : n ≤ N := by exact_mod_cast hnNReal
  have hNpos : 0 < N := lt_of_lt_of_le (by omega) hnN
  letI : Nonempty W := Fintype.card_pos_iff.mp (by simpa [N] using! hNpos)
  have hsepOrder :
      (1 : ℝ) ≤ τsep * n := by
    have hceil : 1 / τsep ≤ (⌈1 / τsep⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hnceil :
        (⌈1 / τsep⌉₊ : ℝ) ≤ n := by
      exact_mod_cast (show ⌈1 / τsep⌉₊ ≤ n by
        simpa [n] using! (Nat.le_add_right _ 1 |>.trans hnSep))
    rw [div_le_iff₀ hτsep0] at hceil
    nlinarith
  have hlargeBase :
      ((q : ℝ) ^ 2 + 1) ≤ 25 * c.η * n := by
    have hceil :
        ((q : ℝ) ^ 2 + 1) / (25 * c.η) ≤
          (⌈((q : ℝ) ^ 2 + 1) /
            (25 * c.η)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hnceil :
        (⌈((q : ℝ) ^ 2 + 1) /
          (25 * c.η)⌉₊ : ℝ) ≤ n := by
      exact_mod_cast (show
        ⌈((q : ℝ) ^ 2 + 1) / (25 * c.η)⌉₊ ≤ n by
          simpa [n] using! (Nat.le_add_right _ 1 |>.trans hnLarge))
    rw [div_le_iff₀ (mul_pos (by norm_num) c.eta_pos)] at hceil
    nlinarith
  have hlarge :
      2 * (q : ℝ) * N + 2 * (q : ℝ) ^ 3 ≤
        100 * (q : ℝ) * c.η * (N : ℝ) ^ 2 := by
    have hbaseN :
        (q : ℝ) ^ 2 + 1 ≤ 25 * c.η * N := by
      nlinarith [hlargeBase,
        mul_le_mul_of_nonneg_left hnNReal
          (show (0 : ℝ) ≤ 25 * c.η from
            mul_nonneg (by norm_num) c.eta_pos.le)]
    have hN1 : (1 : ℝ) ≤ N :=
      (show (1 : ℝ) ≤ n by nlinarith).trans hnNReal
    have hqR : (0 : ℝ) < q := by positivity
    have hN0 : (0 : ℝ) ≤ N := zero_le_one.trans hN1
    have hqSq0 : (0 : ℝ) ≤ (q : ℝ) ^ 2 := sq_nonneg _
    have hqBound :
        (q : ℝ) ^ 2 ≤ 25 * c.η * N := by
      nlinarith
    have honeBound : (1 : ℝ) ≤ 25 * c.η * N := by
      nlinarith
    have hNBound :
        (N : ℝ) ≤ 25 * c.η * N ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right honeBound hN0
      nlinarith
    have hNmono : 25 * c.η * N ≤ 25 * c.η * N ^ 2 := by
      have hNN : (N : ℝ) ≤ N ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hN1 hN0]
      exact mul_le_mul_of_nonneg_left hNN
        (mul_nonneg (by norm_num) c.eta_pos.le)
    have hsum :
        (N : ℝ) + (q : ℝ) ^ 2 ≤
          50 * c.η * N ^ 2 := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsum
      (show (0 : ℝ) ≤ 2 * q by positivity)
    nlinarith
  have hrraw :
      (2 - c.η) * (n : ℝ) ≤ 2 * (r : ℝ) := by
    nlinarith [hrlo]
  have hraw :=
    offTuran_raw_average_from_edges q hq n r (m 0) N
      G.edgeFinset.card δ c.η hδ c.eta_pos c.eta_delta_400
      hnN hpos hr1 hrraw hNformula hlarge hE
  have hLleN : L ≤ N := by
    have hLCleN : L * capNeed ≤ N :=
      hnLC.trans hnN
    exact (Nat.le_mul_of_pos_right L hcapNeed1).trans hLCleN
  have hregLarge : ⌈4 / c.ε⌉₊ ≤ N := by
    exact (SzemerediRegularity.le_bound c.ε
      ⌈4 / c.ε⌉₊).trans hLleN
  have hboundEta :
      (L : ℝ) ≤ c.η * N := by
    have hceil : 1 / c.η ≤ (⌈1 / c.η⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hceilCap :
        (⌈1 / c.η⌉₊ : ℝ) ≤ capNeed := by
      exact_mod_cast hηcap
    have hLC :
        (L : ℝ) * capNeed ≤ N := by
      exact_mod_cast (hnLC.trans hnN)
    rw [div_le_iff₀ c.eta_pos] at hceil
    nlinarith [mul_le_mul_of_nonneg_left hceilCap
      (show (0 : ℝ) ≤ L by positivity)]
  have hboundMin : m₀ * L ≤ N := by
    calc
      m₀ * L ≤ capNeed * L := Nat.mul_le_mul_right L hmcap
      _ = L * capNeed := Nat.mul_comm _ _
      _ ≤ N := hnLC.trans hnN
  have hεη : c.ε ≤ c.η := by
    exact c.eps_linear.le.trans (by
      nlinarith [c.eta_pos])
  obtain ⟨D⟩ :=
    exists_offTuran_reduced_degree_data_of_raw
      G c.ε (n : ℝ) c.η m₀
      c.eps_pos hεη
      (by positivity) hnNReal c.eta_pos
      (c.eta_small.le.trans
        (by norm_num : (1 / 10000 : ℝ) ≤ 1 / 100))
      hregLarge (by simpa [L] using! hboundEta)
      (by simpa [L] using! hboundMin) hraw
  have hellEta :
      (D.P.parts.card : ℝ) ≤ c.η * N := by
    have hcast : (D.P.parts.card : ℝ) ≤ L := by
      exact_mod_cast D.upper_parts
    exact hcast.trans hboundEta
  obtain ⟨X, Y, hXY, κ, instκ, decκ, cL, cR,
      hmatch, hinj, haway, hSX, hSY⟩ :=
    D.exists_direct_heads_matching_supply
      F q hq εCap m₀ c hcap hF c.eps_cap.le
      (by simpa [N] using! hellEta)
  have hcapNeedFloor :
      capNeed ≤ N / D.P.parts.card := by
    apply (Nat.le_div_iff_mul_le (D.parts_pos c.eps_pos)).2
    have hpartsL : D.P.parts.card ≤ L := D.upper_parts
    calc
      capNeed * D.P.parts.card ≤ capNeed * L :=
        Nat.mul_le_mul_left capNeed hpartsL
      _ = L * capNeed := Nat.mul_comm _ _
      _ ≤ N := hnLC.trans hnN
  have hfloorHuge :
      16 /
          (c.η ^ 2 /
            (128 * (SzemerediRegularity.bound c.ε
              ⌈4 / c.ε⌉₊ : ℝ))) +
          9 ≤
        c.ε *
          (↑(N / D.P.parts.card) : ℝ) / 4 := by
    have hceil :
        4 * (16 / τsep + 9) / c.ε ≤
          (⌈4 * (16 / τsep + 9) / c.ε⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hstrict :
        4 * (16 / τsep + 9) / c.ε <
          (capNeed : ℝ) := by
      have hnat :
          ⌈4 * (16 / τsep + 9) / c.ε⌉₊ <
            capNeed := by omega
      exact hceil.trans_lt (by exact_mod_cast hnat)
    have hcapCast :
        (capNeed : ℝ) ≤
          (↑(N / D.P.parts.card) : ℝ) := by
      exact_mod_cast hcapNeedFloor
    have hneed :
        16 / τsep + 9 ≤
          c.ε * (↑(N / D.P.parts.card) : ℝ) / 4 := by
      rw [div_lt_iff₀ c.eps_pos] at hstrict
      nlinarith [mul_le_mul_of_nonneg_left hcapCast c.eps_pos.le]
    simpa [τsep, L] using! hneed
  apply offTuran_reduced_parity_embedding_of_large
    c hq T hT G D X Y hXY cL cR hmatch hinj haway
  · simpa [n, N] using! hnN
  · simpa [N] using! hellEta
  · simpa [τsep, L, n] using! hsepOrder
  · simpa [N] using! hfloorHuge
  · simpa [n, N] using! hSX
  · simpa [n, N] using! hSY

/-- Direct near-Turán red-density corollary, by contraposition and exact
complementary edge counting. -/
theorem near_turan_red_density_direct
    (q : ℕ) (hq : 2 ≤ q) (m : Fin (q + 1) → ℕ)
    (hmono : Monotone m) (hpos : 1 ≤ m 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
      T.IsTree → n₀ ≤ Fintype.card V →
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        Fintype.card W
            = q * (ramsey T (Kbip (m 0) (m 1)) - 1) + m 0 →
        ¬ (T ⊑ G) →
        ¬ (Kmult (q + 1) m ⊑ Gᶜ) →
        (turanEdges q (Fintype.card W) : ℝ) -
            δ * (Fintype.card W) ^ 2 ≤
          (Gᶜ).edgeFinset.card := by
  obtain ⟨n₀, H⟩ :=
    off_turan_embedding_direct q hq m hmono hpos δ hδ
  refine ⟨n₀, ?_⟩
  intro V instV T hT hn W instW decW G decAdj hcard hTfree hFfree
  have hedge :
      (G.edgeFinset.card : ℝ) + (Gᶜ).edgeFinset.card =
        (Fintype.card W).choose 2 := by
    norm_cast
    rw [← Finset.card_union_of_disjoint]
    · rw [show G.edgeFinset ∪ Gᶜ.edgeFinset =
        SimpleGraph.edgeFinset (⊤ : SimpleGraph W) by
          ext ⟨u, v⟩
          by_cases h : G.Adj u v <;>
            simp +decide [h, SimpleGraph.compl_adj]
          exact h.ne]
      exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    · simp +decide [Finset.disjoint_left]
      rintro ⟨u, v⟩ huv
      simp_all +decide [SimpleGraph.compl_adj]
  by_contra hnot
  have hblue :
      (Fintype.card W).choose 2 -
          (turanEdges q (Fintype.card W) : ℝ) +
          δ * (Fintype.card W) ^ 2 ≤
        G.edgeFinset.card := by
    push_neg at hnot
    nlinarith
  exact hTfree (H T hT hn G hcard hFfree hblue)

end Erdos550
