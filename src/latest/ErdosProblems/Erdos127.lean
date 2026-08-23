/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 127.
https://www.erdosproblems.com/forum/thread/127

Informal authors:
- Noga Alon

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos127.md
-/
import ErdosProblems.Erdos127.BalancedCut
import ErdosProblems.Erdos127.Chromatic
import ErdosProblems.Erdos127.CutComposition
import ErdosProblems.Erdos127.DenseSubcase
import ErdosProblems.Erdos127.HeavyHalf
import ErdosProblems.Erdos127.HighChromClique

/-!
# Erdős Problem 127

Alon's affirmative resolution of the problem on the largest bipartite subgraph
of a graph with a prescribed number of edges.
-/

open Filter Finset Set
open scoped ENNReal Topology

namespace Erdos127

/-- The Edwards baseline in Problem 127. -/
noncomputable def baseline (m : ℕ) : ℝ :=
  (m : ℝ) / 2 + (Real.sqrt (8 * (m : ℝ) + 1) - 1) / 8

/-- `Guarantees m k` says that every finite simple graph with `m` edges has a
bipartite subgraph whose number of edges is at least the Edwards baseline plus
the integral correction `k`.

The subgraph is represented on the same vertex type; unused vertices are
isolated.  Quantifying over all finite types is equivalent to quantifying over
all finite (unlabelled) simple graphs. -/
def Guarantees (m k : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.edgeSet.ncard = m →
      ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
        baseline m + k ≤ (H.edgeSet.ncard : ℝ)

/-- The integral correction function from Problem 127.  The a priori bound
`k ≤ m` is proved below, so this bounded maximum is the genuine maximum. -/
noncomputable def correction (m : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (Guarantees m) m

private lemma ncard_edgeSet_completeBipartiteGraph (a b : ℕ) :
    (completeBipartiteGraph (Fin a) (Fin b)).edgeSet.ncard = a * b := by
  rw [← Nat.cast_inj (R := ℕ∞)]
  rw [Set.Finite.cast_ncard_eq (Set.toFinite _)]
  simp [SimpleGraph.encard_edgeSet_completeBipartiteGraph]

lemma guarantees_le_edges {m k : ℕ} (h : Guarantees m k) : k ≤ m := by
  let G := completeBipartiteGraph (Fin 1) (Fin m)
  obtain ⟨H, hHG, -, hk⟩ := h (Fin 1 ⊕ Fin m) G (by
    simpa [G] using ncard_edgeSet_completeBipartiteGraph 1 m)
  have hcard : H.edgeSet.ncard ≤ m := by
    have hsub : H.edgeSet ⊆ G.edgeSet := SimpleGraph.edgeSet_mono hHG
    simpa [G, ncard_edgeSet_completeBipartiteGraph] using Set.ncard_le_ncard hsub
  have hbase : 0 ≤ baseline m := by
    unfold baseline
    have hsqrt : 1 ≤ Real.sqrt (8 * (m : ℝ) + 1) := by
      have hm : 0 ≤ (m : ℝ) := by positivity
      calc
        1 = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (8 * (m : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    positivity
  exact_mod_cast (show (k : ℝ) ≤ m by
    exact (le_add_of_nonneg_left hbase).trans (hk.trans (by exact_mod_cast hcard)))

lemma le_correction_of_guarantees {m k : ℕ} (h : Guarantees m k) :
    k ≤ correction m := by
  classical
  unfold correction
  exact Nat.le_findGreatest (guarantees_le_edges h) h

/-- Edwards' theorem in the exact form used in Problem 127. -/
theorem exists_edwards_bipartite_subgraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
      baseline G.edgeSet.ncard ≤ (H.edgeSet.ncard : ℝ) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  by_cases hedge : G.edgeFinset.Nonempty
  · let q := ENat.toNat G.chromaticNumber
    obtain ⟨C, hχ, hsurj⟩ := G.exists_optimal_coloring_toNat
    have hnebot : G ≠ ⊥ := by
      intro hbot
      subst G
      simpa using hedge
    have h2χ : (2 : ℕ∞) ≤ G.chromaticNumber :=
      SimpleGraph.two_le_chromaticNumber_iff_ne_bot.mpr hnebot
    have hq : 2 ≤ q := by
      rw [hχ] at h2χ
      exact_mod_cast h2χ
    obtain ⟨S, hle, hbip, hcut⟩ := G.exists_bipartite_cut_mul_bound hq C hsurj
    let H := G.between (S : Set V) (S : Set V)ᶜ
    let m := G.edgeFinset.card
    let c := H.edgeFinset.card
    have hchrom : q * (q - 1) ≤ 2 * m := by
      simpa only [m] using G.chromatic_toNat_mul_pred_le_twice_card_edges hedge
    have hm : G.edgeSet.ncard = m := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    have hc : H.edgeSet.ncard = c := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    have hqR : (0 : ℝ) < q := by positivity
    have hmR : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
    have hchromR' : (q : ℝ) * ((q - 1 : ℕ) : ℝ) ≤ 2 * m := by
      exact_mod_cast hchrom
    have hchromR : (q : ℝ) * (q - 1) ≤ 2 * m := by
      simpa [Nat.cast_sub (by omega : 1 ≤ q)] using hchromR'
    have hcutR : ((q + 1) * m : ℕ) ≤ 2 * q * c := by
      simpa only [H, m, c] using hcut
    have hcutR' : ((q : ℝ) + 1) * m ≤ 2 * q * c := by exact_mod_cast hcutR
    have hsqrt : Real.sqrt (8 * (m : ℝ) + 1) ≤ 4 * m / q + 1 := by
      have hright : 0 ≤ (4 : ℝ) * m / q + 1 := by
        have : 0 ≤ (4 : ℝ) * m / q := div_nonneg (mul_nonneg (by norm_num) hmR) hqR.le
        linarith
      rw [Real.sqrt_le_left hright]
      have hcore : 0 ≤ (2 : ℝ) * m - q * (q - 1) := by linarith
      have hprod : 0 ≤ (8 : ℝ) * m * ((2 : ℝ) * m - q * (q - 1)) :=
        mul_nonneg (mul_nonneg (by positivity) hmR) hcore
      field_simp
      nlinarith
    have hbonus : (Real.sqrt (8 * (m : ℝ) + 1) - 1) / 8 ≤ m / (2 * q) := by
      have hsub := sub_le_sub_right hsqrt 1
      have hdiv := div_le_div_of_nonneg_right hsub (by norm_num : (0 : ℝ) ≤ 8)
      calc
        (Real.sqrt (8 * (m : ℝ) + 1) - 1) / 8 ≤ (4 * m / q) / 8 := by
          simpa only [add_sub_cancel_right] using hdiv
        _ = m / (2 * q) := by
          field_simp
          ring
    have hbalanced : (m : ℝ) / 2 + m / (2 * q) ≤ c := by
      have hid : (m : ℝ) / 2 + m / (2 * q) = ((q + 1) * m) / (2 * q) := by
        field_simp
      rw [hid, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcutR'
    refine ⟨H, hle, hbip, ?_⟩
    rw [hm, hc]
    unfold baseline
    linarith
  · have hempty : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hedge
    have hm : G.edgeSet.ncard = 0 := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, hempty]
      simp
    refine ⟨⊥, bot_le, ?_, ?_⟩
    · exact ⟨SimpleGraph.Coloring.mk (fun _ ↦ 0) (by simp)⟩
    simp [baseline, hm]

theorem guarantees_zero (m : ℕ) : Guarantees m 0 := by
  intro V _ G hm
  obtain ⟨H, hle, hbip, hbound⟩ := exists_edwards_bipartite_subgraph G
  exact ⟨H, hle, hbip, by simpa [hm] using hbound⟩

lemma correction_spec (m : ℕ) : Guarantees m (correction m) := by
  classical
  unfold correction
  exact Nat.findGreatest_spec (Nat.zero_le m) (guarantees_zero m)

lemma correction_isGreatest (m : ℕ) :
    IsGreatest {k : ℕ | Guarantees m k} (correction m) :=
  ⟨correction_spec m, fun _ hk ↦ le_correction_of_guarantees hk⟩

/-- A division-free coarse consequence of Edwards' coloring argument. -/
theorem exists_coarse_cut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : ℕ) (ha : 1 ≤ a) (hedges : 8 * a ^ 2 ≤ G.edgeSet.ncard) :
  ∃ S : Finset V,
      G.edgeSet.ncard + 2 * a ≤ 2 * #(G.cutEdgeFinset S) := by
  classical
  let w := G.edgeFinset.card
  have hw : G.edgeSet.ncard = w := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hwpos : 0 < w := by
    rw [hw] at hedges
    nlinarith
  have hedge : G.edgeFinset.Nonempty := Finset.card_pos.mp hwpos
  let q := ENat.toNat G.chromaticNumber
  obtain ⟨C, hχ, hsurj⟩ := G.exists_optimal_coloring_toNat
  have hnebot : G ≠ ⊥ := by
    intro hbot
    subst G
    simpa using hedge
  have h2χ : (2 : ℕ∞) ≤ G.chromaticNumber :=
    SimpleGraph.two_le_chromaticNumber_iff_ne_bot.mpr hnebot
  have hq : 2 ≤ q := by
    rw [hχ] at h2χ
    exact_mod_cast h2χ
  have hchrom : q * (q - 1) ≤ 2 * w := by
    simpa only [w] using G.chromatic_toNat_mul_pred_le_twice_card_edges hedge
  obtain ⟨S, -, -, hcut⟩ := G.exists_bipartite_cut_mul_bound hq C hsurj
  rw [G.edgeFinset_between_compl_eq_cutEdgeFinset S] at hcut
  change (q + 1) * w ≤ 2 * q * #(G.cutEdgeFinset S) at hcut
  refine ⟨S, ?_⟩
  rw [hw]
  by_contra! hsmall
  have hwa : w < 2 * q * a := by nlinarith
  have hqbound : q ≤ 4 * a := by
    have hpred : q - 1 + 1 = q := by omega
    nlinarith
  rw [hw] at hedges
  nlinarith

lemma card_insideEdgeFinset_of_isClique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    (hU : G.IsClique (U : Set V)) :
    #(G.insideEdgeFinset U) = U.card.choose 2 := by
  have htop : G.induce (U : Set V) = ⊤ := G.induce_eq_top.mpr hU
  calc
    #(G.insideEdgeFinset U) = #(G.induce (U : Set V)).edgeFinset := by
      rw [SimpleGraph.insideEdgeFinset, ← G.filter_edgeFinset_toFinset_subset U]
      exact G.card_filter_edgeFinset_toFinset_subset U
    _ = (G.induce (U : Set V)).edgeSet.ncard := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    _ = (⊤ : SimpleGraph (U : Set V)).edgeSet.ncard := by rw [htop]
    _ = #(⊤ : SimpleGraph (U : Set V)).edgeFinset := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    _ = U.card.choose 2 := by
      rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      simp

lemma localCutEdgeFinset_inter_self {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U S : Finset V) :
    G.localCutEdgeFinset U (S ∩ U) = G.localCutEdgeFinset U S := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v => simp [SimpleGraph.mem_localCutEdgeFinset_mk] <;> tauto

private theorem thresholdQuarterArithmetic (t : ℕ) (ht : 1 ≤ t) :
    4 * (8 * (128 * t) ^ 2) + 4 * (64 * t) ≤ 2 ^ 20 * t ^ 2 := by
  have htt : t ≤ t ^ 2 := by nlinarith
  norm_num
  nlinarith

private theorem squareRemainderArithmetic (t : ℕ) (ht : 1 ≤ t) :
    2 * ((4 * (64 * t)) * (4 * (64 * t))) + 4 * (64 * t) ≤
      2 ^ 20 * t ^ 2 := by
  have htt : t ≤ t ^ 2 := by nlinarith
  norm_num
  nlinarith

private theorem smallBonusArithmetic (t : ℕ) (ht : 1 ≤ t) :
    4 * (8 * (128 * t) ^ 2) + 2 * (4 * (64 * t)) + 8 * t + 4 * (64 * t) ≤
      2 ^ 20 * t ^ 2 := by
  have htt : t ≤ t ^ 2 := by nlinarith
  norm_num
  nlinarith

/-- Explicit specialization of Alon's theorem at `N = 2^20 t^2`.  The
conclusion is the desired cut estimate with all divisions cleared. -/
theorem explicit_alon_cut {t : ℕ} (ht : 1 ≤ t) {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hedges : 2 * #G.edgeFinset = (2 ^ 20 * t ^ 2) ^ 2) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj,
      H ≤ G ∧ H.IsBipartite ∧
        2 * #G.edgeFinset + (2 ^ 20 * t ^ 2) + 4 * t ≤ 4 * #H.edgeFinset := by
  classical
  let N := 2 ^ 20 * t ^ 2
  let L := 64 * t
  let R := 4 * L
  let y := 128 * t
  let m := #G.edgeFinset
  let q := ENat.toNat G.chromaticNumber
  have htPos : 0 < t := by omega
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hedge : G.edgeFinset.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hcard
    have hcard0 : #G.edgeFinset = 0 := Nat.eq_zero_of_not_pos hcard
    have hright : 0 < (2 ^ 20 * t ^ 2) ^ 2 := by positivity
    rw [hcard0] at hedges
    simp only [Nat.reduceMul] at hedges
    omega
  obtain ⟨C, hχ, hsurj⟩ := G.exists_optimal_coloring_toNat
  have hnebot : G ≠ ⊥ := by
    intro hbot
    subst G
    simpa using hedge
  have h2χ : (2 : ℕ∞) ≤ G.chromaticNumber :=
    SimpleGraph.two_le_chromaticNumber_iff_ne_bot.mpr hnebot
  have hq : 2 ≤ q := by
    rw [hχ] at h2χ
    exact_mod_cast h2χ
  have hedges' : 2 * m = N ^ 2 := by simpa only [m, N] using hedges
  by_cases hlow : q ≤ N - L
  · obtain ⟨S, hle, hbip, hcut⟩ := G.exists_bipartite_cut_mul_bound hq C hsurj
    let H := G.between (S : Set V) (S : Set V)ᶜ
    let c := #H.edgeFinset
    have hLle : L ≤ N := by
      dsimp [N, L]
      nlinarith [show t ≤ t ^ 2 by nlinarith]
    have hsubL : N - L + L = N := Nat.sub_add_cancel hLle
    have hconst : (N - L) * (N + 4 * t) ≤ N ^ 2 := by
      have hfour : 4 * t ≤ L := by
        dsimp [L]
        omega
      have hmul : (N - L) * (4 * t) ≤ N * L :=
        Nat.mul_le_mul (Nat.sub_le N L) hfour
      calc
        (N - L) * (N + 4 * t) = (N - L) * N + (N - L) * (4 * t) := by ring
        _ ≤ (N - L) * N + N * L := Nat.add_le_add_left hmul _
        _ = N * ((N - L) + L) := by ring
        _ = N ^ 2 := by rw [hsubL]; ring
    have hqm : q * (N + 4 * t) ≤ 2 * m := by
      calc
        q * (N + 4 * t) ≤ (N - L) * (N + 4 * t) :=
          Nat.mul_le_mul_right (N + 4 * t) hlow
        _ ≤ N ^ 2 := hconst
        _ = 2 * m := hedges'.symm
    have hcut' : (q + 1) * m ≤ 2 * q * c := by
      simpa only [m, H, c] using hcut
    have htarget : 2 * m + N + 4 * t ≤ 4 * c := by
      nlinarith
    exact ⟨H, inferInstance, hle, hbip, by simpa only [m, N, H, c] using htarget⟩
  · have hhigh : N - L < q := by omega
    have hNL : 2 * L ≤ N := by
      dsimp [N, L]
      norm_num
      nlinarith
    obtain ⟨-, sCrit, -, -, U, hUclique, hUcard⟩ :=
      G.exists_exact_clique_of_high_chromatic N L hN hNL hedges' hhigh
    let u := #U
    let eU := #(G.insideEdgeFinset U)
    let x := #(G.cutEdgeFinset U)
    let eW := #(G.insideEdgeFinset Uᶜ)
    have hR : R = 4 * L := rfl
    have hu : u = N - R := by simpa only [u, R] using hUcard
    have hRle : R ≤ N := by
      dsimp [N, L, R]
      norm_num
      nlinarith
    have hNuR : u + R = N := by omega
    have huPos : 0 < u := by
      rw [hu]
      dsimp [N, L, R]
      norm_num
      nlinarith
    have hUne : U.Nonempty := Finset.card_pos.mp (by simpa only [u] using huPos)
    have hNeven : Even N := by
      refine ⟨2 ^ 19 * t ^ 2, ?_⟩
      dsimp [N]
      ring
    have hReven : Even R := by
      refine ⟨128 * t, ?_⟩
      dsimp [R, L]
      ring
    rcases hNeven with ⟨nN, hnN⟩
    rcases hReven with ⟨nR, hnR⟩
    have hnRle : nR ≤ nN := by nlinarith [hRle]
    have huEven : Even u := by
      refine ⟨nN - nR, ?_⟩
      omega
    have huHalf : 2 * (u / 2) = u := Nat.two_mul_div_two_of_even huEven
    have hEU : eU = u * (u - 1) / 2 := by
      rw [show eU = u.choose 2 by
        simpa only [eU, u] using card_insideEdgeFinset_of_isClique G U hUclique]
      exact Nat.choose_two_right u
    have hprodEven : Even (u * (u - 1)) := huEven.mul_right (u - 1)
    have hEUtwo : 2 * eU = u * (u - 1) := by
      rw [hEU]
      exact Nat.two_mul_div_two_of_even hprodEven
    have hpart : m = eU + x + eW := by
      simpa only [m, eU, x, eW] using
        G.card_edgeFinset_eq_inside_add_cut_add_inside_compl U
    by_cases hlarge : 8 * y ^ 2 ≤ eW
    · let GW := G.insideGraph Uᶜ
      have hGWcard : GW.edgeSet.ncard = eW := by
        calc
          GW.edgeSet.ncard = #GW.edgeFinset := by
            rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
          _ = eW := by
            rw [G.edgeFinset_insideGraph_eq_insideEdgeFinset]
      have hy : 1 ≤ y := by
        dsimp [y]
        omega
      have hGWlarge : 8 * y ^ 2 ≤ GW.edgeSet.ncard := by
        rw [hGWcard]
        exact hlarge
      obtain ⟨T, hTcut⟩ := exists_coarse_cut GW y hy hGWlarge
      let T' := T ∩ Uᶜ
      have hTsub : T' ⊆ Uᶜ := Finset.inter_subset_right
      have hlocal : eW + 2 * y ≤ 2 * #(G.localCutEdgeFinset Uᶜ T') := by
        rw [localCutEdgeFinset_inter_self G Uᶜ T,
          ← G.cutEdgeFinset_insideGraph_eq_localCutEdgeFinset]
        simpa only [hGWcard] using hTcut
      let r := u / 2
      have hUcard2 : #U = 2 * r := by simpa only [u, r] using huHalf.symm
      obtain ⟨A, S, -, -, -, -, -, hcomp⟩ :=
        G.exists_cut_of_even_clique_and_compl_cut r hUcard2 hUclique hTsub
      let H := G.between (S : Set V) (S : Set V)ᶜ
      have hrr : 4 * (r * r) = u * u := by
        calc
          4 * (r * r) = (2 * r) * (2 * r) := by ring
          _ = u * u := by rw [show 2 * r = u by simpa only [r] using huHalf]
      have hlocal2 : 2 * eW + 4 * y ≤
          4 * #(G.localCutEdgeFinset Uᶜ T') := by omega
      have hcomp2 : 4 * (r * r) + 2 * x +
          4 * #(G.localCutEdgeFinset Uᶜ T') ≤
          4 * #(G.cutEdgeFinset S) := by omega
      have hcutBonus : u * u + 2 * x + 2 * eW + 4 * y ≤
          4 * #(G.cutEdgeFinset S) := by omega
      have hpred : u - 1 + 1 = u := Nat.sub_add_cancel (by omega : 1 ≤ u)
      have hsq : u * (u - 1) + u = u * u := by
        simpa only [Nat.mul_add, Nat.mul_one] using congrArg (fun z => u * z) hpred
      have hm2 : 2 * m = u * (u - 1) + 2 * x + 2 * eW := by omega
      have hRbonus : N + 4 * t ≤ u + 4 * y := by
        dsimp [R, L, y] at hNuR
        omega
      have htarget : 2 * m + N + 4 * t ≤ 4 * #(G.cutEdgeFinset S) := by
        omega
      refine ⟨H, inferInstance, G.between_le, G.between_compl_isBipartite S, ?_⟩
      rw [G.edgeFinset_between_compl_eq_cutEdgeFinset]
      simpa only [m, N, H] using htarget
    · have hsmall : eW < 8 * y ^ 2 := by omega
      have hR2Even : Even (R * R) := by
        refine ⟨2 * L * R, ?_⟩
        dsimp [R]
        ring
      have hR2half : 2 * ((R * R) / 2) = R * R :=
        Nat.two_mul_div_two_of_even hR2Even
      let a0 := u / 2 + (R * R) / 2
      have ha0two : 2 * a0 = u + R * R := by
        dsimp [a0]
        omega
      have hpred : u - 1 + 1 = u := Nat.sub_add_cancel (by omega : 1 ≤ u)
      have hsq : u * (u - 1) + u = u * u := by
        simpa only [Nat.mul_add, Nat.mul_one] using congrArg (fun z => u * z) hpred
      have hm2 : 2 * m = u * (u - 1) + 2 * x + 2 * eW := by omega
      have hN2 : N ^ 2 = u * u + 2 * R * u + R * R := by
        rw [← hNuR]
        ring
      have hDtwo : 2 * (x + eW) = 2 * R * u + u + R * R := by
        omega
      have hrighttwo : 2 * (R * u + a0) = 2 * R * u + u + R * R := by
        calc
          2 * (R * u + a0) = 2 * R * u + 2 * a0 := by ring
          _ = 2 * R * u + u + R * R := by rw [ha0two]; omega
      have hD : x + eW = R * u + a0 :=
        Nat.mul_left_cancel (by norm_num) (hDtwo.trans hrighttwo.symm)
      have hthresholdQuarter : 4 * (8 * y ^ 2) ≤ u := by
        rw [hu]
        apply Nat.le_sub_of_add_le
        simpa only [N, L, R, y] using thresholdQuarterArithmetic t ht
      have heWa0 : eW ≤ a0 := by omega
      let rem := a0 - eW
      have hremadd : rem + eW = a0 := by omega
      have hx : x = R * u + rem := by omega
      have hremlo : u ≤ 4 * rem := by omega
      have hR2u : 2 * (R * R) ≤ u := by
        rw [hu]
        apply Nat.le_sub_of_add_le
        simpa only [N, L, R] using squareRemainderArithmetic t ht
      have hremhi : 4 * rem ≤ 3 * u := by omega
      have hxcut :
          #(G.between (U : Set V) (Uᶜ : Finset V)).edgeFinset = x := by
        have hgraphs : G.between (U : Set V) (Uᶜ : Finset V) =
            G.between (U : Set V) (U : Set V)ᶜ := by
          ext v w
          simp only [SimpleGraph.between_adj, Finset.coe_compl]
        calc
          #(G.between (U : Set V) (Uᶜ : Finset V)).edgeFinset =
              (G.between (U : Set V) (Uᶜ : Finset V)).edgeSet.ncard := by
                rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
          _ = (G.between (U : Set V) (U : Set V)ᶜ).edgeSet.ncard := by rw [hgraphs]
          _ = #(G.between (U : Set V) (U : Set V)ᶜ).edgeFinset := by
                rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
          _ = #(G.cutEdgeFinset U) :=
            congrArg Finset.card (G.edgeFinset_between_compl_eq_cutEdgeFinset U)
          _ = x := rfl
      have hxBetween :
          #(G.between (U : Set V) (Uᶜ : Finset V)).edgeFinset = R * #U + rem := by
        rw [hxcut]
        simpa only [u] using hx
      obtain ⟨H, instH, hHG, hHbip, hbound⟩ :=
        G.exists_bipartite_cut_of_clique_dense_remainder U hUne huEven hUclique
          R rem (by simpa only [u] using hremlo) (by simpa only [u] using hremhi) hxBetween
      letI : DecidableRel H.Adj := instH
      have hbound' : u * u + 2 * x + u / 2 ≤ 4 * #H.edgeFinset := by
        rw [hxcut] at hbound
        simpa only [u, x] using hbound
      have hbonusRaw : 4 * (8 * y ^ 2) + 2 * R + 8 * t ≤ u := by
        rw [hu]
        apply Nat.le_sub_of_add_le
        simpa only [N, L, R, y] using smallBonusArithmetic t ht
      have hhalfBonus : 2 * eW + R + 4 * t ≤ u / 2 := by omega
      have hpretarget : 2 * m + N + 4 * t ≤ u * u + 2 * x + u / 2 := by
        omega
      have htarget : 2 * m + N + 4 * t ≤ 4 * #H.edgeFinset := by
        exact hpretarget.trans hbound'
      exact ⟨H, instH, hHG, hHbip, by simpa only [m, N] using htarget⟩

/-- The vertex scale in the explicit family used for Alon's lower bound. -/
def alonParameter (t : ℕ) : ℕ := 2 ^ 20 * t ^ 2

/-- The edge count `N² / 2` at the scale `N = 2²⁰t²`. -/
def alonEdgeCount (t : ℕ) : ℕ := alonParameter t ^ 2 / 2

lemma two_mul_alonEdgeCount (t : ℕ) :
    2 * alonEdgeCount t = alonParameter t ^ 2 := by
  unfold alonEdgeCount alonParameter
  apply Nat.two_mul_div_two_of_even
  refine ⟨(2 ^ 19 * t ^ 2) * (2 ^ 20 * t ^ 2), ?_⟩
  ring

private lemma parameter_le_edgeCount (t : ℕ) (ht : 1 ≤ t) :
    t ≤ alonEdgeCount t := by
  have htwo := two_mul_alonEdgeCount t
  have hbound : 2 * t ≤ alonParameter t ^ 2 := by
    have htt : t ≤ t ^ 2 := by nlinarith
    have h2t : 2 * t ≤ alonParameter t := by
      dsimp [alonParameter]
      omega
    have hN1 : 1 ≤ alonParameter t := by omega
    have hNsq : alonParameter t ≤ alonParameter t ^ 2 := by nlinarith
    exact h2t.trans hNsq
  omega

/-- Every graph with `alonEdgeCount t` edges has an integral excess of at
least `t` above the exact Edwards baseline. -/
theorem guarantees_alonEdgeCount (t : ℕ) (ht : 1 ≤ t) :
    Guarantees (alonEdgeCount t) t := by
  intro V _ G hG
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hGcard : #G.edgeFinset = alonEdgeCount t := by
    calc
      #G.edgeFinset = G.edgeSet.ncard := by
        rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
      _ = alonEdgeCount t := hG
  have hedges : 2 * #G.edgeFinset = (2 ^ 20 * t ^ 2) ^ 2 := by
    rw [hGcard, two_mul_alonEdgeCount]
    rfl
  obtain ⟨H, instH, hHG, hHbip, hcut⟩ := explicit_alon_cut ht G hedges
  letI : DecidableRel H.Adj := instH
  have hHcard : H.edgeSet.ncard = #H.edgeFinset := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hcutNat :
      2 * alonEdgeCount t + alonParameter t + 4 * t ≤ 4 * #H.edgeFinset := by
    simpa only [hGcard, alonParameter] using hcut
  have hcutReal :
      2 * (alonEdgeCount t : ℝ) + (alonParameter t : ℝ) + 4 * (t : ℝ) ≤
        4 * (#H.edgeFinset : ℝ) := by
    exact_mod_cast hcutNat
  have hexplicit :
      (alonEdgeCount t : ℝ) / 2 + (alonParameter t : ℝ) / 4 + t ≤
        (#H.edgeFinset : ℝ) := by
    linarith
  have hmEq :
      2 * (alonEdgeCount t : ℝ) = (alonParameter t : ℝ) ^ 2 := by
    exact_mod_cast two_mul_alonEdgeCount t
  have hsqrt :
      Real.sqrt (8 * (alonEdgeCount t : ℝ) + 1) ≤ 2 * alonParameter t + 1 := by
    rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ 2 * alonParameter t + 1)]
    nlinarith
  have hbaseline :
      baseline (alonEdgeCount t) + t ≤
        (alonEdgeCount t : ℝ) / 2 + (alonParameter t : ℝ) / 4 + t := by
    unfold baseline
    linarith
  refine ⟨H, hHG, hHbip, ?_⟩
  rw [hHcard]
  exact hbaseline.trans hexplicit

/-- Alon's explicit quantitative lower bound for the correction function. -/
theorem alon_correction_lower_bound (t : ℕ) (ht : 1 ≤ t) :
    t ≤ correction (alonEdgeCount t) :=
  le_correction_of_guarantees (guarantees_alonEdgeCount t ht)

/-- **Erdős Problem 127 (Alon).** There is a sequence of edge counts tending
to infinity along which the integral correction above the Edwards baseline
also tends to infinity. -/
theorem erdos127 :
    ∃ mseq : ℕ → ℕ, Tendsto mseq atTop atTop ∧
      Tendsto (fun i ↦ correction (mseq i)) atTop atTop := by
  let mseq : ℕ → ℕ := fun i ↦ alonEdgeCount (i + 1)
  refine ⟨mseq, ?_, ?_⟩
  · rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro i hi
    have him : i + 1 ≤ mseq i := by
      exact parameter_le_edgeCount (i + 1) (by omega)
    omega
  · rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro i hi
    have hic : i + 1 ≤ correction (mseq i) := by
      exact alon_correction_lower_bound (i + 1) (by omega)
    omega

#print axioms Erdos127.erdos127

end Erdos127
