import ErdosProblems.Erdos581.UpperSpectrum
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Erdős 581: exact-edge padding for the upper witness
-/

open Finset Set
open scoped BigOperators

namespace Erdos581

noncomputable section

/-- A triangle-free graph with exactly `m` edges whose every cut has surplus
at most `B` over half its edges. -/
def HasUpperWitness (m : ℕ) (B : ℝ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    G.CliqueFree 3 ∧ G.edgeSet.ncard = m ∧
      ∀ s : Set V, ((cutGraph G s).edgeSet.ncard : ℝ) ≤ (m : ℝ) / 2 + B

private lemma ncard_edgeSet_sum
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (G ⊕g H).edgeSet.ncard = G.edgeSet.ncard + H.edgeSet.ncard := by
  calc
    (G ⊕g H).edgeSet.ncard = Nat.card (G ⊕g H).edgeSet := by simp
    _ = Nat.card (G.edgeSet ⊕ H.edgeSet) :=
      Nat.card_congr SimpleGraph.edgeSetSumEquiv
    _ = Nat.card G.edgeSet + Nat.card H.edgeSet := Nat.card_sum
    _ = G.edgeSet.ncard + H.edgeSet.ncard := by simp

private lemma cliqueFree_sum_three
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.CliqueFree 3) (hH : H.CliqueFree 3) :
    (G ⊕g H).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨u, v, w, huv, huw, hvw, hset⟩ := SimpleGraph.is3Clique_iff.mp hs
  cases u with
  | inl u =>
      cases v with
      | inl v =>
          cases w with
          | inl w =>
              apply hG {u, v, w}
              exact SimpleGraph.is3Clique_iff.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩
          | inr w => simp at huw
      | inr v => simp at huv
  | inr u =>
      cases v with
      | inl v => simp at huv
      | inr v =>
          cases w with
          | inl w => simp at huw
          | inr w =>
              apply hH {u, v, w}
              exact SimpleGraph.is3Clique_iff.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩

private lemma cutGraph_sum
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (s : Set (V ⊕ W)) :
    cutGraph (G ⊕g H) s =
      cutGraph G {v | Sum.inl v ∈ s} ⊕g cutGraph H {w | Sum.inr w ∈ s} := by
  ext (u | u) (v | v) <;> simp [cutGraph_adj]

lemma HasUpperWitness.add {m n : ℕ} {B C : ℝ}
    (hm : HasUpperWitness m B) (hn : HasUpperWitness n C) :
    HasUpperWitness (m + n) (B + C) := by
  classical
  rcases hm with ⟨V, iV, G, htriG, hedgeG, hcutG⟩
  rcases hn with ⟨W, iW, H, htriH, hedgeH, hcutH⟩
  letI : Fintype V := iV
  letI : Fintype W := iW
  refine ⟨V ⊕ W, inferInstance, G ⊕g H, cliqueFree_sum_three htriG htriH, ?_, ?_⟩
  · rw [ncard_edgeSet_sum, hedgeG, hedgeH]
  · intro s
    rw [cutGraph_sum, ncard_edgeSet_sum]
    have hL := hcutG {v | Sum.inl v ∈ s}
    have hR := hcutH {w | Sum.inr w ∈ s}
    push_cast
    norm_num at hL hR ⊢
    linarith

lemma HasUpperWitness.nsmul {m : ℕ} {B : ℝ}
    (h : HasUpperWitness m B) (a : ℕ) :
    HasUpperWitness (a * m) (a * B) := by
  induction a with
  | zero =>
      refine ⟨Fin 0, inferInstance, ⊥, ?_, by simp, ?_⟩
      · intro s hs
        have hsempty : s = ∅ := by
          ext x
          exact Fin.elim0 x
        rw [hsempty] at hs
        simpa using hs.card_eq
      · intro s
        have hbot : cutGraph (⊥ : SimpleGraph (Fin 0)) s = ⊥ := by
          ext u v
          simp [cutGraph_adj]
        rw [hbot]
        simp
  | succ a ih =>
      simpa [Nat.succ_mul, Nat.cast_add, Nat.cast_mul, add_mul] using ih.add h

lemma matchingWitness (m : ℕ) : HasUpperWitness m ((m : ℝ) / 2) := by
  let G := completeBipartiteGraph (Fin 1) (Fin m)
  have hbip : G.IsBipartite := by
    simpa [G] using completeBipartiteGraph_isBipartite 1 m
  refine ⟨Fin 1 ⊕ Fin m, inferInstance, G,
    isBipartite_cliqueFree_three hbip, ?_, ?_⟩
  · simpa [G] using ncard_edgeSet_completeBipartiteGraph 1 m
  · intro s
    have hsub := SimpleGraph.edgeSet_mono (cutGraph_le G s)
    have hc := Set.ncard_le_ncard hsub
    have hedge : G.edgeSet.ncard = m := by
      simpa [G] using ncard_edgeSet_completeBipartiteGraph 1 m
    rw [hedge] at hc
    have hcr : ((cutGraph G s).edgeSet.ncard : ℝ) ≤ m := by exact_mod_cast hc
    norm_num
    linarith

lemma blockWitness (t : ℕ) :
    HasUpperWitness (UpperBlock.blockEdges t) (3 * (UpperBlock.q t : ℝ) ^ 4 / 4) := by
  letI : Fintype (UpperBlock.F t) := Fintype.ofFinite _
  letI : DecidableEq (UpperBlock.F t) := Classical.decEq _
  letI : DecidableRel (UpperBlock.graph t).Adj := fun _ _ ↦ Finset.decidableMem _ _
  refine ⟨UpperBlock.V t, inferInstance, UpperBlock.graph t,
    UpperBlock.graph_triangleFree t, ?_, ?_⟩
  · rw [← UpperBlock.card_edgeFinset_graph]
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  · exact UpperBlock.cut_graph_le_q t

lemma HasUpperWitness.mono {m : ℕ} {B C : ℝ}
    (h : HasUpperWitness m B) (hBC : B ≤ C) : HasUpperWitness m C := by
  rcases h with ⟨V, iV, G, htri, hedge, hcut⟩
  refine ⟨V, iV, G, htri, hedge, ?_⟩
  intro s
  exact (hcut s).trans (by linarith)

/-- Greedy exact-edge padding below the next block scale.  The error is kept
in the algebraic form `64 q^4` until the final real-power conversion. -/
lemma paddingLevel (j : ℕ) : ∀ m < UpperBlock.blockEdges (j + 1),
    HasUpperWitness m (64 * (UpperBlock.q j : ℝ) ^ 4) := by
  induction j with
  | zero =>
      intro m hm
      let e := UpperBlock.blockEdges 0
      let a := m / e
      let r := m % e
      have he : e = 4 := by norm_num [e, UpperBlock.blockEdges, UpperBlock.q]
      have hq : UpperBlock.q 0 = 2 := by norm_num [UpperBlock.q]
      have hepos : 0 < e := by rw [he]; omega
      have hratio := UpperBlock.blockEdges_ratio_upper 0
      have hmlt : m < 48 * e := hm.trans_le hratio
      have ha : a < 48 := (Nat.div_lt_iff_lt_mul hepos).2 (by simpa [mul_comm] using hmlt)
      have hr : r < e := Nat.mod_lt m hepos
      have hw := (blockWitness 0).nsmul a |>.add (matchingWitness r)
      have hdecomp : a * e + r = m := by
        simpa [a, r, mul_comm] using (Nat.div_add_mod m e)
      rw [← hdecomp]
      apply hw.mono
      rw [hq, he] at *
      have harNat : a ≤ 47 := Nat.le_pred_of_lt ha
      have hrrNat : r ≤ 3 := Nat.le_pred_of_lt hr
      have har : (a : ℝ) ≤ (47 : ℝ) := by exact_mod_cast harNat
      have hrr : (r : ℝ) ≤ (3 : ℝ) := by exact_mod_cast hrrNat
      norm_num
      calc
        (a : ℝ) * 12 + (r : ℝ) / 2 ≤ 47 * 12 + 3 / 2 := by gcongr
        _ ≤ 1024 := by norm_num
  | succ j ih =>
      intro m hm
      let e := UpperBlock.blockEdges (j + 1)
      let a := m / e
      let r := m % e
      have hepos : 0 < e := UpperBlock.blockEdges_pos (j + 1)
      have hratio := UpperBlock.blockEdges_ratio_upper (j + 1)
      have hmlt : m < 48 * e := hm.trans_le hratio
      have ha : a < 48 := (Nat.div_lt_iff_lt_mul hepos).2 (by simpa [mul_comm] using hmlt)
      have hr : r < e := Nat.mod_lt m hepos
      have hrem : HasUpperWitness r (64 * (UpperBlock.q j : ℝ) ^ 4) := by
        exact ih r (by simpa [e, Nat.add_assoc] using hr)
      have hw := (blockWitness (j + 1)).nsmul a |>.add hrem
      have hdecomp : a * e + r = m := by
        simpa [a, r, mul_comm] using (Nat.div_add_mod m e)
      rw [← hdecomp]
      apply hw.mono
      have hq := UpperBlock.q_succ j
      have harNat : a ≤ 47 := Nat.le_pred_of_lt ha
      have har : (a : ℝ) ≤ (47 : ℝ) := by exact_mod_cast harNat
      rw [hq]
      norm_num [Nat.cast_mul, pow_succ]
      let Q : ℝ := (UpperBlock.q j : ℝ) ^ 4
      have hQ : 0 ≤ Q := by positivity
      have hmul : (a : ℝ) * Q ≤ 47 * Q := mul_le_mul_of_nonneg_right har hQ
      dsimp [Q] at hmul
      ring_nf at hmul ⊢
      nlinarith

private lemma blockEdges_linear_lower (t : ℕ) :
    4 * (t + 1) ≤ UpperBlock.blockEdges t := by
  induction t with
  | zero => norm_num [UpperBlock.blockEdges, UpperBlock.q]
  | succ t ih =>
      have hr := UpperBlock.blockEdges_ratio_lower t
      have hp := UpperBlock.blockEdges_pos t
      omega

def upperLevel (m : ℕ) : ℕ :=
  Nat.findGreatest (fun t ↦ UpperBlock.blockEdges t ≤ m) m

private lemma upperLevel_spec {m : ℕ} (hm : 4 ≤ m) :
    UpperBlock.blockEdges (upperLevel m) ≤ m := by
  apply Nat.findGreatest_spec (P := fun t ↦ UpperBlock.blockEdges t ≤ m) (Nat.zero_le m)
  norm_num [UpperBlock.blockEdges, UpperBlock.q]
  exact hm

private lemma upperLevel_next {m : ℕ} (hm : 4 ≤ m) :
    m < UpperBlock.blockEdges (upperLevel m + 1) := by
  by_cases hle : upperLevel m + 1 ≤ m
  · exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest
      (P := fun t ↦ UpperBlock.blockEdges t ≤ m) (Nat.lt_succ_self _) hle)
  · have hlev : upperLevel m ≤ m := Nat.findGreatest_le _
    have heq : upperLevel m = m := by omega
    rw [heq]
    have hlin := blockEdges_linear_lower (m + 1)
    omega

private lemma q_pow_five_le_eight_blockEdges (t : ℕ) :
    UpperBlock.q t ^ 5 ≤ 8 * UpperBlock.blockEdges t := by
  have hq := UpperBlock.two_le_q t
  have hfour := UpperBlock.four_mul_blockEdges t
  have hbase : UpperBlock.q t ≤ 2 * (UpperBlock.q t - 1) := by omega
  calc
    UpperBlock.q t ^ 5 = UpperBlock.q t ^ 4 * UpperBlock.q t := by ring
    _ ≤ UpperBlock.q t ^ 4 * (2 * (UpperBlock.q t - 1)) :=
      Nat.mul_le_mul_left _ hbase
    _ = 2 * (UpperBlock.q t ^ 4 * (UpperBlock.q t - 1)) := by ring
    _ = 8 * UpperBlock.blockEdges t := by rw [← hfour]; ring

private lemma pow_four_le_sixteen_rpow {q m : ℕ} (hq : 0 < q)
    (hqm : q ^ 5 ≤ 8 * m) :
    (q : ℝ) ^ 4 ≤ 16 * (m : ℝ) ^ ((4 : ℝ) / 5) := by
  have hqmR : (q : ℝ) ^ 5 ≤ 8 * (m : ℝ) := by exact_mod_cast hqm
  have hbase : (((q : ℝ) / 2) ^ 5) ≤ (m : ℝ) := by
    nlinarith
  have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ ((q : ℝ) / 2) ^ 5)
    hbase (by norm_num : 0 ≤ (1 : ℝ) / 5)
  have hleft : ((((q : ℝ) / 2) ^ 5 : ℝ) ^ ((1 : ℝ) / 5)) = (q : ℝ) / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (q : ℝ) / 2)]
    norm_num
  rw [hleft] at hroot
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (q : ℝ) / 2) hroot 4
  have hright : (((m : ℝ) ^ ((1 : ℝ) / 5)) ^ 4) =
      (m : ℝ) ^ ((4 : ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]
    norm_num
  rw [hright] at hpow
  nlinarith

/-- Exact-edge upper witness with an explicit absolute constant. -/
theorem uniformUpperWitness (m : ℕ) :
    HasUpperWitness m (1024 * (m : ℝ) ^ ((4 : ℝ) / 5)) := by
  by_cases hm : m < 4
  · apply (matchingWitness m).mono
    by_cases hm0 : m = 0
    · subst m
      norm_num [Real.zero_rpow]
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
      have hrpow : (1 : ℝ) ≤ (m : ℝ) ^ ((4 : ℝ) / 5) :=
        Real.one_le_rpow hm1 (by norm_num)
      have hmR : (m : ℝ) ≤ 3 := by exact_mod_cast (Nat.le_pred_of_lt hm)
      nlinarith
  · have hm4 : 4 ≤ m := by omega
    let t := upperLevel m
    have hlow : UpperBlock.blockEdges t ≤ m := by simpa [t] using upperLevel_spec hm4
    have hnext : m < UpperBlock.blockEdges (t + 1) := by
      simpa [t] using upperLevel_next hm4
    have hw := paddingLevel t m hnext
    apply hw.mono
    have hq5 : UpperBlock.q t ^ 5 ≤ 8 * m :=
      (q_pow_five_le_eight_blockEdges t).trans (Nat.mul_le_mul_left 8 hlow)
    have hqpos : 0 < UpperBlock.q t := by
      have := UpperBlock.two_le_q t
      omega
    have hq4 := pow_four_le_sixteen_rpow hqpos hq5
    nlinarith

end

end Erdos581
