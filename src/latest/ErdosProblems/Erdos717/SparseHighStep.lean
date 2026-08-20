/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- The canonical high-core branch, converted to the real sparse potential. -/

import ErdosProblems.Erdos717.SparseLogArithmetic

open Function Set
open SimpleGraph

namespace Erdos717

theorem sparse_high_step_potential
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a k : ℕ) (hind : G.indepNum ≤ a)
    (ha : 16 * a ≤ Fintype.card V)
    (hnHuge : 10 ^ 100 ≤ Fintype.card V)
    (hdsmall :
      (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ 2 ≤
        1 / 10 ^ (20 : ℕ))
    (hlogCondition :
      ((G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ 2) * a *
          Real.log (1 / ((G.edgeFinset.card : ℝ) /
            (Fintype.card V : ℝ) ^ 2)) ≤
        Real.log (Fintype.card V : ℝ) / 1000000)
    (hhigh : G.edgeSet.ncard ≤ 1000 *
      (sparseCore G
        (degreeCutParameter G.edgeFinset.card (Fintype.card V))
        (patternParameter
          (degreeCutParameter G.edgeFinset.card (Fintype.card V)) a
          (Fintype.card V))).edgeSet.ncard)
    (hXlarge : 320 * Fintype.card V ≤
      (sparseCore G
        (degreeCutParameter G.edgeFinset.card (Fintype.card V))
        (patternParameter
          (degreeCutParameter G.edgeFinset.card (Fintype.card V)) a
          (Fintype.card V))).edgeSet.ncard)
    (hLlarge : 5000 * (Fintype.card V * Fintype.card V * Fintype.card V) ≤
      (sparseCore G
        (degreeCutParameter G.edgeFinset.card (Fintype.card V))
        (patternParameter
          (degreeCutParameter G.edgeFinset.card (Fintype.card V)) a
          (Fintype.card V))).edgeSet.ncard ^ 2)
    (hk : 2 ≤ k) (hnot : ¬Erdos718.ContainsCliqueSubdivision G k) :
    sparsePotential (Fintype.card V) G.edgeFinset.card a < k := by
  classical
  let n := Fintype.card V
  let m := G.edgeFinset.card
  let d : ℝ := (m : ℝ) / (n : ℝ) ^ 2
  let D := degreeCutParameter m n
  let b := patternParameter D a n
  let H := sparseCore G D b
  let h := H.edgeSet.ncard
  let X0 := reservoirSizeParameter h n
  let L := reservoirRouteParameter h n
  let Q := patternSurvivorParameter X0 a b
  change d ≤ 1 / 10 ^ (20 : ℕ) at hdsmall
  change d * (a : ℝ) * Real.log (1 / d) ≤
    Real.log (n : ℝ) / 1000000 at hlogCondition
  have hn : 0 < n := lt_of_lt_of_le (by norm_num) hnHuge
  have haPos : 0 < a := by
    let v : V := Classical.choice (Fintype.card_pos_iff.mp (by simpa [n] using hn))
    have hsingle : G.IsIndepSet ({v} : Finset V) := by simp
    have := hsingle.card_le_indepNum.trans hind
    exact this
  have hmPos : 0 < m := by
    have hdensity := card_sq_le_thirtytwo_mul_edges_mul_indepBound G a hind ha
    by_contra hm0
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
    change n * n ≤ 32 * m * a at hdensity
    rw [hmzero] at hdensity
    nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmPos
  have haR : (0 : ℝ) < a := by exact_mod_cast haPos
  have hd : 0 < d := div_pos hmR (sq_pos_of_pos hnR)
  have hdEq : d * (n : ℝ) ^ 2 = m := by
    dsimp only [d]
    field_simp
  have hA : (1 / 32 : ℝ) ≤ d * a := by
    have hdensity := card_sq_le_thirtytwo_mul_edges_mul_indepBound G a hind ha
    have hdensityR : (n : ℝ) * n ≤ 32 * (m : ℝ) * a := by
      exact_mod_cast hdensity
    nlinarith
  have hDlower : 4 * m ≤ n * D := by
    exact (ceilDiv_le_iff_le_mul hn).mp (by simp [D, degreeCutParameter])
  have hblower : 4 * D * a ≤ n * b := by
    exact (ceilDiv_le_iff_le_mul hn).mp (by simp [b, patternParameter])
  have hpattern : 16 * d * (a : ℝ) ≤ b := by
    have hnat : 16 * m * a ≤ n * n * b := by
      nlinarith [Nat.mul_le_mul_left (4 * a) hDlower,
        Nat.mul_le_mul_left n hblower]
    have hnatR : (16 : ℝ) * m * a ≤ n * n * b := by exact_mod_cast hnat
    nlinarith
  have hDupper : n * D ≤ 4 * m + n := by
    dsimp only [D, degreeCutParameter]
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact (Nat.mul_div_le _ _).trans (Nat.sub_le _ _)
  have hbupperNat : n * b ≤ 4 * D * a + n := by
    dsimp only [b, patternParameter]
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact (Nat.mul_div_le _ _).trans (Nat.sub_le _ _)
  have hbquadratic : n * n * b ≤ 64 * m * a := by
    have h1 := Nat.mul_le_mul_left n hbupperNat
    have h2 := Nat.mul_le_mul_left (4 * a) hDupper
    have hdensity := card_sq_le_thirtytwo_mul_edges_mul_indepBound G a hind ha
    nlinarith
  have hbupper : (b : ℝ) ≤ 64 * (d * a) := by
    have hbR : (n : ℝ) * n * b ≤ 64 * (m : ℝ) * a := by
      exact_mod_cast hbquadratic
    nlinarith
  have hb : 1 ≤ b := by
    by_contra hb0
    have hbzero : b = 0 := by omega
    rw [hbzero] at hpattern
    nlinarith [mul_pos hd haR]
  have hba : b ≤ a := by
    have hd64 : 64 * d ≤ 1 := by
      dsimp only [d] at hdsmall ⊢
      have hpow : (64 : ℝ) ≤ 10 ^ (20 : ℕ) := by norm_num
      nlinarith
    have hbR : (b : ℝ) ≤ a := by nlinarith
    exact_mod_cast hbR
  have hE : 0 < G.edgeFinset.card := by simpa [m] using hmPos
  have hcanonical := sparse_dense_step_canonical G a k hind ha hE
    hhigh hXlarge hLlarge
    (by simpa only [b, D, m, n] using hb)
    (by simpa only [b, D, m, n] using hba) hk hnot
  dsimp only at hcanonical
  have hXlarge' : 320 * n ≤ h := by
    simpa only [h, H, b, D, m, n] using hXlarge
  have hLlarge' : 5000 * (n * n * n) ≤ h ^ 2 := by
    simpa only [h, H, b, D, m, n] using hLlarge
  have hX0 : 20 ≤ X0 := by
    apply reservoirSizeParameter_ge_twenty h n hn
    exact hXlarge'
  have hL5 : 5 ≤ L := by
    apply reservoirRouteParameter_ge_five h n hn
    simpa only [pow_two] using hLlarge'
  have hhigh' : G.edgeSet.ncard ≤ 1000 * h := by
    simpa only [h, H, b, D, m, n] using hhigh
  have hEdgeNat : m ≤ 1000 * h := by
    rw [show m = G.edgeSet.ncard by
      simpa only [m] using
        Erdos718.MaderPrototype.card_edgeFinset_eq_ncard_edgeSet G]
    exact hhigh'
  have hhX : h < 16 * n * (X0 + 1) := by
    have hq : h / (16 * n) < h / (16 * n) + 1 := Nat.lt_succ_self _
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos (by norm_num) hn)] at hq
    simpa [X0, reservoirSizeParameter, mul_comm] using hq
  have hmX : m < 32000 * n * X0 := by
    have hsucc : X0 + 1 ≤ 2 * X0 := by omega
    have := Nat.mul_le_mul_left (16 * n) hsucc
    nlinarith
  let cbin := a.choose b
  have hcbinPos : 0 < cbin := by
    exact Nat.choose_pos hba
  let Y := X0 / 5
  have hXY : X0 < 5 * (Y + 1) := by
    have hq : X0 / 5 < X0 / 5 + 1 := Nat.lt_succ_self _
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 5)] at hq
    dsimp only [Y]
    rw [mul_comm]
    exact hq
  have hYQ : Y < cbin * (Q + 1) := by
    have hq : Y / cbin < Y / cbin + 1 := Nat.lt_succ_self _
    rw [Nat.div_lt_iff_lt_mul hcbinPos] at hq
    have hQeq : Q = Y / cbin := by rfl
    rw [hQeq]
    simpa only [mul_comm] using hq
  have hXQ : X0 < 10 * cbin * (Q + 1) := by
    have hone : 1 ≤ cbin * (Q + 1) := by
      exact Nat.mul_pos hcbinPos (Nat.succ_pos Q)
    have hplus : Y + 1 ≤ 2 * (cbin * (Q + 1)) := by omega
    calc
      X0 < 5 * (Y + 1) := hXY
      _ ≤ 5 * (2 * (cbin * (Q + 1))) := Nat.mul_le_mul_left 5 hplus
      _ = 10 * cbin * (Q + 1) := by ring
  have hdnX : d * n < 32000 * X0 := by
    have hmXR : (m : ℝ) < 32000 * n * X0 := by exact_mod_cast hmX
    rw [show d * (n : ℝ) = (m : ℝ) / n by
      dsimp only [d]
      field_simp]
    rw [div_lt_iff₀ hnR]
    nlinarith only [hmXR]
  have hLlower : d ^ 2 * n < 10 ^ (10 : ℕ) * L := by
    have hhL : h * h < 2000 * (n * n * n) * L := by
      have hq : h * h / (1000 * (n * n * n)) <
          h * h / (1000 * (n * n * n)) + 1 := Nat.lt_succ_self _
      rw [Nat.div_lt_iff_lt_mul
        (Nat.mul_pos (by norm_num) (Nat.mul_pos (Nat.mul_pos hn hn) hn))] at hq
      have hsucc : L + 1 ≤ 2 * L := by omega
      change h * h < (L + 1) * (1000 * (n * n * n)) at hq
      calc
        h * h < (L + 1) * (1000 * (n * n * n)) := hq
        _ ≤ (2 * L) * (1000 * (n * n * n)) :=
          Nat.mul_le_mul_right _ hsucc
        _ = 2000 * (n * n * n) * L := by ring
    have hsquare : m * m ≤ 1000000 * (h * h) := by
      calc
        m * m ≤ (1000 * h) * (1000 * h) := Nat.mul_le_mul hEdgeNat hEdgeNat
        _ = 1000000 * (h * h) := by ring
    have hnat : m * m < 2000000000 * (n * n * n) * L := by
      calc
        m * m ≤ 1000000 * (h * h) := hsquare
        _ < 1000000 * (2000 * (n * n * n) * L) :=
          Nat.mul_lt_mul_of_pos_left hhL (by norm_num)
        _ = 2000000000 * (n * n * n) * L := by ring
    have hnatR : (m : ℝ) * m <
        2000000000 * ((n : ℝ) * n * n) * L := by exact_mod_cast hnat
    rw [show d ^ 2 * (n : ℝ) = ((m : ℝ) * m) / ((n : ℝ) * n * n) by
      dsimp only [d]
      field_simp]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * n * n)]
    calc
      (m : ℝ) * m < 2000000000 * ((n : ℝ) * n * n) * L := hnatR
      _ < 10 ^ (10 : ℕ) * L * ((n : ℝ) * n * n) := by
        have hten : (2000000000 : ℝ) < 10 ^ (10 : ℕ) := by norm_num
        have hLposNat : 0 < L := lt_of_lt_of_le (by norm_num) hL5
        have hLposR : (0 : ℝ) < L := by exact_mod_cast hLposNat
        nlinarith only [hten, show (0 : ℝ) < (n : ℝ) * n * n by positivity,
          hLposR]
  have hcasesReal :
      d * n < 320000 * cbin * k ∨
      (L : ℝ) ^ (b - 1) * (d * n) <
        640000 * cbin * 38 ^ (b - 1) * k ^ (2 * b - 1) := by
    change Q < k ∨ L ^ (b - 1) * Q <
      38 ^ (b - 1) * k ^ (2 * b - 1) at hcanonical
    by_cases hQk : Q < k
    · left
      have hQone : Q + 1 ≤ k := by omega
      have hXk : X0 < 10 * cbin * k := hXQ.trans_le
        (Nat.mul_le_mul_left (10 * cbin) hQone)
      have hXkR : (X0 : ℝ) < 10 * cbin * k := by exact_mod_cast hXk
      calc
        d * (n : ℝ) < 32000 * X0 := hdnX
        _ < 32000 * (10 * cbin * k) :=
          mul_lt_mul_of_pos_left hXkR (by norm_num)
        _ = 320000 * cbin * k := by ring
    · right
      have hpoly := hcanonical.resolve_left hQk
      have hkQ : k ≤ Q := Nat.le_of_not_gt hQk
      have hQone : Q + 1 ≤ 2 * Q := by omega
      have hXQ' : X0 < 20 * cbin * Q := hXQ.trans_le (by
        calc
          10 * cbin * (Q + 1) ≤ 10 * cbin * (2 * Q) :=
            Nat.mul_le_mul_left (10 * cbin) hQone
          _ = 20 * cbin * Q := by ring)
      have hXQ'R : (X0 : ℝ) < 20 * cbin * Q := by exact_mod_cast hXQ'
      have hpolyR : (L : ℝ) ^ (b - 1) * Q <
          38 ^ (b - 1) * k ^ (2 * b - 1) := by exact_mod_cast hpoly
      have hLposNat : 0 < L := lt_of_lt_of_le (by norm_num) hL5
      have hLposR : (0 : ℝ) < L := by exact_mod_cast hLposNat
      have hscale : (32000 : ℝ) * X0 < 640000 * cbin * Q := by
        calc
          (32000 : ℝ) * X0 < 32000 * (20 * cbin * Q) :=
            mul_lt_mul_of_pos_left hXQ'R (by norm_num)
          _ = 640000 * cbin * Q := by ring
      calc
        (L : ℝ) ^ (b - 1) * (d * n) <
            (L : ℝ) ^ (b - 1) * (32000 * X0) := by
              exact mul_lt_mul_of_pos_left hdnX (pow_pos hLposR _)
        _ < (L : ℝ) ^ (b - 1) * (640000 * cbin * Q) := by
              exact mul_lt_mul_of_pos_left hscale (pow_pos hLposR _)
        _ < 640000 * cbin * 38 ^ (b - 1) * k ^ (2 * b - 1) := by
              calc
                (L : ℝ) ^ (b - 1) * (640000 * cbin * Q) =
                    (640000 * cbin) * ((L : ℝ) ^ (b - 1) * Q) := by ring
                _ < (640000 * cbin) *
                    (38 ^ (b - 1) * k ^ (2 * b - 1)) :=
                      mul_lt_mul_of_pos_left hpolyR (by positivity)
                _ = 640000 * cbin * 38 ^ (b - 1) * k ^ (2 * b - 1) := by ring
  have hlogn : 100 ≤ Real.log (n : ℝ) := by
    have hcast : (10 : ℝ) ^ (100 : ℕ) ≤ n := by exact_mod_cast hnHuge
    have hmono := Real.strictMonoOn_log.monotoneOn
      (pow_pos (by norm_num : (0 : ℝ) < 10) _) hnR hcast
    rw [Real.log_pow] at hmono
    have hlogTen : 1 < Real.log (10 : ℝ) := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 10)]
      exact Real.exp_one_lt_three.trans (by norm_num)
    norm_num at hmono
    nlinarith only [hmono, hlogTen]
  have hresult := sparse_high_order_real n a b k L cbin d hn haPos hb hk hd
    hdsmall hA hbupper hlogn hlogCondition rfl hpattern hLlower hcasesReal
  change Real.exp (-1000) * d ^ 4 * Real.sqrt n *
      Real.exp (Real.log n / (1000000000000 * d * a)) < (k : ℝ)
  exact hresult

end Erdos717
