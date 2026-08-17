/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos615.Erdos615Construction

open Filter SimpleGraph Set Real
open scoped Topology BigOperators ENNReal NNReal

namespace Erdos615

attribute [local instance] Classical.propDecidable

open Construction

lemma eventually_asymptotic_numeric_bound :
    ∀ᶠ K : ℕ in atTop,
      200 * (K : ℝ) ^ 19 * Real.exp (-(K : ℝ)) + 200 / (K : ℝ) ^ 3 < 1 := by
  have hExp : Tendsto
      (fun K : ℕ ↦ 200 * (K : ℝ) ^ 19 * Real.exp (-(K : ℝ)))
      atTop (𝓝 0) := by
    have H := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 19).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def, mul_assoc] using H.const_mul 200
  have hInv : Tendsto (fun K : ℕ ↦ 200 / (K : ℝ) ^ 3) atTop (𝓝 0) := by
    have H : Tendsto (fun K : ℕ ↦ ((K : ℝ)⁻¹) ^ 3) atTop (𝓝 0) :=
      by simpa [Function.comp_def] using
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop (R := ℝ))).pow 3
    simpa [div_eq_mul_inv, inv_pow] using H.const_mul 200
  have H := hExp.add hInv
  exact (tendsto_order.1 H).2 1 (by norm_num)

lemma isIndepSet_map_equiv {α β : Type*} (G : SimpleGraph α) (e : α ≃ β)
    {s : Finset α} (hs : G.IsIndepSet s) :
    (G.map e.toEmbedding).IsIndepSet (s.map e.toEmbedding) := by
  rw [SimpleGraph.isIndepSet_iff] at hs ⊢
  intro x hx y hy hxy
  rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
  rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
  have hxy' : x' ≠ y' := fun H ↦ hxy (congrArg e H)
  intro hadj
  exact hs hx' hy' hxy'
    ((SimpleGraph.Embedding.map e.toEmbedding G).map_adj_iff.mp hadj)

lemma indepNum_map_equiv {α β : Type*} [Finite α] [Finite β]
    (G : SimpleGraph α) (e : α ≃ β) :
    (G.map e.toEmbedding).indepNum = G.indepNum := by
  apply le_antisymm
  · rcases (G.map e.toEmbedding).exists_isNIndepSet_indepNum with ⟨s, hs⟩
    have ht := isIndepSet_map_equiv (G.map e.toEmbedding) e.symm hs.isIndepSet
    have hgraph : (G.map e.toEmbedding).map e.symm.toEmbedding = G := by
      ext x y
      simp
    rw [hgraph] at ht
    have hcard := ht.card_le_indepNum
    simpa [hs.card_eq] using hcard
  · rcases G.exists_isNIndepSet_indepNum with ⟨s, hs⟩
    have ht := isIndepSet_map_equiv G e hs.isIndepSet
    have hcard := ht.card_le_indepNum
    simpa [hs.card_eq] using hcard

structure RawCounterexample (c : ℝ) (N : ℕ) where
  Vertex : Type
  fintypeVertex : Fintype Vertex
  graph : SimpleGraph Vertex
  card_pos : 0 < @Fintype.card Vertex fintypeVertex
  card_gt_one : 1 < @Fintype.card Vertex fintypeVertex
  card_lower : N ≤ @Fintype.card Vertex fintypeVertex
  edge_density : (1 / 8 - c) *
    ((@Fintype.card Vertex fintypeVertex : ℕ) : ℝ) ^ 2 ≤ Nat.card graph.edgeSet
  cliqueFree : graph.CliqueFree 4
  indep_log_lt : (graph.indepNum : ℝ) *
    Real.log ((@Fintype.card Vertex fintypeVertex : ℕ) : ℝ) <
      (@Fintype.card Vertex fintypeVertex : ℕ)

lemma exists_raw_counterexample (c : ℝ) (hc : 0 < c) (N : ℕ) :
    Nonempty (RawCounterexample c N) := by
  have hInv : Tendsto (fun K : ℕ ↦ 10 / (K : ℝ)) atTop (𝓝 0) := by
    have H := (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 10
    simpa [Function.comp_def, div_eq_mul_inv] using H
  have hDensity : ∀ᶠ K : ℕ in atTop, 10 / (K : ℝ) < c :=
    (tendsto_order.1 hInv).2 c (by simpa using hc)
  have hLarge : ∀ᶠ K : ℕ in atTop, 10 ≤ K ∧ N ≤ K :=
    (eventually_ge_atTop 10).and (eventually_ge_atTop N)
  obtain ⟨K, ⟨hK10, hNK⟩, hKc, hKasym⟩ :=
    (hLarge.and (hDensity.and eventually_asymptotic_numeric_bound)).exists
  have hKpos : 0 < K := by omega
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hKone : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  let h : ℕ := K ^ 12
  have hh : 1 < h := by
    have Hpow : 2 ^ 12 ≤ K ^ 12 := Nat.pow_le_pow_left (by omega) 12
    norm_num [h] at Hpow ⊢
    omega
  have hh0 : 0 < h := Nat.zero_lt_of_lt hh
  let a : ℝ := 1 / (K : ℝ) ^ 7
  let ρ : ℝ := a / 16
  have ha : 0 < a := by dsimp [a]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hsqrt : Real.sqrt (h : ℝ) = (K : ℝ) ^ 6 := by
    rw [show (h : ℝ) = ((K : ℝ) ^ 6) ^ 2 by
      norm_num [h]
      ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hβ : a + 2 * ρ = 9 / (8 * (K : ℝ) ^ 7) := by
    dsimp [a, ρ]
    field_simp
    ring
  have herror : 4 * (a + 2 * ρ) * Real.sqrt h = 9 / (2 * (K : ℝ)) := by
    rw [hβ, hsqrt]
    field_simp
    ring
  have hβ0 : 0 ≤ a + 2 * ρ := by positivity
  have hβ1 : a + 2 * ρ ≤ 1 := by
    rw [hβ]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * K ^ 7)).2
    have hpowK : (K : ℝ) ≤ K ^ 7 := by
      calc
        (K : ℝ) = K * 1 := by ring
        _ ≤ K * K ^ 6 := mul_le_mul_of_nonneg_left
          (one_le_pow₀ hKone) hKR.le
        _ = K ^ 7 := by ring
    have hK9 : (9 : ℝ) ≤ K := by exact_mod_cast (show 9 ≤ K by omega)
    nlinarith
  have hsmall : 4 * (a + 2 * ρ) * Real.sqrt h ≤ 1 / 2 := by
    rw [herror]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).2
    nlinarith [show (9 : ℝ) ≤ K by exact_mod_cast (show 9 ≤ K by omega)]
  have ha0 : 0 ≤ a := ha.le
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact (div_le_one (by positivity)).2 (one_le_pow₀ hKone)
  have ha2 : a ≤ 2 := ha1.trans (by norm_num)
  have ha4 : a < 1 / 4 := by
    have hpow : (4 : ℝ) < K ^ 7 := by
      have hK4 : (4 : ℝ) < K := by exact_mod_cast (show 4 < K by omega)
      calc
        (4 : ℝ) < K := hK4
        _ ≤ K ^ 7 := by
          calc
            (K : ℝ) = K * 1 := by ring
            _ ≤ K * K ^ 6 := mul_le_mul_of_nonneg_left
              (one_le_pow₀ hKone) hKR.le
            _ = K ^ 7 := by ring
    dsimp [a]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < K ^ 7)]
    nlinarith
  have haMix : a < 2 * (Real.sqrt 2 - 1) := by
    have hsqrt0 := Real.sqrt_nonneg 2
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrt54 : (5 : ℝ) / 4 < Real.sqrt 2 := by nlinarith
    have haQuarter := ha4
    nlinarith
  have hd1 : 1 ≤ 2 - a + 2 * ρ := by
    nlinarith [hρ.le]
  have hρ4 : ρ ≤ 4 := by
    have : ρ < 1 := by
      dsimp [ρ]
      nlinarith [ha4]
    linarith
  let B : ℕ := netCard h ρ hρ
  have hBpos : 0 < B := netCard_pos h ρ hh0 hρ
  let L : ℕ := (B + 1) * K ^ 22
  have hLpos : 0 < L := by dsimp [L]; positivity
  let M : ℕ := copyCard h ρ hh0 hρ L
  let V := Bool × CopyVertex h ρ hh0 hρ L
  let G : SimpleGraph V := BEGraph h ρ hh0 hρ L a
  have hMlower : L ≤ M := scale_le_copyCard h ρ hh0 hρ L
  have hMupper : M ≤ L + B := copyCard_le_scale_add h ρ hh0 hρ L
  have hedgeRaw : (L : ℝ) ^ 2 *
      (1 / 2 - 4 * (a + 2 * ρ) * Real.sqrt h) ≤ Nat.card G.edgeSet := by
    simpa [G] using BEGraph_edgeCard_lower h ρ hh hρ L a hβ0 hβ1 hsmall
  have hfreeRaw : G.CliqueFree 4 := by
    simpa [G] using BEGraph_cliqueFree_four h ρ hh0 hρ L a ha0 ha4 haMix
  have hindRaw : (G.indepNum : ℝ) ≤ 2 *
      ((L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + B) := by
    simpa [G] using BEGraph_indepNum_bound h ρ hh0 hρ L a ha2 hd1
  have hBbound : (B : ℝ) ≤ (128 * (K : ℝ) ^ 7) ^ h := by
    have H := netCard_le_pow h ρ hh0 hρ hρ4
    have hbase : 8 / ρ = 128 * (K : ℝ) ^ 7 := by
      dsimp [ρ, a]
      field_simp
      ring
    simpa [B, hbase] using H
  have hK22 : (K : ℝ) ≤ K ^ 22 := by
    calc
      (K : ℝ) = K * 1 := by ring
      _ ≤ K * K ^ 21 := mul_le_mul_of_nonneg_left
        (one_le_pow₀ hKone) hKR.le
      _ = K ^ 22 := by ring
  have hBKleL : (B : ℝ) * K ≤ L := by
    calc
      (B : ℝ) * K ≤ B * K ^ 22 :=
        mul_le_mul_of_nonneg_left hK22 (Nat.cast_nonneg B)
      _ ≤ (B + 1) * K ^ 22 := by
        gcongr
        norm_num
      _ = (L : ℕ) := by norm_cast
  have hBdiv : (B : ℝ) ≤ L / K := (le_div_iff₀ hKR).2 hBKleL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hMR : (0 : ℝ) < M := by
    exact_mod_cast (hLpos.trans_le hMlower)
  have hMbound : (M : ℝ) ≤ L * (1 + 1 / K) := by
    have HM : (M : ℝ) ≤ L + B := by exact_mod_cast hMupper
    calc
      (M : ℝ) ≤ L + B := HM
      _ ≤ L + L / K := by gcongr
      _ = L * (1 + 1 / K) := by ring
  have ht0 : (0 : ℝ) ≤ 1 / K := by positivity
  have ht1 : (1 : ℝ) / K ≤ 1 := (div_le_one hKR).2 hKone
  have honePlusSq : (1 + (1 : ℝ) / K) ^ 2 ≤ 1 + 3 / K := by
    have hsq : ((1 : ℝ) / K) ^ 2 ≤ 1 / K := by
      nlinarith only [ht0, ht1]
    calc
      (1 + (1 : ℝ) / K) ^ 2 =
          1 + 2 * ((1 : ℝ) / K) + ((1 : ℝ) / K) ^ 2 := by ring
      _ ≤ 1 + 2 * ((1 : ℝ) / K) + 1 / K := by gcongr
      _ = 1 + 3 / K := by ring
  have hvertexSq : ((2 * M : ℕ) : ℝ) ^ 2 ≤
      4 * (L : ℝ) ^ 2 * (1 + 3 / K) := by
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (M : ℝ)) hMbound 2
    calc
      ((2 * M : ℕ) : ℝ) ^ 2 = 4 * (M : ℝ) ^ 2 := by push_cast; ring
      _ ≤ 4 * ((L : ℝ) * (1 + 1 / K)) ^ 2 := by gcongr
      _ = 4 * (L : ℝ) ^ 2 * (1 + 1 / K) ^ 2 := by ring
      _ ≤ 4 * (L : ℝ) ^ 2 * (1 + 3 / K) := by gcongr
  have hedgeRaw' : (L : ℝ) ^ 2 * (1 / 2 - 9 / (2 * K)) ≤
      Nat.card G.edgeSet := by
    simpa [herror] using hedgeRaw
  have hdensityRaw : (1 / 8 - c) * (((2 * M : ℕ) : ℝ) ^ 2) ≤
      Nat.card G.edgeSet := by
    by_cases hc8 : 1 / 8 - c ≤ 0
    · exact (mul_nonpos_of_nonpos_of_nonneg hc8 (sq_nonneg _)).trans
        (Nat.cast_nonneg _)
    · have hc8nonneg : 0 ≤ 1 / 8 - c := le_of_not_ge hc8
      have hct : 10 * ((1 : ℝ) / K) < c := by
        simpa [div_eq_mul_inv, mul_assoc] using hKc
      have hcoeff : 4 * (1 / 8 - c) * (1 + 3 / K) ≤
          1 / 2 - 9 / (2 * K) := by
        have hctnonneg : 0 ≤ c * ((1 : ℝ) / K) := mul_nonneg hc.le ht0
        calc
          4 * (1 / 8 - c) * (1 + 3 / K) =
              1 / 2 + (3 / 2) * (1 / K) - 4 * c -
                12 * (c * (1 / K)) := by ring
          _ ≤ 1 / 2 + (3 / 2) * (1 / K) - 4 * c := by
            nlinarith only [hctnonneg]
          _ ≤ 1 / 2 - (9 / 2) * (1 / K) := by
            nlinarith only [hct, ht0]
          _ = 1 / 2 - 9 / (2 * K) := by field_simp
      calc
        (1 / 8 - c) * (((2 * M : ℕ) : ℝ) ^ 2) ≤
            (1 / 8 - c) * (4 * (L : ℝ) ^ 2 * (1 + 3 / K)) :=
          mul_le_mul_of_nonneg_left hvertexSq hc8nonneg
        _ = (L : ℝ) ^ 2 * (4 * (1 / 8 - c) * (1 + 3 / K)) := by ring
        _ ≤ (L : ℝ) ^ 2 * (1 / 2 - 9 / (2 * K)) :=
          mul_le_mul_of_nonneg_left hcoeff (sq_nonneg _)
        _ ≤ Nat.card G.edgeSet := hedgeRaw'
  let A : ℝ := (128 * (K : ℝ) ^ 7) ^ h
  have hQone : (1 : ℝ) ≤ 128 * K ^ 7 := by
    have : (1 : ℝ) ≤ K ^ 7 := one_le_pow₀ hKone
    nlinarith only [this]
  have hAone : (1 : ℝ) ≤ A := by
    dsimp [A]
    exact one_le_pow₀ hQone
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hAone
  have hB_A : (B : ℝ) ≤ A := hBbound
  have hLupper : (L : ℝ) ≤ 2 * A * K ^ 22 := by
    change (((B + 1) * K ^ 22 : ℕ) : ℝ) ≤ _
    push_cast
    have hB1 : (B : ℝ) + 1 ≤ 2 * A := by
      nlinarith only [hB_A, hAone]
    exact mul_le_mul_of_nonneg_right hB1 (by positivity)
  have hBleL : (B : ℝ) ≤ L := by
    calc
      (B : ℝ) ≤ L / K := hBdiv
      _ ≤ L := div_le_self hLR.le hKone
  have hMtwice : (M : ℝ) ≤ 2 * L := by
    have HM : (M : ℝ) ≤ L + B := by exact_mod_cast hMupper
    nlinarith only [HM, hBleL]
  have hnUpper : (((2 * M : ℕ) : ℝ)) ≤ 8 * A * K ^ 22 := by
    push_cast
    nlinarith only [hMtwice, hLupper]
  have hnPos : (0 : ℝ) < ((2 * M : ℕ) : ℝ) := by
    push_cast
    nlinarith only [hMR]
  have hRhsPos : (0 : ℝ) < 8 * A * K ^ 22 := by positivity
  have hlogMono : Real.log ((2 * M : ℕ) : ℝ) ≤
      Real.log (8 * A * K ^ 22) := Real.log_le_log hnPos hnUpper
  have hlogEq : Real.log (8 * A * K ^ 22) =
      Real.log 8 + (h : ℝ) * Real.log (128 * K ^ 7) +
        22 * Real.log K := by
    rw [Real.log_mul (mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) hApos.ne')
      (pow_ne_zero _ hKR.ne'),
      Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hApos.ne',
      show A = (128 * (K : ℝ) ^ 7) ^ h by rfl,
      Real.log_pow, Real.log_pow]
    ring
  have hlog8 : Real.log 8 ≤ 7 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)).trans_eq (by norm_num)
  have hlogQ : Real.log (128 * (K : ℝ) ^ 7) ≤ 128 * K ^ 7 := by
    have H := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 128 * K ^ 7)
    linarith only [H]
  have hlogK : Real.log (K : ℝ) ≤ K := by
    have H := Real.log_le_sub_one_of_pos hKR
    linarith only [H]
  have hhcast : (h : ℝ) = (K : ℝ) ^ 12 := by norm_num [h]
  have htermQ : (h : ℝ) * Real.log (128 * K ^ 7) ≤ 128 * K ^ 19 := by
    calc
      (h : ℝ) * Real.log (128 * K ^ 7) ≤ h * (128 * K ^ 7) :=
        mul_le_mul_of_nonneg_left hlogQ (Nat.cast_nonneg h)
      _ = 128 * K ^ 19 := by rw [hhcast]; ring
  have htermK : 22 * Real.log (K : ℝ) ≤ 22 * K := by
    nlinarith only [hlogK]
  have hK19one : (1 : ℝ) ≤ K ^ 19 := one_le_pow₀ hKone
  have hKleK19 : (K : ℝ) ≤ K ^ 19 := by
    calc
      (K : ℝ) = K * 1 := by ring
      _ ≤ K * K ^ 18 := mul_le_mul_of_nonneg_left
        (one_le_pow₀ hKone) hKR.le
      _ = K ^ 19 := by ring
  have hlogBound : Real.log ((2 * M : ℕ) : ℝ) ≤ 200 * K ^ 19 := by
    rw [hlogEq] at hlogMono
    nlinarith only [hlogMono, hlog8, htermQ, htermK, hK19one, hKleK19]
  have hradiusBase : (2 - a + 2 * ρ) / 2 =
      1 - 7 / (16 * (K : ℝ) ^ 7) := by
    dsimp [a, ρ]
    field_simp
    ring
  let x : ℝ := 7 / (16 * (K : ℝ) ^ 7)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * K ^ 7)).2
    have : (1 : ℝ) ≤ K ^ 7 := one_le_pow₀ hKone
    nlinarith only [this]
  have honeSub : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hbaseExp : 1 - x ≤ Real.exp (-x) := by
    simpa [add_comm] using Real.add_one_le_exp (-x)
  have hpowExp : (1 - x) ^ h ≤ Real.exp (-x) ^ h :=
    pow_le_pow_left₀ honeSub hbaseExp h
  have hexponent : Real.exp (-x) ^ h = Real.exp (-(7 * (K : ℝ) ^ 5 / 16)) := by
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    dsimp [x]
    rw [hhcast]
    field_simp
  have hKexp : (K : ℝ) ≤ 7 * K ^ 5 / 16 := by
    have hK4 : (16 : ℝ) ≤ 7 * K ^ 4 := by
      have hK4ten : (10 : ℝ) ^ 4 ≤ K ^ 4 :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hK10) 4
      norm_num at hK4ten ⊢
      nlinarith only [hK4ten]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
    have Hmul := mul_le_mul_of_nonneg_left hK4 hKR.le
    nlinarith only [Hmul]
  have halphaExp : ((2 - a + 2 * ρ) / 2) ^ h ≤ Real.exp (-(K : ℝ)) := by
    rw [hradiusBase]
    change (1 - x) ^ h ≤ _
    calc
      (1 - x) ^ h ≤ Real.exp (-x) ^ h := hpowExp
      _ = Real.exp (-(7 * (K : ℝ) ^ 5 / 16)) := hexponent
      _ ≤ Real.exp (-(K : ℝ)) := Real.exp_le_exp.mpr (by linarith only [hKexp])
  have hBK22leL : (B : ℝ) * K ^ 22 ≤ L := by
    change (B : ℝ) * K ^ 22 ≤ (((B + 1) * K ^ 22 : ℕ) : ℝ)
    push_cast
    gcongr
    norm_num
  have hRound : (B : ℝ) / L ≤ 1 / K ^ 22 := by
    rw [div_le_div_iff₀ hLR (by positivity : (0 : ℝ) < K ^ 22)]
    simpa using hBK22leL
  have hlogNonneg : 0 ≤ Real.log ((2 * M : ℕ) : ℝ) :=
    Real.log_natCast_nonneg _
  have hAlphaLog :
      (((2 - a + 2 * ρ) / 2) ^ h + (B : ℝ) / L) *
          Real.log ((2 * M : ℕ) : ℝ) < 1 := by
    have hsumAlpha : ((2 - a + 2 * ρ) / 2) ^ h + (B : ℝ) / L ≤
        Real.exp (-(K : ℝ)) + 1 / K ^ 22 := add_le_add halphaExp hRound
    calc
      (((2 - a + 2 * ρ) / 2) ^ h + (B : ℝ) / L) *
          Real.log ((2 * M : ℕ) : ℝ) ≤
        (Real.exp (-(K : ℝ)) + 1 / K ^ 22) *
          Real.log ((2 * M : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hsumAlpha hlogNonneg
      _ ≤ (Real.exp (-(K : ℝ)) + 1 / K ^ 22) * (200 * K ^ 19) := by
        gcongr
      _ = 200 * K ^ 19 * Real.exp (-(K : ℝ)) + 200 / K ^ 3 := by
        field_simp
      _ < 1 := hKasym
  have hIndLog : (G.indepNum : ℝ) * Real.log ((2 * M : ℕ) : ℝ) < 2 * M := by
    calc
      (G.indepNum : ℝ) * Real.log ((2 * M : ℕ) : ℝ) ≤
          (2 * ((L : ℝ) * ((2 - a + 2 * ρ) / 2) ^ h + B)) *
            Real.log ((2 * M : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hindRaw hlogNonneg
      _ = 2 * L * ((((2 - a + 2 * ρ) / 2) ^ h + (B : ℝ) / L) *
          Real.log ((2 * M : ℕ) : ℝ)) := by
        field_simp
      _ < 2 * L := by
        simpa [mul_assoc] using
          (mul_lt_mul_of_pos_left hAlphaLog
            (mul_pos (by norm_num : (0 : ℝ) < 2) hLR))
      _ ≤ 2 * M := by exact_mod_cast (Nat.mul_le_mul_left 2 hMlower)
  let instV : Fintype V := inferInstance
  have hcard : @Fintype.card V instV = 2 * M := by
    simp [instV, V, M, copyCard]
  have hcardPos : 0 < @Fintype.card V instV := by
    rw [hcard]
    exact Nat.mul_pos (by norm_num) (by exact_mod_cast hMR)
  have hcardOne : 1 < @Fintype.card V instV := by
    rw [hcard]
    have hMpos : 0 < M := by exact_mod_cast hMR
    omega
  have hK22leL : (K : ℝ) ^ 22 ≤ L := by
    change (K : ℝ) ^ 22 ≤ (((B + 1) * K ^ 22 : ℕ) : ℝ)
    push_cast
    have hB1 : (1 : ℝ) ≤ (B : ℝ) + 1 := by norm_num
    calc
      (K : ℝ) ^ 22 = 1 * K ^ 22 := by ring
      _ ≤ ((B : ℝ) + 1) * K ^ 22 :=
        mul_le_mul_of_nonneg_right hB1 (by positivity)
  have hKleLNat : K ≤ L := by exact_mod_cast hK22.trans hK22leL
  have hcardLower : N ≤ @Fintype.card V instV := by
    rw [hcard]
    exact hNK.trans
      (hKleLNat.trans (hMlower.trans (Nat.le_mul_of_pos_left _ (by omega))))
  have hEdge : (1 / 8 - c) * ((@Fintype.card V instV : ℕ) : ℝ) ^ 2 ≤
      Nat.card G.edgeSet := by
    rw [hcard]
    exact hdensityRaw
  have hInd : (G.indepNum : ℝ) *
      Real.log ((@Fintype.card V instV : ℕ) : ℝ) <
        (@Fintype.card V instV : ℕ) := by
    rw [hcard]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hIndLog
  exact ⟨⟨V, instV, G, hcardPos, hcardOne, hcardLower, hEdge, hfreeRaw, hInd⟩⟩

lemma exists_counterexample (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∃ G : SimpleGraph (Fin n),
      (1 / 8 - c) * n ^ 2 ≤ G.edgeFinset.card ∧
      G.CliqueFree 4 ∧ G.indepNum < (n : ℝ) / Real.log n := by
  rcases exists_raw_counterexample c hc N with ⟨W⟩
  letI : Fintype W.Vertex := W.fintypeVertex
  let n : ℕ := Fintype.card W.Vertex
  let e : W.Vertex ≃ Fin n := Fintype.equivFin W.Vertex
  let Gfin : SimpleGraph (Fin n) := W.graph.map e.toEmbedding
  letI : DecidableRel Gfin.Adj := fun _ _ ↦ Classical.propDecidable _
  letI : Nonempty W.Vertex := Fintype.card_pos_iff.mp W.card_pos
  have hedgeEq : Gfin.edgeFinset.card = Nat.card W.graph.edgeSet := by
    calc
      Gfin.edgeFinset.card = W.graph.edgeFinset.card := by
        simpa [Gfin] using
          (SimpleGraph.Iso.map e W.graph).card_edgeFinset_eq.symm
      _ = Fintype.card W.graph.edgeSet := W.graph.edgeFinset_card
      _ = Nat.card W.graph.edgeSet := Nat.card_eq_fintype_card.symm
  have hfreeFin : Gfin.CliqueFree 4 := by
    simpa [Gfin] using
      (SimpleGraph.cliqueFree_map_iff (G := W.graph) (f := e.toEmbedding)).2 W.cliqueFree
  have hindEq : Gfin.indepNum = W.graph.indepNum := by
    simpa [Gfin] using indepNum_map_equiv W.graph e
  have hdensityFin : (1 / 8 - c) * (n : ℝ) ^ 2 ≤ Gfin.edgeFinset.card := by
    rw [hedgeEq]
    exact W.edge_density
  have hnOne : (1 : ℝ) < n := by
    exact_mod_cast (show 1 < n by simpa [n] using W.card_gt_one)
  have hlogPos : 0 < Real.log (n : ℝ) := Real.log_pos hnOne
  have hindFin : (Gfin.indepNum : ℝ) < (n : ℝ) / Real.log n := by
    rw [hindEq]
    exact (lt_div_iff₀ hlogPos).2 W.indep_log_lt
  exact ⟨n, W.card_lower, Gfin, hdensityFin, hfreeFin, hindFin⟩

/-- Erdős Problem 615 has a negative answer, by the quantitative
Bollobás--Erdős construction. -/
theorem erdos_615 :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ (n : ℕ) in atTop,
      ∀ G : SimpleGraph (Fin n), (1 / 8 - c) * n ^ 2 ≤ G.edgeFinset.card →
        ¬ G.CliqueFree 4 ∨ (n : ℝ) / Real.log n ≤ G.indepNum := by
  rintro ⟨c, hc, hlarge⟩
  rcases eventually_atTop.1 hlarge with ⟨N, hN⟩
  obtain ⟨n, hn, G, hedges, hfree, hind⟩ := exists_counterexample c hc N
  rcases hN n hn G hedges with hnotfree | hlargeindep
  · exact hnotfree hfree
  · exact (not_le_of_gt hind) hlargeindep

#print axioms erdos_615

end Erdos615
