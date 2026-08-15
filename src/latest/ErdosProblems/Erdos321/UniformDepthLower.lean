import ErdosProblems.Erdos321.NaturalMassBudget

namespace Erdos321

private theorem logLog_nat_le_cast {n : ℕ} (hn : 3 ≤ n) :
    Real.log (Real.log (n : ℝ)) ≤ n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have h1 := Real.log_le_sub_one_of_pos hnpos
  have h2 := Real.log_le_sub_one_of_pos hlogpos
  linarith

private theorem coordinate_step_factor
    {B x z : ℝ} {d : ℕ} (hB : 64 ≤ B)
    (htower : LogTowerAbove B (d + 1) x)
    (hz : x / (2 : ℝ) ^ (d + 4) ≤ z) :
    (1 - coordinateError B d) * Real.log x ≤ Real.log z ∧
      Real.log x / 2 ≤ Real.log z := by
  have hBpos : 0 < B := by linarith
  have hx : B ≤ x := htower 0 (by omega)
  have hxpos : 0 < x := lt_of_lt_of_le hBpos hx
  have hzlowerpos : 0 < x / (2 : ℝ) ^ (d + 4) := by positivity
  have hzpos : 0 < z := lt_of_lt_of_le hzlowerpos hz
  let X := Real.log x
  let Z := Real.log z
  let e := coordinateError B d
  have hX : B ≤ X := by
    simpa [X, realIteratedLog] using htower 1 (by omega)
  have hXpos : 0 < X := lt_of_lt_of_le hBpos hX
  have hmono := Real.strictMonoOn_log.monotoneOn hzlowerpos hzpos hz
  have hloglower : X - ((d : ℝ) + 4) * Real.log 2 ≤ Z := by
    have hpowlog : Real.log ((2 : ℝ) ^ (d + 4)) =
        (d + 4 : ℕ) * Real.log 2 := by rw [Real.log_pow]
    dsimp [X, Z]
    rw [Real.log_div (ne_of_gt hxpos)
      (by positivity : (2 : ℝ) ^ (d + 4) ≠ 0), hpowlog] at hmono
    norm_num [Nat.cast_add, Nat.cast_one] at hmono ⊢
    linarith
  have htower' : LogTowerAbove B (1 + d) x := by
    simpa [Nat.add_comm] using htower
  have hgeom := pow_two_mul_terminal_iteratedLog_le
    (B := B) (x := x) (j := 1) (d := d) (by linarith) htower'
  have hterminal : B ≤ realIteratedLog (1 + d) x :=
    htower (1 + d) (by omega)
  have hXB : (2 : ℝ) ^ d * B ≤ X := by
    have hm := mul_le_mul_of_nonneg_left hterminal
      (by positivity : 0 ≤ (2 : ℝ) ^ d)
    dsimp [X]
    exact hm.trans hgeom
  have he0 : 0 ≤ e := by
    dsimp [e, coordinateError]
    positivity
  have hehalf : e ≤ 1 / 2 := by
    have hpoint : e ≤ ∑ r ∈ Finset.range (d + 1), coordinateError B r := by
      dsimp [e]
      apply Finset.single_le_sum (fun i hi => by
        unfold coordinateError
        positivity)
      simp
    have hsum := coordinateError_sum_le hBpos (d + 1)
    have hten : 10 / B ≤ 1 / 2 := by
      apply (div_le_iff₀ hBpos).2
      nlinarith
    exact hpoint.trans (hsum.trans hten)
  have hloss : ((d : ℝ) + 4) * Real.log 2 ≤ e * X := by
    dsimp [e, coordinateError]
    have hdenpos : 0 < (2 : ℝ) ^ d * B := by positivity
    have hcoef : 0 ≤ ((d : ℝ) + 4) * Real.log 2 /
        ((2 : ℝ) ^ d * B) := by positivity
    have hm := mul_le_mul_of_nonneg_left hXB hcoef
    calc
      ((d : ℝ) + 4) * Real.log 2 =
          (((d : ℝ) + 4) * Real.log 2 / ((2 : ℝ) ^ d * B)) *
            ((2 : ℝ) ^ d * B) := by field_simp
      _ ≤ (((d : ℝ) + 4) * Real.log 2 / ((2 : ℝ) ^ d * B)) * X := hm
  have hfactor : (1 - e) * X ≤ Z := by nlinarith
  exact ⟨hfactor, by nlinarith⟩

private theorem naturalMassError_le_half
    {B : ℝ} (hB : 192 ≤ B) (d : ℕ) :
    naturalMassError B d ≤ 17 / 32 := by
  have hBpos : 0 < B := by linarith
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hfirst : 1 / (2 : ℝ) ^ (d + 1) ≤ 1 / 2 := by
    rw [show d + 1 = d + 1 by rfl, pow_succ]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ d * 2)).2
    nlinarith
  have hsecond : 6 / ((2 : ℝ) ^ d * B) ≤ 1 / 32 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ d * B)).2
    nlinarith
  dsimp [naturalMassError]
  linarith

/-- Every retained depth term dominates the corresponding ordinary
iterated-log product with two uniformly summable retention products. -/
theorem adaptiveNeumannTerm_uniform_lower
    {A : ℕ} {B : ℝ}
    (hA : 3 ≤ A) (hdata : ∀ n, A ≤ n → AdaptiveIterationData n)
    (hB : 192 ≤ B) (hBA : 8 * (A : ℝ) ≤ B)
    {d n : ℕ} {x : ℝ}
    (htower : LogTowerAbove B d x)
    (hnA : A ≤ n)
    (hscale : x / (2 : ℝ) ^ (d + 3) ≤
      Real.log (Real.log (n : ℝ))) :
    naturalMassRetention B d * coordinateRetention B d *
        iteratedLogTailProduct d x ≤ adaptiveNeumannTerm A d n := by
  induction d generalizing n x with
  | zero =>
      simp [naturalMassRetention, coordinateRetention,
        iteratedLogTailProduct]
  | succ d ih =>
      let z := Real.log (Real.log (n : ℝ))
      let X := Real.log x
      let Z := Real.log z
      let T := adaptiveEndpoint n
      let U := Real.log (Real.log ((T : ℝ) + 1))
      let b : ℝ := 1 / (2 : ℝ) ^ (d + 1)
      let L := fractionalLogBlockStart b T
      let me := naturalMassError B d
      let ce := coordinateError B d
      have hnData := hdata n hnA
      have hBpos : 0 < B := by linarith
      have hx : B ≤ x := htower 0 (by omega)
      have hxpos : 0 < x := lt_of_lt_of_le hBpos hx
      have hzpos : 0 < z := by
        have hzlower : 0 < x / (2 : ℝ) ^ (d + 1 + 3) := by positivity
        exact lt_of_lt_of_le hzlower hscale
      have hcoord := coordinate_step_factor (show 64 ≤ B by linarith) htower hscale
      have hfactor : (1 - ce) * X ≤ Z := by simpa [X, Z, ce] using hcoord.1
      have hZhalf : X / 2 ≤ Z := by simpa [X, Z] using hcoord.2
      have htower' : LogTowerAbove B (1 + d) x := by
        simpa [Nat.add_comm] using htower
      have hgeom := pow_two_mul_terminal_iteratedLog_le
        (B := B) (x := x) (j := 1) (d := d) (by linarith) htower'
      have hterminal : B ≤ realIteratedLog (1 + d) x :=
        htower (1 + d) (by omega)
      have hXB : (2 : ℝ) ^ d * B ≤ X := by
        have hm := mul_le_mul_of_nonneg_left hterminal
          (by positivity : 0 ≤ (2 : ℝ) ^ d)
        dsimp [X]
        exact hm.trans hgeom
      have hUhalf : Z / 2 ≤ U := by
        simpa [Z, z, U, T, thirdIteratedLog] using hnData.endpoint_logLog_half
      have hUadd : Z - 1 ≤ U := by
        simpa [Z, z, U, T, thirdIteratedLog] using hnData.endpoint_logLog_additive
      have hb0 : 0 < b := by dsimp [b]; positivity
      have hbhalf : b ≤ 1 / 2 := by
        dsimp [b]
        have hp : (2 : ℝ) ≤ (2 : ℝ) ^ (d + 1) := by
          calc
            (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp
      have hblock := fractionalLogBlockStart_properties hb0 hbhalf
        hnData.endpoint_ge_three hnData.endpoint_logLog_large
      have hmass0 := fractionalLogBlock_mass_lower hb0 hbhalf
        hnData.endpoint_ge_three hnData.endpoint_logLog_large
      have hme : me = b + 6 / ((2 : ℝ) ^ d * B) := by
        dsimp [me, naturalMassError, b]
      have hmass : (1 - me) * Z ≤
          truncatedLogOperator L (fun _ => 1) T := by
        have hthree : 3 ≤ (6 / ((2 : ℝ) ^ d * B)) * Z := by
          have hZB : ((2 : ℝ) ^ d * B) / 2 ≤ Z := by
            nlinarith [hXB, hZhalf]
          have hm := mul_le_mul_of_nonneg_left hZB
            (show 0 ≤ 6 / ((2 : ℝ) ^ d * B) by positivity)
          have hden : 0 < (2 : ℝ) ^ d * B := by positivity
          have heq : (6 / ((2 : ℝ) ^ d * B)) *
              (((2 : ℝ) ^ d * B) / 2) = 3 := by
            field_simp
            norm_num
          linarith
        dsimp [L, T, U, b] at hmass0 ⊢
        rw [hme]
        nlinarith
      have hmeNonneg : 0 ≤ 1 - me := by
        have hmle := naturalMassError_le_half hB d
        dsimp [me]
        linarith
      have hceNonneg : 0 ≤ 1 - ce := by
        have hpoint : ce ≤ ∑ r ∈ Finset.range (d + 1), coordinateError B r := by
          dsimp [ce]
          apply Finset.single_le_sum (fun i hi => by
            unfold coordinateError
            positivity)
          simp
        have hs := coordinateError_sum_le hBpos (d + 1)
        have : 10 / B ≤ 1 := by
          apply (div_le_iff₀ hBpos).2
          nlinarith
        dsimp [ce]
        linarith
      have hchildTower : LogTowerAbove B d X := by
        intro j hj
        rw [← realIteratedLog_succ_shift j x]
        exact htower (j + 1) (by omega)
      have hchildRef : X / (2 : ℝ) ^ (d + 3) ≤ b * U := by
        calc
          X / (2 : ℝ) ^ (d + 3) =
              (1 / (2 : ℝ) ^ (d + 1)) * (X / 4) := by
                rw [show d + 3 = (d + 1) + 2 by omega, pow_add]
                norm_num
                ring
          _ ≤ (1 / (2 : ℝ) ^ (d + 1)) * (Z / 2) := by
            have := mul_le_mul_of_nonneg_left hZhalf
              (show 0 ≤ 1 / (2 : ℝ) ^ (d + 1) by positivity)
            nlinarith
          _ ≤ b * U := by
            dsimp [b]
            exact mul_le_mul_of_nonneg_left hUhalf (by positivity)
      have hLA : A ≤ L := by
        have hLcoord : b * U ≤ Real.log (Real.log (L : ℝ)) := by
          simpa [L, T, U, b] using hblock.2.2.1
        have hBA8 : (A : ℝ) ≤ B / 8 := by nlinarith
        have hB8 : B / 8 ≤ X / (2 : ℝ) ^ (d + 3) := by
          calc
            B / 8 = ((2 : ℝ) ^ d * B) / (2 : ℝ) ^ (d + 3) := by
              rw [show d + 3 = d + 3 by rfl, pow_add]
              norm_num
              field_simp
            _ ≤ X / (2 : ℝ) ^ (d + 3) :=
              div_le_div_of_nonneg_right hXB (by positivity)
        have hreal : (A : ℝ) ≤ L := by
          calc
            (A : ℝ) ≤ B / 8 := hBA8
            _ ≤ X / (2 : ℝ) ^ (d + 3) := hB8
            _ ≤ b * U := hchildRef
            _ ≤ Real.log (Real.log (L : ℝ)) := hLcoord
            _ ≤ L := logLog_nat_le_cast hblock.1
        exact_mod_cast hreal
      have hsubset : Finset.Icc L T ⊆ Finset.Icc A T := by
        intro q hq
        exact Finset.mem_Icc.mpr
          ⟨hLA.trans (Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2⟩
      let C := naturalMassRetention B d * coordinateRetention B d *
        iteratedLogTailProduct d X
      have hCnonneg : 0 ≤ C := by
        have hmret : 0 ≤ naturalMassRetention B d :=
          (by norm_num : (0 : ℝ) ≤ 1 / 8).trans
            (one_eighth_le_naturalMassRetention hB d)
        have hcret : 0 ≤ coordinateRetention B d := by
          have hr := one_sub_ten_div_le_coordinateRetention
            (show 20 ≤ B by linarith) d
          have hbase : 0 ≤ 1 - 10 / B := by
            apply sub_nonneg.mpr
            apply (div_le_iff₀ hBpos).2
            nlinarith
          exact hbase.trans hr
        have hp : 0 ≤ iteratedLogTailProduct d X :=
          iteratedLogTailProduct_nonneg
            (logPositive_of_tower hBpos hchildTower)
        dsimp [C]
        positivity
      have hpoint : ∀ q ∈ Finset.Icc L T,
          C ≤ adaptiveNeumannTerm A d q := by
        intro q hq
        have hqL := (Finset.mem_Icc.mp hq).1
        have hqA := hLA.trans hqL
        have hqcoord : b * U ≤ Real.log (Real.log (q : ℝ)) := by
          have hLcoord : b * U ≤ Real.log (Real.log (L : ℝ)) := by
            simpa [L, T, U, b] using hblock.2.2.1
          have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
          have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
          have hlogL : 0 < Real.log (L : ℝ) :=
            Real.log_pos (by exact_mod_cast (show 1 < L by omega))
          have hlogq : 0 < Real.log (q : ℝ) :=
            Real.log_pos (by exact_mod_cast (show 1 < q by omega))
          have h1 := Real.strictMonoOn_log.monotoneOn hLpos hqpos
            (by exact_mod_cast hqL)
          have h2 := Real.strictMonoOn_log.monotoneOn hlogL hlogq h1
          exact hLcoord.trans h2
        have hqscale : X / (2 : ℝ) ^ (d + 3) ≤
            Real.log (Real.log (q : ℝ)) := hchildRef.trans hqcoord
        exact ih hchildTower hqA hqscale
      have hrestricted : C * truncatedLogOperator L (fun _ => 1) T ≤
          truncatedLogOperator A (adaptiveNeumannTerm A d) T := by
        dsimp [truncatedLogOperator]
        rw [Finset.mul_sum]
        calc
          (∑ q ∈ Finset.Icc L T,
              C * (1 / (((q : ℝ) + 1) * Real.log q))) ≤
            ∑ q ∈ Finset.Icc L T,
              adaptiveNeumannTerm A d q /
                (((q : ℝ) + 1) * Real.log q) := by
                  apply Finset.sum_le_sum
                  intro q hq
                  have hden : 0 < ((q : ℝ) + 1) * Real.log q := by
                    have hq3 := hblock.1.trans (Finset.mem_Icc.mp hq).1
                    have hlog : 0 < Real.log (q : ℝ) :=
                      Real.log_pos (by exact_mod_cast (show 1 < q by omega))
                    positivity
                  have hh := (div_le_div_iff_of_pos_right hden).2 (hpoint q hq)
                  convert hh using 1 <;> ring
          _ ≤ ∑ q ∈ Finset.Icc A T,
              adaptiveNeumannTerm A d q /
                (((q : ℝ) + 1) * Real.log q) := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
                  intro q hq hnot
                  have hqA := (Finset.mem_Icc.mp hq).1
                  have hlog : 0 < Real.log (q : ℝ) :=
                    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
                  exact div_nonneg (adaptiveNeumannTerm_nonneg (show 2 ≤ A by omega) d q)
                    (mul_pos (by positivity) hlog).le
      rw [adaptiveNeumannTerm_succ]
      rw [safeAdaptiveEndpoint_eq_of_data hnData.cutoff]
      have hmain : C * ((1 - me) * Z) ≤
          truncatedLogOperator A (adaptiveNeumannTerm A d) T := by
        exact (mul_le_mul_of_nonneg_left hmass hCnonneg).trans hrestricted
      rw [naturalMassRetention, coordinateRetention,
        Finset.prod_range_succ, Finset.prod_range_succ]
      dsimp [iteratedLogTailProduct]
      change ((naturalMassRetention B d * (1 - me)) *
          (coordinateRetention B d * (1 - ce))) *
          (X * iteratedLogTailProduct d X) ≤ _
      change _ ≤ truncatedLogOperator A (adaptiveNeumannTerm A d) T
      have htarget :
          ((naturalMassRetention B d * (1 - me)) *
            (coordinateRetention B d * (1 - ce))) *
            (X * iteratedLogTailProduct d X) =
          C * ((1 - me) * ((1 - ce) * X)) := by
        dsimp [C]
        ring
      rw [htarget]
      have hinner : (1 - me) * ((1 - ce) * X) ≤ (1 - me) * Z :=
        mul_le_mul_of_nonneg_left hfactor hmeNonneg
      exact (mul_le_mul_of_nonneg_left hinner hCnonneg).trans hmain

/-- One fixed stopped model uniformly dominates every retained terminal
iterated-log product. -/
theorem exists_uniform_iteratedLogProduct_lower :
    ∃ A : ℕ, ∃ B : ℝ,
      3 ≤ A ∧ 192 ≤ B ∧ 8 * (A : ℝ) ≤ B ∧
      ∀ n d, A ≤ n → d ≤ n →
        LogTowerAbove B d (Real.log (Real.log (n : ℝ))) →
        iteratedLogTailProduct d (Real.log (Real.log (n : ℝ))) / 16 ≤
          adaptiveNeumannModel A n := by
  obtain ⟨A, hA, hdata⟩ := exists_iterationData_threshold
  let B : ℝ := max 192 (8 * (A : ℝ))
  have hB : (192 : ℝ) ≤ B := le_max_left _ _
  have hBA : 8 * (A : ℝ) ≤ B := le_max_right _ _
  refine ⟨A, B, hA, hB, hBA, ?_⟩
  intro n d hnA hdN htower
  let x := Real.log (Real.log (n : ℝ))
  have hBpos : 0 < B := by linarith
  have hx : B ≤ x := htower 0 (by omega)
  have hx0 : 0 ≤ x := (le_of_lt hBpos).trans hx
  have hscale : x / (2 : ℝ) ^ (d + 3) ≤
      Real.log (Real.log (n : ℝ)) := by
    dsimp [x]
    have hp : 1 ≤ (2 : ℝ) ^ (d + 3) := one_le_pow₀ (by norm_num)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (d + 3))).2
    nlinarith
  have hterm := adaptiveNeumannTerm_uniform_lower hA hdata hB hBA
    htower hnA hscale
  have hp0 : 0 ≤ iteratedLogTailProduct d x :=
    iteratedLogTailProduct_nonneg (logPositive_of_tower hBpos htower)
  have hmret := one_eighth_le_naturalMassRetention hB d
  have hcret0 := one_sub_ten_div_le_coordinateRetention
    (show 20 ≤ B by linarith) d
  have hhalfbase : (1 / 2 : ℝ) ≤ 1 - 10 / B := by
    have hten : 10 / B ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hBpos).2
      nlinarith
    linarith
  have hcret : (1 / 2 : ℝ) ≤ coordinateRetention B d :=
    hhalfbase.trans hcret0
  have hretprod : (1 / 16 : ℝ) ≤
      naturalMassRetention B d * coordinateRetention B d := by
    have hmnonneg : 0 ≤ naturalMassRetention B d :=
      (by norm_num : (0 : ℝ) ≤ 1 / 8).trans hmret
    have hm := mul_le_mul hmret hcret (by norm_num) hmnonneg
    nlinarith
  have htoTerm : iteratedLogTailProduct d x / 16 ≤
      adaptiveNeumannTerm A d n := by
    calc
      iteratedLogTailProduct d x / 16 =
          (1 / 16 : ℝ) * iteratedLogTailProduct d x := by ring
      _ ≤ (naturalMassRetention B d * coordinateRetention B d) *
          iteratedLogTailProduct d x :=
        mul_le_mul_of_nonneg_right hretprod hp0
      _ = naturalMassRetention B d * coordinateRetention B d *
          iteratedLogTailProduct d x := by ring
      _ ≤ adaptiveNeumannTerm A d n := hterm
  have htermModel : adaptiveNeumannTerm A d n ≤ adaptiveNeumannModel A n := by
    rw [adaptiveNeumannModel_eq_sum_terms (show 2 ≤ A by omega)]
    apply Finset.single_le_sum
      (s := Finset.range (n + 1))
      (f := fun k => adaptiveNeumannTerm A k n)
    · intro k hk
      exact adaptiveNeumannTerm_nonneg (show 2 ≤ A by omega) k n
    · simp
      omega
  simpa [x] using htoTerm.trans htermModel

end Erdos321
