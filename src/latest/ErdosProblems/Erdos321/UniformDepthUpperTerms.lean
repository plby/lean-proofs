import ErdosProblems.Erdos321.UpperIterationCoordinates

namespace Erdos321

noncomputable def upperCoordinateError (B : ℝ) (r : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ r * B)

noncomputable def upperCoordinateRetention (B : ℝ) (d : ℕ) : ℝ :=
  ∏ r ∈ Finset.range d, (1 + upperCoordinateError B r)

private theorem geometric_sum_le_two_upper (d : ℕ) :
    (∑ r ∈ Finset.range d, 1 / (2 : ℝ) ^ r) ≤ 2 := by
  have h := blockFraction_sum_le_half d
  have heq : (∑ r ∈ Finset.range d, 1 / (2 : ℝ) ^ r) =
      4 * ∑ r ∈ Finset.range d, 1 / (2 : ℝ) ^ (r + 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ, pow_succ]
    ring
  rw [heq]
  nlinarith

private theorem upperCoordinateError_sum_le
    {B : ℝ} (hB : 0 < B) (d : ℕ) :
    (∑ r ∈ Finset.range d, upperCoordinateError B r) ≤ 2 / B := by
  have hg := geometric_sum_le_two_upper d
  have heq : (∑ r ∈ Finset.range d, upperCoordinateError B r) =
      (1 / B) * ∑ r ∈ Finset.range d, 1 / (2 : ℝ) ^ r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp [upperCoordinateError]
    field_simp
  rw [heq]
  have := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 1 / B)
  calc
    (1 / B) * (∑ r ∈ Finset.range d, 1 / (2 : ℝ) ^ r) ≤
        (1 / B) * 2 := this
    _ = 2 / B := by ring

/-- The cumulative upper coordinate inflation is uniformly at most three. -/
theorem upperCoordinateRetention_le_three
    {B : ℝ} (hB : 4 ≤ B) (d : ℕ) :
    upperCoordinateRetention B d ≤ 3 := by
  have hBpos : 0 < B := by linarith
  have hpoint : ∀ r ∈ Finset.range d,
      1 + upperCoordinateError B r ≤ Real.exp (upperCoordinateError B r) := by
    intro r hr
    simpa [add_comm] using Real.add_one_le_exp (upperCoordinateError B r)
  have hp : upperCoordinateRetention B d ≤
      ∏ r ∈ Finset.range d, Real.exp (upperCoordinateError B r) := by
    dsimp [upperCoordinateRetention]
    apply Finset.prod_le_prod (fun r hr => by
      have : 0 ≤ upperCoordinateError B r := by
        dsimp [upperCoordinateError]
        positivity
      linarith) hpoint
  have hprodexp : (∏ r ∈ Finset.range d, Real.exp (upperCoordinateError B r)) =
      Real.exp (∑ r ∈ Finset.range d, upperCoordinateError B r) := by
    rw [← Real.exp_sum]
  rw [hprodexp] at hp
  have hsum := upperCoordinateError_sum_le hBpos d
  have hsum1 : (∑ r ∈ Finset.range d, upperCoordinateError B r) ≤ 1 := by
    have : 2 / B ≤ 1 := by
      apply (div_le_iff₀ hBpos).2
      linarith
    exact hsum.trans this
  have hexp := Real.exp_monotone hsum1
  have he3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  exact hp.trans (hexp.trans he3)

private theorem upperCoordinateRetention_nonneg
    {B : ℝ} (hB : 0 < B) (d : ℕ) :
    0 ≤ upperCoordinateRetention B d := by
  dsimp [upperCoordinateRetention]
  apply Finset.prod_nonneg
  intro r hr
  have : 0 ≤ upperCoordinateError B r := by
    dsimp [upperCoordinateError]
    positivity
  linarith

private theorem logLog_mono_nat
    {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) :
    Real.log (Real.log (a : ℝ)) ≤ Real.log (Real.log (b : ℝ)) := by
  have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hcast : (a : ℝ) ≤ b := by exact_mod_cast hab
  have h1 := Real.strictMonoOn_log.monotoneOn hapos hbpos hcast
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogb : 0 < Real.log (b : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  exact Real.strictMonoOn_log.monotoneOn hloga hlogb h1

/-- Every finite Neumann depth term is at most its ordinary iterated-log
product times one uniformly bounded inflation product. -/
theorem adaptiveNeumannTerm_uniform_upper
    {A : ℕ} {B : ℝ}
    (hA : 3 ≤ A) (hthirdA : 0 ≤ thirdIteratedLog A)
    (hdata : ∀ n, A ≤ n → AdaptiveUpperIterationData n)
    (hB : 4 ≤ B)
    {d n : ℕ} {x : ℝ}
    (htower : LogTowerAbove B d x)
    (hnA : A ≤ n)
    (hactual : Real.log (Real.log (n : ℝ)) ≤ x) :
    adaptiveNeumannTerm A d n ≤
      upperCoordinateRetention B d * iteratedLogTailProduct d x := by
  induction d generalizing n x with
  | zero => simp [upperCoordinateRetention, iteratedLogTailProduct]
  | succ d ih =>
      let z := Real.log (Real.log (n : ℝ))
      let X := Real.log x
      let Z := Real.log z
      let T := adaptiveEndpoint n
      let ue := upperCoordinateError B d
      let C := upperCoordinateRetention B d * iteratedLogTailProduct d X
      have hnData := hdata n hnA
      have hBpos : 0 < B := by linarith
      have hx : B ≤ x := htower 0 (by omega)
      have hxpos : 0 < x := lt_of_lt_of_le hBpos hx
      have hzA : Real.log (Real.log (A : ℝ)) ≤ z := by
        dsimp [z]
        exact logLog_mono_nat hA hnA
      have hloglogApos : 0 < Real.log (Real.log (A : ℝ)) := by
        have hlog3 : 1 < Real.log (3 : ℝ) := by
          have h := Real.strictMonoOn_log
            (Real.exp_pos (1 : ℝ)) (by norm_num : (0 : ℝ) < 3)
            Real.exp_one_lt_three
          simpa using h
        have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
        have hm := Real.strictMonoOn_log.monotoneOn
          (by norm_num : (0 : ℝ) < 3) hApos (by exact_mod_cast hA)
        exact Real.log_pos (by linarith)
      have hzpos : 0 < z := hloglogApos.trans_le hzA
      have hX : B ≤ X := by
        simpa [X, realIteratedLog] using htower 1 (by omega)
      have hXpos : 0 < X := lt_of_lt_of_le hBpos hX
      have hZX : Z ≤ X := by
        have hm := Real.strictMonoOn_log.monotoneOn hzpos hxpos hactual
        simpa [Z, X, z] using hm
      have hchildTower : LogTowerAbove B d X := by
        intro j hj
        rw [← realIteratedLog_succ_shift j x]
        exact htower (j + 1) (by omega)
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
      have hueX : 1 ≤ ue * X := by
        dsimp [ue, upperCoordinateError]
        have hcoef : 0 ≤ 1 / ((2 : ℝ) ^ d * B) := by positivity
        have hm := mul_le_mul_of_nonneg_left hXB hcoef
        have heq : (1 / ((2 : ℝ) ^ d * B)) *
            ((2 : ℝ) ^ d * B) = 1 := by field_simp
        linarith
      have hmass0 := truncated_mass_upper_of_upperData hA hthirdA hnA hnData
      have hmass : truncatedLogOperator A (fun _ => 1) T ≤
          (1 + ue) * X := by
        have hmass0' : truncatedLogOperator A (fun _ => 1) T ≤ Z + 1 := by
          simpa [T, Z, z, thirdIteratedLog] using hmass0
        nlinarith
      have hC0 : 0 ≤ C := by
        have hr := upperCoordinateRetention_nonneg hBpos d
        have hp := iteratedLogTailProduct_nonneg
          (logPositive_of_tower hBpos hchildTower)
        dsimp [C]
        positivity
      have hpoint : ∀ q ∈ Finset.Icc A T,
          adaptiveNeumannTerm A d q ≤ C := by
        intro q hq
        have hqA := (Finset.mem_Icc.mp hq).1
        have hqT := (Finset.mem_Icc.mp hq).2
        have hq3 := hA.trans hqA
        have hqcoord : Real.log (Real.log (q : ℝ)) ≤ X := by
          have hqT1 : q ≤ T + 1 := by omega
          have hfirst := logLog_mono_nat hq3 hqT1
          have hu := hnData.endpoint_logLog_upper
          have huX : Real.log (Real.log (((T + 1 : ℕ) : ℝ))) ≤ X := by
            simpa [T, Nat.cast_add, Nat.cast_one] using hu.trans hZX
          exact hfirst.trans huX
        exact ih hchildTower hqA hqcoord
      have hoperator : truncatedLogOperator A (adaptiveNeumannTerm A d) T ≤
          C * truncatedLogOperator A (fun _ => 1) T := by
        dsimp [truncatedLogOperator]
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro q hq
        have hqA := (Finset.mem_Icc.mp hq).1
        have hlog : 0 < Real.log (q : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < q by omega))
        have hden : 0 < ((q : ℝ) + 1) * Real.log q := by positivity
        have hh := (div_le_div_iff_of_pos_right hden).2 (hpoint q hq)
        convert hh using 1 <;> ring
      rw [adaptiveNeumannTerm_succ,
        safeAdaptiveEndpoint_eq_of_data hnData.cutoff]
      rw [upperCoordinateRetention, Finset.prod_range_succ]
      dsimp [iteratedLogTailProduct]
      change _ ≤ (upperCoordinateRetention B d * (1 + ue)) *
        (X * iteratedLogTailProduct d X)
      calc
        truncatedLogOperator A (adaptiveNeumannTerm A d) T ≤
            C * truncatedLogOperator A (fun _ => 1) T := hoperator
        _ ≤ C * ((1 + ue) * X) :=
          mul_le_mul_of_nonneg_left hmass hC0
        _ = (upperCoordinateRetention B d * (1 + ue)) *
            (X * iteratedLogTailProduct d X) := by
          dsimp [C]
          ring

end Erdos321
