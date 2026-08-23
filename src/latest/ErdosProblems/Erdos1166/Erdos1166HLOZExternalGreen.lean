import ErdosProblems.Erdos1166.Erdos1166HLOZExternalKernel
import ErdosProblems.Erdos1166.Erdos1166HLOZGreen
import ErdosProblems.Erdos1166.Erdos1166HLOZProp44ExternalChain

namespace Erdos1166.HLOZExternalStepLaw

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open HLOZExternalUpper HLOZExternalChain HLOZExternalKernel HLOZProp44

/-- The fifteen possible terminal labels. -/
abbrev TerminalLabel := {p : IncrementPair // p ≠ distinguishedIncrementPair}

/-- The displacement during one complete terminal label. -/
def terminalStep (p : TerminalLabel) : Site :=
  directionStep (p.1 0) + directionStep (p.1 1)

theorem card_terminalLabel : Fintype.card TerminalLabel = 15 := by
  decide

instance : Nonempty TerminalLabel :=
  ⟨⟨![2, 2], by decide⟩⟩

/-- Multiplicity of a displacement among the fifteen terminal labels. -/
def terminalStepMultiplicity (z : Site) : ℕ :=
  Finset.univ.filter (fun p : TerminalLabel ↦ terminalStep p = z) |>.card

theorem terminalStepMultiplicity_zero : terminalStepMultiplicity (0, 0) = 3 := by
  decide

theorem terminalStepMultiplicity_two_zero : terminalStepMultiplicity (2, 0) = 1 := by
  decide

theorem terminalStepMultiplicity_neg_two_zero : terminalStepMultiplicity (-2, 0) = 1 := by
  decide

theorem terminalStepMultiplicity_zero_two : terminalStepMultiplicity (0, 2) = 1 := by
  decide

theorem terminalStepMultiplicity_zero_neg_two : terminalStepMultiplicity (0, -2) = 1 := by
  decide

theorem terminalStepMultiplicity_one_one : terminalStepMultiplicity (1, 1) = 2 := by
  decide

theorem terminalStepMultiplicity_one_neg_one : terminalStepMultiplicity (1, -1) = 2 := by
  decide

theorem terminalStepMultiplicity_neg_one_one : terminalStepMultiplicity (-1, 1) = 2 := by
  decide

theorem terminalStepMultiplicity_neg_one_neg_one :
    terminalStepMultiplicity (-1, -1) = 2 := by
  decide

theorem terminalStep_mem_support (p : TerminalLabel) :
    terminalStep p ∈ ({(0, 0), (2, 0), (-2, 0), (0, 2), (0, -2),
      (1, 1), (1, -1), (-1, 1), (-1, -1)} : Finset Site) := by
  revert p
  decide

/-- One terminal step is centered. -/
theorem sum_terminalStep : ∑ p : TerminalLabel, terminalStep p = (0, 0) := by
  decide

/-- The unnormalized coordinate covariance matrix is `16 I`. -/
theorem sum_terminalStep_x_sq :
    ∑ p : TerminalLabel, (terminalStep p).1 ^ 2 = 16 := by decide

theorem sum_terminalStep_y_sq :
    ∑ p : TerminalLabel, (terminalStep p).2 ^ 2 = 16 := by decide

theorem sum_terminalStep_xy :
    ∑ p : TerminalLabel, (terminalStep p).1 * (terminalStep p).2 = 0 := by
  decide

/-- Macro path obtained by concatenating complete terminal labels. -/
def terminalMacroPath (labels : ℕ → TerminalLabel) (n : ℕ) : Site :=
  ∑ j ∈ Finset.range n, terminalStep (labels j)

/-- Product law of iid uniform terminal labels. -/
noncomputable def terminalLabelLaw : Measure (ℕ → TerminalLabel) :=
  Measure.infinitePi fun _ : ℕ ↦ (PMF.uniformOfFintype TerminalLabel).toMeasure

instance : IsProbabilityMeasure terminalLabelLaw := by
  unfold terminalLabelLaw
  infer_instance

theorem terminalLabel_eval_prob (n : ℕ) (p : TerminalLabel) :
    terminalLabelLaw {ω | ω n = p} = (15 : ENNReal)⁻¹ := by
  calc
    terminalLabelLaw {ω | ω n = p} =
        ((PMF.uniformOfFintype TerminalLabel).toMeasure) {p} := by
      rw [show {ω : ℕ → TerminalLabel | ω n = p} =
          (fun ω : ℕ → TerminalLabel ↦ ω n) ⁻¹' {p} by rfl]
      rw [← Measure.map_apply (measurable_pi_apply n) (measurableSet_singleton p)]
      simp [terminalLabelLaw, Measure.infinitePi_map_eval]
    _ = (15 : ENNReal)⁻¹ := by
      simp [PMF.toMeasure_apply_singleton, card_terminalLabel]

/-- Return probability of the even-time terminal-label chain. -/
noncomputable def terminalMacroReturnProb (n : ℕ) : ℝ :=
  terminalLabelLaw.real {ω | terminalMacroPath ω n = (0, 0)}

theorem terminalMacroReturnProb_nonneg (n : ℕ) :
    0 ≤ terminalMacroReturnProb n := measureReal_nonneg

theorem sum_terminalStep_fiberwise (f : Site → ℂ) :
    ∑ p : TerminalLabel, f (terminalStep p) =
      3 * f (0, 0) + f (2, 0) + f (-2, 0) + f (0, 2) + f (0, -2) +
      2 * f (1, 1) + 2 * f (1, -1) + 2 * f (-1, 1) + 2 * f (-1, -1) := by
  classical
  let S : Finset Site :=
    {(0, 0), (2, 0), (-2, 0), (0, 2), (0, -2),
      (1, 1), (1, -1), (-1, 1), (-1, -1)}
  have hmap : ((Finset.univ : Finset TerminalLabel) : Set TerminalLabel).MapsTo
      terminalStep S := by
    intro p hp
    exact terminalStep_mem_support p
  calc
    ∑ p : TerminalLabel, f (terminalStep p) =
        ∑ z ∈ S, ∑ p ∈ (Finset.univ.filter fun p : TerminalLabel ↦
          terminalStep p = z), f (terminalStep p) := by
      rw [Finset.sum_fiberwise_of_maps_to hmap]
    _ = ∑ z ∈ S, (terminalStepMultiplicity z : ℂ) * f z := by
      apply Finset.sum_congr rfl
      intro z hz
      calc
        ∑ p ∈ (Finset.univ.filter fun p : TerminalLabel ↦ terminalStep p = z),
            f (terminalStep p) =
            ∑ _p ∈ (Finset.univ.filter fun p : TerminalLabel ↦ terminalStep p = z),
              f z := by
          apply Finset.sum_congr rfl
          intro p hp
          exact congrArg f (Finset.mem_filter.mp hp).2
        _ = (terminalStepMultiplicity z : ℂ) * f z := by
          simp [terminalStepMultiplicity]
    _ = _ := by
      simp [S, terminalStepMultiplicity_zero,
        terminalStepMultiplicity_two_zero, terminalStepMultiplicity_neg_two_zero,
        terminalStepMultiplicity_zero_two, terminalStepMultiplicity_zero_neg_two,
        terminalStepMultiplicity_one_one, terminalStepMultiplicity_one_neg_one,
        terminalStepMultiplicity_neg_one_one, terminalStepMultiplicity_neg_one_neg_one]
      ring

/-- Characteristic function of one complete terminal-label displacement. -/
noncomputable def terminalCharacteristic (x y : ℝ) : ℂ :=
  (15 : ℂ)⁻¹ * ∑ p : TerminalLabel,
    Complex.exp (Complex.I *
      (((terminalStep p).1 : ℝ) * x + ((terminalStep p).2 : ℝ) * y))

/-- Exact nine-atom characteristic function.  In particular this is not the
characteristic function of ordinary planar SRW. -/
theorem terminalCharacteristic_formula (x y : ℝ) :
    terminalCharacteristic x y = (15 : ℂ)⁻¹ *
      (3 +
        Complex.exp (Complex.I * (2 * x)) +
        Complex.exp (Complex.I * (-2 * x)) +
        Complex.exp (Complex.I * (2 * y)) +
        Complex.exp (Complex.I * (-2 * y)) +
        2 * Complex.exp (Complex.I * (x + y)) +
        2 * Complex.exp (Complex.I * (x - y)) +
        2 * Complex.exp (Complex.I * (-x + y)) +
        2 * Complex.exp (Complex.I * (-x - y))) := by
  unfold terminalCharacteristic
  have h := sum_terminalStep_fiberwise (fun z : Site ↦
    Complex.exp (Complex.I * (((z.1 : ℝ) * x + (z.2 : ℝ) * y))))
  rw [h]
  push_cast
  congr 1
  ring_nf
  simp

/-- Displacement of an arbitrary adjacent direction pair. -/
def pairStep (p : IncrementPair) : Site :=
  directionStep (p 0) + directionStep (p 1)

@[simp] theorem pairStep_distinguished : pairStep distinguishedIncrementPair = (0, 0) := by
  decide

theorem sum_pairStep_eq_hold_add_terminal (f : Site → ℕ) :
    ∑ p : IncrementPair, f (pairStep p) =
      f (0, 0) + ∑ p : TerminalLabel, f (terminalStep p) := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun p : IncrementPair ↦ p ≠ distinguishedIncrementPair)
    (fun p ↦ f (pairStep p))
  have hcomp :
      (∑ p : {p : IncrementPair // ¬p ≠ distinguishedIncrementPair},
        f (pairStep p.1)) = f (0, 0) := by
    let d : {p : IncrementPair // ¬p ≠ distinguishedIncrementPair} :=
      ⟨distinguishedIncrementPair, by simp⟩
    calc
      (∑ p : {p : IncrementPair // ¬p ≠ distinguishedIncrementPair},
          f (pairStep p.1)) = f (pairStep d.1) := by
        apply Fintype.sum_eq_single d
        intro p hpd
        exfalso
        apply hpd
        apply Subtype.ext
        exact not_ne_iff.mp p.2
      _ = f (0, 0) := by rw [pairStep_distinguished]
  rw [← hsplit]
  rw [hcomp, add_comm]
  rfl

/-- Integer path counts for the genuine fifteen-label macro chain. -/
def terminalPathCount : ℕ → Site → ℕ
  | 0, x => if x = (0, 0) then 1 else 0
  | n + 1, x => ∑ p : TerminalLabel, terminalPathCount n (x - terminalStep p)

/-- Integer path counts for unrestricted adjacent pairs (ordinary SRW at
even times). -/
def pairPathCount : ℕ → Site → ℕ
  | 0, x => if x = (0, 0) then 1 else 0
  | n + 1, x => ∑ p : IncrementPair, pairPathCount n (x - pairStep p)

@[simp] theorem terminalPathCount_zero_zero : terminalPathCount 0 (0, 0) = 1 := by
  simp [terminalPathCount]

@[simp] theorem pairPathCount_zero_zero : pairPathCount 0 (0, 0) = 1 := by
  simp [pairPathCount]

/-- Exact binomial de-lazification identity at every lattice site. -/
theorem pairPathCount_eq_binomial_terminal : ∀ n x,
    pairPathCount n x =
      ∑ j ∈ Finset.range (n + 1), Nat.choose n j * terminalPathCount j x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [pairPathCount, terminalPathCount]
  | succ n ih =>
      intro x
      rw [pairPathCount]
      calc
        (∑ p : IncrementPair, pairPathCount n (x - pairStep p)) =
            pairPathCount n x +
              ∑ p : TerminalLabel, pairPathCount n (x - terminalStep p) := by
          rw [sum_pairStep_eq_hold_add_terminal
            (fun z ↦ pairPathCount n (x - z))]
          congr 1
          rcases x with ⟨x₁, x₂⟩
          apply congrArg (pairPathCount n)
          ext <;> simp
        _ = (∑ j ∈ Finset.range (n + 1), Nat.choose n j * terminalPathCount j x) +
              ∑ p : TerminalLabel,
                ∑ j ∈ Finset.range (n + 1),
                  Nat.choose n j * terminalPathCount j (x - terminalStep p) := by
          rw [ih]
          apply congrArg (fun z ↦
            (∑ j ∈ Finset.range (n + 1), Nat.choose n j * terminalPathCount j x) + z)
          apply Fintype.sum_congr
          intro p
          exact ih (x - terminalStep p)
        _ = (∑ j ∈ Finset.range (n + 1), Nat.choose n j * terminalPathCount j x) +
              ∑ j ∈ Finset.range (n + 1),
                Nat.choose n j * terminalPathCount (j + 1) x := by
          congr 1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.mul_sum]
          rfl
        _ = ∑ j ∈ Finset.range (n + 2),
              Nat.choose (n + 1) j * terminalPathCount j x := by
          simpa using (Finset.sum_choose_succ_mul
            (R := ℕ) (fun i _ ↦ terminalPathCount i x) n).symm

/-- Finite-prefix count realizing `terminalPathCount`. -/
def terminalPrefixEndpoint {n : ℕ} (v : Fin n → TerminalLabel) : Site :=
  ∑ i, terminalStep (v i)

theorem terminalPathCount_eq_sum_indicator : ∀ n x,
    terminalPathCount n x =
      ∑ v : Fin n → TerminalLabel,
        if terminalPrefixEndpoint v = x then 1 else 0 := by
  intro n
  induction n with
  | zero =>
      intro x
      have hzero (v : Fin 0 → TerminalLabel) : terminalPrefixEndpoint v = (0, 0) := by
        unfold terminalPrefixEndpoint
        rw [Finset.univ_eq_empty, Finset.sum_empty]
        change ((0 : ℤ), (0 : ℤ)) = (0, 0)
        rfl
      rw [terminalPathCount]
      simp only [Fintype.sum_unique, hzero]
      by_cases hx : x = (0, 0)
      · subst x; simp
      · simp [hx, Ne.symm hx]
  | succ n ih =>
      intro x
      rw [terminalPathCount]
      calc
        (∑ p : TerminalLabel, terminalPathCount n (x - terminalStep p)) =
            ∑ p : TerminalLabel, ∑ v : Fin n → TerminalLabel,
              if terminalPrefixEndpoint v = x - terminalStep p then 1 else 0 := by
          apply Fintype.sum_congr
          intro p
          exact ih (x - terminalStep p)
        _ = ∑ pv : TerminalLabel × (Fin n → TerminalLabel),
              if terminalPrefixEndpoint pv.2 = x - terminalStep pv.1 then 1 else 0 := by
          rw [Fintype.sum_prod_type]
        _ = ∑ v : Fin (n + 1) → TerminalLabel,
              if terminalPrefixEndpoint v = x then 1 else 0 := by
          apply Fintype.sum_equiv
            (Fin.consEquiv (fun _ : Fin (n + 1) ↦ TerminalLabel))
          intro pv
          change (if terminalPrefixEndpoint pv.2 = x - terminalStep pv.1 then 1 else 0) =
            if terminalPrefixEndpoint (Fin.cons pv.1 pv.2) = x then 1 else 0
          unfold terminalPrefixEndpoint
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          have hadd : terminalStep pv.1 + ∑ i, terminalStep (pv.2 i) = x ↔
              (∑ i, terminalStep (pv.2 i)) = x - terminalStep pv.1 := by
            constructor <;> intro h
            · rw [← h]
              abel
            · rw [h]
              abel
          by_cases h : (∑ i, terminalStep (pv.2 i)) = x - terminalStep pv.1
          · have hs := hadd.mpr h
            simp [h, hs]
          · have hs : ¬ terminalStep pv.1 + ∑ i, terminalStep (pv.2 i) = x :=
              fun hs ↦ h (hadd.mp hs)
            simp [h, hs]

/-- Finite-prefix count realizing `pairPathCount`. -/
def pairPrefixEndpoint {n : ℕ} (v : Fin n → IncrementPair) : Site :=
  ∑ i, pairStep (v i)

theorem pairPathCount_eq_sum_indicator : ∀ n x,
    pairPathCount n x =
      ∑ v : Fin n → IncrementPair,
        if pairPrefixEndpoint v = x then 1 else 0 := by
  intro n
  induction n with
  | zero =>
      intro x
      have hzero (v : Fin 0 → IncrementPair) : pairPrefixEndpoint v = (0, 0) := by
        unfold pairPrefixEndpoint
        rw [Finset.univ_eq_empty, Finset.sum_empty]
        rfl
      rw [pairPathCount]
      simp only [Fintype.sum_unique, hzero]
      by_cases hx : x = (0, 0)
      · subst x; simp
      · simp [hx, Ne.symm hx]
  | succ n ih =>
      intro x
      rw [pairPathCount]
      calc
        (∑ p : IncrementPair, pairPathCount n (x - pairStep p)) =
            ∑ p : IncrementPair, ∑ v : Fin n → IncrementPair,
              if pairPrefixEndpoint v = x - pairStep p then 1 else 0 := by
          apply Fintype.sum_congr
          intro p
          exact ih (x - pairStep p)
        _ = ∑ pv : IncrementPair × (Fin n → IncrementPair),
              if pairPrefixEndpoint pv.2 = x - pairStep pv.1 then 1 else 0 := by
          rw [Fintype.sum_prod_type]
        _ = ∑ v : Fin (n + 1) → IncrementPair,
              if pairPrefixEndpoint v = x then 1 else 0 := by
          apply Fintype.sum_equiv
            (Fin.consEquiv (fun _ : Fin (n + 1) ↦ IncrementPair))
          intro pv
          change (if pairPrefixEndpoint pv.2 = x - pairStep pv.1 then 1 else 0) =
            if pairPrefixEndpoint (Fin.cons pv.1 pv.2) = x then 1 else 0
          unfold pairPrefixEndpoint
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          have hadd : pairStep pv.1 + ∑ i, pairStep (pv.2 i) = x ↔
              (∑ i, pairStep (pv.2 i)) = x - pairStep pv.1 := by
            constructor <;> intro h
            · rw [← h]
              abel
            · rw [h]
              abel
          by_cases h : (∑ i, pairStep (pv.2 i)) = x - pairStep pv.1
          · have hs := hadd.mpr h
            simp [h, hs]
          · have hs : ¬ pairStep pv.1 + ∑ i, pairStep (pv.2 i) = x :=
              fun hs ↦ h (hadd.mp hs)
            simp [h, hs]

/-- Pair indices identify canonically with the first `2n` direction indices. -/
def pairIndexEquiv (n : ℕ) : Fin n × Fin 2 ≃ ↑(Finset.range (2 * n)) where
  toFun jr := ⟨2 * jr.1.val + jr.2.val, by
    have hj := jr.1.isLt
    have hr := jr.2.isLt
    simp only [Finset.mem_range]
    omega⟩
  invFun i :=
    (⟨i.val / 2, by
      have hi := i.property
      simp only [Finset.mem_range] at hi
      omega⟩,
     ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
  left_inv jr := by
    apply Prod.ext <;> apply Fin.ext <;> simp only
    · omega
    · omega
  right_inv i := by
    apply Subtype.ext
    simp only
    omega

/-- Grouping consecutive directions into adjacent pairs is a finite-prefix
equivalence. -/
def pairPrefixEquiv (n : ℕ) : (Fin n → IncrementPair) ≃ Prefix (2 * n) where
  toFun v i :=
    let jr := (pairIndexEquiv n).symm i
    v jr.1 jr.2
  invFun w j r := w (pairIndexEquiv n (j, r))
  left_inv v := by
    funext j r
    simp only
    rw [Equiv.symm_apply_apply]
  right_inv w := by
    funext i
    simp only
    rw [Equiv.apply_symm_apply]

theorem finitePosition_pairPrefixEquiv {n : ℕ} (v : Fin n → IncrementPair) :
    finitePosition (pairPrefixEquiv n v) = pairPrefixEndpoint v := by
  unfold finitePosition pairPrefixEndpoint
  calc
    (∑ i : ↑(Finset.range (2 * n)),
        directionStep (pairPrefixEquiv n v i)) =
        ∑ jr : Fin n × Fin 2, directionStep (v jr.1 jr.2) := by
      symm
      apply Fintype.sum_equiv (pairIndexEquiv n)
      intro jr
      simp [pairPrefixEquiv]
    _ = ∑ j : Fin n, ∑ r : Fin 2, directionStep (v j r) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ j : Fin n, pairStep (v j) := by
      apply Fintype.sum_congr
      intro j
      rw [Fin.sum_univ_two]
      rfl

def pairReturningPrefixes (n : ℕ) : Finset (Fin n → IncrementPair) :=
  Finset.univ.filter fun v ↦ pairPrefixEndpoint v = (0, 0)

theorem pairReturningPrefixes_card (n : ℕ) :
    (pairReturningPrefixes n).card = pairPathCount n (0, 0) := by
  rw [pairPathCount_eq_sum_indicator]
  unfold pairReturningPrefixes
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

def pairReturningEquiv (n : ℕ) :
    ↑(pairReturningPrefixes n) ≃ ↑(returningPrefixes (2 * n)) where
  toFun v := ⟨pairPrefixEquiv n v.1, by
    simp only [returningPrefixes, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [finitePosition_pairPrefixEquiv]
    simpa [pairReturningPrefixes] using v.2⟩
  invFun w := ⟨(pairPrefixEquiv n).symm w.1, by
    simp only [pairReturningPrefixes, Finset.mem_filter, Finset.mem_univ, true_and]
    have hw : finitePosition w.1 = (0, 0) := by
      simpa [returningPrefixes] using w.2
    rw [← finitePosition_pairPrefixEquiv]
    simpa using hw⟩
  left_inv v := by
    apply Subtype.ext
    exact (pairPrefixEquiv n).symm_apply_apply v.1
  right_inv w := by
    apply Subtype.ext
    exact (pairPrefixEquiv n).apply_symm_apply w.1

theorem pairPathCount_zero_eq_returningPrefixes (n : ℕ) :
    pairPathCount n (0, 0) = (returningPrefixes (2 * n)).card := by
  rw [← pairReturningPrefixes_card]
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (pairReturningEquiv n)

/-- Ordinary SRW at time `2n` is exactly the unrestricted adjacent-pair
walk at macro time `n`. -/
theorem returnProb_even_eq_pairPathCount (n : ℕ) :
    returnProb (2 * n) = (pairPathCount n (0, 0) : ℝ) / (16 : ℝ) ^ n := by
  rw [returnProb, return_real_even]
  rw [pairPathCount_zero_eq_returningPrefixes, returningPrefixes_card_even]
  push_cast
  have hpow : (4 : ℝ) ^ (2 * n) = 16 ^ n := by
    rw [pow_mul]
    norm_num
  rw [hpow]

def terminalReturningPrefixes (n : ℕ) : Finset (Fin n → TerminalLabel) :=
  Finset.univ.filter fun v ↦ terminalPrefixEndpoint v = (0, 0)

theorem terminalReturningPrefixes_card (n : ℕ) :
    (terminalReturningPrefixes n).card = terminalPathCount n (0, 0) := by
  rw [terminalPathCount_eq_sum_indicator]
  unfold terminalReturningPrefixes
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

noncomputable def terminalPrefixLaw (n : ℕ) : Measure (Fin n → TerminalLabel) :=
  Measure.infinitePi fun _ : Fin n ↦ (PMF.uniformOfFintype TerminalLabel).toMeasure

theorem terminalLabel_iidBlock_map (n : ℕ) :
    terminalLabelLaw.map (iidBlock (X := TerminalLabel) 0 n) = terminalPrefixLaw n := by
  unfold terminalLabelLaw terminalPrefixLaw
  exact iidBlock_map (PMF.uniformOfFintype TerminalLabel).toMeasure 0 n

theorem terminalPrefixLaw_singleton (n : ℕ) (v : Fin n → TerminalLabel) :
    terminalPrefixLaw n {v} = (15 : ENNReal)⁻¹ ^ n := by
  unfold terminalPrefixLaw
  rw [Measure.infinitePi_singleton_of_fintype]
  simp [card_terminalLabel]

theorem terminalPrefixEndpoint_iidBlock (n : ℕ) (ω : ℕ → TerminalLabel) :
    terminalPrefixEndpoint (iidBlock (X := TerminalLabel) 0 n ω) =
      terminalMacroPath ω n := by
  unfold terminalPrefixEndpoint terminalMacroPath
  simp only [iidBlock, Nat.zero_add]
  exact Fin.sum_univ_eq_sum_range (fun i ↦ terminalStep (ω i)) n

theorem terminalMacroReturnProb_eq_count (n : ℕ) :
    terminalMacroReturnProb n =
      (terminalPathCount n (0, 0) : ℝ) / (15 : ℝ) ^ n := by
  let A := terminalReturningPrefixes n
  have hprobENN : terminalLabelLaw {ω | terminalMacroPath ω n = (0, 0)} =
      (terminalPathCount n (0, 0) : ENNReal) / (15 : ENNReal) ^ n := by
    calc
      terminalLabelLaw {ω | terminalMacroPath ω n = (0, 0)} =
          (terminalLabelLaw.map (iidBlock (X := TerminalLabel) 0 n))
            (A : Set (Fin n → TerminalLabel)) := by
        rw [Measure.map_apply (measurable_iidBlock 0 n) (by measurability)]
        congr 1
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Finset.mem_coe, A,
          terminalReturningPrefixes, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [terminalPrefixEndpoint_iidBlock]
      _ = terminalPrefixLaw n (A : Set (Fin n → TerminalLabel)) := by
        rw [terminalLabel_iidBlock_map]
      _ = ∑ v ∈ A, terminalPrefixLaw n {v} := by rw [sum_measure_singleton]
      _ = ∑ _v ∈ A, (15 : ENNReal)⁻¹ ^ n := by
        apply Finset.sum_congr rfl
        intro v hv
        exact terminalPrefixLaw_singleton n v
      _ = (terminalPathCount n (0, 0) : ENNReal) / (15 : ENNReal) ^ n := by
        rw [← terminalReturningPrefixes_card]
        simp [A, div_eq_mul_inv, ENNReal.inv_pow]
  unfold terminalMacroReturnProb
  rw [measureReal_def, hprobENN]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]

/-! ### A sharp lazy-chain Green transfer

If ordinary two-step SRW is viewed pair by pair, a distinguished pair occurs
with probability `1/16` and has zero displacement.  Removing exactly that
atom leaves the terminal-label law.  The lemmas below isolate the analytic
part of this de-lazification argument. -/

/-- Weight of seeing `j` retained labels and `k` distinguished holding pairs. -/
noncomputable def lazyPairWeight (j k : ℕ) : ℝ :=
  (Nat.choose (j + k) j : ℝ) * (15 / 16 : ℝ) ^ j * (1 / 16 : ℝ) ^ k

theorem lazyPairWeight_eq_negBinMass (j k : ℕ) :
    lazyPairWeight j k = (16 / 15 : ℝ) * HLOZUrn.negBinMass (j + 1) k := by
  unfold lazyPairWeight HLOZUrn.negBinMass
  have htop : j + 1 + k - 1 = j + k := by omega
  rw [htop, Nat.choose_symm_add]
  push_cast
  norm_num [div_pow, pow_add, pow_succ]
  ring

theorem summable_lazyPairWeight (j : ℕ) : Summable (lazyPairWeight j) := by
  rw [show lazyPairWeight j = fun k ↦
      (16 / 15 : ℝ) * HLOZUrn.negBinMass (j + 1) k by
    funext k; exact lazyPairWeight_eq_negBinMass j k]
  exact (HLOZUrn.negBinMass_summable (j + 1) (by omega)).mul_left _

theorem hasSum_lazyPairWeight (j : ℕ) :
    HasSum (lazyPairWeight j) (16 / 15 : ℝ) := by
  have h := HLOZUrn.hasSum_negBinMass_mul_exp (j + 1) (by omega) (t := 0)
    (by norm_num)
  have hmass : HasSum (HLOZUrn.negBinMass (j + 1)) 1 := by
    convert h using 1 <;> norm_num
  have hfun : lazyPairWeight j = fun k ↦
      (16 / 15 : ℝ) * HLOZUrn.negBinMass (j + 1) k := by
    funext k
    exact lazyPairWeight_eq_negBinMass j k
  rw [hfun]
  simpa only [mul_one] using hmass.mul_left (16 / 15 : ℝ)

theorem lazyPairWeight_nonneg (j k : ℕ) : 0 ≤ lazyPairWeight j k := by
  unfold lazyPairWeight
  positivity

theorem lazyPairWeight_le_geometric {j k : ℕ} (hjk : j ≤ k) :
    lazyPairWeight j k ≤ (1 / 4 : ℝ) ^ k := by
  unfold lazyPairWeight
  have hchooseN : Nat.choose (j + k) j ≤ 2 ^ (j + k) := Nat.choose_le_two_pow _ _
  have hchooseR : (Nat.choose (j + k) j : ℝ) ≤ (2 : ℝ) ^ (j + k) := by
    exact_mod_cast hchooseN
  have hq : (15 / 16 : ℝ) ^ j ≤ 1 := by
    exact pow_le_one₀ (by positivity) (by norm_num)
  calc
    (Nat.choose (j + k) j : ℝ) * (15 / 16 : ℝ) ^ j * (1 / 16 : ℝ) ^ k ≤
        (2 : ℝ) ^ (j + k) * 1 * (1 / 16 : ℝ) ^ k := by
      gcongr
    _ = (2 : ℝ) ^ j * (1 / 8 : ℝ) ^ k := by
      rw [pow_add]
      calc
        2 ^ j * 2 ^ k * 1 * (1 / 16 : ℝ) ^ k =
            2 ^ j * (2 ^ k * (1 / 16 : ℝ) ^ k) := by ring
        _ = 2 ^ j * ((2 : ℝ) * (1 / 16)) ^ k := by rw [mul_pow]
        _ = 2 ^ j * (1 / 8 : ℝ) ^ k := by norm_num
    _ ≤ (2 : ℝ) ^ k * (1 / 8 : ℝ) ^ k := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjk) (by positivity)
    _ = (1 / 4 : ℝ) ^ k := by
      rw [← mul_pow]
      norm_num

/-- The negative-binomial tail after `K`, uniformly for `j < K`. -/
theorem tsum_lazyPairWeight_natAdd_le {j K : ℕ} (hjK : j ≤ K) :
    ∑' t : ℕ, lazyPairWeight j (t + K) ≤
      (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ K := by
  have hpoint (t : ℕ) :
      lazyPairWeight j (t + K) ≤ (1 / 4 : ℝ) ^ (t + K) :=
    lazyPairWeight_le_geometric (hjK.trans (Nat.le_add_left K t))
  have hgeom : Summable (fun t : ℕ ↦ (1 / 4 : ℝ) ^ (t + K)) := by
    exact (summable_nat_add_iff K).2
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1))
  calc
    ∑' t : ℕ, lazyPairWeight j (t + K) ≤
        ∑' t : ℕ, (1 / 4 : ℝ) ^ (t + K) := by
      exact Summable.tsum_le_tsum hpoint
        ((summable_nat_add_iff K).2 (summable_lazyPairWeight j)) hgeom
    _ = (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ K := by
      have hfun : (fun t : ℕ ↦ (1 / 4 : ℝ) ^ (t + K)) =
          fun t : ℕ ↦ (1 / 4 : ℝ) ^ K * (1 / 4 : ℝ) ^ t := by
        funext t
        rw [add_comm, pow_add]
      rw [hfun]
      rw [tsum_mul_left]
      rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
      norm_num
      ring

theorem finite_lazyPairWeight_lower {j K : ℕ} (hjK : j ≤ K) :
    (16 / 15 : ℝ) - (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ K ≤
      ∑ k ∈ Finset.range K, lazyPairWeight j k := by
  have hsplit := (summable_lazyPairWeight j).sum_add_tsum_nat_add K
  have htotal := (hasSum_lazyPairWeight j).tsum_eq
  have htail := tsum_lazyPairWeight_natAdd_le hjK
  rw [htotal] at hsplit
  nlinarith

/-- Coefficient identity saying that `u` is the `1/16`-lazy version of `p`. -/
def IsLazyPairReturnLaw (u p : ℕ → ℝ) : Prop :=
  ∀ n, u n = ∑ j ∈ Finset.range (n + 1), lazyPairWeight j (n - j) * p j

/-- The unrestricted adjacent-pair return law is the `1/16`-lazy version of
the genuine fifteen-label terminal chain. -/
theorem terminalMacro_isLazyPairReturnLaw :
    IsLazyPairReturnLaw (fun j ↦ returnProb (2 * j))
      terminalMacroReturnProb := by
  intro n
  change returnProb (2 * n) =
    ∑ j ∈ Finset.range (n + 1), lazyPairWeight j (n - j) * terminalMacroReturnProb j
  rw [returnProb_even_eq_pairPathCount, pairPathCount_eq_binomial_terminal]
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [terminalMacroReturnProb_eq_count]
  unfold lazyPairWeight
  have hadd : j + (n - j) = n := Nat.add_sub_of_le hjn
  rw [hadd]
  push_cast
  simp only [div_pow]
  field_simp
  have hpow : (16 : ℝ) ^ j * 16 ^ (n - j) = 16 ^ n := by
    rw [← pow_add, hadd]
  simp only [one_pow]
  calc
    (n.choose j : ℝ) * terminalPathCount j (0, 0) * 16 ^ j * 16 ^ (n - j) =
        (n.choose j : ℝ) * terminalPathCount j (0, 0) *
          (16 ^ j * 16 ^ (n - j)) := by ring
    _ = _ := by rw [hpow]; ring

theorem sum_IsLazyPairReturnLaw (u p : ℕ → ℝ)
    (hlaw : IsLazyPairReturnLaw u p) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), u n =
      ∑ j ∈ Finset.range (M + 1), p j *
        (∑ k ∈ Finset.range (M + 1 - j), lazyPairWeight j k) := by
  induction M with
  | zero =>
      have h0 := hlaw 0
      simpa [lazyPairWeight] using h0
  | succ M ih =>
      rw [Finset.sum_range_succ, ih, hlaw]
      let oldTerm : ℕ → ℝ := fun j ↦
        p j * (∑ k ∈ Finset.range (M + 1 - j), lazyPairWeight j k)
      let edgeTerm : ℕ → ℝ := fun j ↦
        lazyPairWeight j (M + 1 - j) * p j
      let newTerm : ℕ → ℝ := fun j ↦
        p j * (∑ k ∈ Finset.range (M + 2 - j), lazyPairWeight j k)
      change (∑ j ∈ Finset.range (M + 1), oldTerm j) +
          ∑ j ∈ Finset.range (M + 2), edgeTerm j =
        ∑ j ∈ Finset.range (M + 2), newTerm j
      have hprefix :
          (∑ j ∈ Finset.range (M + 1), oldTerm j) +
              ∑ j ∈ Finset.range (M + 1), edgeTerm j =
            ∑ j ∈ Finset.range (M + 1), newTerm j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hjM : j ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        dsimp only [oldTerm, edgeTerm, newTerm]
        rw [show M + 2 - j = (M + 1 - j) + 1 by omega]
        rw [Finset.sum_range_succ]
        ring
      calc
        (∑ j ∈ Finset.range (M + 1), oldTerm j) +
              ∑ j ∈ Finset.range (M + 2), edgeTerm j =
            (∑ j ∈ Finset.range (M + 1), oldTerm j) +
              ((∑ j ∈ Finset.range (M + 1), edgeTerm j) + edgeTerm (M + 1)) := by
          apply congrArg (fun z : ℝ ↦
            (∑ j ∈ Finset.range (M + 1), oldTerm j) + z)
          exact Finset.sum_range_succ edgeTerm (M + 1)
        _ = ((∑ j ∈ Finset.range (M + 1), oldTerm j) +
              ∑ j ∈ Finset.range (M + 1), edgeTerm j) + edgeTerm (M + 1) := by ring
        _ = (∑ j ∈ Finset.range (M + 1), newTerm j) + edgeTerm (M + 1) := by
          rw [hprefix]
        _ = (∑ j ∈ Finset.range (M + 1), newTerm j) + newTerm (M + 1) := by
          congr 1
          dsimp only [edgeTerm, newTerm]
          simp [lazyPairWeight]
          ring
        _ = ∑ j ∈ Finset.range (M + 2), newTerm j := by
          exact (Finset.sum_range_succ newTerm (M + 1)).symm

noncomputable def finiteGreenSeq (p : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), p j

theorem lazyGreen_core (u p : ℕ → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hlaw : IsLazyPairReturnLaw u p) (J : ℕ) :
    ((16 / 15 : ℝ) - (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ (J + 1)) *
        finiteGreenSeq p J ≤ finiteGreenSeq u (2 * J) := by
  let e : ℝ := (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ (J + 1)
  let small : ℝ := ∑ j ∈ Finset.range (J + 1), p j *
    (∑ k ∈ Finset.range (J + 1), lazyPairWeight j k)
  have hsmall : ((16 / 15 : ℝ) - e) * finiteGreenSeq p J ≤ small := by
    dsimp only [finiteGreenSeq, small]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    calc
      ((16 / 15 : ℝ) - e) * p j = p j * ((16 / 15 : ℝ) - e) := mul_comm _ _
      _ ≤ p j * (∑ k ∈ Finset.range (J + 1), lazyPairWeight j k) := by
        apply mul_le_mul_of_nonneg_left _ (hp0 j)
        dsimp only [e]
        exact finite_lazyPairWeight_lower
          (show j ≤ J + 1 by exact (Finset.mem_range.mp hj).le)
  have hsmallFull : small ≤
      ∑ j ∈ Finset.range (2 * J + 1), p j *
        (∑ k ∈ Finset.range (2 * J + 1 - j), lazyPairWeight j k) := by
    dsimp only [small]
    calc
      ∑ j ∈ Finset.range (J + 1), p j *
          (∑ k ∈ Finset.range (J + 1), lazyPairWeight j k) ≤
          ∑ j ∈ Finset.range (J + 1), p j *
            (∑ k ∈ Finset.range (2 * J + 1 - j), lazyPairWeight j k) := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (hp0 j)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          simp only [Finset.mem_range] at hk ⊢
          have hjle : j ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          omega
        · intro k hk hnot
          exact lazyPairWeight_nonneg j k
      _ ≤ ∑ j ∈ Finset.range (2 * J + 1), p j *
          (∑ k ∈ Finset.range (2 * J + 1 - j), lazyPairWeight j k) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_range] at hj ⊢
          omega
        · intro j hj hnot
          exact mul_nonneg (hp0 j)
            (Finset.sum_nonneg fun k hk ↦ lazyPairWeight_nonneg j k)
  calc
    ((16 / 15 : ℝ) - (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ (J + 1)) *
        finiteGreenSeq p J = ((16 / 15 : ℝ) - e) * finiteGreenSeq p J := rfl
    _ ≤ small := hsmall
    _ ≤ _ := hsmallFull
    _ = finiteGreenSeq u (2 * J) := by
      symm
      exact sum_IsLazyPairReturnLaw u p hlaw (2 * J)

theorem error_mul_card_le_two (J : ℕ) :
    (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ (J + 1) * (J + 1 : ℝ) ≤ 2 := by
  have hnat : J + 1 ≤ 4 ^ (J + 1) := by
    induction J with
    | zero => norm_num
    | succ J ih =>
        calc
          J + 1 + 1 ≤ 4 * (J + 1) := by omega
          _ ≤ 4 * 4 ^ (J + 1) := Nat.mul_le_mul_left 4 ih
          _ = 4 ^ (J + 1 + 1) := by rw [pow_succ]; ring
  have hreal : (J + 1 : ℝ) ≤ (4 : ℝ) ^ (J + 1) := by exact_mod_cast hnat
  have hpowpos : 0 < (4 : ℝ) ^ (J + 1) := by positivity
  have hdiv : (J + 1 : ℝ) / (4 : ℝ) ^ (J + 1) ≤ 1 :=
    (div_le_one hpowpos).2 hreal
  calc
    (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ (J + 1) * (J + 1 : ℝ) =
        (4 / 3 : ℝ) * ((J + 1 : ℝ) / 4 ^ (J + 1)) := by
      rw [div_pow]
      ring
    _ ≤ (4 / 3 : ℝ) * 1 := mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ ≤ 2 := by norm_num

/-- Sharp de-lazification: the external Green function costs exactly the
factor `15/16`, with only an absolute additive error. -/
theorem finiteGreenSeq_le_fifteen_sixteen (u p : ℕ → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (hlaw : IsLazyPairReturnLaw u p) (J : ℕ) :
    finiteGreenSeq p J ≤
      (15 / 16 : ℝ) * finiteGreenSeq u (2 * J) + 2 := by
  have hcore := lazyGreen_core u p hp0 hlaw J
  have hGp0 : 0 ≤ finiteGreenSeq p J :=
    Finset.sum_nonneg fun j hj ↦ hp0 j
  have hcard : finiteGreenSeq p J ≤ (J + 1 : ℝ) := by
    calc
      finiteGreenSeq p J ≤ ∑ _j ∈ Finset.range (J + 1), (1 : ℝ) := by
        exact Finset.sum_le_sum fun j hj ↦ hp1 j
      _ = (J + 1 : ℝ) := by simp
  have herr := error_mul_card_le_two J
  let e : ℝ := (4 / 3 : ℝ) * (1 / 4 : ℝ) ^ (J + 1)
  have heGp : e * finiteGreenSeq p J ≤ 2 := by
    calc
      e * finiteGreenSeq p J ≤ e * (J + 1 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hcard (by positivity)
      _ ≤ 2 := herr
  have hmain : (16 / 15 : ℝ) * finiteGreenSeq p J ≤
      finiteGreenSeq u (2 * J) + 2 := by
    dsimp only [e] at heGp
    nlinarith
  nlinarith

/-- The paired ordinary SRW Green function has the exact `1/π` logarithmic
upper coefficient needed by the de-lazification argument. -/
theorem ordinaryEvenFiniteGreen_le_harmonic (M : ℕ) :
    finiteGreenSeq (fun j ↦ returnProb (2 * j)) M ≤
      1 + (1 / Real.pi) * (harmonic M : ℝ) := by
  rw [show finiteGreenSeq (fun j ↦ returnProb (2 * j)) M =
      returnProb 0 + ∑ j ∈ Finset.range M, returnProb (2 * (j + 1)) by
    unfold finiteGreenSeq
    rw [Finset.sum_range_succ']
    simp
    ring]
  have hzero : returnProb 0 = 1 := by
    have hevent : { ω : ℕ → Direction | simpleRandomWalk ω 0 = (0, 0) } = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      change (∑ j ∈ Finset.range 0, directionStep (ω j)) = (0, 0)
      rw [Finset.sum_range_zero]
      change ((0 : ℤ), (0 : ℤ)) = (0, 0)
      rfl
    rw [returnProb, hevent]
    simp
  rw [hzero]
  gcongr
  calc
    ∑ j ∈ Finset.range M, returnProb (2 * (j + 1)) ≤
        ∑ j ∈ Finset.range M,
          1 / (Real.pi * ((j + 1 : ℕ) : ℝ)) := by
      exact Finset.sum_le_sum fun j hj ↦
        returnProb_even_le_one_div_pi_mul (j + 1) (by omega)
    _ = (1 / Real.pi) * (harmonic M : ℝ) := by
      rw [harmonic]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp

theorem ordinaryEvenFiniteGreen_le_log {M : ℕ} (hM : 1 ≤ M) :
    finiteGreenSeq (fun j ↦ returnProb (2 * j)) M ≤
      1 + (1 / Real.pi) * (1 + Real.log (M : ℝ)) := by
  have hh := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M)
    (by positivity : (0 : ℝ) ≤ 1 / Real.pi)
  exact (ordinaryEvenFiniteGreen_le_harmonic M).trans (by nlinarith)

/-- Source-facing sharp Green consequence of the lazy relation. -/
theorem terminalGreen_le_sharp_of_lazyLaw
    (hlaw : IsLazyPairReturnLaw (fun j ↦ returnProb (2 * j))
      terminalMacroReturnProb) (J : ℕ) (hJ : 1 ≤ J) :
    finiteGreenSeq terminalMacroReturnProb J ≤
      (15 / (16 * Real.pi)) * Real.log (J : ℝ) + 5 := by
  have hp0 : ∀ j, 0 ≤ terminalMacroReturnProb j :=
    terminalMacroReturnProb_nonneg
  have hp1 : ∀ j, terminalMacroReturnProb j ≤ 1 := by
    intro j
    exact measureReal_le_one
  have htransfer := finiteGreenSeq_le_fifteen_sixteen
    (fun j ↦ returnProb (2 * j)) terminalMacroReturnProb hp0 hp1 hlaw J
  have hordinary := ordinaryEvenFiniteGreen_le_log (M := 2 * J) (by omega)
  calc
    finiteGreenSeq terminalMacroReturnProb J ≤
        (15 / 16 : ℝ) * finiteGreenSeq (fun j ↦ returnProb (2 * j)) (2 * J) + 2 :=
      htransfer
    _ ≤ (15 / 16 : ℝ) *
        (1 + (1 / Real.pi) * (1 + Real.log ((2 * J : ℕ) : ℝ))) + 2 := by
      gcongr
    _ ≤ (15 / (16 * Real.pi)) * Real.log (J : ℝ) + 5 := by
      have hJreal : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      have hlogmul : Real.log ((2 * J : ℕ) : ℝ) =
          Real.log 2 + Real.log (J : ℝ) := by
        push_cast
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
      rw [hlogmul]
      have hpi : 3 < Real.pi := Real.pi_gt_three
      have hlogtwo : Real.log 2 < 1 :=
        Real.log_two_lt_d9.trans (by norm_num)
      have hinvpi : (1 / Real.pi : ℝ) ≤ 1 / 3 := by
        exact one_div_le_one_div_of_le (by norm_num) hpi.le
      have hsum : 0 ≤ 1 + Real.log 2 := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith
      have hprod : (1 / Real.pi) * (1 + Real.log 2) ≤ (1 / 3 : ℝ) * 2 := by
        exact (mul_le_mul hinvpi (by linarith [hlogtwo]) hsum (by positivity))
      have hcoeff : (15 / 16 : ℝ) * (1 / Real.pi) * Real.log (J : ℝ) =
          15 / (16 * Real.pi) * Real.log (J : ℝ) := by
        field_simp
      rw [← hcoeff]
      nlinarith

/-! ### Identification with the source external chain -/

theorem externalWalk_even_eq_terminalMacroPath
    (labels : ℕ → ExternalPairLabel) (m : ℕ) :
    externalWalk labels (2 * m) = terminalMacroPath labels m := by
  induction m with
  | zero => simp [externalWalk, simpleRandomWalk, terminalMacroPath]
  | succ m ih =>
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        externalWalk_succ, show 2 * m + 1 = 2 * m + 1 by rfl,
        externalWalk_succ, ih]
      simp only [terminalMacroPath, Finset.sum_range_succ]
      have hdiv : (2 * m + 1) / 2 = m := by omega
      simp [externalDirectionStream, pairOffset, terminalStep, hdiv]
      abel

theorem terminalLabelLaw_eq_externalLabelLaw :
    terminalLabelLaw = externalLabelLaw := by
  rfl

theorem externalReturnProb_even (m : ℕ) :
    externalReturnProb (2 * m) = terminalMacroReturnProb m := by
  have h := externalPathLaw_return_eq_externalChainReturnAt (2 * m)
  rw [externalPathLaw,
    Measure.map_apply measurable_externalWalk
      (measurableSet_eq_fun (measurable_pi_apply (2 * m)) measurable_const)] at h
  change externalLabelLaw
      {labels | externalWalk labels (2 * m) = (0, 0)} = _ at h
  unfold externalReturnProb terminalMacroReturnProb
  rw [Measure.real, Measure.real]
  have hr := congrArg ENNReal.toReal h.symm
  simpa only [terminalLabelLaw_eq_externalLabelLaw,
    externalWalk_even_eq_terminalMacroPath] using hr

theorem externalWalk_odd_ne_zero
    (labels : ℕ → ExternalPairLabel) (m : ℕ) :
    externalWalk labels (2 * m + 1) ≠ (0, 0) := by
  intro hzero
  have hchess : HLOZPairing.chessEven (externalWalk labels (2 * m + 1)) := by
    rw [hzero]
    norm_num [HLOZPairing.chessEven]
  have heven := (chessEven_externalWalk_iff labels (2 * m + 1)).mp hchess
  obtain ⟨q, hq⟩ := heven
  omega

theorem externalReturnProb_odd (m : ℕ) :
    externalReturnProb (2 * m + 1) = 0 := by
  have hbridge := externalPathLaw_return_eq_externalChainReturnAt (2 * m + 1)
  unfold externalReturnProb
  rw [Measure.real]
  have hr := congrArg ENNReal.toReal hbridge.symm
  rw [externalPathLaw,
    Measure.map_apply measurable_externalWalk
      (measurableSet_eq_fun (measurable_pi_apply (2 * m + 1)) measurable_const)] at hr
  have hevent :
      {labels : ℕ → ExternalPairLabel |
          externalWalk labels (2 * m + 1) = (0, 0)} = ∅ := by
    ext labels
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact externalWalk_odd_ne_zero labels m
  change (incrementLaw (externalChainReturnAt (2 * m + 1))).toReal =
    (externalLabelLaw
      {labels | externalWalk labels (2 * m + 1) = (0, 0)}).toReal at hr
  rw [hevent] at hr
  simpa using hr

theorem externalFiniteGreen_succ (n : ℕ) :
    externalFiniteGreen (n + 1) =
      externalFiniteGreen n + externalReturnProb (n + 1) := by
  unfold externalFiniteGreen
  rw [show n + 1 + 1 = (n + 1) + 1 by omega, Finset.sum_range_succ]

theorem externalFiniteGreen_even (m : ℕ) :
    externalFiniteGreen (2 * m) = finiteGreenSeq terminalMacroReturnProb m := by
  induction m with
  | zero =>
      simpa [externalFiniteGreen, finiteGreenSeq] using externalReturnProb_even 0
  | succ m ih =>
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        externalFiniteGreen_succ, externalFiniteGreen_succ, ih]
      rw [show 2 * m + 1 = 2 * m + 1 by rfl,
        externalReturnProb_odd, show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
        externalReturnProb_even]
      unfold finiteGreenSeq
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      ring

theorem externalFiniteGreen_odd (m : ℕ) :
    externalFiniteGreen (2 * m + 1) = finiteGreenSeq terminalMacroReturnProb m := by
  rw [externalFiniteGreen_succ, externalFiniteGreen_even,
    externalReturnProb_odd]
  ring

/-- The genuine external chain has the sharp HLOZ Green coefficient
`15/(16π)`, with an absolute additive error. -/
theorem hasExternalSharpGreenUpper : HasExternalSharpGreenUpper := by
  refine ⟨5, Filter.eventually_atTop.2 ⟨2, ?_⟩⟩
  intro n hn
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 1 ≤ m := by omega
    rw [externalFiniteGreen_even]
    refine (terminalGreen_le_sharp_of_lazyLaw
      terminalMacro_isLazyPairReturnLaw m hm).trans ?_
    have hlog : Real.log (m : ℝ) ≤ Real.log ((2 * m : ℕ) : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · change 0 < (m : ℝ)
        exact_mod_cast (show 0 < m by omega)
      · change 0 < ((2 * m : ℕ) : ℝ)
        exact_mod_cast (show 0 < 2 * m by omega)
      · exact_mod_cast (show m ≤ 2 * m by omega)
    have hcoeff : 0 ≤ 15 / (16 * Real.pi) := by positivity
    gcongr
  · have hm : 1 ≤ m := by omega
    rw [externalFiniteGreen_odd]
    refine (terminalGreen_le_sharp_of_lazyLaw
      terminalMacro_isLazyPairReturnLaw m hm).trans ?_
    have hlog : Real.log (m : ℝ) ≤ Real.log ((2 * m + 1 : ℕ) : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · change 0 < (m : ℝ)
        exact_mod_cast (show 0 < m by omega)
      · change 0 < ((2 * m + 1 : ℕ) : ℝ)
        exact_mod_cast (show 0 < 2 * m + 1 by omega)
      · exact_mod_cast (show m ≤ 2 * m + 1 by omega)
    have hcoeff : 0 ≤ 15 / (16 * Real.pi) := by positivity
    gcongr

/-- The genuine external-clock upper deviation (HLOZ (2.19)) is now
unconditional: combine the sharp Green estimate with the iid fixed-origin
kernel. -/
theorem hasExternalChainUpperDeviation : HasExternalChainUpperDeviation :=
  HLOZExternalKernel.hasExternalChainUpperDeviation_of_sharpGreen
    hasExternalSharpGreenUpper

/-- HLOZ Proposition 4.4 for the actual iid terminal-label external chain,
with both probabilistic inputs discharged. -/
theorem eventually_prop44_many_even_sites_bound :
    ∀ᶠ m : ℕ in atTop,
      externalPathLaw {s |
          Real.exp (16 * (m : ℝ) ^ prop44RateExponent) <
            ((evenSitesAtLeastReal s (prop44Psi m)
              (prop44SiteThreshold m)).card : ℝ)} ≤
        ENNReal.ofReal
          (Real.exp (-(m : ℝ) ^ prop44RateExponent)) :=
  HLOZProp44ExternalChain.eventually_prop44_many_even_sites_bound_of_chain_deviation
    hasExternalChainUpperDeviation

end Erdos1166.HLOZExternalStepLaw
