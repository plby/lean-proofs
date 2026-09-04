import ErdosProblems.Erdos381.FixedPowerPrimes
import ErdosProblems.Erdos381.Trial
import ErdosProblems.Erdos381.Pade

namespace Erdos381

open Complex Set Filter Asymptotics
open scoped BigOperators ComplexConjugate Topology

noncomputable section

theorem exists_fixedPower_prime_windows :
    ∃ L N₀ : ℕ, 8 ≤ L ∧ ∀ n : ℕ, N₀ ≤ n →
      ∃ p : ℕ, p.Prime ∧ n ^ L < p ∧ p ≤ (n + 1) ^ L := by
  obtain ⟨L, hL, h⟩ := eventually_exists_prime_between_consecutive_fixed_powers
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 h
  exact ⟨L, N₀, hL, hN₀⟩

theorem rpow_inv_natCast_pow_eq {x : ℝ} (hx : 0 < x) {L : ℕ}
    (hL : 0 < L) :
    (x ^ (1 / (L : ℝ))) ^ L = x := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx.le]
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [one_div, inv_mul_cancel₀ hLR, Real.rpow_one]

/-- The natural floor of the fixed-power root brackets a positive real
number between two consecutive powers. -/
theorem floor_rpow_root_bracket {x : ℝ} (hx : 0 < x) {L : ℕ}
    (hL : 0 < L) :
    let a := ⌊x ^ (1 / (L : ℝ))⌋₊
    ((a : ℝ) ^ L ≤ x) ∧ (x < ((a + 1 : ℕ) : ℝ) ^ L) := by
  let r : ℝ := x ^ (1 / (L : ℝ))
  let a : ℕ := ⌊r⌋₊
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hfloor : (a : ℝ) ≤ r := by
    dsimp [a]
    exact Nat.floor_le hr0
  have hfloorSucc : r < (a : ℝ) + 1 := by
    simpa [a] using Nat.lt_floor_add_one r
  have hrpow : r ^ L = x := by
    dsimp [r]
    exact rpow_inv_natCast_pow_eq hx hL
  change ((a : ℝ) ^ L ≤ x) ∧ x < (((a + 1 : ℕ) : ℝ) ^ L)
  constructor
  · rw [← hrpow]
    exact pow_le_pow_left₀ (by positivity) hfloor L
  · rw [← hrpow]
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact pow_lt_pow_left₀ hfloorSucc (by positivity) (by omega)

/-- Consecutive fixed-power windows give arbitrarily long, pairwise distinct
prime blocks on both sides of a real center.  The hypotheses say that the
root index is far enough beyond the uniform starting point. -/
theorem exists_prime_blocks_around
    {L N₀ H a : ℕ} {x : ℝ} (hL : 0 < L)
    (hwindow : ∀ n : ℕ, N₀ ≤ n →
      ∃ p : ℕ, p.Prime ∧ n ^ L < p ∧ p ≤ (n + 1) ^ L)
    (hrootLow : ((a : ℝ) ^ L) ≤ x)
    (hrootHigh : x < (((a + 1 : ℕ) : ℝ) ^ L))
    (ha : N₀ + H + 1 ≤ a) :
    ∃ up down : Fin H → ℕ,
      Function.Injective up ∧ Function.Injective down ∧
      (∀ i, (up i).Prime ∧ x < up i ∧
        up i ≤ (a + H + 1) ^ L) ∧
      (∀ i, (down i).Prime ∧ (a - (H + 1)) ^ L < down i ∧
        (down i : ℝ) < x) := by
  let upBase : Fin H → ℕ := fun i ↦ a + i.1 + 1
  let downBase : Fin H → ℕ := fun i ↦ a - (i.1 + 2)
  have hupStart : ∀ i, N₀ ≤ upBase i := by
    intro i
    dsimp [upBase]
    omega
  have hdownStart : ∀ i, N₀ ≤ downBase i := by
    intro i
    dsimp [downBase]
    omega
  let up : Fin H → ℕ := fun i ↦
    Classical.choose (hwindow (upBase i) (hupStart i))
  let down : Fin H → ℕ := fun i ↦
    Classical.choose (hwindow (downBase i) (hdownStart i))
  have hupSpec : ∀ i, (up i).Prime ∧
      (upBase i) ^ L < up i ∧ up i ≤ (upBase i + 1) ^ L := by
    intro i
    exact Classical.choose_spec (hwindow (upBase i) (hupStart i))
  have hdownSpec : ∀ i, (down i).Prime ∧
      (downBase i) ^ L < down i ∧ down i ≤ (downBase i + 1) ^ L := by
    intro i
    exact Classical.choose_spec (hwindow (downBase i) (hdownStart i))
  have hupInj : Function.Injective up := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hbase : upBase i + 1 ≤ upBase j := by
        dsimp [upBase]
        omega
      have hpij : up i < up j := by
        calc
          up i ≤ (upBase i + 1) ^ L := (hupSpec i).2.2
          _ ≤ (upBase j) ^ L := Nat.pow_le_pow_left hbase L
          _ < up j := (hupSpec j).2.1
      exact (ne_of_lt hpij) hij
    · have hbase : upBase j + 1 ≤ upBase i := by
        dsimp [upBase]
        omega
      have hpji : up j < up i := by
        calc
          up j ≤ (upBase j + 1) ^ L := (hupSpec j).2.2
          _ ≤ (upBase i) ^ L := Nat.pow_le_pow_left hbase L
          _ < up i := (hupSpec i).2.1
      exact (ne_of_lt hpji) hij.symm
  have hdownInj : Function.Injective down := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hbase : downBase j + 1 ≤ downBase i := by
        dsimp [downBase]
        omega
      have hpji : down j < down i := by
        calc
          down j ≤ (downBase j + 1) ^ L := (hdownSpec j).2.2
          _ ≤ (downBase i) ^ L := Nat.pow_le_pow_left hbase L
          _ < down i := (hdownSpec i).2.1
      exact (ne_of_lt hpji) hij.symm
    · have hbase : downBase i + 1 ≤ downBase j := by
        dsimp [downBase]
        omega
      have hpij : down i < down j := by
        calc
          down i ≤ (downBase i + 1) ^ L := (hdownSpec i).2.2
          _ ≤ (downBase j) ^ L := Nat.pow_le_pow_left hbase L
          _ < down j := (hdownSpec j).2.1
      exact (ne_of_lt hpij) hij
  refine ⟨up, down, hupInj, hdownInj, ?_, ?_⟩
  · intro i
    refine ⟨(hupSpec i).1, ?_, ?_⟩
    · have hroot : (((a + 1 : ℕ) : ℝ) ^ L) ≤
          ((upBase i : ℕ) : ℝ) ^ L := by
        exact_mod_cast Nat.pow_le_pow_left (by dsimp [upBase]; omega) L
      exact (hrootHigh.trans_le hroot).trans
        (by exact_mod_cast (hupSpec i).2.1)
    · exact (hupSpec i).2.2.trans
        (Nat.pow_le_pow_left (by dsimp [upBase]; omega) L)
  · intro i
    refine ⟨(hdownSpec i).1, ?_, ?_⟩
    · exact (Nat.pow_le_pow_left (by dsimp [downBase]; omega) L).trans_lt
        (hdownSpec i).2.1
    · have hupper : down i ≤ (a - 1) ^ L :=
        (hdownSpec i).2.2.trans
          (Nat.pow_le_pow_left (by dsimp [downBase]; omega) L)
      have hpowlt : (a - 1) ^ L < a ^ L :=
        Nat.pow_lt_pow_left (by omega) hL.ne'
      have hnat : down i < a ^ L := hupper.trans_lt hpowlt
      exact (by exact_mod_cast hnat : (down i : ℝ) < (a : ℝ) ^ L) |>.trans_le
        hrootLow

theorem log_sub_log_le_sub_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log b - Real.log a ≤ (b - a) / a := by
  have hb : 0 < b := ha.trans_le hab
  calc
    Real.log b - Real.log a = Real.log (b / a) := by
      rw [Real.log_div hb.ne' ha.ne']
    _ ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
    _ = (b - a) / a := by field_simp

theorem log_gap_le_of_power_bounds
    {a b L : ℕ} {x p : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hax : (a : ℝ) ^ L ≤ x) (hxp : x ≤ p)
    (hpb : p ≤ (b : ℝ) ^ L) :
    Real.log p - Real.log x ≤
      (L : ℝ) * (((b : ℝ) - a) / a) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := haR.trans_le (by exact_mod_cast hab)
  have hxa : 0 < x := (pow_pos haR L).trans_le hax
  have hpa : 0 < p := hxa.trans_le hxp
  have hlogLow : (L : ℝ) * Real.log (a : ℝ) ≤ Real.log x := by
    rw [← Real.log_pow]
    exact Real.log_le_log (pow_pos haR L) hax
  have hlogHigh : Real.log p ≤ (L : ℝ) * Real.log (b : ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log hpa hpb
  have habR : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
  have hbase := log_sub_log_le_sub_div haR habR
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  calc
    Real.log p - Real.log x ≤
        (L : ℝ) * (Real.log b - Real.log a) := by
      calc
        Real.log p - Real.log x ≤
            (L : ℝ) * Real.log b - (L : ℝ) * Real.log a :=
          sub_le_sub hlogHigh hlogLow
        _ = (L : ℝ) * (Real.log b - Real.log a) := by ring
    _ ≤ (L : ℝ) * (((b : ℝ) - a) / a) :=
      mul_le_mul_of_nonneg_left hbase hL0

/-- The two prime blocks supplied above have logarithmic displacement at
most a root-scale quantity. -/
theorem prime_blocks_log_error
    {L N₀ H a : ℕ} {x : ℝ} (hL : 0 < L)
    (hwindow : ∀ n : ℕ, N₀ ≤ n →
      ∃ p : ℕ, p.Prime ∧ n ^ L < p ∧ p ≤ (n + 1) ^ L)
    (hrootLow : ((a : ℝ) ^ L) ≤ x)
    (hrootHigh : x < (((a + 1 : ℕ) : ℝ) ^ L))
    (ha : N₀ + H + 1 ≤ a) (hHa : 2 * H + 4 ≤ a) :
    ∃ up down : Fin H → ℕ,
      Function.Injective up ∧ Function.Injective down ∧
      (∀ i, (up i).Prime ∧ x < up i ∧
        |Real.log (up i) - Real.log x| ≤
          (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a : ℝ)) ∧
      (∀ i, (down i).Prime ∧ (down i : ℝ) < x ∧
        |Real.log (down i) - Real.log x| ≤
          (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a : ℝ)) := by
  obtain ⟨up, down, hupInj, hdownInj, hup, hdown⟩ :=
    exists_prime_blocks_around hL hwindow hrootLow hrootHigh ha
  have ha0 : 0 < a := by omega
  have haH0 : 0 < a - (H + 1) := by omega
  have hratio :
      ((H + 2 : ℕ) : ℝ) / ((a - (H + 1) : ℕ) : ℝ) ≤
        2 * ((H + 2 : ℕ) : ℝ) / (a : ℝ) := by
    have hden : (a : ℝ) ≤ 2 * (a - (H + 1) : ℕ) := by
      exact_mod_cast (show a ≤ 2 * (a - (H + 1)) by omega)
    have hapos : (0 : ℝ) < a := by exact_mod_cast ha0
    have haHpos : (0 : ℝ) < (a - (H + 1) : ℕ) := by exact_mod_cast haH0
    rw [div_le_div_iff₀ haHpos hapos]
    have hnum : (0 : ℝ) ≤ (H + 2 : ℕ) := by positivity
    nlinarith
  refine ⟨up, down, hupInj, hdownInj, ?_, ?_⟩
  · intro i
    refine ⟨(hup i).1, (hup i).2.1, ?_⟩
    rw [abs_of_nonneg]
    · have hmain := log_gap_le_of_power_bounds
          (a := a) (b := a + H + 1) (L := L)
          (x := x) (p := (up i : ℝ)) ha0 (by omega)
          hrootLow (hup i).2.1.le (by exact_mod_cast (hup i).2.2)
      have hmain' : Real.log (up i) - Real.log x ≤
          (L : ℝ) * (((H + 1 : ℕ) : ℝ) / (a : ℝ)) := by
        convert hmain using 1 <;>
          norm_num only [Nat.cast_add, Nat.cast_one] <;> ring
      calc
        Real.log (up i) - Real.log x ≤
            (L : ℝ) * (((H + 1 : ℕ) : ℝ) / (a : ℝ)) := hmain'
        _ ≤ (L : ℝ) * (((H + 2 : ℕ) : ℝ) / (a : ℝ)) := by
          gcongr <;> norm_num
        _ ≤ (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a : ℝ) := by
          have ht : 0 ≤ (L : ℝ) * (((H + 2 : ℕ) : ℝ) / (a : ℝ)) := by
            positivity
          have htarget :
              (((2 * L : ℕ) : ℝ) * ((H + 2 : ℕ) : ℝ) / (a : ℝ)) =
                2 * ((L : ℝ) * (((H + 2 : ℕ) : ℝ) / (a : ℝ))) := by
            push_cast
            ring
          rw [htarget]
          exact le_mul_of_one_le_left ht (by norm_num)
    · have hxpos : 0 < x :=
          (pow_pos (by exact_mod_cast ha0 : (0 : ℝ) < a) L).trans_le hrootLow
      exact sub_nonneg.mpr (Real.log_le_log hxpos (hup i).2.1.le)
  · intro i
    refine ⟨(hdown i).1, (hdown i).2.2, ?_⟩
    rw [abs_sub_comm, abs_of_nonneg]
    · have hmain := log_gap_le_of_power_bounds
          (a := a - (H + 1)) (b := a + 1) (L := L)
          (x := (down i : ℝ)) (p := x) haH0 (by omega)
          (by exact_mod_cast (hdown i).2.1.le)
          (hdown i).2.2.le hrootHigh.le
      norm_num only [Nat.cast_add, Nat.cast_one] at hmain
      have hdiff :
          (a : ℝ) + 1 - ((a - (H + 1) : ℕ) : ℝ) = ((H + 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : H + 1 ≤ a)]
        push_cast
        ring
      rw [hdiff] at hmain
      have hL0 : (0 : ℝ) ≤ L := by positivity
      calc
        Real.log x - Real.log (down i) ≤
            (L : ℝ) * (((H + 2 : ℕ) : ℝ) / (a - (H + 1) : ℕ)) := by
              exact hmain
        _ ≤ (L : ℝ) *
            (2 * ((H + 2 : ℕ) : ℝ) / (a : ℝ)) :=
              mul_le_mul_of_nonneg_left hratio hL0
        _ = (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a : ℝ) := by
              push_cast
              ring
    · exact sub_nonneg.mpr <| Real.log_le_log
        (by exact_mod_cast (hdown i).1.pos) (hdown i).2.2.le

/-- Change every exponent in `up` by `+1`, every exponent in `down` by
`-1`, and leave all other coordinates unchanged. -/
noncomputable def modifyFactorization
    (f : ℕ →₀ ℕ) (up down : Finset ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset (f.support ∪ up ∪ down)
    (fun p ↦ if p ∈ up then f p + 1 else if p ∈ down then f p - 1 else f p)
    (by
      intro p hp
      by_cases hpu : p ∈ up
      · exact Finset.mem_union_left down (Finset.mem_union_right _ hpu)
      by_cases hpd : p ∈ down
      · exact Finset.mem_union_right _ hpd
      have hfp : f p ≠ 0 := by simpa [hpu, hpd] using hp
      exact Finset.mem_union_left down
        (Finset.mem_union_left up (Finsupp.mem_support_iff.mpr hfp)))

@[simp] theorem modifyFactorization_apply
    (f : ℕ →₀ ℕ) (up down : Finset ℕ) (p : ℕ) :
    modifyFactorization f up down p =
      if p ∈ up then f p + 1 else if p ∈ down then f p - 1 else f p := by
  simp [modifyFactorization]

theorem modifyFactorization_eq_of_not_mem
    {f : ℕ →₀ ℕ} {up down : Finset ℕ} {p : ℕ}
    (hup : p ∉ up) (hdown : p ∉ down) :
    modifyFactorization f up down p = f p := by
  simp [modifyFactorization_apply, hup, hdown]

theorem modifyFactorization_prime_support
    {f : ℕ →₀ ℕ} {up down : Finset ℕ}
    (hf : ∀ p ∈ f.support, p.Prime)
    (hup : ∀ p ∈ up, p.Prime) (hdown : ∀ p ∈ down, p.Prime) :
    ∀ p ∈ (modifyFactorization f up down).support, p.Prime := by
  intro p hp
  by_cases hpu : p ∈ up
  · exact hup p hpu
  by_cases hpd : p ∈ down
  · exact hdown p hpd
  apply hf p
  rw [Finsupp.mem_support_iff] at hp ⊢
  simpa [modifyFactorization_apply, hpu, hpd] using hp

/-- The benefit of a finite coordinate modification is the sum of its local
benefits over the changed coordinates. -/
theorem benefit_from_modifyFactorization
    {ε : ℝ} {N : ℕ} {up down : Finset ℕ}
    (hN : 0 < N)
    (hupPrime : ∀ p ∈ up, p.Prime)
    (hdownPrime : ∀ p ∈ down, p.Prime)
    (hdownPos : ∀ p ∈ down, 0 < N.factorization p) :
    let g := modifyFactorization N.factorization up down
    benefit ε N (fromFactorization g) =
      ∑ p ∈ up ∪ down,
        localBenefit ε p (N.factorization p) (g p) := by
  let g := modifyFactorization N.factorization up down
  have hfN : ∀ p ∈ N.factorization.support, p.Prime := by
    intro p hp
    rw [Nat.support_factorization] at hp
    exact Nat.prime_of_mem_primeFactors hp
  have hgPrime : ∀ p ∈ g.support, p.Prime :=
    modifyFactorization_prime_support hfN hupPrime hdownPrime
  have hMpos : 0 < fromFactorization g := fromFactorization_pos hgPrime
  change benefit ε N (fromFactorization g) =
    ∑ p ∈ up ∪ down, localBenefit ε p (N.factorization p) (g p)
  rw [benefit_eq_factorizationBenefit hN.ne' hMpos.ne', factorizationBenefit,
    factorization_fromFactorization hgPrime]
  let S := N.primeFactors ∪ (fromFactorization g).primeFactors
  have hzero : ∀ p ∈ S, p ∉ up ∪ down →
      localBenefit ε p (N.factorization p) (g p) = 0 := by
    intro p hp hpchange
    have hpu : p ∉ up := fun h ↦ hpchange (Finset.mem_union_left _ h)
    have hpd : p ∉ down := fun h ↦ hpchange (Finset.mem_union_right _ h)
    rw [modifyFactorization_eq_of_not_mem hpu hpd]
    simp [localBenefit]
  have hchangeSubset : up ∪ down ⊆ S := by
    intro p hp
    have hpPrime : p.Prime := by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hupPrime p hp
      · exact hdownPrime p hp
    by_cases hpN : 0 < N.factorization p
    · exact Finset.mem_union_left _ <|
        (Nat.mem_primeFactors_of_ne_zero hN.ne').2
          ⟨hpPrime, Nat.dvd_of_factorization_pos hpN.ne'⟩
    · have hpg : 0 < g p := by
        have hpu : p ∈ up := by
          rcases Finset.mem_union.mp hp with hpu | hpd
          · exact hpu
          · exact (hpN (hdownPos p hpd)).elim
        simp [g, modifyFactorization_apply, hpu]
      apply Finset.mem_union_right
      rw [← Nat.support_factorization, factorization_fromFactorization hgPrime,
        Finsupp.mem_support_iff]
      exact hpg.ne'
  rw [show N.primeFactors ∪ (fromFactorization g).primeFactors = S by rfl]
  exact (Finset.sum_subset hchangeSubset (by
    intro p hpS hpnot
    exact hzero p hpS hpnot)).symm

theorem log_tau_div_from_modifyFactorization
    {N : ℕ} {up down : Finset ℕ}
    (hN : 0 < N)
    (hupPrime : ∀ p ∈ up, p.Prime)
    (hdownPrime : ∀ p ∈ down, p.Prime)
    (hdownPos : ∀ p ∈ down, 0 < N.factorization p) :
    let g := modifyFactorization N.factorization up down
    Real.log ((tau (fromFactorization g) : ℝ) / (tau N : ℝ)) =
      ∑ p ∈ up ∪ down,
        Real.log (((g p + 1 : ℕ) : ℝ) /
          ((N.factorization p + 1 : ℕ) : ℝ)) := by
  let g := modifyFactorization N.factorization up down
  have hfN : ∀ p ∈ N.factorization.support, p.Prime := by
    intro p hp
    rw [Nat.support_factorization] at hp
    exact Nat.prime_of_mem_primeFactors hp
  have hgPrime : ∀ p ∈ g.support, p.Prime :=
    modifyFactorization_prime_support hfN hupPrime hdownPrime
  let M := fromFactorization g
  have hMpos : 0 < M := fromFactorization_pos hgPrime
  have hMfact : M.factorization = g := factorization_fromFactorization hgPrime
  let S := N.primeFactors ∪ M.primeFactors
  have hlogN : Real.log (tau N : ℝ) =
      ∑ p ∈ S, Real.log (N.factorization p + 1 : ℕ) :=
    log_tau_eq_sum_factorization_on hN.ne' S Finset.subset_union_left
  have hlogM : Real.log (tau M : ℝ) =
      ∑ p ∈ S, Real.log (g p + 1 : ℕ) := by
    have h := log_tau_eq_sum_factorization_on hMpos.ne' S Finset.subset_union_right
    rwa [hMfact] at h
  have hchangeSubset : up ∪ down ⊆ S := by
    intro p hp
    have hpPrime : p.Prime := by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hupPrime p hp
      · exact hdownPrime p hp
    by_cases hpN : 0 < N.factorization p
    · exact Finset.mem_union_left _ <|
        (Nat.mem_primeFactors_of_ne_zero hN.ne').2
          ⟨hpPrime, Nat.dvd_of_factorization_pos hpN.ne'⟩
    · have hpu : p ∈ up := by
        rcases Finset.mem_union.mp hp with hpu | hpd
        · exact hpu
        · exact (hpN (hdownPos p hpd)).elim
      have hpg : 0 < g p := by simp [g, modifyFactorization_apply, hpu]
      apply Finset.mem_union_right
      rw [← Nat.support_factorization, hMfact, Finsupp.mem_support_iff]
      exact hpg.ne'
  have hoff : ∀ p ∈ S, p ∉ up ∪ down →
      Real.log (g p + 1 : ℕ) -
        Real.log (N.factorization p + 1 : ℕ) = 0 := by
    intro p hp hpchange
    have hpu : p ∉ up := fun h ↦ hpchange (Finset.mem_union_left _ h)
    have hpd : p ∉ down := fun h ↦ hpchange (Finset.mem_union_right _ h)
    rw [modifyFactorization_eq_of_not_mem hpu hpd]
    ring
  change Real.log ((tau M : ℝ) / (tau N : ℝ)) = _
  rw [Real.log_div (by exact_mod_cast (tau_pos hMpos.ne').ne')
      (by exact_mod_cast (tau_pos hN.ne').ne'),
    hlogM, hlogN, ← Finset.sum_sub_distrib]
  calc
    (∑ p ∈ S, (Real.log (g p + 1 : ℕ) -
        Real.log (N.factorization p + 1 : ℕ))) =
        ∑ p ∈ up ∪ down, (Real.log (g p + 1 : ℕ) -
          Real.log (N.factorization p + 1 : ℕ)) :=
      (Finset.sum_subset hchangeSubset (by
        intro p hpS hpnot
        exact hoff p hpS hpnot)).symm
    _ = ∑ p ∈ up ∪ down,
        Real.log (((g p + 1 : ℕ) : ℝ) /
          ((N.factorization p + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Real.log_div]
      · positivity
      · positivity

theorem exists_modified_integer_summary
    {ε : ℝ} {N : ℕ} {up down : Finset ℕ}
    (hN : 0 < N)
    (hupPrime : ∀ p ∈ up, p.Prime)
    (hdownPrime : ∀ p ∈ down, p.Prime)
    (hdownPos : ∀ p ∈ down, 0 < N.factorization p) :
    ∃ M : ℕ, 0 < M ∧
      M.factorization = modifyFactorization N.factorization up down ∧
      benefit ε N M =
        ∑ p ∈ up ∪ down,
          localBenefit ε p (N.factorization p) (M.factorization p) ∧
      Real.log ((tau M : ℝ) / (tau N : ℝ)) =
        ∑ p ∈ up ∪ down,
          Real.log (((M.factorization p + 1 : ℕ) : ℝ) /
            ((N.factorization p + 1 : ℕ) : ℝ)) := by
  let g := modifyFactorization N.factorization up down
  have hfN : ∀ p ∈ N.factorization.support, p.Prime := by
    intro p hp
    rw [Nat.support_factorization] at hp
    exact Nat.prime_of_mem_primeFactors hp
  have hgPrime : ∀ p ∈ g.support, p.Prime :=
    modifyFactorization_prime_support hfN hupPrime hdownPrime
  let M := fromFactorization g
  have hMpos : 0 < M := fromFactorization_pos hgPrime
  have hMfact : M.factorization = g := factorization_fromFactorization hgPrime
  refine ⟨M, hMpos, hMfact, ?_, ?_⟩
  · rw [hMfact]
    exact benefit_from_modifyFactorization hN hupPrime hdownPrime hdownPos
  · rw [hMfact]
    exact log_tau_div_from_modifyFactorization hN hupPrime hdownPrime hdownPos

noncomputable def blockFinset {m : ℕ} (P : Fin m → ℕ) : Finset ℕ :=
  Finset.univ.image P

theorem mem_blockFinset_iff {m : ℕ} {P : Fin m → ℕ} {p : ℕ} :
    p ∈ blockFinset P ↔ ∃ i, P i = p := by
  simp [blockFinset]

theorem card_blockFinset {m : ℕ} {P : Fin m → ℕ}
    (hP : Function.Injective P) :
    (blockFinset P).card = m := by
  calc
    (blockFinset P).card = (Finset.univ : Finset (Fin m)).card := by
      exact Finset.card_image_of_injective _ hP
    _ = m := Fintype.card_fin m

theorem blockFinset_prime {m : ℕ} {P : Fin m → ℕ}
    (hP : ∀ i, (P i).Prime) :
    ∀ p ∈ blockFinset P, p.Prime := by
  intro p hp
  obtain ⟨i, rfl⟩ := mem_blockFinset_iff.1 hp
  exact hP i

theorem sum_blockFinset_const {m : ℕ} {P : Fin m → ℕ}
    (hP : Function.Injective P) (c : ℝ) :
    ∑ _p ∈ blockFinset P, c = (m : ℝ) * c := by
  rw [Finset.sum_const, nsmul_eq_mul, card_blockFinset hP]

/-- Away from the critical endpoint, every superior integer has the unique
canonical exponent prescribed by the open threshold interval. -/
theorem Superior.factorization_eq_of_threshold_interval
    {ε : ℝ} {N p k : ℕ} (hε : 0 < ε) (hN : Superior ε N)
    (hp : p.Prime) (hk : 0 < k)
    (hlower : thresholdScale ε (k + 1) < p)
    (hupper : (p : ℝ) < thresholdScale ε k) :
    N.factorization p = k := by
  have hcanon : canonicalExponent ε p = k :=
    (canonicalExponent_eq_iff_thresholdScale_interval hε hp hk).2
      ⟨hlower, hupper.le⟩
  rcases hN.factorization_eq_canonical_or_tiedLower hε hp with h | h
  · exact h.trans hcanon
  · have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hxR : 0 < thresholdScale ε k := thresholdScale_pos hk
    have hloglt : Real.log p < Real.log (thresholdScale ε k) :=
      Real.strictMonoOn_log (Set.mem_Ioi.mpr hpR) (Set.mem_Ioi.mpr hxR) hupper
    have hscaled := mul_lt_mul_of_pos_left hloglt hε
    have heps : ε * (1 / ε) = 1 := by field_simp
    rw [log_thresholdScale hε hk] at hscaled
    have hstrict : ε * Real.log p < Real.log (1 + 1 / (k : ℝ)) := by
      calc
        ε * Real.log p < ε * ((1 / ε) * Real.log (1 + 1 / (k : ℝ))) := hscaled
        _ = Real.log (1 + 1 / (k : ℝ)) := by rw [← mul_assoc, heps, one_mul]
    rw [hcanon] at h
    exfalso
    exact (ne_of_lt hstrict) h.2

/-- The primes above the first threshold do not occur in a superior number. -/
theorem Superior.factorization_eq_zero_of_threshold_one_lt
    {ε : ℝ} {N p : ℕ} (hε : 0 < ε) (hN : Superior ε N)
    (hp : p.Prime) (hpAbove : thresholdScale ε 1 < p) :
    N.factorization p = 0 := by
  have hcanon0 : canonicalExponent ε p = 0 := by
    apply Nat.eq_zero_of_not_pos
    rw [canonicalExponent_pos_iff_le_thresholdScale_one hε hp]
    exact not_le_of_gt hpAbove
  rcases hN.factorization_eq_canonical_or_tiedLower hε hp with h | h
  · exact h.trans hcanon0
  ·
    rw [hcanon0] at h
    omega

/-- The primes strictly between the first and second thresholds have
exponent one in every superior number. -/
theorem Superior.factorization_eq_one_of_threshold_interval
    {ε : ℝ} {N p : ℕ} (hε : 0 < ε) (hN : Superior ε N)
    (hp : p.Prime) (hlower : thresholdScale ε 2 < p)
    (hupper : (p : ℝ) < thresholdScale ε 1) :
    N.factorization p = 1 := by
  exact hN.factorization_eq_of_threshold_interval hε hp (by omega)
    (by simpa using hlower) (by simpa using hupper)

/-- The primes strictly between the second and third thresholds have
exponent two in every superior number. -/
theorem Superior.factorization_eq_two_of_threshold_interval
    {ε : ℝ} {N p : ℕ} (hε : 0 < ε) (hN : Superior ε N)
    (hp : p.Prime) (hlower : thresholdScale ε 3 < p)
    (hupper : (p : ℝ) < thresholdScale ε 2) :
    N.factorization p = 2 := by
  exact hN.factorization_eq_of_threshold_interval hε hp (by omega)
    (by simpa using hlower) (by simpa using hupper)

/-- The primes in a signed trial block are raised when the coefficient is
nonnegative and lowered when it is negative. -/
noncomputable def signedBlockUp (z : ℤ) (P : Fin z.natAbs → ℕ) : Finset ℕ :=
  if 0 ≤ z then blockFinset P else ∅

noncomputable def signedBlockDown (z : ℤ) (P : Fin z.natAbs → ℕ) : Finset ℕ :=
  if z < 0 then blockFinset P else ∅

theorem signedBlockUp_union_down (z : ℤ) (P : Fin z.natAbs → ℕ) :
    signedBlockUp z P ∪ signedBlockDown z P = blockFinset P := by
  by_cases hz : 0 ≤ z
  · simp [signedBlockUp, signedBlockDown, hz, not_lt.mpr hz]
  · have hz' : z < 0 := lt_of_not_ge hz
    simp [signedBlockUp, signedBlockDown, hz, hz']

theorem signedBlockUp_disjoint_down (z : ℤ) (P : Fin z.natAbs → ℕ) :
    Disjoint (signedBlockUp z P) (signedBlockDown z P) := by
  by_cases hz : 0 ≤ z
  · simp [signedBlockUp, signedBlockDown, hz, not_lt.mpr hz]
  · have hz' : z < 0 := lt_of_not_ge hz
    simp [signedBlockUp, signedBlockDown, hz, hz']

theorem signedBlock_prime {z : ℤ} {P : Fin z.natAbs → ℕ}
    (hP : ∀ i, (P i).Prime) :
    (∀ p ∈ signedBlockUp z P, p.Prime) ∧
      (∀ p ∈ signedBlockDown z P, p.Prime) := by
  by_cases hz : 0 ≤ z
  · rw [show signedBlockUp z P = blockFinset P by simp [signedBlockUp, hz],
      show signedBlockDown z P = ∅ by simp [signedBlockDown, not_lt.mpr hz]]
    exact ⟨blockFinset_prime hP, by simp⟩
  · have hz' : z < 0 := lt_of_not_ge hz
    rw [show signedBlockUp z P = ∅ by simp [signedBlockUp, hz],
      show signedBlockDown z P = blockFinset P by simp [signedBlockDown, hz']]
    exact ⟨by simp, blockFinset_prime hP⟩

/-- A signed block changes a constant exponent `k-1` to `k` above the
threshold, or `k` to `k-1` below it.  This is the exact contribution to the
logarithm of the divisor ratio. -/
theorem sum_signedBlock_log_tau
    {N k : ℕ} {z : ℤ} {P : Fin z.natAbs → ℕ}
    (hk : 0 < k) (hP : Function.Injective P)
    (hfactUp : 0 ≤ z → ∀ i, N.factorization (P i) = k - 1)
    (hfactDown : z < 0 → ∀ i, N.factorization (P i) = k) :
    let up := signedBlockUp z P
    let down := signedBlockDown z P
    let g := modifyFactorization N.factorization up down
    ∑ p ∈ blockFinset P,
        Real.log (((g p + 1 : ℕ) : ℝ) /
          ((N.factorization p + 1 : ℕ) : ℝ)) =
      (z : ℝ) * Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
  dsimp only
  by_cases hz : 0 ≤ z
  · have hdown : signedBlockDown z P = ∅ := by
      simp [signedBlockDown, not_lt.mpr hz]
    have hup : signedBlockUp z P = blockFinset P := by
      simp [signedBlockUp, hz]
    have hzNat : z = (z.natAbs : ℤ) := by
      exact Int.eq_natAbs_of_nonneg hz
    have hzR : (0 : ℝ) ≤ z := by exact_mod_cast hz
    have hzCast : (z : ℝ) = (z.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hzR]
    rw [hdown, hup]
    calc
      (∑ p ∈ blockFinset P,
          Real.log ((((modifyFactorization N.factorization (blockFinset P) ∅ p) + 1 : ℕ) : ℝ) /
            ((N.factorization p + 1 : ℕ) : ℝ))) =
          ∑ _p ∈ blockFinset P,
            Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
              apply Finset.sum_congr rfl
              intro p hp
              obtain ⟨i, rfl⟩ := mem_blockFinset_iff.1 hp
              rw [modifyFactorization_apply, if_pos hp, hfactUp hz i]
              have hkSub : k - 1 + 1 = k := Nat.sub_add_cancel hk
              rw [hkSub]
      _ = (z.natAbs : ℝ) *
          Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) :=
            sum_blockFinset_const hP _
      _ = (z : ℝ) * Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
            rw [hzCast]
  · have hz' : z < 0 := lt_of_not_ge hz
    have hup : signedBlockUp z P = ∅ := by simp [signedBlockUp, hz]
    have hdown : signedBlockDown z P = blockFinset P := by
      simp [signedBlockDown, hz']
    have hzNat : z = -((z.natAbs : ℕ) : ℤ) := by
      have h := Int.ofNat_natAbs_of_nonpos hz'.le
      omega
    have hzR : (z : ℝ) < 0 := by exact_mod_cast hz'
    have hzCast : (z : ℝ) = -(z.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg hzR]
      ring
    rw [hup, hdown]
    calc
      (∑ p ∈ blockFinset P,
          Real.log ((((modifyFactorization N.factorization ∅ (blockFinset P) p) + 1 : ℕ) : ℝ) /
            ((N.factorization p + 1 : ℕ) : ℝ))) =
          ∑ _p ∈ blockFinset P,
            -Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
              apply Finset.sum_congr rfl
              intro p hp
              obtain ⟨i, rfl⟩ := mem_blockFinset_iff.1 hp
              rw [modifyFactorization_apply, if_neg (by simp), if_pos hp,
                hfactDown hz' i]
              have hkSub : k - 1 + 1 = k := Nat.sub_add_cancel hk
              rw [hkSub]
              have hkR : (0 : ℝ) < k := by exact_mod_cast hk
              have hk1R : (0 : ℝ) < k + 1 := by positivity
              rw [← Real.log_inv, inv_div]
      _ = (z.natAbs : ℝ) *
          (-Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ))) :=
            sum_blockFinset_const hP _
      _ = (z : ℝ) * Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
            rw [hzCast]
            ring

/-- Version of the preceding calculation inside a larger modification.  The
two membership equivalences say that this block is assigned exactly the
direction prescribed by the sign of `z`. -/
theorem sum_signedBlock_log_tau_of_membership
    {N k : ℕ} {z : ℤ} {P : Fin z.natAbs → ℕ} {up down : Finset ℕ}
    (hk : 0 < k) (hP : Function.Injective P)
    (hup : ∀ p ∈ blockFinset P, (p ∈ up ↔ 0 ≤ z))
    (hdown : ∀ p ∈ blockFinset P, (p ∈ down ↔ z < 0))
    (hfactUp : 0 ≤ z → ∀ i, N.factorization (P i) = k - 1)
    (hfactDown : z < 0 → ∀ i, N.factorization (P i) = k) :
    let g := modifyFactorization N.factorization up down
    ∑ p ∈ blockFinset P,
        Real.log (((g p + 1 : ℕ) : ℝ) /
          ((N.factorization p + 1 : ℕ) : ℝ)) =
      (z : ℝ) * Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
  dsimp only
  by_cases hz : 0 ≤ z
  · have hzR : (0 : ℝ) ≤ z := by exact_mod_cast hz
    have hzCast : (z : ℝ) = (z.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hzR]
    calc
      (∑ p ∈ blockFinset P,
          Real.log ((((modifyFactorization N.factorization up down p) + 1 : ℕ) : ℝ) /
            ((N.factorization p + 1 : ℕ) : ℝ))) =
          ∑ _p ∈ blockFinset P,
            Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
              apply Finset.sum_congr rfl
              intro p hp
              obtain ⟨i, rfl⟩ := mem_blockFinset_iff.1 hp
              have hpP : P i ∈ blockFinset P := mem_blockFinset_iff.2 ⟨i, rfl⟩
              rw [modifyFactorization_apply, if_pos ((hup _ hpP).2 hz),
                hfactUp hz i]
              have hkSub : k - 1 + 1 = k := Nat.sub_add_cancel hk
              rw [hkSub]
      _ = (z.natAbs : ℝ) *
          Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) :=
            sum_blockFinset_const hP _
      _ = (z : ℝ) * Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
            rw [hzCast]
  · have hz' : z < 0 := lt_of_not_ge hz
    have hzR : (z : ℝ) < 0 := by exact_mod_cast hz'
    have hzCast : (z : ℝ) = -(z.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg hzR]
      ring
    calc
      (∑ p ∈ blockFinset P,
          Real.log ((((modifyFactorization N.factorization up down p) + 1 : ℕ) : ℝ) /
            ((N.factorization p + 1 : ℕ) : ℝ))) =
          ∑ _p ∈ blockFinset P,
            -Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
              apply Finset.sum_congr rfl
              intro p hp
              obtain ⟨i, rfl⟩ := mem_blockFinset_iff.1 hp
              have hpP : P i ∈ blockFinset P := mem_blockFinset_iff.2 ⟨i, rfl⟩
              rw [modifyFactorization_apply,
                if_neg (fun hmem ↦ hz ((hup _ hpP).1 hmem)),
                if_pos ((hdown _ hpP).2 hz'), hfactDown hz' i]
              have hkSub : k - 1 + 1 = k := Nat.sub_add_cancel hk
              rw [hkSub, ← Real.log_inv, inv_div]
      _ = (z.natAbs : ℝ) *
          (-Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ))) :=
            sum_blockFinset_const hP _
      _ = (z : ℝ) * Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
            rw [hzCast]
            ring

/-- A signed threshold block has total benefit at most its cardinality times
the supplied logarithmic displacement. -/
theorem sum_signedBlock_localBenefit_le
    {ε E : ℝ} {N k : ℕ} {z : ℤ} {P : Fin z.natAbs → ℕ}
    {up down : Finset ℕ}
    (hε : 0 < ε) (hk : 0 < k) (hP : Function.Injective P)
    (hup : ∀ p ∈ blockFinset P, (p ∈ up ↔ 0 ≤ z))
    (hdown : ∀ p ∈ blockFinset P, (p ∈ down ↔ z < 0))
    (hfactUp : 0 ≤ z → ∀ i, N.factorization (P i) = k - 1)
    (hfactDown : z < 0 → ∀ i, N.factorization (P i) = k)
    (herror : ∀ i, |Real.log (P i) - Real.log (thresholdScale ε k)| ≤ E) :
    let g := modifyFactorization N.factorization up down
    ∑ p ∈ blockFinset P,
        localBenefit ε p (N.factorization p) (g p) ≤
      (z.natAbs : ℝ) * (ε * E) := by
  dsimp only
  have hscale : ε * Real.log (thresholdScale ε k) =
      Real.log (1 + 1 / (k : ℝ)) := by
    rw [log_thresholdScale hε hk]
    have heps : ε * (1 / ε) = 1 := by field_simp
    rw [← mul_assoc, heps, one_mul]
  have hpoint : ∀ p ∈ blockFinset P,
      localBenefit ε p (N.factorization p)
          (modifyFactorization N.factorization up down p) ≤ ε * E := by
    intro p hp
    obtain ⟨i, rfl⟩ := mem_blockFinset_iff.1 hp
    have hpP : P i ∈ blockFinset P := mem_blockFinset_iff.2 ⟨i, rfl⟩
    by_cases hz : 0 ≤ z
    · rw [modifyFactorization_apply, if_pos ((hup _ hpP).2 hz),
          hfactUp hz i]
      have hkSub : k - 1 + 1 = k := Nat.sub_add_cancel hk
      have hformula := localBenefit_raise ε (P i) (k - 1)
      rw [hkSub] at hformula
      rw [hkSub, hformula, ← hscale]
      have hgap : Real.log (P i) - Real.log (thresholdScale ε k) ≤ E :=
        (le_abs_self _).trans (herror i)
      nlinarith
    · have hz' : z < 0 := lt_of_not_ge hz
      rw [modifyFactorization_apply,
          if_neg (fun hmem ↦ hz ((hup _ hpP).1 hmem)),
          if_pos ((hdown _ hpP).2 hz'), hfactDown hz' i]
      have hkSub : k - 1 + 1 = k := Nat.sub_add_cancel hk
      have hformula := localBenefit_lower ε (P i) (k - 1)
      rw [hkSub] at hformula
      rw [hformula, ← hscale]
      have hgap : -(Real.log (P i) - Real.log (thresholdScale ε k)) ≤ E :=
        (neg_le_abs _).trans (herror i)
      nlinarith
  calc
    (∑ p ∈ blockFinset P,
        localBenefit ε p (N.factorization p)
          (modifyFactorization N.factorization up down p)) ≤
        ∑ _p ∈ blockFinset P, ε * E := by
          exact Finset.sum_le_sum fun p hp ↦ hpoint p hp
    _ = (z.natAbs : ℝ) * (ε * E) := sum_blockFinset_const hP _

/-- Two disjoint signed threshold blocks produce an actual integer with the
prescribed two-term divisor logarithm and controlled total benefit. -/
theorem exists_two_signedBlock_trial
    {ε EP EQ : ℝ} {N kp kq : ℕ} {z w : ℤ}
    {P : Fin z.natAbs → ℕ} {Q : Fin w.natAbs → ℕ}
    (hε : 0 < ε) (hN : 0 < N) (hkp : 0 < kp) (hkq : 0 < kq)
    (hPinj : Function.Injective P) (hQinj : Function.Injective Q)
    (hPprime : ∀ i, (P i).Prime) (hQprime : ∀ i, (Q i).Prime)
    (hdisj : Disjoint (blockFinset P) (blockFinset Q))
    (hPfactUp : 0 ≤ z → ∀ i, N.factorization (P i) = kp - 1)
    (hPfactDown : z < 0 → ∀ i, N.factorization (P i) = kp)
    (hQfactUp : 0 ≤ w → ∀ i, N.factorization (Q i) = kq - 1)
    (hQfactDown : w < 0 → ∀ i, N.factorization (Q i) = kq)
    (hPerror : ∀ i,
      |Real.log (P i) - Real.log (thresholdScale ε kp)| ≤ EP)
    (hQerror : ∀ i,
      |Real.log (Q i) - Real.log (thresholdScale ε kq)| ≤ EQ) :
    ∃ M : ℕ, 0 < M ∧
      benefit ε N M ≤
        (z.natAbs : ℝ) * (ε * EP) + (w.natAbs : ℝ) * (ε * EQ) ∧
      Real.log ((tau M : ℝ) / (tau N : ℝ)) =
        (z : ℝ) * Real.log (((kp + 1 : ℕ) : ℝ) / (kp : ℝ)) +
          (w : ℝ) * Real.log (((kq + 1 : ℕ) : ℝ) / (kq : ℝ)) := by
  let upP := signedBlockUp z P
  let downP := signedBlockDown z P
  let upQ := signedBlockUp w Q
  let downQ := signedBlockDown w Q
  let up := upP ∪ upQ
  let down := downP ∪ downQ
  have hPnotQ : ∀ p ∈ blockFinset P, p ∉ blockFinset Q := by
    intro p hp
    exact Finset.disjoint_left.1 hdisj hp
  have hQnotP : ∀ p ∈ blockFinset Q, p ∉ blockFinset P := by
    intro p hp
    exact Finset.disjoint_left.1 hdisj.symm hp
  have hupPmem : ∀ p ∈ blockFinset P, (p ∈ up ↔ 0 ≤ z) := by
    intro p hp
    have hpQ := hPnotQ p hp
    dsimp [up, upP, upQ]
    by_cases hz : 0 ≤ z <;> by_cases hw : 0 ≤ w <;>
      simp [signedBlockUp, hz, hw, hp, hpQ]
  have hdownPmem : ∀ p ∈ blockFinset P, (p ∈ down ↔ z < 0) := by
    intro p hp
    have hpQ := hPnotQ p hp
    dsimp [down, downP, downQ]
    by_cases hz : z < 0 <;> by_cases hw : w < 0 <;>
      simp [signedBlockDown, hz, hw, hp, hpQ]
  have hupQmem : ∀ p ∈ blockFinset Q, (p ∈ up ↔ 0 ≤ w) := by
    intro p hp
    have hpP := hQnotP p hp
    dsimp [up, upP, upQ]
    by_cases hz : 0 ≤ z <;> by_cases hw : 0 ≤ w <;>
      simp [signedBlockUp, hz, hw, hp, hpP]
  have hdownQmem : ∀ p ∈ blockFinset Q, (p ∈ down ↔ w < 0) := by
    intro p hp
    have hpP := hQnotP p hp
    dsimp [down, downP, downQ]
    by_cases hz : z < 0 <;> by_cases hw : w < 0 <;>
      simp [signedBlockDown, hz, hw, hp, hpP]
  have hupPrime : ∀ p ∈ up, p.Prime := by
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · exact (signedBlock_prime hPprime).1 p hp
    · exact (signedBlock_prime hQprime).1 p hp
  have hdownPrime : ∀ p ∈ down, p.Prime := by
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · exact (signedBlock_prime hPprime).2 p hp
    · exact (signedBlock_prime hQprime).2 p hp
  have hdownPos : ∀ p ∈ down, 0 < N.factorization p := by
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · have hz : z < 0 := by
        dsimp [downP] at hp
        by_cases hz : z < 0
        · exact hz
        · simp [signedBlockDown, hz] at hp
      have hpBlock : p ∈ blockFinset P := by
        simpa [downP, signedBlockDown, hz] using hp
      obtain ⟨i, rfl⟩ := mem_blockFinset_iff.1 hpBlock
      rw [hPfactDown hz i]
      exact hkp
    · have hw : w < 0 := by
        dsimp [downQ] at hp
        by_cases hw : w < 0
        · exact hw
        · simp [signedBlockDown, hw] at hp
      have hpBlock : p ∈ blockFinset Q := by
        simpa [downQ, signedBlockDown, hw] using hp
      obtain ⟨i, rfl⟩ := mem_blockFinset_iff.1 hpBlock
      rw [hQfactDown hw i]
      exact hkq
  have hsupport : up ∪ down = blockFinset P ∪ blockFinset Q := by
    dsimp [up, down, upP, downP, upQ, downQ]
    ext p
    by_cases hz : 0 ≤ z <;> by_cases hw : 0 ≤ w
    · have hnz : ¬z < 0 := not_lt.mpr hz
      have hnw : ¬w < 0 := not_lt.mpr hw
      simp [signedBlockUp, signedBlockDown, hz, hw, hnz, hnw, or_comm]
    · have hw' : w < 0 := lt_of_not_ge hw
      have hnz : ¬z < 0 := not_lt.mpr hz
      simp [signedBlockUp, signedBlockDown, hz, hw, hw', hnz, or_comm]
    · have hz' : z < 0 := lt_of_not_ge hz
      have hnw : ¬w < 0 := not_lt.mpr hw
      simp [signedBlockUp, signedBlockDown, hz, hz', hw, hnw, or_comm]
    · have hz' : z < 0 := lt_of_not_ge hz
      have hw' : w < 0 := lt_of_not_ge hw
      simp [signedBlockUp, signedBlockDown, hz, hz', hw, hw', or_comm]
  obtain ⟨M, hM, hMfact, hbenefit, htau⟩ :=
    exists_modified_integer_summary (ε := ε) hN hupPrime hdownPrime hdownPos
  refine ⟨M, hM, ?_, ?_⟩
  · rw [hsupport] at hbenefit
    rw [Finset.sum_union hdisj] at hbenefit
    have hPbound := sum_signedBlock_localBenefit_le hε hkp hPinj
      hupPmem hdownPmem hPfactUp hPfactDown hPerror
    have hQbound := sum_signedBlock_localBenefit_le hε hkq hQinj
      hupQmem hdownQmem hQfactUp hQfactDown hQerror
    rw [← hMfact] at hPbound hQbound
    linarith
  · rw [hsupport] at htau
    rw [Finset.sum_union hdisj] at htau
    have hPsum := sum_signedBlock_log_tau_of_membership hkp hPinj
      hupPmem hdownPmem hPfactUp hPfactDown
    have hQsum := sum_signedBlock_log_tau_of_membership hkq hQinj
      hupQmem hdownQmem hQfactUp hQfactDown
    rw [← hMfact] at hPsum hQsum
    linarith

theorem lt_of_log_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : Real.log a < Real.log b) : a < b := by
  rw [← Real.exp_log ha, ← Real.exp_log hb]
  exact Real.exp_lt_exp.mpr h

/-- Prime blocks near the second and first Nicolas thresholds realize the
two-dimensional trial family.  The three displayed gap hypotheses keep the
blocks inside the strict canonical-exponent bands and separate them from one
another. -/
theorem exists_nicolas_trial_of_blocks
    {ε E₂ E₁ : ℝ} {N : ℕ} {h j : ℤ}
    {P : Fin h.natAbs → ℕ} {Q : Fin (-j).natAbs → ℕ}
    (hε : 0 < ε) (hN : Superior ε N)
    (hPinj : Function.Injective P) (hQinj : Function.Injective Q)
    (hPprime : ∀ i, (P i).Prime) (hQprime : ∀ i, (Q i).Prime)
    (hPabove : 0 ≤ h → ∀ i, thresholdScale ε 2 < P i)
    (hPbelow : h < 0 → ∀ i, (P i : ℝ) < thresholdScale ε 2)
    (hQabove : 0 ≤ -j → ∀ i, thresholdScale ε 1 < Q i)
    (hQbelow : -j < 0 → ∀ i, (Q i : ℝ) < thresholdScale ε 1)
    (hPerror : ∀ i,
      |Real.log (P i) - Real.log (thresholdScale ε 2)| ≤ E₂)
    (hQerror : ∀ i,
      |Real.log (Q i) - Real.log (thresholdScale ε 1)| ≤ E₁)
    (hgap12P : E₂ <
      Real.log (thresholdScale ε 1) - Real.log (thresholdScale ε 2))
    (hgap12Q : E₁ <
      Real.log (thresholdScale ε 1) - Real.log (thresholdScale ε 2))
    (hgap23 : E₂ <
      Real.log (thresholdScale ε 2) - Real.log (thresholdScale ε 3))
    (hseparate : E₂ + E₁ <
      Real.log (thresholdScale ε 1) - Real.log (thresholdScale ε 2)) :
    ∃ M : ℕ, 0 < M ∧
      benefit ε N M ≤
        (h.natAbs : ℝ) * (ε * E₂) + ((-j).natAbs : ℝ) * (ε * E₁) ∧
      Real.log ((tau M : ℝ) / (tau N : ℝ)) =
        ((h : ℝ) * nicolasTheta - (j : ℝ)) * Real.log 2 := by
  have hx1 : 0 < thresholdScale ε 1 := thresholdScale_pos (by omega)
  have hx2 : 0 < thresholdScale ε 2 := thresholdScale_pos (by omega)
  have hx3 : 0 < thresholdScale ε 3 := thresholdScale_pos (by omega)
  have hPupper : ∀ i, (P i : ℝ) < thresholdScale ε 1 := by
    intro i
    have hlog := (abs_le.1 (hPerror i)).2
    have hp : (0 : ℝ) < P i := by exact_mod_cast (hPprime i).pos
    apply lt_of_log_lt hp hx1
    linarith
  have hPlower : ∀ i, thresholdScale ε 3 < P i := by
    intro i
    have hlog := (abs_le.1 (hPerror i)).1
    have hp : (0 : ℝ) < P i := by exact_mod_cast (hPprime i).pos
    apply lt_of_log_lt hx3 hp
    linarith
  have hQlower : ∀ i, thresholdScale ε 2 < Q i := by
    intro i
    have hlog := (abs_le.1 (hQerror i)).1
    have hp : (0 : ℝ) < Q i := by exact_mod_cast (hQprime i).pos
    apply lt_of_log_lt hx2 hp
    linarith
  have hPfactUp : 0 ≤ h → ∀ i, N.factorization (P i) = 1 := by
    intro hh i
    exact hN.factorization_eq_one_of_threshold_interval hε (hPprime i)
      (hPabove hh i) (hPupper i)
  have hPfactDown : h < 0 → ∀ i, N.factorization (P i) = 2 := by
    intro hh i
    exact hN.factorization_eq_two_of_threshold_interval hε (hPprime i)
      (hPlower i) (hPbelow hh i)
  have hQfactUp : 0 ≤ -j → ∀ i, N.factorization (Q i) = 0 := by
    intro hj i
    exact hN.factorization_eq_zero_of_threshold_one_lt hε (hQprime i)
      (hQabove hj i)
  have hQfactDown : -j < 0 → ∀ i, N.factorization (Q i) = 1 := by
    intro hj i
    exact hN.factorization_eq_one_of_threshold_interval hε (hQprime i)
      (hQlower i) (hQbelow hj i)
  have hdisj : Disjoint (blockFinset P) (blockFinset Q) := by
    rw [Finset.disjoint_left]
    intro p hpP hpQ
    obtain ⟨i, rfl⟩ := mem_blockFinset_iff.1 hpP
    obtain ⟨q, hq⟩ := mem_blockFinset_iff.1 hpQ
    have hPlog := (abs_le.1 (hPerror i)).2
    have hQlog := (abs_le.1 (hQerror q)).1
    have hlt : Real.log (P i) < Real.log (Q q) := by linarith
    rw [hq] at hlt
    exact (lt_irrefl _ hlt)
  obtain ⟨M, hM, hbenefit, htau⟩ := exists_two_signedBlock_trial
    hε hN.1 (by omega : 0 < (2 : ℕ)) (by omega : 0 < (1 : ℕ))
    hPinj hQinj hPprime hQprime hdisj hPfactUp hPfactDown
    hQfactUp hQfactDown hPerror hQerror
  refine ⟨M, hM, hbenefit, ?_⟩
  rw [htau]
  norm_num only [Nat.cast_ofNat]
  have hlog32 : Real.log ((3 : ℝ) / 2) = nicolasTheta * Real.log 2 := by
    rw [nicolasTheta]
    field_simp
  rw [hlog32, Int.cast_neg]
  ring

theorem tau_mul_prime_of_factorization_eq_zero
    {N P : ℕ} (hN : 0 < N) (hP : P.Prime)
    (hzero : N.factorization P = 0) :
    tau (N * P) = 2 * tau N := by
  have hnot : ¬P ∣ N := by
    intro hdvd
    have hpos := hP.factorization_pos_of_dvd hN.ne' hdvd
    rw [hzero] at hpos
    omega
  have hcop : N.Coprime P := (hP.coprime_iff_not_dvd.2 hnot).symm
  rw [tau, hcop.card_divisors_mul, hP.divisors]
  simp [tau, mul_comm, hP.ne_one.symm, hN.ne']

theorem tau_mul_prime_le_two_mul {N P : ℕ}
    (hN : 0 < N) (hP : P.Prime) :
    tau (N * P) ≤ 2 * tau N := by
  let up : Finset ℕ := {P}
  let down : Finset ℕ := ∅
  let g := modifyFactorization N.factorization up down
  have hupPrime : ∀ p ∈ up, p.Prime := by
    intro p hp
    have hpP : p = P := by simpa [up] using hp
    simpa [hpP] using hP
  have hdownPrime : ∀ p ∈ down, p.Prime := by simp [down]
  have hdownPos : ∀ p ∈ down, 0 < N.factorization p := by simp [down]
  have hg : g = N.factorization + Finsupp.single P 1 := by
    ext q
    by_cases hq : q = P
    · subst q
      simp [g, up, down, modifyFactorization_apply]
    · simp [g, up, down, modifyFactorization_apply, hq]
  have hfN : ∀ p ∈ N.factorization.support, p.Prime := by
    intro p hp
    rw [Nat.support_factorization] at hp
    exact Nat.prime_of_mem_primeFactors hp
  have hgPrime : ∀ p ∈ g.support, p.Prime :=
    modifyFactorization_prime_support hfN hupPrime hdownPrime
  have hfrom : fromFactorization g = N * P := by
    rw [hg, fromFactorization_add, fromFactorization_factorization hN.ne',
      fromFactorization_single, pow_one]
  have hlog := log_tau_div_from_modifyFactorization
    (N := N) (up := up) (down := down) hN hupPrime hdownPrime hdownPos
  change Real.log ((tau (fromFactorization g) : ℝ) / (tau N : ℝ)) = _ at hlog
  have hsum : (∑ p ∈ up ∪ down,
      Real.log ((((g p + 1 : ℕ) : ℕ) : ℝ) /
        ((N.factorization p + 1 : ℕ) : ℝ))) =
      Real.log (((N.factorization P + 2 : ℕ) : ℝ) /
        ((N.factorization P + 1 : ℕ) : ℝ)) := by
    simp [up, down, g, modifyFactorization_apply]
    push_cast
    ring_nf
  rw [hsum, hfrom] at hlog
  have hratioPos : 0 < ((N.factorization P + 2 : ℕ) : ℝ) /
      ((N.factorization P + 1 : ℕ) : ℝ) := by positivity
  have hratioLe : (((N.factorization P + 2 : ℕ) : ℝ) /
      ((N.factorization P + 1 : ℕ) : ℝ)) ≤ 2 := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < N.factorization P + 1)]
    have hnonneg : (0 : ℝ) ≤ N.factorization P := by positivity
    linarith
  have hlogLe : Real.log ((tau (N * P) : ℝ) / (tau N : ℝ)) ≤
      Real.log 2 := by
    rw [hlog]
    exact Real.log_le_log hratioPos hratioLe
  have htauNP : (0 : ℝ) < tau (N * P) := by
    exact_mod_cast tau_pos (Nat.mul_pos hN hP.pos).ne'
  have htauN : (0 : ℝ) < tau N := by exact_mod_cast tau_pos hN.ne'
  have hratioTau : (tau (N * P) : ℝ) / (tau N : ℝ) ≤ 2 := by
    by_contra hnot
    have hlt : (2 : ℝ) < (tau (N * P) : ℝ) / (tau N : ℝ) :=
      lt_of_not_ge hnot
    have hstrict := Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
      (Set.mem_Ioi.mpr (div_pos htauNP htauN)) hlt
    exact (not_lt_of_ge hlogLe) hstrict
  rw [div_le_iff₀ htauN] at hratioTau
  exact_mod_cast hratioTau

theorem tau_le_of_log_tau_div_le {M A N : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hN : 0 < N)
    (hlog : Real.log ((tau M : ℝ) / (tau N : ℝ)) ≤
      Real.log ((tau A : ℝ) / (tau N : ℝ))) :
    tau M ≤ tau A := by
  by_contra hnot
  have htau : tau A < tau M := Nat.lt_of_not_ge hnot
  have hden : (0 : ℝ) < tau N := by exact_mod_cast tau_pos hN.ne'
  have hnumA : (0 : ℝ) < tau A := by exact_mod_cast tau_pos hA.ne'
  have hnumM : (0 : ℝ) < tau M := by exact_mod_cast tau_pos hM.ne'
  have hratio : (tau A : ℝ) / (tau N : ℝ) <
      (tau M : ℝ) / (tau N : ℝ) := by
    exact div_lt_div_of_pos_right (by exact_mod_cast htau) hden
  have hstrict := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (div_pos hnumA hden))
    (Set.mem_Ioi.mpr (div_pos hnumM hden)) hratio
  exact (not_lt_of_ge hlog) hstrict

theorem tau_eq_two_mul_of_log_tau_div_eq_log_two {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N)
    (hlog : Real.log ((tau M : ℝ) / (tau N : ℝ)) = Real.log 2) :
    tau M = 2 * tau N := by
  have hratioPos : 0 < (tau M : ℝ) / (tau N : ℝ) :=
    div_pos (by exact_mod_cast tau_pos hM.ne')
      (by exact_mod_cast tau_pos hN.ne')
  have hratio : (tau M : ℝ) / (tau N : ℝ) = 2 :=
    Real.strictMonoOn_log.injOn (Set.mem_Ioi.mpr hratioPos)
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2)) hlog
  have htauN0 : (tau N : ℝ) ≠ 0 := by exact_mod_cast (tau_pos hN.ne').ne'
  rw [div_eq_iff htauN0] at hratio
  exact_mod_cast hratio

/-- Abstract bracketing step in Nicolas's argument.  A `d`-net of trial
divisor coordinates, together with the endpoint coordinate one, brackets
the divisor count of every record in the superior interval. -/
theorem benefit_le_of_trial_net
    {ε U d : ℝ} {N A E : ℕ}
    (hε : 0 < ε) (hN : Superior ε N) (hA : HighlyComposite A)
    (hNA : N ≤ A) (hE : 0 < E)
    (htauAE : tau A ≤ tau E)
    (hendpointBenefit : benefit ε N E ≤ U)
    (hendpointLog : Real.log ((tau E : ℝ) / (tau N : ℝ)) = Real.log 2)
    (hd0 : 0 ≤ d)
    (htrial : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ M : ℕ, ∃ r : ℝ, 0 < M ∧ benefit ε N M ≤ U ∧
        Real.log ((tau M : ℝ) / (tau N : ℝ)) = r * Real.log 2 ∧
        |r - t| ≤ d) :
    benefit ε N A ≤ U + 6 * d * Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htauNA : tau N ≤ tau A := by
    rcases eq_or_lt_of_le hNA with rfl | hlt
    · exact le_rfl
    · exact (hA.2 N hN.1 hlt).le
  let s : ℝ := Real.log ((tau A : ℝ) / (tau N : ℝ)) / Real.log 2
  have hratioN : 1 ≤ (tau A : ℝ) / (tau N : ℝ) := by
    rw [one_le_div₀ (by exact_mod_cast tau_pos hN.1.ne' : (0 : ℝ) < tau N)]
    exact_mod_cast htauNA
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact div_nonneg (Real.log_nonneg hratioN) hlog2.le
  have hlogAE : Real.log ((tau A : ℝ) / (tau N : ℝ)) ≤
      Real.log ((tau E : ℝ) / (tau N : ℝ)) := by
    apply Real.log_le_log
    · exact div_pos (by exact_mod_cast tau_pos hA.1.ne')
        (by exact_mod_cast tau_pos hN.1.ne')
    · exact div_le_div_of_nonneg_right (by exact_mod_cast htauAE)
        (by exact_mod_cast (tau_pos hN.1.ne').le)
  have hs1 : s ≤ 1 := by
    dsimp [s]
    rw [hendpointLog] at hlogAE
    exact (div_le_one hlog2).2 hlogAE
  obtain ⟨M, r, hM, hMbenefit, hMlog, hrUpper, hrLower⟩ :
      ∃ M : ℕ, ∃ r : ℝ, 0 < M ∧ benefit ε N M ≤ U ∧
        Real.log ((tau M : ℝ) / (tau N : ℝ)) = r * Real.log 2 ∧
        r ≤ s ∧ s - r ≤ 3 * d := by
    by_cases hsLow : s ≤ 2 * d
    · refine ⟨N, 0, hN.1, ?_, ?_, hs0, ?_⟩
      · have hzero : benefit ε N N = 0 := by simp [benefit]
        rw [hzero]
        have htrialZero := htrial 0 (by norm_num) (by norm_num)
        obtain ⟨M0, r0, hM0, hB0, hlog0, herr0⟩ := htrialZero
        have hnonneg := superior_benefit_nonneg hN hM0
        linarith
      · simp [tau_pos hN.1.ne']
      · linarith
    · have ht0 : 0 ≤ s - 2 * d := by linarith
      have ht1 : s - 2 * d ≤ 1 := by linarith
      obtain ⟨M, r, hM, hB, hlog, herr⟩ := htrial (s - 2 * d) ht0 ht1
      have herr' := abs_le.1 herr
      refine ⟨M, r, hM, hB, hlog, ?_, ?_⟩ <;> linarith
  obtain ⟨M', r', hM', hM'benefit, hM'log, hr'Lower, hr'Upper⟩ :
      ∃ M' : ℕ, ∃ r' : ℝ, 0 < M' ∧ benefit ε N M' ≤ U ∧
        Real.log ((tau M' : ℝ) / (tau N : ℝ)) = r' * Real.log 2 ∧
        s ≤ r' ∧ r' - s ≤ 3 * d := by
    by_cases hsHigh : 1 - s ≤ 2 * d
    · refine ⟨E, 1, hE, hendpointBenefit, ?_, hs1, ?_⟩
      · simpa using hendpointLog
      · linarith
    · have ht0 : 0 ≤ s + 2 * d := by linarith
      have ht1 : s + 2 * d ≤ 1 := by linarith
      obtain ⟨M', r', hM', hB', hlog', herr'⟩ := htrial (s + 2 * d) ht0 ht1
      have herr'' := abs_le.1 herr'
      refine ⟨M', r', hM', hB', hlog', ?_, ?_⟩ <;> linarith
  have hlogA : Real.log ((tau A : ℝ) / (tau N : ℝ)) =
      s * Real.log 2 := by
    dsimp [s]
    field_simp
  have htauMA : tau M ≤ tau A := by
    apply tau_le_of_log_tau_div_le hM hA.1 hN.1
    rw [hMlog, hlogA]
    exact mul_le_mul_of_nonneg_right hrUpper hlog2.le
  have htauAM' : tau A ≤ tau M' := by
    apply tau_le_of_log_tau_div_le hA.1 hM' hN.1
    rw [hM'log, hlogA]
    exact mul_le_mul_of_nonneg_right hr'Lower hlog2.le
  have hcompare := benefit_comparison hε.le hN.1 hA hM hM' htauMA htauAM'
  have hlogGap : Real.log ((tau M' : ℝ) / (tau M : ℝ)) =
      (r' - r) * Real.log 2 := by
    have htauM : (0 : ℝ) < tau M := by exact_mod_cast tau_pos hM.ne'
    have htauM' : (0 : ℝ) < tau M' := by exact_mod_cast tau_pos hM'.ne'
    have htauN : (0 : ℝ) < tau N := by exact_mod_cast tau_pos hN.1.ne'
    have hquot : (tau M' : ℝ) / (tau M : ℝ) =
        ((tau M' : ℝ) / (tau N : ℝ)) /
          ((tau M : ℝ) / (tau N : ℝ)) := by field_simp
    rw [hquot, Real.log_div (div_ne_zero htauM'.ne' htauN.ne')
      (div_ne_zero htauM.ne' htauN.ne'), hM'log, hMlog]
    ring
  rw [hlogGap] at hcompare
  have hrgap : r' - r ≤ 6 * d := by linarith
  calc
    benefit ε N A ≤ benefit ε N M' + (r' - r) * Real.log 2 := hcompare
    _ ≤ U + 6 * d * Real.log 2 := by
      gcongr

/-- Uniform prime-window data up to size `H` supplies every signed Nicolas
trial whose two coefficients have absolute value at most `H`. -/
theorem exists_nicolas_trial_of_capacity
    {ε : ℝ} {N L N₀ H a₂ a₁ : ℕ} {h j : ℤ}
    (hε : 0 < ε) (hN : Superior ε N) (hL : 0 < L)
    (hwindow : ∀ n : ℕ, N₀ ≤ n →
      ∃ p : ℕ, p.Prime ∧ n ^ L < p ∧ p ≤ (n + 1) ^ L)
    (hroot₂Low : ((a₂ : ℝ) ^ L) ≤ thresholdScale ε 2)
    (hroot₂High : thresholdScale ε 2 < (((a₂ + 1 : ℕ) : ℝ) ^ L))
    (hroot₁Low : ((a₁ : ℝ) ^ L) ≤ thresholdScale ε 1)
    (hroot₁High : thresholdScale ε 1 < (((a₁ + 1 : ℕ) : ℝ) ^ L))
    (ha₂a₁ : a₂ ≤ a₁)
    (hcapStart : N₀ + H + 1 ≤ a₂) (hcapWidth : 2 * H + 4 ≤ a₂)
    (hh : h.natAbs ≤ H) (hj : (-j).natAbs ≤ H)
    (hgap12P : (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₂ : ℝ) <
      Real.log (thresholdScale ε 1) - Real.log (thresholdScale ε 2))
    (hgap12Q : (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₁ : ℝ) <
      Real.log (thresholdScale ε 1) - Real.log (thresholdScale ε 2))
    (hgap23 : (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₂ : ℝ) <
      Real.log (thresholdScale ε 2) - Real.log (thresholdScale ε 3))
    (hseparate :
      (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₂ : ℝ) +
        (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₁ : ℝ) <
      Real.log (thresholdScale ε 1) - Real.log (thresholdScale ε 2)) :
    ∃ M : ℕ, 0 < M ∧
      benefit ε N M ≤ (H : ℝ) * ε *
        ((2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₂ : ℝ) +
          (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₁ : ℝ)) ∧
      Real.log ((tau M : ℝ) / (tau N : ℝ)) =
        ((h : ℝ) * nicolasTheta - (j : ℝ)) * Real.log 2 := by
  have ha₂Start : N₀ + h.natAbs + 1 ≤ a₂ := by omega
  have ha₂Width : 2 * h.natAbs + 4 ≤ a₂ := by omega
  obtain ⟨upP, downP, hupPinj, hdownPinj, hupP, hdownP⟩ :=
    prime_blocks_log_error hL hwindow hroot₂Low hroot₂High
      ha₂Start ha₂Width
  let P : Fin h.natAbs → ℕ :=
    if 0 ≤ h then upP else downP
  have hPinj : Function.Injective P := by
    by_cases hs : 0 ≤ h
    · simpa [P, hs] using hupPinj
    · simpa [P, hs] using hdownPinj
  have hPprime : ∀ i, (P i).Prime := by
    intro i
    by_cases hs : 0 ≤ h
    · simpa [P, hs] using (hupP i).1
    · simpa [P, hs] using (hdownP i).1
  have hPabove : 0 ≤ h → ∀ i, thresholdScale ε 2 < P i := by
    intro hs i
    simpa [P, hs] using (hupP i).2.1
  have hPbelow : h < 0 → ∀ i, (P i : ℝ) < thresholdScale ε 2 := by
    intro hs i
    have hn : ¬0 ≤ h := not_le_of_gt hs
    simpa [P, hn] using (hdownP i).2.1
  have ha₂pos : 0 < a₂ := by omega
  have hPerror : ∀ i,
      |Real.log (P i) - Real.log (thresholdScale ε 2)| ≤
        (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₂ : ℝ) := by
    intro i
    have hsmall :
        (2 * L : ℕ) * ((h.natAbs + 2 : ℕ) : ℝ) / (a₂ : ℝ) ≤
          (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₂ : ℝ) := by
      gcongr
    by_cases hs : 0 ≤ h
    · have hi := (hupP i).2.2
      simpa [P, hs] using hi.trans hsmall
    · have hi := (hdownP i).2.2
      simpa [P, hs] using hi.trans hsmall
  have ha₁Start : N₀ + (-j).natAbs + 1 ≤ a₁ := by omega
  have ha₁Width : 2 * (-j).natAbs + 4 ≤ a₁ := by omega
  obtain ⟨upQ, downQ, hupQinj, hdownQinj, hupQ, hdownQ⟩ :=
    prime_blocks_log_error hL hwindow hroot₁Low hroot₁High
      ha₁Start ha₁Width
  let Q : Fin (-j).natAbs → ℕ :=
    if 0 ≤ -j then upQ else downQ
  have hQinj : Function.Injective Q := by
    by_cases hs : 0 ≤ -j
    · rw [show Q = upQ by dsimp [Q]; rw [if_pos hs]]
      exact hupQinj
    · rw [show Q = downQ by dsimp [Q]; rw [if_neg hs]]
      exact hdownQinj
  have hQprime : ∀ i, (Q i).Prime := by
    intro i
    by_cases hs : 0 ≤ -j
    · rw [show Q = upQ by dsimp [Q]; rw [if_pos hs]]
      exact (hupQ i).1
    · rw [show Q = downQ by dsimp [Q]; rw [if_neg hs]]
      exact (hdownQ i).1
  have hQabove : 0 ≤ -j → ∀ i, thresholdScale ε 1 < Q i := by
    intro hs i
    rw [show Q = upQ by dsimp [Q]; rw [if_pos hs]]
    exact (hupQ i).2.1
  have hQbelow : -j < 0 → ∀ i, (Q i : ℝ) < thresholdScale ε 1 := by
    intro hs i
    have hn : ¬0 ≤ -j := not_le_of_gt hs
    rw [show Q = downQ by dsimp [Q]; rw [if_neg hn]]
    exact (hdownQ i).2.1
  have ha₁pos : 0 < a₁ := ha₂pos.trans_le ha₂a₁
  have hQerror : ∀ i,
      |Real.log (Q i) - Real.log (thresholdScale ε 1)| ≤
        (2 * L : ℕ) * (((-j).natAbs + 2 : ℕ) : ℝ) / (a₁ : ℝ) := by
    intro i
    by_cases hs : 0 ≤ -j
    · rw [show Q = upQ by dsimp [Q]; rw [if_pos hs]]
      exact (hupQ i).2.2
    · rw [show Q = downQ by dsimp [Q]; rw [if_neg hs]]
      exact (hdownQ i).2.2
  have hQerror' : ∀ i,
      |Real.log (Q i) - Real.log (thresholdScale ε 1)| ≤
        (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₁ : ℝ) := by
    intro i
    apply (hQerror i).trans
    gcongr
  obtain ⟨M, hM, hbenefit, htau⟩ := exists_nicolas_trial_of_blocks
    hε hN hPinj hQinj hPprime hQprime hPabove hPbelow hQabove hQbelow
    hPerror hQerror' hgap12P hgap12Q hgap23 hseparate
  refine ⟨M, hM, ?_, htau⟩
  calc
    benefit ε N M ≤
        (h.natAbs : ℝ) *
            (ε * ((2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₂ : ℝ))) +
          ((-j).natAbs : ℝ) *
            (ε * ((2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₁ : ℝ))) := hbenefit
    _ ≤ (H : ℝ) * ε *
        ((2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₂ : ℝ) +
          (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₁ : ℝ)) := by
      have hE₂ : 0 ≤ (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₂ : ℝ) := by positivity
      have hE₁ : 0 ≤ (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₁ : ℝ) := by positivity
      have hhR : (h.natAbs : ℝ) ≤ H := by exact_mod_cast hh
      have hjR : ((-j).natAbs : ℝ) ≤ H := by exact_mod_cast hj
      calc
        (h.natAbs : ℝ) * (ε *
              ((2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₂ : ℝ))) +
            ((-j).natAbs : ℝ) * (ε *
              ((2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₁ : ℝ))) ≤
            (H : ℝ) * (ε *
              ((2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₂ : ℝ))) +
            (H : ℝ) * (ε *
              ((2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₁ : ℝ))) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_right hhR (mul_nonneg hε.le hE₂))
                  (mul_le_mul_of_nonneg_right hjR (mul_nonneg hε.le hE₁))
        _ = (H : ℝ) * ε *
            ((2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₂ : ℝ) +
              (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a₁ : ℝ)) := by ring

noncomputable def nicolasThetaThree : ℝ :=
  Real.log (4 / 3) / Real.log 2

theorem nicolasThetaThree_pos : 0 < nicolasThetaThree := by
  rw [nicolasThetaThree]
  positivity

theorem nicolasThetaThree_lt_theta : nicolasThetaThree < nicolasTheta := by
  rw [nicolasThetaThree, nicolasTheta]
  apply div_lt_div_of_pos_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  apply Real.strictMonoOn_log
  · norm_num
  · norm_num
  · norm_num

noncomputable def nicolasAlpha (L : ℕ) : ℝ := nicolasTheta / (L : ℝ)

noncomputable def nicolasDelta (L K : ℕ) : ℝ :=
  nicolasAlpha L / (8 * (K + 1 : ℕ))

noncomputable def nicolasBeta (L : ℕ) : ℝ := nicolasAlpha L / 8

noncomputable def nicolasGamma (L K : ℕ) : ℝ := nicolasDelta L K / 2

noncomputable def nicolasRotationScale (L K : ℕ) (x : ℝ) : ℕ :=
  ⌈x ^ nicolasDelta L K⌉₊

noncomputable def nicolasBlockBound (L K : ℕ) (c x : ℝ) : ℕ :=
  ⌈(nicolasRotationScale L K x : ℝ) ^ (K + 1) / c⌉₊ + 2

noncomputable def nicolasRootTwo (L : ℕ) (x : ℝ) : ℕ :=
  ⌊(x ^ nicolasTheta) ^ (1 / (L : ℝ))⌋₊

noncomputable def nicolasRootOne (L : ℕ) (x : ℝ) : ℕ :=
  ⌊x ^ (1 / (L : ℝ))⌋₊

noncomputable def nicolasBlockError (L H a : ℕ) : ℝ :=
  (2 * L : ℕ) * ((H + 2 : ℕ) : ℝ) / (a : ℝ)

theorem nicolasAlpha_pos {L : ℕ} (hL : 0 < L) : 0 < nicolasAlpha L := by
  rw [nicolasAlpha]
  exact div_pos nicolasTheta_pos (by exact_mod_cast hL)

theorem nicolasDelta_pos {L K : ℕ} (hL : 0 < L) :
    0 < nicolasDelta L K := by
  rw [nicolasDelta]
  exact div_pos (nicolasAlpha_pos hL) (by positivity)

theorem nicolasGamma_pos {L K : ℕ} (hL : 0 < L) :
    0 < nicolasGamma L K := by
  rw [nicolasGamma]
  exact half_pos (nicolasDelta_pos hL)

theorem nicolasDelta_mul_succ {L K : ℕ} :
    nicolasDelta L K * (K + 1 : ℕ) = nicolasBeta L := by
  rw [nicolasDelta, nicolasBeta]
  have hK : (0 : ℝ) < (K + 1 : ℕ) := by positivity
  field_simp

theorem nicolasBeta_lt_alpha {L : ℕ} (hL : 0 < L) :
    nicolasBeta L < nicolasAlpha L := by
  rw [nicolasBeta]
  have := nicolasAlpha_pos hL
  linarith

theorem nicolasGamma_lt_delta {L K : ℕ} (hL : 0 < L) :
    nicolasGamma L K < nicolasDelta L K := by
  rw [nicolasGamma]
  have := nicolasDelta_pos (K := K) hL
  linarith

theorem two_mul_beta_sub_alpha_lt_neg_gamma {L K : ℕ} (hL : 0 < L) :
    2 * nicolasBeta L - nicolasAlpha L < -nicolasGamma L K := by
  have ha := nicolasAlpha_pos hL
  have hd := nicolasDelta_pos (K := K) hL
  rw [nicolasBeta, nicolasGamma, nicolasDelta]
  have hK : (1 : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
  have hden : (0 : ℝ) < 8 * (K + 1 : ℕ) := by positivity
  have hfrac : nicolasAlpha L / (8 * (K + 1 : ℕ)) ≤
      nicolasAlpha L / 8 := by
    gcongr
    norm_num
  linarith

theorem eventually_const_mul_rpow_lt_rpow_real
    {a b C : ℝ} (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a < x ^ b := by
  have ht := tendsto_rpow_atTop (sub_pos.mpr hab)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
      ht.eventually_gt_atTop C] with x hx hlarge
  calc
    C * x ^ a < x ^ (b - a) * x ^ a :=
      mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hx a)
    _ = x ^ b := by
      rw [← Real.rpow_add hx]
      congr 2
      ring

theorem half_rpow_le_floor {x a : ℝ} (hpow : 2 ≤ x ^ a) :
    (1 / 2 : ℝ) * x ^ a ≤ (⌊x ^ a⌋₊ : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (x ^ a)
  linarith

theorem natCeil_rpow_le_two_mul {x a : ℝ} (hx : 1 ≤ x)
    (ha : 0 ≤ a) :
    (⌈x ^ a⌉₊ : ℝ) ≤ 2 * x ^ a := by
  have hpow : 1 ≤ x ^ a := by
    exact Real.one_le_rpow hx ha
  have hceil : (⌈x ^ a⌉₊ : ℝ) < x ^ a + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
  linarith

theorem nicolasBlockError_le_rpow
    {L H a : ℕ} {x A α β : ℝ}
    (hx : 0 < x) (hxβ : 1 ≤ x ^ β) (hA : 0 ≤ A)
    (ha : (1 / 2 : ℝ) * x ^ α ≤ (a : ℝ))
    (hapos : 0 < a) (hH : (H : ℝ) ≤ A * x ^ β) :
    nicolasBlockError L H a ≤
      4 * (L : ℝ) * (A + 2) * x ^ (β - α) := by
  have haposR : (0 : ℝ) < a := by exact_mod_cast hapos
  have hH2 : ((H + 2 : ℕ) : ℝ) ≤ (A + 2) * x ^ β := by
    push_cast
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (sub_nonneg.mpr hxβ)]
  have hnum : ((2 * L : ℕ) : ℝ) * ((H + 2 : ℕ) : ℝ) ≤
      2 * (L : ℝ) * (A + 2) * x ^ β := by
    calc
      ((2 * L : ℕ) : ℝ) * ((H + 2 : ℕ) : ℝ) =
          (2 * (L : ℝ)) * ((H + 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (2 * (L : ℝ)) * ((A + 2) * x ^ β) :=
        mul_le_mul_of_nonneg_left hH2 (by positivity)
      _ = 2 * (L : ℝ) * (A + 2) * x ^ β := by ring
  have hpowmul : x ^ (β - α) * x ^ α = x ^ β := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hB : 0 ≤ 4 * (L : ℝ) * (A + 2) * x ^ (β - α) := by positivity
  dsimp [nicolasBlockError]
  rw [div_le_iff₀ haposR]
  calc
    ((2 * L : ℕ) : ℝ) * ((H + 2 : ℕ) : ℝ) ≤
        2 * (L : ℝ) * (A + 2) * x ^ β := hnum
    _ = (4 * (L : ℝ) * (A + 2) * x ^ (β - α)) *
        ((1 / 2 : ℝ) * x ^ α) := by
      calc
        2 * (L : ℝ) * (A + 2) * x ^ β =
            2 * (L : ℝ) * (A + 2) *
              (x ^ (β - α) * x ^ α) := by rw [hpowmul]
        _ = _ := by ring
    _ ≤ (4 * (L : ℝ) * (A + 2) * x ^ (β - α)) * (a : ℝ) :=
      mul_le_mul_of_nonneg_left ha hB

/-- All numerical inequalities needed by the trial family hold uniformly
once the first threshold is large. -/
theorem eventually_nicolas_numeric
    {L N₀ K : ℕ} {c : ℝ} (hL : 0 < L) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      let R := nicolasRotationScale L K x
      let H := nicolasBlockBound L K c x
      let a₂ := nicolasRootTwo L x
      let a₁ := nicolasRootOne L x
      1 ≤ x ∧ 0 < R ∧ 1 ≤ H ∧
        N₀ + H + 1 ≤ a₂ ∧ 2 * H + 4 ≤ a₂ ∧ a₂ ≤ a₁ ∧
        nicolasBlockError L H a₂ + nicolasBlockError L H a₁ < 1 ∧
        (H : ℝ) *
            (nicolasBlockError L H a₂ + nicolasBlockError L H a₁) ≤
          C * x ^ (-nicolasGamma L K) ∧
        1 / ((R + 1 : ℕ) : ℝ) ≤ x ^ (-nicolasGamma L K) ∧
        3 < (1 - nicolasTheta) * Real.log x ∧
        3 < (nicolasTheta - nicolasThetaThree) * Real.log x := by
  let D : ℝ := (2 : ℝ) ^ (K + 1) / c
  let A : ℝ := D + 3
  let C : ℝ := 8 * (L : ℝ) * A * (A + 2)
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 < A := by dsimp [A]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hβ : 0 < nicolasBeta L := by
    rw [nicolasBeta]
    exact div_pos (nicolasAlpha_pos hL) (by norm_num)
  have hδ := nicolasDelta_pos (K := K) hL
  have hα := nicolasAlpha_pos hL
  have hβ_lt_α := nicolasBeta_lt_alpha hL
  have hcap := eventually_const_mul_rpow_lt_rpow_real
    (C := 4 * ((N₀ : ℝ) + A + 5)) hβ_lt_α
  have herr := eventually_const_mul_rpow_lt_rpow_real
    (C := 8 * (L : ℝ) * (A + 2)) hβ_lt_α
  have hpowLarge := (tendsto_rpow_atTop hα).eventually_gt_atTop 2
  have hgap12pos : 0 < 1 - nicolasTheta := sub_pos.mpr nicolasTheta_lt_one
  have hgap23pos : 0 < nicolasTheta - nicolasThetaThree :=
    sub_pos.mpr nicolasThetaThree_lt_theta
  have hlog12 : ∀ᶠ x : ℝ in atTop,
      3 < (1 - nicolasTheta) * Real.log x := by
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop
      (3 / (1 - nicolasTheta))] with x hx
    have := mul_lt_mul_of_pos_left hx hgap12pos
    field_simp at this
    linarith
  have hlog23 : ∀ᶠ x : ℝ in atTop,
      3 < (nicolasTheta - nicolasThetaThree) * Real.log x := by
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop
      (3 / (nicolasTheta - nicolasThetaThree))] with x hx
    have := mul_lt_mul_of_pos_left hx hgap23pos
    field_simp at this
    linarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), hcap, herr, hpowLarge,
      hlog12, hlog23] with x hx hcapx herrx hpowl hlog12x hlog23x
  dsimp only
  let R := nicolasRotationScale L K x
  let H := nicolasBlockBound L K c x
  let a₂ := nicolasRootTwo L x
  let a₁ := nicolasRootOne L x
  have hx1 : 1 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hxβ : 1 ≤ x ^ nicolasBeta L := Real.one_le_rpow hx1 hβ.le
  have hxδ : 1 ≤ x ^ nicolasDelta L K := Real.one_le_rpow hx1 hδ.le
  have hRlow : x ^ nicolasDelta L K ≤ (R : ℝ) := by
    dsimp [R, nicolasRotationScale]
    exact Nat.le_ceil _
  have hRhigh : (R : ℝ) ≤ 2 * x ^ nicolasDelta L K := by
    dsimp [R, nicolasRotationScale]
    exact natCeil_rpow_le_two_mul hx1 hδ.le
  have hRpos : 0 < R := by
    have : (0 : ℝ) < R := (Real.rpow_pos_of_pos hxpos _).trans_le hRlow
    exact_mod_cast this
  have hRpow : (R : ℝ) ^ (K + 1) ≤
      (2 : ℝ) ^ (K + 1) * x ^ nicolasBeta L := by
    have hxpowEq : (x ^ nicolasDelta L K) ^ (K + 1) =
        x ^ nicolasBeta L := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le,
        nicolasDelta_mul_succ]
    calc
      (R : ℝ) ^ (K + 1) ≤
          (2 * x ^ nicolasDelta L K) ^ (K + 1) := by gcongr
      _ = (2 : ℝ) ^ (K + 1) *
          (x ^ nicolasDelta L K) ^ (K + 1) := by rw [mul_pow]
      _ = (2 : ℝ) ^ (K + 1) * x ^ nicolasBeta L := by
        rw [hxpowEq]
  have hbase : (R : ℝ) ^ (K + 1) / c ≤ D * x ^ nicolasBeta L := by
    dsimp [D]
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hRpow hc.le
  have hbase0 : 0 ≤ (R : ℝ) ^ (K + 1) / c := by positivity
  have hHlt : (H : ℝ) < A * x ^ nicolasBeta L := by
    have hceil :
        (⌈(R : ℝ) ^ (K + 1) / c⌉₊ : ℝ) <
          (R : ℝ) ^ (K + 1) / c + 1 := Nat.ceil_lt_add_one hbase0
    dsimp [H, nicolasBlockBound]
    push_cast
    dsimp [A]
    nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hxβ)]
  have hHone : 1 ≤ H := by dsimp [H, nicolasBlockBound]; omega
  have hrootEq :
      (x ^ nicolasTheta) ^ (1 / (L : ℝ)) = x ^ nicolasAlpha L := by
    rw [← Real.rpow_mul hxpos.le]
    congr 1
    rw [nicolasAlpha]
    ring
  have ha₂low : (1 / 2 : ℝ) * x ^ nicolasAlpha L ≤ (a₂ : ℝ) := by
    dsimp [a₂, nicolasRootTwo]
    rw [hrootEq]
    exact half_rpow_le_floor hpowl.le
  have ha₂posR : (0 : ℝ) < a₂ :=
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos hxpos _)).trans_le ha₂low
  have ha₂pos : 0 < a₂ := by exact_mod_cast ha₂posR
  have hrootOrder : (x ^ nicolasTheta) ^ (1 / (L : ℝ)) ≤
      x ^ (1 / (L : ℝ)) := by
    rw [hrootEq]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    rw [nicolasAlpha]
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    exact (div_le_div_iff_of_pos_right hLR).2 nicolasTheta_lt_one.le
  have ha₂a₁ : a₂ ≤ a₁ := by
    dsimp [a₂, a₁, nicolasRootTwo, nicolasRootOne]
    exact Nat.floor_mono hrootOrder
  have ha₁pos : 0 < a₁ := ha₂pos.trans_le ha₂a₁
  have hcapStart : N₀ + H + 1 ≤ a₂ := by
    have hleft : ((N₀ + H + 1 : ℕ) : ℝ) <
        ((N₀ : ℝ) + A + 2) * x ^ nicolasBeta L := by
      push_cast
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ N₀ + 2)
        (sub_nonneg.mpr hxβ)]
    have hmid : ((N₀ : ℝ) + A + 2) * x ^ nicolasBeta L <
        (1 / 2 : ℝ) * x ^ nicolasAlpha L := by
      have hcoef : 2 * ((N₀ : ℝ) + A + 2) ≤
          4 * ((N₀ : ℝ) + A + 5) := by linarith [hA]
      nlinarith [mul_le_mul_of_nonneg_right hcoef
        (Real.rpow_nonneg hxpos.le (nicolasBeta L))]
    have : ((N₀ + H + 1 : ℕ) : ℝ) < (a₂ : ℝ) :=
      hleft.trans (hmid.trans_le ha₂low)
    exact_mod_cast this.le
  have hcapWidth : 2 * H + 4 ≤ a₂ := by
    have hleft : (((2 * H + 4 : ℕ) : ℕ) : ℝ) <
        (2 * A + 4) * x ^ nicolasBeta L := by
      push_cast
      nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
        (sub_nonneg.mpr hxβ)]
    have hmid : (2 * A + 4) * x ^ nicolasBeta L <
        (1 / 2 : ℝ) * x ^ nicolasAlpha L := by
      have hcoef : 2 * (2 * A + 4) ≤
          4 * ((N₀ : ℝ) + A + 5) := by
        have hN₀ : (0 : ℝ) ≤ N₀ := by positivity
        linarith
      nlinarith [mul_le_mul_of_nonneg_right hcoef
        (Real.rpow_nonneg hxpos.le (nicolasBeta L))]
    have : ((2 * H + 4 : ℕ) : ℝ) < (a₂ : ℝ) :=
      hleft.trans (hmid.trans_le ha₂low)
    exact_mod_cast this.le
  let Berr : ℝ := 4 * (L : ℝ) * (A + 2) *
    x ^ (nicolasBeta L - nicolasAlpha L)
  have hE₂ : nicolasBlockError L H a₂ ≤ Berr := by
    exact nicolasBlockError_le_rpow hxpos hxβ hA.le ha₂low ha₂pos hHlt.le
  have hE₁ : nicolasBlockError L H a₁ ≤ Berr := by
    have hnum0 : 0 ≤ ((2 * L : ℕ) : ℝ) * ((H + 2 : ℕ) : ℝ) := by positivity
    have hdiv : nicolasBlockError L H a₁ ≤ nicolasBlockError L H a₂ := by
      dsimp [nicolasBlockError]
      exact div_le_div_of_nonneg_left hnum0 ha₂posR (by exact_mod_cast ha₂a₁)
    exact hdiv.trans hE₂
  have hBerrSmall : 2 * Berr < 1 := by
    have hpowα : 0 < x ^ nicolasAlpha L := Real.rpow_pos_of_pos hxpos _
    have hpowmul : x ^ (nicolasBeta L - nicolasAlpha L) *
        x ^ nicolasAlpha L = x ^ nicolasBeta L := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    have hdiv :
        (8 * (L : ℝ) * (A + 2) * x ^ nicolasBeta L) /
            x ^ nicolasAlpha L < 1 :=
      (div_lt_one hpowα).2 herrx
    have heq :
        (8 * (L : ℝ) * (A + 2) * x ^ nicolasBeta L) /
            x ^ nicolasAlpha L = 2 * Berr := by
      apply (div_eq_iff hpowα.ne').2
      dsimp [Berr]
      rw [show (2 * (4 * (L : ℝ) * (A + 2) *
          x ^ (nicolasBeta L - nicolasAlpha L))) *
            x ^ nicolasAlpha L =
          8 * (L : ℝ) * (A + 2) *
            (x ^ (nicolasBeta L - nicolasAlpha L) *
              x ^ nicolasAlpha L) by ring,
        hpowmul]
    rwa [heq] at hdiv
  have hEsum : nicolasBlockError L H a₂ + nicolasBlockError L H a₁ < 1 := by
    linarith
  have hUraw : (H : ℝ) *
      (nicolasBlockError L H a₂ + nicolasBlockError L H a₁) ≤
        C * x ^ (2 * nicolasBeta L - nicolasAlpha L) := by
    have hEsumBound : nicolasBlockError L H a₂ + nicolasBlockError L H a₁ ≤
        2 * Berr := by linarith
    have hHnonneg : (0 : ℝ) ≤ H := by positivity
    have hEtotal0 : 0 ≤ nicolasBlockError L H a₂ +
        nicolasBlockError L H a₁ := by dsimp [nicolasBlockError]; positivity
    have hpowmul : x ^ nicolasBeta L *
        x ^ (nicolasBeta L - nicolasAlpha L) =
          x ^ (2 * nicolasBeta L - nicolasAlpha L) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    calc
      (H : ℝ) * (nicolasBlockError L H a₂ + nicolasBlockError L H a₁) ≤
          (H : ℝ) * (2 * Berr) := mul_le_mul_of_nonneg_left hEsumBound hHnonneg
      _ ≤ (A * x ^ nicolasBeta L) * (2 * Berr) := by
        exact mul_le_mul_of_nonneg_right hHlt.le (by dsimp [Berr]; positivity)
      _ = C * x ^ (2 * nicolasBeta L - nicolasAlpha L) := by
        dsimp [Berr, C]
        rw [show A * x ^ nicolasBeta L *
            (2 * (4 * (L : ℝ) * (A + 2) *
              x ^ (nicolasBeta L - nicolasAlpha L))) =
            8 * (L : ℝ) * A * (A + 2) *
              (x ^ nicolasBeta L *
                x ^ (nicolasBeta L - nicolasAlpha L)) by ring,
          hpowmul]
  have hUpower : C * x ^ (2 * nicolasBeta L - nicolasAlpha L) ≤
      C * x ^ (-nicolasGamma L K) := by
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx1
        (two_mul_beta_sub_alpha_lt_neg_gamma (K := K) hL).le) hC.le
  have hmesh : 1 / ((R + 1 : ℕ) : ℝ) ≤ x ^ (-nicolasGamma L K) := by
    have hRplus : x ^ nicolasDelta L K ≤ ((R + 1 : ℕ) : ℝ) := by
      exact hRlow.trans (by norm_num)
    have hdenpos : (0 : ℝ) < ((R + 1 : ℕ) : ℝ) := by positivity
    have hxδpos : 0 < x ^ nicolasDelta L K := Real.rpow_pos_of_pos hxpos _
    calc
      1 / ((R + 1 : ℕ) : ℝ) ≤ 1 / x ^ nicolasDelta L K :=
        one_div_le_one_div_of_le hxδpos hRplus
      _ = x ^ (-nicolasDelta L K) := by rw [one_div, Real.rpow_neg hxpos.le]
      _ ≤ x ^ (-nicolasGamma L K) := by
        exact Real.rpow_le_rpow_of_exponent_le hx1
          (neg_le_neg (nicolasGamma_lt_delta (K := K) hL).le)
  exact ⟨hx1, hRpos, hHone, hcapStart, hcapWidth, ha₂a₁,
    hEsum, hUraw.trans hUpower, hmesh, hlog12x, hlog23x⟩

/-- Nicolas's quantitative power-saving estimate, obtained unconditionally
from the fixed-power prime-window theorem and the explicit Feldman estimate. -/
theorem nicolasPowerBenefitBound : NicolasPowerBenefitBound := by
  obtain ⟨L, N₀, hL8, hwindow⟩ := exists_fixedPower_prime_windows
  have hL : 0 < L := by omega
  obtain ⟨c, hc, K, hfeldman⟩ := nicolasFeldmanEstimate
  obtain ⟨C, hC, hnumeric⟩ :=
    eventually_nicolas_numeric (N₀ := N₀) (K := K) hL hc
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 hnumeric
  let γ := nicolasGamma L K
  let C' := C + 6 * Real.log 2
  have hγ : 0 < γ := nicolasGamma_pos hL
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨C', γ, X₀, hC', hγ, ?_⟩
  intro ε N A hε hN hxX₀ hNA hANext hA
  let x := thresholdScale ε 1
  let R := nicolasRotationScale L K x
  let H := nicolasBlockBound L K c x
  let a₂ := nicolasRootTwo L x
  let a₁ := nicolasRootOne L x
  have hnum := hX₀ x (by simpa [x] using hxX₀)
  dsimp only at hnum
  change 1 ≤ x ∧ 0 < R ∧ 1 ≤ H ∧
      N₀ + H + 1 ≤ a₂ ∧ 2 * H + 4 ≤ a₂ ∧ a₂ ≤ a₁ ∧
      nicolasBlockError L H a₂ + nicolasBlockError L H a₁ < 1 ∧
      (H : ℝ) * (nicolasBlockError L H a₂ + nicolasBlockError L H a₁) ≤
        C * x ^ (-nicolasGamma L K) ∧
      1 / ((R + 1 : ℕ) : ℝ) ≤ x ^ (-nicolasGamma L K) ∧
      3 < (1 - nicolasTheta) * Real.log x ∧
      3 < (nicolasTheta - nicolasThetaThree) * Real.log x at hnum
  obtain ⟨hx1, hR, hH, hcapStart, hcapWidth, ha₂a₁,
    hEsum, hUraw, hmesh, hlog12, hlog23⟩ := hnum
  have hx : 0 < x := by
    dsimp [x]
    exact thresholdScale_pos (by omega)
  have hx2eq : thresholdScale ε 2 = x ^ nicolasTheta := by
    rw [thresholdScale_eq_one_rpow hε (k := 2) (by omega)]
    change x ^ (Real.log (1 + 1 / ((2 : ℕ) : ℝ)) / Real.log 2) =
      x ^ nicolasTheta
    congr 1
    rw [nicolasTheta]
    congr 2
    norm_num
  have hx3eq : thresholdScale ε 3 = x ^ nicolasThetaThree := by
    rw [thresholdScale_eq_one_rpow hε (k := 3) (by omega)]
    change x ^ (Real.log (1 + 1 / ((3 : ℕ) : ℝ)) / Real.log 2) =
      x ^ nicolasThetaThree
    congr 1
    rw [nicolasThetaThree]
    congr 2
    norm_num
  have hroot₂ := floor_rpow_root_bracket
    (x := thresholdScale ε 2) (thresholdScale_pos (by omega)) hL
  have hroot₁ := floor_rpow_root_bracket (x := x) hx hL
  have hroot₂Low : ((a₂ : ℝ) ^ L) ≤ thresholdScale ε 2 := by
    simpa [a₂, nicolasRootTwo, hx2eq] using hroot₂.1
  have hroot₂High : thresholdScale ε 2 < (((a₂ + 1 : ℕ) : ℝ) ^ L) := by
    simpa [a₂, nicolasRootTwo, hx2eq] using hroot₂.2
  have hroot₁Low : ((a₁ : ℝ) ^ L) ≤ thresholdScale ε 1 := by
    simpa [a₁, nicolasRootOne, x] using hroot₁.1
  have hroot₁High : thresholdScale ε 1 < (((a₁ + 1 : ℕ) : ℝ) ^ L) := by
    simpa [a₁, nicolasRootOne, x] using hroot₁.2
  have hgap12eq : Real.log (thresholdScale ε 1) -
      Real.log (thresholdScale ε 2) =
        (1 - nicolasTheta) * Real.log x := by
    rw [hx2eq, Real.log_rpow hx]
    dsimp [x]
    ring
  have hgap23eq : Real.log (thresholdScale ε 2) -
      Real.log (thresholdScale ε 3) =
        (nicolasTheta - nicolasThetaThree) * Real.log x := by
    rw [hx2eq, hx3eq, Real.log_rpow hx, Real.log_rpow hx]
    ring
  have hE₂0 : 0 ≤ nicolasBlockError L H a₂ := by
    dsimp [nicolasBlockError]
    positivity
  have hE₁0 : 0 ≤ nicolasBlockError L H a₁ := by
    dsimp [nicolasBlockError]
    positivity
  have hgap12P : nicolasBlockError L H a₂ <
      Real.log (thresholdScale ε 1) - Real.log (thresholdScale ε 2) := by
    rw [hgap12eq]
    linarith
  have hgap12Q : nicolasBlockError L H a₁ <
      Real.log (thresholdScale ε 1) - Real.log (thresholdScale ε 2) := by
    rw [hgap12eq]
    linarith
  have hgap23E : nicolasBlockError L H a₂ <
      Real.log (thresholdScale ε 2) - Real.log (thresholdScale ε 3) := by
    rw [hgap23eq]
    linarith
  have hseparate : nicolasBlockError L H a₂ + nicolasBlockError L H a₁ <
      Real.log (thresholdScale ε 1) - Real.log (thresholdScale ε 2) := by
    rw [hgap12eq]
    linarith
  have hlogx : Real.log x = (1 / ε) * Real.log 2 := by
    simpa [x] using log_thresholdScale_one hε
  have hlogx3 : 3 < Real.log x := by
    have hcoef0 : 0 < 1 - nicolasTheta := sub_pos.mpr nicolasTheta_lt_one
    have hlog0 : 0 < Real.log x := by
      by_contra hn
      have hnonpos : Real.log x ≤ 0 := le_of_not_gt hn
      have := mul_nonpos_of_nonneg_of_nonpos hcoef0.le hnonpos
      linarith
    have hcoef1 : 1 - nicolasTheta ≤ 1 := by linarith [nicolasTheta_pos]
    exact hlog12.trans_le (mul_le_of_le_one_left hlog0.le hcoef1)
  have hεle : ε ≤ 1 := by
    have hlog2lt : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
    have heq : ε * Real.log x = Real.log 2 := by
      rw [hlogx]
      field_simp
    nlinarith
  let U : ℝ := (H : ℝ) * ε *
    (nicolasBlockError L H a₂ + nicolasBlockError L H a₁)
  have hU : U ≤ C * x ^ (-γ) := by
    have hEtot0 : 0 ≤ nicolasBlockError L H a₂ +
        nicolasBlockError L H a₁ := add_nonneg hE₂0 hE₁0
    have hH0 : (0 : ℝ) ≤ H := by positivity
    calc
      U ≤ (H : ℝ) *
          (nicolasBlockError L H a₂ + nicolasBlockError L H a₁) := by
        dsimp [U]
        nlinarith [mul_nonneg hH0 hEtot0]
      _ ≤ C * x ^ (-nicolasGamma L K) := hUraw
      _ = C * x ^ (-γ) := by rfl
  have hpowerOne : x ^ (-γ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx1 (neg_nonpos.mpr hγ.le)
  have hdOne : 1 / ((R + 1 : ℕ) : ℝ) ≤ 1 := hmesh.trans hpowerOne
  have htrial : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ M : ℕ, ∃ r : ℝ, 0 < M ∧ benefit ε N M ≤ U ∧
        Real.log ((tau M : ℝ) / (tau N : ℝ)) = r * Real.log 2 ∧
        |r - t| ≤ 1 / ((R + 1 : ℕ) : ℝ) := by
    intro t ht0 ht1
    obtain ⟨h, j, hh, happ⟩ :=
      signedRotationCover hc hR hfeldman t ht0 ht1
    have hbase0 : 0 ≤ (R : ℝ) ^ (K + 1) / c := by positivity
    have hhNat : h.natAbs ≤ H := by
      have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      have hceil : (R : ℝ) ^ (K + 1) / c ≤
          (⌈(R : ℝ) ^ (K + 1) / c⌉₊ : ℝ) := Nat.le_ceil _
      have : (h.natAbs : ℝ) ≤
          (⌈(R : ℝ) ^ (K + 1) / c⌉₊ : ℝ) := by
        rw [habs]
        exact hh.trans hceil
      dsimp [H, nicolasBlockBound]
      exact_mod_cast this.trans (by norm_num :
        (⌈(R : ℝ) ^ (K + 1) / c⌉₊ : ℝ) ≤
          (⌈(R : ℝ) ^ (K + 1) / c⌉₊ + 2 : ℕ))
    let r : ℝ := (h : ℝ) * nicolasTheta - (j : ℝ)
    have hrabs : |r| ≤ 2 := by
      have hr : |r| ≤ |r - t| + |t| := by
        have := abs_add_le (r - t) t
        simpa [sub_add_cancel] using this
      have htAbs : |t| = t := abs_of_nonneg ht0
      calc
        |r| ≤ |r - t| + |t| := hr
        _ ≤ 1 + 1 := by
          exact add_le_add (happ.trans hdOne) (by simpa [htAbs] using ht1)
        _ = 2 := by norm_num
    have hjabs : |(j : ℝ)| ≤ |(h : ℝ)| + 2 := by
      have hjEq : (j : ℝ) = (h : ℝ) * nicolasTheta - r := by
        dsimp [r]
        ring
      rw [hjEq]
      calc
        |(h : ℝ) * nicolasTheta - r| ≤
            |(h : ℝ) * nicolasTheta| + |r| := abs_sub _ _
        _ = |(h : ℝ)| * nicolasTheta + |r| := by
          rw [abs_mul, abs_of_pos nicolasTheta_pos]
        _ ≤ |(h : ℝ)| * nicolasTheta + 2 := by gcongr
        _ ≤ |(h : ℝ)| + 2 := by
          have hh0 : 0 ≤ |(h : ℝ)| := abs_nonneg _
          simpa [add_comm] using add_le_add_right
            (mul_le_of_le_one_right hh0 nicolasTheta_lt_one.le) 2
    have hjNat : (-j).natAbs ≤ H := by
      have habsneg : (((-j).natAbs : ℕ) : ℝ) = |(j : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_neg, abs_neg]
      have hceil : (R : ℝ) ^ (K + 1) / c ≤
          (⌈(R : ℝ) ^ (K + 1) / c⌉₊ : ℝ) := Nat.le_ceil _
      have hreal : (((-j).natAbs : ℕ) : ℝ) ≤
          (⌈(R : ℝ) ^ (K + 1) / c⌉₊ + 2 : ℕ) := by
        push_cast
        rw [habsneg]
        exact hjabs.trans (by
          simpa [add_comm] using add_le_add_right (hh.trans hceil) 2)
      dsimp [H, nicolasBlockBound]
      exact_mod_cast hreal
    obtain ⟨M, hM, hMB, hMlog⟩ := exists_nicolas_trial_of_capacity
      hε hN hL hwindow hroot₂Low hroot₂High hroot₁Low hroot₁High
      ha₂a₁ hcapStart hcapWidth hhNat hjNat
      (by simpa [nicolasBlockError] using hgap12P)
      (by simpa [nicolasBlockError] using hgap12Q)
      (by simpa [nicolasBlockError] using hgap23E)
      (by simpa [nicolasBlockError] using hseparate)
    refine ⟨M, r, hM, ?_, ?_, ?_⟩
    · simpa [U, nicolasBlockError] using hMB
    · simpa [r] using hMlog
    · simpa [r] using happ
  have hzeroNat : (0 : ℤ).natAbs ≤ H := by simp
  have honeNat : (-(-1 : ℤ)).natAbs ≤ H := by simpa using hH
  obtain ⟨E, hE, hEB, hElog⟩ := exists_nicolas_trial_of_capacity
    (h := (0 : ℤ)) (j := (-1 : ℤ)) hε hN hL hwindow
    hroot₂Low hroot₂High hroot₁Low hroot₁High ha₂a₁ hcapStart hcapWidth
    hzeroNat honeNat
    (by simpa [nicolasBlockError] using hgap12P)
    (by simpa [nicolasBlockError] using hgap12Q)
    (by simpa [nicolasBlockError] using hgap23E)
    (by simpa [nicolasBlockError] using hseparate)
  have hEbenefit : benefit ε N E ≤ U := by
    simpa [U, nicolasBlockError] using hEB
  have hElog' : Real.log ((tau E : ℝ) / (tau N : ℝ)) = Real.log 2 := by
    simpa using hElog
  obtain ⟨upOne, downOne, hupOneInj, hdownOneInj, hupOne, hdownOne⟩ :=
    prime_blocks_log_error (H := 1) hL hwindow hroot₁Low hroot₁High
      (by omega) (by omega)
  let P : ℕ := upOne ⟨0, by omega⟩
  have hP : P.Prime := (hupOne ⟨0, by omega⟩).1
  have hxP : x < P := (hupOne ⟨0, by omega⟩).2.1
  have hPzero : N.factorization P = 0 :=
    hN.factorization_eq_zero_of_threshold_one_lt hε hP (by simpa [x] using hxP)
  obtain ⟨q, hq, hqP, hNqSuperior, hnextNq⟩ :=
    exists_superior_mul_prime_above_threshold hε hN hP
      (by simpa [x] using hxP)
  obtain ⟨η, hη, hNq⟩ := hNqSuperior
  have hNqHC : HighlyComposite (N * q) := hNq.highlyComposite hη
  have hANq : A < N * q := hANext.trans_le hnextNq
  have htauANq : tau A < tau (N * q) :=
    hNqHC.2 A hA.1 hANq
  have htauNq : tau (N * q) ≤ 2 * tau N :=
    tau_mul_prime_le_two_mul hN.1 hq
  have htauE : tau E = 2 * tau N :=
    tau_eq_two_mul_of_log_tau_div_eq_log_two hE hN.1 hElog'
  have htauAE : tau A ≤ tau E := by omega
  have hmain := benefit_le_of_trial_net hε hN hA hNA hE htauAE
    hEbenefit hElog' (by positivity : 0 ≤ 1 / (((R + 1 : ℕ) : ℕ) : ℝ)) htrial
  calc
    benefit ε N A ≤ U + 6 * (1 / ((R + 1 : ℕ) : ℝ)) * Real.log 2 := hmain
    _ ≤ C * x ^ (-γ) + 6 * x ^ (-γ) * Real.log 2 := by
      gcongr
    _ = C' * x ^ (-γ) := by dsimp [C']; ring
    _ = C' * (thresholdScale ε 1) ^ (-γ) := by rfl

theorem nicolasLocalPolynomialBound : NicolasLocalPolynomialBound :=
  nicolasLocalPolynomialBound_of_powerBenefitBound nicolasPowerBenefitBound

theorem nicolasPolynomialUpperBound : NicolasPolynomialUpperBound :=
  nicolasPolynomialUpperBound_of_local nicolasLocalPolynomialBound

theorem not_erdos381Claim : ¬ Erdos381Claim :=
  not_erdos381Claim_of_nicolasPolynomialUpperBound nicolasPolynomialUpperBound


end

end Erdos381
