import ErdosProblems.Erdos486.Statement

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Logarithmic density of eventually periodic sets

An eventually periodic set of positive natural numbers has logarithmic density equal to the
fraction of occupied residue classes.  The final theorem is stated using the real cutoffs and the
normalization `logAverage` from `Erdos486.Statement`.
-/

open Filter Set Asymptotics
open scoped Topology

namespace Erdos486

noncomputable section

/-- The reciprocal counting sum below a natural cutoff.  The term at zero is harmless, since its
inverse in `ℝ` is zero. -/
private def natLogSum (B : Set ℕ) (N : ℕ) : ℝ := by
  classical
  exact ∑ m ∈ Finset.range N, if m ∈ B then (m : ℝ)⁻¹ else 0

/-- The contribution of one complete block of length `L`. -/
private def periodicBlockSum (B : Set ℕ) (L q : ℕ) : ℝ := by
  classical
  exact ∑ r ∈ Finset.range L,
    if q * L + r ∈ B then ((q * L + r : ℕ) : ℝ)⁻¹ else 0

/-- The harmonic number, regarded as a real number. -/
private def realHarmonic (N : ℕ) : ℝ :=
  (harmonic N : ℝ)

/-- The occupied residues in the canonical interval `[0, L)`. -/
private def residueFinset (R : Set ℕ) (L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range L).filter fun r ↦ r ∈ R

/-- The number of occupied residues in one period. -/
private def occupiedResidues (R : Set ℕ) (L : ℕ) : ℕ :=
  (residueFinset R L).card

private lemma realHarmonic_eq_sum_range (N : ℕ) :
    realHarmonic N = ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ)⁻¹ := by
  simp [realHarmonic, harmonic]

private lemma tendsto_realHarmonic_div_log :
    Tendsto (fun N : ℕ ↦ realHarmonic N / Real.log N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herror :
      Tendsto (fun N : ℕ ↦ (realHarmonic N - Real.log N) / Real.log N) atTop (𝓝 0) :=
    Real.tendsto_harmonic_sub_log.div_atTop hlog
  have h : Tendsto
      (fun N : ℕ ↦ (1 : ℝ) + (realHarmonic N - Real.log N) / Real.log N)
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add herror
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog_ne : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp
  ring

private lemma natLogSum_nonneg (B : Set ℕ) (N : ℕ) : 0 ≤ natLogSum B N := by
  apply Finset.sum_nonneg
  intro m hm
  split_ifs
  · positivity
  · exact le_rfl

private lemma natLogSum_mono (B : Set ℕ) : Monotone (natLogSum B) := by
  intro M N hMN
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN)
  intro m hmN hmM
  split_ifs
  · positivity
  · exact le_rfl

private lemma natLogSum_mul_eq_sum_blocks (B : Set ℕ) (L Q : ℕ) :
    natLogSum B (Q * L) = ∑ q ∈ Finset.range Q, periodicBlockSum B L q := by
  classical
  induction Q with
  | zero => simp [natLogSum]
  | succ Q ih =>
      calc
        natLogSum B ((Q + 1) * L) =
            natLogSum B (Q * L) + periodicBlockSum B L Q := by
          simp only [Nat.succ_mul, natLogSum, periodicBlockSum, Finset.sum_range_add]
        _ = ∑ q ∈ Finset.range (Q + 1), periodicBlockSum B L q := by
          rw [ih, Finset.sum_range_succ]

private lemma periodicBlockSum_eq_filter (B R : Set ℕ) (L N₀ q : ℕ) (hL : 0 < L)
    (hq : N₀ ≤ q)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    periodicBlockSum B L q =
      ∑ r ∈ residueFinset R L, ((q * L + r : ℕ) : ℝ)⁻¹ := by
  classical
  simp only [residueFinset]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  have hrL : r < L := Finset.mem_range.mp hr
  have hq_le_mul : q ≤ q * L := by
    exact Nat.le_mul_of_pos_right q hL
  have hcutoff : N₀ ≤ q * L + r := hq.trans (hq_le_mul.trans (Nat.le_add_right _ _))
  have hmod : (q * L + r) % L = r := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hrL]
  rw [if_congr ((hperiodic _ hcutoff).trans (by rw [hmod])) rfl rfl]

private lemma periodicBlockSum_nonneg (B : Set ℕ) (L q : ℕ) :
    0 ≤ periodicBlockSum B L q := by
  apply Finset.sum_nonneg
  intro r hr
  split_ifs
  · positivity
  · exact le_rfl

private lemma periodicBlockSum_lower (B R : Set ℕ) (L N₀ q : ℕ) (hL : 0 < L)
    (hq₀ : N₀ ≤ q) (hq : 0 < q)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    (occupiedResidues R L : ℝ) * (((q + 1) * L : ℕ) : ℝ)⁻¹ ≤
      periodicBlockSum B L q := by
  classical
  rw [periodicBlockSum_eq_filter B R L N₀ q hL hq₀ hperiodic]
  calc
    (occupiedResidues R L : ℝ) * (((q + 1) * L : ℕ) : ℝ)⁻¹ =
        ∑ _r ∈ residueFinset R L,
          (((q + 1) * L : ℕ) : ℝ)⁻¹ := by
            simp [occupiedResidues]
    _ ≤ ∑ r ∈ residueFinset R L,
          ((q * L + r : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro r hr
      have hrL : r < L := by
        exact Finset.mem_range.mp (Finset.mem_filter.mp (by simpa [residueFinset] using hr)).1
      apply (inv_le_inv₀ (by positivity)
        (by exact_mod_cast (Nat.mul_pos hq hL).trans_le (Nat.le_add_right _ _))).2
      exact_mod_cast (show q * L + r ≤ (q + 1) * L by
        simpa [Nat.add_mul] using Nat.add_le_add_left hrL.le (q * L))

private lemma periodicBlockSum_upper (B R : Set ℕ) (L N₀ q : ℕ) (hL : 0 < L)
    (hq₀ : N₀ ≤ q) (hq : 0 < q)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    periodicBlockSum B L q ≤
      (occupiedResidues R L : ℝ) * ((q * L : ℕ) : ℝ)⁻¹ := by
  classical
  rw [periodicBlockSum_eq_filter B R L N₀ q hL hq₀ hperiodic]
  calc
    (∑ r ∈ residueFinset R L,
        ((q * L + r : ℕ) : ℝ)⁻¹) ≤
        ∑ _r ∈ residueFinset R L,
          ((q * L : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro r hr
      apply (inv_le_inv₀ (by positivity) (by exact_mod_cast Nat.mul_pos hq hL)).2
      exact_mod_cast Nat.le_add_right (q * L) r
    _ = (occupiedResidues R L : ℝ) * ((q * L : ℕ) : ℝ)⁻¹ := by
      simp [occupiedResidues]

private lemma cast_mul_inv_mul (k a L : ℕ) (ha : 0 < a) (hL : 0 < L) :
    (k : ℝ) * (((a * L : ℕ) : ℝ)⁻¹) =
      ((k : ℝ) / (L : ℝ)) * ((a : ℝ)⁻¹) := by
  push_cast
  field_simp

private lemma realHarmonic_eq_sum_Ico (N : ℕ) :
    realHarmonic N = ∑ n ∈ Finset.Ico 1 (N + 1), (n : ℝ)⁻¹ := by
  rw [realHarmonic_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

private lemma realHarmonic_sub_eq_sum_Ico {M N : ℕ} (hMN : M ≤ N) :
    realHarmonic N - realHarmonic M =
      ∑ n ∈ Finset.Ico M N, ((n + 1 : ℕ) : ℝ)⁻¹ := by
  rw [realHarmonic_eq_sum_range, realHarmonic_eq_sum_range,
    ← Finset.sum_Ico_eq_sub _ hMN]

private lemma natLogSum_mul_lower (B R : Set ℕ) (L N₀ M Q : ℕ) (hL : 0 < L)
    (hN₀M : N₀ ≤ M) (hM : 0 < M) (hMQ : M ≤ Q)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    ((occupiedResidues R L : ℝ) / (L : ℝ)) *
        (realHarmonic Q - realHarmonic M) ≤ natLogSum B (Q * L) := by
  rw [realHarmonic_sub_eq_sum_Ico hMQ, Finset.mul_sum,
    natLogSum_mul_eq_sum_blocks]
  calc
    (∑ q ∈ Finset.Ico M Q,
        ((occupiedResidues R L : ℝ) / (L : ℝ)) * ((q + 1 : ℕ) : ℝ)⁻¹) =
        ∑ q ∈ Finset.Ico M Q,
          (occupiedResidues R L : ℝ) * ((((q + 1) * L : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [cast_mul_inv_mul (occupiedResidues R L) (q + 1) L (Nat.succ_pos q) hL]
    _ ≤ ∑ q ∈ Finset.Ico M Q, periodicBlockSum B L q := by
      apply Finset.sum_le_sum
      intro q hq
      have hMq : M ≤ q := (Finset.mem_Ico.mp hq).1
      exact periodicBlockSum_lower B R L N₀ q hL (hN₀M.trans hMq)
        (hM.trans_le hMq) hperiodic
    _ ≤ ∑ q ∈ Finset.range Q, periodicBlockSum B L q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hq).2
      · intro q hq hq'
        exact periodicBlockSum_nonneg B L q

private lemma natLogSum_mul_upper (B R : Set ℕ) (L N₀ M Q : ℕ) (hL : 0 < L)
    (hN₀M : N₀ ≤ M) (hM : 0 < M) (hMQ : M ≤ Q)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    natLogSum B (Q * L) ≤ natLogSum B (M * L) +
      ((occupiedResidues R L : ℝ) / (L : ℝ)) * realHarmonic Q := by
  have hd_nonneg : 0 ≤ (occupiedResidues R L : ℝ) / (L : ℝ) := by positivity
  calc
    natLogSum B (Q * L) = natLogSum B (M * L) +
        ∑ q ∈ Finset.Ico M Q, periodicBlockSum B L q := by
      rw [natLogSum_mul_eq_sum_blocks, natLogSum_mul_eq_sum_blocks,
        Finset.sum_range_add_sum_Ico _ hMQ]
    _ ≤ natLogSum B (M * L) +
        ∑ q ∈ Finset.Ico M Q,
          (occupiedResidues R L : ℝ) * (((q * L : ℕ) : ℝ)⁻¹) := by
      gcongr with q hq
      have hMq : M ≤ q := (Finset.mem_Ico.mp hq).1
      exact periodicBlockSum_upper B R L N₀ q hL (hN₀M.trans hMq)
        (hM.trans_le hMq) hperiodic
    _ = natLogSum B (M * L) +
        ((occupiedResidues R L : ℝ) / (L : ℝ)) *
          ∑ q ∈ Finset.Ico M Q, ((q : ℕ) : ℝ)⁻¹ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hq_pos : 0 < q := hM.trans_le (Finset.mem_Ico.mp hq).1
      rw [cast_mul_inv_mul (occupiedResidues R L) q L hq_pos hL]
    _ ≤ natLogSum B (M * L) +
        ((occupiedResidues R L : ℝ) / (L : ℝ)) * realHarmonic Q := by
      gcongr
      rw [realHarmonic_eq_sum_Ico]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        have hqmem := Finset.mem_Ico.mp hq
        exact Finset.mem_Ico.mpr ⟨hM.trans_le hqmem.1, hqmem.2.trans_le (Nat.le_succ Q)⟩
      · intro q hq hq'
        positivity

private lemma tendsto_nat_mul_right_atTop (L : ℕ) (hL : 0 < L) :
    Tendsto (fun Q : ℕ ↦ Q * L) atTop atTop := by
  simpa [nsmul_eq_mul, mul_comm] using! (tendsto_id.nsmul_atTop hL)

private lemma tendsto_log_nat_mul_atTop (L : ℕ) (hL : 0 < L) :
    Tendsto (fun Q : ℕ ↦ Real.log ((Q * L : ℕ) : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_nat_mul_right_atTop L hL))

private lemma tendsto_log_div_log_nat_mul (L : ℕ) (hL : 0 < L) :
    Tendsto (fun Q : ℕ ↦ Real.log Q / Real.log ((Q * L : ℕ) : ℝ)) atTop (𝓝 1) := by
  have hlogQL := tendsto_log_nat_mul_atTop L hL
  have hlim : Tendsto
      (fun Q : ℕ ↦ 1 - Real.log (L : ℝ) / Real.log ((Q * L : ℕ) : ℝ))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hlogQL.const_div_atTop (Real.log (L : ℝ)))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with Q hQ
  have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast (Nat.zero_lt_of_lt hQ)
  have hL_pos : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogQL_ne : Real.log (((Q * L : ℕ) : ℝ)) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast (show 1 < Q * L by nlinarith)
  rw [show (((Q * L : ℕ) : ℝ)) = (Q : ℝ) * (L : ℝ) by norm_num,
    Real.log_mul hQ_pos.ne' hL_pos.ne'] at hlogQL_ne ⊢
  field_simp
  ring

private lemma tendsto_realHarmonic_div_log_mul (L : ℕ) (hL : 0 < L) :
    Tendsto (fun Q : ℕ ↦ realHarmonic Q / Real.log ((Q * L : ℕ) : ℝ))
      atTop (𝓝 1) := by
  have hlim : Tendsto
      (fun Q : ℕ ↦ (realHarmonic Q / Real.log Q) *
        (Real.log Q / Real.log ((Q * L : ℕ) : ℝ))) atTop (𝓝 1) := by
    simpa only [one_mul] using
      tendsto_realHarmonic_div_log.mul (tendsto_log_div_log_nat_mul L hL)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with Q hQ
  have hlogQ_ne : Real.log (Q : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hQ)).ne'
  have hlogQL_ne : Real.log (((Q * L : ℕ) : ℝ)) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast (show 1 < Q * L by nlinarith)
  field_simp

private lemma tendsto_natLogSum_mul_div_log (B R : Set ℕ) (L N₀ M : ℕ) (hL : 0 < L)
    (hN₀M : N₀ ≤ M) (hM : 0 < M)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    Tendsto
      (fun Q : ℕ ↦ natLogSum B (Q * L) / Real.log ((Q * L : ℕ) : ℝ)) atTop
      (𝓝 ((occupiedResidues R L : ℝ) / (L : ℝ))) := by
  let d : ℝ := (occupiedResidues R L : ℝ) / (L : ℝ)
  let C : ℝ := natLogSum B (M * L)
  have hden := tendsto_log_nat_mul_atTop L hL
  have hH := tendsto_realHarmonic_div_log_mul L hL
  have hlower : Tendsto
      (fun Q : ℕ ↦ d * (realHarmonic Q - realHarmonic M) /
        Real.log ((Q * L : ℕ) : ℝ)) atTop (𝓝 d) := by
    have hlim : Tendsto
        (fun Q : ℕ ↦ d * (realHarmonic Q / Real.log ((Q * L : ℕ) : ℝ)) -
          (d * realHarmonic M) / Real.log ((Q * L : ℕ) : ℝ)) atTop (𝓝 d) := by
      simpa using (hH.const_mul d).sub (hden.const_div_atTop (d * realHarmonic M))
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 2] with Q hQ
    have hlog_ne : Real.log (((Q * L : ℕ) : ℝ)) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast (show 1 < Q * L by nlinarith)
    field_simp
  have hupper : Tendsto
      (fun Q : ℕ ↦ (C + d * realHarmonic Q) /
        Real.log ((Q * L : ℕ) : ℝ)) atTop (𝓝 d) := by
    have hlim : Tendsto
        (fun Q : ℕ ↦ C / Real.log ((Q * L : ℕ) : ℝ) +
          d * (realHarmonic Q / Real.log ((Q * L : ℕ) : ℝ))) atTop (𝓝 d) := by
      simpa using (hden.const_div_atTop C).add (hH.const_mul d)
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 2] with Q hQ
    have hlog_ne : Real.log (((Q * L : ℕ) : ℝ)) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast (show 1 < Q * L by nlinarith)
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop (max M 2)] with Q hQ
    have hMQ : M ≤ Q := le_max_left M 2 |>.trans hQ
    have hlog_pos : 0 < Real.log (((Q * L : ℕ) : ℝ)) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < Q * L by
        have hQ2 : 2 ≤ Q := (le_max_right M 2).trans hQ
        nlinarith)
    apply (div_le_div_iff_of_pos_right hlog_pos).2
    exact natLogSum_mul_lower B R L N₀ M Q hL hN₀M hM hMQ hperiodic
  · filter_upwards [eventually_ge_atTop (max M 2)] with Q hQ
    have hMQ : M ≤ Q := le_max_left M 2 |>.trans hQ
    have hlog_pos : 0 < Real.log (((Q * L : ℕ) : ℝ)) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < Q * L by
        have hQ2 : 2 ≤ Q := (le_max_right M 2).trans hQ
        nlinarith)
    apply (div_le_div_iff_of_pos_right hlog_pos).2
    simpa [C, d] using natLogSum_mul_upper B R L N₀ M Q hL hN₀M hM hMQ hperiodic

private lemma tendsto_nat_div_mul_ratio (L : ℕ) (hL : 0 < L) :
    Tendsto (fun N : ℕ ↦ ((((N / L) * L : ℕ) : ℝ) / (N : ℝ))) atTop (𝓝 1) := by
  have hcast : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlower : Tendsto (fun N : ℕ ↦ 1 - (L : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hcast.const_div_atTop (L : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hnear : N < (N / L) * L + L := by
      calc
        N = N % L + L * (N / L) := (Nat.mod_add_div N L).symm
        _ < L + L * (N / L) := Nat.add_lt_add_right (Nat.mod_lt N hL) _
        _ = (N / L) * L + L := by ring
    rw [le_div_iff₀ hNpos]
    have hnear' : (N : ℝ) - (L : ℝ) ≤ (((N / L) * L : ℕ) : ℝ) := by
      have hnear_real : (N : ℝ) < (((N / L) * L : ℕ) : ℝ) + (L : ℝ) := by
        exact_mod_cast hnear
      linarith
    calc
      (1 - (L : ℝ) / (N : ℝ)) * (N : ℝ) = (N : ℝ) - (L : ℝ) := by
        field_simp
      _ ≤ (((N / L) * L : ℕ) : ℝ) := hnear'
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_one hNpos]
    exact_mod_cast Nat.div_mul_le_self N L

private lemma tendsto_nat_div_add_one_mul_ratio (L : ℕ) (hL : 0 < L) :
    Tendsto (fun N : ℕ ↦ ((((N / L + 1) * L : ℕ) : ℝ) / (N : ℝ))) atTop (𝓝 1) := by
  have hcast : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlim : Tendsto
      (fun N : ℕ ↦ ((((N / L) * L : ℕ) : ℝ) / (N : ℝ)) + (L : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
    simpa using (tendsto_nat_div_mul_ratio L hL).add (hcast.const_div_atTop (L : ℝ))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  push_cast
  field_simp

private lemma tendsto_log_div_log_of_isEquivalent {α : Type*} {l : Filter α}
    {f g : α → ℝ} (hfg : f ~[l] g) (hg : Tendsto g l atTop) :
    Tendsto (fun x ↦ Real.log (f x) / Real.log (g x)) l (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one
    ((Real.tendsto_log_atTop.comp hg).eventually_ne_atTop 0)).1
  exact hfg.log hg

private lemma tendsto_log_nat_div_mul_ratio (L : ℕ) (hL : 0 < L) :
    Tendsto
      (fun N : ℕ ↦ Real.log (((N / L) * L : ℕ) : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
  apply tendsto_log_div_log_of_isEquivalent
  · apply (isEquivalent_iff_tendsto_one
      (tendsto_natCast_atTop_atTop.eventually_ne_atTop 0)).2
    exact tendsto_nat_div_mul_ratio L hL
  · exact tendsto_natCast_atTop_atTop

private lemma tendsto_log_nat_div_add_one_mul_ratio (L : ℕ) (hL : 0 < L) :
    Tendsto
      (fun N : ℕ ↦ Real.log (((N / L + 1) * L : ℕ) : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
  apply tendsto_log_div_log_of_isEquivalent
  · apply (isEquivalent_iff_tendsto_one
      (tendsto_natCast_atTop_atTop.eventually_ne_atTop 0)).2
    exact tendsto_nat_div_add_one_mul_ratio L hL
  · exact tendsto_natCast_atTop_atTop

/-- Natural-cutoff form of logarithmic-density recovery for an eventual residue pattern. -/
private lemma tendsto_natLogSum_div_log_of_eventually_modPeriodic
    (B R : Set ℕ) (L N₀ : ℕ) (hL : 0 < L)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    Tendsto (fun N : ℕ ↦ natLogSum B N / Real.log (N : ℝ)) atTop
      (𝓝 ((occupiedResidues R L : ℝ) / (L : ℝ))) := by
  let M : ℕ := max N₀ 1
  have hN₀M : N₀ ≤ M := le_max_left _ _
  have hM : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hblocks := tendsto_natLogSum_mul_div_log B R L N₀ M hL hN₀M hM hperiodic
  have hquot : Tendsto (fun N : ℕ ↦ N / L) atTop atTop :=
    Nat.tendsto_div_const_atTop hL.ne'
  have hquot_succ : Tendsto (fun N : ℕ ↦ N / L + 1) atTop atTop := by
    simpa [Function.comp_def] using (tendsto_add_atTop_nat 1).comp hquot
  have hlower : Tendsto
      (fun N : ℕ ↦ natLogSum B ((N / L) * L) / Real.log (N : ℝ)) atTop
      (𝓝 ((occupiedResidues R L : ℝ) / (L : ℝ))) := by
    have hlim : Tendsto
        (fun N : ℕ ↦
          (natLogSum B ((N / L) * L) / Real.log (((N / L) * L : ℕ) : ℝ)) *
            (Real.log (((N / L) * L : ℕ) : ℝ) / Real.log (N : ℝ))) atTop
        (𝓝 ((occupiedResidues R L : ℝ) / (L : ℝ))) := by
      simpa only [mul_one] using!
        (hblocks.comp hquot).mul (tendsto_log_nat_div_mul_ratio L hL)
    apply hlim.congr'
    filter_upwards [hquot.eventually_ge_atTop 2, eventually_ge_atTop 2] with N hq hN
    have hlogq_ne : Real.log ((((N / L) * L : ℕ) : ℝ)) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast (show 1 < (N / L) * L by nlinarith)
    have hlogN_ne : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hN)).ne'
    field_simp
  have hupper : Tendsto
      (fun N : ℕ ↦ natLogSum B ((N / L + 1) * L) / Real.log (N : ℝ)) atTop
      (𝓝 ((occupiedResidues R L : ℝ) / (L : ℝ))) := by
    have hlim : Tendsto
        (fun N : ℕ ↦
          (natLogSum B ((N / L + 1) * L) /
              Real.log (((N / L + 1) * L : ℕ) : ℝ)) *
            (Real.log (((N / L + 1) * L : ℕ) : ℝ) / Real.log (N : ℝ))) atTop
        (𝓝 ((occupiedResidues R L : ℝ) / (L : ℝ))) := by
      simpa only [mul_one] using!
        (hblocks.comp hquot_succ).mul (tendsto_log_nat_div_add_one_mul_ratio L hL)
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogq_ne : Real.log ((((N / L + 1) * L : ℕ) : ℝ)) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast (show 1 < (N / L + 1) * L by
        have hnear : N < (N / L + 1) * L := by
          calc
            N = N % L + L * (N / L) := (Nat.mod_add_div N L).symm
            _ < L + L * (N / L) := Nat.add_lt_add_right (Nat.mod_lt N hL) _
            _ = (N / L + 1) * L := by ring
        omega)
    have hlogN_ne : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hN)).ne'
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    apply (div_le_div_iff_of_pos_right hlogN_pos).2
    exact natLogSum_mono B (Nat.div_mul_le_self N L)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
    have hnear : N ≤ (N / L + 1) * L := by
      apply le_of_lt
      calc
        N = N % L + L * (N / L) := (Nat.mod_add_div N L).symm
        _ < L + L * (N / L) := Nat.add_lt_add_right (Nat.mod_lt N hL) _
        _ = (N / L + 1) * L := by ring
    apply (div_le_div_iff_of_pos_right hlogN_pos).2
    exact natLogSum_mono B hnear

private lemma logSum_eq_natLogSum_ceil (B : Set ℕ) (x : ℝ) :
    logSum B x = natLogSum B ⌈x⌉₊ := by
  classical
  rw [logSum, natLogSum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmx : (m : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hm)
  simp [hmx]

/-- Bridge from natural cutoffs to the exact real-cutoff normalization in `Statement.lean`. -/
private lemma hasLogDensity_of_tendsto_natLogSum_div_log (B : Set ℕ) (d : ℝ)
    (h : Tendsto (fun N : ℕ ↦ natLogSum B N / Real.log (N : ℝ)) atTop (𝓝 d)) :
    HasLogDensity B d := by
  have hceil : Tendsto (fun x : ℝ ↦ ⌈x⌉₊) atTop atTop := tendsto_nat_ceil_atTop
  have hceil_equiv :
      (fun x : ℝ ↦ (⌈x⌉₊ : ℝ)) ~[atTop] (fun x : ℝ ↦ x) := by
    apply (isEquivalent_iff_tendsto_one
      ((eventually_gt_atTop (0 : ℝ)).mono fun _ hx ↦ hx.ne')).2
    exact tendsto_nat_ceil_div_atTop
  have hlog_ratio : Tendsto
      (fun x : ℝ ↦ Real.log (⌈x⌉₊ : ℝ) / Real.log x) atTop (𝓝 1) :=
    tendsto_log_div_log_of_isEquivalent hceil_equiv tendsto_id
  have hlim : Tendsto
      (fun x : ℝ ↦
        (natLogSum B ⌈x⌉₊ / Real.log (⌈x⌉₊ : ℝ)) *
          (Real.log (⌈x⌉₊ : ℝ) / Real.log x)) atTop (𝓝 d) := by
    simpa only [mul_one] using! (h.comp hceil).mul hlog_ratio
  unfold HasLogDensity logAverage
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hceil_two : 2 ≤ ⌈x⌉₊ := by
    apply Nat.add_one_le_ceil_iff.mpr
    simpa using hx
  have hlogceil_ne : Real.log (⌈x⌉₊ : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hceil_two)).ne'
  have hlogx_ne : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [logSum_eq_natLogSum_ceil]
  field_simp

/-- **Finite-periodic logarithmic-density recovery.**

If `B` consists of positive naturals and, from `N₀` onward, membership in `B` is exactly
membership of `n % L` in the finite residue set `R`, then `B` has logarithmic density
`R.card / L` in the exact real-cutoff sense of `HasLogDensity`.  Positivity of the period and the
fact that every listed residue lies in `[0, L)` are explicit assumptions.
-/
theorem hasLogDensity_of_eventually_periodic
    (B : Set ℕ) (R : Finset ℕ) (L N₀ : ℕ)
    (hL : 0 < L)
    (hR : ∀ r ∈ R, r < L)
    (_hpositive : ∀ n ∈ B, 0 < n)
    (hperiodic : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ R)) :
    HasLogDensity B ((R.card : ℝ) / (L : ℝ)) := by
  have hpattern : ∀ n, N₀ ≤ n → (n ∈ B ↔ n % L ∈ (R : Set ℕ)) := by
    simpa using hperiodic
  have hresidues : residueFinset (R : Set ℕ) L = R := by
    ext r
    simp only [residueFinset, Finset.mem_filter, Finset.mem_range, Finset.mem_coe]
    constructor
    · exact fun hr ↦ hr.2
    · intro hr
      exact ⟨hR r hr, hr⟩
  have hcount : occupiedResidues (R : Set ℕ) L = R.card := by
    simp [occupiedResidues, hresidues]
  have hnat := tendsto_natLogSum_div_log_of_eventually_modPeriodic
    B (R : Set ℕ) L N₀ hL hpattern
  have hdensity := hasLogDensity_of_tendsto_natLogSum_div_log B
    ((occupiedResidues (R : Set ℕ) L : ℝ) / (L : ℝ)) hnat
  rw [hcount] at hdensity
  exact hdensity

end

end Erdos486
