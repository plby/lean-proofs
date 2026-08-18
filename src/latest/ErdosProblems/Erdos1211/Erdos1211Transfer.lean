import ErdosProblems.Erdos1211.Erdos1211Local
import ErdosProblems.Erdos1211.Erdos1211Shadow

/-!
# From long finite intervals to logarithmic density

This file transfers the finite rough-shell theorem to the interval-shadow
process.  The exponential scale has a deliberately large fixed offset.  As a
result, every shadow block is contained in one of the finite subset-sum
intervals, with no trimming or boundary-error argument.
-/

namespace Erdos1211Transfer

open BigOperators Filter Finset Set

attribute [local instance] Classical.propDecidable
noncomputable section

def lowerCoeff : ℕ := 512 * Erdos1211Local.pivotCount

def offsetCore : ℕ :=
  32 * Erdos1211Local.modulus * lowerCoeff

def transferOffset : ℕ := Erdos1211Local.largeThreshold + offsetCore

def shellScale (n : ℕ) : ℕ := 2 ^ (transferOffset + n)

def blockStart (n : ℕ) : ℕ := lowerCoeff * shellScale n

lemma lowerCoeff_pos : 0 < lowerCoeff := by
  exact Nat.mul_pos (by norm_num) Erdos1211Local.pivotCount_pos

lemma transferOffset_pos : 0 < transferOffset := by
  have hcore : 0 < offsetCore := by
    exact Nat.mul_pos
      (Nat.mul_pos (by norm_num) Erdos1211Local.modulus_pos) lowerCoeff_pos
  simp only [transferOffset]
  omega

lemma shellScale_pos (n : ℕ) : 0 < shellScale n := by
  simp [shellScale]

lemma blockStart_pos (n : ℕ) : 0 < blockStart n := by
  exact Nat.mul_pos lowerCoeff_pos (shellScale_pos n)

lemma shellScale_succ (n : ℕ) : shellScale (n + 1) = 2 * shellScale n := by
  simp only [shellScale]
  rw [show transferOffset + (n + 1) = (transferOffset + n) + 1 by omega,
    pow_succ]
  ring

lemma blockStart_succ (n : ℕ) : blockStart (n + 1) = 2 * blockStart n := by
  rw [blockStart, shellScale_succ, blockStart]
  ring

lemma shellScale_mono {j n : ℕ} (hjn : j ≤ n) : shellScale j ≤ shellScale n := by
  change 2 ^ (transferOffset + j) ≤ 2 ^ (transferOffset + n)
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma blockStart_mono {j n : ℕ} (hjn : j ≤ n) : blockStart j ≤ blockStart n := by
  exact Nat.mul_le_mul_left lowerCoeff (shellScale_mono hjn)

lemma transferOffset_le_pow : transferOffset ≤ 2 ^ transferOffset := by
  exact (Nat.lt_two_pow_self).le

lemma offsetCore_le_transferOffset : offsetCore ≤ transferOffset := by
  simp [transferOffset]

lemma tendsto_shellScale_atTop : Tendsto shellScale atTop atTop := by
  apply Filter.tendsto_atTop_mono
    (f := fun n : ℕ ↦ 2 ^ n)
    (g := shellScale)
  · intro n
    exact Nat.pow_le_pow_right (by norm_num) (by simp [shellScale])
  · exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)

lemma tendsto_blockStart_atTop : Tendsto blockStart atTop atTop := by
  apply Filter.tendsto_atTop_mono
    (f := shellScale)
    (g := blockStart)
  · intro n
    rw [blockStart]
    exact Nat.le_mul_of_pos_left (shellScale n) lowerCoeff_pos
  · exact tendsto_shellScale_atTop

lemma largeEnough_shellScale (n : ℕ) :
    Erdos1211Local.LargeEnough (shellScale n) := by
  apply Erdos1211Local.largeEnough_of_ge
  calc
    Erdos1211Local.largeThreshold ≤ transferOffset := by simp [transferOffset]
    _ ≤ 2 ^ transferOffset := transferOffset_le_pow
    _ ≤ shellScale n := by
      change 2 ^ transferOffset ≤ 2 ^ (transferOffset + n)
      exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma reserveCount_lower (N : ℕ) :
    N / (16 * Erdos1211Local.modulus) ≤ Erdos1211Local.reserveCount N := by
  have hphi : 1 ≤ Erdos1211Local.phi := Erdos1211Local.phi_pos
  have hN : N ≤ N * Erdos1211Local.phi := by nlinarith
  simpa only [Erdos1211Local.reserveCount] using
    Nat.div_le_div_right (c := 16 * Erdos1211Local.modulus) hN

lemma shadow_block_upper {j n : ℕ} (hjn : j ≤ n) (hnj : n ≤ 2 * j) :
    blockStart (n + 1) ≤
      shellScale j * Erdos1211Local.reserveCount (shellScale j) := by
  let q := lowerCoeff * 2 ^ (n + 1 - j)
  have hden : 0 < 16 * Erdos1211Local.modulus :=
    Nat.mul_pos (by norm_num) Erdos1211Local.modulus_pos
  have hexp : n + 1 - j ≤ j + 1 := by omega
  have hq : q ≤ 2 * lowerCoeff * 2 ^ j := by
    dsimp only [q]
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hexp
    rw [pow_succ] at hp
    nlinarith
  have hmul : (16 * Erdos1211Local.modulus) * q ≤ shellScale j := by
    calc
      (16 * Erdos1211Local.modulus) * q
          ≤ (16 * Erdos1211Local.modulus) * (2 * lowerCoeff * 2 ^ j) :=
            Nat.mul_le_mul_left _ hq
      _ = offsetCore * 2 ^ j := by rw [offsetCore]; ring
      _ ≤ transferOffset * 2 ^ j :=
        Nat.mul_le_mul_right (2 ^ j) offsetCore_le_transferOffset
      _ ≤ 2 ^ transferOffset * 2 ^ j :=
        Nat.mul_le_mul_right (2 ^ j) transferOffset_le_pow
      _ = shellScale j := by simp only [shellScale, pow_add]
  have hqdiv : q ≤ shellScale j / (16 * Erdos1211Local.modulus) :=
    (Nat.le_div_iff_mul_le hden).2 (by simpa [mul_comm] using hmul)
  have hqreserve : q ≤ Erdos1211Local.reserveCount (shellScale j) :=
    hqdiv.trans (reserveCount_lower _)
  have hfactor : shellScale j * q = blockStart (n + 1) := by
    dsimp only [q, shellScale, blockStart]
    calc
      2 ^ (transferOffset + j) * (lowerCoeff * 2 ^ (n + 1 - j)) =
          lowerCoeff * (2 ^ (transferOffset + j) * 2 ^ (n + 1 - j)) := by ring
      _ = lowerCoeff * 2 ^ ((transferOffset + j) + (n + 1 - j)) := by
        exact congrArg (fun z : ℕ ↦ lowerCoeff * z)
          (pow_add (2 : ℕ) (transferOffset + j) (n + 1 - j)).symm
      _ = lowerCoeff * 2 ^ (transferOffset + (n + 1)) := by
        have he : (transferOffset + j) + (n + 1 - j) =
            transferOffset + (n + 1) := by omega
        rw [he]
  rw [← hfactor]
  exact Nat.mul_le_mul_left _ hqreserve

lemma shadow_block_subset_local_interval {j n : ℕ}
    (hjn : j ≤ n) (hnj : n ≤ 2 * j) :
    Finset.Ico (blockStart n) (blockStart (n + 1)) ⊆
      Finset.Icc (Erdos1211Local.lowerEndpoint (shellScale j))
        (Erdos1211Local.upperEndpoint (shellScale j)) := by
  intro x hx
  rw [Finset.mem_Ico] at hx
  rw [Finset.mem_Icc]
  constructor
  · have hlower : Erdos1211Local.lowerEndpoint (shellScale j) = blockStart j := by
      simp [Erdos1211Local.lowerEndpoint, lowerCoeff, blockStart]
    rw [hlower]
    exact (blockStart_mono hjn).trans hx.1
  · have hu := shadow_block_upper hjn hnj
    rw [Erdos1211Local.upperEndpoint]
    exact hx.2.le.trans hu

/-! ### Harmonic mass of the dyadic blocks -/

lemma log_succ_sub_log_le_inv (n : ℕ) (hn : 0 < n) :
    Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ (n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsuccR : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  rw [← Real.log_div hsuccR.ne' hnR.ne']
  calc
    Real.log (((n + 1 : ℕ) : ℝ) / n) ≤
        (((n + 1 : ℕ) : ℝ) / n) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hsuccR hnR)
    _ = (n : ℝ)⁻¹ := by
      rw [inv_eq_one_div]
      field_simp
      norm_num [Nat.cast_add]

lemma log_sub_log_le_harmonic_Ico {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    Real.log (B : ℝ) - Real.log (A : ℝ) ≤
      ∑ n ∈ Finset.Ico A B, (n : ℝ)⁻¹ := by
  have hterm : ∀ n ∈ Finset.Ico A B,
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ (n : ℝ)⁻¹ := by
    intro n hn
    exact log_succ_sub_log_le_inv n (hA.trans_le (Finset.mem_Ico.mp hn).1)
  have htel (K : ℕ) :
      (∑ n ∈ Finset.range K,
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) =
        Real.log (K : ℝ) - Real.log (0 : ℝ) := by
    simpa using Finset.sum_range_sub (fun n : ℕ ↦ Real.log (n : ℝ)) K
  calc
    Real.log (B : ℝ) - Real.log (A : ℝ) =
        ∑ n ∈ Finset.Ico A B,
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) := by
      rw [Finset.sum_Ico_eq_sub _ hAB, htel B, htel A]
      ring
    _ ≤ ∑ n ∈ Finset.Ico A B, (n : ℝ)⁻¹ :=
      Finset.sum_le_sum hterm

def harmonicBlock (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico (blockStart n) (blockStart (n + 1)), (m : ℝ)⁻¹

lemma log_blockStart_succ_sub (n : ℕ) :
    Real.log (blockStart (n + 1) : ℝ) - Real.log (blockStart n : ℝ) =
      Real.log 2 := by
  rw [blockStart_succ]
  have hblockR : (0 : ℝ) < blockStart n := by
    exact_mod_cast blockStart_pos n
  have hcast : ((2 * blockStart n : ℕ) : ℝ) =
      (2 : ℝ) * (blockStart n : ℝ) := Nat.cast_mul 2 (blockStart n)
  rw [hcast]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hblockR.ne']
  ring

lemma log_two_le_harmonicBlock (n : ℕ) : Real.log 2 ≤ harmonicBlock n := by
  rw [← log_blockStart_succ_sub n]
  exact log_sub_log_le_harmonic_Ico (blockStart_pos n)
    (by rw [blockStart_succ]; omega)

def selectedIndices (X : Set ℕ) (T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 T).filter fun n ↦ n ∈ X

def selectedBlocks (X : Set ℕ) (T : ℕ) : Finset ℕ :=
  (selectedIndices X T).biUnion fun n ↦
    Finset.Ico (blockStart n) (blockStart (n + 1))

lemma selectedIndices_eq (X : Set ℕ) (T : ℕ) :
    selectedIndices X T = (Finset.Icc 1 T).filter fun n ↦ n ∈ X := rfl

lemma card_selectedIndices (X : Set ℕ) (T : ℕ) :
    (selectedIndices X T).card = Erdos1211Shadow.cutoffCount X T := rfl

lemma pairwiseDisjoint_selected_blocks (X : Set ℕ) (T : ℕ) :
    (↑(selectedIndices X T) : Set ℕ).PairwiseDisjoint
      (fun n ↦ Finset.Ico (blockStart n) (blockStart (n + 1))) := by
  intro a ha b hb hab
  change Disjoint
    (Finset.Ico (blockStart a) (blockStart (a + 1)))
    (Finset.Ico (blockStart b) (blockStart (b + 1)))
  rw [Finset.disjoint_left]
  intro x hxa hxb
  have hxa' := Finset.mem_Ico.mp hxa
  have hxb' := Finset.mem_Ico.mp hxb
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · have hmono : blockStart (a + 1) ≤ blockStart b :=
      blockStart_mono (by omega)
    omega
  · have hmono : blockStart (b + 1) ≤ blockStart a :=
      blockStart_mono (by omega)
    omega

lemma sum_selectedBlocks (X : Set ℕ) (T : ℕ) :
    ∑ m ∈ selectedBlocks X T, (m : ℝ)⁻¹ =
      ∑ n ∈ selectedIndices X T, harmonicBlock n := by
  exact Finset.sum_biUnion (pairwiseDisjoint_selected_blocks X T)

lemma selectedBlocks_subset_cutoff (X : Set ℕ) (T : ℕ) :
    selectedBlocks X T ⊆ Finset.Ico 1 (blockStart (T + 1)) := by
  intro x hx
  obtain ⟨n, hn, hxn⟩ := Finset.mem_biUnion.mp hx
  have hnI := (Finset.mem_filter.mp hn).1
  have hxnI := Finset.mem_Ico.mp hxn
  rw [Finset.mem_Ico]
  constructor
  · exact (blockStart_pos n).trans_le hxnI.1
  · exact hxnI.2.trans_le (blockStart_mono (by
      have hnT := (Finset.mem_Icc.mp hnI).2
      omega))

lemma card_mul_log_two_le_sum_selectedBlocks (X : Set ℕ) (T : ℕ) :
    ((selectedIndices X T).card : ℝ) * Real.log 2 ≤
      ∑ m ∈ selectedBlocks X T, (m : ℝ)⁻¹ := by
  rw [sum_selectedBlocks]
  calc
    ((selectedIndices X T).card : ℝ) * Real.log 2 =
        ∑ _n ∈ selectedIndices X T, Real.log 2 := by simp
    _ ≤ ∑ n ∈ selectedIndices X T, harmonicBlock n := by
      apply Finset.sum_le_sum
      intro n hn
      exact log_two_le_harmonicBlock n

/-! ### Density transfer -/

def CoversShadowBlocks (α : ℕ → Fin 2) (sigma : Fin 2 → Set ℕ) : Prop :=
  ∀ i : Fin 2, ∀ n : ℕ, n ∈ Erdos1211Shadow.shadow α i →
    (↑(Finset.Ico (blockStart n) (blockStart (n + 1))) : Set ℕ) ⊆ sigma i

lemma selectedBlocks_subset_sigma {α : ℕ → Fin 2} {sigma : Fin 2 → Set ℕ}
    (hcover : CoversShadowBlocks α sigma) (i : Fin 2) (T : ℕ) :
    selectedBlocks (Erdos1211Shadow.shadow α i) T ⊆
      (Finset.Ico 1 (blockStart (T + 1))).filter (fun m ↦ m ∈ sigma i) := by
  intro m hm
  rw [Finset.mem_filter]
  refine ⟨selectedBlocks_subset_cutoff _ _ hm, ?_⟩
  obtain ⟨n, hn, hmn⟩ := Finset.mem_biUnion.mp hm
  have hnshadow : n ∈ Erdos1211Shadow.shadow α i :=
    (Finset.mem_filter.mp hn).2
  exact hcover i n hnshadow hmn

lemma cutoffCount_mul_log_two_le_harmonicPrefix
    {α : ℕ → Fin 2} {sigma : Fin 2 → Set ℕ}
    (hcover : CoversShadowBlocks α sigma) (i : Fin 2) (T : ℕ) :
    (Erdos1211Shadow.cutoffCount (Erdos1211Shadow.shadow α i) T : ℝ) *
        Real.log 2 ≤
      Erdos1211DensityNat.harmonicPrefix (sigma i) (blockStart (T + 1)) := by
  rw [Erdos1211DensityNat.harmonicPrefix_eq_sum_filter]
  calc
    (Erdos1211Shadow.cutoffCount (Erdos1211Shadow.shadow α i) T : ℝ) *
          Real.log 2 =
        ((selectedIndices (Erdos1211Shadow.shadow α i) T).card : ℝ) *
          Real.log 2 := by rw [card_selectedIndices]
    _ ≤ ∑ m ∈ selectedBlocks (Erdos1211Shadow.shadow α i) T,
          (m : ℝ)⁻¹ :=
      card_mul_log_two_le_sum_selectedBlocks _ _
    _ ≤ ∑ m ∈ (Finset.Ico 1 (blockStart (T + 1))).filter
          (fun m ↦ m ∈ sigma i), (m : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (selectedBlocks_subset_sigma hcover i T)
      intro m hm hmnot
      positivity

lemma blockStart_ge_two (n : ℕ) : 2 ≤ blockStart n := by
  have hcoeff : 2 ≤ lowerCoeff := by
    rw [lowerCoeff]
    have hp := Erdos1211Local.pivotCount_ge_eight
    omega
  calc
    2 ≤ lowerCoeff := hcoeff
    _ ≤ lowerCoeff * shellScale n :=
      Nat.le_mul_of_pos_right lowerCoeff (shellScale_pos n)
    _ = blockStart n := rfl

lemma log_blockStart_pos (n : ℕ) : 0 < Real.log (blockStart n : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two (blockStart_ge_two n))

lemma log_blockStart_formula (n : ℕ) :
    Real.log (blockStart n : ℝ) =
      Real.log (blockStart 0 : ℝ) + (n : ℝ) * Real.log 2 := by
  induction n with
  | zero => simp only [Nat.cast_zero, zero_mul, add_zero]
  | succ n ih =>
      have hs := log_blockStart_succ_sub n
      rw [show n + 1 = Nat.succ n by rfl] at hs ⊢
      push_cast
      nlinarith

def densityFactor (T : ℕ) : ℝ :=
  (T : ℝ) * Real.log 2 / Real.log (blockStart (T + 1) : ℝ)

lemma densityFactor_tendsto_one :
    Tendsto densityFactor atTop (nhds 1) := by
  have hstart : Tendsto (fun T : ℕ ↦ blockStart (T + 1)) atTop atTop :=
    tendsto_blockStart_atTop.comp (tendsto_add_atTop_nat 1)
  have hden : Tendsto (fun T : ℕ ↦ Real.log (blockStart (T + 1) : ℝ))
      atTop atTop := Erdos1211DensityNat.tendsto_log_nat_atTop.comp hstart
  have hzero : Tendsto
      (fun T : ℕ ↦ Real.log (blockStart 1 : ℝ) /
        Real.log (blockStart (T + 1) : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hone := (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
  have hevent :
      (fun T : ℕ ↦ 1 - Real.log (blockStart 1 : ℝ) /
        Real.log (blockStart (T + 1) : ℝ)) =ᶠ[atTop] densityFactor := by
    apply Filter.Eventually.of_forall
    intro T
    have hDne : Real.log (blockStart (T + 1) : ℝ) ≠ 0 :=
      (log_blockStart_pos (T + 1)).ne'
    have hdeneq : Real.log (blockStart (T + 1) : ℝ) =
        (T : ℝ) * Real.log 2 + Real.log (blockStart 1 : ℝ) := by
      rw [log_blockStart_formula (T + 1), log_blockStart_formula 1]
      push_cast
      ring
    rw [densityFactor]
    field_simp
    nlinarith
  simpa only [sub_zero] using hone.congr' hevent

lemma scaled_cutoffRatio_le_logRatio
    {α : ℕ → Fin 2} {sigma : Fin 2 → Set ℕ}
    (hcover : CoversShadowBlocks α sigma) (i : Fin 2) {T : ℕ} (hT : 0 < T) :
    Erdos1211Shadow.cutoffRatio (Erdos1211Shadow.shadow α i) T *
        densityFactor T ≤
      Erdos1211DensityNat.logRatio (sigma i) (blockStart (T + 1)) := by
  have hm := cutoffCount_mul_log_two_le_harmonicPrefix hcover i T
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hlog : 0 < Real.log (blockStart (T + 1) : ℝ) :=
    log_blockStart_pos (T + 1)
  have heq :
      Erdos1211Shadow.cutoffRatio (Erdos1211Shadow.shadow α i) T *
          densityFactor T =
        ((Erdos1211Shadow.cutoffCount
            (Erdos1211Shadow.shadow α i) T : ℝ) * Real.log 2) /
          Real.log (blockStart (T + 1) : ℝ) := by
    rw [Erdos1211Shadow.cutoffRatio, densityFactor]
    field_simp
  rw [heq, Erdos1211DensityNat.logRatio]
  exact div_le_div_of_nonneg_right hm hlog.le

lemma index_le_blockStart_succ (T : ℕ) : T ≤ blockStart (T + 1) := by
  have hpowSelf : T ≤ 2 ^ T := Nat.lt_two_pow_self.le
  have hexp : 2 ^ T ≤ shellScale (T + 1) := by
    change 2 ^ T ≤ 2 ^ (transferOffset + (T + 1))
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hscale : shellScale (T + 1) ≤ blockStart (T + 1) := by
    rw [blockStart]
    exact Nat.le_mul_of_pos_left _ lowerCoeff_pos
  exact hpowSelf.trans (hexp.trans hscale)

theorem upperDensity_le_upperLogDensity_of_blocks
    {α : ℕ → Fin 2} {sigma : Fin 2 → Set ℕ}
    (hcover : CoversShadowBlocks α sigma) (i : Fin 2) :
    Erdos1211Shadow.upperDensity (Erdos1211Shadow.shadow α i) ≤
      Erdos1211DensityNat.upperLogDensity (sigma i) := by
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  by_cases hc0 : c ≤ 0
  · exact hc0.trans (Erdos1211DensityNat.upperLogDensity_nonneg (sigma i))
  have hcpos : 0 < c := lt_of_not_ge hc0
  let D := Erdos1211Shadow.upperDensity (Erdos1211Shadow.shadow α i)
  let d := (c + D) / 2
  have hcD : c < D := hc
  have hcd : c < d := by dsimp only [d]; linarith
  have hdD : d < D := by dsimp only [d]; linarith
  have hdpos : 0 < d := hcpos.trans hcd
  have hquot : c / d < 1 := (div_lt_one hdpos).2 hcd
  have hfreqCut : ∃ᶠ T : ℕ in atTop,
      d < Erdos1211Shadow.cutoffRatio (Erdos1211Shadow.shadow α i) T := by
    exact Filter.frequently_lt_of_lt_limsup
      (Erdos1211Shadow.cutoffRatio_cobounded _) hdD
  have heventFactor : ∀ᶠ T : ℕ in atTop, c / d < densityFactor T :=
    densityFactor_tendsto_one.eventually (Ioi_mem_nhds hquot)
  have heventPos : ∀ᶠ T : ℕ in atTop, 0 < T :=
    Filter.eventually_atTop.2 ⟨1, fun T hT ↦ by omega⟩
  have hfreqScaled : ∃ᶠ T : ℕ in atTop,
      c ≤ Erdos1211DensityNat.logRatio (sigma i) (blockStart (T + 1)) := by
    refine (hfreqCut.and_eventually (heventFactor.and heventPos)).mono ?_
    intro T hTdata
    rcases hTdata with ⟨hcut, hfactor, hT⟩
    have hprod : c ≤
        Erdos1211Shadow.cutoffRatio (Erdos1211Shadow.shadow α i) T *
          densityFactor T := by
      have hcutNonneg := Erdos1211Shadow.cutoffRatio_nonneg
        (Erdos1211Shadow.shadow α i) T
      calc
        c = d * (c / d) := by field_simp
        _ ≤ Erdos1211Shadow.cutoffRatio (Erdos1211Shadow.shadow α i) T *
              densityFactor T :=
          mul_le_mul hcut.le hfactor.le (div_nonneg hcpos.le hdpos.le) hcutNonneg
    exact hprod.trans (scaled_cutoffRatio_le_logRatio hcover i hT)
  have hfreqDirect : ∃ᶠ N : ℕ in atTop,
      c ≤ Erdos1211DensityNat.logRatio (sigma i) N := by
    rw [Filter.frequently_atTop] at hfreqScaled ⊢
    intro N₀
    obtain ⟨T, hT, hcT⟩ := hfreqScaled N₀
    refine ⟨blockStart (T + 1), ?_, hcT⟩
    exact hT.trans (index_le_blockStart_succ T)
  exact Erdos1211DensityNat.le_upperLogDensity_of_frequently_le hfreqDirect

/-! ### Applying the finite rough-shell theorem -/

noncomputable def winningColor (chi : ℕ → Fin 2) (j : ℕ) : Fin 2 :=
  Classical.choose
    (Erdos1211Local.twoColor_shell_interval chi (largeEnough_shellScale j))

def localColorSet (chi : ℕ → Fin 2) (j : ℕ) : Finset ℕ :=
  (RoughShellCount.roughShell Erdos1211Local.roughness (shellScale j)).filter
    fun n ↦ chi n = winningColor chi j

lemma winningColor_spec (chi : ℕ → Fin 2) (j : ℕ) :
    Finset.Icc (Erdos1211Local.lowerEndpoint (shellScale j))
        (Erdos1211Local.upperEndpoint (shellScale j)) ⊆
      (localColorSet chi j).subsetSum := by
  exact Classical.choose_spec
    (Erdos1211Local.twoColor_shell_interval chi (largeEnough_shellScale j))

theorem coversShadowBlocks_winningColor
    (chi : ℕ → Fin 2) (sigma : Fin 2 → Set ℕ)
    (hembed : ∀ j : ℕ, (↑((localColorSet chi j).subsetSum) : Set ℕ) ⊆
      sigma (winningColor chi j)) :
    CoversShadowBlocks (winningColor chi) sigma := by
  intro i n hn
  obtain ⟨j, hj1, hjn, hnj, hcolor⟩ := hn
  intro x hx
  have hxlocal : x ∈ (localColorSet chi j).subsetSum :=
    winningColor_spec chi j (shadow_block_subset_local_interval hjn hnj hx)
  simpa only [hcolor] using hembed j hxlocal

theorem sharp_le_max_upperLogDensity
    (chi : ℕ → Fin 2) (sigma : Fin 2 → Set ℕ)
    (hembed : ∀ j : ℕ, (↑((localColorSet chi j).subsetSum) : Set ℕ) ⊆
      sigma (winningColor chi j)) :
    Erdos1211Dynamics.sharpConstant ≤
      max (Erdos1211DensityNat.upperLogDensity (sigma 0))
        (Erdos1211DensityNat.upperLogDensity (sigma 1)) := by
  have hblocks := coversShadowBlocks_winningColor chi sigma hembed
  calc
    Erdos1211Dynamics.sharpConstant ≤
        max
          (Erdos1211Shadow.upperDensity
            (Erdos1211Shadow.shadow (winningColor chi) 0))
          (Erdos1211Shadow.upperDensity
            (Erdos1211Shadow.shadow (winningColor chi) 1)) :=
      Erdos1211Shadow.interval_process (winningColor chi)
    _ ≤ max (Erdos1211DensityNat.upperLogDensity (sigma 0))
          (Erdos1211DensityNat.upperLogDensity (sigma 1)) := by
      exact max_le_max
        (upperDensity_le_upperLogDensity_of_blocks hblocks 0)
        (upperDensity_le_upperLogDensity_of_blocks hblocks 1)

end

end Erdos1211Transfer
