import Wikipedia.GreenTao.Parameters
import Wikipedia.GreenTao.Sieve.CyclicMajorant

/-!
# Assembly-facing prime-weight majorization

The pointwise Selberg majorization theorem reduces its substantive case to
two scalar inequalities: the sieve level lies below the represented prime,
and the scaled logarithm of that prime is at most
`log R / χ.normalizer`.

This file derives both inequalities from global bounds that are independent
of the residue `n`.  The remaining eventual parameter argument only has to
establish those four global bounds for `R = sieveLevel k N`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Real

theorem sieveExponent_lt_one {k : ℕ} (hk : 3 ≤ k) :
    sieveExponent k < 1 := by
  rw [sieveExponent]
  apply inv_lt_one_of_one_lt₀
  have hmax : 1 ≤ maxAPForms k :=
    maxAPForms_pos hk
  exact_mod_cast (show 1 < 100 * maxAPForms k by omega)

/-- The chosen sublinear sieve level eventually lies below the left endpoint
of the localization interval. -/
theorem eventually_sieveLevel_lt_div_sixtyFour
    {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ N : ℕ in atTop,
      sieveLevel k N < N / 64 := by
  have hgap : 0 < 1 - sieveExponent k := by
    linarith [sieveExponent_lt_one hk]
  have hratio :
      Tendsto
        (fun N : ℕ =>
          (N : ℝ) ^ (sieveExponent k - 1))
        atTop (nhds 0) := by
    have h :=
      (tendsto_rpow_neg_atTop hgap).comp
        tendsto_natCast_atTop_atTop
    convert h using 1
    funext N
    congr 1
    ring
  have hratioSmall :
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ (sieveExponent k - 1) <
          (1 : ℝ) / 128 :=
    (tendsto_order.1 hratio).2 _ (by norm_num)
  filter_upwards [
    hratioSmall,
    eventually_two_le_sieveLevel hk,
    eventually_gt_atTop 128] with N hsmall hRtwo hN
  have hNposReal : 0 < (N : ℝ) := by
    positivity
  have hrpow :
      (N : ℝ) ^ sieveExponent k <
        (N : ℝ) / 128 := by
    calc
      (N : ℝ) ^ sieveExponent k =
          (N : ℝ) ^
            ((sieveExponent k - 1) + 1) := by
        apply congrArg (fun z : ℝ => (N : ℝ) ^ z)
        ring
      _ =
          (N : ℝ) ^ (sieveExponent k - 1) *
            (N : ℝ) := by
        rw [Real.rpow_add hNposReal, Real.rpow_one]
      _ < ((1 : ℝ) / 128) * (N : ℝ) :=
        mul_lt_mul_of_pos_right hsmall hNposReal
      _ = (N : ℝ) / 128 := by ring
  have hfloor :
      (sieveLevel k N : ℝ) ≤
        (N : ℝ) ^ sieveExponent k := by
    exact Nat.floor_le
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hscaledReal :
      (128 * sieveLevel k N : ℝ) < (N : ℝ) := by
    nlinarith
  have hscaledNat :
      128 * sieveLevel k N < N := by
    exact_mod_cast hscaledReal
  omega

/-- The natural floor in `sieveLevel` loses only a negligible additive
constant in the logarithm.  Eventually at least half of the nominal
`sieveExponent * log N` remains. -/
theorem eventually_sieveExponent_half_mul_log_le_log_sieveLevel
    {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ N : ℕ in atTop,
      sieveExponent k / 2 * log (N : ℝ) ≤
        log (sieveLevel k N : ℝ) := by
  have hexponent : 0 < sieveExponent k :=
    sieveExponent_pos hk
  have hlog :
      Tendsto (fun N : ℕ => log (N : ℝ))
        atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge :
      ∀ᶠ N : ℕ in atTop,
        2 * log 2 / sieveExponent k ≤
          log (N : ℝ) :=
    hlog.eventually
      (eventually_ge_atTop
        (2 * log 2 / sieveExponent k))
  filter_upwards [
    hlogLarge,
    eventually_two_le_sieveLevel hk,
    eventually_gt_atTop 0] with N hlarge hRtwo hN
  have hNposReal : 0 < (N : ℝ) := by
    positivity
  have hrpowPos :
      0 < (N : ℝ) ^ sieveExponent k :=
    Real.rpow_pos_of_pos hNposReal _
  have hrpowTwo :
      (2 : ℝ) ≤ (N : ℝ) ^ sieveExponent k := by
    have htwoFloor :
        (2 : ℝ) ≤ (sieveLevel k N : ℝ) := by
      exact_mod_cast hRtwo
    exact htwoFloor.trans
      (Nat.floor_le hrpowPos.le)
  have hfloor :
      (N : ℝ) ^ sieveExponent k - 1 <
        (sieveLevel k N : ℝ) := by
    simpa only [sieveLevel] using
      (Nat.sub_one_lt_floor
        ((N : ℝ) ^ sieveExponent k))
  have hhalfFloor :
      (N : ℝ) ^ sieveExponent k / 2 ≤
        (sieveLevel k N : ℝ) := by
    have :
        (N : ℝ) ^ sieveExponent k / 2 ≤
          (N : ℝ) ^ sieveExponent k - 1 := by
      linarith
    exact this.trans hfloor.le
  have hlogFloor :
      log ((N : ℝ) ^ sieveExponent k / 2) ≤
        log (sieveLevel k N : ℝ) :=
    log_le_log (div_pos hrpowPos (by norm_num))
      hhalfFloor
  have hlogIdentity :
      log ((N : ℝ) ^ sieveExponent k / 2) =
        sieveExponent k * log (N : ℝ) - log 2 := by
    rw [Real.log_div hrpowPos.ne' (by norm_num),
      Real.log_rpow hNposReal]
  have hlarge' :
      2 * log 2 ≤
        log (N : ℝ) * sieveExponent k :=
    (div_le_iff₀ hexponent).mp hlarge
  rw [hlogIdentity] at hlogFloor
  nlinarith

/-- A fixed affine coefficient and shift are absorbed by `N²` once their
sum is at most `N`. -/
theorem affine_mul_add_le_sq
    {W b N : ℕ} (hN : 1 ≤ N) (hWB : W + b ≤ N) :
    W * N + b ≤ N ^ 2 := by
  calc
    W * N + b ≤ W * N + b * N := by
      exact Nat.add_le_add_left
        (Nat.le_mul_of_pos_right b (Nat.zero_lt_of_lt hN))
        (W * N)
    _ = (W + b) * N := by ring
    _ ≤ N * N := Nat.mul_le_mul_right N hWB
    _ = N ^ 2 := by ring

/-- Global numerical conditions sufficient for pointwise domination by the
standard smooth Selberg majorant.

The upper bound `W * N + b ≤ N²` controls every W-tricked value in a complete
residue system.  The lower logarithmic bound reserves a factor of two beyond
what is needed after using `primeScale ≤ sieveExponent / (8 * normalizer)`.
-/
theorem wTrickedPrimeWeight_le_sieveMajorant_of_bounds
    {k N W b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 3 ≤ k)
    (hN : 1 ≤ N)
    (hW : 0 < W)
    (hRtwo : 2 ≤ sieveLevel k N)
    (hRbelow : sieveLevel k N < N / 64)
    (hvalueUpper : W * N + b ≤ N ^ 2)
    (hlogLower :
      sieveExponent k / 2 * log (N : ℝ) ≤
        log (sieveLevel k N : ℝ)) :
    ∀ n : ZMod N,
      wTrickedPrimeWeight
          (primeScale k χ.normalizer) W b n ≤
        χ.wTrickedMajorant (sieveLevel k N) W b n := by
  apply wTrickedPrimeWeight_le_majorant
    χ.normalizer_pos (by omega) hW χ.toFun
    χ.value_zero χ.zero_of_one_le
  intro n hn hp
  have hnBounds := mem_greenTaoInterval.mp hn
  have hlevelValue :
      sieveLevel k N < wTrickedValue W b n := by
    calc
      sieveLevel k N < N / 64 := hRbelow
      _ ≤ n.val := hnBounds.1
      _ ≤ W * n.val :=
        Nat.le_mul_of_pos_left n.val hW
      _ ≤ W * n.val + b := Nat.le_add_right _ _
      _ = wTrickedValue W b n := rfl
  refine ⟨hlevelValue, ?_⟩
  have hnVal : n.val ≤ N := (n.val_lt).le
  have hrepresentedUpper :
      wTrickedValue W b n ≤ N ^ 2 := by
    calc
      wTrickedValue W b n = W * n.val + b := rfl
      _ ≤ W * N + b :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_left W hnVal) b
      _ ≤ N ^ 2 := hvalueUpper
  have hrepresentedUpperReal :
      (wTrickedValue W b n : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast hrepresentedUpper
  have hrepresentedPosReal :
      0 < (wTrickedValue W b n : ℝ) := by
    exact_mod_cast hp.pos
  have hlogValue :
      log (wTrickedValue W b n : ℝ) ≤
        2 * log (N : ℝ) := by
    calc
      log (wTrickedValue W b n : ℝ) ≤
          log ((N : ℝ) ^ 2) :=
        log_le_log hrepresentedPosReal hrepresentedUpperReal
      _ = 2 * log (N : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hlogN : 0 ≤ log (N : ℝ) :=
    log_nonneg (by exact_mod_cast hN)
  have hscaleNonneg :
      0 ≤ primeScale k χ.normalizer :=
    primeScale_nonneg hk χ.normalizer_pos
  have hexponentNonneg :
      0 ≤ sieveExponent k :=
    (sieveExponent_pos hk).le
  calc
    primeScale k χ.normalizer *
          log (wTrickedValue W b n : ℝ) ≤
        primeScale k χ.normalizer *
          (2 * log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogValue hscaleNonneg
    _ ≤
        (sieveExponent k / (8 * χ.normalizer)) *
          (2 * log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (primeScale_le_sieveExponent_div k χ.normalizer)
        (mul_nonneg (by norm_num) hlogN)
    _ =
        (sieveExponent k / 4 * log (N : ℝ)) /
          χ.normalizer := by
      ring
    _ ≤
        (sieveExponent k / 2 * log (N : ℝ)) /
          χ.normalizer := by
      apply (div_le_div_iff_of_pos_right χ.normalizer_pos).2
      nlinarith [mul_nonneg hexponentNonneg hlogN]
    _ ≤
        log (sieveLevel k N : ℝ) /
          χ.normalizer :=
      (div_le_div_iff_of_pos_right χ.normalizer_pos).2
        hlogLower

/-- Convenient specialization in which the affine upper bound follows from
the single eventual threshold `W + b ≤ N`. -/
theorem wTrickedPrimeWeight_le_sieveMajorant_of_add_le
    {k N W b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 3 ≤ k)
    (hN : 1 ≤ N)
    (hW : 0 < W)
    (hWB : W + b ≤ N)
    (hRtwo : 2 ≤ sieveLevel k N)
    (hRbelow : sieveLevel k N < N / 64)
    (hlogLower :
      sieveExponent k / 2 * log (N : ℝ) ≤
        log (sieveLevel k N : ℝ)) :
    ∀ n : ZMod N,
      wTrickedPrimeWeight
          (primeScale k χ.normalizer) W b n ≤
        χ.wTrickedMajorant (sieveLevel k N) W b n :=
  wTrickedPrimeWeight_le_sieveMajorant_of_bounds
    χ hk hN hW hRtwo hRbelow
    (affine_mul_add_le_sq hN hWB) hlogLower

/-- Threshold form of eventual pointwise majorization for fixed `W` and
shift `b`.  This is the form consumed by the final nested parameter
selection after the W-trick cutoff has been fixed. -/
theorem exists_threshold_wTrickedPrimeWeight_le_sieveMajorant
    (χ : SmoothSieveCutoff)
    {k W : ℕ} (hk : 3 ≤ k) (hW : 0 < W)
    (b : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ hN : 0 < N,
      letI : NeZero N := ⟨hN.ne'⟩
      ∀ n : ZMod N,
        wTrickedPrimeWeight
            (primeScale k χ.normalizer) W b n ≤
          χ.wTrickedMajorant (sieveLevel k N) W b n := by
  have heventually :
      ∀ᶠ N : ℕ in atTop, ∀ hN : 0 < N,
        letI : NeZero N := ⟨hN.ne'⟩
        ∀ n : ZMod N,
          wTrickedPrimeWeight
              (primeScale k χ.normalizer) W b n ≤
            χ.wTrickedMajorant
              (sieveLevel k N) W b n := by
    filter_upwards [
      eventually_ge_atTop (W + b),
      eventually_ge_atTop 1,
      eventually_two_le_sieveLevel hk,
      eventually_sieveLevel_lt_div_sixtyFour hk,
      eventually_sieveExponent_half_mul_log_le_log_sieveLevel hk
    ] with N hWB hNone hRtwo hRbelow hlogLower
    intro hN
    let : NeZero N := ⟨hN.ne'⟩
    exact
      wTrickedPrimeWeight_le_sieveMajorant_of_add_le
        χ hk hNone hW hWB hRtwo hRbelow hlogLower
  exact eventually_atTop.1 heventually

/-- The same eventual majorization with the global cyclic Selberg majorant.

This is the assembly-facing version useful for the linear-forms estimate:
the prime weight is still localized for the final unwrapping argument, but
the majorant remains a pure Selberg weight on every residue. -/
theorem exists_threshold_wTrickedPrimeWeight_le_cyclicMajorant
    (χ : SmoothSieveCutoff)
    {k W : ℕ} (hk : 3 ≤ k) (hW : 0 < W)
    (b : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ hN : 0 < N,
      letI : NeZero N := ⟨hN.ne'⟩
      ∀ n : ZMod N,
        wTrickedPrimeWeight
            (primeScale k χ.normalizer) W b n ≤
          χ.cyclicMajorant (sieveLevel k N) W b n := by
  obtain ⟨N₀, hlocalized⟩ :=
    exists_threshold_wTrickedPrimeWeight_le_sieveMajorant
      χ hk hW b
  obtain ⟨N₁, hlevel⟩ :=
    eventually_atTop.1 (eventually_two_le_sieveLevel hk)
  refine ⟨max N₀ N₁, ?_⟩
  intro N hNlarge hNpos
  let : NeZero N := ⟨hNpos.ne'⟩
  apply
    wTrickedPrimeWeight_le_cyclicMajorant_of_le_localized
      χ
      (by
        have htwo : 2 ≤ sieveLevel k N :=
          hlevel N ((le_max_right N₀ N₁).trans hNlarge)
        omega)
  exact
    hlocalized N ((le_max_left N₀ N₁).trans hNlarge)
      hNpos

end Wikipedia.SzemeredisTheorem
