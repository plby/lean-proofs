/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.NibbleBounds
import Mathlib

/-!
# The exponential union bound for the concrete nibble

This file proves that the common score isolated in `NibbleBounds` grows as
a fixed positive power of the ground-set size.  It then absorbs the
polynomial number of stopped barriers.
-/

namespace Erdos722.NibbleTail

open Filter Finset
open scoped Topology Real
open Erdos722.Asymptotics
open Erdos722.BinomialBounds
open Erdos722.NibbleProfiles
open Erdos722.NibbleConcrete
open Erdos722.NibbleAsymptotic
open Erdos722.NibbleBarrier
open Erdos722.NibbleBounds
open Erdos722.NibbleBasics
open Erdos722.NibbleInstantiation
open Erdos722.FiniteFreedman
open Erdos722.Typicality

noncomputable section

variable {n q r : ℕ}

lemma concentration_exponent_lt_one (hrq : r ≤ q) :
    (((3 * K q r : ℕ) : ℝ) / den q r) * (10 * K q r - 1) + 1 / 12 < 1 := by
  have hK : 0 < K q r := K_pos hrq
  have hden : (den q r : ℝ) = 36 * (K q r : ℝ) ^ 2 := by
    unfold den
    push_cast
    ring
  rw [hden]
  have hKR : (0 : ℝ) < K q r := by exact_mod_cast hK
  push_cast
  have heq : (3 * (K q r : ℝ)) / (36 * (K q r : ℝ) ^ 2) *
        (10 * (K q r : ℝ) - 1) + 1 / 12 =
      11 / 12 - 1 / (12 * (K q r : ℝ)) := by
    field_simp
    ring
  rw [heq]
  have hpos : (0 : ℝ) < 1 / (12 * (K q r : ℝ)) := by positivity
  linarith

theorem eventually_rpow_le_concentrationScore (hrq : r ≤ q) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 / 12 : ℝ) ≤ concentrationScore n q r := by
  let a : ℝ := 1 / 12
  let e : ℝ := (((3 * K q r : ℕ) : ℝ) / den q r) *
      (10 * K q r - 1) + a
  let M : ℝ := (scaleMultiplier : ℝ) ^ (10 * K q r - 1)
  let C : ℝ := scoreConstant q r * M
  have he : e < 1 := by
    simpa [e, a] using concentration_exponent_lt_one hrq
  have hdom := eventually_const_mul_rpow_le_rpow
    (a := e) (b := (1 : ℝ)) (C := C) he (by
      dsimp [C, M, scoreConstant]
      positivity)
  have hscalePos := (scale_tendsto hrq).eventually (eventually_ge_atTop 1)
  filter_upwards [hdom, eventually_ge_atTop 1, hscalePos] with n hdom hn hTpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hTpow := pow_le_pow_left₀ (Nat.cast_nonneg (scale n q r))
    (scale_cast_le_rpow n q r) (10 * K q r - 1)
  have hQcast : ((10 * K q r - 1 : ℕ) : ℝ) =
      10 * (K q r : ℝ) - 1 := by
    rw [Nat.cast_sub (by
      have := K_pos hrq
      omega : 1 ≤ 10 * K q r)]
    push_cast
    rfl
  have hTpow' : (scale n q r : ℝ) ^ (10 * K q r - 1) ≤
      M * (n : ℝ) ^
        ((((3 * K q r : ℕ) : ℝ) / den q r) * (10 * K q r - 1)) := by
    calc
      _ ≤ ((scaleMultiplier : ℝ) *
          (n : ℝ) ^ (((3 * K q r : ℕ) : ℝ) / den q r)) ^
          (10 * K q r - 1) := hTpow
      _ = (scaleMultiplier : ℝ) ^ (10 * K q r - 1) *
          ((n : ℝ) ^ (((3 * K q r : ℕ) : ℝ) / den q r)) ^
            (10 * K q r - 1) := by rw [mul_pow]
      _ = _ := by
        dsimp [M]
        congr 1
        rw [← Real.rpow_natCast, Real.rpow_mul hnR.le, hQcast]
  have hprod : (n : ℝ) ^ a *
      (scoreConstant q r * (scale n q r : ℝ) ^ (10 * K q r - 1)) ≤
      C * (n : ℝ) ^ e := by
    have hscoreC : 0 ≤ scoreConstant q r := by
      unfold scoreConstant
      positivity
    calc
      _ ≤ (n : ℝ) ^ a * (scoreConstant q r *
          (M * (n : ℝ) ^
            ((((3 * K q r : ℕ) : ℝ) / den q r) *
              (10 * K q r - 1)))) := by gcongr
      _ = C * (n : ℝ) ^ e := by
        rw [show (n : ℝ) ^ a * (scoreConstant q r *
              (M * (n : ℝ) ^
                ((((3 * K q r : ℕ) : ℝ) / den q r) *
                  (10 * K q r - 1)))) =
            C * ((n : ℝ) ^ a *
              (n : ℝ) ^ ((((3 * K q r : ℕ) : ℝ) / den q r) *
                (10 * K q r - 1))) by
          dsimp [C]
          ring]
        congr 1
        rw [← Real.rpow_add hnR]
        congr 1
        dsimp [e]
        ring
  have hmain : (n : ℝ) ^ a *
      (scoreConstant q r * (scale n q r : ℝ) ^ (10 * K q r - 1)) ≤ n := by
    calc
      _ ≤ C * (n : ℝ) ^ e := hprod
      _ ≤ (n : ℝ) ^ (1 : ℝ) := hdom
      _ = n := by simp
  unfold concentrationScore
  have hden : 0 < scoreConstant q r *
      (scale n q r : ℝ) ^ (10 * K q r - 1) := by
    have hTreal : (0 : ℝ) < scale n q r := by exact_mod_cast hTpos
    have hSC : 0 < scoreConstant q r := by
      have hKR : (0 : ℝ) < K q r := by exact_mod_cast K_pos hrq
      have hfac : (0 : ℝ) < (q - r).factorial := by
        exact_mod_cast Nat.factorial_pos (q - r)
      unfold scoreConstant
      positivity
    exact mul_pos hSC (pow_pos hTreal _)
  exact (le_div_iff₀ hden).2 (by simpa [a] using hmain)

lemma card_barrier_depth_le
    (hr : 0 < r) (hn : 1 ≤ n)
    {host : Finset (Finset (Fin n))}
    (hhost : host ⊆ uniformEdges n r) :
    Fintype.card (BarrierIndex host r × Fin (depth host.card n q r + 1)) ≤
      16 * n ^ (2 * r) := by
  have hg : host.card ≤ n ^ r := by
    calc
      host.card ≤ (uniformEdges n r).card := Finset.card_le_card hhost
      _ = Nat.choose n r := by simp [uniformEdges]
      _ ≤ n ^ r := Nat.choose_le_pow n r
  have hpow : 1 ≤ n ^ r := one_le_pow₀ hn
  have hface : Nat.choose n (r - 1) ≤ n ^ r := by
    calc
      Nat.choose n (r - 1) ≤ n ^ (r - 1) := Nat.choose_le_pow n (r - 1)
      _ ≤ n ^ r := Nat.pow_le_pow_right hn (by omega)
  have hbarrier : Fintype.card (BarrierIndex host r) ≤ 5 * n ^ r := by
    have heq : Fintype.card (BarrierIndex host r) =
        2 * host.card + 2 + Nat.choose n (r - 1) := by
      simp [uniformEdges]
      omega
    rw [heq]
    omega
  have hd : depth host.card n q r + 1 ≤ 2 * n ^ r := by
    have hdepth : depth host.card n q r ≤ host.card := by
      unfold depth
      exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    omega
  rw [Fintype.card_prod, Fintype.card_fin]
  calc
    Fintype.card (BarrierIndex host r) * (depth host.card n q r + 1) ≤
        (5 * n ^ r) * (2 * n ^ r) := Nat.mul_le_mul hbarrier hd
    _ = 10 * (n ^ r) ^ 2 := by ring
    _ ≤ 16 * (n ^ r) ^ 2 := Nat.mul_le_mul_right _ (by norm_num)
    _ = 16 * n ^ (2 * r) := by
      rw [← pow_mul]
      congr 2
      omega

theorem eventually_barrier_exponential_bound
    (hr : 0 < r) (hrq : r ≤ q) :
    ∀ᶠ n : ℕ in atTop, ∀ (host : Finset (Finset (Fin n))),
      host ⊆ uniformEdges n r →
      (Fintype.card
          (BarrierIndex host r × Fin (depth host.card n q r + 1)) : ℝ) *
        Real.exp (-concentrationScore n q r) < 1 := by
  have ha : (0 : ℝ) < 1 / 12 := by norm_num
  have hdecay := Erdos722.Reserve.tendsto_pow_mul_exp_neg_rpow_atTop
    (2 * r) ha (by norm_num : (0 : ℝ) < 1)
  have hconst : Tendsto
      (fun x : ℝ ↦ 16 * (x ^ (2 * r) * Real.exp (-x ^ (1 / 12 : ℝ))))
      atTop (nhds 0) := by
    have hsixteen : Tendsto (fun _ : ℝ ↦ (16 : ℝ)) atTop (nhds 16) :=
      tendsto_const_nhds
    simpa using hsixteen.mul hdecay
  have hnat := hconst.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop,
      16 * ((n : ℝ) ^ (2 * r) *
        Real.exp (-(n : ℝ) ^ (1 / 12 : ℝ))) < 1 :=
    (tendsto_order.1 hnat).2 _ (by norm_num)
  have hscore := eventually_rpow_le_concentrationScore (q := q) (r := r) hrq
  filter_upwards [hsmall, hscore, eventually_ge_atTop 1] with n hsmall hscore hn
  intro host hhost
  have hcardNat := card_barrier_depth_le (q := q) hr hn hhost
  have hcard : (Fintype.card
        (BarrierIndex host r × Fin (depth host.card n q r + 1)) : ℝ) ≤
      16 * (n : ℝ) ^ (2 * r) := by
    exact_mod_cast hcardNat
  have hexp : Real.exp (-concentrationScore n q r) ≤
      Real.exp (-(n : ℝ) ^ (1 / 12 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    (Fintype.card
          (BarrierIndex host r × Fin (depth host.card n q r + 1)) : ℝ) *
        Real.exp (-concentrationScore n q r) ≤
      (16 * (n : ℝ) ^ (2 * r)) *
        Real.exp (-(n : ℝ) ^ (1 / 12 : ℝ)) := by
      exact mul_le_mul hcard hexp (Real.exp_pos _).le (by positivity)
    _ = 16 * ((n : ℝ) ^ (2 * r) *
        Real.exp (-(n : ℝ) ^ (1 / 12 : ℝ))) := by ring
    _ < 1 := hsmall

/-- A host containing more than half of the complete `r`-graph eventually
dominates any fixed multiple of `n T`; this supplies both the face-jump
estimate and the elementary stopping inequalities. -/
theorem eventually_const_n_mul_scale_le_host
    (hr : 1 < r) (hrq : r ≤ q) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ n : ℕ in atTop, ∀ g : ℕ,
      Nat.choose n r / 2 < g →
      C₀ * (n : ℝ) * scale n q r ≤ g := by
  let a : ℝ := ((3 * K q r : ℕ) : ℝ) / den q r
  let M : ℝ := scaleMultiplier
  have hK : 0 < K q r := K_pos hrq
  have hden : (den q r : ℝ) = 36 * (K q r : ℝ) ^ 2 := by
    unfold den
    push_cast
    ring
  have haSmall : a < 1 := by
    dsimp [a]
    rw [hden]
    have hKR : (0 : ℝ) < K q r := by exact_mod_cast hK
    push_cast
    have heq : (3 * (K q r : ℝ)) / (36 * (K q r : ℝ) ^ 2) =
        1 / (12 * (K q r : ℝ)) := by field_simp; ring
    rw [heq]
    have hle : (1 : ℝ) ≤ K q r := by exact_mod_cast hK
    have : 1 / (12 * (K q r : ℝ)) ≤ 1 / 12 := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 12 * K q r)
        (by norm_num : (0 : ℝ) < 12)).2
      nlinarith
    linarith
  have har : 1 + a < (r : ℝ) := by
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hdom := eventually_const_mul_rpow_le_rpow
    (a := 1 + a) (b := (r : ℝ))
    (C := 2 * C₀ * M * 2 ^ r * r.factorial) har (by positivity)
  filter_upwards [hdom, eventually_ge_atTop (2 * r),
      eventually_ge_atTop 1] with n hdom hnlarge hn
  intro g hg
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hT := scale_cast_le_rpow n q r
  have hprod : 2 * C₀ * (n : ℝ) * scale n q r ≤
      2 * C₀ * M * (n : ℝ) ^ (1 + a) := by
    calc
      _ ≤ 2 * C₀ * (n : ℝ) *
          (scaleMultiplier * (n : ℝ) ^ a) := by gcongr
      _ = 2 * C₀ * M * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ a) := by
        dsimp [M]
        simp
        ring
      _ = _ := by rw [Real.rpow_add hnR]
  have hchooseLower := half_pow_div_factorial_le_choose_sub n 0 r (by omega)
  have htoChoose : 2 * C₀ * M * (n : ℝ) ^ (1 + a) ≤
      Nat.choose n r := by
    apply hchooseLower.trans'
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < r.factorial)).2
    calc
      2 * C₀ * M * (n : ℝ) ^ (1 + a) * r.factorial ≤
          (n : ℝ) ^ r / 2 ^ r := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ r)).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hdom
      _ = ((n : ℝ) / 2) ^ r := by rw [div_pow]
  have hgNat : Nat.choose n r ≤ 2 * g := by omega
  have hgReal : (Nat.choose n r : ℝ) / 2 ≤ g := by
    have : (Nat.choose n r : ℝ) ≤ 2 * g := by exact_mod_cast hgNat
    linarith
  calc
    C₀ * (n : ℝ) * scale n q r ≤ (Nat.choose n r : ℝ) / 2 := by
      linarith [hprod.trans htoChoose]
    _ ≤ g := hgReal

theorem eventually_const_scale_pow_le_n
    (hrq : r ≤ q) (m : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hexp : (((3 * K q r : ℕ) : ℝ) / den q r) * m < 1) :
    ∀ᶠ n : ℕ in atTop,
      C₀ * (scale n q r : ℝ) ^ m ≤ n := by
  let a : ℝ := (((3 * K q r : ℕ) : ℝ) / den q r) * m
  let M : ℝ := (scaleMultiplier : ℝ) ^ m
  have hdom := eventually_const_mul_rpow_le_rpow
    (a := a) (b := (1 : ℝ)) (C := C₀ * M)
    (by simpa [a] using hexp) (by positivity)
  filter_upwards [hdom, eventually_ge_atTop 1] with n hdom hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hTpow := pow_le_pow_left₀ (Nat.cast_nonneg (scale n q r))
    (scale_cast_le_rpow n q r) m
  calc
    C₀ * (scale n q r : ℝ) ^ m ≤
        C₀ * ((scaleMultiplier : ℝ) *
          (n : ℝ) ^ (((3 * K q r : ℕ) : ℝ) / den q r)) ^ m := by gcongr
    _ = C₀ * M * (n : ℝ) ^ a := by
      rw [mul_pow]
      dsimp [M, a]
      rw [show C₀ * ((scaleMultiplier : ℝ) ^ m *
            ((n : ℝ) ^ (((3 * K q r : ℕ) : ℝ) / den q r)) ^ m) =
          C₀ * (scaleMultiplier : ℝ) ^ m *
            (((n : ℝ) ^ (((3 * K q r : ℕ) : ℝ) / den q r)) ^ m) by ring]
      congr 1
      rw [← Real.rpow_natCast, Real.rpow_mul hnR.le]
    _ ≤ (n : ℝ) ^ (1 : ℝ) := hdom
    _ = n := by simp

lemma scale_three_exponent_lt_one (hrq : r ≤ q) :
    (((3 * K q r : ℕ) : ℝ) / den q r) * 3 < 1 := by
  have hK : 0 < K q r := K_pos hrq
  have hden : (den q r : ℝ) = 36 * (K q r : ℝ) ^ 2 := by
    unfold den
    push_cast
    ring
  rw [hden]
  have hKR : (0 : ℝ) < K q r := by exact_mod_cast hK
  push_cast
  have heq : (3 * (K q r : ℝ)) / (36 * (K q r : ℝ) ^ 2) * 3 =
      1 / (4 * (K q r : ℝ)) := by field_simp; ring
  rw [heq]
  have hle : (1 : ℝ) ≤ K q r := by exact_mod_cast hK
  have hquarter : 1 / (4 * (K q r : ℝ)) ≤ 1 / 4 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * K q r)
      (by norm_num : (0 : ℝ) < 4)).2
    nlinarith
  linarith

/-- The complete asymptotic clique-removal theorem for every sufficiently
regular auxiliary clique family. -/
theorem eventually_exists_boundedNibble
    (hr : 1 < r) (hrq : r < q) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (host H : Finset (Finset (Fin n))),
        host ⊆ uniformEdges n r →
        (∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host) →
        (∀ e ∈ host,
          |((H.filter fun Q ↦ e ⊆ Q).card : ℝ) - centerDegree n q r| <
            Erdos722.NibbleInstantiation.initialError n q r / 4) →
        Nat.choose n r / 2 < host.card →
        Erdos722.NibbleBasics.HasBoundedNibble host q r
          (Erdos722.CoverAsymptotic.coverDen q r)
          (Erdos722.CoverAsymptotic.coverLeaveNumerator q r) := by
  let K₀ := K q r
  let P := 5 * K₀ - 1
  let Nconst : ℝ := 4 + 8 * (K₀ : ℝ) * (K₀ + 1)
  let Rconst : ℕ :=
    6 * (4 * K₀ - 1) * K₀ * 2 ^ (4 * K₀ - 2)
  have hTlarge := (scale_tendsto hrq.le).eventually
    (eventually_ge_atTop (64 * K₀))
  have hpower := eventually_scale_pow_K_le_centerDegree hrq
  have hhostScale := eventually_const_scaleProfile_le_host
    (by omega : 0 < r) hrq.le
    (2 * (K₀ : ℝ) ^ 2 * (K₀ - 1 : ℕ)) (by positivity)
  have hcliqueWide := eventually_const_scaleProfile_le_host
    (by omega : 0 < r) hrq.le (64 * (K₀ : ℝ) ^ 2) (by positivity)
  have hedge := eventually_const_codegree_le_initial_error hrq
    (48 * (K₀ : ℝ) ^ 2) (by positivity)
  have hmarginRaw := eventually_const_codegree_le_initial_error hrq
    Nconst (by dsimp [Nconst]; positivity)
  have hnscale := eventually_const_n_mul_scale_le_host
    hr hrq.le 2 (by norm_num)
  have hface := eventually_const_scale_pow_le_n hrq.le 3
    (12 * (K₀ : ℝ)) (by positivity) (scale_three_exponent_lt_one hrq.le)
  have hterminal := Erdos722.NibbleTerminal.eventually_faceCap_terminal_le_coverLeaveCap
    hr hrq
  have hexponential := eventually_barrier_exponential_bound
    (q := q) (by omega : 0 < r) hrq.le
  filter_upwards [hTlarge, hpower, hhostScale, hcliqueWide, hedge,
      hmarginRaw, hnscale, hface, hterminal, hexponential,
      eventually_ge_atTop (max (2 * q) (max (K₀ + 1) Rconst))]
    with n hT hpower hhostScale hcliqueWide hedge hmarginRaw hnscale
      hface hterminal hexponential hnlarge
  intro host H hhost hH hregular hhalf
  have hnq : 2 * q ≤ n := (le_max_left _ _).trans hnlarge
  have hnK : K₀ + 1 ≤ n :=
    (le_max_right (2 * q) (max (K₀ + 1) Rconst)).trans hnlarge |>.trans'
      (le_max_left _ _)
  have hnRconst : Rconst ≤ n :=
    (le_max_right (2 * q) (max (K₀ + 1) Rconst)).trans hnlarge |>.trans'
      (le_max_right _ _)
  have hnpos : 0 < n := by omega
  have hKthree : 3 ≤ K₀ := K_ge_three hr hrq
  have hKpos : 0 < K₀ := by omega
  have hTpos : 0 < scale n q r := by omega
  have hTtwo : 2 ≤ scale n q r := by omega
  have hTeight : 8 ≤ scale n q r := by omega
  have hg : 0 < host.card := by omega
  have hgR : (0 : ℝ) < host.card := by exact_mod_cast hg
  have hTR : (0 : ℝ) < scale n q r := by exact_mod_cast hTpos
  have hnscale' : (2 : ℝ) * n * scale n q r ≤ host.card := hnscale _ hhalf
  have hng : (n : ℝ) ≤ host.card := by
    have hTone : (1 : ℝ) ≤ scale n q r := by exact_mod_cast (show 1 ≤ scale n q r by omega)
    nlinarith [mul_nonneg (Nat.cast_nonneg n)
      (sub_nonneg.mpr hTone)]
  have hDone : (1 : ℝ) ≤ centerDegree n q r := by
    calc
      (1 : ℝ) ≤ (scale n q r : ℝ) ^ K q r := one_le_pow₀
        (by exact_mod_cast (show 1 ≤ scale n q r by omega))
      _ ≤ centerDegree n q r := hpower
  have hDpos : 0 < centerDegree n q r := lt_of_lt_of_le (by norm_num) hDone
  have htarget : stopTarget host.card n q r ≤ host.card := by
    have hKg : K₀ ≤ host.card := by
      have : (K₀ : ℝ) ≤ host.card := by
        have hnKR : (K₀ : ℝ) + 1 ≤ n := by exact_mod_cast hnK
        nlinarith
      exact_mod_cast this
    have hfourN : (4 : ℝ) * n ≤ host.card := by
      have hTge : (2 : ℝ) ≤ scale n q r := by exact_mod_cast hTtwo
      nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hTge)]
    have hratio : (host.card : ℝ) / scale n q r ≤
        (host.card - K₀ : ℕ) := by
      rw [Nat.cast_sub hKg]
      have hhalfG : (host.card : ℝ) / scale n q r ≤ host.card / 2 := by
        apply (div_le_div_iff₀ hTR (by norm_num : (0 : ℝ) < 2)).2
        nlinarith [mul_nonneg (Nat.cast_nonneg host.card)
          (sub_nonneg.mpr (by exact_mod_cast hTtwo : (2 : ℝ) ≤ scale n q r))]
      have hKhalf : (K₀ : ℝ) ≤ host.card / 2 := by
        have hnKR : (K₀ : ℝ) + 1 ≤ n := by exact_mod_cast hnK
        nlinarith
      linarith
    have hceil : Nat.ceil ((host.card : ℝ) / scale n q r) ≤
        host.card - K₀ := Nat.ceil_le.mpr hratio
    unfold stopTarget
    omega
  have hremaining :
      (6 : ℝ) * (4 * (K q r : ℝ) - 1) * K q r *
          (2 : ℝ) ^ (4 * K q r - 2) ≤ stopTarget host.card n q r := by
    have hratioLower : (Rconst : ℝ) ≤
        (host.card : ℝ) / scale n q r := by
      apply (le_div_iff₀ hTR).2
      have hnRreal : (Rconst : ℝ) ≤ n := by exact_mod_cast hnRconst
      nlinarith
    have hceilReal : (Rconst : ℝ) ≤
        (Nat.ceil ((host.card : ℝ) / scale n q r) : ℝ) :=
      hratioLower.trans (Nat.le_ceil _)
    have hceil : Rconst ≤ Nat.ceil ((host.card : ℝ) / scale n q r) := by
      exact_mod_cast hceilReal
    have hcast : (Rconst : ℝ) =
        (6 : ℝ) * (4 * (K q r : ℝ) - 1) * K q r *
          (2 : ℝ) ^ (4 * K q r - 2) := by
      dsimp [Rconst, K₀]
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ 4 * K q r)]
      push_cast
      ring
    rw [← hcast]
    exact_mod_cast hceil.trans (Nat.le_add_right _ _)
  have hDupper : centerDegree n q r ≤ (n : ℝ) ^ (q - r) := by
    unfold centerDegree Erdos722.Boost.extensionScale
    have hchoose : Nat.choose (n - r) (q - r) ≤ n ^ (q - r) := by
      exact (Nat.choose_le_pow (n - r) (q - r)).trans
        (Nat.pow_le_pow_left (Nat.sub_le n r) (q - r))
    have hchooseR : (Nat.choose (n - r) (q - r) : ℝ) ≤
        (n : ℝ) ^ (q - r) := by exact_mod_cast hchoose
    nlinarith [show (0 : ℝ) ≤ Nat.choose (n - r) (q - r) by positivity]
  have hCD : (n : ℝ) * (n : ℝ) ^ (q - r - 1) ≤
      ((2 : ℝ) ^ (q - r + 1) * (q - r).factorial) * centerDegree n q r := by
    have hpowNat := pow_le_factorial_mul_choose_sub n r (q - r) (by omega)
    have hpowReal : (n : ℝ) ^ (q - r) ≤
        (2 : ℝ) ^ (q - r) * (q - r).factorial *
          Nat.choose (n - r) (q - r) := by exact_mod_cast hpowNat
    have hpowEq : (n : ℝ) ^ (q - r) =
        (n : ℝ) * (n : ℝ) ^ (q - r - 1) := by
      conv_lhs => rw [show q - r = (q - r - 1) + 1 by omega, pow_succ]
      ring
    rw [← hpowEq]
    unfold centerDegree Erdos722.Boost.extensionScale
    calc
      (n : ℝ) ^ (q - r) ≤
          (2 : ℝ) ^ (q - r) * (q - r).factorial *
            Nat.choose (n - r) (q - r) := hpowReal
      _ = (2 : ℝ) ^ (q - r + 1) * (q - r).factorial *
          ((Nat.choose (n - r) (q - r) : ℝ) / 2) := by
        rw [pow_succ]
        ring
  have hDg : centerDegree n q r / host.card ≤
      (n : ℝ) ^ (q - r - 1) := by
    apply (div_le_iff₀ hgR).2
    calc
      centerDegree n q r ≤ (n : ℝ) ^ (q - r) := hDupper
      _ = (n : ℝ) * (n : ℝ) ^ (q - r - 1) := by
        conv_lhs => rw [show q - r = (q - r - 1) + 1 by omega, pow_succ]
        ring
      _ ≤ (host.card : ℝ) * (n : ℝ) ^ (q - r - 1) := by
        exact mul_le_mul_of_nonneg_right hng
          (show (0 : ℝ) ≤ (n : ℝ) ^ (q - r - 1) by positivity)
      _ = (n : ℝ) ^ (q - r - 1) * host.card := by ring
  have hmargin : (4 : ℝ) *
      (1 + (K q r : ℝ) * (K q r + 1) *
        ((n : ℝ) ^ (q - r - 1) + 1)) ≤
      Erdos722.NibbleInstantiation.initialError n q r := by
    let N : ℝ := (n : ℝ) ^ (q - r - 1)
    have hN : 1 ≤ N := one_le_pow₀ (by exact_mod_cast (show 1 ≤ n by omega))
    have hraw : Nconst * N ≤
        Erdos722.NibbleInstantiation.initialError n q r := by
      simpa [Nconst, K₀, N, Erdos722.NibbleInstantiation.initialError] using hmarginRaw
    have haux : (4 : ℝ) *
        (1 + (K q r : ℝ) * (K q r + 1) * (N + 1)) ≤ Nconst * N := by
      dsimp [Nconst, K₀]
      nlinarith [mul_nonneg
        (by positivity : (0 : ℝ) ≤ 4 + 4 * (K q r : ℝ) * (K q r + 1))
        (sub_nonneg.mpr hN)]
    exact haux.trans hraw
  have hhostScale' :
      2 * (K q r : ℝ) ^ 2 * (K q r - 1 : ℕ) *
          (scale n q r : ℝ) ^ (5 * K q r - 1) ≤ host.card := by
    simpa [K₀] using hhostScale _ hhalf
  have hcliqueWide' : 64 * (K q r : ℝ) ^ 2 *
      (scale n q r : ℝ) ^ (5 * K q r - 1) ≤ host.card := by
    simpa [K₀] using hcliqueWide _ hhalf
  have hedge' : 48 * (K q r : ℝ) ^ 2 *
      (n : ℝ) ^ (q - r - 1) ≤
        Erdos722.NibbleInstantiation.initialError n q r := by
    simpa [K₀, Erdos722.NibbleInstantiation.initialError] using hedge
  have hface' : 12 * (K q r : ℝ) * (scale n q r : ℝ) ^ 3 ≤ n := by
    simpa [K₀] using hface
  have hjumpData := concrete_jump_pos_and_half_window hg hnpos
    (by simpa [K₀] using (show 2 < K₀ by omega)) hTeight hDpos hDg
    hedge' hcliqueWide' hface'
  have hjumpLt : ∀ z : BarrierIndex host r,
      concreteJumpCap host q r z < profileWindow host q r z := by
    intro z
    nlinarith [hjumpData.1 z, hjumpData.2 z]
  have hvarianceNonneg : ∀ z : BarrierIndex host r,
      0 ≤ varianceBudget (Erdos722.NibbleInstantiation.concreteVariance host q r z)
        0 (depth host.card n q r) := fun z ↦
    concrete_varianceBudget_nonneg hg (by simpa [K₀] using
      (show 2 < K₀ by omega)) hTeight hpower htarget z
  have hvariance : ∀ z : BarrierIndex host r,
      varianceBudget (Erdos722.NibbleInstantiation.concreteVariance host q r z)
        0 (depth host.card n q r) ≤ concreteVarianceTotalCap host q r z := fun z ↦
    concrete_varianceBudget_le_totalCap hg (by simpa [K₀] using
      (show 2 < K₀ by omega)) hTeight hDone hpower htarget hnscale' z
  have hscore := concentrationScore_le_freedman_score hg hnpos
    (by simpa [K₀] using (show 2 < K₀ by omega)) hTeight hDpos hDg hCD hng
    hedge' hcliqueWide' hface'
  have hsmall := concrete_exponential_sum_lt_one_of_score
    hvarianceNonneg hvariance hjumpData.1 hjumpLt
    (concentrationScore n q r) hscore (hexponential host hhost)
  apply Erdos722.NibbleInstantiation.exists_boundedNibble_of_quantitative
    hr hrq hhost hH hregular hhalf hT hpower htarget hhostScale'
    hremaining hmargin (concreteJumpCap host q r) (concreteRate host q r)
    (fun z ↦ concreteJumpCap_nonneg hg z) hjumpLt
  · intro z i hi
    have htargetPos : 0 < stopTarget host.card n q r := by
      dsimp [stopTarget]
      omega
    have hs : K q r * (i + 1) < host.card :=
      mul_succ_lt_of_lt_depth (by simpa [K₀] using hKpos) htargetPos hi
    have hi1 : i + 1 ≤ depth host.card n q r := by omega
    have hl0 := one_div_scale_le_density
      (g := host.card) (n := n) (q := q) (r := r)
      hg (by simpa [K₀] using hKpos) hTpos htarget hi.le
    have hl1 := one_div_scale_le_density
      (g := host.card) (n := n) (q := q) (r := r)
      hg (by simpa [K₀] using hKpos) hTpos htarget hi1
    exact barrierJump_le_concreteJumpCap hg (by simpa [K₀] using
      (show 2 < K₀ by omega)) hTeight hDone hnscale' hs hl0 hl1 z
  · exact fun z ↦ concrete_rate_pos hjumpData.1 hjumpLt z
  · exact fun z ↦ concrete_rate_mul_jump_le_one hjumpData.1 hjumpLt z
  · exact hsmall
  · exact hterminal host.card hhalf htarget

end

end Erdos722.NibbleTail
