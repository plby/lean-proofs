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
import ErdosProblems.Erdos722.SpecialCliqueCandidates
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Asymptotic abundance of the special-clique candidate family

The distinguished negative cliques in Keevash's exchange are chosen before
the remaining cliques receive fresh random rotations.  Their joint choice
costs `choose q r * (choose q r - 1) / d` powers of the host size.  Each of
the remaining `m` monochromatic-clique constraints costs a further
`choose q r / d`.  Thus the restricted candidate family still beats the
one-power exceptional-pair bound as soon as

`choose q r * (choose q r - 1 + m) < d`.

This file proves that comparison with all floor, pruning, and
falling-factorial losses retained explicitly.
-/

namespace Erdos722.SpecialCliqueCandidatesAsymptotic

open Finset Filter
open scoped Topology Real
open Erdos722.Asymptotics
open Erdos722.GeneratorAsymptotic
open Erdos722.CliqueRotationAsymptotic
open Erdos722.RotationAsymptotic

noncomputable section

/-- The bounded number of anchored cliques discarded at each greedy
special-clique choice. -/
def specialChoiceError (q r n : ℕ) : ℕ :=
  (Nat.choose q r + 1) * (q * n ^ (q - r - 1))

/-- The local clique lower bound after pruning and after the bounded greedy
compatibility loss. -/
def specialChoiceLower (q r d n : ℕ) : ℕ :=
  generatorCliqueLower q r d n - generatorPruneThreshold q r d n -
    specialChoiceError q r n

/-- Number of vertices occupied by the root and all distinguished negative
cliques of a full exchange. -/
def specialSupportSize (q r : ℕ) : ℕ :=
  q + Nat.choose q r * (q - r)

/-- The bounded greedy loss is eventually at most one quarter of the
guaranteed local clique count. -/
theorem eventually_four_mul_specialChoiceError_le_cliqueLower
    (q r d : ℕ) (hr : 0 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d) :
    ∀ᶠ n : ℕ in atTop,
      4 * specialChoiceError q r n ≤ generatorCliqueLower q r d n := by
  let K := Nat.choose q r
  let Cclique : ℕ :=
    2 * 16 ^ (q - r) * (2 ^ q) ^ (q - r)
  let smallExp : ℝ := (q - r - 1 : ℕ)
  let cliqueExp : ℝ :=
    ((d * (q - r) - (K - 1) : ℕ) : ℝ) / d
  let C : ℝ := (4 * (K + 1) * q : ℕ) * Cclique
  have hKpos : 0 < K := by
    dsimp [K]
    exact Nat.choose_pos hrq.le
  have hd : 0 < d := hKpos.trans hqd
  have hcliqueSub : K - 1 ≤ d * (q - r) := by
    have hKd : K - 1 ≤ d := by omega
    exact hKd.trans (Nat.le_mul_of_pos_right d (by omega))
  have hgap : smallExp < cliqueExp := by
    have hqr : 1 ≤ q - r := by omega
    change (((q - r - 1 : ℕ) : ℝ)) <
      (((d * (q - r) - (K - 1) : ℕ) : ℝ) / d)
    rw [Nat.cast_sub (by omega : 1 ≤ q - r), Nat.cast_sub hcliqueSub]
    push_cast
    have hKdR : (K : ℝ) < d := by exact_mod_cast hqd
    have hKcast : (((K - 1 : ℕ) : ℝ)) = (K : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ K)]
      norm_num
    rw [hKcast]
    field_simp
    nlinarith
  have hdom := eventually_const_mul_rpow_le_rpow hgap
    (show 0 ≤ C by positivity)
  have hclique := eventually_generatorCliqueLower_lower q r d hr hrq hqd
  filter_upwards [hdom, hclique, eventually_ge_atTop 1] with
      n hdom hclique hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hleft : ((4 * specialChoiceError q r n : ℕ) : ℝ) ≤
      (n : ℝ) ^ cliqueExp / Cclique := by
    apply (le_div_iff₀ (show (0 : ℝ) < Cclique by positivity)).2
    calc
      ((4 * specialChoiceError q r n : ℕ) : ℝ) * Cclique =
          C * (n : ℝ) ^ smallExp := by
        simp only [specialChoiceError]
        push_cast
        rw [Real.rpow_natCast]
        dsimp [C, smallExp, K]
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring
      _ ≤ (n : ℝ) ^ cliqueExp := hdom
  have hreal : ((4 * specialChoiceError q r n : ℕ) : ℝ) ≤
      generatorCliqueLower q r d n :=
    hleft.trans (by simpa [cliqueExp, Cclique, K] using hclique)
  exact_mod_cast hreal

/-- After both pruning and greedy compatibility losses, one quarter of the
original local clique guarantee remains. -/
theorem cliqueLower_le_four_mul_specialChoiceLower
    {q r d n : ℕ}
    (hprune : 2 * generatorPruneThreshold q r d n ≤
      generatorCliqueLower q r d n)
    (herror : 4 * specialChoiceError q r n ≤
      generatorCliqueLower q r d n) :
    generatorCliqueLower q r d n ≤
      4 * specialChoiceLower q r d n := by
  simp only [specialChoiceLower]
  omega

/-- The local lower bound is large enough to pay the compatibility loss,
so it is a valid input to `many_specialGoodEmbeddings`. -/
theorem specialChoiceError_le_prunedLower
    {q r d n : ℕ}
    (hprune : 2 * generatorPruneThreshold q r d n ≤
      generatorCliqueLower q r d n)
    (herror : 4 * specialChoiceError q r n ≤
      generatorCliqueLower q r d n) :
    specialChoiceError q r n ≤
      generatorCliqueLower q r d n - generatorPruneThreshold q r d n := by
  omega

/-- The exact scalar comparison needed to apply the restricted-candidate
Paley--Zygmund bound.  The right side is the proved lower bound for the
number of special-good embeddings times the probability numerator for the
`m` remaining clique constraints. -/
theorem eventually_specialCandidate_expected_lower
    {v m q r d : ℕ} (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    (hsupport : specialSupportSize q r ≤ v)
    (hbudget : Nat.choose q r * (Nat.choose q r - 1 + m) < d) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (U : Finset (Finset (Fin n))),
      Nat.choose n (r - 1) * generatorDegreeLower d n *
          generatorCliqueLower q r d n ≤
        (4 * r * Nat.choose q r) * U.card →
      ((v - q) ^ 2 * n ^ (v - (q + 1))) * Nat.choose n q ^ m ≤
        specialChoiceLower q r d n ^ Nat.choose q r *
          (n - specialSupportSize q r).descFactorial
            (v - specialSupportSize q r) * U.card ^ m := by
  let K := Nat.choose q r
  let F := specialSupportSize q r
  let s := v - F
  let degreeExp : ℝ := ((d - 1 : ℕ) : ℝ) / d
  let cliqueExp : ℝ :=
    ((d * (q - r) - (K - 1) : ℕ) : ℝ) / d
  let densityExp : ℝ := ((d * q - K : ℕ) : ℝ) / d
  let leftExp : ℝ := (v - (q + 1) : ℕ) + q * m
  let rightExp : ℝ := cliqueExp * K + s + densityExp * m
  let Cchoose : ℕ := 2 ^ (r - 1) * Nat.factorial (r - 1)
  let Cclique : ℕ :=
    2 * 16 ^ (q - r) * (2 ^ q) ^ (q - r)
  let Cmass : ℕ := 4 * r * K
  let Cfamily : ℕ := Cmass * Cchoose * 16 * Cclique
  let Cspecial : ℕ := 4 * Cclique
  let Ctotal : ℝ :=
    ((v - q) ^ 2 : ℕ) * (Cspecial : ℝ) ^ K *
      (2 ^ s : ℕ) * (Cfamily : ℝ) ^ m
  have hKpos : 0 < K := by
    dsimp [K]
    exact Nat.choose_pos hrq.le
  have hd : 0 < d := hKpos.trans hqd
  have hdOne : 1 < d := by omega
  have hcliqueSub : K - 1 ≤ d * (q - r) := by
    have hKd : K - 1 ≤ d := by omega
    exact hKd.trans (Nat.le_mul_of_pos_right d (by omega))
  have hdensitySub : K ≤ d * q :=
    hqd.le.trans (Nat.le_mul_of_pos_right d (by omega))
  have hqv : q < v := by
    have hstrict : q < specialSupportSize q r := by
      have : 0 < Nat.choose q r * (q - r) :=
        Nat.mul_pos (Nat.choose_pos hrq.le) (by omega)
      rw [specialSupportSize]
      omega
    exact hstrict.trans_le hsupport
  have hgap : leftExp < rightExp := by
    change (((v - (q + 1) : ℕ) : ℝ) + (q : ℝ) * m) <
      cliqueExp * K + (s : ℝ) + densityExp * m
    dsimp only [cliqueExp, densityExp]
    rw [Nat.cast_sub (by omega : q + 1 ≤ v), Nat.cast_sub hcliqueSub,
      Nat.cast_sub hdensitySub]
    have hFv : F ≤ v := by simpa [F] using hsupport
    have hsCast : (s : ℝ) = v - F := by
      dsimp [s]
      rw [Nat.cast_sub hFv]
    rw [hsCast]
    dsimp [F, specialSupportSize, K]
    push_cast
    rw [Nat.cast_sub hrq.le, Nat.cast_sub (by omega : 1 ≤ Nat.choose q r)]
    push_cast
    have hbudgetR :
        ((Nat.choose q r : ℝ) *
          ((Nat.choose q r : ℝ) - 1 + m)) < d := by
      have hbudgetR0 :
          (((Nat.choose q r * (Nat.choose q r - 1 + m) : ℕ) : ℝ)) < d := by
        exact_mod_cast hbudget
      rw [Nat.cast_mul, Nat.cast_add,
        Nat.cast_sub (by omega : 1 ≤ Nat.choose q r)] at hbudgetR0
      norm_num at hbudgetR0
      exact hbudgetR0
    field_simp
    nlinarith [hbudgetR]
  have hdom := eventually_const_mul_rpow_le_rpow hgap
    (show 0 ≤ Ctotal by positivity)
  have hdegree := eventually_rpow_div_sixteen_le_generatorDegreeLower hdOne
  have hclique := eventually_generatorCliqueLower_lower q r d
    (by omega) hrq hqd
  have hprune := eventually_two_mul_generatorPruneThreshold_le_cliqueLower
    q r d (by omega) hrq hqd
  have herror := eventually_four_mul_specialChoiceError_le_cliqueLower
    q r d (by omega) hrq hqd
  filter_upwards [hdom, hdegree, hclique, hprune, herror,
      eventually_ge_atTop (max (2 * v) (2 * (r - 1)))] with
      n hdom hdegree hclique hprune herror hnlarge
  intro U hmass
  have hnTwoV : 2 * v ≤ n := (le_max_left _ _).trans hnlarge
  have hnChoose : 2 * (r - 1) ≤ n := (le_max_right _ _).trans hnlarge
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hFv : F ≤ v := by simpa [F] using hsupport
  have hbaseline :=
    Erdos722.LocalDecoderAsymptotic.descFactorial_sub_cast_lower
      (n := n) (r := F) (s := s) (by
        have hFs : F + s = v := Nat.add_sub_of_le hFv
        simpa [hFs] using hnTwoV)
  have hdesc : (n : ℝ) ^ s / (2 : ℝ) ^ s ≤
      ((n - F).descFactorial s : ℕ) := hbaseline
  have hchooseNat :=
    Erdos722.BinomialBounds.pow_le_factorial_mul_choose_sub
      n 0 (r - 1) (by omega : 2 * (0 + (r - 1)) ≤ n)
  have hchoose : (n : ℝ) ^ (r - 1) / Cchoose ≤
      Nat.choose n (r - 1) := by
    have hreal : (n : ℝ) ^ (r - 1) ≤
        (Cchoose : ℝ) * Nat.choose n (r - 1) := by
      exact_mod_cast (by simpa [Cchoose] using hchooseNat)
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < Cchoose)).2 (by
      simpa [mul_comm] using hreal)
  have hfamilyPower :
      (n : ℝ) ^ densityExp =
        (n : ℝ) ^ (r - 1) * (n : ℝ) ^ degreeExp *
          (n : ℝ) ^ cliqueExp := by
    have hexp : densityExp =
        ((r - 1 : ℕ) : ℝ) + degreeExp + cliqueExp := by
      dsimp [densityExp, degreeExp, cliqueExp, K]
      have hcastR : (((r - 1 : ℕ) : ℝ)) = (r : ℝ) - 1 := by
        rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ r)]
        norm_num
      have hcastDegree : (((d - 1 : ℕ) : ℝ)) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ d)]
        norm_num
      have hcastK : (((K - 1 : ℕ) : ℝ)) = (K : ℝ) - 1 := by
        rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ K)]
        norm_num
      have hcastClique : (((d * (q - r) - (K - 1) : ℕ) : ℝ)) =
          ((d * (q - r) : ℕ) : ℝ) - ((K - 1 : ℕ) : ℝ) :=
        Nat.cast_sub hcliqueSub
      have hcastDensity : (((d * q - K : ℕ) : ℝ)) =
          ((d * q : ℕ) : ℝ) - (K : ℝ) := Nat.cast_sub hdensitySub
      have hcastQr : (((q - r : ℕ) : ℝ)) = (q : ℝ) - r :=
        Nat.cast_sub hrq.le
      rw [hcastR, hcastDegree, hcastClique, hcastK, hcastDensity]
      push_cast
      rw [hcastQr]
      field_simp
      ring
    rw [hexp, Real.rpow_add hnR, Real.rpow_add hnR,
      Real.rpow_natCast]
  have hfamily : (n : ℝ) ^ densityExp / Cfamily ≤ U.card := by
    have hprod :
        ((n : ℝ) ^ (r - 1) / Cchoose) *
            ((n : ℝ) ^ degreeExp / 16) *
            ((n : ℝ) ^ cliqueExp / Cclique) ≤
          (Nat.choose n (r - 1) : ℝ) * generatorDegreeLower d n *
            generatorCliqueLower q r d n := by
      exact mul_le_mul
        (mul_le_mul hchoose (by simpa [degreeExp] using hdegree)
          (by positivity) (by positivity))
        (by simpa [cliqueExp, Cclique, K] using hclique)
        (by positivity) (by positivity)
    have hmassR :
        (Nat.choose n (r - 1) : ℝ) * generatorDegreeLower d n *
            generatorCliqueLower q r d n ≤
          (Cmass : ℝ) * U.card := by
      exact_mod_cast (by simpa [Cmass, K] using hmass)
    calc
      (n : ℝ) ^ densityExp / Cfamily =
          (((n : ℝ) ^ (r - 1) / Cchoose) *
            ((n : ℝ) ^ degreeExp / 16) *
            ((n : ℝ) ^ cliqueExp / Cclique)) / Cmass := by
        rw [hfamilyPower]
        dsimp [Cfamily]
        push_cast
        field_simp
      _ ≤ ((Nat.choose n (r - 1) : ℝ) *
          generatorDegreeLower d n * generatorCliqueLower q r d n) /
            Cmass := by gcongr
      _ ≤ U.card := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < Cmass)).2
        simpa [mul_comm] using hmassR
  have hspecial : (n : ℝ) ^ cliqueExp / Cspecial ≤
      specialChoiceLower q r d n := by
    have hquarter : (generatorCliqueLower q r d n : ℝ) / 4 ≤
        specialChoiceLower q r d n := by
      have hnat := cliqueLower_le_four_mul_specialChoiceLower hprune herror
      exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by
        have hnatR : (generatorCliqueLower q r d n : ℝ) ≤
            ((4 * specialChoiceLower q r d n : ℕ) : ℝ) := by
          exact_mod_cast hnat
        simpa [mul_comm] using hnatR)
    calc
      (n : ℝ) ^ cliqueExp / Cspecial =
          ((n : ℝ) ^ cliqueExp / Cclique) / 4 := by
        dsimp [Cspecial]
        push_cast
        ring
      _ ≤ (generatorCliqueLower q r d n : ℝ) / 4 := by
        gcongr
        have hCcast : (Cclique : ℝ) =
            2 * (16 : ℝ) ^ (q - r) * (2 ^ q : ℝ) ^ (q - r) := by
          simp [Cclique]
        rw [hCcast]
        simpa [cliqueExp, K] using hclique
      _ ≤ specialChoiceLower q r d n := hquarter
  have hleft :
      ((((v - q) ^ 2 * n ^ (v - (q + 1))) *
          Nat.choose n q ^ m : ℕ) : ℝ) ≤
        (((v - q : ℕ) : ℝ) ^ 2) * (n : ℝ) ^ leftExp := by
    push_cast
    change ((v - q : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ (v - (q + 1)) *
        (Nat.choose n q : ℝ) ^ m ≤
      ((v - q : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ leftExp
    calc
      ((v - q : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ (v - (q + 1)) *
          (Nat.choose n q : ℝ) ^ m ≤
        ((v - q : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ (v - (q + 1)) *
          ((n : ℝ) ^ q) ^ m := by
        gcongr
        exact_mod_cast Nat.choose_le_pow n q
      _ = (((v - q : ℕ) : ℝ) ^ 2) * (n : ℝ) ^ leftExp := by
        have hexp : leftExp =
            (((v - (q + 1) + q * m : ℕ) : ℕ) : ℝ) := by
          push_cast
          simp [leftExp]
        rw [hexp, Real.rpow_natCast, pow_add, pow_mul]
        push_cast
        ring
  have hright :
      (n : ℝ) ^ rightExp /
          ((Cspecial : ℝ) ^ K * (2 : ℝ) ^ s *
            (Cfamily : ℝ) ^ m) ≤
        (specialChoiceLower q r d n : ℝ) ^ K *
          ((n - F).descFactorial s : ℕ) * (U.card : ℝ) ^ m := by
    calc
      (n : ℝ) ^ rightExp /
          ((Cspecial : ℝ) ^ K * (2 : ℝ) ^ s *
            (Cfamily : ℝ) ^ m) =
        (((n : ℝ) ^ cliqueExp / Cspecial) ^ K) *
          ((n : ℝ) ^ s / (2 : ℝ) ^ s) *
          (((n : ℝ) ^ densityExp / Cfamily) ^ m) := by
        rw [show rightExp = cliqueExp * K + s + densityExp * m by rfl,
          Real.rpow_add hnR, Real.rpow_add hnR,
          Real.rpow_mul hnR.le, Real.rpow_mul hnR.le,
          Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast,
          div_pow, div_pow]
        ring
      _ ≤ (specialChoiceLower q r d n : ℝ) ^ K *
          ((n - F).descFactorial s : ℕ) * (U.card : ℝ) ^ m := by
        gcongr
  have hmiddle :
      (((v - q : ℕ) : ℝ) ^ 2) * (n : ℝ) ^ leftExp ≤
        (n : ℝ) ^ rightExp /
          ((Cspecial : ℝ) ^ K * (2 : ℝ) ^ s *
            (Cfamily : ℝ) ^ m) := by
    have hden : (0 : ℝ) <
        (Cspecial : ℝ) ^ K * (2 : ℝ) ^ s *
          (Cfamily : ℝ) ^ m := by positivity
    apply (le_div_iff₀ hden).2
    have hdom' : Ctotal * (n : ℝ) ^ leftExp ≤
        (n : ℝ) ^ rightExp := hdom
    calc
      (((v - q : ℕ) : ℝ) ^ 2) * (n : ℝ) ^ leftExp *
          ((Cspecial : ℝ) ^ K * (2 : ℝ) ^ s *
            (Cfamily : ℝ) ^ m) =
        Ctotal * (n : ℝ) ^ leftExp := by
          dsimp [Ctotal]
          push_cast
          ring
      _ ≤ _ := hdom'
  have hreal :
      ((((v - q) ^ 2 * n ^ (v - (q + 1))) *
          Nat.choose n q ^ m : ℕ) : ℝ) ≤
        ((specialChoiceLower q r d n ^ Nat.choose q r *
          (n - specialSupportSize q r).descFactorial
            (v - specialSupportSize q r) * U.card ^ m : ℕ) : ℝ) := by
    simpa [K, F, s, Nat.cast_pow] using
      hleft.trans (hmiddle.trans hright)
  exact_mod_cast hreal

end

end Erdos722.SpecialCliqueCandidatesAsymptotic
