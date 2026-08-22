/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.ThickPoint
import ErdosProblems.Erdos1165.NegativeBinomial
import ErdosProblems.Erdos1165.SecondMoment
import ErdosProblems.Erdos1165.Markov
import ErdosProblems.Erdos1165.StirlingLocalCLT
import ErdosProblems.Erdos1165.PathInsertion

/-!
# The first-moment profile calculation in the HLOZ appendix

This file formalizes the exact, discrete part of Appendix A.1.1 of
Hao--Li--Okada--Zheng.  If `u_l` is the number of upcrossings from level
`l-1` to level `l` of the auxiliary killed one-dimensional walk, then,
conditionally on `u_l = a`, `u_(l+1)` is the sum of `a` independent geometric
variables of parameter `1/2`.  Consequently its transition mass is

`p(a,b) = choose (a+b-1) b / 2^(a+b)`.

The definitions below also give the finite constrained-profile sum appearing
in Proposition A.7 and prove all of its finite combinatorics: exact membership,
nonnegativity, strict positivity, the product recursion, reindexing by the
deviations `Delta_l = m_l - 2l^2`, and the deterministic first-moment and
`Y`-to-`Y'` measure bookkeeping used in (A.4) and (A.7).

What is not asserted here is the analytic estimate in Proposition A.7.  Its
remaining input is precisely a uniform two-parameter local central limit
estimate for `p(a,b)`, followed by the Brownian small-ball lower bound for the
Gaussian profile kernel.  Recording the exact finite sum makes that missing
input explicit rather than packaging it as a random-walk assumption.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.AppendixFirstMoment

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The critical negative-binomial transition kernel -/

/-- The upcrossing transition mass.  Zero is absorbing; away from zero this
is the negative-binomial mass with success probability `1/2`. -/
def transitionMass (a b : ℕ) : ℝ :=
  if a = 0 then if b = 0 then 1 else 0
  else NegativeBinomial.mass (1 / 2) a b

@[simp] lemma transitionMass_zero_left (b : ℕ) :
    transitionMass 0 b = if b = 0 then 1 else 0 := by
  simp [transitionMass]

@[simp] lemma transitionMass_zero_zero : transitionMass 0 0 = 1 := by
  simp

@[simp] lemma transitionMass_zero_left_of_pos {b : ℕ} (hb : 0 < b) :
    transitionMass 0 b = 0 := by
  simp [transitionMass, hb.ne']

lemma transitionMass_of_pos {a : ℕ} (ha : 0 < a) (b : ℕ) :
    transitionMass a b = NegativeBinomial.mass (1 / 2) a b := by
  simp [transitionMass, ha.ne']

/-- The exact formula in HLOZ Remark A.5. -/
lemma transitionMass_formula {a : ℕ} (ha : 0 < a) (b : ℕ) :
    transitionMass a b =
      ((a + b - 1).choose b : ℝ) / (2 : ℝ) ^ (a + b) := by
  rw [transitionMass_of_pos ha,
    NegativeBinomial.mass_eq_hloz_formula (1 / 2) ha]
  norm_num [div_pow]
  ring

lemma transitionMass_nonneg (a b : ℕ) : 0 ≤ transitionMass a b := by
  by_cases ha : a = 0
  · subst a
    rw [transitionMass_zero_left]
    split_ifs <;> norm_num
  · rw [transitionMass, if_neg ha]
    exact NegativeBinomial.mass_nonneg (by norm_num) (by norm_num) a b

lemma transitionMass_pos {a : ℕ} (ha : 0 < a) (b : ℕ) :
    0 < transitionMass a b := by
  rw [transitionMass_of_pos ha]
  exact NegativeBinomial.mass_pos (by norm_num) (by norm_num) ha b

lemma hasSum_transitionMass (a : ℕ) : HasSum (transitionMass a) 1 := by
  by_cases ha : a = 0
  · subst a
    exact (hasSum_ite_eq 0 (1 : ℝ)).congr fun b ↦ by
      simp [transitionMass]
  · have h := NegativeBinomial.hasSum_mass (p := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num) (Nat.pos_of_ne_zero ha)
    convert h using 1
    funext b
    exact transitionMass_of_pos (Nat.pos_of_ne_zero ha) b

lemma summable_transitionMass (a : ℕ) : Summable (transitionMass a) :=
  (hasSum_transitionMass a).summable

@[simp] lemma tsum_transitionMass (a : ℕ) :
    ∑' b, transitionMass a b = 1 := (hasSum_transitionMass a).tsum_eq

/-- The transition kernel as a genuine PMF, including the absorbing state. -/
noncomputable def transitionLaw (a : ℕ) : PMF ℕ :=
  if ha : a = 0 then PMF.pure 0
  else NegativeBinomial.law (1 / 2) (by norm_num) (by norm_num) a
    (Nat.pos_of_ne_zero ha)

@[simp] lemma transitionLaw_apply (a b : ℕ) :
    transitionLaw a b = ENNReal.ofReal (transitionMass a b) := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp [transitionLaw]
    · simp [transitionLaw, hb]
  · simp [transitionLaw, transitionMass, ha,
      NegativeBinomial.law_apply]

/-! ### The transition as a sum of geometric offspring -/

/-- Mass of one geometric `(1/2)` offspring count. -/
def halfGeometricMass (q : ℕ) : ℝ := (1 / 2 : ℝ) ^ (q + 1)

lemma halfGeometricMass_nonneg (q : ℕ) : 0 ≤ halfGeometricMass q := by
  unfold halfGeometricMass
  positivity

lemma hasSum_halfGeometricMass : HasSum halfGeometricMass 1 := by
  have h := (hasSum_geometric_of_norm_lt_one
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left (1 / 2 : ℝ)
  norm_num at h
  have heq : halfGeometricMass = fun q : ℕ ↦ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ q := by
    funext q
    rw [halfGeometricMass, pow_succ]
    ring
  rw [heq]
  exact h

/-- A fixed weak composition of `b` into `a` geometric offspring counts has
mass `2^-(a+b)`. -/
lemma prod_halfGeometricMass {a b : ℕ} (g : PathInsertion.GapPattern a b) :
    ∏ i : Fin a, halfGeometricMass (PathInsertion.gapMultiplicity g i) =
      (1 / 2 : ℝ) ^ (a + b) := by
  simp only [halfGeometricMass]
  calc
    (∏ i : Fin a, (1 / 2 : ℝ) ^ (PathInsertion.gapMultiplicity g i + 1)) =
        (1 / 2 : ℝ) ^
          (∑ i : Fin a, (PathInsertion.gapMultiplicity g i + 1)) := by
            simpa using Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin a))
              (fun i ↦ PathInsertion.gapMultiplicity g i + 1) (1 / 2 : ℝ)
    _ = (1 / 2 : ℝ) ^ (a + b) := by
      congr 1
      rw [Finset.sum_add_distrib, PathInsertion.sum_gapMultiplicity]
      simp [add_comm]

/-- Summing over the weak compositions proves, without a probabilistic
oracle, that the sum of `a` independent geometric `(1/2)` variables has the
upcrossing transition mass. -/
theorem transitionMass_eq_sum_geometric_offspring {a : ℕ} (ha : 0 < a) (b : ℕ) :
    transitionMass a b =
      ∑ g : PathInsertion.GapPattern a b,
        ∏ i : Fin a, halfGeometricMass (PathInsertion.gapMultiplicity g i) := by
  rw [transitionMass_formula ha]
  simp_rw [prod_halfGeometricMass]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    PathInsertion.card_gapPattern]
  norm_num [div_pow]
  ring

/-- At a positive state, the transition is centered at that state. -/
lemma hasSum_weighted_transitionMass {a : ℕ} (ha : 0 < a) :
    HasSum (fun b : ℕ ↦ (b : ℝ) * transitionMass a b) (a : ℝ) := by
  have h := NegativeBinomial.hasSum_weighted_mass
    (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num) ha
  have hv : (a : ℝ) * (1 - (1 / 2 : ℝ)) / (1 / 2 : ℝ) = a := by ring
  rw [hv] at h
  simpa only [transitionMass_of_pos ha] using h

/-- The transition variance at state `a` is `2a`. -/
lemma hasSum_variance_transitionMass {a : ℕ} (ha : 0 < a) :
    HasSum (fun b : ℕ ↦ ((b : ℝ) - a) ^ 2 * transitionMass a b)
      (2 * (a : ℝ)) := by
  have h2 := NegativeBinomial.hasSum_square_mass
    (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num) ha
  have h1 := NegativeBinomial.hasSum_weighted_mass
    (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num) ha
  have h0 := NegativeBinomial.hasSum_mass
    (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num) ha
  have h := (h2.add (h1.mul_left (-2 * (a : ℝ)))).add
    (h0.mul_left ((a : ℝ) ^ 2))
  have heq :
      (fun b : ℕ ↦ ((b : ℝ) - a) ^ 2 * transitionMass a b) =
        (fun b : ℕ ↦ (b : ℝ) ^ 2 * NegativeBinomial.mass (1 / 2) a b +
          (-2 * (a : ℝ)) * ((b : ℝ) * NegativeBinomial.mass (1 / 2) a b) +
          (a : ℝ) ^ 2 * NegativeBinomial.mass (1 / 2) a b) := by
    funext b
    rw [transitionMass_of_pos ha]
    ring
  rw [heq]
  convert h using 1
  norm_num
  ring

/-! ## Exact reduction of a transition to Stirling's formula -/

/-- Logarithm of the transition mass, before any local-CLT approximation. -/
lemma log_transitionMass {a : ℕ} (ha : 0 < a) (b : ℕ) :
    Real.log (transitionMass a b) =
      Real.log ((a + b - 1).choose b : ℝ) -
        (a + b : ℕ) * Real.log 2 := by
  rw [transitionMass_formula ha]
  have hchooseNat : 0 < (a + b - 1).choose b := by
    exact Nat.choose_pos (by omega)
  have hchoose : (((a + b - 1).choose b : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hpow : (2 : ℝ) ^ (a + b) ≠ 0 := by positivity
  rw [Real.log_div hchoose hpow, Real.log_pow]

/-- The transition logarithm after subtracting the entropy/Stirling main
term.  This is the exact remainder to which the quantitative results in
`StirlingLocalCLT` apply. -/
noncomputable def transitionLogRemainder (a b : ℕ) : ℝ :=
  Real.log (transitionMass a b) -
    (StirlingLocalCLT.logBinomialMain (a + b - 1) b -
      (a + b : ℕ) * Real.log 2)

lemma transitionLogRemainder_eq_binomial {a : ℕ} (ha : 0 < a) (b : ℕ) :
    transitionLogRemainder a b =
      StirlingLocalCLT.logBinomialRemainder (a + b - 1) b := by
  rw [transitionLogRemainder, log_transitionMass ha,
    StirlingLocalCLT.logBinomialRemainder]
  ring

/-- A global uniform error bound for every genuinely interior transition.
It is weaker than the cubic local-CLT expansion required by Proposition A.7,
but already removes all factorial estimates from that remaining task. -/
lemma abs_transitionLogRemainder_le_two {a b : ℕ}
    (ha : 1 < a) (hb : 0 < b) :
    |transitionLogRemainder a b| ≤ 2 := by
  rw [transitionLogRemainder_eq_binomial (Nat.zero_lt_of_lt ha)]
  apply StirlingLocalCLT.abs_logBinomialRemainder_le_two hb.ne'
  omega

/-! ## Finite constrained profiles -/

/-- A profile has entries corresponding, in order, to HLOZ's
`m_2,...,m_n`. -/
abbrev Profile (n : ℕ) := Fin (n - 1) → ℕ

/-- The HLOZ scale represented by an entry of a profile. -/
def scaleIndex {n : ℕ} (i : Fin (n - 1)) : ℕ := i.1 + 2

/-- The target parabola `2l^2`. -/
def profileCenter (l : ℕ) : ℕ := 2 * l ^ 2

/-- The exact constraint `|m_l - 2l^2| <= l^(1+delta)`. -/
def InProfileWindow (delta : ℝ) (l m : ℕ) : Prop :=
  |(m : ℝ) - profileCenter l| ≤ (l : ℝ) ^ (1 + delta)

/-- A finite search range large enough to contain every value in the profile
window. -/
noncomputable def profileValueCap (delta : ℝ) (l : ℕ) : ℕ :=
  ⌈2 * (l : ℝ) ^ 2 + (l : ℝ) ^ (1 + delta)⌉₊ + 1

/-- The finite set of allowed values at scale `l`. -/
noncomputable def allowedValues (delta : ℝ) (l : ℕ) : Finset ℕ :=
  (Finset.range (profileValueCap delta l)).filter (InProfileWindow delta l)

lemma mem_allowedValues {delta : ℝ} {l m : ℕ} :
    m ∈ allowedValues delta l ↔ InProfileWindow delta l m := by
  rw [allowedValues, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h ↦ h.2
  · intro hm
    refine ⟨?_, hm⟩
    have hupper : (m : ℝ) ≤
        2 * (l : ℝ) ^ 2 + (l : ℝ) ^ (1 + delta) := by
      rw [InProfileWindow, abs_le] at hm
      dsimp only [profileCenter] at hm
      push_cast at hm
      linarith
    have hceil : m ≤ ⌈2 * (l : ℝ) ^ 2 + (l : ℝ) ^ (1 + delta)⌉₊ := by
      exact_mod_cast hupper.trans (Nat.le_ceil _)
    exact Nat.lt_succ_of_le hceil

/-- HLOZ's finite set `M_n(delta)` of constrained profiles. -/
noncomputable def constrainedProfiles (n : ℕ) (delta : ℝ) : Finset (Profile n) :=
  Fintype.piFinset fun i ↦ allowedValues delta (scaleIndex i)

def IsConstrainedProfile {n : ℕ} (delta : ℝ) (m : Profile n) : Prop :=
  ∀ i, InProfileWindow delta (scaleIndex i) (m i)

@[simp] lemma mem_constrainedProfiles {n : ℕ} {delta : ℝ} {m : Profile n} :
    m ∈ constrainedProfiles n delta ↔ IsConstrainedProfile delta m := by
  rw [constrainedProfiles, Fintype.mem_piFinset]
  exact forall_congr' fun i ↦ mem_allowedValues

/-- The central parabola itself, restricted to the finite profile index. -/
def centerProfile (n : ℕ) : Profile n :=
  fun i ↦ profileCenter (scaleIndex i)

lemma centerProfile_mem_constrainedProfiles (n : ℕ) (delta : ℝ) :
    centerProfile n ∈ constrainedProfiles n delta := by
  rw [mem_constrainedProfiles]
  intro i
  rw [InProfileWindow]
  simp only [centerProfile, sub_self, abs_zero]
  exact Real.rpow_nonneg (by positivity) _

/-- Read a finite profile as a list in increasing scale order. -/
def profileList {n : ℕ} (m : Profile n) : List ℕ := List.ofFn m

/-- Product of successive upcrossing transition masses. -/
def transitionProduct : List ℕ → ℝ
  | [] => 1
  | [_] => 1
  | a :: b :: rest => transitionMass a b * transitionProduct (b :: rest)

@[simp] lemma transitionProduct_nil : transitionProduct [] = 1 := rfl

@[simp] lemma transitionProduct_singleton (a : ℕ) : transitionProduct [a] = 1 := rfl

@[simp] lemma transitionProduct_cons_cons (a b : ℕ) (rest : List ℕ) :
    transitionProduct (a :: b :: rest) =
      transitionMass a b * transitionProduct (b :: rest) := rfl

lemma transitionProduct_nonneg (m : List ℕ) : 0 ≤ transitionProduct m := by
  induction m with
  | nil => norm_num
  | cons a tail ih =>
      cases tail with
      | nil => norm_num
      | cons b rest =>
          exact mul_nonneg (transitionMass_nonneg a b) ih

lemma transitionProduct_pos_of_all_pos (m : List ℕ)
    (hm : ∀ a ∈ m, 0 < a) : 0 < transitionProduct m := by
  induction m with
  | nil => norm_num
  | cons a tail ih =>
      cases tail with
      | nil => norm_num
      | cons b rest =>
          rw [transitionProduct_cons_cons]
          exact mul_pos (transitionMass_pos (hm a (by simp)) b)
            (ih (fun c hc ↦ hm c (by simp [hc])))

/-- The individual summand in Proposition A.7. -/
def profileWeight {n : ℕ} (m : Profile n) : ℝ :=
  transitionProduct (profileList m)

/-- The exact constrained-profile sum in Proposition A.7. -/
noncomputable def constrainedProfileWeight (n : ℕ) (delta : ℝ) : ℝ :=
  ∑ m ∈ constrainedProfiles n delta, profileWeight m

lemma profileWeight_nonneg {n : ℕ} (m : Profile n) : 0 ≤ profileWeight m :=
  transitionProduct_nonneg _

lemma profileWeight_centerProfile_pos (n : ℕ) :
    0 < profileWeight (centerProfile n) := by
  apply transitionProduct_pos_of_all_pos
  rw [profileList, List.forall_mem_ofFn_iff]
  intro i
  simp only [centerProfile, profileCenter, scaleIndex]
  positivity

lemma constrainedProfileWeight_nonneg (n : ℕ) (delta : ℝ) :
    0 ≤ constrainedProfileWeight n delta := by
  exact Finset.sum_nonneg fun m _ ↦ profileWeight_nonneg m

/-- In particular, the exact constrained-profile sum is never vacuous. -/
lemma constrainedProfileWeight_pos (n : ℕ) (delta : ℝ) :
    0 < constrainedProfileWeight n delta := by
  unfold constrainedProfileWeight
  exact Finset.sum_pos' (fun m _ ↦ profileWeight_nonneg m)
    ⟨centerProfile n, centerProfile_mem_constrainedProfiles n delta,
      profileWeight_centerProfile_pos n⟩

/-! ## Exact deviation reindexing -/

/-- The centered deviation `Delta_l = m_l - 2l^2`, kept integer-valued so
the change of variables is genuinely bijective. -/
def deviation {n : ℕ} (m : Profile n) (i : Fin (n - 1)) : ℤ :=
  (m i : ℤ) - profileCenter (scaleIndex i)

lemma deviation_add_center {n : ℕ} (m : Profile n) (i : Fin (n - 1)) :
    deviation m i + profileCenter (scaleIndex i) = m i := by
  simp [deviation]

lemma inProfileWindow_iff_deviation {n : ℕ} (delta : ℝ)
    (m : Profile n) (i : Fin (n - 1)) :
    InProfileWindow delta (scaleIndex i) (m i) ↔
      |(deviation m i : ℝ)| ≤ (scaleIndex i : ℝ) ^ (1 + delta) := by
  simp only [InProfileWindow, deviation, profileCenter]
  push_cast
  rfl

/-- The exact centered increment identity used just before (A.11). -/
lemma centered_increment_identity (l m₁ m₂ : ℕ) :
    (m₂ : ℤ) - m₁ =
      (4 * l + 2 : ℕ) +
        (((m₂ : ℤ) - profileCenter (l + 1)) -
          ((m₁ : ℤ) - profileCenter l)) := by
  simp only [profileCenter]
  push_cast
  ring

/-- Exact quadratic expansion behind the discrete Gaussian energy.  HLOZ
sum this identity and bound the two terms containing an extra `l⁻²`; no
asymptotic notation is used here. -/
lemma quadratic_increment_expansion {l d : ℝ} (hl : l ≠ 0) :
    (4 * l + 2 + d) ^ 2 / (8 * l ^ 2) =
      2 + 2 / l + 1 / (2 * l ^ 2) + d / l + d / (2 * l ^ 2) +
        d ^ 2 / (8 * l ^ 2) := by
  field_simp
  ring

/-! ## The finite first-moment and `Y`-to-`Y'` bookkeeping -/

/-- Uniform one-point bounds sum to a first-moment bound.  Applied to
`candidateBox n` and the thick-success events, this is the exact finite step
in (A.4) after Proposition A.3(1). -/
theorem card_mul_le_sum_of_uniform_lower {iota : Type*} (I : Finset iota)
    (q : ℝ) (f : iota → ℝ) (h : ∀ i ∈ I, q ≤ f i) :
    (I.card : ℝ) * q ≤ ∑ i ∈ I, f i := by
  calc
    (I.card : ℝ) * q = ∑ _i ∈ I, q := by simp
    _ ≤ ∑ i ∈ I, f i := Finset.sum_le_sum h

/-- If `thick` is a subevent of `successful`, their difference is exactly
the successful-but-not-thick loss. -/
theorem measureReal_success_eq_thick_add_loss
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsFiniteMeasure mu] {successful thick : Set Omega}
    (hs : MeasurableSet successful) (ht : MeasurableSet thick)
    (hsub : thick ⊆ successful) :
    mu.real successful = mu.real thick + mu.real (successful \ thick) := by
  have hd : Disjoint thick (successful \ thick) := by
    rw [Set.disjoint_left]
    intro omega homega hdiff
    exact hdiff.2 homega
  have hu : thick ∪ (successful \ thick) = successful := by
    ext omega
    constructor
    · rintro (homega | homega)
      · exact hsub homega
      · exact homega.1
    · intro homega
      by_cases hthick : omega ∈ thick
      · exact Or.inl hthick
      · exact Or.inr ⟨homega, hthick⟩
  calc
    mu.real successful = mu.real (thick ∪ (successful \ thick)) :=
      congrArg mu.real hu.symm
    _ = mu.real thick + mu.real (successful \ thick) :=
      measureReal_union (μ := mu) hd (hs.diff ht)
        (measure_ne_top mu thick) (measure_ne_top mu (successful \ thick))

/-- Abstract numerical form of (A.7): once the local-time concentration
argument bounds the lost successful mass by `epsilon` times the successful
mass, the advertised multiplicative comparison follows. -/
theorem one_sub_mul_success_le_thick
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsFiniteMeasure mu] {successful thick : Set Omega}
    (hs : MeasurableSet successful) (ht : MeasurableSet thick)
    (hsub : thick ⊆ successful) {epsilon : ℝ}
    (hloss : mu.real (successful \ thick) ≤ epsilon * mu.real successful) :
    (1 - epsilon) * mu.real successful ≤ mu.real thick := by
  have hsplit := measureReal_success_eq_thick_add_loss mu hs ht hsub
  linarith

/-- The easy half of (A.7). -/
theorem measureReal_thick_le_success
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsFiniteMeasure mu] {successful thick : Set Omega}
    (hsub : thick ⊆ successful) :
    mu.real thick ≤ mu.real successful := measureReal_mono hsub

end

end Erdos1165.AppendixFirstMoment
