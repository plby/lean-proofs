/-
**STANDALONE FLAT BUNDLE** of Erdős Problem #202.

Generated from the modular files under `Erdos/P202` and intended as
a one-file proof snapshot: one `import Mathlib`, no project-local imports.

Trust boundary, verified at the bottom with `#print axioms`:
  Mathlib/Lean core only (`propext`, `Classical.choice`, `Quot.sound`).
-/

import Mathlib

set_option autoImplicit false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.style.cdot false



/-! =============================================================
    Section from: Erdos/P202/P202Basic.lean
    ============================================================= -/

/-
Erdős Problem 202 — Statement layer.

Defines residue classes, admissible families, the extremal function `f(N)`,
the BFV scale `L(α, N) = exp(α · sqrt(log N · log log N))`, and the sharp
asymptotic predicate `HasErdos202Asymptotic`.

Reference: PDF in `docs/`. BFV (de la Bretèche–Ford–Vandehey) for the
unconditional bounds; spread-core variant for the matching upper bound
`f(N) = N · L(-(1+o(1)), N)`. This file formalizes the sharp asymptotic
for Erdős Problem 202 (PDF Theorem 1.1).  The integral / partial-summation
corollary about Erdős Problem 1190 (PDF Corollary 1.2) is formalized as
`Erdos202.erdos1190_main` in `Erdos/P1190/Proof.lean`.
-/


namespace Erdos202

open Filter
open Asymptotics
open scoped BigOperators

/-! ## §1 Residue classes and admissibility -/

/-- The integer residue class `a mod q` (only used for `0 < q`). -/
def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
  {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}

/-- A choice of one integer residue representative for every modulus in `Q`. -/
abbrev ResidueAssignment (Q : Finset ℕ) : Type :=
  {q : ℕ // q ∈ Q} → ℤ

/-- The selected residue classes for a finite set of moduli are pairwise disjoint. -/
def PairwiseDisjointResidues
    (Q : Finset ℕ) (a : ResidueAssignment Q) : Prop :=
  ∀ i j : {q : ℕ // q ∈ Q}, i ≠ j →
    Disjoint (residueClass i.1 (a i)) (residueClass j.1 (a j))

/-- Restrict residue representatives from a family to a subfamily. -/
def restrictAssignment {Q Q' : Finset ℕ}
    (a : ResidueAssignment Q) (hsub : Q' ⊆ Q) : ResidueAssignment Q' :=
  fun q => a ⟨q.1, hsub q.2⟩

lemma PairwiseDisjointResidues.mono
    {Q Q' : Finset ℕ} {a : ResidueAssignment Q}
    (hdisj : PairwiseDisjointResidues Q a) (hsub : Q' ⊆ Q) :
    PairwiseDisjointResidues Q' (restrictAssignment a hsub) := by
  intro i j hij
  let iQ : {q : ℕ // q ∈ Q} := ⟨i.1, hsub i.2⟩
  let jQ : {q : ℕ // q ∈ Q} := ⟨j.1, hsub j.2⟩
  have hijQ : iQ ≠ jQ := by
    intro h
    have hval : iQ.1 = jQ.1 :=
      congrArg (fun x : {q : ℕ // q ∈ Q} => x.1) h
    exact hij (Subtype.ext hval)
  simpa [restrictAssignment, iQ, jQ] using hdisj iQ jQ hijQ

/-- A finite set of moduli `Q ⊆ {1,...,N}` is admissible for Erdős 202: every
modulus is in `[1, N]`, and there exist residue choices making the
corresponding residue classes pairwise disjoint. -/
def Admissible (N : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) ∧
  ∃ a : ResidueAssignment Q, PairwiseDisjointResidues Q a

/-- There is an admissible family of size `r`. -/
def PossibleCard (N r : ℕ) : Prop :=
  ∃ Q : Finset ℕ, Admissible N Q ∧ Q.card = r

/-- The Erdős 202 extremal function `f(N) = max r : PossibleCard N r`.

Implemented via `Nat.findGreatest` over `[0, N]`, since the empty family is
always admissible (`0` is reachable) and `r ≤ |Q| ≤ N`. -/
noncomputable def f (N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (PossibleCard N) N

lemma admissible_card_le {N : ℕ} {Q : Finset ℕ} (hQ : Admissible N Q) :
    Q.card ≤ N := by
  have hsub : Q ⊆ Finset.Icc 1 N := by
    intro q hq
    exact Finset.mem_Icc.2 (hQ.1 q hq)
  have hcard := Finset.card_le_card hsub
  have hIcc : (Finset.Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  simpa [hIcc] using hcard

lemma admissible_empty (N : ℕ) : Admissible N (∅ : Finset ℕ) := by
  constructor
  · intro q hq
    simp at hq
  · refine ⟨fun _ => 0, ?_⟩
    intro i _j _hij
    cases i with
    | mk q hq => simp at hq

lemma admissible_singleton {N q : ℕ} (hq1 : 1 ≤ q) (hqN : q ≤ N) :
    Admissible N ({q} : Finset ℕ) := by
  constructor
  · intro r hr
    rw [Finset.mem_singleton] at hr
    subst r
    exact ⟨hq1, hqN⟩
  · refine ⟨fun _ => 0, ?_⟩
    intro i j hij
    have hi : i.1 = q := Finset.mem_singleton.mp i.2
    have hj : j.1 = q := Finset.mem_singleton.mp j.2
    exact False.elim (hij (Subtype.ext (hi.trans hj.symm)))

lemma possibleCard_zero (N : ℕ) : PossibleCard N 0 :=
  ⟨∅, admissible_empty N, by simp⟩

lemma possibleCard_one {N : ℕ} (hN : 1 ≤ N) : PossibleCard N 1 :=
  ⟨{N}, admissible_singleton hN le_rfl, by simp⟩

lemma possibleCard_le {N r : ℕ} (hr : PossibleCard N r) : r ≤ N := by
  rcases hr with ⟨Q, hQ, hcard⟩
  rw [← hcard]
  exact admissible_card_le hQ

lemma f_le (N : ℕ) : f N ≤ N := by
  classical
  unfold f
  exact Nat.findGreatest_le N

lemma possibleCard_f (N : ℕ) : PossibleCard N (f N) := by
  classical
  unfold f
  exact Nat.findGreatest_spec (P := PossibleCard N) (m := 0)
    (zero_le N) (possibleCard_zero N)

lemma le_f_of_possibleCard {N r : ℕ} (hr : PossibleCard N r) : r ≤ f N := by
  classical
  unfold f
  exact Nat.le_findGreatest (P := PossibleCard N) (possibleCard_le hr) hr

lemma one_le_f {N : ℕ} (hN : 1 ≤ N) : 1 ≤ f N :=
  le_f_of_possibleCard (possibleCard_one hN)

lemma exists_admissible_card_f (N : ℕ) :
    ∃ Q : Finset ℕ, Admissible N Q ∧ Q.card = f N :=
  possibleCard_f N

/-! ## §2 The BFV scale -/

/-- `Z(N) = sqrt(log N · log log N)`. The "L-scale" exponent. -/
noncomputable def Zscale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))

/-- `L(α, N) = exp(α · Z(N))`. -/
noncomputable def Lscale (α : ℝ) (N : ℕ) : ℝ :=
  Real.exp (α * Zscale N)

/-- `M(N) = sqrt(log N / log log N)`. The "shape" parameter; satisfies
`M(N) · log log N = Z(N)` and `K ≤ 3 M(N)` is the BFV pruning bound on the
number of distinct prime factors. -/
noncomputable def Mscale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)))

lemma Zscale_nonneg (N : ℕ) : 0 ≤ Zscale N :=
  Real.sqrt_nonneg _

lemma Zscale_pos_of_exp_one_lt_nat {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    0 < Zscale N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  rw [Zscale, Real.sqrt_pos]
  exact mul_pos hlog_pos hloglog_pos

lemma Zscale_eq_sqrt_log_mul_sqrt_loglog {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Zscale N =
      Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  rw [Zscale, Real.sqrt_mul hlog_nonneg]

lemma eventually_Zscale_pos : ∀ᶠ N : ℕ in atTop, 0 < Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hN
  apply Zscale_pos_of_exp_one_lt_nat
  exact lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)

lemma Mscale_nonneg (N : ℕ) : 0 ≤ Mscale N :=
  Real.sqrt_nonneg _

lemma Mscale_pos_of_exp_one_lt_nat {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    0 < Mscale N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  rw [Mscale, Real.sqrt_pos]
  exact div_pos hlog_pos hloglog_pos

lemma Mscale_mul_loglog_eq_Zscale {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Mscale N * Real.log (Real.log (N : ℝ)) = Zscale N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hleft_nonneg : 0 ≤ Mscale N * Real.log (Real.log (N : ℝ)) :=
    mul_nonneg (Mscale_nonneg N) hloglog_nonneg
  have hsq :
      (Mscale N * Real.log (Real.log (N : ℝ))) ^ 2 = (Zscale N) ^ 2 := by
    rw [Mscale, Zscale, mul_pow, Real.sq_sqrt, Real.sq_sqrt]
    · field_simp [hloglog_pos.ne']
    · exact mul_nonneg hlog_nonneg hloglog_nonneg
    · exact div_nonneg hlog_nonneg hloglog_nonneg
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
  · exact h
  · have hright_nonneg : 0 ≤ Zscale N := Zscale_nonneg N
    nlinarith

lemma Zscale_div_Mscale_eq_loglog {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Zscale N / Mscale N = Real.log (Real.log (N : ℝ)) := by
  have hMll := Mscale_mul_loglog_eq_Zscale hN
  have hMpos := Mscale_pos_of_exp_one_lt_nat hN
  rw [← hMll]
  field_simp [hMpos.ne']

lemma Mscale_mul_Zscale_eq_log {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Mscale N * Zscale N = Real.log (N : ℝ) := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hMll := Mscale_mul_loglog_eq_Zscale hN
  have hMsq : Mscale N ^ 2 =
      Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
    rw [Mscale, Real.sq_sqrt]
    exact div_nonneg hlog_nonneg hloglog_nonneg
  calc
    Mscale N * Zscale N
        = Mscale N * (Mscale N * Real.log (Real.log (N : ℝ))) := by rw [hMll]
    _ = Mscale N ^ 2 * Real.log (Real.log (N : ℝ)) := by ring
    _ = Real.log (N : ℝ) := by
          rw [hMsq]
          field_simp [hloglog_pos.ne']

lemma tendsto_loglog_div_log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
    have hsmall : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
        fun x : ℝ => Real.log x :=
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    exact hsmall.tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

lemma tendsto_loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop := by
  exact (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
    tendsto_natCast_atTop_atTop

lemma tendsto_sqrt_loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log (Real.log (N : ℝ)))) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp tendsto_loglog_nat_atTop

lemma eventually_sqrt_loglog_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  tendsto_sqrt_loglog_nat_atTop.eventually_ge_atTop A

lemma eventually_Mscale_le_log :
    ∀ᶠ N : ℕ in atTop, Mscale N ≤ Real.log (N : ℝ) := by
  filter_upwards [eventually_sqrt_loglog_ge 1,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_ge_one : 1 ≤ Real.log (Real.log (N : ℝ)) := by
    rw [← Real.one_le_sqrt]
    exact hsqrt
  rw [Mscale]
  rw [Real.sqrt_le_left hlog_nonneg]
  have hquot_le_log :
      Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) := by
    exact (div_le_iff₀ hloglog_pos).2 (by nlinarith [hlog_nonneg, hloglog_ge_one])
  have hlog_le_sq : Real.log (N : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by
    nlinarith [hlog_gt_one.le]
  exact hquot_le_log.trans hlog_le_sq

lemma eventually_Mscale_ge (A : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop, A ≤ Mscale N := by
  have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
  have htarget_pos : (0 : ℝ) < 1 / A ^ 2 := by positivity
  have hratio_small : ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) < 1 / A ^ 2 :=
    tendsto_loglog_div_log_nat_atTop.eventually_lt_const htarget_pos
  filter_upwards [hratio_small, Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))]
    with N hsmall hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_lt :
      Real.log (Real.log (N : ℝ)) < (1 / A ^ 2) * Real.log (N : ℝ) :=
    (div_lt_iff₀ hlog_pos).1 hsmall
  have hmulA :
      A ^ 2 * Real.log (Real.log (N : ℝ)) < Real.log (N : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hloglog_lt hA2
    field_simp [hA2.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hquot_ge :
      A ^ 2 ≤ Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) :=
    (le_div_iff₀ hloglog_pos).2 hmulA.le
  rw [Mscale]
  exact (Real.le_sqrt hA.le (div_nonneg hlog_pos.le hloglog_pos.le)).2 hquot_ge

lemma Lscale_pos (α : ℝ) (N : ℕ) : 0 < Lscale α N :=
  Real.exp_pos _

lemma Lscale_nonneg (α : ℝ) (N : ℕ) : 0 ≤ Lscale α N :=
  (Lscale_pos α N).le

lemma Lscale_zero (N : ℕ) : Lscale 0 N = 1 := by
  simp [Lscale]

lemma Lscale_add (α β : ℝ) (N : ℕ) :
    Lscale (α + β) N = Lscale α N * Lscale β N := by
  simp [Lscale, add_mul, Real.exp_add]

lemma Lscale_neg_mul (α : ℝ) (N : ℕ) :
    Lscale (-α) N * Lscale α N = 1 := by
  rw [← Lscale_add]
  simp [Lscale]

lemma Lscale_mono_in_alpha {α β : ℝ} (hαβ : α ≤ β) (N : ℕ) :
    Lscale α N ≤ Lscale β N := by
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hαβ (Zscale_nonneg N))

lemma Lscale_neg_le_one {α : ℝ} (hα : 0 ≤ α) (N : ℕ) :
    Lscale (-α) N ≤ 1 := by
  simpa [Lscale_zero] using Lscale_mono_in_alpha (α := -α) (β := 0) (by linarith) N

lemma log_nat_mul_Lscale {N : ℕ} (hN : 0 < N) (α : ℝ) :
    Real.log ((N : ℝ) * Lscale α N) = Real.log (N : ℝ) + α * Zscale N := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hL : Lscale α N ≠ 0 := (Lscale_pos α N).ne'
  rw [Real.log_mul hNreal hL, Lscale, Real.log_exp]

/-! ## §3 The sharp asymptotic -/

/-- `F : ℕ → ℕ` satisfies `F N = N · exp(-(1 + o(1)) · sqrt(log N · log log N))`,
in epsilon form: for every `ε > 0`, eventually
`N · L(-(1+ε), N) ≤ F N ≤ N · L(-(1-ε), N)`. -/
def HasErdos202Asymptotic (F : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (N : ℝ) * Lscale (-(1 + ε)) N ≤ (F N : ℝ) ∧
    (F N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N

/-- **Erdős Problem 202.** The sharp BFV-conjectured asymptotic for the
extremal function `f`. Statement layer only. -/
def Erdos202Statement : Prop :=
  HasErdos202Asymptotic f

/-! ## §4 The non-coprime gcd criterion (foundational lemma) -/

/-- The gcd intersection criterion: residue classes `a mod q` and `b mod r`
intersect iff `a ≡ b mod gcd(q, r)`. This is the formal version of equation
(7) in the PDF and underlies the entire chain construction. -/
lemma residueClass_inter_nonempty_iff
    {q r : ℕ} (_hq : 0 < q) (_hr : 0 < r) (a b : ℤ) :
    (residueClass q a ∩ residueClass r b).Nonempty ↔
      a ≡ b [ZMOD (Nat.gcd q r : ℤ)] := by
  constructor
  · rintro ⟨n, hnq, hnr⟩
    rw [residueClass, Set.mem_setOf_eq, Int.modEq_iff_dvd] at hnq hnr
    rw [Int.modEq_iff_dvd]
    have hdq : (Nat.gcd q r : ℤ) ∣ (q : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left q r
    have hdr : (Nat.gcd q r : ℤ) ∣ (r : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_right q r
    have hqa : (Nat.gcd q r : ℤ) ∣ a - n := dvd_trans hdq hnq
    have hrb : (Nat.gcd q r : ℤ) ∣ b - n := dvd_trans hdr hnr
    have hsub : (Nat.gcd q r : ℤ) ∣ (b - n) - (a - n) := dvd_sub hrb hqa
    convert hsub using 1
    ring
  · intro hab
    rw [Int.modEq_iff_dvd] at hab
    rcases hab with ⟨k, hk⟩
    let n : ℤ := a + (q : ℤ) * Nat.gcdA q r * k
    refine ⟨n, ?_, ?_⟩
    · rw [residueClass, Set.mem_setOf_eq, Int.modEq_iff_dvd]
      refine ⟨-(Nat.gcdA q r * k), ?_⟩
      simp [n]
      ring
    · rw [residueClass, Set.mem_setOf_eq, Int.modEq_iff_dvd]
      refine ⟨Nat.gcdB q r * k, ?_⟩
      have hbez := Nat.gcd_eq_gcd_ab q r
      calc
        b - n = (b - a) - (q : ℤ) * Nat.gcdA q r * k := by
          simp [n]
          ring
        _ = ((Nat.gcd q r : ℤ) * k) - (q : ℤ) * Nat.gcdA q r * k := by
          rw [hk]
        _ = ((q : ℤ) * Nat.gcdA q r + (r : ℤ) * Nat.gcdB q r) * k
              - (q : ℤ) * Nat.gcdA q r * k := by
          rw [hbez]
        _ = (r : ℤ) * (Nat.gcdB q r * k) := by
          ring

/-- Disjointness form of the gcd criterion. -/
lemma residueClass_disjoint_iff
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (a b : ℤ) :
    Disjoint (residueClass q a) (residueClass r b) ↔
      ¬ a ≡ b [ZMOD (Nat.gcd q r : ℤ)] := by
  rw [Set.disjoint_iff_inter_eq_empty]
  constructor
  · intro h hmod
    have hne : (residueClass q a ∩ residueClass r b).Nonempty :=
      (residueClass_inter_nonempty_iff hq hr a b).2 hmod
    exact hne.ne_empty h
  · intro hmod
    ext n
    constructor
    · intro hn
      exact False.elim (hmod ((residueClass_inter_nonempty_iff hq hr a b).1 ⟨n, hn⟩))
    · intro hn
      cases hn

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/P202Arithmetic.lean
    ============================================================= -/

/-
Erdős Problem 202 — Arithmetic layer.

Project-local definitions of `omega`, `rad`, `h(n) = ∏ p^{vₚ(n)} factors`,
and the exact prime-power block `exactBlock C q = ∏_{p ∈ C} p^{vₚ(q)}`.

All built on top of `Nat.factorization` to avoid drift between
`Nat.primeFactorsList`, `padicValNat`, and `multiplicity`.
-/


namespace Erdos202

open Finset
open scoped BigOperators

/-- The (multi-) set of prime divisors of `n`, as a `Finset`. Equal to
`n.factorization.support` for `n ≠ 0`. -/
def primeSupport (n : ℕ) : Finset ℕ :=
  n.factorization.support

/-- Number of distinct prime factors. Standard `ω(n)`. -/
def omega (n : ℕ) : ℕ :=
  (primeSupport n).card

/-- Radical of `n`: product of distinct prime divisors. -/
def rad (n : ℕ) : ℕ :=
  ∏ p ∈ primeSupport n, p

/-- BFV's `h(n)`: product of the prime *exponents* in the factorization of `n`.
Note: this is NOT the radical and is NOT `n` itself; it is the auxiliary
quantity that BFV pruning bounds by `exp(sqrt(log x))` on the surviving
moduli. -/
def hExp (n : ℕ) : ℕ :=
  ∏ p ∈ primeSupport n, n.factorization p

/-- The exact prime-power block of `q` along the prime set `C`:
`exactBlock C q = ∏_{p ∈ C} p^{vₚ(q)}`. -/
def exactBlock (C : Finset ℕ) (q : ℕ) : ℕ :=
  ∏ p ∈ C, p ^ q.factorization p

/-! ## Basic API -/

lemma hExp_pos (n : ℕ) : 0 < hExp n := by
  unfold hExp primeSupport
  exact Finset.prod_pos (fun _p hp =>
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp))

lemma hExp_one_le (n : ℕ) : 1 ≤ hExp n :=
  hExp_pos n

lemma hExp_one : hExp 1 = 1 := by
  simp [hExp, primeSupport]

lemma hExp_inv_sq_pos (n : ℕ) : 0 < (1 : ℝ) / ((hExp n : ℝ) ^ 2) := by
  have hn : 0 < (hExp n : ℝ) := by exact_mod_cast hExp_pos n
  positivity

lemma hExp_inv_sq_le_one (n : ℕ) : (1 : ℝ) / ((hExp n : ℝ) ^ 2) ≤ 1 := by
  have hn : 1 ≤ (hExp n : ℝ) := by exact_mod_cast hExp_one_le n
  have hpos : 0 < ((hExp n : ℝ) ^ 2) := by positivity
  field_simp [hpos.ne']
  nlinarith [sq_nonneg ((hExp n : ℝ) - 1)]

lemma prime_of_mem_primeSupport {n p : ℕ} (hp : p ∈ primeSupport n) : Nat.Prime p := by
  unfold primeSupport at hp
  rw [Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp

lemma mem_primeSupport_of_prime_dvd {n p : ℕ} (hp : Nat.Prime p) (hn : n ≠ 0)
    (hpn : p ∣ n) : p ∈ primeSupport n := by
  unfold primeSupport
  rw [Finsupp.mem_support_iff]
  exact hp.factorization_pos_of_dvd hn hpn |>.ne'

lemma coprime_of_disjoint_primeSupport {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hdisj : Disjoint (primeSupport m) (primeSupport n)) :
    Nat.Coprime m n := by
  refine Nat.coprime_of_dvd ?_
  intro p hp hpm hpn
  exact (Finset.disjoint_left.1 hdisj)
    (mem_primeSupport_of_prime_dvd hp hm hpm)
    (mem_primeSupport_of_prime_dvd hp hn hpn)

lemma primeSupport_disjoint_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    Disjoint (primeSupport m) (primeSupport n) := by
  rw [Finset.disjoint_left]
  intro p hpm hpn
  have hp : Nat.Prime p := prime_of_mem_primeSupport hpm
  have hpdm : p ∣ m := Nat.dvd_of_factorization_pos (by
    unfold primeSupport at hpm
    exact Finsupp.mem_support_iff.1 hpm)
  have hpdn : p ∣ n := Nat.dvd_of_factorization_pos (by
    unfold primeSupport at hpn
    exact Finsupp.mem_support_iff.1 hpn)
  have hp1 : p ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hpdm hpdn
  exact hp.not_dvd_one hp1

lemma primeSupport_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    primeSupport (m * n) = primeSupport m ∪ primeSupport n := by
  unfold primeSupport
  rw [Nat.factorization_mul_of_coprime hcop]
  exact Finsupp.support_add_eq (primeSupport_disjoint_of_coprime hcop)

lemma omega_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    omega (m * n) = omega m + omega n := by
  unfold omega
  rw [primeSupport_mul_of_coprime hcop]
  exact Finset.card_union_of_disjoint (primeSupport_disjoint_of_coprime hcop)

lemma hExp_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    hExp (m * n) = hExp m * hExp n := by
  unfold hExp
  rw [primeSupport_mul_of_coprime hcop]
  rw [Finset.prod_union (primeSupport_disjoint_of_coprime hcop)]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    have hpnot : p ∉ primeSupport n :=
      (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hp
    have hnzero : n.factorization p = 0 := by
      unfold primeSupport at hpnot
      exact Finsupp.notMem_support_iff.1 hpnot
    rw [Nat.factorization_mul_of_coprime hcop]
    simp [hnzero]
  · apply Finset.prod_congr rfl
    intro p hp
    have hpnot : p ∉ primeSupport m :=
      (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop).symm) hp
    have hmzero : m.factorization p = 0 := by
      unfold primeSupport at hpnot
      exact Finsupp.notMem_support_iff.1 hpnot
    rw [Nat.factorization_mul_of_coprime hcop]
    simp [hmzero]

lemma exactBlock_congr_on {C : Finset ℕ} {m n : ℕ}
    (h : ∀ p ∈ C, m.factorization p = n.factorization p) :
    exactBlock C m = exactBlock C n := by
  unfold exactBlock
  apply Finset.prod_congr rfl
  intro p hp
  rw [h p hp]

lemma exactBlock_dvd (C : Finset ℕ) (q : ℕ) : exactBlock C q ∣ q := by
  by_cases hq : q = 0
  · simp [hq]
  · nth_rw 2 [← Nat.prod_factorization_pow_eq_self hq]
    unfold exactBlock
    have hfilter :
        (∏ p ∈ C, p ^ q.factorization p) =
          ∏ p ∈ C.filter (fun p => p ∈ q.factorization.support),
            p ^ q.factorization p := by
      refine (Finset.prod_subset (Finset.filter_subset _ _) ?_).symm
      intro p hpC hpNot
      have hpnotmem : p ∉ q.factorization.support := by
        intro hp
        exact hpNot (Finset.mem_filter.2 ⟨hpC, hp⟩)
      have hzero : q.factorization p = 0 := by
        by_contra hne
        exact hpnotmem (Finsupp.mem_support_iff.2 hne)
      simp [hzero]
    rw [hfilter]
    exact Finset.prod_dvd_prod_of_subset
      (C.filter (fun p => p ∈ q.factorization.support))
      q.factorization.support
      (fun p => p ^ q.factorization p)
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)

lemma factorization_exactBlock_of_mem {C : Finset ℕ} {q p : ℕ}
    (hC : ∀ r ∈ C, Nat.Prime r) (hpC : p ∈ C) :
    (exactBlock C q).factorization p = q.factorization p := by
  unfold exactBlock
  have hprod_ne : ∀ x ∈ C, x ^ q.factorization x ≠ 0 := by
    intro x hx
    exact pow_ne_zero _ (hC x hx).ne_zero
  rw [Nat.factorization_prod hprod_ne, Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single p]
  · rw [(hC p hpC).factorization_pow, Finsupp.single_eq_same]
  · intro x hx hxp
    rw [(hC x hx).factorization_pow]
    exact Finsupp.single_eq_of_ne hxp.symm
  · intro hpnot
    exact (hpnot hpC).elim

lemma primeSupport_exactBlock {C : Finset ℕ} {q : ℕ}
    (hC : ∀ p ∈ C, Nat.Prime p)
    (hCq : C ⊆ primeSupport q) :
    primeSupport (exactBlock C q) = C := by
  unfold primeSupport exactBlock
  ext p
  have hprod_ne : ∀ x ∈ C, x ^ q.factorization x ≠ 0 := by
    intro x hx
    exact pow_ne_zero _ (hC x hx).ne_zero
  rw [Nat.factorization_prod hprod_ne, Finsupp.mem_support_iff]
  constructor
  · intro hsum
    by_contra hpC
    apply hsum
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_zero_iff]
    intro x hx
    have hxne : x ≠ p := by
      intro hxp
      exact hpC (hxp ▸ hx)
    rw [(hC x hx).factorization_pow]
    exact Finsupp.single_eq_of_ne hxne.symm
  · intro hpC
    have hp : Nat.Prime p := hC p hpC
    have hqpos : q.factorization p ≠ 0 := Finsupp.mem_support_iff.1 (hCq hpC)
    intro hsum
    rw [Finsupp.finset_sum_apply] at hsum
    have hterm := (Finset.sum_eq_zero_iff.mp hsum) p hpC
    rw [hp.factorization_pow, Finsupp.single_eq_same] at hterm
    exact hqpos hterm

lemma omega_exactBlock {C : Finset ℕ} {q : ℕ}
    (hC : ∀ p ∈ C, Nat.Prime p)
    (hCq : C ⊆ primeSupport q) :
    omega (exactBlock C q) = C.card := by
  simp [omega, primeSupport_exactBlock hC hCq]

lemma hExp_exactBlock_le_hExp (C : Finset ℕ) (q : ℕ) :
    hExp (exactBlock C q) ≤ hExp q := by
  by_cases hq : q = 0
  · simp [hExp, primeSupport, exactBlock, hq]
  · have hdvd : exactBlock C q ∣ q := exactBlock_dvd C q
    have hdne : exactBlock C q ≠ 0 := by
      exact (Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hq)).ne'
    have hlefac : (exactBlock C q).factorization ≤ q.factorization :=
      (Nat.factorization_le_iff_dvd hdne hq).2 hdvd
    have hsub : primeSupport (exactBlock C q) ⊆ primeSupport q := by
      intro p hp
      unfold primeSupport at hp ⊢
      rw [Finsupp.mem_support_iff] at hp ⊢
      exact (Nat.pos_of_ne_zero hp).trans_le (hlefac p) |>.ne'
    unfold hExp
    have hprod1 :
        (∏ p ∈ primeSupport (exactBlock C q), (exactBlock C q).factorization p)
          ≤ ∏ p ∈ primeSupport (exactBlock C q), q.factorization p := by
      exact Finset.prod_le_prod' (fun p _hp => hlefac p)
    have hprod2 :
        (∏ p ∈ primeSupport (exactBlock C q), q.factorization p)
          ≤ ∏ p ∈ primeSupport q, q.factorization p := by
      exact Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp _hpnot => by
        unfold primeSupport at hp
        rw [Finsupp.mem_support_iff] at hp
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp))
    exact hprod1.trans hprod2

lemma hExp_le_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    hExp m ≤ hExp n := by
  have hm : m ≠ 0 := by
    intro hm0
    subst m
    exact hn (zero_dvd_iff.mp hmn)
  have hlefac : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hm hn).2 hmn
  have hsub : primeSupport m ⊆ primeSupport n := by
    intro p hp
    unfold primeSupport at hp ⊢
    rw [Finsupp.mem_support_iff] at hp ⊢
    exact (Nat.pos_of_ne_zero hp).trans_le (hlefac p) |>.ne'
  unfold hExp
  have hprod1 :
      (∏ p ∈ primeSupport m, m.factorization p)
        ≤ ∏ p ∈ primeSupport m, n.factorization p := by
    exact Finset.prod_le_prod' (fun p _hp => hlefac p)
  have hprod2 :
      (∏ p ∈ primeSupport m, n.factorization p)
        ≤ ∏ p ∈ primeSupport n, n.factorization p := by
    exact Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp _hpnot => by
      unfold primeSupport at hp
      rw [Finsupp.mem_support_iff] at hp
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp))
  exact hprod1.trans hprod2

/-- The "remaining support" after removing a fixed product `P`. Used in the
chain construction: `A(q) = primeSupport (q / P)`. -/
def remainingSupport (P q : ℕ) : Finset ℕ :=
  primeSupport (q / P)

lemma primeSupport_subset_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    primeSupport m ⊆ primeSupport n := by
  have hm : m ≠ 0 := by
    intro hm0
    subst m
    exact hn (zero_dvd_iff.mp hmn)
  have hle : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hm hn).2 hmn
  intro p hp
  unfold primeSupport at hp ⊢
  rw [Finsupp.mem_support_iff] at hp ⊢
  intro hnzero
  exact hp (Nat.eq_zero_of_le_zero (by simpa [hnzero] using hle p))

lemma omega_le_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    omega m ≤ omega n := by
  unfold omega
  exact Finset.card_le_card (primeSupport_subset_of_dvd hmn hn)

lemma primeSupport_div_subset_of_dvd {P q : ℕ} (hPq : P ∣ q) (hq : q ≠ 0) :
    primeSupport (q / P) ⊆ primeSupport q :=
  primeSupport_subset_of_dvd (by
    refine ⟨P, ?_⟩
    exact (Nat.div_mul_cancel hPq).symm) hq

lemma primeSupport_eq_union_of_dvd {P q : ℕ}
    (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0) :
    primeSupport q = primeSupport P ∪ primeSupport (q / P) := by
  ext p
  unfold primeSupport
  rw [Finset.mem_union]
  simp only [Finsupp.mem_support_iff]
  constructor
  · intro hqfac
    by_cases hPfac : P.factorization p = 0
    · right
      have hdivfac :
          (q / P).factorization p = q.factorization p - P.factorization p := by
        rw [Nat.factorization_div hPq]
        rfl
      rw [hdivfac, hPfac, Nat.sub_zero]
      exact hqfac
    · exact Or.inl hPfac
  · rintro (hPfac | hdivfac)
    · have hle : P.factorization ≤ q.factorization :=
        (Nat.factorization_le_iff_dvd hP hq).2 hPq
      intro hqzero
      exact hPfac (Nat.eq_zero_of_le_zero (by simpa [hqzero] using hle p))
    · have hmem : p ∈ primeSupport (q / P) := by
        unfold primeSupport
        rw [Finsupp.mem_support_iff]
        exact hdivfac
      have hmemq := primeSupport_div_subset_of_dvd hPq hq hmem
      unfold primeSupport at hmemq
      rwa [Finsupp.mem_support_iff] at hmemq

lemma mem_remainingSupport_iff_factorization_lt {P q p : ℕ} (hPq : P ∣ q) :
    p ∈ remainingSupport P q ↔ P.factorization p < q.factorization p := by
  unfold remainingSupport primeSupport
  rw [Finsupp.mem_support_iff, Nat.factorization_div hPq]
  exact Nat.sub_ne_zero_iff_lt

lemma omega_eq_add_omega_div_of_dvd {P q : ℕ}
    (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0)
    (hdisj : Disjoint (primeSupport P) (primeSupport (q / P))) :
    omega q = omega P + omega (q / P) := by
  unfold omega
  rw [primeSupport_eq_union_of_dvd hPq hP hq, Finset.card_union_of_disjoint hdisj]

lemma omega_div_eq_sub_omega_of_dvd {P q : ℕ}
    (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0)
    (hdisj : Disjoint (primeSupport P) (primeSupport (q / P))) :
    omega (q / P) = omega q - omega P := by
  have hsum := omega_eq_add_omega_div_of_dvd hPq hP hq hdisj
  omega

lemma eq_one_of_omega_eq_zero {n : ℕ} (hn : n ≠ 0) (hω : omega n = 0) :
    n = 1 := by
  have hsupp : primeSupport n = ∅ := by
    have hcard : (primeSupport n).card = 0 := by simpa [omega] using hω
    exact Finset.card_eq_zero.mp hcard
  unfold primeSupport at hsupp
  have hprod_eq_one : n.factorization.prod (fun p e => p ^ e) = 1 := by
    unfold Finsupp.prod
    rw [hsupp]
    simp
  have hprod := Nat.prod_factorization_pow_eq_self hn
  rw [← hprod]
  exact hprod_eq_one

lemma gcd_dvd_of_disjoint_remainingSupport {P q r : ℕ}
    (hPq : P ∣ q) (hPr : P ∣ r)
    (hP : P ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hdisj : Disjoint (remainingSupport P q) (remainingSupport P r)) :
    Nat.gcd q r ∣ P := by
  rw [← Nat.factorization_le_iff_dvd (by
      intro hg
      exact hq (Nat.gcd_eq_zero_iff.mp hg).1) hP]
  rw [Nat.factorization_gcd hq hr]
  intro p
  rw [Finsupp.inf_apply]
  have hPq_fac : P.factorization p ≤ q.factorization p :=
    (Nat.factorization_le_iff_dvd hP hq).2 hPq p
  have hPr_fac : P.factorization p ≤ r.factorization p :=
    (Nat.factorization_le_iff_dvd hP hr).2 hPr p
  by_cases hqextra : P.factorization p < q.factorization p
  · have hrnot : ¬ P.factorization p < r.factorization p := by
      intro hrextra
      exact (Finset.disjoint_left.1 hdisj)
        ((mem_remainingSupport_iff_factorization_lt hPq).2 hqextra)
        ((mem_remainingSupport_iff_factorization_lt hPr).2 hrextra)
    have hrle : r.factorization p ≤ P.factorization p := le_of_not_gt hrnot
    exact le_trans (min_le_right _ _) hrle
  · have hqle : q.factorization p ≤ P.factorization p := le_of_not_gt hqextra
    exact le_trans (min_le_left _ _) hqle

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/SpreadDefs.lean
    ============================================================= -/

/-
Erdős Problem 202 — Spread / dense-core layer, definitions.

Bare definitions only: `UniformFamily`, `SpreadFamily`,
`PairwiseDisjointMembers`. Split out from `SpreadCore.lean` so the
ParkPham layer can use these definitions without importing the
spread-disjointness theorem (which would create an import cycle with
`SpreadCore.lean` and the ParkPham proof).
-/


namespace Erdos202

open Finset
open scoped BigOperators

/-- A `k`-uniform family: every member has cardinality exactly `k`. -/
def UniformFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ S ∈ A, S.card = k

/-- A `κ`-spread family: for every nonempty `T`, the count of members
containing `T` is at most `|A| / κ^{|T|}`. -/
def SpreadFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (κ : ℝ) : Prop :=
  ∀ T : Finset α, T.Nonempty →
    ((A.filter fun S => T ⊆ S).card : ℝ) ≤
      (A.card : ℝ) / κ ^ T.card

/-- Members of `B` are pairwise disjoint. -/
def PairwiseDisjointMembers {α : Type*} [DecidableEq α]
    (B : Finset (Finset α)) : Prop :=
  ∀ S ∈ B, ∀ T ∈ B, S ≠ T → Disjoint S T

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/ParkPham/BooleanFamilies.lean
    ============================================================= -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 1.

Finite Boolean families, upper closures, increasing predicate, minimal
members, and the `ell(U)` complexity bound used by the Park–Pham
expectation-threshold theorem.

All definitions live over a finite ground universe `X : Finset α`. We
avoid any general measure theory; subsets of `X` are represented as
`Finset α` filtered by `S ⊆ X`.
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- The upper closure of `A` inside the universe `X`: the set of subsets
`T ⊆ X` that contain some member of `A`. -/
def upClosureIn (X : Finset α) (A : Finset (Finset α)) : Finset (Finset α) :=
  X.powerset.filter fun T => ∃ S ∈ A, S ⊆ T

@[simp]
lemma mem_upClosureIn {X : Finset α} {A : Finset (Finset α)} {T : Finset α} :
    T ∈ upClosureIn X A ↔ T ⊆ X ∧ ∃ S ∈ A, S ⊆ T := by
  simp [upClosureIn, mem_powerset]

/-- A family contained in the ground universe is contained in its upper
closure. -/
lemma subset_upClosureIn {X : Finset α} {A : Finset (Finset α)}
    (hAX : ∀ S ∈ A, S ⊆ X) :
    A ⊆ upClosureIn X A := by
  intro S hS
  exact mem_upClosureIn.mpr ⟨hAX S hS, S, hS, subset_refl _⟩

/-- Upper closure is monotone in the generating family. -/
lemma upClosureIn_mono {X : Finset α} {A B : Finset (Finset α)}
    (hAB : A ⊆ B) :
    upClosureIn X A ⊆ upClosureIn X B := by
  intro T hT
  rcases mem_upClosureIn.mp hT with ⟨hTX, S, hSA, hST⟩
  exact mem_upClosureIn.mpr ⟨hTX, S, hAB hSA, hST⟩

/-- A nonempty upper closure has a nonempty generating family. -/
lemma nonempty_of_upClosureIn_nonempty {X : Finset α} {A : Finset (Finset α)}
    (h : (upClosureIn X A).Nonempty) :
    A.Nonempty := by
  rcases h with ⟨T, hT⟩
  rcases mem_upClosureIn.mp hT with ⟨_, S, hSA, _⟩
  exact ⟨S, hSA⟩

/-- The empty set is in an upper closure exactly when it is one of the
generators. -/
lemma empty_mem_upClosureIn_iff {X : Finset α} {A : Finset (Finset α)} :
    (∅ : Finset α) ∈ upClosureIn X A ↔ (∅ : Finset α) ∈ A := by
  constructor
  · intro h
    rcases mem_upClosureIn.mp h with ⟨_, S, hSA, hSempty⟩
    have hS_eq : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      simpa using hSempty hx
    simpa [hS_eq] using hSA
  · intro h
    exact mem_upClosureIn.mpr ⟨Finset.empty_subset X, ∅, h, subset_refl _⟩

lemma empty_not_mem_upClosureIn_iff {X : Finset α} {A : Finset (Finset α)} :
    (∅ : Finset α) ∉ upClosureIn X A ↔ (∅ : Finset α) ∉ A := by
  rw [empty_mem_upClosureIn_iff]

/-- A family `U ⊆ X.powerset` is increasing if it is closed under taking
supersets inside `X`. -/
def IncreasingIn (X : Finset α) (U : Finset (Finset α)) : Prop :=
  ∀ S ∈ U, ∀ T : Finset α, T ⊆ X → S ⊆ T → T ∈ U

/-- The upper closure of any family is increasing. -/
lemma increasingIn_upClosureIn (X : Finset α) (A : Finset (Finset α)) :
    IncreasingIn X (upClosureIn X A) := by
  intro S hS T hTX hST
  rcases mem_upClosureIn.mp hS with ⟨_, S₀, hS₀A, hS₀S⟩
  exact mem_upClosureIn.mpr ⟨hTX, S₀, hS₀A, hS₀S.trans hST⟩

/-- An increasing family inside `X` is equal to its upper closure. -/
lemma upClosureIn_eq_self_of_increasing {X : Finset α} {U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U) :
    upClosureIn X U = U := by
  ext T
  constructor
  · intro hT
    rcases mem_upClosureIn.mp hT with ⟨hTX, S, hSU, hST⟩
    exact hIncr S hSU T hTX hST
  · intro hTU
    exact mem_upClosureIn.mpr ⟨hUX T hTU, T, hTU, subset_refl _⟩

/-- In an increasing family, the upper closure generated by any member is
contained in the family. -/
lemma upClosureIn_singleton_subset_of_mem_increasing
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α}
    (hIncr : IncreasingIn X U) (hS : S ∈ U) :
    upClosureIn X {S} ⊆ U := by
  intro T hT
  rcases mem_upClosureIn.mp hT with ⟨hTX, R, hR, hRT⟩
  have hR_eq : R = S := by simpa using hR
  exact hIncr S hS T hTX (by simpa [hR_eq] using hRT)

/-- Taking upper closure twice does not change the family. -/
lemma upClosureIn_idempotent (X : Finset α) (A : Finset (Finset α)) :
    upClosureIn X (upClosureIn X A) = upClosureIn X A := by
  exact upClosureIn_eq_self_of_increasing
    (fun S hS => (mem_upClosureIn.mp hS).1)
    (increasingIn_upClosureIn X A)

omit [DecidableEq α] in
/-- A nonempty increasing family on `X` contains the top element `X`. -/
lemma top_mem_of_nonempty_increasing {X : Finset α} {U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hU : U.Nonempty) :
    X ∈ U := by
  rcases hU with ⟨S, hS⟩
  exact hIncr S hS X (subset_refl X) (hUX S hS)

omit [DecidableEq α] in
/-- An increasing family on `X` that contains `∅` is the whole Boolean cube. -/
lemma eq_powerset_of_empty_mem_increasing {X : Finset α} {U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hEmpty : (∅ : Finset α) ∈ U) :
    U = X.powerset := by
  ext S
  constructor
  · intro hS
    exact Finset.mem_powerset.mpr (hUX S hS)
  · intro hS
    exact hIncr ∅ hEmpty S (Finset.mem_powerset.mp hS) (Finset.empty_subset S)

/-- Minimal members of `U`: members with no proper subset also in `U`. -/
def minimalMembersIn (_X : Finset α) (U : Finset (Finset α)) : Finset (Finset α) :=
  U.filter fun S => ∀ T ∈ U, ¬ T ⊂ S

@[simp]
lemma mem_minimalMembersIn {X : Finset α} {U : Finset (Finset α)} {S : Finset α} :
    S ∈ minimalMembersIn X U ↔ S ∈ U ∧ ∀ T ∈ U, ¬ T ⊂ S := by
  simp [minimalMembersIn]

lemma minimalMembersIn_subset {X : Finset α} {U : Finset (Finset α)} :
    minimalMembersIn X U ⊆ U := by
  intro S hS
  exact (mem_minimalMembersIn.mp hS).1

/-- Distinct minimal members cannot be related by strict inclusion. -/
lemma not_ssubset_of_mem_minimalMembersIn
    {X : Finset α} {U : Finset (Finset α)} {S T : Finset α}
    (hS : S ∈ minimalMembersIn X U) (hT : T ∈ minimalMembersIn X U) :
    ¬ S ⊂ T := by
  exact (mem_minimalMembersIn.mp hT).2 S ((mem_minimalMembersIn.mp hS).1)

/-- Minimal members form an antichain under inclusion. -/
lemma eq_of_subset_of_mem_minimalMembersIn
    {X : Finset α} {U : Finset (Finset α)} {S T : Finset α}
    (hS : S ∈ minimalMembersIn X U) (hT : T ∈ minimalMembersIn X U)
    (hST : S ⊆ T) :
    S = T := by
  by_contra hne
  exact not_ssubset_of_mem_minimalMembersIn hS hT (hST.ssubset_of_ne hne)

/-- Inclusion antichain predicate for a finite family of finite sets. -/
def InclusionAntichain (A : Finset (Finset α)) : Prop :=
  ∀ S ∈ A, ∀ T ∈ A, S ⊆ T → T ⊆ S

omit [DecidableEq α] in
lemma InclusionAntichain.eq_of_subset {A : Finset (Finset α)}
    (hA : InclusionAntichain A) {S T : Finset α}
    (hS : S ∈ A) (hT : T ∈ A) (hST : S ⊆ T) :
    S = T :=
  le_antisymm hST (hA S hS T hT hST)

/-- Minimal members form an inclusion antichain. -/
lemma minimalMembersIn_inclusionAntichain (X : Finset α) (U : Finset (Finset α)) :
    InclusionAntichain (minimalMembersIn X U) := by
  intro S hS T hT hST
  have hEq : S = T := eq_of_subset_of_mem_minimalMembersIn hS hT hST
  simp [hEq]

/-- Taking minimal members is idempotent. -/
lemma minimalMembersIn_idempotent (X : Finset α) (U : Finset (Finset α)) :
    minimalMembersIn X (minimalMembersIn X U) = minimalMembersIn X U := by
  ext S
  constructor
  · intro hS
    exact minimalMembersIn_subset hS
  · intro hS
    refine mem_minimalMembersIn.mpr ⟨hS, ?_⟩
    intro T hT hTS
    exact not_ssubset_of_mem_minimalMembersIn hT hS hTS

/-- The complexity parameter `ell(U)`: max card of a minimal member,
clamped at 2 so that `Real.log (ell U) ≥ Real.log 2 > 0`. -/
noncomputable def ell (X : Finset α) (U : Finset (Finset α)) : ℕ :=
  max 2 ((minimalMembersIn X U).sup Finset.card)

lemma two_le_ell (X : Finset α) (U : Finset (Finset α)) : 2 ≤ ell X U :=
  le_max_left _ _

lemma ell_pos (X : Finset α) (U : Finset (Finset α)) : 0 < ell X U :=
  lt_of_lt_of_le (by norm_num) (two_le_ell X U)

lemma card_le_ell_of_mem_minimalMembersIn
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α}
    (hS : S ∈ minimalMembersIn X U) :
    S.card ≤ ell X U := by
  unfold ell
  exact (Finset.le_sup (s := minimalMembersIn X U) (f := Finset.card) hS).trans
    (le_max_right _ _)

/-- The complexity parameter is unchanged by replacing a family with its minimal
members. -/
lemma ell_minimalMembersIn_eq (X : Finset α) (U : Finset (Finset α)) :
    ell X (minimalMembersIn X U) = ell X U := by
  unfold ell
  rw [minimalMembersIn_idempotent]

omit [DecidableEq α] in
/-- A one-element member of a family gives a singleton member. -/
lemma exists_singleton_mem_of_mem_card_eq_one
    {U : Finset (Finset α)} {S : Finset α}
    (hS : S ∈ U) (hcard : S.card = 1) :
    ∃ a : α, ({a} : Finset α) ∈ U := by
  rcases Finset.card_eq_one.mp hcard with ⟨a, rfl⟩
  exact ⟨a, hS⟩

/-- A one-element minimal member of a family gives a singleton member of the
family. -/
lemma exists_singleton_mem_of_mem_minimalMembersIn_card_eq_one
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α}
    (hS : S ∈ minimalMembersIn X U) (hcard : S.card = 1) :
    ∃ a : α, ({a} : Finset α) ∈ U :=
  exists_singleton_mem_of_mem_card_eq_one (minimalMembersIn_subset hS) hcard

/-- Every member of `U` contains a minimal member of `U` (as a subset). -/
lemma exists_minimal_subset
    {X : Finset α} {U : Finset (Finset α)}
    {S : Finset α} (hS : S ∈ U) :
    ∃ T ∈ minimalMembersIn X U, T ⊆ S := by
  classical
  -- Pick T₀ ⊆ S in U with minimum card.
  let candidates : Finset (Finset α) := U.filter fun T => T ⊆ S
  have hSc : S ∈ candidates := by
    simp [candidates, hS, subset_refl]
  rcases candidates.exists_min_image Finset.card ⟨S, hSc⟩ with ⟨T₀, hT₀, hmin⟩
  have hT₀U : T₀ ∈ U := (Finset.mem_filter.mp hT₀).1
  have hT₀S : T₀ ⊆ S := (Finset.mem_filter.mp hT₀).2
  refine ⟨T₀, mem_minimalMembersIn.mpr ⟨hT₀U, ?_⟩, hT₀S⟩
  intro T hTU hT_lt
  -- T ⊂ T₀ ⊆ S, so T ⊆ S, so T ∈ candidates, hence T₀.card ≤ T.card,
  -- contradicting T.card < T₀.card.
  have hTS : T ⊆ S := hT_lt.subset.trans hT₀S
  have hTcand : T ∈ candidates := by
    simp [candidates, hTU, hTS]
  have : T₀.card ≤ T.card := hmin T hTcand
  have hlt : T.card < T₀.card := Finset.card_lt_card hT_lt
  exact absurd this (not_le.mpr hlt)

/-- If `U` is nonempty, then its canonical minimal-member cover is nonempty. -/
lemma minimalMembersIn_nonempty_of_nonempty
    {X : Finset α} {U : Finset (Finset α)} (hU : U.Nonempty) :
    (minimalMembersIn X U).Nonempty := by
  rcases hU with ⟨S, hS⟩
  rcases exists_minimal_subset (X := X) hS with ⟨T, hT, _⟩
  exact ⟨T, hT⟩

/-- If `∅` is not a member of `U`, then every minimal member of `U` is
nonempty. -/
lemma nonempty_of_mem_minimalMembersIn_of_empty_not_mem
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α}
    (hEmpty : (∅ : Finset α) ∉ U) (hS : S ∈ minimalMembersIn X U) :
    S.Nonempty := by
  have hSU : S ∈ U := minimalMembersIn_subset hS
  by_contra hS_empty
  have hS_eq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS_empty
  exact hEmpty (by simpa [hS_eq] using hSU)

/-- If `U` has neither `∅` nor singleton members, then every minimal member has
cardinality at least two. -/
lemma two_le_card_of_mem_minimalMembersIn_of_empty_not_mem_of_no_singleton
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α}
    (hEmpty : (∅ : Finset α) ∉ U)
    (hNoSingleton : ∀ a : α, ({a} : Finset α) ∉ U)
    (hS : S ∈ minimalMembersIn X U) :
    2 ≤ S.card := by
  have hnonempty : S.Nonempty :=
    nonempty_of_mem_minimalMembersIn_of_empty_not_mem hEmpty hS
  have hcard_pos : 1 ≤ S.card := Finset.one_le_card.mpr hnonempty
  by_cases hcard_one : S.card = 1
  · rcases exists_singleton_mem_of_mem_minimalMembersIn_card_eq_one hS hcard_one with ⟨a, ha⟩
    exact False.elim ((hNoSingleton a) ha)
  · omega

/-- An increasing family is generated by its minimal members. -/
lemma upClosureIn_minimalMembersIn_eq_of_increasing
    {X : Finset α} {U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U) :
    upClosureIn X (minimalMembersIn X U) = U := by
  ext S
  constructor
  · intro hS
    rcases mem_upClosureIn.mp hS with ⟨hSX, T, hTmin, hTS⟩
    exact hIncr T (minimalMembersIn_subset hTmin) S hSX hTS
  · intro hSU
    rcases exists_minimal_subset (X := X) hSU with ⟨T, hTmin, hTS⟩
    exact mem_upClosureIn.mpr ⟨hUX S hSU, T, hTmin, hTS⟩

/-- For an inclusion-antichain generator, the minimal members of its upper
closure are exactly the generators. -/
lemma mem_minimalMembersIn_upClosureIn_iff_of_inclusionAntichain
    {X : Finset α} {A : Finset (Finset α)}
    (hAnti : InclusionAntichain A)
    (hAX : ∀ S ∈ A, S ⊆ X)
    {S : Finset α} :
    S ∈ minimalMembersIn X (upClosureIn X A) ↔ S ∈ A := by
  constructor
  · intro hS
    rcases mem_minimalMembersIn.mp hS with ⟨hSup, hmin⟩
    rcases mem_upClosureIn.mp hSup with ⟨_, S₀, hS₀A, hS₀S⟩
    have hS₀_up : S₀ ∈ upClosureIn X A :=
      mem_upClosureIn.mpr ⟨hAX S₀ hS₀A, S₀, hS₀A, subset_refl _⟩
    have hS₀_not_lt : ¬ S₀ ⊂ S := hmin S₀ hS₀_up
    have hS₀_eq_S : S₀ = S := by
      by_contra hne
      exact hS₀_not_lt (hS₀S.ssubset_of_ne hne)
    simpa [← hS₀_eq_S] using hS₀A
  · intro hSA
    refine mem_minimalMembersIn.mpr ⟨?_, ?_⟩
    · exact mem_upClosureIn.mpr ⟨hAX S hSA, S, hSA, subset_refl _⟩
    · intro T hTup hTlt
      rcases mem_upClosureIn.mp hTup with ⟨_, S₀, hS₀A, hS₀T⟩
      have hS₀S : S₀ ⊆ S := hS₀T.trans hTlt.subset
      have hSS₀ : S ⊆ S₀ := hAnti S₀ hS₀A S hSA hS₀S
      have hST : S ⊆ T := hSS₀.trans hS₀T
      have hTS : T ⊆ S := hTlt.subset
      have hEq : T = S := le_antisymm hTS hST
      exact hTlt.ne hEq

/-- For an inclusion-antichain generator, the minimal-member set of its upper
closure is the generator itself. -/
lemma minimalMembersIn_upClosureIn_eq_of_inclusionAntichain
    {X : Finset α} {A : Finset (Finset α)}
    (hAnti : InclusionAntichain A)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    minimalMembersIn X (upClosureIn X A) = A := by
  ext S
  exact mem_minimalMembersIn_upClosureIn_iff_of_inclusionAntichain hAnti hAX

/-- For an inclusion-antichain generator, `ell` of its upper closure is the
clamped maximum generator size. -/
theorem ell_upClosure_eq_of_inclusionAntichain
    {X : Finset α} {A : Finset (Finset α)}
    (hAnti : InclusionAntichain A)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    ell X (upClosureIn X A) = max 2 (A.sup Finset.card) := by
  unfold ell
  rw [minimalMembersIn_upClosureIn_eq_of_inclusionAntichain hAnti hAX]

/-- Minimal members of the upper closure of a `k`-uniform family have card
at most `k`. -/
lemma minimalMembersIn_upClosureIn_card_le
    {X : Finset α} {A : Finset (Finset α)} {k : ℕ}
    (hUniform : Erdos202.UniformFamily A k)
    (hAX : ∀ S ∈ A, S ⊆ X)
    {S : Finset α} (hS : S ∈ minimalMembersIn X (upClosureIn X A)) :
    S.card ≤ k := by
  classical
  rcases mem_minimalMembersIn.mp hS with ⟨hSup, hmin⟩
  rcases mem_upClosureIn.mp hSup with ⟨hSX, S₀, hS₀A, hS₀S⟩
  -- S₀ is in the closure (it contains itself), so by minimality of S, S₀ ⊄ S.
  have hS₀_up : S₀ ∈ upClosureIn X A :=
    mem_upClosureIn.mpr ⟨(hAX S₀ hS₀A), S₀, hS₀A, subset_refl _⟩
  have hS₀_not_lt : ¬ S₀ ⊂ S := hmin S₀ hS₀_up
  -- Then S₀ = S (since S₀ ⊆ S and S₀ is not a strict subset).
  have hS₀_eq_S : S₀ = S := by
    by_contra hne
    exact hS₀_not_lt (hS₀S.ssubset_of_ne hne)
  -- Hence S.card = S₀.card = k.
  have : S.card = k := hS₀_eq_S ▸ hUniform S₀ hS₀A
  exact this.le

/-- For a uniform family, the minimal members of its upper closure are exactly
the original family. -/
lemma mem_minimalMembersIn_upClosureIn_iff
    {X : Finset α} {A : Finset (Finset α)} {k : ℕ}
    (hUniform : Erdos202.UniformFamily A k)
    (hAX : ∀ S ∈ A, S ⊆ X)
    {S : Finset α} :
    S ∈ minimalMembersIn X (upClosureIn X A) ↔ S ∈ A := by
  constructor
  · intro hS
    rcases mem_minimalMembersIn.mp hS with ⟨hSup, hmin⟩
    rcases mem_upClosureIn.mp hSup with ⟨_, S₀, hS₀A, hS₀S⟩
    have hS₀_up : S₀ ∈ upClosureIn X A :=
      mem_upClosureIn.mpr ⟨hAX S₀ hS₀A, S₀, hS₀A, subset_refl _⟩
    have hS₀_not_lt : ¬ S₀ ⊂ S := hmin S₀ hS₀_up
    have hS₀_eq_S : S₀ = S := by
      by_contra hne
      exact hS₀_not_lt (hS₀S.ssubset_of_ne hne)
    simpa [← hS₀_eq_S] using hS₀A
  · intro hSA
    refine mem_minimalMembersIn.mpr ⟨?_, ?_⟩
    · exact mem_upClosureIn.mpr ⟨hAX S hSA, S, hSA, subset_refl _⟩
    · intro T hTup hTlt
      rcases mem_upClosureIn.mp hTup with ⟨_, S₀, hS₀A, hS₀T⟩
      have hS₀S : S₀ ⊆ S := hS₀T.trans hTlt.subset
      have hS₀_eq_S : S₀ = S := by
        refine Finset.eq_of_subset_of_card_le hS₀S ?_
        rw [hUniform S₀ hS₀A, hUniform S hSA]
      have hST : S ⊆ T := by simpa [hS₀_eq_S] using hS₀T
      have hTS : T ⊆ S := hTlt.subset
      have hTS_eq : T = S := le_antisymm hTS hST
      exact hTlt.ne hTS_eq

/-- For a uniform family, the minimal members of its upper closure are exactly
the original family. -/
lemma minimalMembersIn_upClosureIn_eq
    {X : Finset α} {A : Finset (Finset α)} {k : ℕ}
    (hUniform : Erdos202.UniformFamily A k)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    minimalMembersIn X (upClosureIn X A) = A := by
  ext S
  exact mem_minimalMembersIn_upClosureIn_iff hUniform hAX

/-- **`ell` bound.** The complexity parameter of the upper closure of a
`k`-uniform family is at most `max 2 k`. -/
theorem ell_upClosure_le {X : Finset α} {A : Finset (Finset α)} {k : ℕ}
    (hUniform : Erdos202.UniformFamily A k)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    ell X (upClosureIn X A) ≤ max 2 k := by
  classical
  have hsup_le : (minimalMembersIn X (upClosureIn X A)).sup Finset.card ≤ k := by
    refine Finset.sup_le ?_
    intro S hS
    exact minimalMembersIn_upClosureIn_card_le hUniform hAX hS
  unfold ell
  exact max_le_max le_rfl hsup_le

/-- If the uniform family is nonempty, the complexity of its upper closure is
exactly `max 2 k`. -/
theorem ell_upClosure_eq {X : Finset α} {A : Finset (Finset α)} {k : ℕ}
    (hA : A.Nonempty)
    (hUniform : Erdos202.UniformFamily A k)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    ell X (upClosureIn X A) = max 2 k := by
  have hsup_le : A.sup Finset.card ≤ k := by
    refine Finset.sup_le ?_
    intro S hS
    exact (hUniform S hS).le
  have hk_le_sup : k ≤ A.sup Finset.card := by
    rcases hA with ⟨S, hS⟩
    have hk_le_card : k ≤ S.card := (hUniform S hS).ge
    exact hk_le_card.trans (Finset.le_sup (s := A) (f := Finset.card) hS)
  have hsup_eq : A.sup Finset.card = k := le_antisymm hsup_le hk_le_sup
  unfold ell
  rw [minimalMembersIn_upClosureIn_eq hUniform hAX, hsup_eq]

end

end ParkPham
end Erdos202


/-! =============================================================
    Section from: Erdos/P202/ParkPham/ProductMeasure.lean
    ============================================================= -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 2.

Finite Bernoulli product measure on subsets of a finite universe `X`,
expressed as a finite sum (no `MeasureTheory`). Used by the expectation-
threshold theorem and the random-partition argument downstream.
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- Bernoulli mass of a subset `S ⊆ X` at density `p`. -/
noncomputable def bernoulliMass (X S : Finset α) (p : ℝ) : ℝ :=
  p ^ S.card * (1 - p) ^ (X.card - S.card)

/-- Bernoulli probability of a family `U` of subsets of `X` at density `p`. -/
noncomputable def muP (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : ℝ :=
  ∑ S ∈ X.powerset.filter (· ∈ U), bernoulliMass X S p

omit [DecidableEq α] in
lemma bernoulliMass_nonneg {X S : Finset α} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ bernoulliMass X S p := by
  unfold bernoulliMass
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- `muP` is nonnegative for `p ∈ [0, 1]`. -/
lemma muP_nonneg {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ muP X U p := by
  refine Finset.sum_nonneg fun S _ => bernoulliMass_nonneg h0 h1

/-- `muP` is monotone in the family. -/
lemma muP_mono_family {X : Finset α} {U V : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hUV : U ⊆ V) : muP X U p ≤ muP X V p := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSU⟩
    exact Finset.mem_filter.mpr ⟨hSX, hUV hSU⟩
  · intros
    exact bernoulliMass_nonneg h0 h1

/-- Replacing an already-increasing family by its upper closure does not change
its product measure. -/
lemma muP_upClosureIn_eq_self_of_increasing
    {X : Finset α} {U : Finset (Finset α)} (p : ℝ)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U) :
    muP X (upClosureIn X U) p = muP X U p := by
  rw [upClosureIn_eq_self_of_increasing hUX hIncr]

omit [DecidableEq α] in
/-- Bernoulli weights sum to 1 over the powerset of any finite set `X`,
for any `p ∈ ℝ`. This is the finite binomial identity. -/
lemma sum_bernoulliMass_eq_one (X : Finset α) {p : ℝ}
    (h : p + (1 - p) = 1) :
    (∑ S ∈ X.powerset, bernoulliMass X S p) = 1 := by
  classical
  -- Group by cardinality and use the binomial theorem.
  have hsum :
      (∑ S ∈ X.powerset, p ^ S.card * (1 - p) ^ (X.card - S.card)) =
        ∑ k ∈ Finset.range (X.card + 1),
          (X.card.choose k : ℝ) * (p ^ k * (1 - p) ^ (X.card - k)) := by
    classical
    rw [Finset.sum_powerset_apply_card
      (f := fun k => p ^ k * (1 - p) ^ (X.card - k))]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [nsmul_eq_mul]
  unfold bernoulliMass
  rw [hsum]
  have hbinom : (p + (1 - p)) ^ X.card =
      ∑ k ∈ Finset.range (X.card + 1),
        p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ) :=
    add_pow p (1 - p) X.card
  have : (p + (1 - p)) ^ X.card = 1 := by rw [h]; exact one_pow _
  rw [this] at hbinom
  -- Reshape RHS to match.
  have hreshape :
      (∑ k ∈ Finset.range (X.card + 1),
          (X.card.choose k : ℝ) * (p ^ k * (1 - p) ^ (X.card - k))) =
        (∑ k ∈ Finset.range (X.card + 1),
          p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [hreshape, ← hbinom]

/-- Upper bound: `muP X U p ≤ 1` for `p ∈ [0,1]` (in fact equals 1 minus the
mass on the complement). -/
lemma muP_le_one {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : muP X U p ≤ 1 := by
  have hsum := sum_bernoulliMass_eq_one (α := α) X (p := p) (by ring)
  have hsub : muP X U p ≤ ∑ S ∈ X.powerset, bernoulliMass X S p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro S hS; exact (Finset.mem_filter.mp hS).1
    · intros; exact bernoulliMass_nonneg h0 h1
  linarith

omit [DecidableEq α] in
/-- Finite Bernoulli averaging choice principle.  If the Bernoulli-weighted
average of a function on subsets of `X` is strictly below `B`, then at least
one subset has value strictly below `B`. -/
lemma exists_powerset_value_lt_of_bernoulli_average_lt
    (X : Finset α) {p B : ℝ} (F : Finset α → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (havg :
      (∑ W ∈ X.powerset, bernoulliMass X W p * F W) < B) :
    ∃ W ∈ X.powerset, F W < B := by
  by_contra hnone
  have hB_le : ∀ W ∈ X.powerset, B ≤ F W := by
    intro W hW
    exact le_of_not_gt fun hlt => hnone ⟨W, hW, hlt⟩
  have hsum_le :
      (∑ W ∈ X.powerset, bernoulliMass X W p * B) ≤
        ∑ W ∈ X.powerset, bernoulliMass X W p * F W := by
    refine Finset.sum_le_sum ?_
    intro W hW
    exact mul_le_mul_of_nonneg_left (hB_le W hW)
      (bernoulliMass_nonneg hp0 hp1)
  have hsum_const :
      (∑ W ∈ X.powerset, bernoulliMass X W p * B) = B := by
    calc
      (∑ W ∈ X.powerset, bernoulliMass X W p * B)
          = (∑ W ∈ X.powerset, bernoulliMass X W p) * B := by
              rw [Finset.sum_mul]
      _ = 1 * B := by
          rw [sum_bernoulliMass_eq_one (α := α) X (p := p) (by ring)]
      _ = B := by ring
  linarith

omit [DecidableEq α] in
/-- Finite Markov/complement principle over an arbitrary finite probability
space.  This is the bookkeeping form needed for a multi-exposure process:
if all bad outcomes have loss at least `B > 0` and the expected loss is below
`B/2`, then the good event has weight greater than `1/2`. -/
lemma half_lt_weighted_good_of_average_lt_half_of_bad_le
    {Ω : Type*} [DecidableEq Ω] (s : Finset Ω)
    (weight : Ω → ℝ) (Good : Ω → Prop) [DecidablePred Good]
    (F : Ω → ℝ) {B : ℝ}
    (hweight_nonneg : ∀ ω ∈ s, 0 ≤ weight ω)
    (hsum_weight : (∑ ω ∈ s, weight ω) = 1)
    (hB : 0 < B)
    (hF_nonneg : ∀ ω ∈ s, 0 ≤ F ω)
    (hbad : ∀ ω ∈ s, ¬ Good ω → B ≤ F ω)
    (havg : (∑ ω ∈ s, weight ω * F ω) < B * (1 / 2)) :
    (1 / 2 : ℝ) < ∑ ω ∈ s.filter Good, weight ω := by
  let bad : Finset Ω := s.filter fun ω => ¬ Good ω
  have hbad_weight_le :
      (∑ ω ∈ bad, weight ω * B) ≤
        ∑ ω ∈ bad, weight ω * F ω := by
    refine Finset.sum_le_sum ?_
    intro ω hωbad
    have hωs : ω ∈ s := (Finset.mem_filter.mp hωbad).1
    have hωGood : ¬ Good ω := (Finset.mem_filter.mp hωbad).2
    exact mul_le_mul_of_nonneg_left (hbad ω hωs hωGood)
      (hweight_nonneg ω hωs)
  have hbad_avg_le :
      (∑ ω ∈ bad, weight ω * F ω) ≤
        ∑ ω ∈ s, weight ω * F ω := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro ω hωs _hωnot
    exact mul_nonneg (hweight_nonneg ω hωs) (hF_nonneg ω hωs)
  have hbad_mass_mul_lt :
      (∑ ω ∈ bad, weight ω) * B < B * (1 / 2) := by
    calc
      (∑ ω ∈ bad, weight ω) * B
          = ∑ ω ∈ bad, weight ω * B := by
              rw [Finset.sum_mul]
      _ ≤ ∑ ω ∈ bad, weight ω * F ω := hbad_weight_le
      _ ≤ ∑ ω ∈ s, weight ω * F ω := hbad_avg_le
      _ < B * (1 / 2) := havg
  have hbad_mass_lt_half :
      (∑ ω ∈ bad, weight ω) < (1 / 2 : ℝ) := by
    have hbad_mass_mul_lt' :
        (∑ ω ∈ bad, weight ω) * B < (1 / 2 : ℝ) * B := by
      linarith
    exact lt_of_mul_lt_mul_right hbad_mass_mul_lt' hB.le
  have hsplit :
      (∑ ω ∈ s.filter Good, weight ω) + (∑ ω ∈ bad, weight ω) = 1 := by
    have hsplit_raw :=
      Finset.sum_filter_add_sum_filter_not
        (s := s) (p := Good) (f := weight)
    unfold bad
    simpa using hsplit_raw.trans hsum_weight
  linarith

/-- Finite outcome space for `n` independent exposure sets, each chosen from
the powerset of `X`. -/
noncomputable def exposureTupleSpace (X : Finset α) (n : ℕ) :
    Finset (Fin n → Finset α) :=
  Fintype.piFinset fun _ : Fin n => X.powerset

omit [DecidableEq α] in
lemma mem_exposureTupleSpace
    {X : Finset α} {n : ℕ} {Ws : Fin n → Finset α} :
    Ws ∈ exposureTupleSpace X n ↔ ∀ i, Ws i ∈ X.powerset := by
  simp [exposureTupleSpace, Fintype.mem_piFinset]

/-- Product Bernoulli weight of an exposure tuple. -/
noncomputable def exposureTupleWeight
    (X : Finset α) {n : ℕ} (ρ : Fin n → ℝ)
    (Ws : Fin n → Finset α) : ℝ :=
  ∏ i, bernoulliMass X (Ws i) (ρ i)

omit [DecidableEq α] in
lemma exposureTupleWeight_nonneg
    (X : Finset α) {n : ℕ} {ρ : Fin n → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (Ws : Fin n → Finset α) :
    0 ≤ exposureTupleWeight X ρ Ws := by
  unfold exposureTupleWeight
  exact Finset.prod_nonneg fun i _hi =>
    bernoulliMass_nonneg (hρ0 i) (hρ1 i)

omit [DecidableEq α] in
lemma sum_exposureTupleWeight_eq_one
    (X : Finset α) {n : ℕ} (ρ : Fin n → ℝ) :
    (∑ Ws ∈ exposureTupleSpace X n, exposureTupleWeight X ρ Ws) = 1 := by
  unfold exposureTupleSpace exposureTupleWeight
  rw [Finset.sum_prod_piFinset
    (s := X.powerset)
    (g := fun i W => bernoulliMass X W (ρ i))]
  simp [sum_bernoulliMass_eq_one]

/-- Union of all exposure sets in a finite exposure tuple. -/
def exposureTupleUnion {n : ℕ} (Ws : Fin n → Finset α) : Finset α :=
  (Finset.univ : Finset (Fin n)).biUnion fun i => Ws i

/-- Density of the union of independent exposure sets with coordinate
densities `ρ`. -/
noncomputable def tupleUnionDensity {n : ℕ} (ρ : Fin n → ℝ) : ℝ :=
  1 - ∏ i, (1 - ρ i)

omit [DecidableEq α] in
@[simp] lemma tupleUnionDensity_zero (ρ : Fin 0 → ℝ) :
    tupleUnionDensity ρ = 0 := by
  simp [tupleUnionDensity]

omit [DecidableEq α] in
@[simp] lemma tupleUnionDensity_one (ρ : Fin 1 → ℝ) :
    tupleUnionDensity ρ = ρ 0 := by
  simp [tupleUnionDensity]

omit [DecidableEq α] in
@[simp] lemma one_sub_tupleUnionDensity {n : ℕ} (ρ : Fin n → ℝ) :
    1 - tupleUnionDensity ρ = ∏ i, (1 - ρ i) := by
  unfold tupleUnionDensity
  ring

omit [DecidableEq α] in
lemma tupleUnionDensity_snoc {n : ℕ} (ρ : Fin (n + 1) → ℝ) :
    tupleUnionDensity ρ =
      1 - (1 - tupleUnionDensity (fun i : Fin n => ρ i.castSucc)) *
        (1 - ρ (Fin.last n)) := by
  unfold tupleUnionDensity
  rw [Fin.prod_univ_castSucc]
  ring

omit [DecidableEq α] in
@[simp] lemma tupleUnionDensity_const (n : ℕ) (q : ℝ) :
    tupleUnionDensity (fun _ : Fin n => q) = 1 - (1 - q) ^ n := by
  simp [tupleUnionDensity, Finset.prod_const]

omit [DecidableEq α] in
lemma tupleUnionDensity_nonneg {n : ℕ} {ρ : Fin n → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1) :
    0 ≤ tupleUnionDensity ρ := by
  have hprod_le_one : (∏ i, (1 - ρ i)) ≤ (1 : ℝ) := by
    refine Finset.prod_le_one ?_ ?_
    · intro i _hi
      exact sub_nonneg.mpr (hρ1 i)
    · intro i _hi
      linarith [hρ0 i]
  unfold tupleUnionDensity
  linarith

omit [DecidableEq α] in
lemma tupleUnionDensity_le_one {n : ℕ} {ρ : Fin n → ℝ}
    (hρ1 : ∀ i, ρ i ≤ 1) :
    tupleUnionDensity ρ ≤ 1 := by
  have hprod_nonneg : 0 ≤ (∏ i, (1 - ρ i)) := by
    refine Finset.prod_nonneg ?_
    intro i _hi
    exact sub_nonneg.mpr (hρ1 i)
  unfold tupleUnionDensity
  linarith

omit [DecidableEq α] in
lemma tupleUnionDensity_le_sum {n : ℕ} {ρ : Fin n → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1) :
    tupleUnionDensity ρ ≤ ∑ i, ρ i := by
  induction n with
  | zero =>
      simp [tupleUnionDensity]
  | succ n ih =>
      let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
      have htail0 : ∀ i : Fin n, 0 ≤ ρtail i := fun i => hρ0 i.castSucc
      have htail1 : ∀ i : Fin n, ρtail i ≤ 1 := fun i => hρ1 i.castSucc
      have htail_le : tupleUnionDensity ρtail ≤ ∑ i, ρtail i :=
        ih htail0 htail1
      have htail_nonneg : 0 ≤ tupleUnionDensity ρtail :=
        tupleUnionDensity_nonneg htail0 htail1
      have hlast_nonneg : 0 ≤ ρ (Fin.last n) := hρ0 (Fin.last n)
      have hsplit :
          tupleUnionDensity ρ ≤ tupleUnionDensity ρtail + ρ (Fin.last n) := by
        rw [tupleUnionDensity_snoc]
        have hmul_nonneg :
            0 ≤ tupleUnionDensity ρtail * ρ (Fin.last n) :=
          mul_nonneg htail_nonneg hlast_nonneg
        nlinarith
      have hsum :
          (∑ i : Fin (n + 1), ρ i) =
            (∑ i : Fin n, ρtail i) + ρ (Fin.last n) := by
        rw [Fin.sum_univ_castSucc]
      exact hsplit.trans (by
        rw [hsum]
        have h := add_le_add_right htail_le (ρ (Fin.last n))
        simpa [add_comm, add_left_comm, add_assoc] using h)

omit [DecidableEq α] in
lemma tupleUnionDensity_le_sum_of_le {n : ℕ} {ρ B : Fin n → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hρB : ∀ i, ρ i ≤ B i) :
    tupleUnionDensity ρ ≤ ∑ i, B i := by
  exact (tupleUnionDensity_le_sum hρ0 hρ1).trans
    (Finset.sum_le_sum fun i _hi => hρB i)

lemma exposureTupleUnion_subset
    {X : Finset α} {n : ℕ} {Ws : Fin n → Finset α}
    (hWs : Ws ∈ exposureTupleSpace X n) :
    exposureTupleUnion Ws ⊆ X := by
  intro x hx
  rcases (by simpa [exposureTupleUnion] using hx : ∃ i, x ∈ Ws i) with
    ⟨i, hxi⟩
  exact Finset.mem_powerset.mp ((mem_exposureTupleSpace.mp hWs) i) hxi

@[simp] lemma exposureTupleUnion_zero (Ws : Fin 0 → Finset α) :
    exposureTupleUnion Ws = ∅ := by
  ext x
  simp [exposureTupleUnion]

@[simp] lemma exposureTupleUnion_one (Ws : Fin 1 → Finset α) :
    exposureTupleUnion Ws = Ws 0 := by
  ext x
  simp [exposureTupleUnion]

@[simp] lemma exposureTupleUnion_snoc {n : ℕ}
    (Ws : Fin n → Finset α) (W : Finset α) :
    exposureTupleUnion
        (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
      exposureTupleUnion Ws ∪ W := by
  ext x
  constructor
  · intro hx
    rcases (by
      simpa [exposureTupleUnion] using hx :
        ∃ i : Fin (n + 1),
          x ∈ (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) i) with
      ⟨i, hi⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Finset.mem_union.mpr (Or.inl (by
        simpa [exposureTupleUnion] using (Exists.intro j (by simpa using hi))))
    · exact Finset.mem_union.mpr (Or.inr (by simpa using hi))
  · intro hx
    rcases Finset.mem_union.mp hx with htail | hlast
    · rcases (by
        simpa [exposureTupleUnion] using htail :
          ∃ i : Fin n, x ∈ Ws i) with ⟨i, hi⟩
      simpa [exposureTupleUnion] using
        (Exists.intro (i.castSucc : Fin (n + 1)) (by simpa using hi))
    · simpa [exposureTupleUnion] using
        (Exists.intro (Fin.last n) (by simpa using hlast))

omit [DecidableEq α] in
lemma exposureTupleSpace_snoc (X : Finset α) (n : ℕ) :
    exposureTupleSpace X (n + 1) =
      (X.powerset ×ˢ exposureTupleSpace X n).map
        (Fin.snocEquiv (fun _ : Fin (n + 1) => Finset α)).toEmbedding := by
  ext Ws
  constructor
  · intro hWs
    refine Finset.mem_map.mpr ⟨⟨Ws (Fin.last n),
      fun i : Fin n => Ws i.castSucc⟩, ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨(mem_exposureTupleSpace.mp hWs) (Fin.last n),
          mem_exposureTupleSpace.mpr fun i =>
            (mem_exposureTupleSpace.mp hWs) i.castSucc⟩
    · exact (Fin.snocEquiv
        (fun _ : Fin (n + 1) => Finset α)).right_inv Ws
  · intro hWs
    rcases Finset.mem_map.mp hWs with ⟨⟨W, Ws₀⟩, hpair, hEq⟩
    rw [← hEq]
    rcases Finset.mem_product.mp hpair with ⟨hW, hWs₀⟩
    refine mem_exposureTupleSpace.mpr ?_
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa using (mem_exposureTupleSpace.mp hWs₀) j
    · simpa using hW

omit [DecidableEq α] in
@[simp] lemma exposureTupleWeight_snoc {n : ℕ}
    (X : Finset α) (ρ : Fin (n + 1) → ℝ)
    (Ws : Fin n → Finset α) (W : Finset α) :
    exposureTupleWeight X ρ
        (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
      exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
        bernoulliMass X W (ρ (Fin.last n)) := by
  unfold exposureTupleWeight
  rw [Fin.prod_univ_castSucc]
  simp

/-- For one exposure, the exposure-tuple model is exactly `muP`. -/
lemma exposureTupleUnion_measure_one
    (X : Finset α) (U : Finset (Finset α)) (ρ : Fin 1 → ℝ) :
    (∑ Ws ∈ (exposureTupleSpace X 1).filter
      (fun Ws => exposureTupleUnion Ws ∈ U),
      exposureTupleWeight X ρ Ws) =
      muP X U (ρ 0) := by
  unfold exposureTupleSpace exposureTupleWeight muP
  have hmap :
      ((Fintype.piFinset fun _ : Fin 1 => X.powerset).filter
        (fun Ws : Fin 1 → Finset α => exposureTupleUnion Ws ∈ U)).image
          (fun Ws => Ws 0) =
        X.powerset.filter (fun W => W ∈ U) := by
    ext W
    constructor
    · intro hW
      rcases Finset.mem_image.mp hW with ⟨Ws, hWs, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨(Fintype.mem_piFinset.mp (Finset.mem_filter.mp hWs).1) 0,
          by simpa using (Finset.mem_filter.mp hWs).2⟩
    · intro hW
      refine Finset.mem_image.mpr ⟨(fun _ : Fin 1 => W), ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Fintype.mem_piFinset.mpr (by intro i; simpa using (Finset.mem_filter.mp hW).1),
          by simpa [exposureTupleUnion_one] using (Finset.mem_filter.mp hW).2⟩
  have hinj :
      Set.InjOn (fun Ws : Fin 1 → Finset α => Ws 0)
        (((Fintype.piFinset fun _ : Fin 1 => X.powerset).filter
          (fun Ws : Fin 1 → Finset α => exposureTupleUnion Ws ∈ U)) : Set (Fin 1 → Finset α)) := by
    intro Ws _hWs Vs _hVs h0
    funext i
    have hi : i = 0 := by fin_cases i; rfl
    simpa [hi] using h0
  rw [← hmap, Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro Ws hWs
    simp
  · exact hinj

/-- One-exposure case expressed using `tupleUnionDensity`. -/
lemma exposureTupleUnion_measure_one_density
    (X : Finset α) (U : Finset (Finset α)) (ρ : Fin 1 → ℝ) :
    (∑ Ws ∈ (exposureTupleSpace X 1).filter
      (fun Ws => exposureTupleUnion Ws ∈ U),
      exposureTupleWeight X ρ Ws) =
      muP X U (tupleUnionDensity ρ) := by
  simpa using exposureTupleUnion_measure_one X U ρ

/-- Finite Markov/complement principle for Bernoulli sums.  If every outcome
outside `U` has loss at least `B > 0`, and the expected loss is below `B/2`,
then `U` has Bernoulli measure strictly bigger than `1/2`. -/
lemma half_lt_muP_of_average_lt_half_of_bad_le
    (X : Finset α) (U : Finset (Finset α)) {p B : ℝ}
    (F : Finset α → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hB : 0 < B)
    (hF_nonneg : ∀ W ∈ X.powerset, 0 ≤ F W)
    (hbad : ∀ W ∈ X.powerset, W ∉ U → B ≤ F W)
    (havg :
      (∑ W ∈ X.powerset, bernoulliMass X W p * F W) < B * (1 / 2)) :
    (1 / 2 : ℝ) < muP X U p := by
  let bad : Finset (Finset α) := X.powerset.filter fun W => W ∉ U
  have hbad_weight_le :
      (∑ W ∈ bad, bernoulliMass X W p * B) ≤
        ∑ W ∈ bad, bernoulliMass X W p * F W := by
    refine Finset.sum_le_sum ?_
    intro W hWbad
    have hWX : W ∈ X.powerset := (Finset.mem_filter.mp hWbad).1
    have hWU : W ∉ U := (Finset.mem_filter.mp hWbad).2
    exact mul_le_mul_of_nonneg_left (hbad W hWX hWU)
      (bernoulliMass_nonneg hp0 hp1)
  have hbad_avg_le :
      (∑ W ∈ bad, bernoulliMass X W p * F W) ≤
        ∑ W ∈ X.powerset, bernoulliMass X W p * F W := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro W hWX _hWnot
    exact mul_nonneg (bernoulliMass_nonneg hp0 hp1) (hF_nonneg W hWX)
  have hbad_mass_mul_lt :
      (∑ W ∈ bad, bernoulliMass X W p) * B < B * (1 / 2) := by
    calc
      (∑ W ∈ bad, bernoulliMass X W p) * B
          = ∑ W ∈ bad, bernoulliMass X W p * B := by
              rw [Finset.sum_mul]
      _ ≤ ∑ W ∈ bad, bernoulliMass X W p * F W := hbad_weight_le
      _ ≤ ∑ W ∈ X.powerset, bernoulliMass X W p * F W := hbad_avg_le
      _ < B * (1 / 2) := havg
  have hbad_mass_lt_half :
      (∑ W ∈ bad, bernoulliMass X W p) < (1 / 2 : ℝ) := by
    have hbad_mass_mul_lt' :
        (∑ W ∈ bad, bernoulliMass X W p) * B < (1 / 2 : ℝ) * B := by
      linarith
    exact lt_of_mul_lt_mul_right hbad_mass_mul_lt' hB.le
  have htotal :
      (∑ W ∈ X.powerset, bernoulliMass X W p) = 1 :=
    sum_bernoulliMass_eq_one (α := α) X (p := p) (by ring)
  have hsplit :
      muP X U p + (∑ W ∈ bad, bernoulliMass X W p) = 1 := by
    have hsplit_raw :=
      Finset.sum_filter_add_sum_filter_not
        (s := X.powerset) (p := fun W : Finset α => W ∈ U)
        (f := fun W => bernoulliMass X W p)
    unfold muP bad
    simpa using hsplit_raw.trans htotal
  linarith

omit [DecidableEq α] in
/-- Uniform geometric estimate used in the Park--Pham/Park--Vondrak cost
lemma.  If `p = 1 - (1 - q)^L`, then the numerator
`L * q * (1 - q)^L` is bounded by the denominator `p`. -/
lemma nat_mul_q_mul_one_sub_q_pow_le_one_sub_pow
    {q : ℝ} {L : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (L : ℝ) * q * (1 - q) ^ L ≤ 1 - (1 - q) ^ L := by
  let r : ℝ := 1 - q
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hq_eq : q = 1 - r := by dsimp [r]; ring
  have hsum_ge :
      (L : ℝ) * r ^ L ≤ ∑ i ∈ Finset.range L, r ^ i := by
    calc
      (L : ℝ) * r ^ L = ∑ _i ∈ Finset.range L, r ^ L := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range L, r ^ i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact pow_le_pow_of_le_one hr0 hr1
          (Nat.le_of_lt (Finset.mem_range.mp hi))
  have hmul :=
    mul_le_mul_of_nonneg_right hsum_ge (by dsimp [r]; linarith : 0 ≤ 1 - r)
  calc
    (L : ℝ) * q * (1 - q) ^ L
        = ((L : ℝ) * r ^ L) * (1 - r) := by
          dsimp [r]
          ring
    _ ≤ (∑ i ∈ Finset.range L, r ^ i) * (1 - r) := hmul
    _ = 1 - r ^ L := geom_sum_mul_neg r L
    _ = 1 - (1 - q) ^ L := by rfl

omit [DecidableEq α] in
lemma one_sub_one_sub_q_pow_pos
    {q : ℝ} {L : ℕ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    0 < 1 - (1 - q) ^ L := by
  have hr0 : 0 ≤ 1 - q := by linarith
  have hr1 : 1 - q ≤ 1 := by linarith
  have hpow_le : (1 - q) ^ L ≤ (1 - q) ^ 1 :=
    pow_le_pow_of_le_one hr0 hr1 hL
  have hq_le : q ≤ 1 - (1 - q) ^ L := by
    simpa using sub_le_sub_left hpow_le 1
  exact lt_of_lt_of_le hq0 hq_le

omit [DecidableEq α] in
/-- Bernoulli union bound in scalar form:
`1 - (1 - q)^L <= L q` for `q ∈ [0,1]`. -/
lemma one_sub_one_sub_q_pow_le_nat_mul
    {q : ℝ} {L : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    1 - (1 - q) ^ L ≤ (L : ℝ) * q := by
  let r : ℝ := 1 - q
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hsum_le :
      (∑ i ∈ Finset.range L, r ^ i) ≤
        ∑ _i ∈ Finset.range L, (1 : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact pow_le_one₀ hr0 hr1
  have hmul :=
    mul_le_mul_of_nonneg_right hsum_le (by dsimp [r]; linarith : 0 ≤ 1 - r)
  calc
    1 - (1 - q) ^ L = (∑ i ∈ Finset.range L, r ^ i) * (1 - r) := by
        dsimp [r]
        rw [geom_sum_mul_neg]
    _ ≤ (∑ _i ∈ Finset.range L, (1 : ℝ)) * (1 - r) := hmul
    _ = (L : ℝ) * q := by
        dsimp [r]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

omit [DecidableEq α] in
lemma tupleUnionDensity_one_sub_pow_le_q_sum
    {q : ℝ} {n : ℕ} (L : Fin n → ℕ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    tupleUnionDensity (fun i : Fin n => 1 - (1 - q) ^ L i) ≤
      q * ∑ i : Fin n, (L i : ℝ) := by
  have hbase0 : 0 ≤ 1 - q := by linarith
  have hbase1 : 1 - q ≤ 1 := by linarith
  have hρ0 :
      ∀ i : Fin n, 0 ≤ 1 - (1 - q) ^ L i := by
    intro i
    have hpow_le_one : (1 - q) ^ L i ≤ (1 : ℝ) :=
      pow_le_one₀ hbase0 hbase1
    linarith
  have hρ1 :
      ∀ i : Fin n, 1 - (1 - q) ^ L i ≤ 1 := by
    intro i
    have hpow_nonneg : 0 ≤ (1 - q) ^ L i :=
      pow_nonneg hbase0 _
    linarith
  have hbound :
      ∀ i : Fin n, 1 - (1 - q) ^ L i ≤ (L i : ℝ) * q := by
    intro i
    exact one_sub_one_sub_q_pow_le_nat_mul hq0 hq1
  calc
    tupleUnionDensity (fun i : Fin n => 1 - (1 - q) ^ L i)
        ≤ ∑ i : Fin n, (L i : ℝ) * q :=
          tupleUnionDensity_le_sum_of_le hρ0 hρ1 hbound
    _ = q * ∑ i : Fin n, (L i : ℝ) := by
          rw [← Finset.sum_mul]
          ring

omit [DecidableEq α] in
/-- Divided form of `nat_mul_q_mul_one_sub_q_pow_le_one_sub_pow`. -/
lemma q_mul_one_sub_q_pow_div_one_sub_pow_le_inv_nat
    {q : ℝ} {L : ℕ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    q * (1 - q) ^ L / (1 - (1 - q) ^ L) ≤ 1 / (L : ℝ) := by
  have hmain :=
    nat_mul_q_mul_one_sub_q_pow_le_one_sub_pow
      (q := q) (L := L) hq0.le hq1
  have hden : 0 < 1 - (1 - q) ^ L :=
    one_sub_one_sub_q_pow_pos hL hq0 hq1
  have hLpos : 0 < (L : ℝ) := by
    have hL_nat_pos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
    exact_mod_cast hL_nat_pos
  have hnum :
      q * (1 - q) ^ L ≤ (1 - (1 - q) ^ L) / (L : ℝ) := by
    rw [le_div_iff₀ hLpos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmain
  calc
    q * (1 - q) ^ L / (1 - (1 - q) ^ L)
        ≤ ((1 - (1 - q) ^ L) / (L : ℝ)) /
            (1 - (1 - q) ^ L) :=
          div_le_div_of_nonneg_right hnum hden.le
    _ = 1 / (L : ℝ) := by
          field_simp [hden.ne', hLpos.ne']

/-- Termwise uniform Park--Vondrak reindexing bound.  If
`ρ = 1 - (1 - q)^L`, then for a disjoint pair `W,S`, the Bernoulli weight of
`W` times `q^|S|` is bounded by the Bernoulli weight of `W ∪ S` times
`(1/L)^|S|`. -/
lemma bernoulliMass_mul_pow_le_union_mul_inv_nat_pow
    {X W S : Finset α} {q ρ : ℝ} {L : ℕ}
    (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hdisj : Disjoint S W) (hUnionX : W ∪ S ⊆ X) :
    bernoulliMass X W ρ * q ^ S.card ≤
      bernoulliMass X (W ∪ S) ρ * (1 / (L : ℝ)) ^ S.card := by
  have hρ_pos : 0 < ρ := by
    simpa [hρ] using one_sub_one_sub_q_pow_pos hL hq0 hq1
  have hρ_nonneg : 0 ≤ ρ := hρ_pos.le
  have hρ_le_one : ρ ≤ 1 := by
    rw [hρ]
    have hpow_nonneg : 0 ≤ (1 - q) ^ L := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
    linarith
  have hone_minus_ρ_nonneg : 0 ≤ 1 - ρ := by linarith
  have hLpos : 0 < (L : ℝ) := by
    have hL_nat_pos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
    exact_mod_cast hL_nat_pos
  have hsingle : q * (1 - ρ) ≤ ρ * (1 / (L : ℝ)) := by
    have hmain :
        (L : ℝ) * q * (1 - ρ) ≤ ρ := by
      have hraw :=
        nat_mul_q_mul_one_sub_q_pow_le_one_sub_pow
          (q := q) (L := L) hq0.le hq1
      simpa [hρ, mul_assoc, mul_comm, mul_left_comm] using hraw
    rw [← div_eq_mul_one_div]
    rw [le_div_iff₀ hLpos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmain
  have hpow_single :
      (q * (1 - ρ)) ^ S.card ≤ (ρ * (1 / (L : ℝ))) ^ S.card :=
    pow_le_pow_left₀ (mul_nonneg hq0.le hone_minus_ρ_nonneg) hsingle S.card
  have hcard_union : (W ∪ S).card = W.card + S.card := by
    rw [Finset.card_union_of_disjoint]
    exact hdisj.symm
  have hWsub : W ⊆ W ∪ S := Finset.subset_union_left
  have hWcard_le : W.card ≤ X.card :=
    Finset.card_le_card (hWsub.trans hUnionX)
  have hUcard_le : (W ∪ S).card ≤ X.card :=
    Finset.card_le_card hUnionX
  have hdiff : X.card - W.card = (X.card - (W ∪ S).card) + S.card := by
    rw [hcard_union]
    omega
  have hcommon_nonneg :
      0 ≤ ρ ^ W.card * (1 - ρ) ^ (X.card - (W ∪ S).card) := by
    positivity
  calc
    bernoulliMass X W ρ * q ^ S.card
        = (ρ ^ W.card * (1 - ρ) ^ (X.card - (W ∪ S).card)) *
            (q * (1 - ρ)) ^ S.card := by
          unfold bernoulliMass
          rw [hdiff, pow_add, mul_pow]
          ring
    _ ≤ (ρ ^ W.card * (1 - ρ) ^ (X.card - (W ∪ S).card)) *
          (ρ * (1 / (L : ℝ))) ^ S.card :=
        mul_le_mul_of_nonneg_left hpow_single hcommon_nonneg
    _ = bernoulliMass X (W ∪ S) ρ * (1 / (L : ℝ)) ^ S.card := by
          unfold bernoulliMass
          rw [hcard_union, pow_add, mul_pow]
          ring

omit [DecidableEq α] in
/-- At density `1`, the top set `X` has Bernoulli mass `1`. -/
lemma bernoulliMass_self_one (X : Finset α) :
    bernoulliMass X X (1 : ℝ) = 1 := by
  simp [bernoulliMass]

omit [DecidableEq α] in
/-- At density `1`, any proper subset of `X` has Bernoulli mass `0`. -/
lemma bernoulliMass_one_of_ne_top {X S : Finset α}
    (hSX : S ⊆ X) (hS_ne : S ≠ X) :
    bernoulliMass X S (1 : ℝ) = 0 := by
  have hlt : S.card < X.card := Finset.card_lt_card (hSX.ssubset_of_ne hS_ne)
  have hpos : 0 < X.card - S.card := Nat.sub_pos_of_lt hlt
  simp [bernoulliMass, hpos.ne']

/-- If the family contains the top set `X`, then its product measure at
density `1` is `1`. -/
lemma muP_one_of_mem_top {X : Finset α} {U : Finset (Finset α)}
    (hXU : X ∈ U) :
    muP X U (1 : ℝ) = 1 := by
  classical
  unfold muP
  refine Finset.sum_eq_single_of_mem X ?_ ?_ |>.trans (bernoulliMass_self_one X)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (subset_refl X), hXU⟩
  · intro S hS hS_ne
    have hSX : S ⊆ X := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    exact bernoulliMass_one_of_ne_top hSX hS_ne

/-- A nonempty increasing family on `X` has product measure `1` at density
`1`. -/
lemma muP_one_of_nonempty_increasing {X : Finset α} {U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hU : U.Nonempty) :
    muP X U (1 : ℝ) = 1 :=
  muP_one_of_mem_top (top_mem_of_nonempty_increasing hUX hIncr hU)

omit [DecidableEq α] in
/-- At density `0`, the empty set has Bernoulli mass `1`. -/
lemma bernoulliMass_empty_zero (X : Finset α) :
    bernoulliMass X ∅ (0 : ℝ) = 1 := by
  simp [bernoulliMass]

omit [DecidableEq α] in
/-- At density `0`, every nonempty set has Bernoulli mass `0`. -/
lemma bernoulliMass_zero_of_nonempty {X S : Finset α}
    (hS : S.Nonempty) :
    bernoulliMass X S (0 : ℝ) = 0 := by
  simp [bernoulliMass, hS.card_pos.ne']

/-- If the family contains `∅`, then its product measure at density `0` is
`1`. -/
lemma muP_zero_of_mem_empty {X : Finset α} {U : Finset (Finset α)}
    (hEmpty : (∅ : Finset α) ∈ U) :
    muP X U (0 : ℝ) = 1 := by
  classical
  unfold muP
  refine (Finset.sum_eq_single_of_mem ∅ ?_ ?_).trans (bernoulliMass_empty_zero X)
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.empty_subset X), hEmpty⟩
  · intro S hS hS_ne
    have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_ne
    exact bernoulliMass_zero_of_nonempty hS_nonempty

/-- If the family does not contain `∅`, then its product measure at density
`0` is `0`. -/
lemma muP_zero_of_not_mem_empty {X : Finset α} {U : Finset (Finset α)}
    (hEmpty : (∅ : Finset α) ∉ U) :
    muP X U (0 : ℝ) = 0 := by
  classical
  unfold muP
  refine Finset.sum_eq_zero ?_
  intro S hS
  have hSU : S ∈ U := (Finset.mem_filter.mp hS).2
  have hS_ne : S ≠ ∅ := by
    intro hS_empty
    exact hEmpty (by simpa [hS_empty] using hSU)
  exact bernoulliMass_zero_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hS_ne)

/-- Base case for the tuple-union distribution identity. -/
lemma exposureTupleUnion_measure_zero
    (X : Finset α) (U : Finset (Finset α)) (ρ : Fin 0 → ℝ) :
    (∑ Ws ∈ (exposureTupleSpace X 0).filter
      (fun Ws => exposureTupleUnion Ws ∈ U),
      exposureTupleWeight X ρ Ws) =
      muP X U (0 : ℝ) := by
  by_cases hEmpty : (∅ : Finset α) ∈ U
  · have hfilter :
        (exposureTupleSpace X 0).filter
          (fun Ws : Fin 0 → Finset α => exposureTupleUnion Ws ∈ U) =
            exposureTupleSpace X 0 := by
      apply Finset.filter_eq_self.mpr
      intro Ws _hWs
      simpa using hEmpty
    rw [hfilter, sum_exposureTupleWeight_eq_one X ρ,
      muP_zero_of_mem_empty hEmpty]
  · have hfilter :
        (exposureTupleSpace X 0).filter
          (fun Ws : Fin 0 → Finset α => exposureTupleUnion Ws ∈ U) =
            ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro Ws _hWs
      simpa using hEmpty
    rw [hfilter]
    simp [muP_zero_of_not_mem_empty hEmpty]

/-- Zero-exposure case expressed using `tupleUnionDensity`. -/
lemma exposureTupleUnion_measure_zero_density
    (X : Finset α) (U : Finset (Finset α)) (ρ : Fin 0 → ℝ) :
    (∑ Ws ∈ (exposureTupleSpace X 0).filter
      (fun Ws => exposureTupleUnion Ws ∈ U),
      exposureTupleWeight X ρ Ws) =
      muP X U (tupleUnionDensity ρ) := by
  simpa using exposureTupleUnion_measure_zero X U ρ

/-- If `U` is the whole powerset of `X`, then its product measure is `1`. -/
lemma muP_eq_one_of_eq_powerset {X : Finset α} {U : Finset (Finset α)}
    (hU : U = X.powerset) (p : ℝ) :
    muP X U p = 1 := by
  classical
  unfold muP
  have hfilter : X.powerset.filter (fun S => S ∈ U) = X.powerset := by
    apply Finset.filter_eq_self.mpr
    intro S hS
    simpa [hU] using hS
  rw [hfilter]
  exact sum_bernoulliMass_eq_one (α := α) X (p := p) (by ring)

/-- An increasing family on `X` containing `∅` has product measure `1` at every
density. -/
lemma muP_eq_one_of_empty_mem_increasing {X : Finset α} {U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hEmpty : (∅ : Finset α) ∈ U) (p : ℝ) :
    muP X U p = 1 :=
  muP_eq_one_of_eq_powerset
    (eq_powerset_of_empty_mem_increasing hUX hIncr hEmpty) p

/-! ## Marginal at a fixed subset

If `U = upClosureIn X {T₀}` (the upper closure of a single set), then
`muP X U p = p^|T₀|`. This is the "probability that random subset at
density `p` contains `T₀`" identity used by the random-partition argument.
-/

/-- The upper closure of a singleton family `{T₀}` inside `X` is
`{T ⊆ X : T₀ ⊆ T}`. -/
lemma upClosureIn_singleton (X T₀ : Finset α) (hT₀ : T₀ ⊆ X) :
    upClosureIn X {T₀} =
      X.powerset.filter (fun T => T₀ ⊆ T) := by
  classical
  ext T
  constructor
  · intro hT
    rcases mem_upClosureIn.mp hT with ⟨hTX, S, hS, hST⟩
    rcases Finset.mem_singleton.mp hS with rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTX, hST⟩
  · intro hT
    rcases Finset.mem_filter.mp hT with ⟨hTX, hT₀T⟩
    exact mem_upClosureIn.mpr ⟨Finset.mem_powerset.mp hTX, T₀,
      Finset.mem_singleton.mpr rfl, hT₀T⟩

/-- **Marginal identity.** For `T₀ ⊆ X` and `p ∈ [0,1]`,
`muP X (upClosureIn X {T₀}) p = p^|T₀|`. -/
theorem muP_upClosure_single (X T₀ : Finset α) (hT₀ : T₀ ⊆ X) {p : ℝ}
    (_h0 : 0 ≤ p) (_h1 : p ≤ 1) :
    muP X (upClosureIn X {T₀}) p = p ^ T₀.card := by
  classical
  -- Reparametrize: subsets `S ⊆ X` with `T₀ ⊆ S` correspond bijectively
  -- to subsets `S' ⊆ X \ T₀` via `S = T₀ ∪ S'`. The Bernoulli mass factors
  -- as `p^|T₀| · p^|S'| · (1-p)^(|X\T₀|-|S'|)`, and the inner sum is 1.
  set Y : Finset α := X \ T₀ with hY
  have hY_card : Y.card = X.card - T₀.card := by
    simp [hY, Finset.card_sdiff_of_subset hT₀]
  have hT₀_disj_Y : Disjoint T₀ Y := by
    simp [hY, Finset.disjoint_sdiff]
  -- Set up the bijection.
  let f : Finset α → Finset α := fun S' => T₀ ∪ S'
  have hf_inj : Set.InjOn f (↑Y.powerset) := by
    intro S' hS' R' hR' hfeq
    have hS'Y : S' ⊆ Y := Finset.mem_powerset.mp hS'
    have hR'Y : R' ⊆ Y := Finset.mem_powerset.mp hR'
    have hdisj_S' : Disjoint T₀ S' := Finset.disjoint_of_subset_right hS'Y hT₀_disj_Y
    have hdisj_R' : Disjoint T₀ R' := Finset.disjoint_of_subset_right hR'Y hT₀_disj_Y
    have heq : T₀ ∪ S' = T₀ ∪ R' := hfeq
    -- Use sdiff: S' = (T₀ ∪ S') \ T₀ when T₀ is disjoint from S'.
    have hS'_eq : S' = (T₀ ∪ S') \ T₀ := by
      ext x
      constructor
      · intro hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
        exact fun hxT₀ => (Finset.disjoint_left.mp hdisj_S' hxT₀ hx).elim
      · intro hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxun, hxnT₀⟩
        rcases Finset.mem_union.mp hxun with hxT₀ | hxS'
        · exact (hxnT₀ hxT₀).elim
        · exact hxS'
    have hR'_eq : R' = (T₀ ∪ R') \ T₀ := by
      ext x
      constructor
      · intro hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
        exact fun hxT₀ => (Finset.disjoint_left.mp hdisj_R' hxT₀ hx).elim
      · intro hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxun, hxnT₀⟩
        rcases Finset.mem_union.mp hxun with hxT₀ | hxR'
        · exact (hxnT₀ hxT₀).elim
        · exact hxR'
    rw [hS'_eq, hR'_eq, heq]
  -- The image of Y.powerset under f is exactly the filter we sum over.
  have him :
      Y.powerset.image f =
        X.powerset.filter (fun T => T ∈ upClosureIn X {T₀}) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_filter,
      mem_upClosureIn, Finset.mem_singleton]
    constructor
    · rintro ⟨S', hS'Y, rfl⟩
      have hS'X : S' ⊆ X := hS'Y.trans Finset.sdiff_subset
      have hfX : T₀ ∪ S' ⊆ X := Finset.union_subset hT₀ hS'X
      refine ⟨hfX, hfX, T₀, rfl, ?_⟩
      exact Finset.subset_union_left
    · rintro ⟨hTX, _, S₀, hS₀eq, hS₀T⟩
      refine ⟨T \ T₀, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxnT₀⟩
        exact Finset.mem_sdiff.mpr ⟨hTX hxT, hxnT₀⟩
      · -- f (T \ T₀) = T₀ ∪ (T \ T₀) = T, since T₀ ⊆ T (via S₀ = T₀ ⊆ T).
        have hT₀T : T₀ ⊆ T := by
          have := hS₀T
          rw [hS₀eq] at this
          exact this
        show T₀ ∪ (T \ T₀) = T
        ext x
        constructor
        · intro hx
          rcases Finset.mem_union.mp hx with hxT₀ | hxd
          · exact hT₀T hxT₀
          · exact (Finset.mem_sdiff.mp hxd).1
        · intro hxT
          by_cases hxT₀ : x ∈ T₀
          · exact Finset.mem_union.mpr (Or.inl hxT₀)
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxT, hxT₀⟩))
  -- Now: muP = Σ_{T in filter} bernoulli T = Σ_{S' ⊆ Y} bernoulli (T₀ ∪ S').
  unfold muP
  rw [← him, Finset.sum_image hf_inj]
  -- bernoulliMass X (T₀ ∪ S') p = p^|T₀ ∪ S'| (1-p)^(|X| - |T₀ ∪ S'|)
  --                              = p^(|T₀| + |S'|) (1-p)^(|Y| - |S'|)
  --                              = p^|T₀| · [p^|S'| (1-p)^(|Y| - |S'|)]
  have hkey :
      ∀ S' ∈ Y.powerset,
        bernoulliMass X (f S') p = p ^ T₀.card * bernoulliMass Y S' p := by
    intro S' hS'
    have hS'Y : S' ⊆ Y := Finset.mem_powerset.mp hS'
    have hdisj : Disjoint T₀ S' := Finset.disjoint_of_subset_right hS'Y hT₀_disj_Y
    have hcard : (T₀ ∪ S').card = T₀.card + S'.card :=
      Finset.card_union_of_disjoint hdisj
    have hsum_eq : X.card - (T₀.card + S'.card) = Y.card - S'.card := by
      rw [hY_card]; omega
    show p ^ (f S').card * (1 - p) ^ (X.card - (f S').card)
        = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
    show p ^ (T₀ ∪ S').card * (1 - p) ^ (X.card - (T₀ ∪ S').card)
        = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
    rw [hcard, hsum_eq, pow_add, mul_assoc]
  -- Apply hkey, factor out p^|T₀|, and use sum_bernoulliMass_eq_one on Y.
  rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum]
  have : (∑ S' ∈ Y.powerset, bernoulliMass Y S' p) = 1 :=
    sum_bernoulliMass_eq_one (α := α) Y (p := p) (by ring)
  rw [this, mul_one]

/-! ## Conditioning on one coordinate -/

/-- If `S ⊆ X` and `a ∉ X`, then the Bernoulli mass of `S` inside
`insert a X` is `(1-p)` times its mass inside `X`. -/
lemma bernoulliMass_insert_of_notMem {X S : Finset α} {a : α} {p : ℝ}
    (ha : a ∉ X) (hS : S ⊆ X) :
    bernoulliMass (insert a X) S p = (1 - p) * bernoulliMass X S p := by
  have hcardX : (insert a X).card = X.card + 1 := Finset.card_insert_of_notMem ha
  have hS_le : S.card ≤ X.card := Finset.card_le_card hS
  have hdiff : (insert a X).card - S.card = (X.card - S.card) + 1 := by
    rw [hcardX]
    omega
  unfold bernoulliMass
  rw [hdiff, pow_succ]
  ring

/-- If `S ⊆ X` and `a ∉ X`, then the Bernoulli mass of `insert a S` inside
`insert a X` is `p` times the mass of `S` inside `X`. -/
lemma bernoulliMass_insert_with_mem {X S : Finset α} {a : α} {p : ℝ}
    (ha : a ∉ X) (hS : S ⊆ X) :
    bernoulliMass (insert a X) (insert a S) p = p * bernoulliMass X S p := by
  have haS : a ∉ S := fun h => ha (hS h)
  have hcardX : (insert a X).card = X.card + 1 := Finset.card_insert_of_notMem ha
  have hcardS : (insert a S).card = S.card + 1 := Finset.card_insert_of_notMem haS
  have hS_le : S.card ≤ X.card := Finset.card_le_card hS
  have hdiff : (insert a X).card - (S.card + 1) = X.card - S.card := by
    rw [hcardX]
    omega
  unfold bernoulliMass
  rw [hcardS, hdiff, pow_succ]
  ring

/-- On subsets of `X`, adjoining a new element `a ∉ X` is injective. -/
lemma insert_injective_on_powerset_of_notMem {X : Finset α} {a : α}
    (ha : a ∉ X) :
    Set.InjOn (fun S : Finset α => insert a S) X.powerset := by
  intro S hS T hT hST
  have haS : a ∉ S := fun h => ha ((Finset.mem_powerset.mp hS) h)
  have haT : a ∉ T := fun h => ha ((Finset.mem_powerset.mp hT) h)
  calc
    S = (insert a S).erase a := (Finset.erase_insert haS).symm
    _ = (insert a T).erase a := congrArg (fun U : Finset α => U.erase a) hST
    _ = T := Finset.erase_insert haT

/-- The old subsets of `X` are disjoint from the subsets obtained by adjoining
a new element `a`. -/
lemma powerset_disjoint_image_insert_of_notMem {X : Finset α} {a : α}
    (ha : a ∉ X) :
    Disjoint X.powerset (X.powerset.image fun S : Finset α => insert a S) := by
  rw [Finset.disjoint_left]
  intro S hS hSimage
  rcases Finset.mem_image.mp hSimage with ⟨T, _hT, rfl⟩
  have ha_insert : a ∈ insert a T := Finset.mem_insert_self a T
  have ha_not_insert : a ∉ insert a T := fun h =>
    ha ((Finset.mem_powerset.mp hS) h)
  exact ha_not_insert ha_insert

/-- Slice of a family consisting of members not using the new coordinate. -/
noncomputable def withoutCoordFamily (X : Finset α) (U : Finset (Finset α)) :
    Finset (Finset α) :=
  X.powerset.filter fun S => S ∈ U

/-- Slice of a family consisting of members that use the new coordinate,
with that coordinate removed. -/
noncomputable def withCoordFamily (a : α) (X : Finset α)
    (U : Finset (Finset α)) : Finset (Finset α) :=
  X.powerset.filter fun S => insert a S ∈ U

/-- Slice of a family seen after unioning with a fixed exposure `W`. -/
noncomputable def unionShiftFamily (X : Finset α)
    (U : Finset (Finset α)) (W : Finset α) : Finset (Finset α) :=
  X.powerset.filter fun S => S ∪ W ∈ U

lemma mem_unionShiftFamily {X : Finset α} {U : Finset (Finset α)}
    {W S : Finset α} :
    S ∈ unionShiftFamily X U W ↔ S ⊆ X ∧ S ∪ W ∈ U := by
  simp [unionShiftFamily]

lemma unionShiftFamily_subset_ground
    (X : Finset α) (U : Finset (Finset α)) (W : Finset α) :
    ∀ S ∈ unionShiftFamily X U W, S ⊆ X := by
  intro S hS
  exact (mem_unionShiftFamily.mp hS).1

lemma withoutCoordFamily_unionShiftFamily_absent
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
    (hW : W ⊆ X) :
    withoutCoordFamily X (unionShiftFamily (insert a X) U W) =
      unionShiftFamily X (withoutCoordFamily X U) W := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSshift⟩
    rcases mem_unionShiftFamily.mp hSshift with ⟨_hS_insert, hSU⟩
    exact mem_unionShiftFamily.mpr
      ⟨Finset.mem_powerset.mp hSX,
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
            hSU⟩⟩
  · intro hS
    rcases mem_unionShiftFamily.mp hS with ⟨hSX, hSU0⟩
    rcases Finset.mem_filter.mp hSU0 with ⟨_hunionX, hSU⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSX,
        mem_unionShiftFamily.mpr
          ⟨hSX.trans (Finset.subset_insert a X), hSU⟩⟩

lemma withCoordFamily_unionShiftFamily_absent
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
    (hW : W ⊆ X) :
    withCoordFamily a X (unionShiftFamily (insert a X) U W) =
      unionShiftFamily X (withCoordFamily a X U) W := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSshift⟩
    rcases mem_unionShiftFamily.mp hSshift with ⟨_hinsertX, hSU⟩
    have hrewrite : insert a (S ∪ W) = insert a S ∪ W := by
      ext x
      simp [or_comm]
    exact mem_unionShiftFamily.mpr
      ⟨Finset.mem_powerset.mp hSX,
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
            by rwa [hrewrite]⟩⟩
  · intro hS
    rcases mem_unionShiftFamily.mp hS with ⟨hSX, hSU1⟩
    rcases Finset.mem_filter.mp hSU1 with ⟨_hunionX, hSU⟩
    have hrewrite : insert a S ∪ W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSX,
        mem_unionShiftFamily.mpr
          ⟨Finset.insert_subset (Finset.mem_insert_self a X)
            (hSX.trans (Finset.subset_insert a X)),
            by rwa [hrewrite]⟩⟩

lemma withoutCoordFamily_unionShiftFamily_present
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
    (hW : W ⊆ X) :
    withoutCoordFamily X (unionShiftFamily (insert a X) U (insert a W)) =
      unionShiftFamily X (withCoordFamily a X U) W := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSshift⟩
    rcases mem_unionShiftFamily.mp hSshift with ⟨_hS_insert, hSU⟩
    have hrewrite : S ∪ insert a W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact mem_unionShiftFamily.mpr
      ⟨Finset.mem_powerset.mp hSX,
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
            by rwa [← hrewrite]⟩⟩
  · intro hS
    rcases mem_unionShiftFamily.mp hS with ⟨hSX, hSU1⟩
    rcases Finset.mem_filter.mp hSU1 with ⟨_hunionX, hSU⟩
    have hrewrite : S ∪ insert a W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSX,
        mem_unionShiftFamily.mpr
          ⟨hSX.trans (Finset.subset_insert a X),
            by rwa [hrewrite]⟩⟩

lemma withCoordFamily_unionShiftFamily_present
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
    (hW : W ⊆ X) :
    withCoordFamily a X (unionShiftFamily (insert a X) U (insert a W)) =
      unionShiftFamily X (withCoordFamily a X U) W := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSshift⟩
    rcases mem_unionShiftFamily.mp hSshift with ⟨_hinsertX, hSU⟩
    have hrewrite : insert a S ∪ insert a W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact mem_unionShiftFamily.mpr
      ⟨Finset.mem_powerset.mp hSX,
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
            by rwa [← hrewrite]⟩⟩
  · intro hS
    rcases mem_unionShiftFamily.mp hS with ⟨hSX, hSU1⟩
    rcases Finset.mem_filter.mp hSU1 with ⟨_hunionX, hSU⟩
    have hrewrite : insert a S ∪ insert a W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSX,
        mem_unionShiftFamily.mpr
          ⟨Finset.insert_subset (Finset.mem_insert_self a X)
              (hSX.trans (Finset.subset_insert a X)),
            by rwa [hrewrite]⟩⟩

/-- Product measure conditioned on whether a new coordinate is absent or
present. -/
lemma muP_insert_split {X : Finset α} {U : Finset (Finset α)} {a : α} {p : ℝ}
    (ha : a ∉ X) :
    muP (insert a X) U p =
      (1 - p) * muP X (withoutCoordFamily X U) p +
        p * muP X (withCoordFamily a X U) p := by
  classical
  let ins : Finset α → Finset α := fun S => insert a S
  let A : Finset (Finset α) := X.powerset.filter fun S => S ∈ U
  let B : Finset (Finset α) := (X.powerset.image ins).filter fun S => S ∈ U
  have hdisj_raw :
      Disjoint X.powerset (X.powerset.image ins) := by
    simpa [ins] using powerset_disjoint_image_insert_of_notMem (X := X) (a := a) ha
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro S hSA hSB
    exact (Finset.disjoint_left.mp hdisj_raw)
      (Finset.mem_filter.mp hSA).1 (Finset.mem_filter.mp hSB).1
  have hfilter_union :
      (insert a X).powerset.filter (fun S => S ∈ U) = A ∪ B := by
    calc
      (insert a X).powerset.filter (fun S => S ∈ U)
          = (X.powerset ∪ X.powerset.image ins).filter (fun S => S ∈ U) := by
            rw [Finset.powerset_insert]
      _ = A ∪ B := by
            rw [Finset.filter_union]
  have hU0_filter :
      X.powerset.filter (fun S => S ∈ withoutCoordFamily X U) = A := by
    ext S
    simp [withoutCoordFamily, A]
  have hterm0 :
      (∑ S ∈ A, bernoulliMass (insert a X) S p) =
        (1 - p) * muP X (withoutCoordFamily X U) p := by
    calc
      (∑ S ∈ A, bernoulliMass (insert a X) S p)
          = ∑ S ∈ A, (1 - p) * bernoulliMass X S p := by
            refine Finset.sum_congr rfl ?_
            intro S hSA
            have hSX : S ⊆ X :=
              Finset.mem_powerset.mp (Finset.mem_filter.mp hSA).1
            exact bernoulliMass_insert_of_notMem ha hSX
      _ = (1 - p) * ∑ S ∈ A, bernoulliMass X S p := by
            rw [Finset.mul_sum]
      _ = (1 - p) * muP X (withoutCoordFamily X U) p := by
            unfold muP
            rw [hU0_filter]
  have hB_image :
      (X.powerset.filter fun S => ins S ∈ U).image ins = B := by
    ext R
    constructor
    · intro hR
      rcases Finset.mem_image.mp hR with ⟨S, hS, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨S, (Finset.mem_filter.mp hS).1, rfl⟩,
          (Finset.mem_filter.mp hS).2⟩
    · intro hR
      rcases Finset.mem_filter.mp hR with ⟨hRimg, hRU⟩
      rcases Finset.mem_image.mp hRimg with ⟨S, hS, rfl⟩
      exact Finset.mem_image.mpr
        ⟨S, Finset.mem_filter.mpr ⟨hS, hRU⟩, rfl⟩
  have hinj :
      Set.InjOn ins (↑(X.powerset.filter fun S => ins S ∈ U)) := by
    exact (insert_injective_on_powerset_of_notMem (X := X) (a := a) ha).mono
      (by intro S hS; exact (Finset.mem_filter.mp hS).1)
  have hU1_filter :
      X.powerset.filter (fun S => S ∈ withCoordFamily a X U) =
        X.powerset.filter fun S => ins S ∈ U := by
    ext S
    simp [withCoordFamily, ins]
  have hterm1 :
      (∑ S ∈ B, bernoulliMass (insert a X) S p) =
        p * muP X (withCoordFamily a X U) p := by
    calc
      (∑ S ∈ B, bernoulliMass (insert a X) S p)
          = ∑ S ∈ (X.powerset.filter fun S => ins S ∈ U).image ins,
              bernoulliMass (insert a X) S p := by rw [hB_image]
      _ = ∑ S ∈ X.powerset.filter (fun S => ins S ∈ U),
              bernoulliMass (insert a X) (ins S) p := by
            rw [Finset.sum_image hinj]
      _ = ∑ S ∈ X.powerset.filter (fun S => ins S ∈ U),
              p * bernoulliMass X S p := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            have hSX : S ⊆ X := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
            simpa [ins] using bernoulliMass_insert_with_mem (X := X) (S := S)
              (a := a) (p := p) ha hSX
      _ = p * ∑ S ∈ X.powerset.filter (fun S => ins S ∈ U),
              bernoulliMass X S p := by
            rw [Finset.mul_sum]
      _ = p * muP X (withCoordFamily a X U) p := by
            unfold muP
            rw [hU1_filter]
  calc
    muP (insert a X) U p
        = ∑ S ∈ A ∪ B, bernoulliMass (insert a X) S p := by
          unfold muP
          rw [hfilter_union]
    _ = (∑ S ∈ A, bernoulliMass (insert a X) S p) +
        ∑ S ∈ B, bernoulliMass (insert a X) S p := by
          rw [Finset.sum_union hdisj]
    _ = (1 - p) * muP X (withoutCoordFamily X U) p +
        p * muP X (withCoordFamily a X U) p := by
          rw [hterm0, hterm1]

/-- Splitting a fixed-union slice when the fixed exposure does not contain the
new coordinate. -/
lemma muP_insert_unionShift_absent
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α} {p : ℝ}
    (ha : a ∉ X) (hW : W ⊆ X) :
    muP (insert a X) (unionShiftFamily (insert a X) U W) p =
      (1 - p) *
          muP X (unionShiftFamily X (withoutCoordFamily X U) W) p +
        p * muP X (unionShiftFamily X (withCoordFamily a X U) W) p := by
  rw [muP_insert_split (X := X)
    (U := unionShiftFamily (insert a X) U W) (a := a) (p := p) ha]
  rw [withoutCoordFamily_unionShiftFamily_absent (a := a) hW,
    withCoordFamily_unionShiftFamily_absent (a := a) hW]

/-- Splitting a fixed-union slice when the fixed exposure already contains the
new coordinate. -/
lemma muP_insert_unionShift_present
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α} {p : ℝ}
    (ha : a ∉ X) (hW : W ⊆ X) :
    muP (insert a X) (unionShiftFamily (insert a X) U (insert a W)) p =
      muP X (unionShiftFamily X (withCoordFamily a X U) W) p := by
  rw [muP_insert_split (X := X)
    (U := unionShiftFamily (insert a X) U (insert a W)) (a := a) (p := p) ha]
  rw [withoutCoordFamily_unionShiftFamily_present (a := a) hW,
    withCoordFamily_unionShiftFamily_present (a := a) hW]
  ring

/-- The union of two independent Bernoulli subsets has Bernoulli density
`1 - (1 - θ) * (1 - r)`.  This is stated as a finite convolution over the
second exposure `W`, with `unionShiftFamily` encoding the first exposure's
target event. -/
lemma muP_unionShift_average_eq_muP_union_density
    (X : Finset α) (U : Finset (Finset α)) (θ r : ℝ) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W r * muP X (unionShiftFamily X U W) θ) =
      muP X U (1 - (1 - θ) * (1 - r)) := by
  classical
  induction X using Finset.induction generalizing U with
  | empty =>
      by_cases hEmpty : (∅ : Finset α) ∈ U
      · have hleft_filter :
            ({∅} : Finset (Finset α)).filter
              (fun S => S = ∅ ∧ S ∈ U) = {∅} := by
          apply Finset.filter_eq_self.mpr
          intro S hS
          have hSempty : S = ∅ := by simpa using hS
          exact ⟨hSempty, by simpa [hSempty] using hEmpty⟩
        have hright_filter :
            ({∅} : Finset (Finset α)).filter
              (fun S => S ∈ U) = {∅} := by
          apply Finset.filter_eq_self.mpr
          intro S hS
          have hSempty : S = ∅ := by simpa using hS
          simpa [hSempty] using hEmpty
        simp [muP, bernoulliMass, unionShiftFamily, hleft_filter, hright_filter]
      · have hleft_filter :
            ({∅} : Finset (Finset α)).filter
              (fun S => S = ∅ ∧ S ∈ U) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro S hS hbad
          exact hEmpty (by simpa [hbad.1] using hbad.2)
        have hright_filter :
            ({∅} : Finset (Finset α)).filter
              (fun S => S ∈ U) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro S hS hSU
          have hSempty : S = ∅ := by simpa using hS
          exact hEmpty (by simpa [hSempty] using hSU)
        simp [muP, bernoulliMass, unionShiftFamily, hleft_filter, hright_filter]
  | insert a X ha ih =>
      let η : ℝ := 1 - (1 - θ) * (1 - r)
      let ins : Finset α → Finset α := fun S => insert a S
      have hdisj :
          Disjoint X.powerset (X.powerset.image ins) := by
        simpa [ins] using powerset_disjoint_image_insert_of_notMem
          (X := X) (a := a) ha
      have hinj : Set.InjOn ins (↑X.powerset) := by
        simpa [ins] using insert_injective_on_powerset_of_notMem
          (X := X) (a := a) ha
      have hpowerset_split :
          (∑ W ∈ (insert a X).powerset,
            bernoulliMass (insert a X) W r *
              muP (insert a X) (unionShiftFamily (insert a X) U W) θ) =
            (∑ W ∈ X.powerset,
              bernoulliMass (insert a X) W r *
                muP (insert a X) (unionShiftFamily (insert a X) U W) θ) +
              ∑ W ∈ X.powerset,
                bernoulliMass (insert a X) (insert a W) r *
                  muP (insert a X)
                    (unionShiftFamily (insert a X) U (insert a W)) θ := by
        calc
          (∑ W ∈ (insert a X).powerset,
            bernoulliMass (insert a X) W r *
              muP (insert a X) (unionShiftFamily (insert a X) U W) θ)
              = ∑ W ∈ X.powerset ∪ X.powerset.image ins,
                  bernoulliMass (insert a X) W r *
                    muP (insert a X) (unionShiftFamily (insert a X) U W) θ := by
                    rw [Finset.powerset_insert]
          _ = (∑ W ∈ X.powerset,
                bernoulliMass (insert a X) W r *
                  muP (insert a X) (unionShiftFamily (insert a X) U W) θ) +
                ∑ W ∈ X.powerset.image ins,
                  bernoulliMass (insert a X) W r *
                    muP (insert a X) (unionShiftFamily (insert a X) U W) θ := by
                    rw [Finset.sum_union hdisj]
          _ = (∑ W ∈ X.powerset,
                bernoulliMass (insert a X) W r *
                  muP (insert a X) (unionShiftFamily (insert a X) U W) θ) +
                ∑ W ∈ X.powerset,
                  bernoulliMass (insert a X) (insert a W) r *
                    muP (insert a X)
                      (unionShiftFamily (insert a X) U (insert a W)) θ := by
                    rw [Finset.sum_image hinj]
      have habsent :
          (∑ W ∈ X.powerset,
            bernoulliMass (insert a X) W r *
              muP (insert a X) (unionShiftFamily (insert a X) U W) θ) =
            ((1 - r) * (1 - θ)) *
                (∑ W ∈ X.powerset,
                  bernoulliMass X W r *
                    muP X (unionShiftFamily X (withoutCoordFamily X U) W) θ) +
              ((1 - r) * θ) *
                (∑ W ∈ X.powerset,
                  bernoulliMass X W r *
                    muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
        calc
          (∑ W ∈ X.powerset,
            bernoulliMass (insert a X) W r *
              muP (insert a X) (unionShiftFamily (insert a X) U W) θ)
              = ∑ W ∈ X.powerset,
                  (((1 - r) * (1 - θ)) *
                    (bernoulliMass X W r *
                      muP X (unionShiftFamily X (withoutCoordFamily X U) W) θ) +
                  ((1 - r) * θ) *
                    (bernoulliMass X W r *
                      muP X (unionShiftFamily X (withCoordFamily a X U) W) θ)) := by
                    refine Finset.sum_congr rfl ?_
                    intro W hW
                    have hWX : W ⊆ X := Finset.mem_powerset.mp hW
                    rw [bernoulliMass_insert_of_notMem ha hWX,
                      muP_insert_unionShift_absent (X := X) (U := U)
                        (a := a) (W := W) (p := θ) ha hWX]
                    ring
          _ = ((1 - r) * (1 - θ)) *
                (∑ W ∈ X.powerset,
                  bernoulliMass X W r *
                    muP X (unionShiftFamily X (withoutCoordFamily X U) W) θ) +
              ((1 - r) * θ) *
                (∑ W ∈ X.powerset,
                  bernoulliMass X W r *
                    muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
                    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      have hpresent :
          (∑ W ∈ X.powerset,
            bernoulliMass (insert a X) (insert a W) r *
              muP (insert a X)
                (unionShiftFamily (insert a X) U (insert a W)) θ) =
            r *
              (∑ W ∈ X.powerset,
                bernoulliMass X W r *
                  muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
        calc
          (∑ W ∈ X.powerset,
            bernoulliMass (insert a X) (insert a W) r *
              muP (insert a X)
                (unionShiftFamily (insert a X) U (insert a W)) θ)
              = ∑ W ∈ X.powerset,
                  r *
                    (bernoulliMass X W r *
                      muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
                    refine Finset.sum_congr rfl ?_
                    intro W hW
                    have hWX : W ⊆ X := Finset.mem_powerset.mp hW
                    rw [bernoulliMass_insert_with_mem ha hWX,
                      muP_insert_unionShift_present (X := X) (U := U)
                        (a := a) (W := W) (p := θ) ha hWX]
                    ring
          _ = r *
              (∑ W ∈ X.powerset,
                bernoulliMass X W r *
                  muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
                    rw [Finset.mul_sum]
      have hwithout :=
        ih (withoutCoordFamily X U)
      have hwith :=
        ih (withCoordFamily a X U)
      rw [hpowerset_split, habsent, hpresent, hwithout, hwith]
      have hsplit :=
        muP_insert_split (X := X) (U := U) (a := a) (p := η) ha
      change
        ((1 - r) * (1 - θ)) * muP X (withoutCoordFamily X U) η +
            ((1 - r) * θ) * muP X (withCoordFamily a X U) η +
          r * muP X (withCoordFamily a X U) η =
        muP (insert a X) U η
      rw [hsplit]
      ring

/-- Distribution identity for the union of an independent tuple of Bernoulli
exposures.  The union has the same law as one Bernoulli subset with density
`tupleUnionDensity ρ = 1 - ∏ i, (1 - ρ i)`. -/
lemma exposureTupleUnion_measure_eq_muP
    (X : Finset α) (U : Finset (Finset α)) {n : ℕ}
    (ρ : Fin n → ℝ) :
    (∑ Ws ∈ (exposureTupleSpace X n).filter
      (fun Ws => exposureTupleUnion Ws ∈ U),
      exposureTupleWeight X ρ Ws) =
      muP X U (tupleUnionDensity ρ) := by
  classical
  induction n generalizing U with
  | zero =>
      simpa using exposureTupleUnion_measure_zero_density X U ρ
  | succ n ih =>
      let e : Finset α × (Fin n → Finset α) ↪
          (Fin (n + 1) → Finset α) :=
        (Fin.snocEquiv (fun _ : Fin (n + 1) => Finset α)).toEmbedding
      let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
      let ρlast : ℝ := ρ (Fin.last n)
      have hmap :
          (∑ Ws ∈ (exposureTupleSpace X (n + 1)).filter
            (fun Ws => exposureTupleUnion Ws ∈ U),
            exposureTupleWeight X ρ Ws) =
          ∑ P ∈ ((X.powerset ×ˢ exposureTupleSpace X n).filter
              (fun P => exposureTupleUnion (e P) ∈ U)),
            exposureTupleWeight X ρ (e P) := by
        rw [exposureTupleSpace_snoc X n, Finset.filter_map]
        rw [Finset.sum_map]
        rfl
      have hproduct :
          (∑ P ∈ ((X.powerset ×ˢ exposureTupleSpace X n).filter
              (fun P => exposureTupleUnion (e P) ∈ U)),
            exposureTupleWeight X ρ (e P)) =
          ∑ W ∈ X.powerset,
            ∑ Ws ∈ (exposureTupleSpace X n).filter
              (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
              exposureTupleWeight X ρ (e (W, Ws)) := by
        rw [Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl ?_
        intro W hW
        rw [← Finset.sum_filter]
        have hfilter :
            (exposureTupleSpace X n).filter
                (fun Ws => exposureTupleUnion (e (W, Ws)) ∈ U) =
              (exposureTupleSpace X n).filter
                (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W) := by
          ext Ws
          by_cases hWs : Ws ∈ exposureTupleSpace X n
          · have hWsX : exposureTupleUnion Ws ⊆ X :=
              exposureTupleUnion_subset hWs
            have hevent :
                exposureTupleUnion (e (W, Ws)) ∈ U ↔
                  exposureTupleUnion Ws ∈ unionShiftFamily X U W := by
              change
                exposureTupleUnion
                    (Fin.snoc
                      (α := fun _ : Fin (n + 1) => Finset α) Ws W) ∈ U ↔
                  exposureTupleUnion Ws ∈ unionShiftFamily X U W
              rw [exposureTupleUnion_snoc]
              simp [mem_unionShiftFamily, hWsX]
            simp [hWs, hevent]
          · simp [hWs]
        rw [hfilter]
      have hfactor :
          (∑ W ∈ X.powerset,
            ∑ Ws ∈ (exposureTupleSpace X n).filter
              (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
              exposureTupleWeight X ρ (e (W, Ws))) =
          ∑ W ∈ X.powerset,
            bernoulliMass X W ρlast *
              (∑ Ws ∈ (exposureTupleSpace X n).filter
                (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                exposureTupleWeight X ρtail Ws) := by
        refine Finset.sum_congr rfl ?_
        intro W hW
        calc
          (∑ Ws ∈ (exposureTupleSpace X n).filter
              (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
              exposureTupleWeight X ρ (e (W, Ws)))
              = ∑ Ws ∈ (exposureTupleSpace X n).filter
                  (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                  exposureTupleWeight X ρtail Ws * bernoulliMass X W ρlast := by
                    refine Finset.sum_congr rfl ?_
                    intro Ws hWs
                    change
                      exposureTupleWeight X ρ
                          (Fin.snoc
                            (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
                        exposureTupleWeight X ρtail Ws *
                          bernoulliMass X W ρlast
                    simp [ρtail, ρlast]
          _ = (∑ Ws ∈ (exposureTupleSpace X n).filter
                  (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                  exposureTupleWeight X ρtail Ws) * bernoulliMass X W ρlast := by
                    rw [Finset.sum_mul]
          _ = bernoulliMass X W ρlast *
                (∑ Ws ∈ (exposureTupleSpace X n).filter
                  (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                  exposureTupleWeight X ρtail Ws) := by
                    ring
      calc
        (∑ Ws ∈ (exposureTupleSpace X (n + 1)).filter
          (fun Ws => exposureTupleUnion Ws ∈ U),
          exposureTupleWeight X ρ Ws)
            = ∑ W ∈ X.powerset,
                bernoulliMass X W ρlast *
                  (∑ Ws ∈ (exposureTupleSpace X n).filter
                    (fun Ws =>
                      exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                    exposureTupleWeight X ρtail Ws) := by
                  rw [hmap, hproduct, hfactor]
        _ = ∑ W ∈ X.powerset,
              bernoulliMass X W ρlast *
                muP X (unionShiftFamily X U W) (tupleUnionDensity ρtail) := by
                  refine Finset.sum_congr rfl ?_
                  intro W hW
                  rw [ih (unionShiftFamily X U W) ρtail]
        _ = muP X U
              (1 - (1 - tupleUnionDensity ρtail) * (1 - ρlast)) :=
            muP_unionShift_average_eq_muP_union_density
              X U (tupleUnionDensity ρtail) ρlast
        _ = muP X U (tupleUnionDensity ρ) := by
            rw [tupleUnionDensity_snoc]

/-- Bernoulli product measure is monotone in the density for increasing
families. -/
theorem muP_mono_density {X : Finset α} {U : Finset (Finset α)} {p q : ℝ}
    (hIncr : IncreasingIn X U) (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1) :
    muP X U p ≤ muP X U q := by
  classical
  induction X using Finset.induction generalizing U with
  | empty =>
      by_cases hU : (∅ : Finset α) ∈ U
      · have hfilter :
            ({∅} : Finset (Finset α)).filter (fun x => x ∈ U) = {∅} := by
          apply Finset.filter_eq_self.mpr
          intro x hx
          have hxempty : x = ∅ := by simpa using hx
          simpa [hxempty] using hU
        simp [muP, bernoulliMass, hfilter]
      · have hfilter :
            ({∅} : Finset (Finset α)).filter (fun x => x ∈ U) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx
          have hxempty : x = ∅ := by simpa using hx
          simpa [hxempty] using hU
        simp [muP, bernoulliMass, hfilter]
  | insert a X ha ih =>
      let U0 : Finset (Finset α) := withoutCoordFamily X U
      let U1 : Finset (Finset α) := withCoordFamily a X U
      have hp1 : p ≤ 1 := hpq.trans hq1
      have hq0 : 0 ≤ q := hp0.trans hpq
      have hIncr0 : IncreasingIn X U0 := by
        intro S hSU0 T hTX hST
        rcases Finset.mem_filter.mp hSU0 with ⟨_hSX, hSU⟩
        have hT_insert : T ⊆ insert a X := hTX.trans (Finset.subset_insert a X)
        have hTU : T ∈ U := hIncr S hSU T hT_insert hST
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTX, hTU⟩
      have hIncr1 : IncreasingIn X U1 := by
        intro S hSU1 T hTX hST
        rcases Finset.mem_filter.mp hSU1 with ⟨_hSX, hInsSU⟩
        have hInsT_insert : insert a T ⊆ insert a X := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxT
          · simp
          · exact Finset.mem_insert.mpr (Or.inr (hTX hxT))
        have hInsSInsT : insert a S ⊆ insert a T := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxS
          · simp
          · exact Finset.mem_insert.mpr (Or.inr (hST hxS))
        have hInsTU : insert a T ∈ U :=
          hIncr (insert a S) hInsSU (insert a T) hInsT_insert hInsSInsT
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTX, hInsTU⟩
      have hU0U1 : U0 ⊆ U1 := by
        intro S hSU0
        rcases Finset.mem_filter.mp hSU0 with ⟨hSXpow, hSU⟩
        have hSX : S ⊆ X := Finset.mem_powerset.mp hSXpow
        have hInsSX : insert a S ⊆ insert a X := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxS
          · simp
          · exact Finset.mem_insert.mpr (Or.inr (hSX hxS))
        have hSInsS : S ⊆ insert a S := Finset.subset_insert a S
        have hInsSU : insert a S ∈ U := hIncr S hSU (insert a S) hInsSX hSInsS
        exact Finset.mem_filter.mpr ⟨hSXpow, hInsSU⟩
      have hF0 : muP X U0 p ≤ muP X U0 q := ih hIncr0
      have hF1 : muP X U1 p ≤ muP X U1 q := ih hIncr1
      have hF01q : muP X U0 q ≤ muP X U1 q :=
        muP_mono_family hq0 hq1 hU0U1
      rw [muP_insert_split (X := X) (U := U) (a := a) (p := p) ha,
        muP_insert_split (X := X) (U := U) (a := a) (p := q) ha]
      have hfirst :
          (1 - p) * muP X U0 p + p * muP X U1 p ≤
            (1 - p) * muP X U0 q + p * muP X U1 q := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hF0 (by linarith))
          (mul_le_mul_of_nonneg_left hF1 hp0)
      have hsecond :
          (1 - p) * muP X U0 q + p * muP X U1 q ≤
            (1 - q) * muP X U0 q + q * muP X U1 q := by
        have hqp_nonneg : 0 ≤ q - p := by linarith
        have hmul := mul_le_mul_of_nonneg_left hF01q hqp_nonneg
        nlinarith
      exact hfirst.trans hsecond

/-- A single member of an increasing family gives a product-measure lower bound:
the event contains all random subsets that include that member. -/
lemma pow_card_le_muP_of_mem_increasing
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U) (hS : S ∈ U) :
    p ^ S.card ≤ muP X U p := by
  have hSX : S ⊆ X := hUX S hS
  have hsub : upClosureIn X {S} ⊆ U :=
    upClosureIn_singleton_subset_of_mem_increasing hIncr hS
  have hmono :
      muP X (upClosureIn X {S}) p ≤ muP X U p :=
    muP_mono_family hp0 hp1 hsub
  have hsingle : muP X (upClosureIn X {S}) p = p ^ S.card :=
    muP_upClosure_single X S hSX hp0 hp1
  simpa [hsingle] using hmono

/-- If an increasing family contains a singleton, its product measure is at
least the density. -/
lemma density_le_muP_of_singleton_mem_increasing
    {X : Finset α} {U : Finset (Finset α)} {a : α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U)
    (hS : ({a} : Finset α) ∈ U) :
    p ≤ muP X U p := by
  have hpow :
      p ^ ({a} : Finset α).card ≤ muP X U p :=
    pow_card_le_muP_of_mem_increasing hp0 hp1 hUX hIncr hS
  simpa using hpow

/-- A nonempty increasing family has product measure at least `p^ell`: choose a
minimal member, whose cardinality is bounded by `ell`. -/
lemma pow_ell_le_muP_of_nonempty_increasing
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U) (hU : U.Nonempty) :
    p ^ ell X U ≤ muP X U p := by
  rcases minimalMembersIn_nonempty_of_nonempty (X := X) hU with ⟨S, hSmin⟩
  have hSU : S ∈ U := minimalMembersIn_subset hSmin
  have hcard : S.card ≤ ell X U := card_le_ell_of_mem_minimalMembersIn hSmin
  have hpow : p ^ ell X U ≤ p ^ S.card :=
    pow_le_pow_of_le_one hp0 hp1 hcard
  exact hpow.trans (pow_card_le_muP_of_mem_increasing hp0 hp1 hUX hIncr hSU)

end

end ParkPham
end Erdos202


/-! =============================================================
    Section from: Erdos/P202/ParkPham/Smallness.lean
    ============================================================= -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 3.

The `p`-small predicate underlying the Kahn–Kalai expectation threshold:
a family `U` is `p`-small if some "cover" `G` (a finite family whose
upper closure contains `U`) has total `p`-weight at most `1/2`.

`qSmallUpper X U q` asserts that `U` is NOT `p`-small for any `p > q`,
i.e. the threshold lies in `[0, q]`. This is the form consumed by the
Park–Pham theorem in `Threshold.lean`.
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- `G` covers `U` inside `X`: every member of `U` contains some member of
`G`. -/
def CoversIn (_X : Finset α) (G U : Finset (Finset α)) : Prop :=
  ∀ S ∈ U, ∃ T ∈ G, T ⊆ S

/-- The `p`-weight of a cover family.  This is the finite quantity minimized
in the expectation-threshold cost. -/
def coverWeight (G : Finset (Finset α)) (p : ℝ) : ℝ :=
  ∑ T ∈ G, p ^ T.card

/-- A family `U` is `p`-small inside `X` if there is a cover `G` with
total weight `∑ p^|T|` at most `1/2`. -/
def pSmall (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : Prop :=
  ∃ G : Finset (Finset α),
    CoversIn X G U ∧ (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ)

/-- `qSmallUpper X U q`: `U` is not `p`-small for any strictly larger `p`. -/
def qSmallUpper (X : Finset α) (U : Finset (Finset α)) (q : ℝ) : Prop :=
  ∀ p : ℝ, q < p → p ≤ 1 → ¬ pSmall X U p

omit [DecidableEq α] in
/-- Direct eliminator for `qSmallUpper`. -/
lemma not_pSmall_of_qSmallUpper {X : Finset α} {U : Finset (Finset α)}
    {q p : ℝ} (hSmall : qSmallUpper X U q) (hqp : q < p) (hp1 : p ≤ 1) :
    ¬ pSmall X U p :=
  hSmall p hqp hp1

omit [DecidableEq α] in
/-- If one finds a `p`-small witness above `q`, then `q` is not an upper bound
for the expectation threshold. -/
lemma not_qSmallUpper_of_pSmall {X : Finset α} {U : Finset (Finset α)}
    {q p : ℝ} (hqp : q < p) (hp1 : p ≤ 1) (hSmall : pSmall X U p) :
    ¬ qSmallUpper X U q := by
  intro hq
  exact hq p hqp hp1 hSmall

omit [DecidableEq α] in
/-- `qSmallUpper` is monotone in the threshold parameter. -/
lemma qSmallUpper_mono_q {X : Finset α} {U : Finset (Finset α)}
    {q₀ q₁ : ℝ} (hqq : q₀ ≤ q₁)
    (hSmall : qSmallUpper X U q₀) :
    qSmallUpper X U q₁ := by
  intro p hq₁p hp1
  exact hSmall p (lt_of_le_of_lt hqq hq₁p) hp1

omit [DecidableEq α] in
/-- The value `q = 1` is always an upper bound in the `qSmallUpper` sense. -/
lemma qSmallUpper_one (X : Finset α) (U : Finset (Finset α)) :
    qSmallUpper X U (1 : ℝ) := by
  intro p hp hp1 _
  linarith

omit [DecidableEq α] in
/-- The empty family is `p`-small for every density. -/
lemma pSmall_empty (X : Finset α) (p : ℝ) :
    pSmall X (∅ : Finset (Finset α)) p := by
  refine ⟨∅, ?_, ?_⟩
  · intro S hS
    simp at hS
  · simp

omit [DecidableEq α] in
/-- A non-small family must be nonempty. -/
lemma nonempty_of_not_pSmall {X : Finset α} {U : Finset (Finset α)}
    {p : ℝ} (h : ¬ pSmall X U p) :
    U.Nonempty := by
  by_contra hU
  have hUeq : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
  exact h (by simpa [hUeq] using pSmall_empty X p)

omit [DecidableEq α] in
/-- At density `1`, the only `p`-small family is the empty family. -/
lemma pSmall_one_iff_empty (X : Finset α) (U : Finset (Finset α)) :
    pSmall X U (1 : ℝ) ↔ U = ∅ := by
  constructor
  · rintro ⟨G, hCover, hsum⟩
    have hGsum : ((G.card : ℕ) : ℝ) ≤ 1 / 2 := by
      simpa using hsum
    have hG_empty : G = ∅ := by
      by_contra hGne
      have hG_nonempty : G.Nonempty := Finset.nonempty_iff_ne_empty.mpr hGne
      have hge : (1 : ℝ) ≤ (G.card : ℝ) := by
        exact_mod_cast (Finset.one_le_card.mpr hG_nonempty)
      linarith
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    rcases hCover S hS with ⟨T, hTG, _⟩
    simp [hG_empty] at hTG
  · intro hU
    subst hU
    exact pSmall_empty X 1

omit [DecidableEq α] in
/-- Non-smallness at density `1` is exactly nonemptiness. -/
lemma not_pSmall_one_iff_nonempty (X : Finset α) (U : Finset (Finset α)) :
    ¬ pSmall X U (1 : ℝ) ↔ U.Nonempty := by
  constructor
  · intro h
    exact nonempty_of_not_pSmall h
  · intro hU hSmall
    exact hU.ne_empty (pSmall_one_iff_empty X U |>.mp hSmall)

omit [DecidableEq α] in
/-- At density `0`, a family is `p`-small exactly when it does not contain
the empty set. -/
lemma pSmall_zero_iff_empty_not_mem (X : Finset α) (U : Finset (Finset α)) :
    pSmall X U (0 : ℝ) ↔ (∅ : Finset α) ∉ U := by
  constructor
  · rintro ⟨G, hCover, hsum⟩ hEmptyU
    rcases hCover ∅ hEmptyU with ⟨T, hTG, hTsub⟩
    have hT_empty : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hxT
      simpa using hTsub hxT
    have hsingle :
        (0 : ℝ) ^ T.card ≤ ∑ S ∈ G, (0 : ℝ) ^ S.card :=
      Finset.single_le_sum
        (s := G) (f := fun S : Finset α => (0 : ℝ) ^ S.card)
        (fun S _ => by positivity) hTG
    have hterm : (0 : ℝ) ^ T.card = 1 := by
      subst hT_empty
      simp
    linarith
  · intro hEmpty
    refine ⟨U, ?_, ?_⟩
    · intro S hS
      exact ⟨S, hS, subset_refl S⟩
    · have hsum_zero : (∑ T ∈ U, (0 : ℝ) ^ T.card) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro T hTU
        have hT_ne : T ≠ ∅ := by
          intro hT_empty
          exact hEmpty (by simpa [hT_empty] using hTU)
        exact by
          have hT_nonempty : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT_ne
          simp [hT_nonempty.card_pos.ne']
      rw [hsum_zero]
      norm_num

omit [DecidableEq α] in
/-- Non-smallness at density `0` is exactly membership of the empty set. -/
lemma not_pSmall_zero_iff_empty_mem (X : Finset α) (U : Finset (Finset α)) :
    ¬ pSmall X U (0 : ℝ) ↔ (∅ : Finset α) ∈ U := by
  rw [pSmall_zero_iff_empty_not_mem]
  exact not_not

omit [DecidableEq α] in
/-- If the family contains `∅`, it is not `p`-small at any nonnegative
density. -/
lemma not_pSmall_of_empty_mem {X : Finset α} {U : Finset (Finset α)}
    {p : ℝ} (hp0 : 0 ≤ p) (hEmpty : (∅ : Finset α) ∈ U) :
    ¬ pSmall X U p := by
  rintro ⟨G, hCover, hsum⟩
  rcases hCover ∅ hEmpty with ⟨T, hTG, hTsub⟩
  have hT_empty : T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hxT
    simpa using hTsub hxT
  have hsingle :
      p ^ T.card ≤ ∑ S ∈ G, p ^ S.card :=
    Finset.single_le_sum
      (s := G) (f := fun S : Finset α => p ^ S.card)
      (fun S _ => pow_nonneg hp0 S.card) hTG
  have hterm : p ^ T.card = 1 := by
    subst hT_empty
    simp
  linarith

omit [DecidableEq α] in
/-- If the family contains `∅`, then every nonnegative `q ≤ 1` is an upper
bound in the `qSmallUpper` sense. -/
lemma qSmallUpper_of_empty_mem {X : Finset α} {U : Finset (Finset α)}
    {q : ℝ} (hq0 : 0 ≤ q) (hEmpty : (∅ : Finset α) ∈ U) :
    qSmallUpper X U q := by
  intro p hqp _hp1
  exact not_pSmall_of_empty_mem (hq0.trans hqp.le) hEmpty

omit [DecidableEq α] in
/-- If `∅ ∉ U`, then `U` is `p`-small at some positive density.  The cover is
`U` itself, and the density is chosen small enough that
`∑_{T∈U} p^|T| ≤ |U|p ≤ 1/2`. -/
lemma exists_pos_pSmall_of_empty_not_mem
    (X : Finset α) (U : Finset (Finset α))
    (hEmpty : (∅ : Finset α) ∉ U) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ pSmall X U p := by
  classical
  let p : ℝ := 1 / (2 * ((U.card : ℝ) + 1))
  have hden_pos : 0 < 2 * ((U.card : ℝ) + 1) := by positivity
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hp_nonneg : 0 ≤ p := hp_pos.le
  have hp_le_one : p ≤ 1 := by
    dsimp [p]
    rw [div_le_one hden_pos]
    have hcard_nonneg : 0 ≤ (U.card : ℝ) := by positivity
    nlinarith
  refine ⟨p, hp_pos, hp_le_one, ?_⟩
  refine ⟨U, ?_, ?_⟩
  · intro S hS
    exact ⟨S, hS, subset_refl S⟩
  · have hterm : ∀ T ∈ U, p ^ T.card ≤ p := by
      intro T hT
      have hT_nonempty : T.Nonempty := by
        by_contra hT_empty
        exact hEmpty (by
          have hT_eq : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT_empty
          simpa [hT_eq] using hT)
      have hcard : 1 ≤ T.card := Finset.one_le_card.mpr hT_nonempty
      calc
        p ^ T.card ≤ p ^ 1 := pow_le_pow_of_le_one hp_nonneg hp_le_one hcard
        _ = p := by simp
    calc
      (∑ T ∈ U, p ^ T.card) ≤ ∑ T ∈ U, p :=
        Finset.sum_le_sum hterm
      _ = (U.card : ℝ) * p := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 / 2 := by
        have hcard_nonneg : 0 ≤ (U.card : ℝ) := by positivity
        dsimp [p]
        field_simp [hden_pos.ne']
        nlinarith

omit [DecidableEq α] in
/-- At the endpoint `q = 0`, `qSmallUpper` is exactly membership of the empty
set. -/
lemma qSmallUpper_zero_iff_empty_mem (X : Finset α) (U : Finset (Finset α)) :
    qSmallUpper X U (0 : ℝ) ↔ (∅ : Finset α) ∈ U := by
  constructor
  · intro hq
    by_contra hEmpty
    rcases exists_pos_pSmall_of_empty_not_mem X U hEmpty with ⟨p, hp0, hp1, hpSmall⟩
    exact hq p hp0 hp1 hpSmall
  · intro hEmpty
    exact qSmallUpper_of_empty_mem le_rfl hEmpty

omit [DecidableEq α] in
/-- Enlarging the cover preserves the covering property. -/
lemma CoversIn.mono_cover {X : Finset α} {G H U : Finset (Finset α)}
    (hGH : G ⊆ H) (hCover : CoversIn X G U) :
    CoversIn X H U := by
  intro S hS
  rcases hCover S hS with ⟨T, hTG, hTS⟩
  exact ⟨T, hGH hTG, hTS⟩

omit [DecidableEq α] in
/-- A cover of a larger family covers every subfamily. -/
lemma CoversIn.mono_family {X : Finset α} {G U V : Finset (Finset α)}
    (hVU : V ⊆ U) (hCover : CoversIn X G U) :
    CoversIn X G V := by
  intro S hS
  exact hCover S (hVU hS)

/-- The union of two covers covers the union of the target families. -/
lemma CoversIn.union {X : Finset α} {G H U V : Finset (Finset α)}
    (hG : CoversIn X G U) (hH : CoversIn X H V) :
    CoversIn X (G ∪ H) (U ∪ V) := by
  intro S hS
  rcases Finset.mem_union.mp hS with hSU | hSV
  · rcases hG S hSU with ⟨T, hTG, hTS⟩
    exact ⟨T, Finset.mem_union.mpr (Or.inl hTG), hTS⟩
  · rcases hH S hSV with ⟨T, hTH, hTS⟩
    exact ⟨T, Finset.mem_union.mpr (Or.inr hTH), hTS⟩

/-- Covering is the same as containment in the upper closure, once the target
family is known to live inside the ground universe. -/
lemma CoversIn_iff_subset_upClosureIn {X : Finset α} {G U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) :
    CoversIn X G U ↔ U ⊆ upClosureIn X G := by
  constructor
  · intro hCover S hS
    rcases hCover S hS with ⟨T, hTG, hTS⟩
    exact mem_upClosureIn.mpr ⟨hUX S hS, T, hTG, hTS⟩
  · intro hsub S hS
    rcases mem_upClosureIn.mp (hsub hS) with ⟨_, T, hTG, hTS⟩
    exact ⟨T, hTG, hTS⟩

/-- Covering a family is equivalent to covering its upper closure, provided the
original family lives in the ground universe. -/
lemma CoversIn_upClosureIn_iff {X : Finset α} {G U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) :
    CoversIn X G (upClosureIn X U) ↔ CoversIn X G U := by
  constructor
  · intro hCover S hS
    exact hCover S (subset_upClosureIn hUX hS)
  · intro hCover S hS
    rcases mem_upClosureIn.mp hS with ⟨_, T, hTU, hTS⟩
    rcases hCover T hTU with ⟨R, hRG, hRT⟩
    exact ⟨R, hRG, hRT.trans hTS⟩

/-- If the target family lives inside `X`, a cover can be restricted to sets
inside `X` without losing the covering property. -/
lemma CoversIn.filter_subset_ground {X : Finset α} {G U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hCover : CoversIn X G U) :
    CoversIn X (G.filter fun T => T ⊆ X) U := by
  intro S hS
  rcases hCover S hS with ⟨T, hTG, hTS⟩
  have hTX : T ⊆ X := hTS.trans (hUX S hS)
  exact ⟨T, Finset.mem_filter.mpr ⟨hTG, hTX⟩, hTS⟩

lemma pSmall_upClosureIn_iff {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hUX : ∀ S ∈ U, S ⊆ X) :
    pSmall X (upClosureIn X U) p ↔ pSmall X U p := by
  constructor
  · rintro ⟨G, hCover, hsum⟩
    exact ⟨G, (CoversIn_upClosureIn_iff hUX).mp hCover, hsum⟩
  · rintro ⟨G, hCover, hsum⟩
    exact ⟨G, (CoversIn_upClosureIn_iff hUX).mpr hCover, hsum⟩

lemma not_pSmall_upClosureIn_iff {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hUX : ∀ S ∈ U, S ⊆ X) :
    ¬ pSmall X (upClosureIn X U) p ↔ ¬ pSmall X U p := by
  rw [pSmall_upClosureIn_iff hUX]

lemma qSmallUpper_upClosureIn_iff {X : Finset α} {U : Finset (Finset α)} {q : ℝ}
    (hUX : ∀ S ∈ U, S ⊆ X) :
    qSmallUpper X (upClosureIn X U) q ↔ qSmallUpper X U q := by
  constructor
  · intro hSmall p hqp hp1 hSmallU
    exact hSmall p hqp hp1 ((pSmall_upClosureIn_iff hUX).mpr hSmallU)
  · intro hSmall p hqp hp1 hSmallClosure
    exact hSmall p hqp hp1 ((pSmall_upClosureIn_iff hUX).mp hSmallClosure)

omit [DecidableEq α] in
/-- A single cover with total weight at most `1/2` proves `p`-smallness. -/
lemma pSmall_of_cover_sum_le {X : Finset α} {U G : Finset (Finset α)}
    {p : ℝ} (hCover : CoversIn X G U)
    (hsum : (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ)) :
    pSmall X U p :=
  ⟨G, hCover, hsum⟩

/-- Cover weight is subadditive under union, with nonnegative density. -/
lemma coverWeight_union_le {G H : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) :
    coverWeight (G ∪ H) p ≤ coverWeight G p + coverWeight H p := by
  classical
  unfold coverWeight
  let H' : Finset (Finset α) := H \ G
  have hdisj : Disjoint G H' := by
    exact disjoint_sdiff
  have hunion : G ∪ H = G ∪ H' := by
    ext T
    by_cases hTG : T ∈ G <;> simp [H', hTG]
  calc
    (∑ T ∈ G ∪ H, p ^ T.card)
        = ∑ T ∈ G ∪ H', p ^ T.card := by rw [hunion]
    _ = (∑ T ∈ G, p ^ T.card) + ∑ T ∈ H', p ^ T.card := by
      rw [Finset.sum_union hdisj]
    _ ≤ (∑ T ∈ G, p ^ T.card) + ∑ T ∈ H, p ^ T.card := by
      exact add_le_add_right
        (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.sdiff_subset : H' ⊆ H)
        (by intro T _ _; exact pow_nonneg hp0 T.card))
        (∑ T ∈ G, p ^ T.card)

/-- A `pSmall` witness may be chosen with every cover set inside the ground
universe. -/
lemma pSmall.exists_ground_cover
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hUX : ∀ S ∈ U, S ⊆ X) (hSmall : pSmall X U p) :
    ∃ G : Finset (Finset α),
      (∀ T ∈ G, T ⊆ X) ∧
      CoversIn X G U ∧
      (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ) := by
  rcases hSmall with ⟨G, hCover, hsum⟩
  refine ⟨G.filter fun T => T ⊆ X, ?_, ?_, ?_⟩
  · intro T hT
    exact (Finset.mem_filter.mp hT).2
  · exact hCover.filter_subset_ground hUX
  · have hfilter_le :
        (∑ T ∈ G.filter (fun T => T ⊆ X), p ^ T.card) ≤
          ∑ T ∈ G, p ^ T.card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intro T _ _; exact pow_nonneg hp0 T.card)
    exact hfilter_le.trans hsum

omit [DecidableEq α] in
/-- Contrapositive form of `pSmall`: if `U` is not `p`-small, every cover has
weight strictly larger than `1/2`. -/
lemma cover_sum_gt_half_of_not_pSmall
    {X : Finset α} {U G : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X U p) (hCover : CoversIn X G U) :
    (1 / 2 : ℝ) < ∑ T ∈ G, p ^ T.card := by
  exact lt_of_not_ge fun hsum => h (pSmall_of_cover_sum_le hCover hsum)

omit [DecidableEq α] in
/-- Logical normal form for non-smallness. -/
lemma not_pSmall_iff_forall_cover_sum_gt_half
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} :
    ¬ pSmall X U p ↔
      ∀ G : Finset (Finset α), CoversIn X G U →
        (1 / 2 : ℝ) < ∑ T ∈ G, p ^ T.card := by
  constructor
  · intro h G hCover
    exact cover_sum_gt_half_of_not_pSmall h hCover
  · intro h hSmall
    rcases hSmall with ⟨G, hCover, hsum⟩
    exact not_le_of_gt (h G hCover) hsum

/-- Minimal members are a canonical cover of a family. -/
lemma minimalMembers_cover (X : Finset α) (U : Finset (Finset α)) :
    CoversIn X (minimalMembersIn X U) U := by
  intro S hS
  exact exists_minimal_subset hS

/-- A generating family covers its own upper closure. -/
lemma generators_cover_upClosureIn (X : Finset α) (A : Finset (Finset α)) :
    CoversIn X A (upClosureIn X A) := by
  intro S hS
  rcases mem_upClosureIn.mp hS with ⟨_, T, hTA, hTS⟩
  exact ⟨T, hTA, hTS⟩

/-- Covering the minimal members is equivalent to covering the whole family. -/
lemma CoversIn_minimalMembersIn_iff
    {X : Finset α} {G U : Finset (Finset α)} :
    CoversIn X G (minimalMembersIn X U) ↔ CoversIn X G U := by
  constructor
  · intro hCover S hS
    rcases exists_minimal_subset (X := X) hS with ⟨T, hTmin, hTS⟩
    rcases hCover T hTmin with ⟨R, hRG, hRT⟩
    exact ⟨R, hRG, hRT.trans hTS⟩
  · intro hCover
    exact hCover.mono_family minimalMembersIn_subset

/-- `pSmall` can be tested on the minimal members. -/
lemma pSmall_minimalMembersIn_iff
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} :
    pSmall X (minimalMembersIn X U) p ↔ pSmall X U p := by
  constructor
  · rintro ⟨G, hCover, hsum⟩
    exact ⟨G, CoversIn_minimalMembersIn_iff.mp hCover, hsum⟩
  · rintro ⟨G, hCover, hsum⟩
    exact ⟨G, CoversIn_minimalMembersIn_iff.mpr hCover, hsum⟩

/-- Non-smallness can be tested on minimal members. -/
lemma not_pSmall_minimalMembersIn_iff
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} :
    ¬ pSmall X (minimalMembersIn X U) p ↔ ¬ pSmall X U p := by
  rw [pSmall_minimalMembersIn_iff]

/-- The expectation-threshold upper-bound predicate can be tested on minimal
members. -/
lemma qSmallUpper_minimalMembersIn_iff
    {X : Finset α} {U : Finset (Finset α)} {q : ℝ} :
    qSmallUpper X (minimalMembersIn X U) q ↔ qSmallUpper X U q := by
  constructor
  · intro hSmall p hqp hp1 hSmallU
    exact hSmall p hqp hp1 (pSmall_minimalMembersIn_iff.mpr hSmallU)
  · intro hSmall p hqp hp1 hSmallMin
    exact hSmall p hqp hp1 (pSmall_minimalMembersIn_iff.mp hSmallMin)

/-- If the minimal-member cover has small enough total weight, then the family
is `p`-small. -/
lemma pSmall_of_minimalMembers_sum_le {X : Finset α} {U : Finset (Finset α)}
    {p : ℝ}
    (hsum : (∑ T ∈ minimalMembersIn X U, p ^ T.card) ≤ (1 / 2 : ℝ)) :
    pSmall X U p :=
  pSmall_of_cover_sum_le (minimalMembers_cover X U) hsum

/-- If a family is not `p`-small, then even its canonical minimal-member cover
has weight strictly larger than `1/2`. -/
lemma half_lt_minimalMembers_sum_of_not_pSmall
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X U p) :
    (1 / 2 : ℝ) < ∑ T ∈ minimalMembersIn X U, p ^ T.card := by
  exact lt_of_not_ge fun hle => h (pSmall_of_minimalMembers_sum_le hle)

/-- If an upper closure is not `p`-small, then the generator cover has weight
strictly larger than `1/2`. -/
lemma half_lt_generators_sum_of_not_pSmall_upClosureIn
    {X : Finset α} {A : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X (upClosureIn X A) p) :
    (1 / 2 : ℝ) < ∑ T ∈ A, p ^ T.card := by
  exact cover_sum_gt_half_of_not_pSmall h (generators_cover_upClosureIn X A)

omit [DecidableEq α] in
/-- If a finite weighted sum is larger than `1/2`, then some term is larger
than the average threshold `1 / (2 * card)`. -/
lemma exists_mem_weight_gt_inv_two_mul_card_of_half_lt_sum
    {β : Type*} (s : Finset β) (w : β → ℝ)
    (hsum : (1 / 2 : ℝ) < ∑ x ∈ s, w x) :
    ∃ x ∈ s, (1 : ℝ) / (2 * (s.card : ℝ)) < w x := by
  classical
  have hs_nonempty : s.Nonempty := by
    by_contra hs_empty
    have hs_eq : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs_empty
    have hbad : (1 / 2 : ℝ) < 0 := by simpa [hs_eq] using hsum
    norm_num at hbad
  by_contra hnone
  have hbound : ∀ x ∈ s, w x ≤ (1 : ℝ) / (2 * (s.card : ℝ)) := by
    intro x hx
    exact le_of_not_gt fun hxgt => hnone ⟨x, hx, hxgt⟩
  have hsum_le :
      (∑ x ∈ s, w x) ≤
        ∑ x ∈ s, (1 : ℝ) / (2 * (s.card : ℝ)) :=
    Finset.sum_le_sum hbound
  have hcard_pos_nat : 0 < s.card := hs_nonempty.card_pos
  have hcard_pos : 0 < (s.card : ℝ) := by exact_mod_cast hcard_pos_nat
  have hconst :
      (∑ x ∈ s, (1 : ℝ) / (2 * (s.card : ℝ))) = 1 / 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard_pos.ne']
  linarith

/-- If `U` is not `p`-small, then one minimal member has larger-than-average
`p`-weight in the canonical minimal cover. -/
lemma exists_minimalMember_weight_gt_inv_two_mul_card_of_not_pSmall
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X U p) :
    ∃ T ∈ minimalMembersIn X U,
      (1 : ℝ) / (2 * ((minimalMembersIn X U).card : ℝ)) < p ^ T.card :=
  exists_mem_weight_gt_inv_two_mul_card_of_half_lt_sum
    (minimalMembersIn X U) (fun T => p ^ T.card)
    (half_lt_minimalMembers_sum_of_not_pSmall h)

/-- If an upper closure is not `p`-small, then one generator has
larger-than-average `p`-weight in the generator cover. -/
lemma exists_generator_weight_gt_inv_two_mul_card_of_not_pSmall_upClosureIn
    {X : Finset α} {A : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X (upClosureIn X A) p) :
    ∃ T ∈ A, (1 : ℝ) / (2 * (A.card : ℝ)) < p ^ T.card :=
  exists_mem_weight_gt_inv_two_mul_card_of_half_lt_sum
    A (fun T => p ^ T.card)
    (half_lt_generators_sum_of_not_pSmall_upClosureIn h)

/-- If every minimal member has size at least `k`, then non-smallness forces
many minimal members at scale `p^k`. -/
lemma half_lt_minimalMembers_card_mul_pow_of_not_pSmall_card_ge
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} {k : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcard_ge : ∀ T ∈ minimalMembersIn X U, k ≤ T.card)
    (h : ¬ pSmall X U p) :
    (1 / 2 : ℝ) < ((minimalMembersIn X U).card : ℝ) * p ^ k := by
  have hsum_gt := half_lt_minimalMembers_sum_of_not_pSmall h
  have hterm : ∀ T ∈ minimalMembersIn X U, p ^ T.card ≤ p ^ k := by
    intro T hT
    exact pow_le_pow_of_le_one hp0 hp1 (hcard_ge T hT)
  have hsum_le :
      (∑ T ∈ minimalMembersIn X U, p ^ T.card) ≤
        ∑ T ∈ minimalMembersIn X U, p ^ k :=
    Finset.sum_le_sum hterm
  have hconst :
      (∑ T ∈ minimalMembersIn X U, p ^ k) =
        ((minimalMembersIn X U).card : ℝ) * p ^ k := by
    rw [Finset.sum_const, nsmul_eq_mul]
  linarith

/-- Rearranged form of
`half_lt_minimalMembers_card_mul_pow_of_not_pSmall_card_ge`. -/
lemma inv_two_mul_inv_pow_lt_minimalMembers_card_of_not_pSmall_card_ge
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} {k : ℕ}
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hcard_ge : ∀ T ∈ minimalMembersIn X U, k ≤ T.card)
    (h : ¬ pSmall X U p) :
    (1 : ℝ) / (2 * p ^ k) < ((minimalMembersIn X U).card : ℝ) := by
  have hhalf :
      (1 / 2 : ℝ) < ((minimalMembersIn X U).card : ℝ) * p ^ k :=
    half_lt_minimalMembers_card_mul_pow_of_not_pSmall_card_ge
      hp0.le hp1 hcard_ge h
  have hden : 0 < 2 * p ^ k := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith

/-- If `U` has neither `∅` nor singleton members, non-smallness forces many
minimal members at scale `p^2`. -/
lemma half_lt_minimalMembers_card_mul_sq_of_not_pSmall_no_singleton
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hEmpty : (∅ : Finset α) ∉ U)
    (hNoSingleton : ∀ a : α, ({a} : Finset α) ∉ U)
    (h : ¬ pSmall X U p) :
    (1 / 2 : ℝ) < ((minimalMembersIn X U).card : ℝ) * p ^ 2 :=
  half_lt_minimalMembers_card_mul_pow_of_not_pSmall_card_ge hp0 hp1
    (fun _T hT =>
      two_le_card_of_mem_minimalMembersIn_of_empty_not_mem_of_no_singleton
        hEmpty hNoSingleton hT)
    h

/-- Rearranged no-singleton minimal-cover lower bound. -/
lemma inv_two_mul_inv_sq_lt_minimalMembers_card_of_not_pSmall_no_singleton
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hEmpty : (∅ : Finset α) ∉ U)
    (hNoSingleton : ∀ a : α, ({a} : Finset α) ∉ U)
    (h : ¬ pSmall X U p) :
    (1 : ℝ) / (2 * p ^ 2) < ((minimalMembersIn X U).card : ℝ) :=
  inv_two_mul_inv_pow_lt_minimalMembers_card_of_not_pSmall_card_ge hp0 hp1
    (fun _T hT =>
      two_le_card_of_mem_minimalMembersIn_of_empty_not_mem_of_no_singleton
        hEmpty hNoSingleton hT)
    h

/-- In the nontrivial case `∅ ∉ U`, non-smallness implies that the number of
minimal members is large at scale `1 / p`. -/
lemma half_lt_minimalMembers_card_mul_of_not_pSmall_empty_not_mem
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hEmpty : (∅ : Finset α) ∉ U) (h : ¬ pSmall X U p) :
    (1 / 2 : ℝ) < ((minimalMembersIn X U).card : ℝ) * p := by
  have hsum_gt := half_lt_minimalMembers_sum_of_not_pSmall h
  have hterm : ∀ T ∈ minimalMembersIn X U, p ^ T.card ≤ p := by
    intro T hT
    have hT_nonempty : T.Nonempty :=
      nonempty_of_mem_minimalMembersIn_of_empty_not_mem hEmpty hT
    have hcard : 1 ≤ T.card := Finset.one_le_card.mpr hT_nonempty
    calc
      p ^ T.card ≤ p ^ 1 := pow_le_pow_of_le_one hp0 hp1 hcard
      _ = p := by simp
  have hsum_le :
      (∑ T ∈ minimalMembersIn X U, p ^ T.card) ≤
        ∑ T ∈ minimalMembersIn X U, p :=
    Finset.sum_le_sum hterm
  have hconst :
      (∑ T ∈ minimalMembersIn X U, p) =
        ((minimalMembersIn X U).card : ℝ) * p := by
    rw [Finset.sum_const, nsmul_eq_mul]
  linarith

/-- Rearranged cardinality lower bound from
`half_lt_minimalMembers_card_mul_of_not_pSmall_empty_not_mem`. -/
lemma inv_two_mul_inv_lt_minimalMembers_card_of_not_pSmall_empty_not_mem
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hEmpty : (∅ : Finset α) ∉ U) (h : ¬ pSmall X U p) :
    (1 : ℝ) / (2 * p) < ((minimalMembersIn X U).card : ℝ) := by
  have hhalf :
      (1 / 2 : ℝ) < ((minimalMembersIn X U).card : ℝ) * p :=
    half_lt_minimalMembers_card_mul_of_not_pSmall_empty_not_mem hp0.le hp1 hEmpty h
  have hden : 0 < 2 * p := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith

/-- A non-small family has at least one minimal member. -/
lemma minimalMembersIn_nonempty_of_not_pSmall
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X U p) :
    (minimalMembersIn X U).Nonempty :=
  minimalMembersIn_nonempty_of_nonempty (nonempty_of_not_pSmall h)

/-- Existential form of `minimalMembersIn_nonempty_of_not_pSmall`. -/
lemma exists_mem_minimalMembersIn_of_not_pSmall
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X U p) :
    ∃ S, S ∈ minimalMembersIn X U := by
  exact minimalMembersIn_nonempty_of_not_pSmall h

omit [DecidableEq α] in
/-- `pSmall` is monotone in `p`: if `U` is `p`-small and `0 ≤ p₀ ≤ p`,
then `U` is `p₀`-small (the same cover works). -/
lemma pSmall_mono_density {X : Finset α} {U : Finset (Finset α)}
    {p₀ p : ℝ} (h0 : 0 ≤ p₀) (hle : p₀ ≤ p)
    (hSmall : pSmall X U p) : pSmall X U p₀ := by
  classical
  rcases hSmall with ⟨G, hCover, hsum⟩
  refine ⟨G, hCover, le_trans ?_ hsum⟩
  refine Finset.sum_le_sum ?_
  intro T _
  exact pow_le_pow_left₀ h0 hle T.card

omit [DecidableEq α] in
/-- A subfamily of a `p`-small family is `p`-small. -/
lemma pSmall_mono_family {X : Finset α} {U V : Finset (Finset α)}
    {p : ℝ} (hUV : U ⊆ V) (hSmall : pSmall X V p) :
    pSmall X U p := by
  rcases hSmall with ⟨G, hCover, hsum⟩
  exact ⟨G, hCover.mono_family hUV, hsum⟩

omit [DecidableEq α] in
/-- Non-smallness is monotone upward in the family. -/
lemma not_pSmall_mono_family {X : Finset α} {U V : Finset (Finset α)}
    {p : ℝ} (hUV : U ⊆ V) (hNotSmall : ¬ pSmall X U p) :
    ¬ pSmall X V p := by
  intro hSmallV
  exact hNotSmall (pSmall_mono_family hUV hSmallV)

omit [DecidableEq α] in
/-- The `qSmallUpper` predicate is monotone upward in the family. -/
lemma qSmallUpper_mono_family {X : Finset α} {U V : Finset (Finset α)}
    {q : ℝ} (hUV : U ⊆ V) (hSmall : qSmallUpper X U q) :
    qSmallUpper X V q := by
  intro p hqp hp1 hSmallV
  exact hSmall p hqp hp1 (pSmall_mono_family hUV hSmallV)

omit [DecidableEq α] in
/-- If `U` is not `p`-small at `p = p₀`, then it is not `p`-small for any
`p > p₀` with `p ≤ 1`. This is the `qSmallUpper` form. -/
lemma qSmallUpper_of_not_pSmall {X : Finset α} {U : Finset (Finset α)}
    {p₀ : ℝ} (hp₀_nonneg : 0 ≤ p₀)
    (h : ¬ pSmall X U p₀) :
    qSmallUpper X U p₀ := by
  intro p hgt _ hSmall
  exact h (pSmall_mono_density hp₀_nonneg hgt.le hSmall)

/-- Finite union bound for sums over a `biUnion`, with nonnegative weights. -/
lemma sum_biUnion_le_sum_of_nonneg {ι β : Type*} [DecidableEq β]
    (s : Finset ι) (t : ι → Finset β) (w : β → ℝ)
    (hw : ∀ x, 0 ≤ w x) :
    (∑ x ∈ s.biUnion t, w x) ≤ ∑ i ∈ s, ∑ x ∈ t i, w x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    have hunion_le :
        (∑ x ∈ t a ∪ s.biUnion t, w x) ≤
          (∑ x ∈ t a, w x) + ∑ x ∈ s.biUnion t, w x := by
      let A : Finset β := t a
      let B : Finset β := s.biUnion t
      have hdisj : Disjoint A (B \ A) := by
        exact disjoint_sdiff
      have hAB : A ∪ B = A ∪ (B \ A) := by
        ext x
        by_cases hxA : x ∈ A <;> simp [A, B, hxA]
      calc
        (∑ x ∈ A ∪ B, w x)
            = ∑ x ∈ A ∪ (B \ A), w x := by rw [hAB]
        _ = (∑ x ∈ A, w x) + ∑ x ∈ B \ A, w x := by
          rw [Finset.sum_union hdisj]
        _ ≤ (∑ x ∈ A, w x) + ∑ x ∈ B, w x := by
          have hsdiff_le : (∑ x ∈ B \ A, w x) ≤ ∑ x ∈ B, w x :=
            Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.sdiff_subset : B \ A ⊆ B)
            (by intro x _ _; exact hw x)
          exact add_le_add_right hsdiff_le _
    calc
      (∑ x ∈ (insert a s).biUnion t, w x)
          = ∑ x ∈ t a ∪ s.biUnion t, w x := by simp
      _ ≤ (∑ x ∈ t a, w x) + ∑ x ∈ s.biUnion t, w x := hunion_le
      _ ≤ (∑ x ∈ t a, w x) + ∑ i ∈ s, ∑ x ∈ t i, w x := by
        gcongr
      _ = ∑ i ∈ insert a s, ∑ x ∈ t i, w x := by simp [has]

/-- If `G` covers `U`, then the Bernoulli mass of `U` is bounded by the
sum of the singleton-upclosure masses of the cover. -/
lemma muP_le_cover_sum {X : Finset α} {U G : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hCover : CoversIn X G U) :
    muP X U p ≤ ∑ T ∈ G.filter (fun T => T ⊆ X), p ^ T.card := by
  classical
  let Gx : Finset (Finset α) := G.filter fun T => T ⊆ X
  let B : Finset α → Finset (Finset α) := fun T =>
    X.powerset.filter fun S => T ⊆ S
  have hsubset :
      X.powerset.filter (fun S => S ∈ U) ⊆ Gx.biUnion B := by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSXpow, hSU⟩
    have hSX : S ⊆ X := Finset.mem_powerset.mp hSXpow
    rcases hCover S hSU with ⟨T, hTG, hTS⟩
    have hTX : T ⊆ X := hTS.trans hSX
    exact Finset.mem_biUnion.mpr
      ⟨T, Finset.mem_filter.mpr ⟨hTG, hTX⟩,
        Finset.mem_filter.mpr ⟨hSXpow, hTS⟩⟩
  have hnonneg : ∀ S, 0 ≤ bernoulliMass X S p := fun _ =>
    bernoulliMass_nonneg h0 h1
  calc
    muP X U p
        = ∑ S ∈ X.powerset.filter (fun S => S ∈ U), bernoulliMass X S p := rfl
    _ ≤ ∑ S ∈ Gx.biUnion B, bernoulliMass X S p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (by intro S _ _; exact hnonneg S)
    _ ≤ ∑ T ∈ Gx, ∑ S ∈ B T, bernoulliMass X S p :=
      sum_biUnion_le_sum_of_nonneg Gx B (fun S => bernoulliMass X S p) hnonneg
    _ = ∑ T ∈ Gx, p ^ T.card := by
      refine Finset.sum_congr rfl ?_
      intro T hTGx
      have hTX : T ⊆ X := (Finset.mem_filter.mp hTGx).2
      have hB_eq : B T = upClosureIn X {T} := by
        rw [upClosureIn_singleton X T hTX]
      have hmuB :
          muP X (B T) p = ∑ S ∈ B T, bernoulliMass X S p := by
        unfold muP
        have hfilter : X.powerset.filter (fun S => S ∈ B T) = B T := by
          ext S
          simp [B]
        rw [hfilter]
      have hsingleB : muP X (B T) p = p ^ T.card := by
        rw [hB_eq]
        exact muP_upClosure_single X T hTX h0 h1
      exact hmuB.symm.trans hsingleB

/-- Union-bound direction of the expectation-threshold setup: a `p`-small
family has Bernoulli measure at most `1/2` at density `p`. -/
theorem muP_le_half_of_pSmall {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hSmall : pSmall X U p) :
    muP X U p ≤ 1 / 2 := by
  classical
  rcases hSmall with ⟨G, hCover, hsum⟩
  have hcover := muP_le_cover_sum h0 h1 hCover
  have hfilter :
      (∑ T ∈ G.filter (fun T => T ⊆ X), p ^ T.card) ≤
        ∑ T ∈ G, p ^ T.card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intro T _ _; exact pow_nonneg h0 T.card)
  exact hcover.trans (hfilter.trans hsum)

/-- Contrapositive of `muP_le_half_of_pSmall`: if the Bernoulli measure is
strictly larger than `1/2`, the family is not `p`-small. -/
lemma not_pSmall_of_muP_gt_half {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hmu : 1 / 2 < muP X U p) :
    ¬ pSmall X U p := by
  intro hSmall
  exact not_le_of_gt hmu (muP_le_half_of_pSmall h0 h1 hSmall)

/-- A measure-lower-bound way to establish `qSmallUpper`: if every density
above `q` has Bernoulli measure strictly larger than `1/2`, then no such
density can be `p`-small. -/
lemma qSmallUpper_of_forall_muP_gt_half
    {X : Finset α} {U : Finset (Finset α)} {q : ℝ}
    (hq0 : 0 ≤ q)
    (hmu : ∀ p : ℝ, q < p → p ≤ 1 → 1 / 2 < muP X U p) :
    qSmallUpper X U q := by
  intro p hqp hp1
  have hp0 : 0 ≤ p := hq0.trans hqp.le
  exact not_pSmall_of_muP_gt_half hp0 hp1 (hmu p hqp hp1)

end

end ParkPham
end Erdos202


/-! =============================================================
    Section from: Erdos/P202/ParkPham/Fragments.lean
    ============================================================= -/

/-
Erdos Problem 202 — Park–Pham layer, fragment infrastructure.

This file starts the source-aligned formalization of the Park--Pham /
Kahn--Kalai expectation-threshold proof.  The "simple proof" route of
Park--Vondrak works with fragments

  F(H, W) = {S \ W | S in H}

and their inclusion-minimal members, then splits those minimal fragments into
large and small parts at a cardinality cutoff.  The deep probabilistic cost
lemma is not proved here; this file only provides the finite set-system
bookkeeping needed to state it cleanly.
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- Fragment family `F(H,W) = {S \ W | S in H}`. -/
def fragmentFamily (H : Finset (Finset α)) (W : Finset α) :
    Finset (Finset α) :=
  H.image fun S => S \ W

@[simp]
lemma mem_fragmentFamily {H : Finset (Finset α)} {W T : Finset α} :
    T ∈ fragmentFamily H W ↔ ∃ S ∈ H, S \ W = T := by
  simp [fragmentFamily]

/-- Minimal fragments `F*(H,W)`: inclusion-minimal members of
`fragmentFamily H W`.  The ground-set argument of `minimalMembersIn` is
irrelevant for minimality, so we use `∅`. -/
def minimalFragments (H : Finset (Finset α)) (W : Finset α) :
    Finset (Finset α) :=
  minimalMembersIn (∅ : Finset α) (fragmentFamily H W)

@[simp]
lemma mem_minimalFragments {H : Finset (Finset α)} {W T : Finset α} :
    T ∈ minimalFragments H W ↔
      T ∈ fragmentFamily H W ∧
        ∀ R ∈ fragmentFamily H W, ¬ R ⊂ T := by
  simp [minimalFragments]

lemma minimalFragments_subset_fragmentFamily
    (H : Finset (Finset α)) (W : Finset α) :
    minimalFragments H W ⊆ fragmentFamily H W :=
  minimalMembersIn_subset

lemma fragmentFamily_card_le_card
    (H : Finset (Finset α)) (W : Finset α) :
    (fragmentFamily H W).card ≤ H.card := by
  rw [fragmentFamily]
  exact Finset.card_image_le

lemma minimalFragments_card_le_card
    (H : Finset (Finset α)) (W : Finset α) :
    (minimalFragments H W).card ≤ H.card :=
  (Finset.card_le_card (minimalFragments_subset_fragmentFamily H W)).trans
    (fragmentFamily_card_le_card H W)

lemma fragment_disjoint_exposure
    {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ fragmentFamily H W) :
    Disjoint T W := by
  rcases mem_fragmentFamily.mp hT with ⟨S, _hS, rfl⟩
  rw [Finset.disjoint_left]
  intro x hx hW
  exact (Finset.mem_sdiff.mp hx).2 hW

lemma minimalFragment_disjoint_exposure
    {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ minimalFragments H W) :
    Disjoint T W :=
  fragment_disjoint_exposure (minimalFragments_subset_fragmentFamily H W hT)

/-- Large minimal fragments: those of cardinality at least `m`. -/
def largeMinimalFragments (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    Finset (Finset α) :=
  (minimalFragments H W).filter fun T => m ≤ T.card

/-- Small minimal fragments: those of cardinality strictly below `m`. -/
def smallMinimalFragments (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    Finset (Finset α) :=
  (minimalFragments H W).filter fun T => T.card < m

lemma largeMinimalFragments_card_le_card
    (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    (largeMinimalFragments m H W).card ≤ H.card :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (minimalFragments_card_le_card H W)

lemma smallMinimalFragments_card_le_card
    (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    (smallMinimalFragments m H W).card ≤ H.card :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (minimalFragments_card_le_card H W)

@[simp]
lemma mem_largeMinimalFragments {m : ℕ} {H : Finset (Finset α)}
    {W T : Finset α} :
    T ∈ largeMinimalFragments m H W ↔
      T ∈ minimalFragments H W ∧ m ≤ T.card := by
  simp [largeMinimalFragments]

lemma largeMinimalFragment_disjoint_exposure
    {m : ℕ} {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ largeMinimalFragments m H W) :
    Disjoint T W :=
  minimalFragment_disjoint_exposure (mem_largeMinimalFragments.mp hT).1

lemma union_sdiff_right_eq_left_of_disjoint
    {W S : Finset α} (hdisj : Disjoint S W) :
    (W ∪ S) \ S = W := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxWS, hxSnot⟩
    rcases Finset.mem_union.mp hxWS with hxW | hxS
    · exact hxW
    · exact False.elim (hxSnot hxS)
  · intro hxW
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_union.mpr (Or.inl hxW),
        fun hxS => (Finset.disjoint_left.mp hdisj) hxS hxW⟩

@[simp]
lemma mem_smallMinimalFragments {m : ℕ} {H : Finset (Finset α)}
    {W T : Finset α} :
    T ∈ smallMinimalFragments m H W ↔
      T ∈ minimalFragments H W ∧ T.card < m := by
  simp [smallMinimalFragments]

/-- The large/small split partitions the minimal fragments. -/
lemma small_union_large_minimalFragments
    (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    smallMinimalFragments m H W ∪ largeMinimalFragments m H W =
      minimalFragments H W := by
  ext T
  by_cases hT : T ∈ minimalFragments H W
  · by_cases hsmall : T.card < m
    · simp [hT, hsmall, largeMinimalFragments, smallMinimalFragments,
        not_le.mpr hsmall]
    · have hlarge : m ≤ T.card := le_of_not_gt hsmall
      simp [hT, hlarge, hsmall, largeMinimalFragments, smallMinimalFragments]
  · simp [hT, largeMinimalFragments, smallMinimalFragments]

/-- The large and small minimal-fragment parts are disjoint. -/
lemma disjoint_small_large_minimalFragments
    (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    Disjoint (smallMinimalFragments m H W) (largeMinimalFragments m H W) := by
  rw [Finset.disjoint_left]
  intro T hsmall hlarge
  rcases mem_smallMinimalFragments.mp hsmall with ⟨_, hlt⟩
  rcases mem_largeMinimalFragments.mp hlarge with ⟨_, hle⟩
  exact not_lt_of_ge hle hlt

/-- Fragments inherit any cardinality upper bound on the source family. -/
lemma fragmentFamily_card_le_of_forall_card_le
    {H : Finset (Finset α)} {W T : Finset α} {ℓ : ℕ}
    (hH : ∀ S ∈ H, S.card ≤ ℓ)
    (hT : T ∈ fragmentFamily H W) :
    T.card ≤ ℓ := by
  rcases mem_fragmentFamily.mp hT with ⟨S, hS, rfl⟩
  have hsub : S \ W ⊆ S := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  exact (Finset.card_le_card hsub).trans (hH S hS)

/-- Minimal fragments inherit any cardinality upper bound on the source
family. -/
lemma minimalFragments_card_le_of_forall_card_le
    {H : Finset (Finset α)} {W T : Finset α} {ℓ : ℕ}
    (hH : ∀ S ∈ H, S.card ≤ ℓ)
    (hT : T ∈ minimalFragments H W) :
    T.card ≤ ℓ :=
  fragmentFamily_card_le_of_forall_card_le hH
    (minimalFragments_subset_fragmentFamily H W hT)

/-- Minimal fragments are a canonical cover of the fragment family. -/
lemma minimalFragments_cover
    (X : Finset α) (H : Finset (Finset α)) (W : Finset α) :
    CoversIn X (minimalFragments H W) (fragmentFamily H W) := by
  simpa [minimalFragments] using
    (minimalMembers_cover (X := (∅ : Finset α)) (U := fragmentFamily H W))

/-- If a family covers all minimal fragments, then it covers the original
family.  This is the finite covering step used in the Park--Vondrak proof when
passing from `F*(H,W)` back to `H`. -/
lemma CoversIn.of_minimalFragments
    {X : Finset α} {G H : Finset (Finset α)} {W : Finset α}
    (hCover : CoversIn X G (minimalFragments H W)) :
    CoversIn X G H := by
  intro S hS
  have hfrag : S \ W ∈ fragmentFamily H W :=
    mem_fragmentFamily.mpr ⟨S, hS, rfl⟩
  rcases minimalFragments_cover X H W (S \ W) hfrag with
    ⟨R, hRmin, hRsub⟩
  rcases hCover R hRmin with ⟨T, hTG, hTR⟩
  have hsdiff_sub : S \ W ⊆ S := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  exact ⟨T, hTG, hTR.trans (hRsub.trans hsdiff_sub)⟩

lemma sdiff_eq_empty_iff_subset {S W : Finset α} :
    S \ W = ∅ ↔ S ⊆ W := by
  constructor
  · intro h x hxS
    by_contra hxW
    have hx : x ∈ S \ W := Finset.mem_sdiff.mpr ⟨hxS, hxW⟩
    simp [h] at hx
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (Finset.mem_sdiff.mp hx).2 (h (Finset.mem_sdiff.mp hx).1)

/-- The empty set is a fragment exactly when some source member is contained in
`W`. -/
lemma empty_mem_fragmentFamily_iff
    {H : Finset (Finset α)} {W : Finset α} :
    (∅ : Finset α) ∈ fragmentFamily H W ↔ ∃ S ∈ H, S ⊆ W := by
  constructor
  · intro h
    rcases mem_fragmentFamily.mp h with ⟨S, hS, hdiff⟩
    exact ⟨S, hS, sdiff_eq_empty_iff_subset.mp hdiff⟩
  · rintro ⟨S, hS, hSW⟩
    exact mem_fragmentFamily.mpr ⟨S, hS, sdiff_eq_empty_iff_subset.mpr hSW⟩

lemma subset_union_of_sdiff_subset
    {S W V : Finset α} (h : S \ W ⊆ V) :
    S ⊆ W ∪ V := by
  intro x hxS
  by_cases hxW : x ∈ W
  · exact Finset.mem_union.mpr (Or.inl hxW)
  · exact Finset.mem_union.mpr
      (Or.inr (h (Finset.mem_sdiff.mpr ⟨hxS, hxW⟩)))

lemma sdiff_subset_of_subset_union
    {S W V : Finset α} (h : S ⊆ W ∪ V) :
    S \ W ⊆ V := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxS, hxW_not⟩
  rcases Finset.mem_union.mp (h hxS) with hxW | hxV
  · exact False.elim (hxW_not hxW)
  · exact hxV

lemma exists_source_subset_union_of_minimalFragment_subset
    {H : Finset (Finset α)} {W V : Finset α}
    (h : ∃ R ∈ minimalFragments H W, R ⊆ V) :
    ∃ S ∈ H, S ⊆ W ∪ V := by
  rcases h with ⟨R, hR, hRV⟩
  have hRfrag : R ∈ fragmentFamily H W :=
    minimalFragments_subset_fragmentFamily H W hR
  rcases mem_fragmentFamily.mp hRfrag with ⟨S, hS, hSR⟩
  refine ⟨S, hS, subset_union_of_sdiff_subset ?_⟩
  intro x hx
  exact hRV (by simpa [hSR] using hx)

lemma exists_minimalFragment_subset_of_source_subset_union
    {H : Finset (Finset α)} {W V : Finset α}
    (h : ∃ S ∈ H, S ⊆ W ∪ V) :
    ∃ R ∈ minimalFragments H W, R ⊆ V := by
  rcases h with ⟨S, hS, hSWV⟩
  have hfrag : S \ W ∈ fragmentFamily H W :=
    mem_fragmentFamily.mpr ⟨S, hS, rfl⟩
  rcases minimalFragments_cover (∅ : Finset α) H W (S \ W) hfrag with
    ⟨R, hR, hRsub⟩
  exact ⟨R, hR, hRsub.trans (sdiff_subset_of_subset_union hSWV)⟩

lemma exists_minimalFragment_subset_iff_source_subset_union
    {H : Finset (Finset α)} {W V : Finset α} :
    (∃ R ∈ minimalFragments H W, R ⊆ V) ↔
      ∃ S ∈ H, S ⊆ W ∪ V := by
  constructor
  · exact exists_source_subset_union_of_minimalFragment_subset
  · exact exists_minimalFragment_subset_of_source_subset_union

/-- Park--Pham/Park--Vondrak containment trick.  If `T ∈ H` is contained in
`Z`, then every minimal fragment `S ∈ F*(H, Z \ S)` with `S ⊆ Z` is contained
in `T`.  Otherwise the smaller set `T \ (Z \ S)` would be a fragment properly
contained in `S`. -/
lemma minimalFragment_subset_of_source_subset
    {H : Finset (Finset α)} {Z S T : Finset α}
    (hT : T ∈ H) (hTZ : T ⊆ Z)
    (hSmin : S ∈ minimalFragments H (Z \ S)) :
    S ⊆ T := by
  by_contra hnot
  have hRfrag : T \ (Z \ S) ∈ fragmentFamily H (Z \ S) :=
    mem_fragmentFamily.mpr ⟨T, hT, rfl⟩
  have hRsub : T \ (Z \ S) ⊆ S := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxNot⟩
    by_contra hxS
    exact hxNot (Finset.mem_sdiff.mpr ⟨hTZ hxT, hxS⟩)
  have hproper : T \ (Z \ S) ⊂ S := by
    refine hRsub.ssubset_of_ne ?_
    intro hEq
    have hST : S ⊆ T := by
      intro x hxS
      have hxR : x ∈ T \ (Z \ S) := by
        simpa [hEq] using hxS
      exact (Finset.mem_sdiff.mp hxR).1
    exact hnot hST
  exact (mem_minimalFragments.mp hSmin).2 (T \ (Z \ S)) hRfrag hproper

lemma largeMinimalFragment_subset_of_source_subset
    {H : Finset (Finset α)} {Z S T : Finset α} {m : ℕ}
    (hT : T ∈ H) (hTZ : T ⊆ Z)
    (hS : S ∈ largeMinimalFragments m H (Z \ S)) :
    S ⊆ T :=
  minimalFragment_subset_of_source_subset hT hTZ
    (mem_largeMinimalFragments.mp hS).1

lemma largeMinimalFragment_subset_ground
    {X : Finset α} {H : Finset (Finset α)} {W S : Finset α} {m : ℕ}
    (hHX : ∀ T ∈ H, T ⊆ X)
    (hS : S ∈ largeMinimalFragments m H W) :
    S ⊆ X := by
  have hSfrag : S ∈ fragmentFamily H W :=
    minimalFragments_subset_fragmentFamily H W
      (mem_largeMinimalFragments.mp hS).1
  rcases mem_fragmentFamily.mp hSfrag with ⟨T, hT, rfl⟩
  exact (Finset.sdiff_subset : T \ W ⊆ T).trans (hHX T hT)

/-- Inner witness set in the Park--Pham/Park--Vondrak double-counting
argument: subsets `S ⊆ Z` that are large minimal fragments after exposing
`Z \ S`. -/
def largeFragmentWitnesses
    (H : Finset (Finset α)) (m : ℕ) (Z : Finset α) :
    Finset (Finset α) :=
  Z.powerset.filter fun S => S ∈ largeMinimalFragments m H (Z \ S)

@[simp]
lemma mem_largeFragmentWitnesses
    {H : Finset (Finset α)} {m : ℕ} {Z S : Finset α} :
    S ∈ largeFragmentWitnesses H m Z ↔
      S ⊆ Z ∧ S ∈ largeMinimalFragments m H (Z \ S) := by
  simp [largeFragmentWitnesses]

lemma largeMinimalFragment_mem_witnesses_union
    {m : ℕ} {H : Finset (Finset α)} {W S : Finset α}
    (hS : S ∈ largeMinimalFragments m H W) :
    S ∈ largeFragmentWitnesses H m (W ∪ S) := by
  have hdisj : Disjoint S W := largeMinimalFragment_disjoint_exposure hS
  have hsdiff : (W ∪ S) \ S = W :=
    union_sdiff_right_eq_left_of_disjoint hdisj
  rw [mem_largeFragmentWitnesses]
  constructor
  · exact Finset.subset_union_right
  · simpa [hsdiff] using hS

lemma largeFragmentWitnesses_subset_source_powerset_filter
    {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α}
    (hT : T ∈ H) (hTZ : T ⊆ Z) :
    largeFragmentWitnesses H m Z ⊆
      T.powerset.filter fun S => m ≤ S.card := by
  intro S hS
  rcases mem_largeFragmentWitnesses.mp hS with ⟨_hSZ, hSlarge⟩
  have hST : S ⊆ T :=
    largeMinimalFragment_subset_of_source_subset hT hTZ hSlarge
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hST, (mem_largeMinimalFragments.mp hSlarge).2⟩

lemma largeFragmentWitnesses_card_le_source
    {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α}
    (hT : T ∈ H) (hTZ : T ⊆ Z) :
    (largeFragmentWitnesses H m Z).card ≤
      (T.powerset.filter fun S => m ≤ S.card).card :=
  Finset.card_le_card
    (largeFragmentWitnesses_subset_source_powerset_filter hT hTZ)

lemma exists_source_subset_of_largeFragmentWitness
    {H : Finset (Finset α)} {m : ℕ} {Z S : Finset α}
    (hS : S ∈ largeFragmentWitnesses H m Z) :
    ∃ T ∈ H, T ⊆ Z := by
  rcases mem_largeFragmentWitnesses.mp hS with ⟨hSZ, hSlarge⟩
  have hSfrag : S ∈ fragmentFamily H (Z \ S) :=
    minimalFragments_subset_fragmentFamily H (Z \ S)
      (mem_largeMinimalFragments.mp hSlarge).1
  rcases mem_fragmentFamily.mp hSfrag with ⟨T, hT, hdiff⟩
  refine ⟨T, hT, ?_⟩
  intro x hxT
  by_contra hxZ
  have hxNot : x ∉ Z \ S := by
    intro hx
    exact hxZ (Finset.mem_sdiff.mp hx).1
  have hxS : x ∈ S := by
    have hx : x ∈ T \ (Z \ S) :=
      Finset.mem_sdiff.mpr ⟨hxT, hxNot⟩
    simpa [hdiff] using hx
  exact hxZ (hSZ hxS)

lemma largeFragmentWitnesses_eq_empty_of_no_source_subset
    {H : Finset (Finset α)} {m : ℕ} {Z : Finset α}
    (hno : ¬ ∃ T ∈ H, T ⊆ Z) :
    largeFragmentWitnesses H m Z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  exact hno (exists_source_subset_of_largeFragmentWitness hS)

lemma sum_largeFragmentWitnesses_le_source_sum
    {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α}
    (w : Finset α → ℝ) (hw : ∀ S, 0 ≤ w S)
    (hT : T ∈ H) (hTZ : T ⊆ Z) :
    (∑ S ∈ largeFragmentWitnesses H m Z, w S) ≤
      ∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), w S :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (largeFragmentWitnesses_subset_source_powerset_filter hT hTZ)
    (by intro S _ _; exact hw S)

omit [DecidableEq α] in
lemma sum_powerset_filter_pow_card_le_card_mul_pow
    (T : Finset α) (m : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card) ≤
      (((T.powerset.filter fun S => m ≤ S.card).card : ℝ) * a ^ m) := by
  calc
    (∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card)
        ≤ ∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ m := by
          refine Finset.sum_le_sum ?_
          intro S hS
          exact pow_le_pow_of_le_one ha0 ha1 (Finset.mem_filter.mp hS).2
    _ = (((T.powerset.filter fun S => m ≤ S.card).card : ℝ) * a ^ m) := by
          rw [Finset.sum_const, nsmul_eq_mul]

omit [DecidableEq α] in
lemma sum_powerset_filter_pow_card_le_two_pow_mul_pow
    (T : Finset α) (m : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card) ≤
      (2 : ℝ) ^ T.card * a ^ m := by
  have hsum :=
    sum_powerset_filter_pow_card_le_card_mul_pow T m ha0 ha1
  have hcard_nat :
      (T.powerset.filter fun S => m ≤ S.card).card ≤ T.powerset.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hcard_real :
      (((T.powerset.filter fun S => m ≤ S.card).card : ℝ)) ≤
        (2 : ℝ) ^ T.card := by
    have hcast : (((T.powerset.filter fun S => m ≤ S.card).card : ℝ)) ≤
        (T.powerset.card : ℝ) := by
      exact_mod_cast hcard_nat
    simpa using hcast
  have hmul :
      (((T.powerset.filter fun S => m ≤ S.card).card : ℝ) * a ^ m) ≤
        (2 : ℝ) ^ T.card * a ^ m :=
    mul_le_mul_of_nonneg_right hcard_real (pow_nonneg ha0 m)
  exact hsum.trans hmul

lemma sum_largeFragmentWitnesses_pow_le_two_pow_mul_pow
    {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : T ∈ H) (hTZ : T ⊆ Z) :
    (∑ S ∈ largeFragmentWitnesses H m Z, a ^ S.card) ≤
      (2 : ℝ) ^ T.card * a ^ m := by
  have hle_source :
      (∑ S ∈ largeFragmentWitnesses H m Z, a ^ S.card) ≤
        ∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card :=
    sum_largeFragmentWitnesses_le_source_sum
      (fun S => a ^ S.card) (fun S => pow_nonneg ha0 S.card) hT hTZ
  exact hle_source.trans
    (sum_powerset_filter_pow_card_le_two_pow_mul_pow T m ha0 ha1)

/-- Pairs `(W,S)` with `W ⊆ X` and `S` a large minimal fragment after
exposing `W`. -/
def largeFragmentPairs
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ) :
    Finset (Finset α × Finset α) :=
  X.powerset.biUnion fun W =>
    (largeMinimalFragments m H W).image fun S => (W, S)

lemma disjoint_largeFragmentPair_fibers
    {H : Finset (Finset α)} {m : ℕ} {W W' : Finset α}
    (hWW' : W ≠ W') :
    Disjoint
      ((largeMinimalFragments m H W).image fun S => (W, S))
      ((largeMinimalFragments m H W').image fun S => (W', S)) := by
  rw [Finset.disjoint_left]
  intro P hP hP'
  rcases Finset.mem_image.mp hP with ⟨S, _hS, hEq⟩
  rcases Finset.mem_image.mp hP' with ⟨S', _hS', hEq'⟩
  have hfirst : W = W' := by
    calc
      W = (W, S).1 := rfl
      _ = P.1 := congrArg Prod.fst hEq
      _ = (W', S').1 := (congrArg Prod.fst hEq').symm
      _ = W' := rfl
  exact hWW' hfirst

lemma pairwiseDisjoint_largeFragmentPair_fibers
    (H : Finset (Finset α)) (m : ℕ) :
    (X : Finset (Finset α)) →
      ∀ W ∈ X, ∀ W' ∈ X, W ≠ W' →
        Disjoint
          ((largeMinimalFragments m H W).image fun S => (W, S))
          ((largeMinimalFragments m H W').image fun S => (W', S)) :=
  fun _ W _ W' _ hWW' =>
    disjoint_largeFragmentPair_fibers (H := H) (m := m) (W := W) (W' := W') hWW'

@[simp]
lemma mem_largeFragmentPairs
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    {P : Finset α × Finset α} :
    P ∈ largeFragmentPairs X H m ↔
      P.1 ⊆ X ∧ P.2 ∈ largeMinimalFragments m H P.1 := by
  constructor
  · intro hP
    rcases Finset.mem_biUnion.mp hP with ⟨W, hWXpow, hPimg⟩
    rcases Finset.mem_image.mp hPimg with ⟨S, hS, hEq⟩
    have hP1 : P.1 = W := (congrArg Prod.fst hEq).symm
    have hP2 : P.2 = S := (congrArg Prod.snd hEq).symm
    exact ⟨by simpa [hP1] using Finset.mem_powerset.mp hWXpow,
      by simpa [hP1, hP2] using hS⟩
  · intro h
    rcases P with ⟨W, S⟩
    exact Finset.mem_biUnion.mpr
      ⟨W, Finset.mem_powerset.mpr h.1,
        Finset.mem_image.mpr ⟨S, h.2, rfl⟩⟩

/-- Pairs `(Z,S)` where `S` is a large-fragment witness inside `Z`. -/
def largeWitnessPairs
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ) :
    Finset (Finset α × Finset α) :=
  X.powerset.biUnion fun Z =>
    (largeFragmentWitnesses H m Z).image fun S => (Z, S)

lemma disjoint_largeWitnessPair_fibers
    {H : Finset (Finset α)} {m : ℕ} {Z Z' : Finset α}
    (hZZ' : Z ≠ Z') :
    Disjoint
      ((largeFragmentWitnesses H m Z).image fun S => (Z, S))
      ((largeFragmentWitnesses H m Z').image fun S => (Z', S)) := by
  rw [Finset.disjoint_left]
  intro P hP hP'
  rcases Finset.mem_image.mp hP with ⟨S, _hS, hEq⟩
  rcases Finset.mem_image.mp hP' with ⟨S', _hS', hEq'⟩
  have hfirst : Z = Z' := by
    calc
      Z = (Z, S).1 := rfl
      _ = P.1 := congrArg Prod.fst hEq
      _ = (Z', S').1 := (congrArg Prod.fst hEq').symm
      _ = Z' := rfl
  exact hZZ' hfirst

lemma pairwiseDisjoint_largeWitnessPair_fibers
    (H : Finset (Finset α)) (m : ℕ) :
    (X : Finset (Finset α)) →
      ∀ Z ∈ X, ∀ Z' ∈ X, Z ≠ Z' →
        Disjoint
          ((largeFragmentWitnesses H m Z).image fun S => (Z, S))
          ((largeFragmentWitnesses H m Z').image fun S => (Z', S)) :=
  fun _ Z _ Z' _ hZZ' =>
    disjoint_largeWitnessPair_fibers (H := H) (m := m) (Z := Z) (Z' := Z') hZZ'

@[simp]
lemma mem_largeWitnessPairs
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    {P : Finset α × Finset α} :
    P ∈ largeWitnessPairs X H m ↔
      P.1 ⊆ X ∧ P.2 ∈ largeFragmentWitnesses H m P.1 := by
  constructor
  · intro hP
    rcases Finset.mem_biUnion.mp hP with ⟨Z, hZXpow, hPimg⟩
    rcases Finset.mem_image.mp hPimg with ⟨S, hS, hEq⟩
    have hP1 : P.1 = Z := (congrArg Prod.fst hEq).symm
    have hP2 : P.2 = S := (congrArg Prod.snd hEq).symm
    exact ⟨by simpa [hP1] using Finset.mem_powerset.mp hZXpow,
      by simpa [hP1, hP2] using hS⟩
  · intro h
    rcases P with ⟨Z, S⟩
    exact Finset.mem_biUnion.mpr
      ⟨Z, Finset.mem_powerset.mpr h.1,
        Finset.mem_image.mpr ⟨S, h.2, rfl⟩⟩

def largeFragmentPairToWitness
    (P : Finset α × Finset α) : Finset α × Finset α :=
  (P.1 ∪ P.2, P.2)

lemma largeFragmentPairToWitness_mem
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    (hHX : ∀ T ∈ H, T ⊆ X)
    {P : Finset α × Finset α}
    (hP : P ∈ largeFragmentPairs X H m) :
    largeFragmentPairToWitness P ∈ largeWitnessPairs X H m := by
  rcases P with ⟨W, S⟩
  rcases mem_largeFragmentPairs.mp hP with ⟨hWX, hS⟩
  rw [mem_largeWitnessPairs]
  constructor
  · exact Finset.union_subset hWX (largeMinimalFragment_subset_ground hHX hS)
  · exact largeMinimalFragment_mem_witnesses_union hS

lemma largeFragmentPairToWitness_injOn
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ} :
    Set.InjOn (largeFragmentPairToWitness : Finset α × Finset α → Finset α × Finset α)
      (↑(largeFragmentPairs X H m)) := by
  intro P hP Q hQ hEq
  rcases P with ⟨W, S⟩
  rcases Q with ⟨W', S'⟩
  have hS_eq : S = S' := by
    exact congrArg Prod.snd hEq
  have hUnion_eq : W ∪ S = W' ∪ S' := by
    exact congrArg Prod.fst hEq
  rcases mem_largeFragmentPairs.mp hP with ⟨_hWX, hSlarge⟩
  rcases mem_largeFragmentPairs.mp hQ with ⟨_hW'X, hS'large⟩
  have hW_eq : W = W' := by
    have hleft :
        (W ∪ S) \ S = W :=
      union_sdiff_right_eq_left_of_disjoint
        (largeMinimalFragment_disjoint_exposure hSlarge)
    have hright :
        (W' ∪ S') \ S' = W' :=
      union_sdiff_right_eq_left_of_disjoint
        (largeMinimalFragment_disjoint_exposure hS'large)
    calc
      W = (W ∪ S) \ S := hleft.symm
      _ = (W' ∪ S') \ S' := by rw [hUnion_eq, hS_eq]
      _ = W' := hright
  simp [hW_eq, hS_eq]

lemma image_largeFragmentPairToWitness_subset
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    (hHX : ∀ T ∈ H, T ⊆ X) :
    (largeFragmentPairs X H m).image largeFragmentPairToWitness ⊆
      largeWitnessPairs X H m := by
  intro Q hQ
  rcases Finset.mem_image.mp hQ with ⟨P, hP, rfl⟩
  exact largeFragmentPairToWitness_mem hHX hP

lemma sum_largeFragmentPairs_toWitness_le_sum_witnessPairs
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    (hHX : ∀ T ∈ H, T ⊆ X)
    (w : Finset α × Finset α → ℝ)
    (hw : ∀ P, 0 ≤ w P) :
    (∑ P ∈ largeFragmentPairs X H m, w (largeFragmentPairToWitness P)) ≤
      ∑ Q ∈ largeWitnessPairs X H m, w Q := by
  have himage_subset := image_largeFragmentPairToWitness_subset
    (X := X) (H := H) (m := m) hHX
  calc
    (∑ P ∈ largeFragmentPairs X H m, w (largeFragmentPairToWitness P))
        = ∑ Q ∈ (largeFragmentPairs X H m).image largeFragmentPairToWitness, w Q := by
          rw [Finset.sum_image (largeFragmentPairToWitness_injOn
            (X := X) (H := H) (m := m))]
    _ ≤ ∑ Q ∈ largeWitnessPairs X H m, w Q :=
        Finset.sum_le_sum_of_subset_of_nonneg himage_subset
          (by intro Q _ _; exact hw Q)

/-- Union of a finite list of exposure sets. -/
def exposureUnion : List (Finset α) → Finset α
  | [] => ∅
  | W :: Ws => W ∪ exposureUnion Ws

lemma exposureUnion_subset
    {Ws : List (Finset α)} {X : Finset α}
    (hWs : ∀ W ∈ Ws, W ⊆ X) :
    exposureUnion Ws ⊆ X := by
  induction Ws with
  | nil =>
      simp [exposureUnion]
  | cons W Ws ih =>
      intro x hx
      rcases Finset.mem_union.mp (by simpa [exposureUnion] using hx) with hxW | hxRest
      · exact hWs W (by simp) hxW
      · exact ih (by
          intro V hV
          exact hWs V (by simp [hV])) hxRest

lemma exposureUnion_union_subset
    {Ws : List (Finset α)} {V X : Finset α}
    (hWs : ∀ W ∈ Ws, W ⊆ X) (hV : V ⊆ X) :
    exposureUnion Ws ∪ V ⊆ X :=
  Finset.union_subset (exposureUnion_subset hWs) hV

/-- Iterated minimal-fragment family after exposing a finite list of sets. -/
def iteratedMinimalFragments (H : Finset (Finset α)) :
    List (Finset α) → Finset (Finset α)
  | [] => H
  | W :: Ws => iteratedMinimalFragments (minimalFragments H W) Ws

lemma exists_iteratedMinimalFragment_subset_iff_source_subset_union
    (H : Finset (Finset α)) (Ws : List (Finset α)) (V : Finset α) :
    (∃ T ∈ iteratedMinimalFragments H Ws, T ⊆ V) ↔
      ∃ S ∈ H, S ⊆ exposureUnion Ws ∪ V := by
  induction Ws generalizing H V with
  | nil =>
      simp [iteratedMinimalFragments, exposureUnion]
  | cons W Ws ih =>
      rw [iteratedMinimalFragments]
      rw [ih (H := minimalFragments H W) (V := V)]
      rw [exists_minimalFragment_subset_iff_source_subset_union
        (H := H) (W := W) (V := exposureUnion Ws ∪ V)]
      simp [exposureUnion, Finset.union_assoc]

/-- Exposing `V` after passing to minimal fragments of `F(H,W)` finds an empty
fragment exactly when some original source member is contained in `W ∪ V`. -/
lemma empty_mem_fragmentFamily_minimalFragments_iff
    {H : Finset (Finset α)} {W V : Finset α} :
    (∅ : Finset α) ∈ fragmentFamily (minimalFragments H W) V ↔
      ∃ S ∈ H, S ⊆ W ∪ V := by
  rw [empty_mem_fragmentFamily_iff]
  exact exists_minimalFragment_subset_iff_source_subset_union

/-- For any family, `∅` is a minimal member exactly when it belongs to the
family. -/
lemma empty_mem_minimalMembersIn_iff
    (X : Finset α) (U : Finset (Finset α)) :
    (∅ : Finset α) ∈ minimalMembersIn X U ↔ (∅ : Finset α) ∈ U := by
  constructor
  · intro h
    exact minimalMembersIn_subset h
  · intro h
    refine mem_minimalMembersIn.mpr ⟨h, ?_⟩
    intro T _hT hTlt
    have hT_empty : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      simpa using hTlt.subset hx
    exact hTlt.ne hT_empty

/-- The empty set is a minimal fragment exactly when some source member is
already contained in `W`. -/
lemma empty_mem_minimalFragments_iff
    {H : Finset (Finset α)} {W : Finset α} :
    (∅ : Finset α) ∈ minimalFragments H W ↔ ∃ S ∈ H, S ⊆ W := by
  rw [minimalFragments, empty_mem_minimalMembersIn_iff,
    empty_mem_fragmentFamily_iff]

end

end ParkPham
end Erdos202


/-! =============================================================
    Section from: Erdos/P202/ParkPham/Cost.lean
    ============================================================= -/

/-
Erdos Problem 202 — Park–Pham layer, finite cover cost.

The Park--Pham/Park--Vondrak proofs use the cost of a family: the minimum
`p`-weight of a cover.  The existing `pSmall` predicate only needs existence
of a cover of weight at most `1/2`; this file packages the corresponding
finite minimum over covers supported on the ground set `X`.
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- Covers whose members are all subsets of the finite ground set `X`. -/
noncomputable def groundCoversIn (X : Finset α) (U : Finset (Finset α)) :
    Finset (Finset (Finset α)) :=
  by
    classical
    exact X.powerset.powerset.filter fun G => CoversIn X G U

omit [DecidableEq α] in
/-- The singleton cover `{∅}` covers every family. -/
lemma singleton_empty_covers (X : Finset α) (U : Finset (Finset α)) :
    CoversIn X ({∅} : Finset (Finset α)) U := by
  intro S _hS
  exact ⟨∅, by simp, Finset.empty_subset S⟩

omit [DecidableEq α] in
/-- The finite set of ground-supported covers is nonempty. -/
lemma groundCoversIn_nonempty (X : Finset α) (U : Finset (Finset α)) :
    (groundCoversIn X U).Nonempty := by
  refine ⟨{∅}, ?_⟩
  classical
  rw [groundCoversIn, Finset.mem_filter]
  constructor
  · rw [Finset.mem_powerset]
    intro T hT
    have hT_empty : T = ∅ := by simpa using hT
    subst hT_empty
    exact Finset.mem_powerset.mpr (Finset.empty_subset X)
  · exact singleton_empty_covers X U

omit [DecidableEq α] in
lemma mem_groundCoversIn {X : Finset α} {U G : Finset (Finset α)} :
    G ∈ groundCoversIn X U ↔
      (∀ T ∈ G, T ⊆ X) ∧ CoversIn X G U := by
  classical
  rw [groundCoversIn, Finset.mem_filter]
  constructor
  · intro h
    constructor
    · intro T hTG
      exact Finset.mem_powerset.mp (Finset.mem_powerset.mp h.1 hTG)
    · exact h.2
  · rintro ⟨hGX, hCover⟩
    refine ⟨?_, hCover⟩
    exact Finset.mem_powerset.mpr (by
      intro T hTG
      exact Finset.mem_powerset.mpr (hGX T hTG))

/-- The finite set of cover weights for ground-supported covers. -/
noncomputable def groundCoverWeights (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
    Finset ℝ :=
  by
    classical
    exact (groundCoversIn X U).image fun G => coverWeight G p

omit [DecidableEq α] in
lemma groundCoverWeights_nonempty
    (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
    (groundCoverWeights X U p).Nonempty :=
  (groundCoversIn_nonempty X U).image _

/-- The cost of `U` at density `p`: the minimum `p`-weight of a
ground-supported cover. -/
noncomputable def coverCost
    (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : ℝ :=
  (groundCoverWeights X U p).min' (groundCoverWeights_nonempty X U p)

omit [DecidableEq α] in
lemma coverCost_le_of_ground_cover
    {X : Finset α} {U G : Finset (Finset α)} {p : ℝ}
    (hGX : ∀ T ∈ G, T ⊆ X) (hCover : CoversIn X G U) :
    coverCost X U p ≤ coverWeight G p := by
  unfold coverCost groundCoverWeights
  exact Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨G, (mem_groundCoversIn.mpr ⟨hGX, hCover⟩), rfl⟩)

omit [DecidableEq α] in
lemma coverCost_nonneg
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} (hp0 : 0 ≤ p) :
    0 ≤ coverCost X U p := by
  unfold coverCost groundCoverWeights
  refine Finset.le_min' _ _ _ ?_
  intro w hw
  rcases Finset.mem_image.mp hw with ⟨G, _hG, rfl⟩
  unfold coverWeight
  exact Finset.sum_nonneg fun T _ => pow_nonneg hp0 T.card

omit [DecidableEq α] in
lemma exists_ground_cover_weight_eq_coverCost
    (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
    ∃ G : Finset (Finset α),
      (∀ T ∈ G, T ⊆ X) ∧
      CoversIn X G U ∧
      coverCost X U p = coverWeight G p := by
  unfold coverCost groundCoverWeights
  have hmem :=
    Finset.min'_mem ((groundCoversIn X U).image fun G => coverWeight G p)
      (groundCoverWeights_nonempty X U p)
  rcases Finset.mem_image.mp hmem with ⟨G, hG, hEq⟩
  rcases mem_groundCoversIn.mp hG with ⟨hGX, hCover⟩
  exact ⟨G, hGX, hCover, hEq.symm⟩

omit [DecidableEq α] in
lemma coverWeight_singleton_empty (p : ℝ) :
    coverWeight ({∅} : Finset (Finset α)) p = 1 := by
  simp [coverWeight]

omit [DecidableEq α] in
lemma coverCost_le_one (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
    coverCost X U p ≤ 1 := by
  have hle := coverCost_le_of_ground_cover
    (X := X) (U := U) (G := ({∅} : Finset (Finset α))) (p := p)
    (by
      intro T hT
      have hT_empty : T = ∅ := by simpa using hT
      subst hT_empty
      exact Finset.empty_subset X)
    (singleton_empty_covers X U)
  simpa [coverWeight_singleton_empty] using hle

omit [DecidableEq α] in
lemma self_covers (X : Finset α) (U : Finset (Finset α)) :
    CoversIn X U U := by
  intro S hS
  exact ⟨S, hS, subset_refl S⟩

omit [DecidableEq α] in
lemma coverCost_le_coverWeight_self
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hUX : ∀ T ∈ U, T ⊆ X) :
    coverCost X U p ≤ coverWeight U p :=
  coverCost_le_of_ground_cover hUX (self_covers X U)

omit [DecidableEq α] in
lemma coverCost_empty_eq_zero
    (X : Finset α) {p : ℝ} (hp0 : 0 ≤ p) :
    coverCost X (∅ : Finset (Finset α)) p = 0 := by
  have hle : coverCost X (∅ : Finset (Finset α)) p ≤ 0 := by
    have hcover : CoversIn X (∅ : Finset (Finset α))
        (∅ : Finset (Finset α)) := by
      intro S hS
      simp at hS
    have hground : ∀ T ∈ (∅ : Finset (Finset α)), T ⊆ X := by
      intro T hT
      simp at hT
    simpa [coverWeight] using
      (coverCost_le_of_ground_cover (X := X)
        (U := (∅ : Finset (Finset α)))
        (G := (∅ : Finset (Finset α))) (p := p) hground hcover)
  exact le_antisymm hle (coverCost_nonneg hp0)

omit [DecidableEq α] in
lemma one_le_coverCost_of_empty_mem
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hEmpty : (∅ : Finset α) ∈ U) :
    1 ≤ coverCost X U p := by
  unfold coverCost groundCoverWeights
  refine Finset.le_min' _ _ _ ?_
  intro w hw
  rcases Finset.mem_image.mp hw with ⟨G, hG, rfl⟩
  rcases mem_groundCoversIn.mp hG with ⟨_hGX, hCover⟩
  rcases hCover ∅ hEmpty with ⟨T, hTG, hTsub⟩
  have hT_empty : T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simpa using hTsub hx
  have hsingle :
      p ^ T.card ≤ coverWeight G p := by
    unfold coverWeight
    exact Finset.single_le_sum
      (s := G) (f := fun S : Finset α => p ^ S.card)
      (fun S _ => pow_nonneg hp0 S.card) hTG
  have hterm : p ^ T.card = 1 := by
    subst hT_empty
    simp
  linarith

omit [DecidableEq α] in
lemma coverCost_eq_one_of_empty_mem
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hEmpty : (∅ : Finset α) ∈ U) :
    coverCost X U p = 1 :=
  le_antisymm (coverCost_le_one X U p)
    (one_le_coverCost_of_empty_mem hp0 hEmpty)

omit [DecidableEq α] in
lemma eq_empty_of_forall_card_zero_empty_not_mem
    {U : Finset (Finset α)}
    (hcard : ∀ S ∈ U, S.card = 0)
    (hEmpty : (∅ : Finset α) ∉ U) :
    U = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hS_empty : S = ∅ := Finset.card_eq_zero.mp (hcard S hS)
  exact hEmpty (by simpa [hS_empty] using hS)

omit [DecidableEq α] in
lemma coverCost_pos_iff_empty_mem_of_forall_card_zero
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p)
    (hcard : ∀ S ∈ U, S.card = 0) :
    0 < coverCost X U p ↔ (∅ : Finset α) ∈ U := by
  constructor
  · intro hpos
    by_contra hEmpty
    have hU_empty : U = ∅ :=
      eq_empty_of_forall_card_zero_empty_not_mem hcard hEmpty
    have hcost : coverCost X U p = 0 := by
      rw [hU_empty]
      exact coverCost_empty_eq_zero X hp0
    linarith
  · intro hEmpty
    rw [coverCost_eq_one_of_empty_mem hp0 hEmpty]
    norm_num

/-- Ground-supported cover cost recovers the existing `pSmall` predicate for
families living inside `X`. -/
theorem pSmall_iff_coverCost_le
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hUX : ∀ S ∈ U, S ⊆ X) :
    pSmall X U p ↔ coverCost X U p ≤ (1 / 2 : ℝ) := by
  constructor
  · intro hSmall
    rcases pSmall.exists_ground_cover hp0 hUX hSmall with
      ⟨G, hGX, hCover, hsum⟩
    exact (coverCost_le_of_ground_cover hGX hCover).trans hsum
  · intro hCost
    rcases exists_ground_cover_weight_eq_coverCost X U p with
      ⟨G, _hGX, hCover, hEq⟩
    exact ⟨G, hCover, by simpa [hEq] using hCost⟩

lemma not_pSmall_iff_half_lt_coverCost
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hUX : ∀ S ∈ U, S ⊆ X) :
    ¬ pSmall X U p ↔ (1 / 2 : ℝ) < coverCost X U p := by
  rw [pSmall_iff_coverCost_le hp0 hUX]
  exact not_le

omit [DecidableEq α] in
/-- Cover cost is monotone decreasing as the target family shrinks. -/
lemma coverCost_mono_family
    {X : Finset α} {U V : Finset (Finset α)} {p : ℝ}
    (hUV : U ⊆ V) :
    coverCost X U p ≤ coverCost X V p := by
  rcases exists_ground_cover_weight_eq_coverCost X V p with
    ⟨G, hGX, hCoverV, hEq⟩
  have hCoverU : CoversIn X G U := hCoverV.mono_family hUV
  exact (coverCost_le_of_ground_cover hGX hCoverU).trans_eq hEq.symm

/-- Finite subadditivity of cover cost. -/
lemma coverCost_union_le
    {X : Finset α} {U V : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) :
    coverCost X (U ∪ V) p ≤ coverCost X U p + coverCost X V p := by
  rcases exists_ground_cover_weight_eq_coverCost X U p with
    ⟨G, hGX, hCoverU, hEqG⟩
  rcases exists_ground_cover_weight_eq_coverCost X V p with
    ⟨H, hHX, hCoverV, hEqH⟩
  have hGroundUnion : ∀ T ∈ G ∪ H, T ⊆ X := by
    intro T hT
    rcases Finset.mem_union.mp hT with hTG | hTH
    · exact hGX T hTG
    · exact hHX T hTH
  have hCoverUnion : CoversIn X (G ∪ H) (U ∪ V) :=
    hCoverU.union hCoverV
  calc
    coverCost X (U ∪ V) p ≤ coverWeight (G ∪ H) p :=
      coverCost_le_of_ground_cover hGroundUnion hCoverUnion
    _ ≤ coverWeight G p + coverWeight H p := coverWeight_union_le hp0
    _ = coverCost X U p + coverCost X V p := by
      rw [hEqG, hEqH]

end

end ParkPham
end Erdos202


/-! =============================================================
    Section from: Erdos/P202/ParkPham/FragmentCost.lean
    ============================================================= -/

/-
Erdos Problem 202 — Park–Pham layer, fragment cost bookkeeping.

This file connects the fragment infrastructure to the finite cover-cost API.
The key local step in the Park--Vondrak proof is that minimal fragments split
into small and large parts, and cost subadditivity gives

  cost(H) <= cost(S_m(F*(H,W))) + cost(L_m(F*(H,W))).

No probabilistic estimate is used here.
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- A cover of the minimal fragments is automatically a cover of the original
family, so the original family has no larger cover cost than the minimal
fragment family. -/
lemma coverCost_le_minimalFragments
    (X : Finset α) (H : Finset (Finset α)) (W : Finset α) (p : ℝ) :
    coverCost X H p ≤ coverCost X (minimalFragments H W) p := by
  rcases exists_ground_cover_weight_eq_coverCost X (minimalFragments H W) p with
    ⟨G, hGX, hCover, hEq⟩
  exact (coverCost_le_of_ground_cover hGX hCover.of_minimalFragments).trans_eq
    hEq.symm

/-- The finite cost subadditivity step for the large/small minimal-fragment
split. -/
lemma coverCost_le_small_add_large_minimalFragments
    (X : Finset α) (m : ℕ) (H : Finset (Finset α)) (W : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p) :
    coverCost X H p ≤
      coverCost X (smallMinimalFragments m H W) p +
        coverCost X (largeMinimalFragments m H W) p := by
  have htoMin :
      coverCost X H p ≤ coverCost X (minimalFragments H W) p :=
    coverCost_le_minimalFragments X H W p
  have hpartition :
      smallMinimalFragments m H W ∪ largeMinimalFragments m H W =
        minimalFragments H W :=
    small_union_large_minimalFragments m H W
  have hsubadd :
      coverCost X (smallMinimalFragments m H W ∪ largeMinimalFragments m H W) p ≤
        coverCost X (smallMinimalFragments m H W) p +
          coverCost X (largeMinimalFragments m H W) p :=
    coverCost_union_le hp0
  calc
    coverCost X H p ≤ coverCost X (minimalFragments H W) p := htoMin
    _ = coverCost X
          (smallMinimalFragments m H W ∪ largeMinimalFragments m H W) p := by
        rw [hpartition]
    _ ≤ coverCost X (smallMinimalFragments m H W) p +
        coverCost X (largeMinimalFragments m H W) p := hsubadd

lemma largeMinimalFragments_subset_ground
    {X : Finset α} {m : ℕ} {H : Finset (Finset α)} {W T : Finset α}
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hT : T ∈ largeMinimalFragments m H W) :
    T ⊆ X := by
  have hTmin : T ∈ minimalFragments H W :=
    (mem_largeMinimalFragments.mp hT).1
  have hTfrag : T ∈ fragmentFamily H W :=
    minimalFragments_subset_fragmentFamily H W hTmin
  rcases mem_fragmentFamily.mp hTfrag with ⟨S, hS, rfl⟩
  exact (Finset.sdiff_subset : S \ W ⊆ S).trans (hHX S hS)

lemma coverCost_largeMinimalFragments_le_card_mul_pow
    {X : Finset α} {m : ℕ} {H : Finset (Finset α)} {W : Finset α}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X) :
    coverCost X (largeMinimalFragments m H W) p ≤
      ((largeMinimalFragments m H W).card : ℝ) * p ^ m := by
  have hcost :
      coverCost X (largeMinimalFragments m H W) p ≤
        coverWeight (largeMinimalFragments m H W) p :=
    coverCost_le_coverWeight_self
      (fun T hT => largeMinimalFragments_subset_ground hHX hT)
  have hweight :
      coverWeight (largeMinimalFragments m H W) p ≤
        ((largeMinimalFragments m H W).card : ℝ) * p ^ m := by
    unfold coverWeight
    calc
      (∑ T ∈ largeMinimalFragments m H W, p ^ T.card)
          ≤ ∑ T ∈ largeMinimalFragments m H W, p ^ m := by
            refine Finset.sum_le_sum ?_
            intro T hT
            exact pow_le_pow_of_le_one hp0 hp1
              (mem_largeMinimalFragments.mp hT).2
      _ = ((largeMinimalFragments m H W).card : ℝ) * p ^ m := by
            rw [Finset.sum_const, nsmul_eq_mul]
  exact hcost.trans hweight

lemma coverCost_largeMinimalFragments_le_source_card_mul_pow
    {X : Finset α} {m : ℕ} {H : Finset (Finset α)} {W : Finset α}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X) :
    coverCost X (largeMinimalFragments m H W) p ≤
      (H.card : ℝ) * p ^ m := by
  have hcost :=
    coverCost_largeMinimalFragments_le_card_mul_pow
      (X := X) (m := m) (H := H) (W := W)
      hp0 hp1 hHX
  have hcard :
      ((largeMinimalFragments m H W).card : ℝ) * p ^ m ≤
        (H.card : ℝ) * p ^ m := by
    have hcard_nat := largeMinimalFragments_card_le_card m H W
    have hcard_real :
        ((largeMinimalFragments m H W).card : ℝ) ≤ (H.card : ℝ) := by
      exact_mod_cast hcard_nat
    exact mul_le_mul_of_nonneg_right hcard_real (pow_nonneg hp0 m)
  exact hcost.trans hcard

lemma coverCost_smallMinimalFragments_pos_of_large_cost_lt
    (X : Finset α) (m : ℕ) (H : Finset (Finset α)) (W : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hlarge :
      coverCost X (largeMinimalFragments m H W) p < coverCost X H p) :
    0 < coverCost X (smallMinimalFragments m H W) p := by
  have hle := coverCost_le_small_add_large_minimalFragments X m H W hp0
  linarith

lemma smallMinimalFragments_one_card_zero
    {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ smallMinimalFragments 1 H W) :
    T.card = 0 := by
  exact Nat.lt_one_iff.mp (mem_smallMinimalFragments.mp hT).2

/-- At cutoff `1`, the small-fragment family consists only of `∅`, so
positive cover cost exactly means that some original member is already covered
by `W`. -/
lemma coverCost_smallMinimalFragments_one_pos_iff_exists_subset
    (X : Finset α) (H : Finset (Finset α)) (W : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p) :
    0 < coverCost X (smallMinimalFragments 1 H W) p ↔
      ∃ S ∈ H, S ⊆ W := by
  rw [coverCost_pos_iff_empty_mem_of_forall_card_zero
    (X := X) (U := smallMinimalFragments 1 H W) (p := p) hp0
    (fun T hT => smallMinimalFragments_one_card_zero hT)]
  simp

lemma exists_subset_of_largeMinimalFragments_one_cost_lt
    (X : Finset α) (H : Finset (Finset α)) (W : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hlarge :
      coverCost X (largeMinimalFragments 1 H W) p < coverCost X H p) :
    ∃ S ∈ H, S ⊆ W := by
  have hpos :
      0 < coverCost X (smallMinimalFragments 1 H W) p :=
    coverCost_smallMinimalFragments_pos_of_large_cost_lt X 1 H W hp0 hlarge
  exact (coverCost_smallMinimalFragments_one_pos_iff_exists_subset
    X H W hp0).mp hpos

/-- One-step endpoint for the fragment iteration: after exposing `W`, a final
cutoff-`1` small-fragment step with exposure `V` has positive cost exactly
when an original source member is contained in `W ∪ V`. -/
lemma coverCost_smallMinimalFragments_one_minimalFragments_pos_iff_exists_subset_union
    (X : Finset α) (H : Finset (Finset α)) (W V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p) :
    0 < coverCost X (smallMinimalFragments 1 (minimalFragments H W) V) p ↔
      ∃ S ∈ H, S ⊆ W ∪ V := by
  rw [coverCost_smallMinimalFragments_one_pos_iff_exists_subset
    X (minimalFragments H W) V hp0]
  exact exists_minimalFragment_subset_iff_source_subset_union

lemma exists_subset_union_of_largeMinimalFragments_one_minimalFragments_cost_lt
    (X : Finset α) (H : Finset (Finset α)) (W V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hlarge :
      coverCost X (largeMinimalFragments 1 (minimalFragments H W) V) p <
        coverCost X (minimalFragments H W) p) :
    ∃ S ∈ H, S ⊆ W ∪ V := by
  have hpos :
      0 < coverCost X (smallMinimalFragments 1 (minimalFragments H W) V) p :=
    coverCost_smallMinimalFragments_pos_of_large_cost_lt
      X 1 (minimalFragments H W) V hp0 hlarge
  exact
    (coverCost_smallMinimalFragments_one_minimalFragments_pos_iff_exists_subset_union
      X H W V hp0).mp hpos

/-- Endpoint for a finite fragment iteration: after a list of exposures `Ws`,
positive final cutoff-`1` small-fragment cost is equivalent to an original
source member being contained in the union of all exposures and the final
exposure `V`. -/
lemma coverCost_smallMinimalFragments_one_iterated_pos_iff_exists_subset_union
    (X : Finset α) (H : Finset (Finset α)) (Ws : List (Finset α))
    (V : Finset α) {p : ℝ} (hp0 : 0 ≤ p) :
    0 < coverCost X (smallMinimalFragments 1 (iteratedMinimalFragments H Ws) V) p ↔
      ∃ S ∈ H, S ⊆ exposureUnion Ws ∪ V := by
  rw [coverCost_smallMinimalFragments_one_pos_iff_exists_subset
    X (iteratedMinimalFragments H Ws) V hp0]
  exact exists_iteratedMinimalFragment_subset_iff_source_subset_union H Ws V

lemma exposureUnion_mem_upClosureIn_of_smallMinimalFragments_one_iterated_pos
    (X : Finset α) (H : Finset (Finset α)) (Ws : List (Finset α))
    (V : Finset α) {p : ℝ} (hp0 : 0 ≤ p)
    (hUnionX : exposureUnion Ws ∪ V ⊆ X)
    (hpos :
      0 < coverCost X (smallMinimalFragments 1 (iteratedMinimalFragments H Ws) V) p) :
    exposureUnion Ws ∪ V ∈ upClosureIn X H := by
  rcases
    (coverCost_smallMinimalFragments_one_iterated_pos_iff_exists_subset_union
      X H Ws V hp0).mp hpos with ⟨S, hS, hSsub⟩
  exact mem_upClosureIn.mpr ⟨hUnionX, S, hS, hSsub⟩

lemma exists_subset_union_of_largeMinimalFragments_one_iterated_cost_lt
    (X : Finset α) (H : Finset (Finset α)) (Ws : List (Finset α))
    (V : Finset α) {p : ℝ} (hp0 : 0 ≤ p)
    (hlarge :
      coverCost X (largeMinimalFragments 1 (iteratedMinimalFragments H Ws) V) p <
        coverCost X (iteratedMinimalFragments H Ws) p) :
    ∃ S ∈ H, S ⊆ exposureUnion Ws ∪ V := by
  have hpos :
      0 < coverCost X
        (smallMinimalFragments 1 (iteratedMinimalFragments H Ws) V) p :=
    coverCost_smallMinimalFragments_pos_of_large_cost_lt
      X 1 (iteratedMinimalFragments H Ws) V hp0 hlarge
  exact
    (coverCost_smallMinimalFragments_one_iterated_pos_iff_exists_subset_union
      X H Ws V hp0).mp hpos

lemma exposureUnion_mem_upClosureIn_of_largeMinimalFragments_one_iterated_cost_lt
    (X : Finset α) (H : Finset (Finset α)) (Ws : List (Finset α))
    (V : Finset α) {p : ℝ} (hp0 : 0 ≤ p)
    (hUnionX : exposureUnion Ws ∪ V ⊆ X)
    (hlarge :
      coverCost X (largeMinimalFragments 1 (iteratedMinimalFragments H Ws) V) p <
        coverCost X (iteratedMinimalFragments H Ws) p) :
    exposureUnion Ws ∪ V ∈ upClosureIn X H := by
  have hpos :
      0 < coverCost X
        (smallMinimalFragments 1 (iteratedMinimalFragments H Ws) V) p :=
    coverCost_smallMinimalFragments_pos_of_large_cost_lt
      X 1 (iteratedMinimalFragments H Ws) V hp0 hlarge
  exact exposureUnion_mem_upClosureIn_of_smallMinimalFragments_one_iterated_pos
    X H Ws V hp0 hUnionX hpos

end

end ParkPham
end Erdos202


/-! =============================================================
    Section from: Erdos/P202/ParkPham/FragmentIteration.lean
    ============================================================= -/

/-
Erdos Problem 202 — Park–Pham layer, fragment iteration bookkeeping.

This file packages the deterministic Park--Vondrak iteration skeleton.  It
does not prove the probabilistic large-fragment estimate; it only proves that
if the accumulated large-fragment cost losses are strictly smaller than the
initial cover cost, then the final cutoff-`1` small-fragment step forces an
original generator to be contained in the union of the exposed sets.
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- Union of the exposure sets in a finite list of `(cutoff, exposure)` steps. -/
def smallStepExposureUnion : List (ℕ × Finset α) → Finset α
  | [] => ∅
  | step :: steps => step.2 ∪ smallStepExposureUnion steps

/-- Iteration of `smallMinimalFragments` along a finite list of
`(cutoff, exposure)` steps. -/
def iteratedSmallFragments (H : Finset (Finset α)) :
    List (ℕ × Finset α) → Finset (Finset α)
  | [] => H
  | step :: steps =>
      iteratedSmallFragments
        (smallMinimalFragments step.1 H step.2) steps

/-- Accumulated large-fragment cover-cost loss along the same finite
small-fragment iteration. -/
noncomputable def iteratedLargeCostSum
    (X : Finset α) (p : ℝ) (H : Finset (Finset α)) :
    List (ℕ × Finset α) → ℝ
  | [] => 0
  | step :: steps =>
      coverCost X (largeMinimalFragments step.1 H step.2) p +
        iteratedLargeCostSum X p
          (smallMinimalFragments step.1 H step.2) steps

/-- Convert a tuple of exposure sets and cutoff values into the list format
used by the deterministic fragment iteration. -/
def exposureTupleSteps {n : ℕ} (cutoff : Fin n → ℕ)
    (Ws : Fin n → Finset α) : List (ℕ × Finset α) :=
  List.ofFn fun i => (cutoff i, Ws i)

/-- Snoc-ordered version of `exposureTupleSteps`, convenient when the final
cutoff-`1` exposure must be peeled off. -/
def exposureTupleStepsSnoc :
    {n : ℕ} → (Fin n → ℕ) → (Fin n → Finset α) → List (ℕ × Finset α)
  | 0, _cutoff, _Ws => []
  | n + 1, cutoff, Ws =>
      exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc)
        (fun i : Fin n => Ws i.castSucc) ++
        [(cutoff (Fin.last n), Ws (Fin.last n))]

omit [DecidableEq α] in
lemma exposureTupleStepsSnoc_snoc {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin n → Finset α)
    (W : Finset α) :
    exposureTupleStepsSnoc cutoff
        (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
      exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws ++
        [(cutoff (Fin.last n), W)] := by
  simp [exposureTupleStepsSnoc]

lemma smallStepExposureUnion_exposureTupleSteps
    {n : ℕ} (cutoff : Fin n → ℕ) (Ws : Fin n → Finset α) :
    smallStepExposureUnion (exposureTupleSteps cutoff Ws) =
      exposureTupleUnion Ws := by
  induction n with
  | zero =>
      ext x
      simp [exposureTupleSteps, smallStepExposureUnion, exposureTupleUnion]
  | succ n ih =>
      have htail :=
        ih (fun i : Fin n => cutoff i.succ) (fun i : Fin n => Ws i.succ)
      have htail' :
          smallStepExposureUnion
              (List.ofFn fun i : Fin n => (cutoff i.succ, Ws i.succ)) =
            exposureTupleUnion (fun i : Fin n => Ws i.succ) := by
        simpa [exposureTupleSteps] using htail
      ext x
      rw [exposureTupleSteps, List.ofFn_succ]
      simp only [smallStepExposureUnion, Finset.mem_union]
      rw [htail']
      constructor
      · intro hx
        rcases hx with hx0 | hxtail
        · simpa [exposureTupleUnion] using
            (Exists.intro (0 : Fin (n + 1)) hx0)
        · rcases (by
            simpa [exposureTupleUnion] using hxtail :
              ∃ i : Fin n, x ∈ Ws i.succ) with ⟨i, hi⟩
          simpa [exposureTupleUnion] using
            (Exists.intro (i.succ : Fin (n + 1)) hi)
      · intro hx
        rcases (by
          simpa [exposureTupleUnion] using hx :
            ∃ i : Fin (n + 1), x ∈ Ws i) with ⟨i, hi⟩
        cases i using Fin.cases with
        | zero =>
            exact Or.inl hi
        | succ i =>
            exact Or.inr (by
              have : x ∈ exposureTupleUnion (fun i : Fin n => Ws i.succ) := by
                simpa [exposureTupleUnion] using (Exists.intro i hi)
              simpa using this)

lemma exists_exposure_largeCost_lt_of_bernoulli_average_lt
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    {ρ p B : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (havg :
      (∑ W ∈ X.powerset,
        bernoulliMass X W ρ *
          coverCost X (largeMinimalFragments m H W) p) < B) :
    ∃ W ∈ X.powerset,
      coverCost X (largeMinimalFragments m H W) p < B :=
  exists_powerset_value_lt_of_bernoulli_average_lt X
    (fun W => coverCost X (largeMinimalFragments m H W) p) hρ0 hρ1 havg

lemma bernoulli_average_largeCost_le_source_card_mul_pow
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    {ρ p : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) p) ≤
      (H.card : ℝ) * p ^ m := by
  have hpoint :
      ∀ W ∈ X.powerset,
        coverCost X (largeMinimalFragments m H W) p ≤
          (H.card : ℝ) * p ^ m := by
    intro W _hW
    exact coverCost_largeMinimalFragments_le_source_card_mul_pow
      hp0 hp1 hHX
  calc
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) p)
        ≤ ∑ W ∈ X.powerset,
            bernoulliMass X W ρ * ((H.card : ℝ) * p ^ m) := by
          refine Finset.sum_le_sum ?_
          intro W hW
          exact mul_le_mul_of_nonneg_left (hpoint W hW)
            (bernoulliMass_nonneg hρ0 hρ1)
    _ = (∑ W ∈ X.powerset, bernoulliMass X W ρ) *
          ((H.card : ℝ) * p ^ m) := by
          rw [Finset.sum_mul]
    _ = (H.card : ℝ) * p ^ m := by
          rw [sum_bernoulliMass_eq_one (α := α) X (p := ρ) (by ring)]
          ring

lemma exists_exposure_largeCost_lt_of_source_card_mul_pow_lt
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    {ρ p B : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hbound : (H.card : ℝ) * p ^ m < B) :
    ∃ W ∈ X.powerset,
      coverCost X (largeMinimalFragments m H W) p < B := by
  have havg :
      (∑ W ∈ X.powerset,
        bernoulliMass X W ρ *
          coverCost X (largeMinimalFragments m H W) p) < B :=
    (bernoulli_average_largeCost_le_source_card_mul_pow
      X H m hρ0 hρ1 hp0 hp1 hHX).trans_lt hbound
  exact exists_exposure_largeCost_lt_of_bernoulli_average_lt
    X H m hρ0 hρ1 havg

lemma sum_largeFragmentPairs_eq_nested
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    (w : Finset α × Finset α → ℝ) :
    (∑ P ∈ largeFragmentPairs X H m, w P) =
      ∑ W ∈ X.powerset,
        ∑ S ∈ largeMinimalFragments m H W, w (W, S) := by
  unfold largeFragmentPairs
  rw [Finset.sum_biUnion (pairwiseDisjoint_largeFragmentPair_fibers H m X.powerset)]
  refine Finset.sum_congr rfl ?_
  intro W _hW
  rw [Finset.sum_image]
  intro S _hS T _hT hEq
  exact congrArg Prod.snd hEq

lemma bernoulli_average_largeCoverWeight_eq_pair_sum
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    (ρ q : ℝ) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ * coverWeight (largeMinimalFragments m H W) q) =
      ∑ P ∈ largeFragmentPairs X H m,
        bernoulliMass X P.1 ρ * q ^ P.2.card := by
  rw [sum_largeFragmentPairs_eq_nested]
  unfold coverWeight
  refine Finset.sum_congr rfl ?_
  intro W _hW
  rw [Finset.mul_sum]

lemma sum_largeWitnessPairs_eq_nested
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    (w : Finset α × Finset α → ℝ) :
    (∑ P ∈ largeWitnessPairs X H m, w P) =
      ∑ Z ∈ X.powerset,
        ∑ S ∈ largeFragmentWitnesses H m Z, w (Z, S) := by
  unfold largeWitnessPairs
  rw [Finset.sum_biUnion (pairwiseDisjoint_largeWitnessPair_fibers H m X.powerset)]
  refine Finset.sum_congr rfl ?_
  intro Z _hZ
  rw [Finset.sum_image]
  intro S _hS T _hT hEq
  exact congrArg Prod.snd hEq

lemma bernoulli_average_largeCost_le_pair_sum
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    {ρ q : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) q) ≤
      ∑ P ∈ largeFragmentPairs X H m,
        bernoulliMass X P.1 ρ * q ^ P.2.card := by
  calc
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) q)
        ≤ ∑ W ∈ X.powerset,
            bernoulliMass X W ρ *
              coverWeight (largeMinimalFragments m H W) q := by
          refine Finset.sum_le_sum ?_
          intro W _hW
          have hcost :
              coverCost X (largeMinimalFragments m H W) q ≤
                coverWeight (largeMinimalFragments m H W) q :=
            coverCost_le_coverWeight_self
              (fun T hT => largeMinimalFragment_subset_ground hHX hT)
          exact mul_le_mul_of_nonneg_left hcost
            (bernoulliMass_nonneg hρ0 hρ1)
    _ = ∑ P ∈ largeFragmentPairs X H m,
          bernoulliMass X P.1 ρ * q ^ P.2.card :=
        bernoulli_average_largeCoverWeight_eq_pair_sum X H m ρ q

lemma largeFragment_pair_sum_le_witness_sum
    (X : Finset α) (H : Finset (Finset α)) (m L : ℕ)
    {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X) :
    (∑ P ∈ largeFragmentPairs X H m,
      bernoulliMass X P.1 ρ * q ^ P.2.card) ≤
      ∑ Q ∈ largeWitnessPairs X H m,
        bernoulliMass X Q.1 ρ * (1 / (L : ℝ)) ^ Q.2.card := by
  have hρ0 : 0 ≤ ρ := by
    have hρpos : 0 < ρ := by
      simpa [hρ] using one_sub_one_sub_q_pow_pos hL hq0 hq1
    exact hρpos.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]
    have hpow_nonneg : 0 ≤ (1 - q) ^ L := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
    linarith
  have hLpos : 0 < (L : ℝ) := by
    have hL_nat_pos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
    exact_mod_cast hL_nat_pos
  let w : Finset α × Finset α → ℝ :=
    fun Q => bernoulliMass X Q.1 ρ * (1 / (L : ℝ)) ^ Q.2.card
  have hterm :
      (∑ P ∈ largeFragmentPairs X H m,
        bernoulliMass X P.1 ρ * q ^ P.2.card) ≤
        ∑ P ∈ largeFragmentPairs X H m, w (largeFragmentPairToWitness P) := by
    refine Finset.sum_le_sum ?_
    intro P hP
    rcases P with ⟨W, S⟩
    rcases mem_largeFragmentPairs.mp hP with ⟨hWX, hSlarge⟩
    have hdisj : Disjoint S W :=
      largeMinimalFragment_disjoint_exposure hSlarge
    have hUnionX : W ∪ S ⊆ X :=
      Finset.union_subset hWX (largeMinimalFragment_subset_ground hHX hSlarge)
    exact bernoulliMass_mul_pow_le_union_mul_inv_nat_pow
      (X := X) (W := W) (S := S) (q := q) (ρ := ρ) (L := L)
      hL hq0 hq1 hρ hdisj hUnionX
  have hw_nonneg : ∀ Q, 0 ≤ w Q := by
    intro Q
    exact mul_nonneg (bernoulliMass_nonneg hρ0 hρ1)
      (pow_nonneg (by positivity : 0 ≤ (1 / (L : ℝ))) Q.2.card)
  exact hterm.trans
    (sum_largeFragmentPairs_toWitness_le_sum_witnessPairs hHX w hw_nonneg)

lemma largeWitness_sum_le_muP_mul_two_pow
    (X : Finset α) (H : Finset (Finset α)) (m ell : ℕ)
    {ρ a : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hHbound : ∀ T ∈ H, T.card ≤ ell) :
    (∑ Q ∈ largeWitnessPairs X H m,
      bernoulliMass X Q.1 ρ * a ^ Q.2.card) ≤
      muP X (upClosureIn X H) ρ * ((2 : ℝ) ^ ell * a ^ m) := by
  let B : ℝ := (2 : ℝ) ^ ell * a ^ m
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hinner_zero :
      ∀ Z ∈ X.powerset, Z ∉ upClosureIn X H →
        (∑ S ∈ largeFragmentWitnesses H m Z,
          bernoulliMass X Z ρ * a ^ S.card) = 0 := by
    intro Z _hZ hZnot
    have hno : ¬ ∃ T ∈ H, T ⊆ Z := by
      intro h
      exact hZnot (mem_upClosureIn.mpr
        ⟨Finset.mem_powerset.mp _hZ, h⟩)
    rw [largeFragmentWitnesses_eq_empty_of_no_source_subset hno]
    simp
  have hinner_bound :
      ∀ Z ∈ X.powerset, Z ∈ upClosureIn X H →
        (∑ S ∈ largeFragmentWitnesses H m Z,
          bernoulliMass X Z ρ * a ^ S.card) ≤
          bernoulliMass X Z ρ * B := by
    intro Z _hZ hZU
    rcases mem_upClosureIn.mp hZU with ⟨_hZX, T, hT, hTZ⟩
    have hsum_le :
        (∑ S ∈ largeFragmentWitnesses H m Z, a ^ S.card) ≤
          (2 : ℝ) ^ T.card * a ^ m :=
      sum_largeFragmentWitnesses_pow_le_two_pow_mul_pow ha0 ha1 hT hTZ
    have hT_le : T.card ≤ ell := hHbound T hT
    have hpow2_le : (2 : ℝ) ^ T.card ≤ (2 : ℝ) ^ ell :=
      pow_le_pow_right₀ (by norm_num) hT_le
    have hsource_le_B :
        (2 : ℝ) ^ T.card * a ^ m ≤ B := by
      exact mul_le_mul_of_nonneg_right hpow2_le (pow_nonneg ha0 m)
    calc
      (∑ S ∈ largeFragmentWitnesses H m Z,
          bernoulliMass X Z ρ * a ^ S.card)
          = bernoulliMass X Z ρ *
              ∑ S ∈ largeFragmentWitnesses H m Z, a ^ S.card := by
            rw [Finset.mul_sum]
      _ ≤ bernoulliMass X Z ρ * ((2 : ℝ) ^ T.card * a ^ m) :=
            mul_le_mul_of_nonneg_left hsum_le
              (bernoulliMass_nonneg hρ0 hρ1)
      _ ≤ bernoulliMass X Z ρ * B :=
            mul_le_mul_of_nonneg_left hsource_le_B
              (bernoulliMass_nonneg hρ0 hρ1)
  calc
    (∑ Q ∈ largeWitnessPairs X H m,
      bernoulliMass X Q.1 ρ * a ^ Q.2.card)
        = ∑ Z ∈ X.powerset,
            ∑ S ∈ largeFragmentWitnesses H m Z,
              bernoulliMass X Z ρ * a ^ S.card := by
          rw [sum_largeWitnessPairs_eq_nested]
    _ = ∑ Z ∈ X.powerset,
            if Z ∈ upClosureIn X H then
              ∑ S ∈ largeFragmentWitnesses H m Z,
                bernoulliMass X Z ρ * a ^ S.card
            else 0 := by
          refine Finset.sum_congr rfl ?_
          intro Z hZ
          by_cases hZU : Z ∈ upClosureIn X H
          · simp [hZU]
          · simp [hZU, hinner_zero Z hZ hZU]
    _ = ∑ Z ∈ X.powerset.filter (fun Z => Z ∈ upClosureIn X H),
            ∑ S ∈ largeFragmentWitnesses H m Z,
              bernoulliMass X Z ρ * a ^ S.card := by
          rw [Finset.sum_filter]
    _ ≤ ∑ Z ∈ X.powerset.filter (fun Z => Z ∈ upClosureIn X H),
            bernoulliMass X Z ρ * B := by
          refine Finset.sum_le_sum ?_
          intro Z hZ
          exact hinner_bound Z (Finset.mem_filter.mp hZ).1
            (Finset.mem_filter.mp hZ).2
    _ = muP X (upClosureIn X H) ρ * B := by
          unfold muP
          rw [← Finset.sum_mul]

/-- Loose uniform Park--Vondrak large-fragment cost lemma.  This is the
`2^ell / L^m` version mentioned in the paper, sufficient for a large absolute
constant in the expectation-threshold theorem. -/
lemma bernoulli_average_largeCost_le_muP_mul_two_pow_inv
    (X : Finset α) (H : Finset (Finset α)) (m ell L : ℕ)
    {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) q) ≤
      muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ m) := by
  have hρ0 : 0 ≤ ρ := by
    have hρpos : 0 < ρ := by
      simpa [hρ] using one_sub_one_sub_q_pow_pos hL hq0 hq1
    exact hρpos.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]
    have hpow_nonneg : 0 ≤ (1 - q) ^ L := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
    linarith
  have hLpos : 0 < (L : ℝ) := by
    have hL_nat_pos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
    exact_mod_cast hL_nat_pos
  have hinv0 : 0 ≤ (1 / (L : ℝ)) := by positivity
  have hinv1 : (1 / (L : ℝ)) ≤ 1 := by
    rw [div_le_one hLpos]
    exact_mod_cast hL
  calc
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) q)
        ≤ ∑ P ∈ largeFragmentPairs X H m,
            bernoulliMass X P.1 ρ * q ^ P.2.card :=
          bernoulli_average_largeCost_le_pair_sum X H m hρ0 hρ1 hHX
    _ ≤ ∑ Q ∈ largeWitnessPairs X H m,
          bernoulliMass X Q.1 ρ * (1 / (L : ℝ)) ^ Q.2.card :=
          largeFragment_pair_sum_le_witness_sum
            X H m L hL hq0 hq1 hρ hHX
    _ ≤ muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ m) :=
          largeWitness_sum_le_muP_mul_two_pow
            X H m ell hρ0 hρ1 hinv0 hinv1 hHbound

/-- If the Park--Vondrak large-fragment expectation bound is below a budget,
then one exposure has large-fragment cost below that budget. -/
lemma exists_exposure_largeCost_lt_of_muP_mul_two_pow_inv_lt
    (X : Finset α) (H : Finset (Finset α)) (m ell L : ℕ)
    {q ρ B : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell)
    (hbound :
      muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ m) < B) :
    ∃ W ∈ X.powerset,
      coverCost X (largeMinimalFragments m H W) q < B := by
  have hρ0 : 0 ≤ ρ := by
    have hρpos : 0 < ρ := by
      simpa [hρ] using one_sub_one_sub_q_pow_pos hL hq0 hq1
    exact hρpos.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]
    have hpow_nonneg : 0 ≤ (1 - q) ^ L := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
    linarith
  have havg_lt :
      (∑ W ∈ X.powerset,
        bernoulliMass X W ρ *
          coverCost X (largeMinimalFragments m H W) q) < B :=
    (bernoulli_average_largeCost_le_muP_mul_two_pow_inv
      X H m ell L hL hq0 hq1 hρ hHX hHbound).trans_lt hbound
  exact exists_exposure_largeCost_lt_of_bernoulli_average_lt
    X H m hρ0 hρ1 havg_lt

lemma smallStepExposureUnion_subset
    {steps : List (ℕ × Finset α)} {X : Finset α}
    (hsteps : ∀ step ∈ steps, step.2 ⊆ X) :
    smallStepExposureUnion steps ⊆ X := by
  induction steps with
  | nil =>
      simp [smallStepExposureUnion]
  | cons step steps ih =>
      intro x hx
      rcases Finset.mem_union.mp (by
        simpa [smallStepExposureUnion] using hx) with hxStep | hxRest
      · exact hsteps step (by simp) hxStep
      · exact ih (by
          intro step' hstep'
          exact hsteps step' (by simp [hstep'])) hxRest

lemma smallStepExposureUnion_append_singleton
    (steps : List (ℕ × Finset α)) (step : ℕ × Finset α) :
    smallStepExposureUnion (steps ++ [step]) =
      smallStepExposureUnion steps ∪ step.2 := by
  induction steps with
  | nil =>
      simp [smallStepExposureUnion]
  | cons head steps ih =>
      simp [smallStepExposureUnion, ih, Finset.union_assoc]

lemma smallStepExposureUnion_exposureTupleStepsSnoc
    {n : ℕ} (cutoff : Fin n → ℕ) (Ws : Fin n → Finset α) :
    smallStepExposureUnion (exposureTupleStepsSnoc cutoff Ws) =
      exposureTupleUnion Ws := by
  induction n with
  | zero =>
      ext x
      simp [exposureTupleStepsSnoc, smallStepExposureUnion, exposureTupleUnion]
  | succ n ih =>
      rw [exposureTupleStepsSnoc]
      rw [smallStepExposureUnion_append_singleton]
      rw [ih]
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hxtail | hxlast
        · rcases (by
            simpa [exposureTupleUnion] using hxtail :
              ∃ i : Fin n, x ∈ Ws i.castSucc) with ⟨i, hi⟩
          simpa [exposureTupleUnion] using
            (Exists.intro (i.castSucc : Fin (n + 1)) hi)
        · simpa [exposureTupleUnion] using
            (Exists.intro (Fin.last n) hxlast)
      · intro hx
        rcases (by
          simpa [exposureTupleUnion] using hx :
            ∃ i : Fin (n + 1), x ∈ Ws i) with ⟨i, hi⟩
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · exact Finset.mem_union.mpr (Or.inl (by
            simpa [exposureTupleUnion] using (Exists.intro j hi)))
        · exact Finset.mem_union.mpr (Or.inr hi)

lemma exposureTupleStepsSnoc_last_shape
    {X : Finset α} {n : ℕ} {cutoff : Fin (n + 1) → ℕ}
    {Ws : Fin (n + 1) → Finset α}
    (hWs : Ws ∈ exposureTupleSpace X (n + 1))
    (hlast : cutoff (Fin.last n) = 1) :
    ∃ steps V,
      exposureTupleStepsSnoc cutoff Ws = steps ++ [(1, V)] ∧
      smallStepExposureUnion steps ∪ V ⊆ X := by
  refine ⟨exposureTupleStepsSnoc
      (fun i : Fin n => cutoff i.castSucc)
      (fun i : Fin n => Ws i.castSucc),
    Ws (Fin.last n), ?_, ?_⟩
  · simp [exposureTupleStepsSnoc, hlast]
  · rw [smallStepExposureUnion_exposureTupleStepsSnoc]
    intro x hx
    rcases Finset.mem_union.mp hx with hxtail | hxlast
    · rcases (by
        simpa [exposureTupleUnion] using hxtail :
          ∃ i : Fin n, x ∈ Ws i.castSucc) with ⟨i, hi⟩
      exact Finset.mem_powerset.mp ((mem_exposureTupleSpace.mp hWs) i.castSucc) hi
    · exact Finset.mem_powerset.mp
        ((mem_exposureTupleSpace.mp hWs) (Fin.last n)) hxlast

lemma smallStepExposureUnion_exposureTupleSteps_append_singleton
    {n : ℕ} (cutoff : Fin n → ℕ) (Ws : Fin n → Finset α)
    (V : Finset α) :
    smallStepExposureUnion (exposureTupleSteps cutoff Ws ++ [(1, V)]) =
      exposureTupleUnion Ws ∪ V := by
  rw [smallStepExposureUnion_append_singleton,
    smallStepExposureUnion_exposureTupleSteps]

lemma exposureTupleSteps_append_singleton_shape
    {X : Finset α} {n : ℕ} {cutoff : Fin n → ℕ}
    {Ws : Fin n → Finset α} {V : Finset α}
    (hWs : Ws ∈ exposureTupleSpace X n) (hV : V ⊆ X) :
    ∃ steps V',
      exposureTupleSteps cutoff Ws ++ [(1, V)] = steps ++ [(1, V')] ∧
      smallStepExposureUnion steps ∪ V' ⊆ X := by
  refine ⟨exposureTupleSteps cutoff Ws, V, rfl, ?_⟩
  rw [smallStepExposureUnion_exposureTupleSteps]
  exact Finset.union_subset (exposureTupleUnion_subset hWs) hV

lemma iteratedSmallFragments_append_singleton
    (H : Finset (Finset α)) (steps : List (ℕ × Finset α))
    (step : ℕ × Finset α) :
    iteratedSmallFragments H (steps ++ [step]) =
      smallMinimalFragments step.1 (iteratedSmallFragments H steps) step.2 := by
  induction steps generalizing H with
  | nil =>
      simp [iteratedSmallFragments]
  | cons head steps ih =>
      simp [iteratedSmallFragments, ih]

lemma smallMinimalFragments_subset_ground
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ} {W : Finset α}
    (hHX : ∀ S ∈ H, S ⊆ X) :
    ∀ T ∈ smallMinimalFragments m H W, T ⊆ X := by
  intro T hT x hx
  rcases mem_smallMinimalFragments.mp hT with ⟨hTmin, _hsmall⟩
  rcases mem_fragmentFamily.mp
      (minimalFragments_subset_fragmentFamily H W hTmin) with
    ⟨S, hS, rfl⟩
  exact hHX S hS (Finset.mem_sdiff.mp hx).1

lemma smallMinimalFragments_card_le_of_forall_card_le
    {H : Finset (Finset α)} {m ℓ : ℕ} {W : Finset α}
    (hH : ∀ S ∈ H, S.card ≤ ℓ) :
    ∀ T ∈ smallMinimalFragments m H W, T.card ≤ ℓ := by
  intro T hT
  exact minimalFragments_card_le_of_forall_card_le hH
    (mem_smallMinimalFragments.mp hT).1

lemma iteratedSmallFragments_subset_ground
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α))
    (hHX : ∀ S ∈ H, S ⊆ X) :
    ∀ T ∈ iteratedSmallFragments H steps, T ⊆ X := by
  induction steps generalizing H with
  | nil =>
      simpa [iteratedSmallFragments] using hHX
  | cons step steps ih =>
      simpa [iteratedSmallFragments] using
        ih (H := smallMinimalFragments step.1 H step.2)
          (smallMinimalFragments_subset_ground (X := X) hHX)

lemma iteratedSmallFragments_card_le_of_forall_card_le
    (H : Finset (Finset α)) (steps : List (ℕ × Finset α)) {ℓ : ℕ}
    (hH : ∀ S ∈ H, S.card ≤ ℓ) :
    ∀ T ∈ iteratedSmallFragments H steps, T.card ≤ ℓ := by
  induction steps generalizing H with
  | nil =>
      simpa [iteratedSmallFragments] using hH
  | cons step steps ih =>
      simpa [iteratedSmallFragments] using
        ih (H := smallMinimalFragments step.1 H step.2)
          (smallMinimalFragments_card_le_of_forall_card_le hH)

lemma iteratedLargeCostSum_nonneg
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) {p : ℝ} (hp0 : 0 ≤ p) :
    0 ≤ iteratedLargeCostSum X p H steps := by
  induction steps generalizing H with
  | nil =>
      simp [iteratedLargeCostSum]
  | cons step steps ih =>
      have hcost :
          0 ≤ coverCost X (largeMinimalFragments step.1 H step.2) p :=
        coverCost_nonneg hp0
      have hrest :
          0 ≤ iteratedLargeCostSum X p
            (smallMinimalFragments step.1 H step.2) steps :=
        ih (H := smallMinimalFragments step.1 H step.2)
      simpa [iteratedLargeCostSum] using add_nonneg hcost hrest

lemma iteratedLargeCostSum_append_singleton
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) (step : ℕ × Finset α) {p : ℝ} :
    iteratedLargeCostSum X p H (steps ++ [step]) =
      iteratedLargeCostSum X p H steps +
        coverCost X
          (largeMinimalFragments step.1 (iteratedSmallFragments H steps) step.2) p := by
  induction steps generalizing H with
  | nil =>
      simp [iteratedLargeCostSum, iteratedSmallFragments]
  | cons head steps ih =>
      simp [iteratedLargeCostSum, iteratedSmallFragments, ih, add_assoc]

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_snoc
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ} {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin n → Finset α)
    (W : Finset α) :
    iteratedLargeCostSum X p H
        (exposureTupleStepsSnoc cutoff
          (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W)) =
      iteratedLargeCostSum X p H
        (exposureTupleStepsSnoc
          (fun i : Fin n => cutoff i.castSucc) Ws) +
        coverCost X
          (largeMinimalFragments (cutoff (Fin.last n))
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) W) p := by
  rw [exposureTupleStepsSnoc_snoc]
  simpa using
    iteratedLargeCostSum_append_singleton
      (X := X) (H := H)
      (steps := exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws)
      (step := (cutoff (Fin.last n), W)) (p := p)

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ} {n : ℕ}
    (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ) :
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ω)) =
      ∑ W ∈ X.powerset,
        ∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
              bernoulliMass X W (ρ (Fin.last n))) *
            (iteratedLargeCostSum X p H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
              coverCost X
                (largeMinimalFragments (cutoff (Fin.last n))
                  (iteratedSmallFragments H
                    (exposureTupleStepsSnoc
                      (fun i : Fin n => cutoff i.castSucc) Ws)) W) p) := by
  classical
  let e : Finset α × (Fin n → Finset α) ↪
      (Fin (n + 1) → Finset α) :=
    (Fin.snocEquiv (fun _ : Fin (n + 1) => Finset α)).toEmbedding
  calc
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ω))
        = ∑ P ∈ (X.powerset ×ˢ exposureTupleSpace X n),
            exposureTupleWeight X ρ (e P) *
              iteratedLargeCostSum X p H
                (exposureTupleStepsSnoc cutoff (e P)) := by
            rw [exposureTupleSpace_snoc X n, Finset.sum_map]
    _ = ∑ W ∈ X.powerset,
        ∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
              bernoulliMass X W (ρ (Fin.last n))) *
            (iteratedLargeCostSum X p H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
              coverCost X
                (largeMinimalFragments (cutoff (Fin.last n))
                  (iteratedSmallFragments H
                    (exposureTupleStepsSnoc
                      (fun i : Fin n => cutoff i.castSucc) Ws)) W) p) := by
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl ?_
          intro W _hW
          refine Finset.sum_congr rfl ?_
          intro Ws _hWs
          change
            exposureTupleWeight X ρ
                (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) *
              iteratedLargeCostSum X p H
                (exposureTupleStepsSnoc cutoff
                  (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W)) =
            (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
                bernoulliMass X W (ρ (Fin.last n))) *
              (iteratedLargeCostSum X p H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws) +
                coverCost X
                  (largeMinimalFragments (cutoff (Fin.last n))
                    (iteratedSmallFragments H
                      (exposureTupleStepsSnoc
                        (fun i : Fin n => cutoff i.castSucc) Ws)) W) p)
          rw [exposureTupleWeight_snoc,
            iteratedLargeCostSum_exposureTupleStepsSnoc_snoc]

lemma bernoulli_average_iterated_final_largeCost_le_muP_mul_two_pow_inv
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q ρlast : ℝ} {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin n → Finset α)
    (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρlast : ρlast = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρlast *
        coverCost X
          (largeMinimalFragments (cutoff (Fin.last n))
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) W) q) ≤
      muP X
        (upClosureIn X
          (iteratedSmallFragments H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws))) ρlast *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)) := by
  exact bernoulli_average_largeCost_le_muP_mul_two_pow_inv
    X
    (iteratedSmallFragments H
      (exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws))
    (cutoff (Fin.last n)) ell L hL hq0 hq1 hρlast
    (iteratedSmallFragments_subset_ground X H
      (exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws) hHX)
    (iteratedSmallFragments_card_le_of_forall_card_le H
      (exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws) hHbound)

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_of_final_average_le
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ} {n : ℕ}
    (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ)
    (B : (Fin n → Finset α) → ℝ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hfinal :
      ∀ Ws ∈ exposureTupleSpace X n,
        (∑ W ∈ X.powerset,
          bernoulliMass X W (ρ (Fin.last n)) *
            coverCost X
              (largeMinimalFragments (cutoff (Fin.last n))
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)) W) p) ≤
          B Ws) :
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ω)) ≤
      ∑ Ws ∈ exposureTupleSpace X n,
        (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
            iteratedLargeCostSum X p H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws) +
          exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws * B Ws) := by
  classical
  rw [iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum ?_
  intro Ws hWs
  let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
  let ρlast : ℝ := ρ (Fin.last n)
  let loss : ℝ :=
    iteratedLargeCostSum X p H
      (exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws)
  let finalCost : Finset α → ℝ := fun W =>
    coverCost X
      (largeMinimalFragments (cutoff (Fin.last n))
        (iteratedSmallFragments H
          (exposureTupleStepsSnoc
            (fun i : Fin n => cutoff i.castSucc) Ws)) W) p
  let wt : ℝ := exposureTupleWeight X ρtail Ws
  have hwt0 : 0 ≤ wt := by
    dsimp [wt, ρtail]
    exact exposureTupleWeight_nonneg X
      (fun i : Fin n => hρ0 i.castSucc)
      (fun i : Fin n => hρ1 i.castSucc) Ws
  have hinner_eq :
      (∑ W ∈ X.powerset,
        (wt * bernoulliMass X W ρlast) * (loss + finalCost W)) =
        wt * loss +
          wt * (∑ W ∈ X.powerset,
            bernoulliMass X W ρlast * finalCost W) := by
    calc
      (∑ W ∈ X.powerset,
        (wt * bernoulliMass X W ρlast) * (loss + finalCost W))
          = ∑ W ∈ X.powerset,
            (  bernoulliMass X W ρlast * (wt * loss) +
                wt * (bernoulliMass X W ρlast * finalCost W)) := by
              refine Finset.sum_congr rfl ?_
              intro W _hW
              ring
      _ = (∑ W ∈ X.powerset, bernoulliMass X W ρlast) * (wt * loss) +
            wt * (∑ W ∈ X.powerset,
              bernoulliMass X W ρlast * finalCost W) := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      _ = wt * loss +
            wt * (∑ W ∈ X.powerset,
              bernoulliMass X W ρlast * finalCost W) := by
              rw [sum_bernoulliMass_eq_one (α := α) X (p := ρlast) (by ring)]
              ring
  calc
    (∑ W ∈ X.powerset,
      (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
          bernoulliMass X W (ρ (Fin.last n))) *
        (iteratedLargeCostSum X p H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws) +
          coverCost X
            (largeMinimalFragments (cutoff (Fin.last n))
              (iteratedSmallFragments H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws)) W) p))
        = wt * loss +
          wt * (∑ W ∈ X.powerset,
            bernoulliMass X W ρlast * finalCost W) := by
            simpa [wt, loss, finalCost, ρtail, ρlast] using hinner_eq
    _ ≤ wt * loss + wt * B Ws := by
          have hmul_le :
              wt * (∑ W ∈ X.powerset,
                bernoulliMass X W ρlast * finalCost W) ≤ wt * B Ws :=
            mul_le_mul_of_nonneg_left (by
              simpa [finalCost, ρlast] using hfinal Ws hWs) hwt0
          linarith
    _ = exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
          iteratedLargeCostSum X p H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws) +
        exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws * B Ws := by
          simp [wt, loss, ρtail]

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_muP_final
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q : ℝ} {n : ℕ}
    (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρlast : ρ (Fin.last n) = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
      ∑ Ws ∈ exposureTupleSpace X n,
        (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws) +
          exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
            (muP X
              (upClosureIn X
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)))
                (ρ (Fin.last n)) *
              ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)))) := by
  refine
    iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_of_final_average_le
      X H ρ cutoff
      (fun Ws =>
        muP X
          (upClosureIn X
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)))
          (ρ (Fin.last n)) *
          ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)))
      hρ0 hρ1 ?_
  intro Ws _hWs
  exact bernoulli_average_iterated_final_largeCost_le_muP_mul_two_pow_inv
    X H ell L cutoff Ws hL hq0 hq1 hρlast hHX hHbound

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_tail_add_budget
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q : ℝ} {n : ℕ}
    (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρlast : ρ (Fin.last n) = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
      (∑ Ws ∈ exposureTupleSpace X n,
        exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
          iteratedLargeCostSum X q H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws)) +
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)) := by
  classical
  let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
  let C : ℝ := (2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbase :=
    iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_muP_final
      X H ell L ρ cutoff hρ0 hρ1 hL hq0 hq1 hρlast hHX hHbound
  have hsum_le :
      (∑ Ws ∈ exposureTupleSpace X n,
        (exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws) +
          exposureTupleWeight X ρtail Ws *
            (muP X
              (upClosureIn X
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)))
                (ρ (Fin.last n)) * C))) ≤
        ∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
            exposureTupleWeight X ρtail Ws * C) := by
    refine Finset.sum_le_sum ?_
    intro Ws _hWs
    have hwt0 : 0 ≤ exposureTupleWeight X ρtail Ws := by
      dsimp [ρtail]
      exact exposureTupleWeight_nonneg X
        (fun i : Fin n => hρ0 i.castSucc)
        (fun i : Fin n => hρ1 i.castSucc) Ws
    have hmu_le :
        muP X
          (upClosureIn X
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)))
          (ρ (Fin.last n)) ≤ 1 :=
      muP_le_one (hρ0 (Fin.last n)) (hρ1 (Fin.last n))
    have hmuC_le :
        muP X
          (upClosureIn X
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)))
          (ρ (Fin.last n)) * C ≤ C := by
      have := mul_le_mul_of_nonneg_right hmu_le hC0
      simpa using this
    have hterm :
        exposureTupleWeight X ρtail Ws *
            (muP X
              (upClosureIn X
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)))
              (ρ (Fin.last n)) * C) ≤
          exposureTupleWeight X ρtail Ws * C :=
      mul_le_mul_of_nonneg_left hmuC_le hwt0
    have h := add_le_add_right hterm
      (exposureTupleWeight X ρtail Ws *
        iteratedLargeCostSum X q H
          (exposureTupleStepsSnoc
            (fun i : Fin n => cutoff i.castSucc) Ws))
    simpa [add_comm, add_left_comm, add_assoc] using h
  have hsum_eq :
      (∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
            exposureTupleWeight X ρtail Ws * C)) =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) + C := by
    calc
      (∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
            exposureTupleWeight X ρtail Ws * C))
          =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) +
          ∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws * C := by
            rw [Finset.sum_add_distrib]
      _ =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) +
          (∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws) * C := by
            rw [Finset.sum_mul]
      _ =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) + C := by
            rw [sum_exposureTupleWeight_eq_one X ρtail]
            ring
  exact hbase.trans (hsum_le.trans_eq hsum_eq)

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_tail_add_budget_of_current_bound
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q : ℝ} {n : ℕ}
    (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρlast : ρ (Fin.last n) = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hCurrentBound :
      ∀ Ws ∈ exposureTupleSpace X n,
        ∀ S ∈ iteratedSmallFragments H
          (exposureTupleStepsSnoc
            (fun i : Fin n => cutoff i.castSucc) Ws),
          S.card ≤ ell) :
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
      (∑ Ws ∈ exposureTupleSpace X n,
        exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
          iteratedLargeCostSum X q H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws)) +
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)) := by
  classical
  let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
  let C : ℝ := (2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hfinal :
      ∀ Ws ∈ exposureTupleSpace X n,
        (∑ W ∈ X.powerset,
          bernoulliMass X W (ρ (Fin.last n)) *
            coverCost X
              (largeMinimalFragments (cutoff (Fin.last n))
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)) W) q) ≤
          C := by
    intro Ws hWs
    have hlarge :
        (∑ W ∈ X.powerset,
          bernoulliMass X W (ρ (Fin.last n)) *
            coverCost X
              (largeMinimalFragments (cutoff (Fin.last n))
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)) W) q) ≤
          muP X
            (upClosureIn X
              (iteratedSmallFragments H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws)))
            (ρ (Fin.last n)) * C := by
      simpa [C] using
        bernoulli_average_largeCost_le_muP_mul_two_pow_inv
          X
          (iteratedSmallFragments H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws))
          (cutoff (Fin.last n)) ell L hL hq0 hq1 hρlast
          (iteratedSmallFragments_subset_ground X H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws) hHX)
          (hCurrentBound Ws hWs)
    have hmu_le :
        muP X
          (upClosureIn X
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)))
          (ρ (Fin.last n)) ≤ 1 :=
      muP_le_one (hρ0 (Fin.last n)) (hρ1 (Fin.last n))
    have hmuC_le :
        muP X
          (upClosureIn X
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)))
          (ρ (Fin.last n)) * C ≤ C := by
      have := mul_le_mul_of_nonneg_right hmu_le hC0
      simpa using this
    exact hlarge.trans hmuC_le
  have hbase :=
    iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_of_final_average_le
      X H ρ cutoff (fun _Ws => C) hρ0 hρ1 hfinal
  have hsum_eq :
      (∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
            exposureTupleWeight X ρtail Ws * C)) =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) + C := by
    calc
      (∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
            exposureTupleWeight X ρtail Ws * C))
          =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) +
          ∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws * C := by
            rw [Finset.sum_add_distrib]
      _ =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) +
          (∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws) * C := by
            rw [Finset.sum_mul]
      _ =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) + C := by
            rw [sum_exposureTupleWeight_eq_one X ρtail]
            ring
  exact hbase.trans_eq hsum_eq

lemma iteratedSmallFragments_exposureTupleStepsSnoc_card_lt_last
    (H : Finset (Finset α)) {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin (n + 1) → Finset α) :
    ∀ T ∈ iteratedSmallFragments H (exposureTupleStepsSnoc cutoff Ws),
      T.card < cutoff (Fin.last n) := by
  intro T hT
  rw [exposureTupleStepsSnoc, iteratedSmallFragments_append_singleton] at hT
  exact (mem_smallMinimalFragments.mp hT).2

lemma iteratedSmallFragments_exposureTupleStepsSnoc_card_le_last
    (H : Finset (Finset α)) {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin (n + 1) → Finset α) :
    ∀ T ∈ iteratedSmallFragments H (exposureTupleStepsSnoc cutoff Ws),
      T.card ≤ cutoff (Fin.last n) := by
  intro T hT
  exact Nat.le_of_lt
    (iteratedSmallFragments_exposureTupleStepsSnoc_card_lt_last H cutoff Ws T hT)

/-- Cardinality bound available just before the last snoc stage.  If there is
no previous stage, this is the original bound `ell`; otherwise it is the cutoff
from the previous small-fragment step. -/
def snocCurrentCardBound :
    {n : ℕ} → ℕ → (Fin n → ℕ) → ℕ
  | 0, ell, _cutoff => ell
  | n + 1, _ell, cutoff => cutoff (Fin.last n)

/-- Recursive large-fragment budget for a snoc-ordered exposure tuple, charging
each stage against the cardinality bound available immediately before that
stage. -/
noncomputable def snocLargeCostBudget :
    {n : ℕ} → ℕ → (Fin n → ℕ) → (Fin n → ℕ) → ℝ
  | 0, _ell, _cutoff, _L => 0
  | n + 1, ell, cutoff, L =>
      snocLargeCostBudget ell
        (fun i : Fin n => cutoff i.castSucc)
        (fun i : Fin n => L i.castSucc) +
        (2 : ℝ) ^
            snocCurrentCardBound ell
              (fun i : Fin n => cutoff i.castSucc) *
          (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_le_snocLargeCostBudget
    (X : Finset α) (H : Finset (Finset α)) (ell : ℕ)
    {q : ℝ} {n : ℕ}
    (ρ : Fin n → ℝ) (cutoff L : Fin n → ℕ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hL : ∀ i, 1 ≤ L i) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ∀ i, ρ i = 1 - (1 - q) ^ L i)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ Ws ∈ exposureTupleSpace X n,
      exposureTupleWeight X ρ Ws *
        iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ws)) ≤
      snocLargeCostBudget ell cutoff L := by
  classical
  induction n with
  | zero =>
      simp [snocLargeCostBudget, exposureTupleSpace, exposureTupleWeight,
        exposureTupleStepsSnoc, iteratedLargeCostSum]
  | succ n ih =>
      let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
      let cutoffTail : Fin n → ℕ := fun i => cutoff i.castSucc
      let Ltail : Fin n → ℕ := fun i => L i.castSucc
      have htail :
          (∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc cutoffTail Ws)) ≤
            snocLargeCostBudget ell cutoffTail Ltail := by
        exact ih ρtail cutoffTail Ltail
          (fun i => hρ0 i.castSucc)
          (fun i => hρ1 i.castSucc)
          (fun i => hL i.castSucc)
          (fun i => hρ i.castSucc)
      have hCurrentBound :
          ∀ Ws ∈ exposureTupleSpace X n,
            ∀ S ∈ iteratedSmallFragments H
              (exposureTupleStepsSnoc cutoffTail Ws),
              S.card ≤ snocCurrentCardBound ell cutoffTail := by
        cases n with
        | zero =>
            intro Ws _hWs S hS
            simpa [snocCurrentCardBound, exposureTupleStepsSnoc,
              iteratedSmallFragments] using hHbound S hS
        | succ m =>
            intro Ws _hWs S hS
            exact
              iteratedSmallFragments_exposureTupleStepsSnoc_card_le_last
                H cutoffTail Ws S hS
      have hsnoc :
          (∑ Ω ∈ exposureTupleSpace X (n + 1),
            exposureTupleWeight X ρ Ω *
              iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
            (∑ Ws ∈ exposureTupleSpace X n,
              exposureTupleWeight X ρtail Ws *
                iteratedLargeCostSum X q H
                  (exposureTupleStepsSnoc cutoffTail Ws)) +
              ((2 : ℝ) ^ snocCurrentCardBound ell cutoffTail *
                (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)) := by
        exact
          iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_tail_add_budget_of_current_bound
            X H (snocCurrentCardBound ell cutoffTail) (L (Fin.last n))
            ρ cutoff hρ0 hρ1 (hL (Fin.last n)) hq0 hq1
            (hρ (Fin.last n)) hHX hCurrentBound
      have hadd := add_le_add_right htail
        ((2 : ℝ) ^ snocCurrentCardBound ell cutoffTail *
          (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n))
      exact hsnoc.trans (by
        simpa [snocLargeCostBudget, cutoffTail, Ltail, add_comm,
          add_left_comm, add_assoc] using hadd)

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_le_budget_sum
    (X : Finset α) (H : Finset (Finset α)) (ell : ℕ)
    {q : ℝ} {n : ℕ}
    (ρ : Fin n → ℝ) (cutoff L : Fin n → ℕ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hL : ∀ i, 1 ≤ L i) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ∀ i, ρ i = 1 - (1 - q) ^ L i)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ Ws ∈ exposureTupleSpace X n,
      exposureTupleWeight X ρ Ws *
        iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ws)) ≤
      ∑ i : Fin n, (2 : ℝ) ^ ell * (1 / (L i : ℝ)) ^ cutoff i := by
  classical
  induction n with
  | zero =>
      simp [exposureTupleSpace, exposureTupleWeight, exposureTupleStepsSnoc,
        iteratedLargeCostSum]
  | succ n ih =>
      let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
      let cutoffTail : Fin n → ℕ := fun i => cutoff i.castSucc
      let Ltail : Fin n → ℕ := fun i => L i.castSucc
      have htail :
          (∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc cutoffTail Ws)) ≤
            ∑ i : Fin n,
              (2 : ℝ) ^ ell * (1 / (Ltail i : ℝ)) ^ cutoffTail i := by
        exact ih ρtail cutoffTail Ltail
          (fun i => hρ0 i.castSucc)
          (fun i => hρ1 i.castSucc)
          (fun i => hL i.castSucc)
          (fun i => hρ i.castSucc)
      have hsnoc :
          (∑ Ω ∈ exposureTupleSpace X (n + 1),
            exposureTupleWeight X ρ Ω *
              iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
            (∑ Ws ∈ exposureTupleSpace X n,
              exposureTupleWeight X ρtail Ws *
                iteratedLargeCostSum X q H
                  (exposureTupleStepsSnoc cutoffTail Ws)) +
              ((2 : ℝ) ^ ell *
                (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)) := by
        exact iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_tail_add_budget
          X H ell (L (Fin.last n)) ρ cutoff hρ0 hρ1
          (hL (Fin.last n)) hq0 hq1 (hρ (Fin.last n)) hHX hHbound
      have hcombined :
          (∑ Ω ∈ exposureTupleSpace X (n + 1),
            exposureTupleWeight X ρ Ω *
              iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
            (∑ i : Fin n,
              (2 : ℝ) ^ ell * (1 / (Ltail i : ℝ)) ^ cutoffTail i) +
              ((2 : ℝ) ^ ell *
                (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)) := by
        have hadd := add_le_add_right htail
          ((2 : ℝ) ^ ell *
            (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n))
        exact hsnoc.trans (by
          simpa [add_comm, add_left_comm, add_assoc] using hadd)
      have hsum :
          (∑ i : Fin (n + 1),
              (2 : ℝ) ^ ell * (1 / (L i : ℝ)) ^ cutoff i) =
            (∑ i : Fin n,
              (2 : ℝ) ^ ell * (1 / (Ltail i : ℝ)) ^ cutoffTail i) +
              ((2 : ℝ) ^ ell *
                (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)) := by
        rw [Fin.sum_univ_castSucc]
      exact hcombined.trans_eq hsum.symm

lemma exists_source_subset_union_of_iteratedSmallFragment_subset
    {H : Finset (Finset α)} {steps : List (ℕ × Finset α)} {V : Finset α}
    (h : ∃ T ∈ iteratedSmallFragments H steps, T ⊆ V) :
    ∃ S ∈ H, S ⊆ smallStepExposureUnion steps ∪ V := by
  induction steps generalizing H V with
  | nil =>
      simpa [iteratedSmallFragments, smallStepExposureUnion] using h
  | cons step steps ih =>
      rcases ih (H := smallMinimalFragments step.1 H step.2) h with
        ⟨R, hRsmall, hRsub⟩
      have hRmin : R ∈ minimalFragments H step.2 :=
        (mem_smallMinimalFragments.mp hRsmall).1
      rcases exists_source_subset_union_of_minimalFragment_subset
          (H := H) (W := step.2)
          (V := smallStepExposureUnion steps ∪ V)
          ⟨R, hRmin, hRsub⟩ with
        ⟨S, hS, hSsub⟩
      exact ⟨S, hS, by
        simpa [smallStepExposureUnion, Finset.union_assoc] using hSsub⟩

lemma coverCost_le_iteratedSmallFragments_add_largeCostSum
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) {p : ℝ} (hp0 : 0 ≤ p) :
    coverCost X H p ≤
      coverCost X (iteratedSmallFragments H steps) p +
        iteratedLargeCostSum X p H steps := by
  induction steps generalizing H with
  | nil =>
      simp [iteratedSmallFragments, iteratedLargeCostSum]
  | cons step steps ih =>
      let H' : Finset (Finset α) :=
        smallMinimalFragments step.1 H step.2
      let L : Finset (Finset α) :=
        largeMinimalFragments step.1 H step.2
      have hstep :
          coverCost X H p ≤ coverCost X H' p + coverCost X L p := by
        simpa [H', L] using
          coverCost_le_small_add_large_minimalFragments
            X step.1 H step.2 hp0
      have hih :
          coverCost X H' p ≤
            coverCost X (iteratedSmallFragments H' steps) p +
              iteratedLargeCostSum X p H' steps :=
        ih (H := H')
      have hcombine :
          coverCost X H' p + coverCost X L p ≤
            coverCost X (iteratedSmallFragments H' steps) p +
              (coverCost X L p + iteratedLargeCostSum X p H' steps) := by
        linarith
      exact hstep.trans (by
        simpa [iteratedSmallFragments, iteratedLargeCostSum, H', L,
          add_assoc, add_comm, add_left_comm] using hcombine)

lemma coverCost_iteratedSmallFragments_pos_of_largeCostSum_lt
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) {p : ℝ} (hp0 : 0 ≤ p)
    (hloss : iteratedLargeCostSum X p H steps < coverCost X H p) :
    0 < coverCost X (iteratedSmallFragments H steps) p := by
  have hle :=
    coverCost_le_iteratedSmallFragments_add_largeCostSum
      X H steps hp0
  linarith

lemma exists_source_subset_union_of_iteratedSmallCost_pos_append_one
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) (V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hpos :
      0 < coverCost X (iteratedSmallFragments H (steps ++ [(1, V)])) p) :
    ∃ S ∈ H, S ⊆ smallStepExposureUnion steps ∪ V := by
  have hpos' :
      0 < coverCost X
        (smallMinimalFragments 1 (iteratedSmallFragments H steps) V) p := by
    simpa [iteratedSmallFragments_append_singleton] using hpos
  rcases
      (coverCost_smallMinimalFragments_one_pos_iff_exists_subset
        X (iteratedSmallFragments H steps) V hp0).mp hpos' with
    ⟨T, hT, hTV⟩
  exact exists_source_subset_union_of_iteratedSmallFragment_subset
    (H := H) (steps := steps) (V := V) ⟨T, hT, hTV⟩

lemma exists_source_subset_union_of_largeCostSum_lt_append_one
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) (V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hloss :
      iteratedLargeCostSum X p H (steps ++ [(1, V)]) < coverCost X H p) :
    ∃ S ∈ H, S ⊆ smallStepExposureUnion steps ∪ V := by
  have hpos :
      0 < coverCost X (iteratedSmallFragments H (steps ++ [(1, V)])) p :=
    coverCost_iteratedSmallFragments_pos_of_largeCostSum_lt
      X H (steps ++ [(1, V)]) hp0 hloss
  exact exists_source_subset_union_of_iteratedSmallCost_pos_append_one
    X H steps V hp0 hpos

lemma exposureUnion_mem_upClosureIn_of_largeCostSum_lt_append_one
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) (V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hUnionX : smallStepExposureUnion steps ∪ V ⊆ X)
    (hloss :
      iteratedLargeCostSum X p H (steps ++ [(1, V)]) < coverCost X H p) :
    smallStepExposureUnion steps ∪ V ∈ upClosureIn X H := by
  rcases exists_source_subset_union_of_largeCostSum_lt_append_one
      X H steps V hp0 hloss with
    ⟨S, hS, hSsub⟩
  exact mem_upClosureIn.mpr ⟨hUnionX, S, hS, hSsub⟩

/-- One-step endpoint of the deterministic iteration: if the cutoff-`1`
large-fragment loss after exposing `V` is smaller than the original cover cost,
then `V` already lies in the upper closure generated by `H`. -/
lemma exposure_mem_upClosureIn_of_largeCost_lt
    (X : Finset α) (H : Finset (Finset α)) (V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p) (hVX : V ⊆ X)
    (hloss :
      coverCost X (largeMinimalFragments 1 H V) p < coverCost X H p) :
    V ∈ upClosureIn X H := by
  have hUnionX : smallStepExposureUnion ([] : List (ℕ × Finset α)) ∪ V ⊆ X := by
    simpa [smallStepExposureUnion] using hVX
  have hloss' :
      iteratedLargeCostSum X p H (([] : List (ℕ × Finset α)) ++ [(1, V)]) <
        coverCost X H p := by
    simpa [iteratedLargeCostSum] using hloss
  simpa [smallStepExposureUnion] using
    exposureUnion_mem_upClosureIn_of_largeCostSum_lt_append_one
      X H ([] : List (ℕ × Finset α)) V hp0 hUnionX hloss'

/-- Probabilistic one-step endpoint: if the large-fragment expectation estimate
is below the original cover cost at cutoff `1`, then some exposure in the
ground cube lies in the upper closure. -/
lemma exists_exposure_mem_upClosureIn_of_muP_mul_two_pow_inv_lt
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell)
    (hbound :
      muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ))) < coverCost X H q) :
    ∃ W ∈ X.powerset, W ∈ upClosureIn X H := by
  rcases exists_exposure_largeCost_lt_of_muP_mul_two_pow_inv_lt
      X H 1 ell L hL hq0 hq1 hρ hHX hHbound (by
        simpa using hbound) with
    ⟨W, hWX, hloss⟩
  exact ⟨W, hWX,
    exposure_mem_upClosureIn_of_largeCost_lt X H W hq0.le
      (Finset.mem_powerset.mp hWX) hloss⟩

/-- One-step Markov bridge: if the expected cutoff-`1` large-fragment loss is
less than half the original cover cost, then the upper closure already has
Bernoulli measure greater than `1/2`. -/
lemma half_lt_muP_of_average_largeCost_lt_half_coverCost
    (X : Finset α) (H : Finset (Finset α)) {q ρ : ℝ}
    (hq0 : 0 < q) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hcost_pos : 0 < coverCost X H q)
    (havg :
      (∑ W ∈ X.powerset,
        bernoulliMass X W ρ *
          coverCost X (largeMinimalFragments 1 H W) q) <
        coverCost X H q * (1 / 2)) :
    (1 / 2 : ℝ) < muP X (upClosureIn X H) ρ := by
  refine half_lt_muP_of_average_lt_half_of_bad_le
    X (upClosureIn X H)
    (fun W => coverCost X (largeMinimalFragments 1 H W) q)
    hρ0 hρ1 hcost_pos ?_ ?_ havg
  · intro W _hWX
    exact coverCost_nonneg hq0.le
  · intro W hWX hWnot
    exact le_of_not_gt fun hloss =>
      hWnot (exposure_mem_upClosureIn_of_largeCost_lt
        X H W hq0.le (Finset.mem_powerset.mp hWX) hloss)

/-- One-step Park--Vondrak bridge using the proved large-fragment expectation
estimate.  This is intentionally a weak one-step corollary; the full
Kahn--Kalai proof needs the multi-step version with geometrically decreasing
cutoffs. -/
lemma half_lt_muP_of_muP_mul_two_pow_inv_lt_half_coverCost
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell)
    (hcost_pos : 0 < coverCost X H q)
    (hbound :
      muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ))) <
          coverCost X H q * (1 / 2)) :
    (1 / 2 : ℝ) < muP X (upClosureIn X H) ρ := by
  have hρ0 : 0 ≤ ρ := by
    have hρpos : 0 < ρ := by
      simpa [hρ] using one_sub_one_sub_q_pow_pos hL hq0 hq1
    exact hρpos.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]
    have hpow_nonneg : 0 ≤ (1 - q) ^ L := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
    linarith
  have havg_lt :
      (∑ W ∈ X.powerset,
        bernoulliMass X W ρ *
          coverCost X (largeMinimalFragments 1 H W) q) <
        coverCost X H q * (1 / 2) :=
    (bernoulli_average_largeCost_le_muP_mul_two_pow_inv
      X H 1 ell L hL hq0 hq1 hρ hHX hHbound).trans_lt (by
        simpa using hbound)
  exact half_lt_muP_of_average_largeCost_lt_half_coverCost
    X H hq0 hρ0 hρ1 hcost_pos havg_lt

lemma half_lt_coverCost_of_not_pSmall_upClosureIn
    {X : Finset α} {H : Finset (Finset α)} {q : ℝ}
    (hq0 : 0 ≤ q) (hHX : ∀ S ∈ H, S ⊆ X)
    (hNotSmall : ¬ pSmall X (upClosureIn X H) q) :
    (1 / 2 : ℝ) < coverCost X H q := by
  have hNotSmallH : ¬ pSmall X H q :=
    (not_pSmall_upClosureIn_iff hHX).mp hNotSmall
  exact (not_pSmall_iff_half_lt_coverCost hq0 hHX).mp hNotSmallH

/-- One-step Park--Vondrak threshold corollary from non-smallness.  Since
`¬ pSmall` gives cover cost larger than `1/2`, an expected large-fragment
loss below `1/4` is enough for Markov's inequality. -/
lemma half_lt_muP_of_not_pSmall_upClosureIn_muP_mul_two_pow_inv_lt_quarter
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell)
    (hNotSmall : ¬ pSmall X (upClosureIn X H) q)
    (hbound :
      muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ))) < (1 / 4 : ℝ)) :
    (1 / 2 : ℝ) < muP X (upClosureIn X H) ρ := by
  have hcost_half :
      (1 / 2 : ℝ) < coverCost X H q :=
    half_lt_coverCost_of_not_pSmall_upClosureIn hq0.le hHX hNotSmall
  have hcost_pos : 0 < coverCost X H q := by linarith
  have hbudget :
      muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ))) <
          coverCost X H q * (1 / 2) := by
    nlinarith
  exact half_lt_muP_of_muP_mul_two_pow_inv_lt_half_coverCost
    X H ell L hL hq0 hq1 hρ hHX hHbound hcost_pos hbudget

/-- Abstract multi-outcome Park--Vondrak Markov bridge.  The outcome space is
kept arbitrary so the later proof can instantiate it with independent exposure
tuples.  Each outcome must end with a cutoff-`1` exposure; if the accumulated
loss has expectation below half the initial cover cost, then the endpoint
upper-closure event has weight greater than `1/2`. -/
lemma half_lt_weighted_endpoint_of_iteratedLargeCost_average_lt
    {Ω : Type*} [DecidableEq Ω]
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
    (s : Finset Ω) (weight : Ω → ℝ)
    (stepsOf : Ω → List (ℕ × Finset α))
    (hp0 : 0 ≤ p)
    (hcost_pos : 0 < coverCost X H p)
    (hweight_nonneg : ∀ ω ∈ s, 0 ≤ weight ω)
    (hsum_weight : (∑ ω ∈ s, weight ω) = 1)
    (hshape :
      ∀ ω ∈ s,
        ∃ steps V,
          stepsOf ω = steps ++ [(1, V)] ∧
          smallStepExposureUnion steps ∪ V ⊆ X)
    (havg :
      (∑ ω ∈ s,
        weight ω * iteratedLargeCostSum X p H (stepsOf ω)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) <
      ∑ ω ∈ s.filter
        (fun ω => smallStepExposureUnion (stepsOf ω) ∈ upClosureIn X H),
        weight ω := by
  refine half_lt_weighted_good_of_average_lt_half_of_bad_le
    s weight
    (fun ω => smallStepExposureUnion (stepsOf ω) ∈ upClosureIn X H)
    (fun ω => iteratedLargeCostSum X p H (stepsOf ω))
    hweight_nonneg hsum_weight hcost_pos ?_ ?_ havg
  · intro ω _hωs
    exact iteratedLargeCostSum_nonneg X H (stepsOf ω) hp0
  · intro ω hωs hbad
    rcases hshape ω hωs with ⟨steps, V, hsteps, hUnionX⟩
    exact le_of_not_gt fun hloss =>
      hbad (by
        have hmem :=
          exposureUnion_mem_upClosureIn_of_largeCostSum_lt_append_one
            X H steps V hp0 hUnionX (by
              simpa [hsteps] using hloss)
        simpa [hsteps, smallStepExposureUnion_append_singleton] using hmem)

/-- Exposure-tuple specialization of
`half_lt_weighted_endpoint_of_iteratedLargeCost_average_lt`. -/
lemma half_lt_exposureTuple_endpoint_of_iteratedLargeCost_average_lt
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
    {n : ℕ} (ρ : Fin n → ℝ)
    (stepsOf : (Fin n → Finset α) → List (ℕ × Finset α))
    (hp0 : 0 ≤ p)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hcost_pos : 0 < coverCost X H p)
    (hshape :
      ∀ Ws ∈ exposureTupleSpace X n,
        ∃ steps V,
          stepsOf Ws = steps ++ [(1, V)] ∧
          smallStepExposureUnion steps ∪ V ⊆ X)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X n,
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X p H (stepsOf Ws)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) <
      ∑ Ws ∈ (exposureTupleSpace X n).filter
        (fun Ws => smallStepExposureUnion (stepsOf Ws) ∈ upClosureIn X H),
        exposureTupleWeight X ρ Ws := by
  exact half_lt_weighted_endpoint_of_iteratedLargeCost_average_lt
    X H (exposureTupleSpace X n) (exposureTupleWeight X ρ) stepsOf
    hp0 hcost_pos
    (fun Ws _hWs => exposureTupleWeight_nonneg X hρ0 hρ1 Ws)
    (sum_exposureTupleWeight_eq_one X ρ)
    hshape havg

/-- Snoc-step exposure-tuple endpoint bridge.  If the final cutoff is `1` and
the accumulated large-fragment loss has expectation below half the initial
cover cost, then the tuple union lands in the upper closure with probability
greater than `1/2`. -/
lemma half_lt_exposureTupleUnion_of_iteratedLargeCostSnoc_average_lt
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
    {n : ℕ} (ρ : Fin (n + 1) → ℝ)
    (cutoff : Fin (n + 1) → ℕ)
    (hp0 : 0 ≤ p)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hcost_pos : 0 < coverCost X H p)
    (hlast : cutoff (Fin.last n) = 1)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ws)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) <
      ∑ Ws ∈ (exposureTupleSpace X (n + 1)).filter
        (fun Ws => exposureTupleUnion Ws ∈ upClosureIn X H),
        exposureTupleWeight X ρ Ws := by
  have hhalf :=
    half_lt_exposureTuple_endpoint_of_iteratedLargeCost_average_lt
      X H ρ (fun Ws => exposureTupleStepsSnoc cutoff Ws)
      hp0 hρ0 hρ1 hcost_pos
      (fun Ws hWs => exposureTupleStepsSnoc_last_shape hWs hlast)
      havg
  simpa [smallStepExposureUnion_exposureTupleStepsSnoc] using hhalf

/-- Snoc-step endpoint bridge converted to a `muP` conclusion once the
tuple-union distribution identity is available.  This lemma deliberately keeps
that identity as an explicit hypothesis, isolating the remaining probability
bookkeeping from the deterministic fragment iteration. -/
lemma half_lt_muP_of_iteratedLargeCostSnoc_average_lt_of_union_measure_eq
    (X : Finset α) (H : Finset (Finset α)) {p θ : ℝ}
    {n : ℕ} (ρ : Fin (n + 1) → ℝ)
    (cutoff : Fin (n + 1) → ℕ)
    (hp0 : 0 ≤ p)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hcost_pos : 0 < coverCost X H p)
    (hlast : cutoff (Fin.last n) = 1)
    (hmeasure :
      (∑ Ws ∈ (exposureTupleSpace X (n + 1)).filter
        (fun Ws => exposureTupleUnion Ws ∈ upClosureIn X H),
        exposureTupleWeight X ρ Ws) =
          muP X (upClosureIn X H) θ)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ws)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) < muP X (upClosureIn X H) θ := by
  have hhalf :=
    half_lt_exposureTupleUnion_of_iteratedLargeCostSnoc_average_lt
      X H ρ cutoff hp0 hρ0 hρ1 hcost_pos hlast havg
  rw [← hmeasure]
  simpa [upClosureIn] using hhalf

/-- Snoc-step endpoint bridge with the tuple-union distribution identity
already discharged. -/
lemma half_lt_muP_of_iteratedLargeCostSnoc_average_lt
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
    {n : ℕ} (ρ : Fin (n + 1) → ℝ)
    (cutoff : Fin (n + 1) → ℕ)
    (hp0 : 0 ≤ p)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hcost_pos : 0 < coverCost X H p)
    (hlast : cutoff (Fin.last n) = 1)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ws)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) <
      muP X (upClosureIn X H) (tupleUnionDensity ρ) := by
  exact half_lt_muP_of_iteratedLargeCostSnoc_average_lt_of_union_measure_eq
    X H ρ cutoff hp0 hρ0 hρ1 hcost_pos hlast
    (exposureTupleUnion_measure_eq_muP X (upClosureIn X H) ρ)
    havg

/-- Non-smallness-budget version of the snoc-step endpoint bridge.  Since
`¬ pSmall` gives cover cost greater than `1/2`, it is enough to bound the
expected accumulated large-fragment loss by `1/4`. -/
lemma half_lt_muP_of_not_pSmall_iteratedLargeCostSnoc_average_lt_quarter
    (X : Finset α) (H : Finset (Finset α)) {q : ℝ}
    {n : ℕ} (ρ : Fin (n + 1) → ℝ)
    (cutoff : Fin (n + 1) → ℕ)
    (hq0 : 0 < q)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hNotSmall : ¬ pSmall X (upClosureIn X H) q)
    (hlast : cutoff (Fin.last n) = 1)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ws)) <
          (1 / 4 : ℝ)) :
    (1 / 2 : ℝ) <
      muP X (upClosureIn X H) (tupleUnionDensity ρ) := by
  have hcost_half :
      (1 / 2 : ℝ) < coverCost X H q :=
    half_lt_coverCost_of_not_pSmall_upClosureIn hq0.le hHX hNotSmall
  have hcost_pos : 0 < coverCost X H q := by linarith
  have hbudget :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ws)) <
          coverCost X H q * (1 / 2) := by
    nlinarith
  exact half_lt_muP_of_iteratedLargeCostSnoc_average_lt
    X H ρ cutoff hq0.le hρ0 hρ1 hcost_pos hlast hbudget

end

end ParkPham
end Erdos202


/-! =============================================================
    Section from: Erdos/P202/ParkPham/Threshold.lean
    ============================================================= -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 4.

# Status

This file formalizes the Park–Pham / Kahn–Kalai expectation-threshold package
used by the spread-disjointness layer.  The finite Boolean-family reductions,
fragment-cost iteration, and scalar snoc budget schedule are all proved in
`ParkPham/`; the exported theorem below has no project-level assumption
dependency.

# Classical content

The Kahn–Kalai expectation-threshold conjecture, proved by Jinyoung Park
and Huy Tuan Pham in 2022 (arXiv:2203.17207), states roughly:

  For every increasing family `U` on a finite ground set `X`, the actual
  threshold `p_c(U)` differs from the expectation threshold `q(U)` by at
  most a logarithmic factor:
        `p_c(U) ≤ C · q(U) · log(ℓ(U))`
  for an absolute constant `C` and a complexity parameter
  `ℓ(U) := max(2, max cardinality of minimal members of U)`.

In the finite form below we phrase the conclusion as: if `q` is an upper
bound on the expectation threshold (in the sense of `qSmallUpper`), then
at density `p = C · q · log(ℓ(U))` the product measure `muP X U p` is at
least `1/2`.

# Shape decision

The deep input is stated as an existential package at the exact threshold
`p = C_KK q log ell`, in the genuinely subcritical case `p < 1`.
The endpoint case `p = 1` is elementary and is proved below, using
`muP_one_of_nonempty_increasing`.  The "any larger `p`" downstream interface is
then derived using the finite density-monotonicity theorem `muP_mono_density`.

# Formalization status

The final scalar schedule uses constant block length `64` and power-of-two
cutoffs of length `Nat.log 2 m + 1`, reducing the recursive snoc budget to the
finite geometric bound `∑ (1/16)^(2^j) < 1/4`.
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

universe u

section ThresholdDefinitions

variable {α : Type*} [DecidableEq α]

/-- `CriticalAtMost X U p` is the finite product-measure form of
`p_c(U) ≤ p`: at density `p`, the increasing event already has measure at
least `1/2`. -/
def CriticalAtMost (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ muP X U p ≥ 1 / 2

/-- `ExpectationAtMost X U q` is the finite `q(U) ≤ q` predicate used by the
Park--Pham theorem.  The substantive part is `qSmallUpper`; the interval bounds
are bundled for theorem statements that mirror the paper. -/
def ExpectationAtMost (X : Finset α) (U : Finset (Finset α)) (q : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧ qSmallUpper X U q

lemma CriticalAtMost.mono_density {X : Finset α} {U : Finset (Finset α)}
    {p r : ℝ} (hIncr : IncreasingIn X U)
    (hcrit : CriticalAtMost X U p) (hpr : p ≤ r) (hr1 : r ≤ 1) :
    CriticalAtMost X U r := by
  rcases hcrit with ⟨hp0, _hp1, hmu⟩
  have hmono : muP X U p ≤ muP X U r :=
    muP_mono_density hIncr hp0 hpr hr1
  exact ⟨hp0.trans hpr, hr1, hmu.trans hmono⟩

omit [DecidableEq α] in
lemma ExpectationAtMost.mono_q {X : Finset α} {U : Finset (Finset α)}
    {q r : ℝ} (hexp : ExpectationAtMost X U q) (hqr : q ≤ r) (hr1 : r ≤ 1) :
    ExpectationAtMost X U r := by
  rcases hexp with ⟨hq0, _hq1, hSmall⟩
  exact ⟨hq0.trans hqr, hr1, qSmallUpper_mono_q hqr hSmall⟩

omit [DecidableEq α] in
lemma ExpectationAtMost.of_not_pSmall {X : Finset α} {U : Finset (Finset α)}
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hNotSmall : ¬ pSmall X U q) :
    ExpectationAtMost X U q :=
  ⟨hq0, hq1, qSmallUpper_of_not_pSmall hq0 hNotSmall⟩

lemma CriticalAtMost.of_empty_mem_increasing {X : Finset α} {U : Finset (Finset α)}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hEmpty : (∅ : Finset α) ∈ U) :
    CriticalAtMost X U p := by
  have hmu : muP X U p = 1 :=
    muP_eq_one_of_empty_mem_increasing hUX hIncr hEmpty p
  rw [CriticalAtMost, hmu]
  norm_num [hp0, hp1]

omit [DecidableEq α] in
lemma ExpectationAtMost.one (X : Finset α) (U : Finset (Finset α)) :
    ExpectationAtMost X U (1 : ℝ) := by
  exact ⟨by norm_num, le_rfl, qSmallUpper_one X U⟩

omit [DecidableEq α] in
lemma ExpectationAtMost.zero_iff_empty_mem
    (X : Finset α) (U : Finset (Finset α)) :
    ExpectationAtMost X U (0 : ℝ) ↔ (∅ : Finset α) ∈ U := by
  rw [ExpectationAtMost, qSmallUpper_zero_iff_empty_mem]
  constructor
  · intro h
    exact h.2.2
  · intro h
    exact ⟨le_rfl, by norm_num, h⟩

lemma ExpectationAtMost.minimalMembersIn_iff
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ) :
    ExpectationAtMost X (minimalMembersIn X U) q ↔
      ExpectationAtMost X U q := by
  rw [ExpectationAtMost, ExpectationAtMost, qSmallUpper_minimalMembersIn_iff]

lemma CriticalAtMost.of_mu_ge {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hmu : muP X U p ≥ 1 / 2) :
    CriticalAtMost X U p :=
  ⟨hp0, hp1, hmu⟩

lemma CriticalAtMost.of_pow_ell_ge_half
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hU : U.Nonempty) (hpow : (1 / 2 : ℝ) ≤ p ^ ell X U) :
    CriticalAtMost X U p := by
  have hmu_lower : p ^ ell X U ≤ muP X U p :=
    pow_ell_le_muP_of_nonempty_increasing hp0 hp1 hUX hIncr hU
  exact CriticalAtMost.of_mu_ge hp0 hp1 (hpow.trans hmu_lower)

lemma CriticalAtMost.of_mem_pow_card_ge_half
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U) (hS : S ∈ U)
    (hpow : (1 / 2 : ℝ) ≤ p ^ S.card) :
    CriticalAtMost X U p := by
  have hmu_lower : p ^ S.card ≤ muP X U p :=
    pow_card_le_muP_of_mem_increasing hp0 hp1 hUX hIncr hS
  exact CriticalAtMost.of_mu_ge hp0 hp1 (hpow.trans hmu_lower)

lemma CriticalAtMost.of_mem_card_le
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α} {p : ℝ} {k : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U) (hS : S ∈ U)
    (hcard : S.card ≤ k) (hpow : (1 / 2 : ℝ) ≤ p ^ k) :
    CriticalAtMost X U p := by
  have hpow_le : p ^ k ≤ p ^ S.card :=
    pow_le_pow_of_le_one hp0 hp1 hcard
  exact CriticalAtMost.of_mem_pow_card_ge_half hp0 hp1 hUX hIncr hS
    (hpow.trans hpow_le)

lemma CriticalAtMost.of_exists_mem_card_le
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} {k : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U)
    (hExists : ∃ S ∈ U, S.card ≤ k) (hpow : (1 / 2 : ℝ) ≤ p ^ k) :
    CriticalAtMost X U p := by
  rcases hExists with ⟨S, hS, hcard⟩
  exact CriticalAtMost.of_mem_card_le hp0 hp1 hUX hIncr hS hcard hpow

/-- Finite dichotomy behind the reduced Park--Pham core: either a small member
already makes the family critical, or all minimal members are large enough that
non-smallness forces many of them. -/
lemma CriticalAtMost.or_many_minimalMembers_of_not_pSmall
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} {k : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U)
    (hNotSmall : ¬ pSmall X U p) (hpow : (1 / 2 : ℝ) ≤ p ^ k) :
    CriticalAtMost X U p ∨
      (1 / 2 : ℝ) <
        ((minimalMembersIn X U).card : ℝ) * p ^ (k + 1) := by
  by_cases hExists : ∃ S ∈ U, S.card ≤ k
  · exact Or.inl
      (CriticalAtMost.of_exists_mem_card_le hp0 hp1 hUX hIncr hExists hpow)
  · refine Or.inr ?_
    exact half_lt_minimalMembers_card_mul_pow_of_not_pSmall_card_ge hp0 hp1
      (fun T hT => by
        have hTU : T ∈ U := minimalMembersIn_subset hT
        have hnot_le : ¬ T.card ≤ k := by
          intro hle
          exact hExists ⟨T, hTU, hle⟩
        exact Nat.succ_le_iff.mpr (lt_of_not_ge hnot_le))
      hNotSmall

lemma CriticalAtMost.of_singleton_mem
    {X : Finset α} {U : Finset (Finset α)} {a : α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hhalf : (1 / 2 : ℝ) ≤ p)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hS : ({a} : Finset α) ∈ U) :
    CriticalAtMost X U p := by
  have hmu_lower : p ≤ muP X U p :=
    density_le_muP_of_singleton_mem_increasing hp0 hp1 hUX hIncr hS
  exact CriticalAtMost.of_mu_ge hp0 hp1 (hhalf.trans hmu_lower)

lemma CriticalAtMost.of_minimal_card_one
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hhalf : (1 / 2 : ℝ) ≤ p)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U)
    (hS : S ∈ minimalMembersIn X U) (hcard : S.card = 1) :
    CriticalAtMost X U p := by
  rcases exists_singleton_mem_of_mem_minimalMembersIn_card_eq_one hS hcard with ⟨a, ha⟩
  exact CriticalAtMost.of_singleton_mem hp0 hp1 hhalf hUX hIncr ha

end ThresholdDefinitions

/-- The strict Park--Pham conclusion is elementary when an increasing family
contains `∅`: then the family is the whole Boolean cube, so its product measure
is `1` at every density. -/
lemma park_pham_threshold_not_small_lt_of_empty_mem
    {α : Type*} [DecidableEq α]
    (CKK : ℝ) (X : Finset α) (U : Finset (Finset α)) (q : ℝ)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hEmpty : (∅ : Finset α) ∈ U) :
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  have hmu : muP X U (CKK * q * Real.log (ell X U)) = 1 :=
    muP_eq_one_of_empty_mem_increasing hUX hIncr hEmpty _
  rw [hmu]
  norm_num

/-- Reduction of the strict Park--Pham theorem to the nontrivial case
`∅ ∉ U`.  This keeps future work focused on the actual Kahn--Kalai/Park--Pham
core rather than the endpoint where the increasing family is the whole cube. -/
theorem park_pham_threshold_not_small_lt_reduce_empty
    {α : Type*} [DecidableEq α] (CKK : ℝ)
    (hCore :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        (∅ : Finset α) ∉ U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2)
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ)
    (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hNotSmall : ¬ pSmall X U q) :
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  by_cases hEmpty : (∅ : Finset α) ∈ U
  · exact park_pham_threshold_not_small_lt_of_empty_mem CKK X U q hUX hIncr hEmpty
  · exact hCore X U q hq0 hq1 hthreshold_lt_one hUX hIncr hEmpty hNotSmall

/-- For a Park--Pham constant at least `2 / log 2`, the bounded case
`C * q * log(ell) ≤ 1` automatically has `q < 1`. -/
lemma q_lt_one_of_large_constant_threshold_le_one
    {α : Type*} [DecidableEq α]
    {CKK q : ℝ} {X : Finset α} {U : Finset (Finset α)}
    (hCKK : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hq1 : q ≤ 1)
    (hthreshold_le_one : CKK * q * Real.log (ell X U) ≤ 1) :
    q < 1 := by
  by_contra hnot
  have hq_ge_one : (1 : ℝ) ≤ q := le_of_not_gt hnot
  have hq_eq_one : q = 1 := le_antisymm hq1 hq_ge_one
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hell_ge_two_nat : 2 ≤ ell X U := two_le_ell X U
  have hell_ge_two : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast hell_ge_two_nat
  have hlog2_le : Real.log 2 ≤ Real.log (ell X U) :=
    Real.log_le_log (by norm_num) hell_ge_two
  have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK
  have hCKK_log2_le :
      CKK * Real.log 2 ≤ CKK * Real.log (ell X U) :=
    mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
  have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right hCKK hlog2_pos.le
    have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
      field_simp [hlog2_pos.ne']
    linarith
  have hCKK_log_le_one : CKK * Real.log (ell X U) ≤ 1 := by
    simpa [hq_eq_one] using hthreshold_le_one
  linarith

/-- For a Park--Pham constant at least `2 / log 2`, the strict case
`C * q * log(ell) < 1` automatically has `q < 1`. -/
lemma q_lt_one_of_large_constant_threshold_lt_one
    {α : Type*} [DecidableEq α]
    {CKK q : ℝ} {X : Finset α} {U : Finset (Finset α)}
    (hCKK : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hq1 : q ≤ 1)
    (hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1) :
    q < 1 :=
  q_lt_one_of_large_constant_threshold_le_one hCKK hq1 hthreshold_lt_one.le

/-- The genuinely nontrivial strict Park--Pham/Kahn--Kalai core on one fixed
ground type, after local finite reductions: the family does not contain `∅`,
the expectation-threshold parameter is strictly inside `(0,1)`, and the target
density is strictly below `1`. -/
def StrictNonSmallCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    CKK * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    IncreasingIn X U →
    (∅ : Finset α) ∉ U →
    ¬ pSmall X U q →
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2

/-- Generated-family form of the reduced strict core.  Instead of taking an
already-increasing family `U`, the theorem is stated for the upper closure of a
generating family `A`. -/
def StrictGeneratedCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    CKK * q * Real.log (ell X (upClosureIn X A)) < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ upClosureIn X A →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log (ell X (upClosureIn X A))) ≥ 1 / 2

/-- The remaining strict core after removing the elementary branch where the
target density already gives a single minimal member probability at least
`1/2`. -/
def StrictHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    CKK * q * Real.log (ell X U) < 1 →
    (CKK * q * Real.log (ell X U)) ^ ell X U < 1 / 2 →
    (∀ S ∈ U, S ⊆ X) →
    IncreasingIn X U →
    (∅ : Finset α) ∉ U →
    ¬ pSmall X U q →
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2

/-- Generated-family version of `StrictHardCoreOn`. -/
def StrictGeneratedHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    CKK * q * Real.log (ell X (upClosureIn X A)) < 1 →
    (CKK * q * Real.log (ell X (upClosureIn X A))) ^
        ell X (upClosureIn X A) < 1 / 2 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ upClosureIn X A →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log (ell X (upClosureIn X A))) ≥ 1 / 2

/-- Antichain-generator form of the hard core, with the complexity parameter
rewritten away from the upper closure. -/
def StrictAntichainHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    (∅ : Finset α) ∉ A →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Antichain hard core after the elementary one-generator case has been
removed. -/
def StrictAntichainMultiHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    1 < A.card →
    (∅ : Finset α) ∉ A →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Antichain hard core after the elementary one- and two-generator cases have
been removed. -/
def StrictAntichainLargeHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    2 < A.card →
    (∅ : Finset α) ∉ A →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Remaining antichain hard core after removing any branch where one
generator alone already has probability at least `1/2` at the target density. -/
def StrictAntichainSparseHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    2 < A.card →
    (∅ : Finset α) ∉ A →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Remaining antichain hard core with the automatic sparse size condition
exposed as a hypothesis. -/
def StrictAntichainScaledHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    2 < A.card →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Scaled hard core with the redundant nonempty/cardinality hypotheses
removed.  They follow from the scale condition when the constant is large. -/
def StrictAntichainScaleOnlyHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Current reduced antichain hard core.  The scale condition implies
nonemptiness and the global low-density condition follows from the per-generator
smallness condition. -/
def StrictAntichainReducedHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Park--Vondrak certificate form for the current reduced hard core.  It
isolates the remaining probabilistic iteration work: construct a finite snoc
sequence of independent exposures whose union density is at most the target
density and whose expected accumulated large-fragment loss is below half the
initial cover cost. -/
def StrictAntichainReducedPVCertificateOn
    (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    ∃ n : ℕ, ∃ ρ : Fin (n + 1) → ℝ, ∃ cutoff : Fin (n + 1) → ℕ,
      (∀ i, 0 ≤ ρ i) ∧
      (∀ i, ρ i ≤ 1) ∧
      cutoff (Fin.last n) = 1 ∧
      tupleUnionDensity ρ ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) ∧
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q A (exposureTupleStepsSnoc cutoff Ws)) <
        coverCost X A q * (1 / 2)

/-- Quarter-budget version of the Park--Vondrak certificate.  Non-smallness
implies the initial cover cost is greater than `1/2`, so a uniform accumulated
loss bound by `1/4` is enough for the reduced hard core. -/
def StrictAntichainReducedPVQuarterCertificateOn
    (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    ∃ n : ℕ, ∃ ρ : Fin (n + 1) → ℝ, ∃ cutoff : Fin (n + 1) → ℕ,
      (∀ i, 0 ≤ ρ i) ∧
      (∀ i, ρ i ≤ 1) ∧
      cutoff (Fin.last n) = 1 ∧
      tupleUnionDensity ρ ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) ∧
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q A (exposureTupleStepsSnoc cutoff Ws)) <
        (1 / 4 : ℝ)

/-- Coarse numeric Park--Vondrak stage scheme for the reduced antichain target.
This is a sufficient bridge for testing the scalar density/budget plumbing.
The final proof is expected to use a refined variant whose large-fragment
budget uses the current post-small-fragment cardinality bound at each stage,
not the original `max 2 (A.sup card)` at every stage. -/
def StrictAntichainReducedPVNumericSchemeOn
    (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    ∃ n : ℕ, ∃ L : Fin (n + 1) → ℕ, ∃ cutoff : Fin (n + 1) → ℕ,
      (∀ i, 1 ≤ L i) ∧
      cutoff (Fin.last n) = 1 ∧
      q * (∑ i : Fin (n + 1), (L i : ℝ)) ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) ∧
      (∑ i : Fin (n + 1),
        (2 : ℝ) ^ max 2 (A.sup Finset.card) *
          (1 / (L i : ℝ)) ^ cutoff i) < (1 / 4 : ℝ)

/-- Refined numeric Park--Vondrak stage scheme for the reduced antichain
target.  This is the viable scalar target exposed by the current finite
bookkeeping: the large-fragment budget charges stage `i` using the cardinality
bound available after the previous small-fragment stage. -/
def StrictAntichainReducedPVSnocBudgetSchemeOn
    (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    ∃ n : ℕ, ∃ L : Fin (n + 1) → ℕ, ∃ cutoff : Fin (n + 1) → ℕ,
      (∀ i, 1 ≤ L i) ∧
      cutoff (Fin.last n) = 1 ∧
      q * (∑ i : Fin (n + 1), (L i : ℝ)) ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) ∧
      snocLargeCostBudget (max 2 (A.sup Finset.card)) cutoff L <
        (1 / 4 : ℝ)

/-- Pure scalar parameter target for the refined Park--Vondrak stage scheme.
This removes all Boolean-family data: it remains only to construct a finite
sequence of integer block lengths and cutoffs whose exposure budget is
`O(log m)` and whose recursive large-fragment budget is below `1/4`. -/
def PVSnocScalarParameterScheme (CKK : ℝ) : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    ∃ n : ℕ, ∃ L : Fin (n + 1) → ℕ, ∃ cutoff : Fin (n + 1) → ℕ,
      (∀ i, 1 ≤ L i) ∧
      cutoff (Fin.last n) = 1 ∧
      (∑ i : Fin (n + 1), (L i : ℝ)) ≤ CKK * Real.log (m : ℝ) ∧
      snocLargeCostBudget m cutoff L < (1 / 4 : ℝ)

/-- Power-of-two cutoffs for the scalar snoc schedule.  At stage `i`, the
cutoff is `2^(a+n-i)`; the public scalar scheme uses `a=0` and
`n = Nat.log 2 m`. -/
noncomputable def pvSnocPowerCutoff (a n : ℕ) (i : Fin (n + 1)) : ℕ :=
  2 ^ (a + (n - i.1))

lemma pvSnocPowerCutoff_tail (a n : ℕ) :
    (fun i : Fin (n + 1) => pvSnocPowerCutoff a (n + 1) i.castSucc) =
      pvSnocPowerCutoff (a + 1) n := by
  funext i
  have hi : i.1 ≤ n := Nat.lt_succ_iff.mp i.2
  simp [pvSnocPowerCutoff]
  have hsub : n + 1 - i.1 = n - i.1 + 1 := by omega
  rw [hsub]
  omega

lemma pvSnocPowerCutoff_last (a n : ℕ) :
    pvSnocPowerCutoff a n (Fin.last n) = 2 ^ a := by
  simp [pvSnocPowerCutoff]

lemma nat_succ_le_two_pow_local (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
      rw [Nat.pow_succ]
      nlinarith

lemma pow_two_mul_inv_sixtyfour_pow_le (c b : ℕ) (hb : b ≤ 2 * c) :
    (2 : ℝ) ^ b * (1 / (64 : ℝ)) ^ c ≤ (1 / 16 : ℝ) ^ c := by
  have hpow : (2 : ℝ) ^ b ≤ (2 : ℝ) ^ (2 * c) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hb
  have hnonneg : 0 ≤ (1 / (64 : ℝ)) ^ c := by positivity
  calc
    (2 : ℝ) ^ b * (1 / (64 : ℝ)) ^ c
        ≤ (2 : ℝ) ^ (2 * c) * (1 / (64 : ℝ)) ^ c :=
          mul_le_mul_of_nonneg_right hpow hnonneg
    _ = (1 / 16 : ℝ) ^ c := by
          rw [pow_mul]
          rw [← mul_pow]
          norm_num

lemma snocLargeCostBudget_pvSnocPowerCutoff_le_geometric
    (ell a n : ℕ) (hfirst : ell ≤ 2 * 2 ^ (a + n)) :
    snocLargeCostBudget ell (pvSnocPowerCutoff a n)
        (fun _ : Fin (n + 1) => 64) ≤
      ∑ j ∈ Finset.range (n + 1),
        (1 / 16 : ℝ) ^ (2 ^ (a + (n - j))) := by
  induction n generalizing a with
  | zero =>
      have hterm := pow_two_mul_inv_sixtyfour_pow_le (2 ^ a) ell hfirst
      simpa [snocLargeCostBudget, snocCurrentCardBound, pvSnocPowerCutoff]
        using hterm
  | succ n ih =>
      have htail_first : ell ≤ 2 * 2 ^ ((a + 1) + n) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst
      have htail := ih (a + 1) htail_first
      have hcurrent :
          snocCurrentCardBound ell (pvSnocPowerCutoff (a + 1) n) =
            2 ^ (a + 1) := by
        simp [snocCurrentCardBound, pvSnocPowerCutoff]
      have hcurrent_le : 2 ^ (a + 1) ≤ 2 * 2 ^ a := by
        rw [Nat.pow_succ]
        omega
      have hterm :=
        pow_two_mul_inv_sixtyfour_pow_le (2 ^ a) (2 ^ (a + 1)) hcurrent_le
      calc
        snocLargeCostBudget ell (pvSnocPowerCutoff a (n + 1))
            (fun _ : Fin (n + 1 + 1) => 64)
            ≤ (∑ j ∈ Finset.range (n + 1),
                  (1 / 16 : ℝ) ^ (2 ^ ((a + 1) + (n - j)))) +
                (1 / 16 : ℝ) ^ (2 ^ a) := by
              rw [snocLargeCostBudget]
              simp only [pvSnocPowerCutoff_tail]
              have hLtail :
                  (fun i : Fin (n + 1) =>
                    (fun _ : Fin (n + 1 + 1) => 64) i.castSucc) =
                    (fun _ : Fin (n + 1) => 64) := rfl
              rw [hLtail]
              have hlastCut :
                  pvSnocPowerCutoff a (n + 1) (Fin.last (n + 1)) = 2 ^ a :=
                pvSnocPowerCutoff_last a (n + 1)
              rw [hlastCut, hcurrent]
              exact add_le_add htail hterm
        _ = ∑ j ∈ Finset.range (n + 1 + 1),
              (1 / 16 : ℝ) ^ (2 ^ (a + ((n + 1) - j))) := by
              conv_rhs => rw [Finset.sum_range_succ]
              congr 1
              · refine Finset.sum_congr rfl ?_
                intro j hj
                have hjle : j ≤ n :=
                  Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
                have hsub : n + 1 - j = n - j + 1 := by omega
                rw [hsub]
                congr 2
                omega
              · simp

lemma pvSnocGeometricSum_le (a n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (1 / 16 : ℝ) ^ (2 ^ (a + (n - j)))) ≤
      (1 / 16 : ℝ) ^ (a + 1) / (1 - (1 / 16 : ℝ)) := by
  induction n generalizing a with
  | zero =>
      have hle_exp : a + 1 ≤ 2 ^ a := nat_succ_le_two_pow_local a
      have hpow_le :
          (1 / 16 : ℝ) ^ (2 ^ a) ≤ (1 / 16 : ℝ) ^ (a + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hle_exp
      have hden_pos : 0 < (1 - (1 / 16 : ℝ)) := by norm_num
      have hx : 0 ≤ (1 / 16 : ℝ) ^ (a + 1) := by positivity
      have hle_div :
          (1 / 16 : ℝ) ^ (a + 1) ≤
            (1 / 16 : ℝ) ^ (a + 1) / (1 - (1 / 16 : ℝ)) := by
        rw [le_div_iff₀ hden_pos]
        nlinarith
      simpa using hpow_le.trans hle_div
  | succ n ih =>
      have htail := ih (a + 1)
      have hle_exp : a + 1 ≤ 2 ^ a := nat_succ_le_two_pow_local a
      have hterm_le :
          (1 / 16 : ℝ) ^ (2 ^ a) ≤ (1 / 16 : ℝ) ^ (a + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hle_exp
      calc
        (∑ j ∈ Finset.range (n + 1 + 1),
          (1 / 16 : ℝ) ^ (2 ^ (a + ((n + 1) - j))))
            = (∑ j ∈ Finset.range (n + 1),
                (1 / 16 : ℝ) ^ (2 ^ ((a + 1) + (n - j)))) +
              (1 / 16 : ℝ) ^ (2 ^ a) := by
                conv_lhs => rw [Finset.sum_range_succ]
                congr 1
                · refine Finset.sum_congr rfl ?_
                  intro j hj
                  have hjle : j ≤ n :=
                    Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
                  have hsub : n + 1 - j = n - j + 1 := by omega
                  rw [hsub]
                  congr 2
                  omega
                · simp
        _ ≤ (1 / 16 : ℝ) ^ ((a + 1) + 1) /
              (1 - (1 / 16 : ℝ)) +
              (1 / 16 : ℝ) ^ (a + 1) := by
                exact add_le_add htail hterm_le
        _ = (1 / 16 : ℝ) ^ (a + 1) / (1 - (1 / 16 : ℝ)) := by
              ring_nf

lemma pvSnocGeometricSum_zero_lt_quarter (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (1 / 16 : ℝ) ^ (2 ^ (0 + (n - j)))) < (1 / 4 : ℝ) := by
  have h := pvSnocGeometricSum_le 0 n
  have hconst :
      (1 / 16 : ℝ) ^ (0 + 1) / (1 - (1 / 16 : ℝ)) < (1 / 4 : ℝ) := by
    norm_num
  exact lt_of_le_of_lt h hconst

lemma natLog2_add_one_le_two_log_div_log2 (m : ℕ) (hm : 2 ≤ m) :
    (((Nat.log 2 m + 1 : ℕ) : ℝ)) ≤
      2 * Real.log (m : ℝ) / Real.log 2 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog2_le_logm : Real.log 2 ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by norm_num) hm_real
  have hquot_ge_one : (1 : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
    exact (le_div_iff₀ hlog2pos).2 (by simpa using hlog2_le_logm)
  have hlog_nat_le :
      ((Nat.log 2 m : ℕ) : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
    have h := Real.log2_le_logb m
    simpa [Nat.log2_eq_log_two, Real.logb] using h
  calc
    (((Nat.log 2 m + 1 : ℕ) : ℝ))
        = ((Nat.log 2 m : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ Real.log (m : ℝ) / Real.log 2 + 1 := by linarith
    _ ≤ Real.log (m : ℝ) / Real.log 2 +
          Real.log (m : ℝ) / Real.log 2 := by linarith
    _ = 2 * Real.log (m : ℝ) / Real.log 2 := by ring

theorem pvSnocScalarParameterScheme_128_div_log_two :
    PVSnocScalarParameterScheme (128 / Real.log 2) := by
  intro m hm
  let n : ℕ := Nat.log 2 m
  let L : Fin (n + 1) → ℕ := fun _ => 64
  let cutoff : Fin (n + 1) → ℕ := pvSnocPowerCutoff 0 n
  refine ⟨n, L, cutoff, ?_, ?_, ?_, ?_⟩
  · intro i
    norm_num [L]
  · simpa [cutoff] using pvSnocPowerCutoff_last 0 n
  · have hsum_eq :
        (∑ i : Fin (n + 1), (L i : ℝ)) =
          64 * (((n + 1 : ℕ) : ℝ)) := by
      simp [L]
      ring
    have hlog_bound := natLog2_add_one_le_two_log_div_log2 m hm
    have hmul :=
      mul_le_mul_of_nonneg_left hlog_bound (by norm_num : (0 : ℝ) ≤ 64)
    calc
      (∑ i : Fin (n + 1), (L i : ℝ))
          = 64 * (((n + 1 : ℕ) : ℝ)) := hsum_eq
      _ ≤ 64 * (2 * Real.log (m : ℝ) / Real.log 2) := by
        simpa [n, mul_assoc] using hmul
      _ = (128 / Real.log 2) * Real.log (m : ℝ) := by ring
  · have hfirst : m ≤ 2 * 2 ^ (0 + n) := by
      have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two m
      have hle : m ≤ 2 ^ (Nat.log 2 m + 1) := Nat.le_of_lt hlt
      simpa [n, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using hle
    have hbudget_le :=
      snocLargeCostBudget_pvSnocPowerCutoff_le_geometric m 0 n hfirst
    have hgeom_lt := pvSnocGeometricSum_zero_lt_quarter n
    exact lt_of_le_of_lt (by simpa [cutoff, L, n] using hbudget_le) hgeom_lt

theorem exists_pv_snoc_scalar_parameter_scheme :
    ∃ CKK : ℝ, 0 < CKK ∧ (2 / Real.log 2 : ℝ) ≤ CKK ∧
      PVSnocScalarParameterScheme CKK := by
  refine ⟨128 / Real.log 2, ?_, ?_, pvSnocScalarParameterScheme_128_div_log_two⟩
  · positivity
  · have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 128)
      hlog2pos.le

/-- The pure scalar parameter target implies the reduced snoc-budget scheme. -/
theorem strictAntichainReducedPVSnocBudgetSchemeOn_of_scalarParameterScheme
    {CKK : ℝ} {α : Type*} [DecidableEq α]
    (hScalar : PVSnocScalarParameterScheme CKK) :
    StrictAntichainReducedPVSnocBudgetSchemeOn CKK α := by
  intro X A q hq0 _hq1 _hAX _hAnti _hEmptyA _hscale_lt _hthreshold_lt_one
    _hNoHeavy _hNotSmall
  let m : ℕ := max 2 (A.sup Finset.card)
  have hm_two : 2 ≤ m := by
    dsimp [m]
    exact le_max_left _ _
  rcases hScalar m hm_two with
    ⟨n, L, cutoff, hL, hlast, hsum, hbudget⟩
  have hdensity :
      q * (∑ i : Fin (n + 1), (L i : ℝ)) ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hsum hq0.le
    simpa [m, mul_assoc, mul_comm, mul_left_comm] using hmul
  exact ⟨n, L, cutoff, hL, hlast, hdensity, by simpa [m] using hbudget⟩

/-- A coarse numeric Park--Vondrak stage scheme gives the explicit quarter-budget
certificate by taking coordinate densities `ρᵢ = 1 - (1-q)^{Lᵢ}` and applying
the scalar union bound plus the iterated large-fragment budget lemma. -/
theorem strictAntichainReducedPVQuarterCertificateOn_of_numericSchemeOn
    {CKK : ℝ} {α : Type*} [DecidableEq α]
    (hScheme : StrictAntichainReducedPVNumericSchemeOn CKK α) :
    StrictAntichainReducedPVQuarterCertificateOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt hthreshold_lt_one
    hNoHeavy hNotSmall
  rcases hScheme X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
      hthreshold_lt_one hNoHeavy hNotSmall with
    ⟨n, L, cutoff, hL, hlast, hdensity, hbudget⟩
  let ρ : Fin (n + 1) → ℝ := fun i => 1 - (1 - q) ^ L i
  have hq_le_one : q ≤ 1 := hq1.le
  have hbase0 : 0 ≤ 1 - q := by linarith
  have hbase1 : 1 - q ≤ 1 := by linarith
  have hρ0 : ∀ i, 0 ≤ ρ i := by
    intro i
    have hpow_le_one : (1 - q) ^ L i ≤ (1 : ℝ) :=
      pow_le_one₀ hbase0 hbase1
    dsimp [ρ]
    linarith
  have hρ1 : ∀ i, ρ i ≤ 1 := by
    intro i
    have hpow_nonneg : 0 ≤ (1 - q) ^ L i :=
      pow_nonneg hbase0 _
    dsimp [ρ]
    linarith
  have htuple :
      tupleUnionDensity ρ ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    have htuple_le :
        tupleUnionDensity ρ ≤ q * (∑ i : Fin (n + 1), (L i : ℝ)) := by
      simpa [ρ] using
        tupleUnionDensity_one_sub_pow_le_q_sum L hq0.le hq_le_one
    exact htuple_le.trans hdensity
  let m : ℕ := max 2 (A.sup Finset.card)
  have hAcard_bound : ∀ S ∈ A, S.card ≤ m := by
    intro S hS
    exact (Finset.le_sup (s := A) (f := Finset.card) hS).trans
      (le_max_right _ _)
  have havg_le :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q A (exposureTupleStepsSnoc cutoff Ws)) ≤
        ∑ i : Fin (n + 1),
          (2 : ℝ) ^ m * (1 / (L i : ℝ)) ^ cutoff i := by
    exact iteratedLargeCostSum_exposureTupleStepsSnoc_sum_le_budget_sum
      X A m ρ cutoff L hρ0 hρ1 hL hq0 hq_le_one
      (fun i => rfl) hAX hAcard_bound
  refine ⟨n, ρ, cutoff, hρ0, hρ1, hlast, htuple, ?_⟩
  exact havg_le.trans_lt (by simpa [m] using hbudget)

/-- A refined snoc-budget scheme gives the explicit quarter-budget
certificate. -/
theorem strictAntichainReducedPVQuarterCertificateOn_of_snocBudgetSchemeOn
    {CKK : ℝ} {α : Type*} [DecidableEq α]
    (hScheme : StrictAntichainReducedPVSnocBudgetSchemeOn CKK α) :
    StrictAntichainReducedPVQuarterCertificateOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt hthreshold_lt_one
    hNoHeavy hNotSmall
  rcases hScheme X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
      hthreshold_lt_one hNoHeavy hNotSmall with
    ⟨n, L, cutoff, hL, hlast, hdensity, hbudget⟩
  let ρ : Fin (n + 1) → ℝ := fun i => 1 - (1 - q) ^ L i
  have hq_le_one : q ≤ 1 := hq1.le
  have hbase0 : 0 ≤ 1 - q := by linarith
  have hbase1 : 1 - q ≤ 1 := by linarith
  have hρ0 : ∀ i, 0 ≤ ρ i := by
    intro i
    have hpow_le_one : (1 - q) ^ L i ≤ (1 : ℝ) :=
      pow_le_one₀ hbase0 hbase1
    dsimp [ρ]
    linarith
  have hρ1 : ∀ i, ρ i ≤ 1 := by
    intro i
    have hpow_nonneg : 0 ≤ (1 - q) ^ L i :=
      pow_nonneg hbase0 _
    dsimp [ρ]
    linarith
  have htuple :
      tupleUnionDensity ρ ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    have htuple_le :
        tupleUnionDensity ρ ≤ q * (∑ i : Fin (n + 1), (L i : ℝ)) := by
      simpa [ρ] using
        tupleUnionDensity_one_sub_pow_le_q_sum L hq0.le hq_le_one
    exact htuple_le.trans hdensity
  let m : ℕ := max 2 (A.sup Finset.card)
  have hAcard_bound : ∀ S ∈ A, S.card ≤ m := by
    intro S hS
    exact (Finset.le_sup (s := A) (f := Finset.card) hS).trans
      (le_max_right _ _)
  have havg_le :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q A (exposureTupleStepsSnoc cutoff Ws)) ≤
        snocLargeCostBudget m cutoff L := by
    exact iteratedLargeCostSum_exposureTupleStepsSnoc_sum_le_snocLargeCostBudget
      X A m ρ cutoff L hρ0 hρ1 hL hq0 hq_le_one
      (fun i => rfl) hAX hAcard_bound
  refine ⟨n, ρ, cutoff, hρ0, hρ1, hlast, htuple, ?_⟩
  exact havg_le.trans_lt (by simpa [m] using hbudget)

/-- A Park--Vondrak certificate for the reduced antichain hard core gives the
reduced hard core itself. -/
theorem strictAntichainReducedHardCoreOn_of_pvCertificateOn
    {CKK : ℝ} {α : Type*} [DecidableEq α]
    (hCert : StrictAntichainReducedPVCertificateOn CKK α) :
    StrictAntichainReducedHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt hthreshold_lt_one
    hNoHeavy hNotSmall
  let θ : ℝ :=
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
  rcases hCert X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
      hthreshold_lt_one hNoHeavy hNotSmall with
    ⟨n, ρ, cutoff, hρ0, hρ1, hlast, hρ_le_target, havg⟩
  have hcost_half :
      (1 / 2 : ℝ) < coverCost X A q :=
    half_lt_coverCost_of_not_pSmall_upClosureIn hq0.le hAX hNotSmall
  have hcost_pos : 0 < coverCost X A q := by linarith
  have hhalf :
      (1 / 2 : ℝ) <
        muP X (upClosureIn X A) (tupleUnionDensity ρ) :=
    half_lt_muP_of_iteratedLargeCostSnoc_average_lt
      X A ρ cutoff hq0.le hρ0 hρ1 hcost_pos hlast havg
  have htuple_nonneg : 0 ≤ tupleUnionDensity ρ :=
    tupleUnionDensity_nonneg hρ0 hρ1
  have htheta_le_one : θ ≤ 1 := by
    dsimp [θ]
    exact hthreshold_lt_one.le
  have hmono :
      muP X (upClosureIn X A) (tupleUnionDensity ρ) ≤
        muP X (upClosureIn X A) θ :=
    muP_mono_density (increasingIn_upClosureIn X A)
      htuple_nonneg (by simpa [θ] using hρ_le_target) htheta_le_one
  exact (le_of_lt hhalf).trans (by simpa [θ] using hmono)

/-- The quarter-budget Park--Vondrak certificate gives the reduced hard core
directly. -/
theorem strictAntichainReducedHardCoreOn_of_pvQuarterCertificateOn
    {CKK : ℝ} {α : Type*} [DecidableEq α]
    (hCert : StrictAntichainReducedPVQuarterCertificateOn CKK α) :
    StrictAntichainReducedHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt hthreshold_lt_one
    hNoHeavy hNotSmall
  let θ : ℝ :=
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
  rcases hCert X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
      hthreshold_lt_one hNoHeavy hNotSmall with
    ⟨n, ρ, cutoff, hρ0, hρ1, hlast, hρ_le_target, havg⟩
  have hhalf :
      (1 / 2 : ℝ) <
        muP X (upClosureIn X A) (tupleUnionDensity ρ) :=
    half_lt_muP_of_not_pSmall_iteratedLargeCostSnoc_average_lt_quarter
      X A ρ cutoff hq0 hρ0 hρ1 hAX hNotSmall hlast havg
  have htuple_nonneg : 0 ≤ tupleUnionDensity ρ :=
    tupleUnionDensity_nonneg hρ0 hρ1
  have htheta_le_one : θ ≤ 1 := by
    dsimp [θ]
    exact hthreshold_lt_one.le
  have hmono :
      muP X (upClosureIn X A) (tupleUnionDensity ρ) ≤
        muP X (upClosureIn X A) θ :=
    muP_mono_density (increasingIn_upClosureIn X A)
      htuple_nonneg (by simpa [θ] using hρ_le_target) htheta_le_one
  exact (le_of_lt hhalf).trans (by simpa [θ] using hmono)

/-- The generated-family core implies the increasing-family strict core by
taking the generators to be the minimal members. -/
theorem strict_nonSmallCoreOn_of_generatedCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictGeneratedCoreOn CKK α) :
    StrictNonSmallCoreOn CKK α := by
  intro X U q hq0 hq1 hthreshold_lt_one hUX hIncr hEmpty hNotSmall
  let A : Finset (Finset α) := minimalMembersIn X U
  have hAX : ∀ S ∈ A, S ⊆ X := by
    intro S hS
    exact hUX S (minimalMembersIn_subset hS)
  have hAnti : InclusionAntichain A := by
    simpa [A] using minimalMembersIn_inclusionAntichain X U
  have hclosure_eq : upClosureIn X A = U := by
    simpa [A] using upClosureIn_minimalMembersIn_eq_of_increasing hUX hIncr
  have hthreshold_A :
      CKK * q * Real.log (ell X (upClosureIn X A)) < 1 := by
    simpa [hclosure_eq] using hthreshold_lt_one
  have hEmpty_A : (∅ : Finset α) ∉ upClosureIn X A := by
    simpa [hclosure_eq] using hEmpty
  have hNotSmall_A : ¬ pSmall X (upClosureIn X A) q := by
    simpa [hclosure_eq] using hNotSmall
  have hmu :=
    hCore X A q hq0 hq1 hthreshold_A hAX hAnti hEmpty_A hNotSmall_A
  simpa [hclosure_eq] using hmu

/-- In the strict Park--Pham setup, the branch
`1/2 ≤ (C q log ell)^ell` is elementary: a non-small increasing family is
nonempty, so one of its minimal members has size at most `ell`, and the product
measure is already at least `1/2`. -/
theorem park_pham_threshold_not_small_lt_of_pow_ell_ge_half
    {α : Type*} [DecidableEq α] {CKK q : ℝ}
    (hCKK_pos : 0 < CKK) (hq0 : 0 < q)
    {X : Finset α} {U : Finset (Finset α)}
    (hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hNotSmall : ¬ pSmall X U q)
    (hpow : (1 / 2 : ℝ) ≤
      (CKK * q * Real.log (ell X U)) ^ ell X U) :
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hell_ge_two_nat : 2 ≤ ell X U := two_le_ell X U
  have hell_ge_two : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast hell_ge_two_nat
  have hlog_pos : 0 < Real.log (ell X U) :=
    lt_of_lt_of_le hlog2_pos (Real.log_le_log (by norm_num) hell_ge_two)
  have hp0 : 0 ≤ CKK * q * Real.log (ell X U) := by positivity
  have hp1 : CKK * q * Real.log (ell X U) ≤ 1 := hthreshold_lt_one.le
  have hU : U.Nonempty := nonempty_of_not_pSmall hNotSmall
  exact (CriticalAtMost.of_pow_ell_ge_half hp0 hp1 hUX hIncr hU hpow).2.2

/-- It is enough to prove the strict Park--Pham core in the low-density
hard case `(C q log ell)^ell < 1/2`; the complementary branch is elementary. -/
theorem strict_nonSmallCoreOn_of_hardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_pos : 0 < CKK) (hCore : StrictHardCoreOn CKK α) :
    StrictNonSmallCoreOn CKK α := by
  intro X U q hq0 hq1 hthreshold_lt_one hUX hIncr hEmpty hNotSmall
  by_cases hpow :
      (1 / 2 : ℝ) ≤ (CKK * q * Real.log (ell X U)) ^ ell X U
  · exact park_pham_threshold_not_small_lt_of_pow_ell_ge_half
      hCKK_pos hq0 hthreshold_lt_one hUX hIncr hNotSmall hpow
  · exact hCore X U q hq0 hq1 hthreshold_lt_one
      (lt_of_not_ge hpow) hUX hIncr hEmpty hNotSmall

/-- The generated hard core implies the increasing-family hard core by taking
generators to be the minimal members. -/
theorem strict_hardCoreOn_of_generatedHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictGeneratedHardCoreOn CKK α) :
    StrictHardCoreOn CKK α := by
  intro X U q hq0 hq1 hthreshold_lt_one hpow_lt hUX hIncr hEmpty hNotSmall
  let A : Finset (Finset α) := minimalMembersIn X U
  have hAX : ∀ S ∈ A, S ⊆ X := by
    intro S hS
    exact hUX S (minimalMembersIn_subset hS)
  have hAnti : InclusionAntichain A := by
    simpa [A] using minimalMembersIn_inclusionAntichain X U
  have hclosure_eq : upClosureIn X A = U := by
    simpa [A] using upClosureIn_minimalMembersIn_eq_of_increasing hUX hIncr
  have hthreshold_A :
      CKK * q * Real.log (ell X (upClosureIn X A)) < 1 := by
    simpa [hclosure_eq] using hthreshold_lt_one
  have hpow_A :
      (CKK * q * Real.log (ell X (upClosureIn X A))) ^
          ell X (upClosureIn X A) < 1 / 2 := by
    simpa [hclosure_eq] using hpow_lt
  have hEmpty_A : (∅ : Finset α) ∉ upClosureIn X A := by
    simpa [hclosure_eq] using hEmpty
  have hNotSmall_A : ¬ pSmall X (upClosureIn X A) q := by
    simpa [hclosure_eq] using hNotSmall
  have hmu :=
    hCore X A q hq0 hq1 hthreshold_A hpow_A hAX hAnti hEmpty_A hNotSmall_A
  simpa [hclosure_eq] using hmu

/-- Generated hard-core proofs are enough for the reduced increasing-family
strict core. -/
theorem strict_nonSmallCoreOn_of_generatedHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_pos : 0 < CKK) (hCore : StrictGeneratedHardCoreOn CKK α) :
    StrictNonSmallCoreOn CKK α :=
  strict_nonSmallCoreOn_of_hardCoreOn hCKK_pos
    (strict_hardCoreOn_of_generatedHardCoreOn hCore)

/-- The explicit antichain-generator hard core implies the generated hard
core: nonemptiness follows from non-smallness, `∅ ∉ A` follows from
`∅ ∉ upClosureIn X A`, and `ell` is rewritten by the antichain minimal-member
lemma. -/
theorem strictGeneratedHardCoreOn_of_antichainHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictAntichainHardCoreOn CKK α) :
    StrictGeneratedHardCoreOn CKK α := by
  intro X A q hq0 hq1 hthreshold_lt_one hpow_lt hAX hAnti hEmpty hNotSmall
  have hA_nonempty : A.Nonempty :=
    nonempty_of_upClosureIn_nonempty (nonempty_of_not_pSmall hNotSmall)
  have hEmptyA : (∅ : Finset α) ∉ A :=
    empty_not_mem_upClosureIn_iff.mp hEmpty
  have hEll :
      ell X (upClosureIn X A) = max 2 (A.sup Finset.card) :=
    ell_upClosure_eq_of_inclusionAntichain hAnti hAX
  have hthreshold_A :
      CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 := by
    simpa [hEll] using hthreshold_lt_one
  have hpow_A :
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          max 2 (A.sup Finset.card) < 1 / 2 := by
    simpa [hEll] using hpow_lt
  have hmu :=
    hCore X A q hq0 hq1 hAX hAnti hA_nonempty hEmptyA
      hthreshold_A hpow_A hNotSmall
  simpa [hEll] using hmu

/-- It is enough to prove the explicit antichain hard core when the generator
has at least two members.  The one-generator case is elementary: the sole
generator covers its upper closure, so non-smallness gives
`1 / 2 < q^|S|`; for a large enough Park--Pham constant the target density is
at least `q`, and the singleton-upclosure measure identity finishes. -/
theorem strictAntichainHardCoreOn_of_multiHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictAntichainMultiHardCoreOn CKK α) :
    StrictAntichainHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hA_nonempty hEmptyA
    hthreshold_lt_one _hpow_lt hNotSmall
  by_cases hcard_one : A.card = 1
  · rcases Finset.card_eq_one.mp hcard_one with ⟨S, hAeq⟩
    subst A
    have hSX : S ⊆ X := hAX S (by simp)
    have hCover : CoversIn X {S} (upClosureIn X {S}) := by
      intro T hT
      rcases mem_upClosureIn.mp hT with ⟨_, R, hR, hRT⟩
      have hR_eq : R = S := by simpa using hR
      exact ⟨S, by simp, by simpa [hR_eq] using hRT⟩
    have hqpow_gt : (1 / 2 : ℝ) < q ^ S.card := by
      by_contra hnot
      have hle : q ^ S.card ≤ (1 / 2 : ℝ) := le_of_not_gt hnot
      have hSmall : pSmall X (upClosureIn X {S}) q :=
        pSmall_of_cover_sum_le hCover (by simpa using hle)
      exact hNotSmall hSmall
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
    have hm_ge_two_nat : 2 ≤ max 2 S.card := le_max_left _ _
    have hm_ge_two : (2 : ℝ) ≤ ((max 2 S.card : ℕ) : ℝ) := by
      exact_mod_cast hm_ge_two_nat
    have hlog2_le : Real.log 2 ≤ Real.log ((max 2 S.card : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) hm_ge_two
    have hlog_nonneg : 0 ≤ Real.log ((max 2 S.card : ℕ) : ℝ) :=
      le_trans hlog2_pos.le hlog2_le
    have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_right hCKK_large hlog2_pos.le
      have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
        field_simp [hlog2_pos.ne']
      linarith
    have hone_le_CKK_logm :
        (1 : ℝ) ≤ CKK * Real.log ((max 2 S.card : ℕ) : ℝ) := by
      have hmono :
          CKK * Real.log 2 ≤ CKK * Real.log ((max 2 S.card : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
      linarith
    have hq_le_target :
        q ≤ CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) := by
      calc
        q = q * 1 := by ring
        _ ≤ q * (CKK * Real.log ((max 2 S.card : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hone_le_CKK_logm hq0.le
        _ = CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) := by ring
    have hp0 : 0 ≤ CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) :=
      mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
    have hthreshold_S :
        CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) < 1 := by
      simpa using hthreshold_lt_one
    have hp1 : CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) ≤ 1 :=
      hthreshold_S.le
    have hpow_q_le :
        q ^ S.card ≤
          (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) ^ S.card :=
      pow_le_pow_left₀ hq0.le hq_le_target S.card
    have hmu :
        (1 / 2 : ℝ) ≤
          muP X (upClosureIn X {S})
            (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) := by
      have hstrict :
          (1 / 2 : ℝ) <
            (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) ^ S.card :=
        hqpow_gt.trans_le hpow_q_le
      have hsingle :
          muP X (upClosureIn X {S})
              (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) =
            (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) ^ S.card :=
        muP_upClosure_single X S hSX hp0 hp1
      rw [hsingle]
      exact hstrict.le
    simpa using hmu
  · have hcard_gt_one : 1 < A.card := by
      have hpos : 0 < A.card := hA_nonempty.card_pos
      omega
    exact hCore X A q hq0 hq1 hAX hAnti hA_nonempty hcard_gt_one hEmptyA
      hthreshold_lt_one _hpow_lt hNotSmall

/-- It is enough to prove the explicit antichain hard core when the generator
has at least three members.  The two-generator case is elementary: the cover by
the two generators has weight `> 1/2`, so the smaller generator has
`q`-weight `> 1/4`; at density at least `2q`, its principal up-closure already
has mass at least `1/2`. -/
theorem strictAntichainMultiHardCoreOn_of_largeHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictAntichainLargeHardCoreOn CKK α) :
    StrictAntichainMultiHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hA_nonempty hcard_gt_one hEmptyA
    hthreshold_lt_one hpow_lt hNotSmall
  by_cases hcard_two : A.card = 2
  · rcases A.exists_min_image Finset.card hA_nonempty with ⟨S, hSA, hS_min⟩
    have hCover : CoversIn X A (upClosureIn X A) := by
      intro T hT
      rcases mem_upClosureIn.mp hT with ⟨_, R, hRA, hRT⟩
      exact ⟨R, hRA, hRT⟩
    have hsum_gt :
        (1 / 2 : ℝ) < ∑ R ∈ A, q ^ R.card :=
      cover_sum_gt_half_of_not_pSmall hNotSmall hCover
    have hterm : ∀ R ∈ A, q ^ R.card ≤ q ^ S.card := by
      intro R hRA
      exact pow_le_pow_of_le_one hq0.le hq1.le (hS_min R hRA)
    have hsum_le :
        (∑ R ∈ A, q ^ R.card) ≤ ∑ R ∈ A, q ^ S.card :=
      Finset.sum_le_sum hterm
    have hconst :
        (∑ R ∈ A, q ^ S.card) = (A.card : ℝ) * q ^ S.card := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hqpow_quarter : (1 / 4 : ℝ) < q ^ S.card := by
      have hhalf_lt_two : (1 / 2 : ℝ) < (2 : ℝ) * q ^ S.card := by
        calc
          (1 / 2 : ℝ) < ∑ R ∈ A, q ^ R.card := hsum_gt
          _ ≤ ∑ R ∈ A, q ^ S.card := hsum_le
          _ = (A.card : ℝ) * q ^ S.card := hconst
          _ = (2 : ℝ) * q ^ S.card := by simp [hcard_two]
      linarith
    have hS_nonempty : S.Nonempty := by
      by_contra hS_empty
      have hS_eq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS_empty
      exact hEmptyA (by simpa [hS_eq] using hSA)
    have hS_card_pos : 0 < S.card := hS_nonempty.card_pos
    let m : ℕ := max 2 (A.sup Finset.card)
    let p : ℝ := CKK * q * Real.log ((m : ℕ) : ℝ)
    have hm_ge_two_nat : 2 ≤ m := by
      dsimp [m]
      exact le_max_left _ _
    have hm_ge_two : (2 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hm_ge_two_nat
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_le : Real.log 2 ≤ Real.log ((m : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) hm_ge_two
    have hlog_nonneg : 0 ≤ Real.log ((m : ℕ) : ℝ) :=
      le_trans hlog2_pos.le hlog2_le
    have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
    have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_right hCKK_large hlog2_pos.le
      have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
        field_simp [hlog2_pos.ne']
      linarith
    have htwo_le_CKK_logm : (2 : ℝ) ≤ CKK * Real.log ((m : ℕ) : ℝ) := by
      have hmono :
          CKK * Real.log 2 ≤ CKK * Real.log ((m : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
      linarith
    have htwoq_le_p : 2 * q ≤ p := by
      calc
        2 * q = q * 2 := by ring
        _ ≤ q * (CKK * Real.log ((m : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left htwo_le_CKK_logm hq0.le
        _ = p := by simp [p]; ring
    have htwoq_nonneg : 0 ≤ 2 * q := by positivity
    have htwo_pow_ge_two : (2 : ℝ) ≤ (2 : ℝ) ^ S.card := by
      cases hcard : S.card with
      | zero =>
          omega
      | succ n =>
          have hpow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
            exact one_le_pow₀ (by norm_num)
          calc
            (2 : ℝ) = 2 * 1 := by ring
            _ ≤ 2 * (2 : ℝ) ^ n := by nlinarith
            _ = (2 : ℝ) ^ Nat.succ n := by rw [pow_succ]; ring
    have hhalf_lt_twoq_pow : (1 / 2 : ℝ) < (2 * q) ^ S.card := by
      rw [mul_pow]
      have hqpow_pos : 0 < q ^ S.card := pow_pos hq0 _
      have hhalf_lt_two_qpow : (1 / 2 : ℝ) < 2 * q ^ S.card := by
        linarith
      have htwo_qpow_le :
          2 * q ^ S.card ≤ (2 : ℝ) ^ S.card * q ^ S.card := by
        nlinarith
      exact hhalf_lt_two_qpow.trans_le htwo_qpow_le
    have hp_pow_lower : (1 / 2 : ℝ) ≤ p ^ S.card := by
      have hpow_le : (2 * q) ^ S.card ≤ p ^ S.card :=
        pow_le_pow_left₀ htwoq_nonneg htwoq_le_p S.card
      exact (hhalf_lt_twoq_pow.trans_le hpow_le).le
    have hp0 : 0 ≤ p := by
      dsimp [p]
      exact mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
    have hp1 : p ≤ 1 := by
      dsimp [p, m]
      exact hthreshold_lt_one.le
    have hS_up : S ∈ upClosureIn X A := subset_upClosureIn hAX hSA
    have hUX : ∀ T ∈ upClosureIn X A, T ⊆ X := by
      intro T hT
      exact (mem_upClosureIn.mp hT).1
    have hmu_lower :
        p ^ S.card ≤ muP X (upClosureIn X A) p :=
      pow_card_le_muP_of_mem_increasing hp0 hp1 hUX
        (increasingIn_upClosureIn X A) hS_up
    have hmu : (1 / 2 : ℝ) ≤ muP X (upClosureIn X A) p :=
      hp_pow_lower.trans hmu_lower
    simpa [p, m] using hmu
  · have hcard_large : 2 < A.card := by omega
    exact hCore X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
      hthreshold_lt_one hpow_lt hNotSmall

/-- It is enough to prove the large antichain hard core when no single
generator is already heavy at the target density. -/
theorem strictAntichainLargeHardCoreOn_of_sparseHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictAntichainSparseHardCoreOn CKK α) :
    StrictAntichainLargeHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
    hthreshold_lt_one hpow_lt hNotSmall
  let m : ℕ := max 2 (A.sup Finset.card)
  let p : ℝ := CKK * q * Real.log ((m : ℕ) : ℝ)
  have hm_ge_two_nat : 2 ≤ m := by
    dsimp [m]
    exact le_max_left _ _
  have hm_ge_two : (2 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hm_ge_two_nat
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ Real.log ((m : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) hm_ge_two
  have hlog_nonneg : 0 ≤ Real.log ((m : ℕ) : ℝ) :=
    le_trans hlog2_pos.le hlog2_le
  have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
  have hp0 : 0 ≤ p := by
    dsimp [p]
    exact mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
  have hp1 : p ≤ 1 := by
    dsimp [p, m]
    exact hthreshold_lt_one.le
  by_cases hHeavy : ∃ S ∈ A, (1 / 2 : ℝ) ≤ p ^ S.card
  · rcases hHeavy with ⟨S, hSA, hS_heavy⟩
    have hS_up : S ∈ upClosureIn X A := subset_upClosureIn hAX hSA
    have hUX : ∀ T ∈ upClosureIn X A, T ⊆ X := by
      intro T hT
      exact (mem_upClosureIn.mp hT).1
    have hmu_lower : p ^ S.card ≤ muP X (upClosureIn X A) p :=
      pow_card_le_muP_of_mem_increasing hp0 hp1 hUX
        (increasingIn_upClosureIn X A) hS_up
    exact hS_heavy.trans hmu_lower
  · have hNoHeavy : ∀ S ∈ A, p ^ S.card < 1 / 2 := by
      intro S hSA
      exact lt_of_not_ge fun hge => hHeavy ⟨S, hSA, hge⟩
    exact hCore X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
      (by simpa [p, m] using hthreshold_lt_one)
      (by simpa [p, m] using hpow_lt)
      (by simpa [p, m] using hNoHeavy)
      hNotSmall

/-- The standard exact-threshold `qSmallUpper` Park--Pham theorem implies the
sparse antichain hard core directly. -/
theorem strictAntichainSparseHardCoreOn_of_threshold_at
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hThresholdAt :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2) :
    StrictAntichainSparseHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti _hA_nonempty _hcard_large _hEmptyA
    hthreshold_lt_one _hpow_lt _hNoHeavy hNotSmall
  have hEll :
      ell X (upClosureIn X A) = max 2 (A.sup Finset.card) :=
    ell_upClosure_eq_of_inclusionAntichain hAnti hAX
  have hthreshold_le :
      CKK * q * Real.log (ell X (upClosureIn X A)) ≤ 1 := by
    simpa [hEll] using hthreshold_lt_one.le
  have hUX : ∀ S ∈ upClosureIn X A, S ⊆ X := by
    intro S hS
    exact (mem_upClosureIn.mp hS).1
  have hmu :=
    hThresholdAt X (upClosureIn X A) q hq0 hq1.le hthreshold_le
      hUX (increasingIn_upClosureIn X A)
      (qSmallUpper_of_not_pSmall hq0.le hNotSmall)
  simpa [hEll] using hmu

/-- The standard larger-density `qSmallUpper` Park--Pham theorem implies the
sparse antichain hard core directly. -/
theorem strictAntichainSparseHardCoreOn_of_threshold
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_pos : 0 < CKK)
    (hThreshold :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2) :
    StrictAntichainSparseHardCoreOn CKK α := by
  refine strictAntichainSparseHardCoreOn_of_threshold_at ?_
  intro X U q hq0 hq1 hthreshold_le hUX hIncr hqSmall
  have hell_ge_one : (1 : ℝ) ≤ (ell X U : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (two_le_ell X U))
  have hlog_nonneg : 0 ≤ Real.log (ell X U) := Real.log_nonneg hell_ge_one
  have hp0 : 0 ≤ CKK * q * Real.log (ell X U) :=
    mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
  exact hThreshold X U q (CKK * q * Real.log (ell X U))
    hq0 hq1 hp0 hthreshold_le le_rfl hUX hIncr hqSmall

/-- The standard exact-threshold `qSmallUpper` Park--Pham theorem also implies
the current reduced antichain hard core directly.  The extra reduced-core
hypotheses are finite reductions that are irrelevant once the standard theorem
is available. -/
theorem strictAntichainReducedHardCoreOn_of_threshold_at
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hThresholdAt :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2) :
    StrictAntichainReducedHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti _hEmptyA _hscale_lt
    hthreshold_lt_one _hNoHeavy hNotSmall
  have hEll :
      ell X (upClosureIn X A) = max 2 (A.sup Finset.card) :=
    ell_upClosure_eq_of_inclusionAntichain hAnti hAX
  have hthreshold_le :
      CKK * q * Real.log (ell X (upClosureIn X A)) ≤ 1 := by
    simpa [hEll] using hthreshold_lt_one.le
  have hUX : ∀ S ∈ upClosureIn X A, S ⊆ X := by
    intro S hS
    exact (mem_upClosureIn.mp hS).1
  have hmu :=
    hThresholdAt X (upClosureIn X A) q hq0 hq1.le hthreshold_le
      hUX (increasingIn_upClosureIn X A)
      (qSmallUpper_of_not_pSmall hq0.le hNotSmall)
  simpa [hEll] using hmu

/-- The standard larger-density `qSmallUpper` Park--Pham theorem also implies
the current reduced antichain hard core directly. -/
theorem strictAntichainReducedHardCoreOn_of_threshold
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_pos : 0 < CKK)
    (hThreshold :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2) :
    StrictAntichainReducedHardCoreOn CKK α := by
  refine strictAntichainReducedHardCoreOn_of_threshold_at ?_
  intro X U q hq0 hq1 hthreshold_le hUX hIncr hqSmall
  have hell_ge_one : (1 : ℝ) ≤ (ell X U : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (two_le_ell X U))
  have hlog_nonneg : 0 ≤ Real.log (ell X U) := Real.log_nonneg hell_ge_one
  have hp0 : 0 ≤ CKK * q * Real.log (ell X U) :=
    mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
  exact hThreshold X U q (CKK * q * Real.log (ell X U))
    hq0 hq1 hp0 hthreshold_le le_rfl hUX hIncr hqSmall

/-- A conventional `ExpectationAtMost`/`CriticalAtMost` exact-threshold
statement also implies the current reduced antichain hard core directly. -/
theorem strictAntichainReducedHardCoreOn_of_expectation_critical
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hThreshold :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ExpectationAtMost X U q →
        CriticalAtMost X U (CKK * q * Real.log (ell X U))) :
    StrictAntichainReducedHardCoreOn CKK α := by
  refine strictAntichainReducedHardCoreOn_of_threshold_at ?_
  intro X U q hq0 hq1 hthreshold_le hUX hIncr hqSmall
  exact (hThreshold X U q hq0 hq1 hthreshold_le hUX hIncr
    ⟨hq0.le, hq1, hqSmall⟩).2.2

/-- On a fixed ground type, a proof of the reduced strict core for a constant
large enough to exclude `q = 1` gives the original strict non-smallness theorem
statement. -/
theorem park_pham_threshold_not_small_lt_of_strict_core_on
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictNonSmallCoreOn CKK α)
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ)
    (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hNotSmall : ¬ pSmall X U q) :
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  by_cases hEmpty : (∅ : Finset α) ∈ U
  · exact park_pham_threshold_not_small_lt_of_empty_mem CKK X U q hUX hIncr hEmpty
  · have hq_lt_one : q < 1 :=
      q_lt_one_of_large_constant_threshold_lt_one hCKK_large hq1 hthreshold_lt_one
    exact hCore X U q hq0 hq_lt_one hthreshold_lt_one hUX hIncr hEmpty hNotSmall

/-- A uniform proof of the low-density hard core gives the public strict
Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_strict_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q hq0 hq1 hthreshold_lt_one hUX hIncr hNotSmall
  exact park_pham_threshold_not_small_lt_of_strict_core_on hCKK_large
    (strict_nonSmallCoreOn_of_hardCoreOn (α := α) hCKK_pos (hCore (α := α)))
    X U q hq0 hq1 hthreshold_lt_one hUX hIncr hNotSmall

/-- A uniform proof of the generated low-density hard core gives the public
strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_generated_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictGeneratedHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_strict_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strict_hardCoreOn_of_generatedHardCoreOn (hCore (α := α)))

/-- A uniform proof of the explicit antichain-generator hard core gives the
public strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_generated_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictGeneratedHardCoreOn_of_antichainHardCoreOn
      (hCore (α := α)))

/-- A uniform proof of the multi-generator antichain hard core gives the
public strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_multi_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainMultiHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainHardCoreOn_of_multiHardCoreOn
      hCKK_large (hCore (α := α)))

/-- A uniform proof of the three-or-more-generator antichain hard core gives
the public strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_large_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainLargeHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_multi_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainMultiHardCoreOn_of_largeHardCoreOn
      hCKK_large (hCore (α := α)))

/-- A uniform proof of the sparse antichain hard core gives the public strict
Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_sparse_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainSparseHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_large_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainLargeHardCoreOn_of_sparseHardCoreOn
      hCKK_large (hCore (α := α)))

/-- The standard exact-threshold `qSmallUpper` form implies the strict
non-smallness package used by this file. -/
theorem park_pham_threshold_not_small_lt_exists_of_threshold_at
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hThresholdAt :
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q hq0 hq1 hthreshold_lt_one hUX hIncr hNotSmall
  exact hThresholdAt X U q hq0 hq1 hthreshold_lt_one.le hUX hIncr
    (qSmallUpper_of_not_pSmall hq0.le hNotSmall)

/-- The standard larger-density `qSmallUpper` form also implies the strict
non-smallness package, by evaluating it at the exact threshold. -/
theorem park_pham_threshold_not_small_lt_exists_of_threshold
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hThreshold :
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  refine park_pham_threshold_not_small_lt_exists_of_threshold_at hCKK_pos ?_
  intro α _ X U q hq0 hq1 hthreshold_le_one hUX hIncr hqSmall
  have hell_ge_one : (1 : ℝ) ≤ (ell X U : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (two_le_ell X U))
  have hlog_nonneg : 0 ≤ Real.log (ell X U) := Real.log_nonneg hell_ge_one
  have hp0 : 0 ≤ CKK * q * Real.log (ell X U) := by positivity
  exact hThreshold X U q (CKK * q * Real.log (ell X U))
    hq0 hq1 hp0 hthreshold_le_one le_rfl hUX hIncr hqSmall

/-- A conventional `ExpectationAtMost`/`CriticalAtMost` exact-threshold
statement implies the strict non-smallness package used by this file. -/
theorem park_pham_threshold_not_small_lt_exists_of_expectation_critical
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hThreshold :
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ExpectationAtMost X U q →
        CriticalAtMost X U (CKK * q * Real.log (ell X U))) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  refine park_pham_threshold_not_small_lt_exists_of_threshold_at hCKK_pos ?_
  intro α _ X U q hq0 hq1 hthreshold_le_one hUX hIncr hqSmall
  exact (hThreshold X U q hq0 hq1 hthreshold_le_one hUX hIncr
    ⟨hq0.le, hq1, hqSmall⟩).2.2

/-- Finite consequence of the sparse hard-core assumptions: if the generator
cover is non-small at `q`, but no generator is individually heavy at the target
density, then some generator has `(C log m)^|S| < |A|`. -/
lemma exists_generator_scale_pow_lt_card_of_sparse
    {α : Type*} [DecidableEq α] {CKK q : ℝ}
    {X : Finset α} {A : Finset (Finset α)}
    (hCKK_pos : 0 < CKK) (hq0 : 0 < q)
    (hNoHeavy :
      ∀ S ∈ A,
        (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
            S.card < 1 / 2)
    (hNotSmall : ¬ pSmall X (upClosureIn X A) q) :
    ∃ S ∈ A,
      (CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^ S.card <
        (A.card : ℝ) := by
  rcases exists_generator_weight_gt_inv_two_mul_card_of_not_pSmall_upClosureIn
      hNotSmall with ⟨S, hSA, hq_weight⟩
  have hA_nonempty : A.Nonempty := ⟨S, hSA⟩
  have hAcard_pos_nat : 0 < A.card := hA_nonempty.card_pos
  have hAcard_pos : 0 < (A.card : ℝ) := by exact_mod_cast hAcard_pos_nat
  have hqpow_pos : 0 < q ^ S.card := pow_pos hq0 _
  have hm_ge_two_nat : 2 ≤ max 2 (A.sup Finset.card) := le_max_left _ _
  have hm_ge_two : (2 : ℝ) ≤ ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    exact_mod_cast hm_ge_two_nat
  have hlog_nonneg :
      0 ≤ Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
    (Real.log_pos (lt_of_lt_of_le (by norm_num) hm_ge_two)).le
  let L : ℝ := CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg hCKK_pos.le hlog_nonneg
  have htarget :
      (L * q) ^ S.card < 1 / 2 := by
    have h := hNoHeavy S hSA
    simpa [L, mul_assoc, mul_left_comm, mul_comm] using h
  have hmul_lt : L ^ S.card * q ^ S.card < 1 / 2 := by
    simpa [mul_pow] using htarget
  have hscale_lt : L ^ S.card < (A.card : ℝ) := by
    by_contra hnot
    have hscale_ge : (A.card : ℝ) ≤ L ^ S.card := le_of_not_gt hnot
    have hmul_ge :
        (A.card : ℝ) * q ^ S.card ≤ L ^ S.card * q ^ S.card :=
      mul_le_mul_of_nonneg_right hscale_ge hqpow_pos.le
    have hquarter_lt : (1 / 2 : ℝ) < (A.card : ℝ) * q ^ S.card := by
      have hden_pos : 0 < 2 * (A.card : ℝ) := by positivity
      rw [div_lt_iff₀ hden_pos] at hq_weight
      nlinarith
    have : (1 / 2 : ℝ) < L ^ S.card * q ^ S.card :=
      hquarter_lt.trans_le hmul_ge
    exact not_lt_of_ge hmul_lt.le this
  exact ⟨S, hSA, by simpa [L] using hscale_lt⟩

/-- Under the sparse hard-core assumptions and a large enough constant, the
generator family must have cardinality larger than the scale `C log m`. -/
lemma scale_lt_card_of_sparse
    {α : Type*} [DecidableEq α] {CKK q : ℝ}
    {X : Finset α} {A : Finset (Finset α)}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK) (hq0 : 0 < q)
    (hEmptyA : (∅ : Finset α) ∉ A)
    (hNoHeavy :
      ∀ S ∈ A,
        (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
            S.card < 1 / 2)
    (hNotSmall : ¬ pSmall X (upClosureIn X A) q) :
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
  rcases exists_generator_scale_pow_lt_card_of_sparse hCKK_pos hq0
      hNoHeavy hNotSmall with ⟨S, hSA, hscale_pow_lt⟩
  let L : ℝ := CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
  have hm_ge_two_nat : 2 ≤ max 2 (A.sup Finset.card) := le_max_left _ _
  have hm_ge_two : (2 : ℝ) ≤ ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    exact_mod_cast hm_ge_two_nat
  have hlog2_le : Real.log 2 ≤
      Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) hm_ge_two
  have hL_ge_two : (2 : ℝ) ≤ L := by
    have hmul := mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
    have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
      have hmul2 := mul_le_mul_of_nonneg_right hCKK_large hlog2_pos.le
      have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
        field_simp [hlog2_pos.ne']
      linarith
    dsimp [L]
    linarith
  have hL_nonneg : 0 ≤ L := by linarith
  have hL_ge_one : (1 : ℝ) ≤ L := by linarith
  have hS_nonempty : S.Nonempty := by
    by_contra hS_empty
    have hS_eq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS_empty
    exact hEmptyA (by simpa [hS_eq] using hSA)
  have hL_le_pow : L ≤ L ^ S.card := by
    cases hcard : S.card with
    | zero =>
        have hbad : S.card ≠ 0 := hS_nonempty.card_pos.ne'
        exact False.elim (hbad hcard)
    | succ n =>
        have hpow_ge_one : (1 : ℝ) ≤ L ^ n := one_le_pow₀ hL_ge_one
        rw [pow_succ]
        nlinarith
  exact lt_of_le_of_lt hL_le_pow (by simpa [L] using hscale_pow_lt)

/-- With a large Park--Pham constant, the scale term is always at least `2`. -/
lemma two_le_scale_of_large_constant
    {α : Type*} {CKK : ℝ} {A : Finset (Finset α)}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK) :
    (2 : ℝ) ≤
      CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
  have hm_ge_two_nat : 2 ≤ max 2 (A.sup Finset.card) := le_max_left _ _
  have hm_ge_two : (2 : ℝ) ≤ ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    exact_mod_cast hm_ge_two_nat
  have hlog2_le :
      Real.log 2 ≤ Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) hm_ge_two
  have hmono :
      CKK * Real.log 2 ≤
        CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
  have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right hCKK_large hlog2_pos.le
    have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
      field_simp [hlog2_pos.ne']
    linarith
  exact htwo_le_CKK_log2.trans hmono

/-- The explicit scale condition forces the generator family to have more than
two members. -/
lemma two_lt_card_of_scale_lt_card
    {α : Type*} {CKK : ℝ} {A : Finset (Finset α)}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hscale :
      CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ)) :
    2 < A.card := by
  have htwo_lt_card_real : (2 : ℝ) < (A.card : ℝ) :=
    lt_of_le_of_lt (two_le_scale_of_large_constant (A := A) hCKK_large) hscale
  exact_mod_cast htwo_lt_card_real

/-- A proof of the scale-only hard core gives the scaled hard core. -/
theorem strictAntichainScaledHardCoreOn_of_scaleOnlyHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictAntichainScaleOnlyHardCoreOn CKK α) :
    StrictAntichainScaledHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti _hA_nonempty _hcard_large hEmptyA
    hscale_lt hthreshold_lt_one hpow_lt hNoHeavy hNotSmall
  exact hCore X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
    hthreshold_lt_one hpow_lt hNoHeavy hNotSmall

/-- A proof of the reduced hard core gives the scale-only hard core. -/
theorem strictAntichainScaleOnlyHardCoreOn_of_reducedHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictAntichainReducedHardCoreOn CKK α) :
    StrictAntichainScaleOnlyHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt hthreshold_lt_one
    _hpow_lt hNoHeavy hNotSmall
  exact hCore X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
    hthreshold_lt_one hNoHeavy hNotSmall

/-- In the reduced scale-only setting, the global low-density condition follows
from the per-generator smallness condition. -/
lemma global_pow_lt_half_of_noHeavy
    {α : Type*} {CKK q : ℝ} {A : Finset (Finset α)}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK) (hq0 : 0 < q)
    (hscale :
      CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ))
    (hthreshold :
      CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1)
    (hNoHeavy :
      ∀ S ∈ A,
        (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
            S.card < 1 / 2) :
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 := by
  have hcard_large : 2 < A.card :=
    two_lt_card_of_scale_lt_card hCKK_large hscale
  have hA_nonempty : A.Nonempty := by
    exact Finset.card_pos.mp (Nat.zero_lt_of_lt hcard_large)
  rcases hA_nonempty with ⟨S, hSA⟩
  let p : ℝ := CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
  have hp0 : 0 ≤ p := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
    have hm_ge_two_nat : 2 ≤ max 2 (A.sup Finset.card) := le_max_left _ _
    have hm_ge_two : (2 : ℝ) ≤ ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
      exact_mod_cast hm_ge_two_nat
    have hlog_nonneg :
        0 ≤ Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
      (Real.log_pos (lt_of_lt_of_le (by norm_num) hm_ge_two)).le
    dsimp [p]
    exact mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
  have hp1 : p ≤ 1 := by
    dsimp [p]
    exact hthreshold.le
  have hS_le : S.card ≤ max 2 (A.sup Finset.card) := by
    exact (Finset.le_sup (s := A) (f := Finset.card) hSA).trans (le_max_right _ _)
  have hpow_le : p ^ max 2 (A.sup Finset.card) ≤ p ^ S.card :=
    pow_le_pow_of_le_one hp0 hp1 hS_le
  have hS_small : p ^ S.card < 1 / 2 := by
    simpa [p] using hNoHeavy S hSA
  exact hpow_le.trans_lt hS_small

/-- It is enough to prove the sparse antichain hard core after explicitly
assuming the scale condition that follows from sparse non-smallness. -/
theorem strictAntichainSparseHardCoreOn_of_scaledHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictAntichainScaledHardCoreOn CKK α) :
    StrictAntichainSparseHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
    hthreshold_lt_one hpow_lt hNoHeavy hNotSmall
  have hscale_lt :
      CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) :=
    scale_lt_card_of_sparse hCKK_large hq0 hEmptyA hNoHeavy hNotSmall
  exact hCore X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
    hscale_lt hthreshold_lt_one hpow_lt hNoHeavy hNotSmall

/-- A uniform proof of the scaled antichain hard core gives the public strict
Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_scaled_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainScaledHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_sparse_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainSparseHardCoreOn_of_scaledHardCoreOn
      hCKK_large (hCore (α := α)))

/-- A uniform proof of the scale-only antichain hard core gives the public
strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_scale_only_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainScaleOnlyHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_scaled_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainScaledHardCoreOn_of_scaleOnlyHardCoreOn
      (hCore (α := α)))

/-- A uniform proof of the reduced antichain hard core gives the public strict
Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_reduced_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainReducedHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_scale_only_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainScaleOnlyHardCoreOn_of_reducedHardCoreOn
      (hCore (α := α)))

/-- A uniform Park--Vondrak certificate for the reduced hard core gives the
public strict Park--Pham package.  This is the current clean finite target for
the threshold theorem. -/
theorem park_pham_threshold_not_small_lt_exists_of_pv_certificate
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCert : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainReducedPVCertificateOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_reduced_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainReducedHardCoreOn_of_pvCertificateOn
      (hCert (α := α)))

/-- A uniform quarter-budget Park--Vondrak certificate also gives the public
strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_pv_quarter_certificate
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCert : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainReducedPVQuarterCertificateOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_reduced_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainReducedHardCoreOn_of_pvQuarterCertificateOn
      (hCert (α := α)))

/-- A uniform coarse numeric Park--Vondrak stage scheme gives the public strict
Park--Pham package.  This is a sufficient reduction, mainly useful as a
bookkeeping bridge; the viable final parameter proof should use the refined
stage-dependent cardinality budget. -/
theorem park_pham_threshold_not_small_lt_exists_of_pv_numeric_scheme
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hScheme : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainReducedPVNumericSchemeOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_pv_quarter_certificate
    hCKK_pos hCKK_large
    (fun {α} _ =>
      strictAntichainReducedPVQuarterCertificateOn_of_numericSchemeOn
        (hScheme (α := α)))

/-- A uniform refined snoc-budget Park--Vondrak stage scheme gives the public
strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_pv_snoc_budget_scheme
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hScheme : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainReducedPVSnocBudgetSchemeOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_pv_quarter_certificate
    hCKK_pos hCKK_large
    (fun {α} _ =>
      strictAntichainReducedPVQuarterCertificateOn_of_snocBudgetSchemeOn
        (hScheme (α := α)))

/-- A pure scalar Park--Vondrak parameter scheme gives the public strict
Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_pv_scalar_parameter_scheme
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hScalar : PVSnocScalarParameterScheme CKK) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_pv_snoc_budget_scheme
    hCKK_pos hCKK_large
    (fun {α} _ =>
      strictAntichainReducedPVSnocBudgetSchemeOn_of_scalarParameterScheme
        (α := α) hScalar)

/-- Existential scalar-parameter form of the Park--Vondrak target.  The concrete
power-of-two scalar schedule below supplies this package. -/
theorem park_pham_threshold_not_small_lt_exists_of_exists_pv_scalar_parameter_scheme
    (hScalar :
      ∃ CKK : ℝ, 0 < CKK ∧ (2 / Real.log 2 : ℝ) ≤ CKK ∧
        PVSnocScalarParameterScheme CKK) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  rcases hScalar with ⟨CKK, hCKK_pos, hCKK_large, hScheme⟩
  exact park_pham_threshold_not_small_lt_exists_of_pv_scalar_parameter_scheme
    hCKK_pos hCKK_large hScheme

/-- **Park–Pham expectation-threshold theorem from non-smallness**
(Kahn–Kalai conjecture, arXiv:2203.17207, proved by J. Park and
H. T. Pham, 2022).

If an increasing family `U` is not `q`-small, then the product measure at
density exactly `C_KK · q · log(ℓ(U))` is at least `1/2`, provided this
density is strictly below `1`.  The family is explicitly required to live on the
finite ground set `X`, matching the Boolean-family statement of
Park--Pham/Kahn--Kalai.

This is the single remaining upstream-Mathlib target for the Park–Pham layer.
All other local monotonicity and finite bookkeeping is proved in this repo. -/
theorem park_pham_threshold_not_small_lt_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_exists_pv_scalar_parameter_scheme
    exists_pv_snoc_scalar_parameter_scheme

/-- The strict Park--Pham constant can be enlarged to dominate
`2 / log 2`.  This is often convenient for excluding impossible endpoint
cases; enlarging the density only increases product measure for increasing
families. -/
theorem park_pham_threshold_not_small_lt_large_exists :
    ∃ CKK : ℝ, 0 < CKK ∧ (2 / Real.log 2 : ℝ) ≤ CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  rcases park_pham_threshold_not_small_lt_exists with ⟨C0, hC0_pos, hThresholdLt⟩
  let CKK : ℝ := max C0 (2 / Real.log 2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCKK_pos : 0 < CKK :=
    lt_of_lt_of_le hC0_pos (le_max_left _ _)
  have hCKK_ge_C0 : C0 ≤ CKK := le_max_left _ _
  have hCKK_ge_log2 : (2 / Real.log 2 : ℝ) ≤ CKK := le_max_right _ _
  refine ⟨CKK, hCKK_pos, hCKK_ge_log2, ?_⟩
  intro α _ X U q hq0 hq1 hthreshold_lt_one hUX hIncr hNotSmall
  have hell_ge_two_nat : 2 ≤ ell X U := two_le_ell X U
  have hell_ge_two : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast hell_ge_two_nat
  have hlog2_le : Real.log 2 ≤ Real.log (ell X U) :=
    Real.log_le_log (by norm_num) hell_ge_two
  have hlog_nonneg : 0 ≤ Real.log (ell X U) :=
    le_trans hlog2_pos.le hlog2_le
  have hscale_nonneg : 0 ≤ q * Real.log (ell X U) :=
    mul_nonneg hq0.le hlog_nonneg
  have hsmall_le_large :
      C0 * q * Real.log (ell X U) ≤
        CKK * q * Real.log (ell X U) := by
    calc
      C0 * q * Real.log (ell X U) = C0 * (q * Real.log (ell X U)) := by ring
      _ ≤ CKK * (q * Real.log (ell X U)) :=
        mul_le_mul_of_nonneg_right hCKK_ge_C0 hscale_nonneg
      _ = CKK * q * Real.log (ell X U) := by ring
  have hsmall_lt_one : C0 * q * Real.log (ell X U) < 1 :=
    lt_of_le_of_lt hsmall_le_large hthreshold_lt_one
  have hAtSmall :
      muP X U (C0 * q * Real.log (ell X U)) ≥ 1 / 2 :=
    hThresholdLt X U q hq0 hq1 hsmall_lt_one hUX hIncr hNotSmall
  have hsmall_nonneg : 0 ≤ C0 * q * Real.log (ell X U) := by
    positivity
  have hmono :
      muP X U (C0 * q * Real.log (ell X U)) ≤
        muP X U (CKK * q * Real.log (ell X U)) :=
    muP_mono_density hIncr hsmall_nonneg hsmall_le_large hthreshold_lt_one.le
  exact hAtSmall.trans hmono

/-- **Park–Pham expectation-threshold theorem from non-smallness**, with the
closed endpoint `C_KK · q · log(ℓ(U)) ≤ 1`.

The only deep input needed here is the strict case
`park_pham_threshold_not_small_lt_exists`.  If the threshold density is exactly
`1`, non-smallness makes `U` nonempty; since `U` is increasing on `X`, it
contains `X`, and its product measure at density `1` is exactly `1`. -/
theorem park_pham_threshold_not_small_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  rcases park_pham_threshold_not_small_lt_exists with ⟨CKK, hCKK_pos, hThresholdLt⟩
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q hq0 hq1 hthreshold_le_one hUX hIncr hNotSmall
  by_cases hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1
  · exact hThresholdLt X U q hq0 hq1 hthreshold_lt_one hUX hIncr hNotSmall
  · have hthreshold_eq_one : CKK * q * Real.log (ell X U) = 1 :=
      le_antisymm hthreshold_le_one (le_of_not_gt hthreshold_lt_one)
    have hU_nonempty : U.Nonempty := nonempty_of_not_pSmall hNotSmall
    have hmu_one : muP X U (1 : ℝ) = 1 :=
      muP_one_of_nonempty_increasing hUX hIncr hU_nonempty
    rw [hthreshold_eq_one, hmu_one]
    norm_num

/-- **Park–Pham expectation-threshold theorem at the exact threshold**, in the
`qSmallUpper` form used downstream.  This follows from the primitive
non-smallness form by applying it at `2q` when `q ≤ 1/2`, and at `1` when
`q > 1/2`; the constant is enlarged by an absolute factor. -/
theorem park_pham_threshold_at_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  rcases park_pham_threshold_not_small_exists with ⟨C0, hC0_pos, hThresholdNS⟩
  let CKK : ℝ := max (2 * C0) (2 / Real.log 2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCKK_pos : 0 < CKK := by
    exact lt_of_lt_of_le (mul_pos (by norm_num) hC0_pos) (le_max_left _ _)
  have hCKK_ge_2C0 : 2 * C0 ≤ CKK := le_max_left _ _
  have hCKK_ge_2_log2 : 2 / Real.log 2 ≤ CKK := le_max_right _ _
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q hq0 hq1 hthreshold_le_one hUX hIncr hqSmall
  have hell_ge_two_nat : 2 ≤ ell X U := two_le_ell X U
  have hell_ge_two : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast hell_ge_two_nat
  have hell_pos : 0 < (ell X U : ℝ) := by positivity
  have hlog2_le : Real.log 2 ≤ Real.log (ell X U) :=
    Real.log_le_log (by norm_num) hell_ge_two
  have hlog_nonneg : 0 ≤ Real.log (ell X U) :=
    le_trans hlog2_pos.le hlog2_le
  have htarget_nonneg : 0 ≤ CKK * q * Real.log (ell X U) := by positivity
  by_cases hq_half : q ≤ (1 / 2 : ℝ)
  · let q' : ℝ := 2 * q
    have hq'_pos : 0 < q' := by dsimp [q']; positivity
    have hq'_le_one : q' ≤ 1 := by dsimp [q']; linarith
    have hq_lt_q' : q < q' := by dsimp [q']; linarith
    have hnotSmall : ¬ pSmall X U q' :=
      hqSmall q' hq_lt_q' hq'_le_one
    have hsmall_threshold_le :
        C0 * q' * Real.log (ell X U) ≤ 1 := by
      have hC0q_le : C0 * q' ≤ CKK * q := by
        dsimp [q']
        nlinarith [hCKK_ge_2C0, hq0.le]
      have hle :
          C0 * q' * Real.log (ell X U) ≤
            CKK * q * Real.log (ell X U) := by
        exact mul_le_mul_of_nonneg_right hC0q_le hlog_nonneg
      exact hle.trans hthreshold_le_one
    have hAtSmall :
        muP X U (C0 * q' * Real.log (ell X U)) ≥ 1 / 2 :=
      hThresholdNS X U q' hq'_pos hq'_le_one hsmall_threshold_le hUX hIncr hnotSmall
    have hsmall_nonneg :
        0 ≤ C0 * q' * Real.log (ell X U) := by positivity
    have hsmall_le_target :
        C0 * q' * Real.log (ell X U) ≤
          CKK * q * Real.log (ell X U) := by
      have hC0q_le : C0 * q' ≤ CKK * q := by
        dsimp [q']
        nlinarith [hCKK_ge_2C0, hq0.le]
      exact mul_le_mul_of_nonneg_right hC0q_le hlog_nonneg
    have hmono :
        muP X U (C0 * q' * Real.log (ell X U)) ≤
          muP X U (CKK * q * Real.log (ell X U)) :=
      muP_mono_density hIncr hsmall_nonneg hsmall_le_target hthreshold_le_one
    exact hAtSmall.trans hmono
  · have hq_gt_half : (1 / 2 : ℝ) < q := lt_of_not_ge hq_half
    have hq_lt_one : q < 1 :=
      q_lt_one_of_large_constant_threshold_le_one hCKK_ge_2_log2 hq1 hthreshold_le_one
    have hnotSmall : ¬ pSmall X U (1 : ℝ) :=
      hqSmall 1 hq_lt_one le_rfl
    have hC0_log_le_target :
        C0 * 1 * Real.log (ell X U) ≤
          CKK * q * Real.log (ell X U) := by
      have hC0_le_CKKq : C0 * 1 ≤ CKK * q := by
        nlinarith [hCKK_ge_2C0, hq_gt_half, hC0_pos.le]
      exact mul_le_mul_of_nonneg_right hC0_le_CKKq hlog_nonneg
    have hsmall_threshold_le :
        C0 * 1 * Real.log (ell X U) ≤ 1 :=
      hC0_log_le_target.trans hthreshold_le_one
    have hAtSmall :
        muP X U (C0 * 1 * Real.log (ell X U)) ≥ 1 / 2 :=
      hThresholdNS X U 1 (by norm_num) le_rfl hsmall_threshold_le hUX hIncr hnotSmall
    have hsmall_nonneg :
        0 ≤ C0 * 1 * Real.log (ell X U) := by positivity
    have hmono :
        muP X U (C0 * 1 * Real.log (ell X U)) ≤
          muP X U (CKK * q * Real.log (ell X U)) :=
      muP_mono_density hIncr hsmall_nonneg hC0_log_le_target hthreshold_le_one
    exact hAtSmall.trans hmono

/-- **Park–Pham expectation-threshold theorem** (Kahn–Kalai conjecture,
arXiv:2203.17207, proved by J. Park and H. T. Pham, 2022).

If `q` upper-bounds the expectation threshold of an increasing family
`U`, then the product measure at any density `p` at or above
`C_KK · q · log(ℓ(U))` is at least `1/2`.

This is the downstream-friendly "any `p` at or above the threshold" form,
derived from `park_pham_threshold_at_exists` and `muP_mono_density`. -/
theorem park_pham_threshold_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2 := by
  rcases park_pham_threshold_at_exists with ⟨CKK, hCKK_pos, hThresholdAt⟩
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q p hq0 hq1 hp0 hp1 hDensity hUX hIncr hSmall
  have hell_ge_one : (1 : ℝ) ≤ (ell X U : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (two_le_ell X U))
  have hlog_nonneg : 0 ≤ Real.log (ell X U) := Real.log_nonneg hell_ge_one
  have hthreshold_nonneg :
      0 ≤ CKK * q * Real.log (ell X U) := by positivity
  have hthreshold_le_one :
      CKK * q * Real.log (ell X U) ≤ 1 := hDensity.trans hp1
  have hAt :
      muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 :=
    hThresholdAt X U q hq0 hq1 hthreshold_le_one hUX hIncr hSmall
  have hmono :
      muP X U (CKK * q * Real.log (ell X U)) ≤ muP X U p :=
    muP_mono_density hIncr hthreshold_nonneg hDensity hp1
  exact hAt.trans hmono

end ParkPham
end Erdos202


/-! =============================================================
    Section from: Erdos/P202/ParkPham/ParkPhamTheorem.lean
    ============================================================= -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 5.

Consequences of the Park–Pham threshold theorem for spread families:

1. `pSmall_mono_density`: `pSmall` decreases monotonically as `p` decreases.
2. `qSmallUpper_of_not_pSmall`: lifting `¬ pSmall at p₀` to
   `qSmallUpper X U p₀`.
3. `not_pSmall_of_spread`: the counting argument showing that the upper
   closure of a `κ`-spread family is not `p`-small at `p = κ⁻¹`. **Proved.**
4. `mu_at_partition_density_ge_half`: chains (3), (2), and
   `park_pham_threshold` to get `muP ≥ 1/2` at density `1/(2r)` when
   `κ ≥ Csp · r · log(ek)`. **Proved against the threshold package.**
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-! ## Counting argument: spread families are not small -/

/-- If `A` is a `κ`-spread nonempty `k`-uniform family with `k ≥ 1` and
`1 < κ`, then `upClosureIn X A` is not `p`-small at `p = κ⁻¹`. -/
theorem not_pSmall_of_spread
    {X : Finset α} {A : Finset (Finset α)} {k : ℕ} {κ : ℝ}
    (hA : A.Nonempty) (_hk : 1 ≤ k)
    (_hUniform : Erdos202.UniformFamily A k)
    (hSpread : Erdos202.SpreadFamily A κ)
    (hκ : 1 < κ)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    ¬ pSmall X (upClosureIn X A) (κ⁻¹) := by
  classical
  intro hSmall
  rcases hSmall with ⟨G, hCover, hsum⟩
  have hκ_pos : 0 < κ := by linarith
  have hAcard_pos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  -- Step 1: every S ∈ A is covered by some T ∈ G.
  have hCoverA : ∀ S ∈ A, ∃ T ∈ G, T ⊆ S := by
    intro S hSA
    have hSup : S ∈ upClosureIn X A :=
      mem_upClosureIn.mpr ⟨hAX S hSA, S, hSA, subset_refl _⟩
    exact hCover S hSup
  -- Step 2: A ⊆ ⋃_T∈G {S ∈ A : T ⊆ S}.
  have hAcover : A ⊆ G.biUnion fun T => A.filter fun S => T ⊆ S := by
    intro S hSA
    rcases hCoverA S hSA with ⟨T, hTG, hTS⟩
    exact Finset.mem_biUnion.mpr ⟨T, hTG, Finset.mem_filter.mpr ⟨hSA, hTS⟩⟩
  have hAcardle_nat :
      A.card ≤ ∑ T ∈ G, (A.filter fun S => T ⊆ S).card :=
    (Finset.card_le_card hAcover).trans Finset.card_biUnion_le
  have hAcardle :
      (A.card : ℝ) ≤ ∑ T ∈ G, ((A.filter fun S => T ⊆ S).card : ℝ) := by
    have h := hAcardle_nat
    have : ((A.card : ℕ) : ℝ) ≤
        (((∑ T ∈ G, (A.filter fun S => T ⊆ S).card : ℕ) : ℝ)) := by
      exact_mod_cast h
    rw [Nat.cast_sum] at this
    exact this
  -- Step 3: per-term bound using spread.
  have hbound : ∀ T ∈ G,
      ((A.filter fun S => T ⊆ S).card : ℝ) ≤ (A.card : ℝ) * (κ ^ T.card)⁻¹ := by
    intro T _
    by_cases hTne : T.Nonempty
    · have := hSpread T hTne
      rw [div_eq_mul_inv] at this
      exact this
    · have heq : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
      subst heq
      have hfilter_eq : (A.filter fun S => (∅ : Finset α) ⊆ S) = A := by
        apply Finset.filter_eq_self.mpr
        intro S _
        exact Finset.empty_subset S
      rw [hfilter_eq]
      simp
  -- Step 4: sum.
  have hAsum :
      (A.card : ℝ) ≤ ∑ T ∈ G, (A.card : ℝ) * (κ ^ T.card)⁻¹ :=
    hAcardle.trans (Finset.sum_le_sum hbound)
  -- Convert RHS into |A| * Σ (κ⁻¹)^|T|.
  have hkey :
      (∑ T ∈ G, (A.card : ℝ) * (κ ^ T.card)⁻¹) =
        (A.card : ℝ) * (∑ T ∈ G, (κ⁻¹) ^ T.card) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro T _
    rw [← inv_pow]
  rw [hkey] at hAsum
  -- Step 5: divide by |A|.
  have hsum_ge_one : (1 : ℝ) ≤ ∑ T ∈ G, (κ⁻¹) ^ T.card := by
    have hAsum' : (A.card : ℝ) * 1 ≤
        (A.card : ℝ) * (∑ T ∈ G, (κ⁻¹) ^ T.card) := by
      simpa using hAsum
    exact le_of_mul_le_mul_left hAsum' hAcard_pos
  -- Step 6: but hsum says the sum is ≤ 1/2 < 1. Contradiction.
  linarith

/-! ## Main consequence: muP ≥ 1/2 at partition density

The chain is:
1. `not_pSmall_of_spread` gives `¬ pSmall X (upClosureIn X A) (1/κ)`.
2. `qSmallUpper_of_not_pSmall` lifts to `qSmallUpper X U (1/κ)`.
3. `park_pham_threshold` gives `muP ≥ 1/2` at any density
   `≥ CKK · (1/κ) · log(ell U)`.
4. From `κ ≥ Csp · r · log(ek)` and `ell U ≤ max 2 k ≤ ek`, derive
   `CKK · (1/κ) · log(ell U) ≤ 1/(2r)` with `Csp := max 10 (8 · CKK)`.

The bookkeeping in step 4 is purely algebraic (log inequalities and a few
positivity arguments). It is isolated behind the named Park--Pham threshold
target for a focused subpass. -/

/-- The spread-disjointness constant produced from a Park–Pham threshold
constant. -/
noncomputable def CspOf (CKK : ℝ) : ℝ :=
  max 10 (8 * CKK)

lemma CspOf_pos (CKK : ℝ) : 0 < CspOf CKK := by
  unfold CspOf
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  norm_num

lemma CspOf_ge_ten (CKK : ℝ) : (10 : ℝ) ≤ CspOf CKK := le_max_left _ _

lemma CspOf_ge_two_CKK {CKK : ℝ} (hCKK_pos : 0 < CKK) :
    2 * CKK ≤ CspOf CKK := by
  unfold CspOf
  refine le_trans ?_ (le_max_right _ _)
  linarith

/-- Helper: universe-monomorphic density bound. Takes `CKK` as an opaque
real parameter so elaboration doesn't drag `Classical.choose` through. -/
private lemma density_bound_from_kappa_aux
    (CKK Csp : ℝ) (hCKK_pos : 0 < CKK) (hCsp_ge_2CKK : 2 * CKK ≤ Csp)
    {ell_real κ : ℝ} {r k : ℕ}
    (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hell_real_pos : 0 < ell_real)
    (hell_ge_one : 1 ≤ ell_real)
    (hell_le_ek : ell_real ≤ Real.exp 1 * (k : ℝ))
    (hκ_pos : 0 < κ)
    (hκ : Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ) :
    CKK * κ⁻¹ * Real.log ell_real ≤ (1 : ℝ) / (2 * (r : ℝ)) := by
  have hr_real_ge_two : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr_real_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hk_real_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hek_pos : 0 < Real.exp 1 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk_real_ge_one
    positivity
  have hlog_ek_pos : 0 < Real.log (Real.exp 1 * (k : ℝ)) := by
    have he : (1 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    have hek_ge_e : Real.exp 1 ≤ Real.exp 1 * (k : ℝ) := by
      nlinarith [Real.exp_pos (1 : ℝ)]
    refine Real.log_pos ?_
    linarith
  have hlog_ell_le : Real.log ell_real ≤ Real.log (Real.exp 1 * (k : ℝ)) :=
    Real.log_le_log hell_real_pos hell_le_ek
  have hlog_ell_nonneg : 0 ≤ Real.log ell_real := Real.log_nonneg hell_ge_one
  have h2CKKr_nn : 0 ≤ 2 * CKK * (r : ℝ) := by positivity
  have hκ_lower : 2 * CKK * (r : ℝ) * Real.log ell_real ≤ κ := by
    have s1 : 2 * CKK * (r : ℝ) * Real.log ell_real ≤
        2 * CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_ell_le h2CKKr_nn
    have s2 : 2 * CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤
        Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
      have hrlog_nn : 0 ≤ (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
        positivity
      nlinarith
    linarith
  have h2r_pos : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  have hLHS_eq : CKK * κ⁻¹ * Real.log ell_real =
      CKK * Real.log ell_real / κ := by ring
  rw [hLHS_eq, div_le_div_iff₀ hκ_pos h2r_pos]
  have heq : CKK * Real.log ell_real * (2 * (r : ℝ)) =
      2 * CKK * (r : ℝ) * Real.log ell_real := by ring
  rw [heq, one_mul]
  exact hκ_lower

/-- **Partition-density lower bound, parameterized by a Park–Pham threshold
constant and theorem.** Chains `not_pSmall_of_spread`,
`qSmallUpper_of_not_pSmall`, `density_bound_from_kappa_aux`, and the supplied
threshold theorem. -/
theorem mu_at_partition_density_ge_half_of_threshold
    (CKK : ℝ) (hCKK_pos : 0 < CKK)
    (hThreshold :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2)
    {X : Finset α} {A : Finset (Finset α)} {r k : ℕ} {κ : ℝ}
    (hA : A.Nonempty) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hUniform : Erdos202.UniformFamily A k)
    (hSpread : Erdos202.SpreadFamily A κ)
    (hAX : ∀ S ∈ A, S ⊆ X)
    (hκ : CspOf CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ) :
    muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 := by
  set U := upClosureIn X A with hU_def
  -- Reals from naturals
  have hr_real_ge_two : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr_real_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hk_real_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := by linarith
  -- e > 2 and log(e·k) ≥ 1
  have he_gt_two : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have hek_pos : (0 : ℝ) < Real.exp 1 * (k : ℝ) := by positivity
  have hek_ge_e : Real.exp 1 ≤ Real.exp 1 * (k : ℝ) := by
    have h1 : Real.exp 1 * 1 ≤ Real.exp 1 * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hk_real_ge_one he_pos.le
    simpa using h1
  have hlog_ek_ge_one : (1 : ℝ) ≤ Real.log (Real.exp 1 * (k : ℝ)) := by
    have h := Real.log_le_log he_pos hek_ge_e
    simpa [Real.log_exp] using h
  -- κ ≥ 20 > 1
  have hCsp_ge_ten : (10 : ℝ) ≤ CspOf CKK := CspOf_ge_ten CKK
  have hCsp_pos : 0 < CspOf CKK := CspOf_pos CKK
  have hbase_ge_20 :
      (20 : ℝ) ≤ CspOf CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
    have h1 : (10 : ℝ) * 2 ≤ CspOf CKK * (r : ℝ) :=
      mul_le_mul hCsp_ge_ten hr_real_ge_two (by norm_num) hCsp_pos.le
    have h2 :
        CspOf CKK * (r : ℝ) * 1 ≤
          CspOf CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_ek_ge_one (by positivity)
    linarith
  have hκ_ge_20 : (20 : ℝ) ≤ κ := le_trans hbase_ge_20 hκ
  have hκ_pos : 0 < κ := by linarith
  have hκ_gt_one : 1 < κ := by linarith
  have hκ_ge_one : (1 : ℝ) ≤ κ := hκ_gt_one.le
  have hκ_inv_pos : (0 : ℝ) < κ⁻¹ := inv_pos.mpr hκ_pos
  have hκ_inv_le_one : κ⁻¹ ≤ 1 := by
    have h := inv_anti₀ (by linarith : (0 : ℝ) < 1) hκ_ge_one
    simpa using h
  -- Increasing + not p-small + qSmallUpper
  have hIncr : IncreasingIn X U := increasingIn_upClosureIn X A
  have hUXU : ∀ S ∈ U, S ⊆ X := by
    intro S hS
    have hS' : S ∈ upClosureIn X A := by simpa [hU_def] using hS
    exact (mem_upClosureIn.mp hS').1
  have hNotSmall : ¬ pSmall X U (κ⁻¹) :=
    not_pSmall_of_spread hA hk hUniform hSpread hκ_gt_one hAX
  have hqSmall : qSmallUpper X U (κ⁻¹) :=
    qSmallUpper_of_not_pSmall hκ_inv_pos.le hNotSmall
  -- ell bounds
  have hell_pos_nat : 0 < ell X U := ell_pos X U
  have hell_real_pos : (0 : ℝ) < (ell X U : ℝ) := by exact_mod_cast hell_pos_nat
  have hell_ge_one : (1 : ℝ) ≤ (ell X U : ℝ) := by
    have h := two_le_ell X U
    have h1 : 1 ≤ ell X U := le_trans (by norm_num) h
    exact_mod_cast h1
  have hell_le_max : ell X U ≤ max 2 k := ell_upClosure_le hUniform hAX
  have hmax_le_ek : ((max 2 k : ℕ) : ℝ) ≤ Real.exp 1 * (k : ℝ) := by
    rcases Nat.lt_or_ge k 2 with hk2 | h2k
    · interval_cases k
      · have : (max 2 1 : ℕ) = 2 := by decide
        rw [this]
        have : ((2 : ℕ) : ℝ) = 2 := by norm_num
        rw [this]
        linarith
    · have hmax : max 2 k = k := max_eq_right h2k
      rw [hmax]
      have he_ge_one : (1 : ℝ) ≤ Real.exp 1 := by linarith
      nlinarith
  have hell_real_le_ek : (ell X U : ℝ) ≤ Real.exp 1 * (k : ℝ) := by
    have h1 : ((ell X U : ℕ) : ℝ) ≤ ((max 2 k : ℕ) : ℝ) := by exact_mod_cast hell_le_max
    exact h1.trans hmax_le_ek
  -- Density bound: CKK * κ⁻¹ * log(ell U) ≤ 1/(2r)
  have h_density_bound :
      CKK * κ⁻¹ * Real.log (ell X U) ≤ (1 : ℝ) / (2 * (r : ℝ)) :=
    density_bound_from_kappa_aux CKK (CspOf CKK) hCKK_pos
      (CspOf_ge_two_CKK hCKK_pos)
      hr hk hell_real_pos hell_ge_one hell_real_le_ek hκ_pos hκ
  -- Density at-or-above-threshold positivity bounds
  have h2r_pos : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  have h_p_nn : (0 : ℝ) ≤ (1 : ℝ) / (2 * (r : ℝ)) := by positivity
  have h_p_le_one : (1 : ℝ) / (2 * (r : ℝ)) ≤ 1 := by
    rw [div_le_one h2r_pos]
    linarith
  -- Apply the Park–Pham threshold theorem.
  have hgoal :
      muP X U ((1 : ℝ) / (2 * (r : ℝ))) ≥ 1 / 2 :=
    hThreshold X U (κ⁻¹) ((1 : ℝ) / (2 * (r : ℝ)))
      hκ_inv_pos hκ_inv_le_one h_p_nn h_p_le_one h_density_bound hUXU hIncr hqSmall
  simpa [hU_def] using hgoal

end

end ParkPham
end Erdos202


/-! =============================================================
    Section from: Erdos/P202/ParkPham/SpreadDisjointness.lean
    ============================================================= -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 6.

Final spread-disjointness theorem via the random-partition argument.

# Strategy

Given a κ-spread, k-uniform, nonempty family A with
`κ ≥ Csp · r · log(ek)`:

1. By `mu_at_partition_density_ge_half`, the Bernoulli measure of
   `upClosureIn X A` at density `1/(2r)` is at least `1/2`.
2. Equivalently (via the random-partition / coloring identification): for
   a uniformly random coloring `c : X → Fin (2r)`, the expected number
   of color classes `c⁻¹(i)` that contain a member of A is at least `r`.
3. Hence there exists a coloring with at least `r` "successful" parts.
4. Pick one member of A inside each successful part. The parts are
   pairwise disjoint, so the chosen members are pairwise disjoint.

The translation from "muP ≥ 1/2" to "∃ r pairwise-disjoint members"
(steps 2-4) is purely finite/discrete bookkeeping with no analytic
content.  This file proves that bookkeeping directly, then combines it
with the named Park--Pham threshold package.
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

section

variable {α : Type*} [DecidableEq α]

/-- **Coloring of a finite universe.** A `Fin m`-valued labeling of the
elements of `X` (encoded as a function on the subtype `{x // x ∈ X}`).

The set of colorings is finite (a finite product of `Fin m`). A
uniformly random coloring corresponds to the discrete uniform measure
on this finite set, and color classes have the same marginal as a
random subset at density `1/m`. -/
abbrev Coloring (X : Finset α) (m : ℕ) :=
  {x // x ∈ X} → Fin m

/-- The `i`th part of a coloring as a `Finset α`. -/
noncomputable def colorPart {X : Finset α} {m : ℕ} (c : Coloring X m)
    (i : Fin m) : Finset α :=
  Finset.image Subtype.val (X.attach.filter (fun x => c x = i))

/-- Membership in a color class, unpacked to an element of `X` with the
specified color. -/
lemma mem_colorPart {X : Finset α} {m : ℕ} (c : Coloring X m)
    (i : Fin m) {x : α} :
    x ∈ colorPart c i ↔ ∃ hx : x ∈ X, c ⟨x, hx⟩ = i := by
  simp [colorPart]

lemma colorPart_subset {X : Finset α} {m : ℕ} (c : Coloring X m)
    (i : Fin m) :
    colorPart c i ⊆ X := by
  intro x hx
  rcases (mem_colorPart c i).1 hx with ⟨hxX, _⟩
  exact hxX

lemma colorPart_disjoint {X : Finset α} {m : ℕ} (c : Coloring X m)
    {i j : Fin m} (hij : i ≠ j) :
    Disjoint (colorPart c i) (colorPart c j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rcases (mem_colorPart c i).1 hxi with ⟨hxX, hxi'⟩
  rcases (mem_colorPart c j).1 hxj with ⟨_, hxj'⟩
  exact hij (hxi'.symm.trans hxj')

lemma colorPart_eq_iff {X T : Finset α} (hTX : T ⊆ X) {m : ℕ}
    (c : Coloring X m) (i : Fin m) :
    colorPart c i = T ↔ ∀ x : {x // x ∈ X}, (x.1 ∈ T ↔ c x = i) := by
  constructor
  · intro h x
    constructor
    · intro hxT
      have hxpart : x.1 ∈ colorPart c i := by simpa [h] using hxT
      rcases (mem_colorPart c i).1 hxpart with ⟨hxX, hxci⟩
      have hx_eq : (⟨x.1, hxX⟩ : {x // x ∈ X}) = x := by ext; rfl
      simpa [hx_eq] using hxci
    · intro hci
      have hxpart : x.1 ∈ colorPart c i :=
        (mem_colorPart c i).2 ⟨x.2, hci⟩
      simpa [h] using hxpart
  · intro h
    ext a
    constructor
    · intro ha
      rcases (mem_colorPart c i).1 ha with ⟨haX, hci⟩
      exact (h ⟨a, haX⟩).2 hci
    · intro haT
      have haX : a ∈ X := hTX haT
      exact (mem_colorPart c i).2 ⟨haX, (h ⟨a, haX⟩).1 haT⟩

/-- A fixed color class `T` leaves arbitrary choices of colors different from
`i` on `X \ T`. -/
noncomputable def colorPartFiberEquiv {X T : Finset α} (hTX : T ⊆ X)
    {m : ℕ} (i : Fin m) :
    {c : Coloring X m // colorPart c i = T} ≃
      ({x // x ∈ X \ T} → {j : Fin m // j ≠ i}) where
  toFun c x := by
    refine ⟨c.1 ⟨x.1, (Finset.mem_sdiff.1 x.2).1⟩, ?_⟩
    intro hc
    have hxT : x.1 ∈ T :=
      ((colorPart_eq_iff hTX c.1 i).1 c.2
        ⟨x.1, (Finset.mem_sdiff.1 x.2).1⟩).2 hc
    exact (Finset.mem_sdiff.1 x.2).2 hxT
  invFun g := by
    refine ⟨(fun x =>
      if hxT : x.1 ∈ T then i
      else (g ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hxT⟩⟩).1), ?_⟩
    rw [colorPart_eq_iff hTX]
    intro x
    constructor
    · intro hxT
      simp [hxT]
    · intro hxcolor
      by_contra hxT
      have hg_ne : (g ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hxT⟩⟩).1 ≠ i :=
        (g ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hxT⟩⟩).2
      simp [hxT] at hxcolor
      exact hg_ne hxcolor
  left_inv c := by
    ext x
    by_cases hxT : x.1 ∈ T
    · have hxcolor : c.1 x = i :=
        ((colorPart_eq_iff hTX c.1 i).1 c.2 x).1 hxT
      simp [hxT, hxcolor]
    · simp [hxT]
  right_inv g := by
    funext x
    apply Subtype.ext
    have hxT : x.1 ∉ T := (Finset.mem_sdiff.1 x.2).2
    simp [hxT]

lemma colorPart_fiber_card {X T : Finset α} (hTX : T ⊆ X)
    {m : ℕ} (i : Fin m) :
    ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => colorPart c i = T)).card =
      (m - 1) ^ (X.card - T.card) := by
  classical
  have hleft :
      Fintype.card {c : Coloring X m // colorPart c i = T} =
        ((Finset.univ : Finset (Coloring X m)).filter
          (fun c => colorPart c i = T)).card := by
    exact Fintype.card_ofFinset _ (by
      intro c
      change c ∈ ((Finset.univ : Finset (Coloring X m)).filter
          (fun c => colorPart c i = T)) ↔ colorPart c i = T
      simp)
  have hcongr :
      Fintype.card {c : Coloring X m // colorPart c i = T} =
        Fintype.card ({x // x ∈ X \ T} → {j : Fin m // j ≠ i}) :=
    Fintype.card_congr (colorPartFiberEquiv hTX i)
  have hcod : Fintype.card {j : Fin m // j ≠ i} = m - 1 := by
    have hcompl := Fintype.card_subtype_compl (fun j : Fin m => j = i)
    simp [Fintype.card_fin] at hcompl ⊢
  have hdom : Fintype.card {x // x ∈ X \ T} = X.card - T.card := by
    calc
      Fintype.card {x // x ∈ X \ T} = (X \ T).card := by
          exact Fintype.card_ofFinset _ (by
            intro x
            change x ∈ X \ T ↔ x ∈ X \ T
            rfl)
      _ = X.card - T.card := Finset.card_sdiff_of_subset hTX
  rw [← hleft, hcongr, Fintype.card_fun, hcod, hdom]

lemma coloring_card (X : Finset α) (m : ℕ) :
    Fintype.card (Coloring X m) = m ^ X.card := by
  rw [Fintype.card_fun, Fintype.card_fin]
  congr
  exact Fintype.card_coe X

omit [DecidableEq α] in
lemma bernoulliMass_inv_nat_mul_card {X T : Finset α} (hTX : T ⊆ X)
    {m : ℕ} (hm : 0 < m) :
    ((m : ℝ) ^ X.card) *
        bernoulliMass X T ((1 : ℝ) / m) =
      ((m - 1 : ℕ) : ℝ) ^ (X.card - T.card) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcard_le : T.card ≤ X.card := Finset.card_le_card hTX
  have hsplit : X.card = T.card + (X.card - T.card) :=
    (Nat.add_sub_of_le hcard_le).symm
  have hone :
      (1 : ℝ) - (1 : ℝ) / m = ((m - 1 : ℕ) : ℝ) / m := by
    have hm1 : 1 ≤ m := hm
    rw [Nat.cast_sub hm1]
    field_simp [hmR]
    ring
  unfold bernoulliMass
  rw [hone, hsplit, Nat.add_sub_cancel_left, pow_add]
  rw [div_pow, div_pow]
  field_simp [hmR]
  ring

/-- Colors whose class contains at least one member of `A`. -/
noncomputable def successfulColors {X : Finset α} {m : ℕ}
    (A : Finset (Finset α)) (c : Coloring X m) : Finset (Fin m) :=
  Finset.univ.filter fun i => ∃ S ∈ A, S ⊆ colorPart c i

lemma mem_successfulColors {X : Finset α} {m : ℕ}
    {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m} :
    i ∈ successfulColors A c ↔ ∃ S ∈ A, S ⊆ colorPart c i := by
  simp [successfulColors]

lemma mem_successfulColors_iff_colorPart_mem_upClosureIn {X : Finset α} {m : ℕ}
    {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m} :
    i ∈ successfulColors A c ↔ colorPart c i ∈ upClosureIn X A := by
  rw [mem_successfulColors, mem_upClosureIn]
  exact ⟨fun h => ⟨colorPart_subset c i, h⟩, fun h => h.2⟩

lemma successful_colorings_card (X : Finset α) (A : Finset (Finset α))
    {m : ℕ} (i : Fin m) :
    ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card =
      ∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
        (m - 1) ^ (X.card - T.card) := by
  classical
  let s : Finset (Coloring X m) :=
    (Finset.univ : Finset (Coloring X m)).filter
      (fun c => i ∈ successfulColors A c)
  let t : Finset (Finset α) :=
    X.powerset.filter (fun T => T ∈ upClosureIn X A)
  have hmaps : Set.MapsTo (fun c : Coloring X m => colorPart c i) (↑s) (↑t) := by
    intro c hc
    have hsucc : i ∈ successfulColors A c := by
      simpa [s] using hc
    exact Finset.mem_filter.2
      ⟨Finset.mem_powerset.2 (colorPart_subset c i),
        (mem_successfulColors_iff_colorPart_mem_upClosureIn).1 hsucc⟩
  calc
    ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card
        = s.card := rfl
    _ = ∑ T ∈ t, {c ∈ s | colorPart c i = T}.card :=
        Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ T ∈ t, (m - 1) ^ (X.card - T.card) := by
        apply Finset.sum_congr rfl
        intro T hT
        have hTX : T ⊆ X := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
        have hTU : T ∈ upClosureIn X A := (Finset.mem_filter.1 hT).2
        have hfiber :
            {c ∈ s | colorPart c i = T} =
              (Finset.univ : Finset (Coloring X m)).filter
                (fun c => colorPart c i = T) := by
          ext c
          constructor
          · intro hc
            exact Finset.mem_filter.2 ⟨Finset.mem_univ c, (Finset.mem_filter.1 hc).2⟩
          · intro hc
            have hct : colorPart c i = T := (Finset.mem_filter.1 hc).2
            have hsucc : i ∈ successfulColors A c := by
              rw [mem_successfulColors_iff_colorPart_mem_upClosureIn, hct]
              exact hTU
            exact Finset.mem_filter.2
              ⟨by simpa [s] using hsucc, hct⟩
        rw [hfiber, colorPart_fiber_card hTX i]

lemma successful_colorings_card_real (X : Finset α) (A : Finset (Finset α))
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    (((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card : ℝ) =
      (Fintype.card (Coloring X m) : ℝ) *
        muP X (upClosureIn X A) ((1 : ℝ) / m) := by
  classical
  rw [successful_colorings_card X A i, coloring_card]
  unfold muP
  rw [Nat.cast_sum]
  calc
    (∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
        (((m - 1) ^ (X.card - T.card) : ℕ) : ℝ))
        = ∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
            ((m : ℝ) ^ X.card) *
              bernoulliMass X T ((1 : ℝ) / m) := by
            apply Finset.sum_congr rfl
            intro T hT
            have hTX : T ⊆ X := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
            simpa [Nat.cast_pow] using (bernoulliMass_inv_nat_mul_card hTX hm).symm
    _ = (m : ℝ) ^ X.card *
          (∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
            bernoulliMass X T ((1 : ℝ) / m)) := by
            rw [Finset.mul_sum]
    _ = ↑(m ^ X.card) *
          (∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
            bernoulliMass X T ((1 : ℝ) / m)) := by
            norm_num
    _ = ↑(m ^ X.card) * muP X (upClosureIn X A) ((1 : ℝ) / m) := rfl

lemma sum_successfulColors_card (X : Finset α) (A : Finset (Finset α)) (m : ℕ) :
    (∑ c : Coloring X m, (successfulColors A c).card) =
      ∑ i : Fin m, ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card := by
  calc
    (∑ c : Coloring X m, (successfulColors A c).card)
        = ∑ c : Coloring X m, ∑ i : Fin m,
            if i ∈ successfulColors A c then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro c _
            rw [← Finset.card_filter]
            simp [successfulColors]
    _ = ∑ i : Fin m, ∑ c : Coloring X m,
            if i ∈ successfulColors A c then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ i : Fin m, ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card := by
            apply Finset.sum_congr rfl
            intro i _
            rw [← Finset.card_filter]

theorem exists_coloring_many_successful_of_mu_ge
    (X : Finset α) (A : Finset (Finset α)) (r : ℕ) (hr : 2 ≤ r)
    (hmu : muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2) :
    ∃ c : Coloring X (2 * r), r ≤ (successfulColors A c).card := by
  classical
  let m := 2 * r
  have hm : 0 < m := by dsimp [m]; omega
  let C : ℕ := Fintype.card (Coloring X m)
  have hCpos_nat : 0 < C := by
    dsimp [C]
    rw [coloring_card]
    exact Nat.pow_pos (a := m) (n := X.card) hm
  have hCpos : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hCpos_nat
  have hsum_eq :
      ((∑ c : Coloring X m, (successfulColors A c).card : ℕ) : ℝ) =
        (m : ℝ) * (C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m) := by
    rw [sum_successfulColors_card X A m]
    rw [Nat.cast_sum]
    calc
      (∑ i : Fin m,
          (((Finset.univ : Finset (Coloring X m)).filter
            (fun c => i ∈ successfulColors A c)).card : ℝ))
          = ∑ _i : Fin m,
              (C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m) := by
              apply Finset.sum_congr rfl
              intro i _
              dsimp [C]
              exact successful_colorings_card_real X A hm i
      _ = (m : ℝ) * (C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m) := by
              simp [Fintype.card_fin, mul_assoc]
  have hsum_lower :
      (r : ℝ) * (C : ℝ) ≤
        ((∑ c : Coloring X m, (successfulColors A c).card : ℕ) : ℝ) := by
    rw [hsum_eq]
    have hm_eq : (m : ℝ) = 2 * (r : ℝ) := by simp [m]
    have hmu' :
        (1 / 2 : ℝ) ≤ muP X (upClosureIn X A) ((1 : ℝ) / m) := by
      simpa [m] using hmu
    have hmul :
        (C : ℝ) * (1 / 2 : ℝ) ≤
          (C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m) :=
      mul_le_mul_of_nonneg_left hmu' hCpos.le
    calc
      (r : ℝ) * (C : ℝ) =
          (m : ℝ) * ((C : ℝ) * (1 / 2 : ℝ)) := by
            rw [hm_eq]
            ring
      _ ≤ (m : ℝ) *
          ((C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m)) := by
            exact mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = (m : ℝ) * (C : ℝ) *
          muP X (upClosureIn X A) ((1 : ℝ) / m) := by
            ring
  by_contra hnone
  have hle_each : ∀ c : Coloring X m, (successfulColors A c).card ≤ r - 1 := by
    intro c
    have hnot : ¬ r ≤ (successfulColors A c).card := by
      intro hc
      exact hnone ⟨c, hc⟩
    omega
  have hsum_le_nat :
      (∑ c : Coloring X m, (successfulColors A c).card : ℕ) ≤
        ∑ _c : Coloring X m, (r - 1) := by
    exact Finset.sum_le_sum (fun c _ => hle_each c)
  have hsum_le :
      ((∑ c : Coloring X m, (successfulColors A c).card : ℕ) : ℝ) ≤
        (C : ℝ) * (r - 1 : ℕ) := by
    calc
      ((∑ c : Coloring X m, (successfulColors A c).card : ℕ) : ℝ)
          ≤ ((∑ _c : Coloring X m, (r - 1) : ℕ) : ℝ) := by
            exact_mod_cast hsum_le_nat
      _ = (C : ℝ) * (r - 1 : ℕ) := by
            simp [C]
  have hlt : (C : ℝ) * (r - 1 : ℕ) < (r : ℝ) * (C : ℝ) := by
    have hsub : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r)]
      norm_num
    rw [hsub]
    nlinarith
  nlinarith

/-- A chosen member of `A` witnessing that a color is successful. The value is
irrelevant on unsuccessful colors. -/
noncomputable def successfulMember {X : Finset α} {m : ℕ}
    (A : Finset (Finset α)) (c : Coloring X m) (i : Fin m) : Finset α :=
  if h : i ∈ successfulColors A c then
    Classical.choose ((mem_successfulColors).1 h)
  else
    ∅

lemma successfulMember_mem {X : Finset α} {m : ℕ}
    {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m}
    (hi : i ∈ successfulColors A c) :
    successfulMember A c i ∈ A := by
  unfold successfulMember
  rw [dif_pos hi]
  exact (Classical.choose_spec ((mem_successfulColors).1 hi)).1

lemma successfulMember_subset_colorPart {X : Finset α} {m : ℕ}
    {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m}
    (hi : i ∈ successfulColors A c) :
    successfulMember A c i ⊆ colorPart c i := by
  unfold successfulMember
  rw [dif_pos hi]
  exact (Classical.choose_spec ((mem_successfulColors).1 hi)).2

lemma member_nonempty_of_uniform
    {A : Finset (Finset α)} {S : Finset α} {k : ℕ}
    (hk : 1 ≤ k) (hUniform : Erdos202.UniformFamily A k) (hS : S ∈ A) :
    S.Nonempty := by
  have hcard : S.card = k := hUniform S hS
  exact Finset.card_pos.1 (by omega)

/-- Deterministic part of the random-partition argument: once one coloring has
at least `r` successful colors, choose one nonempty `A`-member inside each of
`r` successful color classes. Distinct color classes are disjoint. -/
theorem disjoint_members_of_many_successful_colors {X : Finset α} {m r k : ℕ}
    {A : Finset (Finset α)} (c : Coloring X m)
    (hk : 1 ≤ k) (hUniform : Erdos202.UniformFamily A k)
    (hSuccess : r ≤ (successfulColors A c).card) :
    ∃ B : Finset (Finset α),
      B ⊆ A ∧ B.card = r ∧ Erdos202.PairwiseDisjointMembers B := by
  classical
  rcases Finset.exists_subset_card_eq hSuccess with ⟨I, hI_success, hI_card⟩
  let pick : Fin m → Finset α := successfulMember A c
  let B : Finset (Finset α) := I.image pick
  have hpick_mem : ∀ i ∈ I, pick i ∈ A := by
    intro i hi
    exact successfulMember_mem (hI_success hi)
  have hpick_subset : ∀ i ∈ I, pick i ⊆ colorPart c i := by
    intro i hi
    exact successfulMember_subset_colorPart (hI_success hi)
  have hpick_inj : Set.InjOn pick I := by
    intro i hi j hj hpick_eq
    by_contra hij
    have hnonempty : (pick i).Nonempty :=
      member_nonempty_of_uniform hk hUniform (hpick_mem i hi)
    rcases hnonempty with ⟨x, hx⟩
    have hxi : x ∈ colorPart c i := hpick_subset i hi hx
    have hxj : x ∈ colorPart c j := by
      have hx' : x ∈ pick j := by simpa [hpick_eq] using hx
      exact hpick_subset j hj hx'
    exact (Finset.disjoint_left.1 (colorPart_disjoint c hij) hxi) hxj
  refine ⟨B, ?_, ?_, ?_⟩
  · intro S hS
    rcases Finset.mem_image.1 hS with ⟨i, hi, rfl⟩
    exact hpick_mem i hi
  · calc
      B.card = I.card := Finset.card_image_of_injOn hpick_inj
      _ = r := hI_card
  · intro S hS T hT hST
    rcases Finset.mem_image.1 hS with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.1 hT with ⟨j, hj, rfl⟩
    have hij : i ≠ j := by
      intro hij
      exact hST (by simp [hij])
    exact (Disjoint.mono (hpick_subset i hi) (hpick_subset j hj)
      (colorPart_disjoint c hij))

end

/-- **Random-partition bookkeeping** (Park–Pham PDF Proposition 2.1 / Cor 2.3
final step). Once `muP X (upClosureIn X A) (1/(2r)) ≥ 1/2` is in hand
(via `mu_at_partition_density_ge_half`), the random-partition argument —
viewing the Bernoulli measure as the marginal of a uniform random `2r`-
coloring of `X`, then a double-counting argument over colorings — produces
`r` pairwise-disjoint members of `A`.

This is **purely finite combinatorics** with no analytic content; it
isolates the discrete random-partition translation from the Park–Pham
expectation-threshold core (`park_pham_threshold_not_small_lt_exists`, exposed
through the derived closed-endpoint theorem
`park_pham_threshold_not_small_exists`, the exact-threshold theorem
`park_pham_threshold_at_exists`, and the larger-density theorem
`park_pham_threshold_exists`).

The proof strategy is:
1. Re-express `muP` as the average over uniform colorings of the
   indicator "some color class contains a member of A".
2. By the `muP ≥ 1/2` hypothesis combined with a union bound over the
   `2r` colors, the expected number of "successful" color classes is at
   least `r`.
3. Pick a coloring witnessing this; pick a member of A inside each
   successful color class; color classes are pairwise disjoint, so the
   picked members are pairwise disjoint. -/
theorem partition_density_to_disjoint_members :
    ∀ {α : Type*} [DecidableEq α]
      (X : Finset α) (A : Finset (Finset α)) (r k : ℕ),
      A.Nonempty →
      2 ≤ r →
      1 ≤ k →
      Erdos202.UniformFamily A k →
      (∀ S ∈ A, S ⊆ X) →
      muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 →
      ∃ B : Finset (Finset α),
        B ⊆ A ∧ B.card = r ∧ Erdos202.PairwiseDisjointMembers B := by
  intro α _ X A r k _hA hr hk hUniform _hAX hmu
  rcases exists_coloring_many_successful_of_mu_ge X A r hr hmu with ⟨c, hc⟩
  exact disjoint_members_of_many_successful_colors c hk hUniform hc

section

variable {α : Type*} [DecidableEq α]

/-- **Spread-disjointness theorem** (PDF Proposition 2.1 / Corollary 2.3).

Matches the historical `Erdos202.spread_disjointness_input` interface in
`SpreadCore.lean`.

Proved from the strict Park--Pham non-smallness theorem
`park_pham_threshold_not_small_lt_exists`; the closed-endpoint theorem,
`qSmallUpper` wrapper, density-monotonicity, and finite random-partition
bookkeeping below are fully formalized in `ParkPham/`. -/
theorem spread_disjointness_theorem :
    ∃ Csp : ℝ, 0 < Csp ∧
      ∀ {α : Type*} [DecidableEq α]
        (A : Finset (Finset α)) (r k : ℕ) (κ : ℝ),
        A.Nonempty →
        2 ≤ r →
        1 ≤ k →
        Erdos202.UniformFamily A k →
        Erdos202.SpreadFamily A κ →
        Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
        ∃ B : Finset (Finset α),
          B ⊆ A ∧ B.card = r ∧ Erdos202.PairwiseDisjointMembers B := by
  rcases park_pham_threshold_exists with ⟨CKK, hCKK_pos, hThreshold⟩
  refine ⟨CspOf CKK, CspOf_pos CKK, ?_⟩
  intro α _ A r k κ hA hr hk hUniform hSpread hκ
  -- Ground universe: X = ⋃_{S ∈ A} S
  let X : Finset α := A.biUnion id
  have hAX : ∀ S ∈ A, S ⊆ X := by
    intro S hSA x hxS
    exact Finset.mem_biUnion.mpr ⟨S, hSA, hxS⟩
  have hThresholdα :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2 := by
    intro X U q p hq0 hq1 hp0 hp1 hDensity hUX hIncr hSmall
    exact hThreshold X U q p hq0 hq1 hp0 hp1 hDensity hUX hIncr hSmall
  -- Step 1: muP ≥ 1/2 from the Park–Pham layer.
  have hmu :
      muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 :=
    mu_at_partition_density_ge_half_of_threshold
      CKK hCKK_pos hThresholdα hA hr hk hUniform hSpread hAX hκ
  -- Step 2: random-partition translation.
  exact partition_density_to_disjoint_members X A r k hA hr hk hUniform hAX hmu

end

end ParkPham
end Erdos202


/-! =============================================================
    Section from: Erdos/P202/SpreadCore.lean
    ============================================================= -/

/-
Erdős Problem 202 — Spread / dense-core layer.

The new ingredient in the May 2026 proof is the spread-core lemma replacing
the Erdős–Lovász / minimal-family loss in the BFV descending chain.

This file:
  * states the finite combinatorial spread-disjointness consequence of
    Park–Pham (Kahn–Kalai) as a derived theorem;
  * derives the dense-core corollary used downstream.

Park–Pham theorem reference: arXiv:2203.17207. We do NOT formalize the full
expectation-threshold theorem here; we isolate exactly the finite consequence
the descending chain needs.
-/


namespace Erdos202

open Finset
open scoped BigOperators

universe u

/-! ## Spread-disjointness (discharged via Park–Pham layer)

Definitions `UniformFamily`, `SpreadFamily`, `PairwiseDisjointMembers`
live in `Erdos.P202.SpreadDefs`. The finite spread-disjointness
consequence of Park–Pham is now proved as
`Erdos202.ParkPham.spread_disjointness_theorem`; the historical name
`spread_disjointness_input` is preserved here as a derived theorem so
downstream consumers (chain, dense-core, optimization) need no edits. -/

/-- **Spread-disjointness input** — preserved name, now a derived theorem
discharging the Park–Pham layer (`spread_disjointness_theorem`).
Trust boundary moves to the non-smallness Park--Pham package
`park_pham_threshold_not_small_lt_exists`; the closed-endpoint theorem, density
monotonicity, the `qSmallUpper` wrapper, and random-partition bookkeeping are
proved in `ParkPham/`. -/
theorem spread_disjointness_input :
  ∃ Csp : ℝ, 0 < Csp ∧
    ∀ {α : Type*} [DecidableEq α]
      (A : Finset (Finset α)) (r k : ℕ) (κ : ℝ),
      A.Nonempty →
      2 ≤ r →
      1 ≤ k →
      UniformFamily A k →
      SpreadFamily A κ →
      Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
      ∃ B : Finset (Finset α),
        B ⊆ A ∧ B.card = r ∧ PairwiseDisjointMembers B :=
  Erdos202.ParkPham.spread_disjointness_theorem

/-! ## Dense-core corollary -/

/-- **Dense-core corollary** (PDF Corollary 2.2). A non-disjoint uniform
family must concentrate on a small "core" appearing in many members. -/
theorem dense_core_from_spread :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ {α : Type u} [DecidableEq α]
        (A : Finset (Finset α)) (k K : ℕ),
        A.Nonempty →
        1 ≤ k → k ≤ K →
        UniformFamily A k →
        (∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ Disjoint S T) →
        ∃ C : Finset α,
          C.Nonempty ∧
          ((A.filter fun S => C ⊆ S).card : ℝ) >
            (A.card : ℝ) /
              (C0 * Real.log (Real.exp 1 * (K : ℝ))) ^ C.card := by
  classical
  let Csp : ℝ := Classical.choose (spread_disjointness_input.{u})
  have hspec := Classical.choose_spec (spread_disjointness_input.{u})
  have hCsp_pos : 0 < Csp := hspec.1
  refine ⟨Csp * 2, by positivity, ?_⟩
  intro α _ A k K hA hk_pos hkK hUniform hIntersect
  let κ : ℝ := (Csp * 2) * Real.log (Real.exp 1 * (K : ℝ))
  by_contra hNoCore
  have hSpread : SpreadFamily A κ := by
    intro T hT
    exact le_of_not_gt (by
      intro hgt
      exact hNoCore ⟨T, hT, hgt⟩)
  have hκ : Csp * (2 : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ := by
    have harg_pos : 0 < Real.exp 1 * (k : ℝ) := by positivity
    have harg_le : Real.exp 1 * (k : ℝ) ≤ Real.exp 1 * (K : ℝ) := by
      gcongr
    have hlog_le : Real.log (Real.exp 1 * (k : ℝ)) ≤
        Real.log (Real.exp 1 * (K : ℝ)) :=
      Real.log_le_log harg_pos harg_le
    have hcoef_nonneg : 0 ≤ Csp * 2 := by positivity
    exact mul_le_mul_of_nonneg_left hlog_le hcoef_nonneg
  rcases hspec.2 (A := A) (r := 2) (k := k) (κ := κ)
      hA (by norm_num) hk_pos hUniform hSpread hκ with
    ⟨B, hBA, hBcard, hBdisj⟩
  have hBgt : 1 < B.card := by omega
  rcases Finset.one_lt_card.mp hBgt with ⟨S, hS, T, hT, hST⟩
  exact hIntersect S (hBA hS) T (hBA hT) hST (hBdisj S hS T hT hST)

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFV/Mertens.lean
    ============================================================= -/

/-
Erdős Problem 202 — Mertens / Euler-product estimate.

# Status

This file proves the consumer-shaped weighted-sum bound used by the BFV
omega-tail proof in `Erdos/P202/BFV/OmegaTail.lean`.

# Relation to P694's `mertens_product`

The repo's `Erdos/P694/Proof.lean:417` axiomatizes **Mertens' third theorem**
(the product form `∏_{p ≤ y} p/(p-1) ~ e^γ · log y`). P202 only needs a weak
Mertens-style upper bound `∑_{p ≤ y} 1/p = O(log log y)`, proved below from
Mathlib's Chebyshev upper bound for `Nat.primeCounting`. The sharp Mertens
second theorem is also derivable from Mertens 3rd by taking logs:
  `log ∏_{p ≤ y} (1 - 1/p)^{-1} = ∑_{p ≤ y} (1/p + 1/(2 p²) + …)
                                = ∑_{p ≤ y} 1/p + O(1)`.

P694's sharper product-form Mertens input remains a separate issue, but P202 no
longer depends on it.

# Classical content

The finite Hardy-Ramanujan sieve bookkeeping is proved in this file, as is the
weak reciprocal-prime upper bound:

* **A Mertens-type upper bound**: there exist constants `A > 0` and `C` such
   that for all sufficiently large `N`,
   `∑_{p prime, p ≤ N} (1 / p : ℝ) ≤ A * Real.log (Real.log N) + C`.
   Mertens' second theorem gives the sharp `A = 1`.  For this P202 consumer,
   any fixed `A` is enough because `BFVz N * log log N = sqrt(log N) = o(Z(N))`.
   In Mathlib `v4.27.0`, the prime-counting function `Nat.primeCounting` and
   Chebyshev's upper bound on it are available; the dyadic summation below
   packages them into the reciprocal-prime bound needed here.

Combining the proved finite sieve below with this Mertens input: with
`BFVz N := √(log N) / log log N`,
  `∏_{p ≤ N} (1 + BFVz N / p)
     ≤ Real.exp (BFVz N * ∑_{p ≤ N} 1 / p)
     ≤ Real.exp (BFVz N * (A * Real.log (Real.log N) + C))`,
which is `≤ Real.exp (ε * Zscale N)` eventually for any `ε > 0`, since
`BFVz N · log log N = √(log N) = Zscale N / √(log log N) = o(Zscale N)`.

# Where this is consumed

* `Erdos.P202.BFV.OmegaExact` → `Erdos.P202.BFV.OmegaCountInput` →
  supplies the historical `Erdos202.bfv_omega_count_input` interface.

-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-- The BFV Rankin parameter `sqrt(log N) / log log N`. -/
noncomputable def BFVz (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ))

lemma finite_euler_product_one_add_le_exp_sum
    (s : Finset ℕ) {z : ℝ} (hz : 0 ≤ z)
    (hpos : ∀ p ∈ s, 0 < (p : ℝ)) :
    s.prod (fun p : ℕ => (1 : ℝ) + z / (p : ℝ)) ≤
      Real.exp (z * s.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ))) := by
  calc
    s.prod (fun p : ℕ => (1 : ℝ) + z / (p : ℝ))
        ≤ s.prod (fun p : ℕ => Real.exp (z / (p : ℝ))) := by
          exact Finset.prod_le_prod
            (s := s)
            (f := fun p : ℕ => (1 : ℝ) + z / (p : ℝ))
            (g := fun p : ℕ => Real.exp (z / (p : ℝ)))
            (fun p hp => by
              have hp_nonneg : 0 ≤ (p : ℝ) := (hpos p hp).le
              positivity)
            (fun p hp => by
              have h := Real.add_one_le_exp (z / (p : ℝ))
              linarith)
    _ = Real.exp (s.sum (fun p : ℕ => z / (p : ℝ))) := by
          rw [← Real.exp_sum]
    _ = Real.exp (z * s.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ))) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring

private lemma primeSupport_eq_primeFactors (n : ℕ) :
    primeSupport n = n.primeFactors := by
  unfold primeSupport
  rw [Nat.support_factorization]

private lemma rad_eq_prod_primeFactors (n : ℕ) :
    rad n = ∏ p ∈ n.primeFactors, p := by
  unfold rad
  rw [primeSupport_eq_primeFactors]

private lemma rad_squarefree (n : ℕ) : Squarefree (rad n) := by
  rw [rad_eq_prod_primeFactors]
  classical
  have hprod_ne : (∏ p ∈ n.primeFactors, p) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (by intro p hp; exact (Nat.prime_of_mem_primeFactors hp).ne_zero)
  refine (Nat.squarefree_iff_factorization_le_one hprod_ne).2 ?_
  intro q
  by_cases hq : q ∈ n.primeFactors
  · have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    rw [Nat.factorization_prod]
    · rw [Finsupp.finset_sum_apply]
      calc
        ∑ x ∈ n.primeFactors, x.factorization q
            = q.factorization q := by
                refine Finset.sum_eq_single q ?_ ?_
                · intro x hx hxq
                  have hxprime : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
                  rw [← pow_one x, hxprime.factorization_pow]
                  simp [hxq]
                · intro hnot
                  exact (hnot hq).elim
        _ = 1 := by
                rw [← pow_one q, hqprime.factorization_pow]
                simp
        _ ≤ 1 := le_rfl
    · intro x hx
      exact (Nat.prime_of_mem_primeFactors hx).ne_zero
  · rw [Nat.factorization_prod]
    · rw [Finsupp.finset_sum_apply]
      calc
        ∑ x ∈ n.primeFactors, x.factorization q = 0 := by
          refine Finset.sum_eq_zero ?_
          intro x hx
          have hxprime : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
          rw [← pow_one x, hxprime.factorization_pow]
          have hxq : x ≠ q := by
            intro h
            exact hq (h ▸ hx)
          simp [hxq]
        _ ≤ 1 := by norm_num
    · intro x hx
      exact (Nat.prime_of_mem_primeFactors hx).ne_zero

private lemma rad_dvd_self (n : ℕ) : rad n ∣ n := by
  rw [rad_eq_prod_primeFactors]
  exact Nat.prod_primeFactors_dvd n

private lemma primeSupport_rad (n : ℕ) :
    primeSupport (rad n) = primeSupport n := by
  calc
    primeSupport (rad n) = (rad n).primeFactors := primeSupport_eq_primeFactors _
    _ = (∏ p ∈ n.primeFactors, p).primeFactors := by rw [rad_eq_prod_primeFactors]
    _ = n.primeFactors := by
      exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)
    _ = primeSupport n := (primeSupport_eq_primeFactors n).symm

private lemma omega_rad (n : ℕ) : omega (rad n) = omega n := by
  unfold omega
  rw [primeSupport_rad]

lemma zpow_omega_le_squarefree_divisor_sum
    (z : ℝ) (hz : 0 ≤ z) {n : ℕ} (hn : n ≠ 0) :
    z ^ omega n ≤ ∑ d ∈ (n.divisors.filter Squarefree), z ^ omega d := by
  classical
  have hmem : rad n ∈ n.divisors.filter Squarefree := by
    rw [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨rad_dvd_self n, hn⟩, rad_squarefree n⟩
  have hnonneg :
      ∀ d ∈ n.divisors.filter Squarefree, 0 ≤ z ^ omega d := by
    intro d hd
    exact pow_nonneg hz _
  have hsingle :
      z ^ omega (rad n) ≤ ∑ d ∈ (n.divisors.filter Squarefree), z ^ omega d :=
    Finset.single_le_sum hnonneg hmem
  simpa [omega_rad] using hsingle

lemma card_Icc_filter_dvd_le_div (y d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 y).filter fun n => d ∣ n).card ≤ y / d := by
  classical
  calc
    ((Finset.Icc 1 y).filter fun n => d ∣ n).card
        ≤ (Finset.Icc 1 (y / d)).card := by
          refine Finset.card_le_card_of_injOn
            (s := (Finset.Icc 1 y).filter fun n => d ∣ n)
            (t := Finset.Icc 1 (y / d))
            (fun n : ℕ => n / d) ?_ ?_
          · intro n hn
            have hn' : n ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using hn
            rw [Finset.mem_filter] at hn'
            have hnIcc := Finset.mem_Icc.mp hn'.1
            have hdn : d ∣ n := hn'.2
            have htarget : n / d ∈ Finset.Icc 1 (y / d) := by
              rw [Finset.mem_Icc]
              refine ⟨?_, Nat.div_le_div_right hnIcc.2⟩
              exact Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hnIcc.1 hdn) hd)
            simpa using htarget
          · intro a ha b hb hab
            have ha' : a ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using ha
            have hb' : b ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using hb
            rw [Finset.mem_filter] at ha'
            rw [Finset.mem_filter] at hb'
            have hda : d ∣ a := ha'.2
            have hdb : d ∣ b := hb'.2
            have hab' : a / d = b / d := by simpa using hab
            calc
              a = a / d * d := (Nat.div_mul_cancel hda).symm
              _ = b / d * d := by rw [hab']
              _ = b := Nat.div_mul_cancel hdb
    _ = y / d := by simp

lemma omega_weighted_sum_le_squarefree_multiple_sum
    (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤
      ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
        (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) * z ^ omega d := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n)
        ≤ ∑ n ∈ Finset.Icc 1 y,
            ∑ d ∈ (n.divisors.filter Squarefree), z ^ omega d := by
          refine Finset.sum_le_sum ?_
          intro n hn
          exact zpow_omega_le_squarefree_divisor_sum z hz
            (by
              have hnIcc := Finset.mem_Icc.mp hn
              exact Nat.ne_of_gt hnIcc.1)
    _ ≤ ∑ n ∈ Finset.Icc 1 y,
            ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ d ∣ n),
              z ^ omega d := by
          refine Finset.sum_le_sum ?_
          intro n hn
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            rw [Finset.mem_filter] at hd ⊢
            have hddiv : d ∈ n.divisors := hd.1
            have hdsq : Squarefree d := hd.2
            have hnIcc := Finset.mem_Icc.mp hn
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hddiv
            have hddvd : d ∣ n := (Nat.mem_divisors.mp hddiv).1
            have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnIcc.1
            have hdle : d ≤ y := (Nat.le_of_dvd hnpos hddvd).trans hnIcc.2
            exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hdpos, hdle⟩, hdsq, hddvd⟩
          · intro d hd _hnot
            exact pow_nonneg hz _
    _ = ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
          (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) * z ^ omega d := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hsq : Squarefree d
          · calc
              (∑ x ∈ Finset.Icc 1 y, if Squarefree d ∧ d ∣ x then z ^ omega d else 0)
                  = ∑ x ∈ Finset.Icc 1 y, if d ∣ x then z ^ omega d else 0 := by
                    simp [hsq]
              _ = ∑ x ∈ (Finset.Icc 1 y).filter (fun x => d ∣ x), z ^ omega d := by
                    rw [Finset.sum_filter]
              _ = (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) *
                    z ^ omega d := by
                    simp [Finset.sum_const, nsmul_eq_mul]
              _ = if Squarefree d then
                    (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) *
                      z ^ omega d
                  else 0 := by
                    simp [hsq]
          · simp [hsq]

lemma omega_weighted_sum_le_squarefree_recip_sum
    (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤
      (y : ℝ) *
        ∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n)
        ≤ ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
            (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) *
              z ^ omega d :=
          omega_weighted_sum_le_squarefree_multiple_sum y z hz
    _ ≤ ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
            ((y : ℝ) / (d : ℝ)) * z ^ omega d := by
          refine Finset.sum_le_sum ?_
          intro d hd
          rw [Finset.mem_filter] at hd
          have hdIcc := Finset.mem_Icc.mp hd.1
          have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
          have hcard_nat :
              ((Finset.Icc 1 y).filter fun n => d ∣ n).card ≤ y / d :=
            card_Icc_filter_dvd_le_div y d hdpos
          have hcard_real :
              (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) ≤
                (y : ℝ) / (d : ℝ) := by
            exact (Nat.cast_le.mpr hcard_nat).trans Nat.cast_div_le
          exact mul_le_mul_of_nonneg_right hcard_real (pow_nonneg hz _)
    _ = ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
            (y : ℝ) * (z ^ omega d / (d : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mem_filter] at hd
          have hdIcc := Finset.mem_Icc.mp hd.1
          have hdne : (d : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hdIcc.1))
          field_simp [hdne]
    _ = (y : ℝ) *
          ∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ) := by
          rw [Finset.mul_sum]

lemma squarefree_zpow_omega_div_eq_primeSupport_prod
    (z : ℝ) {d : ℕ} (hsq : Squarefree d) :
    z ^ omega d / (d : ℝ) =
      ∏ p ∈ primeSupport d, z / (p : ℝ) := by
  classical
  have hprod_nat : ∏ p ∈ primeSupport d, p = d := by
    rw [primeSupport_eq_primeFactors]
    exact Nat.prod_primeFactors_of_squarefree hsq
  have hprod_real : (d : ℝ) = ∏ p ∈ primeSupport d, (p : ℝ) := by
    calc
      (d : ℝ) = ((∏ p ∈ primeSupport d, p : ℕ) : ℝ) := by
        exact_mod_cast hprod_nat.symm
      _ = ∏ p ∈ primeSupport d, (p : ℝ) := by
        norm_num
  have hpow : z ^ omega d = ∏ p ∈ primeSupport d, z := by
    simp [omega, Finset.prod_const]
  calc
    z ^ omega d / (d : ℝ)
        = (∏ p ∈ primeSupport d, z) / (∏ p ∈ primeSupport d, (p : ℝ)) := by
          rw [hpow, hprod_real]
    _ = ∏ p ∈ primeSupport d, z / (p : ℝ) := by
          rw [Finset.prod_div_distrib]

private lemma primeSupport_subset_primesUpTo_of_le
    {d y : ℕ} (hd1 : 1 ≤ d) (hdy : d ≤ y) :
    primeSupport d ⊆ (Finset.Icc 1 y).filter Nat.Prime := by
  intro p hp
  rw [Finset.mem_filter]
  have hpPrime : Nat.Prime p := prime_of_mem_primeSupport hp
  have hp_pf : p ∈ d.primeFactors := by
    simpa [primeSupport_eq_primeFactors] using hp
  have hpdvd : p ∣ d := Nat.dvd_of_mem_primeFactors hp_pf
  have hp_le_d : p ≤ d :=
    Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hd1) hpdvd
  exact ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le, hp_le_d.trans hdy⟩, hpPrime⟩

lemma squarefree_recip_sum_le_euler_product
    (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ)) ≤
      ((Finset.Icc 1 y).filter Nat.Prime).prod
        (fun p => (1 : ℝ) + z / (p : ℝ)) := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 y).filter Squarefree
  let P : Finset ℕ := (Finset.Icc 1 y).filter Nat.Prime
  let term : Finset ℕ → ℝ := fun T => (∏ p ∈ T, z / (p : ℝ))
  have hinj :
      ∀ d ∈ S, ∀ e ∈ S, primeSupport d = primeSupport e → d = e := by
    intro d hd e he hsupport
    simp [S] at hd he
    have hdprod : ∏ p ∈ primeSupport d, p = d := by
      rw [primeSupport_eq_primeFactors]
      exact Nat.prod_primeFactors_of_squarefree hd.2
    have heprod : ∏ p ∈ primeSupport e, p = e := by
      rw [primeSupport_eq_primeFactors]
      exact Nat.prod_primeFactors_of_squarefree he.2
    calc
      d = ∏ p ∈ primeSupport d, p := hdprod.symm
      _ = ∏ p ∈ primeSupport e, p := by rw [hsupport]
      _ = e := heprod
  have himage_subset : S.image primeSupport ⊆ P.powerset := by
    intro T hT
    rw [Finset.mem_powerset]
    rcases Finset.mem_image.mp hT with ⟨d, hdS, rfl⟩
    simp [S] at hdS
    have hdIcc := hdS.1
    exact primeSupport_subset_primesUpTo_of_le hdIcc.1 hdIcc.2
  have hterm_nonneg :
      ∀ T ∈ P.powerset, 0 ≤ term T := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    refine Finset.prod_nonneg ?_
    intro p hpT
    have hpP : p ∈ P := hT hpT
    simp [P] at hpP
    have hpPrime : Nat.Prime p := hpP.2
    exact div_nonneg hz (by exact_mod_cast hpPrime.pos.le)
  calc
    (∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ))
        = ∑ d ∈ S, term (primeSupport d) := by
          apply Finset.sum_congr
          · simp [S]
          · intro d hd
            simp [S] at hd
            exact squarefree_zpow_omega_div_eq_primeSupport_prod z hd.2
    _ = ∑ T ∈ S.image primeSupport, term T := by
          rw [Finset.sum_image]
          intro d hd e he hsupport
          exact hinj d hd e he hsupport
    _ ≤ ∑ T ∈ P.powerset, term T := by
          exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
            (by
              intro T hTP _hnot
              exact hterm_nonneg T hTP)
    _ = P.prod (fun p => (1 : ℝ) + z / (p : ℝ)) := by
          rw [Finset.prod_one_add]
    _ = ((Finset.Icc 1 y).filter Nat.Prime).prod
          (fun p => (1 : ℝ) + z / (p : ℝ)) := by
          rfl

lemma omega_weighted_sum_le_euler_product
    (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤
      (y : ℝ) *
        ((Finset.Icc 1 y).filter Nat.Prime).prod
          (fun p => (1 : ℝ) + z / (p : ℝ)) := by
  exact (omega_weighted_sum_le_squarefree_recip_sum y z hz).trans
    (mul_le_mul_of_nonneg_left
      (squarefree_recip_sum_le_euler_product y z hz)
      (by positivity))

lemma eventually_primeCounting_nat_le_const_log :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤ B * (n : ℝ) / Real.log (n : ℝ) := by
  refine ⟨Real.log 4 + 1, ?_, ?_⟩
  · have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  · have hreal :
        ∀ᶠ x : ℝ in atTop,
          (Nat.primeCounting (Nat.floor x) : ℝ) ≤
            (Real.log 4 + 1) * x / Real.log x :=
      Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one
    have hnat := tendsto_natCast_atTop_atTop.eventually hreal
    filter_upwards [hnat] with n hn
    simpa using hn

lemma one_div_nat_succ_le_log_succ_sub_log {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / (m + 1 : ℕ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hsuccpos : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have h :=
    Real.one_sub_inv_le_log_of_pos
      (div_pos hsuccpos hmpos)
  rw [Real.log_div hsuccpos.ne' hmpos.ne'] at h
  have hleft :
      1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) =
        (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    field_simp [hmpos.ne', hsuccpos.ne']
    norm_num
  calc
    (1 : ℝ) / ((m + 1 : ℕ) : ℝ)
        = 1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) := hleft.symm
    _ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := h

lemma harmonic_Icc_one_le_one_add_log (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) ≤
      1 + Real.log (m : ℝ) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp
      · have hm : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
        have htop_not : m + 1 ∉ Finset.Icc 1 m := by
          simp
        have hIcc :
            Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext k
          simp
          omega
        have hterm := one_div_nat_succ_le_log_succ_sub_log (m := m) hm
        calc
          (∑ k ∈ Finset.Icc 1 (m + 1), (1 : ℝ) / (k : ℝ))
              = (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) +
                  (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
                    rw [hIcc, Finset.sum_insert htop_not]
                    ring
          _ ≤ (1 + Real.log (m : ℝ)) +
                (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right ih ((1 : ℝ) / ((m + 1 : ℕ) : ℝ))
          _ ≤ 1 + Real.log (((m + 1 : ℕ) : ℝ)) := by
                  linarith
          _ = 1 + Real.log ((Nat.succ m : ℕ) : ℝ) := by
                  rfl

lemma primeCounting_eq_card_Icc_filter_prime (n : ℕ) :
    ((Finset.Icc 1 n).filter Nat.Prime).card = Nat.primeCounting n := by
  have hset :
      (Finset.Icc 1 n).filter Nat.Prime =
        (Finset.range (n + 1)).filter Nat.Prime := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      have hpIcc := Finset.mem_Icc.mp hp.1
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpIcc.2), hp.2⟩
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_Icc.mpr
        ⟨hp.2.one_le, Nat.le_of_lt_succ (Finset.mem_range.mp hp.1)⟩, hp.2⟩
  calc
    ((Finset.Icc 1 n).filter Nat.Prime).card
        = ((Finset.range (n + 1)).filter Nat.Prime).card := by rw [hset]
    _ = Nat.count Nat.Prime (n + 1) := by
          exact (Nat.count_eq_card_filter_range Nat.Prime (n + 1)).symm
    _ = Nat.primeCounting n := rfl

lemma reciprocal_prime_sum_Ico_pow_two_le (k : ℕ) :
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ)) ≤
      (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
  classical
  let S := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime
  have hdenpos : 0 < (((2 ^ k : ℕ) : ℝ)) := by positivity
  have hpoint : ∀ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ 1 / ((2 ^ k : ℕ) : ℝ) := by
    intro p hp
    simp [S] at hp
    have hlow_nat : 2 ^ k ≤ p := hp.1.1
    have hlow : (((2 ^ k : ℕ) : ℝ)) ≤ (p : ℝ) := by exact_mod_cast hlow_nat
    exact one_div_le_one_div_of_le hdenpos hlow
  have hcard_le :
      S.card ≤ Nat.primeCounting (2 ^ (k + 1)) := by
    rw [← primeCounting_eq_card_Icc_filter_prime]
    refine Finset.card_le_card ?_
    intro p hp
    simp [S] at hp
    rw [Finset.mem_filter]
    have hpIco := hp.1
    have hpPrime : Nat.Prime p := hp.2
    exact ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le, hpIco.2.le⟩, hpPrime⟩
  calc
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ))
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := rfl
    _ ≤ ∑ p ∈ S, (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
          exact Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hcard_le) hdenpos.le

lemma reciprocal_prime_sum_Ico_pow_two_le_of_primeCounting_bound
    (B : ℝ) {k : ℕ}
    (hπ : (Nat.primeCounting (2 ^ (k + 1)) : ℝ) ≤
      B * (((2 ^ (k + 1) : ℕ) : ℝ)) /
        Real.log (((2 ^ (k + 1) : ℕ) : ℝ))) :
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ)) ≤
      (2 * B / Real.log 2) / ((k + 1 : ℕ) : ℝ) := by
  have hdenpos : 0 < (((2 ^ k : ℕ) : ℝ)) := by positivity
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  calc
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ))
        ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) /
            ((2 ^ k : ℕ) : ℝ) :=
          reciprocal_prime_sum_Ico_pow_two_le k
    _ ≤ (B * (((2 ^ (k + 1) : ℕ) : ℝ)) /
          Real.log (((2 ^ (k + 1) : ℕ) : ℝ))) /
            ((2 ^ k : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right hπ hdenpos.le
    _ = (2 * B / Real.log 2) / ((k + 1 : ℕ) : ℝ) := by
          have hpow_succ :
              (((2 ^ (k + 1) : ℕ) : ℝ)) =
                (2 : ℝ) * (((2 ^ k : ℕ) : ℝ)) := by
            norm_num [pow_succ, mul_comm]
          have hlog_pow :
              Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) =
                ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
            rw [show (((2 ^ (k + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 1) by norm_num]
            rw [Real.log_pow]
          rw [hlog_pow, hpow_succ]
          field_simp [hdenpos.ne', hlog2pos.ne', hkpos.ne']

lemma eventually_reciprocal_prime_sum_Ico_pow_two_le_const :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ)) ≤
        D / ((k + 1 : ℕ) : ℝ) := by
  rcases eventually_primeCounting_nat_le_const_log with ⟨B, hBpos, hBbound⟩
  refine ⟨2 * B / Real.log 2, ?_, ?_⟩
  · positivity
  · have hpw : Tendsto (fun k : ℕ => 2 ^ (k + 1)) atTop atTop := by
      exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)).comp
        (tendsto_add_atTop_nat 1)
    have hBpow := hpw.eventually hBbound
    filter_upwards [hBpow] with k hk
    exact reciprocal_prime_sum_Ico_pow_two_le_of_primeCounting_bound B hk

lemma reciprocal_prime_sum_Ico_pow_two_le_const_global :
    ∃ D : ℝ, 0 < D ∧ ∀ k : ℕ,
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ)) ≤
        D / ((k + 1 : ℕ) : ℝ) := by
  classical
  rcases eventually_reciprocal_prime_sum_Ico_pow_two_le_const with
    ⟨D, hDpos, hDevent⟩
  rcases eventually_atTop.1 hDevent with ⟨K, hK⟩
  let block : ℕ → ℝ := fun k =>
    ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
      (1 : ℝ) / (p : ℝ)
  let extra : ℝ := ∑ k ∈ Finset.Icc 0 K, ((k + 1 : ℕ) : ℝ) * block k
  refine ⟨D + extra + 1, ?_, ?_⟩
  · have hextra_nonneg : 0 ≤ extra := by
      refine Finset.sum_nonneg ?_
      intro k hk
      exact mul_nonneg (by positivity)
        (by
          refine Finset.sum_nonneg ?_
          intro p hp
          exact div_nonneg zero_le_one (by positivity))
    linarith
  · intro k
    have hdenpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
    by_cases hlarge : K ≤ k
    · have hDle : D ≤ D + extra + 1 := by
        have hextra_nonneg : 0 ≤ extra := by
          refine Finset.sum_nonneg ?_
          intro j hj
          exact mul_nonneg (by positivity)
            (by
              refine Finset.sum_nonneg ?_
              intro p hp
              exact div_nonneg zero_le_one (by positivity))
        linarith
      calc
        block k ≤ D / ((k + 1 : ℕ) : ℝ) := hK k hlarge
        _ ≤ (D + extra + 1) / ((k + 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right hDle hdenpos.le
    · have hkle : k ≤ K := Nat.le_of_not_ge hlarge
      have hk_mem : k ∈ Finset.Icc 0 K := by
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le k, hkle⟩
      have hterm_nonneg :
          ∀ j ∈ Finset.Icc 0 K, 0 ≤ ((j + 1 : ℕ) : ℝ) * block j := by
        intro j hj
        exact mul_nonneg (by positivity)
          (by
            refine Finset.sum_nonneg ?_
            intro p hp
            exact div_nonneg zero_le_one (by positivity))
      have hsingle :
          ((k + 1 : ℕ) : ℝ) * block k ≤ extra :=
        Finset.single_le_sum hterm_nonneg hk_mem
      have hmul :
          block k * ((k + 1 : ℕ) : ℝ) ≤ D + extra + 1 := by
        calc
          block k * ((k + 1 : ℕ) : ℝ)
              = ((k + 1 : ℕ) : ℝ) * block k := by ring
          _ ≤ extra := hsingle
          _ ≤ D + extra + 1 := by linarith
      exact (le_div_iff₀ hdenpos).2 hmul

lemma reciprocal_prime_sum_le_dyadic_harmonic
    (D : ℝ)
    (hD : ∀ k : ℕ,
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ)) ≤
        D / ((k + 1 : ℕ) : ℝ))
    (N : ℕ) :
    (((Finset.Icc 1 N).filter Nat.Prime).sum
        (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
      ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  let T : Finset ℕ := Finset.Icc 0 (Nat.log 2 N)
  have hmaps : ∀ p ∈ S, Nat.log 2 p ∈ T := by
    intro p hp
    simp [S, T] at hp ⊢
    exact Nat.log_mono_right hp.1.2
  have hdecomp :
      ∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          (1 : ℝ) / (p : ℝ)
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_fiberwise_of_maps_to hmaps (fun p : ℕ => (1 : ℝ) / (p : ℝ))
  have hfiber_le :
      ∀ k ∈ T,
        (∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
            (1 : ℝ) / (p : ℝ)) ≤
          ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ) := by
    intro k hk
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      simp [S] at hp ⊢
      have hpPrime : Nat.Prime p := hp.1.2
      have hpne : p ≠ 0 := hpPrime.ne_zero
      have hlog : Nat.log 2 p = k := hp.2
      exact ⟨⟨by simpa [hlog] using Nat.pow_log_le_self 2 hpne,
        by simpa [hlog, Nat.succ_eq_add_one] using
          Nat.lt_pow_succ_log_self Nat.one_lt_two p⟩, hpPrime⟩
    · intro p hp _hnot
      exact div_nonneg zero_le_one (by positivity)
  have hsum_blocks :
      ∑ k ∈ T,
        (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ))
        ≤ ∑ k ∈ T, D / ((k + 1 : ℕ) : ℝ) := by
    exact Finset.sum_le_sum (fun k hk => hD k)
  have hsum_shift :
      (∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ))
        = ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
    have himage :
        T.image (fun k : ℕ => k + 1) = Finset.Icc 1 (Nat.log 2 N + 1) := by
      ext j
      simp [T]
    have hinj : Set.InjOn (fun k : ℕ => k + 1) T := by
      intro a ha b hb hab
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hab)
    have hsum_image :
        (∑ j ∈ T.image (fun k : ℕ => k + 1), (1 : ℝ) / (j : ℝ))
          = ∑ k ∈ T, (1 : ℝ) / (((fun k : ℕ => k + 1) k : ℕ) : ℝ) := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj ha hb hab
    calc
      (∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ))
          = ∑ j ∈ T.image (fun k : ℕ => k + 1), (1 : ℝ) / (j : ℝ) := by
            exact hsum_image.symm
      _ = ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
            rw [himage]
  calc
    (((Finset.Icc 1 N).filter Nat.Prime).sum
        (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := rfl
    _ = ∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          (1 : ℝ) / (p : ℝ) := hdecomp.symm
    _ ≤ ∑ k ∈ T,
          (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ)) :=
          Finset.sum_le_sum hfiber_le
    _ ≤ ∑ k ∈ T, D / ((k + 1 : ℕ) : ℝ) := hsum_blocks
    _ = D * ∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = D * ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
          rw [hsum_shift]
    _ ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (harmonic_Icc_one_le_one_add_log (Nat.log 2 N + 1))
            (by
              have hD0 := hD 0
              have hblock0_nonneg :
                  0 ≤
                    (∑ p ∈ (Finset.Ico (2 ^ 0) (2 ^ (0 + 1))).filter Nat.Prime,
                      (1 : ℝ) / (p : ℝ)) := by
                refine Finset.sum_nonneg ?_
                intro p hp
                exact div_nonneg zero_le_one (by positivity)
              have hden : (((0 + 1 : ℕ) : ℝ)) = 1 := by norm_num
              nlinarith [hD0, hblock0_nonneg])

lemma eventually_one_add_log_nat_log_le_two_loglog :
    ∀ᶠ N : ℕ in atTop,
      1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
        ≤ 2 * Real.log (Real.log (N : ℝ)) := by
  let C : ℝ := 2 / Real.log 2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by positivity
  have hloglog_large :
      ∀ᶠ N : ℕ in atTop,
        1 + Real.log C ≤ Real.log (Real.log (N : ℝ)) :=
    tendsto_loglog_nat_atTop.eventually_ge_atTop (1 + Real.log C)
  filter_upwards [hloglog_large,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hll_large hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog2_lt_one : Real.log 2 < 1 :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2 Real.exp_one_gt_two
  have hlog2_le_logN : Real.log 2 ≤ Real.log (N : ℝ) := by linarith
  have hquot_ge_one : 1 ≤ Real.log (N : ℝ) / Real.log 2 := by
    have : (1 : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
      simpa using hlog2_le_logN
    exact (le_div_iff₀ hlog2pos).2 this
  have hlog_nat_le :
      ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    have h := Real.log2_le_logb N
    simpa [Nat.log2_eq_log_two, Real.logb] using h
  have hnatlog_add_le :
      (((Nat.log 2 N + 1 : ℕ) : ℝ)) ≤ C * Real.log (N : ℝ) := by
    calc
      (((Nat.log 2 N + 1 : ℕ) : ℝ))
          = ((Nat.log 2 N : ℕ) : ℝ) + 1 := by norm_num
      _ ≤ Real.log (N : ℝ) / Real.log 2 + 1 := by linarith
      _ ≤ Real.log (N : ℝ) / Real.log 2 +
            Real.log (N : ℝ) / Real.log 2 := by linarith
      _ = C * Real.log (N : ℝ) := by
            dsimp [C]
            ring
  have hleft_pos : 0 < (((Nat.log 2 N + 1 : ℕ) : ℝ)) := by positivity
  have hright_pos : 0 < C * Real.log (N : ℝ) := mul_pos hCpos hlogpos
  have hlog_bound :
      Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
        ≤ Real.log C + Real.log (Real.log (N : ℝ)) := by
    calc
      Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
          ≤ Real.log (C * Real.log (N : ℝ)) :=
            Real.log_le_log hleft_pos hnatlog_add_le
      _ = Real.log C + Real.log (Real.log (N : ℝ)) := by
            rw [Real.log_mul hCpos.ne' hlogpos.ne']
  linarith

/-- A constant-coefficient reciprocal-prime Mertens upper bound.

This proof is intentionally non-sharp: Chebyshev's upper bound for
`Nat.primeCounting` gives an `O(1/k)` estimate on dyadic prime blocks, and the
dyadic harmonic sum is `O(log log N)`. -/
theorem reciprocal_prime_sum_mertens :
    ∃ A C : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
      (((Finset.Icc 1 N).filter Nat.Prime).sum
          (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
        ≤ A * Real.log (Real.log (N : ℝ)) + C := by
  rcases reciprocal_prime_sum_Ico_pow_two_le_const_global with ⟨D, hDpos, hD⟩
  refine ⟨2 * D, 0, by positivity, ?_⟩
  filter_upwards [eventually_one_add_log_nat_log_le_two_loglog] with N hloglog
  calc
    (((Finset.Icc 1 N).filter Nat.Prime).sum
        (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
        ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) :=
          reciprocal_prime_sum_le_dyadic_harmonic D hD N
    _ ≤ D * (2 * Real.log (Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hloglog hDpos.le
    _ = (2 * D) * Real.log (Real.log (N : ℝ)) + 0 := by ring

/-- **Analytic gap (Mertens + sieve).** Euler-product upper bound for the
weighted omega sum before the final BFV scale simplification.

This packages the classical sieve inequality together with Mertens' reciprocal
prime sum in the form
`∑ z^ω(n) ≤ y * exp(z * (log log N + C))`, specialized to `z = BFVz N`.
The proof is the analytic-number-theory target described in the file header. -/
theorem omega_weighted_sum_euler_mertens :
    ∃ A C : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
      ∀ y : ℕ, y ≤ N →
        (∑ n ∈ Finset.Icc 1 y, (BFVz N) ^ omega n)
          ≤ (y : ℝ) *
              Real.exp (BFVz N *
                (A * Real.log (Real.log (N : ℝ)) + C)) := by
  rcases reciprocal_prime_sum_mertens with ⟨A, C, hA, hMertens⟩
  refine ⟨A, C, hA, ?_⟩
  filter_upwards [hMertens,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hMertensN hNlarge_nat
  intro y hy
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hz_nonneg : 0 ≤ BFVz N := by
    rw [BFVz]
    exact div_nonneg (Real.sqrt_nonneg _) hloglog_pos.le
  let Py : Finset ℕ := (Finset.Icc 1 y).filter Nat.Prime
  let PN : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  have hPy_subset : Py ⊆ PN := by
    intro p hp
    simp [Py, PN] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hy⟩, hp.2⟩
  have hsum_y_le_N :
      Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) ≤
        PN.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hPy_subset
      (by
        intro p hpN _hpnot
        simp [PN] at hpN
        exact div_nonneg zero_le_one (by exact_mod_cast hpN.2.pos.le))
  have hsum_y_bound :
      Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) ≤
        A * Real.log (Real.log (N : ℝ)) + C := by
    exact hsum_y_le_N.trans (by simpa [PN] using hMertensN)
  have hpos_p : ∀ p ∈ Py, 0 < (p : ℝ) := by
    intro p hp
    simp [Py] at hp
    exact_mod_cast hp.2.pos
  have hprod_exp :
      Py.prod (fun p : ℕ => (1 : ℝ) + BFVz N / (p : ℝ)) ≤
        Real.exp (BFVz N *
          Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ))) :=
    finite_euler_product_one_add_le_exp_sum Py hz_nonneg hpos_p
  have hprod_bound :
      Py.prod (fun p : ℕ => (1 : ℝ) + BFVz N / (p : ℝ)) ≤
        Real.exp (BFVz N *
          (A * Real.log (Real.log (N : ℝ)) + C)) := by
    exact hprod_exp.trans
      (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left hsum_y_bound hz_nonneg))
  exact (omega_weighted_sum_le_euler_product y (BFVz N) hz_nonneg).trans
    (mul_le_mul_of_nonneg_left (by simpa [Py] using hprod_bound) (by positivity))

lemma BFVz_linear_loglog_exponent_le_Zscale
    (A C ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      BFVz N * (A * Real.log (Real.log (N : ℝ)) + C) ≤ ε * Zscale N := by
  let R : ℝ := max (4 * (A + 1) / ε) (max 1 |C|)
  filter_upwards [eventually_sqrt_loglog_ge R,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsqrtlog_nonneg : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
  have hA1_pos : 0 < A + 1 := by linarith
  have hR_ge_main : 4 * (A + 1) / ε ≤ R := le_max_left _ _
  have hR_ge_one : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR_ge_abs : |C| ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hsqrt_ge_main :
      4 * (A + 1) / ε ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_main.trans hsqrt
  have hsqrt_ge_one : 1 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_one.trans hsqrt
  have hsqrt_ge_abs : |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_abs.trans hsqrt
  have hloglog_ge_abs : |C| ≤ Real.log (Real.log (N : ℝ)) := by
    calc
      |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) := hsqrt_ge_abs
      _ ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) ^ 2 := by
            nlinarith [sq_nonneg (Real.sqrt (Real.log (Real.log (N : ℝ))) - 1)]
      _ = Real.log (Real.log (N : ℝ)) := Real.sq_sqrt hloglog_nonneg
  have hmain_sqrt :
      2 * (A + 1) ≤
        ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
    have hfour :
        4 * (A + 1) ≤
          ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
      simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using
        (div_le_iff₀ hε).1 hsqrt_ge_main
    linarith
  have hBFVz_nonneg : 0 ≤ BFVz N := by
    rw [BFVz]
    exact div_nonneg hsqrtlog_nonneg hloglog_nonneg
  have hlinear_le :
      A * Real.log (Real.log (N : ℝ)) + C ≤
        (A + 1) * Real.log (Real.log (N : ℝ)) := by
    calc
      A * Real.log (Real.log (N : ℝ)) + C
          ≤ A * Real.log (Real.log (N : ℝ)) + |C| := by
            nlinarith [le_abs_self C]
      _ ≤ A * Real.log (Real.log (N : ℝ)) +
            Real.log (Real.log (N : ℝ)) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hloglog_ge_abs
                (A * Real.log (Real.log (N : ℝ)))
      _ = (A + 1) * Real.log (Real.log (N : ℝ)) := by ring
  have hwith_bound :
      BFVz N * (A * Real.log (Real.log (N : ℝ)) + C) ≤
        BFVz N * ((A + 1) * Real.log (Real.log (N : ℝ))) :=
    mul_le_mul_of_nonneg_left hlinear_le hBFVz_nonneg
  have hZeq := Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge
  have hbound :
      BFVz N * ((A + 1) * Real.log (Real.log (N : ℝ))) ≤
        ε * Zscale N := by
    rw [BFVz, hZeq]
    calc
      Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ)) *
          ((A + 1) * Real.log (Real.log (N : ℝ)))
          = (A + 1) * Real.sqrt (Real.log (N : ℝ)) := by
            field_simp [hloglog_pos.ne']
      _ ≤ ε * (Real.sqrt (Real.log (N : ℝ)) *
            Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
            calc
              (A + 1) * Real.sqrt (Real.log (N : ℝ))
                  ≤ (ε * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
                      Real.sqrt (Real.log (N : ℝ)) := by
                        exact mul_le_mul_of_nonneg_right
                          (by linarith [hmain_sqrt]) hsqrtlog_nonneg
              _ = ε * (Real.sqrt (Real.log (N : ℝ)) *
                    Real.sqrt (Real.log (Real.log (N : ℝ)))) := by ring
  exact hwith_bound.trans hbound

lemma BFVz_mertens_exponent_le_Zscale (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      BFVz N * (Real.log (Real.log (N : ℝ)) + C) ≤ ε * Zscale N := by
  let R : ℝ := max (4 / ε) (max 1 |C|)
  filter_upwards [eventually_sqrt_loglog_ge R,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsqrtlog_nonneg : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
  have hsqrtloglog_nonneg : 0 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    Real.sqrt_nonneg _
  have hR_ge_four : 4 / ε ≤ R := le_max_left _ _
  have hR_ge_one : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR_ge_abs : |C| ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hsqrt_ge_four : 4 / ε ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_four.trans hsqrt
  have hsqrt_ge_one : 1 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_one.trans hsqrt
  have hsqrt_ge_abs : |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_abs.trans hsqrt
  have hloglog_ge_abs : |C| ≤ Real.log (Real.log (N : ℝ)) := by
    calc
      |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) := hsqrt_ge_abs
      _ ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) ^ 2 := by
            nlinarith [sq_nonneg (Real.sqrt (Real.log (Real.log (N : ℝ))) - 1)]
      _ = Real.log (Real.log (N : ℝ)) := Real.sq_sqrt hloglog_nonneg
  have htwo_le_eps_sqrt : 2 ≤ ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
    have hfour : 4 ≤ ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
      simpa [mul_comm] using (div_le_iff₀ hε).1 hsqrt_ge_four
    linarith
  have hBFVz_nonneg : 0 ≤ BFVz N := by
    rw [BFVz]
    exact div_nonneg hsqrtlog_nonneg hloglog_nonneg
  have hwith_abs :
      BFVz N * (Real.log (Real.log (N : ℝ)) + C) ≤
        BFVz N * (Real.log (Real.log (N : ℝ)) + |C|) := by
    have hsum_abs :
        Real.log (Real.log (N : ℝ)) + C ≤
          Real.log (Real.log (N : ℝ)) + |C| := by
      nlinarith [le_abs_self C]
    exact mul_le_mul_of_nonneg_left hsum_abs hBFVz_nonneg
  have hZeq := Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge
  have hbound_abs :
      BFVz N * (Real.log (Real.log (N : ℝ)) + |C|) ≤ ε * Zscale N := by
    rw [BFVz, hZeq]
    calc
      Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ)) *
          (Real.log (Real.log (N : ℝ)) + |C|)
          ≤ Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ)) *
              (2 * Real.log (Real.log (N : ℝ))) := by
                have hsum_le :
                    Real.log (Real.log (N : ℝ)) + |C| ≤
                      2 * Real.log (Real.log (N : ℝ)) := by linarith
                exact mul_le_mul_of_nonneg_left hsum_le
                  (div_nonneg hsqrtlog_nonneg hloglog_nonneg)
      _ = 2 * Real.sqrt (Real.log (N : ℝ)) := by
            field_simp [hloglog_pos.ne']
      _ ≤ ε * (Real.sqrt (Real.log (N : ℝ)) *
            Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
            calc
              2 * Real.sqrt (Real.log (N : ℝ))
                  ≤ (ε * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
                      Real.sqrt (Real.log (N : ℝ)) := by
                        exact mul_le_mul_of_nonneg_right htwo_le_eps_sqrt
                          hsqrtlog_nonneg
              _ = ε * (Real.sqrt (Real.log (N : ℝ)) *
                    Real.sqrt (Real.log (Real.log (N : ℝ)))) := by ring
  exact hwith_abs.trans hbound_abs

/-- Euler-product upper bound for the weighted omega sum at the BFV scale.

For every `ε > 0`, eventually in `N`, for every `y ≤ N`:
  `∑_{n ≤ y} (BFVz N) ^ omega n ≤ y · exp(ε · Z(N))`.

The analytic input is `omega_weighted_sum_euler_mertens`; this theorem proves
the remaining scale algebra at `z = BFVz N`. -/
theorem omega_weighted_sum_bfvz_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y : ℕ, y ≤ N →
        (∑ n ∈ Finset.Icc 1 y, (BFVz N) ^ omega n)
          ≤ (y : ℝ) * Real.exp (ε * Zscale N) := by
  intro ε hε
  rcases omega_weighted_sum_euler_mertens with ⟨A, C, hA, hC⟩
  filter_upwards [hC, BFVz_linear_loglog_exponent_le_Zscale A C ε hA hε]
    with N hAnalytic hExp y hy
  have hExp_le :
      Real.exp (BFVz N * (A * Real.log (Real.log (N : ℝ)) + C)) ≤
        Real.exp (ε * Zscale N) :=
    Real.exp_le_exp.2 hExp
  exact (hAnalytic y hy).trans
    (mul_le_mul_of_nonneg_left hExp_le (by positivity))

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFV/OmegaTail.lean
    ============================================================= -/

/-
Erdos Problem 202 -- BFV omega-tail estimates.

This file contains the elementary Rankin counting step used before the
BFV/Hardy-Ramanujan analytic input.  The Euler-product estimate is proved in
`Erdos.P202.BFV.Mertens`.
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Rankin's inequality for omega tails

The BFV Rankin parameter `BFVz N := √(log N) / log log N` lives in
`Erdos.P202.BFV.Mertens`, alongside the weighted omega-sum estimate consumed
below. -/

lemma card_le_floor_of_natCast_le {m : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hm : (m : ℝ) ≤ x) : m ≤ Nat.floor x :=
  (Nat.le_floor_iff hx).2 hm

/-- Rankin's inequality:
`#{n ≤ y : t ≤ omega n} * z^t ≤ sum_{n≤y} z^(omega n)` for `z ≥ 1`. -/
lemma rankin_omega_tail_sum_le (y t : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
      ≤ ∑ n ∈ Finset.Icc 1 y, z ^ omega n := by
  classical
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  calc
    (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
        = ∑ n ∈ (Finset.Icc 1 y).filter (fun n => t ≤ omega n), z ^ t := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ (Finset.Icc 1 y).filter (fun n => t ≤ omega n), z ^ omega n := by
          refine Finset.sum_le_sum ?_
          intro n hn
          exact pow_le_pow_right₀ hz (Finset.mem_filter.1 hn).2
    _ ≤ ∑ n ∈ Finset.Icc 1 y, z ^ omega n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro n _hnIcc hnNotFilter
          exact pow_nonneg hz0 (omega n)

/-- A Rankin wrapper that turns an upper bound for the weighted omega sum into
a real-valued bound for the tail count. -/
lemma omega_tail_card_real_le_of_sum_le
    (y t : ℕ) {z B : ℝ} (hz : 1 ≤ z)
    (hSum : (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤ (y : ℝ) * B) :
    (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ)
      ≤ (y : ℝ) * B / z ^ t := by
  classical
  have hzpow_pos : 0 < z ^ t := pow_pos (zero_lt_one.trans_le hz) t
  have htail := rankin_omega_tail_sum_le y t hz
  have hmul_le : (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
      ≤ (y : ℝ) * B :=
    htail.trans hSum
  exact (le_div_iff₀ hzpow_pos).2 hmul_le

/-- A floor-valued version of `omega_tail_card_real_le_of_sum_le`. -/
lemma omega_tail_card_le_floor_of_sum_le
    (y t : ℕ) {z B X : ℝ} (hz : 1 ≤ z)
    (hX : 0 ≤ X)
    (hSum : (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤ (y : ℝ) * B)
    (hRankinTarget : (y : ℝ) * B / z ^ t ≤ X) :
    ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card ≤ Nat.floor X := by
  refine card_le_floor_of_natCast_le hX ?_
  exact (omega_tail_card_real_le_of_sum_le y t hz hSum).trans hRankinTarget

/-! ## BFV analytic omega tail -/

private lemma tendsto_logloglog_div_loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ))) /
        Real.log (Real.log (N : ℝ))) atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
    have hsmall : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
        fun x : ℝ => Real.log x :=
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    exact hsmall.tendsto_div_nhds_zero
  exact hreal.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma eventually_logloglog_le_mul_loglog
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (Real.log (N : ℝ))) ≤
        δ * Real.log (Real.log (N : ℝ)) := by
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        Real.log (Real.log (Real.log (N : ℝ))) /
          Real.log (Real.log (N : ℝ)) < δ :=
    tendsto_logloglog_div_loglog_nat_atTop.eventually_lt_const hδ
  filter_upwards [hsmall, Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))]
    with N hsmallN hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  exact ((div_lt_iff₀ hloglog_pos).1 hsmallN).le

private lemma BFVz_pos_of_exp_one_lt_nat {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    0 < BFVz N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  rw [BFVz]
  exact div_pos (Real.sqrt_pos.2 hlog_pos) hloglog_pos

private lemma eventually_BFVz_log_lower
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)) ≤ Real.log (BFVz N) := by
  filter_upwards [eventually_logloglog_le_mul_loglog δ hδ,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hlll hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hsqrt_pos : 0 < Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_pos.2 hlog_pos
  have hlog_BFVz :
      Real.log (BFVz N) =
        Real.log (Real.log (N : ℝ)) / 2 -
          Real.log (Real.log (Real.log (N : ℝ))) := by
    rw [BFVz, Real.log_div hsqrt_pos.ne' hloglog_pos.ne',
      Real.log_sqrt hlog_nonneg]
  rw [hlog_BFVz]
  nlinarith

private lemma eventually_BFVz_ge_one :
    ∀ᶠ N : ℕ in atTop, 1 ≤ BFVz N := by
  filter_upwards [eventually_BFVz_log_lower ((1 : ℝ) / 4) (by norm_num),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hlog_lower hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hzpos : 0 < BFVz N := BFVz_pos_of_exp_one_lt_nat hNlarge
  have hlog_nonneg : 0 ≤ Real.log (BFVz N) := by
    nlinarith
  have hone : Real.exp 0 ≤ BFVz N :=
    (Real.le_log_iff_exp_le hzpos).1 hlog_nonneg
  simpa using hone

private lemma eventually_rankin_factor_le
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ t : ℕ, (t : ℝ) ≤ 3 * Mscale N →
        Real.exp ((ε / 2) * Zscale N) / (BFVz N) ^ t
          ≤ Real.exp ((-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N) := by
  let δ : ℝ := ε / 6
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [eventually_BFVz_log_lower δ hδ,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hlog_lower hNlarge_nat t ht
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hNlarge
  have hZnonneg : 0 ≤ Zscale N := Zscale_nonneg N
  have hzpos : 0 < BFVz N := BFVz_pos_of_exp_one_lt_nat hNlarge
  have hLL :
      Real.log (Real.log (N : ℝ)) = Zscale N / Mscale N :=
    (Zscale_div_Mscale_eq_loglog hNlarge).symm
  have ht_nonneg : 0 ≤ (t : ℝ) := by positivity
  have hlog_mul :
      (t : ℝ) * (((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)))
        ≤ (t : ℝ) * Real.log (BFVz N) :=
    mul_le_mul_of_nonneg_left hlog_lower ht_nonneg
  have ht_div_le : (t : ℝ) / Mscale N ≤ 3 := by
    exact (div_le_iff₀ hMpos).2 (by simpa [mul_comm] using ht)
  have hdelta_div : δ * ((t : ℝ) / Mscale N) ≤ ε / 2 := by
    calc
      δ * ((t : ℝ) / Mscale N) ≤ δ * 3 := by
        exact mul_le_mul_of_nonneg_left ht_div_le hδ.le
      _ = ε / 2 := by
        dsimp [δ]
        ring
  have hexp_le :
      (ε / 2) * Zscale N - (t : ℝ) * Real.log (BFVz N)
        ≤ (-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N := by
    have hmain :
        (ε / 2) * Zscale N -
            (t : ℝ) * (((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)))
          ≤ (-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N := by
      rw [hLL]
      have hdeltaZ :
          (δ * ((t : ℝ) / Mscale N)) * Zscale N ≤ (ε / 2) * Zscale N :=
        mul_le_mul_of_nonneg_right hdelta_div hZnonneg
      have hrewrite :
          (t : ℝ) * (((1 : ℝ) / 2 - δ) * (Zscale N / Mscale N)) =
            (((1 : ℝ) / 2 - δ) * ((t : ℝ) / Mscale N)) * Zscale N := by
        field_simp [hMpos.ne']
      rw [hrewrite]
      nlinarith
    nlinarith
  have hzpow :
      (BFVz N) ^ t = Real.exp ((t : ℝ) * Real.log (BFVz N)) := by
    calc
      (BFVz N) ^ t = (Real.exp (Real.log (BFVz N))) ^ t := by
        rw [Real.exp_log hzpos]
      _ = Real.exp ((t : ℝ) * Real.log (BFVz N)) := by
        rw [← Real.exp_nat_mul]
  rw [hzpow, ← Real.exp_sub]
  exact Real.exp_le_exp.2 hexp_le

/-- BFV omega-tail estimate, in the explicit epsilon form used by the exact
counting step.

The Euler-product bound is consumed from `Erdos.P202.BFV.Mertens`
(`omega_weighted_sum_bfvz_bound`); see that file for the analytic gap. -/
theorem bfv_omega_tail_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y t : ℕ, y ≤ N → (t : ℝ) ≤ 3 * Mscale N →
        let α : ℝ := (t : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-α / 2 + ε) * Zscale N)) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [omega_weighted_sum_bfvz_bound (ε / 2) hε2,
      eventually_rankin_factor_le ε hε, eventually_BFVz_ge_one]
    with N hWeighted hRankin hBFVz_ge_one
  intro y t hy ht
  dsimp only
  refine omega_tail_card_le_floor_of_sum_le (y := y) (t := t)
    (z := BFVz N) (B := Real.exp ((ε / 2) * Zscale N))
    (X := (y : ℝ) *
      Real.exp ((-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N))
    hBFVz_ge_one ?_ (hWeighted y hy) ?_
  · positivity
  · have hy_nonneg : 0 ≤ (y : ℝ) := by positivity
    calc
      (y : ℝ) * Real.exp ((ε / 2) * Zscale N) / (BFVz N) ^ t
          = (y : ℝ) *
              (Real.exp ((ε / 2) * Zscale N) / (BFVz N) ^ t) := by
              ring
      _ ≤ (y : ℝ) *
              Real.exp ((-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N) := by
              exact mul_le_mul_of_nonneg_left (hRankin t ht) hy_nonneg

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFV/OmegaExact.lean
    ============================================================= -/

/-
Erdos Problem 202 -- exact omega-count reduction.

This file reduces an exact omega level to the omega-tail estimate from
`OmegaTail.lean` and performs the scale algebra for the BFV `W` factor.
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Exact omega levels are bounded by omega tails -/

lemma omega_exact_filter_subset_tail (y t : ℕ) :
    (Finset.Icc 1 y).filter (fun n => omega n = t)
      ⊆ (Finset.Icc 1 y).filter (fun n => t ≤ omega n) := by
  intro n hn
  exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2.ge⟩

lemma omega_exact_card_le_tail_card (y t : ℕ) :
    ((Finset.Icc 1 y).filter (fun n => omega n = t)).card
      ≤ ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card :=
  Finset.card_le_card (omega_exact_filter_subset_tail y t)

/-! ## BFV scale algebra -/

private lemma exact_target_eq_tail_target {N y K W : ℕ} (ε : ℝ)
    (hN : Real.exp 1 < (N : ℝ)) (hWK : W ≤ K) :
    (y : ℝ) *
        Real.exp ((-(((K - W : ℕ) : ℝ) / Mscale N) / 2 + ε) * Zscale N)
      =
    (y : ℝ) *
        Real.exp ((-((K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hN
  have hZdivM : Zscale N / Mscale N = Real.log (Real.log (N : ℝ)) :=
    Zscale_div_Mscale_eq_loglog hN
  have hcast : (((K - W : ℕ) : ℝ)) = (K : ℝ) - (W : ℝ) := by
    exact_mod_cast (Nat.cast_sub hWK : ((K - W : ℕ) : ℝ) = (K : ℝ) - (W : ℝ))
  have hexp :
      ((-(((K - W : ℕ) : ℝ) / Mscale N) / 2 + ε) * Zscale N)
        =
      ((-((K : ℝ) / Mscale N) / 2 + ε) * Zscale N) +
        (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
    rw [hcast, ← hZdivM]
    field_simp [hMpos.ne']
    ring
  rw [hexp, Real.exp_add]
  ring

/-! ## Exact BFV omega count -/

/-- Exact omega count, derived from `bfv_omega_tail_theorem`.

The statement matches the BFV input shape except for the theorem name. -/
theorem bfv_omega_exact_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) := by
  intro ε hε
  filter_upwards [bfv_omega_tail_theorem ε hε,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hTail hNlarge_nat
  intro y K W hy hWK hK
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hExactTail := omega_exact_card_le_tail_card y (K - W)
  have ht_le_K_real : ((K - W : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast Nat.sub_le K W
  have ht_bound : ((K - W : ℕ) : ℝ) ≤ 3 * Mscale N := ht_le_K_real.trans hK
  have hTailApplied := hTail y (K - W) hy ht_bound
  have htarget :=
    exact_target_eq_tail_target (N := N) (y := y) (K := K) (W := W) ε hNlarge hWK
  dsimp only at hTailApplied ⊢
  exact hExactTail.trans (by simpa [htarget] using hTailApplied)

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFV/OmegaCountInput.lean
    ============================================================= -/

/-
Erdos Problem 202 -- theorem-shaped BFV omega-count input.

This file exposes the theorem name intended to replace
`Erdos202.bfv_omega_count_input` in a later review step.
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-- Proven replacement target for `bfv_omega_count_input`.

At present this theorem depends on `bfv_omega_tail_theorem`, whose analytic
Euler-product component is still the open theorem stub
`omega_weighted_sum_bfvz_bound` in `Mertens.lean`. -/
theorem bfv_omega_count_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) :=
  bfv_omega_exact_theorem

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFV/PrimeIntervals.lean
    ============================================================= -/

/-
Erdos Problem 202 -- prime supply for the BFV lower construction.

This file defines the `dyadicPrimeInterval` used by the explicit lower
construction. The analytic lower bound on its cardinality lives in
`Erdos.P202.BFV.Chebyshev`; this file contains only definitions.
-/


namespace Erdos202

open Filter Finset

/-! ## Dyadic prime intervals -/

/-- The primes in the dyadic interval `(y, 2y]`, represented with natural
floor endpoints.  This is the finite set used by the BFV construction. -/
noncomputable def dyadicPrimeInterval (y : ℝ) : Finset ℕ :=
  (Finset.Ioc (Nat.floor y) (Nat.floor (2 * y))).filter Nat.Prime

lemma mem_dyadicPrimeInterval {y : ℝ} {p : ℕ} :
    p ∈ dyadicPrimeInterval y ↔
      Nat.floor y < p ∧ p ≤ Nat.floor (2 * y) ∧ Nat.Prime p := by
  simp [dyadicPrimeInterval, and_assoc]

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFV/Chebyshev.lean
    ============================================================= -/

/-
Erdős Problem 202 — Chebyshev-style dyadic-interval prime cardinality bound.

# Status

This file proves the prime-supply theorem consumed by the BFV lower path
construction.  The lower bound has a fixed positive Chebyshev constant, which
is enough for the `Lscale (-(1 + ε), N)` BFV lower-bound target.

# Classical content

Chebyshev (1850) proved that there exist absolute constants `c_1, c_2 > 0`
with `c_1 · y / log y ≤ π(y) ≤ c_2 · y / log y`. Subtracting gives, for
some absolute `c > 0`,
  `π(2y) − π(y) ≥ c · y / log y`  for all sufficiently large `y`.

Mathlib `v4.27.0` already has Chebyshev's `θ`-function bounds
(`Nat.theta_le`, `Nat.theta_le_id`, `Nat.id_lt_theta`, etc.) and the
prime-counting function `Nat.primeCounting`. What is NOT packaged is the
Chebyshev-style dyadic-interval lower bound `π(2y) − π(y) ≥ c · y / log y`
nor its `(1 − ε) · y / log y` PNT-strength refinement.

The earlier `(1 - ε)` PNT-strength target has been replaced by the fixed
positive constant `dyadicPrimeIntervalConstant = log 4 / 16`.  The proof below
uses central-binomial/Bertrand-style estimates rather than PNT.

# Where this is consumed

* `Erdos.P202.BFV.Chebyshev.dyadicPrimeInterval_card_lower_bound`
* downstream: `Erdos.P202.BFV.LowerPathConstruction.lowerPath_f_lower_bound_eventually`
  → `Erdos.P202.BFV.LowerBoundInput.bfv_lower_bound_theorem`
  → supplies the historical `Erdos202.bfv_lower_bound_input` interface.
-/


namespace Erdos202

open Filter Finset

/-- Central-binomial upper bound with the actual number of primes in `(n, 2n]`
kept as a factor.  This is the quantitative version of the Bertrand proof:
Mathlib's `centralBinom_le_of_no_bertrand_prime` is the special case where
that interval has cardinality zero. -/
theorem centralBinom_le_mul_pow_dyadicPrimeInterval_card (n : ℕ)
    (hn : 2 < n) :
    n.centralBinom ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
        (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
  classical
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt hn
  have n2_pos : 1 ≤ 2 * n := mul_pos (by norm_num : 0 < 2) n_pos
  let S : Finset ℕ := (Finset.range (2 * n + 1)).filter Nat.Prime
  let f : ℕ → ℕ := fun p => p ^ n.centralBinom.factorization p
  let A : Finset ℕ := S.filter (fun p => p ≤ Nat.sqrt (2 * n))
  let B : Finset ℕ := S.filter (fun p => ¬ p ≤ Nat.sqrt (2 * n))
  let B₁ : Finset ℕ := B.filter (fun p => p ≤ 2 * n / 3)
  let B₂ : Finset ℕ := B.filter (fun p => ¬ p ≤ 2 * n / 3)
  let C : Finset ℕ := B₂.filter (fun p => p ≤ n)
  let D : Finset ℕ := B₂.filter (fun p => ¬ p ≤ n)
  have hfilter :
      (∏ p ∈ S, f p) =
        ∏ p ∈ Finset.range (2 * n + 1), f p := by
    refine Finset.prod_filter_of_ne fun p _hp h => ?_
    contrapose! h
    dsimp [f]
    rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom h, pow_zero]
  have hfull : n.centralBinom = ∏ p ∈ S, f p := by
    calc
      n.centralBinom = ∏ p ∈ Finset.range (2 * n + 1), f p := by
        simpa [f] using (Nat.prod_pow_factorization_centralBinom n).symm
      _ = ∏ p ∈ S, f p := hfilter.symm
  have hsplitA :
      (∏ p ∈ S, f p) = (∏ p ∈ A, f p) * (∏ p ∈ B, f p) := by
    simpa [A, B] using
      (Finset.prod_filter_mul_prod_filter_not S
        (fun p => p ≤ Nat.sqrt (2 * n)) f).symm
  have hsplitB :
      (∏ p ∈ B, f p) = (∏ p ∈ B₁, f p) * (∏ p ∈ B₂, f p) := by
    simpa [B₁, B₂] using
      (Finset.prod_filter_mul_prod_filter_not B
        (fun p => p ≤ 2 * n / 3) f).symm
  have hsplitC :
      (∏ p ∈ B₂, f p) = (∏ p ∈ C, f p) * (∏ p ∈ D, f p) := by
    simpa [C, D] using
      (Finset.prod_filter_mul_prod_filter_not B₂
        (fun p => p ≤ n) f).symm
  have hsmall : (∏ p ∈ A, f p) ≤ (2 * n) ^ Nat.sqrt (2 * n) := by
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ 2 * n)).trans ?_
    · exact Nat.pow_factorization_choose_le (mul_pos (by norm_num : 0 < 2) n_pos)
    have hcard : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
      rw [Nat.card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun p hp => ?_).trans hcard.le)
    obtain ⟨hpS, hple⟩ := Finset.mem_filter.1 hp
    obtain ⟨_hrange, hpprime⟩ := Finset.mem_filter.1 hpS
    exact Finset.mem_Icc.mpr ⟨hpprime.one_lt.le, hple⟩
  have hmid : (∏ p ∈ B₁, f p) ≤ 4 ^ (2 * n / 3) := by
    refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    have htoP : (∏ p ∈ B₁, f p) ≤ ∏ p ∈ B₁, p := by
      refine Finset.prod_le_prod' fun p hp => ?_
      obtain ⟨hpB, _hple_mid⟩ := Finset.mem_filter.1 hp
      obtain ⟨hpS, hp_not_small⟩ := Finset.mem_filter.1 hpB
      obtain ⟨_hrange, hpprime⟩ := Finset.mem_filter.1 hpS
      dsimp [f]
      refine (pow_right_mono₀ hpprime.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one
        (Nat.sqrt_lt'.mp (Nat.lt_of_not_ge hp_not_small))
    refine htoP.trans ?_
    unfold primorial
    refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
    · intro p hp
      obtain ⟨hpB, hple_mid⟩ := Finset.mem_filter.1 hp
      obtain ⟨hpS, _hp_not_small⟩ := Finset.mem_filter.1 hpB
      obtain ⟨_hrange, hpprime⟩ := Finset.mem_filter.1 hpS
      exact Finset.mem_filter.2
        ⟨Finset.mem_range.2 (Nat.lt_succ_iff.2 hple_mid), hpprime⟩
    · intro p hpT _hpnot
      exact (Finset.mem_filter.1 hpT).2.one_lt.le
  have hgap : (∏ p ∈ C, f p) = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    obtain ⟨hpB₂, hple_n⟩ := Finset.mem_filter.1 hp
    obtain ⟨_hpB, hp_not_mid⟩ := Finset.mem_filter.1 hpB₂
    have htwo_lt_three :
        2 * n < 3 * p := by
      have hlt : 2 * n / 3 < p := Nat.lt_of_not_ge hp_not_mid
      have h := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).1 hlt
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hfac0 :
        n.centralBinom.factorization p = 0 :=
      Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hple_n htwo_lt_three
    simp [f, hfac0]
  have hDsub : D ⊆ (Finset.Ioc n (2 * n)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpB₂, hp_not_le_n⟩ := Finset.mem_filter.1 hp
    obtain ⟨hpB, _hp_not_mid⟩ := Finset.mem_filter.1 hpB₂
    obtain ⟨hpS, _hp_not_small⟩ := Finset.mem_filter.1 hpB
    obtain ⟨hrange, hpprime⟩ := Finset.mem_filter.1 hpS
    have hle_two : p ≤ 2 * n := by
      exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hrange)
    have hn_lt : n < p := Nat.lt_of_not_ge hp_not_le_n
    exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hn_lt, hle_two⟩, hpprime⟩
  have hinterval :
      (∏ p ∈ D, f p) ≤
        (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
    refine (Finset.prod_le_prod' fun p _hp => (?_ : f p ≤ 2 * n)).trans ?_
    · exact Nat.pow_factorization_choose_le (mul_pos (by norm_num : 0 < 2) n_pos)
    rw [Finset.prod_const]
    exact pow_right_mono₀ n2_pos (Finset.card_le_card hDsub)
  calc
    n.centralBinom = ∏ p ∈ S, f p := hfull
    _ = (∏ p ∈ A, f p) *
          ((∏ p ∈ B₁, f p) * ((∏ p ∈ C, f p) * (∏ p ∈ D, f p))) := by
            rw [hsplitA, hsplitB, hsplitC]
    _ = (∏ p ∈ A, f p) * ((∏ p ∈ B₁, f p) * (∏ p ∈ D, f p)) := by
            rw [hgap]
            simp
    _ ≤ (2 * n) ^ Nat.sqrt (2 * n) *
          (4 ^ (2 * n / 3) *
            (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card) := by
            gcongr
    _ = (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
          (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
            ac_rfl

lemma dyadicPrimeInterval_nat_card_mul_log_lower_of_estimates
    (n : ℕ) (hn4 : 4 ≤ n)
    (hlogn : Real.log (n : ℝ) ≤ (Real.log 4 / 24) * (n : ℝ))
    (hsqrtlog :
      Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) ≤
        (Real.log 4 / 24) * (n : ℝ)) :
    (Real.log 4 / 4) * (n : ℝ) ≤
      (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) *
        Real.log (2 * (n : ℝ)) := by
  classical
  let K : ℕ := ((Finset.Ioc n (2 * n)).filter Nat.Prime).card
  have hn2 : 2 < n := by omega
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 4) hn4
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have h2n_pos_real : 0 < (2 * (n : ℝ)) := by positivity
  have h2n_cast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by norm_num
  have hn_ge_four_real : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hlog2n_nonneg : 0 ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hcentral :=
    centralBinom_le_mul_pow_dyadicPrimeInterval_card n hn2
  have hfour : 4 ^ n < n * n.centralBinom :=
    Nat.four_pow_lt_mul_centralBinom n hn4
  have hlt_nat :
      4 ^ n <
        n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
          (2 * n) ^ K) := by
    exact hfour.trans_le (Nat.mul_le_mul_left n hcentral)
  have hlt_real :
      (4 : ℝ) ^ n <
        (n : ℝ) *
          (((2 * (n : ℝ)) ^ Nat.sqrt (2 * n)) *
            ((4 : ℝ) ^ (2 * n / 3)) *
            ((2 * (n : ℝ)) ^ K)) := by
    exact_mod_cast hlt_nat
  have hlog_le := Real.log_le_log (by positivity : (0 : ℝ) < (4 : ℝ) ^ n) hlt_real.le
  have hlog_expand :
      Real.log
        ((n : ℝ) *
          (((2 * (n : ℝ)) ^ Nat.sqrt (2 * n)) *
            ((4 : ℝ) ^ (2 * n / 3)) *
            ((2 * (n : ℝ)) ^ K)))
        =
        Real.log (n : ℝ) +
          (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) +
          ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 +
          (K : ℝ) * Real.log (2 * (n : ℝ)) := by
    rw [Real.log_mul hn_pos.ne']
    · rw [Real.log_mul]
      · rw [Real.log_mul]
        · rw [Real.log_pow, Real.log_pow, Real.log_pow]
          ring
        · exact pow_ne_zero _ h2n_pos_real.ne'
        · exact pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0)
      · exact mul_ne_zero (pow_ne_zero _ h2n_pos_real.ne')
          (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0))
      · exact pow_ne_zero _ h2n_pos_real.ne'
    · exact mul_ne_zero
        (mul_ne_zero (pow_ne_zero _ h2n_pos_real.ne')
          (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0)))
        (pow_ne_zero _ h2n_pos_real.ne')
  have hlog_main :
      (n : ℝ) * Real.log 4 ≤
        Real.log (n : ℝ) +
          (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) +
          ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 +
          (K : ℝ) * Real.log (2 * (n : ℝ)) := by
    have hleft : Real.log ((4 : ℝ) ^ n) = (n : ℝ) * Real.log 4 := by
      rw [Real.log_pow]
    linarith
  have hsqrt_cast :
      (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := by
    rw [← h2n_cast]
    exact_mod_cast Real.nat_sqrt_le_real_sqrt
  have hsqrt_term :
      (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) ≤
        Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) := by
    exact mul_le_mul_of_nonneg_right hsqrt_cast hlog2n_nonneg
  have hdiv_term :
      ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 ≤
        ((2 : ℝ) * (n : ℝ) / 3) * Real.log 4 := by
    have hdiv : ((2 * n / 3 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) / 3 :=
      Nat.cast_div_le.trans_eq (by norm_num)
    rw [h2n_cast] at hdiv
    exact mul_le_mul_of_nonneg_right hdiv hlog4_pos.le
  have hmain' :
      (n : ℝ) * Real.log 4 ≤
        Real.log (n : ℝ) +
          Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) +
          ((2 : ℝ) * (n : ℝ) / 3) * Real.log 4 +
          (K : ℝ) * Real.log (2 * (n : ℝ)) := by
    linarith
  have hsmall_sum :
      Real.log (n : ℝ) +
        Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) ≤
        (Real.log 4 / 12) * (n : ℝ) := by
    linarith
  have hresult :
      (Real.log 4 / 4) * (n : ℝ) ≤
        (K : ℝ) * Real.log (2 * (n : ℝ)) := by
    nlinarith
  simpa [K] using hresult

lemma eventually_log_nat_le_const_mul_self (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ δ * (n : ℝ) := by
  have hsmall :
      (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
        fun n : ℕ => (n : ℝ) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [Asymptotics.isLittleO_iff.mp hsmall hδ] with n hn
  have hright_norm : ‖(n : ℝ)‖ = (n : ℝ) := by
    exact Real.norm_of_nonneg (Nat.cast_nonneg n)
  have hlog_le_norm :
      Real.log (n : ℝ) ≤ ‖Real.log (n : ℝ)‖ := by
    simpa [Real.norm_eq_abs] using le_abs_self (Real.log (n : ℝ))
  calc
    Real.log (n : ℝ) ≤ ‖Real.log (n : ℝ)‖ := hlog_le_norm
    _ ≤ δ * ‖(n : ℝ)‖ := hn
    _ = δ * (n : ℝ) := by rw [hright_norm]

lemma eventually_sqrt_two_mul_log_two_mul_le_const_mul_self
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) ≤
        δ * (n : ℝ) := by
  have hδ2 : 0 < δ / 2 := by positivity
  have htwo_atTop :
      Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      tendsto_natCast_atTop_atTop
  have hsmall :
      (fun n : ℕ => Real.log (2 * (n : ℝ))) =o[atTop]
        fun n : ℕ => Real.sqrt (2 * (n : ℝ)) := by
    have h :=
      (isLittleO_log_rpow_atTop
        (show (0 : ℝ) < (1 / 2 : ℝ) by norm_num)).comp_tendsto
          htwo_atTop
    simpa [Real.sqrt_eq_rpow, mul_comm, mul_left_comm, mul_assoc] using h
  filter_upwards [Asymptotics.isLittleO_iff.mp hsmall hδ2] with n hn
  set x : ℝ := 2 * (n : ℝ)
  have hx_nonneg : 0 ≤ x := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt_norm : ‖Real.sqrt x‖ = Real.sqrt x :=
    Real.norm_of_nonneg hsqrt_nonneg
  have hlog_le : Real.log x ≤ (δ / 2) * Real.sqrt x := by
    have hlog_le_norm : Real.log x ≤ ‖Real.log x‖ := by
      simpa [Real.norm_eq_abs] using le_abs_self (Real.log x)
    calc
      Real.log x ≤ ‖Real.log x‖ := hlog_le_norm
      _ ≤ (δ / 2) * ‖Real.sqrt x‖ := by simpa [x] using hn
      _ = (δ / 2) * Real.sqrt x := by rw [hsqrt_norm]
  calc
    Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ))
        = Real.sqrt x * Real.log x := by simp [x]
    _ ≤ Real.sqrt x * ((δ / 2) * Real.sqrt x) :=
          mul_le_mul_of_nonneg_left hlog_le hsqrt_nonneg
    _ = (δ / 2) * (Real.sqrt x) ^ 2 := by ring
    _ = (δ / 2) * x := by rw [Real.sq_sqrt hx_nonneg]
    _ = δ * (n : ℝ) := by simp [x]; ring

theorem dyadicPrimeInterval_nat_card_lower_bound_eventually :
    ∀ᶠ n : ℕ in atTop,
      Nat.floor (((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ))) ≤
        ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
  filter_upwards [
      Filter.eventually_ge_atTop 4,
      eventually_log_nat_le_const_mul_self (Real.log 4 / 24)
        (by positivity),
      eventually_sqrt_two_mul_log_two_mul_le_const_mul_self
        (Real.log 4 / 24) (by positivity)] with n hn4 hlogn hsqrtlog
  have hmul :=
    dyadicPrimeInterval_nat_card_mul_log_lower_of_estimates n hn4 hlogn hsqrtlog
  have hlog_pos : 0 < Real.log (2 * (n : ℝ)) := by
    have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    exact Real.log_pos (by nlinarith)
  have hdiv :
      ((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ)) ≤
        (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) := by
    exact (div_le_iff₀ hlog_pos).2 hmul
  exact Nat.floor_le_of_le hdiv

/-- A fixed Chebyshev constant supplied by the elementary central-binomial
argument above.  The value is intentionally conservative; the BFV lower
construction only needs some positive absolute constant. -/
noncomputable def dyadicPrimeIntervalConstant : ℝ :=
  Real.log 4 / 16

lemma dyadicPrimeIntervalConstant_pos : 0 < dyadicPrimeIntervalConstant := by
  unfold dyadicPrimeIntervalConstant
  positivity

/-- Chebyshev-strength lower bound for the number of primes in a dyadic
interval.  This is weaker than the PNT-strength `(1 - ε)` estimate, but it is
enough for the BFV lower construction because a fixed constant per block is
only an `L(o(1), N)` loss. -/
theorem dyadicPrimeInterval_card_lower_bound :
    ∀ᶠ y : ℝ in atTop,
      Nat.floor (dyadicPrimeIntervalConstant * y / Real.log y) ≤
        (dyadicPrimeInterval y).card := by
  rcases eventually_atTop.1 dyadicPrimeInterval_nat_card_lower_bound_eventually with
    ⟨N0, hN0⟩
  filter_upwards [Filter.eventually_ge_atTop (max 8 (N0 + 1 : ℕ) : ℝ)] with y hy
  classical
  let n : ℕ := Nat.floor y
  have hy_ge8 : (8 : ℝ) ≤ y := (le_max_left _ _).trans hy
  have hy_ge2 : (2 : ℝ) ≤ y := by linarith
  have hy_pos : 0 < y := by linarith
  have hy_nonneg : 0 ≤ y := hy_pos.le
  have hn_floor_le : (n : ℝ) ≤ y := by
    simpa [n] using Nat.floor_le hy_nonneg
  have hn_large : N0 ≤ n := by
    have hN0y : ((N0 + 1 : ℕ) : ℝ) ≤ y := by
      exact (le_max_right (8 : ℝ) (N0 + 1 : ℕ)).trans hy
    have hN0_le_floor : (N0 + 1 : ℕ) ≤ n := by
      exact Nat.le_floor hN0y
    exact (Nat.le_succ N0).trans hN0_le_floor
  have hn_ge4_nat : 4 ≤ n := by
    have h4y : (4 : ℝ) ≤ y := by linarith
    exact Nat.le_floor h4y
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 4) hn_ge4_nat
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hnat_bound :
      Nat.floor (((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ))) ≤
        ((Finset.Ioc n (2 * n)).filter Nat.Prime).card :=
    hN0 n hn_large
  have hn_lower : y / 2 ≤ (n : ℝ) := by
    have hfloor_gt : y < (n : ℝ) + 1 := by
      simpa [n] using Nat.lt_floor_add_one y
    linarith
  have hlog_y_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog2n_pos : 0 < Real.log (2 * (n : ℝ)) := by
    exact Real.log_pos (by nlinarith)
  have hlog2n_le : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log y := by
    have h2n_pos : 0 < 2 * (n : ℝ) := by positivity
    have h2n_le_y_sq : 2 * (n : ℝ) ≤ y ^ 2 := by
      have h2n_le_2y : 2 * (n : ℝ) ≤ 2 * y := by nlinarith
      have h2y_le_y_sq : 2 * y ≤ y ^ 2 := by
        nlinarith [mul_self_nonneg (y - 1)]
      exact h2n_le_2y.trans h2y_le_y_sq
    calc
      Real.log (2 * (n : ℝ)) ≤ Real.log (y ^ 2) :=
        Real.log_le_log h2n_pos h2n_le_y_sq
      _ = 2 * Real.log y := by
        rw [Real.log_pow]
        norm_num
  have htarget_le_nat_arg :
      dyadicPrimeIntervalConstant * y / Real.log y ≤
        ((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ)) := by
    have hnum :
        dyadicPrimeIntervalConstant * y ≤
          ((Real.log 4 / 4) * (n : ℝ)) / 2 := by
      unfold dyadicPrimeIntervalConstant
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 4), hn_lower]
    have hstep1 :
        dyadicPrimeIntervalConstant * y / Real.log y ≤
          (((Real.log 4 / 4) * (n : ℝ)) / 2) / Real.log y :=
      div_le_div_of_nonneg_right hnum hlog_y_pos.le
    have hstep2 :
        (((Real.log 4 / 4) * (n : ℝ)) / 2) / Real.log y =
          ((Real.log 4 / 4) * (n : ℝ)) / (2 * Real.log y) := by
      field_simp [hlog_y_pos.ne']
    have hnum_nonneg : 0 ≤ (Real.log 4 / 4) * (n : ℝ) := by positivity
    have hstep3 :
        ((Real.log 4 / 4) * (n : ℝ)) / (2 * Real.log y) ≤
          ((Real.log 4 / 4) * (n : ℝ)) /
            Real.log (2 * (n : ℝ)) := by
      exact div_le_div_of_nonneg_left hnum_nonneg hlog2n_pos hlog2n_le
    calc
      dyadicPrimeIntervalConstant * y / Real.log y
          ≤ (((Real.log 4 / 4) * (n : ℝ)) / 2) / Real.log y := hstep1
      _ = ((Real.log 4 / 4) * (n : ℝ)) / (2 * Real.log y) := hstep2
      _ ≤ ((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ)) := hstep3
  have hfloor_le_nat :
      Nat.floor (dyadicPrimeIntervalConstant * y / Real.log y) ≤
        ((Finset.Ioc n (2 * n)).filter Nat.Prime).card :=
    (Nat.floor_le_floor htarget_le_nat_arg).trans hnat_bound
  have hsubset :
      ((Finset.Ioc n (2 * n)).filter Nat.Prime) ⊆ dyadicPrimeInterval y := by
    intro p hp
    obtain ⟨hpIoc, hpprime⟩ := Finset.mem_filter.1 hp
    obtain ⟨hnp, hp2n⟩ := Finset.mem_Ioc.1 hpIoc
    have h2floor_le : 2 * n ≤ Nat.floor (2 * y) := by
      have hcast : ((2 * n : ℕ) : ℝ) ≤ 2 * y := by
        norm_num
        nlinarith [hn_floor_le]
      exact Nat.le_floor hcast
    exact (mem_dyadicPrimeInterval.2
      ⟨by simpa [n] using hnp, hp2n.trans h2floor_le, hpprime⟩)
  exact hfloor_le_nat.trans (Finset.card_le_card hsubset)

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFV/LowerPathScales.lean
    ============================================================= -/

/-
Erdos Problem 202 -- BFV lower construction, source-aligned path scales.

This file is a non-consuming scaffold for replacing the current fixed-root
lower construction in `LowerConstruction.lean`.  The key point is the BFV
source scale:

* roughly `2 * M(N)` prime blocks;
* logarithmic gap about `(1 / 2) * log log N - sqrt (log log N)`;
* exact normalization `prod_i (2 * Y_i) = N`.

The existing rooted construction fixes a whole root block and is too small for
the lower-bound target.  These path scales are the product/capacity side of the
BFV Section 2 construction, isolated so the later refactor can proceed without
destabilizing the current proof path.
-/


namespace Erdos202

open Filter Finset
open Asymptotics
open scoped BigOperators

/-! ## Source-aligned path parameters -/

/-- BFV path depth, approximately `2 * M(N)`. -/
noncomputable def lowerPathR (N : ℕ) : ℕ :=
  Nat.floor (2 * Mscale N)

/-- Path block indices `{0, ..., lowerPathR N}`. -/
abbrev lowerPathIndex (N : ℕ) : Type :=
  Fin (lowerPathR N + 1)

/-- Source-aligned logarithmic gap between consecutive prime blocks.

Eventually this is larger than `log 2`, so dyadic intervals are disjoint; it
is also small enough relative to the block logarithms to support the BFV
encoding inequality `|block_{i+1}| <= p_i`. -/
noncomputable def lowerPathLogGap (N : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) -
    Real.sqrt (Real.log (Real.log (N : ℝ)))

/-- Product-normalized initial log scale. -/
noncomputable def lowerPathLogBase (N : ℕ) : ℝ :=
  (Real.log (N : ℝ) - ((lowerPathR N : ℝ) + 1) * Real.log 2 -
      lowerPathLogGap N * ((lowerPathR N : ℝ) * ((lowerPathR N : ℝ) + 1) / 2)) /
    ((lowerPathR N : ℝ) + 1)

/-- Logarithmic scale of the `i`th source-aligned path block. -/
noncomputable def lowerPathLogScale (N : ℕ) (i : lowerPathIndex N) : ℝ :=
  lowerPathLogBase N + (i.1 : ℝ) * lowerPathLogGap N

/-- Real prime scale of the `i`th source-aligned path block. -/
noncomputable def lowerPathY (N : ℕ) (i : lowerPathIndex N) : ℝ :=
  Real.exp (lowerPathLogScale N i)

lemma lowerPathLogScale_sub (N : ℕ) (i j : lowerPathIndex N) :
    lowerPathLogScale N i - lowerPathLogScale N j =
      ((i.1 : ℝ) - (j.1 : ℝ)) * lowerPathLogGap N := by
  simp [lowerPathLogScale]
  ring

lemma lowerPathIndex_sum_val (N : ℕ) :
    (∑ i : lowerPathIndex N, (i.1 : ℝ)) =
      (lowerPathR N : ℝ) * ((lowerPathR N : ℝ) + 1) / 2 := by
  let r := lowerPathR N
  change (∑ i : Fin (r + 1), (i.1 : ℝ)) = (r : ℝ) * ((r : ℝ) + 1) / 2
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ x ∈ Finset.range (r + 1), if h : x < r + 1 then (x : ℝ) else 0)
        = ∑ x ∈ Finset.range (r + 1), (x : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [Finset.mem_range.mp hx]
    _ = (r : ℝ) * ((r : ℝ) + 1) / 2 := by
          have hnat : (∑ i ∈ Finset.range (r + 1), i) * 2 = (r + 1) * r := by
            simpa using Finset.sum_range_id_mul_two (r + 1)
          have hreal :
              ((∑ i ∈ Finset.range (r + 1), i : ℕ) : ℝ) * 2 =
                ((r + 1) * r : ℕ) := by
            exact_mod_cast hnat
          rw [← Nat.cast_sum]
          calc
            ((∑ i ∈ Finset.range (r + 1), i : ℕ) : ℝ)
                = (((∑ i ∈ Finset.range (r + 1), i : ℕ) : ℝ) * 2) / 2 := by
                    ring
            _ = (((r + 1) * r : ℕ) : ℝ) / 2 := by rw [hreal]
            _ = (r : ℝ) * ((r : ℝ) + 1) / 2 := by
                    norm_num
                    ring

lemma lowerPathLogScale_sum (N : ℕ) :
    (∑ i : lowerPathIndex N, lowerPathLogScale N i) =
      Real.log (N : ℝ) - ((lowerPathR N : ℝ) + 1) * Real.log 2 := by
  have hcard : ((Finset.univ : Finset (lowerPathIndex N)).card : ℝ) =
      (lowerPathR N : ℝ) + 1 := by
    simp [lowerPathIndex]
  have hsum := lowerPathIndex_sum_val N
  simp [lowerPathLogScale, lowerPathLogBase]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
  rw [hsum, hcard]
  have hden : (lowerPathR N : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- The source-aligned scales are normalized at the dyadic upper endpoints:
`prod_i (2 * Y_i) = N`. -/
lemma lowerPathY_dyadic_product_eq {N : ℕ} (hNpos : 0 < (N : ℝ)) :
    (∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i) = (N : ℝ) := by
  calc
    (∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i)
        = ∏ i : lowerPathIndex N,
            Real.exp (Real.log 2 + lowerPathLogScale N i) := by
          apply Finset.prod_congr rfl
          intro i _hi
          rw [lowerPathY, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = Real.exp (∑ i : lowerPathIndex N,
            (Real.log 2 + lowerPathLogScale N i)) := by
          rw [← Real.exp_sum]
    _ = Real.exp (Real.log (N : ℝ)) := by
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            lowerPathLogScale_sum]
          have hcard : ((Finset.univ : Finset (lowerPathIndex N)).card : ℝ) =
              (lowerPathR N : ℝ) + 1 := by
            simp [lowerPathIndex]
          rw [hcard]
          ring
    _ = (N : ℝ) := Real.exp_log hNpos

lemma eventually_lowerPathLogGap_gt_log_two :
    ∀ᶠ N : ℕ in atTop, Real.log 2 < lowerPathLogGap N := by
  filter_upwards [eventually_sqrt_loglog_ge 4,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 0] with N hsqrt hloglog_nonneg
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg Y
  have hY_eq : Y = s ^ 2 := by
    calc
      Y = Real.sqrt Y * Real.sqrt Y := by
            rw [Real.mul_self_sqrt hloglog_nonneg]
      _ = s ^ 2 := by
            simp [s, sq]
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hmain : Real.log 2 < (1 / 2 : ℝ) * Y - s := by
    rw [hY_eq]
    nlinarith
  simpa [lowerPathLogGap, Y, s] using hmain

lemma lowerPathY_dyadic_lt_of_lt_index {N : ℕ} {i j : lowerPathIndex N}
    (hgap : Real.log 2 < lowerPathLogGap N) (hij : i.1 < j.1) :
    2 * lowerPathY N i < lowerPathY N j := by
  have hsucc : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.2 hij
  have hdiff_real : 1 ≤ (j.1 : ℝ) - (i.1 : ℝ) := by
    have hsuccR : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast hsucc
    linarith
  have hgap_pos : 0 < lowerPathLogGap N :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans hgap
  have hmain :
      Real.log 2 + lowerPathLogScale N i < lowerPathLogScale N j := by
    have hsub := lowerPathLogScale_sub N j i
    have hmul : Real.log 2 < ((j.1 : ℝ) - (i.1 : ℝ)) * lowerPathLogGap N := by
      calc
        Real.log 2 < lowerPathLogGap N := hgap
        _ ≤ ((j.1 : ℝ) - (i.1 : ℝ)) * lowerPathLogGap N := by
          nlinarith
    nlinarith
  calc
    2 * lowerPathY N i
        = Real.exp (Real.log 2 + lowerPathLogScale N i) := by
            rw [lowerPathY, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ < Real.exp (lowerPathLogScale N j) := Real.exp_lt_exp.2 hmain
    _ = lowerPathY N j := by rw [lowerPathY]

lemma lowerPathLogScale_le_of_index_le {N : ℕ} {i j : lowerPathIndex N}
    (hgap_nonneg : 0 ≤ lowerPathLogGap N) (hij : i.1 ≤ j.1) :
    lowerPathLogScale N i ≤ lowerPathLogScale N j := by
  have hsub := lowerPathLogScale_sub N j i
  have hdiff_nonneg : 0 ≤ ((j.1 : ℝ) - (i.1 : ℝ)) * lowerPathLogGap N := by
    have hidx : 0 ≤ (j.1 : ℝ) - (i.1 : ℝ) := by
      exact sub_nonneg.2 (by exact_mod_cast hij)
    exact mul_nonneg hidx hgap_nonneg
  nlinarith

lemma lowerPathY_le_of_index_le {N : ℕ} {i j : lowerPathIndex N}
    (hgap_nonneg : 0 ≤ lowerPathLogGap N) (hij : i.1 ≤ j.1) :
    lowerPathY N i ≤ lowerPathY N j :=
  Real.exp_le_exp.2 (lowerPathLogScale_le_of_index_le hgap_nonneg hij)

lemma lowerPathY_adjacent_eq_mul_exp_gap {N : ℕ} {i j : lowerPathIndex N}
    (hij : j.1 = i.1 + 1) :
    lowerPathY N j = lowerPathY N i * Real.exp (lowerPathLogGap N) := by
  have hsub := lowerPathLogScale_sub N j i
  have hscale : lowerPathLogScale N j = lowerPathLogScale N i + lowerPathLogGap N := by
    have hdiff : ((j.1 : ℝ) - (i.1 : ℝ)) = 1 := by
      rw [hij]
      norm_num
    rw [hdiff, one_mul] at hsub
    linarith
  rw [lowerPathY, lowerPathY, hscale, Real.exp_add]

/-! ## Startup scale estimates -/

lemma eventually_loglog_cubed_le_log :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (N : ℝ)) ^ 3 ≤ Real.log (N : ℝ) := by
  have hsmall_real :
      (fun x : ℝ => Real.log x ^ 3) =o[atTop] fun x : ℝ => x :=
    Real.isLittleO_pow_log_id_atTop
  have hlog_atTop :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall :
      (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ 3) =o[atTop]
        fun N : ℕ => Real.log (N : ℝ) :=
    hsmall_real.comp_tendsto hlog_atTop
  filter_upwards [isLittleO_iff.mp hsmall zero_lt_one,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsmallN hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hleft_norm :
      ‖Real.log (Real.log (N : ℝ)) ^ 3‖ =
        Real.log (Real.log (N : ℝ)) ^ 3 := by
    rw [Real.norm_of_nonneg]
    positivity
  have hright_norm : ‖Real.log (N : ℝ)‖ = Real.log (N : ℝ) := by
    rw [Real.norm_of_nonneg hlog_pos.le]
  simpa [hleft_norm, hright_norm] using hsmallN

lemma eventually_loglog_le_Mscale :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (N : ℝ)) ≤ Mscale N := by
  filter_upwards [eventually_loglog_cubed_le_log,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hcube hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hquot_nonneg :
      0 ≤ Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) :=
    div_nonneg hlog_pos.le hloglog_pos.le
  rw [Mscale]
  refine (Real.le_sqrt hloglog_pos.le hquot_nonneg).2 ?_
  rw [sq]
  exact (le_div_iff₀ hloglog_pos).2 (by
    simpa [pow_succ, pow_two, mul_assoc] using hcube)

lemma lowerPathLogScale_zero_eq (N : ℕ) :
    lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ =
      Real.log (N : ℝ) / ((lowerPathR N : ℝ) + 1) -
        Real.log 2 - lowerPathLogGap N * (lowerPathR N : ℝ) / 2 := by
  have hden : (lowerPathR N : ℝ) + 1 ≠ 0 := by positivity
  simp [lowerPathLogScale, lowerPathLogBase]
  field_simp [hden]

lemma lowerPathLogScale_zero_nonneg_of_loglog_le_Mscale {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ))
    (hloglog_ge : 16 ≤ Real.log (Real.log (N : ℝ)))
    (hloglog_le_M : Real.log (Real.log (N : ℝ)) ≤ Mscale N) :
    0 ≤ lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := by
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  set r : ℝ := (lowerPathR N : ℝ)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg Y
  have hs_sq : s ^ 2 = Y := by
    dsimp [s]
    exact Real.sq_sqrt hY_nonneg
  have hs_ge_four : 4 ≤ s := by
    refine (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 4) hY_nonneg).2 ?_
    norm_num
    exact hloglog_ge
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Mscale_nonneg N
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hY_le_M : Y ≤ M := by
    simpa [Y, M] using hloglog_le_M
  have hM_ge_one : 1 ≤ M := by
    have : (1 : ℝ) ≤ Y := by linarith
    exact this.trans hY_le_M
  have hr_le : r ≤ 2 * M := by
    dsimp [r, M]
    exact Nat.floor_le (by positivity : 0 ≤ 2 * Mscale N)
  have hden_pos : 0 < r + 1 := by positivity
  have hden_le : r + 1 ≤ 2 * M + 1 := by linarith
  have htwoM1_pos : 0 < 2 * M + 1 := by positivity
  have hMll : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hMZ : M * Zscale N = Real.log (N : ℝ) := by
    dsimp [M]
    exact Mscale_mul_Zscale_eq_log hNlarge
  have hlog_eq : Real.log (N : ℝ) = M ^ 2 * Y := by
    rw [← hMZ, ← hMll]
    ring
  have hdiv_ge :
      M ^ 2 * Y / (2 * M + 1) ≤ Real.log (N : ℝ) / (r + 1) := by
    rw [hlog_eq]
    exact div_le_div_of_nonneg_left (by positivity) hden_pos hden_le
  have hgap_eq : lowerPathLogGap N = Y / 2 - s := by
    rw [lowerPathLogGap]
    dsimp [Y, s]
    ring
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    rw [hgap_eq]
    nlinarith [hs_sq]
  have hgap_le : lowerPathLogGap N ≤ Y / 2 - s := by
    rw [hgap_eq]
  have hgap_r_le :
      lowerPathLogGap N * r / 2 ≤ M * (Y / 2 - s) := by
    rw [hgap_eq]
    have hgap0 : 0 ≤ Y / 2 - s := by
      nlinarith [hs_sq]
    nlinarith
  have hfrac_le_M :
      M * Y / (2 * (2 * M + 1)) ≤ M := by
    have hden2_pos : 0 < 2 * (2 * M + 1) := by positivity
    rw [div_le_iff₀ hden2_pos]
    nlinarith
  have hcore :
      1 ≤ M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s) := by
    have hrewrite :
        M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s) =
          M * s - M * Y / (2 * (2 * M + 1)) := by
      field_simp [htwoM1_pos.ne']
      ring
    rw [hrewrite]
    calc
      (1 : ℝ) ≤ M := hM_ge_one
      _ ≤ M * s - M * Y / (2 * (2 * M + 1)) := by
            have hMs_ge_twoM : 2 * M ≤ M * s := by nlinarith
            nlinarith
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  rw [lowerPathLogScale_zero_eq]
  calc
    0 ≤
        (M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s)) - Real.log 2 := by
          linarith
    _ ≤ Real.log (N : ℝ) / (r + 1) - Real.log 2 -
        lowerPathLogGap N * r / 2 := by
          nlinarith

lemma lowerPathLogScale_zero_ge_half_M_mul_sqrt_loglog {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ))
    (hloglog_ge : 16 ≤ Real.log (Real.log (N : ℝ)))
    (hloglog_le_M : Real.log (Real.log (N : ℝ)) ≤ Mscale N) :
    Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) / 2 ≤
      lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := by
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  set r : ℝ := (lowerPathR N : ℝ)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg Y
  have hs_sq : s ^ 2 = Y := by
    dsimp [s]
    exact Real.sq_sqrt hY_nonneg
  have hs_ge_four : 4 ≤ s := by
    refine (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 4) hY_nonneg).2 ?_
    norm_num
    exact hloglog_ge
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Mscale_nonneg N
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hY_le_M : Y ≤ M := by
    simpa [Y, M] using hloglog_le_M
  have hr_le : r ≤ 2 * M := by
    dsimp [r, M]
    exact Nat.floor_le (by positivity : 0 ≤ 2 * Mscale N)
  have hden_pos : 0 < r + 1 := by positivity
  have hden_le : r + 1 ≤ 2 * M + 1 := by linarith
  have htwoM1_pos : 0 < 2 * M + 1 := by positivity
  have hMll : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hMZ : M * Zscale N = Real.log (N : ℝ) := by
    dsimp [M]
    exact Mscale_mul_Zscale_eq_log hNlarge
  have hlog_eq : Real.log (N : ℝ) = M ^ 2 * Y := by
    rw [← hMZ, ← hMll]
    ring
  have hdiv_ge :
      M ^ 2 * Y / (2 * M + 1) ≤ Real.log (N : ℝ) / (r + 1) := by
    rw [hlog_eq]
    exact div_le_div_of_nonneg_left (by positivity) hden_pos hden_le
  have hgap_eq : lowerPathLogGap N = Y / 2 - s := by
    rw [lowerPathLogGap]
    dsimp [Y, s]
    ring
  have hgap_r_le :
      lowerPathLogGap N * r / 2 ≤ M * (Y / 2 - s) := by
    rw [hgap_eq]
    have hgap0 : 0 ≤ Y / 2 - s := by
      nlinarith [hs_sq]
    nlinarith
  have hcore :
      M * s / 2 + Real.log 2 ≤
        M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s) := by
    have hrewrite :
        M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s) =
          M * s - M * Y / (2 * (2 * M + 1)) := by
      field_simp [htwoM1_pos.ne']
      ring
    rw [hrewrite]
    have hfrac_le_M :
        M * Y / (2 * (2 * M + 1)) ≤ M := by
      have hden2_pos : 0 < 2 * (2 * M + 1) := by positivity
      rw [div_le_iff₀ hden2_pos]
      nlinarith
    have hlog_two_le_one : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have hM_ge_one : 1 ≤ M := by
      have hY_ge_one : (1 : ℝ) ≤ Y := by linarith
      exact hY_ge_one.trans hY_le_M
    have hMs_big : M + M * s / 2 + 1 ≤ M * s := by
      nlinarith
    nlinarith
  rw [lowerPathLogScale_zero_eq]
  dsimp [M, Y, s, r] at hcore hdiv_ge hgap_r_le ⊢
  nlinarith

lemma Mscale_mul_sqrt_loglog_eq_exp_half_loglog {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ)) :
    Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) =
      Real.exp (Real.log (Real.log (N : ℝ)) / 2) := by
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hleft_nonneg :
      0 ≤ Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
    exact mul_nonneg (Mscale_nonneg N) (Real.sqrt_nonneg _)
  have hright_nonneg : 0 ≤ Real.exp (Y / 2) := (Real.exp_pos _).le
  have hsq_left :
      (Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 =
        Real.log (N : ℝ) := by
    have hMll := Mscale_mul_loglog_eq_Zscale hNlarge
    have hMZ := Mscale_mul_Zscale_eq_log hNlarge
    have hsqrt_sq :
        Real.sqrt (Real.log (Real.log (N : ℝ))) ^ 2 =
          Real.log (Real.log (N : ℝ)) :=
      Real.sq_sqrt (by simpa [Y] using hY_nonneg)
    calc
      (Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2
          = Mscale N ^ 2 * Real.log (Real.log (N : ℝ)) := by
              rw [mul_pow, hsqrt_sq]
      _ = Mscale N * (Mscale N * Real.log (Real.log (N : ℝ))) := by ring
      _ = Mscale N * Zscale N := by rw [hMll]
      _ = Real.log (N : ℝ) := hMZ
  have hsq_right :
      (Real.exp (Y / 2)) ^ 2 = Real.log (N : ℝ) := by
    calc
      (Real.exp (Y / 2)) ^ 2 = Real.exp Y := by
        rw [sq, ← Real.exp_add]
        ring_nf
      _ = Real.log (N : ℝ) := by
        dsimp [Y]
        rw [Real.exp_log hlog_pos]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (hsq_left.trans hsq_right.symm) |>.elim
    (fun h => h)
    (fun h => by nlinarith)

lemma eventually_lowerPath_adjacent_ratio_le_logscale_zero (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.exp (lowerPathLogGap N) ≤
        lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := by
  let A : ℝ := max (2 * |C|) 1
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      tendsto_sqrt_loglog_nat_atTop.eventually_ge_atTop (Real.log A),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 16,
      eventually_loglog_le_Mscale] with N hNlarge_nat hs hloglog hloglog_le_M
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC_le_A_half : C ≤ A / 2 := by
    have h : 2 * C ≤ 2 * |C| := by nlinarith [le_abs_self C]
    have hA : 2 * |C| ≤ A := le_max_left _ _
    linarith
  have hA_le_exp_s : A ≤ Real.exp s := by
    exact (Real.log_le_iff_le_exp hA_pos).1 (by simpa [s, Y] using hs)
  have hCexp_neg_le_half : C * Real.exp (-s) ≤ 1 / 2 := by
    have hC_le_exp_half : C ≤ Real.exp s / 2 := hC_le_A_half.trans (by linarith)
    have hexp_pos : 0 < Real.exp s := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right hC_le_exp_half (Real.exp_pos (-s)).le
    have hcancel : Real.exp s / 2 * Real.exp (-s) = (1 : ℝ) / 2 := by
      rw [div_mul_eq_mul_div, ← Real.exp_add]
      simp
    linarith
  have hMs_eq := Mscale_mul_sqrt_loglog_eq_exp_half_loglog hNlarge
  have hscale_lower :=
    lowerPathLogScale_zero_ge_half_M_mul_sqrt_loglog hNlarge hloglog hloglog_le_M
  have hgap_eq :
      lowerPathLogGap N = Y / 2 - s := by
    rw [lowerPathLogGap]
    dsimp [Y, s]
    ring
  have htarget :
      C * Real.exp (lowerPathLogGap N) ≤
        Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) / 2 := by
    rw [hgap_eq]
    calc
      C * Real.exp (Y / 2 - s)
          = C * Real.exp (-s) * Real.exp (Y / 2) := by
              rw [show Y / 2 - s = -s + Y / 2 by ring, Real.exp_add]
              ring
      _ ≤ (1 / 2) * Real.exp (Y / 2) := by
              exact mul_le_mul_of_nonneg_right hCexp_neg_le_half (Real.exp_pos _).le
      _ = Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) / 2 := by
              rw [hMs_eq]
              simp [Y]
              ring
  exact htarget.trans hscale_lower

lemma eventually_lowerPathY_zero_ge_one :
    ∀ᶠ N : ℕ in atTop, 1 ≤ lowerPathY N ⟨0, Nat.succ_pos _⟩ := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 16,
      eventually_loglog_le_Mscale] with N hNlarge_nat hloglog hloglog_le_M
  rw [lowerPathY, Real.one_le_exp_iff]
  exact lowerPathLogScale_zero_nonneg_of_loglog_le_Mscale
    (lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat))
    hloglog hloglog_le_M

lemma eventually_lowerPathLogScale_zero_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      A ≤ lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := by
  by_cases hA : A ≤ 0
  · filter_upwards [eventually_lowerPathY_zero_ge_one] with N hY
    rw [lowerPathY, Real.one_le_exp_iff] at hY
    exact hA.trans hY
  · have hApos : 0 < A := lt_of_not_ge hA
    filter_upwards [eventually_lowerPath_adjacent_ratio_le_logscale_zero A,
        eventually_lowerPathLogGap_gt_log_two] with N hscale hgap
    have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
      exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
    have hexp_ge_one : 1 ≤ Real.exp (lowerPathLogGap N) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 hgap_nonneg
    calc
      A ≤ A * Real.exp (lowerPathLogGap N) := by
            exact le_mul_of_one_le_right hApos.le hexp_ge_one
      _ ≤ lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := hscale

lemma eventually_lowerPathY_zero_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ lowerPathY N ⟨0, Nat.succ_pos _⟩ := by
  by_cases hA : 0 < A
  · filter_upwards [eventually_lowerPathLogScale_zero_ge (Real.log A)] with N hscale
    rw [lowerPathY]
    exact (Real.log_le_iff_le_exp hA).1 hscale
  · exact Filter.Eventually.of_forall fun N =>
      (le_of_not_gt hA).trans (Real.exp_pos _).le

lemma eventually_lowerPathLogScale_le_Zscale :
    ∀ᶠ N : ℕ in atTop,
      ∀ i : lowerPathIndex N, lowerPathLogScale N i ≤ Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 4] with N hNlarge_nat hloglog_ge i
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set r : ℝ := (lowerPathR N : ℝ)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hY_ge : 4 ≤ Y := by
    simpa [Y] using hloglog_ge
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hM_nonneg : 0 ≤ M := hM_pos.le
  have hZ_pos : 0 < Zscale N := by
    rw [← Mscale_mul_loglog_eq_Zscale hNlarge]
    simpa [M, Y] using mul_pos hM_pos hY_pos
  have hMZ : M * Zscale N = Real.log (N : ℝ) := by
    dsimp [M]
    exact Mscale_mul_Zscale_eq_log hNlarge
  have hMY : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hr_le : r ≤ 2 * M := by
    dsimp [r, M]
    exact Nat.floor_le (by positivity : 0 ≤ 2 * Mscale N)
  have hr_plus_gt : 2 * M < r + 1 := by
    have hlt := Nat.lt_floor_add_one (2 * Mscale N)
    dsimp [r, M]
    exact_mod_cast hlt
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hden_pos : 0 < r + 1 := by positivity
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    have htmp : 0 ≤ (1 / 2 : ℝ) * Y - Real.sqrt Y := by
      have hsqrt_sq := Real.sq_sqrt hY_nonneg
      nlinarith [Real.sqrt_nonneg Y, hY_ge]
    simpa [lowerPathLogGap, Y] using htmp
  have hgap_le : lowerPathLogGap N ≤ Y / 2 := by
    have htmp : (1 / 2 : ℝ) * Y - Real.sqrt Y ≤ Y / 2 := by
      nlinarith [Real.sqrt_nonneg Y]
    simpa [lowerPathLogGap, Y] using htmp
  have hdiv_le : Real.log (N : ℝ) / (r + 1) ≤ Zscale N / 2 := by
    rw [← hMZ]
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hgap_r_le : lowerPathLogGap N * r / 2 ≤ Zscale N / 2 := by
    nlinarith
  have hidx_le : (i.1 : ℝ) ≤ r := by
    dsimp [r]
    exact_mod_cast Nat.le_of_lt_succ i.2
  have hscale_eq :
      lowerPathLogScale N i =
        Real.log (N : ℝ) / (r + 1) - Real.log 2 -
          lowerPathLogGap N * r / 2 +
          (i.1 : ℝ) * lowerPathLogGap N := by
    rw [lowerPathLogScale, lowerPathLogBase]
    dsimp [r]
    field_simp [show r + 1 ≠ 0 by positivity]
  have htail :
      -lowerPathLogGap N * r / 2 + (i.1 : ℝ) * lowerPathLogGap N
        ≤ lowerPathLogGap N * r / 2 := by
    nlinarith
  have hlog_two_nonneg : 0 ≤ Real.log 2 :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  rw [hscale_eq]
  nlinarith

lemma lowerPathLogScale_zero_le_two_M_mul_sqrt_loglog {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ))
    (hloglog_ge : 16 ≤ Real.log (Real.log (N : ℝ)))
    (hloglog_le_M : Real.log (Real.log (N : ℝ)) ≤ Mscale N) :
    lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ ≤
      2 * Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  set r : ℝ := (lowerPathR N : ℝ)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg Y
  have hs_sq : s ^ 2 = Y := by
    dsimp [s]
    exact Real.sq_sqrt hY_nonneg
  have hY_ge : 16 ≤ Y := by
    simpa [Y] using hloglog_ge
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hY_pos
  have hs_ge_four : 4 ≤ s := by
    refine (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 4) hY_nonneg).2 ?_
    norm_num
    exact hY_ge
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hM_nonneg : 0 ≤ M := hM_pos.le
  have hY_le_M : Y ≤ M := by
    simpa [Y, M] using hloglog_le_M
  have hs_le_M : s ≤ M := by
    have hM_ge_one : 1 ≤ M := by nlinarith
    have hs_sq_le_M_sq : s ^ 2 ≤ M ^ 2 := by
      rw [hs_sq]
      nlinarith
    exact (sq_le_sq₀ hs_nonneg hM_nonneg).1 hs_sq_le_M_sq
  have hMZ : M * Zscale N = Real.log (N : ℝ) := by
    dsimp [M]
    exact Mscale_mul_Zscale_eq_log hNlarge
  have hMY : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hlog_eq : Real.log (N : ℝ) = M ^ 2 * Y := by
    rw [← hMZ, ← hMY]
    ring
  have hr_plus_gt : 2 * M < r + 1 := by
    have hlt := Nat.lt_floor_add_one (2 * Mscale N)
    dsimp [r, M] at hlt ⊢
    exact_mod_cast hlt
  have hr_lower : 2 * M - 1 ≤ r := by linarith
  have hden_pos : 0 < r + 1 := by positivity
  have hgap_eq : lowerPathLogGap N = Y / 2 - s := by
    rw [lowerPathLogGap]
    dsimp [Y, s]
    ring
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    rw [hgap_eq]
    nlinarith [hs_sq, hs_ge_four]
  have hscale_eq :
      lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ =
        Real.log (N : ℝ) / (r + 1) - Real.log 2 -
          lowerPathLogGap N * r / 2 := by
    exact lowerPathLogScale_zero_eq N
  have hdiv_le : Real.log (N : ℝ) / (r + 1) ≤ M * Y / 2 := by
    rw [hlog_eq]
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hsub_le :
      -(Y / 2 - s) * r / 2 ≤ -(Y / 2 - s) * (2 * M - 1) / 2 := by
    have hgap0 : 0 ≤ Y / 2 - s := by
      simpa [hgap_eq] using hgap_nonneg
    nlinarith
  rw [hscale_eq, hgap_eq]
  have hlog_two_nonneg : 0 ≤ Real.log 2 :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  calc
    Real.log (N : ℝ) / (r + 1) - Real.log 2 - (Y / 2 - s) * r / 2
        ≤ M * Y / 2 - (Y / 2 - s) * (2 * M - 1) / 2 := by
          nlinarith
    _ = M * s + Y / 4 - s / 2 := by ring
    _ ≤ 2 * M * s := by
          nlinarith

lemma eventually_lowerPathLogScale_zero_le_mul_Zscale
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ ≤ δ * Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      tendsto_sqrt_loglog_nat_atTop.eventually_ge_atTop (2 / δ),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 16,
      eventually_loglog_le_Mscale] with N hNlarge_nat hs hloglog hloglog_le_M
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  have hY_pos : 0 < Y := by
    dsimp [Y]
    have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
    exact Real.log_pos ((Real.lt_log_iff_exp_lt hNpos).2 hNlarge)
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hY_pos
  have hMY : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hs_sq : s ^ 2 = Y := by
    dsimp [s]
    exact Real.sq_sqrt hY_pos.le
  have hroot :=
    lowerPathLogScale_zero_le_two_M_mul_sqrt_loglog hNlarge hloglog hloglog_le_M
  have htwo_le : 2 ≤ δ * s := by
    have hs' : 2 / δ ≤ s := by simpa [s, Y] using hs
    have htmp : 2 ≤ s * δ := (div_le_iff₀ hδ).1 hs'
    nlinarith
  have hmain : 2 * M * s ≤ δ * (M * Y) := by
    have htwo_mul_s : 2 * s ≤ δ * Y := by
      calc
        2 * s ≤ (δ * s) * s := mul_le_mul_of_nonneg_right htwo_le hs_pos.le
        _ = δ * Y := by rw [← hs_sq]; ring
    have hmul := mul_le_mul_of_nonneg_left htwo_mul_s hM_pos.le
    nlinarith
  calc
    lowerPathLogScale N ⟨0, Nat.succ_pos _⟩
        ≤ 2 * M * s := hroot
    _ ≤ δ * (M * Y) := hmain
    _ = δ * Zscale N := by rw [hMY]

lemma eventually_Zscale_ge_const_path (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ Zscale N := by
  let B : ℝ := max A 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
  have hBnonneg : 0 ≤ B := hBpos.le
  filter_upwards [eventually_Mscale_ge 1 zero_lt_one,
      eventually_sqrt_loglog_ge (Real.sqrt B),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hM hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsq :
      (Real.sqrt B) ^ 2 ≤
        (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg B) hsqrt 2
  have hloglog_ge_B : B ≤ Real.log (Real.log (N : ℝ)) := by
    simpa [Real.sq_sqrt hBnonneg, Real.sq_sqrt hloglog_nonneg] using hsq
  have hZ := Mscale_mul_loglog_eq_Zscale hNlarge
  have hB_le_Z : B ≤ Zscale N := by
    rw [← hZ]
    nlinarith [hM, hloglog_ge_B, hBpos.le]
  exact (le_max_left A 1).trans hB_le_Z

lemma eventually_log_loglog_le_mul_loglog
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (Real.log (N : ℝ))) ≤
        δ * Real.log (Real.log (N : ℝ)) := by
  have hsmall :
      (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ)))) =o[atTop]
        fun N : ℕ => Real.log (Real.log (N : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_loglog_nat_atTop
  filter_upwards [isLittleO_iff.mp hsmall hδ,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 1] with N hsmallN hYge_one
  have hYpos : 0 < Real.log (Real.log (N : ℝ)) := zero_lt_one.trans_le hYge_one
  have hlogY_nonneg : 0 ≤ Real.log (Real.log (Real.log (N : ℝ))) :=
    Real.log_nonneg hYge_one
  have hleft_norm :
      ‖Real.log (Real.log (Real.log (N : ℝ)))‖ =
        Real.log (Real.log (Real.log (N : ℝ))) := by
    rw [Real.norm_of_nonneg hlogY_nonneg]
  have hright_norm :
      ‖Real.log (Real.log (N : ℝ))‖ =
        Real.log (Real.log (N : ℝ)) := by
    rw [Real.norm_of_nonneg hYpos.le]
  simpa [hleft_norm, hright_norm] using hsmallN

lemma eventually_log_const_mul_sqrt_loglog_le_mul_loglog
    (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (A * Real.sqrt (Real.log (Real.log (N : ℝ)))) ≤
        δ * Real.log (Real.log (N : ℝ)) := by
  let C : ℝ := max (2 * Real.log A / δ) 1
  have hδ2 : 0 < δ / 2 := by positivity
  filter_upwards [tendsto_loglog_nat_atTop.eventually_ge_atTop C,
      eventually_log_loglog_le_mul_loglog (δ / 2) hδ2] with N hYgeC hlogY
  set Y := Real.log (Real.log (N : ℝ))
  have hC_ge_main : 2 * Real.log A / δ ≤ C := le_max_left _ _
  have hY_ge_main : 2 * Real.log A / δ ≤ Y := hC_ge_main.trans hYgeC
  have hY_ge_one : 1 ≤ Y := (le_max_right _ _).trans hYgeC
  have hY_pos : 0 < Y := zero_lt_one.trans_le hY_ge_one
  have hsqrt_pos : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY_pos
  have hconst : Real.log A ≤ (δ / 2) * Y := by
    have hmul := mul_le_mul_of_nonneg_right hY_ge_main hδ2.le
    field_simp [hδ.ne'] at hmul
    linarith
  have hlogsqrt : Real.log (Real.sqrt Y) = Real.log Y / 2 :=
    Real.log_sqrt hY_pos.le
  calc
    Real.log (A * Real.sqrt Y)
        = Real.log A + Real.log (Real.sqrt Y) := by
            rw [Real.log_mul hA.ne' hsqrt_pos.ne']
    _ = Real.log A + Real.log Y / 2 := by rw [hlogsqrt]
    _ ≤ (δ / 2) * Y + (δ / 2) * Y / 2 := by
            have hhalf : Real.log Y / 2 ≤ ((δ / 2) * Y) / 2 := by
              exact div_le_div_of_nonneg_right hlogY (by norm_num)
            nlinarith
    _ ≤ δ * Y := by nlinarith

lemma Zscale_eq_exp_half_loglog_mul_sqrt_loglog {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ)) :
    Zscale N =
      Real.exp (Real.log (Real.log (N : ℝ)) / 2) *
        Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  set Y := Real.log (Real.log (N : ℝ))
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_eq : Real.log (N : ℝ) = Real.exp Y := by
    dsimp [Y]
    rw [Real.exp_log hlog_pos]
  have hsqrt_log :
      Real.sqrt (Real.log (N : ℝ)) = Real.exp (Y / 2) := by
    rw [hlog_eq, ← Real.exp_half]
  rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge, hsqrt_log]

lemma eventually_log_eight_mul_Zscale_le
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (8 * Zscale N) ≤
        ((1 + δ) / 2) * Real.log (Real.log (N : ℝ)) := by
  have hδ2 : 0 < δ / 2 := by positivity
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_log_const_mul_sqrt_loglog_le_mul_loglog 8 (δ / 2)
        (by norm_num) hδ2,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 1] with
    N hNlarge_nat hlog_extra hYge_one
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set Y := Real.log (Real.log (N : ℝ))
  have hY_pos : 0 < Y := zero_lt_one.trans_le (by simpa [Y] using hYge_one)
  have hsqrt_pos : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY_pos
  have hZeq := Zscale_eq_exp_half_loglog_mul_sqrt_loglog hNlarge
  calc
    Real.log (8 * Zscale N)
        = Real.log (Real.exp (Y / 2) * (8 * Real.sqrt Y)) := by
            congr 1
            rw [hZeq]
            ring
    _ = Y / 2 + Real.log (8 * Real.sqrt Y) := by
            rw [Real.log_mul (Real.exp_ne_zero _) (mul_pos (by norm_num) hsqrt_pos).ne',
              Real.log_exp]
    _ ≤ Y / 2 + (δ / 2) * Y := by
            have hlog_extraY :
                Real.log (8 * Real.sqrt Y) ≤ (δ / 2) * Y := by
              simpa [Y] using hlog_extra
            nlinarith
    _ = ((1 + δ) / 2) * Y := by ring

lemma eventually_lowerPathR_mul_log_eightZ_le_mul_Zscale
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (lowerPathR N : ℝ) * Real.log (8 * Zscale N) ≤
        (1 + δ) * Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_log_eight_mul_Zscale_le δ hδ,
      eventually_Zscale_ge_const_path (1 / 8)] with N hNlarge_nat hlog_le hZge
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Mscale_nonneg N
  have hY_nonneg : 0 ≤ Y := by
    have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
    have hlog_gt_one : 1 < Real.log (N : ℝ) :=
      (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
    exact (Real.log_pos hlog_gt_one).le
  have hMY : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hr_le : (lowerPathR N : ℝ) ≤ 2 * M := by
    dsimp [lowerPathR, M]
    exact Nat.floor_le (by positivity : 0 ≤ 2 * Mscale N)
  have hbase_ge_one : 1 ≤ 8 * Zscale N := by nlinarith
  have hlog_nonneg : 0 ≤ Real.log (8 * Zscale N) :=
    Real.log_nonneg hbase_ge_one
  calc
    (lowerPathR N : ℝ) * Real.log (8 * Zscale N)
        ≤ (2 * M) * Real.log (8 * Zscale N) := by
            exact mul_le_mul_of_nonneg_right hr_le hlog_nonneg
    _ ≤ (2 * M) * (((1 + δ) / 2) * Y) := by
            exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
    _ = (1 + δ) * (M * Y) := by ring
    _ = (1 + δ) * Zscale N := by rw [hMY]

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFV/LowerPathConstruction.lean
    ============================================================= -/

/-
Erdos Problem 202 -- BFV lower construction, source-aligned rooted path family.

This file builds on `LowerPathScales.lean` and defines the finite objects for
the BFV-compatible lower-bound refactor.  It is intentionally not wired into
`LowerBoundInput.lean` yet: the live lower theorem still uses
`LowerConstruction.lean`.  The point here is to grow a fully proved replacement
around the corrected path scales.
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Path choices and moduli -/

/-- Root block index for the source-aligned path construction. -/
def lowerPathZeroIndex (N : ℕ) : lowerPathIndex N :=
  ⟨0, Nat.succ_pos _⟩

/-- Non-root path blocks.  The lower family fixes a small common root factor and
varies over these tail blocks. -/
abbrev lowerPathTailIndex (N : ℕ) : Type :=
  {i : lowerPathIndex N // i ≠ lowerPathZeroIndex N}

/-- The `k`th varying path block, i.e. block number `k+1`. -/
noncomputable def lowerPathTailBlock (N : ℕ) (k : Fin (lowerPathR N)) :
    lowerPathTailIndex N :=
  ⟨k.succ, by
    intro h
    have hval := congrArg Fin.val h
    simp [lowerPathZeroIndex, Fin.val_succ] at hval⟩

lemma lowerPathTailBlock_surjective (N : ℕ) :
    Function.Surjective (lowerPathTailBlock N) := by
  intro i
  have hi0 : i.1 ≠ 0 := by
    intro h
    exact i.2 (by simpa [lowerPathZeroIndex] using h)
  refine ⟨i.1.pred hi0, ?_⟩
  apply Subtype.ext
  exact Fin.succ_pred i.1 hi0

lemma lowerPathTailBlock_injective (N : ℕ) :
    Function.Injective (lowerPathTailBlock N) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg (fun x : lowerPathTailIndex N => x.1.1) hij
  simpa [lowerPathTailBlock] using hval

noncomputable def lowerPathTailBlockEquiv (N : ℕ) :
    Fin (lowerPathR N) ≃ lowerPathTailIndex N :=
  Equiv.ofBijective (lowerPathTailBlock N)
    ⟨lowerPathTailBlock_injective N, lowerPathTailBlock_surjective N⟩

lemma lowerPathTailIndex_card (N : ℕ) :
    Fintype.card (lowerPathTailIndex N) = lowerPathR N := by
  exact (Fintype.card_congr (lowerPathTailBlockEquiv N).symm).trans
    (Fintype.card_fin (lowerPathR N))

/-- The `i`th dyadic prime block for the source-aligned path construction. -/
noncomputable def lowerPathPrimeInterval (N : ℕ) (i : lowerPathIndex N) :
    Finset ℕ :=
  dyadicPrimeInterval (lowerPathY N i)

/-- Small shared root factor at the first path scale.

Using `floor Y_0 + 1` keeps this file total.  The later BFV proof only needs a
common factor coprime to every tail prime; primality of the root is not needed
for the CRT construction. -/
noncomputable def lowerPathP0 (N : ℕ) : ℕ :=
  Nat.floor (lowerPathY N (lowerPathZeroIndex N)) + 1

lemma lowerPathP0_pos (N : ℕ) : 0 < lowerPathP0 N := by
  simp [lowerPathP0]

/-- A choice of one prime from every non-root path block. -/
abbrev LowerPathPrimeChoice (N : ℕ) : Type :=
  (i : lowerPathTailIndex N) → {p : ℕ // p ∈ lowerPathPrimeInterval N i.1}

lemma lowerPathTailBlock_ext {N : ℕ} {P P' : LowerPathPrimeChoice N}
    (h : ∀ k : Fin (lowerPathR N),
      P (lowerPathTailBlock N k) = P' (lowerPathTailBlock N k)) :
    P = P' := by
  funext i
  rcases lowerPathTailBlock_surjective N i with ⟨k, rfl⟩
  exact h k

/-- All source-aligned path choices. -/
noncomputable def lowerPathChoices (N : ℕ) :
    Finset (LowerPathPrimeChoice N) :=
  Fintype.piFinset fun i : lowerPathTailIndex N =>
    (lowerPathPrimeInterval N i.1).attach

lemma lowerPathChoices_card (N : ℕ) :
    (lowerPathChoices N).card =
      ∏ i : lowerPathTailIndex N, (lowerPathPrimeInterval N i.1).card := by
  simp [lowerPathChoices, Fintype.card_piFinset]

noncomputable def lowerPathPrimeFloorProduct (η : ℝ) (N : ℕ) : ℕ :=
  ∏ i : lowerPathTailIndex N,
    Nat.floor (((1 - η) * lowerPathY N i.1) /
      Real.log (lowerPathY N i.1))

/-- The `η` value whose coefficient `1 - η` is the Chebyshev dyadic-prime
constant proved in `BFV/Chebyshev.lean`. -/
noncomputable def lowerPathChebEta : ℝ :=
  1 - dyadicPrimeIntervalConstant

lemma lowerPath_one_sub_chebEta :
    1 - lowerPathChebEta = dyadicPrimeIntervalConstant := by
  simp [lowerPathChebEta]

lemma dyadicPrimeIntervalConstant_lt_one :
    dyadicPrimeIntervalConstant < 1 := by
  have hlog4_le : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h
    exact h
  unfold dyadicPrimeIntervalConstant
  nlinarith

lemma lowerPathChebEta_pos : 0 < lowerPathChebEta := by
  unfold lowerPathChebEta
  linarith [dyadicPrimeIntervalConstant_lt_one]

noncomputable def lowerPathDenominatorConstant : ℝ :=
  4 / dyadicPrimeIntervalConstant

lemma lowerPathDenominatorConstant_pos : 0 < lowerPathDenominatorConstant := by
  unfold lowerPathDenominatorConstant
  exact div_pos (by norm_num) dyadicPrimeIntervalConstant_pos

noncomputable def lowerPathRealPrimeProduct (N : ℕ) : ℝ :=
  ∏ i : lowerPathTailIndex N,
    (((dyadicPrimeIntervalConstant * lowerPathY N i.1) /
      Real.log (lowerPathY N i.1)) / 2)

noncomputable def lowerPathRealDenominator (N : ℕ) : ℝ :=
  (2 * lowerPathY N (lowerPathZeroIndex N)) *
    ∏ i : lowerPathTailIndex N,
      lowerPathDenominatorConstant * Real.log (lowerPathY N i.1)

lemma lowerPath_half_le_floor_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  have hx_floor : x < (Nat.floor x : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have hx_half_le_sub : x / 2 ≤ x - 1 := by linarith
  linarith

lemma lowerPath_two_le_half_mul_div_log_of_ge_64 {y : ℝ} (hy : 64 ≤ y) :
    2 ≤ ((1 / 2 : ℝ) * y) / Real.log y := by
  have hy_nonneg : 0 ≤ y := by linarith
  have hy_pos : 0 < y := by linarith
  have hy_gt_one : 1 < y := by linarith
  have hlog_pos : 0 < Real.log y := Real.log_pos hy_gt_one
  have hlog_le : Real.log y ≤ 2 * Real.sqrt y := by
    have h :=
      Real.log_le_rpow_div (x := y) (ε := (1 / 2 : ℝ)) hy_nonneg (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    calc
      Real.log y ≤ Real.sqrt y / (1 / 2 : ℝ) := h
      _ = 2 * Real.sqrt y := by ring
  have hsqrt_ge : 8 ≤ Real.sqrt y := by
    refine (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 8) hy_nonneg).2 ?_
    norm_num
    exact hy
  have hsqrt_sq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy_nonneg
  have hfourlog : 4 * Real.log y ≤ y := by
    nlinarith
  have hden_pos : 0 < 2 * Real.log y := by positivity
  have hmain : 2 ≤ y / (2 * Real.log y) :=
    (le_div_iff₀ hden_pos).2 (by nlinarith [hfourlog])
  calc
    2 ≤ y / (2 * Real.log y) := hmain
    _ = ((1 / 2 : ℝ) * y) / Real.log y := by
          field_simp [hlog_pos.ne']

lemma lowerPath_two_le_cheb_mul_div_log_of_ge {y : ℝ}
    (hy : (4 / dyadicPrimeIntervalConstant) ^ 2 ≤ y) :
    2 ≤ (dyadicPrimeIntervalConstant * y) / Real.log y := by
  have hc : 0 < dyadicPrimeIntervalConstant := dyadicPrimeIntervalConstant_pos
  have hc_lt_one : dyadicPrimeIntervalConstant < 1 :=
    dyadicPrimeIntervalConstant_lt_one
  have hfour_le : (4 : ℝ) ≤ 4 / dyadicPrimeIntervalConstant := by
    rw [le_div_iff₀ hc]
    nlinarith
  have hbase_nonneg : 0 ≤ 4 / dyadicPrimeIntervalConstant := by positivity
  have hy_ge16 : (16 : ℝ) ≤ y := by
    have hsq :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hfour_le 2
    norm_num at hsq
    exact hsq.trans hy
  have hy_nonneg : 0 ≤ y := by linarith
  have hy_gt_one : 1 < y := by linarith
  have hlog_pos : 0 < Real.log y := Real.log_pos hy_gt_one
  have hlog_le : Real.log y ≤ 2 * Real.sqrt y := by
    have h :=
      Real.log_le_rpow_div (x := y) (ε := (1 / 2 : ℝ)) hy_nonneg (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    calc
      Real.log y ≤ Real.sqrt y / (1 / 2 : ℝ) := h
      _ = 2 * Real.sqrt y := by ring
  have hsqrt_ge : 4 / dyadicPrimeIntervalConstant ≤ Real.sqrt y := by
    exact (Real.le_sqrt hbase_nonneg hy_nonneg).2 hy
  have hfour_le_csqrt : 4 ≤ dyadicPrimeIntervalConstant * Real.sqrt y := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt_ge hc.le
    field_simp [hc.ne'] at hmul
    exact hmul
  have hfour_sqrt_le_cy :
      4 * Real.sqrt y ≤ dyadicPrimeIntervalConstant * y := by
    calc
      4 * Real.sqrt y ≤
          (dyadicPrimeIntervalConstant * Real.sqrt y) * Real.sqrt y := by
            exact mul_le_mul_of_nonneg_right hfour_le_csqrt (Real.sqrt_nonneg y)
      _ = dyadicPrimeIntervalConstant * y := by
            rw [mul_assoc, ← sq, Real.sq_sqrt hy_nonneg]
  have htwo_log_le : 2 * Real.log y ≤ dyadicPrimeIntervalConstant * y := by
    calc
      2 * Real.log y ≤ 4 * Real.sqrt y := by nlinarith
      _ ≤ dyadicPrimeIntervalConstant * y := hfour_sqrt_le_cy
  exact (le_div_iff₀ hlog_pos).2 htwo_log_le

theorem lowerPathPrimeFloorProduct_floor_loss_eventually :
    ∀ᶠ N : ℕ in atTop,
      lowerPathRealPrimeProduct N ≤
        (lowerPathPrimeFloorProduct lowerPathChebEta N : ℝ) := by
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge
        ((4 / dyadicPrimeIntervalConstant) ^ 2)] with N hgap hY0
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
  unfold lowerPathPrimeFloorProduct
  unfold lowerPathRealPrimeProduct
  rw [Nat.cast_prod]
  exact Finset.prod_le_prod
    (fun i _hi => by
      have hzero_le_i :
          lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
        lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
      have hY0' :
          (4 / dyadicPrimeIntervalConstant) ^ 2 ≤
            lowerPathY N (lowerPathZeroIndex N) := by
        simpa [lowerPathZeroIndex] using hY0
      have hfactor :
          2 ≤ (dyadicPrimeIntervalConstant * lowerPathY N i.1) /
              Real.log (lowerPathY N i.1) :=
        lowerPath_two_le_cheb_mul_div_log_of_ge (hY0'.trans hzero_le_i)
      positivity)
    (fun i _hi => by
      have hzero_le_i :
          lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
        lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
      have hY0' :
          (4 / dyadicPrimeIntervalConstant) ^ 2 ≤
            lowerPathY N (lowerPathZeroIndex N) := by
        simpa [lowerPathZeroIndex] using hY0
      have hfactor :
          2 ≤ (dyadicPrimeIntervalConstant * lowerPathY N i.1) /
              Real.log (lowerPathY N i.1) :=
        lowerPath_two_le_cheb_mul_div_log_of_ge (hY0'.trans hzero_le_i)
      rw [show ((1 - lowerPathChebEta) * lowerPathY N i.1) /
            Real.log (lowerPathY N i.1) =
          (dyadicPrimeIntervalConstant * lowerPathY N i.1) /
            Real.log (lowerPathY N i.1) by
              rw [lowerPath_one_sub_chebEta]]
      exact lowerPath_half_le_floor_of_two_le hfactor)

lemma lowerPathY_dyadic_tail_product_eq {N : ℕ} (hNpos : 0 < (N : ℝ)) :
    (2 * lowerPathY N (lowerPathZeroIndex N)) *
        (∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1)
      = (N : ℝ) := by
  let g : lowerPathIndex N → ℝ := fun i => (2 : ℝ) * lowerPathY N i
  have hsplit := Fintype.prod_eq_mul_prod_compl (lowerPathZeroIndex N) g
  have htail_prod :
      (∏ i ∈ ({lowerPathZeroIndex N} : Finset (lowerPathIndex N))ᶜ, g i) =
        ∏ i : lowerPathTailIndex N, g i.1 := by
    exact Finset.prod_subtype
      (({lowerPathZeroIndex N} : Finset (lowerPathIndex N))ᶜ)
      (by intro x; simp)
      g
  calc
    (2 * lowerPathY N (lowerPathZeroIndex N)) *
        (∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1)
        = ∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i := by
          simpa [g, htail_prod] using hsplit.symm
    _ = (N : ℝ) := lowerPathY_dyadic_product_eq hNpos

lemma lowerPathRealPrimeProduct_mul_denominator_eq {N : ℕ}
    (hNpos : 0 < (N : ℝ))
    (hlog : ∀ i : lowerPathTailIndex N,
      Real.log (lowerPathY N i.1) ≠ 0) :
    lowerPathRealPrimeProduct N * lowerPathRealDenominator N = (N : ℝ) := by
  have htail :
      lowerPathRealPrimeProduct N *
          (∏ i : lowerPathTailIndex N,
            lowerPathDenominatorConstant * Real.log (lowerPathY N i.1))
        =
          ∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1 := by
    unfold lowerPathRealPrimeProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _hi
    have hlogi := hlog i
    dsimp [lowerPathDenominatorConstant]
    field_simp [hlogi, dyadicPrimeIntervalConstant_pos.ne']
    ring
  calc
      lowerPathRealPrimeProduct N *
        lowerPathRealDenominator N
        = (2 * lowerPathY N (lowerPathZeroIndex N)) *
            (lowerPathRealPrimeProduct N *
              ∏ i : lowerPathTailIndex N,
                lowerPathDenominatorConstant * Real.log (lowerPathY N i.1)) := by
          unfold lowerPathRealDenominator
          ring
    _ = (2 * lowerPathY N (lowerPathZeroIndex N)) *
          ∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1 := by rw [htail]
    _ = (N : ℝ) := lowerPathY_dyadic_tail_product_eq hNpos

lemma lowerPathRealDenominator_pos {N : ℕ}
    (hlog_pos : ∀ i : lowerPathTailIndex N,
      0 < Real.log (lowerPathY N i.1)) :
    0 < lowerPathRealDenominator N := by
  unfold lowerPathRealDenominator
  exact mul_pos
    (mul_pos (by norm_num) (Real.exp_pos _))
    (Finset.prod_pos (fun i _hi =>
      mul_pos lowerPathDenominatorConstant_pos (hlog_pos i)))

theorem lowerPathRealDenominator_le_simple_eventually :
    ∀ᶠ N : ℕ in atTop,
      lowerPathRealDenominator N ≤
        (2 * lowerPathY N (lowerPathZeroIndex N)) *
          (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N := by
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge 64,
      eventually_lowerPathLogScale_le_Zscale,
      eventually_Zscale_pos] with N hgap hY0 hscale_le hZpos
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
  have hlog_nonneg : ∀ i : lowerPathTailIndex N,
      0 ≤ Real.log (lowerPathY N i.1) := by
    intro i
    have hzero_le_i :
        lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
      lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
    have hY0' : (64 : ℝ) ≤ lowerPathY N (lowerPathZeroIndex N) := by
      simpa [lowerPathZeroIndex] using hY0
    exact (Real.log_pos (by linarith [hY0'.trans hzero_le_i])).le
  have hprod :
      (∏ i : lowerPathTailIndex N,
          lowerPathDenominatorConstant * Real.log (lowerPathY N i.1))
        ≤ (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N := by
    calc
      (∏ i : lowerPathTailIndex N,
          lowerPathDenominatorConstant * Real.log (lowerPathY N i.1))
          ≤ ∏ _i : lowerPathTailIndex N,
              lowerPathDenominatorConstant * Zscale N := by
            exact Finset.prod_le_prod
              (fun i _hi => mul_nonneg lowerPathDenominatorConstant_pos.le
                (hlog_nonneg i))
              (fun i _hi => by
                have hlog_eq :
                    Real.log (lowerPathY N i.1) = lowerPathLogScale N i.1 := by
                  rw [lowerPathY, Real.log_exp]
                rw [hlog_eq]
                exact mul_le_mul_of_nonneg_left (hscale_le i.1)
                  lowerPathDenominatorConstant_pos.le)
      _ = (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N := by
            rw [Finset.prod_const]
            have hcard :
                (Finset.univ : Finset (lowerPathTailIndex N)).card = lowerPathR N := by
              exact lowerPathTailIndex_card N
            rw [hcard]
  unfold lowerPathRealDenominator
  exact mul_le_mul_of_nonneg_left hprod (by positivity)

theorem lowerPathPrimeInterval_card_lower_bound_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∀ i : lowerPathTailIndex N,
        Nat.floor (((1 - lowerPathChebEta) * lowerPathY N i.1) /
            Real.log (lowerPathY N i.1)) ≤
          (lowerPathPrimeInterval N i.1).card := by
  rcases eventually_atTop.1
      dyadicPrimeInterval_card_lower_bound with
    ⟨Y, hY⟩
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge Y] with N hgap hY0 i
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
  have hzero_le_i :
      lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
    lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
  have hY0' : Y ≤ lowerPathY N (lowerPathZeroIndex N) := by
    simpa [lowerPathZeroIndex] using hY0
  simpa [lowerPathPrimeInterval, lowerPath_one_sub_chebEta] using
    hY (lowerPathY N i.1) (hY0'.trans hzero_le_i)

theorem lowerPathChoices_card_ge_prime_floor_product_eventually :
    ∀ᶠ N : ℕ in atTop,
      lowerPathPrimeFloorProduct lowerPathChebEta N ≤
        (lowerPathChoices N).card := by
  filter_upwards [lowerPathPrimeInterval_card_lower_bound_eventually] with N hblock
  rw [lowerPathChoices_card]
  unfold lowerPathPrimeFloorProduct
  exact Finset.prod_le_prod
    (fun i _hi => Nat.zero_le _)
    (fun i _hi => hblock i)

/-- The modulus attached to a source-aligned path choice. -/
noncomputable def lowerPathModulus (N : ℕ) (P : LowerPathPrimeChoice N) : ℕ :=
  lowerPathP0 N * ∏ i : lowerPathTailIndex N, (P i).1

/-- The finite source-aligned lower family of moduli. -/
noncomputable def lowerPathQ (N : ℕ) : Finset ℕ :=
  (lowerPathChoices N).image (lowerPathModulus N)

lemma lowerPathModulus_pos (N : ℕ) (P : LowerPathPrimeChoice N) :
    0 < lowerPathModulus N P := by
  unfold lowerPathModulus
  exact mul_pos (lowerPathP0_pos N) (Finset.prod_pos (fun i _hi => by
    have hp : Nat.Prime (P i).1 := (mem_dyadicPrimeInterval.1 (P i).2).2.2
    exact hp.pos))

lemma lowerPathRootFactor_le_two_mul_lowerPathY {N : ℕ}
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N)) :
    (lowerPathP0 N : ℝ) ≤ 2 * lowerPathY N (lowerPathZeroIndex N) := by
  have hY0_nonneg : 0 ≤ lowerPathY N (lowerPathZeroIndex N) := (Real.exp_pos _).le
  have hfloor :
      ((Nat.floor (lowerPathY N (lowerPathZeroIndex N)) : ℕ) : ℝ) ≤
        lowerPathY N (lowerPathZeroIndex N) :=
    Nat.floor_le hY0_nonneg
  rw [lowerPathP0]
  norm_num
  linarith

/-- If the small root scale is at least `1`, every source-aligned path modulus
lies in `[1, N]`. -/
lemma lowerPathModulus_le_N_of_root_scale {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N)) (P : LowerPathPrimeChoice N) :
    lowerPathModulus N P ≤ N := by
  classical
  have hroot := lowerPathRootFactor_le_two_mul_lowerPathY (N := N) hY0
  have htail :
      ((∏ i : lowerPathTailIndex N, (P i).1 : ℕ) : ℝ) ≤
        ∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1 := by
    rw [Nat.cast_prod]
    exact Finset.prod_le_prod
      (fun i _hi => by positivity)
      (fun i _hi => by
        have hmem : (P i).1 ∈ lowerPathPrimeInterval N i.1 := (P i).2
        have hle_nat : (P i).1 ≤ Nat.floor (2 * lowerPathY N i.1) :=
          (mem_dyadicPrimeInterval.1 hmem).2.1
        have hnonneg : 0 ≤ 2 * lowerPathY N i.1 := by
          exact mul_nonneg (by norm_num) (Real.exp_pos _).le
        exact le_trans (by exact_mod_cast hle_nat)
          (Nat.floor_le hnonneg))
  have hprod_split :
      (2 : ℝ) * lowerPathY N (lowerPathZeroIndex N) *
          (∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1)
        =
      ∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i := by
    let f : lowerPathIndex N → ℝ := fun i => (2 : ℝ) * lowerPathY N i
    have hsplit := Fintype.prod_eq_mul_prod_compl (lowerPathZeroIndex N) f
    have htail_prod :
        (∏ i ∈ ({lowerPathZeroIndex N} : Finset (lowerPathIndex N))ᶜ, f i) =
          ∏ i : lowerPathTailIndex N, f i.1 := by
      exact Finset.prod_subtype
        (({lowerPathZeroIndex N} : Finset (lowerPathIndex N))ᶜ)
        (by intro x; simp)
        f
    simpa [f, htail_prod] using hsplit.symm
  have hreal :
      (lowerPathModulus N P : ℝ) ≤ (N : ℝ) := by
    rw [lowerPathModulus, Nat.cast_mul]
    calc
      (lowerPathP0 N : ℝ) * ((∏ i : lowerPathTailIndex N, (P i).1 : ℕ) : ℝ)
          ≤ (2 * lowerPathY N (lowerPathZeroIndex N)) *
              (∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1) := by
            exact mul_le_mul hroot htail (by positivity) (by positivity)
      _ = ∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i := hprod_split
      _ = (N : ℝ) := lowerPathY_dyadic_product_eq hNpos
  exact_mod_cast hreal

lemma lowerPathQ_moduli_in_range_of_root_scale {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N)) :
    ∀ q ∈ lowerPathQ N, 1 ≤ q ∧ q ≤ N := by
  intro q hq
  rcases Finset.mem_image.1 hq with ⟨P, _hP, rfl⟩
  exact ⟨lowerPathModulus_pos N P, lowerPathModulus_le_N_of_root_scale hNpos hY0 P⟩

theorem lowerPathQ_moduli_in_range_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∀ q ∈ lowerPathQ N, 1 ≤ q ∧ q ≤ N := by
  filter_upwards [Filter.eventually_gt_atTop 0,
      eventually_lowerPathY_zero_ge_one] with N hNpos_nat hY0
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
  exact lowerPathQ_moduli_in_range_of_root_scale hNpos hY0

/-! ## Eventual separation and root coprimality -/

/-- The source-aligned path prime blocks are eventually pairwise disjoint. -/
theorem lowerPathPrimeIntervals_pairwise_disjoint :
    ∀ᶠ N : ℕ in atTop,
      ∀ i j : lowerPathIndex N, i ≠ j →
        Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j) := by
  filter_upwards [eventually_lowerPathLogGap_gt_log_two] with N hgap
  intro i j hij
  have hijval : i.1 ≠ j.1 := by
    intro h
    exact hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hijval with hlt | hgt
  · have hsep : 2 * lowerPathY N i < lowerPathY N j :=
      lowerPathY_dyadic_lt_of_lt_index hgap hlt
    have hfloor : Nat.floor (2 * lowerPathY N i) ≤ Nat.floor (lowerPathY N j) :=
      Nat.floor_mono hsep.le
    have hIoc :
        Disjoint
          (Finset.Ioc (Nat.floor (lowerPathY N i))
            (Nat.floor (2 * lowerPathY N i)))
          (Finset.Ioc (Nat.floor (lowerPathY N j))
            (Nat.floor (2 * lowerPathY N j))) :=
      Finset.Ioc_disjoint_Ioc_of_le hfloor
    simpa [lowerPathPrimeInterval, dyadicPrimeInterval] using
      (Finset.disjoint_filter_filter (p := Nat.Prime) (q := Nat.Prime) hIoc)
  · have hsep : 2 * lowerPathY N j < lowerPathY N i :=
      lowerPathY_dyadic_lt_of_lt_index hgap hgt
    have hfloor : Nat.floor (2 * lowerPathY N j) ≤ Nat.floor (lowerPathY N i) :=
      Nat.floor_mono hsep.le
    have hIoc :
        Disjoint
          (Finset.Ioc (Nat.floor (lowerPathY N j))
            (Nat.floor (2 * lowerPathY N j)))
          (Finset.Ioc (Nat.floor (lowerPathY N i))
            (Nat.floor (2 * lowerPathY N i))) :=
      Finset.Ioc_disjoint_Ioc_of_le hfloor
    simpa [lowerPathPrimeInterval, dyadicPrimeInterval, disjoint_comm] using
      (Finset.disjoint_filter_filter (p := Nat.Prime) (q := Nat.Prime) hIoc)

lemma lowerPathDyadicPrimeInterval_card_le_primeCounting (y : ℝ) :
    (dyadicPrimeInterval y).card ≤ Nat.primeCounting (Nat.floor (2 * y)) := by
  classical
  have hsub :
      dyadicPrimeInterval y ⊆
        (Finset.range (Nat.floor (2 * y) + 1)).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range]
    have hp' := mem_dyadicPrimeInterval.1 hp
    exact ⟨Nat.lt_succ_of_le hp'.2.1, hp'.2.2⟩
  have hcard := Finset.card_le_card hsub
  simpa [Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range] using hcard

lemma lowerPathPrimeInterval_adjacent_card_le_floor_prev_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∀ i j : lowerPathIndex N, j.1 = i.1 + 1 →
        (lowerPathPrimeInterval N j).card ≤ Nat.floor (lowerPathY N i) := by
  classical
  let B : ℝ := (Real.log 4 + 1) * 2
  have hBpos : 0 < B := by
    dsimp [B]
    have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    positivity
  rcases eventually_atTop.1
      (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one) with
    ⟨X, hcheb⟩
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPath_adjacent_ratio_le_logscale_zero B,
      eventually_lowerPath_adjacent_ratio_le_logscale_zero (Real.log (max X 1))] with
    N hgap_gt hratioB hratioX
  intro i j hij
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    have hlog_two_nonneg : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    exact hlog_two_nonneg.trans hgap_gt.le
  have hexpgap_ge_one : 1 ≤ Real.exp (lowerPathLogGap N) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 hgap_nonneg
  have hzero_le_j_scale :
      lowerPathLogScale N (lowerPathZeroIndex N) ≤ lowerPathLogScale N j :=
    lowerPathLogScale_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
  have hzero_le_j :
      lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N j :=
    lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
  have hYj_eq :
      lowerPathY N j = lowerPathY N i * Real.exp (lowerPathLogGap N) :=
    lowerPathY_adjacent_eq_mul_exp_gap hij
  have hlog_max_nonneg : 0 ≤ Real.log (max X 1) :=
    Real.log_nonneg (le_max_right X 1)
  have hlogmax_le_scale0 :
      Real.log (max X 1) ≤ lowerPathLogScale N (lowerPathZeroIndex N) := by
    calc
      Real.log (max X 1)
          ≤ Real.log (max X 1) * Real.exp (lowerPathLogGap N) := by
            exact le_mul_of_one_le_right hlog_max_nonneg hexpgap_ge_one
      _ ≤ lowerPathLogScale N (lowerPathZeroIndex N) := hratioX
  have hmax_pos : 0 < max X 1 :=
    lt_of_lt_of_le zero_lt_one (le_max_right X 1)
  have hmax_le_Y0 : max X 1 ≤ lowerPathY N (lowerPathZeroIndex N) := by
    rw [lowerPathY]
    exact (Real.log_le_iff_le_exp hmax_pos).1 hlogmax_le_scale0
  have hX_le_arg : X ≤ 2 * lowerPathY N j := by
    have hX_le_j : X ≤ lowerPathY N j :=
      (le_max_left X 1).trans (hmax_le_Y0.trans hzero_le_j)
    have hj_nonneg : 0 ≤ lowerPathY N j := (Real.exp_pos _).le
    nlinarith
  have hcheb_arg := hcheb (2 * lowerPathY N j) hX_le_arg
  have hcard_pc :
      ((lowerPathPrimeInterval N j).card : ℝ) ≤
        (Nat.primeCounting (Nat.floor (2 * lowerPathY N j)) : ℝ) := by
    exact_mod_cast lowerPathDyadicPrimeInterval_card_le_primeCounting (lowerPathY N j)
  have hlog_arg_eq :
      Real.log (2 * lowerPathY N j) =
        Real.log 2 + lowerPathLogScale N j := by
    rw [lowerPathY, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp]
  have hlog_arg_ge_Bexp :
      B * Real.exp (lowerPathLogGap N) ≤ Real.log (2 * lowerPathY N j) := by
    calc
      B * Real.exp (lowerPathLogGap N)
          ≤ lowerPathLogScale N (lowerPathZeroIndex N) := hratioB
      _ ≤ lowerPathLogScale N j := hzero_le_j_scale
      _ ≤ Real.log (2 * lowerPathY N j) := by
            rw [hlog_arg_eq]
            have hlog_two_nonneg : 0 ≤ Real.log 2 :=
              Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
            linarith
  have hlog_arg_pos : 0 < Real.log (2 * lowerPathY N j) :=
    (mul_pos hBpos (Real.exp_pos _)).trans_le hlog_arg_ge_Bexp
  have hnum_eq :
      (Real.log 4 + 1) * (2 * lowerPathY N j) =
        (B * Real.exp (lowerPathLogGap N)) * lowerPathY N i := by
    rw [hYj_eq]
    dsimp [B]
    ring
  have hquot_le :
      (Real.log 4 + 1) * (2 * lowerPathY N j) / Real.log (2 * lowerPathY N j)
        ≤ lowerPathY N i := by
    rw [div_le_iff₀ hlog_arg_pos]
    have hi_nonneg : 0 ≤ lowerPathY N i := (Real.exp_pos _).le
    calc
      (Real.log 4 + 1) * (2 * lowerPathY N j)
          = (B * Real.exp (lowerPathLogGap N)) * lowerPathY N i := hnum_eq
      _ ≤ Real.log (2 * lowerPathY N j) * lowerPathY N i := by
            exact mul_le_mul_of_nonneg_right hlog_arg_ge_Bexp hi_nonneg
      _ = lowerPathY N i * Real.log (2 * lowerPathY N j) := by ring
  have hcard_real : ((lowerPathPrimeInterval N j).card : ℝ) ≤ lowerPathY N i := by
    exact hcard_pc.trans (hcheb_arg.trans hquot_le)
  exact Nat.le_floor hcard_real

/-- Unique factorization plus disjoint source-aligned prime blocks makes the
path modulus map injective. -/
theorem lowerPathModulus_injective_eventually :
    ∀ᶠ N : ℕ in atTop,
      Set.InjOn (lowerPathModulus N)
        (↑(lowerPathChoices N) : Set (LowerPathPrimeChoice N)) := by
  filter_upwards [lowerPathPrimeIntervals_pairwise_disjoint] with N hdisj
  intro P _hP P' _hP' heq
  have htail_eq :
      (∏ i : lowerPathTailIndex N, (P i).1) =
        ∏ i : lowerPathTailIndex N, (P' i).1 := by
    have hp0 : lowerPathP0 N ≠ 0 := (lowerPathP0_pos N).ne'
    exact mul_left_cancel₀ hp0 (by simpa [lowerPathModulus] using heq)
  funext i
  apply Subtype.ext
  let p : ℕ := (P i).1
  have hpPrime : Nat.Prime p := (mem_dyadicPrimeInterval.1 (P i).2).2.2
  have hp_dvd_left : p ∣ ∏ k : lowerPathTailIndex N, (P k).1 := by
    unfold p
    exact Finset.dvd_prod_of_mem
      (fun k : lowerPathTailIndex N => (P k).1) (Finset.mem_univ i)
  have hp_dvd_prod : p ∣ ∏ k : lowerPathTailIndex N, (P' k).1 := by
    rwa [htail_eq] at hp_dvd_left
  rcases (hpPrime.prime.dvd_finset_prod_iff (S := Finset.univ)
      (fun k : lowerPathTailIndex N => (P' k).1)).1 hp_dvd_prod with
    ⟨j, _hj, hp_dvd_pj⟩
  have hpjPrime : Nat.Prime (P' j).1 := (mem_dyadicPrimeInterval.1 (P' j).2).2.2
  have hp_eq_pj : p = (P' j).1 :=
    (Nat.prime_dvd_prime_iff_eq hpPrime hpjPrime).1 hp_dvd_pj
  have hji : j = i := by
    by_contra hne
    have hne' : i.1 ≠ j.1 := by
      intro h
      exact hne (Subtype.ext h.symm)
    have hp_mem_i : p ∈ lowerPathPrimeInterval N i.1 := (P i).2
    have hp_mem_j : p ∈ lowerPathPrimeInterval N j.1 := by
      simp [p, hp_eq_pj, (P' j).2]
    exact Finset.disjoint_left.1 (hdisj i.1 j.1 hne') hp_mem_i hp_mem_j
  subst hji
  simpa [p] using hp_eq_pj

lemma lowerPathQ_card_eq_lowerPathChoices_card_of_injective {N : ℕ}
    (hinj : Set.InjOn (lowerPathModulus N)
      (↑(lowerPathChoices N) : Set (LowerPathPrimeChoice N))) :
    (lowerPathQ N).card = (lowerPathChoices N).card := by
  simpa [lowerPathQ] using Finset.card_image_of_injOn (s := lowerPathChoices N)
    (f := lowerPathModulus N) hinj

theorem lowerPathQ_card_ge_prime_floor_product_eventually :
    ∀ᶠ N : ℕ in atTop,
      lowerPathPrimeFloorProduct lowerPathChebEta N ≤ (lowerPathQ N).card := by
  filter_upwards [lowerPathModulus_injective_eventually,
      lowerPathChoices_card_ge_prime_floor_product_eventually] with
    N hinj hchoices
  rwa [lowerPathQ_card_eq_lowerPathChoices_card_of_injective hinj]

lemma lowerPath_root_coprime_tail_prime {N : ℕ}
    (hgap : Real.log 2 < lowerPathLogGap N)
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N))
    (i : lowerPathTailIndex N) (p : ℕ)
    (hp : p ∈ lowerPathPrimeInterval N i.1) :
    Nat.Coprime (lowerPathP0 N) p := by
  have hroot_le :
      (lowerPathP0 N : ℝ) ≤ 2 * lowerPathY N (lowerPathZeroIndex N) :=
    lowerPathRootFactor_le_two_mul_lowerPathY hY0
  have hi_pos : 0 < i.1.1 := by
    by_contra hnot
    have hzero : i.1.1 = 0 := Nat.eq_zero_of_not_pos hnot
    exact i.2 (Fin.ext hzero)
  have hsep :
      2 * lowerPathY N (lowerPathZeroIndex N) < lowerPathY N i.1 :=
    lowerPathY_dyadic_lt_of_lt_index hgap (by
      simpa [lowerPathZeroIndex] using hi_pos)
  have hp_floor : Nat.floor (lowerPathY N i.1) < p := by
    exact (mem_dyadicPrimeInterval.1 hp).1
  have hy_lt_p : lowerPathY N i.1 < (p : ℝ) := by
    have hy_floor : lowerPathY N i.1 < (Nat.floor (lowerPathY N i.1) : ℝ) + 1 :=
      Nat.lt_floor_add_one (lowerPathY N i.1)
    have hfloor_succ_le : Nat.floor (lowerPathY N i.1) + 1 ≤ p :=
      Nat.succ_le_of_lt hp_floor
    exact hy_floor.trans_le (by exact_mod_cast hfloor_succ_le)
  have hp0_lt_p_real : (lowerPathP0 N : ℝ) < (p : ℝ) :=
    hroot_le.trans_lt (hsep.trans hy_lt_p)
  have hp0_lt_p : lowerPathP0 N < p := by
    exact_mod_cast hp0_lt_p_real
  have hpprime : Nat.Prime p := (mem_dyadicPrimeInterval.1 hp).2.2
  exact (Nat.coprime_of_lt_prime (lowerPathP0_pos N).ne' hp0_lt_p hpprime).symm

theorem lowerPath_root_coprime_tail_prime_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∀ i : lowerPathTailIndex N, ∀ p : ℕ,
        p ∈ lowerPathPrimeInterval N i.1 →
          Nat.Coprime (lowerPathP0 N) p := by
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge_one] with N hgap hY0 i p hp
  exact lowerPath_root_coprime_tail_prime hgap hY0 i p hp

/-! ## CRT modulus skeleton -/

/-- The common root or one selected tail prime, used as a CRT modulus. -/
abbrev lowerPathCRTIndex (N : ℕ) : Type :=
  Option (Fin (lowerPathR N))

/-- CRT modulus attached to a root/tail coordinate. -/
noncomputable def lowerPathCRTModulus (N : ℕ) (P : LowerPathPrimeChoice N) :
    lowerPathCRTIndex N → ℕ
  | none => lowerPathP0 N
  | some k => (P (lowerPathTailBlock N k)).1

lemma lowerPathCRTModulus_ne_zero (N : ℕ) (P : LowerPathPrimeChoice N)
    (i : lowerPathCRTIndex N) :
    lowerPathCRTModulus N P i ≠ 0 := by
  cases i with
  | none => exact (lowerPathP0_pos N).ne'
  | some k =>
      have hp : Nat.Prime (P (lowerPathTailBlock N k)).1 :=
        (mem_dyadicPrimeInterval.1 (P (lowerPathTailBlock N k)).2).2.2
      exact hp.ne_zero

lemma lowerPathCRTModulus_dvd_lowerPathModulus (N : ℕ) (P : LowerPathPrimeChoice N)
    (i : lowerPathCRTIndex N) :
    lowerPathCRTModulus N P i ∣ lowerPathModulus N P := by
  cases i with
  | none =>
      rw [lowerPathCRTModulus, lowerPathModulus]
      exact dvd_mul_right _ _
  | some k =>
      rw [lowerPathCRTModulus, lowerPathModulus]
      exact dvd_mul_of_dvd_right
        (Finset.dvd_prod_of_mem (fun i : lowerPathTailIndex N => (P i).1)
          (Finset.mem_univ (lowerPathTailBlock N k)))
        (lowerPathP0 N)

lemma lowerPathCRTModuli_pairwise_coprime {N : ℕ}
    (P : LowerPathPrimeChoice N)
    (hroot : ∀ i : lowerPathTailIndex N, Nat.Coprime (lowerPathP0 N) (P i).1)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j)) :
    Set.Pairwise (↑(Finset.univ : Finset (lowerPathCRTIndex N)) :
      Set (lowerPathCRTIndex N))
      (fun i j => Nat.Coprime (lowerPathCRTModulus N P i)
        (lowerPathCRTModulus N P j)) := by
  intro i _hi j _hj hij
  cases i with
  | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some k =>
          exact hroot (lowerPathTailBlock N k)
  | some k =>
      cases j with
      | none =>
          exact (hroot (lowerPathTailBlock N k)).symm
      | some l =>
          have hkl : k ≠ l := by
            intro h
            exact hij (by simp [h])
          have hblock_ne :
              (lowerPathTailBlock N k).1 ≠ (lowerPathTailBlock N l).1 := by
            intro hblock
            apply hkl
            apply Fin.ext
            have hval := congrArg Fin.val hblock
            simp [lowerPathTailBlock, Fin.val_succ] at hval
            omega
          have hp : Nat.Prime (P (lowerPathTailBlock N k)).1 :=
            (mem_dyadicPrimeInterval.1 (P (lowerPathTailBlock N k)).2).2.2
          have hq : Nat.Prime (P (lowerPathTailBlock N l)).1 :=
            (mem_dyadicPrimeInterval.1 (P (lowerPathTailBlock N l)).2).2.2
          have hpq_ne : (P (lowerPathTailBlock N k)).1 ≠
              (P (lowerPathTailBlock N l)).1 := by
            intro hpq
            have hmem_l :
                (P (lowerPathTailBlock N k)).1 ∈
                  lowerPathPrimeInterval N (lowerPathTailBlock N l).1 := by
              simp [hpq, (P (lowerPathTailBlock N l)).2]
            exact Finset.disjoint_left.1
              (hdisj (lowerPathTailBlock N k).1 (lowerPathTailBlock N l).1 hblock_ne)
              (P (lowerPathTailBlock N k)).2 hmem_l
          exact (Nat.coprime_primes hp hq).2 hpq_ne

/-! ## CRT targets and residues -/

/-- Finite CRT in the integer `Int.ModEq` form used for path residue
assignments.  This local copy keeps the path scaffold independent of the old
`LowerConstruction.lean` file. -/
theorem lowerPath_int_modEq_crt_finset_exists {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℕ) (b : ι → ℤ)
    (hm : ∀ i ∈ s, m i ≠ 0)
    (hcop : Set.Pairwise (↑s : Set ι)
      (fun i j => Nat.Coprime (m i) (m j))) :
    ∃ a : ℤ, ∀ i ∈ s, a ≡ b i [ZMOD (m i : ℤ)] := by
  classical
  set aN : ι → ℕ := fun i => ((b i) % (m i : ℤ)).toNat with haN
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset aN m s hm hcop
  refine ⟨(k : ℤ), ?_⟩
  intro i hi
  have hm_ne : m i ≠ 0 := hm i hi
  have hm_int_ne : (m i : ℤ) ≠ 0 := by exact_mod_cast hm_ne
  have hmod_nonneg : 0 ≤ (b i) % (m i : ℤ) := Int.emod_nonneg _ hm_int_ne
  have h_aN_eq : (aN i : ℤ) = (b i) % (m i : ℤ) := by
    simp [haN, Int.toNat_of_nonneg hmod_nonneg]
  have hk_nat : k ≡ aN i [MOD m i] := hk i hi
  have hk_int : (k : ℤ) ≡ (aN i : ℤ) [ZMOD ((m i : ℕ) : ℤ)] :=
    Int.natCast_modEq_iff.mpr hk_nat
  have h_aN_modEq_b : (aN i : ℤ) ≡ b i [ZMOD (m i : ℤ)] := by
    rw [h_aN_eq]
    exact (Int.emod_emod_of_dvd (b i) dvd_rfl :
      (b i) % (m i : ℤ) % (m i : ℤ) = b i % (m i : ℤ))
  exact hk_int.trans h_aN_modEq_b

/-- Encode an element of a finite set into a natural residue below `m`,
assuming the set has at most `m` elements. -/
noncomputable def lowerPathFinsetCode (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m)
    (x : {n : ℕ // n ∈ s}) : ℕ :=
  (Fin.castLE h ((Finset.equivFin s) x)).1

lemma lowerPathFinsetCode_lt (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m)
    (x : {n : ℕ // n ∈ s}) :
    lowerPathFinsetCode s m h x < m :=
  (Fin.castLE h ((Finset.equivFin s) x)).2

lemma lowerPathFinsetCode_injective (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m) :
    Function.Injective (lowerPathFinsetCode s m h) := by
  intro x y hxy
  have hfin :
      Fin.castLE h ((Finset.equivFin s) x) =
        Fin.castLE h ((Finset.equivFin s) y) :=
    Fin.ext hxy
  exact (Finset.equivFin s).injective (Fin.castLE_injective h hfin)

lemma lowerPath_nat_eq_of_int_modEq_of_lt {m a b : ℕ}
    (ha : a < m) (hb : b < m)
    (h : (a : ℤ) ≡ (b : ℤ) [ZMOD (m : ℤ)]) :
    a = b := by
  exact Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.mp h) ha hb

/-- Capacity hypotheses needed by the source-aligned path CRT tree.  These are
the finite targets eventually supplied by prime-counting upper bounds and the
path scale separation. -/
structure LowerPathEncodingCapacity (N : ℕ) : Prop where
  root :
    ∀ hR : 0 < lowerPathR N,
      (lowerPathPrimeInterval N (lowerPathTailBlock N ⟨0, hR⟩).1).card ≤
        lowerPathP0 N
  next :
    ∀ k : Fin (lowerPathR N), ∀ hnext : k.1 + 1 < lowerPathR N,
      ∀ p : ℕ, p ∈ lowerPathPrimeInterval N (lowerPathTailBlock N k).1 →
        (lowerPathPrimeInterval N (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1).card ≤
          p
  root_coprime :
    ∀ i : lowerPathTailIndex N, ∀ p : ℕ,
      p ∈ lowerPathPrimeInterval N i.1 →
        Nat.Coprime (lowerPathP0 N) p

lemma lowerPathEncodingCapacity_of_adjacent_card_le {N : ℕ}
    (hadj : ∀ i j : lowerPathIndex N, j.1 = i.1 + 1 →
      (lowerPathPrimeInterval N j).card ≤ Nat.floor (lowerPathY N i))
    (hrootcop : ∀ i : lowerPathTailIndex N, ∀ p : ℕ,
      p ∈ lowerPathPrimeInterval N i.1 →
        Nat.Coprime (lowerPathP0 N) p) :
    LowerPathEncodingCapacity N := by
  constructor
  · intro hR
    have hidx :
        ((lowerPathTailBlock N ⟨0, hR⟩).1).1 =
          (lowerPathZeroIndex N).1 + 1 := by
      simp [lowerPathTailBlock, lowerPathZeroIndex]
    have hcard := hadj (lowerPathZeroIndex N) (lowerPathTailBlock N ⟨0, hR⟩).1 hidx
    exact hcard.trans (by simp [lowerPathP0])
  · intro k hnext p hp
    have hidx :
        ((lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1).1 =
          ((lowerPathTailBlock N k).1).1 + 1 := by
      simp [lowerPathTailBlock, Fin.val_succ]
    have hcard := hadj (lowerPathTailBlock N k).1
      (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1 hidx
    have hp_floor :
        Nat.floor (lowerPathY N (lowerPathTailBlock N k).1) < p :=
      (mem_dyadicPrimeInterval.1 hp).1
    exact hcard.trans (Nat.le_of_lt hp_floor)
  · exact hrootcop

noncomputable def lowerPathRootCode (N : ℕ) (hcap : LowerPathEncodingCapacity N)
    (P : LowerPathPrimeChoice N) : ℕ :=
  if hR : 0 < lowerPathR N then
    lowerPathFinsetCode
      (lowerPathPrimeInterval N (lowerPathTailBlock N ⟨0, hR⟩).1)
      (lowerPathP0 N) (hcap.root hR) (P (lowerPathTailBlock N ⟨0, hR⟩))
  else
    0

noncomputable def lowerPathStepCode (N : ℕ) (hcap : LowerPathEncodingCapacity N)
    (P : LowerPathPrimeChoice N) (k : Fin (lowerPathR N)) : ℕ :=
  if hnext : k.1 + 1 < lowerPathR N then
    lowerPathFinsetCode
      (lowerPathPrimeInterval N (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1)
      (P (lowerPathTailBlock N k)).1
      (hcap.next k hnext (P (lowerPathTailBlock N k)).1
        (P (lowerPathTailBlock N k)).2)
      (P (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩))
  else
    0

noncomputable def lowerPathCRTTarget (N : ℕ) (hcap : LowerPathEncodingCapacity N)
    (P : LowerPathPrimeChoice N) : lowerPathCRTIndex N → ℤ
  | none => lowerPathRootCode N hcap P
  | some k => lowerPathStepCode N hcap P k

noncomputable def lowerPathResidueForChoice {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j))
    (P : LowerPathPrimeChoice N) : ℤ :=
  Classical.choose (lowerPath_int_modEq_crt_finset_exists
    (s := (Finset.univ : Finset (lowerPathCRTIndex N)))
    (m := lowerPathCRTModulus N P)
    (b := lowerPathCRTTarget N hcap P)
    (by intro i _hi; exact lowerPathCRTModulus_ne_zero N P i)
    (lowerPathCRTModuli_pairwise_coprime P
      (fun i => hcap.root_coprime i (P i).1 (P i).2) hdisj))

lemma lowerPathResidueForChoice_spec {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j))
    (P : LowerPathPrimeChoice N) (i : lowerPathCRTIndex N) :
    lowerPathResidueForChoice hcap hdisj P ≡
      lowerPathCRTTarget N hcap P i [ZMOD (lowerPathCRTModulus N P i : ℤ)] :=
  Classical.choose_spec (lowerPath_int_modEq_crt_finset_exists
    (s := (Finset.univ : Finset (lowerPathCRTIndex N)))
    (m := lowerPathCRTModulus N P)
    (b := lowerPathCRTTarget N hcap P)
    (by intro i _hi; exact lowerPathCRTModulus_ne_zero N P i)
    (lowerPathCRTModuli_pairwise_coprime P
      (fun i => hcap.root_coprime i (P i).1 (P i).2) hdisj)) i (Finset.mem_univ i)

/-- A canonical preimage choice for a modulus in `lowerPathQ`. -/
lemma lowerPathChoiceOfQ_exists (N : ℕ) (q : {q : ℕ // q ∈ lowerPathQ N}) :
    ∃ P ∈ lowerPathChoices N, lowerPathModulus N P = q.1 := by
  have hq : q.1 ∈ lowerPathQ N := q.2
  change q.1 ∈ (lowerPathChoices N).image (lowerPathModulus N) at hq
  exact Finset.mem_image.1 hq

noncomputable def lowerPathChoiceOfQ (N : ℕ) (q : {q : ℕ // q ∈ lowerPathQ N}) :
    LowerPathPrimeChoice N :=
  Classical.choose (lowerPathChoiceOfQ_exists N q)

lemma lowerPathChoiceOfQ_mem (N : ℕ) (q : {q : ℕ // q ∈ lowerPathQ N}) :
    lowerPathChoiceOfQ N q ∈ lowerPathChoices N :=
  (Classical.choose_spec (lowerPathChoiceOfQ_exists N q)).1

lemma lowerPathChoiceOfQ_modulus (N : ℕ) (q : {q : ℕ // q ∈ lowerPathQ N}) :
    lowerPathModulus N (lowerPathChoiceOfQ N q) = q.1 :=
  (Classical.choose_spec (lowerPathChoiceOfQ_exists N q)).2

noncomputable def lowerPathResidueAssignment {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j)) :
    ResidueAssignment (lowerPathQ N) :=
  fun q => lowerPathResidueForChoice hcap hdisj (lowerPathChoiceOfQ N q)

lemma lowerPathResidueAssignment_modEq_target {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j))
    (q : {q : ℕ // q ∈ lowerPathQ N}) (i : lowerPathCRTIndex N) {n : ℤ}
    (hn : n ∈ residueClass q.1 (lowerPathResidueAssignment hcap hdisj q)) :
    n ≡ lowerPathCRTTarget N hcap (lowerPathChoiceOfQ N q) i
      [ZMOD (lowerPathCRTModulus N (lowerPathChoiceOfQ N q) i : ℤ)] := by
  have hnq :
      n ≡ lowerPathResidueForChoice hcap hdisj (lowerPathChoiceOfQ N q)
        [ZMOD (q.1 : ℤ)] := by
    simpa [residueClass, lowerPathResidueAssignment] using hn
  have hn_lower :
      n ≡ lowerPathResidueForChoice hcap hdisj (lowerPathChoiceOfQ N q)
        [ZMOD (lowerPathModulus N (lowerPathChoiceOfQ N q) : ℤ)] := by
    simpa [lowerPathChoiceOfQ_modulus N q] using hnq
  have hdivNat :
      lowerPathCRTModulus N (lowerPathChoiceOfQ N q) i ∣
        lowerPathModulus N (lowerPathChoiceOfQ N q) :=
    lowerPathCRTModulus_dvd_lowerPathModulus N (lowerPathChoiceOfQ N q) i
  have hdivInt :
      (lowerPathCRTModulus N (lowerPathChoiceOfQ N q) i : ℤ) ∣
        (lowerPathModulus N (lowerPathChoiceOfQ N q) : ℤ) := by
    exact_mod_cast hdivNat
  exact (Int.ModEq.of_dvd hdivInt hn_lower).trans
    (lowerPathResidueForChoice_spec hcap hdisj (lowerPathChoiceOfQ N q) i)

lemma lowerPathRootCode_eq_of_modEq {N : ℕ} (hcap : LowerPathEncodingCapacity N)
    (P P' : LowerPathPrimeChoice N) (hR : 0 < lowerPathR N)
    (hmod : (lowerPathRootCode N hcap P : ℤ) ≡
      (lowerPathRootCode N hcap P' : ℤ) [ZMOD (lowerPathP0 N : ℤ)]) :
    P (lowerPathTailBlock N ⟨0, hR⟩) = P' (lowerPathTailBlock N ⟨0, hR⟩) := by
  let s := lowerPathPrimeInterval N (lowerPathTailBlock N ⟨0, hR⟩).1
  let m := lowerPathP0 N
  let hcard := hcap.root hR
  have hltP :
      lowerPathRootCode N hcap P < lowerPathP0 N := by
    simpa [lowerPathRootCode, hR, s, m, hcard] using
      lowerPathFinsetCode_lt s m hcard (P (lowerPathTailBlock N ⟨0, hR⟩))
  have hltP' :
      lowerPathRootCode N hcap P' < lowerPathP0 N := by
    simpa [lowerPathRootCode, hR, s, m, hcard] using
      lowerPathFinsetCode_lt s m hcard (P' (lowerPathTailBlock N ⟨0, hR⟩))
  have hcode_eq : lowerPathRootCode N hcap P = lowerPathRootCode N hcap P' :=
    lowerPath_nat_eq_of_int_modEq_of_lt hltP hltP' hmod
  have hcode_eq' :
      lowerPathFinsetCode s m hcard (P (lowerPathTailBlock N ⟨0, hR⟩)) =
        lowerPathFinsetCode s m hcard (P' (lowerPathTailBlock N ⟨0, hR⟩)) := by
    simpa [lowerPathRootCode, hR, s, m, hcard] using hcode_eq
  exact lowerPathFinsetCode_injective s m hcard hcode_eq'

lemma lowerPathStepCode_eq_of_modEq {N : ℕ} (hcap : LowerPathEncodingCapacity N)
    (P P' : LowerPathPrimeChoice N) (k : Fin (lowerPathR N))
    (hnext : k.1 + 1 < lowerPathR N)
    (hprev : P (lowerPathTailBlock N k) = P' (lowerPathTailBlock N k))
    (hmod : (lowerPathStepCode N hcap P k : ℤ) ≡
      (lowerPathStepCode N hcap P' k : ℤ)
        [ZMOD ((P (lowerPathTailBlock N k)).1 : ℤ)]) :
    P (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩) =
      P' (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩) := by
  let s := lowerPathPrimeInterval N (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1
  let m := (P (lowerPathTailBlock N k)).1
  let hcard :=
    hcap.next k hnext (P (lowerPathTailBlock N k)).1 (P (lowerPathTailBlock N k)).2
  have hltP :
      lowerPathStepCode N hcap P k < (P (lowerPathTailBlock N k)).1 := by
    simpa [lowerPathStepCode, hnext, s, m, hcard] using
      lowerPathFinsetCode_lt s m hcard
        (P (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩))
  have hltP' :
      lowerPathStepCode N hcap P' k < (P (lowerPathTailBlock N k)).1 := by
    have hcard' :=
      hcap.next k hnext (P' (lowerPathTailBlock N k)).1 (P' (lowerPathTailBlock N k)).2
    have hlt' :
        lowerPathStepCode N hcap P' k < (P' (lowerPathTailBlock N k)).1 := by
      simpa [lowerPathStepCode, hnext] using
        lowerPathFinsetCode_lt s (P' (lowerPathTailBlock N k)).1 hcard'
          (P' (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩))
    simpa [hprev] using hlt'
  have hcode_eq : lowerPathStepCode N hcap P k = lowerPathStepCode N hcap P' k :=
    lowerPath_nat_eq_of_int_modEq_of_lt hltP hltP' hmod
  have hcode_eq' :
      lowerPathFinsetCode s m hcard
          (P (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩)) =
        lowerPathFinsetCode s m hcard
          (P' (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩)) := by
    simpa [lowerPathStepCode, hnext, s, m, hcard] using hcode_eq
  exact lowerPathFinsetCode_injective s m hcard hcode_eq'

lemma lowerPathResidueAssignment_pairwise_disjoint_of_capacity {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j)) :
    PairwiseDisjointResidues (lowerPathQ N) (lowerPathResidueAssignment hcap hdisj) := by
  intro q r hqr
  rw [Set.disjoint_left]
  intro z hzq hzr
  let P := lowerPathChoiceOfQ N q
  let P' := lowerPathChoiceOfQ N r
  have hP_eq : P = P' := by
    by_cases hR : 0 < lowerPathR N
    · have hq0 := lowerPathResidueAssignment_modEq_target hcap hdisj q none hzq
      have hr0 := lowerPathResidueAssignment_modEq_target hcap hdisj r none hzr
      have hroot_mod :
          (lowerPathCRTTarget N hcap P none) ≡
            (lowerPathCRTTarget N hcap P' none)
              [ZMOD (lowerPathP0 N : ℤ)] := by
        simpa [P, P', lowerPathCRTModulus] using hq0.symm.trans hr0
      have hzero :
          P (lowerPathTailBlock N ⟨0, hR⟩) =
            P' (lowerPathTailBlock N ⟨0, hR⟩) := by
        exact lowerPathRootCode_eq_of_modEq hcap P P' hR
          (by simpa [lowerPathCRTTarget] using hroot_mod)
      have hall :
          ∀ n : ℕ, ∀ hn : n < lowerPathR N,
            P (lowerPathTailBlock N ⟨n, hn⟩) =
              P' (lowerPathTailBlock N ⟨n, hn⟩) := by
        intro n
        induction n with
        | zero =>
            intro hn
            simpa using hzero
        | succ n ih =>
            intro hn
            have hprev_lt : n < lowerPathR N := Nat.lt_of_succ_lt hn
            have hprev := ih hprev_lt
            let k : Fin (lowerPathR N) := ⟨n, hprev_lt⟩
            have hqk := lowerPathResidueAssignment_modEq_target hcap hdisj q (some k) hzq
            have hrk := lowerPathResidueAssignment_modEq_target hcap hdisj r (some k) hzr
            have hstep_mod :
                (lowerPathCRTTarget N hcap P (some k)) ≡
                  (lowerPathCRTTarget N hcap P' (some k))
                    [ZMOD ((P (lowerPathTailBlock N k)).1 : ℤ)] := by
              have hrk' :
                  z ≡ lowerPathCRTTarget N hcap P' (some k)
                    [ZMOD ((P (lowerPathTailBlock N k)).1 : ℤ)] := by
                have hprev_val :
                    (lowerPathChoiceOfQ N r (lowerPathTailBlock N k)).1 =
                      (lowerPathChoiceOfQ N q (lowerPathTailBlock N k)).1 := by
                  dsimp [P, P'] at hprev
                  exact congrArg Subtype.val hprev.symm
                simpa [P, P', lowerPathCRTModulus, hprev_val] using hrk
              simpa [P, P', lowerPathCRTModulus] using hqk.symm.trans hrk'
            exact lowerPathStepCode_eq_of_modEq hcap P P' k hn hprev
              (by simpa [lowerPathCRTTarget] using hstep_mod)
      exact lowerPathTailBlock_ext (fun k => hall k.1 k.2)
    · apply lowerPathTailBlock_ext
      intro k
      have hk : k.1 < lowerPathR N := k.2
      exact False.elim (hR (lt_of_le_of_lt (Nat.zero_le k.1) hk))
  have hqval : q.1 = r.1 := by
    calc
      q.1 = lowerPathModulus N P := (lowerPathChoiceOfQ_modulus N q).symm
      _ = lowerPathModulus N P' := by rw [hP_eq]
      _ = r.1 := lowerPathChoiceOfQ_modulus N r
  exact hqr (Subtype.ext hqval)

/-- Finite admissibility package for the source-aligned path family.  The
remaining work before this can replace the old lower construction is to prove
the hypotheses eventually from the path scale algebra and prime-counting
estimates. -/
theorem lowerPathQ_admissible_of_capacity {N : ℕ}
    (hNpos : 0 < (N : ℝ))
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N))
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j)) :
    Admissible N (lowerPathQ N) := by
  constructor
  · exact lowerPathQ_moduli_in_range_of_root_scale hNpos hY0
  · exact ⟨lowerPathResidueAssignment hcap hdisj,
      lowerPathResidueAssignment_pairwise_disjoint_of_capacity hcap hdisj⟩

theorem lowerPathQ_admissible_eventually_of_capacity :
    ∀ᶠ N : ℕ in atTop,
      LowerPathEncodingCapacity N → Admissible N (lowerPathQ N) := by
  filter_upwards [Filter.eventually_gt_atTop 0,
      eventually_lowerPathY_zero_ge_one,
      lowerPathPrimeIntervals_pairwise_disjoint] with N hNpos_nat hY0 hdisj hcap
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
  exact lowerPathQ_admissible_of_capacity hNpos hY0 hcap hdisj

theorem lowerPathEncodingCapacity_eventually :
    ∀ᶠ N : ℕ in atTop, LowerPathEncodingCapacity N := by
  filter_upwards [lowerPathPrimeInterval_adjacent_card_le_floor_prev_eventually,
      lowerPath_root_coprime_tail_prime_eventually] with N hadj hrootcop
  exact lowerPathEncodingCapacity_of_adjacent_card_le hadj hrootcop

theorem lowerPathQ_admissible_eventually :
    ∀ᶠ N : ℕ in atTop, Admissible N (lowerPathQ N) := by
  filter_upwards [lowerPathQ_admissible_eventually_of_capacity,
      lowerPathEncodingCapacity_eventually] with N hadm hcap
  exact hadm hcap

/-! ## From the source-aligned path family to lower-bound input -/

lemma lowerPath_admissible_mono {N : ℕ} {Q Q' : Finset ℕ}
    (hQ : Admissible N Q) (hsub : Q' ⊆ Q) :
    Admissible N Q' := by
  constructor
  · intro q hq
    exact hQ.1 q (hsub hq)
  · rcases hQ.2 with ⟨a, ha⟩
    exact ⟨restrictAssignment a hsub, PairwiseDisjointResidues.mono ha hsub⟩

lemma lowerPath_possibleCard_of_admissible_card_le {N r : ℕ} {Q : Finset ℕ}
    (hQ : Admissible N Q) (hr : r ≤ Q.card) :
    PossibleCard N r := by
  classical
  rcases Finset.exists_subset_card_eq (s := Q) hr with ⟨Q', hsub, hcard⟩
  exact ⟨Q', lowerPath_admissible_mono hQ hsub, hcard⟩

theorem lowerPath_possibleCard_eventually_of_floor_product
    (ε : ℝ)
    (hfloor :
      ∀ᶠ N : ℕ in atTop,
        Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) ≤
          lowerPathPrimeFloorProduct lowerPathChebEta N) :
    ∀ᶠ N : ℕ in atTop,
      PossibleCard N (Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N)) := by
  filter_upwards [lowerPathQ_admissible_eventually,
      lowerPathQ_card_ge_prime_floor_product_eventually,
      hfloor] with N hadm hfloor_le_Q htarget_le_floor
  exact lowerPath_possibleCard_of_admissible_card_le hadm
    (htarget_le_floor.trans hfloor_le_Q)

theorem lowerPath_floor_product_lower_bound_eventually_of_real_product
    (ε : ℝ)
    (hreal :
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) * Lscale (-(1 + ε)) N ≤ lowerPathRealPrimeProduct N) :
    ∀ᶠ N : ℕ in atTop,
      Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) ≤
        lowerPathPrimeFloorProduct lowerPathChebEta N := by
  filter_upwards [hreal, lowerPathPrimeFloorProduct_floor_loss_eventually] with
    N htarget hfloor
  exact Nat.ceil_le.2 (htarget.trans hfloor)

theorem lowerPath_real_product_lower_bound_eventually_of_denominator_bound
    (ε : ℝ) (_hε : 0 < ε)
    (hden :
      ∀ᶠ N : ℕ in atTop,
        lowerPathRealDenominator N ≤ Lscale (1 + ε) N) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ lowerPathRealPrimeProduct N := by
  filter_upwards [Filter.eventually_gt_atTop 0,
      eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge 64,
      hden] with N hNpos_nat hgap hY0 hden_le
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
  have hNnonneg : 0 ≤ (N : ℝ) := hNpos.le
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
  have hlog_pos : ∀ i : lowerPathTailIndex N,
      0 < Real.log (lowerPathY N i.1) := by
    intro i
    have hzero_le_i :
        lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
      lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
    have hY0' : (64 : ℝ) ≤ lowerPathY N (lowerPathZeroIndex N) := by
      simpa [lowerPathZeroIndex] using hY0
    exact Real.log_pos (by linarith [hY0'.trans hzero_le_i])
  have hden_pos : 0 < lowerPathRealDenominator N :=
    lowerPathRealDenominator_pos hlog_pos
  have hid :
      lowerPathRealPrimeProduct N * lowerPathRealDenominator N = (N : ℝ) :=
    lowerPathRealPrimeProduct_mul_denominator_eq hNpos
      (fun i => (hlog_pos i).ne')
  have hleft_mul :
      ((N : ℝ) * Lscale (-(1 + ε)) N) * lowerPathRealDenominator N ≤
        (N : ℝ) := by
    calc
      ((N : ℝ) * Lscale (-(1 + ε)) N) * lowerPathRealDenominator N
          ≤ ((N : ℝ) * Lscale (-(1 + ε)) N) * Lscale (1 + ε) N := by
            exact mul_le_mul_of_nonneg_left hden_le
              (mul_nonneg hNnonneg (Lscale_nonneg _ _))
      _ = (N : ℝ) * (Lscale (-(1 + ε)) N * Lscale (1 + ε) N) := by ring
      _ = (N : ℝ) := by
            rw [Lscale_neg_mul]
            ring
  have hmul :
      ((N : ℝ) * Lscale (-(1 + ε)) N) * lowerPathRealDenominator N ≤
        lowerPathRealPrimeProduct N * lowerPathRealDenominator N := by
    simpa [hid] using hleft_mul
  exact le_of_mul_le_mul_right hmul hden_pos

theorem lowerPath_denominator_bound_eventually_of_simple_bound
    (ε : ℝ)
    (hsimple :
      ∀ᶠ N : ℕ in atTop,
        (2 * lowerPathY N (lowerPathZeroIndex N)) *
            (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N ≤
              Lscale (1 + ε) N) :
    ∀ᶠ N : ℕ in atTop,
      lowerPathRealDenominator N ≤ Lscale (1 + ε) N := by
  filter_upwards [lowerPathRealDenominator_le_simple_eventually,
      hsimple] with N hden_simple hsimple_N
  exact hden_simple.trans hsimple_N

lemma eventually_log_const_mul_Zscale_le
    (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (C * Zscale N) ≤
        ((1 + δ) / 2) * Real.log (Real.log (N : ℝ)) := by
  have hδ2 : 0 < δ / 2 := by positivity
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_log_const_mul_sqrt_loglog_le_mul_loglog C (δ / 2) hC hδ2,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 1] with
    N hNlarge_nat hlog_extra hYge_one
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set Y := Real.log (Real.log (N : ℝ))
  have hY_pos : 0 < Y := zero_lt_one.trans_le (by simpa [Y] using hYge_one)
  have hsqrt_pos : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY_pos
  have hZeq := Zscale_eq_exp_half_loglog_mul_sqrt_loglog hNlarge
  calc
    Real.log (C * Zscale N)
        = Real.log (Real.exp (Y / 2) * (C * Real.sqrt Y)) := by
            congr 1
            rw [hZeq]
            ring
    _ = Y / 2 + Real.log (C * Real.sqrt Y) := by
            rw [Real.log_mul (Real.exp_ne_zero _)
              (mul_pos hC hsqrt_pos).ne', Real.log_exp]
    _ ≤ Y / 2 + (δ / 2) * Y := by
            have hlog_extraY :
                Real.log (C * Real.sqrt Y) ≤ (δ / 2) * Y := by
              simpa [Y] using hlog_extra
            nlinarith
    _ = ((1 + δ) / 2) * Y := by ring

lemma eventually_lowerPathR_mul_log_constZ_le_mul_Zscale
    (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (lowerPathR N : ℝ) * Real.log (C * Zscale N) ≤
        (1 + δ) * Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_log_const_mul_Zscale_le C δ hC hδ,
      eventually_Zscale_ge_const_path (1 / C)] with N hNlarge_nat hlog_le hZge
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Mscale_nonneg N
  have hY_nonneg : 0 ≤ Y := by
    have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
    have hlog_gt_one : 1 < Real.log (N : ℝ) :=
      (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
    exact (Real.log_pos hlog_gt_one).le
  have hMY : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hr_le : (lowerPathR N : ℝ) ≤ 2 * M := by
    dsimp [lowerPathR, M]
    exact Nat.floor_le (by positivity : 0 ≤ 2 * Mscale N)
  have hbase_ge_one : 1 ≤ C * Zscale N := by
    have hmul := mul_le_mul_of_nonneg_left hZge hC.le
    have hone : (1 : ℝ) = C * (1 / C) := by
      field_simp [hC.ne']
    nlinarith
  have hlog_nonneg : 0 ≤ Real.log (C * Zscale N) :=
    Real.log_nonneg hbase_ge_one
  calc
    (lowerPathR N : ℝ) * Real.log (C * Zscale N)
        ≤ (2 * M) * Real.log (C * Zscale N) := by
            exact mul_le_mul_of_nonneg_right hr_le hlog_nonneg
    _ ≤ (2 * M) * (((1 + δ) / 2) * Y) := by
            exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
    _ = (1 + δ) * (M * Y) := by ring
    _ = (1 + δ) * Zscale N := by rw [hMY]

theorem lowerPath_simple_denominator_bound_eventually :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (2 * lowerPathY N (lowerPathZeroIndex N)) *
          (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N ≤
            Lscale (1 + ε) N := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_Zscale_ge_const_path (3 * Real.log 2 / ε),
      eventually_lowerPathLogScale_zero_le_mul_Zscale (ε / 3) hε3,
      eventually_lowerPathR_mul_log_constZ_le_mul_Zscale
        lowerPathDenominatorConstant (ε / 3)
        lowerPathDenominatorConstant_pos hε3,
      eventually_Zscale_pos] with N hNlarge_nat hZconst hroot hmain hZpos
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hbase_pos : 0 < lowerPathDenominatorConstant * Zscale N :=
    mul_pos lowerPathDenominatorConstant_pos hZpos
  have hpow :
      (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N =
        Real.exp ((lowerPathR N : ℝ) *
          Real.log (lowerPathDenominatorConstant * Zscale N)) := by
    calc
      (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N
          = (Real.exp (Real.log
              (lowerPathDenominatorConstant * Zscale N))) ^ lowerPathR N := by
              rw [Real.exp_log hbase_pos]
      _ = Real.exp ((lowerPathR N : ℝ) *
          Real.log (lowerPathDenominatorConstant * Zscale N)) := by
              rw [← Real.exp_nat_mul]
  have hprod_eq :
      (2 * lowerPathY N (lowerPathZeroIndex N)) *
          (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N =
        Real.exp
          (Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N) +
            (lowerPathR N : ℝ) *
              Real.log (lowerPathDenominatorConstant * Zscale N)) := by
    rw [lowerPathY, hpow]
    calc
      (2 * Real.exp (lowerPathLogScale N (lowerPathZeroIndex N))) *
          Real.exp ((lowerPathR N : ℝ) *
            Real.log (lowerPathDenominatorConstant * Zscale N))
          = Real.exp (Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N)) *
              Real.exp ((lowerPathR N : ℝ) *
                Real.log (lowerPathDenominatorConstant * Zscale N)) := by
              rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp
          (Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N) +
            (lowerPathR N : ℝ) *
              Real.log (lowerPathDenominatorConstant * Zscale N)) := by
              rw [← Real.exp_add]
  have hconst : Real.log 2 ≤ (ε / 3) * Zscale N := by
    have hmul := mul_le_mul_of_nonneg_left hZconst hε.le
    have hthree :
        3 * Real.log 2 ≤ ε * Zscale N := by
      calc
        3 * Real.log 2 = ε * (3 * Real.log 2 / ε) := by
            field_simp [hε.ne']
        _ ≤ ε * Zscale N := hmul
    nlinarith
  have hexponent :
      Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N) +
          (lowerPathR N : ℝ) *
            Real.log (lowerPathDenominatorConstant * Zscale N) ≤
        (1 + ε) * Zscale N := by
    have hroot_zero :
        lowerPathLogScale N (lowerPathZeroIndex N) ≤ (ε / 3) * Zscale N := by
      simpa [lowerPathZeroIndex] using hroot
    calc
      Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N) +
          (lowerPathR N : ℝ) *
            Real.log (lowerPathDenominatorConstant * Zscale N)
          ≤ (ε / 3) * Zscale N + (ε / 3) * Zscale N +
              (1 + ε / 3) * Zscale N := by
              nlinarith [hconst, hroot_zero, hmain]
      _ = (1 + ε) * Zscale N := by ring
  rw [hprod_eq, Lscale]
  exact Real.exp_le_exp.2 hexponent

theorem lowerPath_f_lower_bound_eventually_of_floor_product
    (hfloor :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) ≤
          lowerPathPrimeFloorProduct lowerPathChebEta N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  intro ε hε
  filter_upwards [
      lowerPath_possibleCard_eventually_of_floor_product
        ε (hfloor ε hε)] with N hPossible
  have hceil_le_f :
      Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) ≤ f N :=
    le_f_of_possibleCard hPossible
  have htarget_le_ceil :
      (N : ℝ) * Lscale (-(1 + ε)) N ≤
        (Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) : ℝ) :=
    Nat.le_ceil ((N : ℝ) * Lscale (-(1 + ε)) N)
  exact htarget_le_ceil.trans (by exact_mod_cast hceil_le_f)

theorem lowerPath_f_lower_bound_eventually_of_real_product
    (hreal :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        (N : ℝ) * Lscale (-(1 + ε)) N ≤ lowerPathRealPrimeProduct N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  exact lowerPath_f_lower_bound_eventually_of_floor_product
    (fun ε hε => lowerPath_floor_product_lower_bound_eventually_of_real_product
      ε (hreal ε hε))

theorem lowerPath_f_lower_bound_eventually_of_denominator_bound
    (hden :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        lowerPathRealDenominator N ≤ Lscale (1 + ε) N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  exact lowerPath_f_lower_bound_eventually_of_real_product
    (fun ε hε => lowerPath_real_product_lower_bound_eventually_of_denominator_bound
      ε hε (hden ε hε))

theorem lowerPath_f_lower_bound_eventually_of_simple_bound
    (hsimple :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        (2 * lowerPathY N (lowerPathZeroIndex N)) *
            (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N ≤
              Lscale (1 + ε) N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  exact lowerPath_f_lower_bound_eventually_of_denominator_bound
    (fun ε hε => lowerPath_denominator_bound_eventually_of_simple_bound
      ε (hsimple ε hε))

theorem lowerPath_f_lower_bound_eventually :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) :=
  lowerPath_f_lower_bound_eventually_of_simple_bound
    lowerPath_simple_denominator_bound_eventually

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFV/LowerBoundInput.lean
    ============================================================= -/

/-
Erdos Problem 202 -- BFV lower-bound theorem.

This file proves the theorem with the same signature as
`Erdos202.bfv_lower_bound_input`, using the source-aligned rooted path lower
construction from `LowerPathConstruction.lean`.
-/


namespace Erdos202

open Filter

/-- BFV lower-bound theorem, matching the old input interface. -/
theorem bfv_lower_bound_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) :=
  lowerPath_f_lower_bound_eventually

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFVInputs.lean
    ============================================================= -/

/-
Erdős Problem 202 — BFV inputs layer.

The BFV (de la Bretèche–Ford–Vandehey) input interface used by
the descending chain:

  * `bfv_omega_count_input`       : count of `n ≤ y` with `omega n = K - W`,
                                     uniform in K, W in the BFV range.
  * `bfv_lower_bound_input`       : matching lower bound `f(N) ≥ N · L(-(1+ε), N)`.

The omega-count and lower-bound historical names are theorem aliases to the
current BFV subdirectory replacements.  The pruning theorem is proved in
`Erdos.P202.BFV.Pruning`, which imports this file for the `PrunedData`
structure.
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## §1 The pruned-data structure -/

/-- A pruned BFV family: a subfamily `Q'` of an admissible family with
controlled multiplicative complexity (`omega = K`, `hExp ≤ exp(sqrt(log N))`,
`q ∈ [N L(-2, N), N]`, distinct radicals).

This is the formal output of BFV pruning. Cardinality decay from the input
admissible family is at most a factor of `L(o(1), N)`. -/
structure PrunedData (N : ℕ) where
  Q : Finset ℕ
  Q_nonempty : Q.Nonempty
  a : ResidueAssignment Q
  admissible : Admissible N Q
  pairwise_disjoint : PairwiseDisjointResidues Q a
  K : ℕ
  K_pos : 1 ≤ K
  modulus_lower : ∀ q ∈ Q, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ)
  modulus_upper : ∀ q ∈ Q, q ≤ N
  hExp_bound : ∀ q ∈ Q, (hExp q : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ)))
  omega_eq : ∀ q ∈ Q, omega q = K
  K_bound : (K : ℝ) ≤ 3 * Mscale N
  rad_injective : ∀ q ∈ Q, ∀ r ∈ Q, rad q = rad r → q = r

lemma PrunedData.card_pos {N : ℕ} (D : PrunedData N) : 0 < D.Q.card :=
  D.Q_nonempty.card_pos

lemma PrunedData.N_pos {N : ℕ} (D : PrunedData N) : 0 < N := by
  rcases D.Q_nonempty with ⟨q, hq⟩
  exact lt_of_lt_of_le (D.admissible.1 q hq).1 (D.modulus_upper q hq)

lemma PrunedData.Q_subset_Icc {N : ℕ} (D : PrunedData N) :
    D.Q ⊆ Finset.Icc 1 N := by
  intro q hq
  exact Finset.mem_Icc.2 (D.admissible.1 q hq)

lemma PrunedData.card_le_N {N : ℕ} (D : PrunedData N) :
    D.Q.card ≤ N := by
  have hcard := Finset.card_le_card D.Q_subset_Icc
  have hIcc : (Finset.Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  simpa [hIcc] using hcard

lemma PrunedData.possibleCard {N : ℕ} (D : PrunedData N) :
    PossibleCard N D.Q.card :=
  ⟨D.Q, D.admissible, rfl⟩

lemma PrunedData.card_le_f {N : ℕ} (D : PrunedData N) :
    D.Q.card ≤ f N :=
  le_f_of_possibleCard D.possibleCard

/-! ## §2 BFV ω-count estimate -/

/-- **BFV ω-count input.** Uniform in `1 ≤ y ≤ N`, `K ≤ 3 M(N)`, and
`0 ≤ W ≤ K`, the count of integers up to `y` with `ω(n) = K - W` is at most
`y · L(-d/2 + ε, N) · (log N)^{W/2}`, where `d = K / M(N)`.

The `y ≤ N` hypothesis matches BFV Lemma 3.1's range (the original is stated
for `2 ≤ y ≤ x`); without it the count estimate is not BFV and is probably
false for arbitrarily large `y` relative to `N`. The PDF's quotient count
(Lemma 3.2) likewise requires `1 ≤ y ≤ x`.

The `(log N)^{W/2}` is real-exponentiated; we phrase it as
`exp((W/2) · log log N)` to avoid `Real.rpow` overhead. -/
theorem bfv_omega_count_input :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y K W : ℕ,
      y ≤ N →
      W ≤ K →
      (K : ℝ) ≤ 3 * Mscale N →
      let d : ℝ := (K : ℝ) / Mscale N
      ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
        ≤ Nat.floor
            ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
              * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) :=
  bfv_omega_count_theorem

/-! ## §3 BFV lower-bound construction -/

/-- **BFV lower-bound input.** The unconditional matching lower bound
`f(N) ≥ N · exp(-(1+ε) · Z(N))` for every `ε > 0`, eventually.

Discharged by BFV's explicit construction; published, classical. -/
theorem bfv_lower_bound_input :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) :=
  bfv_lower_bound_theorem

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/P202Chain.lean
    ============================================================= -/

/-
Erdős Problem 202 — Descending chain.

Heart of the new contribution. Builds an `R`-step chain of pairwise coprime
prime-power blocks `P_1, …, P_R` such that every surviving modulus has
`P_{≤r}` as an exact divisor, residues agree mod `P_{≤r}`, and the size
inequality (PDF eq. 9)

  P_r ≤ (N / |Q'|) · exp((-d/2 + ε) Z) · (log N)^{W_{r-1}/2} · LowerOrder(N, ω(P_{≤r}))

holds at each step.

Combines the gcd criterion (`P202Basic.lean`), the dense-core lemma
(`SpreadCore.lean`), and the BFV ω-count input (`BFVInputs.lean`).
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## §0 Weighted pigeonhole -/

lemma nat_cast_le_of_le_floor {m : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (h : m ≤ Nat.floor x) : (m : ℝ) ≤ x := by
  exact (Nat.le_floor_iff hx).1 h

/-- Weighted pigeonhole principle. If a finite weighted average is formed
with positive weights, at least one summand is at least its weighted share.

This is the finite lemma used in PDF Lemma 4.1 to select an attained exact
block value. -/
lemma weighted_pigeonhole {α : Type*} [DecidableEq α] (I : Finset α)
    (N w : α → ℝ) (hI : I.Nonempty)
    (hw : ∀ i ∈ I, 0 < w i) :
    ∃ i ∈ I, (∑ j ∈ I, N j) * w i / (∑ j ∈ I, w j) ≤ N i := by
  classical
  let totalN := ∑ j ∈ I, N j
  let totalW := ∑ j ∈ I, w j
  have htotalW_pos : 0 < totalW := Finset.sum_pos hw hI
  by_contra h
  push Not at h
  have hlt : ∀ i ∈ I, N i < totalN * w i / totalW := by
    intro i hi
    simpa [totalN, totalW] using h i hi
  have hsum_lt : ∑ i ∈ I, N i < ∑ i ∈ I, totalN * w i / totalW := by
    exact Finset.sum_lt_sum_of_nonempty hI hlt
  have hsum_rhs : (∑ i ∈ I, totalN * w i / totalW) = totalN := by
    calc
      (∑ i ∈ I, totalN * w i / totalW) =
          ∑ i ∈ I, (totalN / totalW) * w i := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (totalN / totalW) * totalW := by rw [Finset.mul_sum]
      _ = totalN := div_mul_cancel₀ totalN htotalW_pos.ne'
  have : totalN < totalN := by
    change (∑ i ∈ I, N i) < totalN
    rw [← hsum_rhs]
    exact hsum_lt
  exact lt_irrefl _ this

/-- Weighted pigeonhole applied to fibers of a finite map. For any positive
weight on the attained values of `B`, one value has a fiber at least its
weighted share of the whole domain. -/
lemma exists_fiber_weighted_share {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (B : α → β) (w : β → ℝ) (hS : S.Nonempty)
    (hw : ∀ b ∈ S.image B, 0 < w b) :
    ∃ b ∈ S.image B,
      (S.card : ℝ) * w b / (∑ c ∈ S.image B, w c) ≤
        ((S.filter fun a => B a = b).card : ℝ) := by
  classical
  have hImage : (S.image B).Nonempty := hS.image B
  rcases weighted_pigeonhole (S.image B)
      (fun b => ((S.filter fun a => B a = b).card : ℝ)) w hImage hw with
    ⟨b, hb, hbshare⟩
  refine ⟨b, hb, ?_⟩
  have hsum_counts_nat :
      (∑ b ∈ S.image B, (S.filter fun a => B a = b).card) = S.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro h
      exact h.1
    · intro ha
      exact ⟨ha, a, ha, rfl⟩
  have hsum_counts_real :
      (∑ b ∈ S.image B, ((S.filter fun a => B a = b).card : ℝ)) =
        (S.card : ℝ) := by
    exact_mod_cast hsum_counts_nat
  simpa [hsum_counts_real] using hbshare

lemma fiber_nonempty_of_mem_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {B : α → β} {b : β} (hb : b ∈ S.image B) :
    (S.filter fun a => B a = b).Nonempty := by
  rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
  exact ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩⟩

/-- Ordinary pigeonhole over a finite codomain, in the real-valued form used
for residue classes modulo the chosen exact block. -/
lemma exists_fiber_card_div_le {α β : Type*} [DecidableEq α] [Fintype β]
    [DecidableEq β] (S : Finset α) (r : α → β) (hS : S.Nonempty) :
    ∃ b : β,
      (S.card : ℝ) / (Fintype.card β : ℝ) ≤
        ((S.filter fun a => r a = b).card : ℝ) := by
  classical
  haveI : Nonempty β := by
    rcases hS with ⟨a, _ha⟩
    exact ⟨r a⟩
  have hUniv : (Finset.univ : Finset β).Nonempty := Finset.univ_nonempty
  rcases weighted_pigeonhole (Finset.univ : Finset β)
      (fun b => ((S.filter fun a => r a = b).card : ℝ)) (fun _ => (1 : ℝ))
      hUniv (by intro _b _hb; norm_num) with ⟨b, _hb, hbshare⟩
  refine ⟨b, ?_⟩
  have hsum_counts_nat :
      (∑ b ∈ (Finset.univ : Finset β), (S.filter fun a => r a = b).card) =
        S.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    simp
  have hsum_counts_real :
      (∑ b ∈ (Finset.univ : Finset β),
          ((S.filter fun a => r a = b).card : ℝ)) = (S.card : ℝ) := by
    exact_mod_cast hsum_counts_nat
  have hsum_weights :
      (∑ _b ∈ (Finset.univ : Finset β), (1 : ℝ)) =
        (Fintype.card β : ℝ) := by
    simp
  simpa [hsum_counts_real, hsum_weights] using hbshare

/-- Residue-class pigeonhole specialized to `ZMod P`. -/
lemma exists_zmod_fiber_card_div_le (T : Finset ℕ) (P : ℕ) [NeZero P]
    (r : ℕ → ZMod P) (hT : T.Nonempty) :
    ∃ b : ZMod P,
      (T.card : ℝ) / (P : ℝ) ≤ ((T.filter fun q => r q = b).card : ℝ) := by
  rcases exists_fiber_card_div_le T r hT with ⟨b, hb⟩
  exact ⟨b, by simpa [ZMod.card] using hb⟩

lemma List.mem_dvd_foldr_mul {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
    a ∣ l.foldr (· * ·) 1 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      rw [List.mem_cons] at ha
      cases ha with
      | inl h =>
          subst b
          simp
      | inr h =>
          exact dvd_mul_of_dvd_right (ih h) b

private lemma List.foldr_mul_pos {l : List ℕ}
    (hpos : ∀ a ∈ l, 0 < a) : 0 < l.foldr (· * ·) 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldr_cons]
      exact Nat.mul_pos (hpos a (by simp)) (ih (by
        intro b hb
        exact hpos b (by simp [hb])))

private lemma List.coprime_foldr_mul_of_forall
    {P : ℕ} {Ps : List ℕ} (hcop_all : ∀ Q ∈ Ps, Nat.Coprime P Q) :
    Nat.Coprime P (Ps.foldr (· * ·) 1) := by
  induction Ps with
  | nil =>
      simp
  | cons Q Qs ih =>
      simp only [List.foldr_cons]
      exact Nat.Coprime.mul_right (hcop_all Q (by simp)) (ih (by
        intro R hR
        exact hcop_all R (by simp [hR])))

private lemma sum_inv_sq_range_le_two (m : ℕ) :
    ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤ 2 := by
  have hstrong : ∀ m : ℕ, 1 ≤ m →
      ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤
        2 - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero =>
        cases hm
    | succ m ih =>
        cases m with
        | zero =>
            norm_num
        | succ m =>
            rw [Finset.sum_range_succ]
            have ih' : ∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2)
                ≤ 2 - 1 / ((m + 1 : ℕ) : ℝ) :=
              ih (by omega)
            have hstep :
                (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
                  1 / ((m + 1 : ℕ) : ℝ) -
                    1 / (((m + 1 : ℕ) : ℝ) + 1) := by
              have hm1 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
              have hm2 : 0 < ((m + 1 : ℕ) : ℝ) + 1 := by positivity
              field_simp [hm1.ne', hm2.ne']
              ring_nf
              nlinarith [show 0 ≤ (m : ℝ) by positivity]
            calc
              (∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2))
                  + 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ 2
                  ≤ (2 - 1 / ((m + 1 : ℕ) : ℝ))
                      + (1 / ((m + 1 : ℕ) : ℝ) -
                        1 / (((m + 1 : ℕ) : ℝ) + 1)) := by
                    gcongr
              _ = 2 - 1 / ((m + 2 : ℕ) : ℝ) := by
                    norm_num
                    ring
  by_cases hm : m = 0
  · simp [hm]
  · have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
    exact (hstrong m hm1).trans (by
      have hnonneg : 0 ≤ (1 : ℝ) / (m : ℝ) := by positivity
      linarith)

private lemma one_div_sq_nat_prod {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    (1 : ℝ) / (((∏ i, f i : ℕ) : ℝ) ^ 2) =
      ∏ i, (1 : ℝ) / (((f i : ℕ) : ℝ) ^ 2) := by
  simp [one_div, Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_pow]

/-! ## §1 The chain state -/

/-- Snapshot of the chain after `r` selection steps. -/
structure ChainState (N : ℕ) (D : PrunedData N) where
  /-- Number of completed steps. -/
  r : ℕ
  /-- The selected prime-power blocks `P_1, …, P_r`. -/
  blocks : List ℕ
  blocks_length : blocks.length = r
  /-- Survivors of the chain. Subset of the pruned family. -/
  Qsurv : Finset ℕ
  Qsurv_subset : Qsurv ⊆ D.Q
  Qsurv_nonempty : Qsurv.Nonempty
  /-- Total exponent count `W = ω(P_{≤r})`. -/
  W : ℕ
  /-- The product of all selected blocks. -/
  productP : ℕ
  product_eq : productP = (blocks.foldr (· * ·) 1)
  blocks_pos : ∀ P ∈ blocks, 0 < P
  productP_pos : 0 < productP
  /-- Selected blocks are pairwise coprime — equivalently, their prime
  supports are pairwise disjoint. -/
  pairwise_coprime : blocks.Pairwise Nat.Coprime
  /-- Every surviving modulus has `productP` as an *exact* divisor, i.e. no
  prime in `primeSupport productP` survives in `q / productP`. -/
  exact_divides : ∀ q ∈ Qsurv, productP ∣ q
  no_selected_prime_remains :
    ∀ q ∈ Qsurv, ∀ p ∈ primeSupport productP,
      p ∉ primeSupport (q / productP)
  /-- All surviving moduli agree on residues modulo `productP`. -/
  residues_agree :
    ∀ qi ∈ Qsurv, ∀ rj ∈ Qsurv,
      ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
        D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (productP : ℤ)]
  W_eq : W = omega productP
  W_le_K : W ≤ D.K

/-- Every selected block contributes at least one prime. This is true for
states produced by the descending-chain constructors, but kept as a predicate
rather than a structure field so basic APIs can still talk about arbitrary
chain states. -/
def ChainState.BlocksOmegaPos {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : Prop :=
  ∀ P ∈ S.blocks, 1 ≤ omega P

lemma ChainState.Qsurv_card_pos {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : 0 < S.Qsurv.card :=
  S.Qsurv_nonempty.card_pos

lemma ChainState.productP_le_of_mem {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    S.productP ≤ q := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1
  exact Nat.le_of_dvd hqpos (S.exact_divides q hq)

lemma ChainState.productP_hExp_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    (hExp S.productP : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rcases S.Qsurv_nonempty with ⟨q, hq⟩
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqne : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hle_nat : hExp S.productP ≤ hExp q :=
    hExp_le_of_dvd (S.exact_divides q hq) hqne
  have hle_real : (hExp S.productP : ℝ) ≤ (hExp q : ℝ) := by
    exact_mod_cast hle_nat
  exact hle_real.trans (D.hExp_bound q hqD)

lemma ChainState.block_dvd_productP {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {B : ℕ} (hB : B ∈ S.blocks) : B ∣ S.productP := by
  rw [S.product_eq]
  exact List.mem_dvd_foldr_mul hB

lemma ChainState.selected_remaining_disjoint {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    Disjoint (primeSupport S.productP) (remainingSupport S.productP q) := by
  rw [Finset.disjoint_left]
  intro p hpP hpRem
  exact S.no_selected_prime_remains q hq p hpP hpRem

lemma ChainState.remainingSupport_card_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    (remainingSupport S.productP q).card = D.K - S.W := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqpos : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have homega :
      omega (q / S.productP) = omega q - omega S.productP :=
    omega_div_eq_sub_omega_of_dvd (S.exact_divides q hq)
      S.productP_pos.ne' hqpos (S.selected_remaining_disjoint hq)
  calc
    (remainingSupport S.productP q).card = omega (q / S.productP) := by
      simp [remainingSupport, omega]
    _ = omega q - omega S.productP := homega
    _ = D.K - S.W := by
      rw [D.omega_eq q hqD, ← S.W_eq]

lemma ChainState.remainingSupport_nonempty_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K)
    {q : ℕ} (hq : q ∈ S.Qsurv) :
    (remainingSupport S.productP q).Nonempty := by
  rw [← Finset.card_pos, S.remainingSupport_card_eq hq]
  omega

lemma ChainState.remainingSupport_card_pos_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K)
    {q : ℕ} (hq : q ∈ S.Qsurv) :
    0 < (remainingSupport S.productP q).card := by
  exact (S.remainingSupport_nonempty_of_room hRoom hq).card_pos

lemma ChainState.gcd_dvd_productP_of_disjoint_remaining {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q r : ℕ} (hq : q ∈ S.Qsurv) (hr : r ∈ S.Qsurv)
    (hdisj : Disjoint (remainingSupport S.productP q) (remainingSupport S.productP r)) :
    Nat.gcd q r ∣ S.productP := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hrD : r ∈ D.Q := S.Qsurv_subset hr
  have hqpos : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hrpos : r ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 r hrD).1).ne'
  exact gcd_dvd_of_disjoint_remainingSupport
    (S.exact_divides q hq) (S.exact_divides r hr)
    S.productP_pos.ne' hqpos hrpos hdisj

lemma ChainState.remainingSupport_not_disjoint_of_ne {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q r : ℕ} (hq : q ∈ S.Qsurv) (hr : r ∈ S.Qsurv)
    (hqr : q ≠ r) :
    ¬ Disjoint (remainingSupport S.productP q) (remainingSupport S.productP r) := by
  intro hdisj
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hrD : r ∈ D.Q := S.Qsurv_subset hr
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one (D.admissible.1 r hrD).1
  have hgcd_dvd : Nat.gcd q r ∣ S.productP :=
    S.gcd_dvd_productP_of_disjoint_remaining hq hr hdisj
  have hmodP := S.residues_agree q hq r hr hqD hrD
  have hmodG :
      D.a ⟨q, hqD⟩ ≡ D.a ⟨r, hrD⟩ [ZMOD (Nat.gcd q r : ℤ)] := by
    rw [Int.modEq_iff_dvd] at hmodP ⊢
    have hgcd_dvd_int : (Nat.gcd q r : ℤ) ∣ (S.productP : ℤ) := by
      exact_mod_cast hgcd_dvd
    exact dvd_trans hgcd_dvd_int hmodP
  have hres_disj :
      Disjoint (residueClass q (D.a ⟨q, hqD⟩))
        (residueClass r (D.a ⟨r, hrD⟩)) :=
    D.pairwise_disjoint ⟨q, hqD⟩ ⟨r, hrD⟩ (by
      intro hsub
      exact hqr (Subtype.ext_iff.mp hsub))
  exact ((residueClass_disjoint_iff hqpos hrpos
    (D.a ⟨q, hqD⟩) (D.a ⟨r, hrD⟩)).1 hres_disj) hmodG

/-- The family of remaining prime supports of surviving moduli. -/
def ChainState.remainingSupportFamily {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : Finset (Finset ℕ) :=
  S.Qsurv.image (fun q => remainingSupport S.productP q)

lemma ChainState.remainingSupportFamily_nonempty {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : S.remainingSupportFamily.Nonempty := by
  rcases S.Qsurv_nonempty with ⟨q, hq⟩
  exact ⟨remainingSupport S.productP q, Finset.mem_image.2 ⟨q, hq, rfl⟩⟩

lemma ChainState.remainingSupportFamily_card_le {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    S.remainingSupportFamily.card ≤ S.Qsurv.card := by
  rw [ChainState.remainingSupportFamily]
  exact Finset.card_image_le

lemma ChainState.remainingSupport_injOn_Qsurv {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    Set.InjOn (fun q => remainingSupport S.productP q) S.Qsurv := by
  intro q hq r hr hqr
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hrD : r ∈ D.Q := S.Qsurv_subset hr
  have hqne : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hrne : r ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 r hrD).1).ne'
  have hqsupp :
      primeSupport q = primeSupport S.productP ∪ remainingSupport S.productP q :=
    primeSupport_eq_union_of_dvd (S.exact_divides q hq) S.productP_pos.ne' hqne
  have hrsupp :
    primeSupport r = primeSupport S.productP ∪ remainingSupport S.productP r :=
    primeSupport_eq_union_of_dvd (S.exact_divides r hr) S.productP_pos.ne' hrne
  have hsupp : primeSupport q = primeSupport r := by
    change remainingSupport S.productP q = remainingSupport S.productP r at hqr
    rw [hqsupp, hrsupp, hqr]
  have hrad : rad q = rad r := by
    unfold rad
    rw [hsupp]
  exact D.rad_injective q hqD r hrD hrad

lemma ChainState.remainingSupportFamily_card_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    S.remainingSupportFamily.card = S.Qsurv.card := by
  rw [ChainState.remainingSupportFamily]
  exact Finset.card_image_of_injOn (fun q hq r hr hqr =>
    S.remainingSupport_injOn_Qsurv hq hr hqr)

/-- Survivors whose remaining support contains a fixed core. -/
def ChainState.coreSurvivors {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) : Finset ℕ :=
  S.Qsurv.filter fun q => C ⊆ remainingSupport S.productP q

/-- Exact prime-power block values attached to a fixed core. -/
def ChainState.coreBlocks {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) : Finset ℕ :=
  (S.coreSurvivors C).image (fun q => exactBlock C q)

/-- Weighted pigeonhole on exact block values carried by a fixed core. This
is the formal selection step for the paper's attained value `P_r`, before
the subsequent residue-class pigeonhole. -/
lemma ChainState.exists_coreBlock_weighted_share {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ)
    (hCore : (S.coreSurvivors C).Nonempty) :
    ∃ P ∈ S.coreBlocks C,
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) := by
  classical
  rw [ChainState.coreBlocks]
  exact exists_fiber_weighted_share (S.coreSurvivors C) (fun q => exactBlock C q)
    (fun P => (1 : ℝ) / ((hExp P : ℝ) ^ 2)) hCore (by
      intro P _hP
      exact hExp_inv_sq_pos P)

/-- Quotients `q / productP` for survivors carrying a fixed core. -/
def ChainState.coreQuotients {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) : Finset ℕ :=
  (S.coreSurvivors C).image (fun q => q / S.productP)

lemma ChainState.remainingSupportFamily_filter_subset_coreImage {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    (S.remainingSupportFamily.filter fun A => C ⊆ A) ⊆
      (S.coreSurvivors C).image (fun q => remainingSupport S.productP q) := by
  intro A hA
  rw [ChainState.remainingSupportFamily] at hA
  rw [Finset.mem_filter] at hA
  rcases Finset.mem_image.mp hA.1 with ⟨q, hq, rfl⟩
  exact Finset.mem_image.2 ⟨q, by
    rw [ChainState.coreSurvivors, Finset.mem_filter]
    exact ⟨hq, hA.2⟩, rfl⟩

lemma ChainState.remainingSupportFamily_filter_card_le_coreSurvivors {N : ℕ}
    {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ) :
    (S.remainingSupportFamily.filter fun A => C ⊆ A).card ≤
      (S.coreSurvivors C).card := by
  exact (Finset.card_le_card (S.remainingSupportFamily_filter_subset_coreImage C)).trans
    Finset.card_image_le

lemma ChainState.quotient_injOn_Qsurv {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    Set.InjOn (fun q => q / S.productP) S.Qsurv := by
  intro q hq r hr hqr
  have hqmul := Nat.div_mul_cancel (S.exact_divides q hq)
  have hrmul := Nat.div_mul_cancel (S.exact_divides r hr)
  calc
    q = (q / S.productP) * S.productP := hqmul.symm
    _ = (r / S.productP) * S.productP := by
      exact congrArg (fun x => x * S.productP) hqr
    _ = r := hrmul

lemma ChainState.coreQuotients_card {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    (S.coreQuotients C).card = (S.coreSurvivors C).card := by
  rw [ChainState.coreQuotients]
  exact Finset.card_image_of_injOn fun q hq r hr hqr =>
    S.quotient_injOn_Qsurv (Finset.mem_filter.1 hq).1
      (Finset.mem_filter.1 hr).1 hqr

lemma ChainState.coreQuotients_subset_omegaCount {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    S.coreQuotients C ⊆
      (Finset.Icc 1 N).filter (fun n => omega n = D.K - S.W) := by
  intro n hn
  rw [ChainState.coreQuotients] at hn
  rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
  have hqsurv : q ∈ S.Qsurv := (Finset.mem_filter.1 hq).1
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.succ_le_of_lt (Nat.div_pos (S.productP_le_of_mem hqsurv) S.productP_pos),
      (Nat.div_le_self q S.productP).trans (D.modulus_upper q hqD)⟩,
    S.remainingSupport_card_eq hqsurv⟩

lemma ChainState.coreSurvivors_card_le_omegaCount {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    (S.coreSurvivors C).card ≤
      ((Finset.Icc 1 N).filter (fun n => omega n = D.K - S.W)).card := by
  rw [← S.coreQuotients_card C]
  exact Finset.card_le_card (S.coreQuotients_subset_omegaCount C)

lemma ChainState.coreSurvivors_card_le_bfv_omega_count
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    (S.coreSurvivors C).card ≤
      Nat.floor
        ((N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) := by
  exact (S.coreSurvivors_card_le_omegaCount C).trans
    (hCount N D.K S.W le_rfl S.W_le_K D.K_bound)

lemma ChainState.coreSurvivors_card_real_le_bfv_omega_count
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((S.coreSurvivors C).card : ℝ) ≤
      (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  apply nat_cast_le_of_le_floor
  · positivity
  · exact S.coreSurvivors_card_le_bfv_omega_count C ε hCount

lemma ChainState.coreSurvivors_subset {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    S.coreSurvivors C ⊆ S.Qsurv := by
  intro q hq
  exact (Finset.mem_filter.1 hq).1

lemma ChainState.core_subset_remainingSupport {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    C ⊆ remainingSupport S.productP q :=
  (Finset.mem_filter.1 hq).2

lemma ChainState.exactBlock_eq_quotient_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    exactBlock C q = exactBlock C (q / S.productP) := by
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hC : C ⊆ remainingSupport S.productP q :=
    S.core_subset_remainingSupport hq
  apply exactBlock_congr_on
  intro p hpC
  have hpRem : p ∈ remainingSupport S.productP q := hC hpC
  have hpNotP : p ∉ primeSupport S.productP := by
    intro hpP
    exact (Finset.disjoint_left.1 (S.selected_remaining_disjoint hqsurv)) hpP hpRem
  have hPzero : S.productP.factorization p = 0 := by
      unfold primeSupport at hpNotP
      exact Finsupp.notMem_support_iff.1 hpNotP
  rw [Nat.factorization_div (S.exact_divides q hqsurv)]
  simp [Finsupp.coe_tsub, hPzero]

lemma ChainState.quotient_pos_of_mem {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    0 < q / S.productP := by
  exact Nat.div_pos (S.productP_le_of_mem hq) S.productP_pos

lemma ChainState.exactBlock_dvd_quotient_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    exactBlock C q ∣ q / S.productP := by
  rw [S.exactBlock_eq_quotient_of_core hq]
  exact exactBlock_dvd C (q / S.productP)

lemma ChainState.exactBlock_pos_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    0 < exactBlock C q := by
  exact Nat.pos_of_dvd_of_pos (S.exactBlock_dvd_quotient_of_core hq)
    (S.quotient_pos_of_mem (S.coreSurvivors_subset C hq))

lemma ChainState.primeSupport_exactBlock_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    primeSupport (exactBlock C q) = C := by
  have hC : C ⊆ remainingSupport S.productP q :=
    S.core_subset_remainingSupport hq
  rw [S.exactBlock_eq_quotient_of_core hq]
  exact primeSupport_exactBlock
    (fun p hp => prime_of_mem_primeSupport (hC hp))
    hC

lemma ChainState.omega_exactBlock_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    omega (exactBlock C q) = C.card := by
  simp [omega, S.primeSupport_exactBlock_of_core hq]

lemma ChainState.product_mul_exactBlock_dvd_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    S.productP * exactBlock C q ∣ q := by
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  rcases S.exactBlock_dvd_quotient_of_core hq with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have hdiv := Nat.div_mul_cancel (S.exact_divides q hqsurv)
  calc
    q = q / S.productP * S.productP := hdiv.symm
    _ = exactBlock C q * t * S.productP := by rw [ht]
    _ = S.productP * exactBlock C q * t := by ring

lemma ChainState.productP_coprime_exactBlock_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    Nat.Coprime S.productP (exactBlock C q) := by
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hC : C ⊆ remainingSupport S.productP q :=
    S.core_subset_remainingSupport hq
  have hsupport : primeSupport (exactBlock C q) = C :=
    S.primeSupport_exactBlock_of_core hq
  refine coprime_of_disjoint_primeSupport S.productP_pos.ne'
    (S.exactBlock_pos_of_core hq).ne' ?_
  rw [hsupport]
  rw [Finset.disjoint_left]
  intro p hpP hpC
  exact (Finset.disjoint_left.1 (S.selected_remaining_disjoint hqsurv)) hpP (hC hpC)

lemma ChainState.coreBlock_pos {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : 0 < P := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.exactBlock_pos_of_core hq

lemma ChainState.coreBlock_coprime_productP {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : Nat.Coprime S.productP P := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.productP_coprime_exactBlock_of_core hq

lemma ChainState.coreBlock_omega_eq_card {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : omega P = C.card := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.omega_exactBlock_of_core hq

lemma ChainState.coreBlock_primeSupport_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : primeSupport P = C := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.primeSupport_exactBlock_of_core hq

lemma ChainState.product_mul_coreBlock_dvd {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P q : ℕ}
    (hq : q ∈ (S.coreSurvivors C).filter fun q => exactBlock C q = P) :
    S.productP * P ∣ q := by
  have hqcore : q ∈ S.coreSurvivors C := (Finset.mem_filter.1 hq).1
  have hP : exactBlock C q = P := (Finset.mem_filter.1 hq).2
  simpa [hP] using S.product_mul_exactBlock_dvd_of_core hqcore

lemma ChainState.product_mul_coreBlock_no_selected_prime_remains
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P q : ℕ}
    (hq : q ∈ (S.coreSurvivors C).filter fun q => exactBlock C q = P) :
    ∀ p ∈ primeSupport (S.productP * P), p ∉ primeSupport (q / (S.productP * P)) := by
  intro p hpNew hpRem
  have hqcore : q ∈ S.coreSurvivors C := (Finset.mem_filter.1 hq).1
  have hP : exactBlock C q = P := (Finset.mem_filter.1 hq).2
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hqcore
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  have hqne : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hPmem : P ∈ S.coreBlocks C := by
    rw [ChainState.coreBlocks]
    exact Finset.mem_image.2 ⟨q, hqcore, hP⟩
  have hcop : Nat.Coprime S.productP P := S.coreBlock_coprime_productP hPmem
  have hnewdvd : S.productP * P ∣ q := S.product_mul_coreBlock_dvd hq
  have hltNew : (S.productP * P).factorization p < q.factorization p :=
    (mem_remainingSupport_iff_factorization_lt hnewdvd).1 hpRem
  have hsupportNew :
      primeSupport (S.productP * P) = primeSupport S.productP ∪ primeSupport P :=
    primeSupport_mul_of_coprime hcop
  have hfacNew : (S.productP * P).factorization p =
      S.productP.factorization p + P.factorization p := by
    rw [Nat.factorization_mul_of_coprime hcop]
    rfl
  rw [hsupportNew, Finset.mem_union] at hpNew
  cases hpNew with
  | inl hpOld =>
      have hpNotRemOld : p ∉ primeSupport (q / S.productP) :=
        S.no_selected_prime_remains q hqsurv p hpOld
      have hnotltOld : ¬ S.productP.factorization p < q.factorization p := by
        intro hlt
        exact hpNotRemOld
          ((mem_remainingSupport_iff_factorization_lt (S.exact_divides q hqsurv)).2 hlt)
      have hleOld : S.productP.factorization p ≤ q.factorization p :=
        (Nat.factorization_le_iff_dvd S.productP_pos.ne' hqne).2
          (S.exact_divides q hqsurv) p
      have hq_le_old : q.factorization p ≤ S.productP.factorization p :=
        le_of_not_gt hnotltOld
      have hEqOld : S.productP.factorization p = q.factorization p :=
        le_antisymm hleOld hq_le_old
      have hpNotP : p ∉ primeSupport P :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hpOld
      have hPzero : P.factorization p = 0 := by
        unfold primeSupport at hpNotP
        exact Finsupp.notMem_support_iff.1 hpNotP
      rw [hfacNew, hPzero, add_zero, hEqOld] at hltNew
      exact lt_irrefl _ hltNew
  | inr hpP =>
      have hsupportP : primeSupport P = C := by
        rw [← hP]
        exact S.primeSupport_exactBlock_of_core hqcore
      have hpC : p ∈ C := by
        simpa [hsupportP] using hpP
      have hpNotOld : p ∉ primeSupport S.productP := by
        intro hpOld
        exact (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hpOld hpP
      have hOldzero : S.productP.factorization p = 0 := by
        unfold primeSupport at hpNotOld
        exact Finsupp.notMem_support_iff.1 hpNotOld
      have hCprime : ∀ r ∈ C, Nat.Prime r := by
        intro r hr
        exact prime_of_mem_primeSupport (S.core_subset_remainingSupport hqcore hr)
      have hPfac : P.factorization p = q.factorization p := by
        rw [← hP]
        exact factorization_exactBlock_of_mem hCprime hpC
      rw [hfacNew, hOldzero, zero_add, hPfac] at hltNew
      exact lt_irrefl _ hltNew

lemma ChainState.coreBlock_card_le_remaining {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : C.card ≤ D.K - S.W := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact (Finset.card_le_card (S.core_subset_remainingSupport hq)).trans_eq
    (S.remainingSupport_card_eq (S.coreSurvivors_subset C hq))

lemma ChainState.omega_product_mul_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    omega (S.productP * P) = S.W + C.card := by
  rw [omega_mul_of_coprime (S.coreBlock_coprime_productP hP), ← S.W_eq,
    S.coreBlock_omega_eq_card hP]

lemma ChainState.selectedFiber_card_real_le_bfv_omega_count_div
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ} (hP : P ∈ S.coreBlocks C) (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ) ≤
      ((N / (S.productP * P) : ℕ) : ℝ) *
        Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  classical
  let T : Finset ℕ := (S.coreSurvivors C).filter fun q => exactBlock C q = P
  let dP : ℕ := S.productP * P
  let quotient : ℕ → ℕ := fun q => q / dP
  have hdP_pos : 0 < dP := by
    dsimp [dP]
    exact Nat.mul_pos S.productP_pos (S.coreBlock_pos hP)
  have hWle : S.W + C.card ≤ D.K := by
    have hcard := S.coreBlock_card_le_remaining hP
    have hWK := S.W_le_K
    omega
  have hinj : Set.InjOn quotient T := by
    intro q hq r hr hqr
    have hq_dvd : dP ∣ q := by
      dsimp [dP]
      exact S.product_mul_coreBlock_dvd (by simpa [T] using hq)
    have hr_dvd : dP ∣ r := by
      dsimp [dP]
      exact S.product_mul_coreBlock_dvd (by simpa [T] using hr)
    calc
      q = quotient q * dP := (Nat.div_mul_cancel hq_dvd).symm
      _ = quotient r * dP := by rw [hqr]
      _ = r := Nat.div_mul_cancel hr_dvd
  have hsubset :
      T.image quotient ⊆
        (Finset.Icc 1 (N / dP)).filter (fun n => omega n = D.K - (S.W + C.card)) := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨q, hqT, rfl⟩
    have hqT' : q ∈ (S.coreSurvivors C).filter fun q => exactBlock C q = P := by
      simpa [T] using hqT
    have hqcore : q ∈ S.coreSurvivors C := (Finset.mem_filter.1 hqT').1
    have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hqcore
    have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
    have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1
    have hqne : q ≠ 0 := hqpos.ne'
    have hdvd : dP ∣ q := by
      dsimp [dP]
      exact S.product_mul_coreBlock_dvd hqT'
    have hdisj : Disjoint (primeSupport dP) (primeSupport (q / dP)) := by
      rw [Finset.disjoint_left]
      intro p hp hqrem
      exact S.product_mul_coreBlock_no_selected_prime_remains hqT' p (by simpa [dP] using hp)
        (by simpa [dP] using hqrem)
    have homega :
        omega (q / dP) = D.K - (S.W + C.card) := by
      calc
        omega (q / dP) = omega q - omega dP :=
          omega_div_eq_sub_omega_of_dvd hdvd hdP_pos.ne' hqne hdisj
        _ = D.K - (S.W + C.card) := by
          rw [D.omega_eq q hqD, show omega dP = S.W + C.card by
            dsimp [dP]
            exact S.omega_product_mul_coreBlock hP]
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hqpos hdvd) hdP_pos),
      Nat.div_le_div_right (D.modulus_upper q hqD)⟩, homega⟩
  have hcard : T.card ≤
      ((Finset.Icc 1 (N / dP)).filter (fun n => omega n = D.K - (S.W + C.card))).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsubset
  have hcount := hCount (N / dP) D.K (S.W + C.card) (Nat.div_le_self N dP) hWle D.K_bound
  dsimp only at hcount
  have hfloor :
      T.card ≤ Nat.floor
        (((N / dP : ℕ) : ℝ) *
          Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ)))) :=
    hcard.trans hcount
  simpa [T, dP] using nat_cast_le_of_le_floor (by positivity) hfloor

lemma ChainState.selectedFiber_card_real_le_bfv_omega_count
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ} (hP : P ∈ S.coreBlocks C) (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ) ≤
      ((N : ℝ) / (S.productP * P : ℝ)) *
        Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  have hdiv := S.selectedFiber_card_real_le_bfv_omega_count_div hP ε hCount
  have hquot :
      ((N / (S.productP * P) : ℕ) : ℝ) ≤ (N : ℝ) / (S.productP * P : ℝ) :=
    by
      simpa [Nat.cast_mul] using
        (Nat.cast_div_le (m := N) (n := S.productP * P) : ((N / (S.productP * P) : ℕ) : ℝ) ≤
          (N : ℝ) / ((S.productP * P : ℕ) : ℝ))
  have hfactor_nonneg :
      0 ≤ Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
    positivity
  calc
    ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ)
        ≤ ((N / (S.productP * P) : ℕ) : ℝ) *
            Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
            Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
              Real.log (Real.log (N : ℝ))) := hdiv
    _ = ((N / (S.productP * P) : ℕ) : ℝ) *
            (Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
              Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
                Real.log (Real.log (N : ℝ)))) := by ring
    _ ≤ ((N : ℝ) / (S.productP * P : ℝ)) *
            (Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
              Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
                Real.log (Real.log (N : ℝ)))) := by
          exact mul_le_mul_of_nonneg_right hquot hfactor_nonneg
    _ = ((N : ℝ) / (S.productP * P : ℝ)) *
            Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
            Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
              Real.log (Real.log (N : ℝ))) := by ring

lemma ChainState.W_add_coreBlock_card_le_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : S.W + C.card ≤ D.K := by
  have hcard := S.coreBlock_card_le_remaining hP
  have hW := S.W_le_K
  omega

lemma ChainState.productP_eq_of_W_eq_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hW : S.W = D.K) {q : ℕ} (hq : q ∈ S.Qsurv) :
    S.productP = q := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqdivpos : q / S.productP ≠ 0 := (S.quotient_pos_of_mem hq).ne'
  have hremcard : (remainingSupport S.productP q).card = 0 := by
    rw [S.remainingSupport_card_eq hq, hW]
    simp
  have homega : omega (q / S.productP) = 0 := by
    simpa [remainingSupport, omega] using hremcard
  have hquot : q / S.productP = 1 := eq_one_of_omega_eq_zero hqdivpos homega
  have hdiv := Nat.div_mul_cancel (S.exact_divides q hq)
  calc
    S.productP = 1 * S.productP := by simp
    _ = q / S.productP * S.productP := by rw [hquot]
    _ = q := hdiv

lemma ChainState.productP_lower_of_W_eq_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hW : S.W = D.K) :
    (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) := by
  rcases S.Qsurv_nonempty with ⟨q, hq⟩
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hpq := S.productP_eq_of_W_eq_K hW hq
  rw [hpq]
  exact D.modulus_lower q hqD

lemma ChainState.pairwise_cons_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : (P :: S.blocks).Pairwise Nat.Coprime := by
  rw [List.pairwise_cons]
  constructor
  · intro B hB
    exact Nat.Coprime.of_dvd_right (S.block_dvd_productP hB)
      (S.coreBlock_coprime_productP hP).symm
  · exact S.pairwise_coprime

lemma ChainState.extend_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ} {Qnext : Finset ℕ}
    (hP : P ∈ S.coreBlocks C)
    (hQnext_nonempty : Qnext.Nonempty)
    (hQnext_subset : Qnext ⊆ (S.coreSurvivors C).filter fun q => exactBlock C q = P)
    (hResiduesP :
      ∀ qi ∈ Qnext, ∀ rj ∈ Qnext,
        ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
          D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (P : ℤ)]) :
    ∃ S' : ChainState N D,
      S'.blocks = P :: S.blocks ∧ S'.r = S.r + 1 ∧ S'.productP = P * S.productP ∧
        S'.Qsurv = Qnext ∧ S'.W = S.W + C.card := by
  classical
  refine ⟨{
    r := S.r + 1
    blocks := P :: S.blocks
    blocks_length := by simp [S.blocks_length]
    Qsurv := Qnext
    Qsurv_subset := ?_
    Qsurv_nonempty := hQnext_nonempty
    W := S.W + C.card
    productP := P * S.productP
    product_eq := by simp [S.product_eq]
    blocks_pos := ?_
    productP_pos := ?_
    pairwise_coprime := S.pairwise_cons_coreBlock hP
    exact_divides := ?_
    no_selected_prime_remains := ?_
    residues_agree := ?_
    W_eq := ?_
    W_le_K := S.W_add_coreBlock_card_le_K hP
  }, rfl, rfl, rfl, rfl, rfl⟩
  · intro q hq
    exact S.Qsurv_subset (S.coreSurvivors_subset C
      (Finset.mem_filter.1 (hQnext_subset hq)).1)
  · intro B hB
    rw [List.mem_cons] at hB
    cases hB with
    | inl h =>
        subst B
        exact S.coreBlock_pos hP
    | inr h => exact S.blocks_pos B h
  · exact mul_pos (S.coreBlock_pos hP) S.productP_pos
  · intro q hq
    have hfiber := hQnext_subset hq
    have hdvd := S.product_mul_coreBlock_dvd hfiber
    simpa [Nat.mul_comm] using hdvd
  · intro q hq p hp
    have hfiber := hQnext_subset hq
    have hno := S.product_mul_coreBlock_no_selected_prime_remains hfiber p
    simpa [Nat.mul_comm] using hno (by simpa [Nat.mul_comm] using hp)
  · intro qi hqi rj hrj hqiD hrjD
    have hqicore : qi ∈ S.coreSurvivors C :=
      (Finset.mem_filter.1 (hQnext_subset hqi)).1
    have hrjcore : rj ∈ S.coreSurvivors C :=
      (Finset.mem_filter.1 (hQnext_subset hrj)).1
    have hqiSurv : qi ∈ S.Qsurv := S.coreSurvivors_subset C hqicore
    have hrjSurv : rj ∈ S.Qsurv := S.coreSurvivors_subset C hrjcore
    have hOld := S.residues_agree qi hqiSurv rj hrjSurv hqiD hrjD
    have hNew := hResiduesP qi hqi rj hrj hqiD hrjD
    have hcopInt : (S.productP : ℤ).natAbs.Coprime (P : ℤ).natAbs := by
      simpa using S.coreBlock_coprime_productP hP
    have hBoth :
        D.a ⟨qi, hqiD⟩ ≡ D.a ⟨rj, hrjD⟩ [ZMOD (S.productP : ℤ)] ∧
        D.a ⟨qi, hqiD⟩ ≡ D.a ⟨rj, hrjD⟩ [ZMOD (P : ℤ)] := ⟨hOld, hNew⟩
    have hMul := (Int.modEq_and_modEq_iff_modEq_mul hcopInt).1 hBoth
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hMul
  · rw [Nat.mul_comm]
    exact (S.omega_product_mul_coreBlock hP).symm

lemma ChainState.exists_residue_subfamily {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    ∃ Qnext : Finset ℕ,
      Qnext.Nonempty ∧
      Qnext ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      (∀ qi ∈ Qnext, ∀ rj ∈ Qnext,
        ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
          D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (P : ℤ)]) ∧
      (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) /
          (P : ℝ) ≤ (Qnext.card : ℝ) := by
  classical
  let T : Finset ℕ := (S.coreSurvivors C).filter fun q => exactBlock C q = P
  let residue : ℕ → ZMod P :=
    fun q => if hq : q ∈ D.Q then (D.a ⟨q, hq⟩ : ZMod P) else 0
  have hPpos : 0 < P := S.coreBlock_pos hP
  haveI : NeZero P := ⟨hPpos.ne'⟩
  have hTnonempty : T.Nonempty := by
    dsimp [T]
    rw [ChainState.coreBlocks] at hP
    exact fiber_nonempty_of_mem_image (S := S.coreSurvivors C)
      (B := fun q => exactBlock C q) hP
  rcases exists_zmod_fiber_card_div_le T P residue hTnonempty with ⟨b, hb⟩
  let Qnext : Finset ℕ := T.filter fun q => residue q = b
  refine ⟨Qnext, ?_, ?_, ?_, ?_⟩
  · have hratio_pos : 0 < (T.card : ℝ) / (P : ℝ) := by
      have hTcard : 0 < (T.card : ℝ) := by exact_mod_cast hTnonempty.card_pos
      have hPreal : 0 < (P : ℝ) := by exact_mod_cast hPpos
      exact div_pos hTcard hPreal
    have hQreal : 0 < (Qnext.card : ℝ) := lt_of_lt_of_le hratio_pos hb
    exact Finset.card_pos.1 (by exact_mod_cast hQreal)
  · intro q hq
    exact (Finset.mem_filter.1 hq).1
  · intro qi hqi rj hrj hqiD hrjD
    have hqiResidue : residue qi = b := (Finset.mem_filter.1 hqi).2
    have hrjResidue : residue rj = b := (Finset.mem_filter.1 hrj).2
    have hqiCast : ((D.a ⟨qi, hqiD⟩ : ℤ) : ZMod P) = b := by
      simpa [residue, hqiD] using hqiResidue
    have hrjCast : ((D.a ⟨rj, hrjD⟩ : ℤ) : ZMod P) = b := by
      simpa [residue, hrjD] using hrjResidue
    have hcast : ((D.a ⟨qi, hqiD⟩ : ℤ) : ZMod P) =
        ((D.a ⟨rj, hrjD⟩ : ℤ) : ZMod P) := hqiCast.trans hrjCast.symm
    exact (ZMod.intCast_eq_intCast_iff
      (D.a ⟨qi, hqiD⟩) (D.a ⟨rj, hrjD⟩) P).1 hcast
  · simpa [T, Qnext] using hb

lemma ChainState.exists_extended_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    ∃ S' : ChainState N D,
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) := by
  rcases S.exists_residue_subfamily hP with
    ⟨Qnext, hQnext_nonempty, hQnext_subset, hResiduesP, hcard⟩
  rcases S.extend_coreBlock hP hQnext_nonempty hQnext_subset hResiduesP with
    ⟨S', hblocks, hr, hprod, hQsurv, hW⟩
  have hsubset : S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) := by
    intro q hq
    rw [hQsurv] at hq
    exact hQnext_subset hq
  exact ⟨S', hblocks, hr, hprod, hsubset, Finset.card_le_card hsubset, hW,
    by simpa [hQsurv] using hcard⟩

lemma ChainState.exists_weighted_extended_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) :
    ∃ P : ℕ, ∃ S' : ChainState N D,
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) := by
  rcases S.exists_coreBlock_weighted_share C hCore with ⟨P, hP, hshare⟩
  rcases S.exists_extended_coreBlock hP with
    ⟨S', hblocks, hr, hprod, hQsubset, hQcard_le, hW, hcard⟩
  refine ⟨P, S', hP, hblocks, hr, hprod, hQsubset, hQcard_le, hW, hshare, ?_⟩
  have hPreal_nonneg : 0 ≤ (P : ℝ) := by positivity
  have hdiv_share :
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤
        ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) /
          (P : ℝ)) := by
    exact div_le_div_of_nonneg_right hshare hPreal_nonneg
  exact hdiv_share.trans hcard

lemma ChainState.coreBlocks_subset_omegaCount {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    S.coreBlocks C ⊆
      (Finset.Icc 1 N).filter (fun n => omega n = C.card) := by
  intro B hB
  rw [ChainState.coreBlocks] at hB
  rcases Finset.mem_image.mp hB with ⟨q, hq, rfl⟩
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  have hblock_le_quotient :
      exactBlock C q ≤ q / S.productP :=
    Nat.le_of_dvd (S.quotient_pos_of_mem hqsurv) (S.exactBlock_dvd_quotient_of_core hq)
  have hblock_le_N : exactBlock C q ≤ N := by
    exact hblock_le_quotient.trans ((Nat.div_le_self q S.productP).trans (D.modulus_upper q hqD))
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.succ_le_of_lt (S.exactBlock_pos_of_core hq), hblock_le_N⟩,
    S.omega_exactBlock_of_core hq⟩

lemma ChainState.coreBlock_le_N {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : P ≤ N := by
  have hmem := S.coreBlocks_subset_omegaCount C hP
  exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hmem).1).2

lemma ChainState.coreBlock_hExp_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  have hle_nat : hExp (exactBlock C q) ≤ hExp q := hExp_exactBlock_le_hExp C q
  have hle_real : (hExp (exactBlock C q) : ℝ) ≤ (hExp q : ℝ) := by
    exact_mod_cast hle_nat
  exact hle_real.trans (D.hExp_bound q hqD)

lemma ChainState.coreBlock_card_le_K_of_nonempty {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) : C.card ≤ D.K := by
  rcases hCore with ⟨q, hq⟩
  have hle := Finset.card_le_card (S.core_subset_remainingSupport hq)
  have heq := S.remainingSupport_card_eq (S.coreSurvivors_subset C hq)
  omega

lemma ChainState.coreBlock_card_bound_real {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) :
    (C.card : ℝ) ≤ 3 * Mscale N := by
  have hCK : (C.card : ℝ) ≤ (D.K : ℝ) := by
    exact_mod_cast S.coreBlock_card_le_K_of_nonempty hCore
  exact hCK.trans D.K_bound

lemma ChainState.coreBlocks_card_le_bfv_omega_count {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) (ε : ℝ)
    (hCore : (S.coreSurvivors C).Nonempty)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    (S.coreBlocks C).card ≤
      Nat.floor
        ((N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N)) := by
  have hsubset := S.coreBlocks_subset_omegaCount C
  have hcard : (S.coreBlocks C).card ≤
      ((Finset.Icc 1 N).filter (fun n => omega n = C.card)).card :=
    Finset.card_le_card hsubset
  have hcount := hCount N C.card 0 le_rfl (Nat.zero_le _) (S.coreBlock_card_bound_real hCore)
  dsimp only at hcount
  have hsimp :
      Nat.floor
        ((N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((0 : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) =
      Nat.floor
        ((N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N)) := by
    simp
  exact hcard.trans (by simpa [hsimp] using hcount)

lemma ChainState.coreBlocks_card_real_le_bfv_omega_count {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) (ε : ℝ)
    (hCore : (S.coreSurvivors C).Nonempty)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((S.coreBlocks C).card : ℝ) ≤
      (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N) := by
  apply nat_cast_le_of_le_floor
  · positivity
  · exact S.coreBlocks_card_le_bfv_omega_count C ε hCore hCount

lemma ChainState.remainingSupportFamily_uniform {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    UniformFamily S.remainingSupportFamily (D.K - S.W) := by
  intro A hA
  rw [ChainState.remainingSupportFamily] at hA
  rcases Finset.mem_image.mp hA with ⟨q, hq, rfl⟩
  exact S.remainingSupport_card_eq hq

lemma ChainState.remainingSupportFamily_intersecting {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    ∀ A ∈ S.remainingSupportFamily, ∀ B ∈ S.remainingSupportFamily,
      A ≠ B → ¬ Disjoint A B := by
  intro A hA B hB hAB
  rw [ChainState.remainingSupportFamily] at hA hB
  rcases Finset.mem_image.mp hA with ⟨q, hq, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨r, hr, rfl⟩
  exact S.remainingSupport_not_disjoint_of_ne hq hr (by
    intro hqr
    subst r
    exact hAB rfl)

lemma ChainState.remainingSupportFamily_rank_pos_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) : 1 ≤ D.K - S.W := by
  omega

lemma ChainState.remainingSupportFamily_rank_le_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : D.K - S.W ≤ D.K :=
  Nat.sub_le D.K S.W

lemma ChainState.remainingSupportFamily_denseCoreData {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) :
    S.remainingSupportFamily.Nonempty ∧
      1 ≤ D.K - S.W ∧
      D.K - S.W ≤ D.K ∧
      UniformFamily S.remainingSupportFamily (D.K - S.W) ∧
      (∀ A ∈ S.remainingSupportFamily, ∀ B ∈ S.remainingSupportFamily,
        A ≠ B → ¬ Disjoint A B) :=
  ⟨S.remainingSupportFamily_nonempty,
    S.remainingSupportFamily_rank_pos_of_room hRoom,
    S.remainingSupportFamily_rank_le_K,
    S.remainingSupportFamily_uniform,
    S.remainingSupportFamily_intersecting⟩

/-- A fixed dense-core constant supplied by the spread-core input. Keeping it
fixed is important for iterating the chain. This file only needs the
`α = ℕ` instance, so the universe is fixed to avoid polymorphic choice
metavariables. -/
noncomputable def denseCoreConstant : ℝ :=
  Classical.choose (dense_core_from_spread.{0})

lemma denseCoreConstant_pos : 0 < denseCoreConstant :=
  (Classical.choose_spec (dense_core_from_spread.{0})).1

lemma dense_core_from_spread_fixed_nat
    (A : Finset (Finset ℕ)) (k K : ℕ) :
    A.Nonempty →
    1 ≤ k → k ≤ K →
    UniformFamily A k →
    (∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ Disjoint S T) →
    ∃ C : Finset ℕ,
      C.Nonempty ∧
      ((A.filter fun S => C ⊆ S).card : ℝ) >
        (A.card : ℝ) /
          (denseCoreConstant * Real.log (Real.exp 1 * (K : ℝ))) ^ C.card :=
  (Classical.choose_spec (dense_core_from_spread.{0})).2 A k K

noncomputable def chainKappa {N : ℕ} (D : PrunedData N) : ℝ :=
  denseCoreConstant * Real.log (Real.exp 1 * (D.K : ℝ))

noncomputable def chainLambda {N : ℕ} (D : PrunedData N) : ℝ :=
  2 * chainKappa D

lemma chainKappa_pos {N : ℕ} (D : PrunedData N) : 0 < chainKappa D := by
  have hKreal : 1 ≤ (D.K : ℝ) := by exact_mod_cast D.K_pos
  have harg_ge : Real.exp 1 ≤ Real.exp 1 * (D.K : ℝ) := by
    nlinarith [Real.exp_pos 1, hKreal]
  have hlog_ge_one : 1 ≤ Real.log (Real.exp 1 * (D.K : ℝ)) := by
    have hlog := Real.log_le_log (Real.exp_pos 1) harg_ge
    simpa using hlog
  exact mul_pos denseCoreConstant_pos (zero_lt_one.trans_le hlog_ge_one)

lemma chainLambda_pos {N : ℕ} (D : PrunedData N) : 0 < chainLambda D := by
  dsimp [chainLambda]
  exact mul_pos (by norm_num) (chainKappa_pos D)

lemma ChainState.exists_dense_core_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∃ C : Finset ℕ,
        C.Nonempty ∧
        ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
          (S.remainingSupportFamily.card : ℝ) /
            (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card := by
  rcases dense_core_from_spread with ⟨C0, hC0, hcore⟩
  rcases S.remainingSupportFamily_denseCoreData hRoom with
    ⟨hA, hk, hkK, hUniform, hIntersect⟩
  rcases hcore S.remainingSupportFamily (D.K - S.W) D.K
      hA hk hkK hUniform hIntersect with ⟨C, hC⟩
  exact ⟨C0, hC0, C, hC⟩

lemma ChainState.exists_dense_core_fixed_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C : Finset ℕ,
      C.Nonempty ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
  rcases S.remainingSupportFamily_denseCoreData hRoom with
    ⟨hA, hk, hkK, hUniform, hIntersect⟩
  rcases dense_core_from_spread_fixed_nat S.remainingSupportFamily (D.K - S.W) D.K
      hA hk hkK hUniform hIntersect with ⟨C, hC⟩
  exact ⟨C, by simpa [chainKappa] using hC⟩

lemma ChainState.coreSurvivors_nonempty_of_filter_card_pos
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hpos : 0 < (((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℕ) : ℝ)) :
    (S.coreSurvivors C).Nonempty := by
  have hfilter_nat : 0 < (S.remainingSupportFamily.filter fun A => C ⊆ A).card := by
    exact_mod_cast hpos
  have hle := S.remainingSupportFamily_filter_card_le_coreSurvivors C
  have hcore_card : 0 < (S.coreSurvivors C).card := lt_of_lt_of_le hfilter_nat hle
  exact Finset.card_pos.1 hcore_card

lemma ChainState.exists_dense_core_with_survivor_of_room
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∃ C : Finset ℕ,
        C.Nonempty ∧ (S.coreSurvivors C).Nonempty ∧
        ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
          (S.remainingSupportFamily.card : ℝ) /
            (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card := by
  rcases S.exists_dense_core_of_room hRoom with ⟨C0, hC0, C, hC, hbound⟩
  have hKreal : 1 ≤ (D.K : ℝ) := by exact_mod_cast D.K_pos
  have harg_ge : Real.exp 1 ≤ Real.exp 1 * (D.K : ℝ) := by
    nlinarith [Real.exp_pos 1, hKreal]
  have hlog_ge_one : 1 ≤ Real.log (Real.exp 1 * (D.K : ℝ)) := by
    have hlog := Real.log_le_log (Real.exp_pos 1) harg_ge
    simpa using hlog
  have hbase_nonneg : 0 ≤ C0 * Real.log (Real.exp 1 * (D.K : ℝ)) := by
    exact mul_nonneg hC0.le (zero_le_one.trans hlog_ge_one)
  have hden_nonneg :
      0 ≤ (S.remainingSupportFamily.card : ℝ) /
            (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card := by
    exact div_nonneg (by positivity) (pow_nonneg hbase_nonneg _)
  have hpos : 0 < (((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℕ) : ℝ) :=
    lt_of_le_of_lt hden_nonneg hbound
  exact ⟨C0, hC0, C, hC, S.coreSurvivors_nonempty_of_filter_card_pos hpos, hbound⟩

lemma ChainState.exists_dense_core_fixed_with_survivor_of_room
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C : Finset ℕ,
      C.Nonempty ∧ (S.coreSurvivors C).Nonempty ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
  rcases S.exists_dense_core_fixed_of_room hRoom with ⟨C, hC, hbound⟩
  have hbase_nonneg : 0 ≤ chainKappa D := (chainKappa_pos D).le
  have hden_nonneg :
      0 ≤ (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
    exact div_nonneg (by positivity) (pow_nonneg hbase_nonneg _)
  have hpos : 0 < (((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℕ) : ℝ) :=
    lt_of_le_of_lt hden_nonneg hbound
  exact ⟨C, hC, S.coreSurvivors_nonempty_of_filter_card_pos hpos, hbound⟩

lemma ChainState.coreSurvivors_card_gt_of_dense_bound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ} {A : ℝ}
    (hbound : A < ((S.remainingSupportFamily.filter fun B => C ⊆ B).card : ℝ)) :
    A < ((S.coreSurvivors C).card : ℝ) := by
  have hle : ((S.remainingSupportFamily.filter fun B => C ⊆ B).card : ℝ) ≤
      ((S.coreSurvivors C).card : ℝ) := by
    exact_mod_cast S.remainingSupportFamily_filter_card_le_coreSurvivors C
  exact hbound.trans_le hle

lemma ChainState.coreSurvivors_card_gt_qsurv_div_of_dense_bound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ} {Λ : ℝ}
    (hbound :
      ((S.remainingSupportFamily.card : ℝ) / Λ ^ C.card) <
        ((S.remainingSupportFamily.filter fun B => C ⊆ B).card : ℝ)) :
    ((S.Qsurv.card : ℝ) / Λ ^ C.card) <
      ((S.coreSurvivors C).card : ℝ) := by
  have h := S.coreSurvivors_card_gt_of_dense_bound hbound
  simpa [S.remainingSupportFamily_card_eq] using h

lemma ChainState.coreBlocks_nonempty_of_coreSurvivors
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) : (S.coreBlocks C).Nonempty := by
  rw [ChainState.coreBlocks]
  exact hCore.image _

lemma ChainState.coreBlocks_weight_sum_pos
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) :
    0 < ∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) := by
  exact Finset.sum_pos (fun B _hB => hExp_inv_sq_pos B)
    (S.coreBlocks_nonempty_of_coreSurvivors hCore)

lemma ChainState.coreBlocks_weight_sum_le_card
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ) :
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
      (S.coreBlocks C).card := by
  calc
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        ∑ _B ∈ S.coreBlocks C, (1 : ℝ) := by
          exact Finset.sum_le_sum (fun B _hB => hExp_inv_sq_le_one B)
    _ = (S.coreBlocks C).card := by simp

lemma ChainState.coreBlocks_weight_sum_le_two_pow_card
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hC : C.Nonempty) :
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
      (2 : ℝ) ^ C.card := by
  classical
  let Index := {p : ℕ // p ∈ C}
  let E : Finset (Index → ℕ) :=
    Fintype.piFinset fun _ : Index => Finset.range N
  let vec : ℕ → Index → ℕ := fun B p => B.factorization p.1 - 1
  let term : (Index → ℕ) → ℝ :=
    fun e => ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)
  have hvec_mem : ∀ B ∈ S.coreBlocks C, vec B ∈ E := by
    intro B hB
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range]
    have hsupport : primeSupport B = C := S.coreBlock_primeSupport_eq hB
    have hpSupport : p.1 ∈ primeSupport B := by
      simp [hsupport, p.2]
    have hBne : B ≠ 0 := by
      intro hzero
      subst B
      simp [primeSupport] at hpSupport
    have hfac_pos : 1 ≤ B.factorization p.1 := by
      unfold primeSupport at hpSupport
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
    have hfac_le_N : B.factorization p.1 ≤ N := by
      exact (Nat.factorization_lt p.1 hBne).le.trans (S.coreBlock_le_N hB)
    dsimp [vec]
    omega
  have hvec_inj : Set.InjOn vec (S.coreBlocks C) := by
    intro B hB R hR hBR
    have hsupportB : primeSupport B = C := S.coreBlock_primeSupport_eq hB
    have hsupportR : primeSupport R = C := S.coreBlock_primeSupport_eq hR
    have hBne : B ≠ 0 := by
      rcases hC with ⟨p, hp⟩
      have hpSupport : p ∈ primeSupport B := by simpa [hsupportB] using hp
      intro hzero
      subst B
      simp [primeSupport] at hpSupport
    have hRne : R ≠ 0 := by
      rcases hC with ⟨p, hp⟩
      have hpSupport : p ∈ primeSupport R := by simpa [hsupportR] using hp
      intro hzero
      subst R
      simp [primeSupport] at hpSupport
    apply Nat.eq_of_factorization_eq hBne hRne
    intro p
    by_cases hp : p ∈ C
    · have hcoord := congrFun hBR ⟨p, hp⟩
      dsimp [vec] at hcoord
      have hBpos : 1 ≤ B.factorization p := by
        have hpSupport : p ∈ primeSupport B := by simpa [hsupportB] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      have hRpos : 1 ≤ R.factorization p := by
        have hpSupport : p ∈ primeSupport R := by simpa [hsupportR] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      omega
    · have hpB : p ∉ primeSupport B := by simpa [hsupportB] using hp
      have hpR : p ∉ primeSupport R := by simpa [hsupportR] using hp
      rw [Finsupp.notMem_support_iff.1 hpB, Finsupp.notMem_support_iff.1 hpR]
  have hterm_eq :
      ∀ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) = term (vec B) := by
    intro B hB
    have hsupport : primeSupport B = C := S.coreBlock_primeSupport_eq hB
    have hhexp :
        hExp B = ∏ p : Index, B.factorization p.1 := by
      calc
        hExp B = ∏ p ∈ C, B.factorization p := by
          simp [hExp, hsupport]
        _ = ∏ p : Index, B.factorization p.1 := by
          rw [Finset.prod_coe_sort]
    have hsucc : ∀ p : Index, vec B p + 1 = B.factorization p.1 := by
      intro p
      have hpSupport : p.1 ∈ primeSupport B := by simp [hsupport, p.2]
      have hpos : 1 ≤ B.factorization p.1 := by
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      dsimp [vec]
      omega
    rw [hhexp, one_div_sq_nat_prod]
    dsimp [term]
    apply Finset.prod_congr rfl
    intro p _hp
    rw [hsucc p]
  calc
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))
        = ∑ B ∈ S.coreBlocks C, term (vec B) := by
            apply Finset.sum_congr rfl
            intro B hB
            exact hterm_eq B hB
    _ = ∑ e ∈ (S.coreBlocks C).image vec, term e := by
            rw [Finset.sum_image]
            intro B hB R hR hEq
            exact hvec_inj hB hR hEq
    _ ≤ ∑ e ∈ E, term e := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro e he
                rcases Finset.mem_image.mp he with ⟨B, hB, rfl⟩
                exact hvec_mem B hB)
              (by
                intro e _heE _heNot
                dsimp [term]
                positivity)
    _ = ∏ _p : Index,
          ∑ ν ∈ Finset.range N, (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2) := by
            change
              (∑ e ∈ Fintype.piFinset (fun _ : Index => Finset.range N),
                ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)) =
              ∏ _p : Index,
                ∑ ν ∈ Finset.range N, (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)
            exact
              (Finset.sum_prod_piFinset
                (ι := Index) (κ := ℕ) (R := ℝ)
                (s := Finset.range N)
                (g := fun _p ν => (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)))
    _ ≤ ∏ _p : Index, (2 : ℝ) := by
            exact Finset.prod_le_prod
              (s := (Finset.univ : Finset Index))
              (fun _p _hp => by positivity)
              (fun _p _hp => by
                simpa [Nat.cast_add, Nat.cast_one] using sum_inv_sq_range_le_two N)
    _ = (2 : ℝ) ^ C.card := by
            simp [Index]

/-- Prefix-omega sum for a newest-first list of selected blocks. Since the
chain constructor prepends the new block, the prefix before the head is the
product of the tail. -/
noncomputable def chainTFromBlocks : List ℕ → ℕ
  | [] => 0
  | _P :: Ps => omega (Ps.foldr (· * ·) 1) + chainTFromBlocks Ps

/-- The accumulated `T = ∑ W_{r-1}` along a chain, computed from the stored
block list. -/
noncomputable def chainT {N : ℕ} {D : PrunedData N} (S : ChainState N D) : ℕ :=
  chainTFromBlocks S.blocks

private lemma chainTFromBlocks_le_length_mul_omega_foldr
    (blocks : List ℕ) (hpos : ∀ P ∈ blocks, 0 < P) :
    chainTFromBlocks blocks ≤ blocks.length * omega (blocks.foldr (· * ·) 1) := by
  induction blocks with
  | nil =>
      simp [chainTFromBlocks, omega, primeSupport]
  | cons P Ps ih =>
      simp only [chainTFromBlocks, List.foldr_cons, List.length_cons]
      have hPs_pos : ∀ B ∈ Ps, 0 < B := by
        intro B hB
        exact hpos B (by simp [hB])
      have htail_le_full :
          omega (Ps.foldr (· * ·) 1) ≤ omega (P * Ps.foldr (· * ·) 1) := by
        apply omega_le_of_dvd
        · exact dvd_mul_left (Ps.foldr (· * ·) 1) P
        · exact (Nat.mul_pos (hpos P (by simp)) (List.foldr_mul_pos hPs_pos)).ne'
      calc
        omega (Ps.foldr (· * ·) 1) + chainTFromBlocks Ps
            ≤ omega (P * Ps.foldr (· * ·) 1) +
                Ps.length * omega (Ps.foldr (· * ·) 1) := by
              exact Nat.add_le_add htail_le_full (ih hPs_pos)
        _ ≤ omega (P * Ps.foldr (· * ·) 1) +
                Ps.length * omega (P * Ps.foldr (· * ·) 1) := by
              exact Nat.add_le_add_left
                (Nat.mul_le_mul_left Ps.length htail_le_full) _
        _ = (Ps.length + 1) * omega (P * Ps.foldr (· * ·) 1) := by
              rw [Nat.add_mul, Nat.one_mul]
              omega

private lemma chainTFromBlocks_real_quadratic_bound
    (blocks : List ℕ)
    (hpair : blocks.Pairwise Nat.Coprime)
    (homega_pos : ∀ P ∈ blocks, 1 ≤ omega P) :
    ((chainTFromBlocks blocks : ℝ) * 2) ≤
      2 * (blocks.length : ℝ) * (omega (blocks.foldr (· * ·) 1) : ℝ) -
        (blocks.length : ℝ) * ((blocks.length : ℝ) - 1) := by
  induction blocks with
  | nil =>
      simp [chainTFromBlocks, omega, primeSupport]
  | cons P Ps ih =>
      rw [List.pairwise_cons] at hpair
      have hPs_pair : Ps.Pairwise Nat.Coprime := hpair.2
      have hPs_omega : ∀ B ∈ Ps, 1 ≤ omega B := by
        intro B hB
        exact homega_pos B (by simp [hB])
      have hPomega : 1 ≤ omega P := homega_pos P (by simp)
      have hcop : Nat.Coprime P (Ps.foldr (· * ·) 1) :=
        List.coprime_foldr_mul_of_forall hpair.1
      have homega :
          omega (P * Ps.foldr (· * ·) 1) =
            omega P + omega (Ps.foldr (· * ·) 1) :=
        omega_mul_of_coprime hcop
      have hih := ih hPs_pair hPs_omega
      have hPomega_real : (1 : ℝ) ≤ (omega P : ℝ) := by
        exact_mod_cast hPomega
      have hlen_nonneg : 0 ≤ (Ps.length : ℝ) := by positivity
      simp only [chainTFromBlocks, List.foldr_cons, List.length_cons]
      rw [homega]
      norm_num [Nat.cast_add, Nat.cast_mul] at hih ⊢
      nlinarith [hih, hPomega_real, hlen_nonneg]

private lemma chainTFromBlocks_add_omega_real_quadratic_bound
    (blocks : List ℕ)
    (hpair : blocks.Pairwise Nat.Coprime)
    (homega_pos : ∀ P ∈ blocks, 1 ≤ omega P) :
    (((chainTFromBlocks blocks + omega (blocks.foldr (· * ·) 1) : ℕ) : ℝ) * 2) ≤
      2 * (blocks.length : ℝ) * (omega (blocks.foldr (· * ·) 1) : ℝ) -
        (blocks.length : ℝ) * ((blocks.length : ℝ) - 1) := by
  induction blocks with
  | nil =>
      simp [chainTFromBlocks, omega, primeSupport]
  | cons P Ps ih =>
      rw [List.pairwise_cons] at hpair
      have hPs_pair : Ps.Pairwise Nat.Coprime := hpair.2
      have hPs_omega : ∀ B ∈ Ps, 1 ≤ omega B := by
        intro B hB
        exact homega_pos B (by simp [hB])
      have hPomega : 1 ≤ omega P := homega_pos P (by simp)
      have hcop : Nat.Coprime P (Ps.foldr (· * ·) 1) :=
        List.coprime_foldr_mul_of_forall hpair.1
      have homega :
          omega (P * Ps.foldr (· * ·) 1) =
            omega P + omega (Ps.foldr (· * ·) 1) :=
        omega_mul_of_coprime hcop
      have hih := ih hPs_pair hPs_omega
      have hPomega_real : (1 : ℝ) ≤ (omega P : ℝ) := by
        exact_mod_cast hPomega
      have hlen_nonneg : 0 ≤ (Ps.length : ℝ) := by positivity
      simp only [chainTFromBlocks, List.foldr_cons, List.length_cons]
      rw [homega]
      norm_num [Nat.cast_add, Nat.cast_mul] at hih ⊢
      nlinarith [hih, hPomega_real, hlen_nonneg]

lemma ChainState.chainT_le_r_mul_W {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    chainT S ≤ S.r * S.W := by
  have h := chainTFromBlocks_le_length_mul_omega_foldr S.blocks S.blocks_pos
  simpa [chainT, S.blocks_length, ← S.product_eq, S.W_eq] using h

lemma ChainState.chainT_le_r_mul_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    chainT S ≤ S.r * D.K := by
  exact (S.chainT_le_r_mul_W).trans (Nat.mul_le_mul_left S.r S.W_le_K)

lemma ChainState.chainT_real_quadratic_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hblocks : S.BlocksOmegaPos) :
    ((chainT S : ℝ) * 2) ≤
      2 * (S.r : ℝ) * (S.W : ℝ) - (S.r : ℝ) * ((S.r : ℝ) - 1) := by
  have h := chainTFromBlocks_real_quadratic_bound S.blocks S.pairwise_coprime hblocks
  simpa [chainT, S.blocks_length, ← S.product_eq, S.W_eq] using h

lemma ChainState.chainT_add_W_real_quadratic_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hblocks : S.BlocksOmegaPos) :
    ((((chainT S + S.W : ℕ) : ℝ) * 2)) ≤
      2 * (S.r : ℝ) * (S.W : ℝ) - (S.r : ℝ) * ((S.r : ℝ) - 1) := by
  have h := chainTFromBlocks_add_omega_real_quadratic_bound
    S.blocks S.pairwise_coprime hblocks
  simpa [chainT, S.blocks_length, ← S.product_eq, S.W_eq] using h

lemma ChainState.chainT_cons_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {P : ℕ} {S' : ChainState N D}
    (hblocks : S'.blocks = P :: S.blocks) :
    chainT S' = S.W + chainT S := by
  calc
    chainT S' = omega (S.blocks.foldr (· * ·) 1) + chainTFromBlocks S.blocks := by
      simp [chainT, hblocks, chainTFromBlocks]
    _ = S.W + chainT S := by
      rw [← S.product_eq, ← S.W_eq]
      rfl

/-- Cumulative lower-bound scale for the survivor set after a chain state.
This is the formal slot for the PDF's iterated lower bound (12), with
`Λ` standing for the spread/block loss constant. -/
noncomputable def chainLowerScale {N : ℕ} {D : PrunedData N}
    (Λ : ℝ) (S : ChainState N D) : ℝ :=
  (D.Q.card : ℝ) /
    ((S.productP : ℝ) * (hExp S.productP : ℝ) ^ 2 * Λ ^ S.W)

/-- The cumulative survivor-size invariant needed to turn the local
structural step into the global chain inequality. -/
def ChainState.HasLowerBound {N : ℕ} {D : PrunedData N}
    (Λ : ℝ) (S : ChainState N D) : Prop :=
  chainLowerScale Λ S ≤ (S.Qsurv.card : ℝ)

private lemma div_scale_le_weighted_share
    {a q c w p h κ : ℝ} {n : ℕ}
    (hq_nonneg : 0 ≤ q) (hw_pos : 0 < w)
    (hp : 0 < p) (hh : 0 < h) (hκ : 0 < κ)
    (haq : a ≤ q) (hdense : q / κ ^ n < c) (hweight : w ≤ (2 : ℝ) ^ n) :
    a / (p * h * (2 * κ) ^ n) ≤ (c * (1 / h) / w) / p := by
  have hκpow : 0 < κ ^ n := pow_pos hκ _
  have htwopow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hΛpow : 0 < (2 * κ) ^ n := pow_pos (mul_pos (by norm_num) hκ) _
  have hq_lt : q < c * κ ^ n := by
    have hmul := mul_lt_mul_of_pos_right hdense hκpow
    rwa [div_mul_cancel₀ _ hκpow.ne'] at hmul
  have haw_le : a * w ≤ q * (2 : ℝ) ^ n :=
    mul_le_mul haq hweight hw_pos.le hq_nonneg
  have htarget : a * w ≤ c * (2 * κ) ^ n := by
    calc
      a * w ≤ q * (2 : ℝ) ^ n := haw_le
      _ ≤ (c * κ ^ n) * (2 : ℝ) ^ n :=
            (mul_lt_mul_of_pos_right hq_lt htwopow).le
      _ = c * (2 * κ) ^ n := by
            rw [mul_pow]
            ring
  calc
    a / (p * h * (2 * κ) ^ n)
        = (a * w) / ((p * h * (2 * κ) ^ n) * w) := by
            field_simp [hw_pos.ne']
    _ ≤ (c * (2 * κ) ^ n) / ((p * h * (2 * κ) ^ n) * w) := by
            exact div_le_div_of_nonneg_right htarget
              (mul_nonneg
                (mul_nonneg (mul_pos hp hh).le hΛpow.le)
                hw_pos.le)
    _ = (c * (1 / h) / w) / p := by
            field_simp [hp.ne', hh.ne', hΛpow.ne', hw_pos.ne']

private lemma div_scale_le_weighted_fiber
    {a q c w h κ : ℝ} {n : ℕ}
    (hq_nonneg : 0 ≤ q) (hw_pos : 0 < w)
    (hh : 0 < h) (hκ : 0 < κ)
    (haq : a ≤ q) (hdense : q / κ ^ n < c) (hweight : w ≤ (2 : ℝ) ^ n) :
    a / (h * (2 * κ) ^ n) ≤ (c * (1 / h) / w) := by
  have hκpow : 0 < κ ^ n := pow_pos hκ _
  have htwopow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hΛpow : 0 < (2 * κ) ^ n := pow_pos (mul_pos (by norm_num) hκ) _
  have hq_lt : q < c * κ ^ n := by
    have hmul := mul_lt_mul_of_pos_right hdense hκpow
    rwa [div_mul_cancel₀ _ hκpow.ne'] at hmul
  have haw_le : a * w ≤ q * (2 : ℝ) ^ n :=
    mul_le_mul haq hweight hw_pos.le hq_nonneg
  have htarget : a * w ≤ c * (2 * κ) ^ n := by
    calc
      a * w ≤ q * (2 : ℝ) ^ n := haw_le
      _ ≤ (c * κ ^ n) * (2 : ℝ) ^ n :=
            (mul_lt_mul_of_pos_right hq_lt htwopow).le
      _ = c * (2 * κ) ^ n := by
            rw [mul_pow]
            ring
  calc
    a / (h * (2 * κ) ^ n)
        = (a * w) / ((h * (2 * κ) ^ n) * w) := by
            field_simp [hw_pos.ne']
    _ ≤ (c * (2 * κ) ^ n) / ((h * (2 * κ) ^ n) * w) := by
            exact div_le_div_of_nonneg_right htarget
              (mul_nonneg (mul_pos hh hΛpow).le hw_pos.le)
    _ = c * (1 / h) / w := by
            field_simp [hh.ne', hΛpow.ne', hw_pos.ne']

lemma ChainState.chainLowerScale_extend_coreBlock_eq
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {Λ : ℝ} {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hP : P ∈ S.coreBlocks C)
    (hprod : S'.productP = P * S.productP)
    (hW : S'.W = S.W + C.card) :
    chainLowerScale Λ S' =
      chainLowerScale Λ S / ((P : ℝ) * (hExp P : ℝ) ^ 2 * Λ ^ C.card) := by
  rw [chainLowerScale, chainLowerScale, hprod, hW,
    hExp_mul_of_coprime (S.coreBlock_coprime_productP hP).symm, pow_add]
  norm_num [Nat.cast_mul]
  ring_nf

lemma ChainState.hasLowerBound_extend_coreBlock
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {κ Λ : ℝ} {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hκ : 0 < κ) (hΛ : Λ = 2 * κ)
    (hP : P ∈ S.coreBlocks C)
    (hLower : S.HasLowerBound Λ)
    (hDense :
      ((S.Qsurv.card : ℝ) / κ ^ C.card) <
        ((S.coreSurvivors C).card : ℝ))
    (hWeight :
      (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (2 : ℝ) ^ C.card)
    (hCard :
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ))
    (hprod : S'.productP = P * S.productP)
    (hW : S'.W = S.W + C.card) :
    S'.HasLowerBound Λ := by
  rw [ChainState.HasLowerBound]
  rw [S.chainLowerScale_extend_coreBlock_eq hP hprod hW, hΛ]
  have hCore : (S.coreSurvivors C).Nonempty := by
    have hPmem := hP
    rw [ChainState.coreBlocks] at hPmem
    rcases Finset.mem_image.mp hPmem with ⟨q, hq, _hP⟩
    exact ⟨q, hq⟩
  have hWeight_pos :
      0 < ∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) :=
    S.coreBlocks_weight_sum_pos hCore
  have hP_pos_real : 0 < (P : ℝ) := by
    exact_mod_cast S.coreBlock_pos hP
  have hExpP_pos : 0 < (hExp P : ℝ) := by exact_mod_cast hExp_pos P
  have hh_pos : 0 < ((hExp P : ℝ) ^ 2) := sq_pos_of_pos hExpP_pos
  have hq_nonneg : 0 ≤ (S.Qsurv.card : ℝ) := by positivity
  have hstep :
      chainLowerScale (2 * κ) S /
          ((P : ℝ) * ((hExp P : ℝ) ^ 2) * (2 * κ) ^ C.card) ≤
        (((S.coreSurvivors C).card : ℝ) *
            ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) :=
    div_scale_le_weighted_share
      hq_nonneg hWeight_pos hP_pos_real hh_pos hκ
      (by simpa [ChainState.HasLowerBound, hΛ] using hLower)
      hDense hWeight
  exact hstep.trans hCard

lemma ChainState.selectedFiber_lower_from_invariant
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ}
    (hCne : C.Nonempty)
    (hP : P ∈ S.coreBlocks C)
    (hLower : S.HasLowerBound (chainLambda D))
    (hDense :
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card)
    (hWeightedFiber :
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ)) :
    (D.Q.card : ℝ) /
        ((S.productP : ℝ) * (hExp (S.productP * P) : ℝ) ^ 2 *
          (chainLambda D) ^ (S.W + C.card)) ≤
      (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) := by
  have hCore : (S.coreSurvivors C).Nonempty := by
    rw [ChainState.coreBlocks] at hP
    rcases Finset.mem_image.mp hP with ⟨q, hq, _hP⟩
    exact ⟨q, hq⟩
  have hDenseQ :
      ((S.Qsurv.card : ℝ) / (chainKappa D) ^ C.card) <
        ((S.coreSurvivors C).card : ℝ) :=
    S.coreSurvivors_card_gt_qsurv_div_of_dense_bound (Λ := chainKappa D)
      (by simpa using hDense)
  have hWeight :
      (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (2 : ℝ) ^ C.card :=
    S.coreBlocks_weight_sum_le_two_pow_card hCne
  have hWeight_pos :
      0 < ∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) :=
    S.coreBlocks_weight_sum_pos hCore
  have hExpP_pos : 0 < (hExp P : ℝ) := by exact_mod_cast hExp_pos P
  have hh_pos : 0 < ((hExp P : ℝ) ^ 2) := sq_pos_of_pos hExpP_pos
  have hq_nonneg : 0 ≤ (S.Qsurv.card : ℝ) := by positivity
  have hstep :
      chainLowerScale (2 * chainKappa D) S /
          (((hExp P : ℝ) ^ 2) * (2 * chainKappa D) ^ C.card) ≤
        (((S.coreSurvivors C).card : ℝ) *
            ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) :=
    div_scale_le_weighted_fiber
      hq_nonneg hWeight_pos hh_pos (chainKappa_pos D)
      (by simpa [ChainState.HasLowerBound, chainLambda] using hLower)
      hDenseQ hWeight
  have hstepΛ :
      chainLowerScale (chainLambda D) S /
          (((hExp P : ℝ) ^ 2) * (chainLambda D) ^ C.card) ≤
        (((S.coreSurvivors C).card : ℝ) *
            ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) := by
    simpa [chainLambda] using hstep
  have hleft :
      chainLowerScale (chainLambda D) S /
          (((hExp P : ℝ) ^ 2) * (chainLambda D) ^ C.card) =
        (D.Q.card : ℝ) /
          ((S.productP : ℝ) * (hExp (S.productP * P) : ℝ) ^ 2 *
            (chainLambda D) ^ (S.W + C.card)) := by
    rw [chainLowerScale,
      hExp_mul_of_coprime (S.coreBlock_coprime_productP hP), pow_add]
    norm_num [Nat.cast_mul]
    ring_nf
  rw [← hleft]
  exact hstepΛ.trans hWeightedFiber

lemma ChainState.blocksOmegaPos_extend_coreBlock
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hBlocks : S.BlocksOmegaPos)
    (hCne : C.Nonempty)
    (hP : P ∈ S.coreBlocks C)
    (hblocks : S'.blocks = P :: S.blocks) :
    S'.BlocksOmegaPos := by
  intro B hB
  rw [hblocks] at hB
  rcases List.mem_cons.1 hB with hBP | hBtail
  · subst B
    rw [S.coreBlock_omega_eq_card hP]
    exact Nat.succ_le_of_lt hCne.card_pos
  · exact hBlocks B hBtail

/-! ## §2 Initial state -/

/-- The chain starts with no selected blocks, all pruned moduli surviving,
product `1`, and accumulated exponent count `0`. -/
noncomputable def initialChainState (N : ℕ) (D : PrunedData N) : ChainState N D where
  r := 0
  blocks := []
  blocks_length := by simp
  Qsurv := D.Q
  Qsurv_subset := by intro q hq; exact hq
  Qsurv_nonempty := D.Q_nonempty
  W := 0
  productP := 1
  product_eq := by simp
  blocks_pos := by intro P hP; simp at hP
  productP_pos := by norm_num
  pairwise_coprime := by simp
  exact_divides := by intro q _hq; exact one_dvd q
  no_selected_prime_remains := by
    intro _q _hq _p hp
    simp [primeSupport] at hp
  residues_agree := by
    intro qi _hqi rj _hrj hqiD hrjD
    rw [Int.modEq_iff_dvd]
    exact one_dvd (D.a ⟨rj, hrjD⟩ - D.a ⟨qi, hqiD⟩)
  W_eq := by simp [omega, primeSupport]
  W_le_K := by omega

lemma initialChainState_room (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).W < D.K := by
  simp [initialChainState]
  exact D.K_pos

lemma initialChainState_r_zero (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).r = 0 := rfl

lemma initialChainState_product_one (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).productP = 1 := rfl

lemma initialChainState_chainT (N : ℕ) (D : PrunedData N) :
    chainT (initialChainState N D) = 0 := rfl

lemma initialChainState_blocksOmegaPos (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).BlocksOmegaPos := by
  intro P hP
  simp [initialChainState] at hP

lemma initialChainState_hasLowerBound {N : ℕ} (D : PrunedData N) (Λ : ℝ) :
    ChainState.HasLowerBound Λ (initialChainState N D) := by
  rw [ChainState.HasLowerBound, chainLowerScale]
  simp [initialChainState, hExp_one]

/-! ## §3 Structural chain step -/

theorem chain_step_structural
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (hRoom : S.W < D.K) :
    ∃ C0 : ℝ, ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      0 < C0 ∧
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) /
          (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card := by
  rcases S.exists_dense_core_with_survivor_of_room hRoom with
    ⟨C0, hC0, C, hCne, hCore, hDense⟩
  rcases S.exists_weighted_extended_coreBlock hCore with
    ⟨P, S', hP, hblocks, hr, hprod, _hQsubset, _hQcard_le, hW, _hShare, hcard⟩
  have hWincrease : S.W < S'.W := by
    rw [hW]
    exact Nat.lt_add_of_pos_right hCne.card_pos
  exact ⟨C0, C, P, S', hC0, hCne, hP, hblocks, hr, hWincrease, hprod, hcard, hDense⟩

theorem chain_step_structural_with_lowerBound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D)) :
    ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      chainT S' = S.W + chainT S ∧
      S'.HasLowerBound (chainLambda D) ∧
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
  rcases S.exists_dense_core_fixed_with_survivor_of_room hRoom with
    ⟨C, hCne, hCore, hDense⟩
  rcases S.exists_weighted_extended_coreBlock hCore with
    ⟨P, S', hP, hblocks, hr, hprod, hQsubset, hQcard_le, hW, hShare, hcard⟩
  have hWincrease : S.W < S'.W := by
    rw [hW]
    exact Nat.lt_add_of_pos_right hCne.card_pos
  have hDenseQ :
      ((S.Qsurv.card : ℝ) / (chainKappa D) ^ C.card) <
        ((S.coreSurvivors C).card : ℝ) :=
    S.coreSurvivors_card_gt_qsurv_div_of_dense_bound (Λ := chainKappa D)
      (by simpa using hDense)
  have hWeight :
      (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (2 : ℝ) ^ C.card :=
    S.coreBlocks_weight_sum_le_two_pow_card hCne
  have hLower' : S'.HasLowerBound (chainLambda D) := by
    apply S.hasLowerBound_extend_coreBlock
      (κ := chainKappa D) (Λ := chainLambda D)
      (hκ := chainKappa_pos D) (hΛ := by rfl)
      (hP := hP) (hLower := hLower) (hDense := hDenseQ)
      (hWeight := hWeight) (hCard := hcard)
      (hprod := hprod) (hW := hW)
  exact ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, hQsubset, hQcard_le, hW,
    S.chainT_cons_eq hblocks, hLower', hShare, hcard, hDense⟩

lemma ChainState.coreSurvivors_nonempty_of_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : (S.coreSurvivors C).Nonempty := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, _⟩
  exact ⟨q, hq⟩

theorem chain_step_structural_with_counts
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (hRoom : S.W < D.K) :
    ∃ C0 : ℝ, ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      0 < C0 ∧
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) /
          (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card ∧
      ((S.coreSurvivors C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) ∧
      ((S.coreBlocks C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N) ∧
      P ≤ N ∧
      (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rcases chain_step_structural S hRoom with
    ⟨C0, C, P, S', hC0, hCne, hP, hblocks, hr, hWincrease, hprod, hweighted, hDense⟩
  have hCore : (S.coreSurvivors C).Nonempty := S.coreSurvivors_nonempty_of_coreBlock hP
  exact ⟨C0, C, P, S', hC0, hCne, hP, hblocks, hr, hWincrease, hprod, hweighted, hDense,
    S.coreSurvivors_card_real_le_bfv_omega_count C ε hCount,
    S.coreBlocks_card_real_le_bfv_omega_count C ε hCore hCount,
    S.coreBlock_le_N hP, S.coreBlock_hExp_bound hP⟩

theorem chain_step_structural_with_counts_and_lowerBound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D)) :
    ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      chainT S' = S.W + chainT S ∧
      S'.HasLowerBound (chainLambda D) ∧
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card ∧
      ((S.coreSurvivors C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) ∧
      ((S.coreBlocks C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N) ∧
      P ≤ N ∧
      (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rcases chain_step_structural_with_lowerBound S hRoom hLower with
    ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, hQsubset, hQcard_le,
      hW, hT, hLower', hShare, hweighted, hDense⟩
  have hCore : (S.coreSurvivors C).Nonempty := S.coreSurvivors_nonempty_of_coreBlock hP
  exact ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, hQsubset, hQcard_le,
    hW, hT, hLower',
    hShare, hweighted, hDense,
    S.coreSurvivors_card_real_le_bfv_omega_count C ε hCount,
    S.coreBlocks_card_real_le_bfv_omega_count C ε hCore hCount,
    S.coreBlock_le_N hP, S.coreBlock_hExp_bound hP⟩

noncomputable def chainStepBound {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : ℝ :=
  (N : ℝ) / (D.Q.card : ℝ)
    * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))

noncomputable def chainProductBound {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : ℝ :=
  ((N : ℝ) / (D.Q.card : ℝ)) ^ S.r
    * Real.exp ((S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp (((chainT S : ℝ) / 2) * Real.log (Real.log (N : ℝ)))

lemma chainStepBound_nonneg {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : 0 ≤ chainStepBound ε S := by
  rw [chainStepBound]
  positivity

lemma chainProductBound_pos {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : 0 < chainProductBound ε S := by
  rw [chainProductBound]
  have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
  have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
  positivity

noncomputable def chainStepBoundWithLosses {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (_S S' : ChainState N D) : ℝ :=
  (N : ℝ) / (D.Q.card : ℝ)
    * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp (((S'.W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))
    * (hExp S'.productP : ℝ) ^ 2
    * (chainLambda D) ^ S'.W

noncomputable def chainProductBoundWithLosses {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : ℝ :=
  ((N : ℝ) / (D.Q.card : ℝ)) ^ S.r
    * Real.exp ((S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ)))
    * Real.exp (2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ)))
    * (chainLambda D) ^ (chainT S + S.W)

lemma chainStepBoundWithLosses_nonneg {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S S' : ChainState N D) : 0 ≤ chainStepBoundWithLosses ε S S' := by
  rw [chainStepBoundWithLosses]
  have hΛ : 0 ≤ chainLambda D := (chainLambda_pos D).le
  positivity

lemma chainProductBoundWithLosses_pos {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : 0 < chainProductBoundWithLosses ε S := by
  rw [chainProductBoundWithLosses]
  have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
  have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
  have hΛ : 0 < chainLambda D := chainLambda_pos D
  positivity

lemma log_chainProductBound {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) :
    Real.log (chainProductBound ε S) =
      (S.r : ℝ) * Real.log ((N : ℝ) / (D.Q.card : ℝ)) +
        (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
        ((chainT S : ℝ) / 2) * Real.log (Real.log (N : ℝ)) := by
  rw [chainProductBound]
  set q : ℝ := (N : ℝ) / (D.Q.card : ℝ)
  set a : ℝ := (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N
  set b : ℝ := ((chainT S : ℝ) / 2) * Real.log (Real.log (N : ℝ))
  have hq_pos : 0 < q := by
    dsimp [q]
    have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
    have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
    positivity
  have hqpow_ne : q ^ S.r ≠ 0 := pow_ne_zero _ hq_pos.ne'
  have hexpa_ne : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
  have hexpb_ne : Real.exp b ≠ 0 := (Real.exp_pos b).ne'
  rw [Real.log_mul (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne,
    Real.log_mul hqpow_ne hexpa_ne, Real.log_pow, Real.log_exp, Real.log_exp]

lemma log_chainProductBoundWithLosses {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) :
    Real.log (chainProductBoundWithLosses ε S) =
      (S.r : ℝ) * Real.log ((N : ℝ) / (D.Q.card : ℝ)) +
        (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
        ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
        2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
        ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) := by
  rw [chainProductBoundWithLosses]
  set q : ℝ := (N : ℝ) / (D.Q.card : ℝ)
  set a : ℝ := (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N
  set b : ℝ := (((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))
  set c : ℝ := 2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ))
  set Λ : ℝ := chainLambda D
  have hq_pos : 0 < q := by
    dsimp [q]
    have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
    have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
    positivity
  have hΛ_pos : 0 < Λ := by
    dsimp [Λ]
    exact chainLambda_pos D
  have hqpow_ne : q ^ S.r ≠ 0 := pow_ne_zero _ hq_pos.ne'
  have hexpa_ne : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
  have hexpb_ne : Real.exp b ≠ 0 := (Real.exp_pos b).ne'
  have hexpc_ne : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
  have hΛpow_ne : Λ ^ (chainT S + S.W) ≠ 0 := pow_ne_zero _ hΛ_pos.ne'
  rw [Real.log_mul
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne) hexpc_ne)
        hΛpow_ne,
      Real.log_mul (mul_ne_zero (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne) hexpc_ne,
      Real.log_mul (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne,
      Real.log_mul hqpow_ne hexpa_ne,
      Real.log_pow, Real.log_exp, Real.log_exp, Real.log_exp, Real.log_pow]

lemma initialChainState_productBound {N : ℕ} (D : PrunedData N) (ε : ℝ) :
    ((initialChainState N D).productP : ℝ) ≤
      chainProductBound ε (initialChainState N D) := by
  simp [chainProductBound, initialChainState]

lemma initialChainState_productBoundWithLosses {N : ℕ} (D : PrunedData N) (ε : ℝ) :
    ((initialChainState N D).productP : ℝ) ≤
      chainProductBoundWithLosses ε (initialChainState N D) := by
  simp [chainProductBoundWithLosses, initialChainState, chainT, chainTFromBlocks]

lemma chainProductBound_step
    {N : ℕ} {D : PrunedData N} {ε : ℝ} {S S' : ChainState N D}
    (hr : S'.r = S.r + 1)
    (hT : chainT S' = S.W + chainT S)
    (hProd : (S.productP : ℝ) ≤ chainProductBound ε S)
    (hStep :
      (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBound ε S) :
    (S'.productP : ℝ) ≤ chainProductBound ε S' := by
  have hstep_nonneg : 0 ≤ chainStepBound ε S := chainStepBound_nonneg ε S
  calc
    (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBound ε S := hStep
    _ ≤ chainProductBound ε S * chainStepBound ε S := by
          exact mul_le_mul_of_nonneg_right hProd hstep_nonneg
    _ = chainProductBound ε S' := by
          rw [chainProductBound, chainStepBound, chainProductBound, hr, hT]
          set q : ℝ := (N : ℝ) / (D.Q.card : ℝ)
          set a : ℝ := (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N with ha
          set l : ℝ := Real.log (Real.log (N : ℝ))
          rw [pow_succ]
          have hExpR :
              Real.exp ((S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) =
                Real.exp ((S.r : ℝ) * a) := by
            rw [ha]
            ring_nf
          have hExpR1 :
              Real.exp (((S.r + 1 : ℕ) : ℝ) *
                  (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) =
                Real.exp (((S.r + 1 : ℕ) : ℝ) * a) := by
            rw [ha]
            ring_nf
          rw [hExpR, hExpR1]
          change
            (q ^ S.r * Real.exp ((S.r : ℝ) * a) *
                  Real.exp (((chainT S : ℝ) / 2) * l)) *
                (q * Real.exp a * Real.exp (((S.W : ℝ) / 2) * l)) =
              q ^ S.r * q * Real.exp (((S.r + 1 : ℕ) : ℝ) * a) *
                Real.exp ((((S.W + chainT S : ℕ) : ℝ) / 2) * l)
          calc
            (q ^ S.r * Real.exp ((S.r : ℝ) * a) *
                  Real.exp (((chainT S : ℝ) / 2) * l)) *
                (q * Real.exp a * Real.exp (((S.W : ℝ) / 2) * l))
                = q ^ S.r * q *
                    (Real.exp ((S.r : ℝ) * a) * Real.exp a) *
                    (Real.exp (((chainT S : ℝ) / 2) * l) *
                      Real.exp (((S.W : ℝ) / 2) * l)) := by
                    ring
            _ = q ^ S.r * q * Real.exp (((S.r + 1 : ℕ) : ℝ) * a) *
                  Real.exp ((((S.W + chainT S : ℕ) : ℝ) / 2) * l) := by
                    rw [← Real.exp_add, ← Real.exp_add]
                    congr 2
                    · congr 1
                      norm_num
                      ring
                    · norm_num
                      ring

lemma chainProductBoundWithLosses_step
    {N : ℕ} {D : PrunedData N} {ε : ℝ} {S S' : ChainState N D}
    (hr : S'.r = S.r + 1)
    (hT : chainT S' = S.W + chainT S)
    (hProd : (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S)
    (hStep :
      (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S') :
    (S'.productP : ℝ) ≤ chainProductBoundWithLosses ε S' := by
  have hstep_nonneg : 0 ≤ chainStepBoundWithLosses ε S S' :=
    chainStepBoundWithLosses_nonneg ε S S'
  have hExpBound : (hExp S'.productP : ℝ) ≤
      Real.exp (Real.sqrt (Real.log (N : ℝ))) :=
    S'.productP_hExp_bound
  have hExpSq :
      (hExp S'.productP : ℝ) ^ 2 ≤
        Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
    have hnonneg : 0 ≤ (hExp S'.productP : ℝ) := by positivity
    calc
      (hExp S'.productP : ℝ) ^ 2
          ≤ (Real.exp (Real.sqrt (Real.log (N : ℝ)))) ^ 2 :=
            sq_le_sq₀ hnonneg (Real.exp_pos _).le |>.2 hExpBound
      _ = Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
            rw [sq, ← Real.exp_add]
            ring_nf
  calc
    (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := hStep
    _ ≤ chainProductBoundWithLosses ε S * chainStepBoundWithLosses ε S S' := by
          exact mul_le_mul_of_nonneg_right hProd hstep_nonneg
    _ ≤ chainProductBoundWithLosses ε S' := by
          rw [chainProductBoundWithLosses, chainStepBoundWithLosses,
            chainProductBoundWithLosses, hr, hT]
          set q : ℝ := (N : ℝ) / (D.Q.card : ℝ) with hq
          set a : ℝ := -((D.K : ℝ) / Mscale N) / 2 + ε with ha
          set l : ℝ := Real.log (Real.log (N : ℝ)) with hl
          set u : ℝ := Real.sqrt (Real.log (N : ℝ)) with hu
          have hΛnonneg : 0 ≤ chainLambda D := (chainLambda_pos D).le
          calc
            (q ^ S.r * Real.exp ((S.r : ℝ) * a * Zscale N) *
                  Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                  Real.exp (2 * (S.r : ℝ) * u) *
                  (chainLambda D) ^ (chainT S + S.W)) *
                (q * Real.exp (a * Zscale N) * Real.exp (((S'.W : ℝ) / 2) * l) *
                  (hExp S'.productP : ℝ) ^ 2 * (chainLambda D) ^ S'.W)
                ≤
              (q ^ S.r * Real.exp ((S.r : ℝ) * a * Zscale N) *
                  Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                  Real.exp (2 * (S.r : ℝ) * u) *
                  (chainLambda D) ^ (chainT S + S.W)) *
                (q * Real.exp (a * Zscale N) * Real.exp (((S'.W : ℝ) / 2) * l) *
                  Real.exp (2 * u) * (chainLambda D) ^ S'.W) := by
                    exact mul_le_mul_of_nonneg_left
                      (by
                        exact mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left hExpSq (by positivity))
                          (pow_nonneg hΛnonneg _))
                      (by positivity)
            _ = q ^ (S.r + 1) *
                  Real.exp (((S.r + 1 : ℕ) : ℝ) * a * Zscale N) *
                  Real.exp ((((S.W + chainT S + S'.W : ℕ) : ℝ) / 2) * l) *
                  Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) *
                  (chainLambda D) ^ (S.W + chainT S + S'.W) := by
                    rw [pow_succ]
                    calc
                      (q ^ S.r * Real.exp ((S.r : ℝ) * a * Zscale N) *
                            Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                            Real.exp (2 * (S.r : ℝ) * u) *
                            (chainLambda D) ^ (chainT S + S.W)) *
                          (q * Real.exp (a * Zscale N) *
                            Real.exp (((S'.W : ℝ) / 2) * l) *
                            Real.exp (2 * u) * (chainLambda D) ^ S'.W)
                          =
                        q ^ S.r * q *
                          (Real.exp ((S.r : ℝ) * a * Zscale N) *
                            Real.exp (a * Zscale N)) *
                          (Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                            Real.exp (((S'.W : ℝ) / 2) * l)) *
                          (Real.exp (2 * (S.r : ℝ) * u) * Real.exp (2 * u)) *
                          ((chainLambda D) ^ (chainT S + S.W) *
                            (chainLambda D) ^ S'.W) := by ring
                      _ =
                        q ^ S.r * q *
                          Real.exp (((S.r + 1 : ℕ) : ℝ) * a * Zscale N) *
                          Real.exp ((((S.W + chainT S + S'.W : ℕ) : ℝ) / 2) * l) *
                          Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) *
                          (chainLambda D) ^ (S.W + chainT S + S'.W) := by
                            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
                              ← pow_add]
                            have hA :
                                Real.exp ((S.r : ℝ) * a * Zscale N + a * Zscale N) =
                                  Real.exp (((S.r + 1 : ℕ) : ℝ) * a * Zscale N) := by
                              congr 1
                              norm_num
                              ring
                            have hL :
                                Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l +
                                    ((S'.W : ℝ) / 2) * l) =
                                  Real.exp ((((S.W + chainT S + S'.W : ℕ) : ℝ) / 2) *
                                    l) := by
                              congr 1
                              norm_num [Nat.cast_add]
                              ring
                            have hU :
                                Real.exp (2 * (S.r : ℝ) * u + 2 * u) =
                                  Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) := by
                              congr 1
                              norm_num
                              ring
                            rw [hA, hL, hU]
                            ring

theorem chain_terminal_with_product_bound_from_state
    {N : ℕ} {D : PrunedData N} (ε : ℝ)
    (hStep :
      ∀ S : ChainState N D,
        S.HasLowerBound (chainLambda D) →
        S.BlocksOmegaPos →
        S.W < D.K →
        ∃ S' : ChainState N D,
          S'.r = S.r + 1 ∧
          S.W < S'.W ∧
          chainT S' = S.W + chainT S ∧
          S'.HasLowerBound (chainLambda D) ∧
          S'.BlocksOmegaPos ∧
          (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S')
    (S : ChainState N D)
    (hLower : S.HasLowerBound (chainLambda D))
    (hBlocks : S.BlocksOmegaPos)
    (hProd : (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S) :
    ∃ Sfinal : ChainState N D,
      S.r ≤ Sfinal.r ∧
      Sfinal.r ≤ S.r + (D.K - S.W) ∧
      Sfinal.W = D.K ∧
      Sfinal.HasLowerBound (chainLambda D) ∧
      Sfinal.BlocksOmegaPos ∧
      (Sfinal.productP : ℝ) ≤ chainProductBoundWithLosses ε Sfinal := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ S : ChainState N D,
      D.K - S.W = n →
      S.HasLowerBound (chainLambda D) →
      S.BlocksOmegaPos →
      (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S →
      ∃ Sfinal : ChainState N D,
        S.r ≤ Sfinal.r ∧
        Sfinal.r ≤ S.r + (D.K - S.W) ∧
        Sfinal.W = D.K ∧
        Sfinal.HasLowerBound (chainLambda D) ∧
        Sfinal.BlocksOmegaPos ∧
        (Sfinal.productP : ℝ) ≤ chainProductBoundWithLosses ε Sfinal
  have hmain : ∀ n, motive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hn hLowerS hBlocksS hProdS
        by_cases hdone : S.W = D.K
        · refine ⟨S, le_rfl, ?_, hdone, hLowerS, hBlocksS, hProdS⟩
          rw [hdone]
          simp
        · have hRoom : S.W < D.K := lt_of_le_of_ne S.W_le_K hdone
          rcases hStep S hLowerS hBlocksS hRoom with
            ⟨S', hr, hWincrease, hT, hLower', hBlocks', hStepProd⟩
          have hProd' : (S'.productP : ℝ) ≤ chainProductBoundWithLosses ε S' :=
            chainProductBoundWithLosses_step hr hT hProdS hStepProd
          have hlt : D.K - S'.W < n := by
            rw [← hn]
            omega
          rcases ih (D.K - S'.W) hlt S' rfl hLower' hBlocks' hProd' with
            ⟨Sfinal, hle_start, hle_budget, hWfinal, hLowerFinal, hBlocksFinal,
              hProdFinal⟩
          refine ⟨Sfinal, ?_, ?_, hWfinal, hLowerFinal, hBlocksFinal, hProdFinal⟩
          · have hstep : S.r ≤ S'.r := by
              rw [hr]
              omega
            exact hstep.trans hle_start
          · have hbudget :
                S'.r + (D.K - S'.W) ≤ S.r + (D.K - S.W) := by
              rw [hr]
              omega
            exact hle_budget.trans hbudget
  exact hmain (D.K - S.W) S rfl hLower hBlocks hProd

theorem chain_terminal_with_product_bound_from_initial
    (N : ℕ) (D : PrunedData N) (ε : ℝ)
    (hStep :
      ∀ S : ChainState N D,
        S.HasLowerBound (chainLambda D) →
        S.BlocksOmegaPos →
        S.W < D.K →
        ∃ S' : ChainState N D,
          S'.r = S.r + 1 ∧
          S.W < S'.W ∧
          chainT S' = S.W + chainT S ∧
          S'.HasLowerBound (chainLambda D) ∧
          S'.BlocksOmegaPos ∧
          (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S') :
    ∃ R : ℕ, ∃ S : ChainState N D,
      S.r = R ∧ 1 ≤ R ∧ R ≤ D.K ∧
      ((N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) ∧
      S.HasLowerBound (chainLambda D) ∧
      S.BlocksOmegaPos ∧
      (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S := by
  let S0 := initialChainState N D
  have hRoom0 : S0.W < D.K := by
    simpa [S0] using initialChainState_room N D
  have hLower0 : S0.HasLowerBound (chainLambda D) := by
    simpa [S0] using initialChainState_hasLowerBound D (chainLambda D)
  have hBlocks0 : S0.BlocksOmegaPos := by
    simpa [S0] using initialChainState_blocksOmegaPos N D
  have hProd0 : (S0.productP : ℝ) ≤ chainProductBoundWithLosses ε S0 := by
    simpa [S0] using initialChainState_productBoundWithLosses D ε
  rcases hStep S0 hLower0 hBlocks0 hRoom0 with
    ⟨S1, hr1, hWincrease1, _hT1, hLower1, hBlocks1, hStepProd1⟩
  have hProd1 : (S1.productP : ℝ) ≤ chainProductBoundWithLosses ε S1 :=
    chainProductBoundWithLosses_step hr1 _hT1 hProd0 hStepProd1
  rcases chain_terminal_with_product_bound_from_state ε hStep S1 hLower1 hBlocks1 hProd1 with
    ⟨S, hle_start, hle_budget, hW, hLower, hBlocks, hProd⟩
  refine ⟨S.r, S, rfl, ?_, ?_, Or.inr hW, hLower, hBlocks, hProd⟩
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    exact hS1r ▸ hle_start
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    have hS1W_pos : 0 < S1.W := by
      have hS0W : S0.W = 0 := rfl
      omega
    calc
      S.r ≤ S1.r + (D.K - S1.W) := hle_budget
      _ ≤ D.K := by
        rw [hS1r]
        omega

theorem chain_terminal_from_state
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (hLower : S.HasLowerBound (chainLambda D)) :
    ∃ Sfinal : ChainState N D,
      S.r ≤ Sfinal.r ∧
      Sfinal.r ≤ S.r + (D.K - S.W) ∧
      Sfinal.W = D.K ∧
      Sfinal.HasLowerBound (chainLambda D) := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ S : ChainState N D,
      D.K - S.W = n →
      S.HasLowerBound (chainLambda D) →
      ∃ Sfinal : ChainState N D,
        S.r ≤ Sfinal.r ∧
        Sfinal.r ≤ S.r + (D.K - S.W) ∧
        Sfinal.W = D.K ∧
        Sfinal.HasLowerBound (chainLambda D)
  have hmain : ∀ n, motive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hn hLowerS
        by_cases hdone : S.W = D.K
        · refine ⟨S, le_rfl, ?_, hdone, hLowerS⟩
          rw [hdone]
          simp
        · have hRoom : S.W < D.K := lt_of_le_of_ne S.W_le_K hdone
          rcases chain_step_structural_with_lowerBound S hRoom hLowerS with
            ⟨_C, _P, S', _hCne, _hP, _hblocks, hr, hWincrease, _hprod,
              _hQsubset, _hQcard_le, _hW, _hT, hLower', _hShare, _hcard, _hDense⟩
          have hlt : D.K - S'.W < n := by
            rw [← hn]
            omega
          rcases ih (D.K - S'.W) hlt S' rfl hLower' with
            ⟨Sfinal, hle_start, hle_budget, hWfinal, hLowerFinal⟩
          refine ⟨Sfinal, ?_, ?_, hWfinal, hLowerFinal⟩
          · have hstep : S.r ≤ S'.r := by
              rw [hr]
              omega
            exact hstep.trans hle_start
          · have hbudget :
                S'.r + (D.K - S'.W) ≤ S.r + (D.K - S.W) := by
              rw [hr]
              omega
            exact hle_budget.trans hbudget
  exact hmain (D.K - S.W) S rfl hLower

theorem chain_terminal_from_initial (N : ℕ) (D : PrunedData N) :
    ∃ R : ℕ, ∃ S : ChainState N D,
      S.r = R ∧
      1 ≤ R ∧ R ≤ D.K ∧
      ((N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) ∧
      S.HasLowerBound (chainLambda D) := by
  let S0 := initialChainState N D
  have hRoom0 : S0.W < D.K := by
    simpa [S0] using initialChainState_room N D
  have hLower0 : S0.HasLowerBound (chainLambda D) := by
    simpa [S0] using initialChainState_hasLowerBound D (chainLambda D)
  rcases chain_step_structural_with_lowerBound S0 hRoom0 hLower0 with
    ⟨_C, _P, S1, _hCne, _hP, _hblocks, hr1, hWincrease1, _hprod,
      _hQsubset, _hQcard_le, _hW, _hT, hLower1, _hShare, _hcard, _hDense⟩
  rcases chain_terminal_from_state S1 hLower1 with
    ⟨S, hle_start, hle_budget, hW, hLower⟩
  refine ⟨S.r, S, rfl, ?_, ?_, Or.inr hW, hLower⟩
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    exact hS1r ▸ hle_start
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    have hS1W_pos : 0 < S1.W := by
      have hS0W : S0.W = 0 := rfl
      omega
    calc
      S.r ≤ S1.r + (D.K - S1.W) := hle_budget
      _ ≤ D.K := by
        rw [hS1r]
        omega

/-! ## §4 Chain step -/

/-- The remaining quantitative estimate in PDF Lemma 4.1: once the
structural step has selected an exact block `P`, the BFV count, dense-core
lower bound, weighted block choice, `hExp` control, and lower-order estimates
bound that block by the one-step product factor. -/
theorem chain_step_selected_block_bound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ) (_hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (_hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D))
    (_hBlocks : S.BlocksOmegaPos)
    {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hCne : C.Nonempty)
    (hP : P ∈ S.coreBlocks C)
    (hStepProduct : S'.productP = P * S.productP)
    (hStepW : S'.W = S.W + C.card)
    (_hStepLower : S'.HasLowerBound (chainLambda D))
    (_hQsurv_subset :
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P))
    (_hQsurv_card_le :
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card)
    (hWeightedFiber :
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ))
    (_hWeighted :
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ))
    (hDense :
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card)
    (_hCoreCount :
      ((S.coreSurvivors C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))
    (_hBlockCount :
      ((S.coreBlocks C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N))
    (_hP_le_N : P ≤ N)
    (_hP_hExp : (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ)))) :
    (P : ℝ) ≤ chainStepBoundWithLosses ε S S' := by
  have hFiberLower :
      (D.Q.card : ℝ) /
          ((S.productP : ℝ) * (hExp (S.productP * P) : ℝ) ^ 2 *
            (chainLambda D) ^ (S.W + C.card)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) :=
    S.selectedFiber_lower_from_invariant hCne hP hLower hDense hWeightedFiber
  have hFiberUpper :
      ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ) ≤
        ((N : ℝ) / (S.productP * P : ℝ)) *
          Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ))) :=
    S.selectedFiber_card_real_le_bfv_omega_count hP ε hCount
  have hWithLosses :
      (P : ℝ) ≤
        ((N : ℝ) / (D.Q.card : ℝ)) *
          Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ))) *
          (hExp (S.productP * P) : ℝ) ^ 2 *
          (chainLambda D) ^ (S.W + C.card) := by
    have hcompare := hFiberLower.trans hFiberUpper
    have hDQpos : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
    have hSpos : 0 < (S.productP : ℝ) := by exact_mod_cast S.productP_pos
    have hPpos : 0 < (P : ℝ) := by exact_mod_cast S.coreBlock_pos hP
    have hHpos : 0 < (hExp (S.productP * P) : ℝ) ^ 2 := by
      have h : 0 < (hExp (S.productP * P) : ℝ) := by exact_mod_cast hExp_pos (S.productP * P)
      exact sq_pos_of_pos h
    have hΛpos : 0 < (chainLambda D) ^ (S.W + C.card) :=
      pow_pos (chainLambda_pos D) _
    have hEpos :
        0 < Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ))) := by
      positivity
    field_simp [hSpos.ne', hPpos.ne', hHpos.ne', hΛpos.ne'] at hcompare
    have hmain :
        (D.Q.card : ℝ) * (P : ℝ) ≤
          (N : ℝ) *
            Real.exp ((-((D.K : ℝ) / Mscale N) + 2 * ε) * Zscale N / 2) *
            Real.exp (((S.W + C.card : ℕ) : ℝ) * Real.log (Real.log (N : ℝ)) / 2) *
            ((hExp (S.productP * P) : ℝ) ^ 2) *
            (chainLambda D) ^ (S.W + C.card) := by
      have hmul := mul_le_mul_of_nonneg_right hcompare hHpos.le
      rw [div_mul_cancel₀ _ hHpos.ne'] at hmul
      nlinarith [hmul]
    field_simp [hDQpos.ne']
    nlinarith [hmain]
  rw [chainStepBoundWithLosses, hStepW, hStepProduct]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hWithLosses

/-- **One chain step** (PDF Lemma 4.1). From a chain state with at least
one prime still to commit, the dense-core lemma + BFV count + residue
pigeonhole produce a next block `P_{r+1}` and a still-large surviving
sub-family. -/
theorem chain_step
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ) (_hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D))
    (hBlocks : S.BlocksOmegaPos) :
    ∃ S' : ChainState N D,
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      chainT S' = S.W + chainT S ∧
      S'.HasLowerBound (chainLambda D) ∧
      S'.BlocksOmegaPos ∧
      (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := by
  rcases chain_step_structural_with_counts_and_lowerBound S ε hCount hRoom hLower with
    ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, _hQsubset, _hQcard_le,
      _hW, hT, hLower', _hWeightedFiber, _hweighted, _hDense, _hCoreCount, _hBlockCount,
      _hP_le_N, _hP_hExp⟩
  have hBlocks' : S'.BlocksOmegaPos :=
    S.blocksOmegaPos_extend_coreBlock hBlocks hCne hP hblocks
  refine ⟨S', hr, hWincrease, hT, hLower', hBlocks', ?_⟩
  have hPbound : (P : ℝ) ≤ chainStepBoundWithLosses ε S S' :=
    chain_step_selected_block_bound S ε _hε hCount hRoom hLower hBlocks
      hCne hP hprod _hW hLower' _hQsubset _hQcard_le _hWeightedFiber _hweighted _hDense
      _hCoreCount _hBlockCount _hP_le_N _hP_hExp
  rw [hprod]
  calc
    ((P * S.productP : ℕ) : ℝ) = (P : ℝ) * (S.productP : ℝ) := by norm_num
    _ ≤ chainStepBoundWithLosses ε S S' * (S.productP : ℝ) := by
          exact mul_le_mul_of_nonneg_right hPbound (by positivity)
    _ = (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := by ring

/-! ## §5 The chain inequality (telescoped) -/

/-- **Chain inequality** (PDF Proposition 4.2). The full descending chain
runs for `R` steps until either `W = K` or `productP ≥ N L(-2, N)`. -/
theorem chain_inequality
    (N : ℕ) (D : PrunedData N) (ε : ℝ) (_hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ∃ R : ℕ, ∃ S : ChainState N D,
      S.r = R ∧ 1 ≤ R ∧ R ≤ D.K ∧
      ((N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) ∧
      S.BlocksOmegaPos ∧
      -- telescoped product bound, parameterized by ε, with the explicit
      -- lower-order losses from the paper:
      (S.productP : ℝ) ≤
        ((N : ℝ) / (D.Q.card : ℝ)) ^ R
        * Real.exp ((R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
        * Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ)))
        * Real.exp (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)))
        * (chainLambda D) ^ (chainT S + S.W) := by
  have hStep :
      ∀ S : ChainState N D,
        S.HasLowerBound (chainLambda D) →
        S.BlocksOmegaPos →
        S.W < D.K →
        ∃ S' : ChainState N D,
          S'.r = S.r + 1 ∧
          S.W < S'.W ∧
          chainT S' = S.W + chainT S ∧
          S'.HasLowerBound (chainLambda D) ∧
          S'.BlocksOmegaPos ∧
          (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := by
    intro S hLower hBlocks hRoom
    exact chain_step S ε _hε hCount hRoom hLower hBlocks
  rcases chain_terminal_with_product_bound_from_initial N D ε hStep with
    ⟨R, S, hR, hRpos, hRle, hStop, _hLower, hBlocks, hProd⟩
  refine ⟨R, S, hR, hRpos, hRle, hStop, hBlocks, ?_⟩
  simpa [chainProductBoundWithLosses, hR] using hProd

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFV/Filtering.lean
    ============================================================= -/

/-
Erdos Problem 202 -- finite filtering helpers for BFV pruning.

These lemmas are deliberately elementary.  They isolate the finite-set
bookkeeping used by the pruning step from the analytic BFV estimates.
-/


namespace Erdos202

open Finset
open scoped BigOperators

/-! ## Removing a small bad set -/

lemma filter_card_add_filter_not_card {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (s.filter p).card + (s.filter fun x => ¬ p x).card = s.card := by
  classical
  exact Finset.card_filter_add_card_filter_not p

lemma filter_not_card_real_ge_of_filter_card_real_le {α : Type*} (s : Finset α)
    (p : α → Prop) [DecidablePred p] {δ : ℝ}
    (hbad : ((s.filter p).card : ℝ) ≤ δ * (s.card : ℝ)) :
    ((s.filter fun x => ¬ p x).card : ℝ) ≥ (1 - δ) * (s.card : ℝ) := by
  classical
  have hsum := filter_card_add_filter_not_card s p
  have hreal :
      ((s.filter fun x => ¬ p x).card : ℝ) =
        (s.card : ℝ) - ((s.filter p).card : ℝ) := by
    nlinarith [show ((s.filter p).card + (s.filter fun x => ¬ p x).card : ℝ) =
      (s.card : ℝ) by exact_mod_cast hsum]
  rw [hreal]
  nlinarith

lemma filter_not_card_real_ge_of_filter_card_le_floor {α : Type*} (s : Finset α)
    (p : α → Prop) [DecidablePred p] {δ X : ℝ}
    (hXnonneg : 0 ≤ X)
    (hfloor : (s.filter p).card ≤ Nat.floor X)
    (hX : X ≤ δ * (s.card : ℝ)) :
    ((s.filter fun x => ¬ p x).card : ℝ) ≥ (1 - δ) * (s.card : ℝ) := by
  refine filter_not_card_real_ge_of_filter_card_real_le s p ?_
  have hfloor_real : ((s.filter p).card : ℝ) ≤ (Nat.floor X : ℝ) := by
    exact_mod_cast hfloor
  have hfloor_le : (Nat.floor X : ℝ) ≤ X := Nat.floor_le hXnonneg
  exact hfloor_real.trans (hfloor_le.trans hX)

lemma filter_large_of_bad_small {α : Type*} [DecidableEq α]
    (Q Bad : Finset α) {δ : ℝ}
    (hBad : Bad ⊆ Q)
    (hsmall : (Bad.card : ℝ) ≤ δ * (Q.card : ℝ)) :
    (((Q \ Bad).card : ℝ) ≥ (1 - δ) * (Q.card : ℝ)) := by
  have hreal : ((Q \ Bad).card : ℝ) = (Q.card : ℝ) - (Bad.card : ℝ) := by
    simpa using (Finset.cast_card_sdiff (R := ℝ) hBad)
  rw [hreal]
  nlinarith

lemma filter_large_of_three_bad_small {α : Type*} [DecidableEq α]
    (Q Bad₁ Bad₂ Bad₃ : Finset α) {δ₁ δ₂ δ₃ : ℝ}
    (hBad₁ : Bad₁ ⊆ Q) (hBad₂ : Bad₂ ⊆ Q) (hBad₃ : Bad₃ ⊆ Q)
    (hsmall₁ : (Bad₁.card : ℝ) ≤ δ₁ * (Q.card : ℝ))
    (hsmall₂ : (Bad₂.card : ℝ) ≤ δ₂ * (Q.card : ℝ))
    (hsmall₃ : (Bad₃.card : ℝ) ≤ δ₃ * (Q.card : ℝ)) :
    (((Q \ (Bad₁ ∪ Bad₂ ∪ Bad₃)).card : ℝ) ≥
      (1 - (δ₁ + δ₂ + δ₃)) * (Q.card : ℝ)) := by
  have hBad : Bad₁ ∪ Bad₂ ∪ Bad₃ ⊆ Q := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx12 | hx3
    · rcases Finset.mem_union.1 hx12 with hx1 | hx2
      · exact hBad₁ hx1
      · exact hBad₂ hx2
    · exact hBad₃ hx3
  refine filter_large_of_bad_small Q (Bad₁ ∪ Bad₂ ∪ Bad₃) hBad ?_
  have hcard_nat :
      (Bad₁ ∪ Bad₂ ∪ Bad₃).card ≤ Bad₁.card + Bad₂.card + Bad₃.card := by
    calc
      (Bad₁ ∪ Bad₂ ∪ Bad₃).card
          ≤ (Bad₁ ∪ Bad₂).card + Bad₃.card := Finset.card_union_le _ _
      _ ≤ (Bad₁.card + Bad₂.card) + Bad₃.card := by
            exact Nat.add_le_add_right (Finset.card_union_le Bad₁ Bad₂) Bad₃.card
      _ = Bad₁.card + Bad₂.card + Bad₃.card := by omega
  have hcard_real :
      ((Bad₁ ∪ Bad₂ ∪ Bad₃).card : ℝ) ≤
        (Bad₁.card : ℝ) + (Bad₂.card : ℝ) + (Bad₃.card : ℝ) := by
    exact_mod_cast hcard_nat
  nlinarith

/-! ## Pigeonhole over a finite range -/

lemma exists_fiber_card_mul_range_card_ge {α β : Type*} [DecidableEq β]
    (s : Finset α) (B : Finset β) (g : α → β)
    (hBne : B.Nonempty) (hB : ∀ x ∈ s, g x ∈ B) :
    ∃ b ∈ B, s.card ≤ B.card * (s.filter fun x => g x = b).card := by
  classical
  rcases Finset.exists_max_image B (fun b => (s.filter fun x => g x = b).card) hBne with
    ⟨b, hb, hbmax⟩
  refine ⟨b, hb, ?_⟩
  have hsum :
      s.card = ∑ b ∈ B, (s.filter fun x => g x = b).card := by
    exact Finset.card_eq_sum_card_fiberwise hB
  have hsum_le :
      (∑ b ∈ B, (s.filter fun x => g x = b).card) ≤
        ∑ _b ∈ B, (s.filter fun x => g x = b).card := by
    exact Finset.sum_le_sum hbmax
  rw [hsum]
  exact hsum_le.trans (by simp)

/-! ## Choosing one representative per fiber -/

noncomputable def chooseOnePerImage {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) : Finset α :=
  ((s.image g).attach.image fun b =>
    Classical.choose (Finset.mem_image.1 b.2))

lemma chooseOnePerImage_subset {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) :
    chooseOnePerImage s g ⊆ s := by
  classical
  intro x hx
  unfold chooseOnePerImage at hx
  rw [Finset.mem_image] at hx
  rcases hx with ⟨b, -, rfl⟩
  exact (Classical.choose_spec (Finset.mem_image.1 b.2)).1

lemma chooseOnePerImage_maps {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) {b : β} (hb : b ∈ s.image g) :
    g (Classical.choose (Finset.mem_image.1 hb)) = b := by
  exact (Classical.choose_spec (Finset.mem_image.1 hb)).2

lemma chooseOnePerImage_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) :
    ∀ x ∈ chooseOnePerImage s g, ∀ y ∈ chooseOnePerImage s g, g x = g y → x = y := by
  classical
  intro x hx y hy hxy
  unfold chooseOnePerImage at hx hy
  rw [Finset.mem_image] at hx
  rw [Finset.mem_image] at hy
  rcases hx with ⟨bx, hbx, rfl⟩
  rcases hy with ⟨byy, hby, rfl⟩
  have hbxval : g (Classical.choose (Finset.mem_image.1 bx.2)) = bx.1 := by
    exact chooseOnePerImage_maps s g bx.2
  have hbyval : g (Classical.choose (Finset.mem_image.1 byy.2)) = byy.1 := by
    exact chooseOnePerImage_maps s g byy.2
  have hbxy : bx = byy := by
    ext
    simpa [hbxval, hbyval] using hxy
  subst hbxy
  rfl

lemma chooseOnePerImage_card_eq_image_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) :
    (chooseOnePerImage s g).card = (s.image g).card := by
  classical
  unfold chooseOnePerImage
  calc
    (((s.image g).attach.image fun b =>
        Classical.choose (Finset.mem_image.1 b.2))).card =
        (s.image g).attach.card := by
          apply Finset.card_image_of_injective
          intro b₁ b₂ h
          have hb₁ : g (Classical.choose (Finset.mem_image.1 b₁.2)) = b₁.1 :=
            chooseOnePerImage_maps s g b₁.2
          have hb₂ : g (Classical.choose (Finset.mem_image.1 b₂.2)) = b₂.1 :=
            chooseOnePerImage_maps s g b₂.2
          ext
          simpa [hb₁, hb₂] using congrArg g h
    _ = (s.image g).card := by simp

lemma image_card_mul_fiber_bound_ge {α β : Type*} [DecidableEq β]
    (s : Finset α) (g : α → β) (C : ℕ)
    (hC : ∀ b ∈ s.image g, (s.filter fun x => g x = b).card ≤ C) :
    s.card ≤ C * (s.image g).card := by
  classical
  exact Finset.card_le_mul_card_image s C hC

lemma choose_one_per_fiber_card_lower {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) (C : ℕ)
    (hC : ∀ b ∈ s.image g, (s.filter fun x => g x = b).card ≤ C) :
    ∃ s' : Finset α,
      s' ⊆ s ∧
      (∀ x ∈ s', ∀ y ∈ s', g x = g y → x = y) ∧
      s.card ≤ C * s'.card := by
  classical
  refine ⟨chooseOnePerImage s g, chooseOnePerImage_subset s g,
    chooseOnePerImage_injOn s g, ?_⟩
  simpa [chooseOnePerImage_card_eq_image_card s g] using
    image_card_mul_fiber_bound_ge s g C hC

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFV/RadMultiplicity.lean
    ============================================================= -/

/-
Erdos Problem 202 -- radical multiplicity in BFV pruning.

For fixed radical, fixed omega, and bounded `hExp`, BFV Lemma 3.3 gives a
finite multiplicity bound.  This is a finite combinatorial theorem, but the
full exponent-vector encoding is kept isolated here so the final pruning file
only consumes a single clean interface.
-/


namespace Erdos202

open Finset
open scoped BigOperators

/--
Finite reciprocal-square bound used in the exponent-vector count.

This is the local BFV copy of the elementary estimate
`∑_{m=1}^H 1 / m^2 ≤ 2`.  It is duplicated here rather than importing
`P202Optimization`, which depends on the BFV input layer.
-/
lemma sum_inv_sq_le_two_bfv (H : ℕ) :
    (∑ ν ∈ Finset.range H, (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
  have hstrong : ∀ H : ℕ, 1 ≤ H →
      (∑ ν ∈ Finset.range H, (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2) ≤
        2 - 1 / (H : ℝ) := by
    intro H hH
    induction H with
    | zero =>
        cases hH
    | succ H ih =>
        cases H with
        | zero =>
            norm_num
        | succ H =>
            rw [Finset.sum_range_succ]
            have ih' :
                (∑ ν ∈ Finset.range (H + 1),
                    (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2)
                  ≤ 2 - 1 / ((H + 1 : ℕ) : ℝ) :=
              ih (by omega)
            have hstep :
                (1 : ℝ) / (((H + 1 + 1 : ℕ) : ℝ)) ^ 2 ≤
                  1 / ((H + 1 : ℕ) : ℝ) -
                    1 / (((H + 1 + 1 : ℕ) : ℝ)) := by
              have hcast :
                  (((H + 1 + 1 : ℕ) : ℝ)) = ((H + 1 : ℕ) : ℝ) + 1 := by
                norm_num
              rw [hcast]
              have hH1 : 0 < ((H + 1 : ℕ) : ℝ) := by positivity
              have hH2 : 0 < ((H + 1 : ℕ) : ℝ) + 1 := by positivity
              field_simp [hH1.ne', hH2.ne']
              ring_nf
              nlinarith [show 0 ≤ (H : ℝ) by positivity]
            calc
              (∑ ν ∈ Finset.range (H + 1),
                    (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2)
                  + 1 / (((H + 1 + 1 : ℕ) : ℝ)) ^ 2
                  ≤ (2 - 1 / ((H + 1 : ℕ) : ℝ))
                      + (1 / ((H + 1 : ℕ) : ℝ) -
                        1 / (((H + 1 + 1 : ℕ) : ℝ))) := by
                    gcongr
              _ = 2 - 1 / ((H + 2 : ℕ) : ℝ) := by
                    norm_num
                    ring
  by_cases hH : H = 0
  · simp [hH]
  · have hH1 : 1 ≤ H := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hH)
    exact (hstrong H hH1).trans (by
      have hnonneg : 0 ≤ (1 : ℝ) / (H : ℝ) := by positivity
      linarith)

private lemma one_div_sq_nat_prod_bfv {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    (1 : ℝ) / (((∏ i, f i : ℕ) : ℝ) ^ 2) =
      ∏ i, (1 : ℝ) / (((f i : ℕ) : ℝ) ^ 2) := by
  simp [one_div, Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_pow]

lemma rad_pos (n : ℕ) : 0 < rad n := by
  unfold rad
  exact Finset.prod_pos (fun p hp => (prime_of_mem_primeSupport hp).pos)

lemma rad_ne_zero (n : ℕ) : rad n ≠ 0 :=
  (rad_pos n).ne'

lemma primeSupport_rad_of_ne_zero {n : ℕ} (_hn : n ≠ 0) :
    primeSupport (rad n) = primeSupport n := by
  classical
  ext p
  constructor
  · intro hpRad
    have hp : Nat.Prime p := prime_of_mem_primeSupport hpRad
    have hpdvd : p ∣ rad n := Nat.dvd_of_factorization_pos (by
      unfold primeSupport at hpRad
      exact Finsupp.mem_support_iff.1 hpRad)
    unfold rad at hpdvd
    rcases (hp.prime.dvd_finset_prod_iff
        (S := primeSupport n) (fun x : ℕ => x)).1 hpdvd with ⟨q, hq, hpq⟩
    have hqprime : Nat.Prime q := prime_of_mem_primeSupport hq
    have hqp : q = p := (hqprime.dvd_iff_eq hp.ne_one).1 hpq
    simpa [hqp] using hq
  · intro hpN
    have hp : Nat.Prime p := prime_of_mem_primeSupport hpN
    have hpdvd : p ∣ rad n := by
      unfold rad
      exact Finset.dvd_prod_of_mem (fun x : ℕ => x) hpN
    exact mem_primeSupport_of_prime_dvd hp (rad_ne_zero n) hpdvd

lemma primeSupport_eq_of_rad_eq {q r : ℕ} (hq : q ≠ 0) (hqr : rad q = r) :
    primeSupport q = primeSupport r := by
  rw [← primeSupport_rad_of_ne_zero hq, hqr]

private lemma factorization_le_hExp_of_mem {q p : ℕ} (hp : p ∈ primeSupport q) :
    q.factorization p ≤ hExp q := by
  have hdvd : q.factorization p ∣ hExp q := by
    unfold hExp
    exact Finset.dvd_prod_of_mem (fun x : ℕ => q.factorization x) hp
  exact Nat.le_of_dvd (hExp_pos q) hdvd

private lemma rad_multiplicity_weight_sum_le
    (S : Finset ℕ) (C : Finset ℕ) (H : ℝ)
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hSupp : ∀ q ∈ S, primeSupport q = C)
    (hHbound : ∀ q ∈ S, (hExp q : ℝ) ≤ H) :
    (∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2)) ≤ (2 : ℝ) ^ C.card := by
  classical
  let Index := {p : ℕ // p ∈ C}
  let E : Finset (Index → ℕ) :=
    Fintype.piFinset fun _ : Index => Finset.range (Nat.floor H)
  let vec : ℕ → Index → ℕ := fun q p => q.factorization p.1 - 1
  let term : (Index → ℕ) → ℝ :=
    fun e => ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)
  have hH_nonneg : 0 ≤ H := by
    linarith
  have hvec_mem : ∀ q ∈ S, vec q ∈ E := by
    intro q hqS
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range]
    have hsupport : primeSupport q = C := hSupp q hqS
    have hpSupport : p.1 ∈ primeSupport q := by
      simp [hsupport, p.2]
    have hfac_pos : 1 ≤ q.factorization p.1 := by
      unfold primeSupport at hpSupport
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
    have hfac_le_hExp : q.factorization p.1 ≤ hExp q :=
      factorization_le_hExp_of_mem hpSupport
    have hfac_le_H : ((q.factorization p.1 : ℕ) : ℝ) ≤ H := by
      have hfac_le_hExp_real :
          ((q.factorization p.1 : ℕ) : ℝ) ≤ (hExp q : ℝ) := by
        exact_mod_cast hfac_le_hExp
      exact hfac_le_hExp_real.trans (hHbound q hqS)
    have hfac_floor : q.factorization p.1 ≤ Nat.floor H :=
      (Nat.le_floor_iff hH_nonneg).2 hfac_le_H
    dsimp [vec]
    omega
  have hvec_inj : Set.InjOn vec S := by
    intro q hqS q' hq'S hqq'
    apply Nat.eq_of_factorization_eq (hSpos q hqS) (hSpos q' hq'S)
    intro p
    by_cases hp : p ∈ C
    · have hcoord := congrFun hqq' ⟨p, hp⟩
      dsimp [vec] at hcoord
      have hsupport : primeSupport q = C := hSupp q hqS
      have hsupport' : primeSupport q' = C := hSupp q' hq'S
      have hfac_pos : 1 ≤ q.factorization p := by
        have hpSupport : p ∈ primeSupport q := by simpa [hsupport] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      have hfac_pos' : 1 ≤ q'.factorization p := by
        have hpSupport : p ∈ primeSupport q' := by simpa [hsupport'] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      omega
    · have hpq : p ∉ primeSupport q := by simpa [hSupp q hqS] using hp
      have hpq' : p ∉ primeSupport q' := by simpa [hSupp q' hq'S] using hp
      rw [Finsupp.notMem_support_iff.1 hpq, Finsupp.notMem_support_iff.1 hpq']
  have hterm_eq :
      ∀ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2) = term (vec q) := by
    intro q hqS
    have hsupport : primeSupport q = C := hSupp q hqS
    have hhexp :
        hExp q = ∏ p : Index, q.factorization p.1 := by
      calc
        hExp q = ∏ p ∈ C, q.factorization p := by
          simp [hExp, hsupport]
        _ = ∏ p : Index, q.factorization p.1 := by
          rw [Finset.prod_coe_sort]
    have hsucc : ∀ p : Index, vec q p + 1 = q.factorization p.1 := by
      intro p
      have hpSupport : p.1 ∈ primeSupport q := by simp [hsupport, p.2]
      have hpos : 1 ≤ q.factorization p.1 := by
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      dsimp [vec]
      omega
    rw [hhexp, one_div_sq_nat_prod_bfv]
    dsimp [term]
    apply Finset.prod_congr rfl
    intro p _hp
    rw [hsucc p]
  calc
    (∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2))
        = ∑ q ∈ S, term (vec q) := by
            apply Finset.sum_congr rfl
            intro q hq
            exact hterm_eq q hq
    _ = ∑ e ∈ S.image vec, term e := by
            rw [Finset.sum_image]
            intro q hq q' hq' hEq
            exact hvec_inj hq hq' hEq
    _ ≤ ∑ e ∈ E, term e := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro e he
                rcases Finset.mem_image.mp he with ⟨q, hq, rfl⟩
                exact hvec_mem q hq)
              (by
                intro e _heE _heNot
                dsimp [term]
                positivity)
    _ = ∏ _p : Index,
          ∑ ν ∈ Finset.range (Nat.floor H),
            (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2) := by
            change
              (∑ e ∈ Fintype.piFinset
                  (fun _ : Index => Finset.range (Nat.floor H)),
                ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)) =
              ∏ _p : Index,
                ∑ ν ∈ Finset.range (Nat.floor H),
                  (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)
            exact
              (Finset.sum_prod_piFinset
                (ι := Index) (κ := ℕ) (R := ℝ)
                (s := Finset.range (Nat.floor H))
                (g := fun _p ν => (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)))
    _ ≤ ∏ _p : Index, (2 : ℝ) := by
            exact Finset.prod_le_prod
              (s := (Finset.univ : Finset Index))
              (fun _p _hp => by positivity)
              (fun _p _hp => by
                exact sum_inv_sq_le_two_bfv (Nat.floor H))
    _ = (2 : ℝ) ^ C.card := by
            simp [Index]

/--
BFV Lemma 3.3 multiplicity bound.

For a fixed radical `r`, fixed `omega = K`, and `hExp ≤ H`, the possible
moduli are encoded by exponent vectors on the `K` primes in the radical.  BFV
counts those vectors by
`H^2 * (∑_{ν≥1} ν⁻²)^K ≤ H^2 * 2^K`.

The remaining formal work is finite: construct the exponent-vector injection
from `Nat.factorization`, prove the product bound from `hExp`, and apply
`sum_inv_sq_le_two_bfv`.  No analytic number theory is hidden in this target.
-/
theorem rad_multiplicity_bfv33
    (S : Finset ℕ) (r K : ℕ) (H : ℝ)
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hS : ∀ q ∈ S, rad q = r ∧ omega q = K ∧ (hExp q : ℝ) ≤ H) :
    (S.card : ℝ) ≤ H ^ 2 * (2 : ℝ) ^ K := by
  classical
  by_cases hSne : S.Nonempty
  · rcases hSne with ⟨q0, hq0S⟩
    let C : Finset ℕ := primeSupport r
    have hSupp : ∀ q ∈ S, primeSupport q = C := by
      intro q hq
      exact primeSupport_eq_of_rad_eq (hSpos q hq) (hS q hq).1
    have hCcard : C.card = K := by
      have homega := (hS q0 hq0S).2.1
      unfold omega at homega
      rw [hSupp q0 hq0S] at homega
      exact homega
    have hWeighted :
        (∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2)) ≤ (2 : ℝ) ^ K := by
      simpa [C, hCcard] using
        rad_multiplicity_weight_sum_le S C H hH hSpos hSupp
          (fun q hq => (hS q hq).2.2)
    have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
    have hHsq_pos : 0 < H ^ 2 := by positivity
    have hTermLower :
        ∀ q ∈ S, (1 : ℝ) / (H ^ 2) ≤
          (1 : ℝ) / ((hExp q : ℝ) ^ 2) := by
      intro q hq
      have hExp_nonneg : 0 ≤ (hExp q : ℝ) := by positivity
      have hExp_pos : 0 < (hExp q : ℝ) := by exact_mod_cast hExp_pos q
      have hExp_le : (hExp q : ℝ) ≤ H := (hS q hq).2.2
      have hsq_le : (hExp q : ℝ) ^ 2 ≤ H ^ 2 := by
        nlinarith [sq_nonneg (H - (hExp q : ℝ))]
      exact one_div_le_one_div_of_le (by positivity) hsq_le
    have hCardScaled :
        (S.card : ℝ) * ((1 : ℝ) / (H ^ 2)) ≤ (2 : ℝ) ^ K := by
      calc
        (S.card : ℝ) * ((1 : ℝ) / (H ^ 2))
            = ∑ _q ∈ S, ((1 : ℝ) / (H ^ 2)) := by
                simp
        _ ≤ ∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2) := by
                exact Finset.sum_le_sum hTermLower
        _ ≤ (2 : ℝ) ^ K := hWeighted
    have hmul := mul_le_mul_of_nonneg_right hCardScaled hHsq_pos.le
    field_simp [hHsq_pos.ne'] at hmul
    nlinarith
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.1 hSne
    have hnonneg : 0 ≤ H ^ 2 * (2 : ℝ) ^ K := by positivity
    simpa [hEmpty] using hnonneg

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFV/HExpRare.lean
    ============================================================= -/

/-
Erdos Problem 202 -- rarity of large hExp values in BFV pruning.

The paper-shaped BFV Lemma 3.2 estimate is isolated as a named theorem stub.
The super-`L` consumer form used by pruning is proved from that estimate by
explicit scale algebra.
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-- The hExp cutoff used in BFV Proposition 3.1. -/
noncomputable def hExpCutoff (N : ℕ) : ℝ :=
  Real.exp (Real.sqrt (Real.log (N : ℝ)))

lemma hExp_prime_pow {p e : ℕ} (hp : Nat.Prime p) :
    hExp (p ^ e) = if e = 0 then 1 else e := by
  by_cases he : e = 0
  · simp [he, hExp_one]
  · unfold hExp primeSupport
    rw [hp.factorization_pow]
    rw [Finsupp.support_single_ne_zero p he]
    rw [if_neg he]
    change (∏ q ∈ ({p} : Finset ℕ), Finsupp.single p e q) = e
    simp

noncomputable def hExpMomentTerm (s n : ℕ) : ℝ :=
  if n = 0 then 0 else (hExp n : ℝ) ^ s / (n : ℝ)

lemma hExpMomentTerm_nonneg (s n : ℕ) :
    0 ≤ hExpMomentTerm s n := by
  by_cases hn : n = 0
  · simp [hExpMomentTerm, hn]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp [hExpMomentTerm, hn]
    exact div_nonneg (by positivity) hnpos.le

lemma hExpMomentTerm_one (s : ℕ) : hExpMomentTerm s 1 = 1 := by
  simp [hExpMomentTerm, hExp_one]

lemma hExpMomentTerm_prime_pow {s p e : ℕ} (hp : Nat.Prime p) :
    hExpMomentTerm s (p ^ e) =
      if e = 0 then 1 else ((e : ℝ) ^ s / (p : ℝ) ^ e) := by
  by_cases he : e = 0
  · rw [he, pow_zero, hExpMomentTerm_one]
    simp
  · simp [hExpMomentTerm, hExp_prime_pow hp, he, hp.ne_zero, Nat.cast_pow]

lemma hExpMomentTerm_mul_of_coprime
    (s : ℕ) {m n : ℕ} (hcop : Nat.Coprime m n) :
    hExpMomentTerm s (m * n) =
      hExpMomentTerm s m * hExpMomentTerm s n := by
  by_cases hmn : m * n = 0
  · rcases hcop.eq_of_mul_eq_zero hmn with h | h
    · rcases h with ⟨hm, hn⟩
      simp [hExpMomentTerm, hm, hn]
    · rcases h with ⟨hm, hn⟩
      simp [hExpMomentTerm, hm, hn]
  · have hm : m ≠ 0 := left_ne_zero_of_mul hmn
    have hn : n ≠ 0 := right_ne_zero_of_mul hmn
    have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp [hExpMomentTerm, hmn, hm, hn, hExp_mul_of_coprime hcop,
      Nat.cast_mul, mul_pow]
    field_simp [hmreal, hnreal]

def squarefullSupport (n : ℕ) : Finset ℕ :=
  (primeSupport n).filter fun p => 2 ≤ n.factorization p

def squarefullKernel (n : ℕ) : ℕ :=
  exactBlock (squarefullSupport n) n

def IsSquarefull (n : ℕ) : Prop :=
  ∀ p ∈ primeSupport n, 2 ≤ n.factorization p

instance instDecidablePredIsSquarefull : DecidablePred IsSquarefull := by
  intro n
  unfold IsSquarefull
  infer_instance

lemma squarefullSupport_subset (n : ℕ) :
    squarefullSupport n ⊆ primeSupport n := by
  intro p hp
  exact (Finset.mem_filter.1 hp).1

lemma prime_of_mem_squarefullSupport {n p : ℕ}
    (hp : p ∈ squarefullSupport n) : Nat.Prime p :=
  prime_of_mem_primeSupport (squarefullSupport_subset n hp)

lemma squarefullKernel_dvd (n : ℕ) : squarefullKernel n ∣ n := by
  simp [squarefullKernel, exactBlock_dvd]

lemma squarefullKernel_ne_zero {n : ℕ} (hn : n ≠ 0) :
    squarefullKernel n ≠ 0 := by
  exact (Nat.pos_of_dvd_of_pos (squarefullKernel_dvd n)
    (Nat.pos_of_ne_zero hn)).ne'

lemma primeSupport_squarefullKernel {n : ℕ} :
    primeSupport (squarefullKernel n) = squarefullSupport n := by
  by_cases hn : n = 0
  · simp [squarefullKernel, squarefullSupport, primeSupport, exactBlock, hn]
  · exact primeSupport_exactBlock
      (fun p hp => prime_of_mem_squarefullSupport hp)
      (squarefullSupport_subset n)

lemma squarefullKernel_isSquarefull (n : ℕ) :
    IsSquarefull (squarefullKernel n) := by
  intro p hp
  rw [primeSupport_squarefullKernel] at hp
  have hp' := Finset.mem_filter.1 hp
  change 2 ≤ (exactBlock (squarefullSupport n) n).factorization p
  rw [factorization_exactBlock_of_mem
    (C := squarefullSupport n)
    (q := n)
    (p := p)
    (fun r hr => prime_of_mem_squarefullSupport hr)
    hp]
  exact hp'.2

lemma isSquarefull_mul_iff_of_coprime {m n : ℕ}
    (hcop : Nat.Coprime m n) :
    IsSquarefull (m * n) ↔ IsSquarefull m ∧ IsSquarefull n := by
  constructor
  · intro hmn
    constructor
    · intro p hp
      have hp_prod : p ∈ primeSupport (m * n) := by
        rw [primeSupport_mul_of_coprime hcop]
        exact Finset.mem_union_left _ hp
      have htwo := hmn p hp_prod
      have hpnot : p ∉ primeSupport n :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hp
      have hnzero : n.factorization p = 0 := by
        unfold primeSupport at hpnot
        exact Finsupp.notMem_support_iff.1 hpnot
      rw [Nat.factorization_mul_of_coprime hcop] at htwo
      simpa [Finsupp.add_apply, hnzero] using htwo
    · intro p hp
      have hp_prod : p ∈ primeSupport (m * n) := by
        rw [primeSupport_mul_of_coprime hcop]
        exact Finset.mem_union_right _ hp
      have htwo := hmn p hp_prod
      have hpnot : p ∉ primeSupport m :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop).symm) hp
      have hmzero : m.factorization p = 0 := by
        unfold primeSupport at hpnot
        exact Finsupp.notMem_support_iff.1 hpnot
      rw [Nat.factorization_mul_of_coprime hcop] at htwo
      simpa [Finsupp.add_apply, hmzero] using htwo
  · rintro ⟨hm, hn⟩ p hp
    rw [primeSupport_mul_of_coprime hcop] at hp
    rw [Nat.factorization_mul_of_coprime hcop]
    rcases Finset.mem_union.1 hp with hp | hp
    · have hpnot : p ∉ primeSupport n :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hp
      have hnzero : n.factorization p = 0 := by
        unfold primeSupport at hpnot
        exact Finsupp.notMem_support_iff.1 hpnot
      simpa [Finsupp.add_apply, hnzero] using hm p hp
    · have hpnot : p ∉ primeSupport m :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop).symm) hp
      have hmzero : m.factorization p = 0 := by
        unfold primeSupport at hpnot
        exact Finsupp.notMem_support_iff.1 hpnot
      simpa [Finsupp.add_apply, hmzero, add_comm] using hn p hp

lemma hExp_squarefullKernel_eq (n : ℕ) :
    hExp (squarefullKernel n) = hExp n := by
  by_cases hn : n = 0
  · simp [squarefullKernel, squarefullSupport, primeSupport, exactBlock, hExp, hn]
  · unfold hExp
    rw [primeSupport_squarefullKernel]
    have hprod :
        (∏ p ∈ primeSupport n, n.factorization p) =
          ∏ p ∈ squarefullSupport n, n.factorization p := by
      refine (Finset.prod_subset (squarefullSupport_subset n) ?_).symm
      intro p hpPrime hpNot
      have hpos : 1 ≤ n.factorization p := by
        unfold primeSupport at hpPrime
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero
          (Finsupp.mem_support_iff.1 hpPrime))
      have hnot_two : ¬ 2 ≤ n.factorization p := by
        intro htwo
        exact hpNot (Finset.mem_filter.2 ⟨hpPrime, htwo⟩)
      omega
    rw [hprod]
    apply Finset.prod_congr rfl
    intro p hp
    change (exactBlock (squarefullSupport n) n).factorization p =
      n.factorization p
    rw [factorization_exactBlock_of_mem
      (C := squarefullSupport n)
      (q := n)
      (p := p)
      (fun r hr => prime_of_mem_squarefullSupport hr)
      hp]

lemma squarefullKernel_mem_divisors {n : ℕ} (hn : n ≠ 0) :
    squarefullKernel n ∈ n.divisors := by
  exact Nat.mem_divisors.2
    ⟨squarefullKernel_dvd n, hn⟩

lemma hExp_pow_le_squarefull_divisor_sum (s : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (hExp n : ℝ) ^ s ≤
      ∑ d ∈ n.divisors.filter IsSquarefull, (hExp d : ℝ) ^ s := by
  classical
  have hmem :
      squarefullKernel n ∈ n.divisors.filter IsSquarefull := by
    exact Finset.mem_filter.2
      ⟨squarefullKernel_mem_divisors hn, squarefullKernel_isSquarefull n⟩
  have hterm :
      (hExp (squarefullKernel n) : ℝ) ^ s = (hExp n : ℝ) ^ s := by
    rw [hExp_squarefullKernel_eq]
  calc
    (hExp n : ℝ) ^ s = (hExp (squarefullKernel n) : ℝ) ^ s := hterm.symm
    _ ≤ ∑ d ∈ n.divisors.filter IsSquarefull, (hExp d : ℝ) ^ s :=
        Finset.single_le_sum
          (fun d _hd => pow_nonneg (by positivity : 0 ≤ (hExp d : ℝ)) s)
          hmem

lemma nat_pow_le_factorial_mul_exp_quarter (s e : ℕ) :
    ((e : ℝ) ^ s) ≤
      (4 : ℝ) ^ s * (s.factorial : ℝ) * Real.exp ((e : ℝ) / 4) := by
  have hx : 0 ≤ (e : ℝ) / 4 := by positivity
  have h := Real.pow_div_factorial_le_exp ((e : ℝ) / 4) hx s
  have hfac : ((s.factorial : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero s
  have h1 :
      ((e : ℝ) / 4) ^ s ≤
        (s.factorial : ℝ) * Real.exp ((e : ℝ) / 4) := by
    have hmul := mul_le_mul_of_nonneg_left h
      (by positivity : 0 ≤ (s.factorial : ℝ))
    field_simp [hfac] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  calc
    (e : ℝ) ^ s = (4 : ℝ) ^ s * ((e : ℝ) / 4) ^ s := by
      rw [div_pow]
      field_simp
    _ ≤ (4 : ℝ) ^ s *
          ((s.factorial : ℝ) * Real.exp ((e : ℝ) / 4)) := by
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (4 : ℝ) ^ s * (s.factorial : ℝ) *
          Real.exp ((e : ℝ) / 4) := by
      ring

lemma exp_quarter_lt_two : Real.exp ((1 : ℝ) / 4) < 2 := by
  have hpow_lt : Real.exp ((1 : ℝ) / 4) ^ 4 < (2 : ℝ) ^ 4 := by
    calc
      Real.exp ((1 : ℝ) / 4) ^ 4 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ < 3 := Real.exp_one_lt_three
      _ < (2 : ℝ) ^ 4 := by norm_num
  by_contra hnot
  have hge : (2 : ℝ) ≤ Real.exp ((1 : ℝ) / 4) := le_of_not_gt hnot
  have hpow_ge :
      (2 : ℝ) ^ 4 ≤ Real.exp ((1 : ℝ) / 4) ^ 4 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hge 4
  exact not_lt_of_ge hpow_ge hpow_lt

lemma exp_quarter_div_two_lt_one : Real.exp ((1 : ℝ) / 4) / 2 < 1 := by
  nlinarith [exp_quarter_lt_two]

lemma exp_quarter_lt_three_halves :
    Real.exp ((1 : ℝ) / 4) < 3 / 2 := by
  have hpow_lt : Real.exp ((1 : ℝ) / 4) ^ 4 < ((3 : ℝ) / 2) ^ 4 := by
    calc
      Real.exp ((1 : ℝ) / 4) ^ 4 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ < 3 := Real.exp_one_lt_three
      _ < ((3 : ℝ) / 2) ^ 4 := by norm_num
  by_contra hnot
  have hge : (3 : ℝ) / 2 ≤ Real.exp ((1 : ℝ) / 4) := le_of_not_gt hnot
  have hpow_ge :
      ((3 : ℝ) / 2) ^ 4 ≤ Real.exp ((1 : ℝ) / 4) ^ 4 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2) hge 4
  exact not_lt_of_ge hpow_ge hpow_lt

lemma exp_quarter_div_two_le_three_quarters :
    Real.exp ((1 : ℝ) / 4) / 2 ≤ 3 / 4 := by
  nlinarith [exp_quarter_lt_three_halves]

lemma hExp_large_rankin_sum_le
    (N s : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    (((Finset.Icc 1 N).filter fun n => H < (hExp n : ℝ)).card : ℝ) * H ^ s
      ≤ ∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s := by
  classical
  let Bad := (Finset.Icc 1 N).filter fun n => H < (hExp n : ℝ)
  have hpoint :
      ∀ n ∈ Bad, H ^ s ≤ (hExp n : ℝ) ^ s := by
    intro n hn
    exact pow_le_pow_left₀ hH (le_of_lt (Finset.mem_filter.1 hn).2) s
  calc
    (((Finset.Icc 1 N).filter fun n => H < (hExp n : ℝ)).card : ℝ) * H ^ s
        = ∑ n ∈ Bad, H ^ s := by
            simp [Bad, mul_comm]
    _ ≤ ∑ n ∈ Bad, (hExp n : ℝ) ^ s := by
            exact Finset.sum_le_sum (fun n hn => hpoint n hn)
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _)
              (by
                intro n _hn _hnot
                positivity)

lemma hExp_pow_le_divisor_sum (s : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (hExp n : ℝ) ^ s ≤
      ∑ d ∈ n.divisors, (hExp d : ℝ) ^ s := by
  classical
  have hnmem : n ∈ n.divisors := Nat.mem_divisors_self n hn
  exact Finset.single_le_sum
    (fun d _hd => pow_nonneg (by positivity : 0 ≤ (hExp d : ℝ)) s)
    hnmem

lemma hExp_moment_sum_le_divisor_multiple_sum (N s : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
      ∑ d ∈ Finset.Icc 1 N,
        (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
          (hExp d : ℝ) ^ s := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
        ≤ ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ n.divisors, (hExp d : ℝ) ^ s := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hnIcc := Finset.mem_Icc.mp hn
          exact hExp_pow_le_divisor_sum s
            (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1))
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ n),
              (hExp d : ℝ) ^ s := by
          refine Finset.sum_le_sum ?_
          intro n hn
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            rw [Finset.mem_filter]
            have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
            have hnIcc := Finset.mem_Icc.mp hn
            have hdle : d ≤ N :=
              (Nat.le_of_dvd
                (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1) hdn).trans hnIcc.2
            exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hdpos, hdle⟩, hdn⟩
          · intro d _hd _hnot
            positivity
    _ = ∑ d ∈ Finset.Icc 1 N,
          (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
            (hExp d : ℝ) ^ s := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          calc
            (∑ x ∈ Finset.Icc 1 N,
                if d ∣ x then (hExp d : ℝ) ^ s else 0)
                =
              ∑ x ∈ Finset.Icc 1 N,
                if d ∣ x then (hExp d : ℝ) ^ s else 0 := by
                rfl
            _ = ∑ x ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n),
                  (hExp d : ℝ) ^ s := by
                rw [Finset.sum_filter]
            _ = (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
                  (hExp d : ℝ) ^ s := by
                simp [Finset.sum_const, nsmul_eq_mul]

lemma hExp_moment_sum_le_recip_sum (N s : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
      (N : ℝ) *
        ∑ d ∈ Finset.Icc 1 N, (hExp d : ℝ) ^ s / (d : ℝ) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
        ≤ ∑ d ∈ Finset.Icc 1 N,
            (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
              (hExp d : ℝ) ^ s :=
          hExp_moment_sum_le_divisor_multiple_sum N s
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
            ((N : ℝ) / (d : ℝ)) * (hExp d : ℝ) ^ s := by
          refine Finset.sum_le_sum ?_
          intro d hd
          have hdIcc := Finset.mem_Icc.mp hd
          have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
          have hcard_nat :
              ((Finset.Icc 1 N).filter fun n => d ∣ n).card ≤ N / d := by
            exact card_Icc_filter_dvd_le_div N d hdpos
          have hcard_real :
              (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) ≤
                (N : ℝ) / (d : ℝ) := by
            exact (Nat.cast_le.mpr hcard_nat).trans Nat.cast_div_le
          exact mul_le_mul_of_nonneg_right hcard_real (by positivity)
    _ = ∑ d ∈ Finset.Icc 1 N,
          (N : ℝ) * ((hExp d : ℝ) ^ s / (d : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdIcc := Finset.mem_Icc.mp hd
          have hdne : (d : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hdIcc.1))
          field_simp [hdne]
    _ = (N : ℝ) *
          ∑ d ∈ Finset.Icc 1 N, (hExp d : ℝ) ^ s / (d : ℝ) := by
          rw [Finset.mul_sum]

lemma hExp_moment_sum_le_squarefull_divisor_multiple_sum (N s : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
      ∑ d ∈ Finset.Icc 1 N,
        if IsSquarefull d then
          (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
            (hExp d : ℝ) ^ s
        else 0 := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
        ≤ ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ n.divisors.filter IsSquarefull, (hExp d : ℝ) ^ s := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hnIcc := Finset.mem_Icc.mp hn
          exact hExp_pow_le_squarefull_divisor_sum s
            (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1))
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ (Finset.Icc 1 N).filter
                (fun d => d ∣ n ∧ IsSquarefull d),
              (hExp d : ℝ) ^ s := by
          refine Finset.sum_le_sum ?_
          intro n hn
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            rw [Finset.mem_filter]
            rw [Finset.mem_filter] at hd
            have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd.1
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hd.1
            have hnIcc := Finset.mem_Icc.mp hn
            have hdle : d ≤ N :=
              (Nat.le_of_dvd
                (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1) hdn).trans hnIcc.2
            exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hdpos, hdle⟩,
              hdn, hd.2⟩
          · intro d _hd _hnot
            positivity
    _ = ∑ d ∈ Finset.Icc 1 N,
          if IsSquarefull d then
            (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
              (hExp d : ℝ) ^ s
          else 0 := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hsq : IsSquarefull d
          · simp [hsq]
            calc
              (∑ x ∈ Finset.Icc 1 N,
                  if d ∣ x then (hExp d : ℝ) ^ s else 0)
                  = ∑ x ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n),
                      (hExp d : ℝ) ^ s := by
                    rw [Finset.sum_filter]
              _ = (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
                    (hExp d : ℝ) ^ s := by
                    simp [Finset.sum_const, nsmul_eq_mul]
          · simp [hsq]

lemma hExp_moment_sum_le_squarefull_recip_sum (N s : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
      (N : ℝ) *
        ∑ d ∈ Finset.Icc 1 N,
          if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0 := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
        ≤ ∑ d ∈ Finset.Icc 1 N,
            if IsSquarefull d then
              (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
                (hExp d : ℝ) ^ s
            else 0 :=
          hExp_moment_sum_le_squarefull_divisor_multiple_sum N s
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
          if IsSquarefull d then
            ((N : ℝ) / (d : ℝ)) * (hExp d : ℝ) ^ s
          else 0 := by
          refine Finset.sum_le_sum ?_
          intro d hd
          by_cases hsq : IsSquarefull d
          · simp [hsq]
            have hdIcc := Finset.mem_Icc.mp hd
            have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
            have hcard_nat :
                ((Finset.Icc 1 N).filter fun n => d ∣ n).card ≤ N / d := by
              exact card_Icc_filter_dvd_le_div N d hdpos
            have hcard_real :
                (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) ≤
                  (N : ℝ) / (d : ℝ) := by
              exact (Nat.cast_le.mpr hcard_nat).trans Nat.cast_div_le
            exact mul_le_mul_of_nonneg_right hcard_real (by positivity)
          · simp [hsq]
    _ = ∑ d ∈ Finset.Icc 1 N,
          (N : ℝ) *
            (if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hsq : IsSquarefull d
          · simp [hsq]
            have hdIcc := Finset.mem_Icc.mp hd
            have hdne : (d : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hdIcc.1))
            field_simp [hdne]
          · simp [hsq]
    _ = (N : ℝ) *
          ∑ d ∈ Finset.Icc 1 N,
            if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0 := by
          rw [Finset.mul_sum]

noncomputable def squarefullMomentTerm (s n : ℕ) : ℝ :=
  if IsSquarefull n then hExpMomentTerm s n else 0

lemma squarefullMomentTerm_nonneg (s n : ℕ) :
    0 ≤ squarefullMomentTerm s n := by
  unfold squarefullMomentTerm
  by_cases hsq : IsSquarefull n <;> simp [hsq, hExpMomentTerm_nonneg]

lemma one_isSquarefull : IsSquarefull 1 := by
  intro p hp
  simp [primeSupport] at hp

lemma squarefullMomentTerm_one (s : ℕ) :
    squarefullMomentTerm s 1 = 1 := by
  simp [squarefullMomentTerm, one_isSquarefull, hExpMomentTerm_one]

lemma not_isSquarefull_prime {p : ℕ} (hp : Nat.Prime p) :
    ¬ IsSquarefull p := by
  intro hsq
  have hmem : p ∈ primeSupport p := by
    unfold primeSupport
    rw [Finsupp.mem_support_iff]
    exact Nat.Prime.factorization_self hp ▸ one_ne_zero
  have htwo := hsq p hmem
  rw [Nat.Prime.factorization_self hp] at htwo
  omega

lemma squarefullMomentTerm_prime_pow {s p e : ℕ} (hp : Nat.Prime p) :
    squarefullMomentTerm s (p ^ e) =
      if e = 0 then 1
      else if e = 1 then 0
      else ((e : ℝ) ^ s / (p : ℝ) ^ e) := by
  by_cases he0 : e = 0
  · subst e
    simp [squarefullMomentTerm, one_isSquarefull, hExpMomentTerm_one]
  · by_cases he1 : e = 1
    · subst e
      simp [squarefullMomentTerm, not_isSquarefull_prime hp]
    · have hsq : IsSquarefull (p ^ e) := by
        intro q hq
        have hqprime : Nat.Prime q := prime_of_mem_primeSupport hq
        have hqeq : q = p := by
          have hfac_ne : (p ^ e).factorization q ≠ 0 := by
            unfold primeSupport at hq
            exact Finsupp.mem_support_iff.1 hq
          rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply,
            nsmul_eq_mul] at hfac_ne
          have hpq_ne : p.factorization q ≠ 0 := by
            intro hpq
            simp [hpq] at hfac_ne
          exact (hp.eq_of_factorization_pos hpq_ne).symm
        subst q
        rw [Nat.factorization_pow_self hp]
        omega
      simp [squarefullMomentTerm, hExpMomentTerm_prime_pow hp, he0, he1, hsq]

lemma squarefullMomentTerm_mul_of_coprime
    (s : ℕ) {m n : ℕ} (hcop : Nat.Coprime m n) :
    squarefullMomentTerm s (m * n) =
      squarefullMomentTerm s m * squarefullMomentTerm s n := by
  by_cases hm : IsSquarefull m
  · by_cases hn : IsSquarefull n
    · have hmn : IsSquarefull (m * n) :=
        (isSquarefull_mul_iff_of_coprime hcop).2 ⟨hm, hn⟩
      simp [squarefullMomentTerm, hm, hn, hmn,
        hExpMomentTerm_mul_of_coprime s hcop]
    · have hmn : ¬ IsSquarefull (m * n) := by
        intro h
        exact hn ((isSquarefull_mul_iff_of_coprime hcop).1 h).2
      simp [squarefullMomentTerm, hn, hmn]
  · have hmn : ¬ IsSquarefull (m * n) := by
      intro h
      exact hm ((isSquarefull_mul_iff_of_coprime hcop).1 h).1
    simp [squarefullMomentTerm, hm, hmn]

lemma squarefullMomentTerm_prime_pow_summable
    (s p : ℕ) (hp : Nat.Prime p) :
    Summable (fun e : ℕ => ‖squarefullMomentTerm s (p ^ e)‖) := by
  have hp_real_gt_one : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hp_real_pos : 0 < (p : ℝ) := zero_lt_one.trans hp_real_gt_one
  have hr : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hp_real_pos]
    exact inv_lt_one_of_one_lt₀ hp_real_gt_one
  have hgeom :
      Summable fun e : ℕ =>
        ‖(((e : ℝ) ^ s) * ((p : ℝ)⁻¹) ^ e : ℝ)‖ :=
    summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) s hr
  refine hgeom.congr_atTop ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with e he
  have he0 : e ≠ 0 := by omega
  have he1 : e ≠ 1 := by omega
  rw [squarefullMomentTerm_prime_pow hp]
  simp [he0, he1, div_eq_mul_inv, inv_pow]

lemma squarefullMomentTerm_prime_pow_le_factorial_exp
    {s p e : ℕ} (hp : Nat.Prime p) (he : 2 ≤ e) :
    squarefullMomentTerm s (p ^ e) ≤
      ((4 : ℝ) ^ s * (s.factorial : ℝ) *
        Real.exp ((e : ℝ) / 4)) / (p : ℝ) ^ e := by
  have he0 : e ≠ 0 := by omega
  have he1 : e ≠ 1 := by omega
  have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_pos : 0 < (p : ℝ) ^ e := pow_pos hp_real_pos e
  rw [squarefullMomentTerm_prime_pow hp]
  simp [he0, he1]
  exact div_le_div_of_nonneg_right
    (nat_pow_le_factorial_mul_exp_quarter s e) hp_pos.le

lemma exp_e_div_four_le_three_halves_pow (e : ℕ) :
    Real.exp ((e : ℝ) / 4) ≤ ((3 : ℝ) / 2) ^ e := by
  calc
    Real.exp ((e : ℝ) / 4) = Real.exp ((1 : ℝ) / 4) ^ e := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ ((3 : ℝ) / 2) ^ e :=
      pow_le_pow_left₀ (Real.exp_pos _).le
        (le_of_lt exp_quarter_lt_three_halves) e

lemma squarefullMomentTerm_prime_pow_le_geo
    {s p e : ℕ} (hp : Nat.Prime p) (he : 2 ≤ e) :
    squarefullMomentTerm s (p ^ e) ≤
      (4 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) / (p : ℝ) ^ 2) *
        ((3 : ℝ) / 4) ^ e := by
  let A : ℝ := (4 : ℝ) ^ s * (s.factorial : ℝ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hden_pos : 0 < (p : ℝ) ^ e := pow_pos hp_real_pos e
  have hden2_pos : 0 < (p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2) := by positivity
  have hp_pow_ge :
      (p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2) ≤ (p : ℝ) ^ e := by
    calc
      (p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)
          ≤ (p : ℝ) ^ 2 * (p : ℝ) ^ (e - 2) := by
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp_two (e - 2))
              (by positivity)
      _ = (p : ℝ) ^ e := by
            rw [← pow_add]
            congr 1
            omega
  have hstep1 :
      squarefullMomentTerm s (p ^ e) ≤
        A * Real.exp ((e : ℝ) / 4) / (p : ℝ) ^ e := by
    simpa [A, mul_assoc] using
      squarefullMomentTerm_prime_pow_le_factorial_exp (s := s) hp he
  have hstep2 :
      A * Real.exp ((e : ℝ) / 4) / (p : ℝ) ^ e ≤
        A * Real.exp ((e : ℝ) / 4) /
          ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) := by
    exact div_le_div_of_nonneg_left
      (mul_nonneg hA_nonneg (Real.exp_pos _).le)
      hden2_pos hp_pow_ge
  have hstep3 :
      A * Real.exp ((e : ℝ) / 4) /
          ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) ≤
        A * ((3 : ℝ) / 2) ^ e /
          ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exp_e_div_four_le_three_halves_pow e) hA_nonneg)
      hden2_pos.le
  have hidentity :
      A * ((3 : ℝ) / 2) ^ e /
          ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) =
        (4 * A / (p : ℝ) ^ 2) * ((3 : ℝ) / 4) ^ e := by
    have h2pos : (0 : ℝ) < 2 ^ (e - 2) := by positivity
    have hp2pos : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    rw [show e = 2 + (e - 2) by omega]
    rw [pow_add, pow_add]
    norm_num
    field_simp [hp2pos.ne', h2pos.ne']
    have hmul :
        ((3 : ℝ) / 4) ^ (e - 2) * 2 ^ (e - 2) =
          ((3 : ℝ) / 2) ^ (e - 2) := by
      rw [← mul_pow]
      norm_num
    rw [← hmul]
    ring_nf
  exact hstep1.trans (hstep2.trans (hstep3.trans_eq hidentity))

lemma squarefullMomentTerm_prime_pow_tsum_le
    (s p : ℕ) (hp : Nat.Prime p) :
    (∑' e : ℕ, squarefullMomentTerm s (p ^ e)) ≤
      1 + 16 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) / (p : ℝ) ^ 2 := by
  let A : ℝ := (4 : ℝ) ^ s * (s.factorial : ℝ)
  let C : ℝ := 4 * A / (p : ℝ) ^ 2
  let g : ℕ → ℝ := fun e => (if e = 0 then 1 else 0) + C * ((3 : ℝ) / 4) ^ e
  have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hlhs : Summable fun e : ℕ => squarefullMomentTerm s (p ^ e) :=
    (squarefullMomentTerm_prime_pow_summable s p hp).of_norm
  have hsingle : Summable fun e : ℕ => if e = 0 then (1 : ℝ) else 0 :=
    (hasSum_single (0 : ℕ)
      (f := fun e : ℕ => if e = 0 then (1 : ℝ) else 0)
      (by intro e he; simp [he])).summable
  have hgeo : Summable fun e : ℕ => C * ((3 : ℝ) / 4) ^ e :=
    (summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 : ℝ) / 4 < 1)).mul_left C
  have hg : Summable g := hsingle.add hgeo
  have hpoint :
      ∀ e : ℕ, squarefullMomentTerm s (p ^ e) ≤ g e := by
    intro e
    by_cases he0 : e = 0
    · subst e
      change squarefullMomentTerm s 1 ≤ g 0
      rw [squarefullMomentTerm_one]
      simp [g]
      exact hC_nonneg
    · by_cases he1 : e = 1
      · subst e
        rw [squarefullMomentTerm_prime_pow hp]
        simp [g]
        dsimp [C]
        positivity
      · have he2 : 2 ≤ e := by omega
        have h := squarefullMomentTerm_prime_pow_le_geo
          (s := s) (p := p) (e := e) hp he2
        simpa [g, C, A, he0] using h
  calc
    (∑' e : ℕ, squarefullMomentTerm s (p ^ e))
        ≤ ∑' e : ℕ, g e := hlhs.tsum_le_tsum hpoint hg
    _ = 1 + C * (∑' e : ℕ, ((3 : ℝ) / 4) ^ e) := by
          dsimp [g]
          rw [hsingle.tsum_add hgeo]
          rw [tsum_eq_single (0 : ℕ)
            (f := fun e : ℕ => if e = 0 then (1 : ℝ) else 0)]
          · rw [tsum_mul_left]
            simp
          · intro e he
            simp [he]
    _ = 1 + 16 * A / (p : ℝ) ^ 2 := by
          rw [tsum_geometric_of_lt_one
            (by norm_num : (0 : ℝ) ≤ 3 / 4)
            (by norm_num : (3 : ℝ) / 4 < 1)]
          dsimp [C]
          norm_num
          ring
    _ = 1 + 16 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) / (p : ℝ) ^ 2 := by
          rfl

lemma sum_Icc_inv_sq_le_two_bfv (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 2 := by
  classical
  have hIcc :
      Finset.Icc 1 N = (Finset.range N).image (fun ν : ℕ => ν + 1) := by
    ext d
    constructor
    · intro hd
      have hdIcc := Finset.mem_Icc.mp hd
      exact Finset.mem_image.2
        ⟨d - 1, Finset.mem_range.2 (Nat.sub_one_lt_of_le hdIcc.1 hdIcc.2),
          by omega⟩
    · intro hd
      rcases Finset.mem_image.1 hd with ⟨ν, hν, rfl⟩
      exact Finset.mem_Icc.2
        ⟨by omega, Nat.succ_le_iff.2 (Finset.mem_range.1 hν)⟩
  rw [hIcc]
  rw [Finset.sum_image]
  ·
    simpa using sum_inv_sq_le_two_bfv N
  · intro a _ha b _hb h
    exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using h)

lemma primes_Icc_inv_sq_sum_le_two_bfv (N : ℕ) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset Nat.Prime (Finset.Icc 1 N))
    (by
      intro p _hp _hnot
      positivity)).trans (sum_Icc_inv_sq_le_two_bfv N)

lemma finite_euler_product_one_add_sq_le_exp_sum
    (s : Finset ℕ) {z : ℝ} (hz : 0 ≤ z) :
    s.prod (fun p : ℕ => (1 : ℝ) + z / (p : ℝ) ^ 2) ≤
      Real.exp (z * s.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ) ^ 2)) := by
  calc
    s.prod (fun p : ℕ => (1 : ℝ) + z / (p : ℝ) ^ 2)
        ≤ s.prod (fun p : ℕ => Real.exp (z / (p : ℝ) ^ 2)) := by
          exact Finset.prod_le_prod
            (s := s)
            (f := fun p : ℕ => (1 : ℝ) + z / (p : ℝ) ^ 2)
            (g := fun p : ℕ => Real.exp (z / (p : ℝ) ^ 2))
            (fun p hp => by
              positivity)
            (fun p hp => by
              have h := Real.add_one_le_exp (z / (p : ℝ) ^ 2)
              linarith)
    _ = Real.exp (s.sum (fun p : ℕ => z / (p : ℝ) ^ 2)) := by
          rw [← Real.exp_sum]
    _ = Real.exp (z * s.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ) ^ 2)) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring

lemma finite_squarefull_eulerProduct_le
    (N s : ℕ) :
    (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
        ∑' e : ℕ, squarefullMomentTerm s (p ^ e))
      ≤ Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
  classical
  let P := (Finset.Icc 1 N).filter Nat.Prime
  let A : ℝ := (4 : ℝ) ^ s * (s.factorial : ℝ)
  let z : ℝ := 16 * A
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hz_nonneg : 0 ≤ z := by
    dsimp [z]
    positivity
  have hlocal :
      ∀ p ∈ P,
        (∑' e : ℕ, squarefullMomentTerm s (p ^ e)) ≤
          (1 : ℝ) + z / (p : ℝ) ^ 2 := by
    intro p hp
    have hpprime : Nat.Prime p := (Finset.mem_filter.1 hp).2
    simpa [z, A] using squarefullMomentTerm_prime_pow_tsum_le s p hpprime
  calc
    (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
        ∑' e : ℕ, squarefullMomentTerm s (p ^ e))
        = P.prod fun p => ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
          change (P.filter Nat.Prime).prod
              (fun p => ∑' e : ℕ, squarefullMomentTerm s (p ^ e)) =
            P.prod (fun p => ∑' e : ℕ, squarefullMomentTerm s (p ^ e))
          rw [Finset.filter_true_of_mem]
          intro p hp
          exact (Finset.mem_filter.1 hp).2
    _ ≤ P.prod fun p => (1 : ℝ) + z / (p : ℝ) ^ 2 := by
          exact Finset.prod_le_prod
            (s := P)
            (f := fun p => ∑' e : ℕ, squarefullMomentTerm s (p ^ e))
            (g := fun p => (1 : ℝ) + z / (p : ℝ) ^ 2)
            (fun p hp => by
              have hsum_nonneg :
                  0 ≤ ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
                exact tsum_nonneg (fun e => squarefullMomentTerm_nonneg s (p ^ e))
              exact hsum_nonneg)
            hlocal
    _ ≤ Real.exp (z * P.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ) ^ 2)) :=
          finite_euler_product_one_add_sq_le_exp_sum P hz_nonneg
    _ ≤ Real.exp (z * 2) := by
          exact Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left
              (by
                simpa [P] using primes_Icc_inv_sq_sum_le_two_bfv N)
              hz_nonneg)
    _ = Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
          congr 1
          dsimp [z, A]
          ring

lemma eventually_log_const_mul_sqrt_loglog_le_mul_sqrt_loglog
    (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (A * Real.sqrt (Real.log (Real.log (N : ℝ)))) ≤
        δ * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  have hδ2 : 0 < δ / 2 := by positivity
  have hsmall :
      (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ)))) =o[atTop]
        fun N : ℕ => Real.sqrt (Real.log (Real.log (N : ℝ))) := by
    have h :=
      (isLittleO_log_rpow_atTop
        (show (0 : ℝ) < (1 / 2 : ℝ) by norm_num)).comp_tendsto
          tendsto_loglog_nat_atTop
    simpa [Real.sqrt_eq_rpow] using h
  filter_upwards [Asymptotics.isLittleO_iff.mp hsmall hδ2,
      eventually_sqrt_loglog_ge (2 * |Real.log A| / δ),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 1] with
    N hlog_small hsqrt_large hY_large
  set Y := Real.log (Real.log (N : ℝ))
  have hY_pos : 0 < Y := zero_lt_one.trans_le (by simpa [Y] using hY_large)
  have hsqrt_pos : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY_pos
  have hlogY_nonneg : 0 ≤ Real.log Y := Real.log_nonneg (by simpa [Y] using hY_large)
  have hleft_norm :
      ‖Real.log Y‖ = Real.log Y := by
    rw [Real.norm_of_nonneg hlogY_nonneg]
  have hright_norm :
      ‖Real.sqrt Y‖ = Real.sqrt Y := by
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg Y)]
  have hlogY_le : Real.log Y ≤ (δ / 2) * Real.sqrt Y := by
    simpa [Y, hleft_norm, hright_norm] using hlog_small
  have hconst : Real.log A ≤ (δ / 2) * Real.sqrt Y := by
    have hmul : 2 * |Real.log A| ≤ δ * Real.sqrt Y :=
      by simpa [mul_comm] using (div_le_iff₀ hδ).1 hsqrt_large
    have hlogA_le_abs : Real.log A ≤ |Real.log A| := le_abs_self _
    linarith
  have hlogsqrt : Real.log (Real.sqrt Y) = Real.log Y / 2 :=
    Real.log_sqrt hY_pos.le
  calc
    Real.log (A * Real.sqrt Y)
        = Real.log A + Real.log (Real.sqrt Y) := by
            rw [Real.log_mul hA.ne' hsqrt_pos.ne']
    _ = Real.log A + Real.log Y / 2 := by rw [hlogsqrt]
    _ ≤ (δ / 2) * Real.sqrt Y + ((δ / 2) * Real.sqrt Y) / 2 := by
            have hhalf : Real.log Y / 2 ≤ ((δ / 2) * Real.sqrt Y) / 2 := by
              exact div_le_div_of_nonneg_right hlogY_le (by norm_num)
            nlinarith
    _ ≤ δ * Real.sqrt Y := by nlinarith

lemma eventually_squarefull_moment_factor_le_Zscale
    (B : ℝ) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop,
      let s : ℕ := Nat.ceil (B * Real.sqrt (Real.log (Real.log (N : ℝ))))
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) ≤ Zscale N := by
  let B' : ℝ := B + 1
  let C : ℝ := 4 * B'
  have hB' : 0 < B' := by dsimp [B']; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < (1 / (12 * B') : ℝ) := by positivity
  filter_upwards [eventually_log_const_mul_sqrt_loglog_le_mul_sqrt_loglog
      C (1 / (12 * B')) hC hδ,
      eventually_sqrt_loglog_ge (max 1 (1 / B)),
      tendsto_loglog_nat_atTop.eventually_ge_atTop (max 1 (12 * Real.log 32)),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N hlogC hsqrt_large hY_large hNlarge_nat
  set Y := Real.log (Real.log (N : ℝ))
  set R := Real.sqrt Y
  set s : ℕ := Nat.ceil (B * R)
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hY_ge_one : 1 ≤ Y := (le_max_left _ _).trans (by simpa [Y] using hY_large)
  have hY_ge_log32 : 12 * Real.log 32 ≤ Y :=
    (le_max_right _ _).trans (by simpa [Y] using hY_large)
  have hY_pos : 0 < Y := zero_lt_one.trans_le hY_ge_one
  have hR_pos : 0 < R := by simpa [R] using Real.sqrt_pos.2 hY_pos
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have hR_ge_one : 1 ≤ R := by
    have hsquares :
        (1 : ℝ) ^ 2 ≤ R ^ 2 := by
      simpa [R, Real.sq_sqrt hY_pos.le] using hY_ge_one
    have habs : |(1 : ℝ)| ≤ |R| := sq_le_sq.mp hsquares
    simpa [abs_of_nonneg hR_nonneg] using habs
  have hBR_nonneg : 0 ≤ B * R := by positivity
  have hs_le : (s : ℝ) ≤ B' * R := by
    have hsceil : (s : ℝ) ≤ B * R + 1 := by
      dsimp [s]
      exact (Nat.ceil_lt_add_one hBR_nonneg).le
    have hone_le_R : (1 : ℝ) ≤ R := hR_ge_one
    dsimp [B']
    nlinarith
  have hfour_s_le : (4 : ℝ) * (s : ℝ) ≤ C * R := by
    dsimp [C]
    nlinarith [hs_le, hR_nonneg]
  have hC_R_pos : 0 < C * R := mul_pos hC hR_pos
  have hC_R_ge_one : 1 ≤ C * R := by
    have hC_ge_one_or : 0 < C := hC
    nlinarith [hC_ge_one_or, hR_ge_one]
  have hlogC_nonneg : 0 ≤ Real.log (C * R) :=
    Real.log_nonneg hC_R_ge_one
  have hs_log_le :
      (s : ℝ) * Real.log (C * R) ≤ Y / 12 := by
    have hlogC' :
        Real.log (C * R) ≤ (1 / (12 * B')) * R := by
      simpa [C, Y, R] using hlogC
    calc
      (s : ℝ) * Real.log (C * R)
          ≤ (B' * R) * Real.log (C * R) := by
            exact mul_le_mul_of_nonneg_right hs_le hlogC_nonneg
      _ ≤ (B' * R) * ((1 / (12 * B')) * R) := by
            exact mul_le_mul_of_nonneg_left hlogC' (by positivity)
      _ = Y / 12 := by
            have hRsq : R ^ 2 = Y := by
              simpa [R] using Real.sq_sqrt hY_pos.le
            have hcoef : B' * (1 / (12 * B')) = (1 / 12 : ℝ) := by
              have hden : (12 : ℝ) * B' ≠ 0 :=
                mul_ne_zero (by norm_num) hB'.ne'
              apply (mul_right_injective₀ hden)
              calc
                (12 * B') * (B' * (1 / (12 * B'))) = B' := by
                  rw [div_eq_mul_inv]
                  rw [show (12 * B') * (B' * (1 * (12 * B')⁻¹)) =
                    B' * ((12 * B') * (12 * B')⁻¹) by ring]
                  rw [mul_inv_cancel₀ hden, mul_one]
                _ = (12 * B') * (1 / 12 : ℝ) := by
                  rw [div_eq_mul_inv]
                  rw [show (12 * B') * (1 * 12⁻¹) =
                    B' * (12 * 12⁻¹) by ring]
                  rw [mul_inv_cancel₀ (by norm_num : (12 : ℝ) ≠ 0), mul_one]
            calc
              (B' * R) * ((1 / (12 * B')) * R)
                  = (B' * (1 / (12 * B'))) * R ^ 2 := by ring
              _ = (1 / 12 : ℝ) * Y := by rw [hcoef, hRsq]
              _ = Y / 12 := by ring
  have hfac :
      ((s.factorial : ℕ) : ℝ) ≤ (s : ℝ) ^ s := by
    exact_mod_cast Nat.factorial_le_pow s
  have hmoment_le_pow :
      (4 : ℝ) ^ s * (s.factorial : ℝ) ≤ ((4 : ℝ) * (s : ℝ)) ^ s := by
    calc
      (4 : ℝ) ^ s * (s.factorial : ℝ)
          ≤ (4 : ℝ) ^ s * (s : ℝ) ^ s := by
            exact mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = ((4 : ℝ) * (s : ℝ)) ^ s := by rw [mul_pow]
  have hbase_le :
      ((4 : ℝ) * (s : ℝ)) ^ s ≤ (C * R) ^ s := by
    exact pow_le_pow_left₀ (by positivity) hfour_s_le s
  have hpow_exp :
      (C * R) ^ s ≤ Real.exp (Y / 12) := by
    have hpow_eq :
        (C * R) ^ s = Real.exp ((s : ℝ) * Real.log (C * R)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hC_R_pos]
      ring_nf
    rw [hpow_eq]
    exact Real.exp_le_exp.2 hs_log_le
  have hthirtytwo :
      (32 : ℝ) ≤ Real.exp (Y / 12) := by
    have hlog32 : Real.log 32 ≤ Y / 12 := by nlinarith
    calc
      (32 : ℝ) = Real.exp (Real.log 32) := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 32)]
      _ ≤ Real.exp (Y / 12) := Real.exp_le_exp.2 hlog32
  have hmain :
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) ≤ Real.exp (Y / 6) := by
    calc
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
          ≤ Real.exp (Y / 12) * Real.exp (Y / 12) := by
            exact mul_le_mul hthirtytwo (hmoment_le_pow.trans (hbase_le.trans hpow_exp))
              (by positivity) (by positivity)
      _ = Real.exp (Y / 6) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have hZeq := Zscale_eq_exp_half_loglog_mul_sqrt_loglog hNlarge
  calc
    32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
        ≤ Real.exp (Y / 6) := hmain
    _ ≤ Real.exp (Y / 2) * R := by
          have hexp : Real.exp (Y / 6) ≤ Real.exp (Y / 2) :=
            Real.exp_le_exp.2 (by nlinarith)
          exact hexp.trans (by
            calc
              Real.exp (Y / 2) ≤ Real.exp (Y / 2) * R := by
                nlinarith [Real.exp_pos (Y / 2), hR_ge_one])
    _ = Zscale N := by
          rw [hZeq]

lemma squarefullMoment_eulerProduct_hasSum (N s : ℕ) :
    HasSum
      (fun m : Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime) =>
        squarefullMomentTerm s m)
      (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
        ∑' e : ℕ, squarefullMomentTerm s (p ^ e)) := by
  exact (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := squarefullMomentTerm s)
    (squarefullMomentTerm_one s)
    (fun {m n} hcop => squarefullMomentTerm_mul_of_coprime s hcop)
    (fun {p} hp => squarefullMomentTerm_prime_pow_summable s p hp)
    ((Finset.Icc 1 N).filter Nat.Prime)).2

lemma squarefull_mem_factored_primes_Icc {N d : ℕ}
    (hd : d ∈ Finset.Icc 1 N) :
    d ∈ Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime) := by
  rw [Nat.mem_factoredNumbers']
  intro p hp hpd
  have hdIcc := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
  have hple : p ≤ N := (Nat.le_of_dvd hdpos hpd).trans hdIcc.2
  exact Finset.mem_filter.2
    ⟨Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt hp.pos, hple⟩, hp⟩

lemma squarefullMomentTerm_eq_of_squarefull_Icc
    {N d s : ℕ} (hd : d ∈ Finset.Icc 1 N) (hsq : IsSquarefull d) :
    squarefullMomentTerm s d = (hExp d : ℝ) ^ s / (d : ℝ) := by
  have hdIcc := Finset.mem_Icc.mp hd
  have hdne : d ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hdIcc.1)
  simp [squarefullMomentTerm, hExpMomentTerm, hsq, hdne]

noncomputable def squarefullFactoredFinset (N : ℕ) :
    Finset (Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime)) :=
  ((Finset.Icc 1 N).filter IsSquarefull).attach.image
    (fun d =>
      (⟨d.1, squarefull_mem_factored_primes_Icc
        (Finset.mem_filter.1 d.2).1⟩ :
        Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime)))

lemma squarefull_recip_sum_eq_factoredFinset_sum (N s : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0)
      =
    ∑ x ∈ squarefullFactoredFinset N, squarefullMomentTerm s x := by
  classical
  unfold squarefullFactoredFinset
  rw [Finset.sum_image]
  · rw [Finset.sum_attach]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    exact (squarefullMomentTerm_eq_of_squarefull_Icc
      (N := N) (d := d) (s := s)
      (Finset.mem_filter.1 hd).1
      (Finset.mem_filter.1 hd).2).symm
  · intro a _ha b _hb hab
    apply Subtype.ext
    exact congrArg
      (fun x : Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime) =>
        (x : ℕ)) hab

lemma squarefull_recip_sum_le_factored_tsum (N s : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0)
      ≤
    ∑' m : Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime),
      squarefullMomentTerm s m := by
  rw [squarefull_recip_sum_eq_factoredFinset_sum]
  exact (squarefullMoment_eulerProduct_hasSum N s).summable.sum_le_tsum
    (squarefullFactoredFinset N)
    (fun x _hx => squarefullMomentTerm_nonneg s x)

lemma squarefull_recip_sum_le_eulerProduct (N s : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0)
      ≤
    ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
      ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
  rw [← (squarefullMoment_eulerProduct_hasSum N s).tsum_eq]
  exact squarefull_recip_sum_le_factored_tsum N s

lemma hExp_moment_sum_le_squarefull_eulerProduct (N s : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
      (N : ℝ) *
        ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
          ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
  calc
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
        ≤ (N : ℝ) *
            ∑ d ∈ Finset.Icc 1 N,
              if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0 :=
          hExp_moment_sum_le_squarefull_recip_sum N s
    _ ≤ (N : ℝ) *
        ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
          ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
          exact mul_le_mul_of_nonneg_left
            (squarefull_recip_sum_le_eulerProduct N s)
            (by positivity)

lemma hExp_rare_count_rankin_real_bound (N s : ℕ) :
    (((Finset.Icc 1 N).filter
        (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ)
      ≤ (N : ℝ) *
          Real.exp
            (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
              - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))) := by
  have hH_nonneg : 0 ≤ hExpCutoff N := by
    unfold hExpCutoff
    positivity
  have hRankin :=
    hExp_large_rankin_sum_le (N := N) (s := s) (H := hExpCutoff N) hH_nonneg
  have hMoment :
      (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
        (N : ℝ) *
          Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
    calc
      (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
          ≤ (N : ℝ) *
              ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
                ∑' e : ℕ, squarefullMomentTerm s (p ^ e) :=
            hExp_moment_sum_le_squarefull_eulerProduct N s
      _ ≤ (N : ℝ) *
            Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
            exact mul_le_mul_of_nonneg_left
              (finite_squarefull_eulerProduct_le N s)
              (by positivity)
  have hCombined :
      (((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ) *
          hExpCutoff N ^ s
        ≤ (N : ℝ) *
          Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) :=
    hRankin.trans hMoment
  have hHpow :
      hExpCutoff N ^ s =
        Real.exp ((s : ℝ) * Real.sqrt (Real.log (N : ℝ))) := by
    unfold hExpCutoff
    rw [← Real.exp_nat_mul]
  have hHpow_pos :
      0 < hExpCutoff N ^ s := by
    rw [hHpow]
    positivity
  have hdiv :
      (((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ)
        ≤ ((N : ℝ) *
          Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)))) /
            hExpCutoff N ^ s := by
    exact (le_div_iff₀ hHpow_pos).2 hCombined
  refine hdiv.trans_eq ?_
  rw [hHpow]
  rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
  congr 1

/--
BFV Lemma 3.2, in the explicit super-`L` form needed for pruning.

The proof is a Rankin moment estimate.  At moment order
`s = ceil((A+2) * sqrt(log log N))`, the cutoff contributes
`exp(-s * sqrt(log N))`, while the squarefull Euler product contributes only
`exp(o(Zscale N))`; the explicit helper above packages that as
`32 * 4^s * s! <= Zscale N`.
-/
theorem hExp_rare_count_rankin_squarefull :
    ∀ A : ℝ, 0 < A → ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N) := by
  intro A hA
  let B : ℝ := A + 2
  have hB : 0 < B := by dsimp [B]; linarith
  filter_upwards [eventually_squarefull_moment_factor_le_Zscale B hB,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N hfactor hNlarge_nat
  let s : ℕ := Nat.ceil (B * Real.sqrt (Real.log (Real.log (N : ℝ))))
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
    have hlog_gt_one : 1 < Real.log (N : ℝ) :=
      (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
    exact (zero_lt_one.trans hlog_gt_one).le
  have hZ_nonneg : 0 ≤ Zscale N := by
    rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge]
    positivity
  have hfactor' :
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) ≤ Zscale N := by
    simpa [s, B] using hfactor
  have hs_ge :
      B * Real.sqrt (Real.log (Real.log (N : ℝ))) ≤ (s : ℝ) := by
    dsimp [s]
    exact Nat.le_ceil _
  have hs_cutoff :
      B * Zscale N ≤ (s : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by
    rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge]
    calc
      B * (Real.sqrt (Real.log (N : ℝ)) *
          Real.sqrt (Real.log (Real.log (N : ℝ))))
          = (B * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
              Real.sqrt (Real.log (N : ℝ)) := by ring
      _ ≤ (s : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg _)
  have hexponent :
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
          - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))
        ≤ -A * Zscale N := by
    have hstep :
        32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
            - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))
          ≤ Zscale N - B * Zscale N := by
      nlinarith [hfactor', hs_cutoff]
    have htarget : Zscale N - B * Zscale N ≤ -A * Zscale N := by
      dsimp [B]
      nlinarith [hZ_nonneg]
    exact hstep.trans htarget
  have hreal :
      (((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ)
        ≤ (N : ℝ) * Lscale (-A) N := by
    calc
      (((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ)
          ≤ (N : ℝ) *
              Real.exp
                (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
                  - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))) :=
            hExp_rare_count_rankin_real_bound N s
      _ ≤ (N : ℝ) * Lscale (-A) N := by
            rw [Lscale]
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.2 hexponent) hN_nonneg
  exact Nat.le_floor hreal

/-- BFV Lemma 3.2 in the super-`L` consumer form used by pruning. -/
theorem hExp_rare_count_superL :
    ∀ A : ℝ, 0 < A → ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N) :=
  hExp_rare_count_rankin_squarefull

/-- A subset version of the hExp rarity estimate. -/
theorem hExp_rare_subset_count
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop,
      ∀ S : Finset ℕ,
        S ⊆ Finset.Icc 1 N →
        (S.filter fun n => hExpCutoff N < (hExp n : ℝ)).card
          ≤ Nat.floor ((N : ℝ) * Lscale (-A) N) := by
  filter_upwards [hExp_rare_count_superL A hA] with N hN S hS
  exact (Finset.card_le_card (by
    intro n hn
    exact Finset.mem_filter.2
      ⟨hS (Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2⟩)).trans hN

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/BFV/Pruning.lean
    ============================================================= -/

/-
Erdos Problem 202 -- BFV pruning theorem.

This file proves `bfv_pruning_theorem`, the pruning interface consumed by the
upper-bound argument.
-/


namespace Erdos202

open Filter Finset

lemma eventually_Zscale_ge_const (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ Zscale N := by
  let B : ℝ := max A 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
  have hBnonneg : 0 ≤ B := hBpos.le
  filter_upwards [eventually_Mscale_ge 1 zero_lt_one,
      eventually_sqrt_loglog_ge (Real.sqrt B),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hM hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsq :
      (Real.sqrt B) ^ 2 ≤
        (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg B) hsqrt 2
  have hloglog_ge_B : B ≤ Real.log (Real.log (N : ℝ)) := by
    simpa [Real.sq_sqrt hBnonneg, Real.sq_sqrt hloglog_nonneg] using hsq
  have hZ := Mscale_mul_loglog_eq_Zscale hNlarge
  have hB_le_Z : B ≤ Zscale N := by
    rw [← hZ]
    nlinarith [hM, hloglog_ge_B, hBpos.le]
  exact (le_max_left A 1).trans hB_le_Z

lemma eventually_Lscale_neg_le_const {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, Lscale (-A) N ≤ c := by
  filter_upwards [eventually_Zscale_ge_const ((-Real.log c) / A)] with N hZ
  rw [Lscale]
  exact (Real.le_log_iff_exp_le hc).1 (by
    have hmul : -Real.log c ≤ A * Zscale N := by
      simpa [mul_comm] using (div_le_iff₀ hA).1 hZ
    nlinarith)

lemma eventually_const_le_Lscale {A C : ℝ} (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop, C ≤ Lscale A N := by
  by_cases hC : C ≤ 0
  · filter_upwards with N
    exact hC.trans (Lscale_nonneg A N)
  · have hCpos : 0 < C := lt_of_not_ge hC
    filter_upwards [eventually_Zscale_ge_const (Real.log C / A)] with N hZ
    rw [Lscale]
    exact (Real.log_le_iff_le_exp hCpos).1 (by
      have hmul : Real.log C ≤ A * Zscale N := by
        simpa [mul_comm] using (div_le_iff₀ hA).1 hZ
      exact hmul)

lemma eventually_const_mul_Zscale_le_Lscale {C η : ℝ}
    (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, C * Zscale N ≤ Lscale η N := by
  have hηsq_pos : 0 < η ^ 2 := sq_pos_of_pos hη
  filter_upwards [eventually_Zscale_ge_const (4 * C / η ^ 2)] with N hZlarge
  let x : ℝ := η * Zscale N / 2
  have hZ_nonneg : 0 ≤ Zscale N := Zscale_nonneg N
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hfactor : 2 * C / η ≤ x := by
    dsimp [x]
    rw [div_le_iff₀ hη]
    have hmul' : 4 * C ≤ η ^ 2 * Zscale N := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_le_iff₀ hηsq_pos).1 hZlarge
    have hmul'' : 4 * C ≤ η * (η * Zscale N) := by
      simpa [pow_two, mul_assoc] using hmul'
    nlinarith
  have hCZ_eq : C * Zscale N = (2 * C / η) * x := by
    dsimp [x]
    field_simp [hη.ne']
  have hCZ_le_xsq : C * Zscale N ≤ x ^ 2 := by
    rw [hCZ_eq, pow_two]
    exact mul_le_mul_of_nonneg_right hfactor hx_nonneg
  have hx_le_exp : x ≤ Real.exp x := by
    calc
      x ≤ 1 + x := by linarith
      _ ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hxsq_le : x ^ 2 ≤ Real.exp (2 * x) := by
    calc
      x ^ 2 = x * x := by ring
      _ ≤ Real.exp x * Real.exp x := by
            exact mul_le_mul hx_le_exp hx_le_exp hx_nonneg (Real.exp_pos x).le
      _ = Real.exp (2 * x) := by
            rw [← Real.exp_add]
            ring_nf
  calc
    C * Zscale N ≤ x ^ 2 := hCZ_le_xsq
    _ ≤ Real.exp (2 * x) := hxsq_le
    _ = Lscale η N := by
          dsimp [x, Lscale]
          congr 1
          ring

lemma eventually_Mscale_le_Zscale :
    ∀ᶠ N : ℕ in atTop, Mscale N ≤ Zscale N := by
  filter_upwards [eventually_sqrt_loglog_ge 1,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hloglog_ge_one : 1 ≤ Real.log (Real.log (N : ℝ)) := by
    have hsq :
        (1 : ℝ) ^ 2 ≤
          (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hsqrt 2
    simpa [Real.sq_sqrt hloglog_nonneg] using hsq
  rw [← Mscale_mul_loglog_eq_Zscale hNlarge]
  exact le_mul_of_one_le_right (Mscale_nonneg N) hloglog_ge_one

lemma eventually_floor_threeM_succ_le_Lscale
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      ((Nat.floor (3 * Mscale N) + 1 : ℕ) : ℝ) ≤ Lscale η N := by
  filter_upwards [eventually_Mscale_le_Zscale,
      eventually_Zscale_ge_const 1,
      eventually_const_mul_Zscale_le_Lscale (C := 4) (by norm_num) hη] with
    N hMleZ hZge h4Z
  have hfloor :
      ((Nat.floor (3 * Mscale N) : ℕ) : ℝ) ≤ 3 * Mscale N := by
    exact Nat.floor_le (mul_nonneg (by norm_num) (Mscale_nonneg N))
  calc
    ((Nat.floor (3 * Mscale N) + 1 : ℕ) : ℝ)
        = ((Nat.floor (3 * Mscale N) : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ 3 * Mscale N + 1 := by linarith
    _ ≤ 3 * Zscale N + Zscale N := by nlinarith
    _ = 4 * Zscale N := by ring
    _ ≤ Lscale η N := h4Z

lemma q_card_lower_from_bfv_lower
    {ε η : ℝ} {N : ℕ} {Q : Finset ℕ}
    (hQ : (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ (f N : ℝ)) :
    (N : ℝ) * Lscale (-(1 + η + ε)) N ≤ (Q.card : ℝ) := by
  calc
    (N : ℝ) * Lscale (-(1 + η + ε)) N
        = ((N : ℝ) * Lscale (-(1 + η)) N) * Lscale (-ε) N := by
            rw [show -(1 + η + ε) = -(1 + η) + -ε by ring, Lscale_add]
            ring
    _ ≤ (f N : ℝ) * Lscale (-ε) N := by
          exact mul_le_mul_of_nonneg_right hf (Lscale_nonneg (-ε) N)
    _ ≤ (Q.card : ℝ) := hQ

lemma eventually_nat_mul_Lscale_neg_gt_one (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, 1 < (N : ℝ) * Lscale (-A) N := by
  let B : ℝ := max (A + 1) 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right (A + 1) 1)
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_Mscale_ge B hBpos] with N hN hM
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)
  have hNposNat : 0 < N := by
    exact Nat.pos_of_ne_zero (by
      intro h0
      have : ((N : ℕ) : ℝ) = 0 := by simp [h0]
      linarith [show (0 : ℝ) < Real.exp 1 from Real.exp_pos 1])
  have hZpos : 0 < Zscale N := Zscale_pos_of_exp_one_lt_nat hNlarge
  have hMgeA1 : A + 1 ≤ Mscale N := (le_max_left (A + 1) 1).trans hM
  have hlog_eq : Real.log ((N : ℝ) * Lscale (-A) N) =
      Real.log (N : ℝ) + (-A) * Zscale N :=
    log_nat_mul_Lscale hNposNat (-A)
  have hMZ := Mscale_mul_Zscale_eq_log hNlarge
  have hlog_pos :
      0 < Real.log ((N : ℝ) * Lscale (-A) N) := by
    rw [hlog_eq, ← hMZ]
    have hdiff : 1 ≤ Mscale N - A := by linarith
    nlinarith
  have htarget_nonneg : 0 ≤ (N : ℝ) * Lscale (-A) N :=
    mul_nonneg (by positivity) (Lscale_nonneg (-A) N)
  exact (Real.log_pos_iff htarget_nonneg).1 hlog_pos

lemma omega_pos_of_one_lt {n : ℕ} (hn : 1 < n) : 1 ≤ omega n := by
  by_contra h
  have homega : omega n = 0 := by omega
  have hnne : n ≠ 0 := by omega
  have hnone : n = 1 := eq_one_of_omega_eq_zero hnne homega
  omega

lemma eventually_omega_pos_of_modulus_lower :
    ∀ᶠ N : ℕ in atTop,
      ∀ q : ℕ, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ) → 1 ≤ omega q := by
  filter_upwards [eventually_nat_mul_Lscale_neg_gt_one 2] with N hlarge q hq
  have hq_gt_one_real : (1 : ℝ) < (q : ℝ) := hlarge.trans_le hq
  have hq_gt_one : 1 < q := by exact_mod_cast hq_gt_one_real
  exact omega_pos_of_one_lt hq_gt_one

lemma nat_mul_Lscale_neg_le_fraction_of_nat_mul_Lscale_neg
    {A B δ : ℝ} (hAB : B + δ ≤ A) (N : ℕ) :
    (N : ℝ) * Lscale (-A) N ≤
      Lscale (-δ) N * ((N : ℝ) * Lscale (-B) N) := by
  have hmono : Lscale (-A) N ≤ Lscale (-(B + δ)) N := by
    exact Lscale_mono_in_alpha (by linarith) N
  calc
    (N : ℝ) * Lscale (-A) N
        ≤ (N : ℝ) * Lscale (-(B + δ)) N := by
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = Lscale (-δ) N * ((N : ℝ) * Lscale (-B) N) := by
          rw [show -(B + δ) = -B + -δ by ring, Lscale_add]
          ring

lemma nat_mul_Lscale_neg_le_fraction_of_card
    {A B δ : ℝ} (hAB : B + δ ≤ A) {N : ℕ} {Q : Finset ℕ}
    (hQ : (N : ℝ) * Lscale (-B) N ≤ (Q.card : ℝ)) :
    (N : ℝ) * Lscale (-A) N ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  calc
    (N : ℝ) * Lscale (-A) N
        ≤ Lscale (-δ) N * ((N : ℝ) * Lscale (-B) N) :=
          nat_mul_Lscale_neg_le_fraction_of_nat_mul_Lscale_neg hAB N
    _ ≤ Lscale (-δ) N * (Q.card : ℝ) := by
          exact mul_le_mul_of_nonneg_left hQ (Lscale_nonneg (-δ) N)

lemma floor_nat_mul_Lscale_neg_le_fraction_of_card
    {A B δ : ℝ} (hAB : B + δ ≤ A) {N : ℕ} {Q : Finset ℕ}
    (hQ : (N : ℝ) * Lscale (-B) N ≤ (Q.card : ℝ)) :
    (Nat.floor ((N : ℝ) * Lscale (-A) N) : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have htarget_nonneg :
      0 ≤ (N : ℝ) * Lscale (-A) N :=
    mul_nonneg (by positivity) (Lscale_nonneg (-A) N)
  exact (Nat.floor_le htarget_nonneg).trans
    (nat_mul_Lscale_neg_le_fraction_of_card hAB hQ)

lemma floor_nat_mul_Lscale_neg_le_near_extremal_fraction
    {A ε η δ : ℝ} (hAB : 1 + η + ε + δ ≤ A)
    {N : ℕ} {Q : Finset ℕ}
    (hQ : (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ (f N : ℝ)) :
    (Nat.floor ((N : ℝ) * Lscale (-A) N) : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have hQlower :
      (N : ℝ) * Lscale (-(1 + η + ε)) N ≤ (Q.card : ℝ) :=
    q_card_lower_from_bfv_lower hQ hf
  exact floor_nat_mul_Lscale_neg_le_fraction_of_card
    (A := A) (B := 1 + η + ε) (δ := δ) (by linarith) hQlower

lemma card_filter_natCast_lt_le_floor {S : Finset ℕ} {X : ℝ}
    (hX : 0 ≤ X) (hpos : ∀ n ∈ S, 1 ≤ n) :
    (S.filter (fun n : ℕ => (n : ℝ) < X)).card ≤ Nat.floor X := by
  classical
  have hsub :
      (S.filter (fun n : ℕ => (n : ℝ) < X)) ⊆ Finset.Icc 1 (Nat.floor X) := by
    intro n hn
    have hnS : n ∈ S := (Finset.mem_filter.1 hn).1
    have hnlt : (n : ℝ) < X := (Finset.mem_filter.1 hn).2
    exact Finset.mem_Icc.2 ⟨hpos n hnS, (Nat.le_floor_iff hX).2 hnlt.le⟩
  have hcard := Finset.card_le_card hsub
  have hIcc_le : (Finset.Icc 1 (Nat.floor X)).card ≤ Nat.floor X := by
    rw [Nat.card_Icc]
    omega
  exact hcard.trans hIcc_le

lemma small_moduli_in_admissible_count
    {N : ℕ} {Q : Finset ℕ}
    (hRange : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) :
    (Q.filter (fun q : ℕ => (q : ℝ) < (N : ℝ) * Lscale (-2) N)).card
      ≤ Nat.floor ((N : ℝ) * Lscale (-2) N) := by
  exact card_filter_natCast_lt_le_floor
    (mul_nonneg (by positivity) (Lscale_nonneg (-2) N))
    (fun q hq => (hRange q hq).1)

lemma small_moduli_count_le_near_extremal_fraction
    {ε η δ : ℝ} (hmargin : 1 + η + ε + δ ≤ 2)
    {N : ℕ} {Q : Finset ℕ}
    (hRange : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N)
    (hQ : (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ (f N : ℝ)) :
    ((Q.filter
        (fun q : ℕ => (q : ℝ) < (N : ℝ) * Lscale (-2) N)).card : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have hcount := small_moduli_in_admissible_count (N := N) (Q := Q) hRange
  have hcount_real :
      (((Q.filter
        (fun q : ℕ => (q : ℝ) < (N : ℝ) * Lscale (-2) N)).card : ℕ) : ℝ) ≤
        (Nat.floor ((N : ℝ) * Lscale (-2) N) : ℝ) := by
    exact_mod_cast hcount
  exact hcount_real.trans
    (floor_nat_mul_Lscale_neg_le_near_extremal_fraction
      (A := 2) (ε := ε) (η := η) (δ := δ) hmargin hQ hf)

lemma hExp_bad_count_le_near_extremal_fraction
    {A ε η δ : ℝ} (hmargin : 1 + η + ε + δ ≤ A)
    {N : ℕ} {Q : Finset ℕ}
    (hQ : (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ (f N : ℝ))
    (hRare :
      (Q.filter fun q : ℕ => hExpCutoff N < (hExp q : ℝ)).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N)) :
    (((Q.filter
        fun q : ℕ => hExpCutoff N < (hExp q : ℝ)).card : ℕ) : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have hcount_real :
      (((Q.filter
        fun q : ℕ => hExpCutoff N < (hExp q : ℝ)).card : ℕ) : ℝ) ≤
        (Nat.floor ((N : ℝ) * Lscale (-A) N) : ℝ) := by
    exact_mod_cast hRare
  exact hcount_real.trans
    (floor_nat_mul_Lscale_neg_le_near_extremal_fraction
      (A := A) (ε := ε) (η := η) (δ := δ) hmargin hQ hf)

lemma omega_tail_subset_count
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ,
        Q ⊆ Finset.Icc 1 N →
        ∀ t : ℕ, (t : ℝ) ≤ 3 * Mscale N →
          let α : ℝ := (t : ℝ) / Mscale N
          (Q.filter fun q => t ≤ omega q).card
            ≤ Nat.floor
                ((N : ℝ) * Real.exp ((-α / 2 + ε) * Zscale N)) := by
  filter_upwards [bfv_omega_tail_theorem ε hε] with N htail Q hQ t ht
  have hsub :
      (Q.filter fun q => t ≤ omega q) ⊆
        (Finset.Icc 1 N).filter fun q => t ≤ omega q := by
    intro q hq
    exact Finset.mem_filter.2
      ⟨hQ (Finset.mem_filter.1 hq).1, (Finset.mem_filter.1 hq).2⟩
  exact (Finset.card_le_card hsub).trans (htail N t le_rfl ht)

lemma omega_bad_count_le_near_extremal_fraction
    {A ε η δ : ℝ} (hmargin : 1 + η + ε + δ ≤ A)
    {N t : ℕ} {Q : Finset ℕ}
    (hQ : (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ (f N : ℝ))
    (hTail :
      (Q.filter fun q : ℕ => t ≤ omega q).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N)) :
    (((Q.filter fun q : ℕ => t ≤ omega q).card : ℕ) : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have hcount_real :
      (((Q.filter fun q : ℕ => t ≤ omega q).card : ℕ) : ℝ) ≤
        (Nat.floor ((N : ℝ) * Lscale (-A) N) : ℝ) := by
    exact_mod_cast hTail
  exact hcount_real.trans
    (floor_nat_mul_Lscale_neg_le_near_extremal_fraction
      (A := A) (ε := ε) (η := η) (δ := δ) hmargin hQ hf)

lemma omega_floor_threeM_tail_subset_count :
    ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ,
        Q ⊆ Finset.Icc 1 N →
          (Q.filter
              (fun q : ℕ => Nat.floor (3 * Mscale N) ≤ omega q)).card
            ≤ Nat.floor ((N : ℝ) * Lscale (-(4 / 3)) N) := by
  have hτ : (0 : ℝ) < 1 / 24 := by norm_num
  filter_upwards [omega_tail_subset_count (1 / 24) hτ,
      eventually_Mscale_ge 4 (by norm_num),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N htail hMge hNlarge_nat Q hQ
  let t : ℕ := Nat.floor (3 * Mscale N)
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hNlarge
  have hZnonneg : 0 ≤ Zscale N := Zscale_nonneg N
  have ht_le : (t : ℝ) ≤ 3 * Mscale N := by
    dsimp [t]
    exact Nat.floor_le (mul_nonneg (by norm_num) (Mscale_nonneg N))
  have ht_count := htail Q hQ t ht_le
  have ht_lower : 3 * Mscale N - 1 < (t : ℝ) := by
    have hlt : 3 * Mscale N < (t : ℝ) + 1 := by
      dsimp [t]
      exact Nat.lt_floor_add_one (3 * Mscale N)
    linarith
  have halpha_lower : (11 / 4 : ℝ) ≤ (t : ℝ) / Mscale N := by
    have hdiv : (3 * Mscale N - 1) / Mscale N < (t : ℝ) / Mscale N :=
      div_lt_div_of_pos_right ht_lower hMpos
    have hM_inv : 1 / Mscale N ≤ (1 / 4 : ℝ) := by
      exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hMge)
    have hthree_sub : (11 / 4 : ℝ) ≤ 3 - 1 / Mscale N := by
      linarith
    have hdiv_eq : (3 * Mscale N - 1) / Mscale N = 3 - 1 / Mscale N := by
      field_simp [hMpos.ne']
    linarith
  have hexp_scale :
      (N : ℝ) *
          Real.exp ((-((t : ℝ) / Mscale N) / 2 + (1 / 24 : ℝ)) *
            Zscale N)
        ≤ (N : ℝ) * Lscale (-(4 / 3)) N := by
    have hcoeff :
        -((t : ℝ) / Mscale N) / 2 + (1 / 24 : ℝ) ≤ -(4 / 3 : ℝ) := by
      nlinarith
    have hexp :
        Real.exp ((-((t : ℝ) / Mscale N) / 2 + (1 / 24 : ℝ)) *
            Zscale N)
          ≤ Lscale (-(4 / 3)) N := by
      rw [Lscale]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hcoeff hZnonneg)
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  exact ht_count.trans (Nat.floor_mono hexp_scale)

lemma eventually_radical_multiplicity_ceiling_le_Lscale
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ 3 * Mscale N →
        (Nat.ceil (hExpCutoff N ^ 2 * (2 : ℝ) ^ K) : ℝ) ≤
          Lscale ε N := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_nonneg : 0 ≤ Real.log 2 := hlog2_pos.le
  let Clog : ℝ := 9 * Real.log 2 / ε
  have hClog_pos : 0 < Clog := by
    dsimp [Clog]
    positivity
  filter_upwards [eventually_Zscale_ge_const (3 * Real.log 2 / ε),
      eventually_sqrt_loglog_ge (6 / ε),
      eventually_sqrt_loglog_ge (Real.sqrt Clog),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N hZconst hsqrtloglog hsqrtClog hNlarge_nat K hK
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsqrtlog_nonneg : 0 ≤ Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_nonneg _
  have hsqrtloglog_nonneg :
      0 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    Real.sqrt_nonneg _
  have hloglog_ge_Clog : Clog ≤ Real.log (Real.log (N : ℝ)) := by
    have hsq :
        (Real.sqrt Clog) ^ 2 ≤
          (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg Clog) hsqrtClog 2
    simpa [Real.sq_sqrt hClog_pos.le, Real.sq_sqrt hloglog_nonneg] using hsq
  have hZsqrt := Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge
  have hZloglog := Mscale_mul_loglog_eq_Zscale hNlarge
  let a : ℝ := (ε / 3) * Zscale N
  have htwo : (2 : ℝ) ≤ Real.exp a := by
    have hlog_le : Real.log 2 ≤ a := by
      dsimp [a]
      have hzmul : 3 * Real.log 2 ≤ ε * Zscale N := by
        simpa [mul_comm] using (div_le_iff₀ hε).1 hZconst
      nlinarith
    exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).1 hlog_le
  have hHsq : hExpCutoff N ^ 2 ≤ Real.exp a := by
    have hcoeff : 2 ≤ (ε / 3) *
        Real.sqrt (Real.log (Real.log (N : ℝ))) := by
      have hmul : 6 ≤ ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
        simpa [mul_comm] using (div_le_iff₀ hε).1 hsqrtloglog
      nlinarith
    have hexp_arg :
        2 * Real.sqrt (Real.log (N : ℝ)) ≤ a := by
      dsimp [a]
      rw [hZsqrt]
      calc
        2 * Real.sqrt (Real.log (N : ℝ))
            ≤ ((ε / 3) * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
                Real.sqrt (Real.log (N : ℝ)) := by
              exact mul_le_mul_of_nonneg_right hcoeff hsqrtlog_nonneg
        _ = (ε / 3) *
              (Real.sqrt (Real.log (N : ℝ)) *
                Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
              ring
    have hHsq_eq :
        hExpCutoff N ^ 2 = Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
      simp [hExpCutoff, pow_two, ← Real.exp_add, two_mul]
    rw [hHsq_eq]
    exact Real.exp_le_exp.2 hexp_arg
  have hpow : (2 : ℝ) ^ K ≤ Real.exp a := by
    have hlog_le : Real.log ((2 : ℝ) ^ K) ≤ a := by
      rw [Real.log_pow]
      dsimp [a]
      rw [← hZloglog]
      calc
        (K : ℝ) * Real.log 2
            ≤ (3 * Mscale N) * Real.log 2 := by
              exact mul_le_mul_of_nonneg_right hK hlog2_nonneg
        _ = Mscale N * (3 * Real.log 2) := by ring
        _ ≤ Mscale N * ((ε / 3) *
              Real.log (Real.log (N : ℝ))) := by
              have hmain : 3 * Real.log 2 ≤ (ε / 3) *
                  Real.log (Real.log (N : ℝ)) := by
                dsimp [Clog] at hloglog_ge_Clog
                have hmul : 9 * Real.log 2 ≤
                    ε * Real.log (Real.log (N : ℝ)) := by
                  simpa [mul_comm] using (div_le_iff₀ hε).1 hloglog_ge_Clog
                nlinarith
              exact mul_le_mul_of_nonneg_left hmain (Mscale_nonneg N)
        _ = (ε / 3) *
              (Mscale N * Real.log (Real.log (N : ℝ))) := by ring
        _ = ε / 3 * (Mscale N * Real.log (Real.log (N : ℝ))) := by ring
    exact (Real.log_le_iff_le_exp (by positivity : 0 < (2 : ℝ) ^ K)).1 hlog_le
  let X : ℝ := hExpCutoff N ^ 2 * (2 : ℝ) ^ K
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    positivity
  have hH_ge_one : 1 ≤ hExpCutoff N := by
    rw [show (1 : ℝ) = Real.exp 0 by simp, hExpCutoff]
    exact Real.exp_le_exp.2 (Real.sqrt_nonneg _)
  have hHsq_ge_one : 1 ≤ hExpCutoff N ^ 2 := by
    nlinarith [hH_ge_one]
  have hpow_ge_one : 1 ≤ (2 : ℝ) ^ K := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hX_ge_one : 1 ≤ X := by
    dsimp [X]
    nlinarith [mul_le_mul hHsq_ge_one hpow_ge_one
      (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ hExpCutoff N ^ 2)]
  have hceil_le : (Nat.ceil X : ℝ) ≤ 2 * X := by
    have hceil_lt : (Nat.ceil X : ℝ) < X + 1 := Nat.ceil_lt_add_one hX_nonneg
    linarith
  have htwoX : 2 * X ≤ Lscale ε N := by
    dsimp [X]
    calc
      2 * (hExpCutoff N ^ 2 * (2 : ℝ) ^ K)
          ≤ Real.exp a * (Real.exp a * Real.exp a) := by
            nlinarith [htwo, hHsq, hpow,
              Real.exp_pos a, hX_nonneg]
      _ = Real.exp (3 * a) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
      _ = Lscale ε N := by
            dsimp [a, Lscale]
            congr 1
            ring
  exact hceil_le.trans htwoX

lemma card_lower_of_mul_factor_le_Lscale
    {S S' : Finset ℕ} {C N : ℕ} {η : ℝ}
    (hcard : S.card ≤ C * S'.card)
    (hC : (C : ℝ) ≤ Lscale η N) :
    (S.card : ℝ) * Lscale (-η) N ≤ (S'.card : ℝ) := by
  have hcard_real : (S.card : ℝ) ≤ (C : ℝ) * (S'.card : ℝ) := by
    exact_mod_cast hcard
  have hfactor :
      (C : ℝ) * (S'.card : ℝ) ≤
        Lscale η N * (S'.card : ℝ) := by
    exact mul_le_mul_of_nonneg_right hC (by positivity)
  have hmain : (S.card : ℝ) ≤ Lscale η N * (S'.card : ℝ) :=
    hcard_real.trans hfactor
  calc
    (S.card : ℝ) * Lscale (-η) N
        ≤ (Lscale η N * (S'.card : ℝ)) * Lscale (-η) N := by
          exact mul_le_mul_of_nonneg_right hmain (Lscale_nonneg (-η) N)
    _ = (S'.card : ℝ) * (Lscale η N * Lscale (-η) N) := by ring
    _ = (S'.card : ℝ) := by
          rw [show Lscale η N * Lscale (-η) N = 1 by
            rw [mul_comm, Lscale_neg_mul]]
          ring

lemma prunedData_of_subset {N : ℕ} {Q S : Finset ℕ} (a : ResidueAssignment Q)
    (hsub : S ⊆ Q)
    (hRange : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N)
    (hDisj : PairwiseDisjointResidues Q a)
    (hSnonempty : S.Nonempty)
    (K : ℕ)
    (hKpos : 1 ≤ K)
    (hModLower : ∀ q ∈ S, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ))
    (hHExp : ∀ q ∈ S, (hExp q : ℝ) ≤ hExpCutoff N)
    (hOmega : ∀ q ∈ S, omega q = K)
    (hKbound : (K : ℝ) ≤ 3 * Mscale N)
    (hRadInj : ∀ q ∈ S, ∀ r ∈ S, rad q = rad r → q = r) :
    ∃ D : PrunedData N, D.Q = S ∧ D.K = K ∧
      (D.Q.card : ℝ) = (S.card : ℝ) := by
  let aS : ResidueAssignment S := restrictAssignment a hsub
  have hAdmissible : Admissible N S := by
    constructor
    · intro q hq
      exact hRange q (hsub hq)
    · exact ⟨aS, PairwiseDisjointResidues.mono hDisj hsub⟩
  refine ⟨{
      Q := S
      Q_nonempty := hSnonempty
      a := aS
      admissible := hAdmissible
      pairwise_disjoint := PairwiseDisjointResidues.mono hDisj hsub
      K := K
      K_pos := hKpos
      modulus_lower := hModLower
      modulus_upper := ?_
      hExp_bound := ?_
      omega_eq := hOmega
      K_bound := hKbound
      rad_injective := hRadInj
    }, rfl, rfl, rfl⟩
  · intro q hq
    exact (hRange q (hsub hq)).2
  · intro q hq
    simpa [hExpCutoff] using hHExp q hq

lemma rad_fiber_card_le_ceiling {S : Finset ℕ} {K : ℕ} {H : ℝ}
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hOmega : ∀ q ∈ S, omega q = K)
    (hHExp : ∀ q ∈ S, (hExp q : ℝ) ≤ H) :
    ∀ r ∈ S.image rad,
      (S.filter fun q => rad q = r).card ≤ Nat.ceil (H ^ 2 * (2 : ℝ) ^ K) := by
  intro r hr
  let F : Finset ℕ := S.filter fun q => rad q = r
  have hFpos : ∀ q ∈ F, q ≠ 0 := by
    intro q hq
    exact hSpos q (Finset.mem_filter.1 hq).1
  have hF :
      ∀ q ∈ F, rad q = r ∧ omega q = K ∧ (hExp q : ℝ) ≤ H := by
    intro q hq
    exact ⟨(Finset.mem_filter.1 hq).2,
      hOmega q (Finset.mem_filter.1 hq).1,
      hHExp q (Finset.mem_filter.1 hq).1⟩
  have hreal := rad_multiplicity_bfv33 F r K H hH hFpos hF
  have hceil : H ^ 2 * (2 : ℝ) ^ K ≤
      (Nat.ceil (H ^ 2 * (2 : ℝ) ^ K) : ℝ) :=
    Nat.le_ceil _
  exact_mod_cast hreal.trans hceil

lemma choose_rad_representatives {S : Finset ℕ} {K : ℕ} {H : ℝ}
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hOmega : ∀ q ∈ S, omega q = K)
    (hHExp : ∀ q ∈ S, (hExp q : ℝ) ≤ H) :
    ∃ S' : Finset ℕ,
      S' ⊆ S ∧
      (∀ q ∈ S', ∀ r ∈ S', rad q = rad r → q = r) ∧
      S.card ≤ Nat.ceil (H ^ 2 * (2 : ℝ) ^ K) * S'.card := by
  exact choose_one_per_fiber_card_lower S rad
    (Nat.ceil (H ^ 2 * (2 : ℝ) ^ K))
    (rad_fiber_card_le_ceiling hH hSpos hOmega hHExp)

lemma exists_prunedData_after_radical_selection
    {N K : ℕ} {Q S : Finset ℕ} (a : ResidueAssignment Q)
    (hsub : S ⊆ Q)
    (hRange : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N)
    (hDisj : PairwiseDisjointResidues Q a)
    (hSnonempty : S.Nonempty)
    (hKpos : 1 ≤ K)
    (hKbound : (K : ℝ) ≤ 3 * Mscale N)
    (hH : 1 ≤ hExpCutoff N)
    (hModLower : ∀ q ∈ S, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ))
    (hHExp : ∀ q ∈ S, (hExp q : ℝ) ≤ hExpCutoff N)
    (hOmega : ∀ q ∈ S, omega q = K) :
    ∃ D : PrunedData N,
      S.card ≤ Nat.ceil (hExpCutoff N ^ 2 * (2 : ℝ) ^ K) * D.Q.card := by
  have hSpos : ∀ q ∈ S, q ≠ 0 := by
    intro q hq
    have hqpos : 1 ≤ q := (hRange q (hsub hq)).1
    omega
  rcases choose_rad_representatives
      (S := S) (K := K) (H := hExpCutoff N)
      hH hSpos hOmega hHExp with
    ⟨S', hS'sub, hRadInj, hCard⟩
  have hS'nonempty : S'.Nonempty := by
    by_contra hnone
    have hS'empty : S' = ∅ := Finset.not_nonempty_iff_eq_empty.1 hnone
    have hSpos_card : 0 < S.card := hSnonempty.card_pos
    have hle0 : S.card ≤ 0 := by
      simpa [hS'empty] using hCard
    exact (Nat.lt_irrefl 0) (hSpos_card.trans_le hle0)
  rcases prunedData_of_subset (N := N) (Q := Q) (S := S') a
      (fun q hq => hsub (hS'sub hq))
      hRange hDisj hS'nonempty K hKpos
      (fun q hq => hModLower q (hS'sub hq))
      (fun q hq => hHExp q (hS'sub hq))
      (fun q hq => hOmega q (hS'sub hq))
      hKbound
      (fun q hq r hr hrad => hRadInj q hq r hr hrad) with
    ⟨D, hDQ, _hDK, hDcard⟩
  refine ⟨D, ?_⟩
  simpa [hDQ] using hCard

lemma exists_omega_fiber_large (S : Finset ℕ) (T : ℕ)
    (_hS : S.Nonempty) (hOmegaLe : ∀ q ∈ S, omega q ≤ T) :
    ∃ K : ℕ,
      K ≤ T ∧ S.card ≤ (T + 1) * (S.filter fun q => omega q = K).card := by
  classical
  have hBne : (Finset.range (T + 1)).Nonempty := by
    exact ⟨0, by simp⟩
  have hB : ∀ q ∈ S, omega q ∈ Finset.range (T + 1) := by
    intro q hq
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hOmegaLe q hq)
  rcases exists_fiber_card_mul_range_card_ge S (Finset.range (T + 1)) omega hBne hB with
    ⟨K, hKmem, hK⟩
  refine ⟨K, ?_, ?_⟩
  · exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hKmem)
  · simpa [Finset.card_range] using hK

theorem bfv_pruning_small_epsilon_theorem :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
        ∃ D : PrunedData N,
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N := by
  intro ε hε hεle
  let μ : ℝ := ε / 24
  have hμ : 0 < μ := by
    dsimp [μ]
    positivity
  have hε3 : 0 < ε / 3 := by positivity
  have hmargin_small : 1 + μ + ε + μ ≤ 2 := by
    dsimp [μ]
    nlinarith
  have hmargin_omega : 1 + μ + ε + μ ≤ (4 / 3 : ℝ) := by
    dsimp [μ]
    nlinarith
  filter_upwards [bfv_lower_bound_theorem μ hμ,
      hExp_rare_subset_count 2 (by norm_num),
      omega_floor_threeM_tail_subset_count,
      eventually_floor_threeM_succ_le_Lscale (ε / 3) hε3,
      eventually_radical_multiplicity_ceiling_le_Lscale (ε / 3) hε3,
      eventually_Lscale_neg_le_const (A := μ) (c := 1 / 6) hμ (by norm_num),
      eventually_Lscale_neg_le_const (A := ε / 3) (c := 1 / 2) hε3 (by norm_num),
      eventually_nat_mul_Lscale_neg_gt_one (1 + μ + ε),
      eventually_omega_pos_of_modulus_lower] with
    N hf hHrare hOmegaRare hPigeonLoss hRadLoss hBadTiny hDelTargetTiny hQlowerOne hOmegaPos
    Q a hRange hDisj hQlarge
  classical
  let T : ℕ := Nat.floor (3 * Mscale N)
  let BadSmall : Finset ℕ :=
    Q.filter (fun q : ℕ => (q : ℝ) < (N : ℝ) * Lscale (-2) N)
  let BadOmega : Finset ℕ :=
    Q.filter (fun q : ℕ => T ≤ omega q)
  let BadH : Finset ℕ :=
    Q.filter (fun q : ℕ => hExpCutoff N < (hExp q : ℝ))
  let Good : Finset ℕ := Q \ (BadSmall ∪ BadOmega ∪ BadH)
  have hQsubset : Q ⊆ Finset.Icc 1 N := by
    intro q hq
    exact Finset.mem_Icc.2 (hRange q hq)
  have hfQlower :
      (N : ℝ) * Lscale (-(1 + μ + ε)) N ≤ (Q.card : ℝ) :=
    q_card_lower_from_bfv_lower hQlarge hf
  have hQcard_gt_one : (1 : ℝ) < (Q.card : ℝ) :=
    hQlowerOne.trans_le hfQlower
  have hBadSmall_sub : BadSmall ⊆ Q := by
    intro q hq
    exact (Finset.mem_filter.1 hq).1
  have hBadOmega_sub : BadOmega ⊆ Q := by
    intro q hq
    exact (Finset.mem_filter.1 hq).1
  have hBadH_sub : BadH ⊆ Q := by
    intro q hq
    exact (Finset.mem_filter.1 hq).1
  have hSmall_small : (BadSmall.card : ℝ) ≤ Lscale (-μ) N * (Q.card : ℝ) := by
    simpa [BadSmall] using
      small_moduli_count_le_near_extremal_fraction
        (ε := ε) (η := μ) (δ := μ) hmargin_small hRange hQlarge hf
  have hOmega_tail :
      (BadOmega.card : ℝ) ≤ Lscale (-μ) N * (Q.card : ℝ) := by
    have hTail :
        (Q.filter (fun q : ℕ => T ≤ omega q)).card
          ≤ Nat.floor ((N : ℝ) * Lscale (-(4 / 3)) N) := by
      simpa [T] using hOmegaRare Q hQsubset
    simpa [BadOmega] using
      omega_bad_count_le_near_extremal_fraction
        (A := 4 / 3) (ε := ε) (η := μ) (δ := μ)
        hmargin_omega hQlarge hf hTail
  have hH_tail : (BadH.card : ℝ) ≤ Lscale (-μ) N * (Q.card : ℝ) := by
    have hRareQ :
        (Q.filter fun q : ℕ => hExpCutoff N < (hExp q : ℝ)).card
          ≤ Nat.floor ((N : ℝ) * Lscale (-2) N) :=
      hHrare Q hQsubset
    simpa [BadH] using
      hExp_bad_count_le_near_extremal_fraction
        (A := 2) (ε := ε) (η := μ) (δ := μ)
        hmargin_small hQlarge hf hRareQ
  have hGood_large_raw :
      (Good.card : ℝ) ≥
        (1 - (Lscale (-μ) N + Lscale (-μ) N + Lscale (-μ) N)) *
          (Q.card : ℝ) := by
    simpa [Good] using
      filter_large_of_three_bad_small Q BadSmall BadOmega BadH
        hBadSmall_sub hBadOmega_sub hBadH_sub
        hSmall_small hOmega_tail hH_tail
  have hGood_large :
      (Q.card : ℝ) * Lscale (-(ε / 3)) N ≤ (Good.card : ℝ) := by
    have hcoeff :
        Lscale (-(ε / 3)) N ≤
          1 - (Lscale (-μ) N + Lscale (-μ) N + Lscale (-μ) N) := by
      linarith [hBadTiny, hDelTargetTiny]
    calc
      (Q.card : ℝ) * Lscale (-(ε / 3)) N
          ≤ (Q.card : ℝ) *
              (1 - (Lscale (-μ) N + Lscale (-μ) N + Lscale (-μ) N)) := by
            exact mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ ≤ (Good.card : ℝ) := by
            simpa [mul_comm] using hGood_large_raw
  have hGood_nonempty : Good.Nonempty := by
    have hpos : 0 < (Good.card : ℝ) := by
      have hLpos : 0 < Lscale (-(ε / 3)) N := Lscale_pos _ _
      exact lt_of_lt_of_le (mul_pos (lt_trans zero_lt_one hQcard_gt_one) hLpos)
        hGood_large
    exact Finset.card_pos.1 (by exact_mod_cast hpos)
  have hGood_sub_Q : Good ⊆ Q := by
    intro q hq
    exact Finset.mem_sdiff.1 hq |>.1
  have hGood_modLower :
      ∀ q ∈ Good, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ) := by
    intro q hq
    have hqQ : q ∈ Q := hGood_sub_Q hq
    have hnot : q ∉ BadSmall := by
      have hnotUnion : q ∉ BadSmall ∪ BadOmega ∪ BadH :=
        (Finset.mem_sdiff.1 hq).2
      intro hbad
      exact hnotUnion (by simp [hbad])
    exact le_of_not_gt (by
      intro hlt
      exact hnot (Finset.mem_filter.2 ⟨hqQ, hlt⟩))
  have hGood_hExp :
      ∀ q ∈ Good, (hExp q : ℝ) ≤ hExpCutoff N := by
    intro q hq
    have hqQ : q ∈ Q := hGood_sub_Q hq
    have hnot : q ∉ BadH := by
      have hnotUnion : q ∉ BadSmall ∪ BadOmega ∪ BadH :=
        (Finset.mem_sdiff.1 hq).2
      intro hbad
      exact hnotUnion (by simp [hbad])
    exact le_of_not_gt (by
      intro hlt
      exact hnot (Finset.mem_filter.2 ⟨hqQ, hlt⟩))
  have hGood_omega_le : ∀ q ∈ Good, omega q ≤ T := by
    intro q hq
    have hqQ : q ∈ Q := hGood_sub_Q hq
    have hnot : q ∉ BadOmega := by
      have hnotUnion : q ∉ BadSmall ∪ BadOmega ∪ BadH :=
        (Finset.mem_sdiff.1 hq).2
      intro hbad
      exact hnotUnion (by simp [hbad])
    have hnotle : ¬ T ≤ omega q := by
      intro hle
      exact hnot (Finset.mem_filter.2 ⟨hqQ, hle⟩)
    omega
  rcases exists_omega_fiber_large Good T hGood_nonempty hGood_omega_le with
    ⟨K, hKleT, hGood_le_fiber⟩
  let Fiber : Finset ℕ := Good.filter fun q : ℕ => omega q = K
  have hFiber_large :
      (Good.card : ℝ) * Lscale (-(ε / 3)) N ≤ (Fiber.card : ℝ) := by
    simpa [Fiber, T] using
      card_lower_of_mul_factor_le_Lscale
        (S := Good) (S' := Good.filter fun q : ℕ => omega q = K)
        (C := T + 1) (N := N) (η := ε / 3)
        hGood_le_fiber hPigeonLoss
  have hFiber_nonempty : Fiber.Nonempty := by
    have hpos : 0 < (Fiber.card : ℝ) := by
      exact lt_of_lt_of_le
        (mul_pos
          (lt_of_lt_of_le
            (mul_pos (lt_trans zero_lt_one hQcard_gt_one) (Lscale_pos _ _))
            hGood_large)
          (Lscale_pos _ _))
        hFiber_large
    exact Finset.card_pos.1 (by exact_mod_cast hpos)
  have hFiber_sub_Q : Fiber ⊆ Q := by
    intro q hq
    exact hGood_sub_Q (Finset.mem_filter.1 hq).1
  have hFiber_modLower :
      ∀ q ∈ Fiber, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ) := by
    intro q hq
    exact hGood_modLower q (Finset.mem_filter.1 hq).1
  have hFiber_hExp :
      ∀ q ∈ Fiber, (hExp q : ℝ) ≤ hExpCutoff N := by
    intro q hq
    exact hGood_hExp q (Finset.mem_filter.1 hq).1
  have hFiber_omega : ∀ q ∈ Fiber, omega q = K := by
    intro q hq
    exact (Finset.mem_filter.1 hq).2
  have hKbound : (K : ℝ) ≤ 3 * Mscale N := by
    have hT_le : (T : ℝ) ≤ 3 * Mscale N := by
      dsimp [T]
      exact Nat.floor_le (mul_nonneg (by norm_num) (Mscale_nonneg N))
    have hKleTreal : (K : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast hKleT
    exact hKleTreal.trans hT_le
  have hKpos : 1 ≤ K := by
    rcases hFiber_nonempty with ⟨q, hq⟩
    have hOmegaQ : 1 ≤ omega q :=
      hOmegaPos q (hFiber_modLower q hq)
    rw [hFiber_omega q hq] at hOmegaQ
    exact hOmegaQ
  have hCutoff_one : 1 ≤ hExpCutoff N := by
    rw [show (1 : ℝ) = Real.exp 0 by simp, hExpCutoff]
    exact Real.exp_le_exp.2 (Real.sqrt_nonneg _)
  rcases exists_prunedData_after_radical_selection (N := N) (K := K)
      (Q := Q) (S := Fiber) a hFiber_sub_Q hRange hDisj
      hFiber_nonempty hKpos hKbound hCutoff_one
      hFiber_modLower hFiber_hExp hFiber_omega with
    ⟨D, hFiber_le_D⟩
  have hD_from_fiber :
      (Fiber.card : ℝ) * Lscale (-(ε / 3)) N ≤ (D.Q.card : ℝ) := by
    exact card_lower_of_mul_factor_le_Lscale
      (S := Fiber) (S' := D.Q)
      (C := Nat.ceil (hExpCutoff N ^ 2 * (2 : ℝ) ^ K))
      (N := N) (η := ε / 3) hFiber_le_D (hRadLoss K hKbound)
  refine ⟨D, ?_⟩
  have hLsplit :
      Lscale (-ε) N =
        Lscale (-(ε / 3)) N * Lscale (-(ε / 3)) N *
          Lscale (-(ε / 3)) N := by
    calc
      Lscale (-ε) N
          = Lscale (-(ε / 3) + -(ε / 3) + -(ε / 3)) N := by
              congr 1
              ring
      _ = Lscale (-(ε / 3) + -(ε / 3)) N *
            Lscale (-(ε / 3)) N := by
              rw [Lscale_add]
      _ = Lscale (-(ε / 3)) N * Lscale (-(ε / 3)) N *
            Lscale (-(ε / 3)) N := by
              rw [Lscale_add]
  calc
    (Q.card : ℝ) * Lscale (-ε) N
        = (((Q.card : ℝ) * Lscale (-(ε / 3)) N) *
            Lscale (-(ε / 3)) N) * Lscale (-(ε / 3)) N := by
          rw [hLsplit]
          ring
    _ ≤ ((Good.card : ℝ) * Lscale (-(ε / 3)) N) *
          Lscale (-(ε / 3)) N := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hGood_large (Lscale_nonneg _ _))
            (Lscale_nonneg _ _)
    _ ≤ (Fiber.card : ℝ) * Lscale (-(ε / 3)) N := by
          exact mul_le_mul_of_nonneg_right hFiber_large (Lscale_nonneg _ _)
    _ ≤ (D.Q.card : ℝ) := hD_from_fiber

/-!
The pruning proof uses the following BFV-local inputs:

* `bfv_lower_bound_theorem` to compare deleted sets with a near-extremal `Q`.
* `bfv_omega_tail_theorem` to delete the large-omega tail.
* `hExp_rare_count_rankin_squarefull` to delete large hExp values.
* `rad_multiplicity_bfv33` and `choose_one_per_fiber_card_lower` to choose one
  representative per radical.

The remaining work in this file is epsilon bookkeeping: each deletion and each
pigeonhole loss is bounded by a small `Lscale(η, N)` factor, and the factors are
combined with `Lscale_add`.
-/

/--
Bookkeeping target for BFV pruning.

The analytic and finite inputs are now named separately.  This theorem is the
remaining assembly step: compare the three deleted sets against a near-extremal
input family, pigeonhole an omega fiber, apply the radical representative
selection, and package the result as `PrunedData`.
-/
theorem bfv_pruning_bookkeeping_from_bfv_inputs :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
        ∃ D : PrunedData N,
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N :=
  by
    intro ε hε
    by_cases hsmall : ε ≤ 1 / 4
    · exact bfv_pruning_small_epsilon_theorem ε hε hsmall
    · have hquarter_pos : (0 : ℝ) < 1 / 4 := by norm_num
      have hquarter_le : (1 / 4 : ℝ) ≤ ε := le_of_lt (lt_of_not_ge hsmall)
      filter_upwards [bfv_pruning_small_epsilon_theorem (1 / 4) hquarter_pos le_rfl]
        with N hPruneQuarter Q a hRange hDisj _hQlarge
      rcases exists_admissible_card_f N with ⟨Q₀, hQ₀adm, hQ₀card⟩
      rcases hQ₀adm.2 with ⟨a₀, ha₀⟩
      have hQ₀large :
          (Q₀.card : ℝ) ≥ (f N : ℝ) * Lscale (-(1 / 4 : ℝ)) N := by
        rw [hQ₀card]
        calc
          (f N : ℝ) * Lscale (-(1 / 4 : ℝ)) N
              ≤ (f N : ℝ) * 1 := by
                exact mul_le_mul_of_nonneg_left
                  (Lscale_neg_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4) N)
                  (by positivity)
          _ = (f N : ℝ) := by ring
      rcases hPruneQuarter Q₀ a₀ hQ₀adm.1 ha₀ hQ₀large with ⟨D, hD⟩
      refine ⟨D, ?_⟩
      have hQleF : Q.card ≤ f N :=
        le_f_of_possibleCard ⟨Q, ⟨hRange, ⟨a, hDisj⟩⟩, rfl⟩
      have hLmono : Lscale (-ε) N ≤ Lscale (-(1 / 4 : ℝ)) N :=
        Lscale_mono_in_alpha (by linarith) N
      calc
        (Q.card : ℝ) * Lscale (-ε) N
            ≤ (f N : ℝ) * Lscale (-ε) N := by
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hQleF)
                (Lscale_nonneg (-ε) N)
        _ ≤ (f N : ℝ) * Lscale (-(1 / 4 : ℝ)) N := by
              exact mul_le_mul_of_nonneg_left hLmono (by positivity)
        _ = (Q₀.card : ℝ) * Lscale (-(1 / 4 : ℝ)) N := by rw [hQ₀card]
        _ ≤ (D.Q.card : ℝ) := hD

/--
BFV pruning theorem.

Formal target for Erdős Problem 202, Proposition 3.1. From a near-extremal
admissible family `Q`, remove small moduli, large-omega moduli, and large-hExp
moduli; pigeonhole a single omega value; then choose one representative per
radical.  The resulting data satisfy all fields of `PrunedData N` and retain
`Q.card * Lscale (-ε) N` elements.
-/
theorem bfv_pruning_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
        ∃ D : PrunedData N,
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N :=
  bfv_pruning_bookkeeping_from_bfv_inputs

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/P202Optimization.lean
    ============================================================= -/

/-
Erdős Problem 202 — Final optimization layer.

Converts the chain inequality into the upper bound `f(N) ≤ N · L(-(1-ε), N)`.

Key explicit replacements (versus the PDF):

  * `(π²/6)`-constants → `2`, via the elementary `∑_{ν=1}^m 1/ν² ≤ 2`.
  * `T = ∑ W_{r-1}` is bounded by `R K - R(R-1)/2` (no informal `O(R)`).
  * The single inequality `c σ - c²/4 ≤ σ²` is a square-completion.

The `o(1)` of the PDF is replaced by an explicit `η`-quantifier:
"for every `η > 0`, eventually `1 - η ≤ c σ_N - c²/4 + η`".
-/


namespace Erdos202

open Filter
open Asymptotics
open scoped BigOperators

/-! ## §1 Explicit elementary inequalities -/

/-- The crude `∑_{ν=1}^m 1/ν² ≤ 2` replacing Basel. -/
lemma sum_inv_sq_le_two (m : ℕ) :
    ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤ 2 := by
  have hstrong : ∀ m : ℕ, 1 ≤ m →
      ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤
        2 - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero =>
        cases hm
    | succ m ih =>
        cases m with
        | zero =>
            norm_num
        | succ m =>
            rw [Finset.sum_range_succ]
            have ih' : ∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2)
                ≤ 2 - 1 / ((m + 1 : ℕ) : ℝ) :=
              ih (by omega)
            have hstep :
                (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
                  1 / ((m + 1 : ℕ) : ℝ) -
                    1 / (((m + 1 : ℕ) : ℝ) + 1) := by
              have hm1 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
              have hm2 : 0 < ((m + 1 : ℕ) : ℝ) + 1 := by positivity
              field_simp [hm1.ne', hm2.ne']
              ring_nf
              nlinarith [show 0 ≤ (m : ℝ) by positivity]
            calc
              (∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2))
                  + 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ 2
                  ≤ (2 - 1 / ((m + 1 : ℕ) : ℝ))
                      + (1 / ((m + 1 : ℕ) : ℝ) -
                        1 / (((m + 1 : ℕ) : ℝ) + 1)) := by
                    gcongr
              _ = 2 - 1 / ((m + 2 : ℕ) : ℝ) := by
                    norm_num
                    ring
  by_cases hm : m = 0
  · simp [hm]
  · have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
    exact (hstrong m hm1).trans (by
      have hnonneg : 0 ≤ (1 : ℝ) / (m : ℝ) := by positivity
      linarith)

/-- `c σ - c² / 4 ≤ σ²` for any reals `c`, `σ`. Square-completion. -/
lemma quad_bound (c σ : ℝ) : c * σ - c ^ 2 / 4 ≤ σ ^ 2 := by
  nlinarith [sq_nonneg (c / 2 - σ)]

private lemma log_chain_quadratic_algebra
    (M R K σ ε : ℝ) (hM : M ≠ 0) :
    R * σ + R * (-(K / M) / 2 + ε) +
        (2 * R * K - R * (R - 1)) / (4 * M) =
      R * σ - (R * (R - 1)) / (4 * M) + R * ε := by
  field_simp [hM]
  ring

private lemma one_sub_two_div_eq (M : ℝ) (hM : M ≠ 0) :
    1 - 2 / M = (M - 2) / M := by
  field_simp [hM]

private lemma log_chain_shape_algebra
    (M R σ ε sqrtE lambdaE : ℝ) (hM : M ≠ 0) :
    (R * σ - (R * (R - 1)) / (4 * M) + R * ε + sqrtE + lambdaE) / M =
      (R / M) * σ - (R / M) ^ 2 / 4 + (R / M) / (4 * M) + (R / M) * ε +
        sqrtE / M + lambdaE / M := by
  field_simp [hM]
  ring

private lemma eventually_log_const_mul_le_mul_self
    (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.log (A * x) ≤ δ * x := by
  have hAtop : Tendsto (fun x : ℝ => A * x) atTop atTop :=
    tendsto_id.const_mul_atTop hA
  have hsmallA :
      (fun x : ℝ => Real.log (A * x)) =o[atTop] fun x : ℝ => A * x :=
    Real.isLittleO_log_id_atTop.comp_tendsto hAtop
  have hbig : (fun x : ℝ => A * x) =O[atTop] fun x : ℝ => x :=
    isBigO_const_mul_self A (fun x : ℝ => x) atTop
  have hsmall : (fun x : ℝ => Real.log (A * x)) =o[atTop] fun x : ℝ => x :=
    hsmallA.trans_isBigO hbig
  filter_upwards [isLittleO_iff.mp hsmall hδ, eventually_gt_atTop (0 : ℝ)]
    with x hx hxpos
  calc
    Real.log (A * x) ≤ ‖Real.log (A * x)‖ := le_abs_self _
    _ ≤ δ * ‖x‖ := hx
    _ = δ * x := by rw [Real.norm_of_nonneg hxpos.le]

private lemma eventually_log_chainLambda_le_mul_loglog
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ D : PrunedData N,
        Real.log (chainLambda D) ≤ δ * Real.log (Real.log (N : ℝ)) := by
  let B : ℝ := |Real.log (3 * Real.exp 1)| + 1
  let A : ℝ := 2 * denseCoreConstant * B
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos (mul_pos (by norm_num) denseCoreConstant_pos) hBpos
  have hlogA_real := eventually_log_const_mul_le_mul_self A δ hApos hδ
  have hlogA :
      ∀ᶠ N : ℕ in atTop,
        Real.log (A * Real.log (Real.log (N : ℝ))) ≤
          δ * Real.log (Real.log (N : ℝ)) :=
    tendsto_loglog_nat_atTop.eventually hlogA_real
  filter_upwards [hlogA, eventually_Mscale_le_log, eventually_sqrt_loglog_ge 1,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N hlogA_N hMle hsqrtloglog hNlarge_nat D
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_ge_one : 1 ≤ Real.log (Real.log (N : ℝ)) := by
    rw [← Real.one_le_sqrt]
    exact hsqrtloglog
  have hKle_log : (D.K : ℝ) ≤ 3 * Real.log (N : ℝ) := by
    nlinarith [D.K_bound, hMle]
  have hKpos_real : 0 < (D.K : ℝ) := by exact_mod_cast D.K_pos
  have harg_pos : 0 < Real.exp 1 * (D.K : ℝ) :=
    mul_pos (Real.exp_pos 1) hKpos_real
  have harg_le :
      Real.exp 1 * (D.K : ℝ) ≤ Real.exp 1 * (3 * Real.log (N : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hKle_log (Real.exp_pos 1).le
  have hlog_arg_le :
      Real.log (Real.exp 1 * (D.K : ℝ)) ≤
        Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) :=
    Real.log_le_log harg_pos harg_le
  have hlog_three_pos : 0 < 3 * Real.exp 1 := by positivity
  have hlog_rhs :
      Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) =
        Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ)) := by
    have hmul :
        Real.exp 1 * (3 * Real.log (N : ℝ)) =
          (3 * Real.exp 1) * Real.log (N : ℝ) := by ring
    rw [hmul, Real.log_mul hlog_three_pos.ne' hlog_pos.ne']
  have hlog_part_le :
      Real.log (Real.exp 1 * (D.K : ℝ)) ≤
        B * Real.log (Real.log (N : ℝ)) := by
    calc
      Real.log (Real.exp 1 * (D.K : ℝ))
          ≤ Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) := hlog_arg_le
      _ = Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ)) := hlog_rhs
      _ ≤ B * Real.log (Real.log (N : ℝ)) := by
            dsimp [B]
            have hconst_le : Real.log (3 * Real.exp 1) ≤ |Real.log (3 * Real.exp 1)| :=
              le_abs_self _
            have hconst_mul :
                |Real.log (3 * Real.exp 1)| ≤
                  |Real.log (3 * Real.exp 1)| * Real.log (Real.log (N : ℝ)) :=
              le_mul_of_one_le_right (abs_nonneg _) hloglog_ge_one
            calc
              Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ))
                  ≤ |Real.log (3 * Real.exp 1)| + Real.log (Real.log (N : ℝ)) := by
                    exact add_le_add hconst_le le_rfl
              _ ≤ |Real.log (3 * Real.exp 1)| * Real.log (Real.log (N : ℝ)) +
                    Real.log (Real.log (N : ℝ)) := by
                    exact add_le_add hconst_mul le_rfl
              _ = (|Real.log (3 * Real.exp 1)| + 1) *
                    Real.log (Real.log (N : ℝ)) := by ring
  have hLambda_le :
      chainLambda D ≤ A * Real.log (Real.log (N : ℝ)) := by
    rw [chainLambda, chainKappa]
    calc
      2 * (denseCoreConstant * Real.log (Real.exp 1 * (D.K : ℝ)))
          = 2 * denseCoreConstant * Real.log (Real.exp 1 * (D.K : ℝ)) := by ring
      _ ≤ 2 * denseCoreConstant * (B * Real.log (Real.log (N : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hlog_part_le
              (mul_nonneg (by norm_num) denseCoreConstant_pos.le)
      _ = A * Real.log (Real.log (N : ℝ)) := by
            dsimp [A]
            ring
  exact (Real.log_le_log (chainLambda_pos D) hLambda_le).trans hlogA_N

private lemma coeff_sum_two (R : ℕ) :
    (∑ j : Fin R, (R - j.1)) * 2 = R * (R + 1) := by
  rw [Fin.sum_univ_eq_sum_range]
  have hreflect :
      (∑ x ∈ Finset.range R, (R - x)) =
        ∑ x ∈ Finset.range R, (x + 1) := by
    rw [← Finset.sum_range_reflect (fun x => x + 1) R]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    omega
  rw [hreflect]
  have hsumadd :
      (∑ x ∈ Finset.range R, (x + 1)) =
        (∑ x ∈ Finset.range R, x) + R := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    simp
  rw [hsumadd]
  have hid := Finset.sum_range_id_mul_two R
  by_cases hR : R = 0
  · simp [hR]
  · apply Nat.cast_injective (R := ℤ)
    push_cast
    have hcast_sub : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by
      omega
    have hidz : ((∑ i ∈ Finset.range R, (i : ℕ) : ℕ) : ℤ) * 2 =
        (R : ℤ) * ((R : ℤ) - 1) := by
      have hid' : (((∑ i ∈ Finset.range R, i) * 2 : ℕ) : ℤ) =
          ((R * (R - 1) : ℕ) : ℤ) := by
        exact_mod_cast hid
      simpa [Nat.cast_mul, hcast_sub] using hid'
    ring_nf at hidz ⊢
    nlinarith

/-- The `T`-bound: if `R, K ≥ 0` with `R ≤ K` and weights `w_j ≥ 1` summing
to `K`, then `T = ∑ (R - j + 1) w_j ≤ R K - R (R - 1) / 2`. Discrete; no
asymptotics. -/
lemma chain_T_bound
    {R K : ℕ} (hRK : R ≤ K)
    (w : Fin R → ℕ) (hw_pos : ∀ j, 1 ≤ w j)
    (hw_sum : (∑ j, w j) = K) :
    (∑ j : Fin R, (R - j.1) * w j) * 2 ≤ 2 * R * K - R * (R - 1) := by
  let u : Fin R → ℕ := fun j => w j - 1
  let c : Fin R → ℕ := fun j => R - j.1
  have hw_decomp : ∀ j, w j = u j + 1 := by
    intro j
    simp [u, Nat.sub_add_cancel (hw_pos j)]
  have hsum_u_add : (∑ j, u j) + R = K := by
    calc
      (∑ j, u j) + R = (∑ j, u j) + ∑ _j : Fin R, 1 := by simp
      _ = ∑ j : Fin R, (u j + 1) := by rw [Finset.sum_add_distrib]
      _ = ∑ j : Fin R, w j := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [hw_decomp j]
      _ = K := hw_sum
  have hsum_u : ∑ j, u j = K - R := by omega
  have hmain_sum :
      (∑ j : Fin R, c j * w j) =
        (∑ j : Fin R, c j * u j) + ∑ j : Fin R, c j := by
    calc
      (∑ j : Fin R, c j * w j)
          = ∑ j : Fin R, c j * (u j + 1) := by
              apply Finset.sum_congr rfl
              intro j _hj
              rw [hw_decomp j]
      _ = ∑ j : Fin R, (c j * u j + c j) := by
              apply Finset.sum_congr rfl
              intro j _hj
              rw [Nat.mul_add, Nat.mul_one]
      _ = (∑ j : Fin R, c j * u j) + ∑ j : Fin R, c j := by
              rw [Finset.sum_add_distrib]
  have hweighted :
      ∑ j : Fin R, c j * u j ≤ R * (∑ j : Fin R, u j) := by
    calc
      ∑ j : Fin R, c j * u j ≤ ∑ j : Fin R, R * u j := by
        apply Finset.sum_le_sum
        intro j _hj
        exact Nat.mul_le_mul_right (u j) (Nat.sub_le R j.1)
      _ = R * (∑ j : Fin R, u j) := by
        rw [Finset.mul_sum]
  have hS_le :
      (∑ j : Fin R, c j * w j) ≤ R * (K - R) + ∑ j : Fin R, c j := by
    rw [hmain_sum]
    have hweighted' : ∑ j : Fin R, c j * u j ≤ R * (K - R) := by
      simpa [hsum_u] using hweighted
    exact Nat.add_le_add_right hweighted' _
  have hcoeff : (∑ j : Fin R, c j) * 2 = R * (R + 1) := by
    simpa [c] using coeff_sum_two R
  have hadd :
      ((∑ j : Fin R, c j * w j) * 2) + R * (R - 1) ≤ 2 * R * K := by
    have h2 : (∑ j : Fin R, c j * w j) * 2
        ≤ (R * (K - R) + ∑ j : Fin R, c j) * 2 :=
      Nat.mul_le_mul_right 2 hS_le
    have hbound :
        (R * (K - R) + ∑ j : Fin R, c j) * 2 + R * (R - 1) = 2 * R * K := by
      by_cases hR0 : R = 0
      · subst R
        simp [c]
      · apply Nat.cast_injective (R := ℤ)
        push_cast
        have hKsub : ((K - R : ℕ) : ℤ) = (K : ℤ) - (R : ℤ) := by
          omega
        have hRsub : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by
          omega
        have hcoeffz : (((∑ j : Fin R, c j) * 2 : ℕ) : ℤ) =
            ((R * (R + 1) : ℕ) : ℤ) := by
          exact_mod_cast hcoeff
        rw [hKsub, hRsub]
        push_cast at hcoeffz
        ring_nf at hcoeffz ⊢
        nlinarith
    exact (Nat.add_le_add_right h2 _).trans_eq hbound
  simpa [c] using Nat.le_sub_of_add_le hadd

/-! ## §2 The σ-bookkeeping -/

/-- `σ_N = log(N / |Q'|) / Z(N)`. The shape parameter that the
optimization shows must satisfy `σ_N ≥ 1 - O(η)` eventually. -/
noncomputable def sigmaN (N : ℕ) (Qcard : ℕ) : ℝ :=
  Real.log ((N : ℝ) / (Qcard : ℝ)) / Zscale N

lemma sigmaN_nonneg {N Qcard : ℕ}
    (hQpos : 0 < Qcard) (hQleN : Qcard ≤ N) (hZ : 0 < Zscale N) :
    0 ≤ sigmaN N Qcard := by
  have hQpos_real : 0 < (Qcard : ℝ) := Nat.cast_pos.mpr hQpos
  have hQleN_real : (Qcard : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hQleN
  have hone : 1 ≤ (N : ℝ) / (Qcard : ℝ) :=
    (one_le_div hQpos_real).2 hQleN_real
  rw [sigmaN]
  exact div_nonneg (Real.log_nonneg hone) hZ.le

private lemma product_lower_of_chain_stop {N : ℕ} {D : PrunedData N}
    {S : ChainState N D}
    (hStop : (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) :
    (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) := by
  rcases hStop with hProd | hW
  · exact hProd
  · exact S.productP_lower_of_W_eq_K hW

private lemma one_sub_le_of_sq_lower
    {η δ σ : ℝ} (hη_nonneg : 0 ≤ η) (hη_le_one : η ≤ 1)
    (hδ_le : δ ≤ η) (hσ_nonneg : 0 ≤ σ)
    (hsq : 1 - δ ≤ σ ^ 2) :
    1 - η ≤ σ := by
  have hone_sub_nonneg : 0 ≤ 1 - η := by linarith
  have hsquare_left : (1 - η) ^ 2 ≤ 1 - δ := by
    have hsq_le_linear : (1 - η) ^ 2 ≤ 1 - η := by
      nlinarith [hη_nonneg, hη_le_one]
    linarith
  have hsquare : (1 - η) ^ 2 ≤ σ ^ 2 := hsquare_left.trans hsq
  exact (sq_le_sq₀ hone_sub_nonneg hσ_nonneg).1 hsquare

lemma card_le_of_sigma_lower {η : ℝ} {N Qcard : ℕ}
    (hN : 0 < N) (hQ : 0 < Qcard) (hZ : 0 < Zscale N)
    (hsigma : 1 - η ≤ sigmaN N Qcard) :
    (Qcard : ℝ) ≤ (N : ℝ) * Lscale (-(1 - η)) N := by
  have hQreal : 0 < (Qcard : ℝ) := by exact_mod_cast hQ
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hratio_pos : 0 < (N : ℝ) / (Qcard : ℝ) := div_pos hNreal hQreal
  have hlog :
      (1 - η) * Zscale N ≤ Real.log ((N : ℝ) / (Qcard : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hsigma hZ.le
    rw [sigmaN, div_mul_cancel₀ _ hZ.ne'] at hmul
    exact hmul
  have hexp_le_ratio :
      Real.exp ((1 - η) * Zscale N) ≤ (N : ℝ) / (Qcard : ℝ) :=
    (Real.le_log_iff_exp_le hratio_pos).1 hlog
  have hmulQ :
      (Qcard : ℝ) * Real.exp ((1 - η) * Zscale N) ≤ (N : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hexp_le_ratio hQreal.le
    rw [div_mul_cancel₀ _ hQreal.ne'] at hmul
    simpa [mul_comm] using hmul
  have hcancel :
      Real.exp ((1 - η) * Zscale N) *
          Real.exp (-((1 - η) * Zscale N)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    (Qcard : ℝ)
        = ((Qcard : ℝ) * Real.exp ((1 - η) * Zscale N)) *
            Real.exp (-((1 - η) * Zscale N)) := by
          rw [mul_assoc, hcancel, mul_one]
    _ ≤ (N : ℝ) * Real.exp (-((1 - η) * Zscale N)) := by
          exact mul_le_mul_of_nonneg_right hmulQ (Real.exp_pos _).le
    _ = (N : ℝ) * Lscale (-(1 - η)) N := by
          rw [Lscale]
          congr 1
          ring_nf

set_option maxHeartbeats 2000000

/-- **Sigma lower bound** (PDF Section 5). For every `η > 0`, eventually
any pruned family with cardinality `Qcard` derived from a chain with
parameters `(c, d) ∈ [0, 3]²` satisfies `1 - η ≤ c σ_N - c² / 4 + η`,
hence `σ_N ≥ 1 - O(η)`. -/
theorem sigma_lower_bound :
    ∀ η : ℝ, 0 < η → ∀ᶠ N in atTop,
      ∀ Qcard : ℕ, 1 ≤ Qcard →
        (∃ D : PrunedData N, D.Q.card = Qcard) →
        1 - η ≤ sigmaN N Qcard := by
  intro η hη
  let ε : ℝ := η / 8
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  filter_upwards [bfv_omega_count_input ε hε,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_Mscale_ge (8 / η) (by positivity),
      eventually_sqrt_loglog_ge (96 / η),
      eventually_log_chainLambda_le_mul_loglog (η / 144) (by positivity)] with
    N hCount hNlarge_nat hMlarge hSqrtLogLogLarge hLogLambdaSmall
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hZpos : 0 < Zscale N := Zscale_pos_of_exp_one_lt_nat hNlarge
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hNlarge
  have hMZ : Mscale N * Zscale N = Real.log (N : ℝ) :=
    Mscale_mul_Zscale_eq_log hNlarge
  have hZdivM : Zscale N / Mscale N = Real.log (Real.log (N : ℝ)) :=
    Zscale_div_Mscale_eq_loglog hNlarge
  intro Qcard _hQcard hD
  rcases hD with ⟨D, hDcard⟩
  have hsigma_nonneg : 0 ≤ sigmaN N Qcard := by
    have hQleN : Qcard ≤ N := by
      rw [← hDcard]
      exact D.card_le_N
    exact sigmaN_nonneg (Nat.succ_le_iff.mp _hQcard) hQleN hZpos
  rcases chain_inequality N D ε hε hCount with
    ⟨R, S, hR, hRpos, hRle, hStop, hBlocks, hProdUpper⟩
  have hProdLower : (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) :=
    product_lower_of_chain_stop hStop
  have hProdUpperBound : (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S := by
    simpa [chainProductBoundWithLosses, hR] using hProdUpper
  have hLogProduct :
      Real.log ((N : ℝ) * Lscale (-2) N) ≤
        Real.log (chainProductBoundWithLosses ε S) := by
    have hLowerPos : 0 < (N : ℝ) * Lscale (-2) N := by
      exact mul_pos (by exact_mod_cast D.N_pos) (Lscale_pos (-2) N)
    exact Real.log_le_log hLowerPos (hProdLower.trans hProdUpperBound)
  have hLogProductExpanded :
      Real.log (N : ℝ) - 2 * Zscale N ≤
        Real.log (chainProductBoundWithLosses ε S) := by
    have hLogLower :
        Real.log ((N : ℝ) * Lscale (-2) N) =
          Real.log (N : ℝ) - 2 * Zscale N := by
      rw [log_nat_mul_Lscale D.N_pos (-2)]
      ring
    rwa [hLogLower] at hLogProduct
  have hLogChainExpanded :
      Real.log (N : ℝ) - 2 * Zscale N ≤
        (R : ℝ) * Real.log ((N : ℝ) / (D.Q.card : ℝ)) +
          (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
          ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
          2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
          ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) := by
    rw [log_chainProductBoundWithLosses ε S] at hLogProductExpanded
    simpa [hR] using hLogProductExpanded
  have hSigmaLog :
      Real.log ((N : ℝ) / (D.Q.card : ℝ)) =
        sigmaN N Qcard * Zscale N := by
    rw [sigmaN, ← hDcard]
    field_simp [hZpos.ne']
  have hLogChainNormalized :
      Mscale N - 2 ≤
        (R : ℝ) * sigmaN N Qcard +
          (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
          ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
          (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N +
          (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) / Zscale N := by
    have hExpandedSigma :
        Real.log (N : ℝ) - 2 * Zscale N ≤
          (R : ℝ) * (sigmaN N Qcard * Zscale N) +
            (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
            ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
            2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
            ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) := by
      simpa [hSigmaLog] using hLogChainExpanded
    have h :
        (Mscale N - 2) * Zscale N ≤
          ((R : ℝ) * sigmaN N Qcard +
            (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
            ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
            (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N +
            (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) / Zscale N) *
              Zscale N := by
      calc
        (Mscale N - 2) * Zscale N
            = Real.log (N : ℝ) - 2 * Zscale N := by
                rw [← hMZ]
                ring
        _ ≤ (R : ℝ) * (sigmaN N Qcard * Zscale N) +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
              ((((chainT S + S.W : ℕ) : ℝ) / 2) *
                Real.log (Real.log (N : ℝ))) +
              2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
              ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) :=
            hExpandedSigma
        _ = ((R : ℝ) * sigmaN N Qcard +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
              ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
              (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N +
              (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) /
                Zscale N) * Zscale N := by
            rw [← hZdivM]
            field_simp [hMpos.ne', hZpos.ne']
    have hdiv := div_le_div_of_nonneg_right h hZpos.le
    field_simp [hZpos.ne'] at hdiv
    field_simp [hMpos.ne']
    nlinarith [hdiv, hMpos]
  have hTbasic : chainT S ≤ S.r * D.K := S.chainT_le_r_mul_K
  have hTbasicR : chainT S ≤ R * D.K := by
    simpa [hR] using hTbasic
  have hTquad : ((((chainT S + S.W : ℕ) : ℝ) * 2)) ≤
      2 * (S.r : ℝ) * (S.W : ℝ) - (S.r : ℝ) * ((S.r : ℝ) - 1) :=
    S.chainT_add_W_real_quadratic_bound hBlocks
  have hTquadK : ((((chainT S + S.W : ℕ) : ℝ) * 2)) ≤
      2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1) := by
    have hWle : (S.W : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast S.W_le_K
    have hRnonneg : 0 ≤ (R : ℝ) := by positivity
    rw [← hR]
    nlinarith [hTquad, hWle, hRnonneg]
  have hTterm :
      ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) ≤
        (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
          (4 * Mscale N) := by
    calc
      ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N)
          = (((chainT S + S.W : ℕ) : ℝ) * 2) * (1 / (4 * Mscale N)) := by
              field_simp [hMpos.ne']
              ring
      _ ≤ (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) *
            (1 / (4 * Mscale N)) := by
              exact mul_le_mul_of_nonneg_right hTquadK (by positivity)
      _ = (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
            (4 * Mscale N) := by ring
  let sqrtE : ℝ := (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N
  let lambdaE : ℝ :=
    (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) / Zscale N
  have hLogChainQuadratic :
      Mscale N - 2 ≤
        (R : ℝ) * sigmaN N Qcard -
          ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
          (R : ℝ) * ε + sqrtE + lambdaE := by
    calc
      Mscale N - 2
          ≤ (R : ℝ) * sigmaN N Qcard +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
              ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
              sqrtE + lambdaE :=
            hLogChainNormalized
      _ ≤ (R : ℝ) * sigmaN N Qcard +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
              (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
                (4 * Mscale N) + sqrtE + lambdaE := by
            let A : ℝ :=
              (R : ℝ) * sigmaN N Qcard +
                (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε)
            let B : ℝ := sqrtE + lambdaE
            have hmid :
                A + ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) ≤
                  A + (2 * (R : ℝ) * (D.K : ℝ) -
                    (R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) :=
              by
                have hmid' := add_le_add_left hTterm A
                linarith
            have hmidB := add_le_add_right hmid B
            dsimp [A, B] at hmidB
            linarith
      _ = (R : ℝ) * sigmaN N Qcard -
            ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
            (R : ℝ) * ε + sqrtE + lambdaE := by
            have hbase :
                (R : ℝ) * sigmaN N Qcard +
                    (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
                    (2 * (R : ℝ) * (D.K : ℝ) -
                        (R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) =
                  (R : ℝ) * sigmaN N Qcard -
                    ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
                    (R : ℝ) * ε :=
              log_chain_quadratic_algebra (Mscale N) (R : ℝ) (D.K : ℝ)
                (sigmaN N Qcard) ε hMpos.ne'
            rw [hbase]
  let c : ℝ := (R : ℝ) / Mscale N
  have hc_pos : 0 < c := by
    dsimp [c]
    have hRpos_real : 0 < (R : ℝ) := by exact_mod_cast hRpos
    exact div_pos hRpos_real hMpos
  have hc_le_three : c ≤ 3 := by
    dsimp [c]
    have hRleK_real : (R : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hRle
    have hRle3M : (R : ℝ) ≤ 3 * Mscale N := hRleK_real.trans D.K_bound
    exact (div_le_iff₀ hMpos).2 hRle3M
  let sqrtLoss : ℝ := sqrtE / Mscale N
  let lambdaLoss : ℝ := lambdaE / Mscale N
  have hLogChainShape :
      (Mscale N - 2) / Mscale N ≤
        c * sigmaN N Qcard - c ^ 2 / 4 + c / (4 * Mscale N) + c * ε +
          sqrtLoss + lambdaLoss := by
    have hdiv := div_le_div_of_nonneg_right hLogChainQuadratic hMpos.le
    calc
      (Mscale N - 2) / Mscale N
          ≤ ((R : ℝ) * sigmaN N Qcard -
            ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
            (R : ℝ) * ε + sqrtE + lambdaE) / Mscale N := hdiv
      _ = c * sigmaN N Qcard - c ^ 2 / 4 + c / (4 * Mscale N) + c * ε +
            sqrtLoss + lambdaLoss := by
              dsimp [c, sqrtLoss, lambdaLoss]
              exact log_chain_shape_algebra (Mscale N) (R : ℝ) (sigmaN N Qcard)
                ε sqrtE lambdaE hMpos.ne'
  have hsigma_sq_shape :
      (Mscale N - 2) / Mscale N ≤
        (sigmaN N Qcard) ^ 2 + c / (4 * Mscale N) + c * ε +
          sqrtLoss + lambdaLoss := by
    calc
      (Mscale N - 2) / Mscale N
          ≤ c * sigmaN N Qcard - c ^ 2 / 4 + c / (4 * Mscale N) + c * ε +
              sqrtLoss + lambdaLoss :=
            hLogChainShape
      _ ≤ (sigmaN N Qcard) ^ 2 + c / (4 * Mscale N) + c * ε +
              sqrtLoss + lambdaLoss := by
            simpa [add_assoc] using
              add_le_add_right (quad_bound c (sigmaN N Qcard))
                (c / (4 * Mscale N) + c * ε + sqrtLoss + lambdaLoss)
  have hsigma_sq_shape_three :
      (Mscale N - 2) / Mscale N ≤
        (sigmaN N Qcard) ^ 2 + 3 / (4 * Mscale N) + 3 * ε +
          sqrtLoss + lambdaLoss := by
    have hsmall1 : c / (4 * Mscale N) ≤ 3 / (4 * Mscale N) := by
      exact div_le_div_of_nonneg_right hc_le_three (by positivity)
    have hsmall2 : c * ε ≤ 3 * ε :=
      mul_le_mul_of_nonneg_right hc_le_three hε.le
    calc
      (Mscale N - 2) / Mscale N
          ≤ (sigmaN N Qcard) ^ 2 + c / (4 * Mscale N) + c * ε +
              sqrtLoss + lambdaLoss :=
            hsigma_sq_shape
      _ ≤ (sigmaN N Qcard) ^ 2 + 3 / (4 * Mscale N) + 3 * ε +
              sqrtLoss + lambdaLoss := by
            have herr :
                c / (4 * Mscale N) + c * ε ≤
                  3 / (4 * Mscale N) + 3 * ε :=
              add_le_add hsmall1 hsmall2
            linarith
  have hsigma_sq_lower :
      1 - (2 / Mscale N + 3 / (4 * Mscale N) + 3 * ε +
          sqrtLoss + lambdaLoss) ≤
        (sigmaN N Qcard) ^ 2 := by
    have hleft : (Mscale N - 2) / Mscale N = 1 - 2 / Mscale N :=
      (one_sub_two_div_eq (Mscale N) hMpos.ne').symm
    linarith [hsigma_sq_shape_three, hleft]
  by_cases hη_big : 1 ≤ η
  · have htarget : 1 - η ≤ 0 := by linarith
    exact htarget.trans hsigma_nonneg
  have hη_le_one : η ≤ 1 := le_of_lt (not_le.mp hη_big)
  let δN : ℝ :=
    2 / Mscale N + 3 / (4 * Mscale N) + 3 * ε + sqrtLoss + lambdaLoss
  have hfinish_of_error (hδN : δN ≤ η) : 1 - η ≤ sigmaN N Qcard := by
    exact one_sub_le_of_sq_lower hη.le hη_le_one hδN hsigma_nonneg (by
      simpa [δN] using hsigma_sq_lower)
  have hδN_le : δN ≤ η := by
    have hApos : 0 < (8 : ℝ) / η := by positivity
    have hinvM_raw : 1 / Mscale N ≤ 1 / (8 / η) :=
      one_div_le_one_div_of_le hApos hMlarge
    have hinvM : 1 / Mscale N ≤ η / 8 := by
      convert hinvM_raw using 1
      field_simp [hη.ne']
    dsimp [δN, ε]
    have hterm1 : 2 / Mscale N ≤ η / 4 := by
      have hmul := mul_le_mul_of_nonneg_left hinvM (show 0 ≤ (2 : ℝ) by norm_num)
      convert hmul using 1 <;> ring
    have hterm2 : 3 / (4 * Mscale N) ≤ 3 * η / 32 := by
      have hmul := mul_le_mul_of_nonneg_left hinvM (show 0 ≤ (3 / 4 : ℝ) by norm_num)
      convert hmul using 1
      · field_simp [hMpos.ne']
      · ring
    have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
      Real.log_pos ((Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hNlarge)).2 hNlarge)
    have hsqrtlog_pos : 0 < Real.sqrt (Real.log (N : ℝ)) := by
      have hlog_pos : 0 < Real.log (N : ℝ) :=
        zero_lt_one.trans ((Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hNlarge)).2 hNlarge)
      rw [Real.sqrt_pos]
      exact hlog_pos
    have hsqrtloglog_pos :
        0 < Real.sqrt (Real.log (Real.log (N : ℝ))) := by
      have hlarge_pos : 0 < (96 : ℝ) / η := by positivity
      exact hlarge_pos.trans_le hSqrtLogLogLarge
    have hRle3M : (R : ℝ) ≤ 3 * Mscale N := by
      have hRleK_real : (R : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hRle
      exact hRleK_real.trans D.K_bound
    have hsqrtLoss_le : sqrtLoss ≤ η / 16 := by
      have hfactor_nonneg :
          0 ≤ 2 * Real.sqrt (Real.log (N : ℝ)) / (Zscale N * Mscale N) := by
        positivity
      calc
        sqrtLoss
            = (R : ℝ) *
                (2 * Real.sqrt (Real.log (N : ℝ)) / (Zscale N * Mscale N)) := by
              dsimp [sqrtLoss, sqrtE]
              field_simp [hZpos.ne', hMpos.ne']
        _ ≤ (3 * Mscale N) *
              (2 * Real.sqrt (Real.log (N : ℝ)) / (Zscale N * Mscale N)) := by
              exact mul_le_mul_of_nonneg_right hRle3M hfactor_nonneg
        _ = 6 / Real.sqrt (Real.log (Real.log (N : ℝ))) := by
              rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge]
              field_simp [hMpos.ne', hsqrtlog_pos.ne', hsqrtloglog_pos.ne']
              ring
        _ ≤ 6 / (96 / η) := by
              exact div_le_div_of_nonneg_left (by norm_num)
                (by positivity) hSqrtLogLogLarge
        _ = η / 16 := by
              field_simp [hη.ne']
              ring
    have hTplus_le_RK :
        (((chainT S + S.W : ℕ) : ℝ)) ≤ (R : ℝ) * (D.K : ℝ) := by
      have hRge_one_real : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hRpos
      have hquad_nonneg : 0 ≤ (R : ℝ) * ((R : ℝ) - 1) := by
        nlinarith [hRge_one_real]
      have hT2_le_2RK :
          (((chainT S + S.W : ℕ) : ℝ) * 2) ≤
            2 * (R : ℝ) * (D.K : ℝ) := by
        nlinarith [hTquadK, hquad_nonneg]
      nlinarith
    have hTplus_le_9M2 :
        (((chainT S + S.W : ℕ) : ℝ)) ≤ 9 * (Mscale N) ^ 2 := by
      have hKle3M : (D.K : ℝ) ≤ 3 * Mscale N := D.K_bound
      have hRnonneg : 0 ≤ (R : ℝ) := by positivity
      have hKnonneg : 0 ≤ (D.K : ℝ) := by positivity
      have hRK_le : (R : ℝ) * (D.K : ℝ) ≤ (3 * Mscale N) * (3 * Mscale N) :=
        mul_le_mul hRle3M hKle3M hKnonneg (by positivity)
      nlinarith [hTplus_le_RK, hRK_le]
    have hlambdaLog_le :
        Real.log (chainLambda D) ≤
          (η / 144) * Real.log (Real.log (N : ℝ)) :=
      hLogLambdaSmall D
    have hlambdaLoss_le : lambdaLoss ≤ η / 16 := by
      have hcoef_nonneg :
          0 ≤ (η / 144) * Real.log (Real.log (N : ℝ)) := by positivity
      have hTnonneg : 0 ≤ (((chainT S + S.W : ℕ) : ℝ)) := by positivity
      have hnum_le :
          (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) ≤
            (9 * (Mscale N) ^ 2) *
              ((η / 144) * Real.log (Real.log (N : ℝ))) := by
        have hlog_scaled :
            (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) ≤
              (((chainT S + S.W : ℕ) : ℝ) *
                ((η / 144) * Real.log (Real.log (N : ℝ)))) :=
          mul_le_mul_of_nonneg_left hlambdaLog_le hTnonneg
        have hT_scaled :
            (((chainT S + S.W : ℕ) : ℝ) *
                ((η / 144) * Real.log (Real.log (N : ℝ)))) ≤
              (9 * (Mscale N) ^ 2) *
                ((η / 144) * Real.log (Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_right hTplus_le_9M2 hcoef_nonneg
        exact hlog_scaled.trans hT_scaled
      have hMll := Mscale_mul_loglog_eq_Zscale hNlarge
      calc
        lambdaLoss
            = (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) /
                (Zscale N * Mscale N) := by
              dsimp [lambdaLoss, lambdaE]
              field_simp [hZpos.ne', hMpos.ne']
        _ ≤ ((9 * (Mscale N) ^ 2) *
                ((η / 144) * Real.log (Real.log (N : ℝ)))) /
                (Zscale N * Mscale N) := by
              exact div_le_div_of_nonneg_right hnum_le
                (mul_nonneg hZpos.le hMpos.le)
        _ = η / 16 := by
              rw [← hMll]
              field_simp [hMpos.ne', hloglog_pos.ne']
              ring
    have hmain_le :
        2 / Mscale N + 3 / (4 * Mscale N) + 3 * (η / 8) ≤
          (23 / 32) * η := by
      calc
        2 / Mscale N + 3 / (4 * Mscale N) + 3 * (η / 8)
          ≤ η / 4 + 3 * η / 32 + 3 * (η / 8) := by
            gcongr
        _ = (23 / 32) * η := by ring
    calc
      2 / Mscale N + 3 / (4 * Mscale N) + 3 * (η / 8) + sqrtLoss + lambdaLoss
          ≤ (23 / 32) * η + η / 16 + η / 16 := by
            linarith [hmain_le, hsqrtLoss_le, hlambdaLoss_le]
      _ = (27 / 32) * η := by ring
      _ ≤ η := by
            exact mul_le_of_le_one_left hη.le (by norm_num)
  exact hfinish_of_error hδN_le

/-! ## §3 The upper bound -/

/-- **Upper bound for f.** From the chain inequality and σ-optimization,
`f(N) ≤ N · L(-(1 - ε), N)` for every `ε > 0`, eventually. -/
theorem f_upper_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (f N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N := by
  intro ε hε
  let ε0 : ℝ := min ε (1 / 2)
  have hε0 : 0 < ε0 := by
    dsimp [ε0]
    exact lt_min hε (by norm_num)
  have hε0leε : ε0 ≤ ε := by
    dsimp [ε0]
    exact min_le_left ε (1 / 2)
  let δ : ℝ := ε0 / 3
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδle_quarter : δ ≤ 1 / 4 := by
    dsimp [δ, ε0]
    have hmin : min ε (1 / 2) ≤ (1 / 2 : ℝ) := min_le_right ε (1 / 2)
    linarith
  have h2δ : 2 * δ ≤ ε := by
    dsimp [δ]
    linarith
  filter_upwards [bfv_pruning_small_epsilon_theorem δ hδ hδle_quarter,
      sigma_lower_bound δ hδ,
      eventually_Zscale_pos] with N hPrune hSigma hZ
  classical
  rcases exists_admissible_card_f N with ⟨Q, hQadm, hQcard⟩
  rcases hQadm.2 with ⟨a, ha⟩
  have hQlarge : (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-δ) N := by
    rw [hQcard]
    calc
      (f N : ℝ) * Lscale (-δ) N ≤ (f N : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left (Lscale_neg_le_one hδ.le N) (by positivity)
      _ = (f N : ℝ) := by ring
  rcases hPrune Q a hQadm.1 ha hQlarge with ⟨D, hDlower⟩
  have hSigmaD :
      1 - δ ≤ sigmaN N D.Q.card :=
    hSigma D.Q.card (Nat.succ_le_of_lt D.card_pos) ⟨D, rfl⟩
  have hDupper :
      (D.Q.card : ℝ) ≤ (N : ℝ) * Lscale (-(1 - δ)) N :=
    card_le_of_sigma_lower D.N_pos D.card_pos hZ hSigmaD
  have hf_to_D :
      (f N : ℝ) ≤ (D.Q.card : ℝ) * Lscale δ N := by
    calc
      (f N : ℝ)
          = ((f N : ℝ) * Lscale (-δ) N) * Lscale δ N := by
              rw [mul_assoc, Lscale_neg_mul, mul_one]
      _ ≤ (D.Q.card : ℝ) * Lscale δ N := by
              exact mul_le_mul_of_nonneg_right
                (by simpa [hQcard] using hDlower) (Lscale_nonneg δ N)
  calc
    (f N : ℝ) ≤ (D.Q.card : ℝ) * Lscale δ N := hf_to_D
    _ ≤ ((N : ℝ) * Lscale (-(1 - δ)) N) * Lscale δ N := by
          exact mul_le_mul_of_nonneg_right hDupper (Lscale_nonneg δ N)
    _ = (N : ℝ) * (Lscale (-(1 - δ)) N * Lscale δ N) := by ring
    _ = (N : ℝ) * Lscale (-(1 - δ) + δ) N := by
          rw [Lscale_add]
    _ = (N : ℝ) * Lscale (-(1 - 2 * δ)) N := by
          congr 1
          congr 1
          ring
    _ ≤ (N : ℝ) * Lscale (-(1 - ε)) N := by
          exact mul_le_mul_of_nonneg_left
            (Lscale_mono_in_alpha (by linarith) N) (by positivity)

end Erdos202


/-! =============================================================
    Section from: Erdos/P202/P202Main.lean
    ============================================================= -/

/-
Erdős Problem 202 — Main theorem.

Combines:
  * upper bound from `Optimization.f_upper_bound`
    (Chain inequality + σ optimization, conditional on the BFV inputs and
     the spread-disjointness input);
  * lower bound from `bfv_lower_bound_theorem`.

The historical omega-count and lower-bound input names now point to theorem
aliases.  The current non-core trust boundary is visible through
`#print axioms Erdos202.erdos202_main`: the only project-level dependency is
the Park--Pham threshold package.

Audit by uncommenting the `#print axioms` block below.
-/


namespace Erdos202

open Filter
open scoped BigOperators

/-- **Conditional Erdős 202 upper bound.** From the BFV pruning theorem layer,
omega-count theorem layer, and spread theorem layer, the upper half of the
asymptotic holds. -/
theorem erdos202_upper_bound_from_inputs :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (f N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N :=
  f_upper_bound

/-- **Erdős Problem 202 — main theorem.** The sharp BFV asymptotic
`f(N) = N · exp(-(1 + o(1)) · sqrt(log N · log log N))`. -/
theorem erdos202_main : Erdos202Statement := by
  intro ε hε
  filter_upwards [bfv_lower_bound_theorem ε hε, f_upper_bound ε hε] with N hLow hUp
  exact ⟨hLow, hUp⟩

/-! ## Axiom audit

The block below audits the public theorem path.  The expected output is only
the standard Mathlib core axioms `propext`, `Classical.choice`, and
`Quot.sound`.
-/

-- #print axioms erdos202_upper_bound_from_inputs
-- #print axioms erdos202_main

end Erdos202

/-! ## Axiom audit -/

#print axioms Erdos202.erdos202_main
-- 'Erdos202.erdos202_main' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Erdos202.ParkPham.park_pham_threshold_not_small_lt_exists
-- 'Erdos202.ParkPham.park_pham_threshold_not_small_lt_exists' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms Erdos202.ParkPham.spread_disjointness_theorem
-- 'Erdos202.ParkPham.spread_disjointness_theorem' depends on axioms: [propext,
-- Classical.choice, Quot.sound]
#print axioms Erdos202.bfv_pruning_theorem
-- 'Erdos202.bfv_pruning_theorem' depends on axioms: [propext, Classical.choice,
-- Quot.sound]
#print axioms Erdos202.bfv_omega_count_theorem
-- 'Erdos202.bfv_omega_count_theorem' depends on axioms: [propext, Classical.choice,
-- Quot.sound]
#print axioms Erdos202.bfv_lower_bound_theorem
-- 'Erdos202.bfv_lower_bound_theorem' depends on axioms: [propext, Classical.choice,
-- Quot.sound]
