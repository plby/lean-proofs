/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# A finite-space Freedman inequality

This file proves a self-contained exponential tail estimate for a finite-time
supermartingale on a finite probability space.  A filtration is represented by
maps `info k : Ω → ι`; equality of the time-`j` observations must imply equality
of all earlier observations.  Conditional moment inequalities are stated in
their finite, integrated form: they may be tested against every nonnegative
function which is constant on the fibres of `info k`.

The numerical constant is deliberately a little weaker than the sharp
Freedman constant.  The conclusion

`P(Sₙ ≥ t) ≤ exp (-t² / (4 * (V + R*t)))`

has the same Bernstein/Freedman dependence on the predictable quadratic
variation `V` and the increment bound `R`, and is convenient in random-greedy
arguments.
-/

open scoped BigOperators

namespace Erdos136.Freedman

set_option autoImplicit false

section FiniteSpace

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A real-valued function is known at time `k` if it is constant on every
fibre of the time-`k` information map. -/
def KnownAt (info : ℕ → Ω → ι) (k : ℕ) (f : Ω → ℝ) : Prop :=
  ∀ ⦃ω ω' : Ω⦄, info k ω = info k ω' → f ω = f ω'

/-- The information maps are increasing: later information distinguishes at
least as many outcomes as earlier information. -/
def IsFiltration (info : ℕ → Ω → ι) : Prop :=
  ∀ ⦃i j : ℕ⦄, i ≤ j → ∀ ⦃ω ω' : Ω⦄,
    info j ω = info j ω' → info i ω = info i ω'

/-- Expectation with respect to a finite real-valued mass function. -/
def expectation (p : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω, p ω * X ω

/-- The mass of a finite event in a finite real-valued mass function. -/
def eventMass (p : Ω → ℝ) (A : Finset Ω) : ℝ :=
  ∑ ω ∈ A, p ω

/-- Partial sum of the first `k` increments. -/
def partialSum (d : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, d i ω

@[simp] lemma partialSum_zero (d : ℕ → Ω → ℝ) (ω : Ω) :
    partialSum d 0 ω = 0 := by
  simp [partialSum]

lemma partialSum_succ (d : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    partialSum d (k + 1) ω = partialSum d k ω + d k ω := by
  simp [partialSum, Finset.sum_range_succ]

lemma KnownAt.const (info : ℕ → Ω → ι) (k : ℕ) (c : ℝ) :
    KnownAt info k (fun _ ↦ c) := by
  intro ω ω' h
  rfl

lemma KnownAt.add {info : ℕ → Ω → ι} {k : ℕ} {f g : Ω → ℝ}
    (hf : KnownAt info k f) (hg : KnownAt info k g) :
    KnownAt info k (fun ω ↦ f ω + g ω) := by
  intro ω ω' h
  change f ω + g ω = f ω' + g ω'
  rw [hf h, hg h]

lemma KnownAt.mul {info : ℕ → Ω → ι} {k : ℕ} {f g : Ω → ℝ}
    (hf : KnownAt info k f) (hg : KnownAt info k g) :
    KnownAt info k (fun ω ↦ f ω * g ω) := by
  intro ω ω' h
  change f ω * g ω = f ω' * g ω'
  rw [hf h, hg h]

lemma KnownAt.exp {info : ℕ → Ω → ι} {k : ℕ} {f : Ω → ℝ}
    (hf : KnownAt info k f) :
    KnownAt info k (fun ω ↦ Real.exp (f ω)) := by
  intro ω ω' h
  change Real.exp (f ω) = Real.exp (f ω')
  rw [hf h]

lemma KnownAt.mono {info : ℕ → Ω → ι} (hinfo : IsFiltration info)
    {i j : ℕ} (hij : i ≤ j) {f : Ω → ℝ} (hf : KnownAt info i f) :
    KnownAt info j f := by
  intro ω ω' h
  exact hf (hinfo hij h)

lemma partialSum_known {info : ℕ → Ω → ι} (hinfo : IsFiltration info)
    {d : ℕ → Ω → ℝ} (hadapted : ∀ k, KnownAt info (k + 1) (d k))
    (k : ℕ) : KnownAt info k (partialSum d k) := by
  induction k with
  | zero =>
      intro ω ω' h
      simp
  | succ k ih =>
      rw [show partialSum d (k + 1) = fun ω ↦ partialSum d k ω + d k ω by
        funext ω
        exact partialSum_succ d k ω]
      exact (ih.mono hinfo (Nat.le_succ k)).add (hadapted k)

/-- The elementary exponential estimate used in the proof. -/
lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hx
  have h' : Real.exp x - 1 - x ≤ x ^ 2 := le_trans (le_abs_self _) h
  linarith

lemma exp_mul_le (a x : ℝ) (hax : |a * x| ≤ 1) :
    Real.exp (a * x) ≤ 1 + a * x + a ^ 2 * x ^ 2 := by
  calc
    Real.exp (a * x) ≤ 1 + a * x + (a * x) ^ 2 :=
      exp_le_one_add_add_sq hax
    _ = 1 + a * x + a ^ 2 * x ^ 2 := by ring

/-- The integrated finite-space form of the conditional first- and
second-moment hypotheses.  `mean` says `E[Z dₖ] ≤ 0` and `variance` says
`E[Z dₖ²] ≤ vₖ E[Z]` for every nonnegative time-`k`-known test `Z`.

On a finite probability space this is precisely the fibrewise conditional
supermartingale/conditional second-moment bound (take `Z` to be the indicator
of one fibre). -/
structure ConditionalMomentBounds (p : Ω → ℝ) (info : ℕ → Ω → ι)
    (d : ℕ → Ω → ℝ) (v : ℕ → ℝ) : Prop where
  mean : ∀ k (Z : Ω → ℝ), (∀ ω, 0 ≤ Z ω) → KnownAt info k Z →
    expectation p (fun ω ↦ Z ω * d k ω) ≤ 0
  variance : ∀ k (Z : Ω → ℝ), (∀ ω, 0 ≤ Z ω) → KnownAt info k Z →
    expectation p (fun ω ↦ Z ω * (d k ω) ^ 2) ≤
      v k * expectation p Z

private lemma expectation_exp_step_le
    {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω)
    {info : ℕ → Ω → ι} {d : ℕ → Ω → ℝ} {v : ℕ → ℝ}
    (hmom : ConditionalMomentBounds p info d v)
    (hknown : ∀ k, KnownAt info (k + 1) (d k))
    (hfil : IsFiltration info)
    {R a : ℝ} (ha : 0 ≤ a) (haR : a * R ≤ 1)
    (hR : ∀ k ω, |d k ω| ≤ R) (k : ℕ) :
    expectation p (fun ω ↦ Real.exp (a * partialSum d (k + 1) ω)) ≤
      Real.exp (a ^ 2 * v k) *
        expectation p (fun ω ↦ Real.exp (a * partialSum d k ω)) := by
  let Z : Ω → ℝ := fun ω ↦ Real.exp (a * partialSum d k ω)
  have hZ_nonneg : ∀ ω, 0 ≤ Z ω := fun ω ↦ (Real.exp_pos _).le
  have hZ_known : KnownAt info k Z :=
    ((KnownAt.const info k a).mul (partialSum_known hfil hknown k)).exp
  have hmean := hmom.mean k Z hZ_nonneg hZ_known
  have hvar := hmom.variance k Z hZ_nonneg hZ_known
  have hpoint (ω : Ω) :
      Real.exp (a * partialSum d (k + 1) ω) ≤
        Z ω * (1 + a * d k ω + a ^ 2 * (d k ω) ^ 2) := by
    rw [partialSum_succ, mul_add, Real.exp_add]
    gcongr
    apply exp_mul_le
    calc
      |a * d k ω| = a * |d k ω| := by rw [abs_mul, abs_of_nonneg ha]
      _ ≤ a * R := mul_le_mul_of_nonneg_left (hR k ω) ha
      _ ≤ 1 := haR
  calc
    expectation p (fun ω ↦ Real.exp (a * partialSum d (k + 1) ω))
        ≤ expectation p (fun ω ↦
            Z ω * (1 + a * d k ω + a ^ 2 * (d k ω) ^ 2)) := by
          apply Finset.sum_le_sum
          intro ω hω
          exact mul_le_mul_of_nonneg_left (hpoint ω) (hp ω)
    _ = expectation p Z + a * expectation p (fun ω ↦ Z ω * d k ω) +
          a ^ 2 * expectation p (fun ω ↦ Z ω * (d k ω) ^ 2) := by
          simp only [expectation]
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro ω hω
          ring
    _ ≤ expectation p Z + a ^ 2 * (v k * expectation p Z) := by
          have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
          nlinarith
    _ = (1 + a ^ 2 * v k) * expectation p Z := by ring
    _ ≤ Real.exp (a ^ 2 * v k) * expectation p Z := by
          have hEZ : 0 ≤ expectation p Z := by
            simp only [expectation]
            apply Finset.sum_nonneg
            intro ω hω
            exact mul_nonneg (hp ω) (Real.exp_pos _).le
          gcongr
          simpa [add_comm] using Real.add_one_le_exp (a ^ 2 * v k)

private lemma expectation_exp_partialSum_le
    {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hp_one : ∑ ω, p ω = 1)
    {info : ℕ → Ω → ι} {d : ℕ → Ω → ℝ} {v : ℕ → ℝ}
    (hmom : ConditionalMomentBounds p info d v)
    (hknown : ∀ k, KnownAt info (k + 1) (d k))
    (hfil : IsFiltration info)
    {R a : ℝ} (ha : 0 ≤ a) (haR : a * R ≤ 1)
    (hR : ∀ k ω, |d k ω| ≤ R) (n : ℕ) :
    expectation p (fun ω ↦ Real.exp (a * partialSum d n ω)) ≤
      Real.exp (a ^ 2 * ∑ k ∈ Finset.range n, v k) := by
  induction n with
  | zero => simpa [expectation] using hp_one.le
  | succ n ih =>
      calc
        expectation p (fun ω ↦ Real.exp (a * partialSum d (n + 1) ω))
            ≤ Real.exp (a ^ 2 * v n) *
                expectation p (fun ω ↦ Real.exp (a * partialSum d n ω)) :=
              expectation_exp_step_le hp hmom hknown hfil ha haR hR n
        _ ≤ Real.exp (a ^ 2 * v n) *
              Real.exp (a ^ 2 * ∑ k ∈ Finset.range n, v k) := by
              gcongr
        _ = Real.exp (a ^ 2 * ∑ k ∈ Finset.range (n + 1), v k) := by
              rw [← Real.exp_add, Finset.sum_range_succ]
              congr 1
              ring

private lemma eventMass_le_exp_mul_expectation
    {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (X : Ω → ℝ)
    {t a : ℝ} (ha : 0 ≤ a) :
    eventMass p (Finset.univ.filter (fun ω ↦ t ≤ X ω)) ≤
      Real.exp (-a * t) * expectation p (fun ω ↦ Real.exp (a * X ω)) := by
  have hmarkov :
      Real.exp (a * t) * eventMass p (Finset.univ.filter (fun ω ↦ t ≤ X ω)) ≤
        expectation p (fun ω ↦ Real.exp (a * X ω)) := by
    rw [eventMass, expectation, Finset.mul_sum]
    calc
      ∑ ω ∈ Finset.univ.filter (fun ω ↦ t ≤ X ω),
          Real.exp (a * t) * p ω
          ≤ ∑ ω ∈ Finset.univ.filter (fun ω ↦ t ≤ X ω),
              p ω * Real.exp (a * X ω) := by
            apply Finset.sum_le_sum
            intro ω hω
            have htω : t ≤ X ω := by simpa using (Finset.mem_filter.mp hω).2
            have hexp : Real.exp (a * t) ≤ Real.exp (a * X ω) := by
              rw [Real.exp_le_exp]
              exact mul_le_mul_of_nonneg_left htω ha
            nlinarith [hp ω]
      _ ≤ ∑ ω, p ω * Real.exp (a * X ω) := by
            calc
              ∑ ω ∈ Finset.univ.filter (fun ω ↦ t ≤ X ω),
                    p ω * Real.exp (a * X ω)
                  ≤ (∑ ω ∈ Finset.univ.filter (fun ω ↦ t ≤ X ω),
                        p ω * Real.exp (a * X ω)) +
                      ∑ ω ∈ Finset.univ.filter (fun ω ↦ ¬t ≤ X ω),
                        p ω * Real.exp (a * X ω) := by
                    apply le_add_of_nonneg_right
                    apply Finset.sum_nonneg
                    intro ω hω
                    exact mul_nonneg (hp ω) (Real.exp_pos _).le
              _ = ∑ ω, p ω * Real.exp (a * X ω) :=
                    Finset.sum_filter_add_sum_filter_not _ _ _
  calc
    eventMass p (Finset.univ.filter (fun ω ↦ t ≤ X ω))
        = Real.exp (-a * t) *
            (Real.exp (a * t) * eventMass p (Finset.univ.filter (fun ω ↦ t ≤ X ω))) := by
            rw [← mul_assoc, ← Real.exp_add]
            ring_nf
            simp
    _ ≤ Real.exp (-a * t) * expectation p (fun ω ↦ Real.exp (a * X ω)) := by
          gcongr

/-- A parameterized finite-space Freedman exponential inequality.

The assumptions `hmom.mean` and `hmom.variance` are respectively the
conditional supermartingale-difference and predictable conditional
second-moment bounds, in finite integrated form. -/
theorem freedman_exp
    {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hp_one : ∑ ω, p ω = 1)
    {info : ℕ → Ω → ι} (hfil : IsFiltration info)
    {d : ℕ → Ω → ℝ} (hadapted : ∀ k, KnownAt info (k + 1) (d k))
    {v : ℕ → ℝ} (hmom : ConditionalMomentBounds p info d v)
    {R a t V : ℝ} (ha : 0 ≤ a) (haR : a * R ≤ 1)
    (hR : ∀ k ω, |d k ω| ≤ R) {n : ℕ}
    (hV : ∑ k ∈ Finset.range n, v k ≤ V) :
    eventMass p (Finset.univ.filter (fun ω ↦ t ≤ partialSum d n ω)) ≤
      Real.exp (-a * t + a ^ 2 * V) := by
  have hmgf := expectation_exp_partialSum_le hp hp_one hmom hadapted hfil ha haR hR n
  calc
    eventMass p (Finset.univ.filter (fun ω ↦ t ≤ partialSum d n ω))
        ≤ Real.exp (-a * t) *
            expectation p (fun ω ↦ Real.exp (a * partialSum d n ω)) :=
          eventMass_le_exp_mul_expectation hp (partialSum d n) ha
    _ ≤ Real.exp (-a * t) *
          Real.exp (a ^ 2 * ∑ k ∈ Finset.range n, v k) := by gcongr
    _ ≤ Real.exp (-a * t) * Real.exp (a ^ 2 * V) := by
          gcongr
    _ = Real.exp (-a * t + a ^ 2 * V) := (Real.exp_add _ _).symm

/-- A denominator-form finite-time Freedman inequality.  This is the form
normally consumed by the random-greedy argument. -/
theorem freedman
    {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hp_one : ∑ ω, p ω = 1)
    {info : ℕ → Ω → ι} (hfil : IsFiltration info)
    {d : ℕ → Ω → ℝ} (hadapted : ∀ k, KnownAt info (k + 1) (d k))
    {v : ℕ → ℝ} (hmom : ConditionalMomentBounds p info d v)
    {R t V : ℝ} (hR0 : 0 ≤ R) (ht : 0 ≤ t) (hV0 : 0 ≤ V)
    (hden : 0 < V + R * t)
    (hR : ∀ k ω, |d k ω| ≤ R) {n : ℕ}
    (hV : ∑ k ∈ Finset.range n, v k ≤ V) :
    eventMass p (Finset.univ.filter (fun ω ↦ t ≤ partialSum d n ω)) ≤
      Real.exp (-(t ^ 2) / (4 * (V + R * t))) := by
  let a : ℝ := t / (2 * (V + R * t))
  have ha : 0 ≤ a := div_nonneg ht (mul_nonneg (by norm_num) hden.le)
  have haR : a * R ≤ 1 := by
    dsimp [a]
    rw [div_mul_eq_mul_div, div_le_one (mul_pos (by norm_num) hden)]
    nlinarith [mul_nonneg hR0 ht]
  have hbase := freedman_exp (t := t) hp hp_one hfil hadapted hmom ha haR hR hV
  calc
    eventMass p (Finset.univ.filter (fun ω ↦ t ≤ partialSum d n ω))
        ≤ Real.exp (-a * t + a ^ 2 * V) := hbase
    _ ≤ Real.exp (-(t ^ 2) / (4 * (V + R * t))) := by
      rw [Real.exp_le_exp]
      dsimp [a]
      have hscale : 0 < 4 * (V + R * t) ^ 2 :=
        mul_pos (by norm_num) (sq_pos_of_pos hden)
      apply le_of_mul_le_mul_left ?_ hscale
      field_simp [ne_of_gt hden]
      nlinarith [mul_nonneg hR0 ht, sq_nonneg t]

end FiniteSpace

end Erdos136.Freedman
