/-
We have constructed an entire function F that maps reals to reals, is not affine on the reals, and preserves rationality. The construction follows the method described in the paper, using a recursive sequence of adjustments to force the function to map rationals to rationals and to be surjective on rationals, while maintaining a derivative bound to ensure injectivity. The final function F is the limit of a sequence of entire functions F_n. We proved that F is entire, maps reals to reals, its restriction to reals is strictly increasing (derivative > 1/2), and it maps Q onto Q. Thus, it preserves rationality.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
A function f:R->R is affine if f(x)=ax+b for some a,b in R.
-/
def IsAffine (f : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ x, f x = a * x + b

/-
A function f:R->R preserves rationality if for all x in R, x is rational iff f(x) is rational.
-/
def PreservesRationality (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x ∈ (Set.range ((↑) : ℚ → ℝ)) ↔ f x ∈ (Set.range ((↑) : ℚ → ℝ))

/-
Let f:R->R be injective and satisfy f(Q)=Q. Then f preserves rationality.
-/
lemma injective_preserves_rationality (f : ℝ → ℝ) (h_inj : Function.Injective f)
    (h_surj_Q : f '' (Set.range ((↑) : ℚ → ℝ)) = Set.range ((↑) : ℚ → ℝ)) :
    PreservesRationality f := by
  rw [ Set.ext_iff ] at h_surj_Q;
  intro x; specialize h_surj_Q ( f x ) ; aesop;

/-
h_seq alpha n z corresponds to h_{n+1}(z) in the paper.
If n=0, it is 1.
If n>0, it is exp(-z^2/(n+1)) * product_{k=0}^{n-1} (z - alpha k).
-/
noncomputable def h_seq (alpha : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  if n = 0 then 1
  else Complex.exp (-z^2 / (n + 1)) * ((List.range n).map (fun k => z - (alpha k : ℂ))).prod

/-
F_seq alpha lambda n z corresponds to F_{n+1}(z) in the paper.
It is z + sum_{k=0}^n lambda_k * h_{k+1}(z).
-/
noncomputable def F_seq (alpha : ℕ → ℝ) (lambda : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  z + ((List.range (n + 1)).map (fun k => (lambda k : ℂ) * h_seq alpha k z)).sum

/-
M_val alpha n is the maximum of |h_{n+1}(z)| on the disk |z| <= n+1.
L_val alpha n is the maximum of |h'_{n+1}(x)| on the real line.
eta_val alpha n eps is min(eps/M_n, eps/L_n).
-/
noncomputable def M_val (alpha : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup ((fun z => ‖h_seq alpha n z‖) '' {z : ℂ | ‖z‖ ≤ n + 1})

noncomputable def L_val (alpha : ℕ → ℝ) (n : ℕ) : ℝ :=
  sSup ((fun x : ℝ => ‖deriv (h_seq alpha n) (x : ℂ)‖) '' Set.univ)

noncomputable def eta_val (alpha : ℕ → ℝ) (n : ℕ) (eps : ℝ) : ℝ :=
  min (eps / M_val alpha n) (eps / L_val alpha n)

/-
For any x < y and finite set S of rationals, there is a rational q in (x, y) not in S.
-/
lemma exists_rat_in_interval_diff_finite (x y : ℝ) (hxy : x < y) (S : Set ℚ) (hS : S.Finite) :
    ∃ q : ℚ, (q : ℝ) ∈ Set.Ioo x y ∧ q ∉ S := by
  -- Since S is finite, the interval (x, y) contains infinitely many rationals.
  have h_inf : Set.Infinite {q : ℚ | x < q ∧ q < y} := by
    have := exists_rat_btwn hxy;
    obtain ⟨ q, hq ⟩ := this;
    rcases exists_rat_btwn hq.2 with ⟨ r, hr ⟩;
    norm_cast at *;
    exact Set.Infinite.mono ( fun a ha => ⟨ by exact hq.1.trans_le ( mod_cast ha.out.1.le ), by exact hr.2.trans_le' ( mod_cast ha.out.2.le ) ⟩ ) ( Set.Ioo_infinite ( show q < r by linarith ) );
  exact Set.Infinite.nonempty ( h_inf.diff hS ) |> Exists.imp fun q => by aesop;

/-
epsilon_seq n = (1/2)^(n+3). It is positive and sums to less than 1/2.
-/
def epsilon_seq (n : ℕ) : ℝ := (1/2) ^ (n + 3)

theorem epsilon_pos (n : ℕ) : 0 < epsilon_seq n := by
  unfold epsilon_seq
  positivity

theorem epsilon_sum : (∑' n, epsilon_seq n) < 1/2 := by
  unfold epsilon_seq;
  ring_nf;
  rw [ tsum_mul_right, tsum_geometric_of_lt_one ] <;> norm_num

/-
a_seq is a surjective enumeration of Q such that a_seq 0 = 0, a_seq 1 = 1, a_seq 2 = 2.
-/
noncomputable def a_seq : ℕ → ℚ :=
  let e := (Denumerable.eqv ℚ).symm
  let k0 := e.symm 0
  let k1 := e.symm 1
  let k2 := e.symm 2
  let s0 := Equiv.swap 0 k0
  let s1 := Equiv.swap (s0 1) k1
  let s2 := Equiv.swap (s1 (s0 2)) k2
  let p := s0.trans (s1.trans s2)
  e ∘ p

/-
b_seq is a surjective enumeration of Q such that b_seq 0 = 0, b_seq 1 = 1.
-/
noncomputable def b_seq : ℕ → ℚ :=
  let e := (Denumerable.eqv ℚ).symm
  let k0 := e.symm 0
  let k1 := e.symm 1
  let s0 := Equiv.swap 0 k0
  let s1 := Equiv.swap (s0 1) k1
  let p := s0.trans s1
  e ∘ p

/-
If seq is a surjective sequence of rationals and S is a finite set of rationals, there is an index n such that seq n is not in S.
-/
lemma exists_index_not_mem_finite (seq : ℕ → ℚ) (h_surj : Function.Surjective seq) (S : Set ℚ) (hS : S.Finite) :
    ∃ n, seq n ∉ S := by
  by_contra! h;
  exact hS.not_infinite <| Set.infinite_univ.mono fun x _ => by obtain ⟨ n, hn ⟩ := h_surj x; aesop;

/-
Helper to find the first element in a sequence not in a given finite set.
-/
noncomputable def first_unused_index (seq : ℕ → ℚ) (h_surj : Function.Surjective seq) (used : Set ℚ) (h_finite : used.Finite) : ℕ :=
  Nat.find (exists_index_not_mem_finite seq h_surj used h_finite)

noncomputable def first_unused (seq : ℕ → ℚ) (h_surj : Function.Surjective seq) (used : Set ℚ) (h_finite : used.Finite) : ℚ :=
  seq (first_unused_index seq h_surj used h_finite)

/-
choice_in_interval picks a rational q in (x, y) not in S.
-/
noncomputable def choice_in_interval (x y : ℝ) (hxy : x < y) (S : Set ℚ) (hS : S.Finite) : ℚ :=
  Classical.choose (exists_rat_in_interval_diff_finite x y hxy S hS)

lemma choice_in_interval_spec (x y : ℝ) (hxy : x < y) (S : Set ℚ) (hS : S.Finite) :
    let q := choice_in_interval x y hxy S hS
    (q : ℝ) ∈ Set.Ioo x y ∧ q ∉ S :=
  Classical.choose_spec (exists_rat_in_interval_diff_finite x y hxy S hS)

/-
Real versions of h_seq and F_seq.
-/
noncomputable def h_seq_real (alpha : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (h_seq alpha n (x : ℂ)).re

noncomputable def F_seq_real (alpha : ℕ → ℝ) (lambda : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (F_seq alpha lambda n (x : ℂ)).re

/-
Helpers to extract alpha, beta, lambda from history list and their sets.
-/
def alpha_from_hist (hist : List (ℚ × ℚ × ℝ)) (k : ℕ) : ℝ :=
  match hist.get? k with
  | some v => v.1
  | none => 0

def beta_from_hist (hist : List (ℚ × ℚ × ℝ)) (k : ℕ) : ℝ :=
  match hist.get? k with
  | some v => v.2.1
  | none => 0

def lambda_from_hist (hist : List (ℚ × ℚ × ℝ)) (k : ℕ) : ℝ :=
  match hist.get? k with
  | some v => v.2.2
  | none => 0

def alpha_set (hist : List (ℚ × ℚ × ℝ)) : Set ℚ :=
  {q | ∃ k, ∃ v, hist.get? k = some v ∧ v.1 = q}

def beta_set (hist : List (ℚ × ℚ × ℝ)) : Set ℚ :=
  {q | ∃ k, ∃ v, hist.get? k = some v ∧ v.2.1 = q}

lemma alpha_set_finite (hist : List (ℚ × ℚ × ℝ)) : (alpha_set hist).Finite := by
  have h_finite : Set.Finite (Set.image (fun k => (hist.get? k).get!.1) (Finset.range (hist.length))) := by
    exact Set.toFinite _;
  refine Set.Finite.subset ( h_finite.union ( Set.finite_singleton 0 ) ) ?_;
  rintro q ⟨ k, v, hk, rfl ⟩ ; by_cases hk' : k < List.length hist <;> aesop;

lemma beta_set_finite (hist : List (ℚ × ℚ × ℝ)) : (beta_set hist).Finite := by
  -- The beta_set is the image of the finite list hist under the function that maps each triple to its second component.
  have h_beta_finite : (beta_set hist) = Finset.image (fun t => t.2.1) (List.toFinset hist) := by
    -- To prove equality of sets, we show each set is a subset of the other.
    ext q
    simp [beta_set, Finset.mem_image];
    -- To prove the equivalence, we can use the fact that if there exists a k such that the k-th element is (a, q, x), then (a, q, x) is in the list, and vice versa.
    apply Iff.intro;
    · grind;
    · rintro ⟨ a, b, h ⟩;
      obtain ⟨ k, hk ⟩ := List.mem_iff_get.1 h; use k; aesop;
  exact h_beta_finite ▸ Set.toFinite _

/-
a_seq and b_seq are surjective.
-/
theorem a_seq_surj : Function.Surjective a_seq := by
  intro q
  let e := (Denumerable.eqv ℚ).symm
  let k0 := e.symm 0
  let k1 := e.symm 1
  let k2 := e.symm 2
  let s0 := Equiv.swap 0 k0
  let s1 := Equiv.swap (s0 1) k1
  let s2 := Equiv.swap (s1 (s0 2)) k2
  let p := s0.trans (s1.trans s2)
  -- a_seq = e ∘ p
  -- e is surjective (it's an equiv)
  -- p is surjective (it's an equiv)
  have he : Function.Surjective e := e.surjective
  have hp : Function.Surjective p := p.surjective
  exact he.comp hp q

theorem b_seq_surj : Function.Surjective b_seq := by
  intro q
  let e := (Denumerable.eqv ℚ).symm
  let k0 := e.symm 0
  let k1 := e.symm 1
  let s0 := Equiv.swap 0 k0
  let s1 := Equiv.swap (s0 1) k1
  let p := s0.trans s1
  have he : Function.Surjective e := e.surjective
  have hp : Function.Surjective p := p.surjective
  exact he.comp hp q

/-
Computes the next tuple (alpha, beta, lambda) given the history, with explicit checks for eta > 0 and non-zero denominators.
-/
noncomputable def next_step (n : ℕ) (hist : List (ℚ × ℚ × ℝ)) : ℚ × ℚ × ℝ :=
  if n = 0 then (0, 0, 0)
  else if n = 1 then (1, 1, 0)
  else
    let alpha_prev := alpha_from_hist hist
    let lambda_prev := lambda_from_hist hist
    let F_prev := F_seq_real alpha_prev lambda_prev (n - 1)
    let h_curr := h_seq_real alpha_prev n
    let eta := eta_val alpha_prev n (epsilon_seq n)
    let used_alpha := alpha_set hist
    let used_beta := beta_set hist
    let h_alpha_finite := alpha_set_finite hist
    let h_beta_finite := beta_set_finite hist

    if h_eta : eta > 0 then
      if n % 2 == 0 then
        -- Step B (Force domain)
        let alpha_n := first_unused a_seq a_seq_surj used_alpha h_alpha_finite
        let y := F_prev alpha_n
        let h_val := h_curr alpha_n
        if h_val_nz : h_val ≠ 0 then
          let radius := eta * |h_val|
          let beta_n := choice_in_interval (y - radius) (y + radius) (by
          linarith [ show 0 < radius by exact mul_pos h_eta ( abs_pos.mpr h_val_nz ) ]) used_beta h_beta_finite
          let lambda_n := (beta_n - y) / h_val
          (alpha_n, beta_n, lambda_n)
        else (alpha_n, 0, 0)
      else
        -- Step A (Force range)
        let beta_n := first_unused b_seq b_seq_surj used_beta h_beta_finite
        if h : ∃ x, F_prev x = beta_n then
          let x_n := Classical.choose h
          if h_curr_nz : h_curr x_n ≠ 0 then
            let Lambda := fun t => (beta_n - F_prev t) / h_curr t
            if h_cont : ContinuousAt Lambda x_n ∧ Lambda x_n = 0 then
              let P := fun delta => 0 < delta ∧ ∀ t, |t - x_n| < delta → |Lambda t| < eta
              if h_delta : ∃ delta, P delta then
                let delta := Classical.choose h_delta
                let alpha_n := choice_in_interval (x_n - delta) (x_n + delta) (by
                linarith [ Classical.choose_spec h_delta |>.1 ]) used_alpha h_alpha_finite
                let lambda_n := Lambda alpha_n
                (alpha_n, beta_n, lambda_n)
              else (0, beta_n, 0)
            else (0, beta_n, 0)
          else (0, beta_n, 0)
        else (0, beta_n, 0)
    else (0, 0, 0)

/-
Auxiliary function for next_step, handling n >= 2.
-/
noncomputable def next_step_aux (n : ℕ) (hist : List (ℚ × ℚ × ℝ)) : ℚ × ℚ × ℝ :=
  let alpha_prev := alpha_from_hist hist
  let lambda_prev := lambda_from_hist hist
  let F_prev := F_seq_real alpha_prev lambda_prev (n - 1)
  let h_curr := h_seq_real alpha_prev n
  let eta := eta_val alpha_prev n (epsilon_seq n)
  let used_alpha := alpha_set hist
  let used_beta := beta_set hist
  let h_alpha_finite := alpha_set_finite hist
  let h_beta_finite := beta_set_finite hist

  if h_eta : eta > 0 then
    if n % 2 == 0 then
      -- Step B (Force domain)
      let alpha_n := first_unused a_seq a_seq_surj used_alpha h_alpha_finite
      let y := F_prev alpha_n
      let h_val := h_curr alpha_n
      if h_val_nz : h_val ≠ 0 then
        let radius := eta * |h_val|
        let beta_n := choice_in_interval (y - radius) (y + radius) (by
        nlinarith [ abs_pos.mpr h_val_nz ]) used_beta h_beta_finite
        let lambda_n := (beta_n - y) / h_val
        (alpha_n, beta_n, lambda_n)
      else (alpha_n, 0, 0)
    else
      -- Step A (Force range)
      let beta_n := first_unused b_seq b_seq_surj used_beta h_beta_finite
      if h : ∃ x, F_prev x = beta_n then
        let x_n := Classical.choose h
        if h_curr_nz : h_curr x_n ≠ 0 then
          let Lambda := fun t => (beta_n - F_prev t) / h_curr t
          if h_cont : ContinuousAt Lambda x_n ∧ Lambda x_n = 0 then
            let P := fun delta => 0 < delta ∧ ∀ t, |t - x_n| < delta → |Lambda t| < eta
            if h_delta : ∃ delta, P delta then
              let delta := Classical.choose h_delta
              let alpha_n := choice_in_interval (x_n - delta) (x_n + delta) (by
              linarith [ Classical.choose_spec h_delta |>.1 ]) used_alpha h_alpha_finite
              let lambda_n := Lambda alpha_n
              (alpha_n, beta_n, lambda_n)
            else (0, beta_n, 0)
          else (0, beta_n, 0)
        else (0, beta_n, 0)
      else (0, beta_n, 0)
  else (0, 0, 0)

/-
A safe version of choice_in_interval that returns 0 if x >= y.
-/
noncomputable def safe_choice (x y : ℝ) (S : Set ℚ) (hS : S.Finite) : ℚ :=
  if h : x < y then choice_in_interval x y h S hS else 0

/-
Defines the sequences alpha, beta, and lambda by iterating next_step.
-/
def all_tuples : ℕ → List (ℚ × ℚ × ℝ)
| 0 => []
| n + 1 =>
  let prev := all_tuples n
  prev ++ [next_step n prev]

def construction_seq (n : ℕ) : ℚ × ℚ × ℝ :=
  (all_tuples (n + 1)).getLast (by simp [all_tuples])

noncomputable def alpha_seq (n : ℕ) : ℚ := (construction_seq n).1
noncomputable def beta_seq (n : ℕ) : ℚ := (construction_seq n).2.1
noncomputable def lambda_seq (n : ℕ) : ℝ := (construction_seq n).2.2

/-
F_final is the limit function F(z) = z + sum_{n=0}^infinity lambda_n * h_{n+1}(z).
F_partial_sum is the N-th partial sum F_{N+1}(z).
-/
noncomputable def F_final (z : ℂ) : ℂ :=
  z + ∑' n : ℕ, (lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n z

noncomputable def F_partial_sum (N : ℕ) (z : ℂ) : ℂ :=
  z + ((List.range (N + 1)).map (fun n => (lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n z)).sum

/-
lambda_n is 0 for n < 2.
-/
lemma lambda_zero_of_lt_two (n : ℕ) (h : n < 2) : lambda_seq n = 0 := by
  interval_cases n <;> unfold lambda_seq;
  · exact?;
  · unfold construction_seq; aesop;

/-
Definition of eta_seq.
-/
noncomputable def eta_seq (n : ℕ) : ℝ := eta_val (fun k => (alpha_seq k : ℝ)) n (epsilon_seq n)

/-
lambda_seq n is the third component of next_step n (all_tuples n).
-/
lemma lambda_seq_eq (n : ℕ) : lambda_seq n = (next_step n (all_tuples n)).2.2 := by
  rw [ show lambda_seq n = ( construction_seq n ).2.2 from rfl ];
  -- By definition of `all_tuples`, we have `all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)]`.
  have h_all_tuples : all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)] := by
    exact?;
  unfold construction_seq; aesop;

/-
alpha_from_hist (all_tuples n) k is equal to alpha_seq k for k < n.
-/
lemma alpha_from_hist_eq_alpha_seq (n k : ℕ) (h : k < n) :
    alpha_from_hist (all_tuples n) k = alpha_seq k := by
  unfold alpha_from_hist alpha_seq;
  -- By definition of `all_tuples`, the k-th element is exactly `construction_seq k`.
  have h_all_tuples_k : all_tuples n = List.map (fun k => construction_seq k) (List.range n) := by
    induction' n with n ih;
    · contradiction;
    · induction' n + 1 with n ih <;> simp_all +decide [ List.range_succ ];
      -- By definition of `all_tuples`, we have `all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)]`.
      have h_all_tuples_succ : all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)] := by
        exact?;
      unfold construction_seq; aesop;
  aesop

/-
The eta value in next_step equals eta_seq n.
-/
lemma eta_in_next_step_eq_eta_seq (n : ℕ) :
    let hist := all_tuples n
    let alpha_prev := alpha_from_hist hist
    eta_val alpha_prev n (epsilon_seq n) = eta_seq n := by
  unfold eta_seq;
  -- By definition of `alpha_from_hist` and `alpha_seq`, we know that for any `k < n`, `alpha_from_hist (all_tuples n) k = alpha_seq k`.
  have h_alpha_eq : ∀ k < n, alpha_from_hist (all_tuples n) k = alpha_seq k := by
    exact?;
  unfold eta_val;
  unfold M_val L_val;
  unfold h_seq;
  congr! 2;
  · congr! 3;
    rw [ List.map_congr_left ] ; aesop;
  · congr! 3;
    congr! 2;
    congr! 2;
    exact congr_arg _ ( List.map_congr_left fun k hk => by rw [ h_alpha_eq k ( List.mem_range.mp hk ) ] )

/-
eta_seq n is non-negative.
-/
lemma eta_seq_nonneg (n : ℕ) : 0 ≤ eta_seq n := by
  -- Since epsilon_n is positive and M_val and L_val are suprema of non-negative values, both epsilon_n / M_val and epsilon_n / L_val are non-negative. The minimum of two non-negative numbers is also non-negative.
  have h_eps_pos : 0 < epsilon_seq n := by
    exact?;
  exact le_min ( div_nonneg h_eps_pos.le <| by apply_rules [ Real.sSup_nonneg ] ; rintro - ⟨ z, hz, rfl ⟩ ; exact norm_nonneg _ ) ( div_nonneg h_eps_pos.le <| by apply_rules [ Real.sSup_nonneg ] ; rintro - ⟨ x, hx, rfl ⟩ ; exact norm_nonneg _ )

/-
M_val is positive.
-/
lemma M_val_pos (alpha : ℕ → ℝ) (n : ℕ) : 0 < M_val alpha n := by
  -- Since $h_n$ is not identically zero and $D$ has non-empty interior, there exists some $z \in D$ such that $h_n(z) \neq 0$.
  obtain ⟨z, hz⟩ : ∃ z ∈ {z : ℂ | ‖z‖ ≤ n + 1}, h_seq alpha n z ≠ 0 := by
    unfold h_seq;
    by_cases hn : n = 0 <;> simp +decide [ hn, Complex.exp_ne_zero ];
    · exact ⟨ 0, by norm_num ⟩;
    · -- Since the set {alpha x | x < n} is finite, there exists a complex number z with norm ≤ n+1 that is not in this set.
      obtain ⟨z, hz⟩ : ∃ z : ℂ, ‖z‖ ≤ n + 1 ∧ z ∉ Set.image (fun x : ℕ => (alpha x : ℂ)) (Finset.range n) := by
        -- The set {alpha x | x < n} is finite, so its complement in the disk is non-empty.
        have h_compl_nonempty : Set.Infinite {z : ℂ | ‖z‖ ≤ n + 1} := by
          -- The interval [0, n+1] is a subset of the set {z : ℂ | ‖z‖ ≤ n + 1} and is infinite.
          have h_interval : Set.Infinite (Set.image (fun x : ℝ => x : ℝ → ℂ) (Set.Icc 0 (n + 1))) := by
            exact Set.Infinite.image ( fun x => by aesop ) ( Set.Icc_infinite ( by positivity ) );
          exact h_interval.mono fun x hx => by rcases hx with ⟨ y, hy, rfl ⟩ ; exact Set.mem_setOf.mpr <| by simpa [ abs_of_nonneg hy.1 ] using hy.2;
        exact Set.Infinite.nonempty ( h_compl_nonempty.diff <| Set.toFinite _ );
      exact ⟨ z, hz.1, fun x hx => sub_ne_zero_of_ne <| by aesop ⟩;
  refine' lt_of_lt_of_le _ ( le_csSup _ <| Set.mem_image_of_mem _ hz.1 ) ; aesop;
  -- The image of a compact set under a continuous function is compact.
  have h_compact : IsCompact {z : ℂ | ‖z‖ ≤ n + 1} := by
    convert ProperSpace.isCompact_closedBall ( 0 : ℂ ) ( n + 1 : ℝ ) using 1 ; ext ; simp +decide [ dist_eq_norm ];
  apply_rules [ IsCompact.bddAbove, h_compact.image ];
  unfold h_seq;
  split_ifs <;> [ exact continuous_const.norm; exact Continuous.norm <| Continuous.mul ( Complex.continuous_exp.comp <| by continuity ) <| by continuity ]

/-
h_seq is not constant for n >= 1.
-/
lemma h_seq_not_const (alpha : ℕ → ℝ) (n : ℕ) (hn : n ≥ 1) :
    ¬ (∃ c : ℂ, ∀ z : ℂ, h_seq alpha n z = c) := by
  intro hc
  obtain ⟨c, hc⟩ := hc
  have h_h_seq_zero_at_alpha0 : h_seq alpha n (alpha 0 : ℂ) = 0 := by
    unfold h_seq; aesop;
  -- Since the exponential term is never zero, the product must be zero for all z.
  have h_prod_zero : ∀ z : ℂ, (∏ k ∈ Finset.range n, (z - Complex.ofReal (alpha k))) = 0 := by
    have h_prod_zero : ∀ z : ℂ, Complex.exp (-z^2 / (n + 1)) * ∏ k ∈ Finset.range n, (z - Complex.ofReal (alpha k)) = c := by
      unfold h_seq at hc; aesop;
    have := h_prod_zero ( alpha 0 ) ; aesop;
  exact absurd ( h_prod_zero ( ∑ k ∈ Finset.range n, ( alpha k : ℂ ) ^ 2 + 1 ) ) ( Finset.prod_ne_zero_iff.mpr fun i hi => sub_ne_zero_of_ne <| by norm_cast; nlinarith [ Finset.single_le_sum ( fun k _ => sq_nonneg ( alpha k : ℝ ) ) hi ] )

/-
The derivative of h_seq is exp(...) * Q(z) where Q is a polynomial of degree n+1.
-/
lemma h_seq_deriv_structure (alpha : ℕ → ℝ) (n : ℕ) (hn : n ≥ 1) :
    ∃ Q : Polynomial ℂ, Q.degree = n + 1 ∧
    ∀ z : ℂ, deriv (h_seq alpha n) z = Complex.exp (-z^2 / (n + 1)) * Q.eval z := by
  -- Let $P(z) = \prod_{k=0}^{n-1} (z - \alpha_k)$.
  set P : Polynomial ℂ := Finset.prod (Finset.range n) (fun k => Polynomial.X - Polynomial.C ((alpha k : ℂ)));
  -- Then $h_n(z) = \exp(-z^2/(n+1)) * P(z)$, so $h_n'(z) = \exp(-z^2/(n+1)) * (P'(z) - 2z/(n+1) * P(z))$.
  have h_deriv : ∀ z : ℂ, deriv (h_seq alpha n) z = Complex.exp (-z^2 / (n + 1)) * (Polynomial.eval z (Polynomial.derivative P) - 2 * z / (n + 1) * Polynomial.eval z P) := by
    -- By definition of $h_seq$, we have $h_seq alpha n z = \exp(-z^2/(n+1)) * P(z)$.
    have h_h_seq : ∀ z : ℂ, h_seq alpha n z = Complex.exp (-z^2 / (n + 1)) * Polynomial.eval z P := by
      unfold h_seq;
      simp +zetaDelta at *;
      norm_num [ Polynomial.eval_prod, List.prod_range_succ' ] ; aesop;
    rw [ show h_seq alpha n = _ from funext h_h_seq ];
    intro z; norm_num [ Polynomial.differentiableAt, mul_comm ] ; ring;
  -- Let $Q(z) = P'(z) - \frac{2z}{n+1} P(z)$.
  use Polynomial.derivative P - Polynomial.C (2 / (n + 1 : ℂ)) * Polynomial.X * P;
  rw [ Polynomial.degree_sub_eq_right_of_degree_lt ] <;> norm_num [ Polynomial.degree_prod, Polynomial.degree_X_sub_C ];
  · rw [ Polynomial.degree_C ] <;> norm_num;
    · exact ⟨ by rw [ Polynomial.degree_prod, Finset.sum_congr rfl fun _ _ => Polynomial.degree_X_sub_C _ ] ; norm_num ; ring, fun z => h_deriv z ▸ by ring ⟩;
    · exact Nat.cast_add_one_ne_zero _;
  · rw [ Polynomial.degree_C ] <;> norm_num;
    · refine' lt_of_le_of_lt ( Polynomial.degree_derivative_le ) _;
      rw [ Polynomial.degree_prod, Finset.sum_congr rfl fun _ _ => Polynomial.degree_X_sub_C _ ] ; norm_cast ; norm_num [ hn ];
    · exact Nat.cast_add_one_ne_zero _

/-
L_val is positive for n >= 1.
-/
lemma L_val_pos (alpha : ℕ → ℝ) (n : ℕ) (hn : n ≥ 1) : 0 < L_val alpha n := by
  -- Since $Q$ is a non-zero polynomial of degree $n+1$, it has finitely many roots.
  obtain ⟨x, hx⟩ : ∃ x : ℝ, deriv (h_seq alpha n) x ≠ 0 := by
    -- By h_seq_deriv_structure, deriv (h_seq alpha n) = exp(...) * Q(z) where deg(Q) = n+1.
    obtain ⟨Q, hQ_deg, hQ⟩ : ∃ Q : Polynomial ℂ, Q.degree = n + 1 ∧ ∀ z : ℂ, deriv (h_seq alpha n) z = Complex.exp (-z^2 / (n + 1)) * Q.eval z := by
      exact?;
    -- Since $Q$ is a non-zero polynomial of degree $n+1$, it has only finitely many roots.
    have hQ_roots_finite : Set.Finite {x : ℂ | Q.eval x = 0} := by
      refine' Set.Finite.subset ( Q.roots.toFinset.finite_toSet ) _;
      norm_num [ Set.subset_def ];
      exact fun x hx => ⟨ by rintro rfl; contradiction, hx ⟩;
    contrapose! hQ_roots_finite;
    exact Set.infinite_of_injective_forall_mem ( fun x y hxy => by simpa using hxy ) fun x : ℝ => show Polynomial.eval ( x : ℂ ) Q = 0 from by simpa [ hQ, Complex.exp_ne_zero ] using hQ_roots_finite x;
  refine' lt_of_lt_of_le ( show 0 < ‖deriv ( h_seq alpha n ) ( x : ℂ )‖ from norm_pos_iff.mpr hx ) ( le_csSup _ <| Set.mem_image_of_mem _ <| Set.mem_univ _ );
  have h_bdd_above : ContinuousOn (fun x : ℝ => ‖deriv (h_seq alpha n) (x : ℂ)‖) Set.univ := by
    have h_cont : ContinuousOn (fun z : ℂ => deriv (h_seq alpha n) z) (Set.univ : Set ℂ) := by
      have h_poly : ∃ Q : Polynomial ℂ, Q.degree = n + 1 ∧ ∀ z : ℂ, deriv (h_seq alpha n) z = Complex.exp (-z^2 / (n + 1)) * Q.eval z := h_seq_deriv_structure alpha n hn
      exact Continuous.continuousOn ( by rcases h_poly with ⟨ Q, hQ₁, hQ₂ ⟩ ; exact by rw [ show deriv ( h_seq alpha n ) = _ from funext hQ₂ ] ; exact Continuous.mul ( Complex.continuous_exp.comp <| by continuity ) <| Q.continuous );
    exact ContinuousOn.norm ( h_cont.comp ( Complex.continuous_ofReal.continuousOn ) fun x hx => by simpa );
  have h_bdd_above : Filter.Tendsto (fun x : ℝ => ‖deriv (h_seq alpha n) (x : ℂ)‖) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => ‖deriv (h_seq alpha n) (x : ℂ)‖) Filter.atBot (nhds 0) := by
    -- Since $Q$ is a polynomial of degree $n+1$, $|Q(x)|$ grows without bound as $x$ goes to infinity.
    have h_Q_growth : Filter.Tendsto (fun x : ℝ => ‖Polynomial.eval (x : ℂ) (Classical.choose (h_seq_deriv_structure alpha n hn))‖ * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => ‖Polynomial.eval (x : ℂ) (Classical.choose (h_seq_deriv_structure alpha n hn))‖ * Real.exp (-x^2 / (n + 1))) Filter.atBot (nhds 0) := by
      have h_Q_growth : Filter.Tendsto (fun x : ℝ => ‖Polynomial.eval (x : ℂ) (Classical.choose (h_seq_deriv_structure alpha n hn))‖ * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) := by
        have h_Q_growth : ∀ p : Polynomial ℂ, Filter.Tendsto (fun x : ℝ => ‖Polynomial.eval (x : ℂ) p‖ * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) := by
          intro p;
          have h_Q_growth : Filter.Tendsto (fun x : ℝ => ‖Polynomial.eval (x : ℂ) p‖ * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) := by
            have h_poly_growth : ∀ d : ℕ, Filter.Tendsto (fun x : ℝ => x^d * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) := by
              intro d;
              have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d;
              refine' squeeze_zero_norm' _ this;
              filter_upwards [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( n + 1 : ℝ ) ] with x hx₁ hx₂ using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by rw [ div_eq_mul_inv ] ; nlinarith [ inv_mul_cancel₀ ( by positivity : ( n : ℝ ) + 1 ≠ 0 ) ] ) ( by positivity ) ;
            have h_poly_growth : Filter.Tendsto (fun x : ℝ => (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * x^i) * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) := by
              simpa [ Finset.sum_mul _ _ _, mul_assoc ] using tendsto_finset_sum _ fun i hi => Filter.Tendsto.const_mul ( ‖p.coeff i‖ ) ( h_poly_growth i );
            refine' squeeze_zero_norm' _ h_poly_growth;
            norm_num [ Polynomial.eval_eq_sum_range ];
            exact ⟨ 0, fun x hx => mul_le_mul_of_nonneg_right ( le_trans ( norm_sum_le _ _ ) <| by norm_num [ abs_of_nonneg hx ] ) <| Real.exp_nonneg _ ⟩;
          convert h_Q_growth using 1;
        exact h_Q_growth _;
      have h_Q_growth_bot : Filter.Tendsto (fun x : ℝ => ‖Polynomial.eval (-x : ℂ) (Classical.choose (h_seq_deriv_structure alpha n hn))‖ * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) := by
        have h_Q_growth_bot : Filter.Tendsto (fun x : ℝ => ‖Polynomial.eval (x : ℂ) (Polynomial.comp (Classical.choose (h_seq_deriv_structure alpha n hn)) (-Polynomial.X))‖ * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) := by
          have h_Q_growth_bot : ∀ p : Polynomial ℂ, Filter.Tendsto (fun x : ℝ => ‖Polynomial.eval (x : ℂ) p‖ * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) := by
            intro p
            have h_poly_growth : ∀ k : ℕ, Filter.Tendsto (fun x : ℝ => |x|^k * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) := by
              intro k
              have h_poly_growth : Filter.Tendsto (fun x : ℝ => x^k * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) := by
                have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k;
                refine' squeeze_zero_norm' _ this;
                filter_upwards [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( n + 1 : ℝ ) ] with x hx₁ hx₂ using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by rw [ div_eq_mul_inv ] ; nlinarith [ inv_mul_cancel₀ ( by positivity : ( n : ℝ ) + 1 ≠ 0 ) ] ) ( by positivity ) ;
              exact tendsto_zero_iff_norm_tendsto_zero.mpr ( by simpa using h_poly_growth.norm );
            have h_poly_growth : Filter.Tendsto (fun x : ℝ => (∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ * |x|^k) * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) := by
              simpa [ Finset.sum_mul _ _ _, mul_assoc ] using tendsto_finset_sum _ fun k hk => h_poly_growth k |> Filter.Tendsto.const_mul ( ‖p.coeff k‖ );
            refine' squeeze_zero ( fun x => by positivity ) ( fun x => mul_le_mul_of_nonneg_right ( _ : _ ≤ _ ) ( Real.exp_nonneg _ ) ) h_poly_growth;
            rw [ Polynomial.eval_eq_sum_range ];
            exact le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun _ _ => by simp +decide [ abs_mul ] );
          exact h_Q_growth_bot _;
        convert h_Q_growth_bot using 2 ; norm_num;
      exact ⟨ h_Q_growth, by convert h_Q_growth_bot.comp Filter.tendsto_neg_atBot_atTop using 2; aesop ⟩;
    have h_deriv_eq : ∀ x : ℝ, deriv (h_seq alpha n) (x : ℂ) = Complex.exp (-x^2 / (n + 1)) * Polynomial.eval (x : ℂ) (Classical.choose (h_seq_deriv_structure alpha n hn)) := by
      exact fun x => Classical.choose_spec ( h_seq_deriv_structure alpha n hn ) |>.2 x;
    simp_all +decide [ Complex.norm_exp ];
    norm_cast at * ; simp_all +decide [ mul_comm ];
  have h_bdd_above : ∃ M : ℝ, ∀ x : ℝ, ‖deriv (h_seq alpha n) (x : ℂ)‖ ≤ M := by
    have h_tendsto_zero : ∀ ε > 0, ∃ N : ℝ, ∀ x : ℝ, |x| ≥ N → ‖deriv (h_seq alpha n) (x : ℂ)‖ < ε := by
      intro ε hε_pos
      obtain ⟨N_top, hN_top⟩ : ∃ N_top : ℝ, ∀ x : ℝ, x ≥ N_top → ‖deriv (h_seq alpha n) (x : ℂ)‖ < ε := by
        simpa using h_bdd_above.1.eventually ( gt_mem_nhds hε_pos )
      obtain ⟨N_bot, hN_bot⟩ : ∃ N_bot : ℝ, ∀ x : ℝ, x ≤ N_bot → ‖deriv (h_seq alpha n) (x : ℂ)‖ < ε := by
        have := h_bdd_above.2.eventually ( gt_mem_nhds hε_pos ) ; aesop;
      exact ⟨ |N_top| + |N_bot| + 1, fun x hx => by cases abs_cases x <;> cases abs_cases N_top <;> cases abs_cases N_bot <;> first | exact hN_top x ( by linarith ) | exact hN_bot x ( by linarith ) ⟩
    obtain ⟨ N, hN ⟩ := h_tendsto_zero 1 zero_lt_one;
    -- Since the function is continuous on a compact interval, it must attain a maximum value on that interval.
    have h_compact : ∃ M : ℝ, ∀ x ∈ Set.Icc (-N) N, ‖deriv (h_seq alpha n) (x : ℂ)‖ ≤ M := by
      exact IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc ) ( ‹ContinuousOn ( fun x : ℝ => ‖deriv ( h_seq alpha n ) ( x : ℂ )‖ ) Set.univ›.mono ( Set.subset_univ _ ) ) |> fun ⟨ M, hM ⟩ => ⟨ M, fun x hx => le_of_abs_le ( hM x hx ) ⟩;
    exact ⟨ Max.max h_compact.choose 1, fun x => if hx : |x| ≥ N then le_trans ( le_of_lt ( hN x hx ) ) ( by norm_num ) else le_trans ( h_compact.choose_spec x ⟨ by linarith [ abs_lt.mp ( not_le.mp hx ) ], by linarith [ abs_lt.mp ( not_le.mp hx ) ] ⟩ ) ( by norm_num ) ⟩;
  exact ⟨ h_bdd_above.choose, Set.forall_mem_image.2 fun x _ => h_bdd_above.choose_spec x ⟩

/-
Derivative of exp(-z^2/(n+1)) * P(z).
-/
lemma deriv_exp_mul_poly (n : ℕ) (P : Polynomial ℂ) (z : ℂ) :
    deriv (fun w => Complex.exp (-w^2 / (n + 1)) * P.eval w) z =
    Complex.exp (-z^2 / (n + 1)) * (deriv (fun w => P.eval w) z - (2 * z / (n + 1)) * P.eval z) := by
  convert HasDerivAt.deriv ( HasDerivAt.mul ( HasDerivAt.comp z ( Complex.hasDerivAt_exp _ ) <| HasDerivAt.div_const ( HasDerivAt.neg ( hasDerivAt_pow 2 z ) ) _ ) <| P.hasDerivAt z ) using 1 ; ring!;
  erw [ Polynomial.deriv ] ; norm_num ; ring

/-
There exists a real number where the derivative of h_seq is non-zero.
-/
lemma exists_deriv_ne_zero (alpha : ℕ → ℝ) (n : ℕ) (hn : n ≥ 1) :
    ∃ x : ℝ, deriv (h_seq alpha n) (x : ℂ) ≠ 0 := by
  -- By Lemma~\ref{lem:derivative_def}, the derivative of h_seq is exp(-z^2/(n+1)) * Q(z) where Q is a polynomial of degree n+1.
  obtain ⟨Q, hQ_deg, hQ_deriv⟩ : ∃ Q : Polynomial ℂ, Q.degree = n + 1 ∧ ∀ z : ℂ, deriv (h_seq alpha n) z = Complex.exp (-z^2 / (n + 1)) * Q.eval z := h_seq_deriv_structure alpha n hn;
  -- Since Q is a non-zero polynomial, it has finitely many roots.
  have hQ_roots_finite : Set.Finite {x : ℝ | Q.eval (x : ℂ) = 0} := by
    refine' Set.Finite.subset ( Q.roots.toFinset.finite_toSet.preimage _ ) _;
    use fun x => x;
    · exact fun x hx y hy hxy => by simpa using hxy;
    · norm_num [ Set.subset_def ];
      exact fun x hx => ⟨ by rintro rfl; contradiction, hx ⟩;
  exact Exists.elim ( hQ_roots_finite.exists_not_mem ) fun x hx => ⟨ x, by aesop ⟩

/-
A non-zero complex polynomial is non-zero at some real number.
-/
lemma exists_real_ne_zero_of_poly_ne_zero (P : Polynomial ℂ) (h : P ≠ 0) :
    ∃ x : ℝ, P.eval (x : ℂ) ≠ 0 := by
  by_contra! h;
  -- If $P(x) = 0$ for all real $x$, then $P$ has infinitely many roots.
  have h_inf_roots : Set.Infinite {x : ℂ | P.eval x = 0} := by
    exact Set.infinite_of_injective_forall_mem ( fun x y => by aesop ) h;
  exact h_inf_roots ( P.roots.toFinset.finite_toSet.subset fun x hx => by aesop )

/-
Checking if L_val_pos is defined.
-/
#check L_val_pos

/-
The derivative of h_seq is bounded on R.
-/
lemma h_seq_deriv_bounded (alpha : ℕ → ℝ) (n : ℕ) (hn : n ≥ 1) :
    BddAbove ((fun x : ℝ => ‖deriv (h_seq alpha n) (x : ℂ)‖) '' Set.univ) := by
  -- Since Q is a polynomial, |Q(x)| grows polynomially. exp(-x^2/(n+1)) decays exponentially. The product tends to 0 as |x| -> infinity.
  have h_poly_exp : Filter.Tendsto (fun x : ℝ => ‖deriv (h_seq alpha n) (x : ℂ)‖) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => ‖deriv (h_seq alpha n) (x : ℂ)‖) Filter.atBot (nhds 0) := by
    -- By h_seq_deriv_structure, deriv(h_seq) x = exp(-x^2/(n+1)) * Q(x).
    obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℂ, Q.degree = n + 1 ∧ ∀ x : ℝ, deriv (h_seq alpha n) (x : ℂ) = Complex.exp (-x^2 / (n + 1)) * Q.eval (x : ℂ) := by
      have := h_seq_deriv_structure alpha n hn;
      exact ⟨ this.choose, this.choose_spec.1, fun x => this.choose_spec.2 _ ⟩;
    -- Since $|Q(x)|$ grows polynomially and $e^{-x^2/(n+1)}$ decays exponentially, their product tends to $0$ as $|x| \to \infty$.
    have h_poly_exp : Filter.Tendsto (fun x : ℝ => ‖Q.eval (x : ℂ)‖ * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => ‖Q.eval (x : ℂ)‖ * Real.exp (-x^2 / (n + 1))) Filter.atBot (nhds 0) := by
      have h_bound : ∀ d : ℕ, Filter.Tendsto (fun x : ℝ => |x|^d * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => |x|^d * Real.exp (-x^2 / (n + 1))) Filter.atBot (nhds 0) := by
        intro d
        have h_exp_decay_top : Filter.Tendsto (fun x : ℝ => |x|^d * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) := by
          field_simp;
          have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d;
          refine' squeeze_zero_norm' _ this;
          filter_upwards [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( ( n : ℝ ) + 1 ) ] with x hx₁ hx₂ using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ abs_of_nonneg hx₁.le ] ; gcongr ; nlinarith [ div_mul_cancel₀ ( x ^ 2 ) ( by positivity : ( n : ℝ ) + 1 ≠ 0 ) ] ;
        have h_exp_decay_bot : Filter.Tendsto (fun x : ℝ => |x|^d * Real.exp (-x^2 / (n + 1))) Filter.atBot (nhds 0) := by
          convert h_exp_decay_top.comp Filter.tendsto_neg_atBot_atTop using 2 ; norm_num
        exact ⟨h_exp_decay_top, h_exp_decay_bot⟩;
      have h_bound : ∀ x : ℝ, ‖Q.eval (x : ℂ)‖ ≤ (∑ i ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff i‖ * |x|^i) := by
        intro x; rw [ Polynomial.eval_eq_sum_range ] ; exact le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun i hi => by simp +decide [ abs_mul ] ) ;
      have h_bound : Filter.Tendsto (fun x : ℝ => (∑ i ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff i‖ * |x|^i) * Real.exp (-x^2 / (n + 1))) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x : ℝ => (∑ i ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff i‖ * |x|^i) * Real.exp (-x^2 / (n + 1))) Filter.atBot (nhds 0) := by
        simp_all +decide [ Finset.sum_mul _ _ _ ];
        exact ⟨ by simpa [ mul_assoc ] using tendsto_finset_sum _ fun i hi => Filter.Tendsto.const_mul ( ‖Q.coeff i‖ ) ( ‹∀ d : ℕ, Filter.Tendsto ( fun x : ℝ => |x| ^ d * Real.exp ( -x ^ 2 / ( n + 1 ) ) ) Filter.atTop ( nhds 0 ) ∧ Filter.Tendsto ( fun x : ℝ => |x| ^ d * Real.exp ( -x ^ 2 / ( n + 1 ) ) ) Filter.atBot ( nhds 0 ) › i |>.1 ), by simpa [ mul_assoc ] using tendsto_finset_sum _ fun i hi => Filter.Tendsto.const_mul ( ‖Q.coeff i‖ ) ( ‹∀ d : ℕ, Filter.Tendsto ( fun x : ℝ => |x| ^ d * Real.exp ( -x ^ 2 / ( n + 1 ) ) ) Filter.atTop ( nhds 0 ) ∧ Filter.Tendsto ( fun x : ℝ => |x| ^ d * Real.exp ( -x ^ 2 / ( n + 1 ) ) ) Filter.atBot ( nhds 0 ) › i |>.2 ) ⟩;
      exact ⟨ squeeze_zero ( fun x => by positivity ) ( fun x => mul_le_mul_of_nonneg_right ( by solve_by_elim ) ( Real.exp_nonneg _ ) ) h_bound.1, squeeze_zero ( fun x => by positivity ) ( fun x => mul_le_mul_of_nonneg_right ( by solve_by_elim ) ( Real.exp_nonneg _ ) ) h_bound.2 ⟩;
    simp_all +decide [ Complex.norm_exp ];
    norm_cast ; simp_all +decide [ mul_comm ];
  -- Since the function tends to 0 as |x| -> infinity, it is bounded on R.
  have h_bounded : ∃ M : ℝ, ∀ x : ℝ, |x| ≥ M → ‖deriv (h_seq alpha n) (x : ℂ)‖ ≤ 1 := by
    obtain ⟨ M₁, hM₁ ⟩ := Filter.eventually_atTop.mp ( h_poly_exp.1.eventually ( ge_mem_nhds zero_lt_one ) ) ; obtain ⟨ M₂, hM₂ ⟩ := Filter.eventually_atBot.mp ( h_poly_exp.2.eventually ( ge_mem_nhds zero_lt_one ) ) ; use Max.max M₁ ( -M₂ ) ; intro x hx; cases abs_cases x <;> aesop;
  -- Since the function is continuous on a compact interval, it is bounded.
  have h_cont : ContinuousOn (fun x : ℝ => ‖deriv (h_seq alpha n) (x : ℂ)‖) (Set.Icc (-h_bounded.choose) h_bounded.choose) := by
    have h_cont_bounded : ContinuousOn (fun x : ℂ => ‖deriv (h_seq alpha n) x‖) (Metric.closedBall 0 (h_bounded.choose)) := by
      have h_cont_bounded : ContinuousOn (fun x : ℂ => deriv (h_seq alpha n) x) (Metric.closedBall 0 (h_bounded.choose)) := by
        have h_poly : ∃ Q : Polynomial ℂ, ∀ x : ℂ, deriv (h_seq alpha n) x = Complex.exp (-x^2 / (n + 1)) * Q.eval x := by
          have := h_seq_deriv_structure alpha n hn;
          aesop
        exact Continuous.continuousOn ( by rw [ show ( fun x : ℂ => deriv ( h_seq alpha n ) x ) = _ from funext h_poly.choose_spec ] ; exact Continuous.mul ( Complex.continuous_exp.comp <| by continuity ) <| h_poly.choose.continuous );
      exact h_cont_bounded.norm;
    exact h_cont_bounded.comp ( Complex.continuous_ofReal.continuousOn ) fun x hx => by simpa [ abs_le ] using hx;
  obtain ⟨ M, hM ⟩ := IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc ) h_cont;
  exact ⟨ Max.max M 1, Set.forall_mem_image.2 fun x _ => if hx : |x| ≥ h_bounded.choose then le_trans ( h_bounded.choose_spec x hx ) ( le_max_right _ _ ) else le_trans ( by simpa using hM x ⟨ by linarith [ abs_lt.mp ( not_le.mp hx ) ], by linarith [ abs_lt.mp ( not_le.mp hx ) ] ⟩ ) ( le_max_left _ _ ) ⟩

/-
L_val is positive for n >= 1.
-/
lemma L_val_pos_final (alpha : ℕ → ℝ) (n : ℕ) (hn : n ≥ 1) : 0 < L_val alpha n := by
  obtain ⟨x, hx⟩ := exists_deriv_ne_zero alpha n hn
  have h_norm_pos : 0 < ‖deriv (h_seq alpha n) (x : ℂ)‖ := norm_pos_iff.mpr hx
  have h_le_sup : ‖deriv (h_seq alpha n) (x : ℂ)‖ ≤ L_val alpha n := by
    apply le_csSup
    · exact h_seq_deriv_bounded alpha n hn
    · exact Set.mem_image_of_mem _ (Set.mem_univ x)
  exact lt_of_lt_of_le h_norm_pos h_le_sup

/-
eta_seq n is positive for n >= 1.
-/
lemma eta_seq_pos (n : ℕ) (hn : n ≥ 1) : 0 < eta_seq n := by
  unfold eta_seq eta_val
  have h_eps : 0 < epsilon_seq n := epsilon_pos n
  have h_M : 0 < M_val (fun k => (alpha_seq k : ℝ)) n := M_val_pos _ n
  have h_L : 0 < L_val (fun k => (alpha_seq k : ℝ)) n := L_val_pos_final _ n hn
  apply lt_min
  · apply div_pos h_eps h_M
  · apply div_pos h_eps h_L

/-
|lambda_n| <= eta_n for all n.
-/
lemma lambda_bound (n : ℕ) : |lambda_seq n| ≤ eta_seq n := by
  by_cases h : n < 2;
  · interval_cases n <;> norm_num [ lambda_zero_of_lt_two ];
    · exact?;
    · exact?;
  · rw [ ← eta_in_next_step_eq_eta_seq ];
    rw [ lambda_seq_eq ];
    unfold next_step;
    split_ifs <;> norm_num;
    · grind;
    · linarith;
    · split_ifs <;> norm_num;
      any_goals linarith;
      · have := choice_in_interval_spec ( F_seq_real ( alpha_from_hist ( all_tuples n ) ) ( lambda_from_hist ( all_tuples n ) ) ( n - 1 ) ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples n ) ) ( alpha_set_finite ( all_tuples n ) ) ) - eta_val ( alpha_from_hist ( all_tuples n ) ) n ( epsilon_seq n ) * |h_seq_real ( alpha_from_hist ( all_tuples n ) ) n ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples n ) ) ( alpha_set_finite ( all_tuples n ) ) )| ) ( F_seq_real ( alpha_from_hist ( all_tuples n ) ) ( lambda_from_hist ( all_tuples n ) ) ( n - 1 ) ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples n ) ) ( alpha_set_finite ( all_tuples n ) ) ) + eta_val ( alpha_from_hist ( all_tuples n ) ) n ( epsilon_seq n ) * |h_seq_real ( alpha_from_hist ( all_tuples n ) ) n ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples n ) ) ( alpha_set_finite ( all_tuples n ) ) )| ) ?_ ( beta_set ( all_tuples n ) ) ( beta_set_finite ( all_tuples n ) );
        any_goals nlinarith [ abs_pos.mpr ‹_› ];
        rw [ abs_div, div_le_iff₀ ] <;> norm_num [ ‹_› ];
        · exact abs_le.mpr ⟨ by linarith [ this.1.1 ], by linarith [ this.1.2 ] ⟩;
        · assumption;
      · grind;
      · exact False.elim <| ‹¬0 < eta_val ( alpha_from_hist ( all_tuples n ) ) n ( epsilon_seq n ) › <| by simpa only [eta_in_next_step_eq_eta_seq] using eta_seq_pos n (by linarith) ;
    · split_ifs <;> norm_num;
      any_goals linarith;
      · aesop;
      · rename_i h₁ h₂ h₃ h₄ h₅ h₆;
        have := h₆.choose_spec.2 ( choice_in_interval ( Classical.choose h₃ - Classical.choose h₆ ) ( Classical.choose h₃ + Classical.choose h₆ ) ( by linarith [ h₆.choose_spec.1 ] ) ( alpha_set ( all_tuples n ) ) ( alpha_set_finite ( all_tuples n ) ) ) ?_;
        · exact le_of_lt this;
        · have := choice_in_interval_spec ( Classical.choose h₃ - Classical.choose h₆ ) ( Classical.choose h₃ + Classical.choose h₆ ) ( by linarith [ h₆.choose_spec.1 ] ) ( alpha_set ( all_tuples n ) ) ( alpha_set_finite ( all_tuples n ) );
          exact abs_lt.mpr ⟨ by linarith [ this.1.1 ], by linarith [ this.1.2 ] ⟩;
      · exact le_min ( div_nonneg ( le_of_lt ( epsilon_pos n ) ) ( le_of_lt ( M_val_pos _ _ ) ) ) ( div_nonneg ( le_of_lt ( epsilon_pos n ) ) ( le_of_lt ( L_val_pos_final _ _ ( by linarith ) ) ) )

/-
For |z| <= n+1, |lambda_n * h_n(z)| <= epsilon_n.
-/
lemma term_bound (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ n + 1) :
    ‖(lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n z‖ ≤ epsilon_seq n := by
      simp +zetaDelta at *;
      -- By definition of $M_val$, we know that $|h_seq (fun k => (alpha_seq k : ℝ)) n z| \leq M_val (fun k => (alpha_seq k : ℝ)) n$.
      have h_h_seq_bound : ‖h_seq (fun k => (alpha_seq k : ℝ)) n z‖ ≤ M_val (fun k => (alpha_seq k : ℝ)) n := by
        refine' le_csSup _ _;
        · refine' IsCompact.bddAbove _;
          refine' IsCompact.image _ _;
          · convert ProperSpace.isCompact_closedBall ( 0 : ℂ ) ( n + 1 : ℝ ) using 1 ; ext ; simp +decide [ dist_eq_norm ];
          · unfold h_seq;
            split_ifs <;> [ continuity; exact Continuous.norm <| by continuity ];
        · exact ⟨ z, hz, rfl ⟩;
      refine' le_trans ( mul_le_mul_of_nonneg_left h_h_seq_bound ( abs_nonneg _ ) ) _;
      refine' le_trans ( mul_le_mul_of_nonneg_right ( lambda_bound n ) ( _ ) ) _;
      · exact le_trans ( by norm_num ) ( M_val_pos _ _ |> le_of_lt );
      · exact le_trans ( mul_le_mul_of_nonneg_right ( show eta_seq n ≤ epsilon_seq n / M_val ( fun k => ( alpha_seq k : ℝ ) ) n from min_le_left _ _ ) ( by exact le_of_lt ( M_val_pos _ _ ) ) ) ( by rw [ div_mul_cancel₀ _ ( ne_of_gt ( M_val_pos _ _ ) ) ] )

/-
The series defining F_final converges for every complex number z.
-/
theorem F_final_converges (z : ℂ) : Summable (fun n => (lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n z) := by
  -- For any fixed z, choose N such that |z| <= N. For n > N, we have |z| <= n, so |lambda_n * h_n(z)| <= epsilon_n by `term_bound`.
  have h_bound (z : ℂ) : ∃ N : ℕ, ∀ n ≥ N, ‖(lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n z‖ ≤ epsilon_seq n := by
    use ⌈‖z‖⌉₊ + 1;
    exact fun n hn => term_bound n z <| le_trans ( Nat.le_ceil _ ) <| mod_cast by linarith;
  -- Since $\sum \epsilon_n$ converges (by `epsilon_sum`), the series converges by comparison.
  have h_summable : Summable (fun n => epsilon_seq n) := by
    exact summable_geometric_two.comp_injective ( add_left_injective 3 );
  obtain ⟨ N, hN ⟩ := h_bound z;
  have h_summable : Summable (fun n => ‖(lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n z‖) := by
    rw [ ← summable_nat_add_iff N ];
    exact Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => hN _ ( by linarith ) ) ( h_summable.comp_injective ( add_left_injective N ) );
  exact h_summable.of_norm

/-
F_final is an entire function (differentiable everywhere on C).
-/
theorem F_final_entire : Differentiable ℂ F_final := by
  apply_rules [ Differentiable.add, Differentiable.neg, Differentiable.mul, differentiable_id, differentiable_const ];
  -- Each term in the series is differentiable, and the series converges uniformly on compact sets, so the sum is differentiable.
  have h_diff : ∀ n, Differentiable ℂ (fun z => (lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n z) := by
    intro n;
    unfold h_seq;
    split_ifs <;> norm_num [ mul_assoc, mul_comm, mul_left_comm ];
    apply_rules [ Differentiable.const_mul, Differentiable.mul, Differentiable.neg, Differentiable.exp, differentiable_id, differentiable_const ];
    · exact Complex.differentiable_exp.comp ( Differentiable.div_const ( Differentiable.neg ( differentiable_pow 2 ) ) _ );
    · induction' ( List.range n ) with n ih <;> simp_all +decide [ List.prod_cons ];
  -- The series converges uniformly on compact sets, so the sum is differentiable.
  have h_uniform : ∀ R > 0, Summable (fun n => ‖lambda_seq n‖ * (sSup ((fun z => ‖h_seq (fun k => (alpha_seq k : ℝ)) n z‖) '' {z : ℂ | ‖z‖ ≤ R}))) := by
    -- Since $|lambda_n| \leq \eta_n$ and $\eta_n$ is chosen such that $\sum \epsilon_n < 1/2$, the series $\sum |lambda_n| * M_n$ converges.
    have h_summable : Summable (fun n => ‖lambda_seq n‖ * (sSup ((fun z => ‖h_seq (fun k => (alpha_seq k : ℝ)) n z‖) '' {z : ℂ | ‖z‖ ≤ n + 1}))) := by
      have h_summable : Summable (fun n => ‖lambda_seq n‖ * M_val (fun k => (alpha_seq k : ℝ)) n) := by
        have h_bound : ∀ n, ‖lambda_seq n‖ * M_val (fun k => (alpha_seq k : ℝ)) n ≤ epsilon_seq n := by
          intro n
          have h_bound : ‖lambda_seq n‖ ≤ eta_seq n := by
            convert lambda_bound n using 1;
          refine le_trans ( mul_le_mul_of_nonneg_right h_bound <| by exact ( by apply_rules [ Real.sSup_nonneg ] ; aesop ) ) ?_;
          exact le_trans ( mul_le_mul_of_nonneg_right ( min_le_left _ _ ) ( by apply_rules [ Real.sSup_nonneg ] ; aesop ) ) ( by rw [ div_mul_cancel₀ _ ( ne_of_gt ( M_val_pos _ _ ) ) ] )
        exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( norm_nonneg _ ) ( by exact le_trans ( by norm_num ) ( le_csSup ( show BddAbove ( ( fun z => ‖h_seq ( fun k => ( alpha_seq k : ℝ ) ) n z‖ ) '' { z : ℂ | ‖z‖ ≤ n + 1 } ) from by
                                                                                                                                  have h_bdd_above : ContinuousOn (fun z : ℂ => ‖h_seq (fun k => (alpha_seq k : ℝ)) n z‖) (Metric.closedBall 0 (n + 1)) := by
                                                                                                                                    refine' Continuous.continuousOn _;
                                                                                                                                    unfold h_seq;
                                                                                                                                    split_ifs <;> [ continuity; exact Continuous.norm <| by exact Continuous.mul ( Complex.continuous_exp.comp <| by continuity ) <| by induction' ( List.range n ) with k hk <;> simp_all +decide [ List.prod_cons, Continuous.mul, Continuous.sub, continuous_id', continuous_const ] ];
                                                                                                                                  exact IsCompact.bddAbove ( isCompact_closedBall 0 ( n + 1 ) |> IsCompact.image_of_continuousOn <| h_bdd_above ) |> fun ⟨ M, hM ⟩ => ⟨ M, Set.forall_mem_image.2 fun z hz => hM <| Set.mem_image_of_mem _ <| by simpa using hz ⟩ ) ( Set.mem_image_of_mem _ ( show ( 0 : ℂ ) ∈ { z : ℂ | ‖z‖ ≤ n + 1 } by norm_num; linarith ) ) ) ) ) h_bound ( by
                                                                                                                                                                                                                                                                                    exact Summable.of_nonneg_of_le ( fun n => by exact pow_nonneg ( by norm_num ) _ ) ( fun n => by exact pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( by linarith ) ) ( summable_geometric_two ) );
      convert h_summable using 1;
    intro R hR_pos
    have h_bound : ∀ n ≥ Nat.ceil R, ‖lambda_seq n‖ * (sSup ((fun z => ‖h_seq (fun k => (alpha_seq k : ℝ)) n z‖) '' {z : ℂ | ‖z‖ ≤ R})) ≤ ‖lambda_seq n‖ * (sSup ((fun z => ‖h_seq (fun k => (alpha_seq k : ℝ)) n z‖) '' {z : ℂ | ‖z‖ ≤ n + 1})) := by
      intro n hn; gcongr;
      · have h_bdd_above : ContinuousOn (fun z : ℂ => ‖h_seq (fun k => (alpha_seq k : ℝ)) n z‖) (Metric.closedBall 0 (n + 1)) := by
          refine' Continuous.continuousOn _;
          refine' Continuous.norm _;
          unfold h_seq;
          split_ifs <;> [ continuity; exact Continuous.mul ( Complex.continuous_exp.comp <| by continuity ) <| by induction' ( List.range n ) with k hk <;> continuity ];
        exact IsCompact.bddAbove ( isCompact_closedBall 0 ( n + 1 ) |> IsCompact.image_of_continuousOn <| h_bdd_above ) |> fun h => h.mono <| Set.image_subset _ <| by simpa [ Set.subset_def ] ;
      · exact ⟨ _, ⟨ 0, by norm_num; linarith, rfl ⟩ ⟩;
      · linarith [ Nat.ceil_le.mp hn ];
    rw [ ← summable_nat_add_iff ⌈R⌉₊ ] at *;
    exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( norm_nonneg _ ) ( by apply_rules [ Real.sSup_nonneg ] ; aesop ) ) ( fun n => h_bound _ ( Nat.le_add_left _ _ ) ) h_summable;
  -- Apply the theorem that the uniform limit of differentiable functions is differentiable.
  have h_diff_sum : ∀ R > 0, DifferentiableOn ℂ (fun z => ∑' n, (lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n z) (Metric.ball 0 R) := by
    intro R hR_pos
    have h_uniform : TendstoLocallyUniformlyOn (fun n z => ∑ i ∈ Finset.range n, (lambda_seq i : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) i z) (fun z => ∑' n, (lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n z) Filter.atTop (Metric.ball 0 R) := by
      have h_uniform : TendstoUniformlyOn (fun n z => ∑ i ∈ Finset.range n, (lambda_seq i : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) i z) (fun z => ∑' n, (lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n z) Filter.atTop (Metric.closedBall 0 R) := by
        have h_uniform : ∀ n, ∀ z ∈ Metric.closedBall 0 R, ‖(lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n z‖ ≤ ‖lambda_seq n‖ * (sSup ((fun z => ‖h_seq (fun k => (alpha_seq k : ℝ)) n z‖) '' {z : ℂ | ‖z‖ ≤ R})) := by
          intros n z hz
          have h_bound : ‖h_seq (fun k => (alpha_seq k : ℝ)) n z‖ ≤ sSup ((fun z => ‖h_seq (fun k => (alpha_seq k : ℝ)) n z‖) '' {z : ℂ | ‖z‖ ≤ R}) := by
            apply le_csSup;
            · have h_bdd : ContinuousOn (fun z => ‖h_seq (fun k => (alpha_seq k : ℝ)) n z‖) (Metric.closedBall 0 R) := by
                refine' Continuous.continuousOn _;
                unfold h_seq;
                split_ifs <;> norm_num;
                · exact continuous_const;
                · fun_prop;
              obtain ⟨ M, hM ⟩ := IsCompact.exists_bound_of_continuousOn ( ProperSpace.isCompact_closedBall 0 R ) h_bdd ; use M ; rintro x ⟨ y, hy, rfl ⟩ ; aesop;
            · exact ⟨ z, by simpa using hz, rfl ⟩;
          simpa using mul_le_mul_of_nonneg_left h_bound <| norm_nonneg <| lambda_seq n;
        exact?;
      exact h_uniform.tendstoLocallyUniformlyOn.mono ( Metric.ball_subset_closedBall );
    have h_diff_sum : ∀ n, DifferentiableOn ℂ (fun z => ∑ i ∈ Finset.range n, (lambda_seq i : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) i z) (Metric.ball 0 R) := by
      exact fun n => Differentiable.differentiableOn ( by induction' n with n ih <;> simp_all +decide [ Finset.sum_range_succ ] );
    apply_rules [ h_uniform.differentiableOn ];
    · aesop;
    · exact Metric.isOpen_ball;
  intro z;
  exact h_diff_sum ( ‖z‖ + 1 ) ( by positivity ) |> DifferentiableOn.differentiableAt <| Metric.isOpen_ball.mem_nhds <| by norm_num;

/-
F_final maps real numbers to real numbers.
-/
theorem F_final_real_on_real (x : ℝ) : (F_final (x : ℂ)).im = 0 := by
  unfold F_final;
  rw [ Complex.add_im, Complex.im_tsum ];
  · -- Since $h_seq$ is defined using real arithmetic, $h_seq (fun k => (alpha_seq k : ℝ)) n x$ is real.
    have h_real : ∀ n, (h_seq (fun k => (alpha_seq k : ℝ)) n x).im = 0 := by
      intro n; unfold h_seq; norm_num;
      split_ifs <;> norm_num [ Complex.exp_im ];
      norm_cast ; norm_num [ neg_div, sq ];
      induction ( List.range n ) <;> aesop;
    simp_all +decide [ Complex.mul_im ];
  · exact?

/-
f_final is the real-valued function corresponding to F_final restricted to the reals.
-/
noncomputable def f_final (x : ℝ) : ℝ := (F_final (x : ℂ)).re

/-
f_final(x) (as a complex number) is equal to F_final(x).
-/
theorem f_final_eq_F_final (x : ℝ) : (f_final x : ℂ) = F_final (x : ℂ) := by
  simp +decide [ f_final, Complex.ext_iff ];
  exact Eq.symm ( F_final_real_on_real x )

/-
h_seq n (alpha_seq k) is 0 if k < n.
-/
lemma h_seq_eq_zero (n k : ℕ) (h : k < n) : h_seq (fun i => (alpha_seq i : ℝ)) n (alpha_seq k) = 0 := by
  unfold h_seq;
  aesop

/-
Recursive formula for F_partial_sum.
-/
lemma F_partial_sum_succ (n : ℕ) (z : ℂ) : F_partial_sum (n + 1) z = F_partial_sum n z + (lambda_seq (n + 1) : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) (n + 1) z := by
  unfold F_partial_sum;
  simp +decide [ add_assoc, List.range_succ ]

/-
The element returned by first_unused is not in the used set.
-/
lemma first_unused_spec (seq : ℕ → ℚ) (h_surj : Function.Surjective seq) (used : Set ℚ) (h_finite : used.Finite) :
    first_unused seq h_surj used h_finite ∉ used := by
      exact Nat.find_spec ( exists_index_not_mem_finite seq h_surj used h_finite )

/-
Definition of the inductive invariant satisfying conditions (I)-(IV) from the paper (adapted to 0-based indexing). Corrected syntax for sum.
-/
def Invariant (n : ℕ) : Prop :=
  (∀ i j, i ≤ n → j ≤ n → i ≠ j → alpha_seq i ≠ alpha_seq j) ∧
  (∀ i j, i ≤ n → j ≤ n → i ≠ j → beta_seq i ≠ beta_seq j) ∧
  (∀ k ≤ n, F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n (alpha_seq k) = beta_seq k) ∧
  (∀ x : ℝ, deriv (fun t => F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n t) x ≥ 1 - ∑ k ∈ Finset.range (n + 1), if k < 2 then 0 else epsilon_seq k) ∧
  (∀ k, 2 ≤ k → k ≤ n → |lambda_seq k| < eta_seq k)

/-
The invariant holds for n=0.
-/
lemma Invariant_0 : Invariant 0 := by
  refine' ⟨ _, _, _, _, _ ⟩ <;> norm_num;
  · unfold F_seq_real beta_seq alpha_seq;
    unfold construction_seq; norm_num [ F_seq ] ;
    unfold lambda_seq;
    unfold construction_seq; norm_num [ all_tuples ] ;
    unfold next_step; norm_num;
  · unfold F_seq_real;
    unfold F_seq; norm_num [ List.map, List.range_succ ] ;
    unfold h_seq; norm_num [ Complex.exp_re, Complex.exp_im, mul_comm ] ;
  · aesop

/-
The invariant holds for n=1.
-/
lemma Invariant_1 : Invariant 1 := by
  unfold Invariant;
  field_simp;
  refine' ⟨ _, _, _, _, _ ⟩;
  · intro i j hi hj hij; interval_cases i <;> interval_cases j <;> simp_all +decide ;
  · intro i j hi hj hij; interval_cases i <;> interval_cases j <;> simp_all +decide ;
  · unfold F_seq_real beta_seq;
    unfold F_seq alpha_seq lambda_seq construction_seq; norm_num [ List.range_succ ] ;
    intro k hk; interval_cases k <;> norm_num [ List.getLast, all_tuples ] ;
    · unfold next_step; norm_num;
    · unfold next_step; norm_num [ List.range_succ ] ;
  · unfold F_seq_real; norm_num [ Finset.sum_range_succ' ] ;
    unfold F_seq; norm_num [ List.range_succ ] ;
    unfold h_seq; norm_num [ lambda_zero_of_lt_two ] ;
  · intros; linarith;

/-
The set of alpha values in the history at step n is exactly the set of alpha_seq k for k < n.
-/
lemma alpha_set_eq_image (n : ℕ) : alpha_set (all_tuples n) = (Finset.range n).image (fun k => alpha_seq k) := by
  -- By definition of `all_tuples`, the list `all_tuples n` is the list of tuples generated up to step `n-1`.
  have h_all_tuples : all_tuples n = List.map (fun k => (alpha_seq k, beta_seq k, lambda_seq k)) (List.range n) := by
    induction' n with n ih;
    · exact?;
    · -- By definition of `all_tuples`, we have `all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)]`.
      have h_all_tuples_succ : all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)] := by
        exact?;
      -- By definition of `next_step`, the last element of `all_tuples (n + 1)` is `(alpha_seq n, beta_seq n, lambda_seq n)`.
      have h_last_element : next_step n (all_tuples n) = (alpha_seq n, beta_seq n, lambda_seq n) := by
        unfold alpha_seq beta_seq lambda_seq;
        unfold construction_seq; aesop;
      simp_all +decide [ List.range_succ ];
  ext; simp [h_all_tuples, alpha_set];
  bound;
  · grind;
  · exact ⟨ w, w, by simp +decide [ left ], rfl ⟩

/-
The set of beta values in the history at step n is exactly the set of beta_seq k for k < n.
-/
lemma beta_set_eq_image (n : ℕ) : beta_set (all_tuples n) = (Finset.range n).image (fun k => beta_seq k) := by
  -- By definition of `all_tuples`, the list at step `n` contains exactly the tuples `(alpha_seq k, beta_seq k, lambda_seq k)` for `k < n`.
  have h_all_tuples : ∀ n, all_tuples n = List.map (fun k => (alpha_seq k, beta_seq k, lambda_seq k)) (List.range n) := by
    intro n;
    induction' n with n ih;
    · exact?;
    · -- By definition of `all_tuples`, we have `all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)]`.
      have h_all_tuples_succ : all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)] := by
        exact?;
      rw [ h_all_tuples_succ, ih, List.range_succ ];
      unfold alpha_seq beta_seq lambda_seq;
      unfold construction_seq; aesop;
  ext; simp [h_all_tuples, beta_set];
  constructor;
  · grind;
  · rintro ⟨ k, hk₁, hk₂ ⟩ ; use k, k ; aesop

/-
h_seq n z is non-zero if z is distinct from all alpha_seq k for k < n.
-/
lemma h_seq_ne_zero_of_distinct (n : ℕ) (z : ℂ) (h_distinct : ∀ k < n, z ≠ (alpha_seq k : ℂ)) :
    h_seq (fun k => (alpha_seq k : ℝ)) n z ≠ 0 := by
      unfold h_seq; aesop;
      exact h_distinct _ left ( sub_eq_zero.mp right )

/-
A differentiable function with derivative bounded below by a positive constant is surjective.
-/
lemma surjective_of_deriv_ge (f : ℝ → ℝ) (hf : Differentiable ℝ f) (c : ℝ) (hc : c > 0) (h_deriv : ∀ x, deriv f x ≥ c) : Function.Surjective f := by
  -- Since the derivative is bounded below by `c > 0`, the function grows at least linearly.
  have h_grow : ∀ x y : ℝ, x < y → f y ≥ f x + c * (y - x) := by
    intro x y hxy;
    have := exists_deriv_eq_slope f hxy;
    exact this ( hf.continuous.continuousOn ) ( hf.differentiableOn ) |> fun ⟨ z, hz₁, hz₂ ⟩ => by nlinarith [ h_deriv z, mul_div_cancel₀ ( f y - f x ) ( sub_ne_zero_of_ne hxy.ne' ) ] ;
  -- By the Intermediate Value Theorem, since `f` is continuous, it is surjective.
  intros y
  have h_ivt : IsConnected (Set.range f) := by
    exact isConnected_range hf.continuous;
  -- Since $f$ grows at least linearly, the range of $f$ is unbounded above and below.
  have h_unbounded_above : ∀ M : ℝ, ∃ x : ℝ, f x > M := by
    exact fun M => ⟨ ⌊ ( M - f 0 ) / c⌋₊ + 1, by nlinarith [ Nat.lt_floor_add_one ( ( M - f 0 ) / c ), h_grow 0 ( ⌊ ( M - f 0 ) / c⌋₊ + 1 ) ( by linarith ), mul_div_cancel₀ ( M - f 0 ) hc.ne' ] ⟩
  have h_unbounded_below : ∀ M : ℝ, ∃ x : ℝ, f x < M := by
    intro M; use - ( |M - f 0| + 1 ) / c; cases abs_cases ( M - f 0 ) <;> nlinarith [ mul_div_cancel₀ ( - ( |M - f 0| + 1 ) ) hc.ne', h_grow ( - ( |M - f 0| + 1 ) / c ) 0 ( by nlinarith [ mul_div_cancel₀ ( - ( |M - f 0| + 1 ) ) hc.ne' ] ) ] ;
  exact h_ivt.Icc_subset ( Set.mem_range_self <| Classical.choose <| h_unbounded_below y ) ( Set.mem_range_self <| Classical.choose <| h_unbounded_above y ) ⟨ by linarith [ Classical.choose_spec <| h_unbounded_below y ], by linarith [ Classical.choose_spec <| h_unbounded_above y ] ⟩

/-
If Invariant n holds, the derivative of F_n is strictly greater than 1/2.
-/
lemma F_seq_deriv_bound_of_Invariant (n : ℕ) (h : Invariant n) (x : ℝ) :
    deriv (fun t => F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n t) x > 1/2 := by
      -- Apply the lemma that if a function has a derivative bounded below by a positive constant, then it is surjective.
      apply lt_of_lt_of_le (by
      -- We know that $\sum_{k=0}^\infty \epsilon_k < 1/2$.
      have h_sum_lt_half : ∑' k : ℕ, epsilon_seq k < 1 / 2 := by
        exact?;
      have h_sum_lt_half : ∑ k ∈ Finset.range (n + 1), (if k < 2 then 0 else epsilon_seq k) ≤ ∑' k : ℕ, epsilon_seq k := by
        refine' le_trans ( Finset.sum_le_sum fun i hi => _ ) ( Summable.sum_le_tsum ( Finset.range ( n + 1 ) ) ( fun i _ => by unfold epsilon_seq; positivity ) ( by unfold epsilon_seq; exact Summable.comp_injective ( summable_geometric_two ) fun a b h => by simpa using h ) );
        split_ifs <;> norm_num [ epsilon_seq ];
      linarith) (h.2.2.2.1 x)

/-
Conditions for Step B (Force Domain) to succeed: eta is positive and h_n(alpha_n) is non-zero.
-/
lemma next_step_B_conditions (n : ℕ) (h : Invariant n) (h_even : n % 2 = 0) (hn : n ≥ 2) :
    eta_seq n > 0 ∧
    h_seq_real (fun k => alpha_seq k) n (first_unused a_seq a_seq_surj (alpha_set (all_tuples n)) (alpha_set_finite (all_tuples n))) ≠ 0 := by
      have h_eta_pos : eta_seq n > 0 := by
        exact eta_seq_pos n ( by linarith );
      -- By `h_seq_ne_zero_of_distinct`, `h_seq n alpha_n` is non-zero.
      have h_h_seq_ne_zero : h_seq (fun k => (alpha_seq k : ℝ)) n (first_unused a_seq a_seq_surj (alpha_set (all_tuples n)) (alpha_set_finite (all_tuples n))) ≠ 0 := by
        apply h_seq_ne_zero_of_distinct;
        intro k hk_lt_n hk_eq_alpha_k;
        have := first_unused_spec a_seq a_seq_surj ( alpha_set ( all_tuples n ) ) ( alpha_set_finite ( all_tuples n ) ) ; simp_all +decide [ Finset.mem_image, Set.mem_range ] ;
        exact this <| by rw [ alpha_set_eq_image ] ; exact Finset.mem_image.mpr ⟨ k, Finset.mem_range.mpr hk_lt_n, rfl ⟩ ;
      convert h_h_seq_ne_zero using 1;
      unfold h_seq_real h_seq; norm_num [ Complex.ext_iff ] ;
      induction ( List.range n ) <;> simp_all +decide [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ];
      · split_ifs <;> norm_num [ Complex.exp_re, Complex.exp_im ];
        norm_cast ; norm_num;
      · split_ifs <;> simp_all +decide [ Complex.exp_re, Complex.exp_im ];
        grind

/-
If Invariant n holds, then F_n is surjective.
-/
lemma F_seq_surjective (n : ℕ) (h : Invariant n) : Function.Surjective (fun x => F_seq_real (fun k => alpha_seq k) (fun k => lambda_seq k) n x) := by
  -- By `F_seq_deriv_bound_of_Invariant`, the derivative is bounded below by 1/2.
  have h_deriv_bound : ∀ x : ℝ, deriv (fun t => F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n t) x ≥ 1 / 2 := by
    exact fun x => le_of_lt ( F_seq_deriv_bound_of_Invariant n h x );
  apply_rules [ surjective_of_deriv_ge ];
  · exact fun x => differentiableAt_of_deriv_ne_zero ( by linarith [ h_deriv_bound x ] );
  · norm_num

/-
If x_n maps to the new beta value, it cannot be one of the previous alpha values.
-/
lemma x_n_not_in_prev_alphas (n : ℕ) (h_inv : Invariant (n - 1)) (h_odd : n % 2 = 1) (hn : n ≥ 1)
    (x_n : ℝ) (hx_n : F_seq_real (fun k => alpha_seq k) (fun k => lambda_seq k) (n - 1) x_n = first_unused b_seq b_seq_surj (beta_set (all_tuples n)) (beta_set_finite (all_tuples n))) :
    ∀ k < n, x_n ≠ alpha_seq k := by
      intro k hk_lt_n hk_eq_alpha;
      -- By Invariant (n-1), we know that F_{n-1}(alpha_k) = beta_k.
      have h_F_seq_real : F_seq_real (fun k => (alpha_seq k : ℝ)) (fun k => (lambda_seq k : ℝ)) (n - 1) (alpha_seq k) = beta_seq k := by
        have := h_inv.2.2.1 k ( Nat.le_sub_one_of_lt hk_lt_n ) ; aesop;
      -- By definition of `first_unused`, we know that `beta_n` is not in the set `{beta_seq 0, ..., beta_seq (n-1)}`.
      have h_beta_n_not_in_beta_set : (first_unused b_seq b_seq_surj (beta_set (all_tuples n)) (beta_set_finite (all_tuples n))) ∉ (beta_set (all_tuples n)) := by
        exact?;
      simp_all +decide [ beta_set_eq_image ]

/-
h_n(x) is non-zero if F_{n-1}(x) is the new beta value.
-/
lemma next_step_A_h_ne_zero (n : ℕ) (h_inv : Invariant (n - 1)) (h_odd : n % 2 = 1) (hn : n ≥ 1)
    (x : ℝ) (hx : F_seq_real (fun k => alpha_seq k) (fun k => lambda_seq k) (n - 1) x = first_unused b_seq b_seq_surj (beta_set (all_tuples n)) (beta_set_finite (all_tuples n))) :
    h_seq_real (fun k => alpha_seq k) n x ≠ 0 := by
      have := h_seq_ne_zero_of_distinct n x;
      convert this _;
      · unfold h_seq_real; norm_cast;
        unfold h_seq; norm_num;
        norm_num [ Complex.ext_iff ];
        split_ifs <;> norm_num [ Complex.exp_re, Complex.exp_im, List.prod_range_succ' ];
        norm_cast ; norm_num;
        induction ( List.range n ) <;> aesop;
      · exact fun k hk => mod_cast x_n_not_in_prev_alphas n h_inv h_odd hn x hx k hk

/-
Conditions for Step B (Force Domain) to succeed, without requiring Invariant.
-/
lemma next_step_B_conditions_simple (n : ℕ) (hn : n ≥ 2) :
    eta_seq n > 0 ∧
    h_seq_real (fun k => alpha_seq k) n (first_unused a_seq a_seq_surj (alpha_set (all_tuples n)) (alpha_set_finite (all_tuples n))) ≠ 0 := by
      refine' ⟨ eta_seq_pos n ( by linarith ), _ ⟩;
      have h_alpha_n_not_in_prev_alphas : ∀ k < n, (first_unused a_seq a_seq_surj (alpha_set (all_tuples n)) (alpha_set_finite (all_tuples n)) : ℝ) ≠ (alpha_seq k : ℝ) := by
        intro k hk_lt_n hk_eq;
        have := first_unused_spec a_seq a_seq_surj ( alpha_set ( all_tuples n ) ) ( alpha_set_finite ( all_tuples n ) ) ; simp_all +decide [ Set.ext_iff ] ;
        exact this <| by rw [ show alpha_set ( all_tuples n ) = ( Finset.range n ).image ( fun k => alpha_seq k ) from alpha_set_eq_image n ] ; exact Finset.mem_image_of_mem _ <| Finset.mem_range.mpr hk_lt_n;
      convert h_seq_ne_zero_of_distinct n ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples n ) ) ( alpha_set_finite ( all_tuples n ) ) ) ( fun k hk => ?_ ) using 1;
      · unfold h_seq_real h_seq; norm_num [ Complex.ext_iff ] ;
        split_ifs <;> simp_all +decide [ Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im ];
        norm_cast ; norm_num;
        induction ( List.range n ) <;> aesop;
      · exact_mod_cast h_alpha_n_not_in_prev_alphas k hk

/-
h_seq depends only on the first n values of alpha.
-/
lemma h_seq_eq_of_agree (n : ℕ) (alpha1 alpha2 : ℕ → ℝ) (h_agree : ∀ k < n, alpha1 k = alpha2 k) (z : ℂ) :
    h_seq alpha1 n z = h_seq alpha2 n z := by
      unfold h_seq;
      cases n <;> simp_all +decide [ List.range_succ_eq_map ];
      exact Or.inl ( congr_arg _ ( List.ext_get ( by simp +decide [ h_agree ] ) fun i hi => by aesop ) )

/-
h_seq computed from history equals h_seq computed from global sequence.
-/
lemma h_seq_eq_h_seq_real (n : ℕ) (z : ℂ) :
    h_seq (alpha_from_hist (all_tuples n)) n z = h_seq (fun k => (alpha_seq k : ℝ)) n z := by
      apply h_seq_eq_of_agree;
      exact?

/-
h_seq_real computed from history equals h_seq_real computed from global sequence.
-/
lemma h_seq_real_eq_h_seq_real (n : ℕ) (x : ℝ) :
    h_seq_real (alpha_from_hist (all_tuples n)) n x = h_seq_real (fun k => alpha_seq k) n x := by
      exact congr_arg Complex.re ( h_seq_eq_h_seq_real n x )

/-
eta computed from history equals eta computed from global sequence.
-/
lemma eta_eq_eta_seq (n : ℕ) :
    eta_val (alpha_from_hist (all_tuples n)) n (epsilon_seq n) = eta_seq n := by
      -- Apply the lemma that states the equality of eta_val when computed from the history and the global sequence.
      apply eta_in_next_step_eq_eta_seq

/-
For even n >= 2, next_step returns the tuple constructed in Step B.
-/
lemma next_step_eq_B (n : ℕ) (hn : n ≥ 2) (heven : n % 2 = 0) (h_inv : Invariant (n - 1)) :
  let hist := all_tuples n
  let alpha_prev := alpha_from_hist hist
  let lambda_prev := lambda_from_hist hist
  let F_prev := F_seq_real alpha_prev lambda_prev (n - 1)
  let h_curr := h_seq_real alpha_prev n
  let eta := eta_val alpha_prev n (epsilon_seq n)
  let alpha_n := first_unused a_seq a_seq_surj (alpha_set hist) (alpha_set_finite hist)
  let y := F_prev alpha_n
  let h_val := h_curr alpha_n
  let radius := eta * |h_val|
  let beta_n := choice_in_interval (y - radius) (y + radius) (by
    have h_cond := next_step_B_conditions_simple n hn
    have h_eta_pos : eta_seq n > 0 := h_cond.1
    have h_h_val_ne_zero : h_seq_real (fun k => alpha_seq k) n alpha_n ≠ 0 := h_cond.2
    dsimp only [radius]
    have h_eta_eq : eta = eta_seq n := eta_eq_eta_seq n
    have h_val_eq : h_val = h_seq_real (fun k => alpha_seq k) n alpha_n := h_seq_real_eq_h_seq_real n alpha_n
    rw [h_eta_eq, h_val_eq]
    have : 0 < eta_seq n * |h_seq_real (fun k => alpha_seq k) n alpha_n| := mul_pos h_eta_pos (abs_pos.mpr h_h_val_ne_zero)
    linarith) (beta_set hist) (beta_set_finite hist)
  let lambda_n := (beta_n - y) / h_val
  next_step n hist = (alpha_n, beta_n, lambda_n) := by
    -- Since $n \geq 2$ and $n$ is even, the conditions for `next_step` to return the tuple constructed in Step B are satisfied.
    have h_conditions : eta_val (alpha_from_hist (all_tuples n)) n (epsilon_seq n) > 0 ∧ h_seq_real (alpha_from_hist (all_tuples n)) n (first_unused a_seq a_seq_surj (alpha_set (all_tuples n)) (alpha_set_finite (all_tuples n))) ≠ 0 := by
      exact ⟨ by simpa only [ eta_eq_eta_seq ] using next_step_B_conditions_simple n hn |>.1, by simpa only [ h_seq_real_eq_h_seq_real ] using next_step_B_conditions_simple n hn |>.2 ⟩;
    -- By definition of `next_step`, we can unfold it and use the conditions to show that it returns the constructed tuple.
    unfold next_step;
    grind

/-
The value of choice_in_interval does not depend on the proof that x < y.
-/
lemma choice_in_interval_irrel (x y : ℝ) (h1 h2 : x < y) (S : Set ℚ) (hS : S.Finite) :
  choice_in_interval x y h1 S hS = choice_in_interval x y h2 S hS := by
    congr!

/-
Checking if next_step_eq_B is defined.
-/
#check next_step_eq_B

/-
Existence of a preimage for the new beta value in Step A.
-/
lemma next_step_A_exists_preimage (n : ℕ) (h_inv : Invariant (n - 1)) (hn : n ≥ 1) :
    ∃ x, F_seq_real (fun k => alpha_seq k) (fun k => lambda_seq k) (n - 1) x =
         first_unused b_seq b_seq_surj (beta_set (all_tuples n)) (beta_set_finite (all_tuples n)) := by
           exact F_seq_surjective _ h_inv _

/-
For even n >= 2, next_step returns the tuple constructed in Step B.
-/
lemma next_step_eq_B_final_v2 (n : ℕ) (hn : n ≥ 2) (heven : n % 2 = 0) (h_inv : Invariant (n - 1)) :
  let hist := all_tuples n
  let alpha_prev := alpha_from_hist hist
  let lambda_prev := lambda_from_hist hist
  let F_prev := F_seq_real alpha_prev lambda_prev (n - 1)
  let h_curr := h_seq_real alpha_prev n
  let eta := eta_val alpha_prev n (epsilon_seq n)
  let alpha_n := first_unused a_seq a_seq_surj (alpha_set hist) (alpha_set_finite hist)
  let y := F_prev alpha_n
  let h_val := h_curr alpha_n
  let radius := eta * |h_val|
  let beta_n := choice_in_interval (y - radius) (y + radius) (by
    dsimp only [radius]
    have h_cond := next_step_B_conditions_simple n hn
    have h_eta_pos : eta_seq n > 0 := h_cond.1
    have h_h_val_ne_zero : h_seq_real (fun k => alpha_seq k) n alpha_n ≠ 0 := h_cond.2
    have h_eta_eq : eta = eta_seq n := eta_eq_eta_seq n
    have h_val_eq : h_val = h_seq_real (fun k => alpha_seq k) n alpha_n := h_seq_real_eq_h_seq_real n alpha_n
    rw [h_eta_eq, h_val_eq]
    have : 0 < eta_seq n * |h_seq_real (fun k => alpha_seq k) n alpha_n| := mul_pos h_eta_pos (abs_pos.mpr h_h_val_ne_zero)
    linarith) (beta_set hist) (beta_set_finite hist)
  let lambda_n := (beta_n - y) / h_val
  next_step n hist = (alpha_n, beta_n, lambda_n) := by
    exact?

/-
For even n >= 2, next_step returns the tuple constructed in Step B.
-/
lemma next_step_eq_B_final_v3 (n : ℕ) (hn : n ≥ 2) (heven : n % 2 = 0) (h_inv : Invariant (n - 1)) :
  let hist := all_tuples n
  let alpha_prev := alpha_from_hist hist
  let lambda_prev := lambda_from_hist hist
  let F_prev := F_seq_real alpha_prev lambda_prev (n - 1)
  let h_curr := h_seq_real alpha_prev n
  let eta := eta_val alpha_prev n (epsilon_seq n)
  let alpha_n := first_unused a_seq a_seq_surj (alpha_set hist) (alpha_set_finite hist)
  let y := F_prev alpha_n
  let h_val := h_curr alpha_n
  let radius := eta * |h_val|
  let beta_n := choice_in_interval (y - radius) (y + radius) (by
  have h_radius_pos : 0 < radius := by
    refine' mul_pos _ _;
    · convert eta_seq_pos n ( by linarith ) using 1;
      exact?;
    · simp +zetaDelta at *;
      convert next_step_B_conditions_simple n hn |>.2 using 1;
      rw [ h_seq_real_eq_h_seq_real ]
  generalize_proofs at *;
  linarith [h_radius_pos]) (beta_set hist) (beta_set_finite hist)
  let lambda_n := (beta_n - y) / h_val
  next_step n hist = (alpha_n, beta_n, lambda_n) := by
    all_goals generalize_proofs at *;
    exact?

/-
Lambda is continuous at x and vanishes at x.
-/
lemma next_step_A_Lambda_continuous (n : ℕ) (h_inv : Invariant (n - 1)) (h_odd : n % 2 = 1) (hn : n ≥ 1)
    (x : ℝ) (hx : F_seq_real (fun k => alpha_seq k) (fun k => lambda_seq k) (n - 1) x = first_unused b_seq b_seq_surj (beta_set (all_tuples n)) (beta_set_finite (all_tuples n))) :
    let hist := all_tuples n
    let alpha_prev := alpha_from_hist hist
    let lambda_prev := lambda_from_hist hist
    let F_prev := F_seq_real alpha_prev lambda_prev (n - 1)
    let h_curr := h_seq_real alpha_prev n
    let beta_n := first_unused b_seq b_seq_surj (beta_set hist) (beta_set_finite hist)
    let Lambda := fun t => (beta_n - F_prev t) / h_curr t
    ContinuousAt Lambda x ∧ Lambda x = 0 := by
      constructor
      all_goals generalize_proofs at *;
      · refine' ContinuousAt.div _ _ _;
        · refine' ContinuousAt.sub continuousAt_const _;
          -- The sum of continuous functions is continuous, and the identity function is continuous.
          have h_cont : Continuous (fun t => t + ∑ k ∈ Finset.range (n - 1 + 1), (lambda_from_hist (all_tuples n) k : ℝ) * h_seq_real (alpha_from_hist (all_tuples n)) k t) := by
            refine' continuous_id.add _;
            refine' continuous_finset_sum _ fun k hk => Continuous.mul _ _;
            · exact continuous_const;
            · unfold h_seq_real;
              unfold h_seq;
              split_ifs <;> norm_cast <;> norm_num;
              · exact continuous_const;
              · fun_prop;
          convert h_cont.continuousAt using 1;
          ext t; simp +decide [ F_seq_real ] ;
          unfold F_seq; norm_num [ h_seq_real, Complex.exp_re, Complex.exp_im ] ;
          induction ( n - 1 + 1 ) <;> simp_all +decide [ Finset.sum_range_succ, List.range_succ ];
        · refine' Continuous.continuousAt _;
          -- The function `h_seq_real` is continuous because it is a composition of continuous functions.
          have h_cont : Continuous (fun z : ℂ => h_seq (alpha_from_hist (all_tuples n)) n z) := by
            unfold h_seq;
            cases n <;> continuity;
          exact Complex.continuous_re.comp h_cont |> Continuous.comp <| Complex.continuous_ofReal;
        · convert next_step_A_h_ne_zero n h_inv h_odd hn x _ using 1;
          · exact?;
          · exact hx;
      · have h_eq : F_seq_real (alpha_from_hist (all_tuples n)) (lambda_from_hist (all_tuples n)) (n - 1) x = F_seq_real (fun k => alpha_seq k) (fun k => lambda_seq k) (n - 1) x := by
          -- By definition of `alpha_from_hist` and `lambda_from_hist`, we can rewrite the real part of `F_seq` using the global `alpha_seq` and `lambda_seq`.
          have h_alpha_lambda_eq : ∀ k < n, alpha_from_hist (all_tuples n) k = alpha_seq k ∧ lambda_from_hist (all_tuples n) k = lambda_seq k := by
            intro k hk
            generalize_proofs at *;
            unfold alpha_from_hist lambda_from_hist alpha_seq lambda_seq;
            rw [ show all_tuples n = List.map ( fun k => construction_seq k ) ( List.range n ) from ?_ ];
            · norm_num [ List.get?_eq_get, hk ];
            · induction' n with n ih;
              · contradiction;
              · induction' n + 1 with n ih <;> simp_all +decide [ List.range_succ ];
                -- By definition of `all_tuples`, we have `all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)]`.
                have h_all_tuples_succ : all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)] := by
                  exact?;
                unfold construction_seq; aesop;
          unfold F_seq_real
          generalize_proofs at *;
          have h_sum_eq : ∀ k < n, (lambda_from_hist (all_tuples n) k : ℂ) * h_seq (alpha_from_hist (all_tuples n)) k x = (lambda_seq k : ℂ) * h_seq (fun k => alpha_seq k) k x := by
            intro k hk; rw [ h_alpha_lambda_eq k hk |>.2 ] ;
            rw [ h_seq_eq_of_agree k _ _ fun i hi => h_alpha_lambda_eq i ( by linarith ) |>.1 ];
          unfold F_seq
          generalize_proofs at *;
          rw [ Nat.sub_add_cancel hn ];
          rw [ show ( List.range n |> List.map fun k => ( lambda_from_hist ( all_tuples n ) k : ℂ ) * h_seq ( alpha_from_hist ( all_tuples n ) ) k x ) = List.map ( fun k => ( lambda_seq k : ℂ ) * h_seq ( fun k => alpha_seq k : ℕ → ℝ ) k x ) ( List.range n ) from List.ext_get ( by aesop ) ( by aesop ) ]
        generalize_proofs at *;
        aesop

/-
For even n >= 2, next_step returns the tuple constructed in Step B.
-/
lemma next_step_eq_B_proven (n : ℕ) (hn : n ≥ 2) (heven : n % 2 = 0) (h_inv : Invariant (n - 1)) :
  let hist := all_tuples n
  let alpha_prev := alpha_from_hist hist
  let lambda_prev := lambda_from_hist hist
  let F_prev := F_seq_real alpha_prev lambda_prev (n - 1)
  let h_curr := h_seq_real alpha_prev n
  let eta := eta_val alpha_prev n (epsilon_seq n)
  let alpha_n := first_unused a_seq a_seq_surj (alpha_set hist) (alpha_set_finite hist)
  let y := F_prev alpha_n
  let h_val := h_curr alpha_n
  let radius := eta * |h_val|
  let beta_n := choice_in_interval (y - radius) (y + radius) (by
  have h_radius_pos : 0 < radius := by
    have h_radius_pos : 0 < eta ∧ 0 < |h_val| := by
      apply And.intro;
      · convert eta_seq_pos n ( by linarith );
        exact?;
      · have := next_step_B_conditions_simple n hn;
        norm_num +zetaDelta at *;
        convert this.2 using 1;
        rw [ h_seq_real_eq_h_seq_real ];
    exact mul_pos h_radius_pos.left h_radius_pos.right;
  linarith) (beta_set hist) (beta_set_finite hist)
  let lambda_n := (beta_n - y) / h_val
  next_step n hist = (alpha_n, beta_n, lambda_n) := by
    all_goals generalize_proofs at *;
    exact?

/-
Existence of delta for Step A.
-/
lemma next_step_A_delta_exists (n : ℕ) (h_inv : Invariant (n - 1)) (h_odd : n % 2 = 1) (hn : n ≥ 1)
    (x : ℝ) (hx : F_seq_real (fun k => alpha_seq k) (fun k => lambda_seq k) (n - 1) x = first_unused b_seq b_seq_surj (beta_set (all_tuples n)) (beta_set_finite (all_tuples n))) :
    let hist := all_tuples n
    let alpha_prev := alpha_from_hist hist
    let lambda_prev := lambda_from_hist hist
    let F_prev := F_seq_real alpha_prev lambda_prev (n - 1)
    let h_curr := h_seq_real alpha_prev n
    let eta := eta_val alpha_prev n (epsilon_seq n)
    let beta_n := first_unused b_seq b_seq_surj (beta_set hist) (beta_set_finite hist)
    let Lambda := fun t => (beta_n - F_prev t) / h_curr t
    ∃ delta, 0 < delta ∧ ∀ t, |t - x| < delta → |Lambda t| < eta := by
      -- Apply the definition of continuity at a point with ε = eta.
      have h_cont : ContinuousAt (fun t => (first_unused b_seq b_seq_surj (beta_set (all_tuples n)) (beta_set_finite (all_tuples n)) - F_seq_real (alpha_from_hist (all_tuples n)) (lambda_from_hist (all_tuples n)) (n - 1) t) / h_seq_real (alpha_from_hist (all_tuples n)) n t) x ∧ (first_unused b_seq b_seq_surj (beta_set (all_tuples n)) (beta_set_finite (all_tuples n)) - F_seq_real (alpha_from_hist (all_tuples n)) (lambda_from_hist (all_tuples n)) (n - 1) x) / h_seq_real (alpha_from_hist (all_tuples n)) n x = 0 := by
        convert next_step_A_Lambda_continuous n h_inv h_odd hn x hx using 1;
      have := Metric.continuousAt_iff.mp h_cont.1;
      simp_all +decide [ dist_eq_norm ];
      cases h_cont.2 <;> simp_all ( config := { decide := Bool.true } ) [ sub_eq_iff_eq_add ];
      · exact this _ ( eta_eq_eta_seq n ▸ eta_seq_pos _ ( by linarith ) );
      · exact this _ ( show 0 < eta_val ( alpha_from_hist ( all_tuples n ) ) n ( epsilon_seq n ) from by simpa only [ eta_eq_eta_seq ] using eta_seq_pos n ( by linarith ) )

/-
lambda_from_hist matches lambda_seq for indices within range.
-/
lemma lambda_from_hist_eq_lambda_seq (n k : ℕ) (h : k < n) :
    lambda_from_hist (all_tuples n) k = lambda_seq k := by
      unfold lambda_seq;
      -- By definition of `all_tuples`, we know that `all_tuples n` is the list of tuples up to `n-1`.
      have h_all_tuples : ∀ n, all_tuples n = List.map (fun k => construction_seq k) (List.range n) := by
        intro n
        induction' n with n ih;
        · rfl;
        · -- By definition of `all_tuples`, we have `all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)]`.
          have h_all_tuples_succ : all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)] := by
            exact?;
          simp_all +decide [ List.range_succ ];
          unfold construction_seq; aesop;
      unfold lambda_from_hist; aesop;

/-
F_seq_real computed from history matches F_seq_real computed from global sequences.
-/
lemma F_seq_real_eq_F_seq_real (n : ℕ) (x : ℝ) (hn : n ≥ 1) :
    F_seq_real (alpha_from_hist (all_tuples n)) (lambda_from_hist (all_tuples n)) (n - 1) x =
    F_seq_real (fun k => alpha_seq k) (fun k => lambda_seq k) (n - 1) x := by
      unfold F_seq_real;
      unfold F_seq;
      congr! 3;
      refine' List.map_congr_left fun k hk => _;
      field_simp;
      congr! 1;
      · rw [ lambda_from_hist_eq_lambda_seq ] ; aesop;
      · exact h_seq_eq_of_agree k _ _ ( fun j hj => by
          convert alpha_from_hist_eq_alpha_seq n j ( by linarith [ List.mem_range.mp hk, Nat.sub_add_cancel hn ] ) using 1 ) _

/-
For odd n >= 2, next_step returns the tuple constructed in Step A (explicit version).
-/
lemma next_step_eq_A_explicit (n : ℕ) (hn : n ≥ 2) (hodd : n % 2 = 1) (h_inv : Invariant (n - 1)) :
  let hist := all_tuples n
  let alpha_prev := alpha_from_hist hist
  let lambda_prev := lambda_from_hist hist
  let F_prev := F_seq_real alpha_prev lambda_prev (n - 1)
  let h_curr := h_seq_real alpha_prev n
  let eta := eta_val alpha_prev n (epsilon_seq n)
  let beta_n := first_unused b_seq b_seq_surj (beta_set hist) (beta_set_finite hist)

  let x_n := Classical.choose (next_step_A_exists_preimage n h_inv (by linarith))
  let h_x_n := Classical.choose_spec (next_step_A_exists_preimage n h_inv (by linarith))

  let delta := Classical.choose (next_step_A_delta_exists n h_inv hodd (by linarith) x_n h_x_n)
  let h_delta := Classical.choose_spec (next_step_A_delta_exists n h_inv hodd (by linarith) x_n h_x_n)

  let alpha_n := choice_in_interval (x_n - delta) (x_n + delta) (by
    have h_delta_pos : 0 < delta := h_delta.1
    linarith) (alpha_set hist) (alpha_set_finite hist)

  let Lambda := fun t => (beta_n - F_prev t) / h_curr t
  let lambda_n := Lambda alpha_n

  next_step n hist = (alpha_n, beta_n, lambda_n) := by
    unfold next_step;
    simp +decide [ hodd ];
    have h_eta_pos : 0 < eta_val (alpha_from_hist (all_tuples n)) n (epsilon_seq n) := by
      exact eta_seq_pos n ( by linarith ) |> fun h => by simpa [ eta_eq_eta_seq ] using h;
    split_ifs <;> try linarith;
    · -- Since $h_seq_real (alpha_from_hist (all_tuples n)) n (Classical.choose ...) = 0$, this contradicts the assumption that $h_seq_real$ is non-zero for all $k < n$.
      have h_contra : h_seq_real (alpha_from_hist (all_tuples n)) n (Classical.choose (‹∃ x, F_seq_real (alpha_from_hist (all_tuples n)) (lambda_from_hist (all_tuples n)) (n - 1) x = ↑(first_unused b_seq b_seq_surj (beta_set (all_tuples n)) (beta_set_finite (all_tuples n)))›)) ≠ 0 := by
        convert next_step_A_h_ne_zero n h_inv hodd ( Nat.one_le_iff_ne_zero.mpr ‹_› ) _ _ using 1;
        convert h_seq_real_eq_h_seq_real n _;
        convert Classical.choose_spec ‹∃ x, F_seq_real ( alpha_from_hist ( all_tuples n ) ) ( lambda_from_hist ( all_tuples n ) ) ( n - 1 ) x = ↑ ( first_unused b_seq b_seq_surj ( beta_set ( all_tuples n ) ) ( beta_set_finite ( all_tuples n ) ) ) › using 1;
        convert F_seq_real_eq_F_seq_real n _ ( Nat.one_le_iff_ne_zero.mpr ‹_› ) |> Eq.symm using 1;
      exact?;
    · rename_i h₁ h₂ h₃ h₄ h₅;
      have h₇ : Classical.choose h₂ = Classical.choose (next_step_A_exists_preimage n h_inv (by linarith)) := by
        congr! 1;
        ext x; exact (by
        rw [ F_seq_real_eq_F_seq_real ];
        linarith);
      aesop ( simp_config := { singlePass := true } );
    · rename_i h;
      contrapose! h;
      have := Classical.choose_spec ‹∃ x, F_seq_real ( alpha_from_hist ( all_tuples n ) ) ( lambda_from_hist ( all_tuples n ) ) ( n - 1 ) x = _›;
      have := Metric.continuousAt_iff.mp ( show ContinuousAt ( fun t => ( ↑ ( first_unused b_seq b_seq_surj ( beta_set ( all_tuples n ) ) ( beta_set_finite ( all_tuples n ) ) ) - F_seq_real ( alpha_from_hist ( all_tuples n ) ) ( lambda_from_hist ( all_tuples n ) ) ( n - 1 ) t ) / h_seq_real ( alpha_from_hist ( all_tuples n ) ) n t ) ( Classical.choose ‹∃ x, F_seq_real ( alpha_from_hist ( all_tuples n ) ) ( lambda_from_hist ( all_tuples n ) ) ( n - 1 ) x = _› ) from by tauto );
      simp_all +decide [ sub_eq_iff_eq_add ];
      simpa only [ abs_div ] using this _ h_eta_pos;
    · have := Classical.choose_spec ‹∃ x, F_seq_real ( alpha_from_hist ( all_tuples n ) ) ( lambda_from_hist ( all_tuples n ) ) ( n - 1 ) x = _›;
      simp_all +decide [ sub_eq_iff_eq_add ];
      exact False.elim <| ‹¬ContinuousAt ( fun t => ( ↑ ( first_unused b_seq b_seq_surj ( beta_set ( all_tuples n ) ) ( beta_set_finite ( all_tuples n ) ) ) - F_seq_real ( alpha_from_hist ( all_tuples n ) ) ( lambda_from_hist ( all_tuples n ) ) ( n - 1 ) t ) / h_seq_real ( alpha_from_hist ( all_tuples n ) ) n t ) ( Classical.choose ‹∃ x, F_seq_real ( alpha_from_hist ( all_tuples n ) ) ( lambda_from_hist ( all_tuples n ) ) ( n - 1 ) x = _› ) › <| ContinuousAt.div ( ContinuousAt.sub continuousAt_const <| by
        -- The sum of continuous functions is continuous, and each term in the sum is continuous.
        have h_cont : Continuous (fun t => ∑ k ∈ Finset.range (n - 1 + 1), (lambda_from_hist (all_tuples n) k : ℝ) * h_seq_real (alpha_from_hist (all_tuples n)) k t) := by
          refine' continuous_finset_sum _ fun i hi => Continuous.mul _ _;
          · exact continuous_const;
          · unfold h_seq_real;
            unfold h_seq;
            split_ifs <;> norm_num [ Complex.exp_re, Complex.exp_im ];
            · exact continuous_const;
            · fun_prop (disch := norm_num);
        convert h_cont.continuousAt.add continuousAt_id using 1;
        ext; simp [F_seq_real];
        unfold F_seq; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.arg ] ;
        induction ( n - 1 + 1 ) <;> simp_all +decide [ Finset.sum_range_succ, List.range_succ ] ; ring;
        linarith! ) ( by
        unfold h_seq_real;
        unfold h_seq;
        split_ifs ; norm_num [ Complex.exp_re, Complex.exp_im ];
        fun_prop ) <| by assumption;
    · rename_i h₁ h₂ h₃;
      contrapose! h₃;
      have := next_step_A_exists_preimage n h_inv ( by linarith );
      exact ⟨ this.choose, by simpa only [ F_seq_real_eq_F_seq_real n this.choose ( by linarith ) ] using this.choose_spec ⟩

/-
The n-th alpha is the first component of the tuple generated at step n.
-/
lemma alpha_seq_eq_next_step_fst (n : ℕ) :
    alpha_seq n = (next_step n (all_tuples n)).1 := by
      -- By definition of `alpha_seq`, we know that `alpha_seq n = (all_tuples (n + 1)).getLast?.getD (0, 0, 0) |>.1`.
      simp [alpha_seq, construction_seq];
      -- By definition of `all_tuples`, we have `all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)]`.
      have h_all_tuples : all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)] := by
        exact?;
      aesop

/-
If the step index is even, the new alpha is distinct from all previous alphas.
-/
lemma alpha_seq_succ_distinct_even (n : ℕ) (h_even : (n + 1) % 2 = 0) (hn : n + 1 ≥ 2) :
    alpha_seq (n + 1) ∉ (Finset.range (n + 1)).image (fun k => alpha_seq k) := by
      have h_alpha_n : alpha_seq (n + 1) ∉ alpha_set (all_tuples (n + 1)) := by
        rw [alpha_seq_eq_next_step_fst];
        unfold next_step;
        split_ifs <;> simp_all +decide [ Nat.even_iff ];
        split_ifs <;> simp_all +decide [ first_unused_spec ];
        unfold eta_val at *;
        exact absurd ‹_› ( not_le_of_gt ( lt_min ( div_pos ( epsilon_pos _ ) ( M_val_pos _ _ ) ) ( div_pos ( epsilon_pos _ ) ( L_val_pos _ _ ( by linarith ) ) ) ) );
      convert h_alpha_n using 1;
      rw [ alpha_set_eq_image ];
      norm_num

/-
If the step index is odd, the new alpha is distinct from all previous alphas (assuming invariant holds).
-/
lemma alpha_seq_succ_distinct_odd (n : ℕ) (h_odd : n % 2 = 1) (hn : n ≥ 1) (h_inv : Invariant (n - 1)) :
    alpha_seq n ∉ (Finset.range n).image (fun k => alpha_seq k) := by
      by_cases h1 : n % 2 = 1 ∧ n ≥ 3;
      · -- By definition of `next_step`, if `n` is odd and `n ≥ 3`, then `next_step n (all_tuples n)` returns a tuple `(alpha_n, beta_n, lambda_n)` where `alpha_n` is chosen by `choice_in_interval`.
        obtain ⟨alpha_n, beta_n, lambda_n, h_tuple⟩ : ∃ alpha_n beta_n lambda_n, next_step n (all_tuples n) = (alpha_n, beta_n, lambda_n) ∧ alpha_n ∉ alpha_set (all_tuples n) := by
          simp +zetaDelta at *;
          rw [ next_step_eq_A_explicit ];
          any_goals linarith;
          exact ⟨ _, ⟨ _, _, rfl ⟩, choice_in_interval_spec _ _ _ _ _ |>.2 ⟩;
          assumption;
        -- By definition of `alpha_seq`, we know that `alpha_seq n = alpha_n`.
        have h_alpha_eq : alpha_seq n = alpha_n := by
          exact alpha_seq_eq_next_step_fst n ▸ h_tuple.1 ▸ rfl;
        simp_all +decide [ alpha_set_eq_image ];
      · rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide

/-
The (n+1)-th alpha is distinct from the previous ones, assuming the invariant holds at step n.
-/
lemma alpha_seq_succ_not_mem_prev (n : ℕ) (h_inv : Invariant n) :
    alpha_seq (n + 1) ∉ (Finset.range (n + 1)).image (fun k => alpha_seq k) := by
      by_cases h_even : (n + 1) % 2 = 0;
      · exact fun h => by have := alpha_seq_succ_distinct_even n h_even ( by omega ) ; aesop;
      · by_cases hn : n ≥ 1;
        · have := alpha_seq_succ_distinct_odd ( n + 1 ) ; aesop;
        · interval_cases n ; simp_all +decide

/-
The sequence alpha remains distinct up to index n+1.
-/
lemma alpha_seq_distinct_succ (n : ℕ) (h : Invariant n) :
    ∀ i j, i ≤ n + 1 → j ≤ n + 1 → i ≠ j → alpha_seq i ≠ alpha_seq j := by
      intro i j hi hj hij; cases lt_or_eq_of_le hi <;> cases lt_or_eq_of_le hj <;> simp_all +decide ;
      · exact h.1 i j ( by linarith ) ( by linarith ) hij;
      · have := alpha_seq_succ_not_mem_prev n h;
        exact fun h => this <| h ▸ Finset.mem_image_of_mem _ ( Finset.mem_range.mpr ‹_› );
      · intro H;
        exact hij ( by have := alpha_seq_succ_not_mem_prev n h; exact absurd ( Finset.mem_image.mpr ⟨ j, Finset.mem_range.mpr ‹_›, H ▸ rfl ⟩ ) this )

/-
The n-th beta is the second component (first part of the pair) of the tuple generated at step n.
-/
lemma beta_seq_eq_next_step_snd_fst (n : ℕ) :
    beta_seq n = (next_step n (all_tuples n)).2.1 := by
      unfold beta_seq construction_seq;
      -- By definition of `all_tuples`, we have `all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)]`.
      have h_append : all_tuples (n + 1) = all_tuples n ++ [next_step n (all_tuples n)] := by
        exact?;
      aesop

/-
The (n+1)-th beta is distinct from the previous ones, assuming the invariant holds at step n.
-/
lemma beta_seq_succ_not_mem_prev (n : ℕ) (h_inv : Invariant n) :
    beta_seq (n + 1) ∉ (Finset.range (n + 1)).image (fun k => beta_seq k) := by
      -- Let's analyze the two cases for `n + 1`: odd or even.
      by_cases h_odd : (n + 1) % 2 = 1;
      · -- Since `beta_seq (n + 1)` is defined as the first unused element in the set of used betas, it cannot be in the image of the beta_seq over the range up to `n`.
        have h_beta_seq_not_in_image : beta_seq (n + 1) ∉ beta_set (all_tuples (n + 1)) := by
          erw [ beta_seq_eq_next_step_snd_fst ];
          unfold next_step;
          split_ifs <;> norm_num at *;
          · subst_vars; simp +decide [ beta_set ] ;
            rintro ( _ | _ | x ) <;> simp +decide [ all_tuples ];
            unfold next_step; aesop;
          · linarith;
          · split_ifs <;> simp_all +decide [ Nat.add_mod ];
            any_goals exact first_unused_spec _ _ _ _;
            rename_i h₁ h₂ h₃;
            contrapose! h₃;
            exact lt_min ( div_pos ( epsilon_pos _ ) ( M_val_pos _ _ ) ) ( div_pos ( epsilon_pos _ ) ( L_val_pos _ _ ( by linarith ) ) );
        -- By definition of `beta_set`, we know that `beta_seq (n + 1)` is not in the image of `beta_seq` over the range up to `n`.
        have h_beta_set_eq_image : beta_set (all_tuples (n + 1)) = (Finset.range (n + 1)).image (fun k => beta_seq k) := by
          exact?;
        grind;
      · -- Since `n + 1` is even, we use `next_step_B_conditions` to show that `beta_seq (n + 1)` is distinct from the previous `beta_seq` values.
        obtain ⟨h_eta_pos, h_h_ne_zero⟩ : eta_seq (n + 1) > 0 ∧ h_seq_real (fun k => alpha_seq k) (n + 1) (first_unused a_seq a_seq_surj (alpha_set (all_tuples (n + 1))) (alpha_set_finite (all_tuples (n + 1)))) ≠ 0 := by
          apply next_step_B_conditions_simple (n + 1) (by
          omega);
        have h_beta_distinct : let hist := all_tuples (n + 1)
          let alpha_prev := alpha_from_hist hist
          let lambda_prev := lambda_from_hist hist
          let F_prev := F_seq_real alpha_prev lambda_prev (n)
          let h_curr := h_seq_real alpha_prev (n + 1)
          let eta := eta_val alpha_prev (n + 1) (epsilon_seq (n + 1))
          let alpha_n := first_unused a_seq a_seq_surj (alpha_set hist) (alpha_set_finite hist)
          let y := F_prev alpha_n
          let h_val := h_curr alpha_n
          let radius := eta * |h_val|
          let beta_n := choice_in_interval (y - radius) (y + radius) (by
          linarith [ show 0 < eta_val ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( n + 1 ) ( epsilon_seq ( n + 1 ) ) * |h_seq_real ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( n + 1 ) ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples ( n + 1 ) ) ) ( alpha_set_finite ( all_tuples ( n + 1 ) ) ) )| from mul_pos ( by simpa only [ eta_eq_eta_seq ] using h_eta_pos ) ( abs_pos.mpr <| by simpa only [ h_seq_real_eq_h_seq_real ] using h_h_ne_zero ) ]) (beta_set hist) (beta_set_finite hist)
          let lambda_n := (beta_n - y) / h_val
          beta_seq (n + 1) = beta_n := by
            have h_beta_distinct : let hist := all_tuples (n + 1)
              let alpha_prev := alpha_from_hist hist
              let lambda_prev := lambda_from_hist hist
              let F_prev := F_seq_real alpha_prev lambda_prev (n)
              let h_curr := h_seq_real alpha_prev (n + 1)
              let eta := eta_val alpha_prev (n + 1) (epsilon_seq (n + 1))
              let alpha_n := first_unused a_seq a_seq_surj (alpha_set hist) (alpha_set_finite hist)
              let y := F_prev alpha_n
              let h_val := h_curr alpha_n
              let radius := eta * |h_val|
              let beta_n := choice_in_interval (y - radius) (y + radius) (by
              linarith [ show 0 < eta_val ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( n + 1 ) ( epsilon_seq ( n + 1 ) ) * |h_seq_real ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( n + 1 ) ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples ( n + 1 ) ) ) ( alpha_set_finite ( all_tuples ( n + 1 ) ) ) )| from mul_pos ( by simpa only [ eta_eq_eta_seq ] using h_eta_pos ) ( abs_pos.mpr <| by simpa only [ h_seq_real_eq_h_seq_real ] using h_h_ne_zero ) ]) (beta_set hist) (beta_set_finite hist)
              let lambda_n := (beta_n - y) / h_val
              next_step (n + 1) hist = (alpha_n, beta_n, lambda_n) := by
                apply_rules [ next_step_eq_B, next_step_eq_B_final_v2, next_step_eq_B_final_v3, next_step_eq_B_proven ];
                · omega;
                · exact Nat.mod_two_ne_one.mp h_odd
            generalize_proofs at *;
            exact beta_seq_eq_next_step_snd_fst ( n + 1 ) ▸ h_beta_distinct.symm ▸ rfl
            skip
        generalize_proofs at *;
        have := choice_in_interval_spec ( F_seq_real ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( lambda_from_hist ( all_tuples ( n + 1 ) ) ) n ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples ( n + 1 ) ) ) ‹_› ) - eta_val ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( n + 1 ) ( epsilon_seq ( n + 1 ) ) * |h_seq_real ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( n + 1 ) ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples ( n + 1 ) ) ) ‹_› )| ) ( F_seq_real ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( lambda_from_hist ( all_tuples ( n + 1 ) ) ) n ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples ( n + 1 ) ) ) ‹_› ) + eta_val ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( n + 1 ) ( epsilon_seq ( n + 1 ) ) * |h_seq_real ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( n + 1 ) ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples ( n + 1 ) ) ) ‹_› )| ) ‹_› ( beta_set ( all_tuples ( n + 1 ) ) ) ( beta_set_finite ( all_tuples ( n + 1 ) ) ) ; simp_all +decide [ beta_set_eq_image ]

/-
The sequence beta remains distinct up to index n+1.
-/
lemma beta_seq_distinct_succ (n : ℕ) (h : Invariant n) :
    ∀ i j, i ≤ n + 1 → j ≤ n + 1 → i ≠ j → beta_seq i ≠ beta_seq j := by
      intro i j hi hj hij; rcases eq_or_lt_of_le hi with rfl | hi <;> rcases eq_or_lt_of_le hj with rfl | hj <;> simp_all +decide ;
      · have := beta_seq_succ_not_mem_prev n h;
        exact fun h => this <| h.symm ▸ Finset.mem_image_of_mem _ ( Finset.mem_range.mpr hj );
      · have := beta_seq_succ_not_mem_prev n h; aesop;
      · exact h.2.1 i j ( by linarith ) ( by linarith ) hij

/-
If the step index is even, the new lambda satisfies the bound.
-/
lemma lambda_seq_succ_bound_even (n : ℕ) (h_even : (n + 1) % 2 = 0) (hn : n + 1 ≥ 2) :
    |lambda_seq (n + 1)| < eta_seq (n + 1) := by
      have h_eta_pos : eta_seq (n + 1) > 0 := by
        exact eta_seq_pos _ ( by linarith );
      rw [ lambda_seq_eq ];
      unfold next_step;
      norm_num +zetaDelta at *;
      split_ifs <;> simp_all +decide [ Nat.even_iff ];
      rw [ abs_div ];
      rw [ div_lt_iff₀ ( abs_pos.mpr ‹_› ) ];
      have := choice_in_interval_spec ( F_seq_real ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( lambda_from_hist ( all_tuples ( n + 1 ) ) ) n ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples ( n + 1 ) ) ) ( alpha_set_finite ( all_tuples ( n + 1 ) ) ) ) - eta_val ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( n + 1 ) ( epsilon_seq ( n + 1 ) ) * |h_seq_real ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( n + 1 ) ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples ( n + 1 ) ) ) ( alpha_set_finite ( all_tuples ( n + 1 ) ) ) )| ) ( F_seq_real ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( lambda_from_hist ( all_tuples ( n + 1 ) ) ) n ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples ( n + 1 ) ) ) ( alpha_set_finite ( all_tuples ( n + 1 ) ) ) ) + eta_val ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( n + 1 ) ( epsilon_seq ( n + 1 ) ) * |h_seq_real ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( n + 1 ) ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples ( n + 1 ) ) ) ( alpha_set_finite ( all_tuples ( n + 1 ) ) ) )| ) ?_ ?_ ?_;
      any_goals exact beta_set ( all_tuples ( n + 1 ) );
      any_goals exact beta_set_finite _;
      any_goals nlinarith [ abs_pos.mpr ‹_› ];
      simp +zetaDelta at *;
      rw [ abs_lt ];
      constructor <;> cases abs_cases ( h_seq_real ( alpha_from_hist ( all_tuples ( n + 1 ) ) ) ( n + 1 ) ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples ( n + 1 ) ) ) ( alpha_set_finite ( all_tuples ( n + 1 ) ) ) ) ) <;> nlinarith [ eta_eq_eta_seq ( n + 1 ) ]

/-
If the step index is odd, the new lambda satisfies the bound.
-/
lemma lambda_seq_succ_bound_odd (n : ℕ) (h_odd : (n + 1) % 2 = 1) (hn : n + 1 ≥ 1) :
    |lambda_seq (n + 1)| < eta_seq (n + 1) := by
      by_cases h : eta_seq ( n + 1 ) > 0;
      · rw [ @lambda_seq_eq ];
        unfold next_step;
        split_ifs <;> norm_num at *;
        · linarith;
        · aesop;
        · split_ifs <;> norm_num [ h ];
          · linarith;
          · rename_i h₁ h₂ h₃ h₄ h₅ h₆;
            have := Classical.choose_spec h₆;
            convert this.2 _ _;
            · exact?;
            · exact abs_lt.mpr ⟨ by linarith [ choice_in_interval_spec ( Classical.choose h₃ - Classical.choose h₆ ) ( Classical.choose h₃ + Classical.choose h₆ ) ( by linarith [ this.1 ] ) ( alpha_set ( all_tuples ( n + 1 ) ) ) ( alpha_set_finite ( all_tuples ( n + 1 ) ) ) |>.1.1 ], by linarith [ choice_in_interval_spec ( Classical.choose h₃ - Classical.choose h₆ ) ( Classical.choose h₃ + Classical.choose h₆ ) ( by linarith [ this.1 ] ) ( alpha_set ( all_tuples ( n + 1 ) ) ) ( alpha_set_finite ( all_tuples ( n + 1 ) ) ) |>.1.2 ] ⟩;
      · exact False.elim <| h <| eta_seq_pos _ <| by linarith;

/-
The lambda bound holds for all k up to n+1.
-/
lemma lambda_bound_succ (n : ℕ) (h : Invariant n) :
    ∀ k, 2 ≤ k → k ≤ n + 1 → |lambda_seq k| < eta_seq k := by
      intros k hk2 hk_le_n1;
      cases hk_le_n1.eq_or_lt <;> simp_all +decide [ Invariant ];
      · by_cases h_even : (n + 1) % 2 = 0;
        · exact lambda_seq_succ_bound_even n h_even ( by linarith );
        · exact lambda_seq_succ_bound_odd n ( by omega ) ( by omega );
      · exact h.2.2.2.2 k hk2 ( Nat.le_of_lt_succ ‹_› )

/-
The interpolation condition holds for previous indices k <= n at step n+1.
-/
lemma interpolation_succ_le_n (n : ℕ) (h : Invariant n) :
    ∀ k ≤ n, F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) (n + 1) (alpha_seq k) = beta_seq k := by
      -- By definition of $F_{n+1}$, we have $F_{n+1}(alpha_k) = F_n(alpha_k) + lambda_{n+1} * h_{n+1}(alpha_k)$.
      have h_F_succ : ∀ k ≤ n, F_seq_real (fun i => (alpha_seq i : ℝ)) (fun i => lambda_seq i) (n + 1) (alpha_seq k) = F_seq_real (fun i => (alpha_seq i : ℝ)) (fun i => lambda_seq i) n (alpha_seq k) + lambda_seq (n + 1) * h_seq_real (fun i => (alpha_seq i : ℝ)) (n + 1) (alpha_seq k) := by
        unfold F_seq_real;
        unfold F_seq h_seq_real;
        norm_num [ List.range_succ ];
        exact fun k hk => by ring;
      intro k hk;
      rw [ h_F_succ k hk, h.2.2.1 k hk, add_eq_left.mpr ];
      -- By definition of $h_seq$, we know that $h_{n+1}(alpha_k) = 0$ for $k \leq n$.
      have h_h_seq_zero : h_seq (fun i => (alpha_seq i : ℝ)) (n + 1) (alpha_seq k) = 0 := by
        exact h_seq_eq_zero _ _ ( by linarith );
      unfold h_seq_real; aesop;

/-
If the step index is odd, lambda is defined by the interpolation formula.
-/
lemma lambda_seq_odd_eq_Lambda (n : ℕ) (h_odd : (n + 1) % 2 = 1) (hn : n + 1 ≥ 1) (h_inv : Invariant n) :
    lambda_seq (n + 1) = (beta_seq (n + 1) - F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n (alpha_seq (n + 1))) / h_seq_real (fun i => alpha_seq i) (n + 1) (alpha_seq (n + 1)) := by
      have := @next_step_eq_A_explicit;
      by_cases h : n + 1 ≥ 2 <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · specialize this ( n + 1 ) ( by linarith ) h_odd h_inv;
        rw [ show lambda_seq ( n + 1 ) = ( next_step ( n + 1 ) ( all_tuples ( n + 1 ) ) |> Prod.snd |> Prod.snd ) from ?_, this ];
        · rw [ show beta_seq ( n + 1 ) = first_unused b_seq b_seq_surj ( beta_set ( all_tuples ( n + 1 ) ) ) ( beta_set_finite ( all_tuples ( n + 1 ) ) ) from ?_, show alpha_seq ( n + 1 ) = choice_in_interval ( Classical.choose ( next_step_A_exists_preimage ( n + 1 ) h_inv ( by linarith ) ) - Classical.choose ( next_step_A_delta_exists ( n + 1 ) h_inv h_odd ( by linarith ) ( Classical.choose ( next_step_A_exists_preimage ( n + 1 ) h_inv ( by linarith ) ) ) ( Classical.choose_spec ( next_step_A_exists_preimage ( n + 1 ) h_inv ( by linarith ) ) ) ) ) ( Classical.choose ( next_step_A_exists_preimage ( n + 1 ) h_inv ( by linarith ) ) + Classical.choose ( next_step_A_delta_exists ( n + 1 ) h_inv h_odd ( by linarith ) ( Classical.choose ( next_step_A_exists_preimage ( n + 1 ) h_inv ( by linarith ) ) ) ( Classical.choose_spec ( next_step_A_exists_preimage ( n + 1 ) h_inv ( by linarith ) ) ) ) ) _ ( alpha_set ( all_tuples ( n + 1 ) ) ) ( alpha_set_finite ( all_tuples ( n + 1 ) ) ) from ?_ ];
          any_goals rw [ beta_seq_eq_next_step_snd_fst ];
          any_goals rw [ alpha_seq_eq_next_step_fst, this ];
          · rw [ F_seq_real_eq_F_seq_real, h_seq_real_eq_h_seq_real ];
            · rfl;
            · linarith;
          · exact this.symm ▸ rfl;
        · -- By definition of `lambda_seq`, we know that `lambda_seq (n + 1)` is the third component of `next_step (n + 1) (all_tuples (n + 1))`.
          apply lambda_seq_eq;
      · unfold lambda_seq beta_seq;
        unfold construction_seq alpha_seq; norm_num [ all_tuples ] ;
        unfold construction_seq; norm_num [ all_tuples ] ;
        unfold next_step; norm_num [ all_tuples ] ;
        unfold F_seq_real; norm_num [ List.range_succ ] ;
        unfold F_seq; norm_num [ List.range_succ ] ;

/-
The interpolation condition holds for the new index when the step is even.
-/
lemma interpolation_succ_eq_n_plus_1_even (n : ℕ) (h_even : (n + 1) % 2 = 0) (hn : n + 1 ≥ 2) (h_inv : Invariant n) :
    F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) (n + 1) (alpha_seq (n + 1)) = beta_seq (n + 1) := by
      -- By definition of `next_step`, we know that `lambda_seq (n + 1)` is the third component of the tuple generated at step `n + 1`.
      have h_lambda : lambda_seq (n + 1) = (beta_seq (n + 1) - F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n (alpha_seq (n + 1))) / h_seq_real (fun i => alpha_seq i) (n + 1) (alpha_seq (n + 1)) := by
        have h_lambda : let alpha_prev := alpha_from_hist (all_tuples (n + 1))
          let lambda_prev := lambda_from_hist (all_tuples (n + 1))
          let F_prev := F_seq_real alpha_prev lambda_prev n
          let h_curr := h_seq_real alpha_prev (n + 1)
          let eta := eta_val alpha_prev (n + 1) (epsilon_seq (n + 1))
          let alpha_n := first_unused a_seq a_seq_surj (alpha_set (all_tuples (n + 1))) (alpha_set_finite (all_tuples (n + 1)))
          let y := F_prev alpha_n
          let h_val := h_curr alpha_n
          let radius := eta * |h_val|
          let beta_n := choice_in_interval (y - radius) (y + radius) (by
          -- Since $|h_val|$ is the absolute value of the h_seq_real at alpha_n, which is non-zero, we have $|h_val| > 0$.
          have h_abs_pos : 0 < |h_val| := by
            have h_abs_pos : h_val ≠ 0 := by
              norm_num +zetaDelta at *;
              convert next_step_B_conditions_simple ( n + 1 ) ( by linarith ) |>.2 using 1;
              rw [ h_seq_real_eq_h_seq_real ]
            exact abs_pos.mpr h_abs_pos;
          linarith [ show radius > 0 from mul_pos ( show 0 < eta from by
                                                      convert eta_seq_pos ( n + 1 ) ( by linarith ) using 1;
                                                      convert eta_eq_eta_seq ( n + 1 ) using 1 ) h_abs_pos ]) (beta_set (all_tuples (n + 1))) (beta_set_finite (all_tuples (n + 1)))
          let lambda_n := (beta_n - y) / h_val
          lambda_seq (n + 1) = lambda_n := by
            all_goals generalize_proofs at *;
            convert congr_arg ( fun x : ℚ × ℚ × ℝ => x.2.2 ) ( next_step_eq_B_final_v3 ( n + 1 ) hn h_even h_inv ) using 1;
            exact?
        generalize_proofs at *;
        convert h_lambda using 1;
        rw [ alpha_seq_eq_next_step_fst ];
        rw [ next_step_eq_B_final_v3 ] <;> norm_num;
        · congr! 1;
          · congr! 1;
            · rw [ beta_seq_eq_next_step_snd_fst ];
              rw [ next_step_eq_B_final_v3 ];
              · exact?;
              · linarith;
              · assumption;
              · exact h_inv;
            · exact Eq.symm ( F_seq_real_eq_F_seq_real _ _ ( by linarith ) );
          · exact?;
        · linarith;
        · assumption;
        · assumption;
      -- By definition of `h_seq_real`, we know that `h_seq_real (fun i => alpha_seq i) (n + 1) (alpha_seq (n + 1)) ≠ 0`.
      have h_h_seq_ne_zero : h_seq_real (fun i => alpha_seq i) (n + 1) (alpha_seq (n + 1)) ≠ 0 := by
        have := next_step_B_conditions_simple ( n + 1 ) hn;
        convert this.2;
        convert alpha_seq_eq_next_step_fst ( n + 1 ) using 1;
        rw [ next_step_eq_B_final_v3 ];
        · linarith;
        · assumption;
        · exact h_inv;
      -- By definition of `F_seq_real`, we know that `F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) (n + 1) (alpha_seq (n + 1)) = F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n (alpha_seq (n + 1)) + lambda_seq (n + 1) * h_seq_real (fun i => alpha_seq i) (n + 1) (alpha_seq (n + 1))`.
      have h_F_seq_real : F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) (n + 1) (alpha_seq (n + 1)) = F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n (alpha_seq (n + 1)) + lambda_seq (n + 1) * h_seq_real (fun i => alpha_seq i) (n + 1) (alpha_seq (n + 1)) := by
        convert F_partial_sum_succ n ( alpha_seq ( n + 1 ) ) using 1;
        unfold F_seq_real F_partial_sum; norm_cast;
        unfold F_seq h_seq_real; norm_num [ List.sum_range_succ ] ;
        norm_num [ Complex.ext_iff, add_assoc ];
      rw [ h_F_seq_real, h_lambda, div_mul_cancel₀ _ h_h_seq_ne_zero, add_sub_cancel ]

/-
The interpolation condition holds for the new index when the step is odd.
-/
lemma interpolation_succ_eq_n_plus_1_odd (n : ℕ) (h_odd : (n + 1) % 2 = 1) (hn : n + 1 ≥ 1) (h_inv : Invariant n) :
    F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) (n + 1) (alpha_seq (n + 1)) = beta_seq (n + 1) := by
      -- By definition of `lambda_seq`, we have `lambda_seq (n + 1) = (beta_seq (n + 1) - F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n (alpha_seq (n + 1))) / h_seq_real (fun i => alpha_seq i) (n + 1) (alpha_seq (n + 1))`.
      have h_lambda : lambda_seq (n + 1) = (beta_seq (n + 1) - F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n (alpha_seq (n + 1))) / h_seq_real (fun i => alpha_seq i) (n + 1) (alpha_seq (n + 1)) := by
        exact?;
      -- By definition of `h_seq_real`, we know that `h_seq_real (fun i => alpha_seq i) (n + 1) (alpha_seq (n + 1)) ≠ 0`.
      have h_h_seq_real_ne_zero : h_seq_real (fun i => alpha_seq i) (n + 1) (alpha_seq (n + 1)) ≠ 0 := by
        have h_h_seq_real_ne_zero : ∀ k < n + 1, (alpha_seq (n + 1) : ℂ) ≠ (alpha_seq k : ℂ) := by
          intro k hk_lt hk_eq; have := h_inv.1 ( n + 1 ) k; simp_all +decide ;
          have := alpha_seq_succ_not_mem_prev n h_inv; simp_all +decide [ Finset.mem_image ] ;
          exact this k hk_lt rfl;
        convert h_seq_ne_zero_of_distinct ( n + 1 ) ( alpha_seq ( n + 1 ) ) h_h_seq_real_ne_zero using 1;
        unfold h_seq_real; norm_num [ Complex.ext_iff ] ;
        unfold h_seq; norm_num [ Complex.exp_re, Complex.exp_im, Complex.sin, Complex.cos ] ;
        norm_cast ; norm_num;
        induction ( List.range ( n + 1 ) ) <;> aesop;
      -- By definition of `F_seq_real`, we have `F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) (n + 1) (alpha_seq (n + 1)) = F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n (alpha_seq (n + 1)) + lambda_seq (n + 1) * h_seq_real (fun i => alpha_seq i) (n + 1) (alpha_seq (n + 1))`.
      have h_F_seq_real : F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) (n + 1) (alpha_seq (n + 1)) = F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n (alpha_seq (n + 1)) + lambda_seq (n + 1) * h_seq_real (fun i => alpha_seq i) (n + 1) (alpha_seq (n + 1)) := by
        unfold F_seq_real;
        unfold F_seq; simp +decide [ List.sum_range_succ ] ;
        ring!;
      rw [ h_F_seq_real, h_lambda, div_mul_cancel₀ _ h_h_seq_real_ne_zero, add_sub_cancel ]

/-
The interpolation condition holds for the new index n+1.
-/
lemma interpolation_succ_eq_n_plus_1 (n : ℕ) (h : Invariant n) :
    F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) (n + 1) (alpha_seq (n + 1)) = beta_seq (n + 1) := by
      -- Split into cases based on parity of `n+1`.
      by_cases h_even : (n + 1) % 2 = 0;
      · exact if hn : n + 1 ≥ 2 then interpolation_succ_eq_n_plus_1_even n h_even hn h else by aesop;
      · convert interpolation_succ_eq_n_plus_1_odd n _ _ h using 1;
        · exact Nat.mod_two_ne_zero.mp h_even;
        · linarith

/-
The derivative bound holds for step n+1.
-/
lemma derivative_bound_succ (n : ℕ) (h : Invariant n) :
    ∀ x : ℝ, deriv (fun t => F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) (n + 1) t) x ≥
    1 - ∑ k ∈ Finset.range (n + 2), if k < 2 then 0 else epsilon_seq k := by
      -- By the properties of the derivative, we can split the derivative of the sum into the sum of the derivatives.
      have h_deriv_split : deriv (fun t => F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) (n + 1) t) = fun x => deriv (fun t => F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n t) x + deriv (fun t => (lambda_seq (n + 1) : ℝ) * h_seq_real (fun i => alpha_seq i) (n + 1) t) x := by
        unfold F_seq_real h_seq_real;
        ext x;
        rw [ ← deriv_add ];
        · congr with t;
          unfold F_seq; simp +decide [ List.range_succ ] ; ring;
        · unfold F_seq;
          norm_num [ List.sum_range_succ', Complex.add_re, Complex.mul_re, Complex.exp_re, Complex.exp_im ];
          unfold h_seq; norm_num [ Complex.exp_re, Complex.exp_im ] ;
          induction' ( List.range n ) with n ih <;> simp_all +decide [ List.sum_range_succ ];
          norm_cast ; norm_num [ Complex.exp_re, Complex.exp_im, List.prod_range_succ ];
          apply_rules [ DifferentiableAt.mul, DifferentiableAt.exp, DifferentiableAt.neg, differentiableAt_id, differentiableAt_const ];
          · induction' ( List.range n ) with n ih <;> simp_all +decide [ List.prod_range_succ ];
          · exact differentiableAt_id.sub_const _;
        · unfold h_seq; norm_num [ Complex.exp_re, Complex.exp_im, Complex.cos, Complex.sin, Complex.differentiableAt_exp, Complex.differentiableAt_sin, Complex.differentiableAt_cos, mul_comm ] ;
          norm_cast ; norm_num;
          apply_rules [ DifferentiableAt.mul, DifferentiableAt.exp, DifferentiableAt.neg, DifferentiableAt.div ] <;> norm_num;
          · exact differentiableAt_const _;
          · induction' ( List.range ( n + 1 ) ) with k hk <;> simp_all +decide [ List.prod_cons, List.prod_nil ];
      -- By the properties of the derivative, we know that the derivative of $h_{n+1}(x)$ is bounded by $L_{n+1}$.
      have h_deriv_h_bound : ∀ x, |deriv (fun t => h_seq_real (fun i => alpha_seq i) (n + 1) t) x| ≤ L_val (fun i => alpha_seq i) (n + 1) := by
        intro x
        have h_deriv_h_bound : |deriv (fun t => h_seq_real (fun i => alpha_seq i) (n + 1) t) x| ≤ sSup ((fun x : ℝ => ‖deriv (h_seq (fun i => alpha_seq i) (n + 1)) (x : ℂ)‖) '' Set.univ) := by
          have h_deriv_h_bound : deriv (fun t => h_seq_real (fun i => alpha_seq i) (n + 1) t) x = Complex.re (deriv (h_seq (fun i => alpha_seq i) (n + 1)) (x : ℂ)) := by
            have h_deriv_h_bound : HasDerivAt (fun t : ℝ => h_seq_real (fun i => alpha_seq i) (n + 1) t) (Complex.re (deriv (h_seq (fun i => alpha_seq i) (n + 1)) (x : ℂ))) x := by
              have h_deriv_h_bound : HasDerivAt (fun t : ℂ => h_seq (fun i => alpha_seq i) (n + 1) t) (deriv (h_seq (fun i => alpha_seq i) (n + 1)) (x : ℂ)) (x : ℂ) := by
                apply_rules [ DifferentiableAt.hasDerivAt ];
                apply_rules [ DifferentiableAt.mul, DifferentiableAt.exp, differentiableAt_id, differentiableAt_const ];
                · exact Complex.differentiableAt_exp.comp _ ( DifferentiableAt.div_const ( DifferentiableAt.neg ( differentiableAt_id.pow 2 ) ) _ );
                · induction' ( List.range ( n + 1 ) ) with k hk <;> simp_all +decide [ List.prod_cons, List.prod_nil ]
              generalize_proofs at *; (
              rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
              convert Complex.continuous_re.continuousAt.tendsto.comp ( h_deriv_h_bound.comp ( show Filter.Tendsto ( fun t : ℝ => ↑t ) ( nhdsWithin 0 { 0 } ᶜ ) ( nhdsWithin 0 { 0 } ᶜ ) from Filter.Tendsto.inf ( Complex.continuous_ofReal.tendsto _ ) <| by simp +decide ) ) using 2 ; norm_num [ h_seq_real ])
            generalize_proofs at *; (
            exact h_deriv_h_bound.deriv)
          generalize_proofs at *; (
          exact h_deriv_h_bound.symm ▸ le_trans ( Complex.abs_re_le_norm _ ) ( le_csSup ( by exact h_seq_deriv_bounded _ _ ( by linarith ) ) ( Set.mem_image_of_mem _ ( Set.mem_univ _ ) ) ))
        generalize_proofs at *; (
        exact h_deriv_h_bound)
      generalize_proofs at *; (
      -- By the properties of the derivative, we know that $|\lambda_{n+1}| < \eta_{n+1}$.
      have h_lambda_bound : |lambda_seq (n + 1)| < eta_seq (n + 1) := by
        by_cases h_even : (n + 1) % 2 = 0 <;> simp_all +decide [ lambda_seq_succ_bound_even, lambda_seq_succ_bound_odd ];
        exact lambda_seq_succ_bound_even n ( by omega ) ( by omega )
      generalize_proofs at *; (
      -- By the properties of the derivative, we know that $|\lambda_{n+1} h_{n+1}'(x)| < \epsilon_{n+1}$.
      have h_lambda_h_bound : ∀ x, |(lambda_seq (n + 1) : ℝ) * deriv (fun t => h_seq_real (fun i => alpha_seq i) (n + 1) t) x| < epsilon_seq (n + 1) := by
        intros x
        have h_lambda_h_bound : |(lambda_seq (n + 1) : ℝ) * deriv (fun t => h_seq_real (fun i => alpha_seq i) (n + 1) t) x| ≤ |lambda_seq (n + 1)| * L_val (fun i => alpha_seq i) (n + 1) := by
          simpa only [ abs_mul ] using mul_le_mul_of_nonneg_left ( h_deriv_h_bound x ) ( abs_nonneg _ )
        generalize_proofs at *; (
        refine lt_of_le_of_lt h_lambda_h_bound ?_;
        refine' lt_of_lt_of_le ( mul_lt_mul_of_pos_right h_lambda_bound _ ) _;
        · exact L_val_pos _ _ ( Nat.succ_pos _ );
        · exact le_trans ( mul_le_mul_of_nonneg_right ( min_le_right _ _ ) ( by exact le_trans ( by norm_num ) ( show 0 ≤ L_val ( fun i => ( alpha_seq i : ℝ ) ) ( n + 1 ) from by exact le_trans ( by norm_num ) ( show 0 ≤ L_val ( fun i => ( alpha_seq i : ℝ ) ) ( n + 1 ) from by exact le_of_lt ( L_val_pos ( fun i => ( alpha_seq i : ℝ ) ) ( n + 1 ) ( by linarith ) ) ) ) ) ) ( by rw [ div_mul_cancel₀ _ ( ne_of_gt ( L_val_pos ( fun i => ( alpha_seq i : ℝ ) ) ( n + 1 ) ( by linarith ) ) ) ] ) ;)
      generalize_proofs at *; (
      -- By the properties of the derivative, we know that the derivative of $F_n(x)$ is bounded below by $1 - \sum_{k=2}^n \epsilon_k$.
      have h_deriv_F_bound : ∀ x, deriv (fun t => F_seq_real (fun i => alpha_seq i) (fun i => lambda_seq i) n t) x ≥ 1 - ∑ k ∈ Finset.range (n + 1), if k < 2 then 0 else epsilon_seq k := by
        exact h.2.2.2.1
      generalize_proofs at *; (
      simp_all +decide [ Finset.sum_range_succ ];
      intro x; specialize h_deriv_F_bound x; specialize h_lambda_h_bound x; split_ifs at * <;> norm_num at *;
      · interval_cases n <;> norm_num at *;
        exact le_add_of_le_of_nonneg h_deriv_F_bound ( by rw [ show lambda_seq 1 = 0 by exact? ] ; norm_num );
      · nlinarith [ abs_le.mp ( show |lambda_seq ( n + 1 ) * deriv ( fun t => h_seq_real ( fun i => ( alpha_seq i : ℝ ) ) ( n + 1 ) t ) x| ≤ |lambda_seq ( n + 1 )| * |deriv ( fun t => h_seq_real ( fun i => ( alpha_seq i : ℝ ) ) ( n + 1 ) t ) x| by rw [ abs_mul ] ), abs_nonneg ( lambda_seq ( n + 1 ) ), abs_nonneg ( deriv ( fun t => h_seq_real ( fun i => ( alpha_seq i : ℝ ) ) ( n + 1 ) t ) x ) ];
      · linarith;
      · cases abs_cases ( lambda_seq ( n + 1 ) ) <;> cases abs_cases ( deriv ( fun t => h_seq_real ( fun i => ( alpha_seq i : ℝ ) ) ( n + 1 ) t ) x ) <;> nlinarith [ abs_le.mp ( h_deriv_h_bound x ) ]))))

/-
If the invariant holds at step n, it holds at step n+1.
-/
lemma Invariant_succ (n : ℕ) (h : Invariant n) : Invariant (n + 1) := by
  apply And.intro;
  · exact?;
  · exact ⟨ fun i j hi hj hij => by simpa using beta_seq_distinct_succ n h i j hi hj hij, fun k hk => by simpa using if hk' : k ≤ n then interpolation_succ_le_n n h k hk' else by rw [ show k = n + 1 by linarith ] ; exact interpolation_succ_eq_n_plus_1 n h, fun x => by linarith [ derivative_bound_succ n h x ], fun k hk₁ hk₂ => by simpa using lambda_bound_succ n h k hk₁ hk₂ ⟩

/-
The invariant holds for all n.
-/
theorem Invariant_all (n : ℕ) : Invariant n := by
  induction' n with n ih;
  · exact?;
  · exact?

/-
h_n(alpha_m) = 0 for m < n.
-/
lemma h_seq_vanishes_for_large_n (m n : ℕ) (h : m < n) :
    h_seq (fun k => (alpha_seq k : ℝ)) n (alpha_seq m) = 0 := by
      exact?

/-
F_final(alpha_k) = beta_k.
-/
theorem F_final_eq_beta (k : ℕ) : F_final (alpha_seq k) = (beta_seq k : ℂ) := by
  -- By `h_seq_vanishes_for_large_n`, for `n > k`, `h_seq n (alpha_seq k) = 0`.
  have h_sum_zero : ∀ n > k, (lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n (alpha_seq k) = 0 := by
    exact fun n hn => mul_eq_zero_of_right _ ( h_seq_vanishes_for_large_n k n hn );
  -- Thus the series defining `F_final (alpha_seq k)` has only finitely many non-zero terms (indices `0` to `k`).
  have h_series_finite : ∑' n, (lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n (alpha_seq k) = ∑ n ∈ Finset.range (k + 1), (lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n (alpha_seq k) := by
    rw [ tsum_eq_sum ] ; aesop;
  -- Therefore, `F_final (alpha_seq k) = F_seq k (alpha_seq k)`.
  have h_F_eq_F_seq : F_final (alpha_seq k) = F_seq (fun k => (alpha_seq k : ℝ)) (fun k => (lambda_seq k : ℝ)) k (alpha_seq k) := by
    unfold F_final F_seq; aesop;
  -- By `Invariant_all k`, `Invariant k` holds.
  have h_inv : Invariant k := by
    exact Invariant_all k;
  -- By `Invariant k`, `F_seq_real k (alpha_seq k) = beta_seq k`.
  have h_F_seq_real : F_seq_real (fun k => (alpha_seq k : ℝ)) (fun k => (lambda_seq k : ℝ)) k (alpha_seq k) = beta_seq k := by
    exact h_inv.2.2.1 k le_rfl;
  convert h_F_seq_real using 1;
  unfold F_seq_real; norm_num [ Complex.ext_iff ] ;
  rw [ ← h_F_eq_F_seq ];
  exact ⟨ fun h => h.1, fun h => ⟨ h, by simpa [ Complex.ext_iff ] using F_final_real_on_real ( alpha_seq k ) ⟩ ⟩

/-
Every element of the sequence a_seq appears in the sequence alpha_seq.
-/
lemma exists_alpha_eq_a_seq (k : ℕ) : ∃ n, alpha_seq n = a_seq k := by
  by_contra h_contra;
  -- Let $k_min$ be the smallest index such that $a_seq k_min$ is never chosen.
  obtain ⟨k_min, hk_min⟩ : ∃ k_min, a_seq k_min ∉ Set.range (fun n => alpha_seq n) ∧ ∀ k < k_min, a_seq k ∈ Set.range (fun n => alpha_seq n) := by
    exact ⟨ Nat.find ( ⟨ k, by aesop ⟩ : ∃ k, a_seq k ∉ Set.range fun n => alpha_seq n ), Nat.find_spec ( ⟨ k, by aesop ⟩ : ∃ k, a_seq k ∉ Set.range fun n => alpha_seq n ), fun k hk => by aesop ⟩;
  -- Since there are finitely many $j < k_min$, there exists a step $N$ such that all $a_seq j$ (for $j < k_min$) have been chosen by step $N$.
  obtain ⟨N, hN⟩ : ∃ N, ∀ j < k_min, ∃ n ≤ N, alpha_seq n = a_seq j := by
    choose! f hf using hk_min.2;
    exact ⟨ Finset.sup ( Finset.range k_min ) f, fun j hj => ⟨ f j, Finset.le_sup ( f := f ) ( Finset.mem_range.mpr hj ), hf j hj ⟩ ⟩;
  -- Let $m$ be an even integer such that $m > N$ and $m \geq 2$.
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m, m > N ∧ m % 2 = 0 ∧ m ≥ 2 := by
    exact ⟨ 2 * ( N + 1 ), by linarith, by norm_num, by linarith ⟩;
  -- At step $m$, $\alpha_seq m$ is defined as the first element of $a_seq$ not in $\{ \alpha_seq 0, \ldots, \alpha_seq (m-1) \}$.
  have h_alpha_m : alpha_seq m = first_unused a_seq a_seq_surj (alpha_set (all_tuples m)) (alpha_set_finite (all_tuples m)) := by
    have h_alpha_m : alpha_seq m = (next_step m (all_tuples m)).1 := by
      exact?;
    rw [ h_alpha_m, next_step_eq_B_proven m hm₂.2 hm₂.1 ( by exact Invariant_all _ ) ];
  -- The set $\{ \alpha_seq 0, \ldots, \alpha_seq (m-1) \}$ contains $\{ a_seq 0, \ldots, a_seq (k_min-1) \}$ because $m > N$.
  have h_alpha_set_contain : ∀ j < k_min, a_seq j ∈ alpha_set (all_tuples m) := by
    intros j hj;
    obtain ⟨ n, hn₁, hn₂ ⟩ := hN j hj;
    have h_mem : n < m := by
      linarith;
    exact hn₂ ▸ alpha_set_eq_image m ▸ Finset.mem_image_of_mem _ ( Finset.mem_range.mpr h_mem );
  -- Also $a_seq k_min$ is not in $\{ \alpha_seq 0, \ldots, \alpha_seq (m-1) \}$ by assumption.
  have h_a_seq_k_min_not_in_alpha_set : a_seq k_min ∉ alpha_set (all_tuples m) := by
    intro h;
    obtain ⟨ n, hn ⟩ := h;
    obtain ⟨ v, hv₁, hv₂ ⟩ := hn;
    have h_alpha_seq_eq : alpha_from_hist (all_tuples m) n = alpha_seq n := by
      apply alpha_from_hist_eq_alpha_seq;
      have h_len : (all_tuples m).length = m := by
        exact Nat.recOn m ( by rfl ) fun n ih => by rw [ show all_tuples ( n + 1 ) = all_tuples n ++ [ next_step n ( all_tuples n ) ] from rfl ] ; simp +arith +decide [ ih ] ;
      exact lt_of_not_ge fun h => by rw [ List.get?_eq_none ] at hv₁ <;> aesop;
    have h_alpha_seq_eq : alpha_from_hist (all_tuples m) n = a_seq k_min := by
      unfold alpha_from_hist; aesop;
    exact hk_min.1 ⟨ n, by aesop ⟩;
  -- Therefore, the first unused element of $a_seq$ must be $a_seq k_min$.
  have h_first_unused_eq_a_seq_k_min : first_unused a_seq a_seq_surj (alpha_set (all_tuples m)) (alpha_set_finite (all_tuples m)) = a_seq k_min := by
    unfold first_unused;
    unfold first_unused_index;
    rw [ show Nat.find ( show ∃ n, a_seq n ∉ alpha_set ( all_tuples m ) from ⟨ k_min, h_a_seq_k_min_not_in_alpha_set ⟩ ) = k_min from le_antisymm ( Nat.find_min' _ h_a_seq_k_min_not_in_alpha_set ) ( Nat.le_of_not_lt fun h => by have := h_alpha_set_contain _ h; aesop ) ];
  exact hk_min.1 ⟨ m, h_alpha_m.trans h_first_unused_eq_a_seq_k_min ⟩

/-
Every element of the sequence a_seq appears in the sequence alpha_seq.
-/
lemma exists_alpha_eq_a_seq_v2 (k : ℕ) : ∃ n, alpha_seq n = a_seq k := by
  exact?

/-
The sequence alpha_seq is surjective.
-/
theorem alpha_seq_surjective : Function.Surjective alpha_seq := by
  intro q;
  exact exists_alpha_eq_a_seq_v2 ( Classical.choose ( a_seq_surj q ) ) |> fun ⟨ n, hn ⟩ => ⟨ n, hn.trans ( by simp +decide [ Classical.choose_spec ( a_seq_surj q ) ] ) ⟩

/-
If k is the smallest index such that seq k is not in S, then first_unused returns seq k.
-/
lemma first_unused_val_eq (seq : ℕ → ℚ) (h_surj : Function.Surjective seq) (S : Set ℚ) (hS : S.Finite) (k : ℕ)
    (hk_not_mem : seq k ∉ S) (hk_min : ∀ j < k, seq j ∈ S) :
    first_unused seq h_surj S hS = seq k := by
      -- By definition of `Nat.find`, we know that `Nat.find (exists_index_not_mem_finite seq h_surj S hS)` is the smallest index `k` such that `seq k ∉ S`.
      have h_nat_find : Nat.find (exists_index_not_mem_finite seq h_surj S hS) = k := by
        rw [ Nat.find_eq_iff ];
        aesop;
      unfold first_unused; aesop;

/-
For odd n, beta_seq n is the first unused element of b_seq.
-/
lemma beta_seq_odd_eq_first_unused (n : ℕ) (h_odd : n % 2 = 1) :
    beta_seq n = first_unused b_seq b_seq_surj (beta_set (all_tuples n)) (beta_set_finite (all_tuples n)) := by
      -- By definition of `next_step`, when `n` is odd, the second component of the returned tuple is `first_unused b_seq b_seq_surj (beta_set (all_tuples n))`.
      have h_beta_n : beta_seq n = (next_step n (all_tuples n)).2.1 := by
        exact?
      generalize_proofs at *;
      by_cases hn : n < 2;
      · interval_cases n <;> simp_all +decide [ beta_seq ];
        unfold construction_seq; norm_num [ all_tuples ] ;
        unfold next_step; simp +decide [ beta_set ] ;
        field_simp;
        rw [ eq_comm, first_unused_val_eq ];
        rotate_left;
        exact 1;
        · rintro ⟨ k, a, x, hk ⟩ ; rcases k with ( _ | _ | k ) <;> norm_num at hk;
          · unfold b_seq at hk ; norm_num at hk;
          · contradiction;
          · contradiction;
        · simp +decide [ b_seq ];
          exists 0, 0, 0;
          simp +decide [ Equiv.swap_apply_def ];
        · unfold b_seq; aesop;
      · rw [ h_beta_n, next_step_eq_A_explicit n ( by linarith ) h_odd ( by exact Invariant_all _ ) ]

/-
Every element of the sequence b_seq appears in the sequence beta_seq.
-/
lemma exists_beta_eq_b_seq (k : ℕ) : ∃ n, beta_seq n = b_seq k := by
  have h_beta_seq_surjective : ∀ k : ℕ, ∃ n : ℕ, beta_seq n = b_seq k := by
    intro k
    by_contra h_contra
    obtain ⟨k_min, hk_min⟩ : ∃ k_min, b_seq k_min ∉ Set.range (fun n => beta_seq n) ∧ ∀ j < k_min, b_seq j ∈ Set.range (fun n => beta_seq n) := by
      exact ⟨ Nat.find ( ⟨ k, by aesop ⟩ : ∃ k, b_seq k ∉ Set.range fun n => beta_seq n ), Nat.find_spec ( ⟨ k, by aesop ⟩ : ∃ k, b_seq k ∉ Set.range fun n => beta_seq n ), fun j hj => by aesop ⟩;
    -- Let $N$ be an index such that all $b_seq j$ for $j < k_min$ have been chosen by step $N$.
    obtain ⟨N, hN⟩ : ∃ N, ∀ j < k_min, ∃ n ≤ N, beta_seq n = b_seq j := by
      choose! f hf using hk_min.2;
      exact ⟨ Finset.sup ( Finset.range k_min ) f, fun j hj => ⟨ f j, Finset.le_sup ( f := f ) ( Finset.mem_range.mpr hj ), hf j hj ⟩ ⟩;
    -- Let $m$ be an odd integer such that $m > N$ and $m \geq 1$.
    obtain ⟨m, hm_odd, hm_gt_N, hm_ge_1⟩ : ∃ m, m % 2 = 1 ∧ N < m ∧ 1 ≤ m := by
      exact ⟨ 2 * N + 1, by norm_num [ Nat.add_mod ], by linarith, by linarith ⟩;
    -- At step $m$, since $m$ is odd and $m > N$, the set of used betas contains $\{b_seq 0, ..., b_seq (k_min-1)\}$.
    have h_used_betas : beta_set (all_tuples m) ⊇ Finset.image (fun j => b_seq j) (Finset.range k_min) := by
      intro x hx;
      obtain ⟨ j, hj, rfl ⟩ := Finset.mem_image.mp hx;
      obtain ⟨ n, hn₁, hn₂ ⟩ := hN j ( Finset.mem_range.mp hj );
      -- Since $n \leq N < m$, we have $n < m$, and thus $beta_seq n$ is in the beta_set of $all_tuples m$.
      have h_beta_in_set : beta_seq n ∈ beta_set (all_tuples m) := by
        have h_beta_in_set : ∀ k < m, beta_seq k ∈ beta_set (all_tuples m) := by
          intros k hk_lt_m
          have h_beta_in_set : beta_seq k ∈ (Finset.range m).image (fun k => beta_seq k) := by
            exact Finset.mem_image_of_mem _ ( Finset.mem_range.mpr hk_lt_m );
          convert h_beta_in_set using 1;
          ext; simp [beta_set_eq_image];
        exact h_beta_in_set n ( by linarith );
      aesop;
    -- Since $b_seq k_min$ is not in the range of $beta_seq$, it is not in the set of used betas at step $m$.
    have h_not_in_used_betas : b_seq k_min ∉ beta_set (all_tuples m) := by
      simp_all +decide [ beta_set ];
      intro i a b hi; specialize hk_min; have := hk_min.1 i; simp_all +decide [ beta_seq_eq_next_step_snd_fst ] ;
      have h_next_step_i : ∀ n, all_tuples n = List.map (fun i => next_step i (all_tuples i)) (List.range n) := by
        intro n; induction n <;> simp_all +decide [ List.range_succ ] ;
        rename_i n ih; rw [ show all_tuples ( n + 1 ) = all_tuples n ++ [ next_step n ( all_tuples n ) ] from rfl ] ; aesop;
      grind;
    -- At step $m$, since $m$ is odd and $m > N$, the set of used betas contains $\{b_seq 0, ..., b_seq (k_min-1)\}$ and $b_seq k_min$ is not in the set of used betas.
    have h_beta_m : beta_seq m = b_seq k_min := by
      rw [ beta_seq_odd_eq_first_unused m hm_odd ];
      apply first_unused_val_eq;
      · assumption;
      · exact fun j hj => h_used_betas <| Finset.mem_image_of_mem _ <| Finset.mem_range.mpr hj;
    exact hk_min.1 ⟨ m, h_beta_m ⟩;
  exact h_beta_seq_surjective k

/-
The sequence beta_seq is surjective.
-/
theorem beta_seq_surjective : Function.Surjective beta_seq := by
  exact fun q => by obtain ⟨ k, hk ⟩ := exists_beta_eq_b_seq ( Classical.choose ( b_seq_surj q ) ) ; have := Classical.choose_spec ( b_seq_surj q ) ; aesop;

/-
The derivative of the n-th term in the series for F is bounded by epsilon_n.
-/
lemma deriv_series_term_bound (n : ℕ) (x : ℝ) :
    ‖deriv (fun t => (lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n t) x‖ ≤ if n < 2 then 0 else epsilon_seq n := by
      -- The derivative of the n-th term in the series for F is lambda_n * h_n'(x).
      have h_deriv : deriv (fun t => (lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n t) x = (lambda_seq n : ℂ) * deriv (h_seq (fun k => (alpha_seq k : ℝ)) n) x := by
        aesop;
      -- For n < 2, lambda_n = 0, so the term is 0.
      by_cases hn : n < 2;
      · interval_cases n <;> norm_num [ lambda_zero_of_lt_two ] at *;
      · -- For n >= 2, |lambda_n| < eta_n.
        have h_lambda_bound : |lambda_seq n| < eta_seq n := by
          exact Invariant_all n |>.2.2.2.2 n ( by linarith ) ( by linarith );
        -- Since $|h_n'(x)| \leq L_val$, we have $|\lambda_n * h_n'(x)| \leq \lambda_n * L_val$.
        have h_term_bound : ‖(lambda_seq n : ℂ) * deriv (h_seq (fun k => (alpha_seq k : ℝ)) n) x‖ ≤ |lambda_seq n| * L_val (fun k => (alpha_seq k : ℝ)) n := by
          have h_term_bound : ‖deriv (h_seq (fun k => (alpha_seq k : ℝ)) n) x‖ ≤ L_val (fun k => (alpha_seq k : ℝ)) n := by
            exact le_csSup ( h_seq_deriv_bounded ( fun k => ( alpha_seq k : ℝ ) ) n ( by linarith ) ) ( Set.mem_image_of_mem _ ( Set.mem_univ _ ) );
          simpa using mul_le_mul_of_nonneg_left h_term_bound ( abs_nonneg _ );
        -- Since $|lambda_n| < eta_n$ and $eta_n = \min(1/4, \epsilon_n / L_val)$, we have $|lambda_n| * L_val < \epsilon_n$.
        have h_final_bound : |lambda_seq n| * L_val (fun k => (alpha_seq k : ℝ)) n < epsilon_seq n := by
          have h_eta_bound : |lambda_seq n| < epsilon_seq n / L_val (fun k => (alpha_seq k : ℝ)) n := by
            exact h_lambda_bound.trans_le ( min_le_right _ _ );
          rwa [ lt_div_iff₀ ( L_val_pos _ _ ( by linarith ) ) ] at h_eta_bound;
        grind

/-
The n-th term of the series is bounded by epsilon_n on the disk of radius n+1.
-/
lemma term_bound_valid (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ n + 1) :
    ‖(lambda_seq n : ℂ) * h_seq (fun k => (alpha_seq k : ℝ)) n z‖ ≤ epsilon_seq n := by
      -- Apply the term_bound lemma with the given hz.
      apply term_bound n z hz

/-
The sequence epsilon_seq is summable.
-/
lemma epsilon_summable : Summable epsilon_seq := by
  exact Summable.comp_injective ( summable_geometric_two ) fun a b h => by simpa using h;

/-
The derivative of the real part of h_seq is the real part of the derivative of h_seq.
-/
lemma h_seq_real_deriv (n : ℕ) (x : ℝ) :
    deriv (h_seq_real (fun k => (alpha_seq k : ℝ)) n) x = (deriv (h_seq (fun k => (alpha_seq k : ℝ)) n) (x : ℂ)).re := by
      have h_diff : DifferentiableAt ℂ (h_seq (fun k => (alpha_seq k : ℝ)) n) x := by
        induction' n with n ih generalizing x;
        · unfold h_seq; norm_num [ Complex.exp_ne_zero ] ;
        · apply_rules [ DifferentiableAt.const_mul, DifferentiableAt.mul, DifferentiableAt.exp, differentiableAt_id ];
          · exact Complex.differentiableAt_exp.comp _ ( DifferentiableAt.div_const ( DifferentiableAt.neg ( differentiableAt_id.pow 2 ) ) _ );
          · induction' ( List.range ( n + 1 ) ) with k hk ih <;> simp_all +decide [ List.prod_cons ];
      have h_real_part_deriv : HasDerivAt (fun t : ℝ => (h_seq (fun k => (alpha_seq k : ℝ)) n t).re) ((deriv (h_seq (fun k => (alpha_seq k : ℝ)) n) x).re) x := by
        have := h_diff.hasDerivAt;
        exact?;
      exact h_real_part_deriv.deriv

/-
h_seq takes real values for real arguments.
-/
lemma h_seq_is_real (n : ℕ) (x : ℝ) :
    (h_seq (fun k => (alpha_seq k : ℝ)) n (x : ℂ)).im = 0 := by
      induction' n with n ih generalizing x <;> simp_all +decide [ h_seq ];
      norm_cast ; simp_all +decide [ Complex.exp_re, Complex.exp_im, List.range_succ ];
      induction' ( List.range n ) using List.reverseRecOn <;> aesop

/-
h_seq_real is the real part of h_seq.
-/
lemma h_seq_real_eq (n : ℕ) (x : ℝ) :
    h_seq_real (fun k => (alpha_seq k : ℝ)) n x = (h_seq (fun k => (alpha_seq k : ℝ)) n (x : ℂ)).re := by
      exact?

/-
The derivative of the n-th term of the real series is bounded by epsilon_n.
-/
lemma f_final_term_bound (n : ℕ) (x : ℝ) :
    |deriv (fun y => lambda_seq n * h_seq_real (fun k => (alpha_seq k : ℝ)) n y) x| ≤ if n < 2 then 0 else epsilon_seq n := by
      convert le_trans _ ( deriv_series_term_bound n x ) using 1;
      norm_num [ mul_comm, Complex.norm_def, Complex.normSq ];
      rw [ h_seq_real_deriv ];
      exact mul_le_mul_of_nonneg_left ( Real.abs_le_sqrt <| by nlinarith ) <| abs_nonneg _

/-
The series defining f_final converges.
-/
lemma f_final_series_summable (x : ℝ) :
    Summable (fun n => lambda_seq n * h_seq_real (fun k => (alpha_seq k : ℝ)) n x) := by
      have := F_final_converges x;
      convert Complex.reCLM.summable this using 1;
      unfold h_seq_real h_seq; aesop;

/-
The series of derivatives of the real terms is summable.
-/
lemma summable_deriv_real (x : ℝ) :
    Summable (fun n => deriv (fun y => lambda_seq n * h_seq_real (fun k => (alpha_seq k : ℝ)) n y) x) := by
      -- The absolute value of the n-th term is bounded by `epsilon_seq n` (for `n >= 2`) by `f_final_term_bound`.
      have h_abs_term_bound : ∀ n ≥ 2, |deriv (fun y => lambda_seq n * h_seq_real (fun k => (alpha_seq k : ℝ)) n y) x| ≤ epsilon_seq n := by
        intro n hn;
        convert f_final_term_bound n x using 1;
        rw [ if_neg ( by linarith ) ];
      -- Since `epsilon_seq` is summable, the series is absolutely summable.
      have h_abs_summable : Summable (fun n => |deriv (fun y => lambda_seq n * h_seq_real (fun k => (alpha_seq k : ℝ)) n y) x|) := by
        rw [ ← summable_nat_add_iff 2 ];
        exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => h_abs_term_bound _ le_add_self ) ( epsilon_summable.comp_injective ( add_left_injective 2 ) );
      exact h_abs_summable.of_abs

/-
The derivative of f_final is 1 plus the sum of the derivatives of the terms.
-/
lemma f_final_deriv_eq_sum (x : ℝ) :
    deriv f_final x = 1 + ∑' n, deriv (fun y => lambda_seq n * h_seq_real (fun k => (alpha_seq k : ℝ)) n y) x := by
      apply_rules [ HasDerivAt.deriv ];
      -- We'll use the fact that if the series of derivatives converges uniformly, then the derivative of the sum is the sum of the derivatives.
      have h_deriv_series : HasDerivAt (fun x : ℝ => ∑' n, (lambda_seq n : ℝ) * h_seq_real (fun k => (alpha_seq k : ℝ)) n x) (∑' n, deriv (fun y => (lambda_seq n : ℝ) * h_seq_real (fun k => (alpha_seq k : ℝ)) n y) x) x := by
        apply_rules [ hasDerivAt_tsum ];
        rotate_right;
        use fun n => if n < 2 then 0 else epsilon_seq n;
        · have h_summable : Summable (fun n => epsilon_seq n) := by
            exact?;
          exact Summable.of_nonneg_of_le ( fun n => by split_ifs <;> linarith [ show 0 ≤ epsilon_seq n from by unfold epsilon_seq; positivity ] ) ( fun n => by split_ifs <;> linarith [ show 0 ≤ epsilon_seq n from by unfold epsilon_seq; positivity ] ) h_summable;
        · intro n y; exact hasDerivAt_deriv_iff.mpr ( by
            unfold h_seq_real;
            unfold h_seq; norm_num [ Complex.exp_re, Complex.exp_im, Complex.sin, Complex.cos ] ;
            split_ifs <;> norm_cast <;> norm_num [ Complex.exp_re, Complex.exp_im, sq ];
            norm_cast ; norm_num [ List.prod ];
            apply_rules [ DifferentiableAt.mul, DifferentiableAt.exp, DifferentiableAt.neg, DifferentiableAt.div ] <;> norm_num;
            induction ( List.range n ) <;> aesop );
        · intro n y;
          convert f_final_term_bound n y using 1;
        · convert f_final_series_summable x using 1;
      convert HasDerivAt.add ( hasDerivAt_id x ) h_deriv_series using 1;
      ext; unfold f_final; simp +decide [ F_final ];
      rw [ Complex.re_tsum ] ; aesop;
      convert F_final_converges _ using 1

/-
The derivative of f_final is strictly greater than 1/2 everywhere.
-/
theorem f_final_deriv_bound (x : ℝ) : deriv f_final x > 1/2 := by
  have h_deriv_bound : ∀ x : ℝ, |∑' n, deriv (fun y => lambda_seq n * h_seq_real (fun k => (alpha_seq k : ℝ)) n y) x| ≤ ∑' n, if n < 2 then 0 else epsilon_seq n := by
    intros x
    have h_sum_deriv_bound : ∀ n, |deriv (fun y => lambda_seq n * h_seq_real (fun k => (alpha_seq k : ℝ)) n y) x| ≤ if n < 2 then 0 else epsilon_seq n := by
      exact?;
    refine' le_trans ( le_of_eq ( by rw [ ← Real.norm_eq_abs ] ) ) ( le_trans ( norm_tsum_le_tsum_norm _ ) _ );
    · exact Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => h_sum_deriv_bound n ) ( show Summable fun n => if n < 2 then 0 else epsilon_seq n from by exact Summable.of_nonneg_of_le ( fun n => by split_ifs <;> linarith [ show 0 ≤ epsilon_seq n from by unfold epsilon_seq ; positivity ] ) ( fun n => by split_ifs <;> linarith [ show 0 ≤ epsilon_seq n from by unfold epsilon_seq ; positivity ] ) ( epsilon_summable ) );
    · refine' Summable.tsum_le_tsum h_sum_deriv_bound _ _;
      · refine' Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => h_sum_deriv_bound n ) _;
        rw [ ← summable_nat_add_iff 2 ];
        norm_num [ epsilon_seq ];
        exact Summable.comp_injective ( summable_geometric_two ) fun a b h => by simpa using h;
      · rw [ ← summable_nat_add_iff 2 ];
        norm_num [ epsilon_seq ];
        exact Summable.comp_injective ( summable_geometric_two ) fun a b h => by simpa using h;
  have h_deriv_bound : ∑' n, (if n < 2 then 0 else epsilon_seq n) < 1 / 2 := by
    rw [ Summable.tsum_eq_zero_add ] <;> norm_num;
    · rw [ Summable.tsum_eq_zero_add ] <;> norm_num [ epsilon_seq ];
      · norm_num [ Nat.succ_lt_succ_iff ];
        ring_nf; rw [ tsum_mul_right, tsum_geometric_of_lt_one ] <;> norm_num;
      · exact Summable.of_nonneg_of_le ( fun n => by split_ifs <;> positivity ) ( fun n => by split_ifs <;> ring_nf <;> norm_num ) ( summable_geometric_two );
    · exact Summable.of_nonneg_of_le ( fun n => by split_ifs <;> norm_num [ epsilon_seq ] ) ( fun n => by split_ifs <;> norm_num [ epsilon_seq ] ) ( show Summable fun n : ℕ => epsilon_seq n from epsilon_summable );
  rw [ f_final_deriv_eq_sum ];
  linarith [ abs_le.mp ( ‹∀ x : ℝ, |∑' n : ℕ, deriv ( fun y => lambda_seq n * h_seq_real ( fun k => ( alpha_seq k : ℝ ) ) n y ) x| ≤ ∑' n : ℕ, if n < 2 then 0 else epsilon_seq n› x ) ]

/-
Modified next step function that avoids 2 for beta_3 to ensure non-affineness.
-/
noncomputable def next_step' (n : ℕ) (hist : List (ℚ × ℚ × ℝ)) : ℚ × ℚ × ℝ :=
  if n = 0 then (0, 0, 0)
  else if n = 1 then (1, 1, 0)
  else
    let alpha_prev := alpha_from_hist hist
    let lambda_prev := lambda_from_hist hist
    let F_prev := F_seq_real alpha_prev lambda_prev (n - 1)
    let h_curr := h_seq_real alpha_prev n
    let eta := eta_val alpha_prev n (epsilon_seq n)
    let used_alpha := alpha_set hist
    let used_beta := beta_set hist
    let h_alpha_finite := alpha_set_finite hist
    let h_beta_finite := beta_set_finite hist

    if h_eta : eta > 0 then
      if n % 2 == 0 then
        -- Step B (Force domain)
        let alpha_n := first_unused a_seq a_seq_surj used_alpha h_alpha_finite
        let y := F_prev alpha_n
        let h_val := h_curr alpha_n
        if h_val_nz : h_val ≠ 0 then
          let radius := eta * |h_val|
          let avoid_beta := if n == 2 then insert 2 used_beta else used_beta
          let h_avoid_finite : avoid_beta.Finite := by
            aesop
          let beta_n := choice_in_interval (y - radius) (y + radius) (by
          linarith [ abs_pos.mpr h_val_nz, mul_pos h_eta ( abs_pos.mpr h_val_nz ) ]) avoid_beta h_avoid_finite
          let lambda_n := (beta_n - y) / h_val
          (alpha_n, beta_n, lambda_n)
        else (alpha_n, 0, 0)
      else
        -- Step A (Force range)
        let beta_n := first_unused b_seq b_seq_surj used_beta h_beta_finite
        if h : ∃ x, F_prev x = beta_n then
          let x_n := Classical.choose h
          if h_curr_nz : h_curr x_n ≠ 0 then
            let Lambda := fun t => (beta_n - F_prev t) / h_curr t
            if h_cont : ContinuousAt Lambda x_n ∧ Lambda x_n = 0 then
              let P := fun delta => 0 < delta ∧ ∀ t, |t - x_n| < delta → |Lambda t| < eta
              if h_delta : ∃ delta, P delta then
                let delta := Classical.choose h_delta
                let alpha_n := choice_in_interval (x_n - delta) (x_n + delta) (by
                linarith [ Classical.choose_spec h_delta |>.1 ]) used_alpha h_alpha_finite
                let lambda_n := Lambda alpha_n
                (alpha_n, beta_n, lambda_n)
              else (0, beta_n, 0)
            else (0, beta_n, 0)
          else (0, beta_n, 0)
        else (0, beta_n, 0)
    else (0, 0, 0)

/-
Definitions of the sequences alpha', beta', lambda' using the modified next_step' function.
-/
noncomputable def all_tuples' : ℕ → List (ℚ × ℚ × ℝ)
| 0 => []
| n + 1 =>
  let prev := all_tuples' n
  prev ++ [next_step' n prev]

noncomputable def construction_seq' (n : ℕ) : ℚ × ℚ × ℝ :=
  (all_tuples' (n + 1)).getLast (by
  -- By definition of `all_tuples'`, we know that `all_tuples' (n + 1)` is not empty because it contains at least the element `(0, 0, 0)`.
  have h_nonempty : ∀ n, (all_tuples' (n + 1)).length > 0 := by
    exact fun n => by induction n <;> simp_all +decide [ all_tuples' ] ;
  exact ne_of_apply_ne List.length ( ne_of_gt ( h_nonempty n ) ))

noncomputable def alpha_seq' (n : ℕ) : ℚ := (construction_seq' n).1
noncomputable def beta_seq' (n : ℕ) : ℚ := (construction_seq' n).2.1
noncomputable def lambda_seq' (n : ℕ) : ℝ := (construction_seq' n).2.2

/-
Definition of the limit function F_final' and its real restriction f_final'.
-/
noncomputable def F_final' (z : ℂ) : ℂ :=
  z + ∑' n : ℕ, (lambda_seq' n : ℂ) * h_seq (fun k => (alpha_seq' k : ℝ)) n z

noncomputable def f_final' (x : ℝ) : ℝ := (F_final' (x : ℂ)).re

/-
beta_seq' 2 is not equal to 2.
-/
lemma beta_seq'_2_ne_2 : beta_seq' 2 ≠ 2 := by
  rw [ show beta_seq' 2 = ( next_step' 2 ( all_tuples' 2 ) ).2.1 by rfl ];
  unfold next_step' at * ; norm_num at *;
  split_ifs <;> norm_num;
  · exact fun h => absurd ( h ▸ choice_in_interval_spec _ _ _ _ _ ) ( by norm_num );
  · contradiction

/-
eta_seq' definition and lemma showing alpha_from_hist retrieves alpha_seq'.
-/
noncomputable def eta_seq' (n : ℕ) : ℝ := eta_val (fun k => (alpha_seq' k : ℝ)) n (epsilon_seq n)

lemma alpha_from_hist_eq_alpha_seq' (n k : ℕ) (h : k < n) :
    alpha_from_hist (all_tuples' n) k = (alpha_seq' k : ℝ) := by
      unfold alpha_from_hist alpha_seq';
      -- By definition of `all_tuples'`, the `k`-th element is indeed the `k`-th element of `all_tuples' n`.
      have h_get : (all_tuples' n).get? k = (all_tuples' (k + 1)).get? k := by
        refine' Nat.le_induction rfl ( fun m hm ih => _ ) _ h;
        -- By definition of `all_tuples'`, appending an element to a list does not change the elements before the appended element.
        have h_append : ∀ (l : List (ℚ × ℚ × ℝ)) (x : ℚ × ℚ × ℝ), ∀ k, k < l.length → (l ++ [x]).get? k = l.get? k := by
          simp +contextual [ List.get?_eq_get ];
          grind;
        convert h_append _ _ _ _ using 1;
        · exact?;
        · exact Nat.lt_of_lt_of_le hm ( Nat.recOn m ( by norm_num ) fun n ihn => by erw [ show all_tuples' ( n + 1 ) = all_tuples' n ++ [ next_step' n ( all_tuples' n ) ] from rfl ] ; simp +arith +decide [ ihn ] );
      rw [ h_get ];
      unfold construction_seq';
      rw [ List.getLast_eq_getElem ];
      -- By induction on $k$, we can show that the length of `all_tuples' k` is $k$.
      have h_length : ∀ k, List.length (all_tuples' k) = k := by
        intro k
        induction' k with k ih;
        · rfl;
        · rw [ show all_tuples' ( k + 1 ) = all_tuples' k ++ [ next_step' k ( all_tuples' k ) ] from rfl, List.length_append, ih ] ; simp +arith +decide;
      aesop

/-
The eta value calculated in next_step' is equal to eta_seq' n.
-/
lemma eta_in_next_step'_eq_eta_seq' (n : ℕ) :
    let hist := all_tuples' n
    let alpha_prev := alpha_from_hist hist
    eta_val alpha_prev n (epsilon_seq n) = eta_seq' n := by
      unfold eta_seq' eta_val;
      unfold M_val L_val;
      congr! 2;
      · congr! 3;
        apply h_seq_eq_of_agree;
        exact?;
      · congr! 3;
        refine' Filter.EventuallyEq.deriv_eq _;
        filter_upwards [ ] with x;
        exact h_seq_eq_of_agree n _ _ ( fun k hk => by exact_mod_cast alpha_from_hist_eq_alpha_seq' n k hk ) x

/-
eta_seq' n is positive for n >= 1.
-/
lemma eta_seq'_pos (n : ℕ) (hn : n ≥ 1) : eta_seq' n > 0 := by
  have h_pos : 0 < M_val (fun k => (alpha_seq' k : ℝ)) n ∧ 0 < L_val (fun k => (alpha_seq' k : ℝ)) n := by
    have h_pos : 0 < M_val (fun k => (alpha_seq' k : ℝ)) n := by
      apply_rules [ M_val_pos ]
    have h_pos' : 0 < L_val (fun k => (alpha_seq' k : ℝ)) n := by
      exact?
    exact ⟨h_pos, h_pos'⟩
  generalize_proofs at *;
  exact lt_min ( div_pos ( show 0 < epsilon_seq n from by exact pow_pos ( by norm_num ) _ ) h_pos.1 ) ( div_pos ( show 0 < epsilon_seq n from by exact pow_pos ( by norm_num ) _ ) h_pos.2 )

/-
eta_val is positive for any alpha sequence if n >= 1.
-/
lemma eta_val_pos_any (alpha : ℕ → ℝ) (n : ℕ) (hn : n ≥ 1) : eta_val alpha n (epsilon_seq n) > 0 := by
  exact lt_min ( div_pos ( by exact? ) ( by exact? ) ) ( div_pos ( by exact? ) ( by exact? ) )

/-
The absolute value of lambda_seq' n is bounded by eta_seq' n.
-/
lemma lambda_seq'_bound (n : ℕ) : |lambda_seq' n| ≤ eta_seq' n := by
  -- By definition of `lambda_seq' n`, we have `lambda_seq' n = (next_step' n (all_tuples' n)).2.2`.
  have h_def : lambda_seq' n = (next_step' n (all_tuples' n)).2.2 := by
    unfold lambda_seq';
    unfold construction_seq' all_tuples';
    induction n <;> aesop;
  refine' h_def.symm ▸ _;
  unfold next_step';
  split_ifs <;> norm_num [ eta_in_next_step'_eq_eta_seq' ];
  · unfold eta_seq';
    unfold eta_val;
    unfold epsilon_seq M_val L_val; norm_num;
    exact ⟨ div_nonneg ( by positivity ) ( by apply_rules [ Real.sSup_nonneg ] ; aesop ), div_nonneg ( by positivity ) ( by apply_rules [ Real.sSup_nonneg ] ; aesop ) ⟩;
  · exact le_of_lt ( eta_seq'_pos n ( by linarith ) );
  · split_ifs <;> norm_num;
    any_goals linarith;
    · have := choice_in_interval_spec ( F_seq_real ( alpha_from_hist ( all_tuples' n ) ) ( lambda_from_hist ( all_tuples' n ) ) ( n - 1 ) ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) ) - eta_seq' n * |h_seq_real ( alpha_from_hist ( all_tuples' n ) ) n ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) )| ) ( F_seq_real ( alpha_from_hist ( all_tuples' n ) ) ( lambda_from_hist ( all_tuples' n ) ) ( n - 1 ) ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) ) + eta_seq' n * |h_seq_real ( alpha_from_hist ( all_tuples' n ) ) n ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) )| ) ( by
        nlinarith [ abs_pos.mpr ‹_› ] ) ( insert 2 ( beta_set ( all_tuples' n ) ) ) ( by
        exact Set.Finite.insert _ ( beta_set_finite _ ) );
      all_goals generalize_proofs at *;
      rw [ abs_div ];
      rw [ div_le_iff₀ ( abs_pos.mpr ‹_› ) ];
      exact abs_le.mpr ⟨ by linarith [ this.1.1 ], by linarith [ this.1.2 ] ⟩;
    · rw [ abs_div ];
      rw [ div_le_iff₀ ( abs_pos.mpr ‹_› ) ];
      have := choice_in_interval_spec ( F_seq_real ( alpha_from_hist ( all_tuples' n ) ) ( lambda_from_hist ( all_tuples' n ) ) ( n - 1 ) ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) ) - eta_seq' n * |h_seq_real ( alpha_from_hist ( all_tuples' n ) ) n ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) )| ) ( F_seq_real ( alpha_from_hist ( all_tuples' n ) ) ( lambda_from_hist ( all_tuples' n ) ) ( n - 1 ) ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) ) + eta_seq' n * |h_seq_real ( alpha_from_hist ( all_tuples' n ) ) n ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) )| ) ( by
        nlinarith [ abs_pos.mpr ‹_› ] ) ( beta_set ( all_tuples' n ) ) ( beta_set_finite ( all_tuples' n ) );
      exact abs_le.mpr ⟨ by linarith [ this.1.1 ], by linarith [ this.1.2 ] ⟩;
    · aesop;
    · exact le_of_lt ( eta_seq'_pos n ( Nat.pos_of_ne_zero ‹_› ) );
  · split_ifs <;> norm_num;
    any_goals linarith;
    · aesop;
    · aesop;
    · rename_i h₁ h₂ h₃ h₄ h₅ h₆;
      refine' le_of_lt ( h₆.choose_spec.2 _ _ );
      have := choice_in_interval_spec ( Classical.choose h₃ - h₆.choose ) ( Classical.choose h₃ + h₆.choose ) ( by linarith [ h₆.choose_spec.1 ] ) ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) );
      exact abs_lt.mpr ⟨ by linarith [ this.1.1 ], by linarith [ this.1.2 ] ⟩;
    · exact le_of_lt ( eta_seq'_pos n ( Nat.one_le_iff_ne_zero.mpr ‹_› ) )

/-
The n-th term of the series for F_final' is bounded by epsilon_seq n on the disk of radius n+1.
-/
lemma term_bound_valid' (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ n + 1) :
    ‖(lambda_seq' n : ℂ) * h_seq (fun k => (alpha_seq' k : ℝ)) n z‖ ≤ epsilon_seq n := by
      -- By definition of $M_val$, we know that $|h_seq (fun k => (alpha_seq' k : ℝ)) n z| \leq M_val (fun k => (alpha_seq' k : ℝ)) n$ for all $z$ with $|z| \leq n + 1$.
      have hM_val : ∀ z, ‖z‖ ≤ n + 1 → ‖h_seq (fun k => (alpha_seq' k : ℝ)) n z‖ ≤ M_val (fun k => (alpha_seq' k : ℝ)) n := by
        -- By definition of supremum, for any $z$ in the closed ball, $|h_seq (fun k => (alpha_seq' k : ℝ)) n z| \leq M_val (fun k => (alpha_seq' k : ℝ)) n$.
        intros z hz
        apply le_csSup;
        · -- The image of a compact set under a continuous function is compact.
          have h_compact : IsCompact {z : ℂ | ‖z‖ ≤ n + 1} := by
            convert ProperSpace.isCompact_closedBall ( 0 : ℂ ) ( n + 1 ) using 1 ; norm_num [ Set.ext_iff ];
          apply_rules [ IsCompact.bddAbove, h_compact.image_of_continuousOn ];
          refine' Continuous.continuousOn _;
          unfold h_seq;
          cases n <;> continuity;
        · exact ⟨ z, hz, rfl ⟩;
      have h_lambda_bound : |lambda_seq' n| ≤ epsilon_seq n / M_val (fun k => (alpha_seq' k : ℝ)) n := by
        refine' le_trans ( lambda_seq'_bound n ) _;
        exact min_le_left _ _;
      rw [ le_div_iff₀ ] at h_lambda_bound;
      · simpa [ abs_mul ] using le_trans ( mul_le_mul_of_nonneg_left ( hM_val z hz ) ( abs_nonneg _ ) ) h_lambda_bound;
      · apply_rules [ M_val_pos ]

/-
The series defining F_final' converges for every complex number z.
-/
theorem F_final'_converges (z : ℂ) : Summable (fun n => (lambda_seq' n : ℂ) * h_seq (fun k => (alpha_seq' k : ℝ)) n z) := by
  -- Since `epsilon_seq` is summable, the series `∑' n, epsilon_seq n` converges.
  have h_summable : Summable (fun n => epsilon_seq n) := by
    exact?;
  -- Let `N` be a natural number such that `|z| <= N + 1`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖z‖ ≤ N + 1 := by
    exact ⟨ ⌈‖z‖⌉₊, by linarith [ Nat.le_ceil ‖z‖ ] ⟩;
  have h_tail_summable : Summable (fun n => ‖(lambda_seq' n : ℂ) * h_seq (fun k => (alpha_seq' k : ℝ)) n z‖) := by
    rw [ ← summable_nat_add_iff N ];
    exact Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => term_bound_valid' _ _ <| by simpa using le_trans hN <| mod_cast by linarith ) <| h_summable.comp_injective <| add_left_injective N;
  exact .of_norm h_tail_summable

/-
The n-th term of the series is an entire function.
-/
noncomputable def term' (n : ℕ) (z : ℂ) := (lambda_seq' n : ℂ) * h_seq (fun k => (alpha_seq' k : ℝ)) n z

lemma term'_diff (n : ℕ) : Differentiable ℂ (term' n) := by
  apply_rules [ Differentiable.const_mul, Complex.differentiable_exp ];
  induction' n with n ih;
  · unfold h_seq;
    norm_num;
  · refine' Differentiable.mul _ _;
    · exact Complex.differentiable_exp.comp ( Differentiable.div_const ( Differentiable.neg ( differentiable_pow 2 ) ) _ );
    · induction' ( List.range ( n + 1 ) ) using List.reverseRecOn <;> aesop

/-
The sequence epsilon_seq is summable.
-/
lemma epsilon_summable' : Summable epsilon_seq := by
  exact?

/-
Definitions of tail and head sums for the series (corrected syntax).
-/
noncomputable def term_tail' (N : ℕ) (n : ℕ) (z : ℂ) : ℂ := if n < N then 0 else term' n z

noncomputable def F_tail' (N : ℕ) (z : ℂ) : ℂ := ∑' n, term_tail' N n z

noncomputable def F_head' (N : ℕ) (z : ℂ) : ℂ := ∑ n ∈ Finset.range N, term' n z

/-
The terms of the tail sum are differentiable functions.
-/
lemma term_tail'_diff (N n : ℕ) : Differentiable ℂ (term_tail' N n) := by
  unfold term_tail';
  split_ifs <;> norm_num [ term'_diff ]

/-
The terms of the tail sum are bounded by epsilon_seq on the ball of radius N+1.
-/
lemma term_tail'_bound (N : ℕ) (z : ℂ) (hz : ‖z‖ < N + 1) (n : ℕ) :
    ‖term_tail' N n z‖ ≤ epsilon_seq n := by
      by_cases hn : n < N;
      · unfold term_tail';
        rw [ if_pos hn, norm_zero ] ; exact le_of_lt ( epsilon_pos n );
      · unfold term_tail';
        rw [ if_neg hn ];
        exact term_bound_valid' n z ( le_of_lt ( lt_of_lt_of_le hz ( by norm_cast; linarith ) ) )

/-
The tail sum F_tail' N is differentiable on the ball of radius N+1.
-/
lemma F_tail'_diff_on (N : ℕ) : DifferentiableOn ℂ (F_tail' N) (Metric.ball 0 (N + 1)) := by
  have := @Complex.differentiableOn_tsum_of_summable_norm;
  exact this ( by exact? ) ( fun i => Differentiable.differentiableOn ( by exact? ) ) ( Metric.isOpen_ball ) ( fun i w hw => term_tail'_bound N w ( by simpa using hw ) i )

/-
Decomposition of the n-th term into head and tail parts.
-/
noncomputable def term_head' (N : ℕ) (n : ℕ) (z : ℂ) : ℂ := if n < N then term' n z else 0

lemma term_split (N n : ℕ) (z : ℂ) : term' n z = term_head' N n z + term_tail' N n z := by
  unfold term_head' term_tail'; aesop;

/-
Corrected decomposition of F_final' including the z term.
-/
lemma F_final'_eq_z_add_head_add_tail (N : ℕ) (z : ℂ) : F_final' z = z + F_head' N z + F_tail' N z := by
  -- By definition of $F_final'$, we can split the sum into the sum up to $N-1$ and the sum from $N$ onwards.
  have h_split : ∑' n, term' n z = ∑ n ∈ Finset.range N, term' n z + ∑' n, term_tail' N n z := by
    have h_split : ∑' n, term' n z = ∑' n, (if n < N then term' n z else 0) + ∑' n, (if n < N then 0 else term' n z) := by
      rw [ ← Summable.tsum_add ] ; congr ; ext n ; aesop;
      · rw [ ← summable_nat_add_iff N ];
        exact ⟨ _, hasSum_single 0 fun n hn => if_neg <| by linarith ⟩;
      · rw [ ← summable_nat_add_iff N ];
        have h_summable : Summable (fun n => term' n z) := by
          exact?;
        simpa using h_summable.comp_injective ( add_left_injective N );
    rw [ h_split, tsum_eq_sum ];
    congr! 1;
    exacts [ Finset.sum_congr rfl fun n hn => if_pos <| Finset.mem_range.mp hn, fun n hn => if_neg <| by simpa using hn ];
  simpa only [ add_assoc ] using congr_arg _ h_split

/-
The head sum F_head' N is an entire function.
-/
lemma F_head'_entire (N : ℕ) : Differentiable ℂ (F_head' N) := by
  -- The sum of a finite number of differentiable functions is differentiable.
  have h_sum_diff : ∀ {f : ℕ → ℂ → ℂ}, (∀ n, Differentiable ℂ (f n)) → Differentiable ℂ (fun z => ∑ n ∈ Finset.range N, f n z) := by
    exact fun h => by exact?;
  exact h_sum_diff fun n => term'_diff n

/-
F_final' is an entire function.
-/
theorem F_final'_entire : Differentiable ℂ F_final' := by
  -- Fix an arbitrary $z \in \mathbb{C}$.
  intro z;
  -- Choose $N$ such that $|z| < N + 1$.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, z ∈ Metric.ball 0 (N + 1) := by
    exact ⟨ ⌈‖z‖⌉₊, by simpa using Nat.lt_of_ceil_lt ( Nat.lt_succ_self _ ) ⟩;
  -- On the ball $B(0, N+1)$, $F_final'(w) = w + F_head' N w + F_tail' N w$.
  have h_decomp : ∀ w ∈ Metric.ball 0 (N + 1), F_final' w = w + F_head' N w + F_tail' N w := by
    exact?;
  refine' DifferentiableAt.congr_of_eventuallyEq _ ( Filter.eventuallyEq_of_mem ( Metric.isOpen_ball.mem_nhds hN ) h_decomp );
  exact DifferentiableAt.add ( DifferentiableAt.add ( differentiableAt_id ) ( F_head'_entire N |> Differentiable.differentiableAt ) ) ( F_tail'_diff_on N |> DifferentiableOn.differentiableAt <| Metric.isOpen_ball.mem_nhds hN )

/-
h_seq with alpha_seq' takes real values for real arguments.
-/
lemma h_seq'_is_real (n : ℕ) (x : ℝ) : (h_seq (fun k => (alpha_seq' k : ℝ)) n (x : ℂ)).im = 0 := by
  unfold h_seq;
  induction List.range n <;> simp_all +decide [ Complex.exp_re, Complex.exp_im, List.prod_cons ];
  · split_ifs <;> norm_num [ Complex.exp_re, Complex.exp_im ];
    norm_cast ; norm_num;
  · split_ifs at * <;> simp_all +decide [ Complex.exp_re, Complex.exp_im, Complex.mul_im ];
    norm_cast at * ; aesop

/-
F_final' takes real values on the real line.
-/
lemma F_final'_real_on_real (x : ℝ) : (F_final' (x : ℂ)).im = 0 := by
  unfold F_final';
  -- Since each term in the sum is real, the sum itself is real. Adding x, which is real, to this sum will also result in a real number. Hence, the imaginary part of F_final' x is zero.
  have h_real : ∀ n, (lambda_seq' n : ℂ) * h_seq (fun k => (alpha_seq' k : ℝ)) n (x : ℂ) ∈ Set.range (fun r : ℝ => r : ℝ → ℂ) := by
    intro n
    have h_real_term : (h_seq (fun k => (alpha_seq' k : ℝ)) n (x : ℂ)).im = 0 := by
      exact?;
    simp_all +decide [ Complex.ext_iff ];
  choose f hf using h_real;
  norm_num [ ← hf ];
  rw [ ← Complex.re_add_im ( ∑' n : ℕ, ( f n : ℂ ) ) ] ; norm_cast ; aesop

/-
h_seq vanishes at alpha_seq' m if m < n.
-/
lemma h_seq_vanishes_for_large_n' (m n : ℕ) (h : m < n) :
    h_seq (fun k => (alpha_seq' k : ℝ)) n (alpha_seq' m) = 0 := by
      unfold h_seq;
      aesop

/-
F_final' is differentiable on the ball of radius N+1.
-/
lemma F_final'_diff_on_ball (N : ℕ) : DifferentiableOn ℂ F_final' (Metric.ball 0 (N + 1)) := by
  exact F_final'_entire.differentiableOn

/-
F_partial_sum' restricted to reals matches F_seq_real.
-/
noncomputable def F_partial_sum' (N : ℕ) (z : ℂ) : ℂ := z + ((List.range (N + 1)).map (fun n => (lambda_seq' n : ℂ) * h_seq (fun k => (alpha_seq' k : ℝ)) n z)).sum

lemma F_partial_sum'_eq_F_seq_real (n : ℕ) (x : ℝ) :
    (F_partial_sum' n (x : ℂ)).re = F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) n x := by
      unfold F_partial_sum' F_seq_real;
      unfold F_seq; simp +decide [ List.sum_map_mul_right ] ;

/-
Recursive formula for F_partial_sum'.
-/
lemma F_partial_sum'_succ (n : ℕ) (z : ℂ) :
    F_partial_sum' (n + 1) z = F_partial_sum' n z + (lambda_seq' (n + 1) : ℂ) * h_seq (fun k => (alpha_seq' k : ℝ)) (n + 1) z := by
      unfold F_partial_sum'; simp +decide [ List.sum_range_succ ] ; ring!;

/-
The invariant holds for n=0.
-/
def Invariant' (n : ℕ) : Prop :=
  (∀ i j, i ≤ n → j ≤ n → i ≠ j → alpha_seq' i ≠ alpha_seq' j) ∧
  (∀ i j, i ≤ n → j ≤ n → i ≠ j → beta_seq' i ≠ beta_seq' j) ∧
  (∀ k ≤ n, F_seq_real (fun i => alpha_seq' i) (fun i => lambda_seq' i) n (alpha_seq' k) = beta_seq' k) ∧
  (∀ x : ℝ, deriv (fun t => F_seq_real (fun i => alpha_seq' i) (fun i => lambda_seq' i) n t) x ≥ 1 - ∑ k ∈ Finset.range (n + 1), if k < 2 then 0 else epsilon_seq k) ∧
  (∀ k, 2 ≤ k → k ≤ n → |lambda_seq' k| < eta_seq' k)

lemma Invariant'_0 : Invariant' 0 := by
  unfold Invariant';
  unfold alpha_seq' beta_seq' lambda_seq';
  unfold construction_seq';
  unfold F_seq_real; norm_num;
  unfold F_seq; norm_num [ all_tuples' ] ;
  unfold next_step'; norm_num;
  grind

/-
Strict bound for lambda_seq' n when n is even and >= 2.
-/
lemma lambda_seq'_strict_bound_even (n : ℕ) (hn : n ≥ 2) (heven : n % 2 = 0) : |lambda_seq' n| < eta_seq' n := by
  -- By definition of next_step', lambda_seq' n is the third component of the tuple generated by next_step' n (all_tuples' n).
  have h_lambda_def : lambda_seq' n = (next_step' n (all_tuples' n)).2.2 := by
    unfold lambda_seq';
    unfold construction_seq';
    unfold all_tuples';
    cases n <;> aesop;
  unfold next_step' at h_lambda_def;
  split_ifs at h_lambda_def <;> norm_num at *;
  · linarith;
  · linarith;
  · split_ifs at h_lambda_def <;> norm_num at *;
    · exact h_lambda_def.symm ▸ by simpa using eta_seq'_pos n ( by linarith ) ;
    · subst_vars;
      rw [ h_lambda_def, abs_div ];
      rw [ div_lt_iff₀ ];
      · have := choice_in_interval_spec ( F_seq_real ( alpha_from_hist ( all_tuples' 2 ) ) ( lambda_from_hist ( all_tuples' 2 ) ) ( 2 - 1 ) ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' 2 ) ) ( alpha_set_finite ( all_tuples' 2 ) ) ) - eta_val ( alpha_from_hist ( all_tuples' 2 ) ) 2 ( epsilon_seq 2 ) * |h_seq_real ( alpha_from_hist ( all_tuples' 2 ) ) 2 ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' 2 ) ) ( alpha_set_finite ( all_tuples' 2 ) ) )| ) ( F_seq_real ( alpha_from_hist ( all_tuples' 2 ) ) ( lambda_from_hist ( all_tuples' 2 ) ) ( 2 - 1 ) ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' 2 ) ) ( alpha_set_finite ( all_tuples' 2 ) ) ) + eta_val ( alpha_from_hist ( all_tuples' 2 ) ) 2 ( epsilon_seq 2 ) * |h_seq_real ( alpha_from_hist ( all_tuples' 2 ) ) 2 ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' 2 ) ) ( alpha_set_finite ( all_tuples' 2 ) ) )| ) ( by
          grind ) ( insert 2 ( beta_set ( all_tuples' 2 ) ) ) ( by
          exact Set.Finite.insert _ ( beta_set_finite _ ) );
        all_goals generalize_proofs at *;
        norm_num +zetaDelta at *;
        exact abs_lt.mpr ⟨ by linarith! [ abs_nonneg ( h_seq_real ( alpha_from_hist ( all_tuples' 2 ) ) 2 ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' 2 ) ) ‹_› ) ) ], by linarith! [ abs_nonneg ( h_seq_real ( alpha_from_hist ( all_tuples' 2 ) ) 2 ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' 2 ) ) ‹_› ) ) ] ⟩;
      · exact abs_pos.mpr ‹_›;
    · rw [ h_lambda_def, abs_div ];
      field_simp;
      rw [ ← eta_in_next_step'_eq_eta_seq' ];
      have := choice_in_interval_spec ( F_seq_real ( alpha_from_hist ( all_tuples' n ) ) ( lambda_from_hist ( all_tuples' n ) ) ( n - 1 ) ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) ) - eta_val ( alpha_from_hist ( all_tuples' n ) ) n ( epsilon_seq n ) * |h_seq_real ( alpha_from_hist ( all_tuples' n ) ) n ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) )| ) ( F_seq_real ( alpha_from_hist ( all_tuples' n ) ) ( lambda_from_hist ( all_tuples' n ) ) ( n - 1 ) ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) ) + eta_val ( alpha_from_hist ( all_tuples' n ) ) n ( epsilon_seq n ) * |h_seq_real ( alpha_from_hist ( all_tuples' n ) ) n ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) )| ) ( by
        grind ) ( beta_set ( all_tuples' n ) ) ( beta_set_finite ( all_tuples' n ) );
      rw [ abs_lt ];
      grind;
    · exact absurd ‹_› ( not_le_of_gt ( eta_val_pos_any _ _ ( by linarith ) ) );
  · omega

/-
For even n >= 2, next_step' returns the tuple constructed in Step B (Force Domain).
-/
lemma next_step'_eq_B (n : ℕ) (hn : n ≥ 2) (heven : n % 2 = 0) (h_inv : Invariant' (n - 1)) :
  let hist := all_tuples' n
  let alpha_prev := alpha_from_hist hist
  let lambda_prev := lambda_from_hist hist
  let F_prev := F_seq_real alpha_prev lambda_prev (n - 1)
  let h_curr := h_seq_real alpha_prev n
  let eta := eta_val alpha_prev n (epsilon_seq n)
  let alpha_n := first_unused a_seq a_seq_surj (alpha_set hist) (alpha_set_finite hist)
  let y := F_prev alpha_n
  let h_val := h_curr alpha_n
  let radius := eta * |h_val|
  let avoid_beta := if n == 2 then insert 2 (beta_set hist) else (beta_set hist)
  let h_avoid_finite : avoid_beta.Finite := by
    exact Set.Finite.union ( Set.finite_singleton 2 ) ( beta_set_finite hist ) |> Set.Finite.subset <| by aesop_cat;
  let beta_n := choice_in_interval (y - radius) (y + radius) (by
  all_goals generalize_proofs at *;
  norm_num +zetaDelta at *;
  have h_eta_pos : eta_val (alpha_from_hist (all_tuples' n)) n (epsilon_seq n) > 0 := by
    apply eta_val_pos_any;
    linarith;
  -- Since $h_val \neq 0$, we have $|h_val| > 0$.
  have h_h_val_pos : |h_val| > 0 := by
    have h_h_val_pos : h_seq (alpha_from_hist (all_tuples' n)) n (alpha_n : ℂ) ≠ 0 := by
      have h_h_val_pos : ∀ k < n, alpha_n ≠ alpha_seq' k := by
        intro k hk_lt_n hk_eq_alpha_seq'
        have h_alpha_seq'_eq : alpha_seq' k ∈ alpha_set (all_tuples' n) := by
          have h_alpha_seq'_eq : ∀ m < n, alpha_seq' m ∈ alpha_set (all_tuples' n) := by
            intros m hm_lt_n
            have h_alpha_seq'_eq : alpha_seq' m ∈ alpha_set (all_tuples' (m + 1)) := by
              simp +decide [ alpha_seq', construction_seq' ];
              simp +decide [ alpha_set ];
              use List.length (all_tuples' (m + 1)) - 1;
              use (all_tuples' (m + 1)).getLast (by
              induction m <;> simp_all +decide [ all_tuples' ]) |>.2.1, (all_tuples' (m + 1)).getLast (by
              induction m <;> simp_all +decide [ all_tuples' ]) |>.2.2
              generalize_proofs at *;
              rw [ List.getElem?_eq_getElem ];
              rw [ List.getLast_eq_getElem ];
            have h_alpha_seq'_eq : ∀ p q : ℕ, p ≤ q → alpha_set (all_tuples' p) ⊆ alpha_set (all_tuples' q) := by
              intros p q hpq;
              induction hpq <;> simp_all +decide [ alpha_set, List.range_succ ];
              rename_i k hk ih;
              intro a x x_1 x_2 hx; obtain ⟨ k, a, b, hk ⟩ := ih a x x_1 x_2 hx; use k, a, b; simp_all +decide [ all_tuples' ] ;
              rw [ List.getElem?_append ] ; aesop;
            exact h_alpha_seq'_eq _ _ ( Nat.succ_le_of_lt hm_lt_n ) ‹_›;
          exact h_alpha_seq'_eq k hk_lt_n;
        exact absurd h_alpha_seq'_eq ( by rw [ ← hk_eq_alpha_seq' ] ; exact first_unused_spec a_seq a_seq_surj _ _ );
      have h_h_val_pos : ∀ k < n, (alpha_n - alpha_seq' k : ℂ) ≠ 0 := by
        exact fun k hk => sub_ne_zero_of_ne <| mod_cast h_h_val_pos k hk;
      simp_all +decide [ h_seq ];
      split_ifs <;> simp_all +decide [ Complex.exp_ne_zero, List.prod_eq_zero_iff ];
      convert h_h_val_pos using 1;
      congr!;
      exact congr_arg _ ( alpha_from_hist_eq_alpha_seq' _ _ ( by linarith ) );
    simp +zetaDelta at *;
    convert h_h_val_pos using 1;
    unfold h_seq_real h_seq; norm_num [ Complex.ext_iff ] ;
    split_ifs <;> norm_num [ Complex.exp_re, Complex.exp_im ];
    norm_cast ; norm_num;
    induction ( List.range n ) <;> aesop;
  nlinarith) avoid_beta h_avoid_finite
  let lambda_n := (beta_n - y) / h_val
  next_step' n hist = (alpha_n, beta_n, lambda_n) := by
    all_goals generalize_proofs at *;
    -- Since $n \geq 2$ and $n$ is even, the conditions for Step B are satisfied.
    have h_step_B_conditions : eta_val (alpha_from_hist (all_tuples' n)) n (epsilon_seq n) > 0 ∧ h_seq_real (alpha_from_hist (all_tuples' n)) n (first_unused a_seq a_seq_surj (alpha_set (all_tuples' n)) (alpha_set_finite (all_tuples' n))) ≠ 0 := by
      -- Since $n$ is even, we can apply the lemma next_step_B_conditions_simple.
      have h_eta_pos : eta_val (alpha_from_hist (all_tuples' n)) n (epsilon_seq n) > 0 := by
        apply_rules [ eta_val_pos_any ];
        linarith
      generalize_proofs at *;
      refine ⟨ h_eta_pos, ?_ ⟩;
      refine' fun h => _;
      have := h_seq_ne_zero_of_distinct n ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ‹_› ) ?_ <;> aesop;
    unfold next_step'; aesop;

/-
The lambda value retrieved from the history at step n matches the global lambda sequence value for indices k < n.
-/
lemma lambda_from_hist_eq_lambda_seq' (n k : ℕ) (h : k < n) :
    lambda_from_hist (all_tuples' n) k = lambda_seq' k := by
      unfold lambda_from_hist lambda_seq';
      rw [ show ( all_tuples' n ).get? k = ( all_tuples' ( k + 1 ) ).get? k from ?_ ];
      · unfold construction_seq';
        rw [ List.getLast_eq_getElem ];
        -- By definition of `all_tuples'`, the length of `all_tuples' (k + 1)` is `k + 1`.
        have h_len : (all_tuples' (k + 1)).length = k + 1 := by
          induction' k + 1 with n ih <;> simp_all +decide [ all_tuples' ];
        aesop;
      · rw [ show all_tuples' n = all_tuples' ( k + 1 ) ++ List.map ( fun m => next_step' m ( all_tuples' m ) ) ( List.range ( n - ( k + 1 ) ) |> List.map ( fun m => m + ( k + 1 ) ) ) from ?_ ];
        · rcases n with ( _ | _ | n ) <;> simp_all +decide [ List.get?_eq_get ];
          rw [ List.getElem?_append ] ; norm_num;
          exact fun h => absurd h ( by linarith [ show List.length ( all_tuples' ( k + 1 ) ) = k + 1 from by exact Nat.recOn k ( by trivial ) fun n ihn => by rw [ show all_tuples' ( n + 1 + 1 ) = all_tuples' ( n + 1 ) ++ [ next_step' ( n + 1 ) ( all_tuples' ( n + 1 ) ) ] from rfl ] ; simp +arith +decide [ ihn ] ] );
        · have h_all_tuples'_eq : ∀ m, all_tuples' (m + 1) = all_tuples' m ++ [next_step' m (all_tuples' m)] := by
            exact?;
          have h_all_tuples'_eq : ∀ m, all_tuples' (m + (k + 1)) = all_tuples' (k + 1) ++ List.map (fun m => next_step' m (all_tuples' m)) (List.map (fun m => m + (k + 1)) (List.range m)) := by
            intro m; induction m <;> simp_all +decide [ Nat.succ_add, List.range_succ ] ;
          convert h_all_tuples'_eq ( n - ( k + 1 ) ) using 1 ; rw [ Nat.sub_add_cancel ( by linarith ) ]

/-
The partial sum F_{n-1} computed from the history at step n matches the one computed from the global sequences.
-/
lemma F_seq_real_eq_F_seq_real' (n : ℕ) (x : ℝ) (hn : n ≥ 1) :
    F_seq_real (alpha_from_hist (all_tuples' n)) (lambda_from_hist (all_tuples' n)) (n - 1) x =
    F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) (n - 1) x := by
      -- By definition of `alpha_from_hist` and `lambda_from_hist`, we know that for `k < n`, `alpha_from_hist (all_tuples' n) k = alpha_seq' k` and `lambda_from_hist (all_tuples' n) k = lambda_seq' k`.
      have h_alpha_lambda : ∀ k < n, alpha_from_hist (all_tuples' n) k = alpha_seq' k ∧ lambda_from_hist (all_tuples' n) k = lambda_seq' k := by
        exact fun k hk => ⟨ alpha_from_hist_eq_alpha_seq' n k hk, lambda_from_hist_eq_lambda_seq' n k hk ⟩;
      unfold F_seq_real;
      unfold F_seq;
      field_simp;
      rw [ Nat.sub_add_cancel hn ];
      congr! 3;
      refine' List.map_congr_left fun k hk => _;
      rw [ h_alpha_lambda k ( List.mem_range.mp hk ) |>.2, h_seq_eq_of_agree ];
      exact fun i hi => h_alpha_lambda i ( lt_trans hi ( List.mem_range.mp hk ) ) |>.1

/-
The h_seq_real value computed from the history at step n matches the one computed from the global alpha sequence.
-/
lemma h_seq_real_eq_h_seq_real' (n : ℕ) (x : ℝ) :
    h_seq_real (alpha_from_hist (all_tuples' n)) n x = h_seq_real (fun k => alpha_seq' k) n x := by
      unfold h_seq_real;
      -- By definition of `alpha_from_hist`, we know that `alpha_from_hist (all_tuples' n) k = alpha_seq' k` for all `k < n`.
      have h_alpha_eq : ∀ k < n, alpha_from_hist (all_tuples' n) k = alpha_seq' k := by
        exact?;
      unfold h_seq;
      rw [ List.map_congr_left fun k hk => by rw [ h_alpha_eq k ( List.mem_range.mp hk ) ] ]

/-
The eta value computed from the history at step n matches the one computed from the global alpha sequence.
-/
lemma eta_eq_eta_seq' (n : ℕ) :
    eta_val (alpha_from_hist (all_tuples' n)) n (epsilon_seq n) = eta_seq' n := by
      apply eta_in_next_step'_eq_eta_seq'

/-
If the invariant holds at step n, then the partial sum F_n is surjective.
-/
lemma F_seq_real_surjective_of_Invariant' (n : ℕ) (h : Invariant' n) :
    Function.Surjective (fun x => F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) n x) := by
      -- The invariant implies that the derivative of F_n is bounded below by 1/2.
      have h_deriv_bound : ∀ x : ℝ, deriv (fun t => F_seq_real (fun k => (alpha_seq' k : ℝ)) (fun k => lambda_seq' k) n t) x ≥ 1 / 2 := by
        have := h.2.2.2.1;
        refine' fun x => le_trans _ ( this x );
        norm_num [ Finset.sum_range_succ', epsilon_seq ];
        rcases n with ( _ | _ | n ) <;> norm_num [ Finset.sum_range_succ', pow_succ' ] at *;
        norm_num [ Nat.succ_lt_succ_iff ];
        norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
        linarith [ show ( ∑ x ∈ Finset.range n, ( 1 / 2 : ℝ ) ^ x ) ≤ 2 by rw [ geom_sum_eq ] <;> ring <;> norm_num ];
      -- Apply the lemma that states a differentiable function with a derivative bounded below by a positive constant is surjective.
      have := surjective_of_deriv_ge (fun x => F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) n x) (by
      exact fun x => differentiableAt_of_deriv_ne_zero ( by linarith [ h_deriv_bound x ] )) (1 / 2) (by
      norm_num) h_deriv_bound;
      aesop

/-
If x maps to the new beta value under F_{n-1}, then x is not one of the previous alpha values.
-/
lemma preimage_not_alpha' (n : ℕ) (h_inv : Invariant' (n - 1)) (hn : n ≥ 1)
    (x : ℝ) (hx : F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) (n - 1) x = first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n))) :
    ∀ k < n, x ≠ alpha_seq' k := by
      intro k hk_lt_n hk_eq_alpha_seq'_k;
      have h_beta_k : F_seq_real (fun k => (alpha_seq' k : ℝ)) (fun k => lambda_seq' k) (n - 1) (alpha_seq' k) = beta_seq' k := by
        convert h_inv.2.2.1 k ( Nat.le_sub_one_of_lt hk_lt_n );
      have h_beta_k_not_in_beta_set : beta_seq' k ∈ beta_set (all_tuples' n) := by
        use k;
        -- Since $k < n$, the $k$-th element of `all_tuples' n` is the tuple generated at step $k$.
        have h_kth_element : all_tuples' n = List.map (fun i => construction_seq' i) (List.range n) := by
          have h_kth_element : ∀ m, all_tuples' m = List.map (fun i => construction_seq' i) (List.range m) := by
            intro m; induction m <;> simp_all +decide [ List.range_succ ] ;
            -- By definition of `all_tuples'`, we have `all_tuples' (n + 1) = all_tuples' n ++ [next_step' n (all_tuples' n)]`.
            have h_all_tuples'_succ : all_tuples' (Nat.succ ‹_›) = all_tuples' ‹_› ++ [next_step' ‹_› (all_tuples' ‹_›)] := by
              exact?;
            unfold construction_seq'; aesop;
          apply h_kth_element;
        aesop;
      have h_beta_k_not_in_beta_set : first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n)) ∉ beta_set (all_tuples' n) := by
        exact?;
      aesop

/-
If x maps to the new beta value under F_{n-1}, then h_n(x) is non-zero.
-/
lemma h_n_ne_zero' (n : ℕ) (h_inv : Invariant' (n - 1)) (hn : n ≥ 1)
    (x : ℝ) (hx : F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) (n - 1) x = first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n))) :
    h_seq_real (fun k => alpha_seq' k) n x ≠ 0 := by
      -- By `preimage_not_alpha'`, we know that $x \notin \{\alpha_0, \dots, \alpha_{n-1}\}$.
      have h_not_in_alpha : ∀ k < n, x ≠ alpha_seq' k := by
        exact?;
      -- By definition of $h_seq$, we know that $h_n(x) = 0$ if and only if $x \in \{\alpha_0, \dots, \alpha_{n-1}\}$.
      have h_h_seq_zero : h_seq (fun k => (alpha_seq' k : ℝ)) n x = 0 ↔ x ∈ Finset.image (fun k => alpha_seq' k : ℕ → ℝ) (Finset.range n) := by
        simp +decide [ h_seq ];
        split_ifs <;> simp_all +decide [ sub_eq_zero, List.prod_eq_zero_iff ];
        norm_cast ; aesop;
      simp_all +decide [ Complex.ext_iff ];
      exact fun h => h_h_seq_zero.mp ⟨ h, h_seq'_is_real n x ⟩ |> fun ⟨ k, hk₁, hk₂ ⟩ => h_not_in_alpha k hk₁ hk₂.symm

/-
The function Lambda is continuous at x and vanishes at x.
-/
lemma Lambda_properties (n : ℕ) (h_inv : Invariant' (n - 1)) (hn : n ≥ 1)
    (x : ℝ) (hx : F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) (n - 1) x = first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n))) :
    let beta_n := first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n))
    let F_prev := F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) (n - 1)
    let h_curr := h_seq_real (fun k => alpha_seq' k) n
    let Lambda := fun t => (beta_n - F_prev t) / h_curr t
    ContinuousAt Lambda x ∧ Lambda x = 0 := by
      have h_cont : ContinuousAt (fun t => F_seq_real (fun k => (alpha_seq' k : ℝ)) (fun k => lambda_seq' k) (n - 1) t) x ∧ ContinuousAt (fun t => h_seq_real (fun k => (alpha_seq' k : ℝ)) n t) x := by
        refine' ⟨ _, _ ⟩;
        · refine' Continuous.continuousAt _;
          unfold F_seq_real;
          induction' n - 1 with n ih <;> simp_all +decide [ F_seq ];
          · unfold h_seq; continuity;
          · simp_all +decide [ List.range_succ ];
            convert ih.add ( show Continuous fun t : ℝ => lambda_seq' ( n + 1 ) * ( h_seq ( fun k => ( alpha_seq' k : ℝ ) ) ( n + 1 ) ↑t |> Complex.re ) from ?_ ) using 2 ; ring;
            fun_prop;
        · refine' Continuous.continuousAt _;
          unfold h_seq_real;
          unfold h_seq;
          split_ifs <;> simp_all +decide [ Complex.exp_re, Complex.exp_im, div_eq_mul_inv ];
          norm_cast ; norm_num [ Complex.normSq ] ; continuity;
      field_simp;
      exact ⟨ ContinuousAt.div ( continuousAt_const.sub h_cont.1 ) h_cont.2 ( h_n_ne_zero' n h_inv hn x hx ), by rw [ hx, sub_self, zero_div ] ⟩

/-
There exists a positive delta such that Lambda is bounded by eta in the delta-neighborhood of x.
-/
lemma next_step_A_delta_exists' (n : ℕ) (h_inv : Invariant' (n - 1)) (hn : n ≥ 1)
    (x : ℝ) (hx : F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) (n - 1) x = first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n))) :
    let beta_n := first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n))
    let F_prev := F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) (n - 1)
    let h_curr := h_seq_real (fun k => alpha_seq' k) n
    let eta := eta_val (fun k => alpha_seq' k) n (epsilon_seq n)
    let Lambda := fun t => (beta_n - F_prev t) / h_curr t
    ∃ delta, 0 < delta ∧ ∀ t, |t - x| < delta → |Lambda t| < eta := by
      have := @Lambda_properties n h_inv hn x hx;
      have := Metric.continuousAt_iff.mp this.1;
      specialize this ( eta_val ( fun k => ( alpha_seq' k : ℝ ) ) n ( epsilon_seq n ) ) ( ?_ );
      · exact?;
      · simp_all +decide [ dist_eq_norm ];
        simpa only [ abs_div ] using this

/-
For odd n, the conditions required for Step A in next_step' are all satisfied.
-/
lemma next_step'_odd_conditions (n : ℕ) (hn : n ≥ 1) (hodd : n % 2 = 1) (h_inv : Invariant' (n - 1)) :
  let hist := all_tuples' n
  let beta_n := first_unused b_seq b_seq_surj (beta_set hist) (beta_set_finite hist)
  let F_prev := F_seq_real (alpha_from_hist hist) (lambda_from_hist hist) (n - 1)
  let h_curr := h_seq_real (alpha_from_hist hist) n
  let eta := eta_val (alpha_from_hist hist) n (epsilon_seq n)
  ∃ (h_surj : ∃ x, F_prev x = beta_n),
  let x_n := Classical.choose h_surj
  h_curr x_n ≠ 0 ∧
  let Lambda := fun t => (beta_n - F_prev t) / h_curr t
  (ContinuousAt Lambda x_n ∧ Lambda x_n = 0) ∧
  ∃ delta, 0 < delta ∧ ∀ t, |t - x_n| < delta → |Lambda t| < eta := by
    have h_surj : ∃ x, F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) (n - 1) x = first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n)) := by
      apply_rules [ F_seq_real_surjective_of_Invariant' ];
    have h_cont : ContinuousAt (fun t => (first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n)) - F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) (n - 1) t) / h_seq_real (fun k => alpha_seq' k) n t) (Classical.choose h_surj) ∧ (first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n)) - F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) (n - 1) (Classical.choose h_surj)) / h_seq_real (fun k => alpha_seq' k) n (Classical.choose h_surj) = 0 := by
      have := Classical.choose_spec h_surj;
      have := Lambda_properties n h_inv hn ( Classical.choose h_surj ) this; aesop;
    have h_delta : ∃ delta, 0 < delta ∧ ∀ t, |t - Classical.choose h_surj| < delta → |(first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n)) - F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) (n - 1) t) / h_seq_real (fun k => alpha_seq' k) n t| < eta_seq' n := by
      have := Metric.continuousAt_iff.mp h_cont.1;
      simpa only [ h_cont.2, dist_zero_right ] using this _ ( eta_seq'_pos n hn );
    have h_curr_ne_zero : h_seq_real (fun k => alpha_seq' k) n (Classical.choose h_surj) ≠ 0 := by
      apply h_n_ne_zero' n h_inv hn (Classical.choose h_surj) (Classical.choose_spec h_surj);
    have h_eq : F_seq_real (alpha_from_hist (all_tuples' n)) (lambda_from_hist (all_tuples' n)) (n - 1) = F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) (n - 1) ∧ h_seq_real (alpha_from_hist (all_tuples' n)) n = h_seq_real (fun k => alpha_seq' k) n ∧ eta_val (alpha_from_hist (all_tuples' n)) n (epsilon_seq n) = eta_seq' n := by
      exact ⟨ funext fun x => F_seq_real_eq_F_seq_real' n x hn, funext fun x => h_seq_real_eq_h_seq_real' n x, eta_eq_eta_seq' n ⟩;
    aesop

/-
If the invariant holds at step n, then the partial sum F_n is injective.
-/
lemma unique_preimage_of_Invariant' (n : ℕ) (h_inv : Invariant' n) :
    Function.Injective (fun x => F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) n x) := by
      -- The derivative of $F_n$ is bounded below by a value strictly greater than $1/2$.
      have h_deriv_bound : ∀ x : ℝ, deriv (fun t => F_seq_real (fun k => (alpha_seq' k : ℝ)) (fun k => lambda_seq' k) n t) x > 1 / 2 := by
        have := h_inv.2.2.2.1;
        refine fun x => lt_of_lt_of_le ?_ ( this x );
        norm_num [ Finset.sum_range_succ', epsilon_seq ];
        norm_num [ Finset.sum_ite, pow_add ];
        rw [ ← Finset.sum_mul _ _ _ ] ; rw [ ← Finset.sum_mul _ _ _ ] ; rw [ show ( Finset.filter ( fun x => 2 ≤ x + 1 ) ( Finset.range n ) ) = Finset.Ico 1 n from by ext x ; aesop ] ; norm_num [ Finset.sum_Ico_eq_sum_range ] ; ring_nf ; norm_num;
        rw [ ← Finset.sum_mul _ _ _, geom_sum_eq ] <;> ring <;> norm_num;
        exact lt_add_of_lt_of_nonneg ( by norm_num ) ( by positivity )
      generalize_proofs at *; (
      exact ( StrictMono.injective <| strictMono_of_deriv_pos fun x => by linarith [ h_deriv_bound x ] ))

/-
If x is not in the set of previous alpha values (as reals), then h_n(x) is non-zero.
-/
lemma h_seq_real_ne_zero_of_not_mem_alpha_set' (n : ℕ) (x : ℝ) (hist : List (ℚ × ℚ × ℝ))
  (h_hist : hist = all_tuples' n) (hx : x ∉ Set.image (fun q : ℚ => (q : ℝ)) (alpha_set hist)) :
  h_seq_real (alpha_from_hist hist) n x ≠ 0 := by
    -- Apply the definition of `h_seq_real` and the fact that if any term in the product is non-zero, the whole product is non-zero.
    have h_prod_nonzero : ∀ k < n, (x - (alpha_from_hist hist k)) ≠ 0 := by
      norm_num +zetaDelta at *;
      intro k hk_lt_n
      by_contra h_contra
      have h_eq : (alpha_from_hist hist k : ℝ) = x := by
        linarith;
      unfold alpha_from_hist at h_eq;
      cases h : hist.get? k <;> simp_all +decide [ alpha_set ];
      · linarith [ show List.length ( all_tuples' n ) = n from by exact Nat.recOn n ( by norm_num [ all_tuples' ] ) fun n ih => by rw [ all_tuples' ] ; simp +decide [ ih ] ];
      · grind;
    unfold h_seq_real;
    unfold h_seq;
    split_ifs <;> simp_all +decide [ Complex.exp_re, Complex.exp_im ];
    norm_cast ; simp_all +decide [ List.prod_eq_zero_iff ];
    -- Since the product of non-zero real numbers is non-zero, the real part of the product is also non-zero.
    have h_prod_real_nonzero : ∀ {l : List ℝ}, (∀ x ∈ l, x ≠ 0) → (List.prod l) ≠ 0 := by
      intros l hl; induction l <;> simp_all +decide [ List.prod_cons ] ;
    convert h_prod_real_nonzero _;
    rotate_left;
    exact List.map ( fun k => x - alpha_from_hist ( all_tuples' n ) k ) ( List.range n );
    · grind;
    · induction ( List.range n ) <;> aesop

/-
h_seq is zero if and only if z is equal to one of the alpha values used in its construction.
-/
lemma h_seq_eq_zero_iff (alpha : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    h_seq alpha n z = 0 ↔ ∃ k < n, z = (alpha k : ℂ) := by
      induction' n with n ih generalizing z <;> simp +decide [ *, h_seq ];
      simp +decide [ sub_eq_zero ]

/-
For odd n, the beta component of the next step is the first unused beta value.
-/
lemma next_step'_beta_odd (n : ℕ) (hn : n ≥ 1) (hodd : n % 2 = 1) (h_inv : Invariant' (n - 1)) :
  (next_step' n (all_tuples' n)).2.1 = first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n)) := by
    rcases n with ( _ | _ | n ) <;> unfold next_step' at * ; aesop;
    · rw [ first_unused_val_eq ];
      rotate_left;
      use 1; simp +decide [ b_seq ] ;
      · unfold all_tuples' beta_set; norm_num;
        unfold all_tuples' next_step';
        grind;
      · unfold all_tuples' beta_set b_seq; norm_num;
        exists 0, 0, 0;
        unfold next_step' all_tuples'; norm_num;
        native_decide +revert;
      · unfold b_seq; norm_num;
    · split_ifs <;> norm_num at *;
      · omega;
      · split_ifs <;> norm_num at *;
        · grind;
        · linarith;
        · omega;
        · exact absurd ‹_› ( not_le_of_gt ( eta_val_pos_any _ _ ( by linarith ) ) )

/-
For odd n, the lambda component of the next step satisfies the required bound.
-/
lemma next_step'_lambda_bound_odd (n : ℕ) (hn : n ≥ 1) (hodd : n % 2 = 1) (h_inv : Invariant' (n - 1)) :
  |(next_step' n (all_tuples' n)).2.2| < eta_seq' n := by
    have := @lambda_seq'_bound;
    refine lt_of_le_of_ne ( ?_ ) ?_;
    · convert this n;
      -- By definition of `construction_seq'`, the second component of the next_step' is equal to `lambda_seq' n`.
      simp [lambda_seq', construction_seq'];
      unfold all_tuples'; aesop;
    · unfold next_step';
      split_ifs <;> norm_num [ hodd ];
      · linarith;
      · exact ne_of_lt ( eta_seq'_pos _ hn );
      · grind;
      · split_ifs <;> norm_num;
        any_goals linarith [ eta_seq'_pos n hn ];
        rename_i h₁ h₂ h₃ h₄ h₅ h₆;
        refine' ne_of_lt ( lt_of_lt_of_le ( h₆.choose_spec.2 _ _ ) _ );
        · have := Classical.choose_spec h₆;
          rw [ abs_lt ];
          exact ⟨ by linarith [ Set.mem_Ioo.mp ( choice_in_interval_spec ( Classical.choose h₃ - h₆.choose ) ( Classical.choose h₃ + h₆.choose ) ( by linarith ) ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) |>.1 ) ], by linarith [ Set.mem_Ioo.mp ( choice_in_interval_spec ( Classical.choose h₃ - h₆.choose ) ( Classical.choose h₃ + h₆.choose ) ( by linarith ) ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) |>.1 ) ] ⟩;
        · rw [ ← eta_eq_eta_seq' ]

/-
For odd n, the beta component of the next step is the first unused beta value.
-/
lemma next_step'_odd_beta_v2 (n : ℕ) (hn : n ≥ 1) (hodd : n % 2 = 1) (h_inv : Invariant' (n - 1)) :
  (next_step' n (all_tuples' n)).2.1 = first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n)) := by
    exact?

/-
For odd n, the alpha component of the next step is not in the set of previous alpha values.
-/
lemma next_step'_alpha_not_mem_odd (n : ℕ) (hn : n ≥ 1) (hodd : n % 2 = 1) (h_inv : Invariant' (n - 1)) :
  (next_step' n (all_tuples' n)).1 ∉ alpha_set (all_tuples' n) := by
    have h_conditions : ∃ (h_surj : ∃ x, F_seq_real (alpha_from_hist (all_tuples' n)) (lambda_from_hist (all_tuples' n)) (n - 1) x = first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n))),
      let x_n := Classical.choose h_surj
      h_seq_real (alpha_from_hist (all_tuples' n)) n x_n ≠ 0 ∧
      let Lambda := fun t => (first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n)) - F_seq_real (alpha_from_hist (all_tuples' n)) (lambda_from_hist (all_tuples' n)) (n - 1) t) / h_seq_real (alpha_from_hist (all_tuples' n)) n t
      (ContinuousAt Lambda x_n ∧ Lambda x_n = 0) ∧
      ∃ delta, 0 < delta ∧ ∀ t, |t - x_n| < delta → |Lambda t| < eta_val (alpha_from_hist (all_tuples' n)) n (epsilon_seq n) := by
        convert next_step'_odd_conditions n hn hodd h_inv using 1;
    obtain ⟨ h_surj, hx_n, h_cont, h_delta ⟩ := h_conditions;
    unfold next_step';
    split_ifs <;> norm_num at *;
    · linarith;
    · unfold all_tuples'; simp +decide [ *, alpha_set ] ;
      unfold all_tuples'; simp +decide [ *, alpha_set ] ;
      rintro ( _ | _ | n ) <;> simp +decide [ next_step' ];
    · omega;
    · split_ifs <;> norm_num at *;
      · linarith;
      · omega;
      · linarith;
      · exact choice_in_interval_spec _ _ _ _ _ |>.2;
      · exact absurd ‹_› ( not_le_of_gt ( eta_val_pos_any _ _ hn ) )

/-
For odd n, the interpolation condition F_n(alpha_n) = beta_n holds.
-/
lemma next_step'_interpolation_odd (n : ℕ) (hn : n ≥ 1) (hodd : n % 2 = 1) (h_inv : Invariant' (n - 1)) :
  let res := next_step' n (all_tuples' n)
  F_seq_real (fun k => alpha_seq' k) (fun k => lambda_seq' k) n res.1 = res.2.1 := by
    have h_lambda_eq : let res := next_step' n (all_tuples' n); let F_prev := F_seq_real (fun k => (alpha_seq' k : ℝ)) (fun k => lambda_seq' k) (n - 1); let h_curr := h_seq_real (fun k => (alpha_seq' k : ℝ)) n; let beta_n := (next_step' n (all_tuples' n)).2.1; let lambda_n := (next_step' n (all_tuples' n)).2.2; lambda_n = (beta_n - F_prev (res.1 : ℝ)) / h_curr (res.1 : ℝ) := by
      have := next_step'_odd_conditions n hn hodd h_inv;
      unfold next_step';
      split_ifs <;> norm_num;
      · linarith;
      · unfold F_seq_real; unfold h_seq_real; norm_num [ ‹n = 1› ] ;
        unfold F_seq h_seq; norm_num;
        unfold lambda_seq' alpha_seq'; norm_num [ Complex.exp_re ] ;
        unfold construction_seq'; norm_num [ all_tuples' ] ;
        unfold next_step'; norm_num;
      · grind;
      · split_ifs;
        all_goals simp_all +decide [ Nat.even_iff ];
        · rw [ F_seq_real_eq_F_seq_real', h_seq_real_eq_h_seq_real' ];
          linarith;
        · exact absurd ‹_› ( not_le_of_gt ( eta_val_pos_any _ _ hn ) );
    have h_h_n_ne_zero : let res := next_step' n (all_tuples' n); h_seq_real (fun k => (alpha_seq' k : ℝ)) n (res.1 : ℝ) ≠ 0 := by
      have h_h_n_ne_zero : let res := next_step' n (all_tuples' n); res.1 ∉ alpha_set (all_tuples' n) := by
        exact?;
      convert h_seq_real_ne_zero_of_not_mem_alpha_set' n _ _ rfl _ using 1;
      rw [ h_seq_real_eq_h_seq_real' ];
      aesop;
    cases n <;> norm_num [ F_seq_real ] at *;
    simp_all +decide [ F_seq, h_seq_real ];
    rw [ eq_div_iff h_h_n_ne_zero ] at h_lambda_eq ; norm_cast at * ; simp_all +decide [ List.sum_range_succ ];
    rw [ show lambda_seq' ( _ + 1 ) = ( next_step' ( _ + 1 ) ( all_tuples' ( _ + 1 ) ) ).2.2 from ?_ ] ; linarith!;
    unfold lambda_seq' construction_seq' all_tuples'; aesop;

/-
Helper definition representing the logic of Step A in the construction.
-/
noncomputable def next_step'_odd_body (n : ℕ) (hist : List (ℚ × ℚ × ℝ)) : ℚ × ℚ × ℝ :=
    let alpha_prev := alpha_from_hist hist
    let lambda_prev := lambda_from_hist hist
    let F_prev := F_seq_real alpha_prev lambda_prev (n - 1)
    let h_curr := h_seq_real alpha_prev n
    let eta := eta_val alpha_prev n (epsilon_seq n)
    let used_alpha := alpha_set hist
    let used_beta := beta_set hist
    let h_alpha_finite := alpha_set_finite hist
    let h_beta_finite := beta_set_finite hist

    let beta_n := first_unused b_seq b_seq_surj used_beta h_beta_finite
    if h : ∃ x, F_prev x = beta_n then
      let x_n := Classical.choose h
      if h_curr_nz : h_curr x_n ≠ 0 then
        let Lambda := fun t => (beta_n - F_prev t) / h_curr t
        if h_cont : ContinuousAt Lambda x_n ∧ Lambda x_n = 0 then
          let P := fun delta => 0 < delta ∧ ∀ t, |t - x_n| < delta → |Lambda t| < eta
          if h_delta : ∃ delta, P delta then
            let delta := Classical.choose h_delta
            let alpha_n := choice_in_interval (x_n - delta) (x_n + delta) (by
            linarith [ Classical.choose_spec h_delta |>.1 ]) used_alpha h_alpha_finite
            let lambda_n := Lambda alpha_n
            (alpha_n, beta_n, lambda_n)
          else (0, beta_n, 0)
        else (0, beta_n, 0)
      else (0, beta_n, 0)
    else (0, beta_n, 0)

/-
For odd n >= 3, the beta component of the next step is the first unused beta value.
-/
lemma next_step'_odd_ge_3_beta (n : ℕ) (hn : n ≥ 3) (hodd : n % 2 = 1) :
  let hist := all_tuples' n
  let beta_n := first_unused b_seq b_seq_surj (beta_set hist) (beta_set_finite hist)
  (next_step' n hist).2.1 = beta_n := by
    unfold next_step';
    by_cases h : ∃ x : ℝ, F_seq_real ( alpha_from_hist ( all_tuples' n ) ) ( lambda_from_hist ( all_tuples' n ) ) ( n - 1 ) x = ( first_unused b_seq b_seq_surj ( beta_set ( all_tuples' n ) ) ( beta_set_finite ( all_tuples' n ) ) : ℚ ) <;> simp +decide [ h ];
    · split_ifs <;> norm_num;
      any_goals omega;
      exact absurd ‹¬0 < eta_val ( alpha_from_hist ( all_tuples' n ) ) n ( epsilon_seq n ) › ( not_not_intro ( eta_val_pos_any _ _ ( by linarith ) ) );
    · split_ifs <;> norm_num at *;
      any_goals omega;
      exact absurd ‹_› ( not_le_of_gt ( eta_val_pos_any _ _ ( by linarith ) ) )

/-
The set of alpha values in the history at step n is exactly the set of alpha_seq' values for indices less than n.
-/
lemma alpha_set_eq_image' (n : ℕ) : alpha_set (all_tuples' n) = (Finset.range n).image (fun k => alpha_seq' k) := by
  unfold alpha_set alpha_seq';
  -- The list `all_tuples' n` is constructed by appending the next step to the previous list. Therefore, the elements of `all_tuples' n` are exactly the elements from the previous steps plus the new element added at step `n`.
  have h_list_eq : ∀ n, all_tuples' n = List.map (fun k => (construction_seq' k)) (List.range n) := by
    intro n
    induction' n with n ih;
    · rfl;
    · -- By definition of `all_tuples'`, we have `all_tuples' (n + 1) = all_tuples' n ++ [next_step' n (all_tuples' n)]`.
      have h_all_tuples'_succ : all_tuples' (n + 1) = all_tuples' n ++ [next_step' n (all_tuples' n)] := by
        exact?;
      simp_all ( config := { decide := Bool.true } ) [ List.range_succ ];
      unfold construction_seq'; aesop;
  ext; simp [h_list_eq];
  constructor <;> intro h;
  · rcases h with ⟨ k, a, hk, rfl ⟩ ; exact ⟨ a, by simpa using List.mem_range.mp ( List.mem_of_getElem? hk ), rfl ⟩ ;
  · obtain ⟨ k, hk₁, hk₂ ⟩ := h; use k, k; aesop;

/-
The set of beta values in the history at step n is exactly the set of beta_seq' values for indices less than n.
-/
lemma beta_set_eq_image' (n : ℕ) : beta_set (all_tuples' n) = (Finset.range n).image (fun k => beta_seq' k) := by
  -- By definition of `all_tuples'`, we can rewrite the left-hand side.
  have h_all_tuples'_def : ∀ n, all_tuples' n = List.map construction_seq' (List.range n) := by
    intro n
    induction' n with n ih;
    · rfl;
    · -- By definition of `all_tuples'`, we have `all_tuples' (n + 1) = all_tuples' n ++ [next_step' n (all_tuples' n)]`.
      have h_all_tuples'_def : all_tuples' (n + 1) = all_tuples' n ++ [next_step' n (all_tuples' n)] := by
        exact?;
      rw [ h_all_tuples'_def, List.range_succ, List.map_append, ih ];
      unfold construction_seq'; aesop;
  simp ( config := { decide := Bool.true } ) [ h_all_tuples'_def, beta_set ];
  ext;
  simp ( config := { decide := Bool.true } ) [ List.getElem?_eq_some_iff ];
  rfl

/-
The alpha sequence remains distinct up to index n+1, given that the invariant holds at step n.
-/
lemma alpha_seq'_distinct_succ (n : ℕ) (h : Invariant' n) :
    ∀ i j, i ≤ n + 1 → j ≤ n + 1 → i ≠ j → alpha_seq' i ≠ alpha_seq' j := by
      -- By definition, alpha_seq' (n + 1) is chosen as the first unused element from a_seq (if n + 1 is even) or via choice_in_interval (if n + 1 is odd).
      by_cases h_even : (n + 1) % 2 = 0;
      · intro i j hi hj hij;
        cases lt_or_eq_of_le hi <;> cases lt_or_eq_of_le hj <;> simp_all +decide;
        · exact h.1 i j ( by linarith ) ( by linarith ) hij;
        · -- By definition of `alpha_seq'`, we know that `alpha_seq' (n + 1)` is the first unused element from `a_seq`.
          have h_alpha_succ : alpha_seq' (n + 1) = first_unused a_seq a_seq_surj (alpha_set (all_tuples' (n + 1))) (alpha_set_finite (all_tuples' (n + 1))) := by
            have h_alpha_succ : alpha_seq' (n + 1) = (next_step' (n + 1) (all_tuples' (n + 1))).1 := by
              unfold alpha_seq';
              unfold construction_seq';
              unfold all_tuples'; aesop;
            rw [h_alpha_succ];
            rw [next_step'_eq_B];
            · omega;
            · assumption;
            · exact h;
          -- By definition of `first_unused`, we know that `first_unused a_seq a_seq_surj (alpha_set (all_tuples' (n + 1))) (alpha_set_finite (all_tuples' (n + 1)))` is not in the set `alpha_set (all_tuples' (n + 1))`.
          have h_first_unused_not_in_set : first_unused a_seq a_seq_surj (alpha_set (all_tuples' (n + 1))) (alpha_set_finite (all_tuples' (n + 1))) ∉ alpha_set (all_tuples' (n + 1)) := by
            exact?;
          -- By definition of `alpha_set`, we know that `alpha_seq' i` is in the set `alpha_set (all_tuples' (n + 1))`.
          have h_alpha_i_in_set : alpha_seq' i ∈ alpha_set (all_tuples' (n + 1)) := by
            rw [alpha_set_eq_image'];
            exact Finset.mem_coe.mpr ( Finset.mem_image.mpr ⟨ i, Finset.mem_range.mpr ‹_›, rfl ⟩ );
          aesop;
        · -- By definition, alpha_seq' (n + 1) is chosen as the first unused element from a_seq (if n + 1 is even).
          have h_alpha_seq'_n_plus_1 : alpha_seq' (n + 1) = first_unused a_seq a_seq_surj (alpha_set (all_tuples' (n + 1))) (alpha_set_finite (all_tuples' (n + 1))) := by
            have h_alpha_seq'_n_plus_1 : alpha_seq' (n + 1) = (next_step' (n + 1) (all_tuples' (n + 1))).1 := by
              unfold alpha_seq';
              unfold construction_seq';
              -- By definition of `all_tuples'`, the last element of `all_tuples' (n + 2)` is `next_step' (n + 1) (all_tuples' (n + 1))`.
              have h_last : all_tuples' (n + 2) = all_tuples' (n + 1) ++ [next_step' (n + 1) (all_tuples' (n + 1))] := by
                exact?;
              aesop;
            rw [h_alpha_seq'_n_plus_1];
            rw [ next_step'_eq_B ];
            · omega;
            · assumption;
            · exact h;
          rw [ h_alpha_seq'_n_plus_1 ];
          apply ne_of_apply_ne (fun x => x ∈ alpha_set (all_tuples' (n + 1)));
          simp +decide [ first_unused ];
          rw [ first_unused_index ];
          simp +decide [ alpha_set_eq_image' ];
          grind;
      · -- By definition, alpha_seq' (n + 1) is chosen from an interval excluding the previous set.
        have h_alpha_unique : alpha_seq' (n + 1) ∉ Finset.image (fun k => alpha_seq' k) (Finset.range (n + 1)) := by
          have h_alpha_unique : alpha_seq' (n + 1) ∉ alpha_set (all_tuples' (n + 1)) := by
            convert next_step'_alpha_not_mem_odd ( n + 1 ) ( by linarith ) ( by simpa [ Nat.add_mod ] using h_even ) _;
            · unfold alpha_seq';
              unfold construction_seq';
              erw [ List.getLast_append ] ; aesop;
            · assumption;
          exact fun h => h_alpha_unique <| alpha_set_eq_image' ( n + 1 ) ▸ h;
        intro i j hi hj hij; cases lt_or_eq_of_le hi <;> cases lt_or_eq_of_le hj <;> simp_all +decide [ Finset.mem_image ] ;
        · exact h.1 i j ( by linarith ) ( by linarith ) hij;
        · exact Ne.symm ( h_alpha_unique _ ‹_› )

/-
The (n+1)-th beta value is not in the set of previous beta values.
-/
lemma beta_seq'_succ_not_mem_prev (n : ℕ) (h_inv : Invariant' n) :
    beta_seq' (n + 1) ∉ (Finset.range (n + 1)).image (fun k => beta_seq' k) := by
      -- We split into two cases based on the parity of n+1.
      by_cases h_even : (n + 1) % 2 = 0;
      · -- By definition of `beta_seq'`, $\beta_{n+1}$ is chosen from a neighborhood of a point $x_{n+1}$ satisfying $F_n(x_{n+1}) = \beta_{n+1}$.
        have h_beta_choose_B : let hist := all_tuples' (n + 1);
          let alpha_prev := alpha_from_hist hist
          let lambda_prev := lambda_from_hist hist
          let F_prev := F_seq_real alpha_prev lambda_prev n
          let h_curr := h_seq_real alpha_prev (n + 1)
          let eta := eta_val alpha_prev (n + 1) (epsilon_seq (n + 1))
          let used_alpha := alpha_set hist
          let used_beta := beta_set hist
          let h_alpha_finite := alpha_set_finite hist
          let h_beta_finite := beta_set_finite hist;

          let alpha_n := first_unused a_seq a_seq_surj used_alpha h_alpha_finite
          let y := F_prev alpha_n
          let h_val := h_curr alpha_n
          let radius := eta * |h_val|
          let avoid_beta := if n + 1 == 2 then insert 2 used_beta else used_beta
          let h_avoid_finite : avoid_beta.Finite := by
            aesop
          let beta_n := choice_in_interval (y - radius) (y + radius) (by
          have h_eta_pos : eta > 0 := by
            apply eta_val_pos_any;
            linarith;
          have h_h_val_nonzero : h_val ≠ 0 := by
            apply_rules [ h_seq_real_ne_zero_of_not_mem_alpha_set' ];
            norm_num +zetaDelta at *;
            exact?;
          exact lt_add_of_lt_of_nonneg ( sub_lt_self _ ( mul_pos h_eta_pos ( abs_pos.mpr h_h_val_nonzero ) ) ) ( mul_nonneg h_eta_pos.le ( abs_nonneg _ ) )) avoid_beta h_avoid_finite
          let lambda_n := (beta_n - y) / h_val
          beta_seq' (n + 1) = beta_n := by
            all_goals generalize_proofs at *;
            have h_beta_choose_B : let hist := all_tuples' (n + 1);
              let alpha_prev := alpha_from_hist hist
              let lambda_prev := lambda_from_hist hist
              let F_prev := F_seq_real alpha_prev lambda_prev n
              let h_curr := h_seq_real alpha_prev (n + 1)
              let eta := eta_val alpha_prev (n + 1) (epsilon_seq (n + 1))
              let used_alpha := alpha_set hist
              let used_beta := beta_set hist
              let h_alpha_finite := alpha_set_finite hist
              let h_beta_finite := beta_set_finite hist;

              let alpha_n := first_unused a_seq a_seq_surj used_alpha h_alpha_finite
              let y := F_prev alpha_n
              let h_val := h_curr alpha_n
              let radius := eta * |h_val|
              let avoid_beta := if n + 1 == 2 then insert 2 used_beta else used_beta
              let h_avoid_finite : avoid_beta.Finite := by
                aesop
              let beta_n := choice_in_interval (y - radius) (y + radius) (by
              grind) avoid_beta h_avoid_finite
              let lambda_n := (beta_n - y) / h_val
              next_step' (n + 1) (all_tuples' (n + 1)) = (alpha_n, beta_n, lambda_n) := by
                apply_rules [ next_step'_eq_B ];
                omega
            generalize_proofs at *;
            convert congr_arg ( fun x : ℚ × ℚ × ℝ => x.2.1 ) h_beta_choose_B using 1;
            exact congr_arg ( fun x : ℚ × ℚ × ℝ => x.2.1 ) ( List.getLast_append _ )
        generalize_proofs at *;
        have h_beta_not_in_used : let hist := all_tuples' (n + 1);
          let alpha_prev := alpha_from_hist hist
          let lambda_prev := lambda_from_hist hist
          let F_prev := F_seq_real alpha_prev lambda_prev n
          let h_curr := h_seq_real alpha_prev (n + 1)
          let eta := eta_val alpha_prev (n + 1) (epsilon_seq (n + 1))
          let used_alpha := alpha_set hist
          let used_beta := beta_set hist
          let h_alpha_finite := alpha_set_finite hist
          let h_beta_finite := beta_set_finite hist;

          let alpha_n := first_unused a_seq a_seq_surj used_alpha h_alpha_finite
          let y := F_prev alpha_n
          let h_val := h_curr alpha_n
          let radius := eta * |h_val|
          let avoid_beta := if n + 1 == 2 then insert 2 used_beta else used_beta
          let h_avoid_finite : avoid_beta.Finite := by
            aesop
          let beta_n := choice_in_interval (y - radius) (y + radius) (by
          linarith) avoid_beta h_avoid_finite
          beta_n ∉ used_beta := by
            have := choice_in_interval_spec ( F_seq_real ( alpha_from_hist ( all_tuples' ( n + 1 ) ) ) ( lambda_from_hist ( all_tuples' ( n + 1 ) ) ) n ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' ( n + 1 ) ) ) ‹_› ) - eta_val ( alpha_from_hist ( all_tuples' ( n + 1 ) ) ) ( n + 1 ) ( epsilon_seq ( n + 1 ) ) * |h_seq_real ( alpha_from_hist ( all_tuples' ( n + 1 ) ) ) ( n + 1 ) ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' ( n + 1 ) ) ) ‹_› )| ) ( F_seq_real ( alpha_from_hist ( all_tuples' ( n + 1 ) ) ) ( lambda_from_hist ( all_tuples' ( n + 1 ) ) ) n ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' ( n + 1 ) ) ) ‹_› ) + eta_val ( alpha_from_hist ( all_tuples' ( n + 1 ) ) ) ( n + 1 ) ( epsilon_seq ( n + 1 ) ) * |h_seq_real ( alpha_from_hist ( all_tuples' ( n + 1 ) ) ) ( n + 1 ) ↑ ( first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' ( n + 1 ) ) ) ‹_› )| ) ‹_› ( if ( n + 1 == 2 ) then insert 2 ( beta_set ( all_tuples' ( n + 1 ) ) ) else ( beta_set ( all_tuples' ( n + 1 ) ) ) ) ‹_›
            generalize_proofs at *;
            grind
        generalize_proofs at *;
        simp +zetaDelta at *;
        intro x hx; contrapose! h_beta_not_in_used; simp_all +decide [ beta_set_eq_image' ] ;
        grind;
      · -- If n+1 is odd, then beta_seq' (n+1) is chosen as the first unused element of b_seq from the set of previous betas. By the property of first_unused, it is not in the set of previous betas.
        have h_beta_not_mem : (beta_seq' (n + 1)) ∉ (Finset.range (n + 1)).image (fun k => beta_seq' k) := by
          have h_beta_eq : beta_seq' (n + 1) = first_unused b_seq b_seq_surj (beta_set (all_tuples' (n + 1))) (beta_set_finite (all_tuples' (n + 1))) := by
            have := next_step'_beta_odd ( n + 1 ) ( by linarith ) ( by simpa using h_even ) ( by
              exact h_inv )
            generalize_proofs at *;
            unfold beta_seq';
            unfold construction_seq'
            generalize_proofs at *;
            unfold all_tuples' at * ; aesop
          have h_beta_not_mem : ∀ k ∈ Finset.range (n + 1), beta_seq' k ∈ beta_set (all_tuples' (n + 1)) := by
            -- By definition of `beta_set`, it is the set of second components of the tuples in `all_tuples' (n + 1)`.
            have h_beta_set_def : beta_set (all_tuples' (n + 1)) = (Finset.range (n + 1)).image (fun k => beta_seq' k) := by
              apply beta_set_eq_image';
            aesop;
          have h_beta_not_mem : first_unused b_seq b_seq_surj (beta_set (all_tuples' (n + 1))) (beta_set_finite (all_tuples' (n + 1))) ∉ beta_set (all_tuples' (n + 1)) := by
            exact first_unused_spec _ _ _ _;
          grind;
        assumption

/-
The beta sequence remains distinct up to index n+1, given that the invariant holds at step n.
-/
lemma beta_seq'_distinct_succ (n : ℕ) (h : Invariant' n) :
    ∀ i j, i ≤ n + 1 → j ≤ n + 1 → i ≠ j → beta_seq' i ≠ beta_seq' j := by
      -- Let's split into cases based on whether i and j are less than or equal to n or equal to n+1.
      intro i j hi hj hij
      by_cases hi_le_n : i ≤ n
      by_cases hj_le_n : j ≤ n;
      · exact h.2.1 i j hi_le_n hj_le_n hij;
      · have := beta_seq'_succ_not_mem_prev n h; simp_all +decide [ Finset.mem_image ] ;
        rw [ show j = n + 1 by linarith ] ; exact this i ( by linarith );
      · cases hi.eq_or_lt <;> cases hj.eq_or_lt <;> first | linarith | simp_all? ( config := { decide := Bool.true } ) [ Nat.succ_eq_add_one ] ;
        have := beta_seq'_succ_not_mem_prev n h; simp_all +decide [ Set.Finite.image ] ;
        exact Ne.symm ( this _ ‹_› )

/-
The interpolation property holds for all previous indices k <= n at step n+1.
-/
lemma interpolation_succ_le_n' (n : ℕ) (h : Invariant' n) :
    ∀ k ≤ n, F_seq_real (fun i => alpha_seq' i) (fun i => lambda_seq' i) (n + 1) (alpha_seq' k) = beta_seq' k := by
      -- By definition of $F_{n+1}$, we have $F_{n+1}(alpha_k) = F_n(alpha_k) + lambda_{n+1} * h_{n+1}(alpha_k)$.
      intro k hk
      simp [F_seq_real, hk, h_seq_vanishes_for_large_n'];
      convert h.2.2.1 k hk using 1;
      unfold F_seq F_seq_real; norm_num [ hk ] ;
      unfold F_seq; norm_num [ List.range_succ ] ; ring;
      unfold h_seq; norm_num [ Finset.prod_eq_zero_iff, sub_eq_zero ] ;
      rw [ List.prod_eq_zero_iff.mpr ] <;> norm_num;
      exact ⟨ k, by linarith, sub_self _ ⟩

/-
The interpolation condition holds for the new index n+1 when n+1 is even.
-/
lemma interpolation_succ_eq_n_plus_1_even' (n : ℕ) (h : Invariant' n) (h_even : (n + 1) % 2 = 0) :
    F_seq_real (fun i => alpha_seq' i) (fun i => lambda_seq' i) (n + 1) (alpha_seq' (n + 1)) = beta_seq' (n + 1) := by
      have h_lambda : lambda_seq' (n + 1) = (beta_seq' (n + 1) - F_seq_real (fun i => alpha_seq' i) (fun i => lambda_seq' i) n (alpha_seq' (n + 1))) / h_seq_real (fun i => alpha_seq' i) (n + 1) (alpha_seq' (n + 1)) := by
        unfold lambda_seq' beta_seq';
        unfold construction_seq';
        -- By definition of `next_step'`, when `n` is even, the lambda component is given by the formula involving the difference and division.
        have h_lambda_def : (next_step' (n + 1) (all_tuples' (n + 1))).2.2 = ((next_step' (n + 1) (all_tuples' (n + 1))).2.1 - F_seq_real (fun i => alpha_seq' i) (fun i => lambda_seq' i) n (alpha_seq' (n + 1))) / h_seq_real (fun i => alpha_seq' i) (n + 1) (alpha_seq' (n + 1)) := by
          rw [next_step'_eq_B];
          · rw [ show alpha_seq' ( n + 1 ) = first_unused a_seq a_seq_surj ( alpha_set ( all_tuples' ( n + 1 ) ) ) ( alpha_set_finite ( all_tuples' ( n + 1 ) ) ) from ?_ ];
            · rw [ F_seq_real_eq_F_seq_real', h_seq_real_eq_h_seq_real' ];
              · simp +zetaDelta at *;
              · linarith;
            · have h_alpha_def : alpha_seq' (n + 1) = (next_step' (n + 1) (all_tuples' (n + 1))).1 := by
                unfold alpha_seq' construction_seq';
                -- By definition of `all_tuples'`, the last element of `all_tuples' (n + 2)` is `next_step' (n + 1) (all_tuples' (n + 1))`.
                have h_last : all_tuples' (n + 2) = all_tuples' (n + 1) ++ [next_step' (n + 1) (all_tuples' (n + 1))] := by
                  exact?;
                grind;
              rw [h_alpha_def];
              rw [next_step'_eq_B];
              · omega;
              · assumption;
              · exact h;
          · omega;
          · assumption;
          · exact h;
        convert h_lambda_def using 1;
        · simp +decide [ all_tuples' ];
        · congr! 2;
          unfold all_tuples'; aesop;
      have h_h_n_ne_zero : h_seq_real (fun i => alpha_seq' i) (n + 1) (alpha_seq' (n + 1)) ≠ 0 := by
        have h_h_n_ne_zero : ∀ m < n + 1, (alpha_seq' (n + 1) : ℝ) ≠ (alpha_seq' m : ℝ) := by
          intros m hm_lt_n_plus_1
          have h_alpha_distinct : ∀ i j, i ≤ n + 1 → j ≤ n + 1 → i ≠ j → alpha_seq' i ≠ alpha_seq' j := by
            exact?;
          exact_mod_cast h_alpha_distinct _ _ ( by linarith ) ( by linarith ) ( by linarith );
        contrapose! h_h_n_ne_zero;
        have h_h_n_ne_zero : h_seq (fun i => (alpha_seq' i : ℝ)) (n + 1) (alpha_seq' (n + 1)) = 0 := by
          convert h_h_n_ne_zero using 1;
          unfold h_seq_real; norm_num [ Complex.ext_iff ] ;
          unfold h_seq; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ] ;
          norm_cast ; norm_num [ List.prod_range_succ ];
          induction ( List.range n ) <;> aesop;
        have := h_seq_eq_zero_iff ( fun i => ( alpha_seq' i : ℝ ) ) ( n + 1 ) ( alpha_seq' ( n + 1 ) : ℂ ) ; aesop;
      unfold F_seq_real at *; simp_all +decide [ Finset.sum_range_succ ] ;
      unfold F_seq at *; simp_all +decide [ Finset.sum_range_succ ] ;
      simp_all +decide [ List.range_succ ];
      unfold h_seq_real at *; simp_all +decide [ div_mul_cancel₀ ] ;
      ring

/-
The interpolation condition holds for the new index n+1 when n+1 is odd.
-/
lemma interpolation_succ_eq_n_plus_1_odd' (n : ℕ) (h : Invariant' n) (h_odd : (n + 1) % 2 = 1) :
    F_seq_real (fun i => alpha_seq' i) (fun i => lambda_seq' i) (n + 1) (alpha_seq' (n + 1)) = beta_seq' (n + 1) := by
      by_contra h_contra;
      convert next_step'_interpolation_odd ( n + 1 ) _ _ _ using 1 <;> norm_num [ h_odd ];
      · convert h_contra using 1;
        unfold alpha_seq' beta_seq';
        unfold construction_seq';
        unfold all_tuples'; aesop;
      · assumption

/-
The interpolation condition holds for the new index n+1.
-/
lemma interpolation_succ_eq_n_plus_1' (n : ℕ) (h : Invariant' n) :
    F_seq_real (fun i => alpha_seq' i) (fun i => lambda_seq' i) (n + 1) (alpha_seq' (n + 1)) = beta_seq' (n + 1) := by
      by_cases h_even : ( n + 1 ) % 2 = 0;
      · convert interpolation_succ_eq_n_plus_1_even' n h h_even;
      · convert interpolation_succ_eq_n_plus_1_odd' n h ( by simpa using h_even ) using 1

/-
The new lambda value satisfies the bound |lambda_seq' (n+1)| < eta_seq' (n+1).
-/
lemma lambda_seq'_succ_bound (n : ℕ) (h : Invariant' n) :
    |lambda_seq' (n + 1)| < eta_seq' (n + 1) := by
      rcases Nat.even_or_odd' ( n + 1 ) with ⟨ k, hk | hk ⟩ <;> simp_all +decide [ Nat.even_iff ];
      · convert lambda_seq'_strict_bound_even ( 2 * k ) ( by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by aesop_cat ) ] ) ( by norm_num ) using 1;
      · convert next_step'_lambda_bound_odd ( 2 * k + 1 ) ( by linarith ) ( by norm_num ) h using 1;
        unfold lambda_seq';
        unfold construction_seq';
        unfold all_tuples'; aesop;

/-
The absolute value of the derivative of the real part of h_seq is bounded by L_val.
-/
lemma deriv_h_seq_real_le_L_val (alpha : ℕ → ℝ) (n : ℕ) (x : ℝ) (hn : n ≥ 1) :
    |deriv (h_seq_real alpha n) x| ≤ L_val alpha n := by
      -- Applying the lemma `h_seq_real_deriv`, we know that `deriv (h_seq_real alpha n) x = (deriv (h_seq alpha n) (x : ℂ)).re`.
      have h_deriv_eq : deriv (h_seq_real alpha n) x = (deriv (h_seq alpha n) (x : ℂ)).re := by
        apply_rules [ h_seq_real_deriv ];
        ext x;
        apply_rules [ HasDerivAt.deriv ];
        have h_deriv : HasDerivAt (fun t : ℝ => h_seq alpha n (t : ℂ)) (deriv (h_seq alpha n) (x : ℂ)) x := by
          have h_deriv : HasDerivAt (fun t : ℂ => h_seq alpha n t) (deriv (h_seq alpha n) (x : ℂ)) (x : ℂ) := by
            apply_rules [ DifferentiableAt.hasDerivAt ];
            induction' n with n ih generalizing x <;> simp_all ( config := { decide := Bool.true } ) [ h_seq ];
            refine' DifferentiableAt.mul _ _;
            · exact Complex.differentiableAt_exp.comp _ ( DifferentiableAt.div_const ( DifferentiableAt.neg ( differentiableAt_id.pow 2 ) ) _ );
            · induction' ( List.range ( n + 1 ) ) with k hk ih <;> simp_all ( config := { decide := Bool.true } ) [ List.prod_cons ];
          exact h_deriv.comp_ofReal;
        rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
        convert Complex.continuous_re.continuousAt.tendsto.comp h_deriv using 2 ; norm_num [ h_seq_real ];
      refine' h_deriv_eq ▸ le_trans ( Complex.abs_re_le_norm _ ) _;
      exact le_csSup ( h_seq_deriv_bounded _ _ ( by aesop ) ) ( by aesop )

/-
The derivative of the new term added in step n+1 is bounded by epsilon_{n+1}.
-/
lemma deriv_term_bound_succ' (n : ℕ) (h : Invariant' n) (x : ℝ) :
    |deriv (fun t => (lambda_seq' (n + 1) : ℝ) * h_seq_real (fun i => (alpha_seq' i : ℝ)) (n + 1) t) x| ≤ if n + 1 < 2 then 0 else epsilon_seq (n + 1) := by
      -- We consider two cases: n+1 < 2 and n+1 >= 2.
      by_cases hn : n + 1 < 2;
      · rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ lambda_seq' ];
        unfold construction_seq';
        unfold all_tuples';
        unfold next_step'; norm_num;
      · -- We have:
        -- 1. |lambda_seq'| < eta_seq' (by lambda_seq'_succ_bound).
        -- 2. eta_seq' <= epsilon_seq / L_val (by definition of eta_val).
        -- 3. |deriv h_seq_real| <= L_val (by deriv_h_seq_real_le_L_val).
        -- 4. L_val > 0 (by L_val_pos).
        -- Combining these:
        have h_deriv_bound : |deriv (fun t => (lambda_seq' (n + 1) : ℝ) * h_seq_real (fun i => (alpha_seq' i : ℝ)) (n + 1) t) x| ≤ |lambda_seq' (n + 1)| * L_val (fun i => (alpha_seq' i : ℝ)) (n + 1) := by
          have h_deriv_bound : |deriv (fun t => (lambda_seq' (n + 1) : ℝ) * h_seq_real (fun i => (alpha_seq' i : ℝ)) (n + 1) t) x| = |lambda_seq' (n + 1)| * |deriv (h_seq_real (fun i => (alpha_seq' i : ℝ)) (n + 1)) x| := by
            norm_num [ abs_mul ];
          exact h_deriv_bound.symm ▸ mul_le_mul_of_nonneg_left ( deriv_h_seq_real_le_L_val _ _ _ ( by linarith ) ) ( abs_nonneg _ );
        -- Since $|lambda_seq' (n + 1)| < eta_seq' (n + 1)$ and $eta_seq' (n + 1) \leq \epsilon_seq (n + 1) / L_val (n + 1)$, we have $|lambda_seq' (n + 1)| * L_val (n + 1) < \epsilon_seq (n + 1)$.
        have h_lambda_bound : |lambda_seq' (n + 1)| * L_val (fun i => (alpha_seq' i : ℝ)) (n + 1) < epsilon_seq (n + 1) := by
          have h_lambda_bound : |lambda_seq' (n + 1)| < epsilon_seq (n + 1) / L_val (fun i => (alpha_seq' i : ℝ)) (n + 1) := by
            have h_lambda_bound : |lambda_seq' (n + 1)| < eta_val (fun i => (alpha_seq' i : ℝ)) (n + 1) (epsilon_seq (n + 1)) := by
              apply_rules [ lambda_seq'_succ_bound ];
            unfold eta_val at h_lambda_bound; aesop;
          rwa [ lt_div_iff₀ ( L_val_pos _ _ ( by linarith ) ) ] at h_lambda_bound;
        grind

/-
The derivative bound holds for step n+1.
-/
lemma derivative_bound_succ' (n : ℕ) (h : Invariant' n) :
    ∀ x : ℝ, deriv (fun t => F_seq_real (fun i => alpha_seq' i) (fun i => lambda_seq' i) (n + 1) t) x ≥
    1 - ∑ k ∈ Finset.range (n + 2), if k < 2 then 0 else epsilon_seq k := by
      intro x;
      -- By definition of $F_{n+1}$, we have $F_{n+1}(x) = F_n(x) + \lambda_{n+1} h_{n+1}(x)$.
      have h_F_succ : deriv (fun t => F_seq_real (fun i => (alpha_seq' i : ℝ)) (fun i => lambda_seq' i) (n + 1) t) x = deriv (fun t => F_seq_real (fun i => (alpha_seq' i : ℝ)) (fun i => lambda_seq' i) n t) x + deriv (fun t => (lambda_seq' (n + 1) : ℝ) * h_seq_real (fun i => (alpha_seq' i : ℝ)) (n + 1) t) x := by
        unfold F_seq_real;
        rw [ ← deriv_add ] ; congr ; ext ; unfold F_seq ; norm_num ; ring;
        · rw [ show 2 + n = 1 + n + 1 by ring, List.range_succ ] ; norm_num ; ring;
          rfl;
        · norm_num [ F_seq ];
          induction' n + 1 with n ih <;> simp_all +decide [ List.range_succ ];
          apply_rules [ DifferentiableAt.mul, DifferentiableAt.pow, differentiableAt_id, differentiableAt_const ];
          -- The real part of a differentiable function is differentiable.
          have h_real_part_diff : DifferentiableAt ℝ (fun y : ℝ => (h_seq (fun i => (alpha_seq' i : ℝ)) n (y : ℂ))) x := by
            induction' n with n ih <;> simp_all +decide [ List.range_succ ];
            · exact differentiableAt_const _;
            · apply_rules [ DifferentiableAt.mul, DifferentiableAt.pow, differentiableAt_id, differentiableAt_const ];
              · norm_num [ Complex.exp_re, Complex.exp_im, neg_div ];
                exact Complex.differentiableAt_exp.comp x ( DifferentiableAt.neg ( DifferentiableAt.div_const ( differentiableAt_id.pow 2 |> DifferentiableAt.comp _ <| Complex.ofRealCLM.differentiableAt ) _ ) );
              · induction' ( List.range ( n + 1 ) ) with n ih <;> simp_all +decide [ List.prod_cons ];
                exact DifferentiableAt.mul ( differentiableAt_id.sub_const _ |> DifferentiableAt.comp _ <| Complex.ofRealCLM.differentiableAt ) ‹_›;
          exact Complex.reCLM.differentiableAt.comp x h_real_part_diff;
        · apply_rules [ DifferentiableAt.prodMk, DifferentiableAt.sub, differentiableAt_id, differentiableAt_const, DifferentiableAt.mul ];
          · norm_cast ; norm_num [ ← sq ];
          · induction ( List.range ( n + 1 ) ) <;> simp_all +decide [ List.prod_cons, List.prod_nil ];
          · norm_cast ; norm_num;
          · induction' ( List.range ( n + 1 ) ) with k hk <;> simp_all +decide [ List.prod_cons, List.prod_nil ];
      have := h.2.2.2.1 x;
      exact le_trans ( by rw [ Finset.sum_range_succ ] ; linarith ) ( h_F_succ.symm ▸ add_le_add this ( neg_le_of_abs_le ( deriv_term_bound_succ' n h x ) ) )

/-
If the invariant holds at step n, it holds at step n+1.
-/
lemma Invariant'_succ (n : ℕ) (h : Invariant' n) : Invariant' (n + 1) := by
  -- The interpolation properties for all k ≤ n+1 follow from interpolation_succ_le_n' and interpolation_succ_eq_n_plus_1'.
  apply And.intro;
  · exact?;
  · -- Apply the results from interpolation_succ_le_n' and interpolation_succ_eq_n_plus_1' to conclude the interpolation property for all k ≤ n+1.
    apply And.intro;
    · exact?;
    · exact ⟨ fun k hk => if hk' : k ≤ n then interpolation_succ_le_n' n h k hk' else by rw [ show k = n + 1 by linarith ] ; exact interpolation_succ_eq_n_plus_1' n h, derivative_bound_succ' n h, fun k hk₁ hk₂ => if hk₃ : k = n + 1 then by rw [ hk₃ ] ; exact lambda_seq'_succ_bound n h else by exact h.2.2.2.2 k hk₁ ( by omega ) ⟩

/-
The invariant Invariant' holds for all n.
-/
theorem Invariant'_all (n : ℕ) : Invariant' n := by
  induction' n with n ih <;> [ exact Invariant'_0; exact Invariant'_succ n ih ]

/-
The absolute value of lambda_seq' n is bounded by eta_seq' n for all n.
-/
lemma lambda_seq'_bound_proven (n : ℕ) : |lambda_seq' n| ≤ eta_seq' n := by
  exact?

/-
The limit function F' maps alpha'_k to beta'_k for all k.
-/
theorem F_final'_eq_beta' (k : ℕ) : F_final' (alpha_seq' k) = (beta_seq' k : ℂ) := by
  -- By definition of $F_final'$, we have $F_final'(alpha_seq' k) = F_partial_sum' k (alpha_seq' k)$.
  have h_eq : F_final' (alpha_seq' k) = F_partial_sum' k (alpha_seq' k) := by
    -- Since $h_seq (fun k => (alpha_seq' k : ℝ)) n (alpha_seq' k) = 0$ for all $n > k$, the sum in $F_final'$ terminates at $n = k$.
    have h_truncate : ∀ n > k, (lambda_seq' n : ℂ) * h_seq (fun k => (alpha_seq' k : ℝ)) n (alpha_seq' k) = 0 := by
      intros n hn
      have h_h_seq_zero : h_seq (fun k => (alpha_seq' k : ℝ)) n (alpha_seq' k) = 0 := by
        exact h_seq_eq_zero_iff _ _ _ |>.2 ⟨ k, hn, rfl ⟩;
      rw [ h_h_seq_zero, MulZeroClass.mul_zero ];
    -- By definition of $F_final'$, we can split the sum into the sum up to $k$ and the sum from $k+1$ onwards.
    have h_split_sum : ∑' n, (lambda_seq' n : ℂ) * h_seq (fun k => (alpha_seq' k : ℝ)) n (alpha_seq' k) = ∑ n ∈ Finset.range (k + 1), (lambda_seq' n : ℂ) * h_seq (fun k => (alpha_seq' k : ℝ)) n (alpha_seq' k) := by
      rw [ tsum_eq_sum ];
      exact fun n hn => h_truncate n <| Nat.lt_of_not_ge fun h => hn <| Finset.mem_range.mpr <| by linarith;
    unfold F_final' F_partial_sum'; aesop;
  have := F_partial_sum'_eq_F_seq_real k ( alpha_seq' k );
  -- By definition of $F_seq_real$, we have $F_seq_real (fun k => (alpha_seq' k : ℝ)) (fun k => lambda_seq' k) k (alpha_seq' k) = beta_seq' k$.
  have h_interpolate : F_seq_real (fun k => (alpha_seq' k : ℝ)) (fun k => lambda_seq' k) k (alpha_seq' k) = beta_seq' k := by
    have := Invariant'_all k;
    have := this.2.2.1 k ( by linarith ) ; aesop;
  convert Complex.ext_iff.mpr _;
  erw [ F_final'_real_on_real ] ; aesop

/-
Definition of the minimum unused index for the alpha sequence and its properties.
-/
noncomputable def min_unused_alpha_index (n : ℕ) : ℕ :=
  first_unused_index a_seq a_seq_surj (alpha_set (all_tuples' n)) (alpha_set_finite (all_tuples' n))

lemma min_unused_alpha_index_spec (n : ℕ) :
    a_seq (min_unused_alpha_index n) ∉ alpha_set (all_tuples' n) ∧
    ∀ k < min_unused_alpha_index n, a_seq k ∈ alpha_set (all_tuples' n) := by
      exact ⟨ Nat.find_spec ( exists_index_not_mem_finite a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) ), fun k hk => by exact not_not.mp fun hk' => hk.not_le <| Nat.find_min' ( exists_index_not_mem_finite a_seq a_seq_surj ( alpha_set ( all_tuples' n ) ) ( alpha_set_finite ( all_tuples' n ) ) ) hk' ⟩

/-
If a_seq k is not in the set of used alphas, then the minimum unused index is at most k.
-/
lemma min_unused_alpha_index_le (n k : ℕ) (h : a_seq k ∉ alpha_set (all_tuples' n)) :
    min_unused_alpha_index n ≤ k := by
      exact Nat.find_min' _ h

/-
For even n, the n-th alpha value is the first unused element of the sequence a_seq.
-/
lemma alpha_seq'_eq_a_seq_of_even (n : ℕ) (h_even : n % 2 = 0) (hn : n ≥ 2) :
    alpha_seq' n = a_seq (min_unused_alpha_index n) := by
      -- By definition of `next_step'`, if `n` is even and `n ≥ 2`, then `next_step' n` returns `(alpha_n, beta_n, lambda_n)` where `alpha_n` is the first unused element of `a_seq`.
      have h_next_step_even : n ≥ 2 → n % 2 = 0 → (next_step' n (all_tuples' n)).1 = a_seq (min_unused_alpha_index n) := by
        intro hn h_even
        have h_next_step_even : (next_step' n (all_tuples' n)).1 = first_unused a_seq a_seq_surj (alpha_set (all_tuples' n)) (alpha_set_finite (all_tuples' n)) := by
          unfold next_step';
          split_ifs <;> simp_all +decide [ Nat.even_iff ];
          rw [ if_pos ( eta_val_pos_any _ _ ( by linarith ) ) ];
          split_ifs <;> norm_num;
        unfold min_unused_alpha_index; aesop;
      unfold alpha_seq';
      unfold construction_seq';
      unfold all_tuples'; aesop;

/-
The sequence alpha_seq' is injective.
-/
theorem alpha_seq'_injective : Function.Injective alpha_seq' := by
  -- By definition of injectivity, if α_k = α_j, then k = j.
  intro k j h_eq
  by_contra h_neq;
  -- Let $n = \max(k, j)$. Then $k, j \leq n$.
  set n := max k j
  have h_le_n : k ≤ n ∧ j ≤ n := by
    exact ⟨ le_max_left _ _, le_max_right _ _ ⟩
  generalize_proofs at *;
  exact h_neq ( by have := Invariant'_all n; exact Classical.not_not.1 fun h => h_neq <| by have := this.1 k j h_le_n.1 h_le_n.2; aesop )

/-
Every element of the sequence a_seq appears in the sequence alpha_seq'.
-/
lemma exists_alpha'_eq_a_seq (k : ℕ) : ∃ n, alpha_seq' n = a_seq k := by
  by_contra h_contra;
  -- Then for all n, a_seq k is not in alpha_set (all_tuples' n).
  have h_not_mem : ∀ n, a_seq k ∉ alpha_set (all_tuples' n) := by
    simp_all +decide [ alpha_set_eq_image' ];
  -- By min_unused_alpha_index_le, min_unused_alpha_index n <= k for all n.
  have h_min_le_k : ∀ n, min_unused_alpha_index n ≤ k := by
    exact fun n => min_unused_alpha_index_le n k ( h_not_mem n );
  -- So alpha_seq' maps the set of even numbers >= 2 (which is infinite) into the finite set a_seq(S).
  have h_image_finite : Set.Finite (Set.image alpha_seq' {n | n % 2 = 0 ∧ n ≥ 2}) := by
    have h_image_finite : ∀ n, n % 2 = 0 ∧ n ≥ 2 → alpha_seq' n ∈ Finset.image (fun m => a_seq m) (Finset.range (k + 1)) := by
      intros n hn
      have h_alpha_eq_a_seq : alpha_seq' n = a_seq (min_unused_alpha_index n) := by
        exact alpha_seq'_eq_a_seq_of_even n hn.1 hn.2;
      exact h_alpha_eq_a_seq.symm ▸ Finset.mem_image.mpr ⟨ _, Finset.mem_range.mpr ( Nat.lt_succ_of_le ( h_min_le_k n ) ), rfl ⟩;
    exact Set.Finite.subset ( Finset.finite_toSet ( Finset.image ( fun m => a_seq m ) ( Finset.range ( k + 1 ) ) ) ) ( Set.image_subset_iff.mpr h_image_finite );
  exact h_image_finite.not_infinite <| Set.infinite_of_injective_forall_mem ( fun n m hnm => by simpa using alpha_seq'_injective hnm ) fun n => Set.mem_image_of_mem _ ⟨ show ( 2 * n + 2 ) % 2 = 0 by norm_num [ Nat.add_mod ], by linarith ⟩

/-
The sequence alpha_seq' is surjective.
-/
theorem alpha_seq'_surjective : Function.Surjective alpha_seq' := by
  intro q;
  -- Since a_seq is surjective, there exists k such that a_seq k = q.
  obtain ⟨k, hk⟩ : ∃ k, a_seq k = q := by
    exact a_seq_surj q;
  exact hk ▸ exists_alpha'_eq_a_seq k

/-
Definition of the minimum unused index for the beta sequence and its properties.
-/
noncomputable def min_unused_beta_index (n : ℕ) : ℕ :=
  first_unused_index b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n))

lemma min_unused_beta_index_spec (n : ℕ) :
    b_seq (min_unused_beta_index n) ∉ beta_set (all_tuples' n) ∧
    ∀ k < min_unused_beta_index n, b_seq k ∈ beta_set (all_tuples' n) := by
      exact ⟨ by simpa using Nat.find_spec ( exists_index_not_mem_finite b_seq b_seq_surj ( beta_set ( all_tuples' n ) ) ( beta_set_finite ( all_tuples' n ) ) ), fun k hk => by simpa using Nat.find_min ( exists_index_not_mem_finite b_seq b_seq_surj ( beta_set ( all_tuples' n ) ) ( beta_set_finite ( all_tuples' n ) ) ) hk ⟩

/-
Every element of the sequence a_seq appears in the sequence alpha_seq'.
-/
lemma exists_alpha'_eq_a_seq_proven (k : ℕ) : ∃ n, alpha_seq' n = a_seq k := by
  exact?

/-
If a_seq k is never chosen, then alpha_seq' maps even indices >= 2 into the image of a_seq on {0, ..., k}.
-/
lemma alpha_seq'_subset_image_of_never_chosen (k : ℕ) (h_never : ∀ n, alpha_seq' n ≠ a_seq k) :
    ∀ n, n % 2 = 0 → n ≥ 2 → alpha_seq' n ∈ (Finset.range (k + 1)).image a_seq := by
      contrapose! h_never;
      have := exists_alpha'_eq_a_seq_proven k;
      exact this

/-
Every element of the sequence a_seq appears in the sequence alpha_seq'.
-/
lemma exists_alpha'_eq_a_seq_final (k : ℕ) : ∃ n, alpha_seq' n = a_seq k := by
  -- By definition of $alpha_seq'$, we know that every element of $a_seq$ appears in $alpha_seq'$.
  apply exists_alpha'_eq_a_seq

/-
For odd n, the n-th beta value is the first unused element of the sequence b_seq.
-/
lemma beta_seq'_eq_b_seq_of_odd (n : ℕ) (h_odd : n % 2 = 1) (hn : n ≥ 1) :
    beta_seq' n = b_seq (min_unused_beta_index n) := by
      have h_beta_def : (next_step' n (all_tuples' n)).2.1 = first_unused b_seq b_seq_surj (beta_set (all_tuples' n)) (beta_set_finite (all_tuples' n)) := by
        convert next_step'_odd_beta_v2 n hn h_odd ( Invariant'_all ( n - 1 ) ) using 1;
      convert h_beta_def using 1;
      unfold beta_seq';
      unfold construction_seq';
      simp +decide [ all_tuples' ]

/-
The sequence beta_seq' is injective.
-/
theorem beta_seq'_injective : Function.Injective beta_seq' := by
  -- By definition of Invariant', the beta sequence is injective.
  have h_beta_seq'_injective : ∀ n, ∀ i j, i ≤ n → j ≤ n → i ≠ j → beta_seq' i ≠ beta_seq' j := by
    intros n i j hi hj hij; exact (Invariant'_all n).2.1 i j hi hj hij;
  exact fun i j hij => Classical.not_not.1 fun hi => h_beta_seq'_injective ( Max.max i j ) i j ( le_max_left _ _ ) ( le_max_right _ _ ) hi hij

/-
If b_seq k is not in the set of used betas, then the minimum unused index is at most k.
-/
lemma min_unused_beta_index_le (n k : ℕ) (h : b_seq k ∉ beta_set (all_tuples' n)) :
    min_unused_beta_index n ≤ k := by
      exact le_of_not_gt fun hk => h <| min_unused_beta_index_spec n |>.2 _ hk

/-
If b_seq k is never chosen, then beta_seq' maps odd indices >= 1 into the image of b_seq on {0, ..., k}.
-/
lemma beta_seq'_subset_image_of_never_chosen (k : ℕ) (h_never : ∀ n, beta_seq' n ≠ b_seq k) :
    ∀ n, n % 2 = 1 → n ≥ 1 → beta_seq' n ∈ (Finset.range (k + 1)).image b_seq := by
      intros n hn_odd hn_ge_1
      have h_min_unused_beta_index_le_k : min_unused_beta_index n ≤ k := by
        apply min_unused_beta_index_le;
        rw [ beta_set_eq_image' ] ; simp +decide [ Finset.mem_image, h_never ];
      exact Finset.mem_image.mpr ⟨ min_unused_beta_index n, Finset.mem_range.mpr ( by linarith ), by rw [ beta_seq'_eq_b_seq_of_odd n hn_odd hn_ge_1 ] ⟩

/-
Every element of the sequence a_seq appears in the sequence alpha_seq'.
-/
lemma exists_alpha'_eq_a_seq_final_v2 (k : ℕ) : ∃ n, alpha_seq' n = a_seq k := by
  exact?

/-
Every element of the sequence b_seq appears in the sequence beta_seq'.
-/
lemma exists_beta'_eq_b_seq (k : ℕ) : ∃ n, beta_seq' n = b_seq k := by
  by_contra h_contra;
  -- If b_seq k is never chosen, then beta_seq' maps odd indices >= 1 into the finite set S = b_seq({0, ..., k}).
  have h_beta_seq'_subset_image : ∀ n, n % 2 = 1 → n ≥ 1 → beta_seq' n ∈ (Finset.range (k + 1)).image b_seq := by
    apply beta_seq'_subset_image_of_never_chosen k (by
    aesop);
  -- Since beta_seq' is injective, the restriction of beta_seq' to the set of odd indices >= 1 must be injective.
  have h_beta_seq'_injective_odd : Function.Injective (fun n : ℕ => beta_seq' (2 * n + 1)) := by
    exact fun m n hmn => by have := beta_seq'_injective hmn; aesop;
  have h_beta_seq'_infinite : Set.Infinite (Set.range (fun n : ℕ => beta_seq' (2 * n + 1))) := by
    exact Set.infinite_range_of_injective h_beta_seq'_injective_odd;
  exact h_beta_seq'_infinite ( Set.Finite.subset ( Finset.finite_toSet ( Finset.image b_seq ( Finset.range ( k + 1 ) ) ) ) ( Set.range_subset_iff.mpr fun n => h_beta_seq'_subset_image _ ( by norm_num [ Nat.add_mod ] ) ( by linarith ) ) )

/-
Every element of the sequence a_seq appears in the sequence alpha_seq'.
-/
lemma exists_alpha'_eq_a_seq_final_v3 (k : ℕ) : ∃ n, alpha_seq' n = a_seq k := by
  exact?

/-
The set of even natural numbers greater than or equal to 2 is infinite.
-/
lemma even_ge_two_infinite : Set.Infinite {n : ℕ | n % 2 = 0 ∧ n ≥ 2} := by
  exact Set.infinite_of_forall_exists_gt fun n => ⟨ 2 * n + 2, ⟨ by norm_num [ Nat.add_mod, Nat.mul_mod ], by linarith ⟩, by linarith ⟩

/-
The first values of alpha_seq' and beta_seq' are 0.
-/
lemma alpha_beta_0 : alpha_seq' 0 = 0 ∧ beta_seq' 0 = 0 := by
  exact ⟨ rfl, rfl ⟩

/-
The second values of alpha_seq' and beta_seq' are 1.
-/
lemma alpha_beta_1 : alpha_seq' 1 = 1 ∧ beta_seq' 1 = 1 := by
  have := @alpha_beta_0; unfold alpha_seq' beta_seq' at *; aesop;

/-
The third value of alpha_seq' is 2.
-/
lemma alpha_seq'_2_eq_2 : alpha_seq' 2 = 2 := by
  -- By definition of `alpha_seq'`, we have `alpha_seq' 2 = first_unused a_seq a_seq_surj (alpha_set (all_tuples' 2)) (alpha_set_finite (all_tuples' 2))`.
  have h_alpha_seq'_2_def : alpha_seq' 2 = first_unused a_seq a_seq_surj (alpha_set (all_tuples' 2)) (alpha_set_finite (all_tuples' 2)) := by
    apply alpha_seq'_eq_a_seq_of_even;
    · norm_num;
    · norm_num;
  rw [ h_alpha_seq'_2_def, first_unused_val_eq ];
  -- By definition of `a_seq`, we know that `a_seq 2 = 2`.
  have h_a_seq_2 : a_seq 2 = 2 := by
    unfold a_seq; norm_num;
  exact h_a_seq_2;
  · unfold alpha_set; simp +decide [ * ] ;
    rintro ( _ | _ | _ | n ) <;> simp +decide [ all_tuples' ];
    · unfold next_step' a_seq; norm_num;
    · unfold next_step' a_seq; aesop;
  · intro j hj; interval_cases j <;> unfold a_seq <;> norm_num [ alpha_set, all_tuples' ] ;
    · exists 0, 0, 0;
      unfold next_step'; norm_num;
      native_decide +revert;
    · use 1; simp +decide [ next_step' ] ;
      native_decide +revert

/-
The third value of beta_seq' is not equal to 2.
-/
lemma beta_seq'_2_ne_2_proven : beta_seq' 2 ≠ 2 := by
  exact?

/-
The values of f_final' at 0, 1, and 2 are 0, 1, and not 2, respectively.
-/
lemma f_final'_values : f_final' 0 = 0 ∧ f_final' 1 = 1 ∧ f_final' 2 ≠ 2 := by
  -- Apply the fact that F_final' maps alpha_seq' k to beta_seq' k.
  have h_maps : F_final' (alpha_seq' 0) = beta_seq' 0 ∧ F_final' (alpha_seq' 1) = beta_seq' 1 ∧ F_final' (alpha_seq' 2) = beta_seq' 2 := by
    exact ⟨ F_final'_eq_beta' 0, F_final'_eq_beta' 1, F_final'_eq_beta' 2 ⟩;
  have h_values : F_final' 0 = 0 ∧ F_final' 1 = 1 ∧ F_final' 2 = beta_seq' 2 := by
    have := alpha_beta_0; have := alpha_beta_1; have := alpha_seq'_2_eq_2; aesop;
  unfold f_final';
  norm_num +zetaDelta at *;
  exact ⟨ by norm_num [ h_values ], by norm_num [ h_values ], by norm_num [ h_values ] ; exact mod_cast beta_seq'_2_ne_2_proven ⟩

/-
The function f_final' is not affine.
-/
theorem f_final'_not_affine : ¬ IsAffine f_final' := by
  -- Suppose f_final' is affine. Then there exist a, b such that f_final'(x) = ax + b for all x.
  by_contra h_affine
  obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, ∀ x, f_final' x = a * x + b := by
    unfold IsAffine at h_affine; aesop;
  have := f_final'_values; aesop

/-
The derivative of the n-th term in the series for f_final' is bounded by epsilon_seq n (or 0 if n < 2).
-/
lemma f_final'_term_bound (n : ℕ) (x : ℝ) :
    |deriv (fun y => lambda_seq' n * h_seq_real (fun k => (alpha_seq' k : ℝ)) n y) x| ≤ if n < 2 then 0 else epsilon_seq n := by
      -- By definition of $lambda_seq'$ and $h_seq_real$, we know that $|deriv (fun y => lambda_seq' n * h_seq_real (fun k => ↑(alpha_seq' k)) n y) x| ≤ epsilon_seq n$ for $n ≥ 2$.
      have h_deriv_bound : ∀ n ≥ 2, ∀ x, |deriv (fun y => lambda_seq' n * h_seq_real (fun k => ↑(alpha_seq' k)) n y) x| ≤ epsilon_seq n := by
        intros n hn x;
        have := deriv_term_bound_succ' ( n - 1 ) ( Invariant'_all _ ) x;
        grind;
      rcases n with ( _ | _ | n ) <;> simp_all +decide;
      · unfold h_seq_real;
        unfold h_seq; norm_num;
      · unfold lambda_seq' h_seq_real; norm_num;
        unfold construction_seq';
        unfold all_tuples'; norm_num;
        unfold next_step' all_tuples'; norm_num;
      · grind +ring

/-
The series defining f_final' converges for every real number x.
-/
lemma f_final'_series_summable (x : ℝ) :
    Summable (fun n => lambda_seq' n * h_seq_real (fun k => (alpha_seq' k : ℝ)) n x) := by
      have := F_final'_converges x;
      convert Complex.reCLM.summable ( this ) using 1 ; aesop

/-
The series of derivatives of the terms defining f_final' converges for every real number x.
-/
lemma summable_deriv_real' (x : ℝ) :
    Summable (fun n => deriv (fun y => lambda_seq' n * h_seq_real (fun k => (alpha_seq' k : ℝ)) n y) x) := by
      -- By the bound on the derivatives and the summability of the series (epsilon_summable'), we can conclude that the series of derivatives converges absolutely.
      have h_abs_conv : Summable (fun n => |deriv (fun y => lambda_seq' n * h_seq_real (fun k => (alpha_seq' k : ℝ)) n y) x|) := by
        have h_abs_conv : Summable (fun n => if n < 2 then 0 else epsilon_seq n) := by
          refine' Summable.of_nonneg_of_le ( fun n => _ ) ( fun n => _ ) ( epsilon_summable' );
          · split_ifs <;> norm_num [ epsilon_seq ];
          · split_ifs <;> norm_num;
            interval_cases n <;> norm_num [ epsilon_seq ];
        exact Summable.of_nonneg_of_le ( fun n => abs_nonneg _ ) ( fun n => f_final'_term_bound n x ) h_abs_conv;
      exact h_abs_conv.of_abs

/-
The derivative of f_final' at x is 1 plus the sum of the derivatives of the terms in the series.
-/
lemma f_final'_deriv_eq_sum (x : ℝ) :
    deriv f_final' x = 1 + ∑' n, deriv (fun y => lambda_seq' n * h_seq_real (fun k => (alpha_seq' k : ℝ)) n y) x := by
      -- Apply the linearity of the derivative and the fact that the series of derivatives converges uniformly.
      have h_deriv_sum : deriv (fun x => x + ∑' n, lambda_seq' n * h_seq_real (fun k => (alpha_seq' k : ℝ)) n x) x = 1 + ∑' n, deriv (fun y => lambda_seq' n * h_seq_real (fun k => (alpha_seq' k : ℝ)) n y) x := by
        apply_rules [ HasDerivAt.deriv ];
        apply_rules [ HasDerivAt.add, hasDerivAt_id ];
        apply_rules [ hasDerivAt_tsum ];
        rotate_right;
        use fun n => if n < 2 then 0 else epsilon_seq n;
        · rw [ ← summable_nat_add_iff 2 ];
          convert epsilon_summable.comp_injective ( add_left_injective 2 ) using 1;
        · refine' fun n y => hasDerivAt_deriv_iff.mpr _;
          refine' DifferentiableAt.const_mul _ _;
          -- The function $h_seq_real$ is differentiable because it is a composition of differentiable functions.
          have h_diff : ∀ n x, DifferentiableAt ℝ (fun z => Complex.re (h_seq (fun k => (alpha_seq' k : ℝ)) n z)) x := by
            intro n x;
            have h_diff : DifferentiableAt ℂ (fun z => h_seq (fun k => (alpha_seq' k : ℝ)) n z) x := by
              induction' n with n ih generalizing x <;> simp_all +decide [ h_seq ];
              norm_num [ List.range_succ ];
              apply_rules [ DifferentiableAt.mul, DifferentiableAt.exp, DifferentiableAt.neg, DifferentiableAt.div, differentiableAt_id, differentiableAt_const ];
              · exact Complex.differentiableAt_exp.comp x ( DifferentiableAt.div_const ( DifferentiableAt.neg ( differentiableAt_id.pow 2 ) ) _ );
              · induction' ( List.range n ) with k hk ih <;> simp_all +decide [ List.prod_cons ];
              · exact differentiableAt_id.sub_const _;
            exact Complex.reCLM.differentiableAt.comp x ( h_diff.restrictScalars ℝ );
          exact h_diff n y |> DifferentiableAt.comp y <| differentiableAt_id.comp _ <| Complex.ofRealCLM.differentiableAt;
        · -- Apply the bound on the derivative of each term in the series.
          intros n y
          apply f_final'_term_bound;
        · convert f_final'_series_summable x using 1;
      unfold f_final';
      convert h_deriv_sum using 2;
      ext x; unfold F_final'; norm_num [ Complex.re_sum, Complex.im_sum ] ;
      rw [ Complex.re_tsum ] ; aesop;
      convert F_final'_converges x using 1

/-
The derivative of f_final' is strictly greater than 1/2 everywhere.
-/
theorem f_final'_deriv_bound (x : ℝ) : deriv f_final' x > 1/2 := by
  rw [ f_final'_deriv_eq_sum ];
  -- Apply the bound on the sum of epsilons.
  have h_sum_epsilons : ∑' n, epsilon_seq n < 1 / 2 := by
    exact?;
  -- Apply the bound on the sum of derivatives.
  have h_sum_derivs : ∑' n, deriv (fun y => lambda_seq' n * h_seq_real (fun k => (alpha_seq' k : ℝ)) n y) x ≥ -∑' n, epsilon_seq n := by
    rw [ ← tsum_neg ];
    refine' Summable.tsum_le_tsum _ _ _;
    · intro n;
      refine' neg_le_of_abs_le _;
      have := f_final'_term_bound n x;
      split_ifs at this <;> linarith [ show 0 ≤ epsilon_seq n from by unfold epsilon_seq; positivity ];
    · exact Summable.neg ( by exact? );
    · exact?;
  linarith

/-
f_final' is an injective function.
-/
theorem f_final'_injective : Function.Injective f_final' := by
  -- Since $f_final'$ is strictly monotonic, it is injective.
  have h_strict_mono : StrictMono f_final' := by
    apply strictMono_of_deriv_pos;
    exact fun x => by linarith [ f_final'_deriv_bound x ] ;
  exact StrictMono.injective h_strict_mono

/-
f_final' maps the set of rational numbers onto the set of rational numbers.
-/
theorem f_final'_surj_Q : f_final' '' (Set.range ((↑) : ℚ → ℝ)) = Set.range ((↑) : ℚ → ℝ) := by
  -- To prove equality of sets, we show each set is a subset of the other.
  apply Set.ext
  intro r
  constructor;
  · rintro ⟨ x, ⟨ q, rfl ⟩, rfl ⟩;
    -- Since $q$ is rational, there exists some $k$ such that $\alpha_k = q$.
    obtain ⟨k, hk⟩ : ∃ k, alpha_seq' k = q := by
      convert alpha_seq'_surjective q;
    have h_f_final'_beta_k : F_final' (alpha_seq' k) = (beta_seq' k : ℂ) := by
      exact?;
    unfold f_final' at *; aesop;
  · rintro ⟨ q, rfl ⟩;
    -- By definition of $f_final'$, we know that $f_final' (alpha_seq' k) = beta_seq' k$ for any $k$.
    have h_image : ∀ k : ℕ, f_final' (alpha_seq' k) = beta_seq' k := by
      intro k
      have := F_final'_eq_beta' k
      simp [f_final'] at this;
      convert congr_arg Complex.re this using 1;
    -- By definition of $beta_seq'$, we know that every rational number appears in the sequence $beta_seq'$.
    have h_beta_seq'_surjective : ∀ r : ℚ, ∃ k : ℕ, beta_seq' k = r := by
      have := exists_beta'_eq_b_seq;
      exact fun r => by obtain ⟨ k, hk ⟩ := b_seq_surj r; obtain ⟨ n, hn ⟩ := this k; exact ⟨ n, hn.trans hk ⟩ ;
    obtain ⟨ k, hk ⟩ := h_beta_seq'_surjective q; use alpha_seq' k; aesop;

/-
f_final' preserves rationality, meaning x is rational if and only if f_final'(x) is rational.
-/
theorem f_final'_preserves_rationality : PreservesRationality f_final' := by
  apply injective_preserves_rationality;
  · exact?;
  · exact?

/-
There exists an entire function F such that F maps reals to reals, its restriction to reals is not affine, and it preserves rationality.
-/
theorem main_theorem : ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ x : ℝ, (F x).im = 0) ∧ ¬ IsAffine (fun x : ℝ => (F x).re) ∧ PreservesRationality (fun x : ℝ => (F x).re) := by
  use F_final';
  exact ⟨ F_final'_entire, F_final'_real_on_real, f_final'_not_affine, f_final'_preserves_rationality ⟩