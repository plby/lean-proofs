/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
Formalization of "One-sided limsup sets for middle-a Cantor sets".

We define the middle-a Cantor set `C r` (where `r = (1-a)/2`) and the one-sided limsup sets `C_plus` and `C_minus`.
We prove the symbolic characterization of these sets (Theorems 2.5 and 2.7) and calculate their Hausdorff and box dimensions (Corollary 2.8).

Main results:
- `theorem_plus`: $C_\alpha^+ = C_\alpha \setminus E_\rho^+$
- `theorem_minus`: $C_\alpha^- = C_\alpha \setminus E_\rho^-$
- `theorem_dimension_Ca`: $\dim_H(C_a) = \dim_B(C_a) = \frac{\log 2}{-\log r}$
- `corollary_dimensions_limsup`: $\dim_H(C_\alpha^\pm) = \dim_B(C_\alpha^\pm) = \frac{\log 2}{-\log \rho}$
-/

import Mathlib

namespace MO509164

set_option linter.style.setOption false

open scoped Nat

set_option maxHeartbeats 50000000
set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.multiGoal false

/-
The contraction maps f_0 and f_1 for the middle-a Cantor set construction.
-/
def f (i : Fin 2) (r : ℝ) (x : ℝ) : ℝ :=
  if i = 0 then r * x else 1 - r + r * x

/-
The composition of contraction maps for a finite word.
-/
def f_word (u : List (Fin 2)) (r : ℝ) : ℝ → ℝ :=
  match u with
  | [] => id
  | i :: rest => f i r ∘ f_word rest r

/-
The interval corresponding to a word u.
-/
def I_word (u : List (Fin 2)) (r : ℝ) : Set ℝ :=
  (f_word u r) '' (Set.Icc 0 1)

/-
The set of all words of length n.
-/
def Sigma_n (n : ℕ) : Set (List (Fin 2)) :=
  {u | u.length = n}

/-
The nth stage of the middle-a construction.
-/
def C_n (r : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ u ∈ Sigma_n n, I_word u r

/-
The middle-a Cantor set.
-/
def C (r : ℝ) : Set ℝ :=
  ⋂ n, C_n r n

/-
The projection map from the symbolic space to the Cantor set.
-/
noncomputable def pi (r : ℝ) (ω : ℕ → Fin 2) : ℝ :=
  (1 - r) * ∑' n : ℕ, (ω n : ℝ) * r ^ n

/-
The one-sided limsup sets C_alpha^+ and C_alpha^-, parametrized by rho.
-/
def C_plus (rho : ℝ) : Set ℝ :=
  ⋂ (ε : ℝ) (_ : ε > 0), ⋃ (r : ℝ) (_ : r ∈ Set.Ioo (rho - ε) rho), C r

def C_minus (rho : ℝ) : Set ℝ :=
  ⋂ (ε : ℝ) (_ : ε > 0), ⋃ (r : ℝ) (_ : r ∈ Set.Ioo rho (rho + ε)), C r

/-
The infinite sequence obtained by appending infinitely many zeros to a finite word.
-/
def append_zeros (u : List (Fin 2)) : ℕ → Fin 2 :=
  fun n => match u[n]? with
    | some x => x
    | none => 0

/-
The infinite sequence obtained by appending infinitely many ones to a finite word.
-/
def append_ones (u : List (Fin 2)) : ℕ → Fin 2 :=
  fun n => match u[n]? with
    | some x => x
    | none => 1

/-
Proposition 2.1(1): Explicit formula for f_{u,r}(x).
-/
theorem prop_symbolic_1 (r : ℝ) (u : List (Fin 2)) (x : ℝ) :
    f_word u r x = (1 - r) * (∑ k ∈ Finset.range u.length, ((u[k]?).getD 0 : ℝ) * r ^ k) + r ^ u.length * x := by
      induction u generalizing x with
      | nil =>
        simp [ f_word ]
      | cons hd tl ih =>
      simp_all +decide [ pow_succ', Finset.mul_sum, Finset.sum_range_succ', f_word ] ; ring_nf at *;
      unfold f; fin_cases hd <;> norm_num [ Finset.mul_sum _ _ _, mul_assoc ] <;> ring_nf;
      · simpa [ mul_add, mul_sub, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib ] using by ring_nf;
      · simpa [ Finset.mul_sum _ _ _, mul_add, mul_assoc, mul_left_comm, Finset.sum_add_distrib ] using by ring_nf;

/-
Proposition 2.1(1): Explicit formula for I_u(r), assuming 0 < r < 1 / 2.
-/
theorem prop_symbolic_1_interval (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (u : List (Fin 2)) :
    I_word u r = Set.Icc ((1 - r) * ∑ k ∈ Finset.range u.length, ((u[k]?).getD 0 : ℝ) * r ^ k)
                         ((1 - r) * (∑ k ∈ Finset.range u.length, ((u[k]?).getD 0 : ℝ) * r ^ k) + r ^ u.length) := by
                           ext x;
                           constructor;
                           · rintro ⟨ y, hy, rfl ⟩;
                             rw [ prop_symbolic_1 ] ; constructor <;> nlinarith [ pow_nonneg hr.1.le u.length, hy.1, hy.2 ] ;
                           · intro hx
                             obtain ⟨y, hy⟩ : ∃ y ∈ Set.Icc 0 1, (1 - r) * (∑ k ∈ Finset.range u.length, ((u[k]?).getD 0 : ℝ) * r ^ k) + r ^ u.length * y = x := by
                               exact ⟨ ( x - ( 1 - r ) * ∑ k ∈ Finset.range u.length, ( u[k]? |> Option.getD <| 0 ) * r ^ k ) / r ^ u.length, ⟨ by rw [ le_div_iff₀ ( pow_pos hr.1 _ ) ] ; linarith [ hx.1 ], by rw [ div_le_iff₀ ( pow_pos hr.1 _ ) ] ; linarith [ hx.2 ] ⟩, by rw [ mul_div_cancel₀ _ ( ne_of_gt ( pow_pos hr.1 _ ) ) ] ; ring ⟩;
                             use y;
                             rw [ prop_symbolic_1 ] ; aesop

/-
Formula for pi_r(u0^infty).
-/
theorem pi_append_zeros (r : ℝ) (u : List (Fin 2)) :
    pi r (append_zeros u) = (1 - r) * ∑ k ∈ Finset.range u.length, ((u[k]?).getD 0 : ℝ) * r ^ k := by
      unfold pi;
      rw [ tsum_eq_sum ];
      congr! 2;
      · unfold append_zeros; aesop;
      · unfold append_zeros; aesop;

/-
Formula for pi_r(u1^infty).
-/
theorem pi_append_ones (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (u : List (Fin 2)) :
    pi r (append_ones u) = (1 - r) * (∑ k ∈ Finset.range u.length, ((u[k]?).getD 0 : ℝ) * r ^ k) + r ^ u.length := by
      -- Split the sum in the definition of pi into the first n terms and the rest. The rest form a geometric series.
      have h_split_sum : ∑' k : ℕ, ((append_ones u k : ℝ) * r ^ k) = (∑ k ∈ Finset.range u.length, ((u[k]?).getD 0 : ℝ) * r ^ k) + (∑' k : ℕ, r ^ (k + u.length)) := by
        rw [ ← Summable.sum_add_tsum_nat_add ];
        congr! 2;
        · unfold append_ones; aesop;
        · unfold append_ones; aesop;
        · exact Summable.of_nonneg_of_le ( fun _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hr.1.le _ ) ) ( fun _ => mul_le_of_le_one_left ( pow_nonneg hr.1.le _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hr.1.le ( by linarith ) );
      convert congr_arg ( fun x : ℝ => ( 1 - r ) * x ) h_split_sum using 1;
      norm_num [ pow_add, tsum_mul_left, tsum_geometric_of_lt_one hr.1.le ( by linarith : r < 1 ) ] ; ring_nf;
      rw [ tsum_mul_left, tsum_geometric_of_lt_one hr.1.le ( by linarith ) ] ; ring_nf;
      grind

/-
Proposition 2.1(3) part 2: I_u(r) = [L_u(r), R_u(r)].
-/
theorem prop_symbolic_3_interval (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (u : List (Fin 2)) :
    I_word u r = Set.Icc (pi r (append_zeros u)) (pi r (append_ones u)) := by
      -- Apply the definition of I_word u r from.prop_symbolic_1_interval.
      rw [prop_symbolic_1_interval r hr u];
      rw [ pi_append_zeros r u, pi_append_ones r hr u ]

/-
pi_r(omega) is in the interval corresponding to the prefix of omega of length n.
-/
def take_word (n : ℕ) (ω : ℕ → Fin 2) : List (Fin 2) :=
  List.ofFn (fun i : Fin n => ω i)

theorem pi_mem_I_word (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (ω : ℕ → Fin 2) (n : ℕ) :
    pi r ω ∈ I_word (take_word n ω) r := by
      -- By definition of $f_{word}$, we know that $f_{take\_word n ω}(x) = (1 - r) * ∑ k ∈ Finset.range n, (ω k : ℝ) * r ^ k + r ^ n * x$.
      have h_f_word : ∀ x : ℝ, (f_word (take_word n ω) r) x = (1 - r) * (∑ k ∈ Finset.range n, (ω k : ℝ) * r ^ k) + r ^ n * x := by
        convert prop_symbolic_1 r ( take_word n ω ) using 1;
        simp +decide [ take_word ];
        exact iff_of_eq ( by rw [ Finset.sum_congr rfl ] ; intros i hi; aesop );
      -- By definition of $pi$, we know that $pi r ω = (1 - r) * ∑ k ∈ Finset.range n, (ω k : ℝ) * r ^ k + r ^ n * pi r (ω ∘ (Nat.add n))$.
      have h_pi_def : pi r ω = (1 - r) * ∑ k ∈ Finset.range n, (ω k : ℝ) * r ^ k + r ^ n * pi r (fun k => ω (k + n)) := by
        unfold pi;
        rw [ ← Summable.sum_add_tsum_nat_add ];
        rw [ mul_add ];
        congr! 1;
        · norm_num [ pow_add, mul_assoc, mul_comm, mul_left_comm, ← tsum_mul_left ];
        · exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hr.1.le _ ) ) ( fun n => mul_le_of_le_one_left ( pow_nonneg hr.1.le _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hr.1.le ( by linarith ) );
      -- By definition of $pi$, we know that $pi r (ω ∘ (Nat.add n))$ is in the interval $[0, 1]$.
      have h_pi_range : 0 ≤ pi r (fun k => ω (k + n)) ∧ pi r (fun k => ω (k + n)) ≤ 1 := by
        refine ⟨ mul_nonneg ( by linarith ) ( tsum_nonneg fun _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hr.1.le _ ) ), ?_ ⟩;
        refine le_trans ( mul_le_mul_of_nonneg_left ( Summable.tsum_le_tsum ( g := fun i : ℕ => r ^ i ) ?_ ?_ ?_ ) ( by linarith ) ) ?_;
        · exact fun i => mul_le_of_le_one_left ( pow_nonneg hr.1.le _ ) ( mod_cast Fin.is_le _ );
        · exact Summable.of_nonneg_of_le ( fun _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hr.1.le _ ) ) ( fun _ => mul_le_of_le_one_left ( pow_nonneg hr.1.le _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hr.1.le ( by linarith ) );
        · exact summable_geometric_of_lt_one hr.1.le ( by linarith );
        · rw [ tsum_geometric_of_lt_one ] <;> nlinarith [ mul_inv_cancel₀ ( by linarith : ( 1 - r ) ≠ 0 ) ];
      exact ⟨ pi r ( fun k => ω ( k + n ) ), ⟨ by linarith, by linarith ⟩, by aesop ⟩

/-
The image of the projection map is contained in the Cantor set.
-/
theorem range_pi_subset_C (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    Set.range (pi r) ⊆ C r := by
      intro x;
      rintro ⟨ ω, rfl ⟩;
      refine Set.mem_iInter.mpr fun n => Set.mem_iUnion₂.mpr ⟨ take_word n ω, ?_, ?_ ⟩;
      · exact show List.length ( List.ofFn ( fun i : Fin n => ω i ) ) = n from by simp +decide ;
      · exact pi_mem_I_word r hr ω n

/-
pi_r(omega) is in C_n(r).
-/
theorem pi_mem_C_n (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (ω : ℕ → Fin 2) (n : ℕ) :
    pi r ω ∈ C_n r n := by
      have h_pi_mem_I : pi r ω ∈ I_word (take_word n ω) r := by
        exact pi_mem_I_word r hr ω n
      have h_take_word_in_Sigma_n : take_word n ω ∈ Sigma_n n := by
        exact Set.mem_setOf.mpr ( by unfold take_word; simp +decide ) ;
      exact Set.mem_iUnion₂.mpr ⟨take_word n ω, h_take_word_in_Sigma_n, h_pi_mem_I⟩

/-
For every x in C and n, there is a word u of length n such that x is in I_u.
-/
theorem exists_word_of_mem_C (r : ℝ) (x : ℝ) (hx : x ∈ C r) (n : ℕ) :
    ∃ u ∈ Sigma_n n, x ∈ I_word u r := by
      -- By definition of $C$, we know that $x$ is in the union of $I_u(r)$ over all $u$ of length $n$.
      have hx_union : x ∈ C_n r n := by
        exact Set.mem_iInter.mp hx n;
      unfold C_n at hx_union; aesop;

/-
I_{ui} is a subset of I_u.
-/
theorem I_word_subset_of_append (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (u : List (Fin 2)) (i : Fin 2) :
    I_word (u ++ [i]) r ⊆ I_word u r := by
      intro x hx;
      obtain ⟨ y, hy, rfl ⟩ := hx;
      use f i r y;
      induction u <;> simp_all +decide [ f_word ];
      unfold f; fin_cases i <;> constructor <;> norm_num at * <;> nlinarith;

/-
The image of the projection map is contained in the Cantor set.
-/
theorem range_pi_subset_C' (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    Set.range (pi r) ⊆ C r := by
      exact range_pi_subset_C r hr

/-
The map f_u is injective.
-/
theorem f_word_injective (r : ℝ) (hr : r ≠ 0) (u : List (Fin 2)) :
    Function.Injective (f_word u r) := by
      induction u with
      | nil =>
        exact Function.injective_id;
      | cons i u ih =>
        -- By definition of $f_word$, we have $f_word (i :: u) r = f i r ∘ f_word u r$.
        have h_f_word_cons : f_word (i :: u) r = f i r ∘ f_word u r := by
          exact rfl;
        unfold f at *;
        aesop_cat

/-
Distinct words of the same length correspond to disjoint intervals.
-/
theorem disjoint_I_word (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (n : ℕ) (u v : List (Fin 2)) (hu : u ∈ Sigma_n n) (hv : v ∈ Sigma_n n) (hdiff : u ≠ v) :
    Disjoint (I_word u r) (I_word v r) := by
      induction n generalizing u v with
      | zero =>
        cases u <;> cases v <;> simp_all +decide [ Sigma_n ];
      | succ n ih =>
        -- If u and v start with the same symbol, say u = i :: u' and v = i :: v', then by the induction hypothesis, I_word u' r and I_word v' r are disjoint. Since f_i is injective, applying f_i to these intervals will give disjoint intervals.
        by_cases h_start : u.head! = v.head!;
        · obtain ⟨i, u', v', hu', hv', huv'⟩ : ∃ i : Fin 2, ∃ u' v' : List (Fin 2), u = i :: u' ∧ v = i :: v' ∧ u' ≠ v' := by
            rcases u with ( _ | ⟨ i, u ⟩ ) <;> rcases v with ( _ | ⟨ j, v ⟩ ) <;> simp_all +decide [ Sigma_n ];
          simp_all +decide [ Sigma_n ];
          convert Set.disjoint_image_of_injective ( f_word_injective r ( by linarith ) [ i ] ) ( ih u' v' hu hv huv' ) using 1;
          · ext; simp [I_word, f_word];
          · ext; simp [I_word, f_word];
        · -- Since u and v start with different symbols, say u = i :: u' and v = j :: v' with i ≠ j, then by the induction hypothesis, I_word u' r and I_word v' r are disjoint. Since f_i and f_j are disjoint, their images under f_i and f_j will also be disjoint.
          obtain ⟨i, u', hi⟩ : ∃ i u', u = i :: u' := by
            exact List.exists_cons_of_length_eq_add_one hu
          obtain ⟨j, v', hj⟩ : ∃ j v', v = j :: v' := by
            exact List.exists_cons_of_length_eq_add_one hv
          have h_disjoint : Disjoint (f i r '' I_word u' r) (f j r '' I_word v' r) := by
            have h_disjoint : Disjoint (f i r '' Set.Icc 0 1) (f j r '' Set.Icc 0 1) := by
              fin_cases i <;> fin_cases j <;> simp_all +decide [ Set.disjoint_left ];
              · unfold f; norm_num at *; intros; nlinarith;
              · unfold f; norm_num at *; intros; nlinarith;
            refine h_disjoint.mono ?_ ?_;
            · subst hi hj
              simp_all only [one_div, ne_eq, List.cons.injEq, not_and, List.head!_cons, Set.le_eq_subset,
                Set.image_subset_iff, IsEmpty.forall_iff]
              obtain ⟨left, right⟩ := hr
              intro x hx;
              obtain ⟨ y, hy, rfl ⟩ := hx;
              -- By definition of $f_word$, we know that $f_word u' r y$ is in the interval $[0, 1]$.
              have h_f_word_u'_r_y : ∀ u : List (Fin 2), ∀ r : ℝ, 0 < r ∧ r < 1 / 2 → ∀ y ∈ Set.Icc 0 1, f_word u r y ∈ Set.Icc 0 1 := by
                intros u r hr y hy
                induction u generalizing y with
                | nil =>
                  simp_all +decide [ f_word ]
                | cons i u ih =>
                simp_all +decide [ f_word ] ;
                unfold f; fin_cases i <;> norm_num at * <;> constructor <;> nlinarith [ ih _ hy.1 hy.2 ] ;
              simp_all only [Set.mem_Icc, one_div, and_imp, Set.mem_preimage, Set.mem_image]
              obtain ⟨left_1, right_1⟩ := hy
              apply Exists.intro
              · apply And.intro
                on_goal 2 => { rfl
                }
                · simp_all only [and_self]
            · subst hi hj
              simp_all only [one_div, ne_eq, List.cons.injEq, not_and, List.head!_cons, Set.le_eq_subset,
                Set.image_subset_iff, IsEmpty.forall_iff]
              obtain ⟨left, right⟩ := hr
              intro x hx; obtain ⟨ y, hy, rfl ⟩ := hx; exact (by
              -- By definition of $f_word$, we know that $f_word v' r y$ is in the interval $[0, 1]$.
              have h_f_word_v'_r_y : ∀ (v' : List (Fin 2)) (y : ℝ), y ∈ Set.Icc 0 1 → f_word v' r y ∈ Set.Icc 0 1 := by
                intro v' y hy
                induction v' generalizing y with
                | nil =>
                  simp_all +decide [ f_word ]
                | cons i v' ih =>
                simp_all +decide [ f_word ] ;
                unfold f; fin_cases i <;> norm_num at * <;> constructor <;> nlinarith [ ih _ hy.1 hy.2 ] ;
              simp_all only [Set.mem_Icc, and_imp, Set.mem_preimage, Set.mem_image]
              obtain ⟨left_1, right_1⟩ := hy
              apply Exists.intro
              · apply And.intro
                on_goal 2 => { rfl
                }
                · simp_all only [and_self]);
          convert h_disjoint using 1;
          · unfold I_word; aesop;
          · unfold I_word; aesop;

/-
For every x in C and n, the word u of length n such that x is in I_u is unique.
-/
theorem unique_word_of_mem_C (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (x : ℝ) (hx : x ∈ C r) (n : ℕ) :
    ∃! u, u ∈ Sigma_n n ∧ x ∈ I_word u r := by
      obtain ⟨ u, hu ⟩ := exists_word_of_mem_C r x hx n;
      refine ⟨ u, hu, fun v hv => ?_ ⟩;
      by_contra h_neq
      have h_disjoint : Disjoint (I_word u r) (I_word v r) := by
        apply disjoint_I_word r hr n u v hu.1 hv.1 (Ne.symm h_neq)
      exact h_disjoint.le_bot ⟨hu.2, hv.2⟩

/-
The unique words associated with x are compatible.
-/
theorem compatible_words_of_mem_C (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (x : ℝ) (hx : x ∈ C r) (n : ℕ) :
    let u_n := Classical.choose (unique_word_of_mem_C r hr x hx n)
    let u_succ := Classical.choose (unique_word_of_mem_C r hr x hx (n + 1))
    u_succ.take n = u_n := by
      -- By uniqueness of $u_n$, the restriction of $u_{n+1}$ to length $n$ must be equal to $u_n$.
      have h_restrict : Classical.choose (unique_word_of_mem_C r hr x hx (n + 1)) ∈ Sigma_n (n + 1) ∧ Classical.choose (unique_word_of_mem_C r hr x hx n) ∈ Sigma_n n ∧ x ∈ I_word (Classical.choose (unique_word_of_mem_C r hr x hx (n + 1))) r ∧ x ∈ I_word (Classical.choose (unique_word_of_mem_C r hr x hx n)) r := by
        exact ⟨ Classical.choose_spec ( unique_word_of_mem_C r hr x hx ( n + 1 ) ) |>.1.1, Classical.choose_spec ( unique_word_of_mem_C r hr x hx n ) |>.1.1, Classical.choose_spec ( unique_word_of_mem_C r hr x hx ( n + 1 ) ) |>.1.2, Classical.choose_spec ( unique_word_of_mem_C r hr x hx n ) |>.1.2 ⟩;
      -- By the uniqueness of the word of length $n$ containing $x$, the restriction of $u_{n+1}$ to length $n$ must be equal to $u_n$.
      have h_unique : ∀ u v : List (Fin 2), u ∈ Sigma_n (n + 1) → v ∈ Sigma_n n → x ∈ I_word u r → x ∈ I_word v r → List.take n u = v := by
        intros u v hu hv hxu hxv
        have h_subset : I_word (List.take n u ++ [u[n]!]) r ⊆ I_word (List.take n u) r := by
          convert I_word_subset_of_append r hr ( List.take n u ) ( u[n]! ) using 1;
        have h_eq : x ∈ I_word (List.take n u) r := by
          convert h_subset _;
          convert hxu using 1;
          congr! 1;
          refine List.ext_get ?_ ?_ <;> simp_all +decide [ Sigma_n ];
        have := unique_word_of_mem_C r hr x hx n;
        exact this.unique ⟨ by rw [ show List.take n u = List.take n u from rfl ] ; exact show List.length ( List.take n u ) = n from by rw [ List.length_take, min_eq_left ( Nat.le_of_lt_succ <| by linarith [ hu.symm, List.length_pos_iff.mpr <| show u ≠ [ ] from by rintro rfl; exact absurd hu <| by simp +decide [ Sigma_n ] ] ) ], h_eq ⟩ ⟨ hv, hxv ⟩;
      exact h_unique _ _ h_restrict.1 h_restrict.2.1 h_restrict.2.2.1 h_restrict.2.2.2

/-
The code corresponding to a point in the Cantor set.
-/
noncomputable def code_of_mem_C (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (x : ℝ) (hx : x ∈ C r) : ℕ → Fin 2 :=
  fun n =>
    let u_succ := Classical.choose (unique_word_of_mem_C r hr x hx (n + 1))
    u_succ.get ⟨n, by rw [Classical.choose_spec (unique_word_of_mem_C r hr x hx (n + 1)) |>.1.1]; exact Nat.lt_succ_self n⟩

/-
The projection of the code of x is x.
-/
theorem pi_code_of_mem_C (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (x : ℝ) (hx : x ∈ C r) :
    pi r (code_of_mem_C r hr x hx) = x := by
      -- Let's denote the word of length n corresponding to x as u_n.
      set u_n := fun n => Classical.choose (unique_word_of_mem_C r hr x hx n) with hu_n_def
      have hu_n_prefix : ∀ n m, n ≤ m → u_n n = (u_n m).take n := by
        intro n m hnm
        have h_subset : u_n n = (u_n (n + 1)).take n := by
          exact Eq.symm (compatible_words_of_mem_C r hr x hx n)
        generalize_proofs at *; (
        have h_subset_induction : ∀ k ≥ n, u_n n = (u_n k).take n := by
          intro k hk
          induction hk with
          | refl =>
            generalize_proofs at *; (
            have := Classical.choose_spec ( ‹∀ n : ℕ, ∃ x_1 : List ( Fin 2 ), ( fun u : List ( Fin 2 ) => u ∈ Sigma_n n ∧ x ∈ I_word u r ) x_1 ∧ ∀ y : List ( Fin 2 ), y ∈ Sigma_n n ∧ x ∈ I_word y r → y = x_1› n ) |>.1.1; aesop;)
          | step hk ih =>
            rename_i k
            have h_subset_step : u_n k = (u_n (k + 1)).take k := by
              exact Eq.symm (compatible_words_of_mem_C r hr x hx k)
            generalize_proofs at *; (
            rw [ ih, h_subset_step, List.take_take ] ; aesop;)
        generalize_proofs at *; (
        exact h_subset_induction m hnm ▸ rfl))
      have hu_n_limit : ∀ n, x ∈ I_word (u_n n) r := by
        exact fun n => Classical.choose_spec ( unique_word_of_mem_C r hr x hx n ) |>.1 |>.2 |> fun h => h
      have h_limit_eq : Filter.Tendsto (fun n => (pi r (append_zeros (u_n n)))) Filter.atTop (nhds x) := by
        -- By definition of $u_n$, we know that $x \in I_{u_n}(r)$ for all $n$, and the length of $I_{u_n}(r)$ tends to $0$ as $n$ tends to infinity.
        have h_length_zero : Filter.Tendsto (fun n => (r ^ (u_n n).length)) Filter.atTop (nhds 0) := by
          -- Since $u_n$ is a word of length $n$, we have $(u_n n).length = n$.
          have h_length_eq_n : ∀ n, (u_n n).length = n := by
            intro n; exact (Classical.choose_spec (unique_word_of_mem_C r hr x hx n)).1.1;
          simpa only [ h_length_eq_n ] using tendsto_pow_atTop_nhds_zero_of_lt_one hr.1.le ( by linarith );
        -- Since $x \in I_{u_n}(r)$, we have $|x - \pi_r(u_n)| \leq r^n$.
        have h_dist : ∀ n, |x - pi r (append_zeros (u_n n))| ≤ r ^ (u_n n).length := by
          intro n
          specialize hu_n_limit n
          have h_interval : x ∈ Set.Icc (pi r (append_zeros (u_n n))) (pi r (append_ones (u_n n))) := by
            exact prop_symbolic_3_interval r hr ( u_n n ) ▸ hu_n_limit |> fun h => by simpa using h;
          have h_dist : |x - pi r (append_zeros (u_n n))| ≤ r ^ (u_n n).length := by
            rw [ abs_of_nonneg ] <;> linarith [ h_interval.1, h_interval.2, show pi r ( append_ones ( u_n n ) ) = pi r ( append_zeros ( u_n n ) ) + r ^ ( u_n n |> List.length ) from by rw [ pi_append_ones r hr, pi_append_zeros r ] ] ;
          exact h_dist;
        exact tendsto_iff_norm_sub_tendsto_zero.mpr ( squeeze_zero ( fun _ => abs_nonneg _ ) ( fun n => by simpa [ abs_sub_comm ] using h_dist n ) h_length_zero )
      have h_append_zeros_limit : Filter.Tendsto (fun n => (pi r (append_zeros (u_n n)))) Filter.atTop (nhds (pi r (code_of_mem_C r hr x hx))) := by
        have h_append_zeros_limit : Filter.Tendsto (fun n => (∑ k ∈ Finset.range (u_n n).length, ((u_n n)[k]? |>.getD 0 : ℝ) * r ^ k)) Filter.atTop (nhds (∑' k, ((code_of_mem_C r hr x hx) k : ℝ) * r ^ k)) := by
          convert Summable.hasSum _ |> HasSum.tendsto_sum_nat |> Filter.Tendsto.comp <| Filter.tendsto_id using 1
          generalize_proofs at *;
          · ext n; exact (by
            -- Since the length of `u_n n` is `n`, the sum over the range of `n` is the same as the sum over the range of the length of `u_n n`.
            have h_length : (u_n n).length = n := by
              exact Classical.choose_spec ( ‹∀ n : ℕ, ∃ u_1 : List ( Fin 2 ), ( fun u : List ( Fin 2 ) => u ∈ Sigma_n n ∧ x ∈ I_word u r ) u_1 ∧ ∀ y : List ( Fin 2 ), y ∈ Sigma_n n ∧ x ∈ I_word y r → y = u_1› n ) |>.1 |>.1 |> fun h => h.symm ▸ rfl
            generalize_proofs at *;
            rw [h_length];
            refine Finset.sum_congr rfl fun i hi => ?_ ; simp +decide [ code_of_mem_C ] ; ring_nf;
            simp +zetaDelta at *;
            grind +ring);
          · exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hr.1.le _ ) ) ( fun n => mul_le_of_le_one_left ( pow_nonneg hr.1.le _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hr.1.le ( by linarith ) )
        generalize_proofs at *;
        convert h_append_zeros_limit.const_mul ( 1 - r ) using 2 ; ring_nf!;
        rw [ pi_append_zeros ]
        ring_nf
      have h_eq : pi r (code_of_mem_C r hr x hx) = x := by
        exact tendsto_nhds_unique h_append_zeros_limit h_limit_eq
      exact h_eq.symm ▸ rfl

/-
The projection map pi is continuous.
-/
theorem continuous_pi' (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    Continuous (pi r) := by
      refine continuous_const.mul ?_;
      refine continuous_tsum ( u := fun n => r ^ n ) ?_ ?_ ?_;
      · fun_prop (disch := norm_num);
      · exact summable_geometric_of_lt_one hr.1.le ( by linarith );
      · exact fun n x => by simpa [ abs_of_nonneg hr.1.le ] using mul_le_mul_of_nonneg_right ( show ( x n : ℝ ) ≤ 1 by norm_cast; exact Fin.le_last _ ) ( pow_nonneg hr.1.le _ ) ;

/-
Lemma 2.3: Closedness of the limit of Cantor sets.
-/
theorem closedness_limit_Cantor (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (r : ℕ → ℝ) (hr : Filter.Tendsto r Filter.atTop (nhds rho)) (x : ℝ) (hx : ∀ n, x ∈ C (r n)) :
    x ∈ C rho := by
      have h_cont : ∀ᶠ n in Filter.atTop, 0 < r n ∧ r n < 1 / 2 := by
        exact hr.eventually ( Ioo_mem_nhds hrho.1 hrho.2 );
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, 0 < r n ∧ r n < 1 / 2 := by
        exact Filter.eventually_atTop.mp h_cont;
      have h_seq : ∀ n ≥ N, ∃ ω : ℕ → Fin 2, pi (r n) ω = x := by
        exact fun n hn => by have := hx n; exact ⟨ code_of_mem_C ( r n ) ( hN n hn ) x this, pi_code_of_mem_C ( r n ) ( hN n hn ) x this ⟩ ;
      choose! ω hω using h_seq;
      -- By a diagonal subsequence argument, there is a subsequence $n_k$ and an infinite sequence $\omega$ such that $\omega^{(n_k)} \to \omega$.
      obtain ⟨nk, hnk⟩ : ∃ nk : ℕ → ℕ, StrictMono nk ∧ ∃ ω' : ℕ → Fin 2, Filter.Tendsto (fun k => ω (nk k)) Filter.atTop (nhds ω') := by
        have h_compact : IsCompact (Set.univ : Set (ℕ → Fin 2)) := by
          exact isCompact_univ;
        have := h_compact.isSeqCompact fun n => Set.mem_univ ( ω ( N + n ) );
        exact ⟨ fun k => N + this.choose_spec.2.choose k, fun k l hkl => Nat.add_lt_add_left ( this.choose_spec.2.choose_spec.1 hkl ) N, this.choose, this.choose_spec.2.choose_spec.2 ⟩;
      -- Then $x = \pi_\rho(\omega)$ by joint continuity.
      obtain ⟨ω', hω'⟩ := hnk.right;
      have h_lim : Filter.Tendsto (fun k => pi (r (nk k)) (ω (nk k))) Filter.atTop (nhds (pi rho ω')) := by
        have h_joint_cont : ContinuousOn (fun p : ℝ × (ℕ → Fin 2) => pi p.1 p.2) (Set.Icc 0 (1 / 2) ×ˢ Set.univ) := by
          intros p hp;
          refine ContinuousWithinAt.mul ?_ ?_;
          · exact ContinuousWithinAt.sub continuousWithinAt_const continuousWithinAt_fst;
          · refine ( tendsto_tsum_of_dominated_convergence ( bound := fun k => ( 1 : ℝ ) * ( 1 / 2 ) ^ k ) ?_ ?_ ?_ );
            · exact Summable.mul_left _ ( summable_geometric_two );
            · intro k;
              refine tendsto_nhdsWithin_of_tendsto_nhds ?_;
              refine Continuous.tendsto'
                ( f := fun q : ℝ × ( ℕ → Fin 2 ) => ( q.2 k : ℝ ) * q.1 ^ k )
                ?_ p ( ( p.2 k : ℝ ) * p.1 ^ k ) ?_;
              · fun_prop;
              · rfl;
            · norm_num +zetaDelta at *;
              filter_upwards [ self_mem_nhdsWithin ] with n hn using fun k => le_trans ( mul_le_of_le_one_left ( by positivity ) ( mod_cast Fin.is_le _ ) ) ( pow_le_pow_left₀ ( by positivity ) ( by rw [ abs_of_nonneg ] <;> linarith [ hn.1.1, hn.1.2 ] ) _ );
        have h_joint_cont : Filter.Tendsto (fun k => (r (nk k), ω (nk k))) Filter.atTop (nhds (rho, ω')) := by
          exact Filter.Tendsto.prodMk_nhds ( hr.comp hnk.1.tendsto_atTop ) hω';
        rename_i h;
        exact h.continuousWithinAt ( show ( rho, ω' ) ∈ Set.Icc 0 ( 1 / 2 ) ×ˢ Set.univ from ⟨ ⟨ by linarith, by linarith ⟩, Set.mem_univ _ ⟩ ) |> fun h => h.tendsto.comp <| Filter.tendsto_inf.mpr ⟨ h_joint_cont, Filter.tendsto_principal.mpr <| Filter.eventually_atTop.mpr ⟨ N, fun k hk => ⟨ ⟨ by linarith [ hN ( nk k ) ( hk.trans <| hnk.1.id_le _ ) ], by linarith [ hN ( nk k ) ( hk.trans <| hnk.1.id_le _ ) ] ⟩, Set.mem_univ _ ⟩ ⟩ ⟩;
      have h_lim_eq : pi rho ω' = x := by
        exact tendsto_nhds_unique h_lim ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ge_atTop N ] with k hk; rw [ hω _ ( hk.trans ( hnk.1.id_le _ ) ) ] ) );
      exact h_lim_eq ▸ range_pi_subset_C' rho hrho ( Set.mem_range_self ω' )

/-
Lemma 2.4(1): pi_r(omega) is strictly increasing if omega starts with 0 and is not 0^infty.
-/
theorem pi_strictly_increasing (ω : ℕ → Fin 2) (h0 : ω 0 = 0) (h_not_zero : ∃ n, ω n ≠ 0) :
    StrictMonoOn (fun r => pi r ω) (Set.Ico 0 (1 / 2)) := by
      -- Let $n$ be the smallest index such that $\omega_n = 1$.
      obtain ⟨n, hn⟩ : ∃ n, ω n = 1 ∧ ∀ m < n, ω m = 0 := by
        exact ⟨ Nat.find h_not_zero, Or.resolve_left ( Fin.exists_fin_two.mp ( by aesop ) ) ( Nat.find_spec h_not_zero ), fun m mn => by simpa using Nat.find_min h_not_zero mn ⟩;
      -- We can write $\omega$ as $0^n 1 \sigma$ for some sequence $\sigma$.
      obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → Fin 2, ω = fun m => if m < n then 0 else if m = n then 1 else σ (m - n - 1) := by
        use fun m => ω (m + n + 1);
        grind +ring;
      -- Then $\pi_r(\omega) = (1-r) \sum_{k=0}^{n-1} 0 \cdot r^k + (1-r) r^n + (1-r) r^{n+1} \sum_{k=0}^{\infty} \sigma_k r^k = (1-r) r^n + (1-r) r^{n+1} \sum_{k=0}^{\infty} \sigma_k r^k$.
      have h_pi_expansion : ∀ r ∈ Set.Ico 0 (1 / 2), pi r ω = (1 - r) * r ^ n + (1 - r) * r ^ (n + 1) * ∑' k, (σ k : ℝ) * r ^ k := by
        intro r hr
        have h_split_sum : ∑' k, (ω k : ℝ) * r ^ k = (∑ k ∈ Finset.range n, (ω k : ℝ) * r ^ k) + (ω n : ℝ) * r ^ n + (∑' k, (ω (n + k + 1) : ℝ) * r ^ (n + k + 1)) := by
          rw [ ← Summable.sum_add_tsum_nat_add ];
          case k => exact n + 1;
          · norm_num [ add_comm, add_left_comm, add_assoc, Finset.sum_range_succ ];
          · exact Summable.of_nonneg_of_le ( fun k => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hr.1 _ ) ) ( fun k => mul_le_of_le_one_left ( pow_nonneg hr.1 _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hr.1 ( by linarith [ hr.2 ] ) );
        convert congr_arg ( fun x : ℝ => ( 1 - r ) * x ) h_split_sum using 1 ; norm_num [ Finset.sum_range, hn, hσ ] ; ring_nf;
        norm_num [ add_comm 1, add_assoc, mul_assoc, tsum_mul_left ] ; ring;
      have hn_pos : 0 < n := by
        cases n with
        | zero => simpa [h0] using hn.1
        | succ n => exact Nat.succ_pos n
      -- The term $(1-r) r^n$ is strictly increasing on $[0, 1 / 2)$.
      have h_term1_inc : StrictMonoOn (fun r : ℝ => (1 - r) * r ^ n) (Set.Ico 0 (1 / 2)) := by
        -- Let's calculate the derivative of $(1-r) r^n$ and show it is positive on $(0, 1 / 2)$.
        have h_deriv_pos : ∀ r ∈ Set.Ioo 0 (1 / 2), deriv (fun r : ℝ => (1 - r) * r ^ n) r > 0 := by
          intro r hr
          rcases n with _ | n
          · exact False.elim (Nat.lt_irrefl 0 hn_pos)
          · have hderiv :
                deriv (fun r : ℝ => (1 - r) * r ^ (n + 1)) r =
                  r ^ n * ((n + 1 : ℝ) - (n + 2 : ℝ) * r) := by
              have h1 : HasDerivAt (fun r : ℝ => 1 - r) (-1) r := by
                simpa using (hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)
              have h2 : HasDerivAt (fun r : ℝ => r ^ (n + 1)) ((n + 1 : ℝ) * r ^ n) r := by
                simpa [Nat.cast_add, Nat.cast_one] using hasDerivAt_pow (n + 1) r
              have hderiv' :
                  deriv (fun r : ℝ => (1 - r) * r ^ (n + 1)) r =
                    (-1) * r ^ (n + 1) + (1 - r) * ((n + 1 : ℝ) * r ^ n) := by
                simpa using (h1.mul h2).deriv
              ring_nf at hderiv' ⊢
              exact hderiv'
            rw [hderiv]
            exact mul_pos (pow_pos hr.1 _) (by nlinarith [hr.2])
        intros x hx y hy hxy;
        have := exists_deriv_eq_slope ( fun r => ( 1 - r ) * r ^ n ) hxy ; norm_num at *;
        exact this ( Continuous.continuousOn <| by continuity ) ( Differentiable.differentiableOn <| by exact Differentiable.mul ( differentiable_id.const_sub _ ) <| differentiable_pow _ ) |> fun ⟨ c, hc₁, hc₂ ⟩ => by have := h_deriv_pos c ( by linarith ) ( by linarith ) ; rw [ hc₂, lt_div_iff₀ ] at this <;> linarith;
      -- The term $(1-r) r^{n+1} \sum_{k=0}^{\infty} \sigma_k r^k$ is non-decreasing on $[0, 1 / 2)$.
      have h_term2_nondec : ∀ r1 r2 : ℝ, 0 ≤ r1 → r1 < r2 → r2 < 1 / 2 → (1 - r1) * r1 ^ (n + 1) * ∑' k, (σ k : ℝ) * r1 ^ k ≤ (1 - r2) * r2 ^ (n + 1) * ∑' k, (σ k : ℝ) * r2 ^ k := by
        intros r1 r2 hr1 hr2 hr2_half
        have h_term2_nondec : (1 - r1) * r1 ^ (n + 1) ≤ (1 - r2) * r2 ^ (n + 1) := by
          have := h_term1_inc ( show r1 ∈ Set.Ico 0 ( 1 / 2 ) from ⟨ hr1, by linarith ⟩ ) ( show r2 ∈ Set.Ico 0 ( 1 / 2 ) from ⟨ by linarith, hr2_half ⟩ ) hr2;
          norm_num [ pow_succ' ] at *;
          nlinarith [ mul_le_mul_of_nonneg_left hr2.le ( pow_nonneg hr1 n ), mul_le_mul_of_nonneg_left hr2.le ( pow_nonneg ( by linarith : 0 ≤ r2 ) n ) ];
        gcongr;
        · exact mul_nonneg ( by linarith ) ( pow_nonneg ( by linarith ) _ );
        · exact Summable.of_nonneg_of_le ( fun _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hr1 _ ) ) ( fun _ => mul_le_of_le_one_left ( pow_nonneg hr1 _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hr1 ( by linarith ) );
        · exact Summable.of_nonneg_of_le ( fun _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by linarith ) _ ) ) ( fun _ => mul_le_of_le_one_left ( pow_nonneg ( by linarith ) _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one ( by linarith ) ( by linarith ) );
      intros r1 hr1 r2 hr2 hlt;
      simpa only [ h_pi_expansion r1 hr1, h_pi_expansion r2 hr2 ] using add_lt_add_of_lt_of_le ( h_term1_inc hr1 hr2 hlt ) ( h_term2_nondec r1 r2 hr1.1 hlt hr2.2 )

/-
Lemma 2.4(2): pi_r(omega) is strictly decreasing if omega starts with 1 and is not 1^infty.
-/
theorem pi_strictly_decreasing (ω : ℕ → Fin 2) (h1 : ω 0 = 1) (h_not_one : ∃ n, ω n ≠ 1) :
    StrictAntiOn (fun r => pi r ω) (Set.Ico 0 (1 / 2)) := by
      intro r hr s hs hrs;
      -- By definition of $pi$, we know that $pi_r(omega) = 1 - pi_r(1-omega)$.
      have h_pi_symm : ∀ r ∈ Set.Ico 0 (1 / 2), pi r ω = 1 - pi r (fun n => 1 - ω n) := by
        unfold pi;
        intro r hr; rw [ show ( ∑' n : ℕ, ( ↑ ( ↑ ( ω n ) ) : ℝ ) * r ^ n ) = ∑' n : ℕ, ( 1 - ( ↑ ( ↑ ( 1 - ω n ) ) : ℝ ) ) * r ^ n from tsum_congr fun n => ?_ ] ; norm_num [ sub_mul, tsum_mul_left ];
        · rw [ Summable.tsum_sub, tsum_geometric_of_lt_one hr.1 ( by linarith [ hr.2 ] ) ];
          · linarith [ inv_mul_cancel₀ ( by linarith [ hr.1, hr.2 ] : ( 1 - r ) ≠ 0 ) ];
          · exact summable_geometric_of_lt_one hr.1 ( by linarith [ hr.2 ] );
          · exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hr.1 _ ) ) ( fun n => mul_le_of_le_one_left ( pow_nonneg hr.1 _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hr.1 ( by linarith [ hr.2 ] ) );
        · cases Fin.exists_fin_two.mp ⟨ ω n, rfl ⟩ <;> simp +decide [ * ];
      -- By definition of $pi$, we know that $pi_r(1-omega)$ is strictly increasing.
      have h_pi_inc : StrictMonoOn (fun r => pi r (fun n => 1 - ω n)) (Set.Ico 0 (1 / 2)) := by
        apply_rules [ pi_strictly_increasing ];
        · aesop;
        · exact h_not_one.imp fun n hn => by rw [ Ne.eq_def, sub_eq_zero ] ; aesop;
      aesop

/-
The set E_rho^+ of exceptional points.
-/
def E_plus (rho : ℝ) : Set ℝ :=
  {x | ∃ u : List (Fin 2), u ≠ [] ∧ u.head! = 0 ∧ x = pi rho (append_ones u)} ∪
  {x | ∃ u : List (Fin 2), u ≠ [] ∧ u.head! = 1 ∧ x = pi rho (append_zeros u)}

/-
R_u(rho) is not in C_alpha^+ if u starts with 0.
-/
theorem not_mem_C_plus_of_R_u (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (u : List (Fin 2)) (hu : u ≠ []) (h0 : u.head! = 0) :
    pi rho (append_ones u) ∉ C_plus rho := by
      -- Let $x = \pi_\rho(\text{append\_ones } u)$. We need to show that $x \notin C_\alpha^+$.
      set x := pi rho (append_ones u) with hx
      have hx_not_in_C_plus : ∀ᶠ r in nhdsWithin rho (Set.Iio rho), x∉ C r := by
        -- For $r$ close to $\rho$, $x$ is not in $I_u(r)$ (since $x > R_u(r)$) and not in $I_v(r)$ (by continuity of endpoints).
        have hx_not_in_I_u : ∀ᶠ r in nhdsWithin rho (Set.Iio rho), x∉ I_word u r := by
          -- Since $x = \pi_\rho(\text{append\_ones } u)$, we have $x > R_u(r)$ for $r$ close to $\rho$.
          have hx_gt_R_u_r : ∀ᶠ r in nhdsWithin rho (Set.Iio rho), x > pi r (append_ones u) := by
            have h_inc : StrictMonoOn (fun r => pi r (append_ones u)) (Set.Ico 0 (1 / 2)) := by
              apply pi_strictly_increasing;
              · cases u <;> aesop;
              · use u.length; simp [append_ones];
            filter_upwards [ Ioo_mem_nhdsLT hrho.1 ] with r hr using h_inc ⟨ by linarith [ hr.1 ], by linarith [ hr.2 ] ⟩ ⟨ by linarith [ hr.1 ], by linarith [ hr.2 ] ⟩ hr.2;
          filter_upwards [ hx_gt_R_u_r, Ioo_mem_nhdsLT hrho.1 ] with r hr₁ hr₂ ; rw [ prop_symbolic_3_interval r ⟨ hr₂.1, hr₂.2.trans_le <| by linarith ⟩ u ] ; aesop;
        have hx_not_in_I_v : ∀ᶠ r in nhdsWithin rho (Set.Iio rho), ∀ v ∈ Sigma_n u.length, v ≠ u → x∉ I_word v r := by
          -- Since $x$ is the right endpoint of $I_u(\rho)$, for $r$ close to $\rho$, $x$ is not in $I_v(r)$ for any $v \neq u$ of the same length.
          have hx_not_in_I_v : ∀ v ∈ Sigma_n u.length, v ≠ u → ∀ᶠ r in nhdsWithin rho (Set.Iio rho), x∉ I_word v r := by
            intros v hv hv_ne_u
            have h_disjoint : Disjoint (I_word u rho) (I_word v rho) := by
              apply disjoint_I_word rho hrho u.length u v; aesop;
              · exact hv;
              · exact hv_ne_u.symm
            have h_cont : ContinuousAt (fun r => pi r (append_ones u)) rho ∧ ContinuousAt (fun r => pi r (append_zeros v)) rho ∧ ContinuousAt (fun r => pi r (append_ones v)) rho := by
              have h_cont : ∀ ω : ℕ → Fin 2, ContinuousAt (fun r => pi r ω) rho := by
                intro ω
                have h_cont : ContinuousAt (fun r => (1 - r) * ∑' n : ℕ, (ω n : ℝ) * r ^ n) rho := by
                  refine ContinuousAt.mul ( continuousAt_const.sub continuousAt_id ) ?_;
                  refine ( tendsto_tsum_of_dominated_convergence ( bound := fun k => ( 1 : ℝ ) * ( 1 / 2 ) ^ k ) ?_ ?_ ?_ );
                  all_goals generalize_proofs at *;
                  · exact Summable.mul_left _ ( summable_geometric_two );
                  · exact fun k => Continuous.tendsto ( by continuity ) _;
                  · norm_num +zetaDelta at *;
                    filter_upwards [ Ioo_mem_nhds hrho.1 ( show rho < 1 / 2 by linarith ) ] with n hn k using le_trans ( mul_le_of_le_one_left ( by positivity ) ( mod_cast Fin.is_le _ ) ) ( pow_le_pow_left₀ ( by positivity ) ( show |n| ≤ 1 / 2 by rw [ abs_of_nonneg ] <;> linarith [ hn.1, hn.2 ] ) _ ) |> le_trans <| by norm_num;
                generalize_proofs at *; (
                convert h_cont using 1)
              generalize_proofs at *; (
              exact ⟨ h_cont _, h_cont _, h_cont _ ⟩)
            have h_not_in_I_v : ∀ᶠ r in nhdsWithin rho (Set.Iio rho), x∉ I_word v r := by
              have h_not_in_I_v : ∀ᶠ r in nhdsWithin rho (Set.Iio rho), x∉ Set.Icc (pi r (append_zeros v)) (pi r (append_ones v)) := by
                have h_not_in_I_v : x∉ Set.Icc (pi rho (append_zeros v)) (pi rho (append_ones v)) := by
                  have h_not_in_I_v : x∉ I_word v rho := by
                    exact fun h => h_disjoint.le_bot ⟨ by
                      convert pi_mem_I_word rho hrho ( append_ones u ) u.length using 1
                      generalize_proofs at *; (
                      congr! 1
                      generalize_proofs at *; (
                      refine List.ext_get ?_ ?_ <;> simp +decide [ take_word ];
                      intro n hn; unfold append_ones; aesop;)), h ⟩
                  generalize_proofs at *; (
                  convert h_not_in_I_v using 1
                  generalize_proofs at *; (
                  rw [ prop_symbolic_3_interval rho hrho v ]))
                generalize_proofs at *; (
                have h_not_in_I_v : ∀ᶠ r in nhdsWithin rho (Set.Iio rho), x∉ Set.Icc (pi r (append_zeros v)) (pi r (append_ones v)) := by
                  have h_cont : ContinuousAt (fun r => (pi r (append_zeros v), pi r (append_ones v))) rho := by
                    exact ContinuousAt.prodMk h_cont.2.1 h_cont.2.2
                  have h_not_in_I_v : ∀ᶠ r in nhdsWithin rho (Set.Iio rho), (pi r (append_zeros v), pi r (append_ones v))∉ {p : ℝ × ℝ | x ∈ Set.Icc p.1 p.2} := by
                    have h_closed : IsClosed {p : ℝ × ℝ | x ∈ Set.Icc p.1 p.2} := by
                      exact IsClosed.inter ( isClosed_le continuous_fst continuous_const ) ( isClosed_le continuous_const continuous_snd )
                    exact h_cont.eventually ( h_closed.isOpen_compl.mem_nhds <| by aesop ) |> fun h => h.filter_mono nhdsWithin_le_nhds;
                  generalize_proofs at *; (
                  exact h_not_in_I_v.mono fun r hr => by simpa using hr;)
                generalize_proofs at *; (
                convert h_not_in_I_v using 1))
              generalize_proofs at *; (
              filter_upwards [ h_not_in_I_v, mem_nhdsWithin_of_mem_nhds ( Ioo_mem_nhds hrho.1 hrho.2 ) ] with r hr₁ hr₂ using fun hr₃ => hr₁ <| by rw [ prop_symbolic_3_interval r ⟨ hr₂.1, hr₂.2 ⟩ v ] at hr₃; exact hr₃;)
            exact h_not_in_I_v;
          have h_finite : Set.Finite {v : List (Fin 2) | v ∈ Sigma_n u.length ∧ v ≠ u} := by
            have h_finite : Set.Finite {v : List (Fin 2) | v.length = u.length} := by
              exact List.finite_length_eq (Fin 2) u.length;
            exact h_finite.subset fun v hv => hv.1;
          rw [ eventually_nhdsWithin_iff ] at *;
          rw [ Metric.eventually_nhds_iff ] at *;
          choose! ε hε using fun v hv hv' => Metric.mem_nhdsWithin_iff.mp ( hx_not_in_I_v v hv hv' );
          obtain ⟨ε_min, hε_min⟩ : ∃ ε_min > 0, ∀ v ∈ h_finite.toFinset, ε_min ≤ ε v := by
            by_cases h_empty : h_finite.toFinset.Nonempty;
            · exact ⟨ Finset.min' ( h_finite.toFinset.image ε ) ⟨ _, Finset.mem_image_of_mem ε h_empty.choose_spec ⟩, by have := Finset.min'_mem ( h_finite.toFinset.image ε ) ⟨ _, Finset.mem_image_of_mem ε h_empty.choose_spec ⟩ ; aesop, fun v hv => Finset.min'_le _ _ <| Finset.mem_image_of_mem ε hv ⟩;
            · exact ⟨ 1, zero_lt_one, fun v hv => False.elim <| h_empty ⟨ v, hv ⟩ ⟩;
          exact ⟨ ε_min, hε_min.1, fun y hy₁ hy₂ v hv hv' => hε v hv hv' |>.2 ⟨ Metric.mem_ball.mpr <| lt_of_lt_of_le hy₁ <| hε_min.2 v <| h_finite.mem_toFinset.mpr ⟨ hv, hv' ⟩, hy₂ ⟩ ⟩;
        have hx_not_in_C_n : ∀ᶠ r in nhdsWithin rho (Set.Iio rho), x∉ C_n r u.length := by
          filter_upwards [ hx_not_in_I_u, hx_not_in_I_v ] with r hr₁ hr₂ using fun hr₃ => by rcases Set.mem_iUnion₂.mp hr₃ with ⟨ v, hv₁, hv₂ ⟩ ; by_cases hv₃ : v = u <;> aesop;
        filter_upwards [ hx_not_in_C_n ] with r hr using fun h => hr <| Set.mem_iInter.mp h u.length;
      intro h;
      unfold C_plus at h; simp_all +decide [ eventually_nhdsWithin_iff ] ;
      rcases Metric.eventually_nhds_iff.mp hx_not_in_C_plus with ⟨ ε, ε_pos, hε ⟩ ; rcases h ε ε_pos with ⟨ r, ⟨ hr₁, hr₂ ⟩, hr₃ ⟩ ; exact hε ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) hr₂ hr₃;

/-
R_u(rho) is not in C_alpha^+ if u starts with 0.
-/
theorem not_mem_C_plus_of_R_u' (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (u : List (Fin 2)) (hu : u ≠ []) (h0 : u.head! = 0) :
    pi rho (append_ones u) ∉ C_plus rho := by
      exact not_mem_C_plus_of_R_u rho hrho u hu h0

/-
The left endpoint of the interval I_u(r).
-/
noncomputable def L_word (u : List (Fin 2)) (r : ℝ) := pi r (append_zeros u)

/-
The right endpoint of the interval I_u(r).
-/
noncomputable def R_word (u : List (Fin 2)) (r : ℝ) := pi r (append_ones u)

/-
pi_r(append_zeros u) is strictly decreasing if u starts with 1.
-/
theorem pi_append_zeros_strictly_decreasing (u : List (Fin 2)) (hu : u ≠ []) (h1 : u.head! = 1) :
    StrictAntiOn (fun r => pi r (append_zeros u)) (Set.Ico 0 (1 / 2)) := by
      apply_rules [ pi_strictly_decreasing ];
      · cases u <;> aesop;
      · use u.length + 1; simp [append_zeros]

/-
R_u(rho) is not in I_v(r) for r close to rho, if v != u.
-/
theorem not_mem_I_word_of_ne (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (u : List (Fin 2)) (v : List (Fin 2)) (hv : v ∈ Sigma_n u.length) (h_ne : v ≠ u) :
    ∀ᶠ r in nhds rho, pi rho (append_ones u) ∉ I_word v r := by
      -- By definition of $C_plus$, we know that $I_u(rho)$ and $I_v(rho)$ are disjoint compact sets.
      have h_disjoint : Disjoint (I_word u rho) (I_word v rho) := by
        apply disjoint_I_word;
        exacts [ hrho, by exact rfl, hv, Ne.symm h_ne ];
      -- Since $I_u(rho)$ and $I_v(rho)$ are disjoint compact sets, there exists a neighborhood $U$ of $rho$ such that for all $r \in U$, $I_u(rho)$ and $I_v(r)$ are disjoint.
      obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ r, abs (r - rho) < ε → Disjoint (I_word u rho) (I_word v r) := by
        obtain ⟨δ, hδ⟩ : ∃ δ > 0, ∀ x ∈ I_word u rho, ∀ y ∈ I_word v rho, abs (x - y) ≥ δ := by
          have h_compact : IsCompact (I_word u rho) ∧ IsCompact (I_word v rho) := by
            constructor;
            · exact ( prop_symbolic_1_interval rho hrho u ) ▸ CompactIccSpace.isCompact_Icc;
            · exact ( prop_symbolic_1_interval rho hrho v ) ▸ CompactIccSpace.isCompact_Icc
          generalize_proofs at *; (
          have h_dist : ∃ δ > 0, ∀ x ∈ I_word u rho, ∀ y ∈ I_word v rho, |x - y| ≥ δ := by
            have h_nonempty : I_word u rho ≠ ∅ ∧ I_word v rho ≠ ∅ := by
              exact ⟨ Set.Nonempty.ne_empty ⟨ _, Set.mem_image_of_mem _ <| Set.left_mem_Icc.mpr zero_le_one ⟩, Set.Nonempty.ne_empty ⟨ _, Set.mem_image_of_mem _ <| Set.left_mem_Icc.mpr zero_le_one ⟩ ⟩ ;
            have h_dist : IsCompact (I_word u rho ×ˢ I_word v rho) := by
              exact h_compact.1.prod h_compact.2
            generalize_proofs at *; (
            have h_dist : ∃ δ > 0, ∀ p ∈ I_word u rho ×ˢ I_word v rho, |p.1 - p.2| ≥ δ := by
              have h_cont : ContinuousOn (fun p : ℝ × ℝ => |p.1 - p.2|) (I_word u rho ×ˢ I_word v rho) := by
                exact ContinuousOn.abs ( continuousOn_fst.sub continuousOn_snd )
              have h_min : ∃ p ∈ I_word u rho ×ˢ I_word v rho, ∀ q ∈ I_word u rho ×ˢ I_word v rho, |p.1 - p.2| ≤ |q.1 - q.2| := by
                exact h_dist.exists_isMinOn ( Set.nonempty_iff_ne_empty.mpr <| by aesop ) h_cont |> fun ⟨ p, hp₁, hp₂ ⟩ => ⟨ p, hp₁, fun q hq => hp₂ hq ⟩ ;
              generalize_proofs at *; (
              obtain ⟨ p, hp₁, hp₂ ⟩ := h_min; exact ⟨ |p.1 - p.2|, abs_pos.mpr ( sub_ne_zero.mpr <| by intro h; exact h_disjoint.le_bot ⟨ hp₁.1, by simpa [ h ] using hp₁.2 ⟩ ), fun q hq => hp₂ q hq ⟩ ;)
            generalize_proofs at *; (
            exact ⟨ h_dist.choose, h_dist.choose_spec.1, fun x hx y hy => h_dist.choose_spec.2 ( x, y ) ⟨ hx, hy ⟩ ⟩))
          generalize_proofs at *; (
          exact h_dist));
        -- Since $I_v(r)$ is continuous in $r$, there exists a neighborhood $U$ of $rho$ such that for all $r \in U$, $I_v(r)$ is within $\delta/2$ of $I_v(rho)$.
        obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ r, abs (r - rho) < ε → ∀ x ∈ I_word v r, ∃ y ∈ I_word v rho, abs (x - y) < δ / 2 := by
          have h_cont : ContinuousOn (fun p : ℝ × ℝ => f_word v p.1 p.2) (Set.Icc (rho - 1 / 4) (rho + 1 / 4) ×ˢ Set.Icc 0 1) := by
            refine Continuous.continuousOn ?_;
            have h_cont : ∀ u : List (Fin 2), Continuous (fun p : ℝ × ℝ => f_word u p.1 p.2) := by
              intro u; induction u <;> simp_all +decide [ f_word ] ; continuity;
              rename_i k hk ih; unfold f; split_ifs <;> continuity;
            exact h_cont v;
          obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ r, abs (r - rho) < ε → ∀ x ∈ Set.Icc 0 1, abs (f_word v r x - f_word v rho x) < δ / 2 := by
            have h_unif_cont : UniformContinuousOn (fun p : ℝ × ℝ => f_word v p.1 p.2) (Set.Icc (rho - 1 / 4) (rho + 1 / 4) ×ˢ Set.Icc 0 1) := by
              exact ( isCompact_Icc.prod CompactIccSpace.isCompact_Icc ) |> fun h => h.uniformContinuousOn_of_continuous h_cont;
            rcases Metric.uniformContinuousOn_iff.mp h_unif_cont ( δ / 2 ) ( half_pos hδ.1 ) with ⟨ ε, ε_pos, hε ⟩;
            exact ⟨ Min.min ε ( 1 / 4 ), lt_min ε_pos ( by norm_num ), fun r hr x hx => hε ( r, x ) ⟨ ⟨ by linarith [ abs_lt.mp hr, min_le_left ε ( 1 / 4 ), min_le_right ε ( 1 / 4 ) ], by linarith [ abs_lt.mp hr, min_le_left ε ( 1 / 4 ), min_le_right ε ( 1 / 4 ) ] ⟩, hx ⟩ ( rho, x ) ⟨ ⟨ by linarith [ abs_lt.mp hr, min_le_left ε ( 1 / 4 ), min_le_right ε ( 1 / 4 ) ], by linarith [ abs_lt.mp hr, min_le_left ε ( 1 / 4 ), min_le_right ε ( 1 / 4 ) ] ⟩, hx ⟩ ( by simpa using lt_of_lt_of_le hr ( min_le_left _ _ ) ) ⟩;
          use ε, hε.1;
          rintro r hr x ⟨ y, hy, rfl ⟩ ; exact ⟨ _, ⟨ y, hy, rfl ⟩, hε.2 r hr y hy ⟩ ;
        refine ⟨ ε, hε.1, fun r hr => Set.disjoint_left.mpr fun x hxu hxv => ?_ ⟩;
        obtain ⟨ y, hyv, hyx ⟩ := hε.2 r hr x hxv ; exact not_lt_of_ge ( hδ.2 x hxu y hyv ) ( by cases abs_cases ( x - y ) <;> cases abs_cases ( x - x ) <;> linarith );
      filter_upwards [ Metric.ball_mem_nhds rho hε.1 ] with r hr using fun h => Set.disjoint_left.mp ( hε.2 r hr ) ( show pi rho ( append_ones u ) ∈ I_word u rho from by
                                                                                                                      rw [ prop_symbolic_3_interval rho hrho u ] ; norm_num [ hrho ];
                                                                                                                      rw [ pi_append_zeros rho u, pi_append_ones rho hrho u ] ; linarith [ pow_pos hrho.1 u.length ] ; ) h

/-
L_u(rho) is not in C_alpha^+ if u starts with 1.
-/
theorem not_mem_C_plus_of_L_u (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (u : List (Fin 2)) (hu : u ≠ []) (h1 : u.head! = 1) :
    pi rho (append_zeros u) ∉ C_plus rho := by
      have h_not_in_C_plus : ∀ᶠ r in nhdsWithin rho (Set.Iio rho), pi rho (append_zeros u) ∉ ⋃ u_1 ∈ Sigma_n u.length, I_word u_1 r := by
        -- Since $pi_r(append_zeros u)$ is strictly decreasing and $u$ starts with $1$, for $r$ close to $\rho$, $pi_r(append_zeros u)$ is not in $I_v(r)$ for any $v \neq u$.
        have h_not_in_I_word : ∀ᶠ r in nhdsWithin rho (Set.Iio rho), ∀ v ∈ Sigma_n u.length, v ≠ u → pi rho (append_zeros u) ∉ I_word v r := by
          have h_not_in_I_word : ∀ v ∈ Sigma_n u.length, v ≠ u → ∀ᶠ r in nhds rho, pi rho (append_zeros u) ∉ I_word v r := by
            intros v hv hv_ne_u
            have h_not_in_I_word : ∀ᶠ r in nhds rho, pi rho (append_zeros u) ∉ I_word v r := by
              have h_cont : ContinuousAt (fun r => pi rho (append_zeros u) - (1 - r) * (∑ k ∈ Finset.range v.length, ((v[k]?).getD 0 : ℝ) * r ^ k)) rho ∧ ContinuousAt (fun r => pi rho (append_zeros u) - ((1 - r) * (∑ k ∈ Finset.range v.length, ((v[k]?).getD 0 : ℝ) * r ^ k) + r ^ v.length)) rho := by
                exact ⟨ Continuous.continuousAt ( by continuity ), Continuous.continuousAt ( by continuity ) ⟩;
              have h_not_in_I_word : pi rho (append_zeros u) ∉ I_word v rho := by
                have h_not_in_I_word : Disjoint (I_word v rho) (I_word u rho) := by
                  exact disjoint_I_word rho hrho u.length v u hv rfl hv_ne_u;
                have h_not_in_I_word : pi rho (append_zeros u) ∈ I_word u rho := by
                  rw [ prop_symbolic_3_interval rho hrho u ];
                  simp
                  rw [ pi_append_zeros, pi_append_ones ];
                  · exact le_add_of_nonneg_right ( pow_nonneg hrho.1.le _ );
                  · tauto;
                exact fun h => Set.disjoint_left.mp ‹_› h h_not_in_I_word;
              have h_not_in_I_word : pi rho (append_zeros u) < (1 - rho) * (∑ k ∈ Finset.range v.length, ((v[k]?).getD 0 : ℝ) * rho ^ k) ∨ pi rho (append_zeros u) > (1 - rho) * (∑ k ∈ Finset.range v.length, ((v[k]?).getD 0 : ℝ) * rho ^ k) + rho ^ v.length := by
                contrapose! h_not_in_I_word;
                rw [ prop_symbolic_3_interval ];
                · convert h_not_in_I_word using 1;
                  rw [ pi_append_zeros, pi_append_ones ] <;> norm_num [ hrho ];
                · tauto;
              rcases h_not_in_I_word with h | h;
              · have h_not_in_I_word : ∀ᶠ r in nhds rho, pi rho (append_zeros u) < (1 - r) * (∑ k ∈ Finset.range v.length, ((v[k]?).getD 0 : ℝ) * r ^ k) := by
                  have := h_cont.1.eventually ( gt_mem_nhds <| show pi rho ( append_zeros u ) - ( 1 - rho ) * ∑ k ∈ Finset.range v.length, ( v[k]? |> Option.getD <| 0 ) * rho ^ k < 0 from sub_neg_of_lt h ) ; aesop;
                filter_upwards [ h_not_in_I_word, Ioo_mem_nhds hrho.1 hrho.2 ] with r hr₁ hr₂;
                rw [ prop_symbolic_1_interval ] <;> norm_num at *;
                · exact fun h => False.elim <| hr₁.not_ge h;
                · tauto;
              · have h_not_in_I_word : ∀ᶠ r in nhds rho, pi rho (append_zeros u) > (1 - r) * (∑ k ∈ Finset.range v.length, ((v[k]?).getD 0 : ℝ) * r ^ k) + r ^ v.length := by
                  have := h_cont.2.eventually ( lt_mem_nhds <| show pi rho ( append_zeros u ) - ( ( 1 - rho ) * ∑ k ∈ Finset.range v.length, ( v[k]? |> Option.getD <| 0 ) * rho ^ k + rho ^ v.length ) > 0 from by linarith ) ; aesop;
                filter_upwards [ h_not_in_I_word, Ioo_mem_nhds hrho.1 hrho.2 ] with r hr₁ hr₂;
                rw [ prop_symbolic_1_interval r ⟨ hr₂.1, hr₂.2 ⟩ v ];
                exact fun h => hr₁.not_ge h.2
            exact h_not_in_I_word;
          have h_finite : Set.Finite {v ∈ Sigma_n u.length | v ≠ u} := by
            have h_finite : Set.Finite {v : List (Fin 2) | v.length = u.length} := by
              exact List.finite_length_eq (Fin 2) u.length;
            exact h_finite.subset fun v hv => hv.1;
          have h_finite : ∀ᶠ r in nhds rho, ∀ v ∈ {v ∈ Sigma_n u.length | v ≠ u}, pi rho (append_zeros u) ∉ I_word v r := by
            exact h_finite.eventually_all.mpr fun v hv => h_not_in_I_word v hv.1 hv.2;
          exact h_finite.filter_mono nhdsWithin_le_nhds |> fun h => h.mono fun r hr v hv hv' => hr v ⟨ hv, hv' ⟩;
        -- Since $pi_r(append_zeros u)$ is strictly decreasing and $u$ starts with $1$, for $r$ close to $\rho$, $pi_r(append_zeros u)$ is not in $I_u(r)$.
        have h_not_in_I_u : ∀ᶠ r in nhdsWithin rho (Set.Iio rho), pi rho (append_zeros u) ∉ I_word u r := by
          have h_not_in_I_u : ∀ᶠ r in nhdsWithin rho (Set.Iio rho), pi r (append_zeros u) > pi rho (append_zeros u) := by
            have h_not_in_I_u : StrictAntiOn (fun r => pi r (append_zeros u)) (Set.Ico 0 (1 / 2)) := by
              exact pi_append_zeros_strictly_decreasing u hu h1;
            filter_upwards [ Ioo_mem_nhdsLT hrho.1 ] with r hr using h_not_in_I_u ⟨ by linarith [ hr.1 ], by linarith [ hr.2 ] ⟩ ⟨ by linarith [ hr.1 ], by linarith [ hr.2 ] ⟩ hr.2;
          filter_upwards [ h_not_in_I_u, mem_nhdsWithin_of_mem_nhds ( Ioo_mem_nhds hrho.1 hrho.2 ) ] with r hr₁ hr₂;
          rw [ prop_symbolic_3_interval ] <;> aesop;
        filter_upwards [ h_not_in_I_word, h_not_in_I_u ] with r hr₁ hr₂ using by intro hr₃; rcases Set.mem_iUnion₂.mp hr₃ with ⟨ v, hv₁, hv₂ ⟩ ; by_cases hv₃ : v = u <;> aesop;
      simp_all +decide [ C_plus ];
      obtain ⟨ ε, hε, H ⟩ := Metric.mem_nhdsWithin_iff.mp h_not_in_C_plus;
      refine ⟨ ε, hε, fun r hr₁ hr₂ => ?_ ⟩ ; specialize H ⟨ Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith, by linarith ⟩, hr₂ ⟩ ; simp_all +decide [ C ] ;
      exact ⟨ u.length, fun h => by rcases Set.mem_iUnion₂.mp h with ⟨ x, hx, hx' ⟩ ; exact H x hx hx' ⟩

/-
The set Sigma_n is finite.
-/
theorem finite_Sigma_n (n : ℕ) : Set.Finite (Sigma_n n) := by
  -- The set of all functions from a finite type to a finite type is finite.
  have h_finite_functions : Set.Finite {f : Fin n → Fin 2 | True} := by
    exact Set.toFinite _;
  refine Set.Finite.subset ( h_finite_functions.image ( fun f : Fin n → Fin 2 => List.ofFn f ) ) ?_;
  intro u hu; rcases hu with ⟨ hu₁, hu₂ ⟩ ; use fun i => u[i]!; aesop;

/-
L_u(rho) is not in I_v(r) for r close to rho, if v != u.
-/
theorem not_mem_I_word_of_ne_zeros (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (u : List (Fin 2)) (v : List (Fin 2)) (hv : v ∈ Sigma_n u.length) (h_ne : v ≠ u) :
    ∀ᶠ r in nhds rho, pi rho (append_zeros u) ∉ I_word v r := by
      -- By definition of $C_plus$, we know that if $x \in C_plus$, then there exists a sequence $r_n \to \rho$ such that $x \in C(r_n)$.
      by_contra h_contra;
      obtain ⟨r_n, hr_n⟩ : ∃ r_n : ℕ → ℝ, Filter.Tendsto r_n Filter.atTop (nhds rho) ∧ ∀ n, pi rho (append_zeros u) ∈ I_word v (r_n n) := by
        rw [ Metric.eventually_nhds_iff ] at h_contra;
        push Not at h_contra;
        exact ⟨ fun n => Classical.choose ( h_contra ( 1 / ( n + 1 ) ) ( by positivity ) ), tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => Classical.choose_spec ( h_contra ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.1.le ) <| tendsto_one_div_add_atTop_nhds_zero_nat, fun n => Classical.choose_spec ( h_contra ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.2 ⟩;
      -- By definition of $I_word$, we know that if $x \in I_word v (r_n n)$, then there exists $y \in [0, 1]$ such that $f_word v (r_n n) y = x$.
      obtain ⟨y_n, hy_n⟩ : ∃ y_n : ℕ → ℝ, ∀ n, y_n n ∈ Set.Icc 0 1 ∧ f_word v (r_n n) (y_n n) = pi rho (append_zeros u) := by
        exact ⟨ fun n => Classical.choose ( hr_n.2 n ), fun n => Classical.choose_spec ( hr_n.2 n ) ⟩;
      -- Since $y_n$ is bounded, it has a convergent subsequence.
      obtain ⟨y, hy⟩ : ∃ y, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => y_n (subseq n)) Filter.atTop (nhds y) := by
        have h_compact : IsCompact (Set.Icc (0 : ℝ) 1) := by
          exact CompactIccSpace.isCompact_Icc;
        have := h_compact.isSeqCompact fun n => hy_n n |>.1; aesop;
      -- By continuity of $f_word$, we have $f_word v (rho) y = pi rho (append_zeros u)$.
      have h_cont : f_word v rho y = pi rho (append_zeros u) := by
        obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hy;
        have h_cont : Filter.Tendsto (fun n => f_word v (r_n (subseq n)) (y_n (subseq n))) Filter.atTop (nhds (f_word v rho y)) := by
          have h_cont : Continuous (fun p : ℝ × ℝ => f_word v p.1 p.2) := by
            -- By definition of $f_word$, we know that it is a composition of continuous functions.
            have h_cont : ∀ (u : List (Fin 2)) (r : ℝ) (x : ℝ), f_word u r x = (1 - r) * (∑ k ∈ Finset.range u.length, ((u[k]?).getD 0 : ℝ) * r ^ k) + r ^ u.length * x := by
              exact fun u r x => prop_symbolic_1 r u x;
            simp [h_cont];
            fun_prop;
          exact h_cont.continuousAt.tendsto.comp ( Filter.Tendsto.prodMk_nhds ( hr_n.1.comp hsubseq₁.tendsto_atTop ) hsubseq₂ );
        exact tendsto_nhds_unique h_cont ( by simpa only [ hy_n ] using tendsto_const_nhds );
      -- Since $v \neq u$, we have $I_word v rho$ and $I_word u rho$ are disjoint.
      have h_disjoint : Disjoint (I_word v rho) (I_word u rho) := by
        exact disjoint_I_word rho hrho u.length v u hv rfl h_ne;
      have h_mem : pi rho (append_zeros u) ∈ I_word u rho := by
        use 0
        simp
        rw [ prop_symbolic_1 ]
        norm_num [ pi_append_zeros ]
      exact h_disjoint.le_bot ⟨ ⟨ y, by
        exact ⟨ le_of_tendsto_of_tendsto' tendsto_const_nhds hy.choose_spec.2 fun n => hy_n _ |>.1.1, le_of_tendsto_of_tendsto' hy.choose_spec.2 tendsto_const_nhds fun n => hy_n _ |>.1.2 ⟩, h_cont ⟩, h_mem ⟩

/-
pi(omega) < R_{u_n}(rho) if omega is not eventually 1.
-/
theorem pi_lt_R_word_of_not_eventually_one (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (ω : ℕ → Fin 2) (h_not_ev_one : ∀ n, ∃ k ≥ n, ω k ≠ 1) (n : ℕ) :
    pi rho ω < R_word (take_word n ω) rho := by
      obtain ⟨ k, hk₁, hk₂ ⟩ := h_not_ev_one n; simp_all +decide [ R_word ] ;
      unfold pi; norm_num [ Finset.sum_range_succ, take_word ] ;
      refine mul_lt_mul_of_pos_left ?_ ( sub_pos.mpr <| by norm_num at *; linarith );
      fapply Summable.tsum_lt_tsum;
      use k;
      · intro m; by_cases hm : m < n <;> simp_all +decide [ append_ones ] ;
        exact Fin.is_le _;
      · cases Fin.exists_fin_two.mp ⟨ ω k, rfl ⟩ <;> simp_all +decide [ append_ones ];
      · exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hrho.1.le _ ) ) ( fun n => mul_le_of_le_one_left ( pow_nonneg hrho.1.le _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hrho.1.le ( by norm_num at *; linarith ) );
      · refine Summable.of_nonneg_of_le ( fun _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hrho.1.le _ ) ) ( fun _ => mul_le_of_le_one_left ( pow_nonneg hrho.1.le _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hrho.1.le ( by norm_num at *; linarith ) )

/-
0 and 1 are in C_alpha^+.
-/
theorem endpoints_mem_C_plus (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) :
    0 ∈ C_plus rho ∧ 1 ∈ C_plus rho := by
      constructor <;> refine Set.mem_iInter₂.mpr fun ε hε => ?_;
      · simp +zetaDelta at *;
        refine ⟨ rho - Min.min ε rho / 2, ?_, ?_ ⟩;
        · constructor <;> linarith [ lt_min hε hrho.1, min_le_left ε rho, min_le_right ε rho ];
        · -- By definition of $C$, we know that $0 \in C(r)$ for any $r$.
          have h_zero_in_C : ∀ r : ℝ, 0 < r ∧ r < 1 / 2 → 0 ∈ C r := by
            intros r hr
            have h_zero_in_C : 0 ∈ Set.range (pi r) := by
              use fun _ => 0; simp [pi]
            exact (by
            exact range_pi_subset_C r hr h_zero_in_C);
          exact h_zero_in_C _ ⟨ by linarith [ lt_min hε hrho.1, min_le_left ε rho, min_le_right ε rho ], by linarith [ lt_min hε hrho.1, min_le_left ε rho, min_le_right ε rho ] ⟩;
      · -- Since $C_r$ is a Cantor set for any $r$, it contains the points $0$ and $1$.
        have h_C_r_contains_one : ∀ r : ℝ, 0 < r ∧ r < 1 / 2 → 1 ∈ C r := by
          intro r hr
          have h_one : 1 ∈ Set.range (pi r) := by
            use fun _ => 1; norm_num [ pi ] ; ring_nf ;
            rw [ tsum_geometric_of_lt_one hr.1.le ( by linarith ) ] ; nlinarith [ mul_inv_cancel₀ ( by linarith : ( 1 - r ) ≠ 0 ) ] ;
          exact range_pi_subset_C r hr |> Set.mem_of_mem_of_subset h_one;
        exact Set.mem_iUnion₂.mpr ⟨ rho - Min.min ε rho / 2, ⟨ by linarith [ lt_min hε hrho.1, min_le_left ε rho, min_le_right ε rho ], by linarith [ lt_min hε hrho.1, min_le_left ε rho, min_le_right ε rho ] ⟩, h_C_r_contains_one _ ⟨ by linarith [ lt_min hε hrho.1, min_le_left ε rho, min_le_right ε rho ], by linarith [ lt_min hε hrho.1, min_le_left ε rho, min_le_right ε rho ] ⟩ ⟩

/-
pi(omega) > L_{u_n}(rho) if omega is not eventually 0.
-/
theorem pi_gt_L_word_of_not_eventually_zero (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (ω : ℕ → Fin 2) (h_not_ev_zero : ∀ n, ∃ k ≥ n, ω k ≠ 0) (n : ℕ) :
    pi rho ω > L_word (take_word n ω) rho := by
      unfold L_word;
      -- By definition of $pi$, we can expand both sides.
      have h_expand : (pi rho ω) - (pi rho (append_zeros (take_word n ω))) = (1 - rho) * (∑' k, ((ω (n + k)) : ℝ) * rho ^ (n + k)) := by
        unfold pi append_zeros;
        rw [ ← mul_sub, ← Summable.tsum_sub ];
        · rw [ ← Summable.sum_add_tsum_nat_add n ];
          · simp +decide [ add_comm n, Finset.sum_range, take_word ];
          · refine Summable.sub ?_ ?_;
            · exact Summable.of_nonneg_of_le ( fun _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hrho.1.le _ ) ) ( fun _ => mul_le_of_le_one_left ( pow_nonneg hrho.1.le _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hrho.1.le ( by linarith ) );
            · refine Summable.of_nonneg_of_le ( fun _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hrho.1.le _ ) ) ( fun _ => mul_le_of_le_one_left ( pow_nonneg hrho.1.le _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hrho.1.le ( by linarith ) );
        · exact Summable.of_nonneg_of_le ( fun _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hrho.1.le _ ) ) ( fun _ => mul_le_of_le_one_left ( pow_nonneg hrho.1.le _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hrho.1.le ( by linarith ) );
        · refine Summable.of_nonneg_of_le ( fun _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hrho.1.le _ ) ) ( fun _ => mul_le_of_le_one_left ( pow_nonneg hrho.1.le _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hrho.1.le ( by linarith ) );
      -- Since $\omega$ is not eventually zero, there exists some $k \geq 0$ such that $\omega (n + k) = 1$.
      obtain ⟨k, hk⟩ : ∃ k, ω (n + k) = 1 := by
        obtain ⟨ k, hk₁, hk₂ ⟩ := h_not_ev_zero n; use k - n; simp_all +decide [ add_tsub_cancel_of_le hk₁ ] ;
        exact Or.resolve_left ( Fin.exists_fin_two.mp ( by tauto ) ) hk₂;
      have h_pos : ∑' k, ((ω (n + k)) : ℝ) * rho ^ (n + k) ≥ rho ^ (n + k) := by
        refine le_trans ?_ ( Summable.le_tsum ?_ k ?_ );
        · aesop;
        · exact Summable.of_nonneg_of_le ( fun _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hrho.1.le _ ) ) ( fun _ => mul_le_of_le_one_left ( pow_nonneg hrho.1.le _ ) ( mod_cast Fin.is_le _ ) ) ( Summable.comp_injective ( summable_geometric_of_lt_one hrho.1.le ( by linarith ) ) ( add_right_injective n ) );
        · exact fun _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hrho.1.le _ );
      have h_sum_pos : 0 < ∑' k, ((ω (n + k)) : ℝ) * rho ^ (n + k) :=
        lt_of_lt_of_le ( pow_pos hrho.1 ( n + k ) ) h_pos;
      have h_diff_pos : 0 < pi rho ω - pi rho ( append_zeros ( take_word n ω ) ) := by
        rw [ h_expand ];
        exact mul_pos ( sub_pos.mpr <| by linarith ) h_sum_pos;
      exact sub_pos.mp h_diff_pos

/-
L_u(rho) is not in C_alpha^+ if u starts with 1.
-/
theorem not_mem_C_plus_of_L_u' (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (u : List (Fin 2)) (hu : u ≠ []) (h1 : u.head! = 1) :
    pi rho (append_zeros u) ∉ C_plus rho := by
      -- Apply the theorem that states $L_u(rho) \notin C_\alpha^+$ if $u$ starts with $1$.
      apply not_mem_C_plus_of_L_u rho hrho u hu h1

/-
If x is not in E_plus and starts with 0, its code is not eventually 1.
-/
theorem not_eventually_one_of_mem_diff (rho : ℝ) (_hrho : 0 < rho ∧ rho < 1 / 2) (x : ℝ) (hx_not_E : x ∉ E_plus rho) (ω : ℕ → Fin 2) (hω : pi rho ω = x) (h0 : ω 0 = 0) :
    ∀ n, ∃ k ≥ n, ω k ≠ 1 := by
      classical
      -- Assume for contradiction that ω is eventually 1.
      by_contra h_contra
      obtain ⟨u, hu⟩ : ∃ u : List (Fin 2), u ≠ [] ∧ ω = append_ones u := by
        norm_num +zetaDelta at *;
        obtain ⟨ n, hn ⟩ := Nat.findX h_contra;
        refine ⟨ List.ofFn fun i : Fin n => ω i, ?_, ?_ ⟩ <;> simp_all +decide [ funext_iff ];
        · grind +ring;
        · intro x; by_cases hx : x < n <;> simp_all +decide [ append_ones ] ;
      simp_all +decide [ E_plus ];
      exact hx_not_E.1 u hu.1 ( by cases u <;> tauto ) hω.symm

/-
R_{u_n}(r) converges to pi_r(omega).
-/
theorem tendsto_R_word (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (ω : ℕ → Fin 2) :
    Filter.Tendsto (fun n => R_word (take_word n ω) r) Filter.atTop (nhds (pi r ω)) := by
      -- By definition of $R_word$, we know that $R_word (take_word n ω) r = (1 - r) * (∑ k ∈ Finset.range n, (ω k : ℝ) * r ^ k) + r ^ n$.
      have hR_word : ∀ n, R_word (take_word n ω) r = (1 - r) * (∑ k ∈ Finset.range n, (ω k : ℝ) * r ^ k) + r ^ n := by
        intro n
        simp [R_word, take_word];
        convert pi_append_ones r hr ( List.ofFn fun i : Fin n => ω i ) using 1;
        norm_num [ Finset.sum_range ];
      -- By definition of $pi$, we know that $pi r ω = (1 - r) * ∑' k, (ω k : ℝ) * r ^ k$.
      have hpi : pi r ω = (1 - r) * (∑' k, (ω k : ℝ) * r ^ k) := by
        exact rfl
      simp_all +decide
      exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.mul ( Summable.hasSum ( show Summable _ from Summable.of_nonneg_of_le ( fun _ ↦ mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hr.1.le _ ) ) ( fun _ ↦ mul_le_of_le_one_left ( pow_nonneg hr.1.le _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hr.1.le ( by norm_num at *; linarith ) ) ) |> HasSum.tendsto_sum_nat ) ) ( tendsto_pow_atTop_nhds_zero_of_lt_one hr.1.le ( by norm_num at *; linarith ) ) ) ( by norm_num )

open scoped ENNReal

open Topology Filter Metric MeasureTheory

noncomputable def N_delta (E : Set ℝ) (δ : ℝ) : ℕ :=
  sInf {n | ∃ (U : Fin n → Set ℝ), (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ) ∧ E ⊆ ⋃ i, U i}

noncomputable def lower_box_dim (E : Set ℝ) : ℝ :=
  Filter.liminf (fun δ => Real.log (N_delta E δ) / -Real.log δ) (nhdsWithin 0 (Set.Ioi 0))

noncomputable def upper_box_dim (E : Set ℝ) : ℝ :=
  Filter.limsup (fun δ => Real.log (N_delta E δ) / -Real.log δ) (nhdsWithin 0 (Set.Ioi 0))

/-
The covering number of a set is the same as the covering number of its closure.
-/
lemma N_delta_closure_eq (E : Set ℝ) (δ : ℝ) :
  N_delta E δ = N_delta (closure E) δ := by
    refine congr_arg ?_ ( Set.ext ?_ );
    intro n
    constructor;
    · rintro ⟨ U, hU₁, hU₂ ⟩;
      refine ⟨ ?_, ?_, ?_ ⟩;
      exact fun i => closure ( U i );
      · intro i; specialize hU₁ i; rw [ Metric.ediam_closure ] ; aesop;
      · exact closure_minimal ( Set.Subset.trans hU₂ <| Set.iUnion_mono fun _ => subset_closure ) <| isClosed_iUnion_of_finite fun _ => isClosed_closure;
    · exact fun ⟨ U, hU₁, hU₂ ⟩ => ⟨ U, hU₁, Set.Subset.trans ( subset_closure ) hU₂ ⟩

/-
Box dimensions are unchanged by taking closure.
-/
theorem lem_closure_box (E : Set ℝ) :
    lower_box_dim E = lower_box_dim (closure E) ∧
    upper_box_dim E = upper_box_dim (closure E) := by
      apply And.intro;
      · refine Filter.liminf_congr ?_
        filter_upwards [ self_mem_nhdsWithin ] with δ hδ using by rw [ N_delta_closure_eq E δ ]
      · refine Filter.limsup_congr ?_
        filter_upwards [ self_mem_nhdsWithin ] with δ hδ using by rw [ N_delta_closure_eq E δ ]

/-
Bernoulli measure on {0,1}.
-/
noncomputable def bernoulliMeasure : Measure (Fin 2) := (1 / 2 : ENNReal) • (Measure.dirac 0 + Measure.dirac 1)

instance : IsProbabilityMeasure bernoulliMeasure := by
  constructor ; norm_num [ bernoulliMeasure ];
  rw [ ← two_mul, ENNReal.mul_inv_cancel ] <;> norm_num

/-
Infinite Bernoulli measure on {0,1}^N.
-/
noncomputable def infiniteBernoulliMeasure : Measure (ℕ → Fin 2) := MeasureTheory.Measure.infinitePi (fun _ => bernoulliMeasure)

instance : IsProbabilityMeasure infiniteBernoulliMeasure := by
  unfold infiniteBernoulliMeasure
  infer_instance

/-
The pushforward measure mu on the Cantor set.
-/
noncomputable def mu (r : ℝ) : Measure ℝ := infiniteBernoulliMeasure.map (pi r)

instance (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) : IsProbabilityMeasure (mu r) := by
  unfold mu
  apply MeasureTheory.Measure.isProbabilityMeasure_map
  exact (continuous_pi' r hr).aemeasurable

/-
Helper lemma: the scaled measure is bounded by the diameter power.
-/
theorem measure_le_condition (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    (s : ℝ) (hs : 0 ≤ s) (C : ℝ) (hC : 0 < C) (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (h_bound : ∀ U : Set ℝ, 0 < Metric.ediam U → Metric.ediam U ≤ ENNReal.ofReal δ₀ →
      μ U ≤ ENNReal.ofReal C * (Metric.ediam U) ^ s)
    (U : Set ℝ) (hU : Metric.ediam U ≤ ENNReal.ofReal δ₀) :
    (ENNReal.ofReal C)⁻¹ * μ U ≤ (Metric.ediam U) ^ s := by
      by_cases hU_pos : 0 < Metric.ediam U;
      · rw [ ENNReal.inv_mul_le_iff ] <;> aesop;
      · cases eq_or_ne s 0 <;> simp_all +decide
        · rw [ ENNReal.inv_mul_le_iff ] <;> norm_num [ hC ];
          by_cases hU_empty : U = ∅;
          · aesop;
          · -- Since the diameter of U is zero, U must be a singleton set.
            obtain ⟨x, hx⟩ : ∃ x, U = {x} := by
              rw [ Metric.ediam_eq_zero_iff ] at hU_pos;
              exact ⟨ Classical.choose ( Set.nonempty_iff_ne_empty.mpr hU_empty ), Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨ Set.nonempty_iff_ne_empty.mpr hU_empty, fun x hx => hU_pos hx ( Classical.choose_spec ( Set.nonempty_iff_ne_empty.mpr hU_empty ) ) ⟩ ⟩;
            contrapose! h_bound;
            refine ⟨ Metric.closedBall x ( δ₀ / 2 ), ?_, ?_, ?_ ⟩;
            · refine lt_of_lt_of_le ?_ ( Metric.edist_le_ediam_of_mem ( Metric.mem_closedBall_self <| by positivity ) ( Metric.mem_closedBall.mpr <| show |x + δ₀ / 2 - x| ≤ δ₀ / 2 by norm_num [ abs_of_pos, hδ₀ ] ) ) ; norm_num [ hδ₀ ];
              linarith;
            · refine Metric.ediam_le ?_;
              intro y hy z hz; rw [ edist_dist ] ; exact ENNReal.ofReal_le_ofReal ( by linarith [ dist_triangle_left y z x, dist_triangle_right y z x, Metric.mem_closedBall.mp hy, Metric.mem_closedBall.mp hz ] ) ;
            · exact h_bound.trans_le ( MeasureTheory.measure_mono <| by rw [ hx ] ; exact Set.singleton_subset_iff.mpr <| Metric.mem_closedBall.mpr <| by norm_num; linarith );
        · cases eq_or_ne ( μ U ) 0 <;> simp_all +decide
          simp_all +decide [ Metric.ediam_eq_zero_iff ];
          have h_singleton : ∀ x ∈ U, μ U ≤ 0 := by
            intros x hx
            have h_singleton : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), μ U ≤ ENNReal.ofReal C * (ENNReal.ofReal (2 * r)) ^ s := by
              filter_upwards [ Ioo_mem_nhdsGT ( show 0 < δ₀ / 2 by positivity ) ] with r hr;
              refine le_trans ( MeasureTheory.measure_mono ( show U ⊆ Metric.closedBall x r from fun y hy => ?_ ) ) ?_;
              · exact hU_pos hy hx ▸ by simpa using hr.1.le;
              · refine le_trans ( h_bound ( Metric.closedBall x r ) ?_ ?_ ) ?_;
                · refine lt_of_lt_of_le ?_ ( Metric.edist_le_ediam_of_mem ( Metric.mem_closedBall_self hr.1.le ) ( Metric.mem_closedBall.mpr <| show Dist.dist ( x + r ) x ≤ r from by simp [ abs_of_pos hr.1 ] ) ) ; aesop;
                · refine le_trans ( Metric.ediam_le ( d := ENNReal.ofReal ( 2 * r ) ) ?_ ) ?_;
                  · intro y hy z hz; rw [ edist_dist ] ; exact ENNReal.ofReal_le_ofReal ( by linarith [ dist_triangle_left y z x, dist_triangle_right y z x, Metric.mem_closedBall.mp hy, Metric.mem_closedBall.mp hz ] ) ;
                  · exact ENNReal.ofReal_le_ofReal ( by linarith [ hr.1, hr.2 ] );
                · gcongr;
                  refine Metric.ediam_le ?_;
                  intro y hy z hz; rw [ edist_dist ] ; exact ENNReal.ofReal_le_ofReal ( by linarith [ dist_triangle_left y z x, dist_triangle_right y z x, hy.out, hz.out ] ) ;
            have h_singleton : Filter.Tendsto (fun r : ℝ => ENNReal.ofReal C * (ENNReal.ofReal (2 * r)) ^ s) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
              have h_singleton : Filter.Tendsto (fun r : ℝ => ENNReal.ofReal (2 * r) ^ s) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
                convert ENNReal.continuous_rpow_const.continuousAt.tendsto.comp ( ENNReal.continuous_ofReal.continuousAt.tendsto.comp ( tendsto_const_nhds.mul ( Filter.tendsto_id.mono_left inf_le_left ) ) ) using 2 ; norm_num [ * ];
                rw [ ENNReal.zero_rpow_of_pos ( by positivity ) ];
              convert ENNReal.Tendsto.const_mul h_singleton _ using 1 ; aesop;
              norm_num [ ENNReal.ofReal_ne_top ];
            exact le_of_tendsto_of_tendsto tendsto_const_nhds h_singleton ‹_›;
          cases isEmpty_or_nonempty U <;> aesop

/-
Helper lemma for mass distribution principle: (1/C)μ ≤ H^s.
-/
theorem mass_distribution_le (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    (s : ℝ) (hs : 0 ≤ s) (C : ℝ) (hC : 0 < C) (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (h_bound : ∀ U : Set ℝ, 0 < Metric.ediam U → Metric.ediam U ≤ ENNReal.ofReal δ₀ →
      μ U ≤ ENNReal.ofReal C * (Metric.ediam U) ^ s) :
    (ENNReal.ofReal C)⁻¹ • μ ≤ MeasureTheory.Measure.hausdorffMeasure s := by
  apply MeasureTheory.Measure.le_hausdorffMeasure s _ (ENNReal.ofReal δ₀) (ENNReal.ofReal_pos.mpr hδ₀)
  intro U hU
  rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]
  exact measure_le_condition μ s hs C hC δ₀ hδ₀ h_bound U hU

/-
Mass distribution principle: if a measure scales like (diam)^s, the dimension is at least s.
-/
theorem mass_distribution_principle (E : Set ℝ) (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    (h_supp : μ Eᶜ = 0)
    (s : ℝ) (hs : 0 ≤ s) (C : ℝ) (hC : 0 < C) (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (h_bound : ∀ U : Set ℝ, 0 < Metric.ediam U → Metric.ediam U ≤ ENNReal.ofReal δ₀ →
      μ U ≤ ENNReal.ofReal C * (Metric.ediam U) ^ s) :
    MeasureTheory.Measure.hausdorffMeasure s E ≥ ENNReal.ofReal (1 / C) ∧ dimH E ≥ ENNReal.ofReal s := by
      have h1 : MeasureTheory.Measure.hausdorffMeasure s E ≥ ENNReal.ofReal ( 1 / C ) := by
        have h_mass : (ENNReal.ofReal C)⁻¹ • μ ≤ MeasureTheory.Measure.hausdorffMeasure s := by
          convert mass_distribution_le μ s hs C hC δ₀ hδ₀ h_bound using 1;
        have := h_mass E; simp_all +decide
        rw [ show μ E = 1 by rw [ MeasureTheory.measure_congr ( MeasureTheory.ae_eq_univ.mpr <| MeasureTheory.ae_iff.mp <| by aesop ) ] ; norm_num ] at this ; aesop
      have h2 : dimH E ≥ ENNReal.ofReal s := by
        refine le_of_not_gt fun h => ?_;
        -- Since $\dim_H E < s$, there exists $t < s$ such that $\mathcal{H}^t(E) < \infty$.
        obtain ⟨t, ht₁, ht₂⟩ : ∃ t < s, MeasureTheory.Measure.hausdorffMeasure t E < ⊤ := by
          contrapose! h;
          simp_all +decide [ dimH ];
          refine le_of_forall_lt fun x hx => ?_;
          rcases ENNReal.lt_iff_exists_real_btwn.mp hx with ⟨ y, hy₁, hy₂ ⟩;
          refine lt_of_lt_of_le hy₂.1 ( le_trans ?_ <| le_iSup₂_of_le ⟨ y, hy₁ ⟩ ?_ <| le_rfl );
          · norm_num [ ENNReal.ofReal_le_iff_le_toReal ];
          · exact h y ( by simpa using ENNReal.ofReal_lt_ofReal_iff ( by linarith [ show 0 < s from lt_of_le_of_ne hs ( Ne.symm <| by aesop_cat ) ] ) |>.1 hy₂.2 );
        -- Since $\mathcal{H}^t(E) < \infty$, we have $\mathcal{H}^s(E) = 0$.
        have h3 : MeasureTheory.Measure.hausdorffMeasure s E = 0 := by
          have h3 : ∀ t s : ℝ, t < s → MeasureTheory.Measure.hausdorffMeasure t E < ⊤ → MeasureTheory.Measure.hausdorffMeasure s E = 0 := by
            intros t s hts ht₂; exact (by
            have := @MeasureTheory.Measure.hausdorffMeasure_zero_or_top ℝ;
            exact Or.resolve_right ( this hts E ) ( ne_of_lt ht₂ ));
          exact h3 t s ht₁ ht₂;
        exact absurd h1 ( by rw [ h3 ] ; exact not_le_of_gt ( ENNReal.ofReal_pos.mpr ( one_div_pos.mpr hC ) ) )
      exact ⟨h1, h2⟩

/-
Property of the similarity dimension s: 2 * r^s = 1.
-/
theorem s_property (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    let s := Real.log 2 / -Real.log r
    2 * r ^ s = 1 := by
      norm_num [ Real.rpow_def_of_pos hr.1 ];
      ring_nf; norm_num [ hr.1.ne', hr.2.ne', Real.exp_neg, Real.exp_log ] ;
      rw [ mul_right_comm, mul_inv_cancel₀ ( ne_of_lt ( Real.log_neg hr.1 ( by linarith ) ) ), one_mul, Real.exp_log ] <;> norm_num

/-
Upper bound for the Hausdorff dimension of the Cantor set.
-/
lemma dimH_C_le_s (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    dimH (C r) ≤ ENNReal.ofReal (Real.log 2 / -Real.log r) := by
      -- Let $s$ be the similarity dimension, so $2r^s = 1$.
      set s := Real.log 2 / (-Real.log r)
      have hs : 2 * r^s = 1 := by
        exact s_property r hr;
      -- Therefore, $H^s(C(r)) \leq 1$.
      have h_Hausdorff_le_one : MeasureTheory.Measure.hausdorffMeasure s (C r) ≤ 1 := by
        -- For any $n$, $C(r)$ is covered by $2^n$ intervals of length $r^n$.
        have h_cover : ∀ n : ℕ, ∃ (U : Fin (2^n) → Set ℝ), (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal (r^n)) ∧ C r ⊆ ⋃ i, U i := by
          intro n
          have h_cover : C r ⊆ ⋃ u ∈ Sigma_n n, I_word u r := by
            exact Set.iInter_subset _ _;
          -- Since $I_word u r$ is an interval of length $r^n$, we can cover it with a single interval of length $r^n$.
          have h_interval_length : ∀ u ∈ Sigma_n n, Metric.ediam (I_word u r) ≤ ENNReal.ofReal (r ^ n) := by
            intros u hu
            have h_interval_length : I_word u r = Set.Icc ((1 - r) * ∑ k ∈ Finset.range n, ((u[k]?).getD 0 : ℝ) * r ^ k) ((1 - r) * (∑ k ∈ Finset.range n, ((u[k]?).getD 0 : ℝ) * r ^ k) + r ^ n) := by
              convert prop_symbolic_1_interval r hr u using 1;
              rw [ hu.symm ];
            rw [ h_interval_length, Real.ediam_Icc ] ; norm_num [ hr.1.le, hr.2.le ];
          -- Since $Sigma_n n$ is finite, we can enumerate its elements.
          obtain ⟨u_enum, hu_enum⟩ : ∃ u_enum : Fin (2 ^ n) → List (Fin 2), (∀ i, u_enum i ∈ Sigma_n n) ∧ ∀ u ∈ Sigma_n n, ∃ i, u_enum i = u := by
            have h_finite : Set.Finite (Sigma_n n) := by
              exact finite_Sigma_n n;
            have h_card : Finset.card (h_finite.toFinset) = 2 ^ n := by
              rw [ show h_finite.toFinset = Finset.image ( fun u : Fin n → Fin 2 => List.ofFn u ) Finset.univ from ?_, Finset.card_image_of_injective ];
              · norm_num [ Finset.card_univ ];
              · exact fun u v h => by simpa [ funext_iff ] using h;
              · ext; simp [Sigma_n];
                constructor;
                · intro h; use fun i => ‹List ( Fin 2 ) ›[i]!; ext i; aesop;
                · rintro ⟨ a, rfl ⟩ ; simp +decide [ List.length_ofFn ];
            have h_enum : Nonempty (Fin (2 ^ n) ≃ h_finite.toFinset) := by
              exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ h_card ] ⟩;
            obtain ⟨ e ⟩ := h_enum;
            exact ⟨ fun i => e i |>.1, fun i => h_finite.mem_toFinset.mp ( e i |>.2 ), fun u hu => ⟨ e.symm ⟨ u, h_finite.mem_toFinset.mpr hu ⟩, by simp +decide ⟩ ⟩;
          use fun i => I_word (u_enum i) r;
          exact ⟨ fun i => h_interval_length _ ( hu_enum.1 i ), fun x hx => by rcases Set.mem_iUnion₂.mp ( h_cover hx ) with ⟨ u, hu, hx ⟩ ; obtain ⟨ i, rfl ⟩ := hu_enum.2 u hu; exact Set.mem_iUnion.mpr ⟨ i, hx ⟩ ⟩;
        -- The sum of the s-th powers of the diameters is $2^n * (r^n)^s = (2 * r^s)^n = 1^n = 1$.
        have h_sum : ∀ n : ℕ, ∑ i : Fin (2^n), (ENNReal.ofReal (r^n)) ^ s = 1 := by
          intro n
          have h_sum : ∑ i : Fin (2 ^ n), (ENNReal.ofReal (r ^ n)) ^ s = ENNReal.ofReal (2 ^ n * (r ^ n) ^ s) := by
            norm_num [ ENNReal.ofReal_mul ( pow_nonneg hr.1.le _ ) ];
            rw [ ENNReal.ofReal_rpow_of_pos ( pow_pos hr.1 _ ) ];
          convert h_sum using 1;
          rw [ ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hr.1.le, mul_comm ];
          rw [ show ( r ^ ( n * s ) * 2 ^ ( n : ℝ ) ) = ( 2 * r ^ s ) ^ n by rw [ mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hr.1.le ] ; ring_nf, hs ] ; norm_num;
        refine le_trans ( MeasureTheory.Measure.hausdorffMeasure_apply s ( C r ) |> le_of_eq ) ?_;
        refine iSup_le fun δ => iSup_le fun hδ => ?_;
        -- Choose $n$ such that $r^n < \delta$.
        obtain ⟨n, hn⟩ : ∃ n : ℕ, ENNReal.ofReal (r ^ n) < δ := by
          -- Since $r^n \to 0$ as $n \to \infty$, we can choose $n$ such that $r^n < \delta$.
          have h_lim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (r ^ n)) Filter.atTop (nhds 0) := by
            simpa using ENNReal.tendsto_ofReal ( tendsto_pow_atTop_nhds_zero_of_lt_one hr.1.le ( by linarith ) );
          exact ( h_lim.eventually ( gt_mem_nhds hδ ) ) |> fun h => h.exists;
        obtain ⟨ U, hU₁, hU₂ ⟩ := h_cover n;
        refine le_trans ( iInf_le _ ( fun i => if hi : i < 2 ^ n then U ⟨ i, hi ⟩ else ∅ ) ) ?_;
        refine le_trans ( iInf_le _ ?_ ) ?_;
        · intro x hx; specialize hU₂ hx; aesop;
        · refine le_trans ( iInf_le _ ?_ ) ?_;
          · intro i; by_cases hi : i < 2 ^ n <;> simp +decide [ hi ]
            exact le_trans ( hU₁ _ ) hn.le;
          · rw [ tsum_eq_sum ];
            any_goals exact Finset.range ( 2 ^ n );
            · refine le_trans
                ( Finset.sum_le_sum
                    ( g := fun _ : ℕ => ENNReal.ofReal ( r ^ n ) ^ s )
                    fun i hi => ?_ ) ?_;
              · by_cases hi' : i < 2 ^ n <;> simp_all +decide
                exact fun _ => ENNReal.rpow_le_rpow ( hU₁ _ ) ( by exact div_nonneg ( Real.log_nonneg ( by norm_num ) ) ( neg_nonneg.mpr ( Real.log_nonpos ( by linarith ) ( by norm_num at *; linarith ) ) ) );
              · simp_all +decide
            · simp +contextual [ Finset.mem_range ];
              intro b hb; split_ifs <;> simp_all +decide [ not_lt_of_ge hb ] ;
              linarith;
      contrapose! h_Hausdorff_le_one;
      -- Since $dimH(C(r)) > s$, we have $H^s(C(r)) = \infty$.
      have h_Hausdorff_infinite : MeasureTheory.Measure.hausdorffMeasure s (C r) = ⊤ := by
        contrapose! h_Hausdorff_le_one;
        rw [ dimH ];
        refine iSup_le fun d => iSup_le fun hd => ?_;
        refine le_of_not_gt fun h => hd.not_lt <| lt_of_le_of_lt
          ( MeasureTheory.Measure.hausdorffMeasure_mono
            ( show s ≤ ( d : ℝ ) from ?_ ) ( C r ) ) ?_;
        · rw [ ENNReal.ofReal_lt_iff_lt_toReal ] at h <;> norm_num at * ; linarith [ show 0 < s by exact div_pos ( Real.log_pos one_lt_two ) ( neg_pos.mpr ( Real.log_neg hr.1 ( by linarith ) ) ) ] ;
          exact div_nonneg ( Real.log_nonneg ( by norm_num ) ) ( neg_nonneg.mpr ( Real.log_nonpos hr.1.le ( by linarith ) ) );
        · exact lt_top_iff_ne_top.mpr h_Hausdorff_le_one;
      aesop

/-
The measure of a level-n interval is 2^-n.
-/
lemma mu_I_word (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (u : List (Fin 2)) :
    mu r (I_word u r) = (1 / 2 : ENNReal) ^ u.length := by
      have hI_meas : MeasurableSet (I_word u r) := by
        rw [prop_symbolic_1_interval r hr u]
        exact measurableSet_Icc
      rw [mu, MeasureTheory.Measure.map_apply_of_aemeasurable] <;>
        norm_num [continuous_pi' r hr |> Continuous.aemeasurable, hI_meas]
      · -- The preimage of $I_u$ under $\pi_r$ is the set of sequences $\omega$ such that $\pi_r(\omega) \in I_u$.
        have h_preimage : pi r ⁻¹' I_word u r = {ω : ℕ → Fin 2 | take_word u.length ω = u} := by
          ext ω;
          constructor;
          · intro hω
            have h_unique : ∀ v ∈ Sigma_n u.length, pi r ω ∈ I_word v r → v = u := by
              intros v hv hvω
              have h_unique : pi r ω ∈ I_word v r ∧ pi r ω ∈ I_word u r := by
                aesop;
              have h_unique : Disjoint (I_word v r) (I_word u r) ∨ v = u := by
                exact Classical.or_iff_not_imp_right.2 fun h => disjoint_I_word r hr u.length v u hv ( by aesop ) h;
              exact h_unique.resolve_left ( Set.not_disjoint_iff.mpr ⟨ _, hvω, by tauto ⟩ );
            apply h_unique;
            · unfold take_word Sigma_n; aesop;
            · apply pi_mem_I_word r hr ω u.length;
          · intro hω;
            convert pi_mem_I_word r hr ω u.length using 1;
            aesop;
        -- The measure of the set of sequences where the first n elements are exactly u is the product of the measures of each element. Since each element is independent and has measure 1 / 2, the product is (1 / 2)^n.
        have h_measure : infiniteBernoulliMeasure {ω : ℕ → Fin 2 | ∀ i : Fin u.length, ω i = u[i]!} = (1 / 2 : ENNReal) ^ u.length := by
          have h_cyl :
              infiniteBernoulliMeasure {ω : ℕ → Fin 2 | ∀ i : Fin u.length, ω i = u[i]!}
                = ∏ i ∈ Finset.range u.length, bernoulliMeasure {u[i]!} := by
            rw [infiniteBernoulliMeasure]
            rw [show {ω : ℕ → Fin 2 | ∀ i : Fin u.length, ω i = u[i]!}
                = (↑(Finset.range u.length) : Set ℕ).pi (fun i => {u[i]!}) by
              ext ω
              simp
              exact ⟨fun h i hi => by simpa [List.getElem?_eq_getElem hi] using h ⟨i, hi⟩,
                fun h i => by simpa [List.getElem?_eq_getElem i.2] using h i i.2⟩]
            exact MeasureTheory.Measure.infinitePi_pi (fun _ : ℕ => bernoulliMeasure)
              (fun i _ => MeasurableSingletonClass.measurableSet_singleton (u[i]!))
          calc
            infiniteBernoulliMeasure {ω : ℕ → Fin 2 | ∀ i : Fin u.length, ω i = u[i]!}
                = ∏ i ∈ Finset.range u.length, bernoulliMeasure {u[i]!} := h_cyl
            _ = ∏ i ∈ Finset.range u.length, (2⁻¹ : ENNReal) := by
                  apply Finset.prod_congr rfl
                  intro i hi
                  rcases u[i]! with ⟨j, hj⟩
                  interval_cases j <;> norm_num [bernoulliMeasure, Pi.single]
            _ = (1 / 2 : ENNReal) ^ u.length := by
                  simp [one_div]
        rw [h_preimage]
        calc
          infiniteBernoulliMeasure {ω : ℕ → Fin 2 | take_word u.length ω = u}
              = infiniteBernoulliMeasure {ω : ℕ → Fin 2 | ∀ i : Fin u.length, ω i = u[i]!} := by
                congr with ω
                constructor
                · intro h i
                  have hfun :
                      (fun i : Fin u.length => ω i) = (fun i : Fin u.length => (u[i.1] : Fin 2)) := by
                    apply List.ofFn_injective
                    simpa [take_word, List.ofFn_getElem] using h
                  simpa [List.getElem?_eq_getElem i.2] using congrFun hfun i
                · intro h
                  apply List.ext_getElem
                  · simp [take_word]
                  · intro n hn₁ hn₂
                    simpa [take_word, List.getElem_ofFn, List.getElem?_eq_getElem hn₂]
                      using h ⟨n, by simpa [take_word] using hn₁⟩
          _ = 2⁻¹ ^ u.length := by
                simpa [one_div] using h_measure

/-
The distance between disjoint level-n intervals is at least (1-2r)r^(n-1).
-/
lemma dist_I_word_ge (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (n : ℕ)
    (u v : List (Fin 2)) (hu : u ∈ Sigma_n n) (hv : v ∈ Sigma_n n) (hdiff : u ≠ v) :
    ∀ x ∈ I_word u r, ∀ y ∈ I_word v r, |x - y| ≥ (1 - 2 * r) * r ^ (n - 1) := by
      -- Let k be the first index where u and v differ. Since u ≠ v, k < n.
      obtain ⟨k, hk⟩ : ∃ k < n, u[k]! ≠ v[k]! ∧ ∀ j < k, u[j]! = v[j]! := by
        obtain ⟨k, hk⟩ : ∃ k, k < n ∧ u[k]! ≠ v[k]! := by
          by_contra! h; simp_all +decide [ Sigma_n ] ;
          exact hdiff ( List.ext_get ( by aesop ) ( by aesop ) );
        exact ⟨ Nat.find ( ⟨ k, hk.1, hk.2 ⟩ : ∃ k < n, u[k]! ≠ v[k]! ), Nat.find_spec ( ⟨ k, hk.1, hk.2 ⟩ : ∃ k < n, u[k]! ≠ v[k]! ) |>.1, Nat.find_spec ( ⟨ k, hk.1, hk.2 ⟩ : ∃ k < n, u[k]! ≠ v[k]! ) |>.2, fun j hj => Classical.not_not.1 fun h => Nat.find_min ( ⟨ k, hk.1, hk.2 ⟩ : ∃ k < n, u[k]! ≠ v[k]! ) hj ⟨ by linarith [ Nat.find_spec ( ⟨ k, hk.1, hk.2 ⟩ : ∃ k < n, u[k]! ≠ v[k]! ) |>.1 ], h ⟩ ⟩;
      -- Assume without loss of generality u[k] = 0 and v[k] = 1.
      wlog h_wlog : u[k]! = 0 ∧ v[k]! = 1 generalizing u v k;
      · specialize this v u hv hu hdiff.symm k ; simp_all +decide
        cases Fin.exists_fin_two.mp ⟨ u[k]?.getD 0, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ v[k]?.getD 0, rfl ⟩ <;> simp_all +decide
        exact fun x hx y hy => by simpa only [ abs_sub_comm ] using this y hy x hx;
      · -- Since $u$ and $v$ differ at position $k$, we have $I_u \subseteq I_{w0}$ and $I_v \subseteq I_{w1}$ for some word $w$ of length $k$.
        obtain ⟨w, hw⟩ : ∃ w : List (Fin 2), u = w ++ [0] ++ u.drop (k + 1) ∧ v = w ++ [1] ++ v.drop (k + 1) := by
          have h_split : u = u.take k ++ [u[k]!] ++ u.drop (k + 1) ∧ v = v.take k ++ [v[k]!] ++ v.drop (k + 1) := by
            have h_split : ∀ (l : List (Fin 2)) (k : ℕ), k < l.length → l = l.take k ++ [l[k]!] ++ l.drop (k + 1) := by
              intros l k hk
              induction l generalizing k with
              | nil =>
                aesop
              | cons hd tl ih =>
                aesop
            exact ⟨ h_split u k ( by linarith [ hu.symm ] ), h_split v k ( by linarith [ hv.symm ] ) ⟩;
          have h_take_eq : List.take k u = List.take k v := by
            refine List.ext_get ?_ ?_ <;> simp +decide
            · rw [ hu, hv ];
            · intro n hn hn' hn'' hn'''; specialize hk; have := hk.2.2 n hn; simp +decide [ hn', hn''' ] at this ⊢; tauto;
          grind +ring;
        -- Since $I_u \subseteq I_{w0}$ and $I_v \subseteq I_{w1}$, we have $|x - y| \geq (1 - 2r) * r^k$ for any $x \in I_u$ and $y \in I_v$.
        have h_dist : ∀ x ∈ I_word (w ++ [0]) r, ∀ y ∈ I_word (w ++ [1]) r, |x - y| ≥ (1 - 2 * r) * r ^ (w.length) := by
          intros x hx y hy
          norm_num [ Finset.sum_range_succ, pow_succ' ] at *;
          cases abs_cases ( x - y )
          · obtain ⟨ a, ha, rfl ⟩ := hx; obtain ⟨ b, hb, rfl ⟩ := hy; norm_num [ prop_symbolic_1 ] at *;
            norm_num [ Finset.sum_range_succ, pow_succ' ] at *;
            rw [ abs_of_nonneg ] <;> norm_num [ Finset.sum_range, List.getElem?_append ] at *;
            · nlinarith [ show 0 < r ^ w.length by exact pow_pos hr.1 _, show 0 < r ^ w.length * r by exact mul_pos ( pow_pos hr.1 _ ) hr.1 ];
            · linarith
          · rw [ prop_symbolic_1_interval ] at hx hy <;> norm_num at *;
            · norm_num [ Finset.sum_range_succ, List.getElem?_append ] at *;
              norm_num [ pow_succ, mul_assoc, mul_comm, mul_left_comm, Finset.sum_range, List.getElem?_append ] at *;
              nlinarith [ pow_pos hr.1 w.length ];
            · tauto;
            · tauto
        -- Since $u = w ++ [0] ++ u.drop (k + 1)$ and $v = w ++ [1] ++ v.drop (k + 1)$, we have $I_u \subseteq I_{w0}$ and $I_v \subseteq I_{w1}$.
        have h_subset : I_word u r ⊆ I_word (w ++ [0]) r ∧ I_word v r ⊆ I_word (w ++ [1]) r := by
          have h_subset : ∀ (u v : List (Fin 2)), I_word (u ++ v) r ⊆ I_word u r := by
            intros u v; exact (by
            induction v using List.reverseRecOn with
            | nil =>
              simp +decide [ I_word ];
            | append_singleton v x ih =>
              convert Set.Subset.trans ( I_word_subset_of_append r hr ( u ++ v ) x ) ih using 1;
              simp +decide [ List.append_assoc ]);
          exact ⟨ hw.1 ▸ h_subset _ _, hw.2 ▸ h_subset _ _ ⟩;
        -- Since $w.length = k$, we have $r^w.length = r^k$.
        have h_w_length : w.length = k := by
          have := congr_arg List.length hw.1; norm_num at this;
          linarith [ Nat.sub_add_cancel ( show k + 1 ≤ u.length from by linarith [ show u.length = n from hu ] ), show u.length = n from hu ];
        intro x hx y hy; specialize h_dist x ( h_subset.1 hx ) y ( h_subset.2 hy ) ; rw [ h_w_length ] at h_dist; exact le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_of_le_one ( by linarith ) ( by linarith ) ( Nat.le_sub_one_of_lt hk.1 ) ) ( by linarith ) ) h_dist;

/-
If a set has small diameter, its measure is bounded by 2^-n.
-/
lemma measure_le_two_pow_neg_n_of_diam_le (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (U : Set ℝ) (n : ℕ) (hn : 1 ≤ n)
    (h_diam : Metric.ediam U < ENNReal.ofReal ((1 - 2 * r) * r ^ (n - 1))) :
    mu r U ≤ (1 / 2 : ENNReal) ^ n := by
      classical
      -- By definition of $C_n$, $U$ can intersect at most one interval $I_u$ at level $n$.
      have h_inter : ∀ u v : List (Fin 2), u ∈ Sigma_n n → v ∈ Sigma_n n → u ≠ v → Disjoint U (I_word u r) ∨ Disjoint U (I_word v r) := by
        intros u v hu hv huv
        by_contra h_non_disjoint
        push Not at h_non_disjoint
        obtain ⟨x, hx⟩ : ∃ x, x ∈ U ∧ x ∈ I_word u r ∧ ∃ y, y ∈ U ∧ y ∈ I_word v r := by
          exact ⟨ _, Set.not_disjoint_iff.mp h_non_disjoint.1 |> Classical.choose_spec |> And.left, Set.not_disjoint_iff.mp h_non_disjoint.1 |> Classical.choose_spec |> And.right, _, Set.not_disjoint_iff.mp h_non_disjoint.2 |> Classical.choose_spec |> And.left, Set.not_disjoint_iff.mp h_non_disjoint.2 |> Classical.choose_spec |> And.right ⟩;
        obtain ⟨ y, hy₁, hy₂ ⟩ := hx.2.2; have := dist_I_word_ge r hr n u v hu hv huv x hx.2.1 y hy₂; simp_all +decide
        have := h_diam.trans_le' ( Metric.edist_le_ediam_of_mem hx.1 hy₁ ) ; norm_num at *;
        exact this.not_ge ( by simpa only [ Real.dist_eq ] using ‹ ( 1 - 2 * r ) * r ^ ( n - 1 ) ≤ |x - y| › );
      -- Since $U$ can intersect at most one interval $I_u$ at level $n$, we have $\mu(U) \leq \mu(I_u)$ for some $u \in \Sigma_n$.
      obtain ⟨u, hu⟩ : ∃ u ∈ Sigma_n n, U ∩ I_word u r ≠ ∅ ∨ ∀ v ∈ Sigma_n n, U ∩ I_word v r = ∅ := by
        by_cases h : ∃ u ∈ Sigma_n n, U ∩ I_word u r ≠ ∅;
        · exact ⟨ h.choose, h.choose_spec.1, Or.inl h.choose_spec.2 ⟩;
        · simp +zetaDelta at *;
          exact ⟨ List.replicate n 0, by unfold Sigma_n; aesop, Or.inr h ⟩;
      have h_mu_le : (mu r) U ≤ (mu r) (I_word u r) + (mu r) (⋃ v ∈ Sigma_n n, I_word v r)ᶜ := by
        refine le_trans
          ( MeasureTheory.measure_mono
            ( show U ⊆ I_word u r ∪ ( ⋃ v ∈ Sigma_n n, I_word v r )ᶜ from ?_ ) )
          ( MeasureTheory.measure_union_le
            ( μ := mu r ) ( I_word u r ) ( ( ⋃ v ∈ Sigma_n n, I_word v r )ᶜ ) );
        intro x hx; by_cases hx' : x ∈ ⋃ v ∈ Sigma_n n, I_word v r <;> simp_all +decide [ Set.ext_iff ] ;
        rcases hu.2 with h|h <;> simp_all +decide [ Set.disjoint_left ];
        grind;
      have h_mu_compl : (mu r) (⋃ v ∈ Sigma_n n, I_word v r)ᶜ = 0 := by
        rw [ MeasureTheory.measure_compl ] <;> norm_num;
        · rw [ show ( mu r ) Set.univ = 1 from ?_, show ( mu r ) ( ⋃ v ∈ Sigma_n n, I_word v r ) = 1 from ?_ ] <;> norm_num;
          · have h_mu_union : (mu r) (⋃ v ∈ Sigma_n n, I_word v r) = ∑ v ∈ Finset.filter (fun v => v ∈ Sigma_n n) (Finset.image (fun v : Fin n → Fin 2 => List.ofFn v) (Finset.univ : Finset (Fin n → Fin 2))), (mu r) (I_word v r) := by
              rw [ ← MeasureTheory.measure_biUnion_finset ];
              · congr with x ; simp +decide [ Sigma_n ];
                exact fun _ _ => ⟨ fun i => x[i]!, by rw [ List.ofFn_eq_map ] ; exact List.ext_get ( by aesop ) ( by aesop ) ⟩;
              · intros v hv w hw hvw; exact (by
                apply disjoint_I_word r hr n v w; aesop;
                · aesop;
                · assumption);
              · intro v hv; exact (by
                apply_rules [ IsCompact.measurableSet, CompactIccSpace.isCompact_Icc ];
                have h_compact : IsCompact (Set.Icc ((1 - r) * ∑ k ∈ Finset.range v.length, ((v[k]?).getD 0 : ℝ) * r ^ k) ((1 - r) * (∑ k ∈ Finset.range v.length, ((v[k]?).getD 0 : ℝ) * r ^ k) + r ^ v.length)) := by
                  exact CompactIccSpace.isCompact_Icc;
                convert h_compact using 1;
                exact prop_symbolic_1_interval r hr v);
            rw [ h_mu_union, Finset.sum_congr rfl fun x hx => mu_I_word r hr x ];
            rw [ Finset.filter_true_of_mem ] <;> norm_num [ Sigma_n ];
            rw [Finset.sum_image]
            · simp [List.length_ofFn, ← mul_pow, ENNReal.mul_inv_cancel]
            · intro a _ b _ h
              exact List.ofFn_injective h
          · unfold mu;
            rw [ MeasureTheory.Measure.map_apply_of_aemeasurable ] <;> norm_num;
            exact Continuous.aemeasurable ( continuous_pi' r hr );
        · refine MeasurableSet.iUnion fun v => MeasurableSet.iUnion fun hv => ?_;
          rw [ prop_symbolic_1_interval r hr v ] ; exact measurableSet_Icc;
        · refine ne_of_lt ( lt_of_le_of_lt
            ( MeasureTheory.measure_mono
              ( show ( ⋃ v ∈ Sigma_n n, I_word v r ) ⊆ Set.univ from Set.subset_univ _ ) ) ?_ ) ;
          norm_num [ mu ];
      convert h_mu_le using 1 ; rw [ h_mu_compl ] ; norm_num [ mu_I_word r hr u, hu.1.symm ]

/-
Algebraic bound for the measure estimate.
-/
lemma algebraic_bound (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (d : ℝ) (hd_pos : 0 < d) (n : ℕ)
    (h_lower : (1 - 2 * r) * r ^ n ≤ d) :
    let s := Real.log 2 / -Real.log r
    let a := 1 - 2 * r
    let C := a ^ (-s)
    (1 / 2 : ℝ) ^ n ≤ C * d ^ s := by
      -- From h_lower, we have a * r^n ≤ d, so r^n ≤ d/a.
      have h_r_pow_le_d_div_a : r^n ≤ d / (1 - 2 * r) := by
        rwa [ le_div_iff₀' ( by linarith ) ];
      -- From h_r_pow_le_d_div_a, we have r^n ≤ d/a, so (r^n)^s ≤ (d/a)^s.
      have h_r_pow_s_le_d_div_a_pow_s : (r^n)^((Real.log 2) / (-Real.log r)) ≤ (d / (1 - 2 * r))^((Real.log 2) / (-Real.log r)) := by
        exact Real.rpow_le_rpow ( pow_nonneg hr.1.le _ ) h_r_pow_le_d_div_a ( div_nonneg ( Real.log_nonneg ( by norm_num ) ) ( neg_nonneg.mpr ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ) );
      convert h_r_pow_s_le_d_div_a_pow_s using 1 ; ring_nf;
      · rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ] <;> norm_num [ hr.1 ];
        rw [ Real.rpow_def_of_pos ( pow_pos hr.1 _ ) ] ; norm_num ; ring_nf;
        norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_lt ( Real.log_neg hr.1 ( by linarith ) ) ];
        norm_num [ Real.log_div ];
      · rw [ Real.div_rpow ( by linarith ) ( by linarith ), Real.rpow_neg ( by linarith ) ] ; ring

/-
Bound for the measure of small sets.
-/
lemma mu_bound_specific (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    let s := Real.log 2 / -Real.log r
    let a := 1 - 2 * r
    let C := a ^ (-s)
    let δ₀ := a
    ∀ U : Set ℝ, 0 < Metric.ediam U → Metric.ediam U ≤ ENNReal.ofReal δ₀ →
    mu r U ≤ ENNReal.ofReal C * (Metric.ediam U) ^ s := by
      intros s a C δ₀ U hU_pos hU_le_δ₀
      by_cases hU_diam : Metric.ediam U < ENNReal.ofReal δ₀;
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 ≤ n ∧ Metric.ediam U < ENNReal.ofReal ((1 - 2 * r) * r ^ (n - 1)) ∧ Metric.ediam U ≥ ENNReal.ofReal ((1 - 2 * r) * r ^ n) := by
          -- Since $Metric.ediam U < ENNReal.ofReal δ₀$, we can find $n$ such that $(1 - 2 * r) * r ^ n ≤ Metric.ediam U < (1 - 2 * r) * r ^ (n - 1)$.
          obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 - 2 * r) * r ^ n ≤ ENNReal.toReal (Metric.ediam U) ∧ ENNReal.toReal (Metric.ediam U) < (1 - 2 * r) * r ^ (n - 1) := by
            have h_seq : ∃ n : ℕ, (1 - 2 * r) * r ^ n ≤ ENNReal.toReal (Metric.ediam U) ∧ ∀ m < n, (1 - 2 * r) * r ^ m > ENNReal.toReal (Metric.ediam U) := by
              have h_seq : ∃ n : ℕ, (1 - 2 * r) * r ^ n ≤ ENNReal.toReal (Metric.ediam U) := by
                have h_seq : Filter.Tendsto (fun n => (1 - 2 * r) * r ^ n) Filter.atTop (nhds 0) := by
                  exact MulZeroClass.mul_zero ( 1 - 2 * r ) ▸ tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one hr.1.le ( by linarith ) );
                exact ( h_seq.eventually ( ge_mem_nhds <| ENNReal.toReal_pos hU_pos.ne' <| by aesop ) ) |> fun h => h.exists;
              exact ⟨ Nat.find h_seq, Nat.find_spec h_seq, fun m mn => not_le.1 fun contra => Nat.find_min h_seq mn contra ⟩;
            obtain ⟨ n, hn₁, hn₂ ⟩ := h_seq;
            by_cases hn : n = 0;
            · use 0;
              rw [ ENNReal.lt_ofReal_iff_toReal_lt ] at * <;> aesop;
            · exact ⟨ n, hn₁, hn₂ _ ( Nat.pred_lt hn ) ⟩;
          refine ⟨ n, ?_, ?_, ?_ ⟩ <;> norm_num at *;
          · contrapose! hn; aesop;
          · rw [ ENNReal.lt_ofReal_iff_toReal_lt ] <;> aesop;
          · rw [ ENNReal.ofReal_le_iff_le_toReal ] <;> aesop;
        have h_measure_le : mu r U ≤ (1 / 2 : ENNReal) ^ n := by
          convert measure_le_two_pow_neg_n_of_diam_le r hr U n hn.1 hn.2.1 using 1;
        have h_algebraic_bound : (1 / 2 : ℝ) ^ n ≤ C * (Metric.ediam U).toReal ^ s := by
          convert algebraic_bound r hr ( Metric.ediam U |> ENNReal.toReal ) ?_ n ?_ using 1 <;> norm_num at *;
          · exact ENNReal.toReal_pos hU_pos.ne' ( by aesop );
          · rw [ ← ENNReal.toReal_ofReal ( show 0 ≤ ( 1 - 2 * r ) * r ^ n by exact mul_nonneg ( by linarith ) ( pow_nonneg hr.1.le _ ) ) ] ; exact ENNReal.toReal_mono ( by aesop ) hn.2.2;
        convert h_measure_le.trans _;
        rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
        · convert h_algebraic_bound using 1;
          rw [ ENNReal.toReal_ofReal ( Real.rpow_nonneg ( sub_nonneg.2 <| by linarith ) _ ), ENNReal.toReal_rpow ];
        · refine ENNReal.mul_ne_top ?_ ?_ <;> norm_num;
          exact ⟨ fun h => False.elim <| hU_pos.ne' h, fun h => False.elim <| h.not_lt <| lt_of_le_of_lt hU_le_δ₀ <| ENNReal.ofReal_lt_top ⟩;
      · cases eq_or_lt_of_le hU_le_δ₀ <;> simp_all +decide
        refine le_trans ( MeasureTheory.measure_mono ( show U ⊆ Set.univ from Set.subset_univ U ) ) ?_;
        erw [ MeasureTheory.Measure.map_apply ] <;> norm_num [ infiniteBernoulliMeasure ];
        · rw [ ← ENNReal.ofReal_rpow_of_pos ];
          · rw [ ← ENNReal.rpow_add ] <;> norm_num [ hU_pos ];
            exact hU_pos;
          · exact hU_pos;
        · exact Continuous.measurable ( continuous_pi' r ⟨ by linarith, by norm_num at *; linarith ⟩ )

/-
The Cantor set C r is closed.
-/
theorem isClosed_C (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) : IsClosed (C r) := by
  refine isClosed_iInter ?_;
  intro n
  unfold C_n;
  -- Since $\Sigma_n$ is finite, the union $\bigcup_{u \in \Sigma_n} I_u$ is a finite union of closed intervals, hence closed.
  have h_finite : Set.Finite (Sigma_n n) := by
    exact finite_Sigma_n n;
  refine h_finite.isClosed_biUnion fun u hu => ?_;
  rw [ prop_symbolic_1_interval r hr u ] ; exact isClosed_Icc;

/-
Lower bound for the Hausdorff dimension of the Cantor set.
-/
lemma dimH_C_ge_s (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    dimH (C r) ≥ ENNReal.ofReal (Real.log 2 / -Real.log r) := by
      have := @mass_distribution_principle ( C r ) ( mu r ) ?_;
      · contrapose! this;
        refine ⟨ ?_, Real.log 2 / -Real.log r, div_nonneg ( Real.log_nonneg ( by norm_num ) ) ( neg_nonneg.mpr ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ), ( 1 - 2 * r ) ^ ( - ( Real.log 2 / -Real.log r ) ), Real.rpow_pos_of_pos ( by linarith ) ( - ( Real.log 2 / -Real.log r ) ), 1 - 2 * r, by linarith, ?_, ?_ ⟩;
        · -- By definition of $C_r$, we know that $C_r$ is the image of the projection map $\pi_r$.
          have h_image : C r = Set.range (pi r) := by
            refine Set.Subset.antisymm ?_ ?_;
            · intro x hx
              obtain ⟨ω, hω⟩ : ∃ ω : ℕ → Fin 2, pi r ω = x := by
                exact ⟨ code_of_mem_C r hr x hx, pi_code_of_mem_C r hr x hx ⟩
              use ω;
            · exact range_pi_subset_C' r hr;
          unfold mu;
          rw [ MeasureTheory.measure_compl ] <;> norm_num [ h_image ];
          · rw [ MeasureTheory.Measure.map_apply_of_aemeasurable ] <;> norm_num [ continuous_pi' r hr |> Continuous.aemeasurable ];
            rw [ MeasureTheory.Measure.map_apply_of_aemeasurable ] <;> norm_num [ continuous_pi' r hr |> Continuous.aemeasurable ];
            exact h_image ▸ isClosed_C r hr |> IsClosed.measurableSet;
          · exact h_image ▸ isClosed_C r hr |> IsClosed.measurableSet;
        · convert mu_bound_specific r hr using 1;
        · aesop;
      · exact instIsProbabilityMeasureRealMuOfAndLtOfNatHDiv r hr

/-
Upper bound on the covering number of the Cantor set.
-/
lemma N_delta_le (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (n : ℕ) :
    N_delta (C r) (r ^ n) ≤ 2 ^ n := by
      refine csInf_le ?_ ?_;
      · exact ⟨ 0, fun x hx => Nat.zero_le _ ⟩;
      · -- Let $U_i$ be the interval $I_{u_i}(r)$ for each $u_i \in \Sigma_n n$.
        obtain ⟨u, hu⟩ : ∃ u : Fin (2 ^ n) → List (Fin 2), (∀ i, u i ∈ Sigma_n n) ∧ (∀ u' ∈ Sigma_n n, ∃ i, u' = u i) := by
          have h_finite : Set.Finite (Sigma_n n) := by
            exact finite_Sigma_n n;
          have h_card : Set.ncard (Sigma_n n) = 2 ^ n := by
            rw [ show Sigma_n n = Finset.image ( fun u : Fin n → Fin 2 => List.ofFn u ) ( Finset.univ : Finset ( Fin n → Fin 2 ) ) from ?_, Set.ncard_eq_toFinset_card' ] ; norm_num [ Finset.card_image_of_injective, Function.Injective ];
            ext; simp [Sigma_n];
            exact ⟨ fun h => ⟨ fun i => ‹List ( Fin 2 ) ›[i]!, by rw [ List.ofFn_eq_map ] ; exact List.ext_get ( by aesop ) ( by aesop ) ⟩, by rintro ⟨ y, rfl ⟩ ; simp +decide ⟩;
          have h_equiv : Nonempty (Fin (2 ^ n) ≃ Sigma_n n) := by
            have := h_finite.fintype; exact ⟨ Fintype.equivOfCardEq <| by simpa [ Set.ncard_eq_toFinset_card' ] using h_card.symm ⟩ ;
          exact ⟨ fun i => h_equiv.some i |>.1, fun i => h_equiv.some i |>.2, fun u' hu' => ⟨ h_equiv.some.symm ⟨ u', hu' ⟩, by simp +decide ⟩ ⟩;
        refine ⟨ fun i => I_word ( u i ) r, ?_, ?_ ⟩;
        · intro i
          have h_interval : I_word (u i) r = Set.Icc ((1 - r) * ∑ k ∈ Finset.range (u i).length, ((u i)[k]?).getD 0 * r ^ k) ((1 - r) * (∑ k ∈ Finset.range (u i).length, ((u i)[k]?).getD 0 * r ^ k) + r ^ (u i).length) := by
            exact prop_symbolic_1_interval r hr _;
          simp_all +decide [ Sigma_n ];
        · intro x hx;
          obtain ⟨ u', hu', hx' ⟩ := exists_word_of_mem_C r x hx n;
          obtain ⟨ i, rfl ⟩ := hu.2 u' hu'; exact Set.mem_iUnion.2 ⟨ i, hx' ⟩ ;

/-
The Hausdorff dimension of the middle-a Cantor set is s = log 2 / -log r.
-/
theorem dimH_C_eq_s (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    dimH (C r) = ENNReal.ofReal (Real.log 2 / -Real.log r) := by
      convert le_antisymm ?_ ?_ using 1;
      exact ENNReal.instPartialOrder;
      · exact dimH_C_le_s r hr;
      · exact dimH_C_ge_s r hr

/-
For a bounded set E, the covering number N_delta is non-increasing for positive delta.
-/
lemma N_delta_antitone_on_pos (E : Set ℝ) :
    AntitoneOn (N_delta E) (Set.Ioi 0) := by
      intro δ₁ hδ₁ δ₂ hδ₂ hδ_le
      unfold N_delta
      have hδ₁pos : 0 < δ₁ := hδ₁
      let A₁ : Set ℕ := { n | ∃ U : Fin n → Set ℝ,
        (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ₁) ∧ E ⊆ ⋃ i, U i }
      let A₂ : Set ℕ := { n | ∃ U : Fin n → Set ℝ,
        (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ₂) ∧ E ⊆ ⋃ i, U i }
      change sInf A₂ ≤ sInf A₁
      have cover_bounded :
          ∀ {δ n} {U : Fin n → Set ℝ},
            (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ) → E ⊆ ⋃ i, U i →
              Bornology.IsBounded E := by
        intro δ n U hU hcover
        refine Bornology.IsBounded.subset ?_ hcover
        rw [Bornology.isBounded_iUnion]
        intro i
        rw [isBounded_iff_ediam_ne_top]
        exact ne_of_lt (lt_of_le_of_lt (hU i) ENNReal.ofReal_lt_top)
      have bounded_cover :
          Bornology.IsBounded E → A₁.Nonempty := by
        intro hE
        obtain ⟨M, hM⟩ := hE.exists_pos_norm_le
        refine ⟨Nat.ceil (2 * M / δ₁) + 1, ?_⟩
        refine ⟨fun i => Set.Icc (-M + i.val * δ₁) (-M + (i.val + 1) * δ₁), ?_, ?_⟩
        · intro i
          refine Metric.ediam_le ?_
          intro y hy z hz
          rw [edist_dist]
          exact ENNReal.ofReal_le_ofReal (by
            rw [Real.dist_eq]
            exact abs_sub_le_iff.mpr ⟨by nlinarith [hy.1, hy.2, hz.1, hz.2, hδ₁pos.le],
              by nlinarith [hy.1, hy.2, hz.1, hz.2, hδ₁pos.le]⟩)
        · intro x hx
          have hxM := hM.2 x hx
          norm_num [abs_le] at hxM
          refine Set.mem_iUnion.2 ?_
          refine ⟨⟨⌊(M + x) / δ₁⌋₊, ?_⟩, ?_⟩
          · exact Nat.lt_succ_of_le (Nat.floor_le_of_le (by
              rw [div_le_iff₀ hδ₁pos]
              nlinarith [Nat.le_ceil (2 * M / δ₁), mul_div_cancel₀ (2 * M) hδ₁pos.ne']))
          · exact ⟨by
              nlinarith [Nat.floor_le (show 0 ≤ (M + x) / δ₁ by exact div_nonneg (by linarith) hδ₁pos.le),
                mul_div_cancel₀ (M + x) hδ₁pos.ne'],
              by
                nlinarith [Nat.lt_floor_add_one ((M + x) / δ₁),
                  mul_div_cancel₀ (M + x) hδ₁pos.ne']⟩
      by_cases hE : Bornology.IsBounded E
      · exact Nat.sInf_le (by
          rcases Nat.sInf_mem (bounded_cover hE) with ⟨U, hU, hcover⟩
          exact ⟨U, fun i => le_trans (hU i) (ENNReal.ofReal_le_ofReal hδ_le), hcover⟩)
      · have hA₁ : A₁ = ∅ := by
          ext n
          constructor
          · rintro ⟨U, hU, hcover⟩
            exact (hE (cover_bounded hU hcover)).elim
          · simp
        have hA₂ : A₂ = ∅ := by
          ext n
          constructor
          · rintro ⟨U, hU, hcover⟩
            exact (hE (cover_bounded hU hcover)).elim
          · simp
        simp [hA₁, hA₂]

/-
The upper box dimension of C_r is at most s.
-/
theorem upper_box_dim_le_s (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    upper_box_dim (C r) ≤ Real.log 2 / -Real.log r := by
      -- Using the upper bound on the covering number, we get
      have h_upper_bound : ∀ δ > 0, δ < 1 → Real.log (N_delta (C r) δ) / -Real.log δ ≤ (Real.log 2 / -Real.log r) + (Real.log 2 / -Real.log δ) := by
        intros δ hδ_pos hδ_lt_1
        have h_covering_bound : N_delta (C r) δ ≤ 2 ^ (Nat.floor (-Real.log δ / -Real.log r) + 1) := by
          refine le_trans ?_ ( N_delta_le r hr ( ⌊-Real.log δ / -Real.log r⌋₊ + 1 ) );
          apply_rules [ N_delta_antitone_on_pos ] ; aesop;
          have := Nat.lt_floor_add_one ( -Real.log δ / -Real.log r );
          rw [ div_lt_iff₀ ] at this <;> norm_num at *;
          · rw [ ← Real.log_le_log_iff ( pow_pos hr.1 _ ) hδ_pos, Real.log_pow ] ; norm_num ; linarith;
          · exact Real.log_neg hr.1 ( by linarith );
        -- Taking the logarithm of both sides of the inequality $N_\delta(C_r) \leq 2^{n+1}$, we get $\log(N_\delta(C_r)) \leq (n+1) \log(2)$.
        have h_log_covering_bound : Real.log (N_delta (C r) δ) ≤ (Nat.floor (-Real.log δ / -Real.log r) + 1) * Real.log 2 := by
          by_cases h : N_delta ( C r ) δ = 0 <;> simp_all +decide
          · positivity;
          · simpa using Real.log_le_log ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero h ) ( Nat.cast_le.mpr h_covering_bound );
        field_simp;
        rw [ neg_div', div_le_iff_of_neg ];
        · ring_nf at *;
          nlinarith [ Nat.floor_le ( show 0 ≤ ( Real.log r ) ⁻¹ * Real.log δ by exact mul_nonneg_of_nonpos_of_nonpos ( inv_nonpos.mpr ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ) ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ), Nat.lt_floor_add_one ( ( Real.log r ) ⁻¹ * Real.log δ ), Real.log_pos one_lt_two, mul_inv_cancel₀ ( ne_of_lt ( Real.log_neg hδ_pos hδ_lt_1 ) ) ];
        · exact Real.log_neg hδ_pos hδ_lt_1;
      -- Taking the limit superior as δ approaches 0, we get
      have h_limsup : Filter.Tendsto (fun δ => Real.log 2 / -Real.log δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        exact tendsto_const_nhds.div_atTop ( Filter.tendsto_neg_atBot_atTop.comp ( Real.tendsto_log_nhdsNE_zero.mono_left <| nhdsWithin_mono _ <| by norm_num ) );
      -- Using the upper bound and the fact that the limit superior of a sum is the sum of the limit superiors, we get
      have h_limsup_sum : Filter.limsup (fun δ => Real.log (N_delta (C r) δ) / -Real.log δ) (nhdsWithin 0 (Set.Ioi 0)) ≤ Filter.limsup (fun δ => Real.log 2 / -Real.log r + Real.log 2 / -Real.log δ) (nhdsWithin 0 (Set.Ioi 0)) := by
        apply_rules [ Filter.limsup_le_limsup ];
        · filter_upwards [ Ioo_mem_nhdsGT zero_lt_one ] with δ hδ using h_upper_bound δ hδ.1 hδ.2;
        · refine ⟨ 0, ?_ ⟩ ; norm_num [ IsCoboundedUnder ];
          intro a ha; have := ha.and ( Ioo_mem_nhdsGT zero_lt_one ) ; obtain ⟨ δ, hδ₁, hδ₂ ⟩ := this.exists; exact le_trans ( div_nonneg ( Real.log_natCast_nonneg _ ) ( neg_nonneg.mpr ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ) ) hδ₁;
        · exact Filter.Tendsto.isBoundedUnder_le ( tendsto_const_nhds.add h_limsup );
      convert h_limsup_sum using 1;
      rw [ Filter.Tendsto.limsup_eq ( tendsto_const_nhds.add h_limsup ) ] ; norm_num

/-
For any small enough delta, we can sandwich it between consecutive powers of r scaled by C.
-/
lemma exists_n_sandwich (r : ℝ) (hr : 0 < r ∧ r < 1) (C : ℝ) (δ : ℝ) (hδ : 0 < δ) (hδ_le : δ ≤ C) :
    ∃ n : ℕ, n ≥ 1 ∧ C * r ^ n < δ ∧ δ ≤ C * r ^ (n - 1) := by
      -- By the Archimedean property, since $r^n \to 0$ as $n \to \infty$ (because $0 < r < 1$), there exists some $N$ such that $C * r^n < \delta$ for all $n \geq N$.
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, C * r ^ n < δ := by
        simpa using ( summable_geometric_of_lt_one hr.1.le hr.2 ).mul_left C |> fun h => h.tendsto_atTop_zero.eventually ( gt_mem_nhds hδ ) |> fun h => h.filter_mono <| Filter.tendsto_id;
      -- Let's choose the smallest such $n$.
      obtain ⟨n, hn1, hn2⟩ : ∃ n, C * r ^ n < δ ∧ ∀ m < n, C * r ^ m ≥ δ := by
        exact ⟨ Nat.find ( ⟨ N, hN N le_rfl ⟩ : ∃ n, C * r ^ n < δ ), Nat.find_spec ( ⟨ N, hN N le_rfl ⟩ : ∃ n, C * r ^ n < δ ), fun m mn => not_lt.1 fun contra => Nat.find_min ( ⟨ N, hN N le_rfl ⟩ : ∃ n, C * r ^ n < δ ) mn contra ⟩;
      refine ⟨ n, ?_, hn1, ?_ ⟩;
      · contrapose! hn1; aesop;
      · rcases n <;> aesop

/-
If delta is smaller than the smallest gap at level n, then the covering number is at least 2^n.
-/
lemma N_delta_ge_two_pow (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hδ_lt : δ < (1 - 2 * r) * r ^ (n - 1)) :
    N_delta (C r) δ ≥ 2 ^ n := by
      classical
      -- Let $U$ be a finite cover of $C_r$ with sets of diameter $\le \delta$.
      have h_cover : ∀ (U : Finset (Set ℝ)), (∀ i ∈ U, Metric.ediam i ≤ ENNReal.ofReal δ) → (C r ⊆ ⋃ i ∈ U, i) → U.card ≥ 2 ^ n := by
        intros U hU hU_cover
        have h_inter : ∀ u ∈ Sigma_n n, ∃ S ∈ U, ∃ x ∈ C r, x ∈ I_word u r ∧ x ∈ S := by
          intros u hu
          obtain ⟨x, hx⟩ : ∃ x ∈ C r, x ∈ I_word u r := by
            have h_inter : pi r (append_zeros u) ∈ C r := by
              exact range_pi_subset_C r hr |> Set.mem_of_mem_of_subset ( Set.mem_range_self _ );
            refine ⟨ pi r (append_zeros u), h_inter, ?_ ⟩;
            rw [ prop_symbolic_3_interval r hr u ] ; norm_num [ pi_append_zeros ];
            rw [ pi_append_ones ] ; norm_num [ hr ];
            · exact pow_nonneg hr.1.le _;
            · tauto;
          rcases Set.mem_iUnion₂.mp ( hU_cover hx.1 ) with ⟨ S, hS, hS' ⟩ ; exact ⟨ S, hS, x, hx.1, hx.2, hS' ⟩;
        choose! S hS x hx hx' hx'' using h_inter;
        have h_inj : ∀ u v : List (Fin 2), u ∈ Sigma_n n → v ∈ Sigma_n n → u ≠ v → S u ≠ S v := by
          intros u v hu hv huv h_eq
          have h_dist : |x u - x v| ≥ (1 - 2 * r) * r ^ (n - 1) := by
            apply dist_I_word_ge r hr n u v hu hv huv (x u) (hx' u hu) (x v) (hx' v hv);
          have h_dist_le : Metric.ediam (S u) ≥ ENNReal.ofReal (|x u - x v|) := by
            refine le_trans ?_ ( Metric.edist_le_ediam_of_mem ( hx'' u hu ) ( h_eq.symm ▸ hx'' v hv ) );
            simp +decide [ edist_dist ];
            rw [ Real.dist_eq ];
          exact h_dist_le.not_gt <| lt_of_le_of_lt ( hU _ <| hS _ hu ) <| ENNReal.ofReal_lt_ofReal_iff ( by linarith ) |>.2 <| by linarith;
        have h_card : Finset.card (Finset.image S (Finset.filter (fun u => u ∈ Sigma_n n) (Finset.image (fun u : Fin n → Fin 2 => List.ofFn u) (Finset.univ : Finset (Fin n → Fin 2))))) = 2 ^ n := by
          rw [ Finset.card_image_of_injOn ];
          · rw [ Finset.filter_true_of_mem ] <;> norm_num [ Sigma_n ];
            rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
          · exact fun u hu v hv huv => Classical.not_not.1 fun h => h_inj u v ( by aesop ) ( by aesop ) h huv;
        exact h_card ▸ Finset.card_le_card ( Finset.image_subset_iff.mpr fun u hu => hS u <| Finset.mem_filter.mp hu |>.2 );
      refine le_csInf ?_ ?_ <;> norm_num;
      · -- Since $C_r$ is compact, it can be covered by finitely many sets of diameter $\le \delta$.
        have h_compact : IsCompact (C r) := by
          have h_closed : IsClosed (C r) := by
            exact isClosed_C r hr
          have h_bounded : Bornology.IsBounded (C r) := by
            have h_bounded : ∀ n, C_n r n ⊆ Set.Icc 0 1 := by
              intro n x hx
              obtain ⟨u, hu⟩ : ∃ u ∈ Sigma_n n, x ∈ I_word u r := by
                unfold C_n at hx; aesop;
              obtain ⟨ y, hy, rfl ⟩ := hu.2;
              have h_f_word_bounds : ∀ u : List (Fin 2), ∀ y ∈ Set.Icc 0 1, f_word u r y ∈ Set.Icc 0 1 := by
                intro u y hy
                induction u generalizing y with
                | nil =>
                  simp_all +decide [ f_word ]
                | cons i u ih =>
                simp_all +decide [ f_word ] ;
                unfold f; fin_cases i <;> norm_num at * <;> constructor <;> nlinarith [ ih _ hy.1 hy.2 ] ;
              exact h_f_word_bounds u y hy;
            exact isCompact_Icc.isBounded.subset ( Set.iInter_subset_of_subset 0 <| h_bounded 0 )
          exact (by
          exact ( Metric.isCompact_iff_isClosed_bounded.mpr ⟨ h_closed, h_bounded ⟩ ));
        have := h_compact.elim_nhds_subcover;
        obtain ⟨ t, ht₁, ht₂ ⟩ := this ( fun x => Metric.closedBall x ( δ / 2 ) ) ( fun x hx => Metric.closedBall_mem_nhds _ ( half_pos hδ ) );
        refine ⟨ t.card, ⟨ fun i => Metric.closedBall ( t.orderEmbOfFin rfl i ) ( δ / 2 ), ?_, ?_ ⟩ ⟩ <;> norm_num;
        · intro i; rw [ Metric.ediam ] ; norm_num [ dist_eq_norm ] ; ring_nf; norm_num [ hδ.le ] ;
          exact fun x hx y hy => abs_le.mpr ⟨ by linarith [ abs_le.mp hx, abs_le.mp hy ], by linarith [ abs_le.mp hx, abs_le.mp hy ] ⟩;
        · intro x hx; specialize ht₂ hx; simp_all +decide [ Set.subset_def ] ;
          obtain ⟨ i, hi₁, hi₂ ⟩ := ht₂; rcases Finset.mem_image.mp ( show i ∈ Finset.image ( fun i : Fin t.card => t.orderEmbOfFin rfl i ) Finset.univ from by aesop ) with ⟨ j, _, rfl ⟩ ; exact ⟨ j, hi₂ ⟩ ;
      · intro b x hx hx'; contrapose! h_cover;
        exact ⟨ Finset.image x Finset.univ, by aesop, by simpa using hx', by simpa using lt_of_le_of_lt ( Finset.card_image_le ) ( by simpa ) ⟩

/-
The sequence n log 2 / -log(C r^n) converges to log 2 / -log r.
-/
lemma limit_lower_bound_aux (r : ℝ) (hr : 0 < r ∧ r < 1) (C : ℝ) (hC : 0 < C) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.log 2 / -Real.log (C * r ^ n)) Filter.atTop (nhds (Real.log 2 / -Real.log r)) := by
      -- We'll use the fact that $n \log r + \log C$ grows much faster than $n \log 2$ as $n$ tends to infinity.
      have h_lim : Filter.Tendsto (fun n : ℕ => (Real.log C + n * Real.log r) / n) Filter.atTop (nhds (Real.log r)) := by
        norm_num [ add_div ];
        exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; rw [ mul_div_cancel_left₀ _ ( Nat.cast_ne_zero.mpr hn ) ] ) ) ) ( by norm_num );
      convert Filter.Tendsto.div ( tendsto_const_nhds ) ( h_lim.neg ) _ using 2 <;> norm_num;
      · by_cases h : ‹_› = 0 <;> simp +decide [ h, Real.log_mul, hr.1.ne', hC.ne' ] ; ring_nf;
        grind;
      · exact ⟨ hr.1.ne', hr.2.ne, by linarith ⟩

/-
For delta sandwiched between scaled powers of r, the dimension ratio is bounded below by the sequence term.
-/
lemma ratio_lower_bound (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (h_sandwich_left : (1 - 2 * r) / 2 * r ^ n < δ)
    (h_sandwich_right : δ ≤ (1 - 2 * r) / 2 * r ^ (n - 1)) :
    Real.log (N_delta (C r) δ) / -Real.log δ ≥ (n * Real.log 2) / -Real.log ((1 - 2 * r) / 2 * r ^ n) := by
      gcongr;
      · simp +zetaDelta at *;
        exact Real.log_neg hδ ( by nlinarith [ pow_le_pow_of_le_one hr.1.le ( by norm_num at *; linarith ) ( Nat.zero_le ( n - 1 ) ) ] );
      · rw [ ← Real.log_pow ];
        gcongr;
        refine mod_cast N_delta_ge_two_pow r hr n δ hδ ?_;
        nlinarith [ pow_pos hr.1 ( n - 1 ) ];
      · exact mul_pos ( by linarith ) ( pow_pos hr.1 _ )

/-
The lower box dimension of C_r is at least s.
-/
theorem lower_box_dim_ge_s (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    lower_box_dim (C r) ≥ Real.log 2 / -Real.log r := by
      -- By definition of lower_box_dim, we need to show that for any ε > 0, there exists a δ > 0 such that for all δ' < δ, we have (log (N_delta' (C r))) / (-log δ') ≥ (log 2) / (-log r) - ε.
      suffices h_lower_bound : ∀ ε > 0, ∃ δ > 0, ∀ δ' ∈ Set.Ioo 0 δ, (Real.log (N_delta (C r) δ')) / (-Real.log δ') ≥ (Real.log 2) / (-Real.log r) - ε by
        contrapose! h_lower_bound;
        have := h_lower_bound;
        obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, lower_box_dim (C r) < (Real.log 2) / (-Real.log r) - ε := by
          exact ⟨ ( Real.log 2 / -Real.log r - lower_box_dim ( C r ) ) / 2, half_pos ( sub_pos.mpr this ), by linarith ⟩;
        contrapose! hε;
        refine le_csSup ?_ ?_;
        · refine ⟨ Real.log 2 / -Real.log r, fun x hx => ?_ ⟩;
          -- Since $N_\delta(C_r) \leq 2^n$ for $\delta = r^n$, we have $\frac{\log(N_\delta(C_r))}{-\log(\delta)} \leq \frac{n \log 2}{-\log(r^n)} = \frac{\log 2}{-\log r}$.
          have h_bound : ∀ n : ℕ, n ≥ 1 → (Real.log (N_delta (C r) (r ^ n))) / (-Real.log (r ^ n)) ≤ (Real.log 2) / (-Real.log r) := by
            intros n hn
            have h_bound : N_delta (C r) (r ^ n) ≤ 2 ^ n := by
              apply_rules [ N_delta_le ];
            rw [ div_le_div_iff₀ ] <;> norm_num;
            · have h_log_bound : Real.log (N_delta (C r) (r ^ n)) ≤ n * Real.log 2 := by
                by_cases h : N_delta ( C r ) ( r ^ n ) = 0 <;> simp_all +decide
                · positivity;
                · simpa using Real.log_le_log ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero h ) ) ( Nat.cast_le.mpr h_bound );
              nlinarith [ Real.log_le_sub_one_of_pos hr.1, Real.log_pos one_lt_two ];
            · exact mul_neg_of_pos_of_neg ( Nat.cast_pos.mpr hn ) ( Real.log_neg hr.1 ( by linarith ) );
            · exact Real.log_neg hr.1 ( by linarith );
          have h_seq : Filter.Tendsto (fun n : ℕ => r ^ n) Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
            rw [ tendsto_nhdsWithin_iff ];
            exact ⟨ tendsto_pow_atTop_nhds_zero_of_lt_one hr.1.le ( by linarith ), Filter.Eventually.of_forall fun n => pow_pos hr.1 _ ⟩;
          have := hx.filter_mono h_seq;
          rw [ Filter.eventually_map ] at this; rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ N, hN ⟩ ; exact le_trans ( hN ( N + 1 ) ( by linarith ) ) ( h_bound _ ( by linarith ) ) ;
        · rcases hε ε hε_pos with ⟨ δ, δ_pos, H ⟩ ; filter_upwards [ Ioo_mem_nhdsGT δ_pos ] with x hx using H x hx;
      intro ε hε_pos
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (n * Real.log 2) / (-Real.log ((1 - 2 * r) / 2 * r ^ n)) ≥ (Real.log 2) / (-Real.log r) - ε := by
        have h_limit : Filter.Tendsto (fun n : ℕ => (n * Real.log 2) / (-Real.log ((1 - 2 * r) / 2 * r ^ n))) Filter.atTop (nhds ((Real.log 2) / (-Real.log r))) := by
          convert limit_lower_bound_aux r ⟨ hr.1, by linarith ⟩ ( ( 1 - 2 * r ) / 2 ) ( by linarith ) using 1;
        exact Filter.eventually_atTop.mp ( h_limit.eventually ( le_mem_nhds <| sub_lt_self _ hε_pos ) );
      refine ⟨ ( 1 - 2 * r ) / 2 * r ^ N, ?_, ?_ ⟩ <;> norm_num at *;
      · exact mul_pos ( by linarith ) ( pow_pos hr.1 _ );
      · intro δ' hδ'_pos hδ'_lt
        obtain ⟨n, hn₁, hn₂, hn₃⟩ : ∃ n : ℕ, n ≥ 1 ∧ (1 - 2 * r) / 2 * r ^ n < δ' ∧ δ' ≤ (1 - 2 * r) / 2 * r ^ (n - 1) := by
          simp_all only [one_div, ge_iff_le]
          obtain ⟨left, right⟩ := hr
          apply exists_n_sandwich r ⟨left, by linarith⟩ ((1 - 2 * r) / 2) δ' hδ'_pos (by
          exact hδ'_lt.le.trans ( mul_le_of_le_one_right ( by linarith ) ( pow_le_one₀ ( by linarith ) ( by norm_num at *; linarith ) ) ))
        have := hN n ?_;
          · refine le_trans this ?_;
            simpa [add_comm] using add_le_add_right (ratio_lower_bound r hr n δ' hδ'_pos hn₂ hn₃) ε;
        · contrapose! hδ'_lt;
          exact le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_of_le_one hr.1.le ( by linarith ) hδ'_lt.le ) ( by linarith ) ) hn₂.le

/-
The lower box dimension of C_r is at least s = log 2 / -log r.
-/
theorem lower_box_dim_ge_s' (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    lower_box_dim (C r) ≥ Real.log 2 / -Real.log r := by
      -- Apply the lemma that states the lower box dimension is at least s.
      apply lower_box_dim_ge_s r hr

/-
C_plus is a subset of C.
-/
theorem C_plus_subset_C (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) :
    C_plus rho ⊆ C rho := by
      intro x hx
      obtain ⟨r_n, hr_n_eps, hr_n_C⟩ : ∃ r_n : ℕ → ℝ, Filter.Tendsto r_n Filter.atTop (nhds rho) ∧ ∀ n, x ∈ C (r_n n) := by
        -- By definition of $C_plus$, for every $\epsilon > 0$, there exists $r \in (rho - \epsilon, rho)$ such that $x \in C r$.
        have h_eps : ∀ ε > 0, ∃ r ∈ Set.Ioo (rho - ε) rho, x ∈ C r := by
          unfold C_plus at hx; aesop;
        choose! r hr using h_eps;
        exact ⟨ fun n => r ( 1 / ( n + 1 ) ), tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => abs_nonneg _ ) ( fun n => abs_le.mpr ⟨ by linarith [ Set.mem_Ioo.mp ( hr ( 1 / ( n + 1 ) ) ( by positivity ) |>.1 ) ], by linarith [ Set.mem_Ioo.mp ( hr ( 1 / ( n + 1 ) ) ( by positivity ) |>.1 ) ] ⟩ ) <| tendsto_one_div_add_atTop_nhds_zero_nat, fun n => hr _ ( by positivity ) |>.2 ⟩
      have hx_C : x ∈ C rho := by
        convert closedness_limit_Cantor rho hrho r_n hr_n_eps x hr_n_C using 1
      exact hx_C

/-
The ratio log N_delta / -log delta is eventually bounded.
-/
lemma ratio_eventually_bounded (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    Filter.IsBoundedUnder (· ≤ ·) (nhdsWithin 0 (Set.Ioi 0)) (fun δ => Real.log (N_delta (C r) δ) / -Real.log δ) ∧
    Filter.IsBoundedUnder (· ≥ ·) (nhdsWithin 0 (Set.Ioi 0)) (fun δ => Real.log (N_delta (C r) δ) / -Real.log δ) := by
      constructor;
      · have h_bound : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0), (N_delta (C r) δ : ℝ) ≤ 2 ^ (Nat.ceil (-(Real.log δ) / (-Real.log r))) := by
          filter_upwards [ self_mem_nhdsWithin ] with δ hδ
          have h_bound : N_delta (C r) δ ≤ 2 ^ Nat.ceil (-(Real.log δ) / (-Real.log r)) := by
            have h_cover_bound : ∀ n : ℕ, N_delta (C r) (r ^ n) ≤ 2 ^ n := by
              intro n
              apply N_delta_le r hr n;
            have h_bound : δ ≥ r ^ Nat.ceil (-(Real.log δ) / (-Real.log r)) := by
              have h_bound : Real.log δ ≥ Nat.ceil (-(Real.log δ) / (-Real.log r)) * Real.log r := by
                nlinarith [ Nat.le_ceil ( -Real.log δ / -Real.log r ), Real.log_le_sub_one_of_pos hr.1, mul_div_cancel₀ ( -Real.log δ ) ( by linarith [ Real.log_le_sub_one_of_pos hr.1 ] : ( -Real.log r ) ≠ 0 ) ];
              rw [ ge_iff_le, ← Real.log_le_log_iff ( pow_pos hr.1 _ ) hδ, Real.log_pow ] ; aesop;
            refine le_trans ?_ ( h_cover_bound ( Nat.ceil ( - ( Real.log δ ) / ( -Real.log r ) ) ) );
            apply_rules [ N_delta_antitone_on_pos ];
            exact pow_pos hr.1 _
          exact_mod_cast h_bound;
        have h_bound : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0), Real.log (N_delta (C r) δ) ≤ (Nat.ceil (-(Real.log δ) / (-Real.log r))) * Real.log 2 := by
          filter_upwards [ h_bound, self_mem_nhdsWithin ] with δ hδ hδ';
          by_cases h : N_delta ( C r ) δ = 0 <;> simp_all +decide
          · positivity;
          · simpa using Real.log_le_log ( by positivity ) hδ;
        have h_bound : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0), Real.log (N_delta (C r) δ) / -Real.log δ ≤ (-(Real.log δ) / (-Real.log r) + 1) * Real.log 2 / -Real.log δ := by
          filter_upwards [ h_bound, Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ] with δ hδ₁ hδ₂ using div_le_div_of_nonneg_right ( le_trans hδ₁ <| mul_le_mul_of_nonneg_right ( by linarith [ Nat.ceil_lt_add_one <| show 0 ≤ -Real.log δ / -Real.log r from div_nonneg ( neg_nonneg.mpr <| Real.log_nonpos hδ₂.1.le hδ₂.2.le ) <| neg_nonneg.mpr <| Real.log_nonpos hr.1.le <| by linarith ] ) <| Real.log_nonneg <| by norm_num ) <| neg_nonneg.mpr <| Real.log_nonpos hδ₂.1.le hδ₂.2.le;
        have h_bound : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0), Real.log (N_delta (C r) δ) / -Real.log δ ≤ (Real.log 2 / -Real.log r) + (Real.log 2 / -Real.log δ) := by
          filter_upwards [ h_bound, ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) ] with δ hδ₁ hδ₂ ; convert hδ₁ using 1 ; ring_nf ; norm_num [ ne_of_gt, Real.log_pos, hδ₂.1, hδ₂.2 ] ;
          rw [ mul_assoc, mul_inv_cancel₀ ( ne_of_lt ( Real.log_neg hδ₂.1 hδ₂.2 ) ), mul_one ];
        have h_bound : Filter.Tendsto (fun δ => Real.log 2 / -Real.log δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          have h_log_delta : Filter.Tendsto (fun δ => Real.log δ) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
            exact Real.tendsto_log_nhdsGT_zero;
          exact tendsto_const_nhds.div_atTop ( Filter.tendsto_neg_atBot_atTop.comp h_log_delta );
        have h_bound : Filter.Tendsto (fun δ => Real.log 2 / -Real.log r + Real.log 2 / -Real.log δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log 2 / -Real.log r)) := by
          simpa using tendsto_const_nhds.add h_bound;
        exact ⟨ _, Filter.eventually_map.mpr <| by filter_upwards [ ‹∀ᶠ δ in nhdsWithin 0 ( Set.Ioi 0 ), Real.log ↑ ( N_delta ( C r ) δ ) / -Real.log δ ≤ Real.log 2 / -Real.log r + Real.log 2 / -Real.log δ›, h_bound.eventually ( ge_mem_nhds <| show Real.log 2 / -Real.log r < Real.log 2 / -Real.log r + 1 by linarith ) ] with x hx₁ hx₂ using le_trans hx₁ hx₂ ⟩;
      · refine ⟨ 0, ?_ ⟩;
        norm_num +zetaDelta at *;
        filter_upwards [ Ioo_mem_nhdsGT zero_lt_one ] with x hx using div_nonneg ( Real.log_natCast_nonneg _ ) ( neg_nonneg_of_nonpos ( Real.log_nonpos hx.1.le hx.2.le ) ) ;

/-
The ratio log N_delta / -log delta is bounded below as delta -> 0.
-/
lemma ratio_bounded_below (r : ℝ) :
    Filter.IsBoundedUnder (· ≥ ·) (nhdsWithin 0 (Set.Ioi 0)) (fun δ => Real.log (N_delta (C r) δ) / -Real.log δ) := by
      field_simp;
      refine ⟨ 0, ?_ ⟩ ; simp +decide
      filter_upwards [ Ioo_mem_nhdsGT zero_lt_one ] with x hx using div_nonpos_of_nonneg_of_nonpos ( Real.log_natCast_nonneg _ ) ( Real.log_nonpos hx.1.le hx.2.le ) ;

/-
The ratio log N_delta / -log delta is bounded above as delta -> 0.
-/
lemma ratio_bounded_above (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    Filter.IsBoundedUnder (· ≤ ·) (nhdsWithin 0 (Set.Ioi 0)) (fun δ => Real.log (N_delta (C r) δ) / -Real.log δ) := by
      have := ratio_eventually_bounded r hr;
      exact this.1

/-
Theorem 2.6: The Hausdorff and box dimensions of the middle-a Cantor set are all equal to s.
-/
theorem theorem_dimension_Ca (r : ℝ) (hr : 0 < r ∧ r < 1 / 2) :
    let s := Real.log 2 / -Real.log r
    dimH (C r) = ENNReal.ofReal s ∧
    lower_box_dim (C r) = s ∧
    upper_box_dim (C r) = s := by
      let s := Real.log 2 / -Real.log r
      have h_dimH : dimH (C r) = ENNReal.ofReal s := dimH_C_eq_s r hr
      have h_upper : upper_box_dim (C r) ≤ s := upper_box_dim_le_s r hr
      have h_lower : lower_box_dim (C r) ≥ s := lower_box_dim_ge_s' r hr
      have h_neBot : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := by
        refine mem_closure_iff_nhdsWithin_neBot.mp ?_
        rw [closure_Ioi]
        exact Set.self_mem_Ici
      have h_le : lower_box_dim (C r) ≤ upper_box_dim (C r) := by
        apply Filter.liminf_le_limsup
        · exact ratio_bounded_above r hr
        · exact ratio_bounded_below r
      have h_eq : lower_box_dim (C r) = s ∧ upper_box_dim (C r) = s := by
        constructor
        · apply le_antisymm
          · exact le_trans h_le h_upper
          · exact h_lower
        · apply le_antisymm
          · exact h_upper
          · exact le_trans h_lower h_le
      exact ⟨h_dimH, h_eq.1, h_eq.2⟩

/-
If omega starts with 0 and is not eventually 1, then pi(omega) is in C_plus.
-/
lemma mem_C_plus_of_not_eventually_one (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (ω : ℕ → Fin 2) (h0 : ω 0 = 0) (h_not_ev_one : ∀ n, ∃ k ≥ n, ω k ≠ 1) :
    pi rho ω ∈ C_plus rho := by
      -- Let $x = \pi_\rho(\omega)$.
      set x := pi rho ω;
      by_cases hx : x = 0;
      · convert endpoints_mem_C_plus rho hrho |>.1 using 1;
      · -- Choose $s \in (\max(0, \rho - \epsilon), \rho)$.
        have h_eps : ∀ ε > 0, ε < rho → ∃ s ∈ Set.Ioo (max 0 (rho - ε)) rho, ∃ n : ℕ, ∃ r ∈ Set.Ioo s rho, x = R_word (take_word n ω) r := by
          intro ε hε_pos hε_lt_rho
          obtain ⟨s, hs⟩ : ∃ s ∈ Set.Ioo (max 0 (rho - ε)) rho, pi s ω < x := by
            have h_pi_strictly_increasing : StrictMonoOn (fun r => pi r ω) (Set.Ico 0 (1 / 2)) := by
              apply_rules [ pi_strictly_increasing ];
              contrapose! hx;
              simp +zetaDelta at *;
              unfold pi; aesop;
            exact ⟨ ( rho + max 0 ( rho - ε ) ) / 2, ⟨ by cases max_cases 0 ( rho - ε ) <;> linarith, by cases max_cases 0 ( rho - ε ) <;> linarith ⟩, h_pi_strictly_increasing ⟨ by cases max_cases 0 ( rho - ε ) <;> linarith, by cases max_cases 0 ( rho - ε ) <;> linarith ⟩ ⟨ by cases max_cases 0 ( rho - ε ) <;> linarith, by cases max_cases 0 ( rho - ε ) <;> linarith ⟩ ( by cases max_cases 0 ( rho - ε ) <;> linarith ) ⟩;
          -- Let $u_n = \omega|_n$.
          obtain ⟨n, hn⟩ : ∃ n : ℕ, R_word (take_word n ω) s < x ∧ x < R_word (take_word n ω) rho := by
            -- Since $R_{u_n}(s) \to \pi_s(\omega)$ and $x < R_{u_n}(\rho)$ for all $n$, we can choose $n$ such that $R_{u_n}(s) < x$.
            obtain ⟨n, hn⟩ : ∃ n : ℕ, R_word (take_word n ω) s < x := by
              have h_lim : Filter.Tendsto (fun n => R_word (take_word n ω) s) Filter.atTop (nhds (pi s ω)) := by
                convert tendsto_R_word s ⟨ by linarith [ hs.1.1, le_max_left 0 ( rho - ε ) ], by linarith [ hs.1.2, le_max_right 0 ( rho - ε ) ] ⟩ ω using 1;
              exact ( h_lim.eventually ( gt_mem_nhds hs.2 ) ) |> fun h => h.exists;
            exact ⟨ n, hn, by simpa using pi_lt_R_word_of_not_eventually_one rho hrho ω h_not_ev_one n ⟩;
          -- By the Intermediate Value Theorem, there exists $r \in (s, \rho)$ such that $R_{u_n}(r) = x$.
          obtain ⟨r, hr⟩ : ∃ r ∈ Set.Ioo s rho, R_word (take_word n ω) r = x := by
            apply_rules [ intermediate_value_Ioo ];
            · linarith [ hs.1.2 ];
            · -- The function R_word (take_word n ω) is a composition of continuous functions, hence it is continuous.
              have h_cont : ContinuousOn (fun r => (1 - r) * (∑ k ∈ Finset.range (take_word n ω).length, ((take_word n ω)[k]?.getD 0 : ℝ) * r ^ k) + r ^ (take_word n ω).length) (Set.Icc s rho) := by
                fun_prop;
              refine h_cont.congr fun r hr => ?_;
              convert pi_append_ones r ( show 0 < r ∧ r < 1 / 2 from ⟨ by linarith [ hr.1, hs.1.1, le_max_left 0 ( rho - ε ), le_max_right 0 ( rho - ε ) ], by linarith [ hr.2, hs.1.2 ] ⟩ ) ( take_word n ω ) using 1
          use s, hs.left, n, r, hr.left, hr.right.symm ▸ rfl;
        refine Set.mem_iInter₂.mpr fun ε hε => ?_;
        obtain ⟨ s, hs₁, n, r, hr₁, hr₂ ⟩ := h_eps ( Min.min ε ( rho / 2 ) ) ( lt_min hε ( half_pos hrho.1 ) ) ( by linarith [ min_le_left ε ( rho / 2 ), min_le_right ε ( rho / 2 ) ] );
        simp +zetaDelta at *;
        refine ⟨ r, ⟨ by linarith [ min_le_left ε ( rho / 2 ), min_le_right ε ( rho / 2 ) ], by linarith ⟩, ?_ ⟩;
        refine Set.mem_iInter.mpr fun m => ?_;
        refine Set.mem_iUnion₂.mpr ⟨ take_word m ( append_ones ( take_word n ω ) ), ?_, ?_ ⟩ <;> norm_num [ hr₂ ];
        · unfold take_word Sigma_n; aesop;
        · convert pi_mem_I_word r ⟨ by linarith, by linarith ⟩ ( append_ones ( take_word n ω ) ) m using 1

/-
If omega starts with 1 and is not eventually 0, then pi(omega) is in C_plus.
-/
lemma mem_C_plus_of_not_eventually_zero (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (ω : ℕ → Fin 2) (h1 : ω 0 = 1) (h_not_ev_zero : ∀ n, ∃ k ≥ n, ω k ≠ 0) :
    pi rho ω ∈ C_plus rho := by
      -- Let $x = \pi_\rho(\omega)$. If $x = 1$, then $x \in C_+$.
      by_cases hx1 : pi rho ω = 1;
      · convert endpoints_mem_C_plus rho hrho |>.2 using 1;
      · -- Let $x = \pi_\rho(\omega)$. Since $x \neq 1$, we have $x < 1$.
        set x := pi rho ω
        have hx_lt_1 : x < 1 := by
          refine lt_of_le_of_ne ?_ hx1
          generalize_proofs at *;
          refine le_trans
            ( mul_le_mul_of_nonneg_left
              ( Summable.tsum_le_tsum ( g := fun n : ℕ => rho ^ n ) ?_ ?_ ?_ )
              ( by linarith ) ) ?_;
          all_goals generalize_proofs at *; norm_num at *;
          · exact fun n => mul_le_of_le_one_left ( pow_nonneg hrho.1.le _ ) ( mod_cast Fin.is_le _ );
          · exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hrho.1.le _ ) ) ( fun n => mul_le_of_le_one_left ( pow_nonneg hrho.1.le _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one hrho.1.le ( by linarith ) );
          · rw [ abs_of_pos ] <;> linarith;
          · rw [ tsum_geometric_of_lt_one ] <;> nlinarith [ mul_inv_cancel₀ ( by linarith : ( 1 - rho ) ≠ 0 ) ];
        -- Let $\epsilon > 0$. Choose $s \in (\max(0, \rho - \epsilon), \rho)$.
        have h_eps : ∀ ε > 0, ∃ s ∈ Set.Ioo (max 0 (rho - ε)) rho, ∃ n : ℕ, ∃ r ∈ Set.Ioo s rho, pi r (append_zeros (take_word n ω)) = x := by
          -- Let $\epsilon > 0$. Choose $s \in (\max(0, \rho - \epsilon), \rho)$ such that $pi_s(\omega) > x$.
          intro ε hε_pos
          obtain ⟨s, hs₁, hs₂⟩ : ∃ s ∈ Set.Ioo (max 0 (rho - ε)) rho, pi s ω > x := by
            have h_strict_anti : StrictAntiOn (fun r => pi r ω) (Set.Ico 0 (1 / 2)) := by
              apply_rules [ pi_strictly_decreasing ];
              contrapose! hx1;
              simp +zetaDelta at *;
              unfold pi; norm_num [ hx1, tsum_mul_left, tsum_geometric_of_lt_one, hrho ] ;
              rw [ tsum_geometric_of_lt_one ] <;> norm_num at * <;> nlinarith [ mul_inv_cancel₀ ( by linarith : ( 1 - rho ) ≠ 0 ) ];
            exact ⟨ ( rho + max 0 ( rho - ε ) ) / 2, ⟨ by linarith [ show max 0 ( rho - ε ) < rho by cases max_cases 0 ( rho - ε ) <;> linarith ], by linarith [ show max 0 ( rho - ε ) < rho by cases max_cases 0 ( rho - ε ) <;> linarith ] ⟩, h_strict_anti ⟨ by cases max_cases 0 ( rho - ε ) <;> linarith, by cases max_cases 0 ( rho - ε ) <;> linarith ⟩ ⟨ by cases max_cases 0 ( rho - ε ) <;> linarith, by cases max_cases 0 ( rho - ε ) <;> linarith ⟩ ( by cases max_cases 0 ( rho - ε ) <;> linarith ) ⟩;
          -- Let $u_n = \text{take\_word } n \omega$. Then $L_{u_n}(s) \to \pi_s(\omega) > x$.
          obtain ⟨n, hn⟩ : ∃ n : ℕ, pi s (append_zeros (take_word n ω)) > x := by
            have h_lim : Filter.Tendsto (fun n => pi s (append_zeros (take_word n ω))) Filter.atTop (nhds (pi s ω)) := by
              have h_lim : ∀ n, pi s (append_zeros (take_word n ω)) = (1 - s) * ∑ k ∈ Finset.range n, (ω k : ℝ) * s ^ k := by
                intro n
                simp [take_word];
                convert pi_append_zeros s ( List.ofFn fun i : Fin n => ω i ) using 1;
                simp +decide [ Finset.sum_range ]
              have h_lim : Filter.Tendsto (fun n => (1 - s) * ∑ k ∈ Finset.range n, (ω k : ℝ) * s ^ k) Filter.atTop (nhds ((1 - s) * ∑' k, (ω k : ℝ) * s ^ k)) := by
                refine tendsto_const_nhds.mul ( Summable.hasSum ?_ |> HasSum.tendsto_sum_nat );
                exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by linarith [ hs₁.1, le_max_left 0 ( rho - ε ), le_max_right 0 ( rho - ε ) ] ) _ ) ) ( fun n => mul_le_of_le_one_left ( pow_nonneg ( by linarith [ hs₁.1, le_max_left 0 ( rho - ε ), le_max_right 0 ( rho - ε ) ] ) _ ) ( mod_cast Fin.is_le _ ) ) ( summable_geometric_of_lt_one ( by linarith [ hs₁.1, le_max_left 0 ( rho - ε ), le_max_right 0 ( rho - ε ) ] ) ( by linarith [ hs₁.2, le_max_left 0 ( rho - ε ), le_max_right 0 ( rho - ε ) ] ) );
              convert h_lim using 2 ; aesop;
            exact ( h_lim.eventually ( lt_mem_nhds hs₂ ) ) |> fun h => h.exists;
          -- By the intermediate value theorem, since $L_{u_n}(s) > x$ and $L_{u_n}(\rho) < x$, there exists $r \in (s, \rho)$ such that $L_{u_n}(r) = x$.
          obtain ⟨r, hr₁, hr₂⟩ : ∃ r ∈ Set.Ioo s rho, pi r (append_zeros (take_word n ω)) = x := by
            apply_rules [ intermediate_value_Ioo' ];
            · linarith [ hs₁.2 ];
            · refine ContinuousOn.mul ?_ ?_;
              · exact continuousOn_const.sub continuousOn_id;
              · refine continuousOn_tsum
                  ( f := fun i x => (append_zeros (take_word n ω) i : ℝ) * x ^ i )
                  ( u := fun i => ( 1 : ℝ ) * rho ^ i ) ?_ ?_ ?_;
                · exact fun i => Continuous.continuousOn ( by continuity );
                · exact Summable.mul_left _ ( summable_geometric_of_lt_one hrho.1.le ( by linarith ) );
                · norm_num +zetaDelta at *;
                  exact fun n x hx₁ hx₂ => le_trans ( mul_le_of_le_one_left ( by positivity ) ( mod_cast Fin.is_le _ ) ) ( pow_le_pow_left₀ ( by positivity ) ( by rw [ abs_of_nonneg ] <;> linarith ) _ )
            · exact ⟨ by simpa using pi_gt_L_word_of_not_eventually_zero rho hrho ω h_not_ev_zero n, hn ⟩;
          exact ⟨ s, hs₁, n, r, hr₁, hr₂ ⟩;
        refine Set.mem_iInter₂.mpr fun ε hε => ?_;
        obtain ⟨ s, hs₁, n, r, hr₁, hr₂ ⟩ := h_eps ε hε;
        simp +zetaDelta at *;
        refine ⟨ r, ⟨ by linarith, by linarith ⟩, ?_ ⟩;
        rw [ ← hr₂ ];
        apply range_pi_subset_C' r ⟨ by linarith, by linarith ⟩ |> Set.mem_of_mem_of_subset <| Set.Subset.refl _;
        exact Set.mem_range_self _

/-
Definition of the exceptional set E_minus.
-/
def E_minus (rho : ℝ) : Set ℝ :=
  {x | ∃ u : List (Fin 2), u ≠ [] ∧ u.head! = 0 ∧ (1 : Fin 2) ∈ u ∧ x = pi rho (append_zeros u)} ∪
  {x | ∃ u : List (Fin 2), u ≠ [] ∧ u.head! = 1 ∧ (0 : Fin 2) ∈ u ∧ x = pi rho (append_ones u)}

/-
If u starts with 0 and contains a 1, then L_u(rho) is not in C_minus.
-/
theorem not_mem_C_minus_of_L_u (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (u : List (Fin 2)) (hu : u ≠ []) (h0 : u.head! = 0) (h_contains_one : (1 : Fin 2) ∈ u) :
    pi rho (append_zeros u) ∉ C_minus rho := by
      have h_not_mem_C_n : ∀ᶠ r in nhdsWithin rho (Set.Ioi rho), pi rho (append_zeros u) ∉ C_n r u.length := by
        have h_not_mem_C_n : ∀ᶠ r in nhdsWithin rho (Set.Ioi rho), ∀ v ∈ Sigma_n u.length, v ≠ u → pi rho (append_zeros u) ∉ I_word v r := by
          have h_not_mem_I_word_of_ne_zeros : ∀ v ∈ Sigma_n u.length, v ≠ u → ∀ᶠ r in nhds rho, pi rho (append_zeros u) ∉ I_word v r := by
            exact fun v a a_1 => not_mem_I_word_of_ne_zeros rho hrho u v a a_1;
          have h_finite : Set.Finite {v ∈ Sigma_n u.length | v ≠ u} := by
            exact Set.Finite.subset ( finite_Sigma_n u.length ) fun v hv => hv.1;
          have h_finite : ∀ᶠ r in nhds rho, ∀ v ∈ {v ∈ Sigma_n u.length | v ≠ u}, pi rho (append_zeros u) ∉ I_word v r := by
            have h_finite : ∀ v ∈ {v ∈ Sigma_n u.length | v ≠ u}, ∀ᶠ r in nhds rho, pi rho (append_zeros u) ∉ I_word v r := by
              aesop;
            (expose_names; exact eventually_subset_of_finite h_finite_1 h_finite);
          exact h_finite.filter_mono nhdsWithin_le_nhds |> fun h => h.mono fun r hr v hv hv' => hr v ⟨ hv, hv' ⟩;
        have h_not_mem_C_n : ∀ᶠ r in nhdsWithin rho (Set.Ioi rho), pi rho (append_zeros u) ∉ I_word u r := by
          have h_not_mem_C_n : ∀ᶠ r in nhdsWithin rho (Set.Ioi rho), pi rho (append_zeros u) < L_word u r := by
            have h_not_mem_C_n : StrictMonoOn (fun r => L_word u r) (Set.Ico 0 (1 / 2)) := by
              convert pi_strictly_increasing ( append_zeros u ) _ _ using 1 <;> norm_num [ h0, h_contains_one ];
              · cases u <;> aesop;
              · obtain ⟨ n, hn ⟩ := List.mem_iff_get.mp h_contains_one; use n; simp +decide [ append_zeros ] ;
                aesop;
            filter_upwards [ Ioo_mem_nhdsGT hrho.2 ] with r hr using h_not_mem_C_n ⟨ by linarith, by linarith ⟩ ⟨ by linarith [ hr.1 ], by linarith [ hr.2 ] ⟩ hr.1;
          filter_upwards [ h_not_mem_C_n, mem_nhdsWithin_of_mem_nhds ( Ioo_mem_nhds hrho.1 hrho.2 ) ] with r hr₁ hr₂;
          have h_not_mem_C_n : pi rho (append_zeros u) < pi r (append_zeros u) := by
            exact hr₁;
          exact fun h => h_not_mem_C_n.not_ge <| by linarith [ Set.mem_Icc.mp <| prop_symbolic_3_interval r hr₂ u ▸ h ] ;
        filter_upwards [ h_not_mem_C_n, ‹∀ᶠ r in nhdsWithin rho ( Set.Ioi rho ), ∀ v ∈ Sigma_n u.length, v ≠ u → pi rho ( append_zeros u ) ∉ I_word v r› ] with r hr₁ hr₂;
        simp_all +decide [ C_n ];
        exact fun v hv => if hv' : v = u then hv'.symm ▸ hr₁ else hr₂ v hv hv';
      simp_all +decide [ C_minus ];
      obtain ⟨ ε, hε, H ⟩ := Metric.mem_nhdsWithin_iff.mp h_not_mem_C_n;
      refine ⟨ ε, hε, fun r hr₁ hr₂ => ?_ ⟩;
      intro h;
      exact H ⟨ Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith, by linarith ⟩, hr₁ ⟩ <| Set.mem_iInter.mp h u.length

/-
If u starts with 1 and contains a 0, then R_u(rho) is not in C_minus.
-/
theorem not_mem_C_minus_of_R_u (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (u : List (Fin 2)) (hu : u ≠ []) (h1 : u.head! = 1) (h_contains_zero : (0 : Fin 2) ∈ u) :
    pi rho (append_ones u) ∉ C_minus rho := by
      unfold C_minus;
      -- For $r$ close to $\rho$, $x$ is not in $I_u(r)$ because $R_u(r) < x$.
      have h_not_in_I : ∀ᶠ r in nhdsWithin rho (Set.Ioi rho), pi rho (append_ones u) ∉ I_word u r := by
        have h_not_in_I : ∀ᶠ r in nhdsWithin rho (Set.Ioi rho), pi rho (append_ones u) > R_word u r := by
          have h_not_in_I : StrictAntiOn (fun r => R_word u r) (Set.Ico 0 (1 / 2)) := by
            apply_rules [ pi_strictly_decreasing ];
            · cases u <;> aesop;
            · obtain ⟨ n, hn ⟩ := List.mem_iff_get.mp h_contains_zero; use n; simp_all +decide [ append_ones ] ;
          filter_upwards [ Ioo_mem_nhdsGT ( show rho < 1 / 2 by linarith ) ] with r hr using h_not_in_I ⟨ by linarith, by linarith ⟩ ⟨ by linarith [ hr.1 ], by linarith [ hr.2 ] ⟩ hr.1 |> lt_of_lt_of_le <| by aesop;
        filter_upwards [ h_not_in_I, Ioo_mem_nhdsGT hrho.2 ] with r hr₁ hr₂;
        have := prop_symbolic_3_interval r ⟨ by linarith [ hr₂.1 ], by linarith [ hr₂.2 ] ⟩ u; aesop;
      -- For $v \neq u$ of the same length, $I_v(r)$ is far from $I_u(r)$, so $x \notin I_v(r)$ by continuity.
      have h_not_in_I_v : ∀ᶠ r in nhdsWithin rho (Set.Ioi rho), ∀ v ∈ Sigma_n u.length, v ≠ u → pi rho (append_ones u) ∉ I_word v r := by
        have h_dist : ∀ v ∈ Sigma_n u.length, v ≠ u → ∀ᶠ r in nhds rho, pi rho (append_ones u) ∉ I_word v r := by
          intros v hv hv_ne_u
          apply not_mem_I_word_of_ne rho hrho u v hv hv_ne_u;
        have h_finite : Set.Finite {v : List (Fin 2) | v ∈ Sigma_n u.length ∧ v ≠ u} := by
          exact Set.Finite.subset ( finite_Sigma_n u.length ) fun v hv => hv.1;
        rw [ eventually_nhdsWithin_iff ];
        filter_upwards [ h_finite.eventually_all.mpr fun v hv => h_dist v hv.1 hv.2 ] with x hx hx' v hv hv' using hx v ⟨ hv, hv' ⟩;
      -- Therefore, for $r$ close to $\rho$, $x$ is not in $C_{1-2r}$.
      have h_not_in_C : ∀ᶠ r in nhdsWithin rho (Set.Ioi rho), pi rho (append_ones u) ∉ C_n r u.length := by
        filter_upwards [ h_not_in_I, h_not_in_I_v ] with r hr₁ hr₂;
        contrapose! hr₂; unfold C_n at *; aesop;
      simp +zetaDelta at *;
      rcases Metric.mem_nhdsWithin_iff.mp h_not_in_C with ⟨ ε, εpos, hε ⟩;
      use ε / 2, half_pos εpos, fun r hr₁ hr₂ => fun hr₃ => hε ⟨ Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith, by linarith ⟩, hr₁ ⟩ <| Set.mem_iInter.mp hr₃ u.length |> fun h => by aesop;

/-
If omega starts with 0 and is not eventually 0, then pi(omega) is in C_minus.
-/
theorem mem_C_minus_of_not_eventually_zero (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (ω : ℕ → Fin 2) (h0 : ω 0 = 0) (h_not_ev_zero : ∀ n, ∃ k ≥ n, ω k ≠ 0) :
    pi rho ω ∈ C_minus rho := by
      -- Since $\pi_\rho(\omega)$ is strictly increasing on $[0, 1 / 2)$ and $\pi_\rho(\omega) > L_{u_n}(\rho)$ for all $n$, we can find $r \in (\rho, \min(\rho+\varepsilon, 1 / 2))$ such that $L_{u_n}(r) = \pi_\rho(\omega)$.
      have h_ivt : ∀ ε > 0, ∃ r ∈ Set.Ioo rho (min (rho + ε) (1 / 2)), ∃ n, L_word (take_word n ω) r = pi rho ω := by
        -- Fix an arbitrary $\epsilon > 0$.
        intro ε hε_pos
        obtain ⟨s, hs⟩ : ∃ s ∈ Set.Ioo rho (min (rho + ε) (1 / 2)), pi s ω > pi rho ω := by
          have h_strict_mono : StrictMonoOn (fun r => pi r ω) (Set.Ico 0 (1 / 2)) := by
            apply_rules [ pi_strictly_increasing ];
            exact Exists.elim ( h_not_ev_zero 0 ) fun n hn => ⟨ n, hn.2 ⟩;
          exact ⟨ rho + ( Min.min ( rho + ε ) ( 1 / 2 ) - rho ) / 2, ⟨ by linarith [ lt_min ( show rho + ε > rho by linarith ) ( show 1 / 2 > rho by linarith ) ], by linarith [ lt_min ( show rho + ε > rho by linarith ) ( show 1 / 2 > rho by linarith ), min_le_left ( rho + ε ) ( 1 / 2 ), min_le_right ( rho + ε ) ( 1 / 2 ) ] ⟩, h_strict_mono ⟨ by linarith [ lt_min ( show rho + ε > rho by linarith ) ( show 1 / 2 > rho by linarith ) ], by linarith [ lt_min ( show rho + ε > rho by linarith ) ( show 1 / 2 > rho by linarith ), min_le_left ( rho + ε ) ( 1 / 2 ), min_le_right ( rho + ε ) ( 1 / 2 ) ] ⟩ ⟨ by linarith [ lt_min ( show rho + ε > rho by linarith ) ( show 1 / 2 > rho by linarith ) ], by linarith [ lt_min ( show rho + ε > rho by linarith ) ( show 1 / 2 > rho by linarith ), min_le_left ( rho + ε ) ( 1 / 2 ), min_le_right ( rho + ε ) ( 1 / 2 ) ] ⟩ ( by linarith [ lt_min ( show rho + ε > rho by linarith ) ( show 1 / 2 > rho by linarith ), min_le_left ( rho + ε ) ( 1 / 2 ), min_le_right ( rho + ε ) ( 1 / 2 ) ] ) ⟩;
        -- Since $\pi_s(\omega) > \pi_\rho(\omega)$, there exists $n$ such that $L_{u_n}(s) > \pi_\rho(\omega)$.
        obtain ⟨n, hn⟩ : ∃ n, L_word (take_word n ω) s > pi rho ω := by
          have h_lim : Filter.Tendsto (fun n => L_word (take_word n ω) s) Filter.atTop (nhds (pi s ω)) := by
            have h_lim : Filter.Tendsto (fun n => R_word (take_word n ω) s) Filter.atTop (nhds (pi s ω)) := by
              convert tendsto_R_word s ⟨ by linarith [ hs.1.1 ], by linarith [ hs.1.2, min_le_right ( rho + ε ) ( 1 / 2 ) ] ⟩ ω using 1;
            have h_lim : ∀ n, L_word (take_word n ω) s = R_word (take_word n ω) s - s ^ n := by
              intro n
              simp [L_word, R_word];
              rw [ pi_append_zeros, pi_append_ones ];
              · unfold take_word; aesop;
              · constructor <;> linarith [ hs.1.1, hs.1.2, min_le_left ( rho + ε ) ( 1 / 2 ), min_le_right ( rho + ε ) ( 1 / 2 ) ];
            convert ‹Tendsto ( fun n => R_word ( take_word n ω ) s ) Filter.atTop ( nhds ( pi s ω ) ) ›.sub ( tendsto_pow_atTop_nhds_zero_of_lt_one ( show 0 ≤ s by linarith [ hs.1.1 ] ) ( show s < 1 by linarith [ hs.1.2, min_le_left ( rho + ε ) ( 1 / 2 ), min_le_right ( rho + ε ) ( 1 / 2 ) ] ) ) using 2 ; aesop;
            ring;
          exact ( h_lim.eventually ( lt_mem_nhds hs.2 ) ) |> fun h => h.exists;
        -- By the Intermediate Value Theorem, since $L_{u_n}(r)$ is continuous and $L_{u_n}(s) > \pi_\rho(\omega)$, there exists $r \in (\rho, s)$ such that $L_{u_n}(r) = \pi_\rho(\omega)$.
        have h_ivt : ∃ r ∈ Set.Ioo rho s, L_word (take_word n ω) r = pi rho ω := by
          apply_rules [ intermediate_value_Ioo ] <;> norm_num [ hs.1.1, hs.1.2 ];
          · linarith [ hs.1.1 ];
          · refine ContinuousOn.congr
              ( s := ( Set.Icc rho ( show ℝ from s ) : Set ℝ ) )
              ( f := fun r : ℝ =>
                (1 - r) * ∑ k ∈ Finset.range n, ((take_word n ω)[k]?).getD 0 * r ^ k +
                  r ^ n * 0 ) ?_ ?_;
            · fun_prop (disch := norm_num);
            · intro r hr; unfold L_word; simp +decide
              convert pi_append_zeros r ( take_word n ω ) using 1;
              unfold take_word; aesop;
          · exact ⟨ pi_gt_L_word_of_not_eventually_zero rho hrho ω h_not_ev_zero n, hn ⟩;
        exact ⟨ h_ivt.choose, ⟨ h_ivt.choose_spec.1.1, h_ivt.choose_spec.1.2.trans_le hs.1.2.le ⟩, n, h_ivt.choose_spec.2 ⟩;
      contrapose! h_ivt;
      simp_all +decide [ C_minus ];
      obtain ⟨ ε, hε₁, hε₂ ⟩ := h_ivt; use ε, hε₁; intros r hr₁ hr₂ hr₃ n hn; specialize hε₂ r hr₁ hr₂; simp_all +decide [ C ] ;
      obtain ⟨ x, hx ⟩ := hε₂; exact hx <| hn ▸ pi_mem_C_n r ⟨ by linarith, by linarith ⟩ _ _;

/-
If omega starts with 1 and is not eventually 1, then pi(omega) is in C_minus.
-/
theorem mem_C_minus_of_not_eventually_one (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) (ω : ℕ → Fin 2) (h1 : ω 0 = 1) (h_not_ev_one : ∀ n, ∃ k ≥ n, ω k ≠ 1) :
    pi rho ω ∈ C_minus rho := by
      -- Let's choose any $\epsilon > 0$.
      by_contra h_not_in_C_minus;
      -- Let's choose any $\epsilon > 0$ and derive a contradiction.
      obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ r ∈ Set.Ioo rho (rho + ε), pi rho ω ∉ C r := by
        unfold C_minus at h_not_in_C_minus; aesop;
      -- Choose $s \in (\rho, \min(\rho+\varepsilon, 1 / 2))$.
      obtain ⟨s, hs⟩ : ∃ s ∈ Set.Ioo rho (min (rho + ε) (1 / 2)), True := by
        exact ⟨ rho + ( Min.min ( rho + ε ) ( 1 / 2 ) - rho ) / 2, ⟨ by linarith [ lt_min ( show rho + ε > rho by linarith ) ( show 1 / 2 > rho by linarith ) ], by linarith [ lt_min ( show rho + ε > rho by linarith ) ( show 1 / 2 > rho by linarith ), min_le_left ( rho + ε ) ( 1 / 2 ), min_le_right ( rho + ε ) ( 1 / 2 ) ] ⟩, trivial ⟩;
      -- Since $\omega$ starts with 1 and is not $1^\infty$, $\pi_r(\omega)$ is strictly decreasing on $[0, 1 / 2)$.
      have h_pi_decreasing : StrictAntiOn (fun r => pi r ω) (Set.Ico 0 (1 / 2)) := by
        apply_rules [ pi_strictly_decreasing ];
        exact Exists.elim ( h_not_ev_one 0 ) fun n hn => ⟨ n, hn.2 ⟩;
      -- Since $\pi_s(\omega) < \pi_\rho(\omega) = x$, for large enough $n$, $R_{u_n}(s) < x$.
      obtain ⟨n, hn⟩ : ∃ n : ℕ, R_word (take_word n ω) s < pi rho ω ∧ pi rho ω < R_word (take_word n ω) rho := by
        have h_pi_s_lt_pi_rho : pi s ω < pi rho ω := by
          exact h_pi_decreasing ⟨ by linarith [ hs.1.1 ], by linarith [ hs.1.2, min_le_left ( rho + ε ) ( 1 / 2 ), min_le_right ( rho + ε ) ( 1 / 2 ) ] ⟩ ⟨ by linarith [ hs.1.1 ], by linarith [ hs.1.2, min_le_left ( rho + ε ) ( 1 / 2 ), min_le_right ( rho + ε ) ( 1 / 2 ) ] ⟩ hs.1.1;
        -- Since $\pi_s(\omega) < \pi_\rho(\omega)$, there exists $N$ such that for all $n \geq N$, $R_{u_n}(s) < \pi_\rho(\omega)$.
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, R_word (take_word n ω) s < pi rho ω := by
          have h_pi_s_lt_pi_rho : Filter.Tendsto (fun n => R_word (take_word n ω) s) Filter.atTop (nhds (pi s ω)) := by
            convert tendsto_R_word s ⟨ by linarith [ hs.1.1 ], by linarith [ hs.1.2, min_le_right ( rho + ε ) ( 1 / 2 ) ] ⟩ ω using 1;
          exact Filter.eventually_atTop.mp ( h_pi_s_lt_pi_rho.eventually ( gt_mem_nhds ‹_› ) );
        exact ⟨ N, hN N le_rfl, by simpa using pi_lt_R_word_of_not_eventually_one rho hrho ω h_not_ev_one N ⟩;
      -- By the Intermediate Value Theorem, there exists $r \in (\rho, s)$ such that $R_{u_n}(r) = x$.
      obtain ⟨r, hr⟩ : ∃ r ∈ Set.Ioo rho s, R_word (take_word n ω) r = pi rho ω := by
        apply_rules [ intermediate_value_Ioo' ];
        · linarith [ hs.1.1 ];
        · refine ContinuousOn.congr
            ( s := ( Set.Icc rho ( show ℝ from s ) : Set ℝ ) )
            ( f := fun r => pi r (append_ones (take_word n ω)) ) ?_ ?_;
          · refine ContinuousOn.congr
              ( s := ( Set.Icc rho ( show ℝ from s ) : Set ℝ ) )
              ( f := fun r : ℝ =>
                (1 - r) *
                    (∑ k ∈ Finset.range (take_word n ω).length,
                      ((take_word n ω)[k]?).getD 0 * r ^ k) +
                  r ^ (take_word n ω).length ) ?_ ?_;
            · fun_prop;
            · intro r hr; exact (by
              convert pi_append_ones r ⟨ by linarith [ hr.1 ], by linarith [ hr.2, hs.1.2, min_le_left ( rho + ε ) ( 1 / 2 ), min_le_right ( rho + ε ) ( 1 / 2 ) ] ⟩ ( take_word n ω ) using 1);
          · exact fun x hx => rfl;
      -- Since $r \in (\rho, s)$, we have $r \in (\rho, \rho + \varepsilon)$.
      have hr_interval : r ∈ Set.Ioo rho (rho + ε) := by
        exact ⟨ hr.1.1, hr.1.2.trans_le <| hs.1.2.le.trans <| min_le_left _ _ ⟩;
      refine hε.2 r hr_interval ?_;
      rw [ ← hr.2 ];
      -- Since $R_{u_n}(r) = \pi_r(\text{append\_ones}(u_n))$, and $\text{append\_ones}(u_n)$ is a sequence in $\{0,1\}^\infty$, we have $R_{u_n}(r) \in C_r$.
      have h_R_in_C : R_word (take_word n ω) r ∈ Set.range (pi r) := by
        exact ⟨ _, rfl ⟩;
      convert range_pi_subset_C r ⟨ by linarith [ hr.1.1 ], by linarith [ hr.1.2, hs.1.2, min_le_left ( rho + ε ) ( 1 / 2 ), min_le_right ( rho + ε ) ( 1 / 2 ) ] ⟩ h_R_in_C using 1

theorem theorem_minus (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) :
    C_minus rho = C rho \ E_minus rho := by
      -- To prove equality of sets, we show each set is a subset of the other.
      apply Set.ext
      intro x
      simp [C_minus, E_minus];
      constructor;
      · intro hx;
        refine ⟨ ?_, ?_, ?_ ⟩;
        · -- Apply the closedness_limit_Cantor theorem to conclude that x is in C rho.
          apply closedness_limit_Cantor rho hrho (fun i => Classical.choose (hx (1 / (i + 1)) (by positivity))) (by
          exact tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => abs_nonneg _ ) ( fun n => abs_le.mpr ⟨ by linarith [ Classical.choose_spec ( hx ( 1 / ( n + 1 ) ) ( by positivity ) ) ], by linarith [ Classical.choose_spec ( hx ( 1 / ( n + 1 ) ) ( by positivity ) ) ] ⟩ ) <| tendsto_one_div_add_atTop_nhds_zero_nat) x (by
          exact fun n => Classical.choose_spec ( hx ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.2);
        · intro u hu h0 h1 hx_eq
          have h_not_in_C_minus : pi rho (append_zeros u) ∉ C_minus rho := by
            apply not_mem_C_minus_of_L_u rho hrho u hu h0 h1;
          exact h_not_in_C_minus <| hx_eq ▸ Set.mem_iInter₂.mpr fun r hr => by aesop;
        · intro u hu h1 h0 hx_eq
          have h_not_in_C_minus : pi rho (append_ones u) ∉ C_minus rho := by
            apply not_mem_C_minus_of_R_u rho hrho u hu h1 h0;
          exact h_not_in_C_minus <| hx_eq ▸ by
            unfold C_minus; aesop;
      · intro hx i hi
        by_cases hx0 : x = 0 ∨ x = 1;
        · -- Since $x = 0$ or $x = 1$, we can use the fact that $0$ and $1$ are in $C_r$ for any $r$.
          have h_endpoints : ∀ r : ℝ, 0 < r ∧ r < 1 / 2 → 0 ∈ C r ∧ 1 ∈ C r := by
            intros r hr
            have h0 : 0 ∈ C r := by
              apply Set.mem_iInter.mpr;
              intro n; induction n <;> simp_all +decide [ C_n ] ;
              · unfold Sigma_n I_word; norm_num;
                exact ⟨ 0, by norm_num, by unfold f_word; norm_num ⟩;
              · obtain ⟨ u, hu, hu' ⟩ := ‹_›; use 0 :: u; simp_all +decide [ Sigma_n ] ;
                unfold I_word at *; simp_all +decide [ f_word ] ;
                exact ⟨ hu'.choose, hu'.choose_spec.1, by rw [ hu'.choose_spec.2 ] ; unfold f; norm_num ⟩
            have h1 : 1 ∈ C r := by
              have h1 : 1 ∈ C r := by
                have := endpoints_mem_C_plus r hr
                exact C_plus_subset_C r hr this.2;
              exact h1
            exact ⟨h0, h1⟩;
          by_cases hi' : i < 1 / 2 - rho;
          · exact ⟨ rho + i / 2, ⟨ by linarith, by linarith ⟩, by cases hx0 <;> [ exact h_endpoints ( rho + i / 2 ) ⟨ by linarith, by linarith ⟩ |>.1 |> fun h => by aesop; ; exact h_endpoints ( rho + i / 2 ) ⟨ by linarith, by linarith ⟩ |>.2 |> fun h => by aesop ] ⟩;
          · exact ⟨ rho + ( 1 / 2 - rho ) / 2, ⟨ by linarith, by linarith ⟩, by rcases hx0 with ( rfl | rfl ) <;> [ exact h_endpoints _ ⟨ by linarith, by linarith ⟩ |>.1; exact h_endpoints _ ⟨ by linarith, by linarith ⟩ |>.2 ] ⟩;
        · -- Since $x \neq 0$ and $x \neq 1$, we can find a sequence $\omega$ such that $x = \pi_\rho(\omega)$.
          obtain ⟨ω, hω⟩ : ∃ ω : ℕ → Fin 2, x = pi rho ω := by
            have := pi_code_of_mem_C rho hrho x hx.1;
            exact ⟨ _, this.symm ⟩;
          -- Since $\omega$ is not eventually constant, we can apply the lemma `mem_C_minus_of_not_eventually_zero` or `mem_C_minus_of_not_eventually_one`.
          by_cases hω0 : ω 0 = 0;
          · by_cases hω_not_ev_zero : ∀ n, ∃ k ≥ n, ω k ≠ 0;
            · have hω_mem_C_minus : pi rho ω ∈ C_minus rho := by
                apply mem_C_minus_of_not_eventually_zero rho hrho ω hω0 hω_not_ev_zero;
              unfold C_minus at *; aesop;
            · -- Since $\omega$ is eventually zero, we can write $\omega = u0^\infty$ for some $u$.
              obtain ⟨u, hu⟩ : ∃ u : List (Fin 2), ω = fun n => if n < u.length then u[n]! else 0 := by
                push Not at hω_not_ev_zero;
                obtain ⟨ n, hn ⟩ := hω_not_ev_zero; use List.map ω (List.range n); ext m; aesop;
              -- Since $u$ is non-empty and starts with $0$, we have $1 \in u$.
              have hu1 : 1 ∈ u := by
                by_cases hu1 : 1 ∈ u <;> simp_all +decide [ pi ];
                -- Since $u$ contains no $1$s, we have $u = 0^k$ for some $k$.
                obtain ⟨k, hk⟩ : ∃ k : ℕ, u = List.replicate k 0 := by
                  exact ⟨ u.length, List.eq_replicate_of_mem fun x hx => by have := Fin.exists_fin_two.mp ⟨ x, rfl ⟩ ; aesop ⟩;
                simp_all +decide [ tsum_eq_single 0 ];
              contrapose! hx;
              intro hx1 hx2; specialize hx2 u; simp_all +decide
              cases u <;> simp_all +decide
              unfold append_zeros at hx2; simp_all +decide [ pi ] ;
              grind;
          · by_cases hω1 : ω 0 = 1;
            · by_cases hω1 : ∀ n, ∃ k ≥ n, ω k ≠ 1;
              · have hω1 : pi rho ω ∈ C_minus rho := by
                  apply mem_C_minus_of_not_eventually_one rho hrho ω ‹_› hω1;
                unfold C_minus at hω1; aesop;
              · -- Since $\omega$ is eventually constant, we can write $\omega = u1^\infty$ for some $u$.
                obtain ⟨u, hu⟩ : ∃ u : List (Fin 2), ω = fun n => if n < u.length then u[n]! else 1 := by
                  push Not at hω1;
                  obtain ⟨ n, hn ⟩ := hω1; use List.map ω (List.range n); ext m; aesop;
                -- Since $u$ contains a 0, we have $x \in E_\rho^-$.
                have hu0 : 0 ∈ u := by
                  by_cases hu0 : ∀ n < u.length, u[n]! = 1;
                  · have hω_const : ω = fun _ => 1 := by
                      grind;
                    have hω_const : pi rho ω = 1 := by
                      unfold pi; norm_num [ hω_const ] ;
                      rw [ tsum_geometric_of_lt_one ] <;> try linarith;
                      exact mul_inv_cancel₀ ( by linarith );
                    grind +ring;
                  · simp +zetaDelta at *;
                    obtain ⟨ n, hn, hn' ⟩ := hu0; specialize hn' ; rcases h : u[n]? with ( _ | ⟨ x, hx ⟩ ) <;> simp_all +decide ;
                    interval_cases x <;> simp_all +decide;
                    exact List.mem_of_getElem h;
                contrapose! hx;
                intro hx1 hx2; use u; simp_all +decide
                refine ⟨ ?_, ?_, ?_ ⟩;
                · aesop_cat;
                · cases u <;> aesop;
                · congr with n ; simp +decide [ append_ones ] ; aesop;
            · exact False.elim <| hω1 <| Or.resolve_left ( Fin.exists_fin_two.mp <| by tauto ) hω0

/-
Theorem 2.5: Characterization of the one-sided limsup set C_plus.
-/
theorem theorem_plus (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) :
    C_plus rho = C rho \ E_plus rho := by
      refine Set.Subset.antisymm ?_ ?_;
      · intro x hx;
        refine ⟨ ?_, ?_ ⟩;
        · exact C_plus_subset_C rho hrho hx;
        · rintro ⟨ u, hu, hu', rfl ⟩;
          · exact not_mem_C_plus_of_R_u' rho hrho u hu hu' hx;
          · obtain ⟨ u, hu, hu', rfl ⟩ := ‹_›; exact not_mem_C_plus_of_L_u' rho hrho u hu hu' hx;
      · intro x hx;
        obtain ⟨ω, hω⟩ : ∃ ω : ℕ → Fin 2, pi rho ω = x := by
          have := hx.1;
          have := pi_code_of_mem_C rho hrho x this; aesop;
        by_cases h0 : ω 0 = 0;
        · subst hω
          simp_all only [one_div, Fin.isValue, Set.mem_diff]
          obtain ⟨left, right⟩ := hrho
          obtain ⟨left_1, right_1⟩ := hx
          -- Apply the theorem that states if omega starts with 0 and is not eventually 1, then pi(omega) is in C_plus.
          apply mem_C_plus_of_not_eventually_one rho ⟨left, by norm_num at *; linarith⟩ ω h0;
          -- Apply the lemma not_eventually_one_of_mem_diff to conclude that ω is not eventually 1.
          apply not_eventually_one_of_mem_diff rho ⟨left, by norm_num at *; linarith⟩ _ right_1 ω rfl h0
        · by_cases h1 : ω 0 = 1 <;> simp_all +decide [ E_plus ];
          · by_cases h_not_ev_zero : ∃ n, ∀ k ≥ n, ω k = 0;
            · obtain ⟨ n, hn ⟩ := h_not_ev_zero
              have h_eq : x = pi rho (append_zeros (List.ofFn (fun i : Fin n => ω i))) := by
                convert hω.symm using 1;
                congr! 1;
                ext i; by_cases hi : i < n <;> simp_all +decide [ append_zeros ] ;
              rcases n <;> simp_all +decide [ List.ofFn_eq_map ];
              exact False.elim <| hx.2.2 _ ( by aesop ) ( by aesop ) rfl;
            · exact mem_C_plus_of_not_eventually_zero rho ⟨ hrho.1, by norm_num at *; linarith ⟩ ω h1 ( by push Not at h_not_ev_zero; exact h_not_ev_zero ) |> fun h => hω ▸ h;
          · exact False.elim <| h1 <| Or.resolve_left ( Fin.exists_fin_two.mp <| by tauto ) h0

/-
E_plus is a countable set.
-/
lemma countable_E_plus (rho : ℝ) : Set.Countable (E_plus rho) := by
  refine Set.Countable.union ?_ ?_;
  · refine Set.Countable.mono ?_ ( Set.countable_range ( fun u : List ( Fin 2 ) => pi rho ( append_ones u ) ) ) ; aesop_cat;
  · convert Set.countable_range ( fun u : List ( Fin 2 ) => pi rho ( append_zeros u ) ) |> Set.Countable.mono _ using 1 ; aesop_cat;

/-
E_minus is a countable set.
-/
lemma countable_E_minus (rho : ℝ) : Set.Countable (E_minus rho) := by
  apply Set.Countable.union;
  · convert Set.countable_range ( fun u : List ( Fin 2 ) => pi rho ( append_zeros u ) ) |> Set.Countable.mono _ using 1 ; aesop_cat;
  · refine Set.Countable.mono ?_ ( Set.countable_range ( fun u : List ( Fin 2 ) => pi rho ( append_ones u ) ) ) ; aesop_cat;

/-
The closure of C_plus is C.
-/
theorem closure_C_plus (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) :
    closure (C_plus rho) = C rho := by
      -- We show that $C_+^\rho$ is dense in $C^\rho$.
      have h_dense : ∀ x ∈ C rho, ∀ ε > 0, ∃ y ∈ C_plus rho, |y - x| < ε := by
        intro x hx ε hε_pos
        obtain ⟨ω, hω⟩ : ∃ ω : ℕ → Fin 2, pi rho ω = x := by
          have := pi_code_of_mem_C rho hrho x hx; aesop;
        -- Since $C_\alpha$ is the union of $C_\alpha^+$ and $E_\alpha^-$, and $E_\alpha^-$ is countable, there exists a sequence $\{y_n\}$ in $C_\alpha^+$ such that $y_n \to x$.
        obtain ⟨y_n, hy_n⟩ : ∃ y_n : ℕ → (ℕ → Fin 2), (∀ n, pi rho (y_n n) ∈ C_plus rho) ∧ Filter.Tendsto (fun n => pi rho (y_n n)) Filter.atTop (nhds x) := by
          -- Since $E_\alpha^-$ is countable, we can find a sequence $\{y_n\}$ in $C_\alpha^+$ such that $y_n \to \omega$.
          obtain ⟨y_n, hy_n⟩ : ∃ y_n : ℕ → (ℕ → Fin 2), (∀ n, y_n n ∈ {ω : ℕ → Fin 2 | pi rho ω ∈ C_plus rho}) ∧ Filter.Tendsto y_n Filter.atTop (nhds ω) := by
            have h_dense : ∀ ω : ℕ → Fin 2, ∀ n : ℕ, ∃ y : ℕ → Fin 2, y ∈ {ω : ℕ → Fin 2 | pi rho ω ∈ C_plus rho} ∧ ∀ i < n, y i = ω i := by
              intro ω n
              by_cases hω0 : ω 0 = 0 ∨ ω 0 = 1
              generalize_proofs at *; (
              rcases hω0 with hω0 | hω0 <;> [ exact ⟨ _, mem_C_plus_of_not_eventually_one rho hrho ( fun i => if i < n then ω i else 0 ) ( by aesop ) ( by
                exact fun m => ⟨ m + n, by linarith, by simp +decide ⟩ ), fun i hi => by aesop ⟩ ; exact ⟨ _, mem_C_plus_of_not_eventually_zero rho hrho ( fun i => if i < n then ω i else 1 ) ( by aesop ) ( by
                exact fun m => ⟨ m + n, by linarith, by aesop ⟩ ), fun i hi => by aesop ⟩ ]);
              exact False.elim <| hω0 <| Fin.exists_fin_two.mp ⟨ ω 0, rfl ⟩ |> Or.imp ( fun h => by aesop ) fun h => by aesop;
            generalize_proofs at *; (
            choose y hy using h_dense ω
            generalize_proofs at *; (
            exact ⟨ y, fun n => hy n |>.1, tendsto_pi_nhds.mpr fun i => tendsto_const_nhds.congr' <| by filter_upwards [ Filter.eventually_gt_atTop i ] with n hn; aesop ⟩))
          generalize_proofs at *; (
          exact ⟨ y_n, hy_n.1, by simpa only [ ← hω ] using Filter.Tendsto.comp ( continuous_pi' rho hrho |> Continuous.continuousAt ) hy_n.2 ⟩)
        generalize_proofs at *; (
        rcases Metric.tendsto_atTop.mp hy_n.2 ε hε_pos with ⟨ n, hn ⟩ ; exact ⟨ _, hy_n.1 n, hn n le_rfl ⟩ ;);
      refine Set.Subset.antisymm ?_ ?_;
      · -- Since $C^\rho$ is closed, the closure of any subset of $C^\rho$ is also a subset of $C^\rho$.
        have h_closed : IsClosed (C rho) := by
          convert isClosed_C rho hrho using 1;
        exact h_closed.closure_subset_iff.mpr ( C_plus_subset_C rho hrho );
      · exact fun x hx => Metric.mem_closure_iff.2 fun ε hε => by obtain ⟨ y, hy, hy' ⟩ := h_dense x hx ε hε; exact ⟨ y, hy, by simpa [ abs_sub_comm ] using hy' ⟩ ;

/-
The closure of C_minus is C.
-/
theorem closure_C_minus (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) :
    closure (C_minus rho) = C rho := by
      -- To show the reverse inclusion, take any $x \in C_\alpha$ and let $U$ be an open neighborhood of $x$ in $C_\alpha$.
      have h_reverse : ∀ x ∈ C rho, ∀ U : Set ℝ, IsOpen U → x ∈ U → ∃ y ∈ U, y ∈ C_minus rho := by
        intro x hx U hU hxU
        obtain ⟨ω, hω⟩ : ∃ ω : ℕ → Fin 2, pi rho ω = x := by
          exact ⟨ code_of_mem_C rho hrho x hx, pi_code_of_mem_C rho hrho x hx ⟩;
        -- Since $\pi_\rho^{-1}(U)$ is open in $\Sigma$, it contains a nonempty open set.
        obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ ω' : ℕ → Fin 2, (∀ i < n, ω' i = ω i) → pi rho ω' ∈ U := by
          have h_preimage_open : IsOpen (Set.preimage (pi rho) U) := by
            exact hU.preimage ( continuous_pi' rho hrho );
          rw [ isOpen_pi_iff ] at h_preimage_open;
          obtain ⟨ I, u, hu₁, hu₂ ⟩ := h_preimage_open ω ( by aesop );
          use I.sup id + 1;
          intro ω' hω'; specialize hu₂ ( show ω' ∈ ( I : Set ℕ ).pi u from fun i hi => by have := hω' i ( Nat.lt_succ_of_le ( Finset.le_sup ( f := id ) hi ) ) ; aesop ) ; aesop;
        -- Consider the set of sequences $\omega'$ that agree with $\omega$ on the first $n$ coordinates.
        set S := {ω' : ℕ → Fin 2 | ∀ i < n, ω' i = ω i} with hS_def;
        -- Since $S$ is uncountable, there exists a sequence $\omega' \in S$ such that $\omega'$ is not eventually $0$ or $1$.
        obtain ⟨ω', hω'_S, hω'_not_eventually⟩ : ∃ ω' ∈ S, (∀ n, ∃ k ≥ n, ω' k ≠ 0) ∧ (∀ n, ∃ k ≥ n, ω' k ≠ 1) := by
          -- Define a sequence ω' that agrees with ω on the first n coordinates and then alternates between 0 and 1.
          use fun i => if i < n then ω i else if i % 2 = 0 then 0 else 1;
          exact ⟨ fun i hi => if_pos hi, fun m => ⟨ 2 * m + 2 * n + 1, by linarith, by simp +arith +decide [ Nat.add_mod ] ⟩, fun m => ⟨ 2 * m + 2 * n, by linarith, by simp +arith +decide [ Nat.add_mod ] ⟩ ⟩;
        -- Since $\omega'$ is not eventually $0$ or $1$, we have $\pi_\rho(\omega') \in C_\alpha^-$.
        have h_pi_omega'_in_C_minus : pi rho ω' ∈ C_minus rho := by
          by_cases h0 : ω' 0 = 0;
          · exact mem_C_minus_of_not_eventually_zero rho hrho ω' h0 hω'_not_eventually.1;
          · apply mem_C_minus_of_not_eventually_one rho hrho ω' (by
            exact Or.resolve_left ( Fin.exists_fin_two.mp ( by tauto ) ) h0) (by
            exact hω'_not_eventually.2);
        exact ⟨ _, hn ω' hω'_S, h_pi_omega'_in_C_minus ⟩;
      refine Set.Subset.antisymm ?_ ?_;
      · refine closure_minimal ?_ ( isClosed_C rho hrho );
        intro x hx
        rw [theorem_minus rho hrho] at hx
        aesop;
      · intro x hx
        exact mem_closure_iff_nhds_basis (nhds_basis_opens x) |>.2 (by
        exact fun U hU => by obtain ⟨ y, hy₁, hy₂ ⟩ := h_reverse x hx U hU.2 hU.1; exact ⟨ y, hy₂, hy₁ ⟩ ;)

/-
Hausdorff dimension of C_plus is s.
-/
lemma dimH_C_plus (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) :
    let s := Real.log 2 / -Real.log rho
    dimH (C_plus rho) = ENNReal.ofReal s := by
      refine le_antisymm ?_ ?_;
      · refine le_trans ?_ ( theorem_dimension_Ca rho hrho |>.1.le );
        apply_rules [ dimH_mono, C_plus_subset_C ];
      · -- Since $C_\alpha^+ \subseteq C_\alpha$, we have $\dim_H(C_\alpha^+) \ge \dim_H(C_\alpha)$.
        have h_dim_ge : dimH (C_plus rho) ≥ dimH (C rho) := by
          -- Since $E_plus rho$ is countable, its Hausdorff dimension is 0.
          have h_E_plus_zero : dimH (E_plus rho) = 0 := by
            -- Since $E_plus rho$ is countable, its Hausdorff dimension is 0 by the theorem `dimH_countable`.
            apply dimH_countable; exact countable_E_plus rho;
          have h_subset : C rho ⊆ C_plus rho ∪ E_plus rho := by
            intro x hx; if h : x ∈ E_plus rho then exact Or.inr h else exact Or.inl (by
            exact Classical.not_not.1 fun hx' => h <| by have := theorem_plus rho hrho; rw [ Set.ext_iff ] at this; specialize this x; aesop;);
          refine le_trans ( dimH_mono h_subset ) ?_;
          simp +decide [ *, dimH_union ];
        exact le_trans ( by rw [ theorem_dimension_Ca rho hrho |>.1 ] ) h_dim_ge

/-
Hausdorff dimension of C_minus is s.
-/
lemma dimH_C_minus (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) :
    let s := Real.log 2 / -Real.log rho
    dimH (C_minus rho) = ENNReal.ofReal s := by
      have h_eq : C rho = C_minus rho ∪ (C rho ∩ E_minus rho) := by
        rw [ theorem_minus rho hrho ];
        ext x; by_cases hx : x ∈ E_minus rho <;> aesop;
      -- Since $E_\rho^-$ is countable, $\dim_H(E_\rho^-) = 0$.
      have h_countable : dimH (C rho ∩ E_minus rho) = 0 := by
        have h_countable : Set.Countable (C rho ∩ E_minus rho) := by
          exact Set.Countable.mono ( fun x hx => hx.2 ) ( countable_E_minus rho )
        generalize_proofs at *; (
        exact Set.Countable.dimH_zero h_countable);
      -- Since $C_\alpha = C_\alpha^- \cup (C_\alpha \cap E_\rho^-)$ and $\dim_H(E_\rho^-) = 0$, we have $\dim_H(C_\alpha) \le \dim_H(C_\alpha^-)$.
      have h_le : dimH (C rho) ≤ dimH (C_minus rho) := by
        rw [ h_eq ];
        rw [ dimH_union ] ; norm_num [ h_countable ];
      have h_ge : dimH (C_minus rho) ≤ dimH (C rho) := by
        apply_rules [ dimH_mono ];
        exact fun x hx => h_eq.symm.subset <| Or.inl hx
      exact le_antisymm (by
      exact h_ge.trans ( by simpa using theorem_dimension_Ca rho hrho |>.1.le )) (by
      exact le_trans ( by exact ( theorem_dimension_Ca rho hrho ) |>.1.ge ) h_le |> le_trans <| le_rfl;)

/-
Corollary 2.8: Dimensions of the one-sided limsup sets.
-/
theorem corollary_dimensions_limsup (rho : ℝ) (hrho : 0 < rho ∧ rho < 1 / 2) :
    let s := Real.log 2 / -Real.log rho
    dimH (C_plus rho) = ENNReal.ofReal s ∧
    dimH (C_minus rho) = ENNReal.ofReal s ∧
    lower_box_dim (C_plus rho) = s ∧
    upper_box_dim (C_plus rho) = s ∧
    lower_box_dim (C_minus rho) = s ∧
    upper_box_dim (C_minus rho) = s := by
      refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
      · exact dimH_C_plus rho hrho;
      · exact dimH_C_minus rho hrho;
      · rw [ lem_closure_box _ |>.1, closure_C_plus _ hrho ] ; exact theorem_dimension_Ca _ hrho |>.2.1;
      · have h_closure : upper_box_dim (C_plus rho) = upper_box_dim (C rho) := by
          convert lem_closure_box ( C_plus rho ) |> And.right using 1;
          · rw [ closure_C_plus rho hrho ];
        rw [ h_closure, theorem_dimension_Ca rho hrho |>.2.2 ];
      · -- By `lem_closure_box`, we have `lower_box_dim (C_minus rho) = lower_box_dim (closure (C_minus rho))` and `upper_box_dim (C_minus rho) = upper_box_dim (closure (C_minus rho))`.
        have h_closure_box : lower_box_dim (C_minus rho) = lower_box_dim (C rho) ∧ upper_box_dim (C_minus rho) = upper_box_dim (C rho) := by
          rw [ ← closure_C_minus rho hrho ];
          apply lem_closure_box
        have := theorem_dimension_Ca rho hrho; aesop;

end MO509164

open MO509164

#print axioms theorem_plus
-- 'MO509164.theorem_plus' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms theorem_minus
-- 'MO509164.theorem_minus' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms corollary_dimensions_limsup
-- 'MO509164.corollary_dimensions_limsup' depends on axioms: [propext, Classical.choice, Quot.sound]
