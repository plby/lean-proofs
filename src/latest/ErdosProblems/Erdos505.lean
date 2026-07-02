/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 505.
https://www.erdosproblems.com/forum/thread/505

Informal authors:
- Jeff Kahn
- Gil Kalai

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos505.md
-/
/-
This file formalizes a counterexample to Borsuk's conjecture in dimension 946,
following the paper "A self-contained Kahn--Kalai type counterexample to Borsuk's
conjecture". It defines the Borsuk number, constructs the specific finite set in
dimension 946, and proves that its Borsuk number is at least 1650, contradicting
the conjecture that f(d) = d + 1.
-/

import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos505

open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-
Let $E\subset \RR^d$ be bounded. Its \emph{diameter} is
$\diam(E)\coloneqq \sup\{\norm{x-y}: x,y\in E\}$.
-/
noncomputable def diam {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  sSup {dist x y | (x ∈ E) (y ∈ E)}

/-
Let $E\subset \RR^d$ be bounded and let $\lambda>0$. Then
$\diam(\lambda E)=\lambda\,\diam(E)$, where
$\lambda E\coloneqq\{\lambda x:x\in E\}$.
-/
theorem diam_scaling {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) (c : ℝ) (hc : 0 < c) :
    diam (c • E) = c * diam E := by
      unfold diam;
      rw [ ← smul_eq_mul, ← Real.sSup_smul_of_nonneg hc.le ];
      -- Notice that $c • {dist x y | (x ∈ E) (y ∈ E)}$ is the set of all
      -- distances between points in $c • E$.
      have h_dist :
          {dist x y | (x ∈ c • E) (y ∈ c • E)} =
            c • {dist x y | (x ∈ E) (y ∈ E)} := by
        ext; simp [Set.mem_smul_set, dist_eq_norm];
        simp +decide only [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc];
      grind

/-
For $d\ge 1$, let $f(d)$ be the least integer $m$ such that every bounded set
$E\subset \RR^d$ with $\diam(E)=1$ has a partition
$E = E_1\sqcup \cdots \sqcup E_m$ with $\diam(E_i)<1$ for all $i$.
-/
def BorsukProperty (d m : ℕ) : Prop :=
  ∀ (E : Set (EuclideanSpace ℝ (Fin d))), Bornology.IsBounded E → diam E = 1 →
    ∃ (c : E → Fin m), ∀ (i : Fin m),
      diam {x : EuclideanSpace ℝ (Fin d) |
        ∃ (h : x ∈ E), c ⟨x, h⟩ = i} < 1

/-
For $d\ge 1$, let $f(d)$ be the least integer $m$ such that every bounded set
$E\subset \RR^d$ with $\diam(E)=1$ has a partition
$E = E_1\sqcup \cdots \sqcup E_m$ with $\diam(E_i)<1$ for all $i$.
-/
noncomputable def BorsukNumber (d : ℕ) : ℕ :=
  sInf {m | BorsukProperty d m}

/-
The assertion $f(d)=d+1$ for all $d\ge 1$ is called \emph{Borsuk's conjecture}.
-/
def BorsukConjecture : Prop :=
  ∀ (d : ℕ), d ≥ 1 → BorsukNumber d = d + 1

/-
Let $M \coloneqq \Bigl\{x=(x_1,\dots,x_n)\in\{\pm 1\}^n : x_1=1,\ \prod_{i=1}^n x_i = 1\Bigr\}$.
-/
def M (n : ℕ) [NeZero n] : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, x i = 1 ∨ x i = -1) ∧ x 0 = 1 ∧ ∏ i, x i = 1}

/-
The set of pairs $(i,j)$ with $1\le i<j\le n$.
-/
def Pairs (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-
Define $\Phi\colon M\to \RR^d$ by $\Phi(x)\coloneqq (x_i x_j)_{1\le i<j\le n}$.
-/
def Phi {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Pairs n) :=
  WithLp.toLp 2 fun p : Pairs n =>
    show (fun _ : Pairs n => ℝ) p from x p.val.1 * x p.val.2

/-
Let $X\coloneqq \Phi(M)\subset \RR^d$.
-/
def X (n : ℕ) [NeZero n] : Set (EuclideanSpace ℝ (Pairs n)) :=
  Phi '' (M n)

/-
The set of vectors in $\{\pm 1\}^k$ with product 1.
-/
def SignVectorsProdOne (k : ℕ) : Set (Fin k → ℝ) :=
  {x | (∀ i, x i = 1 ∨ x i = -1) ∧ ∏ i, x i = 1}

/-
The set of vectors in $\{\pm 1\}^m$ has cardinality $2^m$.
-/
def SignVectors (m : ℕ) : Set (Fin m → ℝ) :=
  {x | ∀ i, x i = 1 ∨ x i = -1}

theorem card_SignVectors (m : ℕ) : Set.ncard (SignVectors m) = 2^m := by
  let e : SignVectors m ≃ (Fin m → Fin 2) :=
  { toFun := fun (x : SignVectors m) => fun i => if x.1 i = 1 then 0 else 1
    invFun := fun y =>
      ⟨fun i => if y i = 0 then (1 : ℝ) else -1,
        by
          intro i
          by_cases h : y i = 0
          · simp [h]
          · right
            simp [h]⟩
    left_inv := by
      intro x
      ext i
      rcases x.2 i with h | h
      · norm_num [h]
      · have hne : ¬x.1 i = 1 := by linarith
        norm_num [h, hne]
    right_inv := by
      intro y
      ext i
      by_cases h : y i = 0
      · simp [h]
      · have : y i = 1 := by omega
        norm_num [this] }
  calc
    Set.ncard (SignVectors m) = Nat.card (SignVectors m) := rfl
    _ = Nat.card (Fin m → Fin 2) := Nat.card_congr e
    _ = 2 ^ m := by simp [Nat.card_eq_fintype_card]
/-
There is a bijection between `SignVectorsProdOne (n + 1)` and `SignVectors n`.
-/
def SignVectorsProdOneEquiv (n : ℕ) : SignVectorsProdOne (n + 1) ≃ SignVectors n :=
  { toFun := fun x => ⟨fun i => x.1 (i.castSucc), fun i => (x.2.1 (i.castSucc))⟩
    invFun := fun y => ⟨Fin.snoc y.1 (∏ i, y.1 i), by
      refine ⟨ ?_, ?_ ⟩;
      · intro i; refine Fin.lastCases ?_ ?_ i <;> simp +decide [ Fin.snoc, * ] ;
        · exact eq_or_eq_neg_of_abs_eq (by
            rw [Finset.abs_prod]
            exact Finset.prod_eq_one fun i _ => by
              cases y.2 i <;> aesop);
        · exact y.2;
      · simp +decide [ Fin.prod_univ_castSucc, Fin.snoc ];
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun i _ => by
          rcases y.2 i with h | h <;> norm_num [h];⟩
    left_inv := by
      intro x; ext i; induction i using Fin.lastCases <;> simp_all +decide [ Fin.snoc ] ;
      have := x.2.2; simp_all +decide [ Fin.prod_univ_castSucc ] ;
      rcases eq_or_eq_neg_of_abs_eq
          (show |(x : Fin (n + 1) → ℝ) (Fin.last n)| = 1 from by
            have := x.2.1 (Fin.last n)
            aesop)
          with h | h <;>
        simp_all +decide [mul_comm];
      linarith
    right_inv := by
      intro x; aesop }

/-
The number of vectors in $\{\pm 1\}^k$ with product 1 is $2^{k-1}$.
-/
theorem card_SignVectorsProdOne (k : ℕ) (hk : k ≥ 1) :
    Set.ncard (SignVectorsProdOne k) = 2^(k-1) := by
  rcases k with ⟨ _ | _ | k ⟩ <;> simp_all +decide
  convert card_SignVectors _ using 1;
  rw [ Set.ncard_def, Set.ncard_def, Set.encard_congr ];
  (expose_names; exact SignVectorsProdOneEquiv n)

/-
Map from `M (n + 1)` to `SignVectorsProdOne n`.
-/
def M_to_SignVectorsProdOne (n : ℕ) (x : M (n + 1)) : SignVectorsProdOne n :=
  ⟨fun i => x.1 (i.succ), by
    -- Since $x \in M (n + 1)$, we know that $x$ is a vector in
    -- $\{\pm 1\}^{n+1}$ with the first component $1$ and the product of all
    -- components $1$.
    obtain ⟨hx_bounds, hx_first, hx_prod⟩ := x.2;
    -- Since $x \in M (n + 1)$, we know that $x$ is a vector in
    -- $\{\pm 1\}^{n+1}$ with the first component $1$ and the product of all
    -- components $1$. Therefore, the product of the components from $1$ to
    -- $n$ is also $1$.
    have h_prod : ∏ i : Fin n, (x.val (Fin.succ i)) = 1 := by
      rw [ Fin.prod_univ_succ ] at hx_prod ; aesop;
    exact ⟨ fun i => hx_bounds _, h_prod ⟩⟩

/-
Map from `SignVectorsProdOne n` to `M (n + 1)`.
-/
def SignVectorsProdOne_to_M (n : ℕ) (y : SignVectorsProdOne n) : M (n + 1) :=
  ⟨WithLp.toLp 2 fun i : Fin (n + 1) =>
      show (fun _ : Fin (n + 1) => ℝ) i from Fin.cases 1 y.1 i, by
    refine ⟨ ?_, ?_ ⟩;
    · intro i; refine Fin.cases ?_ ?_ i <;> simp +decide [ * ] ;
      exact y.2.1;
    · simp +decide [ Fin.prod_univ_succ, y.2.2 ]⟩

/-
There is a bijection between `M (n + 1)` and `SignVectorsProdOne n`.
-/
def M_equiv_SignVectorsProdOne (n : ℕ) : M (n + 1) ≃ SignVectorsProdOne n :=
  { toFun := M_to_SignVectorsProdOne n
    invFun := SignVectorsProdOne_to_M n
    left_inv := by
      -- By definition of `M_to_SignVectorsProdOne` and
      -- `SignVectorsProdOne_to_M`, we can show that they are inverses of each
      -- other.
      intros x
      simp [M_to_SignVectorsProdOne, SignVectorsProdOne_to_M];
      congr ; ext i ; induction i using Fin.inductionOn <;> simp +decide [ * ];
      exact Eq.symm ( x.2.2.1 )
    right_inv := by
      intro y; ext i; simp [M_to_SignVectorsProdOne, SignVectorsProdOne_to_M] }

/-
One has $|M|=2^{n-2}$.
-/
theorem card_M (n : ℕ) [NeZero n] (hn : n ≥ 2) : Set.ncard (M n) = 2^(n-2) := by
  rcases n with _ | _ | n
  · exact False.elim (NeZero.ne 0 rfl)
  · omega
  · change Set.ncard (M (n + 2)) = 2 ^ n
    calc
      Set.ncard (M (n + 2)) = Set.ncard (SignVectorsProdOne (n + 1)) := by
        rw [Set.ncard_def, Set.ncard_def, Set.encard_congr]
        exact M_equiv_SignVectorsProdOne (n + 1)
      _ = 2 ^ n := by simpa using card_SignVectorsProdOne (n + 1) (by omega)
/-
`Pairs n` is a finite type.
-/
instance (n : ℕ) : Fintype (Pairs n) :=
  inferInstanceAs (Fintype {p : Fin n × Fin n // p.1 < p.2})

/-
For $x,y\in M$ one has $\norm{\Phi(x)-\Phi(y)}^2 \;=\; n^2 - \ip{x}{y}^2$.
-/
theorem distance_formula
    (n : ℕ) [NeZero n] (hn : n ≥ 2)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M n) (hy : y ∈ M n) :
    norm (Phi x - Phi y) ^ 2 = (n : ℝ)^2 - (inner ℝ x y) ^ 2 := by
      -- By definition of $Phi$, we know that $\|Phi(x) - Phi(y)\|^2 =
      -- \sum_{1 \leq i < j \leq n} (x_i x_j - y_i y_j)^2$.
      have h_norm_sq :
          ‖Phi x - Phi y‖ ^ 2 =
            ∑ p : Fin n × Fin n,
              (if p.1 < p.2 then
                (x p.1 * x p.2 - y p.1 * y p.2) ^ 2
              else 0) := by
        simp +decide [ Finset.sum_ite, sq ];
        rw [ ← sq, ← real_inner_self_eq_norm_sq ];
        erw [ Finset.sum_subtype ];
        all_goals first | exact rfl | aesop
      -- Expanding the sum, we can rewrite it as
      -- $\sum_{1 \leq i < j \leq n} (x_i x_j - y_i y_j)^2 =
      -- \sum_{1 \leq i < j \leq n} (2 - 2 x_i y_i x_j y_j)$.
      have h_expand :
          (∑ p : Fin n × Fin n,
            (if p.1 < p.2 then
              (x p.1 * x p.2 - y p.1 * y p.2) ^ 2
            else 0)) =
            ∑ p : Fin n × Fin n,
              (if p.1 < p.2 then
                2 - 2 * (x p.1 * y p.1) * (x p.2 * y p.2)
              else 0) := by
        -- Since $x_i$ and $y_i$ are either $1$ or $-1$, we have $x_i^2 = 1$
        -- and $y_i^2 = 1$ for all $i$.
        have h_sq : ∀ i : Fin n, x i ^ 2 = 1 ∧ y i ^ 2 = 1 := by
          exact fun i =>
            ⟨by
              rcases hx.1 i with ha | ha <;> rw [ha] <;> norm_num,
             by
              rcases hy.1 i with hb | hb <;> rw [hb] <;> norm_num⟩;
        exact Finset.sum_congr rfl fun p hp => by
          split_ifs <;> nlinarith only [h_sq p.1, h_sq p.2]
      -- The sum of the squares of the differences can be rewritten using the
      -- identity $\sum_{1 \leq i < j \leq n} (u_i u_j) =
      -- \frac{1}{2} \left( \left( \sum_{i=1}^n u_i \right)^2 -
      -- \sum_{i=1}^n u_i^2 \right)$.
      have h_identity :
          (∑ p : Fin n × Fin n,
            (if p.1 < p.2 then
              (x p.1 * y p.1) * (x p.2 * y p.2)
            else 0)) =
            (1 / 2) * ((∑ i : Fin n, x i * y i) ^ 2 -
              ∑ i : Fin n, (x i * y i) ^ 2) := by
        erw [ Finset.sum_product ] ; norm_num [ Finset.sum_ite, Finset.filter_lt_eq_Ioi ] ; ring_nf;
        clear h_norm_sq h_expand hx hy;
        induction hn <;> simp +decide [ Fin.sum_univ_succ, * ]
        · ring
        rename_i k hk ih;
        have htail := ih
          (WithLp.toLp 2 fun i : Fin k => x (Fin.succ i))
          (WithLp.toLp 2 fun i : Fin k => y (Fin.succ i))
        rw [show
            (∑ i : Fin k, x 0 * y 0 * x (Fin.succ i) * y (Fin.succ i)) =
              x 0 * y 0 * ∑ i : Fin k, x (Fin.succ i) * y (Fin.succ i) by
          rw [Finset.mul_sum _ _ _]
          exact Finset.sum_congr rfl fun _ _ => by ring];
        rw [htail]
        ring;
      -- Since $\sum_{i=1}^n u_i^2 = n$ for $u_i = x_i y_i$, we can simplify the expression.
      have h_sum_squares : ∑ i : Fin n, (x i * y i) ^ 2 = n := by
        have h_sum_squares : ∀ i : Fin n, (x i * y i) ^ 2 = 1 := by
          intro i
          rcases hx.1 i with ha | ha <;> rcases hy.1 i with hb | hb <;>
            norm_num [ha, hb]
        simpa [mul_pow] using
          Finset.sum_congr rfl fun i (hi : i ∈ Finset.univ) => h_sum_squares i
      -- The number of pairs $(i, j)$ with $1 \leq i < j \leq n$ is
      -- $\binom{n}{2} = \frac{n(n-1)}{2}$.
      have h_num_pairs :
          ∑ p : Fin n × Fin n, (if p.1 < p.2 then 1 else 0) = n * (n - 1) / 2 := by
        convert Finset.sum_range_id n using 1;
        erw [ Finset.sum_product ] ; simp +decide [ Finset.filter_lt_eq_Ioi ];
        rw [ ← Finset.sum_range_reflect, Finset.sum_range ];
      norm_num [ Finset.sum_ite ] at *;
      simp_all +decide [ ← Finset.mul_sum _ _ _, mul_assoc ];
      cases n <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ] at * ; ring_nf;
      norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul, inner ]

/-
There exist $x,y\in M$ with $\ip{x}{y}=0$.
-/
theorem exists_orthogonal_pair (n : ℕ) [NeZero n] (p : ℕ) (hp : n = 4 * p) :
    ∃ x y, x ∈ M n ∧ y ∈ M n ∧ inner ℝ x y = 0 := by
      -- Define the chosen vector $\tilde{y}$ by setting the first $2p$ entries
      -- to 1 and the remaining $2p$ entries to -1.
      obtain ⟨y, hy⟩ : ∃ y : M n, ∑ i : Fin n, y.1 i = 0 := by
        -- Define the chosen vector $\tilde{y}$ by setting the first $2p$
        -- entries to 1 and the remaining $2p$ entries to -1. This vector is in
        -- $M$.
        obtain ⟨y, hy⟩ :
            ∃ y : Fin n → ℝ,
              (∀ i, y i = 1 ∨ y i = -1) ∧ y 0 = 1 ∧
                ∏ i, y i = 1 ∧ ∑ i, y i = 0 := by
          -- Let's choose $y$ such that $y_1 = 1$ and exactly $2p$ of the
          -- coordinates $y_2, \ldots, y_n$ are $-1$. We can construct such a
          -- vector by setting $y_i = -1$ for $2p$ indices and $y_i = 1$ for the
          -- remaining indices.
          obtain ⟨s, hs⟩ : ∃ s : Finset (Fin n), s.card = 2 * p ∧ 0 ∉ s := by
            use Finset.univ.filter (fun i => i.val < 2 * p + 1 ∧ i.val ≠ 0);
            rw [ Finset.card_eq_of_bijective ];
            rotate_right;
            · exact 2 * p
            all_goals norm_num at *;
            · use fun i hi => ⟨ i + 1, by linarith ⟩
            · exact fun a ha ha' =>
                ⟨a - 1,
                  by
                    rw [tsub_lt_iff_left] <;>
                    linarith [Fin.is_lt a,
                      show (a : ℕ) > 0 from
                        Nat.pos_of_ne_zero fun h => ha' <| Fin.ext h],
                  by
                    rcases a with ⟨_ | a, ha⟩ <;> aesop⟩;
            · exact fun i hi => ⟨ Nat.succ_le_of_lt hi, ne_of_gt ( Nat.succ_pos _ ) ⟩;
            · aesop;
          use fun i => if i ∈ s then -1 else 1;
          simp_all +decide [ Finset.sum_ite ];
          norm_num [ Finset.filter_not, Finset.card_sdiff, hs ];
          exact
            ⟨fun i => by tauto,
              by
                rw [Nat.cast_sub (by linarith)]
                push_cast [hp]
                ring⟩;
        exact
          ⟨⟨WithLp.toLp 2 y,
              by simpa [M] using ⟨hy.1, hy.2.1, hy.2.2.1⟩⟩,
            by simpa using hy.2.2.2⟩;
      refine
        ⟨WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ)),
          (y : EuclideanSpace ℝ (Fin n)), ?_, ?_, ?_⟩ <;>
        simp_all +decide [M];
      convert hy using 1;
      norm_num [ inner ]

/-
General definition of diameter for any finite index type.
-/
noncomputable def diam_general {ι : Type*} [Fintype ι] (E : Set (EuclideanSpace ℝ ι)) : ℝ :=
  sSup {dist x y | (x ∈ E) (y ∈ E)}

/-
One has $\diam(X)=n$.
-/
theorem diam_X (n : ℕ) [NeZero n] (p : ℕ) (hp : n = 4 * p) (hp_odd : Odd p) :
    diam_general (X n) = n := by
      refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ ?_ <;> norm_num;
      · exact
          ⟨_, ⟨_,
              Set.mem_image_of_mem _
                (Classical.choose_spec
                  (Set.nonempty_of_ncard_ne_zero
                    (by
                      rw [card_M n (by linarith [hp_odd.pos])]
                      positivity))),
              _,
              Set.mem_image_of_mem _
                (Classical.choose_spec
                  (Set.nonempty_of_ncard_ne_zero
                    (by
                      rw [card_M n (by linarith [hp_odd.pos])]
                      positivity))),
              rfl⟩⟩;
      · rintro a x ⟨ y, hy, rfl ⟩ z ⟨ w, hw, rfl ⟩ rfl;
        have := distance_formula n
          (show n ≥ 2 from by
            linarith [show p > 0 from Nat.pos_of_ne_zero (by aesop_cat)])
          y w hy hw;
        exact le_trans (Real.le_sqrt_of_sq_le this.le)
          (Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩);
      · intro w hw
        obtain ⟨x, y, hxM, hyM, hxy⟩ :
            ∃ x y : EuclideanSpace ℝ (Fin n),
              x ∈ M n ∧ y ∈ M n ∧ inner ℝ x y = 0 := by
          exact exists_orthogonal_pair n p hp;
        -- By Proposition~\ref{prop:distance}, for $x,y\in M$,
        -- \[
        -- \norm{\Phi(x)-\Phi(y)}^2 = n^2-\ip{x}{y}^2 \le n^2,
        -- \]
        -- so $\diam(X)\le n$. By Lemma~\ref{lem:orthpair}, there exist
        -- $x,y\in M$ with $\ip{x}{y}=0$, and then Proposition~\ref{prop:distance}
        -- gives $\norm{\Phi(x)-\Phi(y)}=n$, so $\diam(X)\ge n$.
        have h_dist : norm (Phi x - Phi y) = n := by
          have := distance_formula n
            (show 2 ≤ n from by
              linarith [NeZero.pos n,
                show p > 0 from Nat.pos_of_ne_zero (by aesop_cat)])
            x y hxM hyM
          aesop
        exact
          ⟨_, Set.mem_image_of_mem _ hxM, _, Set.mem_image_of_mem _ hyM,
            by simpa only [dist_eq_norm] using hw.trans_le h_dist.ge⟩

/-
Let $Y\subseteq X$. If $\diam(Y)<\diam(X)=n$, then for all distinct
$x,y\in \Phi^{-1}(Y)\subseteq M$ one has $\ip{x}{y}\ne 0$.
-/
theorem small_diam_implies_no_orthogonal_pairs
    (n : ℕ) [NeZero n] (p : ℕ) (hp : n = 4 * p) (hp_odd : Odd p)
    (Y : Set (EuclideanSpace ℝ (Pairs n))) (hY : Y ⊆ X n)
    (hdiam : diam_general Y < diam_general (X n)) :
    ∀ x y, x ∈ M n → y ∈ M n → Phi x ∈ Y → Phi y ∈ Y → x ≠ y →
      inner ℝ x y ≠ 0 := by
      intro x y hx hy hxY hyY hxy hxy_inner
      have h_dist : norm (Phi x - Phi y) = n := by
        have := distance_formula n
          (show 2 ≤ n from by
            linarith [show p > 0 from Nat.pos_of_ne_zero (by aesop_cat)])
          x y hx hy
        aesop
      -- Since $\Phi(x)$ and $\Phi(y)$ are in $Y$, we have $\norm{\Phi(x) - \Phi(y)} \leq \diam(Y)$.
      have h_le_diam : norm (Phi x - Phi y) ≤ diam_general Y := by
        refine le_csSup ?_ ?_;
        · -- Since $Y$ is a subset of $X$ and $X$ is bounded, $Y$ is also bounded.
          have hY_bounded : Bornology.IsBounded Y := by
            have hY_bounded : Bornology.IsBounded (X n) := by
              have h_finite : Set.Finite (M n) := by
                have h_finite : Set.ncard (M n) = 2^(n-2) := by
                  convert card_M n ( show n ≥ 2 by linarith [ hp_odd.pos ] ) using 1;
                exact Set.finite_of_ncard_pos ( h_finite.symm ▸ pow_pos ( by decide ) _ );
              exact Set.Finite.isBounded (h_finite.image _) |> fun h =>
                h.subset (Set.image_mono <| Set.Subset.refl _);
            exact hY_bounded.subset hY;
          obtain ⟨ M, hM ⟩ := hY_bounded.exists_pos_norm_le;
          exact
            ⟨2 * M, by
              rintro _ ⟨x, hx, y, hy, rfl⟩
              exact le_trans (dist_le_norm_add_norm _ _)
                (by linarith [hM.2 x hx, hM.2 y hy])⟩;
        · exact ⟨ _, hxY, _, hyY, rfl ⟩;
      linarith [ show diam_general ( X n ) = n by exact_mod_cast diam_X n p hp hp_odd ]

/-
For $x,y\in M$, the integer $\ip{x}{y}$ is divisible by $4$.
-/
theorem inner_divisible_by_four
    (n : ℕ) [NeZero n] (p : ℕ) (hp : n = 4 * p)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M n) (hy : y ∈ M n) :
    ∃ k : ℤ, inner ℝ x y = 4 * k := by
      -- Let $u_i = x_i y_i$. Then $u_i \in \{\pm 1\}$ and $\prod_{i=1}^n u_i = 1$.
      set u : Fin n → ℝ := fun i => x i * y i
      have hu_bounds : ∀ i, u i = 1 ∨ u i = -1 := by
        intro i
        rcases hx.1 i with ha | ha <;> rcases hy.1 i with hb | hb <;>
          norm_num [u, ha, hb]
      have hu_prod : ∏ i, u i = 1 := by
        rw [ Finset.prod_mul_distrib, hx.2.2, hy.2.2, mul_one ];
      -- Since $\prod_{i=1}^n u_i = 1$, the number of indices $i$ with $u_i = -1$ is even, say $2t$.
      obtain ⟨t, ht⟩ : ∃ t : ℕ, (∑ i, if u i = -1 then 1 else 0) = 2 * t := by
        -- Since $\prod_{i=1}^n u_i = 1$, the number of indices $i$ with $u_i = -1$ is even.
        have h_prod_count : (∏ i, u i) = (-1) ^ (∑ i, if u i = -1 then 1 else 0) := by
          rw [← Finset.prod_pow_eq_pow_sum]
          exact Finset.prod_congr rfl fun i _ => by
            rcases hu_bounds i with h | h <;> norm_num [h];
        have h_even_neg : Even (∑ i : Fin n, if u i = -1 then 1 else 0) := by
          refine (neg_one_pow_eq_one_iff_even (R := ℝ) (by norm_num)).mp ?_
          rw [← h_prod_count, hu_prod]
        rcases h_even_neg with ⟨t, ht⟩
        exact ⟨t, by simpa [two_mul] using ht⟩
      -- Then $\ip{x}{y} = \sum_{i=1}^n u_i = (n - 2t) - (2t) =
      -- n - 4t$, which is divisible by $4$ since $n = 4p$.
      have h_inner : inner ℝ x y = n - 4 * t := by
        have h_inner : ∑ i, u i = n - 4 * t := by
          have h_indicator :
              (∑ i : Fin n, (if u i = -1 then (1 : ℝ) else 0)) = (2 * t : ℝ) := by
            exact_mod_cast ht
          calc
            ∑ i, u i = ∑ i : Fin n, (1 - 2 * (if u i = -1 then (1 : ℝ) else 0)) := by
              exact Finset.sum_congr rfl fun i _ => by
                rcases hu_bounds i with h | h <;> norm_num [h]
            _ = (∑ i : Fin n, (1 : ℝ)) -
                ∑ i : Fin n, 2 * (if u i = -1 then (1 : ℝ) else 0) := by
              rw [Finset.sum_sub_distrib]
            _ = (∑ i : Fin n, (1 : ℝ)) -
                2 * ∑ i : Fin n, (if u i = -1 then (1 : ℝ) else 0) := by
              rw [Finset.mul_sum]
            _ = n - 4 * t := by
              rw [h_indicator]
              simp
              ring
        rw [show inner ℝ x y = ∑ i, u i by
          rw [PiLp.inner_apply]
          exact Finset.sum_congr rfl fun i _ => by
            change y i * x i = u i
            simp [u, mul_comm]]
        exact h_inner
      exact ⟨ (p : ℤ) - t, by
        rw [h_inner]
        subst n
        norm_num
        ring ⟩

/-
Let $x,y\in M$ be distinct. If $\ip{x}{y}\ne 0$, then $\ip{x}{y}\not\equiv 0 \pmod p$.
-/
theorem inner_not_divisible_by_p
    (n : ℕ) [NeZero n] (p : ℕ) (hp : n = 4 * p) (hp_odd : Odd p)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M n) (hy : y ∈ M n)
    (h_neq : x ≠ y) (h_nonzero : inner ℝ x y ≠ 0)
    (k : ℤ) (hk : inner ℝ x y = k) : ¬ (p : ℤ) ∣ k := by
      -- Since $\ip{x}{y} \neq 0$, we have $\ip{x}{y} = 4(p - t)$ for some integer $t$.
      obtain ⟨t, ht⟩ : ∃ t : ℤ, inner ℝ x y = 4 * (p - t) := by
        obtain ⟨ t, ht ⟩ := inner_divisible_by_four n p hp x y hx hy;
        exact ⟨ p - t, by push_cast; linarith ⟩;
      -- Since $x \ne y$, at least one coordinate differs, so $t \ge 1$. Also
      -- $u_1=1$ in the proof of Lemma~\ref{lem:dotmod4}, hence at least one
      -- $u_i=+1$, so the number $2t$ of $-1$ entries among $(u_i)$ satisfies
      -- $2t\le n-2$, i.e.\ $t\le 2p-1$.
      have ht_bounds : 1 ≤ t ∧ t ≤ 2 * p - 1 := by
        -- Since $x \ne y$, at least one coordinate differs, so $t \ge 1$.
        -- Also $u_1=1$ in the proof of Lemma~\ref{lem:dotmod4}, hence at
        -- least one $u_i=+1$, so the number $2t$ of $-1$ entries among $(u_i)$
        -- satisfies $2t\le n-2$, i.e.\ $t\le 2p-1$. Therefore, $t$ is an
        -- integer between $1$ and $2p-1$.
        have ht_bounds : 0 ≤ t ∧ t ≤ 2 * p := by
          have ht_bounds : |inner ℝ x y| ≤ n := by
            have h_inner_bound :
                ∀ x y : EuclideanSpace ℝ (Fin n),
                  (∀ i, x i = 1 ∨ x i = -1) →
                  (∀ i, y i = 1 ∨ y i = -1) → |inner ℝ x y| ≤ n := by
              intros x y hx hy
              rw [abs_le]
              constructor <;>
                norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _,
                  Finset.sum_mul _ _ _, inner];
              · exact le_trans (by norm_num)
                  (Finset.sum_le_sum fun i _ =>
                    show y i * x i ≥ -1 by
                      cases hx i <;> cases hy i <;> nlinarith);
              · exact le_trans
                  (Finset.sum_le_sum fun i _ =>
                    show y i * x i ≤ 1 by
                      cases hx i <;> cases hy i <;> nlinarith)
                  (by norm_num);
            exact h_inner_bound x y hx.1 hy.1;
          constructor <;> push_cast [← @Int.cast_le ℝ] <;>
            linarith [abs_le.mp ht_bounds,
              show (n : ℝ) = 4 * p by exact_mod_cast hp];
        rcases lt_or_eq_of_le ht_bounds.1 with ht_pos | ht_zero
        · rcases lt_or_eq_of_le ht_bounds.2 with ht_lt_top | ht_top
          · exact ⟨ by linarith, by linarith ⟩;
          · -- Since $x$ and $y$ are distinct, their inner product cannot be $-4p$.
            have h_inner_ne_neg_4p : inner ℝ x y ≠ -4 * p := by
              have h_inner_ne_neg_4p : inner ℝ x y = -4 * p → x = -y := by
                intro h_inner_eq_neg_4p
                have h_inner_eq_neg_4p : ∑ i, (x i + y i) ^ 2 = 0 := by
                  have h_inner_eq_neg_4p :
                      ∑ i, (x i + y i) ^ 2 =
                        ∑ i, x i ^ 2 + ∑ i, y i ^ 2 + 2 * ∑ i, x i * y i := by
                    simp +decide only [add_sq', mul_assoc, Finset.sum_add_distrib,
                                          Finset.mul_sum _ _ _];
                  have h_inner_eq_neg_4p : ∑ i, x i ^ 2 = n ∧ ∑ i, y i ^ 2 = n := by
                    have h_inner_eq_neg_4p : ∀ i, x i ^ 2 = 1 ∧ y i ^ 2 = 1 := by
                      exact fun i =>
                        ⟨by
                          rcases hx.1 i with ha | ha <;> norm_num [ha],
                         by
                          rcases hy.1 i with hb | hb <;> norm_num [hb]⟩;
                    simp [h_inner_eq_neg_4p];
                  simp_all +decide [ mul_comm, mul_left_comm, inner ];
                  ring;
                rw [ Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _ ] at h_inner_eq_neg_4p;
                ext i
                have hi := h_inner_eq_neg_4p i (by simp)
                have hxyi : x i + y i = 0 := sq_eq_zero_iff.mp hi
                simpa using eq_neg_of_add_eq_zero_left hxyi
              intro h; specialize h_inner_ne_neg_4p h; simp_all +decide
              have := hx.2.1; have := hy.2.1; simp_all +decide [ neg_eq_iff_add_eq_zero ] ;
            exact False.elim <| h_inner_ne_neg_4p ( by rw [ht, ht_top]; norm_num; ring );
        · norm_num [ ← ht_zero ] at *;
          -- Since $x$ and $y$ are distinct elements of $M$, their inner
          -- product $\ip{x}{y}$ cannot be equal to $n$.
          have h_inner_ne_n :
              ∀ x y : EuclideanSpace ℝ (Fin n), x ∈ M n → y ∈ M n →
                x ≠ y → inner ℝ x y ≠ n := by
            intros x y hx hy hxy
            have h_inner_eq_n : inner ℝ x y = n → x = y := by
              intro h_inner_eq_n
              have h_norm_eq : ‖x - y‖ = 0 := by
                have h_norm_eq : ‖x - y‖^2 = ‖x‖^2 + ‖y‖^2 - 2 * inner ℝ x y := by
                  rw [ @norm_sub_sq ℝ ];
                  norm_num ; ring;
                have h_norm_eq : ‖x‖^2 = n ∧ ‖y‖^2 = n := by
                  simp_all +decide [EuclideanSpace.norm_eq,
                    Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _];
                  have h_norm_eq :
                      ∀ x : EuclideanSpace ℝ (Fin n), x ∈ M n →
                        ∑ i, x i ^ 2 = n := by
                    intro x hx; exact (by
                    exact Eq.trans
                      (Finset.sum_congr rfl fun i _ => by
                        rcases hx.1 i with h | h
                        · rw [h]
                        · rw [h]
                          norm_num)
                      (by norm_num));
                  aesop;
                nlinarith;
              exact sub_eq_zero.mp <| norm_eq_zero.mp h_norm_eq;
            exact fun h => hxy <| h_inner_eq_n h;
          exact False.elim <| h_inner_ne_n x y hx hy h_neq ( by norm_num [ hp ] ; linarith );
      -- Since $p$ is odd, $p \mid 4(p - t)$ implies $p \mid (p - t)$.
      by_contra h_div
      have h_div_pt : (p : ℤ) ∣ (p - t) := by
        have h_div_pt : (p : ℤ) ∣ 4 * (p - t) := by
          have hk4 : k = 4 * (p - t) := by
            exact_mod_cast (by rw [← hk, ht] : (k : ℝ) = 4 * (p - t))
          simpa [hk4] using h_div
        refine Int.dvd_of_dvd_mul_right_of_gcd_one h_div_pt ?_;
        rcases hp_odd with ⟨ m, rfl ⟩ ; norm_num [ Int.gcd, Int.natAbs ];
        rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩ <;> ring_nf <;> norm_num;
      obtain ⟨ a, ha ⟩ := h_div_pt
      have hp_pos_int : (0 : ℤ) < p := by exact_mod_cast hp_odd.pos
      have ht_eq_p : t = p := by
        rcases lt_trichotomy a 0 with ha_neg | rfl | ha_pos
        · have : 2 * (p : ℤ) ≤ t := by nlinarith
          linarith [ht_bounds.2]
        · linarith
        · have : t ≤ 0 := by nlinarith [mul_pos hp_pos_int ha_pos]
          linarith [ht_bounds.1]
      have h_inner_zero : inner ℝ x y = 0 := by
        rw [ht, ht_eq_p]
        norm_num
      exact h_nonzero h_inner_zero

/-
Define $\mathrm{ml}(P)\in \FF_p[z_2,\dots,z_n]$ by linear extension of the
rule $\mathrm{ml}\!\left(\prod_{i=2}^n z_i^{e_i}\right) \coloneqq
\prod_{i=2}^n z_i^{\,e_i \bmod 2}$.
-/
noncomputable def ml {σ : Type*} {R : Type*} [CommRing R]
    (P : MvPolynomial σ R) : MvPolynomial σ R :=
  Finsupp.mapDomain (fun e => Finsupp.mapRange (fun n => n % 2) (by simp) e) P

/-
Let $b=(b_2,\dots,b_n)\in \{\pm 1\}^{n-1}\subset \FF_p^{n-1}$. Then for
every $P\in \FF_p[z_2,\dots,z_n]$, $P(b)=\mathrm{ml}(P)(b)$.
-/
theorem ml_eval_eq {σ : Type*} {R : Type*} [CommRing R]
    (P : MvPolynomial σ R) (b : σ → R) (hb : ∀ i, b i ^ 2 = 1) :
    MvPolynomial.eval b P = MvPolynomial.eval b (ml P) := by
      let f : (σ →₀ ℕ) → (σ →₀ ℕ) :=
        fun e => Finsupp.mapRange (fun n => n % 2) (by simp) e
      change (MvPolynomial.eval₂Hom (RingHom.id R) b) P =
        (MvPolynomial.eval₂Hom (RingHom.id R) b) (Finsupp.mapDomain f P)
      rw [← Finsupp.sum_single P]
      rw [Finsupp.mapDomain_sum]
      simp only [Finsupp.mapDomain_single]
      simp only [Finsupp.sum]
      change (MvPolynomial.eval₂Hom (RingHom.id R) b)
          (∑ a ∈ P.support, MvPolynomial.monomial a (P a)) =
        (MvPolynomial.eval₂Hom (RingHom.id R) b)
          (∑ a ∈ P.support, MvPolynomial.monomial (f a) (P a))
      rw [map_sum, map_sum]
      simp only [MvPolynomial.eval₂Hom_monomial]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [RingHom.id_apply]
      congr 1
      dsimp [f]
      rw [Finsupp.prod_mapRange_index]
      · apply Finsupp.prod_congr
        intro i hi
        rw [← Nat.mod_add_div (x i) 2]
        simp [pow_add, pow_mul, hb i]
      · intro a
        simp

variable {σ : Type*} {R : Type*} [CommRing R] (c : R) (p : MvPolynomial σ R)

/-
The submodule of multilinear polynomials.
-/
def MultilinearPolynomials (σ : Type*) (R : Type*) [CommRing R] :
    Submodule R (MvPolynomial σ R) where
  carrier := {p | ∀ n, MvPolynomial.degreeOf n p ≤ 1}
  add_mem' := by
    -- By definition of degree, for any monomial in a + b, its degree is at most 1.
    intros a b ha hb n
    have h_deg :
        MvPolynomial.degreeOf n (a + b) ≤
          max (MvPolynomial.degreeOf n a) (MvPolynomial.degreeOf n b) := by
      exact MvPolynomial.degreeOf_add_le n a b;
    exact h_deg.trans ( max_le ( ha n ) ( hb n ) )
  zero_mem' := by
    -- The degree of the zero polynomial is 0, which is less than or equal to 1.
    simp [MvPolynomial.degreeOf]
  smul_mem' := by
    simp +decide [ MvPolynomial.degreeOf_eq_sup ];
    exact fun c x hx n b hc => hx n b ( by aesop )

/-
The subspace of multilinear polynomials of total degree at most $k$.
-/
noncomputable def MultilinearPolynomialsOfDegreeLE
    (σ : Type*) (R : Type*) [CommRing R] (k : ℕ) :
    Submodule R (MvPolynomial σ R) :=
  MultilinearPolynomials σ R ⊓ MvPolynomial.restrictTotalDegree σ R k

/-
Let $k\ge 0$. The $\FF_p$-vector space of multilinear polynomials in
$z_2,\dots,z_n$ of total degree at most $k$ has dimension
$\sum_{j=0}^{k} \binom{n-1}{j}$.
-/
set_option maxHeartbeats 1000000 in
-- The finrank computation proof times out at the default heartbeat limit.
theorem dim_multilinear_polynomials
    (n : ℕ) [NeZero n] (p : ℕ) [Fact (Nat.Prime p)] (hp : n = 4 * p)
    (k : ℕ) :
    Module.finrank (ZMod p)
        (MultilinearPolynomialsOfDegreeLE (Fin (n - 1)) (ZMod p) k) =
      ∑ j ∈ Finset.range (k + 1), (n - 1).choose j := by
      -- Let's define the set of monomials of total degree at most $k$.
      set Monomials :=
        {m : (Fin (n - 1)) →₀ ℕ |
          m.sum (fun _ e => e) ≤ k ∧ ∀ i, m i ≤ 1} with hMonomials_def;
      -- The set of monomials of total degree at most $k$ is in bijection with
      -- the set of subsets of $\{2, \ldots, n\}$ of size at most $k$.
      have h_bij :
          Monomials =
            Finset.image
              (fun S : Finset (Fin (n - 1)) =>
                S.sum (fun i => Finsupp.single i 1))
              (Finset.filter (fun S => S.card ≤ k)
                (Finset.powerset (Finset.univ : Finset (Fin (n - 1))))) := by
        ext m; simp [Monomials];
        constructor <;> intro h;
        · refine
            ⟨Finset.univ.filter fun i => m i = 1, ?_, ?_⟩ <;>
              simp_all +decide [Finsupp.sum_fintype];
          · exact le_trans
              (by
                rw [Finset.card_filter]
                exact le_trans
                  (Finset.sum_le_sum fun _ _ =>
                    show (m _ : ℕ) ≥ if m _ = 1 then 1 else 0 by
                      cases m ‹_› <;> aesop)
                  (by aesop))
              h.1;
          · ext i; simp [Finsupp.single_apply];
            grind;
        · rcases h with ⟨ x, hx₁, rfl ⟩
          simp +decide [← Finsupp.sum_finsetSum_index, hx₁];
          intro i; by_cases hi : i ∈ x <;> simp +decide [ hi, Finsupp.single_apply ] ;
      -- Therefore, the dimension of the space of multilinear polynomials of
      -- total degree at most $k$ is equal to the cardinality of the set of
      -- subsets of $\{2, \ldots, n\}$ of size at most $k$.
      have h_dim :
          Module.finrank (ZMod p)
              (↥(MultilinearPolynomialsOfDegreeLE (Fin (n - 1)) (ZMod p) k)) =
            Finset.card
              (Finset.filter (fun S => S.card ≤ k)
                (Finset.powerset (Finset.univ : Finset (Fin (n - 1))))) := by
        -- The space of multilinear polynomials of total degree at most $k$ is
        -- spanned by the monomials in $Monomials$.
        have h_span :
            MultilinearPolynomialsOfDegreeLE (Fin (n - 1)) (ZMod p) k =
              Submodule.span (ZMod p)
                (Set.image
                  (fun m : (Fin (n - 1)) →₀ ℕ => MvPolynomial.monomial m 1)
                  Monomials) := by
          refine le_antisymm ?_ ?_ <;> intro x hx <;>
            simp_all +decide [MultilinearPolynomialsOfDegreeLE];
          · -- Since $x$ is in the submodule spanned by the monomials in
            -- $Monomials$, we can write $x$ as a linear combination of these
            -- monomials.
            have h_comb : x = ∑ m ∈ x.support, x.coeff m • MvPolynomial.monomial m 1 := by
              conv_lhs => rw [ x.as_sum ] ; simp +decide [ MvPolynomial.monomial_eq ] ; ring_nf;
              simp +decide [ MvPolynomial.monomial_eq ] ; congr ; ext ; ring_nf;
              simp +decide [ MvPolynomial.smul_eq_C_mul ];
            rw [h_comb];
            refine Submodule.sum_mem _ ?_;
            intro m hm
            refine Submodule.smul_mem _ _
              (Submodule.subset_span <| Set.mem_image_of_mem _ ?_)
            simp +decide
            refine ⟨ ?_, ?_ ⟩ <;>
              simp +decide [MvPolynomial.mem_restrictTotalDegree] at hx ⊢;
            · refine le_trans ?_ hx.2;
              exact
                (Finset.le_sup
                    (f := fun s => Finsupp.sum s fun x e => e)
                    (MvPolynomial.mem_support_iff.mpr <|
                      show x.coeff m ≠ 0 from by simpa using hm)) |>
                  le_trans (by simp +decide [Finsupp.sum_fintype]);
            · intro i; have := hx.1 i; simp +decide [ MvPolynomial.degreeOf_eq_sup ] at this;
              exact this m ( by simpa using hm );
          · refine Submodule.span_induction ?_ ?_ ?_ ?_ hx <;>
              simp +decide [MultilinearPolynomials];
            · rintro x m hm₁ hm₂ rfl; simp_all +decide [ MvPolynomial.degreeOf_eq_sup ] ;
              simp_all +decide [ MvPolynomial.mem_restrictTotalDegree ];
            · intro x y hx hy hx' hx'' hy' hy''
              refine ⟨ ?_, ?_ ⟩ <;> simp_all +decide [MvPolynomial.degreeOf_eq_sup];
              · grind;
              · exact Submodule.add_mem _ hx'' hy'';
            · intro a x hx hx' hx''
              simp_all +decide [MvPolynomial.degreeOf_eq_sup,
                MvPolynomial.mem_restrictTotalDegree];
              exact le_trans ( MvPolynomial.totalDegree_smul_le _ _ ) hx'';
        rw [ h_span, h_bij ];
        rw [ Set.image_eq_range ];
        rw [ @finrank_span_eq_card ];
        · simp +zetaDelta at *;
          rw [ Finset.card_image_of_injective ];
          intro S T h_eq
          ext i
          replace h_eq := congr_arg (fun f => f i) h_eq
          simp_all +decide [Finsupp.single_apply];
          grind;
        · refine Fintype.linearIndependent_iff.2 ?_;
          intro g hg i
          replace hg :=
            congr_arg (fun f => MvPolynomial.coeff (i : Fin (n - 1) →₀ ℕ) f) hg
          simp_all +decide [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial];
      rw [h_dim,
        show
            Finset.filter (fun S => Finset.card S ≤ k)
              (Finset.powerset (Finset.univ : Finset (Fin (n - 1)))) =
              Finset.biUnion (Finset.range (k + 1)) fun j =>
                Finset.powersetCard j (Finset.univ : Finset (Fin (n - 1))) from ?_,
        Finset.card_biUnion];
      · simp +decide [ Finset.card_univ ];
      · exact fun i hi j hj hij =>
          Finset.disjoint_left.mpr fun x hx₁ hx₂ =>
            hij <| by
              rw [Finset.mem_powersetCard] at hx₁ hx₂
              aesop;
      · ext; simp [Finset.mem_biUnion, Finset.mem_powersetCard]

/-
Define $G(t)\coloneqq t^{p-1}-1\in \FF_p[t]$.
-/
noncomputable def G (p : ℕ) : Polynomial (ZMod p) :=
  Polynomial.X ^ (p - 1) - 1

/-
Map from $\mathbb{R}$ to $\mathbb{F}_p$ sending $1 \mapsto 1$ and $-1 \mapsto -1$.
-/
noncomputable def toZMod (p : ℕ) (x : ℝ) : ZMod p :=
  if x = 1 then 1 else if x = -1 then -1 else 0

/-
Define $L_a(z_2,\dots,z_n)\coloneqq a_1 + \sum_{i=2}^n a_i z_i
\in \FF_p[z_2,\dots,z_n]$.
-/
noncomputable def La
    (n : ℕ) [NeZero n] (p : ℕ) (a : EuclideanSpace ℝ (Fin n)) :
    MvPolynomial (Fin (n - 1)) (ZMod p) :=
  MvPolynomial.C (toZMod p (a 0)) +
    ∑ i : Fin (n - 1),
      MvPolynomial.C
          (toZMod p (a (Fin.cast (Nat.sub_add_cancel (NeZero.pos n)) i.succ))) *
        MvPolynomial.X i

/-
Define $P_a(z_2,\dots,z_n)\coloneqq G\!\bigl(L_a(z_2,\dots,z_n)\bigr)
\in \FF_p[z_2,\dots,z_n]$.
-/
noncomputable def Pa
    (n : ℕ) [NeZero n] (p : ℕ) (a : EuclideanSpace ℝ (Fin n)) :
    MvPolynomial (Fin (n - 1)) (ZMod p) :=
  Polynomial.aeval (La n p a) (G p)

/-
Define $F_a\coloneqq \mathrm{ml}(P_a)$.
-/
noncomputable def Fa
    (n : ℕ) [NeZero n] (p : ℕ) [Fact (Nat.Prime p)]
    (a : EuclideanSpace ℝ (Fin n)) :
    MvPolynomial (Fin (n - 1)) (ZMod p) :=
  ml (Pa n p a)

/-
For any polynomial $P$, $\mathrm{ml}(P)$ is multilinear.
-/
theorem ml_is_multilinear {σ : Type*} {R : Type*} [CommRing R] (P : MvPolynomial σ R) :
    ml P ∈ MultilinearPolynomials σ R := by
      intro n;
      -- Let $m$ be the exponent of $n$ in $P$. Then $m \leq \deg_n P$.
      have h_deg : ∀ m ∈ MvPolynomial.support (ml P), m n ≤ 1 := by
        intro m hm;
        -- Since $m$ is in the support of $ml P$, there exists some monomial in
        -- $P$ whose exponent vector, when taken modulo 2, equals $m$.
        obtain ⟨m', hm', hm_eq⟩ :
            ∃ m' ∈ MvPolynomial.support P,
              m = Finsupp.mapRange (fun n => n % 2) (by simp) m' := by
          have h_support :
              ∀ m, m ∈ (ml P).support → ∃ m' ∈ P.support,
                m = Finsupp.mapRange (fun n => n % 2) (by simp) m' := by
            intro m hm
            simp [ml] at hm;
            rw [ Finsupp.mapDomain ] at hm;
            simp_all +decide [ MvPolynomial.coeff ];
            contrapose! hm;
            exact Finset.sum_eq_zero fun x hx => by specialize hm x; aesop;
          exact h_support m hm;
        exact hm_eq.symm ▸ Nat.le_of_lt_succ ( Nat.mod_lt _ ( by decide ) );
      rw [ MvPolynomial.degreeOf_eq_sup ] ; aesop;

/-
The total degree of $L_a$ is at most 1.
-/
theorem La_degree_le_one (n : ℕ) [NeZero n] (p : ℕ) (a : EuclideanSpace ℝ (Fin n)) :
    MvPolynomial.totalDegree (La n p a) ≤ 1 := by
      refine le_trans ( MvPolynomial.totalDegree_add _ _ ) ?_;
      simp +decide [ MvPolynomial.totalDegree ];
      intro b hb
      contrapose! hb
      simp_all +decide [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_X'];
      rw [ Finset.sum_eq_zero ] ; aesop

/-
The total degree of $P_a$ is at most $p-1$.
-/
theorem Pa_degree_le
    (n : ℕ) [NeZero n] (p : ℕ) [Fact (Nat.Prime p)]
    (a : EuclideanSpace ℝ (Fin n)) :
    MvPolynomial.totalDegree (Pa n p a) ≤ p - 1 := by
      -- Apply the degree_le_one lemma to La.
      have hLa_deg : (La n p a).totalDegree ≤ 1 := by
        exact La_degree_le_one n p a;
      -- The total degree of $G$ is $p-1$.
      have hG_deg : (G p).degree ≤ (p - 1 : ℕ) := by
        erw [Polynomial.degree_sub_eq_left_of_degree_lt] <;>
          simp +decide [Nat.sub_pos_of_lt (show 1 < p from Fact.out)];
      -- Apply the lemma that the total degree of a polynomial modulo a prime
      -- is less than or equal to the total degree of the polynomial.
      have hP_deg : (Polynomial.aeval (La n p a) (G p)).totalDegree ≤ (G p).natDegree := by
        rw [ Polynomial.aeval_eq_sum_range ];
        -- The total degree of a sum of polynomials is less than or equal to
        -- the maximum total degree of the summands.
        have h_sum_deg :
            ∀ (s : Finset ℕ) (f : ℕ → MvPolynomial (Fin (n - 1)) (ZMod p)),
              (∀ i ∈ s, (f i).totalDegree ≤ (G p).natDegree) →
              (∑ i ∈ s, f i).totalDegree ≤ (G p).natDegree := by
          exact fun s f a => MvPolynomial.totalDegree_finsetSum_le a;
        convert h_sum_deg _ _ _ using 2;
        intro i hi;
        refine le_trans ( MvPolynomial.totalDegree_smul_le _ _ ) ?_;
        refine le_trans ( MvPolynomial.totalDegree_pow _ _ ) ?_;
        exact le_trans (Nat.mul_le_mul_left _ hLa_deg)
          (by
            linarith [Finset.mem_range.mp hi,
              Polynomial.natDegree_le_of_degree_le hG_deg]);
      exact hP_deg.trans ( Polynomial.natDegree_le_of_degree_le hG_deg )

/-
Projection of a vector $b$ to its last $n-1$ coordinates modulo $p$.
-/
noncomputable def proj_b
    (n : ℕ) [NeZero n] (p : ℕ) (b : EuclideanSpace ℝ (Fin n)) :
    Fin (n - 1) → ZMod p :=
  fun i => toZMod p (b (Fin.cast (Nat.sub_add_cancel (NeZero.pos n)) i.succ))


/-
$L_a(b) = \langle a, b \rangle$ in $\mathbb{F}_p$.
-/
theorem eval_La_eq_inner
    (n : ℕ) [NeZero n] (p : ℕ) (a b : EuclideanSpace ℝ (Fin n))
    (ha : a ∈ M n) (hb : b ∈ M n) :
    MvPolynomial.eval (proj_b n p b) (La n p a) = (round (inner ℝ a b) : ZMod p) := by
      unfold La;
      rcases n with _ | n0 <;> simp_all +decide [ Inner.inner ];
      · exact False.elim <| NeZero.ne 0 rfl;
      · unfold toZMod proj_b; simp +decide [ ha.2.1 ] ;
        unfold toZMod; simp +decide [ Fin.sum_univ_succ, ha.2.1, hb.2.1 ] ;
        field_simp;
        rw [show
            (1 + ∑ x : Fin _, b x.succ * a x.succ : ℝ) =
              (1 + ∑ x : Fin _,
                if a x.succ = 1 then
                  if b x.succ = 1 then 1 else if b x.succ = -1 then -1 else 0
                else if a x.succ = -1 then
                  -(if b x.succ = 1 then 1 else if b x.succ = -1 then -1 else 0)
                else 0) from ?_];
        · norm_cast
          erw [round_intCast]
          change (MvPolynomial.eval
              (fun i : Fin (n0 + 1 - 1) =>
                (((if b i.succ = 1 then 1
                    else if b i.succ = ((Int.negSucc 0 : ℤ) : ℝ) then Int.negSucc 0
                    else 0) : ℤ) :
                  ZMod p))
              ((MvPolynomial.C (1 : ZMod p) :
                  MvPolynomial (Fin (n0 + 1 - 1)) (ZMod p)) +
                ∑ x : Fin (n0 + 1 - 1),
                  (MvPolynomial.C
                    ((((if a x.succ = 1 then 1
                        else if a x.succ = ((Int.negSucc 0 : ℤ) : ℝ) then Int.negSucc 0
                        else 0) :
                      ℤ) : ZMod p)) :
                    MvPolynomial (Fin (n0 + 1 - 1)) (ZMod p)) *
                    MvPolynomial.X x) =
            _)
          rw [MvPolynomial.eval_add]
          rw [MvPolynomial.eval_sum]
          rw [MvPolynomial.eval_C]
          push_cast
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
          rcases ha.1 x.succ with ha' | ha' <;>
            rcases hb.1 x.succ with hb' | hb' <;>
            simp_all
        · congr! 2;
          rcases ha.1 (Fin.succ ‹_›) with ha' | ha' <;>
            rcases hb.1 (Fin.succ ‹_›) with hb' | hb' <;>
            norm_num [ha', hb']

/-
For $a \in M$, $F_a(a) = -1$.
-/
theorem eval_Fa_self (n : ℕ) [NeZero n] (p : ℕ) [Fact (Nat.Prime p)] (hp : n = 4 * p)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ M n) :
    MvPolynomial.eval (proj_b n p a) (Fa n p a) = -1 := by
      have h_Fa_a :
          MvPolynomial.eval (proj_b n p a) (Fa n p a) =
            Polynomial.eval (round (inner ℝ a a) : ZMod p) (G p) := by
        have h_Fa_def :
            MvPolynomial.eval (proj_b n p a) (Fa n p a) =
              MvPolynomial.eval (proj_b n p a) (ml (Pa n p a)) := by
          rfl
        have h_ml_def :
            MvPolynomial.eval (proj_b n p a) (ml (Pa n p a)) =
              MvPolynomial.eval (proj_b n p a) (Pa n p a) := by
          apply Eq.symm
          apply ml_eval_eq
          intro i
          simp [proj_b]
          rcases ha.1 (Fin.cast (Nat.sub_add_cancel (NeZero.pos n)) i.succ)
            with h | h <;> norm_num [h, toZMod]
        rw [h_Fa_def, h_ml_def, Pa]
        rw [← eval_La_eq_inner]
        · induction (G p) using Polynomial.induction_on' with
          | add p q hp hq => simp_all +decide [Polynomial.aeval_def]
          | monomial n b => simp_all +decide [Polynomial.aeval_def]
        · exact ha
        · exact ha
      have h_inner : inner ℝ a a = n := by
        rw [PiLp.inner_apply]
        trans ∑ i : Fin n, (1 : ℝ)
        · apply Finset.sum_congr rfl
          intro i hi
          rcases ha.1 i with h | h <;> norm_num [h]
        · norm_num
      rw [h_Fa_a, h_inner, hp]
      have hp_one_lt : 1 < p := Nat.Prime.one_lt Fact.out
      have hround : ((round (4 * (p : ℝ)) : ℤ) : ZMod p) = 0 := by
        have hcast : (4 * (p : ℝ)) = ((4 * (p : ℤ) : ℤ) : ℝ) := by norm_num
        rw [hcast, round_intCast]
        norm_num
      simp [G, hround, Nat.sub_ne_zero_of_lt hp_one_lt]
/-
For distinct $a, b \in M$ with $\langle a, b \rangle \ne 0$, $F_a(b) = 0$.
-/
theorem eval_Fa_of_ne
    (n : ℕ) [NeZero n] (p : ℕ) [Fact (Nat.Prime p)] (hp : n = 4 * p)
    (hp_odd : Odd p)
    (a b : EuclideanSpace ℝ (Fin n)) (ha : a ∈ M n) (hb : b ∈ M n)
    (h_neq : a ≠ b) (h_inner : inner ℝ a b ≠ 0) :
    MvPolynomial.eval (proj_b n p b) (Fa n p a) = 0 := by
      -- By Lemma 3.3, $F_a(b) = G(\langle a, b \rangle)$.
      have h_Fa_b :
          MvPolynomial.eval (proj_b n p b) (Fa n p a) =
            Polynomial.eval (round (inner ℝ a b) : ZMod p) (G p) := by
        -- By definition of $F_a$, we have $F_a(b) = \mathrm{ml}(P_a)(b)$.
        have h_Fa_def :
            MvPolynomial.eval (proj_b n p b) (Fa n p a) =
              MvPolynomial.eval (proj_b n p b) (ml (Pa n p a)) := by
          rfl;
        -- By definition of $ml$, we have $ml(P_a)(b) = P_a(b)$.
        have h_ml_def :
            MvPolynomial.eval (proj_b n p b) (ml (Pa n p a)) =
              MvPolynomial.eval (proj_b n p b) (Pa n p a) := by
          apply Eq.symm; exact (by
            have h_eval_eq :
                ∀ (P : MvPolynomial (Fin (n - 1)) (ZMod p))
                  (b : Fin (n - 1) → ZMod p), (∀ i, b i ^ 2 = 1) →
                  MvPolynomial.eval b P = MvPolynomial.eval b (ml P) := by
              exact fun P b a => ml_eval_eq P b a
            apply h_eval_eq; intro i; simp [proj_b];
            rcases hb.1 (Fin.cast (Nat.sub_add_cancel (NeZero.pos n)) i.succ)
              with h | h <;> norm_num [h, toZMod]
          );
        rw [ h_Fa_def, h_ml_def, Pa ];
        rw [ ← eval_La_eq_inner ];
        · induction (G p) using Polynomial.induction_on' with
          | add p q hp hq => simp_all +decide [Polynomial.aeval_def]
          | monomial n b => simp_all +decide [Polynomial.aeval_def]
        · assumption;
        · assumption;
      -- By Lemma 3.2, $\langle a, b \rangle \not\equiv 0 \pmod p$.
      have h_inner_not_zero : ¬(p : ℤ) ∣ round (inner ℝ a b) := by
        convert inner_not_divisible_by_p n p hp hp_odd a b ha hb h_neq h_inner
            (round (inner ℝ a b)) _;
        -- Since $a$ and $b$ are in $M$, their inner product is an integer.
        have h_inner_int : ∃ k : ℤ, inner ℝ a b = k := by
          obtain ⟨ k, hk ⟩ := inner_divisible_by_four n p hp a b ha hb;
          exact ⟨ 4 * k, by simpa using hk ⟩;
        aesop;
      simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, G ];
      rw [ sub_eq_zero, ZMod.pow_card_sub_one_eq_one h_inner_not_zero ]

/-
The total degree of `ml(P)` is at most the total degree of `P`.
-/
theorem totalDegree_ml_le {σ : Type*} {R : Type*} [CommRing R] (P : MvPolynomial σ R) :
    MvPolynomial.totalDegree (ml P) ≤ MvPolynomial.totalDegree P := by
      rw [MvPolynomial.totalDegree]
      refine Finset.sup_le_iff.mpr ?_
      intro m hm
      obtain ⟨m', hm', hm_eq⟩ :
          ∃ m' ∈ MvPolynomial.support P,
            m = Finsupp.mapRange (fun n => n % 2) (by simp) m' := by
        have h_support :
            ∀ m, m ∈ (ml P).support → ∃ m' ∈ P.support,
              m = Finsupp.mapRange (fun n => n % 2) (by simp) m' := by
          intro m hm
          simp [ml] at hm
          rw [Finsupp.mapDomain] at hm
          simp_all +decide [MvPolynomial.coeff]
          contrapose! hm
          exact Finset.sum_eq_zero fun x hx => by specialize hm x; aesop
        exact h_support m hm
      rw [hm_eq]
      refine le_trans ?_ (Finset.le_sup hm')
      rw [Finsupp.sum_mapRange_index (fun _ => rfl)]
      exact Finsupp.sum_le_sum fun i _ => Nat.mod_le _ _
/-
$F_a$ lies in the subspace of multilinear polynomials of degree at most $p-1$.
-/
theorem Fa_mem_subspace
    (n : ℕ) [NeZero n] (p : ℕ) [Fact (Nat.Prime p)]
    (a : EuclideanSpace ℝ (Fin n)) :
    Fa n p a ∈ MultilinearPolynomialsOfDegreeLE (Fin (n - 1)) (ZMod p) (p - 1) := by
      refine ⟨ ml_is_multilinear _, ?_ ⟩;
      convert Set.mem_setOf_eq.mpr
          (totalDegree_ml_le _ |> le_trans <| Pa_degree_le _ _ _) using 1;
      rotate_left;
      · exact n
      · grind
      · exact p
      · exact ⟨ Fact.out ⟩
      · exact a
      simp +decide [ MvPolynomial.mem_restrictTotalDegree ];
      rfl

/-
The polynomials $\{F_a\}_{a \in A}$ are linearly independent over $\mathbb{F}_p$.
-/
theorem Fa_linearIndependent
    (n : ℕ) [NeZero n] (p : ℕ) [Fact (Nat.Prime p)] (hp : n = 4 * p)
    (hp_odd : Odd p)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA_subset : A ⊆ M n)
    (hA_no_orth : ∀ x y, x ∈ A → y ∈ A → x ≠ y → inner ℝ x y ≠ 0) :
    LinearIndependent (ZMod p) (fun (a : A) => Fa n p a) := by
      refine linearIndependent_iff'.mpr ?_;
      intro s g hg i hi
      have := congr_arg (fun f => MvPolynomial.eval (proj_b n p i.val) f) hg
      simp_all +decide
      -- By `eval_Fa_self` and `eval_Fa_of_ne`, $F_a(b) = -1$ if $a=b$ and $0$ if $a \ne b$.
      have h_eval :
          ∀ a b : EuclideanSpace ℝ (Fin n), a ∈ A → b ∈ A → a ≠ b →
            MvPolynomial.eval (proj_b n p b) (Fa n p a) = 0 := by
        exact fun a b a_1 a_2 a_3 =>
          eval_Fa_of_ne n p hp hp_odd a b (hA_subset a_1) (hA_subset a_2) a_3
            (hA_no_orth a b a_1 a_2 a_3)
      have h_eval_self :
          ∀ a : EuclideanSpace ℝ (Fin n), a ∈ A →
            MvPolynomial.eval (proj_b n p a) (Fa n p a) = -1 := by
        exact fun a a_1 => eval_Fa_self n p hp a (hA_subset a_1)
      generalize_proofs at *; (
      replace hg := congr_arg (fun f => MvPolynomial.eval (proj_b n p i.val) f) hg
      simp_all +decide;
      rw [ Finset.sum_eq_single i ] at hg <;> aesop;)

/-
The space of multilinear polynomials of degree at most $k$ is finite dimensional.
-/
instance finiteDimensional_multilinear
    (n : ℕ) [NeZero n] (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ) :
    Module.Finite (ZMod p) (MultilinearPolynomialsOfDegreeLE (Fin (n - 1)) (ZMod p) k) := by
      -- By definition of $MultilinearPolynomialsOfDegreeLE$, it is a
      -- submodule of the finite-dimensional space of polynomials of degree at
      -- most $k$.
      have h_submodule :
          MultilinearPolynomialsOfDegreeLE (Fin (n - 1)) (ZMod p) k ≤
            MvPolynomial.restrictTotalDegree (Fin (n - 1)) (ZMod p) k := by
        exact inf_le_right;
      have h_finite :
          Module.Finite (ZMod p)
            (↥(MvPolynomial.restrictTotalDegree (Fin (n - 1)) (ZMod p) k)) := by
        exact
          MvPolynomial.instFiniteSubtypeMemSubmoduleRestrictTotalDegreeOfFinite (Fin (n - 1))
            (ZMod p) k;
      exact Submodule.finiteDimensional_of_le h_submodule

/-
$M$ is a finite set.
-/
theorem M_finite (n : ℕ) [NeZero n] : (M n).Finite := by
  -- Since $M n$ is a subset of the finite set of vectors in $\{\pm 1\}^n$, it must also be finite.
  have h_sign_finite : (SignVectors n).Finite := by
    refine Set.Finite.subset (Set.Finite.pi fun _ => Set.toFinite ({1, -1} : Set ℝ)) ?_
    intro x hx i hi
    rcases hx i with h | h <;> simp [h]
  refine Set.Finite.subset (h_sign_finite.image (WithLp.toLp 2)) ?_
  intro x hx
  exact ⟨WithLp.ofLp x, hx.1, (WithLp.toLp_ofLp 2 x).symm⟩

/-
If $A \subseteq M$ has no orthogonal pairs, then $|A| \le \sum_{j=0}^{p-1} \binom{n-1}{j}$.
-/
theorem indep_bound
    (n : ℕ) [NeZero n] (p : ℕ) [Fact (Nat.Prime p)]
    (hp : n = 4 * p) (hp_odd : Odd p)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA_subset : A ⊆ M n)
    (hA_no_orth : ∀ x y, x ∈ A → y ∈ A → x ≠ y → inner ℝ x y ≠ 0) :
    A.ncard ≤ ∑ j ∈ Finset.range p, (n - 1).choose j := by
      -- By `Fa_linearIndependent`, the set $\{F_a\}_{a \in A}$ is linearly
      -- independent in $\mathbb{F}_p[z_2, \dots, z_n]$, and hence in $V$.
      have h_lin_ind : LinearIndependent (ZMod p) (fun a : A => Fa n p a) := by
        convert Fa_linearIndependent n p hp hp_odd A hA_subset
          (fun x y hx hy hxy => hA_no_orth x y hx hy hxy) using 1;
      have h_dim_V :
          Module.finrank (ZMod p)
              (MultilinearPolynomialsOfDegreeLE (Fin (n - 1)) (ZMod p) (p - 1)) =
            ∑ j ∈ Finset.range p, (n - 1).choose j := by
        convert dim_multilinear_polynomials n p hp ( p - 1 ) using 1;
        rw [ Nat.sub_add_cancel ( Nat.Prime.pos Fact.out ) ];
      have h_card_le_dim :
          (Set.ncard A : ℕ) ≤
            Module.finrank (ZMod p)
              (↥(Submodule.span (ZMod p) (Set.range (fun a : A => Fa n p a)))) := by
        have h_card_le_dim :
            (Set.ncard A : ℕ) ≤
              Module.finrank (ZMod p)
                (↥(Submodule.span (ZMod p)
                  (Set.range (fun a : A => Fa n p a)))) := by
          have h_card_eq_dim :
              Module.finrank (ZMod p)
                  (↥(Submodule.span (ZMod p)
                    (Set.range (fun a : A => Fa n p a)))) =
                Set.ncard A := by
            convert ( finrank_span_eq_card h_lin_ind )
            focus convert Set.ncard_eq_toFinset_card' A
            focus convert Fintype.card_ofFinset _ _
            focus simp +zetaDelta at *
            exact Set.Finite.fintype ( Set.Finite.subset ( M_finite n ) hA_subset )
          rw [h_card_eq_dim];
        exact h_card_le_dim;
      refine le_trans h_card_le_dim <| h_dim_V ▸ ?_;
      apply_rules [ Submodule.finrank_mono ];
      exact Submodule.span_le.mpr ( Set.range_subset_iff.mpr fun a => Fa_mem_subspace n p _ )

/-
$S(p) = \sum_{j=0}^{p-1} \binom{n-1}{j}$.
-/
def Sp (n p : ℕ) : ℕ := ∑ j ∈ Finset.range p, (n - 1).choose j

/-
If $X$ is partitioned into $m$ sets of smaller diameter, then $m \ge \lceil |M|/S(p) \rceil$.
-/
theorem partition_lower_bound
    (n : ℕ) [NeZero n] (p : ℕ) [Fact (Nat.Prime p)]
    (hp : n = 4 * p) (hp_odd : Odd p)
    (m : ℕ) (c : X n → Fin m)
    (h_diam : ∀ i, diam_general {x | ∃ (h : x ∈ X n), c ⟨x, h⟩ = i} < diam_general (X n)) :
    m ≥ Nat.ceil ((M n).ncard / (Sp n p : ℝ)) := by
      -- By `small_diam_implies_no_orthogonal_pairs`, since
      -- $\diam(Y_i) < \diam(X)$, $A_i$ contains no orthogonal pairs.
      have h_no_orthogonal_pairs :
          ∀ i : (Fin m),
            ∀ x y : EuclideanSpace ℝ (Fin n),
              x ∈ M n → y ∈ M n →
                Phi x ∈ {x : EuclideanSpace ℝ (Pairs n) |
                  ∃ h : x ∈ (X n), (c ⟨x, h⟩) = i} →
                Phi y ∈ {x : EuclideanSpace ℝ (Pairs n) |
                  ∃ h : x ∈ (X n), (c ⟨x, h⟩) = i} →
                x ≠ y → inner ℝ x y ≠ 0 := by
        intros i x y hx hy hx' hy' hxy h_inner
        have := h_diam i
        apply (small_diam_implies_no_orthogonal_pairs n p hp hp_odd
          {x : EuclideanSpace ℝ (Pairs n) |
            ∃ h : x ∈ (X n), (c ⟨x, h⟩) = i} (by
            exact fun x hx => hx.choose) this) x y hx hy hx' hy' hxy h_inner;
      -- Let $A_i = \Phi^{-1}(Y_i) \subseteq M$.
      set A : (Fin m) → Set (EuclideanSpace ℝ (Fin n)) := fun i =>
        {x : EuclideanSpace ℝ (Fin n) |
          x ∈ M n ∧
            Phi x ∈ {x : EuclideanSpace ℝ (Pairs n) |
              ∃ h : x ∈ (X n), (c ⟨x, h⟩) = i}};
      -- Since $\Phi$ is injective, $\{A_i\}$ is a partition of $M$.
      have h_partition : Set.ncard (M n) = ∑ i : Fin m, Set.ncard (A i) := by
        have h_partition : Set.ncard (⋃ i : Fin m, A i) = ∑ i : Fin m, Set.ncard (A i) := by
          have h_partition : ∀ i j : Fin m, i ≠ j → Disjoint (A i) (A j) := by
            intro i j hij; rw [ Set.disjoint_left ] ; contrapose! hij; aesop;
          have h_partition :
              ∀ (s : Finset (Fin m)),
                Set.ncard (⋃ i ∈ s, A i) = ∑ i ∈ s, Set.ncard (A i) := by
            intros s
            induction s using Finset.induction with
            | empty => norm_num [ Set.ncard ]
            | @insert i s hi ih =>
              simp +zetaDelta at *;
              rw [ Finset.sum_insert hi, @Set.ncard_union_eq ];
              · rw [ ih ];
              · exact Set.disjoint_left.mpr fun x hx hx' => by
                  obtain ⟨j, hj, hj'⟩ := Set.mem_iUnion₂.mp hx'
                  exact Set.disjoint_left.mp (h_partition i j (by aesop)) hx hj'
              · exact Set.Finite.subset ( M_finite n ) fun x hx => hx.1;
              · exact Set.Finite.biUnion (Finset.finite_toSet s) fun i _ =>
                  Set.Finite.subset
                    (Set.finite_of_ncard_pos (by
                      rw [card_M n (by
                        linarith [NeZero.pos n,
                          show p > 0 from Nat.Prime.pos Fact.out])]
                      positivity))
                    fun x hx => hx.1;
          simpa using h_partition Finset.univ;
        convert h_partition using 2;
        ext x; simp [A];
        exact fun hx => Set.mem_image_of_mem Phi hx
      -- By `indep_bound`, $|A_i| \le S(p)$.
      have h_card_A_le_Sp : ∀ i : (Fin m), Set.ncard (A i) ≤ Sp n p := by
        intro i
        apply indep_bound n p hp hp_odd (A i) (by
        exact fun x hx => hx.1) (by
        exact fun x y hx hy hxy => h_no_orthogonal_pairs i x y hx.1 hy.1 hx.2 hy.2 hxy);
      refine Nat.ceil_le.mpr ?_;
      exact div_le_of_le_mul₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by
        norm_cast
        simpa [h_partition] using
          Finset.sum_le_sum fun i (hi : i ∈ Finset.univ) => h_card_A_le_Sp i)

/-
The diameter of a set is preserved under isometry.
-/
theorem diam_isometry {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (f : EuclideanSpace ℝ ι₁ → EuclideanSpace ℝ ι₂) (hf : Isometry f)
    (E : Set (EuclideanSpace ℝ ι₁)) :
    diam_general (f '' E) = diam_general E := by
      unfold diam_general;
      simp [hf.dist_eq];

/-
`diam` is equal to `diam_general`.
-/
theorem diam_eq_diam_general {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) :
    diam E = diam_general E := rfl

/-
If `BorsukProperty` holds, any bounded set of positive diameter can be
partitioned into sets of smaller diameter.
-/
theorem BorsukProperty_implies_partition (d m : ℕ) (h : BorsukProperty d m)
    (E : Set (EuclideanSpace ℝ (Fin d))) (hE : Bornology.IsBounded E) (h_diam : diam E > 0) :
    ∃ c : E → Fin m, ∀ i, diam {x | ∃ h, c ⟨x, h⟩ = i} < diam E := by
      let D := diam E
      have hD : 0 < D := h_diam
      have hscaled_bounded : Bornology.IsBounded (D⁻¹ • E) := hE.smul₀ D⁻¹
      have hscaled_diam : diam (D⁻¹ • E) = 1 := by
        rw [diam_scaling E D⁻¹ (inv_pos.mpr hD)]
        field_simp [D, h_diam.ne']
        rfl
      obtain ⟨c0, hc0⟩ := h (D⁻¹ • E) hscaled_bounded hscaled_diam
      let c : E → Fin m := fun x =>
        c0 ⟨D⁻¹ • x.1, by exact ⟨x.1, x.2, rfl⟩⟩
      refine ⟨c, ?_⟩
      intro i
      let A : Set (EuclideanSpace ℝ (Fin d)) := {x | ∃ h, c ⟨x, h⟩ = i}
      let B : Set (EuclideanSpace ℝ (Fin d)) := {x | ∃ h, c0 ⟨x, h⟩ = i}
      have hAB : D⁻¹ • A = B := by
        ext z
        constructor
        · rintro ⟨x, hxA, rfl⟩
          rcases hxA with ⟨hxE, hxcolor⟩
          exact ⟨⟨x, hxE, rfl⟩, by simpa [c] using hxcolor⟩
        · rintro ⟨hzscaled, hzcolor⟩
          rcases hzscaled with ⟨x, hxE, rfl⟩
          exact ⟨x, ⟨hxE, by simpa [c] using hzcolor⟩, rfl⟩
      have hscaled_lt : D⁻¹ * diam A < 1 := by
        rw [← diam_scaling A D⁻¹ (inv_pos.mpr hD), hAB]
        exact hc0 i
      have hmul := mul_lt_mul_of_pos_left hscaled_lt hD
      have hinv : D * (D⁻¹ * diam A) = diam A := by
        field_simp [hD.ne']
      have hright : D * 1 = D := by ring
      rw [hinv, hright] at hmul
      exact hmul
/-
The cardinality of `Pairs n` is $\binom{n}{2}$.
-/
theorem card_Pairs (n : ℕ) : Fintype.card (Pairs n) = n.choose 2 := by
  unfold Pairs
  rw [Fintype.card_subtype]
  rw [Finset.card_filter]
  change (∑ p : Fin n × Fin n, (if p.1 < p.2 then 1 else 0)) = n.choose 2
  have h_num_pairs :
      ∑ p : Fin n × Fin n, (if p.1 < p.2 then 1 else 0) = n * (n - 1) / 2 := by
    convert Finset.sum_range_id n using 1
    erw [Finset.sum_product]
    simp +decide [Finset.filter_lt_eq_Ioi]
    rw [← Finset.sum_range_reflect, Finset.sum_range]
  rw [h_num_pairs, Nat.choose_two_right]
/-
$X$ is a finite set.
-/
theorem X_finite (n : ℕ) [NeZero n] : (X n).Finite := by
  exact Set.Finite.image _ ( M_finite n )

/-
The diameter of $X$ is positive.
-/
theorem X_diam_pos
    (n : ℕ) [NeZero n] (p : ℕ) (hp : n = 4 * p) (hp_odd : Odd p) :
    diam_general (X n) > 0 := by
  -- Since $n = 4p$ and $p$ is an odd prime, $n$ is at least 12, which is
  -- positive. Therefore, the diameter of $X n$ is $n$, which is positive.
  have h_diam_pos : diam_general (X n) = n := by
    exact diam_X n p hp hp_odd;
  exact h_diam_pos.symm ▸ Nat.cast_pos.mpr ( NeZero.pos n )

/-
If the Borsuk property holds for $d$, then $X$ can be partitioned into $m$ sets of smaller diameter.
-/
theorem borsuk_implies_partition_X (n : ℕ) [NeZero n] (p : ℕ) (hp : n = 4 * p) (hp_odd : Odd p)
    (d : ℕ) (hd : d = n.choose 2) (m : ℕ) (h_borsuk : BorsukProperty d m) :
    ∃ c : X n → Fin m, ∀ i, diam_general {x | ∃ h, c ⟨x, h⟩ = i} < diam_general (X n) := by
      let e : Pairs n ≃ Fin d := Fintype.equivOfCardEq (by
        rw [card_Pairs, Fintype.card_fin, ← hd])
      let f : EuclideanSpace ℝ (Pairs n) → EuclideanSpace ℝ (Fin d) :=
        LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
      have hf : Isometry f := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).isometry
      have hbounded : Bornology.IsBounded (f '' X n) := by
        exact Set.Finite.isBounded ((X_finite n).image f)
      have hpos : diam (f '' X n) > 0 := by
        rw [diam_eq_diam_general]
        rw [diam_isometry f hf (X n)]
        exact X_diam_pos n p hp hp_odd
      obtain ⟨c0, hc0⟩ :=
        BorsukProperty_implies_partition d m h_borsuk (f '' X n) hbounded hpos
      let c : X n → Fin m := fun x => c0 ⟨f x.1, Set.mem_image_of_mem f x.2⟩
      refine ⟨c, ?_⟩
      intro i
      let Y : Set (EuclideanSpace ℝ (Pairs n)) := {x | ∃ h, c ⟨x, h⟩ = i}
      let Z : Set (EuclideanSpace ℝ (Fin d)) := {x | ∃ h, c0 ⟨x, h⟩ = i}
      have hYZ : f '' Y = Z := by
        ext z
        constructor
        · rintro ⟨x, hxY, rfl⟩
          rcases hxY with ⟨hxX, hxcolor⟩
          exact ⟨Set.mem_image_of_mem f hxX, by simpa [c] using hxcolor⟩
        · rintro ⟨hzX, hzcolor⟩
          rcases hzX with ⟨x, hxX, rfl⟩
          exact ⟨x, ⟨hxX, by simpa [c] using hzcolor⟩, rfl⟩
      have hZ_lt : diam_general Z < diam_general (f '' X n) := by
        simpa [diam_eq_diam_general, Z] using hc0 i
      calc
        diam_general Y = diam_general (f '' Y) := (diam_isometry f hf Y).symm
        _ = diam_general Z := by rw [hYZ]
        _ < diam_general (f '' X n) := hZ_lt
        _ = diam_general (X n) := diam_isometry f hf (X n)
/-
If the Borsuk property holds for $m$ in dimension 946, then $m \ge 1650$.
-/
theorem borsuk_prop_bound (m : ℕ) (h : BorsukProperty 946 m) : m ≥ 1650 := by
  -- Apply `borsuk_implies_partition_X` with $n=44$ and $p=11$.
  obtain ⟨c, hc⟩ :
      ∃ c : X 44 → Fin m,
        ∀ i, diam_general {x | ∃ h, c ⟨x, h⟩ = i} <
          diam_general (X 44) := by
    have := borsuk_implies_partition_X 44 11 ( by decide ) ( by decide ) 946 rfl m h; aesop;
  -- Apply `partition_lower_bound` to get $m \ge \lceil |M| / S(11) \rceil$.
  have h_lower_bound : m ≥ Nat.ceil ((M 44).ncard / (Sp 44 11 : ℝ)) := by
    convert partition_lower_bound 44 11 ( by decide ) ( by decide ) m c hc;
    exact ⟨ by norm_num ⟩;
  -- Use `calculation` to show the RHS is 1650.
  have h_calc : Nat.ceil ((M 44).ncard / (Sp 44 11 : ℝ)) = 1650 := by
    rw [
      show (M 44 : Set (EuclideanSpace ℝ (Fin 44))).ncard = 2 ^ (44 - 2) by
        exact card_M 44 (by decide)]
    norm_num [ Sp ];
    norm_num [ Finset.sum_range_succ, Nat.choose ];
  exact h_calc ▸ h_lower_bound

/-
The unit ball can be covered by finitely many sets of diameter less than 1.
-/
theorem unit_ball_cover_diam_lt_one (d : ℕ) [NeZero d] :
    ∃ (U : Finset (Set (EuclideanSpace ℝ (Fin d)))),
    (∀ u ∈ U, Bornology.IsBounded u ∧ diam_general u < 1) ∧
    Metric.closedBall 0 1 ⊆ ⋃ u ∈ U, u := by
      -- By definition of $diam$, we know that for any finite set of points
      -- $t$, $\diam(t) \leq 2/3$.
      obtain ⟨t, ht⟩ :
          ∃ t : Finset (EuclideanSpace ℝ (Fin d)),
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆
              ⋃ v ∈ t, Metric.ball v (1/3) := by
        have h_tot_bounded :
            TotallyBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
          exact ProperSpace.isCompact_closedBall _ _ |> IsCompact.totallyBounded;
        rw [ totallyBounded_iff_subset ] at h_tot_bounded;
        rcases h_tot_bounded _
            (Metric.dist_mem_uniformity <| show (1 / 3 : ℝ) > 0 by norm_num) with
          ⟨t, ht₁, ht₂, ht₃⟩
        use ht₂.toFinset
        aesop;
      refine ⟨ Finset.image ( fun v => Metric.ball v ( 1 / 3 ) ) t, ?_, ?_ ⟩ <;> norm_num;
      · refine fun x hx => ⟨ Metric.isBounded_ball, ?_ ⟩;
        refine lt_of_le_of_lt
          (show diam_general (Metric.ball x (1 / 3)) ≤ 2 / 3 from ?_)
          ?_ <;>
          norm_num;
        · refine csSup_le ?_ ?_
          · exact ⟨_, ⟨x, by norm_num, x, by norm_num, rfl⟩⟩
          · exact fun b hb => by
              rcases hb with ⟨y, hy, z, hz, rfl⟩
              have hy' := Metric.mem_ball.mp hy
              have hz' := Metric.mem_ball.mp hz
              nlinarith [dist_triangle_right y z x]
      · exact ht

/-
A finite indexed cover can be refined to a partition.
-/
theorem partition_refinement_indexed
    {α : Type*} {ι : Type*} [Finite ι] [LinearOrder ι]
    (U : ι → Set α) :
    ∃ (P : ι → Set α),
    (∀ i, P i ⊆ U i) ∧
    (Pairwise (fun i j => Disjoint (P i) (P j))) ∧
    (⋃ i, U i) = ⋃ i, P i := by
      letI := Fintype.ofFinite ι
      -- Define $P_i$ as $U_i$ minus the union of $U_j$ for $j < i$.
      set P : ι → Set α := fun i => U i \ ⋃ j < i, U j;
      refine ⟨ P, ?_, ?_, ?_ ⟩;
      · exact fun i => Set.diff_subset;
      · intro i j hij; cases lt_or_gt_of_ne hij <;> simp_all +decide [ Set.disjoint_left ] ;
        · aesop;
        · aesop;
      · ext x;
        simp +zetaDelta at *;
        exact
          ⟨fun ⟨i, hi⟩ =>
            ⟨Finset.min' (Finset.univ.filter fun j => x ∈ U j)
                ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩,
              Finset.mem_filter.mp
                  (Finset.min'_mem (Finset.univ.filter fun j => x ∈ U j)
                    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩) |>.2,
              fun j hj => fun hj' =>
                not_lt_of_ge (Finset.min'_le _ _ <| by aesop) hj⟩,
            fun ⟨i, hi, hi'⟩ => ⟨i, hi⟩⟩

/-
For any bounded set E, the distance between any two points in E is at most the diameter of E.
-/
theorem dist_le_diam {d : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin d))) (hE : Bornology.IsBounded E)
    (x y : EuclideanSpace ℝ (Fin d)) (hx : x ∈ E) (hy : y ∈ E) :
    dist x y ≤ diam E := by
  -- By definition of supremum, for any $x, y \in E$, we have
  -- $dist x y \leq \sup_{a, b \in E} dist a b$.
  apply le_csSup;
  · exact hE.exists_pos_norm_le.elim fun M hM =>
      ⟨M + M, by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        exact le_trans (dist_le_norm_add_norm _ _)
          (by linarith [hM.2 x hx, hM.2 y hy])⟩;
  · exact ⟨ x, hx, y, hy, rfl ⟩

/-
If A is a subset of B and B is bounded, then the diameter of A is at most the diameter of B.
-/
theorem diam_mono {d : ℕ} {A B : Set (EuclideanSpace ℝ (Fin d))}
    (hAB : A ⊆ B) (hB : Bornology.IsBounded B) :
    diam A ≤ diam B := by
      -- Take $x,y\in A \subseteq B$. Then $\|x-y\|\le \diam(B)$.
      have h_subset : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ diam B := by
        -- Since $A \subseteq B$, any two points in $A$ are also in $B$, and
        -- thus their distance is part of the set we're taking the supremum
        -- over for $B$.
        intros x hx y hy
        have h_dist_le_diam_B : dist x y ≤ diam B := by
          apply dist_le_diam B hB x y (hAB hx) (hAB hy)
        exact h_dist_le_diam_B;
      by_cases hA : A.Nonempty;
      · exact csSup_le
          ⟨_, ⟨hA.some, hA.choose_spec, hA.some, hA.choose_spec, rfl⟩⟩
          fun x hx => by
            obtain ⟨x, hx, y, hy, rfl⟩ := hx
            exact h_subset _ hx _ hy;
      · simp_all +decide [ Set.not_nonempty_iff_eq_empty.mp hA ];
        simp +decide [ diam ];
        apply_rules [ Real.sSup_nonneg ] ; aesop

/-
Translation preserves diameter.
-/
theorem diam_vadd_eq {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    diam (x +ᵥ S) = diam S := by
      unfold diam
      congr 1
      ext r
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        rcases ha with ⟨a', ha', rfl⟩
        rcases hb with ⟨b', hb', rfl⟩
        exact ⟨a', ha', b', hb', by simp⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨x +ᵥ a, ⟨a, ha, rfl⟩, x +ᵥ b, ⟨b, hb, rfl⟩, by simp⟩
/-
There exists a finite partition of a superset of the unit ball into bounded sets
of diameter less than 1.
-/
theorem unit_ball_partition_diam_lt_one_bounded (d : ℕ) [NeZero d] :
    ∃ (m : ℕ) (P : Fin m → Set (EuclideanSpace ℝ (Fin d))),
    (∀ i, Bornology.IsBounded (P i)) ∧
    (∀ i, diam (P i) < 1) ∧
    (Pairwise (fun i j => Disjoint (P i) (P j))) ∧
    Metric.closedBall 0 1 ⊆ ⋃ i, P i := by
      -- Apply `unit_ball_cover_diam_lt_one` to get the finite cover `U`.
      obtain ⟨U, hU⟩ :
          ∃ U : Finset (Set (EuclideanSpace ℝ (Fin d))),
            (∀ u ∈ U, Bornology.IsBounded u ∧ diam_general u < 1) ∧
              Metric.closedBall 0 1 ⊆ ⋃ u ∈ U, u := by
        convert unit_ball_cover_diam_lt_one d using 1;
      -- Let $m = |U|$ and index the sets in $U$ as $u_0, \dots, u_{m-1}$.
      obtain ⟨m, hm⟩ :
          ∃ m : ℕ,
            ∃ u : Fin m → Set (EuclideanSpace ℝ (Fin d)),
              (∀ i, u i ∈ U) ∧
                (∀ u' ∈ U, ∃ i, u i = u') ∧ Function.Injective u := by
        use U.card;
        have h_enum : Nonempty (Fin U.card ≃ U) := by
          exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
        exact
          ⟨fun i => h_enum.some i |>.1, fun i => h_enum.some i |>.2,
            fun u' hu' =>
              ⟨h_enum.some.symm ⟨u', hu'⟩, by simp +decide⟩,
            fun i j hij => h_enum.some.injective <| Subtype.ext hij⟩;
      obtain ⟨ u, hu₁, hu₂, hu₃ ⟩ := hm;
      -- Apply `partition_refinement_finite` to $u$ to get a partition $P$
      -- such that $P_i \subseteq u_i$.
      obtain ⟨P, hP⟩ :
          ∃ P : Fin m → Set (EuclideanSpace ℝ (Fin d)),
            (∀ i, P i ⊆ u i) ∧
              (Pairwise (fun i j => Disjoint (P i) (P j))) ∧
                (⋃ i, u i) = ⋃ i, P i := by
        convert partition_refinement_indexed u using 1;
      refine ⟨ m, P, ?_, ?_, hP.2.1, ?_ ⟩;
      · exact fun i => Bornology.IsBounded.subset ( hU.1 _ ( hu₁ i ) |>.1 ) ( hP.1 i );
      · intro i
        have hP_subset : P i ⊆ u i := hP.left i
        have hP_bounded : Bornology.IsBounded (P i) := by
          exact Bornology.IsBounded.subset ( hU.1 _ ( hu₁ i ) |>.1 ) hP_subset
        have hP_diam : diam (P i) ≤ diam (u i) := by
          apply_rules [ diam_mono ];
          exact hU.1 _ ( hu₁ i ) |>.1
        have hP_diam_lt_one : diam (u i) < 1 := by
          exact hU.1 _ ( hu₁ i ) |>.2.trans_le' ( by rw [ diam_eq_diam_general ] )
        exact lt_of_le_of_lt hP_diam hP_diam_lt_one;
      · exact hP.2.2 ▸ hU.2.trans
          (Set.iUnion₂_subset fun u hu => by
            obtain ⟨i, rfl⟩ := hu₂ u hu
            exact Set.subset_iUnion _ i)

/-
For any dimension d >= 1, there exists an integer m such that every bounded set
of diameter 1 can be partitioned into m sets of diameter less than 1.
-/
theorem exists_borsuk_number (d : ℕ) [NeZero d] : ∃ m, BorsukProperty d m := by
  -- Let $m$ be such that a finite partition of a superset of `closedBall 0 1`
  -- into $m$ bounded sets of diameter $< 1$ exists.
  obtain ⟨m, P, hP⟩ := unit_ball_partition_diam_lt_one_bounded d;
  use m + 1;
  intro E hE hE_diam
  obtain ⟨x, hx⟩ : ∃ x ∈ E, E ⊆ Metric.closedBall x 1 := by
    have h_unit_ball : ∀ x y : EuclideanSpace ℝ (Fin d), x ∈ E → y ∈ E → dist x y ≤ 1 := by
      intro x y hx hy; exact hE_diam ▸ dist_le_diam E hE x y hx hy;
    exact Exists.elim
      (Set.nonempty_iff_ne_empty.mpr (show E ≠ ∅ by
        rintro rfl
        norm_num [diam] at hE_diam))
      fun x hx =>
        ⟨x, hx, fun y hy =>
          Metric.mem_closedBall.mpr (h_unit_ball _ _ hy hx)⟩;
  -- Define the coloring function $c$ such that $c(y) = i$ if $y - x \in P_i$.
  obtain ⟨c, hc⟩ : ∃ c : E → Fin m, ∀ y : E, y.val - x ∈ P (c y) := by
    have hc : ∀ y ∈ E, ∃ i : Fin m, y - x ∈ P i := by
      intro y hy
      specialize hP
      have := hP.2.2.2 (show y - x ∈ Metric.closedBall 0 1 from by
        simpa [dist_eq_norm] using hx.2 hy)
      aesop;
    exact ⟨ fun y => Classical.choose ( hc y y.2 ), fun y => Classical.choose_spec ( hc y y.2 ) ⟩;
  -- Show that the diameter of each set in the partition is less than 1.
  have h_diam_lt_one : ∀ i, diam {x | ∃ h : x ∈ E, c ⟨x, h⟩ = i} < 1 := by
    intro i
    have h_subset : {x | ∃ h : x ∈ E, c ⟨x, h⟩ = i} ⊆ x +ᵥ P i := by
      rintro y ⟨hy, rfl⟩
      specialize hc ⟨y, hy⟩
      simp_all +decide [Set.mem_vadd_set_iff_neg_vadd_mem];
      rwa [ neg_add_eq_sub ];
    have h_diam_lt_one : diam (x +ᵥ P i) < 1 := by
      convert hP.2.1 i using 1;
      exact diam_vadd_eq (P i) x;
    refine lt_of_le_of_lt ( diam_mono ?_ ?_ ) h_diam_lt_one;
    · assumption;
    · exact hP.1 i |> fun h => h.vadd _;
  use fun y => Fin.castSucc ( c y );
  intro i; cases i using Fin.lastCases <;> simp_all +decide [ Fin.ext_iff ] ;
  rw [
    show
      {x : EuclideanSpace ℝ (Fin d) |
          ∃ h : x ∈ E, (c ⟨x, h⟩ : ℕ) = m} = ∅ from
        Set.eq_empty_of_forall_notMem fun y hy => by
          obtain ⟨hy₁, hy₂⟩ := hy
          linarith [Fin.is_lt (c ⟨y, hy₁⟩)]]
  norm_num [ diam ]

/-
The Borsuk number of dimension 946 is at least 1650.
-/
theorem f_946_ge_1650 : BorsukNumber 946 ≥ 1650 := by
  refine le_csInf ?_ ?_;
  · -- By definition of BorsukNumber, there exists some m such that BorsukProperty 946 m holds.
    apply exists_borsuk_number 946;
  · intro m hm_borsuk
    apply borsuk_prop_bound m hm_borsuk

/-
Borsuk's conjecture is false.
-/
theorem not_erdos_505 : ¬ BorsukConjecture := by
  have h_f946 : BorsukNumber 946 ≥ 1650 := by
    exact f_946_ge_1650
  exact fun h => by linarith [h 946 (by norm_num)] ;

end Erdos505

#print axioms Erdos505.not_erdos_505
-- 'Erdos505.not_erdos_505' depends on axioms: [propext, Classical.choice, Quot.sound]
