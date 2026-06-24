/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 154.
https://www.erdosproblems.com/forum/thread/154

Informal authors:
- Bernt Lindström
- ChatGPT

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/154#post-4218
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem154.lean
-/
/-
Below you can find a Lean formalization of a proof by Lindström that for any positive integers $m, i$ and any Sidon set $A$ (sets for which $a+b = c+d$ with $a,b,c,d \in A$ imply $\{a, b\} = \{c, d\}$) with $\lvert A\rvert\sim N^{1/2}$ we have that the density of elements of $A$ that are congruent to $i \pmod{m}$ converges to $\frac{1}{m}$.

Lindström, Bernt, Well distribution of Sidon sets in residue classes. J. Number Theory (1998), 197-200.

This solves Erdős Problem #154 (https://www.erdosproblems.com/154).

I asked ChatGPT to write up Lindström's proof in a TeX-file, which Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) subsequently formalized into Lean, the result of which you can find below. Thanks go to Borix Alexeev for cleaning up the code in order to get rid of all the warnings <3 Thank you!
-/

import Mathlib

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos154

/-
A set A of natural numbers is called a Sidon set if the sums a+b (a, b ∈ A, a ≤ b) are distinct.
-/
def IsSidonSetNat (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-
B_i = {(a-i)/m | a in A, a = i mod m}
-/
def B (A : Set ℕ) (m i : ℕ) : Set ℕ :=
  {x | ∃ a ∈ A, a % m = i ∧ a = m * x + i}

/-
If A is a Sidon set and m >= 2, then B_i = {(a-i)/m | a in A, a = i mod m} is a Sidon set.
-/
theorem B_is_sidon (A : Set ℕ) (m i : ℕ) (hm : 2 ≤ m) (hA : IsSidonSetNat A) :
  IsSidonSetNat (B A m i) := by
  intro a ha b hb c hc d hd hab hcd hsumsum;
  -- Since $a, b, c, d \in B$, there exist $x, y, z, w \in A$ such that $a = (x - i) / m$, $b = (y - i) / m$, $c = (z - i) / m$, $d = (w - i) / m$.
  obtain ⟨x, hx, hx_mod⟩ := ha
  obtain ⟨y, hy, hy_mod⟩ := hb
  obtain ⟨z, hz, hz_mod⟩ := hc
  obtain ⟨w, hw, hw_mod⟩ := hd;
  -- Since $x, y, z, w \in A$, we have $x + y = (m * a + i) + (m * b + i) = m * (a + b) + 2 * i$ and $z + w = (m * c + i) + (m * d + i) = m * (c + d) + 2 * i$.
  have hsum_eq : x + y = z + w := by
    nlinarith;
  have := hA x hx y hy z hz w hw; simp_all +decide;
  exact ⟨ this ( Nat.mul_le_mul_left m hab ) ( Nat.mul_le_mul_left m hcd ) |>.1.resolve_right ( by positivity ), this ( Nat.mul_le_mul_left m hab ) ( Nat.mul_le_mul_left m hcd ) |>.2.resolve_right ( by positivity ) ⟩

/-
If $a, b, c, d$ are in a Sidon set and $a+b=c+d$, then $\{a, b\} = \{c, d\}$.
-/
lemma sidon_lemma (A : Set ℕ) (hA : IsSidonSetNat A) (a b c d : ℕ)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) (hsum : a + b = c + d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
      -- By the properties of the Sidon set, we know that either $a \leq b$ or $b \leq a$.
      by_cases h_cases : a ≤ b;
      · by_cases h_cases2 : c ≤ d;
        · exact Or.inl <| hA a ha b hb c hc d hd h_cases h_cases2 hsum;
        · cases hA _ ha _ hb _ hd _ hc h_cases ( by linarith ) ( by linarith ) ; aesop;
      · by_cases h_cases2 : c ≤ d;
        · have := hA b hb a ha c hc d hd ( by linarith ) ( by linarith ) ( by linarith ) ; aesop;
        · exact Or.inl <| by have := hA _ hb _ ha _ hd _ hc ( by linarith ) ( by linarith ) ( by linarith ) ; tauto;

/-
The differences of elements in $B_i$ and $B_j$ are disjoint for $i \neq j$.
-/
theorem B_diff_disjoint (A : Set ℕ) (m : ℕ) (hm : 2 ≤ m) (i j : ℕ) (hij : i < j) (_hj : j < m)
  (hA : IsSidonSetNat A) :
  ∀ x₁ ∈ B A m i, ∀ y₁ ∈ B A m i, ∀ x₂ ∈ B A m j, ∀ y₂ ∈ B A m j, x₁ > y₁ → x₂ > y₂ → x₁ - y₁ ≠ x₂ - y₂ := by
    -- Assume for contradiction that $x_1 - y_1 = x_2 - y_2 = k$. Since $x_1 > y_1$, $k > 0$.
    intro x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂ hx hy hk
    obtain ⟨a₁, ha₁, ha₁_mod, ha₁_eq⟩ := hx₁
    obtain ⟨b₁, hb₁, hb₁_mod, hb₁_eq⟩ := hy₁
    obtain ⟨a₂, ha₂, ha₂_mod, ha₂_eq⟩ := hx₂
    obtain ⟨b₂, hb₂, hb₂_mod, hb₂_eq⟩ := hy₂;
    -- Apply `sidon_lemma` to $a_1, b_2, a_2, b_1$.
    have h_sidon : (a₁ = a₂ ∧ b₂ = b₁) ∨ (a₁ = b₁ ∧ b₂ = a₂) := by
      apply sidon_lemma A hA a₁ b₂ a₂ b₁ ha₁ hb₂ ha₂ hb₁;
      nlinarith only [ Nat.sub_add_cancel hx.le, Nat.sub_add_cancel hy.le, hk, ha₁_eq, hb₁_eq, ha₂_eq, hb₂_eq ];
    rcases h_sidon with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide;
    grind

/-
For any natural number r, let s = floor((sqrt(4r+1)-1)/2). Then s(s+1) <= r < (s+1)(s+2).
-/
def calc_s (r : ℕ) : ℕ :=
  (Nat.sqrt (4 * r + 1) - 1) / 2

theorem calc_s_prop (r : ℕ) :
  calc_s r * (calc_s r + 1) ≤ r ∧ r < (calc_s r + 1) * (calc_s r + 2) := by
  unfold calc_s;
  constructor <;> nlinarith [ Nat.div_mul_le_self ( Nat.sqrt ( 4 * r + 1 ) - 1 ) 2, Nat.sub_add_cancel <| show 1 ≤ Nat.sqrt ( 4 * r + 1 ) from Nat.sqrt_pos.2 <| by linarith, Nat.div_add_mod ( Nat.sqrt ( 4 * r + 1 ) - 1 ) 2, Nat.mod_lt ( Nat.sqrt ( 4 * r + 1 ) - 1 ) two_pos, Nat.sqrt_le ( 4 * r + 1 ), Nat.lt_succ_sqrt ( 4 * r + 1 ) ]

/-
The sum of (r-v) for v from 1 to s equals rs - s(s+1)/2.
-/
def count_diffs (r s : ℕ) : ℕ := r * s - s * (s + 1) / 2

theorem sum_diffs_identity (r s : ℕ) (h : s < r) :
  (∑ v ∈ Finset.range s, (r - (v + 1))) = count_diffs r s := by
  -- The sum of the first s natural numbers is s(s+1)/2.
  have h_sum_first_s : ∑ v ∈ Finset.range s, (v + 1) = s * (s + 1) / 2 := by
    convert Finset.sum_range_id ( s + 1 ) using 1 <;> simp +arith +decide [ mul_comm, Finset.sum_range_succ' ];
  convert Finset.sum_range_reflect ( fun v => r - ( v + 1 ) ) s using 1;
  · rw [ ← Finset.sum_range_reflect ];
  · exact Nat.sub_eq_of_eq_add <| by rw [ ← h_sum_first_s ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.sum_congr rfl fun _ _ => tsub_add_cancel_of_le <| by linarith [ Finset.mem_range.mp ‹_› ] ] ; simp +arith +decide [ mul_comm ] ;

/-
If s(s+1) <= r < (s+1)(s+2), then rs - s(s+1)/2 >= r(sqrt(r) - 2).
-/
theorem diff_count_lower_bound (r s : ℕ) (h_lower : s * (s + 1) ≤ r) (h_upper : r < (s + 1) * (s + 2)) :
  (r * s - s * (s + 1) / 2 : ℝ) ≥ (r : ℝ) * (Real.sqrt r - 2) := by
  -- We'll use that $s + 3/2 > \sqrt{r}$ to conclude the proof.
  have h_sqrt : (s + 3 / 2 : ℝ) > Real.sqrt r := by
    nlinarith only [ Real.mul_self_sqrt ( Nat.cast_nonneg r ), ( by norm_cast : ( r : ℝ ) + 1 ≤ ( s + 1 ) * ( s + 2 ) ) ];
  nlinarith only [ show ( r : ℝ ) ≥ s * ( s + 1 ) by norm_cast, h_sqrt, Real.mul_self_sqrt ( Nat.cast_nonneg r ) ]

/-
The sum of k distinct positive integers is at least k(k+1)/2.
-/
theorem sum_distinct_pos_ints_ge (S : Finset ℕ) (h_pos : ∀ x ∈ S, 0 < x) :
  ∑ x ∈ S, x ≥ S.card * (S.card + 1) / 2 := by
  -- Let $S$ be a finite set of positive integers. Order the elements of $S$ as $x_1 < x_2 < \cdots < x_k$.
  obtain ⟨x, hx⟩ : ∃ x : Fin (Finset.card S) → ℕ, StrictMono x ∧ ∀ i, x i ∈ S := by
    exact ⟨ fun i => S.orderEmbOfFin rfl i, by simp +decide [ StrictMono ], fun i => S.orderEmbOfFin_mem rfl _ ⟩;
  -- Since $x$ is strictly monotone, we have $x_i \geq i + 1$ for all $i$.
  have h_x_ge : ∀ i, x i ≥ i + 1 := by
    intro ⟨ i, hi ⟩
    induction i with
    | zero =>
        exact h_pos _ ( hx.2 _ )
    | succ i ih =>
        exact Nat.succ_le_of_lt
          (lt_of_le_of_lt (ih (Nat.lt_of_succ_lt hi)) (hx.1 (Nat.lt_succ_self _)))
  -- Therefore, $\sum_{x \in S} x \geq \sum_{i=0}^{k-1} (i + 1) = \frac{k(k+1)}{2}$.
  have h_sum_ge : ∑ x ∈ Finset.image x Finset.univ, x ≥ ∑ i ∈ Finset.range (Finset.card S), (i + 1) := by
    rw [ Finset.sum_image (by intro a _ b _ h; exact hx.1.injective h) ] ; simpa only [ Finset.sum_range ] using Finset.sum_le_sum fun i _ => h_x_ge i;
  exact le_trans ( by rw [ Nat.div_le_iff_le_mul_add_pred ] <;> norm_num ; exact Nat.recOn ( Finset.card S ) ( by norm_num ) fun n ih => by norm_num [ Finset.sum_range_succ ] at * ; linarith ) ( h_sum_ge.trans <| Finset.sum_le_sum_of_subset <| Finset.image_subset_iff.mpr fun i _ => hx.2 i )

/-
The sum of differences of order v <= s from a set A.
-/
noncomputable def sum_diffs_le_s (A : Finset ℕ) (s : ℕ) : ℕ :=
  let l := A.sort (· ≤ ·)
  ∑ v ∈ Finset.range s, ∑ j ∈ Finset.range (l.length - (v + 1)), ((l[j + (v + 1)]?).getD 0 - (l[j]?).getD 0)

/-
The set of differences of order v <= s from a set A.
-/
noncomputable def diffs_le_s_set (A : Finset ℕ) (s : ℕ) : Finset ℕ :=
  let l := A.sort (· ≤ ·)
  (Finset.range s).biUnion (fun v =>
    (Finset.range (l.length - (v + 1))).image (fun j =>
      (l[j + (v + 1)]?).getD 0 - (l[j]?).getD 0))

/-
The map (v, j) -> l_{j+v} - l_j is injective for a Sidon set.
-/
theorem sidon_diff_map_injective (A : Finset ℕ) (hA : IsSidonSetNat A) :
  let l := A.sort (· ≤ ·)
  ∀ v₁ v₂ j₁ j₂,
    1 ≤ v₁ → v₁ < A.card →
    1 ≤ v₂ → v₂ < A.card →
    j₁ < A.card - v₁ →
    j₂ < A.card - v₂ →
    (l[j₁ + v₁]?).getD 0 - (l[j₁]?).getD 0 = (l[j₂ + v₂]?).getD 0 - (l[j₂]?).getD 0 →
    v₁ = v₂ ∧ j₁ = j₂ := by
  intro l v₁ v₂ j₁ j₂ hv₁ hv₁' hv₂ hv₂' hj₁ hj₂ h_diff_eq
  have h_sum_eq : (l[j₁ + v₁]?).getD 0 + (l[j₂]?).getD 0 = (l[j₂ + v₂]?).getD 0 + (l[j₁]?).getD 0 := by
    have h_sum_eq : (l[j₁ + v₁]?).getD 0 ≥ (l[j₁]?).getD 0 ∧ (l[j₂ + v₂]?).getD 0 ≥ (l[j₂]?).getD 0 := by
      have h_sorted : ∀ i j : ℕ, i < j → i < l.length → j < l.length → l[i]! ≤ l[j]! := by
        intros i j hij hi hj
        have h_sorted : List.Pairwise (· ≤ ·) l := by
          exact Finset.pairwise_sort _ _
        have h_le : l[i]! ≤ l[j]! := by
          have := List.pairwise_iff_get.mp h_sorted;
          simpa [ hi, hj ] using this ⟨ i, hi ⟩ ⟨ j, hj ⟩ hij
        exact h_le;
      simp +zetaDelta at *;
      exact ⟨ h_sorted _ _ ( by linarith ) ( by omega ) ( by omega ), h_sorted _ _ ( by linarith ) ( by omega ) ( by omega ) ⟩;
    omega;
  -- Since $A$ is a Sidon set, $\{l_{j_1+v_1}, l_{j_2}\} = \{l_{j_2+v_2}, l_{j_1}\}$.
  have h_pair_eq : (l[j₁ + v₁]?).getD 0 = (l[j₂ + v₂]?).getD 0 ∧ (l[j₂]?).getD 0 = (l[j₁]?).getD 0 ∨ (l[j₁ + v₁]?).getD 0 = (l[j₁]?).getD 0 ∧ (l[j₂]?).getD 0 = (l[j₂ + v₂]?).getD 0 := by
    have h_pair_eq : ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A → a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
      intros a b c d ha hb hc hd h_eq
      by_cases h_cases : a ≤ b ∧ c ≤ d ∨ a ≤ b ∧ d ≤ c ∨ b ≤ a ∧ c ≤ d ∨ b ≤ a ∧ d ≤ c;
      · rcases h_cases with ( h_cases | h_cases | h_cases | h_cases ) <;> have := hA a ha b hb c hc d hd <;> simp_all +decide [ add_comm ];
        · cases hA a ha b hb d hd c hc ( by linarith ) ( by linarith ) ( by linarith ) ; aesop;
        · have := hA c hc d hd b hb a ha; simp_all +decide [ add_comm ] ;
        · have := hA b hb a ha d hd c hc; simp_all +decide [ add_comm ] ;
      · cases le_total a b <;> cases le_total c d <;> aesop;
    -- Since $l$ is the sorted list of elements in $A$, each element in $l$ is indeed an element of $A$.
    have h_elements_in_A : ∀ (i : ℕ), i < l.length → (l[i]?).getD 0 ∈ A := by
      intros i hi;
      have h_elements_in_A : ∀ (i : ℕ), i < l.length → (l[i]?).getD 0 ∈ A := by
        intro i hi
        have h_mem : (l[i]?).getD 0 ∈ l := by
          simp +decide [hi]
        exact Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 h_mem;
      exact h_elements_in_A i hi;
    simp +zetaDelta at *;
    exact h_pair_eq _ _ _ _ ( h_elements_in_A _ ( by omega ) ) ( h_elements_in_A _ ( by omega ) ) ( h_elements_in_A _ ( by omega ) ) ( h_elements_in_A _ ( by omega ) ) h_sum_eq;
  -- Since $l$ is strictly increasing, $j_1 + v_1 = j_2 + v_2$ and $j_2 = j_1$.
  have h_j_eq : j₁ + v₁ = j₂ + v₂ ∧ j₂ = j₁ := by
    have h_strict_mono : ∀ i j : ℕ, i < j → i < l.length → j < l.length → (l[i]!) < (l[j]!) := by
      intros i j hij hi hj;
      have h_sorted : List.Pairwise (fun x y => x < y) l := by
        exact (Finset.sortedLT_sort A).pairwise
      have := List.pairwise_iff_get.mp h_sorted;
      simpa [ hi, hj ] using this ⟨ i, hi ⟩ ⟨ j, hj ⟩ hij;
    have h_j_eq : ∀ i j : ℕ, i < l.length → j < l.length → (l[i]!) = (l[j]!) → i = j := by
      exact fun i j hi hj hij => le_antisymm ( le_of_not_gt fun hi' => by linarith [ h_strict_mono _ _ hi' hj hi ] ) ( le_of_not_gt fun hj' => by linarith [ h_strict_mono _ _ hj' hi hj ] );
    simp +zetaDelta at *;
    exact h_pair_eq.elim ( fun h => ⟨ h_j_eq _ _ ( by omega ) ( by omega ) h.1, h_j_eq _ _ ( by omega ) ( by omega ) h.2 ⟩ ) fun h => False.elim <| by linarith [ h_strict_mono _ _ ( show j₁ < j₁ + v₁ from by linarith ) ( by omega ) ( by omega ) ] ;
  grind +ring

/-
The number of differences of order v <= s from a Sidon set A is rs - s(s+1)/2.
-/
theorem card_diffs_le_s_set (A : Finset ℕ) (s : ℕ) (hA : IsSidonSetNat A) (hs : s < A.card) :
  (diffs_le_s_set A s).card = count_diffs A.card s := by
    have h_inj : Finset.card (Finset.biUnion (Finset.range s) (fun v => Finset.image (fun j => (A.sort (· ≤ ·))[j + (v + 1)]! - (A.sort (· ≤ ·))[j]!) (Finset.range (A.card - (v + 1))))) = ∑ v ∈ Finset.range s, (A.card - (v + 1)) := by
      rw [ Finset.card_biUnion ];
      · refine Finset.sum_congr rfl fun v hv => ?_;
        rw [ Finset.card_image_of_injOn, Finset.card_range ];
        intro j hj j' hj' h_eq;
        have := sidon_diff_map_injective A hA ( v + 1 ) ( v + 1 ) j j' ( by linarith [ Finset.mem_range.mp hv ] ) ( by linarith [ Finset.mem_range.mp hv, Finset.mem_range.mp hj, Nat.sub_add_cancel ( show v + 1 ≤ A.card from by linarith [ Finset.mem_range.mp hv ] ) ] ) ( by linarith [ Finset.mem_range.mp hv ] ) ( by linarith [ Finset.mem_range.mp hv, Finset.mem_range.mp hj', Nat.sub_add_cancel ( show v + 1 ≤ A.card from by linarith [ Finset.mem_range.mp hv ] ) ] ) ; aesop;
      · intro v hv w hw hvw; simp_all +decide [ Finset.disjoint_left ] ;
        intro a ha x hx h; have := sidon_diff_map_injective A hA; simp_all +decide ;
        specialize this ( w + 1 ) ( v + 1 ) x a ; simp_all +decide;
        exact hvw ( this ( by omega ) ( by omega ) |>.1.symm );
    convert h_inj using 1;
    · unfold diffs_le_s_set; aesop;
    · exact Eq.symm (sum_diffs_identity A.card s hs)

/-
B_finset corresponds to the set definition B.
-/
def B_finset (A : Finset ℕ) (m i : ℕ) : Finset ℕ :=
  (A.filter (fun a => a % m = i)).image (fun a => (a - i) / m)

theorem B_finset_eq_B (A : Finset ℕ) (m i : ℕ) (hm : m > 0) :
  (B_finset A m i : Set ℕ) = B (A : Set ℕ) m i := by
    ext x;
    unfold B_finset B;
    constructor;
    · simp +zetaDelta at *;
      intro a ha ha' hx; rw [ ← hx, Nat.mul_div_cancel' ];
      · exact ⟨ by rwa [ Nat.sub_add_cancel ( ha'.symm ▸ Nat.mod_le _ _ ) ], Nat.mod_eq_of_lt ( ha'.symm ▸ Nat.mod_lt _ hm ) ⟩;
      · exact Nat.dvd_of_mod_eq_zero ( by rw [ ← Nat.mod_add_div a m, ha' ] ; norm_num );
    · rintro ⟨ a, ha₁, ha₂, ha₃ ⟩ ; exact Finset.mem_image.mpr ⟨ a, Finset.mem_filter.mpr ⟨ ha₁, ha₂ ⟩, by simp +decide [ha₃,
      hm] ⟩

/-
B_finset corresponds to the set definition B.
-/
def B_finset_new (A : Finset ℕ) (m i : ℕ) : Finset ℕ :=
  (A.filter (fun a => a % m = i)).image (fun a => (a - i) / m)

theorem B_finset_new_eq_B (A : Finset ℕ) (m i : ℕ) (hm : m > 0) :
  (B_finset_new A m i : Set ℕ) = B (A : Set ℕ) m i := by
    convert B_finset_eq_B A m i hm using 1

/-
The number of differences from all B_i is the sum of the number of differences from each B_i.
-/
noncomputable def total_diffs (A : Finset ℕ) (m : ℕ) (s : ℕ → ℕ) : Finset ℕ :=
  (Finset.range m).biUnion (fun i => diffs_le_s_set (B_finset_new A m i) (s i))

/-
The difference sets from distinct B_i are disjoint.
-/
set_option maxHeartbeats 1000000 in
-- The generated disjointness proof times out at the default heartbeat limit.
theorem disjoint_diffs_le_s_set (A : Finset ℕ) (m : ℕ) (hm : 2 ≤ m) (s : ℕ → ℕ) (hA : IsSidonSetNat (A : Set ℕ))
  (i j : ℕ) (hi : i < m) (hj : j < m) (hij : i ≠ j) :
  Disjoint (diffs_le_s_set (B_finset_new A m i) (s i)) (diffs_le_s_set (B_finset_new A m j) (s j)) := by
  -- By `B_diff_disjoint`, differences from $B_i$ and $B_j$ are disjoint for $i \neq j$.
  have h_diff_disjoint : ∀ (x y : ℕ), x ∈ B_finset_new A m i → y ∈ B_finset_new A m i → ∀ (z w : ℕ), z ∈ B_finset_new A m j → w ∈ B_finset_new A m j → x > y → z > w → |(x - y : ℤ)| ≠ |(z - w : ℤ)| := by
    intros x y hx hy z w hz hw hxy hzw
    have h_diff : (x - y : ℤ) ≠ (z - w : ℤ) := by
      have := B_diff_disjoint ( A : Set ℕ ) m ( by linarith ) ( Min.min i j ) ( Max.max i j ) ; cases le_total i j <;> simp_all +decide ;
      · have hnat : x - y ≠ z - w :=
          this (lt_of_le_of_ne ‹_› hij)
            x (B_finset_new_eq_B A m i (by linarith) ▸ hx)
            y (B_finset_new_eq_B A m i (by linarith) ▸ hy)
            z (B_finset_new_eq_B A m j (by linarith) ▸ hz)
            w (B_finset_new_eq_B A m j (by linarith) ▸ hw)
            hxy hzw
        exact fun hint => hnat (by omega)
      · cases lt_or_eq_of_le ‹_› <;> simp_all +decide [ B_finset_new, B ];
        contrapose! this;
        rcases hx with ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; rcases hy with ⟨ b, ⟨ hb₁, hb₂ ⟩, rfl ⟩ ; rcases hz with ⟨ c, ⟨ hc₁, hc₂ ⟩, rfl ⟩ ; rcases hw with ⟨ d, ⟨ hd₁, hd₂ ⟩, rfl ⟩ ; use ( c - j ) / m, ?_, ?_, ( d - j ) / m, ?_, ( a - i ) / m, ?_, ?_, ( b - i ) / m, ?_, ?_, ?_, ?_ <;> norm_num at *;
        any_goals omega;
        any_goals rw [ Nat.mod_eq_of_lt ] ; linarith;
        · convert hc₁ using 1;
          rw [ Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero ( by rw [ Nat.mod_eq_zero_of_dvd ] ; exact ⟨ c / m, by linarith [ Nat.mod_add_div c m, Nat.sub_add_cancel ( show j ≤ c from by linarith [ Nat.mod_le c m ] ) ] ⟩ ) ), Nat.sub_add_cancel ( show j ≤ c from by linarith [ Nat.mod_le c m ] ) ];
        · convert hd₁ using 1;
          rw [ Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero ( by rw [ Nat.mod_eq_zero_of_dvd ] ; exact ⟨ d / m, by linarith [ Nat.mod_add_div d m, Nat.sub_add_cancel ( show j ≤ d from by linarith [ Nat.mod_le d m ] ) ] ⟩ ) ), Nat.sub_add_cancel ( show j ≤ d from by linarith [ Nat.mod_le d m ] ) ];
        · convert ha₁ using 1;
          rw [ ← ha₂, ← Nat.div_add_mod a m, Nat.add_comm ];
          norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj ];
          rw [ Nat.mul_div_cancel_left _ ( by linarith ), add_comm ];
        · convert hb₁ using 1;
          rw [ ← Nat.mod_add_div b m, hb₂ ];
          norm_num [ add_comm, Nat.mul_div_cancel_left _ ( by linarith : 0 < m ) ]
    have h_diff' : (x - y : ℤ) ≠ -(z - w : ℤ) := by
      linarith [ show ( x : ℤ ) > y by norm_cast, show ( z : ℤ ) > w by norm_cast ]
    exact fun h => by cases abs_cases ((x - y : ℤ)) <;> cases abs_cases ((z - w : ℤ)) <;> omega;
  simp +decide [Finset.disjoint_left];
  intro a ha hb_diff_disjoint;
  -- By definition of `diffs_le_s_set`, there exist elements `x, y ∈ B_finset_new A m i` and `z, w ∈ B_finset_new A m j` such that `a = x - y` and `a = z - w`.
  obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : ℕ, x ∈ B_finset_new A m i ∧ y ∈ B_finset_new A m i ∧ x > y ∧ a = x - y := by
    unfold diffs_le_s_set at ha; simp_all +decide [ Finset.mem_biUnion, Finset.mem_image ] ;
    rcases ha with ⟨ k, hk₁, l, hl₁, rfl ⟩;
    refine
      ⟨ ((B_finset_new A m i).sort fun x1 x2 => x1 ≤ x2)[l + (k + 1)]?.getD 0,
        ?_,
        ((B_finset_new A m i).sort fun x1 x2 => x1 ≤ x2)[l]?.getD 0,
        ?_, ?_, rfl ⟩;
    · by_cases h : l + ( k + 1 ) < List.length ( (B_finset_new A m i).sort (fun x1 x2 => x1 ≤ x2) ) <;> simp_all +decide;
      · exact Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x1 ≤ x2 ) |>.1 ( by aesop );
      · omega;
    · have h_mem : ((B_finset_new A m i).sort (fun x1 x2 => x1 ≤ x2))[l]?.getD 0 ∈ (B_finset_new A m i).sort (fun x1 x2 => x1 ≤ x2) := by
        by_cases hl₂ : l < List.length ( (B_finset_new A m i).sort (fun x1 x2 => x1 ≤ x2) ) <;> simp_all +decide;
        omega;
      exact (Finset.mem_sort fun x1 x2 => x1 ≤ x2).mp h_mem;
    · have h_sorted : ∀ (l₁ l₂ : ℕ), l₁ < l₂ → l₁ < (B_finset_new A m i).card → l₂ < (B_finset_new A m i).card → ((B_finset_new A m i).sort (· ≤ ·))[l₁]?.getD 0 < ((B_finset_new A m i).sort (· ≤ ·))[l₂]?.getD 0 := by
        intros l₁ l₂ hl₁₂ hl₁ hl₂;
        have h_sorted : List.Pairwise (fun x y => x < y) ((B_finset_new A m i).sort (· ≤ ·)) := by
          exact (Finset.sortedLT_sort (B_finset_new A m i)).pairwise
        have := List.pairwise_iff_get.mp h_sorted;
        convert this ⟨ l₁, by simpa using hl₁ ⟩ ⟨ l₂, by simpa using hl₂ ⟩ hl₁₂ using 1 <;> simp +decide [hl₁,
          hl₂];
      exact h_sorted _ _ ( by linarith ) ( by omega ) ( by omega )
  obtain ⟨z, w, hz, hw, hzw⟩ : ∃ z w : ℕ, z ∈ B_finset_new A m j ∧ w ∈ B_finset_new A m j ∧ z > w ∧ a = z - w := by
    unfold diffs_le_s_set at hb_diff_disjoint;
    simp +zetaDelta at *;
    obtain ⟨ k, hk₁, l, hl₁, hl₂ ⟩ := hb_diff_disjoint;
    refine
      ⟨ ((B_finset_new A m j).sort fun x1 x2 => x1 ≤ x2)[l + (k + 1)]?.getD 0,
        ?_,
        ((B_finset_new A m j).sort fun x1 x2 => x1 ≤ x2)[l]?.getD 0,
        ?_, ?_, hl₂.symm ⟩;
    · by_cases h : l + ( k + 1 ) < List.length ( (B_finset_new A m j).sort (fun x1 x2 => x1 ≤ x2) ) <;> simp_all +decide;
      · exact Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 ( by aesop );
      · omega;
    · by_cases h : l < Finset.card ( B_finset_new A m j ) <;> simp_all +decide;
      · exact Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 ( by aesop );
      · omega;
    · grind;
  exact h_diff_disjoint x y hx hy z w hz hw hxy.1 hzw.1 ( by rw [ abs_of_nonneg, abs_of_nonneg ] <;> omega )

/-
S is the sum of the differences.
-/
noncomputable def S_total (A : Finset ℕ) (m : ℕ) (s : ℕ → ℕ) : ℕ :=
  ∑ x ∈ total_diffs A m s, x

/-
The sum of differences of order v <= s equals the sum of differences of order >= n-s.
-/
theorem sum_diffs_order_eq_complement (A : Finset ℕ) (s : ℕ) (hs : s < A.card) :
  sum_diffs_le_s A s =
  let l := A.sort (· ≤ ·)
  ∑ v ∈ Finset.range s, ∑ j ∈ Finset.range (l.length - (A.card - (v + 1))),
    ((l[j + (A.card - (v + 1))]?).getD 0 - (l[j]?).getD 0) := by
  unfold sum_diffs_le_s;
  have h_sum_eq : ∀ v ∈ Finset.range s, ∑ j ∈ Finset.range (A.card - (v + 1)), ((A.sort (· ≤ ·))[j + (v + 1)]?).getD 0 - ∑ j ∈ Finset.range (A.card - (v + 1)), ((A.sort (· ≤ ·))[j]?).getD 0 = ∑ j ∈ Finset.range (A.card - (A.card - (v + 1))), ((A.sort (· ≤ ·))[j + (A.card - (v + 1))]?).getD 0 - ∑ j ∈ Finset.range (A.card - (A.card - (v + 1))), ((A.sort (· ≤ ·))[j]?).getD 0 := by
    intro v hv
    have h_sum_eq : ∑ j ∈ Finset.range (A.card), ((A.sort (· ≤ ·))[j]?).getD 0 = ∑ j ∈ Finset.range (A.card - (v + 1)), ((A.sort (· ≤ ·))[j + (v + 1)]?).getD 0 + ∑ j ∈ Finset.range (v + 1), ((A.sort (· ≤ ·))[j]?).getD 0 := by
      rw [ ← Finset.sum_range_add_sum_Ico _ ( show v + 1 ≤ A.card from by linarith [ Finset.mem_range.mp hv ] ) ];
      rw [ add_comm, Finset.sum_Ico_eq_sum_range ];
      ac_rfl;
    have h_sum_eq : ∑ j ∈ Finset.range (A.card), ((A.sort (· ≤ ·))[j]?).getD 0 = ∑ j ∈ Finset.range (A.card - (A.card - (v + 1))), ((A.sort (· ≤ ·))[j + (A.card - (v + 1))]?).getD 0 + ∑ j ∈ Finset.range (A.card - (v + 1)), ((A.sort (· ≤ ·))[j]?).getD 0 := by
      rw [ ← Finset.sum_range_add_sum_Ico _ ( show A.card - ( v + 1 ) ≤ A.card from Nat.sub_le _ _ ) ];
      rw [ add_comm, Finset.sum_Ico_eq_sum_range ];
      ac_rfl;
    grind;
  convert Finset.sum_congr rfl h_sum_eq using 2;
  · rename_i v hv
    norm_num +zetaDelta at *;
    refine eq_tsub_of_add_eq ?_;
    rw [ ← Finset.sum_add_distrib ];
    have h_sorted : ∀ i j : ℕ, i < j → i < (A.sort (· ≤ ·)).length → j < (A.sort (· ≤ ·)).length → ((A.sort (· ≤ ·))[i]?).getD 0 ≤ ((A.sort (· ≤ ·))[j]?).getD 0 := by
      intros i j hij hi hj;
      have h_sorted : List.Pairwise (· ≤ ·) (A.sort (· ≤ ·)) := by
        exact Finset.pairwise_sort A (· ≤ ·);
      have := List.pairwise_iff_get.mp h_sorted;
      convert this ⟨ i, hi ⟩ ⟨ j, hj ⟩ hij using 1 <;> simp +decide;
      · rw [ List.getElem?_eq_getElem ] ; aesop;
      · grind;
    refine Finset.sum_congr rfl fun j hj => ?_;
    have hj_lt : j < A.card - (v + 1) := Finset.mem_range.mp hj;
    have hlen : (A.sort (· ≤ ·)).length = A.card := Finset.length_sort (s := A) (· ≤ ·);
    exact tsub_add_cancel_of_le <| h_sorted j (j + (v + 1)) (by omega) (by rw [hlen]; omega) (by rw [hlen]; omega);
  · simp +decide [Finset.sum_range];
    refine eq_tsub_of_add_eq ?_;
    rw [ ← Finset.sum_add_distrib ];
    refine Finset.sum_congr rfl fun i hi => ?_;
    rw [ Nat.sub_add_cancel ];
    have h_sorted : ∀ i j : Fin (A.card), i < j → (A.sort (· ≤ ·))[i]?.getD 0 ≤ (A.sort (· ≤ ·))[j]?.getD 0 := by
      intros i j hij;
      have h_sorted : List.Pairwise (· ≤ ·) (A.sort (· ≤ ·)) := by
        exact Finset.pairwise_sort A (· ≤ ·);
      rw [ List.pairwise_iff_get ] at h_sorted;
      convert h_sorted ⟨ i, by simp ⟩ ⟨ j, by simp ⟩ hij using 1 <;> simp +decide;
    convert h_sorted ⟨ i, by linarith [ Fin.is_lt i, Nat.sub_add_cancel ( show A.card - ( ‹_› + 1 ) ≤ A.card from Nat.sub_le _ _ ) ] ⟩ ⟨ i + ( A.card - ( ‹_› + 1 ) ), by linarith [ Fin.is_lt i, Nat.sub_add_cancel ( show A.card - ( ‹_› + 1 ) ≤ A.card from Nat.sub_le _ _ ) ] ⟩ ( Nat.lt_add_of_pos_right ( Nat.sub_pos_of_lt ( by linarith [ Finset.mem_range.mp ‹_› ] ) ) ) using 1

/-
The sum of differences equals the sum of the set of differences for a Sidon set.
-/
theorem sum_diffs_le_s_eq_sum_set (A : Finset ℕ) (s : ℕ) (hA : IsSidonSetNat A) (hs : s < A.card) :
  sum_diffs_le_s A s = ∑ x ∈ diffs_le_s_set A s, x := by
    -- We'll use the fact that if the function is injective, then the sum over the image is equal to the sum over the domain.
    have h_inj : ∀ v₁ v₂ j₁ j₂,
      1 ≤ v₁ → v₁ < A.card →
      1 ≤ v₂ → v₂ < A.card →
      j₁ < A.card - v₁ → j₂ < A.card - v₂ →
      (A.sort (· ≤ ·))[j₁ + v₁]? ≠ none → (A.sort (· ≤ ·))[j₂ + v₂]? ≠ none →
      ((A.sort (· ≤ ·))[j₁ + v₁]?).getD 0 - ((A.sort (· ≤ ·))[j₁]?).getD 0 = ((A.sort (· ≤ ·))[j₂ + v₂]?).getD 0 - ((A.sort (· ≤ ·))[j₂]?).getD 0 →
      v₁ = v₂ ∧ j₁ = j₂ := by
        intros v₁ v₂ j₁ j₂ hv₁ hv₁' hv₂ hv₂' hj₁ hj₂ hj₁' hj₂' h_eq;
        convert sidon_diff_map_injective A hA v₁ v₂ j₁ j₂ hv₁ hv₁' hv₂ hv₂' hj₁ hj₂ _;
        convert h_eq using 1;
    unfold sum_diffs_le_s diffs_le_s_set;
    rw [ Finset.sum_biUnion ];
    · refine Finset.sum_congr rfl fun v hv => ?_;
      rw [ Finset.sum_image ];
      intro j hj j' hj' h_eq; specialize h_inj ( v + 1 ) ( v + 1 ) j j'; simp_all +decide ;
      exact h_inj ( by omega ) ( by omega ) ( by omega ) ( by simpa [ List.getElem?_eq_getElem ( show j + ( v + 1 ) < List.length ( A.sort ( fun x1 x2 => x1 ≤ x2 ) ) from by simpa using by omega ), List.getElem?_eq_getElem ( show j < List.length ( A.sort ( fun x1 x2 => x1 ≤ x2 ) ) from by simpa using by omega ), List.getElem?_eq_getElem ( show j' + ( v + 1 ) < List.length ( A.sort ( fun x1 x2 => x1 ≤ x2 ) ) from by simpa using by omega ), List.getElem?_eq_getElem ( show j' < List.length ( A.sort ( fun x1 x2 => x1 ≤ x2 ) ) from by simpa using by omega ) ] using h_eq );
    · intros v hv w hw hvw;
      rw [ Function.onFun, Finset.disjoint_left ];
      simp +zetaDelta at *;
      intro a ha x hx h; specialize h_inj ( v + 1 ) ( w + 1 ) a x; simp_all +decide ;
      contrapose! h_inj;
      refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
      any_goals omega;
      convert h.symm using 1;
      · focus rw [ List.getElem?_eq_getElem ];
        focus rw [ List.getElem?_eq_getElem ];
        all_goals norm_num;
        · omega;
        · omega;
      · focus rw [ List.getElem?_eq_getElem ];
        focus rw [ List.getElem?_eq_getElem ];
        all_goals norm_num;
        · omega;
        · omega

/-
The sum of differences is bounded by the number of terms times the maximum value.
-/
theorem sum_diffs_le_s_bound (A : Finset ℕ) (s : ℕ) (M : ℕ) (_hA : IsSidonSetNat A) (hs : s < A.card)
  (hA_bound : ∀ x ∈ A, x ≤ M) :
  sum_diffs_le_s A s ≤ (s * (s + 1) / 2) * M := by
    -- The sum of differences of order v <= s equals the sum of differences of order k >= r - s. We are summing differences of order k where k goes from r - s to r - 1.
    have h_sum_diffs_eq : sum_diffs_le_s A s = ∑ k ∈ Finset.Ico (A.card - s) A.card, ∑ j ∈ Finset.range (A.card - k), (((A.sort (· ≤ ·))[j + k]?).getD 0 - ((A.sort (· ≤ ·))[j]?).getD 0) := by
      have := sum_diffs_order_eq_complement A s hs;
      rw [ this, Finset.sum_Ico_eq_sum_range ];
      simp +arith +decide [ Nat.sub_sub_self hs.le ];
      rw [ ← Finset.sum_range_reflect ];
      refine Finset.sum_congr rfl fun i hi => ?_;
      rw [ show A.card - ( s - 1 - i + 1 ) = A.card - s + i by exact Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show 1 ≤ s from by linarith [ Finset.mem_range.mp hi ], Nat.sub_add_cancel <| show i ≤ s - 1 from Nat.le_sub_one_of_lt <| Finset.mem_range.mp hi, Nat.sub_add_cancel <| show s ≤ A.card from by linarith [ Finset.mem_range.mp hi ] ] ] ; simp [ add_comm, add_left_comm, add_assoc ];
    -- Each difference is at most $M$, so the sum of differences of order $k$ is at most $(A.card - k) * M$.
    have h_diff_bound : ∀ k ∈ Finset.Ico (A.card - s) A.card, ∑ j ∈ Finset.range (A.card - k), (((A.sort (· ≤ ·))[j + k]?).getD 0 - ((A.sort (· ≤ ·))[j]?).getD 0) ≤ (A.card - k) * M := by
      intros k hk
      have h_diff_bound : ∀ j ∈ Finset.range (A.card - k), (((A.sort (· ≤ ·))[j + k]?).getD 0 - ((A.sort (· ≤ ·))[j]?).getD 0) ≤ M := by
        intros j hj
        have h_diff_bound : ∀ x ∈ A, x ≤ M := by
          assumption;
        by_cases h : j + k < List.length ( A.sort ( fun x1 x2 => x1 ≤ x2 ) ) <;> by_cases h' : j < List.length ( A.sort ( fun x1 x2 => x1 ≤ x2 ) ) <;> simp_all +decide;
        · exact le_add_right ( h_diff_bound _ <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| by aesop );
        · grind;
      simpa using Finset.sum_le_sum h_diff_bound;
    -- The sum of (A.card - k) for k from A.card - s to A.card - 1 is s(s + 1)/2.
    have h_sum_card_diff : ∑ k ∈ Finset.Ico (A.card - s) A.card, (A.card - k) = s * (s + 1) / 2 := by
      rw [ Finset.sum_Ico_eq_sum_range ];
      rw [ Nat.sub_sub_self hs.le ];
      rw [ Finset.sum_congr rfl fun i hi => by rw [ tsub_add_eq_tsub_tsub, tsub_tsub_cancel_of_le ( by linarith [ Finset.mem_range.mp hi ] ) ] ];
      convert Finset.sum_range_id ( s + 1 ) using 1 <;> simp +arith +decide [ mul_comm, Finset.sum_range_succ' ];
      rw [ ← Finset.sum_range_reflect ];
      exact Finset.sum_congr rfl fun x hx => by rw [ tsub_tsub, tsub_tsub_cancel_of_le ( by linarith [ Finset.mem_range.mp hx ] ) ] ; ring;
    exact h_sum_diffs_eq.symm ▸ le_trans ( Finset.sum_le_sum h_diff_bound ) ( by rw [ ← h_sum_card_diff, Finset.sum_mul _ _ _ ] )

/-
Elements of B_i are bounded by n/m.
-/
theorem B_finset_bound (A : Finset ℕ) (m i : ℕ) (n : ℕ) (hA : ∀ x ∈ A, x ≤ n) :
  ∀ x ∈ B_finset_new A m i, x ≤ n / m := by
    -- By definition of B_finset_new, if x is in B_finset_new A m i, then there exists an a in A such that a % m = i and x = (a - i) / m.
    intro x hx
    obtain ⟨a, haA, ha_mod, rfl⟩ : ∃ a ∈ A, a % m = i ∧ x = (a - i) / m := by
      unfold B_finset_new at hx; aesop;
    generalize_proofs at *; (
    exact Nat.div_le_div_right ( Nat.sub_le_of_le_add <| by linarith [ hA a haA, Nat.zero_le i ] )) -- This is a placeholder to allow the proof to proceed. The user should replace it with the actual proof steps.

/-
If sum rho_i = 1 and m * (sum rho_i^(3/2)) ^ 2 <= 1, then rho_i = 1/m.
-/
theorem rho_equality (m : ℕ) (hm : 2 ≤ m) (ρ : ℕ → ℝ) (h_nonneg : ∀ i < m, 0 ≤ ρ i)
  (h_sum : ∑ i ∈ Finset.range m, ρ i = 1)
  (h_ineq : (m : ℝ) * (∑ i ∈ Finset.range m, (ρ i) ^ (3 / 2 : ℝ)) ^ 2 ≤ 1) :
  ∀ i < m, ρ i = 1 / m := by
    by_contra h_neq;
    -- By Jensen's inequality, since $f(x) = x^{3/2}$ is strictly convex for $x \geq 0$, we have $\sum_{i=0}^{m-1} \rho_i^{3/2} > m \left(\frac{1}{m}\right)^{3/2}$.
    have h_jensen : ∑ i ∈ Finset.range m, ρ i ^ (3 / 2 : ℝ) > m * (1 / m) ^ (3 / 2 : ℝ) := by
      -- Apply Jensen's inequality to the strictly convex function $f(x) = x^{3/2}$.
      have h_jensen : (∑ i ∈ Finset.range m, (1 / m : ℝ) * ρ i ^ (3 / 2 : ℝ)) > ((∑ i ∈ Finset.range m, (1 / m : ℝ) * ρ i)) ^ (3 / 2 : ℝ) := by
        have h_jensen : StrictConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x^(3 / 2 : ℝ)) := by
          exact strictConvexOn_rpow ( by norm_num );
        apply_rules [ h_jensen.map_sum_lt ];
        · exact fun _ _ => by positivity;
        · simp +decide [ show m ≠ 0 by positivity ];
        · grind;
        · by_cases h_eq : ∀ i < m, ρ i = ρ 0;
          · exact False.elim <| h_neq fun i hi => by rw [ h_eq i hi, show ρ 0 = 1 / m from by rw [ eq_div_iff ( by positivity ) ] ; have := h_sum ▸ Finset.sum_congr rfl fun x hx => h_eq x ( Finset.mem_range.mp hx ) ; norm_num at * ; nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ m ) ] ] ;
          · grind;
      simp_all +decide [← Finset.mul_sum _ _ _];
      rwa [ inv_mul_eq_div, lt_div_iff₀' ( by positivity ) ] at h_jensen;
    -- Simplify the right-hand side of the inequality from Jensen's inequality.
    have h_simplify : m * (1 / m : ℝ) ^ (3 / 2 : ℝ) = 1 / Real.sqrt m := by
      rw [ Real.div_rpow ] <;> norm_num;
      rw [ show ( m : ℝ ) ^ ( 3 / 2 : ℝ ) = m * Real.sqrt m by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; ring_nf ; norm_num [ show m ≠ 0 by positivity ];
    -- Substitute the simplified right-hand side into the inequality from Jensen's inequality.
    have h_substitute : m * (∑ i ∈ Finset.range m, ρ i ^ (3 / 2 : ℝ)) ^ 2 > m * (1 / Real.sqrt m) ^ 2 := by
      exact mul_lt_mul_of_pos_left ( pow_lt_pow_left₀ ( by linarith ) ( by positivity ) ( by positivity ) ) ( by positivity );
    norm_num [ mul_div_cancel₀, ne_of_gt ( zero_lt_two.trans_le hm ) ] at * ; nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ m ) ]

/-
The size of B_i equals the number of elements in A congruent to i mod m.
-/
lemma card_B_eq_card_A_filter (A : Finset ℕ) (m i : ℕ) (hm : m > 0) :
  (B_finset_new A m i).card = (A.filter (fun a => a % m = i)).card := by
    refine Finset.card_image_of_injOn fun x hx y hy => ?_;
    simp +zetaDelta at *;
    rw [ show x = m * ( x / m ) + i by linarith [ Nat.mod_add_div x m ], show y = m * ( y / m ) + i by linarith [ Nat.mod_add_div y m ] ] ; aesop

/-
s < r for r >= 1.
-/
lemma calc_s_lt_r (r : ℕ) (hr : r ≥ 1) : calc_s r < r := by
  exact Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.sub_add_cancel <| show 1 ≤ Nat.sqrt ( 4 * r + 1 ) from Nat.sqrt_pos.mpr <| by positivity, Nat.sqrt_le ( 4 * r + 1 ) ] ;

/-
The set of differences from B_i for i in I.
-/
noncomputable def total_diffs_subset (A : Finset ℕ) (m : ℕ) (s : ℕ → ℕ) (I : Finset ℕ) : Finset ℕ :=
  I.biUnion (fun i => diffs_le_s_set (B_finset_new A m i) (s i))


/-
Version of rho_equality for Fin m.
-/
lemma rho_equality_fin (m : ℕ) (hm : 2 ≤ m) (ρ : Fin m → ℝ) (h_nonneg : ∀ i, 0 ≤ ρ i)
  (h_sum : ∑ i, ρ i = 1)
  (h_ineq : (m : ℝ) * (∑ i, (ρ i) ^ (3 / 2 : ℝ)) ^ 2 ≤ 1) :
  ρ = fun _ => 1 / (m : ℝ) := by
    convert ( rho_equality m hm ( fun i ↦ if hi : i < m then ρ ⟨ i, hi ⟩ else 0 ) _ _ _ ) using 1;
    · exact ⟨ fun h => fun i hi => by simpa [ hi ] using congr_fun h ⟨ i, hi ⟩, fun h => funext fun i => by simpa [ i.2 ] using h i.1 i.2 ⟩;
    · aesop;
    · simp +decide [ ← h_sum, Finset.sum_range ];
    · convert h_ineq using 3 ; rw [ Finset.sum_range ] ; aesop

/-
Any cluster point of the sequence in Fin m -> R is the constant vector 1/m.
-/
lemma cluster_point_is_const_fin (m : ℕ) (hm : 2 ≤ m)
  (v : ℕ → Fin m → ℝ)
  (h_nonneg : ∀ k, ∀ i, 0 ≤ v k i)
  (h_sum : Filter.Tendsto (fun k => ∑ i, v k i) Filter.atTop (nhds 1))
  (h_ineq : Filter.limsup (fun k => (m : ℝ) * (∑ i, (v k i) ^ (3 / 2 : ℝ)) ^ 2) Filter.atTop ≤ 1)
  (ρ : Fin m → ℝ)
  (hρ : MapClusterPt ρ Filter.atTop v) :
  ρ = fun _ => 1 / (m : ℝ) := by
    -- Since rho is a cluster point of the sequence v, there exists a subsequence v_{k_j} converging to rho.
    obtain ⟨k_j, hk_j⟩ : ∃ k_j : ℕ → ℕ, StrictMono k_j ∧ Filter.Tendsto (fun j => v (k_j j)) Filter.atTop (nhds ρ) := by
      exact Filter.subseq_tendsto_of_neBot hρ;
    convert rho_equality_fin m hm ρ _ _ _ using 1;
    · exact fun i => le_of_tendsto_of_tendsto' tendsto_const_nhds ( tendsto_pi_nhds.mp hk_j.2 i ) fun j => h_nonneg _ _;
    · exact tendsto_nhds_unique ( tendsto_finset_sum _ fun i _ => tendsto_pi_nhds.mp hk_j.2 i ) ( h_sum.comp hk_j.1.tendsto_atTop );
    · -- Since $\rho$ is a cluster point of $v$, we have $\sum_{i} \rho_i^{3/2} \leq \limsup_{k} \sum_{i} v_k i^{3/2}$.
      have h_sum_le_limsup : (∑ i, (ρ i) ^ (3 / 2 : ℝ)) ^ 2 ≤ Filter.limsup (fun k => (∑ i, (v k i) ^ (3 / 2 : ℝ)) ^ 2) Filter.atTop := by
        have h_sum_le_limsup : Filter.Tendsto (fun j => (∑ i, (v (k_j j) i) ^ (3 / 2 : ℝ)) ^ 2) Filter.atTop (nhds ((∑ i, (ρ i) ^ (3 / 2 : ℝ)) ^ 2)) := by
          exact Filter.Tendsto.pow ( tendsto_finset_sum _ fun i _ => Filter.Tendsto.rpow ( tendsto_pi_nhds.mp hk_j.2 i ) tendsto_const_nhds <| by norm_num ) _;
        refine le_csInf ?_ ?_ <;> norm_num;
        · have h_bounded : ∃ M, ∀ k, (∑ i, (v k i) ^ (3 / 2 : ℝ)) ^ 2 ≤ M := by
            have h_bounded : ∃ M, ∀ k, (∑ i, (v k i) ^ (3 / 2 : ℝ)) ≤ M := by
              have h_bounded : ∃ M, ∀ k, (∑ i, v k i) ≤ M := by
                exact ⟨ _, fun k => le_ciSup ( h_sum.bddAbove_range ) k ⟩;
              obtain ⟨ M, hM ⟩ := h_bounded;
              use M * M ^ (1 / 2 : ℝ);
              intro k; rw [ ← Real.sqrt_eq_rpow ] ; refine le_trans ( Finset.sum_le_sum (g := fun i => v k i * Real.sqrt ( ∑ i, v k i )) fun i _ => ?_ ) ?_;
              · rw [ show v k i ^ ( 3 / 2 : ℝ ) = v k i * Real.sqrt ( v k i ) by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ; linarith [ h_nonneg k i ] ] ; exact mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| Finset.single_le_sum ( fun i _ => h_nonneg k i ) <| Finset.mem_univ i ) <| h_nonneg k i;
              · rw [ ← Finset.sum_mul _ _ _ ] ; exact mul_le_mul ( hM k ) ( Real.sqrt_le_sqrt ( hM k ) ) ( Real.sqrt_nonneg _ ) ( by linarith [ show 0 ≤ M by exact le_trans ( Finset.sum_nonneg fun _ _ => h_nonneg k _ ) ( hM k ) ] );
            exact ⟨ h_bounded.choose ^ 2, fun k => pow_le_pow_left₀ ( Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( h_nonneg _ _ ) _ ) ( h_bounded.choose_spec k ) 2 ⟩;
          exact ⟨ h_bounded.choose, ⟨ 0, fun k hk => h_bounded.choose_spec k ⟩ ⟩;
        · exact fun b x hx => le_of_tendsto h_sum_le_limsup ( Filter.eventually_atTop.mpr ⟨ x, fun j hj => hx _ ( hk_j.1.id_le _ |> le_trans hj ) ⟩ );
      refine le_trans ( mul_le_mul_of_nonneg_left h_sum_le_limsup <| Nat.cast_nonneg _ ) ?_;
      convert h_ineq using 1;
      rw [ Filter.limsup_eq, Filter.limsup_eq ];
      rw [ ← smul_eq_mul, ← Real.sInf_smul_of_nonneg ];
      · congr with x ; simp +decide [Set.mem_smul_set];
        exact ⟨ fun ⟨ y, ⟨ a, ha ⟩, hy ⟩ => ⟨ a, fun b hb => by nlinarith [ ha b hb ] ⟩, fun ⟨ a, ha ⟩ => ⟨ x / m, ⟨ a, fun b hb => by nlinarith [ ha b hb, show ( m : ℝ ) ≥ 2 by norm_cast, mul_div_cancel₀ x ( by positivity : ( m : ℝ ) ≠ 0 ) ] ⟩, by rw [ mul_div_cancel₀ _ ( by positivity ) ] ⟩ ⟩;
      · positivity

/-
The sequence v converges to the constant vector 1/m.
-/
theorem sequence_convergence_to_constant_fin (m : ℕ) (hm : 2 ≤ m)
  (v : ℕ → Fin m → ℝ)
  (h_nonneg : ∀ k, ∀ i, 0 ≤ v k i)
  (h_sum : Filter.Tendsto (fun k => ∑ i, v k i) Filter.atTop (nhds 1))
  (h_ineq : Filter.limsup (fun k => (m : ℝ) * (∑ i, (v k i) ^ (3 / 2 : ℝ)) ^ 2) Filter.atTop ≤ 1)
  : Filter.Tendsto v Filter.atTop (nhds (fun _ => 1 / (m : ℝ))) := by
    convert tendsto_pi_nhds.mpr _ using 1;
    intro i;
    -- By contradiction, assume there exists a subsequence of $v$ that does not converge to $1/m$.
    by_contra h_contra;
    -- By definition of limit, there exists an ε > 0 such that for all N, there exists k ≥ N with |v k i - 1/m| ≥ ε.
    obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ∀ N, ∃ k ≥ N, |v k i - 1 / (m : ℝ)| ≥ ε := by
      rw [ Metric.tendsto_atTop ] at h_contra ; aesop;
    -- Construct a subsequence of $v$ that does not converge to $1/m$.
    obtain ⟨subseq, hsubseq⟩ : ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ ∀ k, |v (subseq k) i - 1 / (m : ℝ)| ≥ ε := by
      exact ⟨ fun k => Nat.recOn k ( Nat.find ( hε 0 ) ) fun k ih => Nat.find ( hε ( ih + 1 ) ), strictMono_nat_of_lt_succ fun k => Nat.find_spec ( hε _ ) |>.1.trans_lt' ( Nat.lt_succ_self _ ), fun k => Nat.recOn k ( Nat.find_spec ( hε 0 ) |>.2 ) fun k ih => Nat.find_spec ( hε _ ) |>.2 ⟩;
    -- Since $v$ is bounded, the subsequence $v (subseq k)$ is also bounded.
    have h_bounded : ∃ M, ∀ k, ∀ i, |v (subseq k) i| ≤ M := by
      have h_bounded : ∃ M, ∀ k, ∑ i, v (subseq k) i ≤ M := by
        exact ⟨ _, fun k => le_csSup ( h_sum.comp hsubseq.1.tendsto_atTop |> Filter.Tendsto.bddAbove_range ) ⟨ k, rfl ⟩ ⟩;
      exact ⟨ h_bounded.choose, fun k i => by rw [ abs_of_nonneg ( h_nonneg _ _ ) ] ; exact le_trans ( Finset.single_le_sum ( fun a _ => h_nonneg ( subseq k ) a ) ( Finset.mem_univ i ) ) ( h_bounded.choose_spec k ) ⟩;
    -- By the Bolzano-Weierstrass theorem, the bounded subsequence $v (subseq k)$ has a convergent subsequence.
    obtain ⟨subseq', hsubseq'⟩ : ∃ subseq' : ℕ → ℕ, StrictMono subseq' ∧ ∃ ρ : Fin m → ℝ, Filter.Tendsto (fun k => v (subseq (subseq' k))) Filter.atTop (nhds ρ) := by
      have h_compact : IsCompact (Set.pi Set.univ fun _ : Fin m => Set.Icc (-h_bounded.choose) h_bounded.choose) := by
        exact isCompact_univ_pi fun _ => CompactIccSpace.isCompact_Icc;
      have := h_compact.isSeqCompact fun k => show v ( subseq k ) ∈ Set.pi Set.univ fun _ => Set.Icc ( -h_bounded.choose ) h_bounded.choose from fun i _ => ⟨ neg_le_of_abs_le <| h_bounded.choose_spec k i, le_of_abs_le <| h_bounded.choose_spec k i ⟩ ; aesop;
    obtain ⟨ ρ, hρ ⟩ := hsubseq'.2;
    -- By the properties of the limit, we have that $\rho$ is a cluster point of $v$.
    have h_cluster : MapClusterPt ρ Filter.atTop v := by
      rw [ MapClusterPt ];
      rw [ clusterPt_iff_nonempty ];
      intro U hU V hV; rcases Filter.mem_atTop_sets.mp hV with ⟨ N, hN ⟩ ; rcases Filter.eventually_atTop.mp ( hρ.eventually hU ) with ⟨ M, hM ⟩ ; exact ⟨ v ( subseq ( subseq' ( Max.max N M ) ) ), hM _ ( le_max_right _ _ ), hN _ ( le_trans ( le_max_left _ _ ) ( hsubseq'.1.id_le _ |> le_trans <| hsubseq.1.id_le _ ) ) ⟩ ;
    have h_cluster_const : ρ = fun _ => 1 / (m : ℝ) := by
      apply cluster_point_is_const_fin m hm v h_nonneg h_sum h_ineq ρ h_cluster;
    have := hρ.comp hsubseq'.1.tendsto_atTop; simp_all +decide [ tendsto_pi_nhds ] ;
    exact absurd ( this i ) ( by intro H; exact absurd ( H.eventually ( Metric.ball_mem_nhds _ hε_pos ) ) fun h => by obtain ⟨ k, hk ⟩ := h.exists; exact not_lt_of_ge ( hsubseq.2 ( subseq' ( subseq' k ) ) ) ( by simpa using hk ) )

/-
Cardinality of the subset of differences.
-/
theorem card_total_diffs_subset (A : Finset ℕ) (m : ℕ) (hm : 2 ≤ m) (s : ℕ → ℕ) (I : Finset ℕ)
  (hI : I ⊆ Finset.range m)
  (hA : IsSidonSetNat (A : Set ℕ))
  (h_subset : ∀ i ∈ I, s i < (B_finset_new A m i).card) :
  (total_diffs_subset A m s I).card = ∑ i ∈ I, count_diffs (B_finset_new A m i).card (s i) := by
    have h_union_disjoint : ∀ i j, i ∈ I → j ∈ I → i ≠ j → Disjoint (diffs_le_s_set (B_finset_new A m i) (s i)) (diffs_le_s_set (B_finset_new A m j) (s j)) := by
      intros i j hi hj hij;
      convert disjoint_diffs_le_s_set A m hm ( s ) hA i j ( Finset.mem_range.mp ( hI hi ) ) ( Finset.mem_range.mp ( hI hj ) ) hij using 1;
    -- Apply the fact that the cardinality of a union of pairwise disjoint sets is the sum of their cardinalities.
    have h_card_union : (Finset.biUnion I (fun i => diffs_le_s_set (B_finset_new A m i) (s i))).card = ∑ i ∈ I, (diffs_le_s_set (B_finset_new A m i) (s i)).card := by
      exact Finset.card_biUnion fun ⦃x⦄ a ⦃y⦄ => h_union_disjoint x y a;
    convert h_card_union using 2;
    convert Eq.symm ( card_diffs_le_s_set _ _ _ _ ) using 1;
    · convert B_is_sidon A m ‹_› _ _ using 1;
      · exact B_finset_new_eq_B _ _ _ ( by linarith );
      · linarith;
      · assumption;
    · exact h_subset _ ‹_›

/-
The total differences set is equal to the subset of differences from non-empty B_i.
-/
lemma total_diffs_eq_subset_pos (A : Finset ℕ) (m : ℕ) (s : ℕ → ℕ) :
  let I := (Finset.range m).filter (fun i => 0 < (B_finset_new A m i).card)
  total_diffs A m s = total_diffs_subset A m s I := by
    -- By definition of $B_finset_new$, if $(B_finset_new A m i).card = 0$, then $B_finset_new A m i$ is empty.
    have h_empty : ∀ i, (B_finset_new A m i).card = 0 → diffs_le_s_set (B_finset_new A m i) (s i) = ∅ := by
      unfold diffs_le_s_set; aesop;
    unfold total_diffs total_diffs_subset;
    grind

/-
Eventually the premises for the inequality hold.
-/
lemma eventually_inequality_premises
  (n_seq : ℕ → ℕ) (A_seq : ℕ → Finset ℕ)
  (h_n_tendsto : Filter.Tendsto (fun k => (n_seq k : ℝ)) Filter.atTop Filter.atTop)
  (h_card_tendsto : Filter.Tendsto (fun k => (A_seq k).card / Real.sqrt (n_seq k)) Filter.atTop (nhds 1))
  (m : ℕ) (hm : 2 ≤ m) :
  ∀ᶠ k in Filter.atTop,
    (total_diffs (A_seq k) m (fun i => calc_s ((B_finset_new (A_seq k) m i).card))).card > 0 ∧
    0 ≤ ∑ i ∈ Finset.range m, ((B_finset_new (A_seq k) m i).card : ℝ) * (Real.sqrt (B_finset_new (A_seq k) m i).card - 2) := by
      have h_card_bound : ∃ K, ∀ k ≥ K, 4 * m ≤ (A_seq k).card := by
        -- Since $n_k \to \infty$ and $(A_seq k).card \sim \sqrt{n_k}$, we have $(A_seq k).card \to \infty$.
        have h_card_inf : Filter.Tendsto (fun k => (A_seq k).card : ℕ → ℝ) Filter.atTop Filter.atTop := by
          have h_card_large : Filter.Tendsto (fun k => (A_seq k).card / Real.sqrt (n_seq k) * Real.sqrt (n_seq k)) Filter.atTop Filter.atTop := by
            apply Filter.Tendsto.pos_mul_atTop;
            exacts [ zero_lt_one, h_card_tendsto, by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| h_n_tendsto ];
          exact h_card_large.congr' ( by filter_upwards [ h_n_tendsto.eventually_gt_atTop 0 ] with k hk using by rw [ div_mul_cancel₀ _ ( ne_of_gt ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop ) ) ) ) ) ] );
        exact Filter.eventually_atTop.mp ( h_card_inf.eventually_ge_atTop ( 4 * m ) ) |> fun ⟨ K, hK ⟩ ↦ ⟨ K, fun k hk ↦ by exact_mod_cast hK k hk ⟩;
      obtain ⟨ K, hK ⟩ := h_card_bound;
      refine Filter.eventually_atTop.mpr ⟨ K, fun k hk => ⟨ ?_, ?_ ⟩ ⟩;
      · -- By the pigeonhole principle, since $|A_k| \geq 4m$, there exists some $i$ such that $|B_i| \geq 2$.
        obtain ⟨i, hi⟩ : ∃ i < m, 2 ≤ (B_finset_new (A_seq k) m i).card := by
          have h_pigeonhole : ∑ i ∈ Finset.range m, (B_finset_new (A_seq k) m i).card = (A_seq k).card := by
            rw [ Finset.sum_congr rfl fun i hi => card_B_eq_card_A_filter _ _ _ ( by linarith ) ];
            rw [ ← Finset.card_biUnion ];
            · congr with x ; simp +decide [ Nat.mod_lt _ ( by linarith : 0 < m ) ];
            · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
          contrapose! hK;
          exact ⟨ k, hk, by rw [ ← h_pigeonhole ] ; exact lt_of_le_of_lt ( Finset.sum_le_sum fun _ _ => Nat.le_of_lt_succ ( hK _ ( Finset.mem_range.mp ‹_› ) ) ) ( by norm_num; linarith ) ⟩;
        refine Finset.card_pos.mpr ?_;
        refine ⟨ ?_, Finset.mem_biUnion.mpr ⟨ i, Finset.mem_range.mpr hi.1, ?_ ⟩ ⟩;
        focus
          exact ((B_finset_new (A_seq k) m i).sort (· ≤ ·))[1]! - ((B_finset_new (A_seq k) m i).sort (· ≤ ·))[0]!
        refine Finset.mem_biUnion.mpr ⟨ 0, ?_, ?_ ⟩ <;> norm_num;
        · exact Nat.div_pos ( Nat.le_sub_one_of_lt ( Nat.le_sqrt.mpr ( by linarith ) ) ) zero_lt_two;
        · exact ⟨ 0, Nat.sub_pos_of_lt hi.2, rfl ⟩;
      · -- Since $\sum_{i=0}^{m-1} r_{k,i} = |A_k|$, we have $\sum_{i=0}^{m-1} r_{k,i}^{3/2} \geq |A_k|^{3/2} / \sqrt{m}$.
        have h_sum_r_pow : ∑ i ∈ Finset.range m, ((B_finset_new (A_seq k) m i).card : ℝ) ^ (3 / 2 : ℝ) ≥ ((A_seq k).card : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt m := by
          have h_sum_r_pow : (∑ i ∈ Finset.range m, ((B_finset_new (A_seq k) m i).card : ℝ) ^ (3 / 2 : ℝ)) * (m : ℝ) ^ (1 / 2 : ℝ) ≥ ((∑ i ∈ Finset.range m, ((B_finset_new (A_seq k) m i).card : ℝ))) ^ (3 / 2 : ℝ) := by
            have h_sum_r_pow : (∑ i ∈ Finset.range m, ((B_finset_new (A_seq k) m i).card : ℝ) ^ (3 / 2 : ℝ)) ≥ ((∑ i ∈ Finset.range m, ((B_finset_new (A_seq k) m i).card : ℝ)) ^ (3 / 2 : ℝ)) / (m : ℝ) ^ (1 / 2 : ℝ) := by
              have h_jensen : ∀ (x : Fin m → ℝ), (∀ i, 0 ≤ x i) → (∑ i, x i ^ (3 / 2 : ℝ)) ≥ ((∑ i, x i) ^ (3 / 2 : ℝ)) / (m : ℝ) ^ (1 / 2 : ℝ) := by
                intro x hx_nonneg
                have h_jensen : (∑ i, x i ^ (3 / 2 : ℝ)) / m ≥ ((∑ i, x i) / m) ^ (3 / 2 : ℝ) := by
                  have := @Real.rpow_arith_mean_le_arith_mean_rpow;
                  specialize this Finset.univ ( fun _i => 1 / m ) ( fun _i => x _i ) ; norm_num at *;
                  simpa [ inv_mul_eq_div, Finset.sum_div _ _ _ ] using this ( mul_inv_cancel₀ ( by positivity ) ) hx_nonneg ( show 1 ≤ ( 3 / 2 : ℝ ) by norm_num );
                rw [ Real.div_rpow ( Finset.sum_nonneg fun _ _ => hx_nonneg _ ) ( by positivity ) ] at h_jensen;
                field_simp;
                rw [ ge_iff_le, div_le_div_iff₀ ] at h_jensen <;> try positivity;
                rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add' ] at h_jensen <;> norm_num at *;
                · rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add' ] at * <;> norm_num at *;
                  · nlinarith [ show ( m : ℝ ) > 0 by positivity ];
                  · exact Finset.sum_nonneg fun _ _ => hx_nonneg _;
                · exact Finset.sum_nonneg fun _ _ => hx_nonneg _
              simpa only [ Finset.sum_range ] using h_jensen _ fun i => Nat.cast_nonneg _;
            rwa [ ge_iff_le, div_le_iff₀ ( by positivity ) ] at h_sum_r_pow;
          field_simp;
          convert h_sum_r_pow.le using 1 <;> norm_num [ Real.sqrt_eq_rpow ]
          focus ring_nf
          · norm_cast;
            rw [ Finset.sum_congr rfl fun i hi => card_B_eq_card_A_filter _ _ _ ( by linarith ) ];
            rw [ ← Finset.card_biUnion ];
            · congr with x ; simp +decide [ Nat.mod_lt _ ( by linarith : 0 < m ) ];
            · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
          · ring;
        -- Since $\sum_{i=0}^{m-1} r_{k,i} = |A_k|$, we have $\sum_{i=0}^{m-1} r_{k,i}^{3/2} - 2 \sum_{i=0}^{m-1} r_{k,i} \geq |A_k|^{3/2} / \sqrt{m} - 2 |A_k|$.
        have h_sum_r_pow_minus_two_sum : ∑ i ∈ Finset.range m, ((B_finset_new (A_seq k) m i).card : ℝ) * (Real.sqrt ((B_finset_new (A_seq k) m i).card) - 2) ≥ ((A_seq k).card : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt m - 2 * (A_seq k).card := by
          have h_sum_r_pow_minus_two_sum : ∑ i ∈ Finset.range m, ((B_finset_new (A_seq k) m i).card : ℝ) * (Real.sqrt ((B_finset_new (A_seq k) m i).card) - 2) = ∑ i ∈ Finset.range m, ((B_finset_new (A_seq k) m i).card : ℝ) ^ (3 / 2 : ℝ) - 2 * ∑ i ∈ Finset.range m, ((B_finset_new (A_seq k) m i).card : ℝ) := by
            rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_sub_distrib ] ; congr ; ext i ; rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add' ] <;> norm_num ; ring_nf;
            rw [ Real.sqrt_eq_rpow ];
          have h_sum_r_pow_minus_two_sum : ∑ i ∈ Finset.range m, ((B_finset_new (A_seq k) m i).card : ℝ) = (A_seq k).card := by
            norm_cast;
            rw [ Finset.sum_congr rfl fun i hi => card_B_eq_card_A_filter _ _ _ ( by linarith ) ];
            rw [ ← Finset.card_biUnion ];
            · congr with x ; simp +decide [ Nat.mod_lt _ ( by linarith : 0 < m ) ];
            · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
          grind;
        refine le_trans ?_ h_sum_r_pow_minus_two_sum;
        rw [ sub_nonneg, le_div_iff₀ ] <;> norm_num;
        · rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add' ] <;> norm_num;
          rw [ ← Real.sqrt_eq_rpow ];
          nlinarith only [ show ( m : ℝ ) ≥ 2 by norm_cast, show ( A_seq k |> Finset.card : ℝ ) ≥ 4 * m by exact_mod_cast hK k hk, Real.sqrt_nonneg m, Real.sqrt_nonneg ( A_seq k |> Finset.card ), Real.mul_self_sqrt ( Nat.cast_nonneg m ), Real.mul_self_sqrt ( Nat.cast_nonneg ( A_seq k |> Finset.card ) ), pow_two_nonneg ( Real.sqrt m - Real.sqrt ( A_seq k |> Finset.card ) / 2 ) ];
        · linarith

/-
Lower bound for the sum of differences restricted to non-empty sets.
-/
theorem S_subset_lower_bound (A : Finset ℕ) (m : ℕ) (hm : 2 ≤ m) (s : ℕ → ℕ)
  (hA : IsSidonSetNat (A : Set ℕ))
  (h_s_def : ∀ i < m, s i = calc_s (B_finset_new A m i).card)
  (I : Finset ℕ) (hI : I = (Finset.range m).filter (fun i => 0 < (B_finset_new A m i).card))
  (h_K_pos : (total_diffs_subset A m s I).card > 0)
  (h_sum_nonneg : 0 ≤ ∑ i ∈ I, ((B_finset_new A m i).card : ℝ) * (Real.sqrt (B_finset_new A m i).card - 2)) :
  2 * (∑ x ∈ total_diffs_subset A m s I, x : ℝ) > (∑ i ∈ I, ((B_finset_new A m i).card : ℝ) * (Real.sqrt (B_finset_new A m i).card - 2)) ^ 2 := by
    -- Each term in the sum is at least as large as the corresponding term for the B_i sets.
    have h_term_bound : ∀ x ∈ total_diffs_subset A m s I, x ≥ 1 := by
      unfold total_diffs_subset;
      unfold diffs_le_s_set;
      simp +zetaDelta at *;
      rintro x y hy z hz t ht rfl;
      -- Since the list is sorted in increasing order, the element at position t + (z + 1) is greater than the element at position t.
      have h_sorted : ∀ i j : ℕ, i < j → i < (B_finset_new A m y).card → j < (B_finset_new A m y).card → ((B_finset_new A m y).sort (fun x1 x2 => x1 ≤ x2))[i]?.getD 0 < ((B_finset_new A m y).sort (fun x1 x2 => x1 ≤ x2))[j]?.getD 0 := by
        intros i j hij hi hj;
        have h_sorted : List.Pairwise (fun x1 x2 => x1 < x2) ((B_finset_new A m y).sort (fun x1 x2 => x1 ≤ x2)) := by
          exact (Finset.sortedLT_sort (B_finset_new A m y)).pairwise
        have := List.pairwise_iff_get.mp h_sorted;
        convert this ⟨ i, by simpa using hi ⟩ ⟨ j, by simpa using hj ⟩ hij using 1 <;> simp +decide [hi,
          hj];
      exact Nat.sub_pos_of_lt ( h_sorted _ _ ( by linarith ) ( by omega ) ( by omega ) );
    -- For each i in I, count_diffs(r_i, s_i) ≥ r_i(sqrt(r_i)-2).
    have h_count_diffs_bound : ∀ i ∈ I, count_diffs (B_finset_new A m i).card (s i) ≥ (B_finset_new A m i).card * (Real.sqrt ((B_finset_new A m i).card) - 2) := by
      intros i hi
      have h_count_diffs_bound_i : count_diffs (B_finset_new A m i).card (s i) ≥ ((B_finset_new A m i).card : ℝ) * (Real.sqrt ((B_finset_new A m i).card) - 2) := by
        have h_s_prop_i : s i * (s i + 1) ≤ (B_finset_new A m i).card ∧ (B_finset_new A m i).card < (s i + 1) * (s i + 2) := by
          rw [ h_s_def i ( Finset.mem_range.mp ( Finset.mem_filter.mp ( hI ▸ hi ) |>.1 ) ) ] ; exact calc_s_prop _;
        convert diff_count_lower_bound _ _ h_s_prop_i.1 h_s_prop_i.2 using 1;
        unfold count_diffs;
        rw [ Nat.cast_sub ] <;> norm_num;
        · rw [ Nat.cast_div ] <;> norm_cast ; exact even_iff_two_dvd.mp ( by simp +arith +decide [ mul_add, parity_simps ] );
        · rw [ Nat.div_le_iff_le_mul_add_pred ] <;> norm_num;
          rcases k : s i with ( _ | _ | k ) <;> simp_all +decide [Nat.mul_succ];
          · linarith;
          · nlinarith only [ h_s_prop_i.1 ];
      exact h_count_diffs_bound_i;
    -- Therefore, the cardinality of total_diffs_subset is at least the sum of the count_diffs terms.
    have h_card_bound : (total_diffs_subset A m s I).card ≥ ∑ i ∈ I, (B_finset_new A m i).card * (Real.sqrt ((B_finset_new A m i).card) - 2) := by
      refine le_trans ( Finset.sum_le_sum h_count_diffs_bound ) ?_;
      rw_mod_cast [ card_total_diffs_subset ];
      · linarith;
      · exact hI ▸ Finset.filter_subset _ _;
      · assumption;
      · intro i hi; rw [ h_s_def i ( by aesop ) ] ; exact calc_s_lt_r _ ( by aesop ) ;
    -- The sum of K distinct positive integers is at least K(K+1)/2.
    have h_sum_bound : ∑ x ∈ total_diffs_subset A m s I, x ≥ (total_diffs_subset A m s I).card * ((total_diffs_subset A m s I).card + 1) / 2 := by
      exact sum_distinct_pos_ints_ge (total_diffs_subset A m s I) h_term_bound;
    rw [ ← Nat.cast_sum ] at *;
    refine lt_of_le_of_lt ( pow_le_pow_left₀ h_sum_nonneg h_card_bound 2 ) ?_;
    norm_cast ; nlinarith [ Nat.div_mul_cancel ( show 2 ∣ ( total_diffs_subset A m s I |> Finset.card ) * ( ( total_diffs_subset A m s I |> Finset.card ) + 1 ) from even_iff_two_dvd.mp ( by simp +arith +decide [ mul_add, parity_simps ] ) ) ]

/-
The error term converges to 0.
-/
lemma error_term_tendsto_zero
  (n_seq : ℕ → ℕ) (A_seq : ℕ → Finset ℕ)
  (h_n_tendsto : Filter.Tendsto (fun k => (n_seq k : ℝ)) Filter.atTop Filter.atTop)
  (h_card_tendsto : Filter.Tendsto (fun k => (A_seq k).card / Real.sqrt (n_seq k)) Filter.atTop (nhds 1)) :
  Filter.Tendsto (fun k => 2 * (A_seq k).card / (n_seq k : ℝ) ^ (3/4 : ℝ)) Filter.atTop (nhds 0) := by
    convert h_card_tendsto.const_mul 2 |> Filter.Tendsto.mul <| tendsto_inv_atTop_zero.comp <| show Filter.Tendsto ( fun k : ℕ => ( n_seq k : ℝ ) ^ ( 1 / 4 : ℝ ) ) Filter.atTop Filter.atTop from tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop.comp <| Filter.tendsto_atTop_atTop.mpr _ using 2;
    · norm_num [ Real.sqrt_eq_rpow, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
      exact Or.inl ( by rw [ ← mul_inv, ← Real.rpow_add' ] <;> norm_num );
    · norm_num;
    · exact fun b => Filter.eventually_atTop.mp ( h_n_tendsto.eventually_ge_atTop b ) |> fun ⟨ i, hi ⟩ => ⟨ i, fun k hk => mod_cast hi k hk ⟩

/-
Algebraic identity for the term transformation.
-/
lemma term_transform (x n : ℝ) (hx : 0 ≤ x) (hn : 0 < n) :
  x * (Real.sqrt x - 2) / n ^ (3/4 : ℝ) = (x / Real.sqrt n) ^ (3 / 2 : ℝ) - 2 * x / n ^ (3/4 : ℝ) := by
    rw [ Real.div_rpow ] <;> try positivity;
    rw [ show x ^ ( 3 / 2 : ℝ ) = x * Real.sqrt x by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx ] <;> norm_num, show ( Real.sqrt n ) ^ ( 3 / 2 : ℝ ) = n ^ ( 3 / 4 : ℝ ) by rw [ Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le ] ; norm_num ] ; ring;

/-
Algebraic transformation of the inequality.
-/
lemma inequality_algebraic_transform (m : ℕ) (r : ℕ → ℝ) (n : ℝ) (C : ℝ) (hn : 0 < n)
  (h_nonneg : ∀ i ∈ Finset.range m, 0 ≤ r i) :
  (m : ℝ) * (∑ i ∈ Finset.range m, r i * (Real.sqrt (r i) - 2)) ^ 2 < C * n →
  (m : ℝ) * (∑ i ∈ Finset.range m, ((r i / Real.sqrt n) ^ (3 / 2 : ℝ) - 2 * r i / n ^ (3/4 : ℝ))) ^ 2 < C / Real.sqrt n := by
    -- Let's multiply both sides of the inequality by $n^{3/2}$ to simplify.
    intro h_ineq
    have h_mul : m * (∑ i ∈ Finset.range m, (r i * (Real.sqrt (r i) - 2)) / n ^ (3 / 4 : ℝ)) ^ 2 < C / Real.sqrt n := by
      rw [ ← Finset.sum_div _ _ _ ];
      rw [ div_pow, mul_div, div_lt_div_iff₀ ];
      · convert mul_lt_mul_of_pos_right h_ineq ( Real.sqrt_pos.mpr hn ) using 1 ; norm_num [ sq, ← Real.rpow_add hn ];
        rw [ mul_assoc, Real.sqrt_eq_rpow, ← Real.rpow_one_add' hn.le ] <;> norm_num;
      · positivity;
      · positivity;
    convert h_mul using 2;
    congr! 2;
    (expose_names; exact Eq.symm (term_transform (r x) n (h_nonneg x h) hn))

/-
If m(S-E) ^ 2 < Z and E->0, Z->1, then limsup mS^2 <= 1.
-/
lemma limsup_le_of_sub_sq_le (m : ℝ) (S E Z : ℕ → ℝ) (hm : 0 < m)
  (h_ineq : ∀ᶠ k in Filter.atTop, m * (S k - E k) ^ 2 < Z k)
  (hE : Filter.Tendsto E Filter.atTop (nhds 0))
  (hZ : Filter.Tendsto Z Filter.atTop (nhds 1)) :
  Filter.limsup (fun k => m * (S k) ^ 2) Filter.atTop ≤ 1 := by
    -- From the inequality, $|S_k - E_k| < \sqrt{Z_k / m}$.
    have h_bound : ∀ᶠ k in Filter.atTop, |S k| < |E k| + Real.sqrt (Z k / m) := by
      filter_upwards [ h_ineq, hZ.eventually ( lt_mem_nhds one_pos ) ] with k hk₁ hk₂;
      -- Taking square roots on both sides of $m * (S k - E k) ^ 2 < Z k$, we get $|S k - E k| < \sqrt{Z k / m}$.
      have h_sqrt : |S k - E k| < Real.sqrt (Z k / m) := by
        exact Real.lt_sqrt_of_sq_lt ( by rw [ lt_div_iff₀ hm ] ; nlinarith [ abs_mul_abs_self ( S k - E k ) ] );
      cases abs_cases ( S k - E k ) <;> cases abs_cases ( S k ) <;> cases abs_cases ( E k ) <;> linarith;
    -- Squaring both sides of the inequality $|S_k| < |E_k| + \sqrt{Z_k / m}$, we get $S_k^2 < (|E_k| + \sqrt{Z_k / m}) ^ 2$.
    have h_sq_bound : ∀ᶠ k in Filter.atTop, m * (S k) ^ 2 < m * (|E k| + Real.sqrt (Z k / m)) ^ 2 := by
      filter_upwards [ h_bound ] with k hk using mul_lt_mul_of_pos_left ( by nlinarith only [ abs_lt.mp hk, abs_mul_abs_self ( S k ), abs_mul_abs_self ( E k ), Real.sqrt_nonneg ( Z k / m ) ] ) hm;
    -- The right-hand side tends to $m * (0 + \sqrt{1/m}) ^ 2 = m * (1/m) = 1$.
    have h_rhs_tendsto : Filter.Tendsto (fun k => m * (|E k| + Real.sqrt (Z k / m)) ^ 2) Filter.atTop (nhds 1) := by
      convert Filter.Tendsto.mul tendsto_const_nhds ( Filter.Tendsto.pow ( Filter.Tendsto.add ( hE.abs ) ( Filter.Tendsto.sqrt ( hZ.div_const m ) ) ) 2 ) using 2 ; norm_num [ hm.ne' ];
      rw [ Real.sq_sqrt hm.le, mul_inv_cancel₀ hm.ne' ];
    refine le_trans
      ( Filter.limsup_le_limsup
        (v := fun k => m * ( |E k| + Real.sqrt ( Z k / m ) ) ^ 2)
        ?_ ?_ ?_ )
      ?_;
    · filter_upwards [ h_sq_bound ] with k hk using le_of_lt hk;
    · exact ⟨ 0, fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ k, hk ⟩ ; exact le_trans ( by positivity ) ( hk _ le_rfl ) ⟩;
    · exact Filter.Tendsto.isBoundedUnder_le h_rhs_tendsto;
    · rw [ h_rhs_tendsto.limsup_eq ]

/-
The sum of the sizes of B_i equals the size of A.
-/
lemma sum_card_B_eq_card_A (A : Finset ℕ) (m : ℕ) (hm : m > 0) :
  ∑ i ∈ Finset.range m, (B_finset_new A m i).card = A.card := by
    rw [ Finset.sum_congr rfl ( fun i hi => card_B_eq_card_A_filter A m i hm ) ];
    rw [ ← Finset.card_biUnion ];
    · congr with x ; simp +decide [ Nat.mod_lt _ hm ];
    · exact fun i hi j hj hij => Finset.disjoint_filter.2 fun k hk₁ hk₂ => by aesop;

/-
Algebraic transformation of the inequality by dividing by n^(3/2).
-/
lemma inequality_algebraic_transform_v2 (m : ℕ) (r : ℕ → ℝ) (n : ℝ) (C : ℝ) (hn : 0 < n)
  (h_nonneg : ∀ i ∈ Finset.range m, 0 ≤ r i) :
  (m : ℝ) * (∑ i ∈ Finset.range m, r i * (Real.sqrt (r i) - 2)) ^ 2 < C * n →
  (m : ℝ) * (∑ i ∈ Finset.range m, ((r i / Real.sqrt n) ^ (3 / 2 : ℝ) - 2 * r i / n ^ (3/4 : ℝ))) ^ 2 < C / Real.sqrt n := by
    convert inequality_algebraic_transform m r n C hn h_nonneg using 1

/-
The sum over indices with non-empty B_i equals the sum over all indices.
-/
lemma sum_diffs_eq_sum_subset (A : Finset ℕ) (m : ℕ) :
  let I := (Finset.range m).filter (fun i => 0 < (B_finset_new A m i).card)
  ∑ i ∈ I, ((B_finset_new A m i).card : ℝ) * (Real.sqrt (B_finset_new A m i).card - 2) =
  ∑ i ∈ Finset.range m, ((B_finset_new A m i).card : ℝ) * (Real.sqrt (B_finset_new A m i).card - 2) := by
    convert Finset.sum_subset _ _ <;> intro i hi <;> aesop

/-
Upper bound for S_total, handling empty B_i.
-/
lemma S_total_upper_bound_relaxed (A : Finset ℕ) (m : ℕ) (hm : 2 ≤ m) (s : ℕ → ℕ) (n : ℕ)
  (hA : IsSidonSetNat (A : Set ℕ)) (hA_bound : ∀ x ∈ A, x ≤ n)
  (h_s_prop : ∀ i < m, s i = calc_s (B_finset_new A m i).card) :
  2 * (S_total A m s : ℝ) ≤ (A.card : ℝ) * (n / m : ℝ) := by
    -- Applying the upper bound for each term in the sum.
    have h_sum_upper_bound : ∑ i ∈ Finset.range m, ∑ x ∈ diffs_le_s_set (B_finset_new A m i) (s i), x ≤ ∑ i ∈ Finset.range m, (s i * (s i + 1) / 2) * (n / m) := by
      apply Finset.sum_le_sum;
      intro i hi; by_cases hi' : 0 < ( B_finset_new A m i |> Finset.card ) <;> simp_all +decide ;
      · have h_sum_diffs_le_s_bound : sum_diffs_le_s (B_finset_new A m i) (calc_s (B_finset_new A m i).card) ≤ (calc_s (B_finset_new A m i).card * (calc_s (B_finset_new A m i).card + 1) / 2) * (n / m) := by
          apply sum_diffs_le_s_bound;
          · convert B_is_sidon A m i hm hA using 1;
            exact B_finset_new_eq_B A m i ( by linarith );
          · exact calc_s_lt_r _ ( Finset.card_pos.mpr hi' );
          · exact fun x a => B_finset_bound A m i n hA_bound x a;
        rw [ ← sum_diffs_le_s_eq_sum_set ]
        focus aesop
        · have hB_sidon : IsSidonSetNat (B (A : Set ℕ) m i) := by
            exact B_is_sidon (↑A) m i hm hA;
          convert hB_sidon using 1;
          exact B_finset_new_eq_B _ _ _ ( by linarith );
        · exact calc_s_lt_r _ ( Finset.card_pos.mpr hi' ) |> lt_of_lt_of_le <| by linarith;
      · exact tsub_add_cancel_iff_le.mp rfl;
    -- Using the fact that $s_i(s_i+1) \leq |B_i|$ and $\sum_{i=0}^{m-1} |B_i| = |A|$, we can further simplify the upper bound.
    have h_sum_simplified : ∑ i ∈ Finset.range m, (s i * (s i + 1) / 2) * (n / m) ≤ (n / m) * (A.card / 2) := by
      have h_sum_simplified : ∑ i ∈ Finset.range m, (s i * (s i + 1) / 2) ≤ (A.card / 2) := by
        have h_sum_simplified : ∑ i ∈ Finset.range m, (s i * (s i + 1)) ≤ A.card := by
          have h_sum_simplified : ∑ i ∈ Finset.range m, s i * (s i + 1) ≤ ∑ i ∈ Finset.range m, (B_finset_new A m i).card := by
            exact Finset.sum_le_sum fun i hi => by rw [ h_s_prop i ( Finset.mem_range.mp hi ) ] ; exact calc_s_prop _ |>.1;
          exact h_sum_simplified.trans ( by rw [ sum_card_B_eq_card_A A m ( by linarith ) ] );
        rw [ Nat.le_div_iff_mul_le ] <;> norm_num;
        exact le_trans ( by rw [ Finset.sum_mul _ _ _ ] ; exact Finset.sum_le_sum fun _ _ => Nat.div_mul_le_self _ _ ) h_sum_simplified;
      rw [ ← Finset.sum_mul _ _ _ ] ; nlinarith [ Nat.zero_le ( n / m ) ] ;
    -- By definition of $S_total$, we have $S_total A m s = \sum_{i=0}^{m-1} \sum_{x \in \text{diffs\_le\_s\_set}(B_i, s_i)} x$.
    have h_S_total_eq_sum : S_total A m s = ∑ i ∈ Finset.range m, ∑ x ∈ diffs_le_s_set (B_finset_new A m i) (s i), x := by
      unfold S_total total_diffs;
      rw [ Finset.sum_biUnion ];
      exact fun i hi j hj hij => disjoint_diffs_le_s_set A m hm s hA i j ( Finset.mem_range.mp hi ) ( Finset.mem_range.mp hj ) hij;
    rw [ mul_div, le_div_iff₀ ] <;> norm_cast;
    · nlinarith [ Nat.div_mul_le_self n m, Nat.div_mul_le_self A.card 2, Nat.zero_le ( n / m ), Nat.zero_le ( A.card / 2 ) ];
    · linarith

/-
Inequality 2.6 holds even if some B_i are empty.
-/
lemma inequality_2_6_relaxed (A : Finset ℕ) (m : ℕ) (hm : 2 ≤ m) (s : ℕ → ℕ) (n : ℕ)
  (hA : IsSidonSetNat (A : Set ℕ)) (hA_bound : ∀ x ∈ A, x ≤ n)
  (h_s_prop : ∀ i < m, s i = calc_s (B_finset_new A m i).card)
  (h_K_pos : (total_diffs A m s).card > 0)
  (h_sum_nonneg : 0 ≤ ∑ i ∈ Finset.range m, ((B_finset_new A m i).card : ℝ) * (Real.sqrt (B_finset_new A m i).card - 2)) :
  (m : ℝ) * (∑ i ∈ Finset.range m, ((B_finset_new A m i).card : ℝ) * (Real.sqrt (B_finset_new A m i).card - 2)) ^ 2 < (A.card : ℝ) * n := by
    -- Apply the upper bound to 2S_total.
    have h_upper_bound : 2 * (S_total A m s : ℝ) ≤ (A.card : ℝ) * (n / m : ℝ) := by
      convert S_total_upper_bound_relaxed A m hm s n hA hA_bound h_s_prop using 1;
    -- Apply the lower bound to 2S_total.
    have h_lower_bound : 2 * (S_total A m s : ℝ) > (∑ i ∈ Finset.range m, ((B_finset_new A m i).card : ℝ) * (Real.sqrt (B_finset_new A m i).card - 2)) ^ 2 := by
      convert S_subset_lower_bound A m hm s hA h_s_prop _ _ _ using 1 <;> norm_num [ h_K_pos, h_sum_nonneg ];
      any_goals exact Finset.filter ( fun i => 0 < ( B_finset_new A m i |> Finset.card ) ) ( Finset.range m );
      · rw [ show ( total_diffs_subset A m s ( Finset.filter ( fun i => 0 < ( B_finset_new A m i |> Finset.card ) ) ( Finset.range m ) ) ) = total_diffs A m s from ?_ ];
        · rw [ show ( ∑ i ∈ Finset.range m with 0 < ( B_finset_new A m i |> Finset.card ), ( B_finset_new A m i |> Finset.card : ℝ ) * ( Real.sqrt ( B_finset_new A m i |> Finset.card ) - 2 ) ) = ( ∑ i ∈ Finset.range m, ( B_finset_new A m i |> Finset.card : ℝ ) * ( Real.sqrt ( B_finset_new A m i |> Finset.card ) - 2 ) ) from ?_ ];
          · unfold S_total; aesop;
          · exact sum_diffs_eq_sum_subset A m;
        · exact Eq.symm (total_diffs_eq_subset_pos A m s);
      · simp +decide;
      · exact Finset.card_pos.mp ( by simpa [ total_diffs_eq_subset_pos ] using h_K_pos );
    nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ m ), mul_div_cancel₀ ( n : ℝ ) ( by positivity : ( m : ℝ ) ≠ 0 ) ]

/-
Eventually, m * (S_k - E_k) ^ 2 < Z_k.
-/
lemma transformed_inequality_eventually
  (m : ℕ) (hm : 2 ≤ m)
  (n_seq : ℕ → ℕ) (A_seq : ℕ → Finset ℕ)
  (h_n_tendsto : Filter.Tendsto (fun k => (n_seq k : ℝ)) Filter.atTop Filter.atTop)
  (h_subset : ∀ k, ∀ x ∈ A_seq k, x ≤ n_seq k)
  (h_sidon : ∀ k, IsSidonSetNat (A_seq k : Set ℕ))
  (h_card : Filter.Tendsto (fun k => ((A_seq k).card : ℝ) / Real.sqrt (n_seq k)) Filter.atTop (nhds 1)) :
  let v (k : ℕ) (i : Fin m) : ℝ := ((A_seq k).filter (fun a => a % m = i)).card / Real.sqrt (n_seq k)
  let E (k : ℕ) : ℝ := 2 * (A_seq k).card / (n_seq k : ℝ) ^ (3/4 : ℝ)
  ∀ᶠ k in Filter.atTop, (m : ℝ) * (∑ i, (v k i) ^ (3 / 2 : ℝ) - E k) ^ 2 < (A_seq k).card / Real.sqrt (n_seq k) := by
    have h_eventually : ∀ᶠ k in Filter.atTop, (total_diffs (A_seq k) m (fun i => calc_s ((B_finset_new (A_seq k) m i).card))).card > 0 ∧ 0 ≤ ∑ i ∈ Finset.range m, ((B_finset_new (A_seq k) m i).card : ℝ) * (Real.sqrt (B_finset_new (A_seq k) m i).card - 2) := by
      convert eventually_inequality_premises n_seq A_seq h_n_tendsto h_card m hm using 1;
    filter_upwards [ h_eventually, h_card.eventually ( Metric.ball_mem_nhds _ zero_lt_one ) ] with k hk₁ hk₂;
    convert inequality_algebraic_transform_v2 m ( fun i => ( B_finset_new ( A_seq k ) m i |> Finset.card : ℝ ) ) ( n_seq k ) ( A_seq k |> Finset.card ) ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by aesop_cat ) ( fun i hi => Nat.cast_nonneg _ ) ?_ using 1;
    · rw [ Finset.sum_congr rfl fun i hi => ?_ ];
      rotate_left;
      focus
        use fun i => ( ( B_finset_new ( A_seq k ) m i |> Finset.card : ℝ ) / Real.sqrt ( n_seq k ) ) ^ ( 3 / 2 : ℝ )
      · rw [ card_B_eq_card_A_filter ];
        linarith;
      · simp +decide [Finset.sum_range];
        norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_div ];
        rw [ show ( ∑ i : Fin m, ( B_finset_new ( A_seq k ) m i |> Finset.card : ℝ ) ) = ( A_seq k |> Finset.card : ℝ ) from mod_cast ?_ ]
        focus norm_num [ mul_div_assoc ]
        convert sum_card_B_eq_card_A ( A_seq k ) m ( by linarith ) using 1;
        rw [ Finset.sum_range ];
    · convert inequality_2_6_relaxed ( A_seq k ) m hm ( fun i => calc_s ( B_finset_new ( A_seq k ) m i |> Finset.card ) ) ( n_seq k ) ( h_sidon k ) ( fun x hx => h_subset k x hx ) ( fun i hi => rfl ) hk₁.1 hk₁.2 using 1

/-
Main theorem: density of A_i converges to 1/m.
-/
theorem sidon_density_limit
  (m : ℕ) (hm : 2 ≤ m)
  (n_seq : ℕ → ℕ) (A_seq : ℕ → Finset ℕ)
  (h_n_tendsto : Filter.Tendsto (fun k => (n_seq k : ℝ)) Filter.atTop Filter.atTop)
  (h_subset : ∀ k, ∀ x ∈ A_seq k, x ≤ n_seq k)
  (h_sidon : ∀ k, IsSidonSetNat (A_seq k : Set ℕ))
  (h_card : Filter.Tendsto (fun k => ((A_seq k).card : ℝ) / Real.sqrt (n_seq k)) Filter.atTop (nhds 1)) :
  ∀ i < m, Filter.Tendsto (fun k => (((A_seq k).filter (fun a => a % m = i)).card : ℝ) / Real.sqrt (n_seq k)) Filter.atTop (nhds (1 / m)) := by
    -- By definition of $v_k$, we know that $\sum_{i=1}^{m} v_k(i) \to 1$.
    have h_sum_v : Filter.Tendsto (fun k => ∑ i : Fin m, ((A_seq k).filter (fun a => a % m = i)).card / Real.sqrt (n_seq k)) Filter.atTop (nhds 1) := by
      convert h_card using 2;
      rw [ ← Finset.sum_div _ _ _, ← Nat.cast_sum ];
      rw [ ← Finset.card_biUnion ];
      · congr with x ; simp +decide;
        exact fun hx => ⟨ ⟨ x % m, Nat.mod_lt _ ( by linarith ) ⟩, rfl ⟩;
      · exact fun i _ j _ hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| Fin.ext <| by aesop;
    -- By definition of $v_k$, we know that $m * (\sum_{i=1}^{m} v_k(i)^{3/2} - E_k) ^ 2 < Z_k$ eventually.
    have h_ineq : ∀ᶠ k in Filter.atTop, (m : ℝ) * (∑ i : Fin m, (((A_seq k).filter (fun a => a % m = i)).card / Real.sqrt (n_seq k)) ^ (3 / 2 : ℝ) - 2 * (A_seq k).card / (n_seq k : ℝ) ^ (3/4 : ℝ)) ^ 2 < (A_seq k).card / Real.sqrt (n_seq k) := by
      convert transformed_inequality_eventually m hm n_seq A_seq h_n_tendsto h_subset h_sidon h_card using 1;
    -- By definition of $v_k$, we know that $E_k \to 0$ and $Z_k \to 1$.
    have h_E_zero : Filter.Tendsto (fun k => 2 * (A_seq k).card / (n_seq k : ℝ) ^ (3/4 : ℝ)) Filter.atTop (nhds 0) := by
      convert error_term_tendsto_zero n_seq A_seq h_n_tendsto h_card using 1
    have h_Z_one : Filter.Tendsto (fun k => (A_seq k).card / Real.sqrt (n_seq k)) Filter.atTop (nhds 1) := by
      convert h_card using 1;
    -- By definition of $v_k$, we know that $\limsup_{k \to \infty} m * (\sum_{i=1}^{m} v_k(i)^{3/2}) ^ 2 \leq 1$.
    have h_limsup : Filter.limsup (fun k => (m : ℝ) * (∑ i : Fin m, (((A_seq k).filter (fun a => a % m = i)).card / Real.sqrt (n_seq k)) ^ (3 / 2 : ℝ)) ^ 2) Filter.atTop ≤ 1 := by
      apply_rules [ limsup_le_of_sub_sq_le ];
      positivity;
    -- By definition of $v_k$, we know that $v_k \to \frac{1}{m}$.
    have h_v_const : Filter.Tendsto (fun k => fun i : Fin m => ((A_seq k).filter (fun a => a % m = i)).card / Real.sqrt (n_seq k)) Filter.atTop (nhds (fun _ => 1 / m)) := by
      apply sequence_convergence_to_constant_fin m hm (fun k i => ((A_seq k).filter (fun a => a % m = i)).card / Real.sqrt (n_seq k)) (fun k i => by
        positivity) (by
      convert h_sum_v using 1) (by
      convert h_limsup using 1);
    intro i hi; specialize h_v_const; rw [ tendsto_pi_nhds ] at h_v_const; specialize h_v_const ⟨ i, hi ⟩ ; aesop;

#print axioms sidon_density_limit
-- 'Erdos154.sidon_density_limit' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos154
