/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
MIT License

Copyright (c) 2026 Axiom Math.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

This file has been modified for Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 328. The imported C = 2 argument and formal proof are by AxiomProver.
Published by Axiom Math. The stronger historical result is due to Nešetřil and Rödl.
Source: https://www.erdosproblems.com/forum/thread/328#post-7066
https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos328/solution.lean
Original Lean/Mathlib version: 4.27.0.
-/
import Mathlib

set_option linter.mathlibStandardSet false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos328

/-
# Disproof of Erdős Problem 328

**Problem description.**
For a set $A \subseteq \mathbb{N}$, the additive representation function is
$r_A(n) = \#\{(x, y) \in A \times A : x + y = n\}$ (counting ordered pairs).

Erdős conjectured (Problem 328) that if $r_A(n) \leq C$ for all $n$, then $A$ can be
partitioned into $t = t(C)$ parts $A_1, \ldots, A_t$ (where $t$ depends only on $C$)
such that $r_{A_i}(n) < C$ for all $i$ and all $n$.

This was disproved by Nešetřil and Rödl (1985). We formalize the negation.

**Disproof strategy used here.** While Nešetřil–Rödl give a deep construction valid
for every integer $k \geq 2$, the negation for the *specific* value $C = 2$ admits a
much simpler argument that we use here:

- Take $A := \{2^k : k \in \mathbb{N}\}$, the set of powers of two.
- The set $A$ is a Sidon set: by uniqueness of binary representations, every
  natural number has at most $2$ ordered representations as $2^a + 2^b$ with
  $a, b \in \mathbb{N}$. Hence $r_A(n) \leq 2$ for all $n$.
- The set $A$ is infinite. Therefore, for every finite partition $A = A_1 \cup \cdots
  \cup A_t$ (with $t \geq 1$), pigeonhole forces some part $A_i$ to be infinite,
  in particular to contain two distinct elements $x \neq y$. Then the ordered pairs
  $(x, y)$ and $(y, x)$ both witness $r_{A_i}(x + y) \geq 2$.

**References.**
1. J. Nešetřil and V. Rödl, *Two Proofs in Combinatorial Number Theory*,
   Proc. Amer. Math. Soc. 93 (1985), no. 1, 185–188.
2. Erdős Problem 328, https://www.erdosproblems.com/328.
-/

-- Main Definition(s)

/-- The additive representation function: counts ordered pairs $(a, b) \in A \times A$
with $a + b = n$. Since both components are bounded by $n$, this is always finite. -/
noncomputable def additiveRepresentation (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

/-- A partition of a set $A$ into $t$ parts is a family of sets indexed by `Fin t`
that are pairwise disjoint and whose union equals $A$. Empty parts are allowed. -/
def IsPartition (A : Set ℕ) (t : ℕ) (P : Fin t → Set ℕ) : Prop :=
  (⋃ i, P i) = A ∧
  Set.PairwiseDisjoint (Set.univ : Set (Fin t)) P

-- Correctness statements for additiveRepresentation

/-- The set of pairs summing to $n$ is always finite (both components are at most $n$). -/
theorem additiveRepresentation_finite (A : Set ℕ) (n : ℕ) :
    Set.Finite {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} := by
  apply Set.Finite.subset (Set.Finite.prod (Set.finite_Iic n) (Set.finite_Iic n))
  rintro ⟨x, y⟩ ⟨_, _, hxy⟩
  simp only [Set.mem_prod, Set.mem_Iic]
  omega

/-- `additiveRepresentation` agrees with `Nat.card` of the corresponding subtype. -/
theorem additiveRepresentation_eq_natCard (A : Set ℕ) (n : ℕ) :
    additiveRepresentation A n =
      Nat.card {p : ℕ × ℕ // p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} := by
  unfold additiveRepresentation
  exact (Nat.card_coe_set_eq _).symm

/-- The set of powers of two: $A = \{2^k : k \in \mathbb{N}\}$. This is the witness
set for our disproof. -/
def pow2Set : Set ℕ := Set.range (fun k : ℕ => 2^k)

/-- The set of powers of two is infinite (since $k \mapsto 2^k$ is injective). -/
lemma pow2Set_infinite : pow2Set.Infinite := by
  apply Set.infinite_range_of_injective
  exact Nat.pow_right_injective (by norm_num)

/-- **Key uniqueness sub-lemma.** If `2^a + 2^b = 2^c + 2^d` then either
`(a = c ∧ b = d)` or `(a = d ∧ b = c)`. Every natural number has at most one
unordered representation as a sum of two powers of two. -/
lemma pow2_pair_sum_unique (a b c d : ℕ) (h : 2^a + 2^b = 2^c + 2^d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  -- WLOG a ≤ b.
  wlog hab : a ≤ b with H1
  · push Not at hab
    have hab' : b ≤ a := le_of_lt hab
    rw [Nat.add_comm (2^a) (2^b)] at h
    rcases H1 b a c d h hab' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; exact ⟨h2, h1⟩
    · left; exact ⟨h2, h1⟩
  -- WLOG c ≤ d.
  wlog hcd : c ≤ d with H2
  · push Not at hcd
    have hcd' : d ≤ c := le_of_lt hcd
    rw [Nat.add_comm (2^c) (2^d)] at h
    rcases H2 a b d c h hab hcd' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; exact ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
  -- WLOG b ≤ d (swap the two halves of the equation).
  wlog hbd : b ≤ d with H3
  · push Not at hbd
    have hbd' : d ≤ b := le_of_lt hbd
    rcases H3 c d a b h.symm hcd hab hbd' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1.symm, h2.symm⟩
    · right; exact ⟨h2.symm, h1.symm⟩
  -- Now a ≤ b ≤ d, c ≤ d.
  have hpow_pos : ∀ k : ℕ, 0 < 2^k := fun k => Nat.two_pow_pos k
  have h2a_le_2b : 2^a ≤ 2^b := Nat.pow_le_pow_right (by norm_num) hab
  have h2c_pos : 0 < 2^c := hpow_pos c
  -- 2^d ≤ 2^a + 2^b ≤ 2^b + 2^b = 2^(b+1).
  have h2d_le : 2^d ≤ 2^(b+1) := by
    have heq : 2^b + 2^b = 2^(b+1) := by ring
    have h_le : 2^d ≤ 2^a + 2^b := by linarith
    linarith
  -- Hence d ≤ b + 1.
  have hd_le : d ≤ b + 1 := by
    rcases Nat.lt_or_ge d (b+1+1) with h | h
    · omega
    · exfalso
      have : 2^(b+1+1) ≤ 2^d := Nat.pow_le_pow_right (by norm_num) h
      have h1 : 2^(b+1+1) = 2 * 2^(b+1) := by ring
      have h2 : 2^(b+1) > 0 := hpow_pos (b+1)
      linarith
  -- d ∈ {b, b+1}.
  rcases (eq_or_lt_of_le hbd) with hdb | hbd_lt
  · -- Case d = b: subtract to get 2^a = 2^c, then injectivity.
    rw [← hdb] at h
    have heq : 2^a = 2^c := by linarith
    have hac : a = c := Nat.pow_right_injective (by norm_num : 2 ≤ 2) heq
    left; exact ⟨hac, hdb⟩
  · -- Case d = b + 1: derive contradiction (would force 2^c = 0).
    have hdb : d = b + 1 := by omega
    rw [hdb] at h
    have h2pow : 2^(b+1) = 2 * 2^b := by ring
    rw [h2pow] at h
    omega

/-- **Sidon (B₂) property of powers of 2.** For `A = {2^k : k ∈ ℕ}`, the additive
representation function is bounded by `2`.

The proof reduces to `pow2_pair_sum_unique`: given `n`, either `n` has no
representation as `2^a + 2^b` (in which case the representation set is empty),
or it has some representation `(a₀, b₀)`, and then by the uniqueness lemma every
other representation is `(a₀, b₀)` or `(b₀, a₀)`, so the set has at most 2
elements. -/
lemma pow2Set_rep_le_two (n : ℕ) : additiveRepresentation pow2Set n ≤ 2 := by
  unfold additiveRepresentation pow2Set
  set S : Set (ℕ × ℕ) :=
    {p | (p.1 ∈ Set.range fun k : ℕ => 2^k) ∧
         (p.2 ∈ Set.range fun k : ℕ => 2^k) ∧ p.1 + p.2 = n} with hS_def
  by_cases hn : ∃ a b, 2^a + 2^b = n
  · obtain ⟨a₀, b₀, hab⟩ := hn
    have hT_fin : ({(2^a₀, 2^b₀), (2^b₀, 2^a₀)} : Set (ℕ × ℕ)).Finite :=
      (Set.finite_singleton _).insert _
    have hsub : S ⊆ {(2^a₀, 2^b₀), (2^b₀, 2^a₀)} := by
      rintro ⟨x, y⟩ ⟨⟨a, hxa⟩, ⟨b, hyb⟩, hxy⟩
      simp only at hxa hyb
      subst hxa; subst hyb
      rw [← hab] at hxy
      rcases pow2_pair_sum_unique a b a₀ b₀ hxy with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · subst ha; subst hb; simp
      · subst ha; subst hb; simp
    calc S.ncard ≤ ({(2^a₀, 2^b₀), (2^b₀, 2^a₀)} : Set (ℕ × ℕ)).ncard :=
            Set.ncard_le_ncard hsub hT_fin
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
  · push Not at hn
    have hempty : S = ∅ := by
      ext ⟨x, y⟩
      simp only [hS_def, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩, hxy⟩
      exact hn a b hxy
    rw [hempty]
    simp

/-- If a set contains two distinct elements `x` and `y`, then the additive
representation function at `x + y` is at least `2`: the ordered pairs `(x, y)`
and `(y, x)` are distinct elements of the representation set. -/
lemma additiveRepresentation_ge_two_of_two_distinct
    (B : Set ℕ) (x y : ℕ) (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y) :
    2 ≤ additiveRepresentation B (x + y) := by
  unfold additiveRepresentation
  set S : Set (ℕ × ℕ) := {p | p.1 ∈ B ∧ p.2 ∈ B ∧ p.1 + p.2 = x + y}
  have h1 : (x, y) ∈ S := ⟨hx, hy, rfl⟩
  have h2 : (y, x) ∈ S := ⟨hy, hx, by ring⟩
  have hne : (x, y) ≠ (y, x) := fun h => hxy (Prod.mk.inj h).1
  have hsub : ({(x, y), (y, x)} : Set (ℕ × ℕ)) ⊆ S := by
    intro p hp
    rcases hp with hp | hp
    · subst hp; exact h1
    · simp at hp; subst hp; exact h2
  have h3 : Set.ncard ({(x, y), (y, x)} : Set (ℕ × ℕ)) = 2 := Set.ncard_pair hne
  have hfin : S.Finite := additiveRepresentation_finite B (x + y)
  calc 2 = Set.ncard ({(x, y), (y, x)} : Set (ℕ × ℕ)) := h3.symm
    _ ≤ S.ncard := Set.ncard_le_ncard hsub hfin

/-- Pigeonhole for sets: if a finite-indexed union of sets is infinite,
some indexed set is infinite. -/
lemma exists_infinite_part_of_infinite_union {t : ℕ} (P : Fin t → Set ℕ)
    (h : (⋃ i, P i).Infinite) : ∃ i, (P i).Infinite := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [show (⋃ i, P i) = (⋃ i ∈ (Set.univ : Set (Fin t)), P i) by simp]
  exact Set.Finite.biUnion Set.finite_univ (fun i _ => hcon i)

/-- Any infinite set of naturals contains two distinct elements. -/
lemma exists_two_distinct_of_infinite (S : Set ℕ) (h : S.Infinite) :
    ∃ x y, x ∈ S ∧ y ∈ S ∧ x ≠ y := by
  obtain ⟨x, hx⟩ := h.nonempty
  obtain ⟨y, hy, hyx⟩ := (h.sdiff (Set.finite_singleton x)).nonempty
  exact ⟨x, y, hx, hy, fun h => hyx (h ▸ rfl)⟩

-- Main Statement(s)

/-- **Disproof of Erdős Problem 328.**
There exists $C \geq 2$ such that for every positive integer $t$, there is a set
$A \subseteq \mathbb{N}$ with $r_A(n) \leq C$ for all $n$, yet for every partition of $A$
into $t$ parts, at least one part $A_i$ satisfies $r_{A_i}(n) \geq C$ for some $n$.

**Proof.** Take `C := 2` and `A := pow2Set = {2^k : k ∈ ℕ}`.
- `pow2Set_rep_le_two` gives `r_A(n) ≤ 2` for all `n`.
- For any partition of `A` into `t` parts, the union of the parts equals `A`,
  which is infinite (`pow2Set_infinite`); by pigeonhole some part `P i` is
  infinite, hence contains two distinct elements `x ≠ y`; then the lemma
  `additiveRepresentation_ge_two_of_two_distinct` gives `r_{P i}(x + y) ≥ 2`. -/
theorem erdos_problem_328_disproof :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      ∃ A : Set ℕ,
        (∀ n : ℕ, additiveRepresentation A n ≤ C) ∧
        (∀ P : Fin t → Set ℕ, IsPartition A t P →
          ∃ i : Fin t, ∃ n : ℕ, C ≤ additiveRepresentation (P i) n) := by
  -- Witness: C = 2, A = pow2Set.
  refine ⟨2, le_refl 2, ?_⟩
  intro t _
  refine ⟨pow2Set, pow2Set_rep_le_two, ?_⟩
  -- Given any partition of pow2Set into t parts, find an i and an n with r ≥ 2.
  intro P hP
  obtain ⟨hcup, _⟩ := hP
  have hAinf : pow2Set.Infinite := pow2Set_infinite
  have hUinf : (⋃ i, P i).Infinite := by
    rw [hcup]; exact hAinf
  obtain ⟨i, hPi_inf⟩ := exists_infinite_part_of_infinite_union P hUinf
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_distinct_of_infinite (P i) hPi_inf
  exact ⟨i, x + y, additiveRepresentation_ge_two_of_two_distinct (P i) x y hx hy hxy⟩

end Erdos328
