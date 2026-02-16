/-

This is a Lean formalization of a solution to Erdős Problem 487
https://www.erdosproblems.com/forum/thread/487

The original proof was found by: Kleitman

[Kl71] Kleitman, Daniel, Collections of subsets containing no two sets
and their union. Proceedings of the LA Meeting AMS (1971), 153-155.


Kleitman's proof was auto-formalized by Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have formally proved the main theorem of the paper: any subset of the natural numbers with positive lower asymptotic density contains a distinct triple $\{a, b, c\}$ such that $\text{lcm}(a, b) = c$.

The proof follows the strategy outlined in the paper:
1.  **Reduction to odd integers**: We use the fact that if $A$ has positive lower density, then for some $t$, the set $B_t = \{a/2^t : a \in A, v_2(a) = t\}$ has positive upper logarithmic density (and consists of odd integers). This relies on the provided lemmas `exists_t_upper_log_density_At_pos` and `upper_log_density_Bt`.
2.  **Upper bound for lcm-triple free sets**: We use the provided result `I_N_upper_bound_asymptotic` (which relies on Kleitman's bound) to show that if a set is lcm-triple free, the quantity $I(N)$ grows slower than $N \log N$.
3.  **Lower bound for sets with positive density**: We show that if a set has positive upper logarithmic density, then $I(N)$ must grow at least as fast as $N \log N$ along a subsequence. This is formalized in `lcm_triple_of_upper_log_density_pos`.
4.  **Contradiction**: Combining the upper and lower bounds yields a contradiction, proving that the set must contain an lcm-triple.

Key intermediate lemmas proved include:
*   `lcm_triple_of_upper_log_density_pos`: The core argument for odd integers.
*   `upper_log_density_Bt`: Relates the density of $B_t$ to $A_t$.
*   `limsup_log_density_stretch`: A technical lemma for handling the density scaling.
*   `lcm_triple_exists`: The final theorem.
-/

/-
Formalized the definitions and theorems from the paper "Union-free families and Kleitman's asymptotic bound", including the main result `kleitman_asymptotic` which establishes that the size of a union-free family is asymptotically bounded by the central binomial coefficient. The formalization covers the Erdős-Ko-Rado lemma, Kleitman's chain inequality, the linear programming bound, weak duality, and the construction of the dual feasible solution.
-/

import Mathlib

namespace Erdos447

set_option linter.mathlibStandardSet false

open scoped Nat
open scoped Classical
open Asymptotics Filter

set_option maxHeartbeats 0

/-
A family F is union-free if there do not exist distinct A, B, C in F with A ∪ B = C.
-/
def UnionFree {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → B ≠ C → A ≠ C → A ∪ B ≠ C

/-
Let m be a natural number and 1 ≤ r ≤ m/2. If G is a family of r-subsets of [m] that is intersecting, then |G| ≤ binom(m-1)(r-1).
-/
lemma erdos_ko_rado_range (m r : ℕ) (hrm : r ≤ m / 2) (G : Finset (Finset (Fin m)))
    (hG_size : ∀ A ∈ G, A.card = r)
    (hG_inter : (G : Set (Finset (Fin m))).Intersecting) :
    G.card ≤ (m - 1).choose (r - 1) := by
  exact Finset.erdos_ko_rado hG_inter hG_size hrm

/-
The family of differences A \ B for B in F strictly contained in A is intersecting.
-/
def DifferenceFamily {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) (k : ℕ) : Finset (Finset (Fin n)) :=
  (F.filter (λ B => B ⊂ A ∧ k ≤ B.card)).image (λ B => A \ B)

lemma difference_family_intersecting {n : ℕ} (F : Finset (Finset (Fin n))) (hF : UnionFree F)
    (A : Finset (Fin n)) (hA : A ∈ F) (k : ℕ) :
    (DifferenceFamily F A k : Set (Finset (Fin n))).Intersecting := by
  intro B hB C hC hE2;
  -- Then there exist $D, E \in F$ such that $B = A \setminus D$ and $C = A \setminus E$ with $D \neq A$ and $E \neq A$.
  obtain ⟨D, hD₁, hD₂⟩ : ∃ D ∈ F, D ⊂ A ∧ B = A \ D := by
    unfold DifferenceFamily at hB; aesop;
  obtain ⟨E, hE₁, hE₂⟩ : ∃ E ∈ F, E ⊂ A ∧ C = A \ E := by
    unfold DifferenceFamily at hC; aesop;
  simp_all +decide [ Finset.disjoint_left ];
  -- Since $B$ and $C$ are disjoint, we have $A \setminus D \subseteq E$ and $A \setminus E \subseteq D$, which implies $A \subseteq D \cup E$.
  have h_union : A ⊆ D ∪ E := by
    exact fun x hx => if hx' : x ∈ D then Finset.mem_union_left _ hx' else Finset.mem_union_right _ ( hE2 hx hx' );
  have := hF D hD₁ E hE₁ A hA; simp_all +decide [ Finset.ssubset_def ] ;
  exact this ( by rintro rfl; exact hE₂.1.2 <| by aesop ) ( by rintro rfl; exact hE₂.1.2 <| by aesop ) ( by rintro rfl; exact hD₂.1.2 <| by aesop ) <| Finset.Subset.antisymm ( Finset.union_subset hD₂.1.1 hE₂.1.1 ) h_union

/-
The family of supersets of differences is intersecting.
-/
def SuperSets {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) (k : ℕ) : Finset (Finset (Fin n)) :=
  (A.powersetCard (A.card - k)).filter (λ S => ∃ E ∈ DifferenceFamily F A k, E ⊆ S)

lemma super_sets_intersecting {n : ℕ} (F : Finset (Finset (Fin n))) (hF : UnionFree F)
    (A : Finset (Fin n)) (hA : A ∈ F) (k : ℕ) :
    (SuperSets F A k : Set (Finset (Fin n))).Intersecting := by
  intro x hx y hy aesop;
  -- By definition of SuperSets, there exist E1, E2 ∈ DifferenceFamily such that E1 ⊆ x and E2 ⊆ y.
  obtain ⟨E1, hE1⟩ : ∃ E1 ∈ DifferenceFamily F A k, E1 ⊆ x := by
    unfold SuperSets at hx; aesop;
  obtain ⟨E2, hE2⟩ : ∃ E2 ∈ DifferenceFamily F A k, E2 ⊆ y := by
    unfold SuperSets at hy; aesop;
  -- By difference_family_intersecting, E1 ∩ E2 ≠ ∅.
  have h_inter : (E1 ∩ E2).Nonempty := by
    have := @difference_family_intersecting n F hF A hA k; simp_all +decide [ Set.Intersecting ] ;
    exact Finset.not_disjoint_iff_nonempty_inter.mp ( this hE1.1 hE2.1 );
  exact h_inter.elim fun z hz => Finset.disjoint_left.mp aesop ( hE1.2 ( Finset.mem_of_mem_inter_left hz ) ) ( hE2.2 ( Finset.mem_of_mem_inter_right hz ) )

/-
An embedding from the subtype of elements in A to the subtype of elements in S.
-/
def subSubsetEmbedding {α : Type*} [DecidableEq α] {S A : Finset α} (h : A ⊆ S) :
    {x // x ∈ A} ↪ {x // x ∈ S} :=
  ⟨λ x => ⟨x.1, h x.2⟩, by
    intro x y e
    apply Subtype.ext
    rw [Subtype.ext_iff] at e
    exact e⟩

/-
Map a subset A of S to a subset of the subtype {x // x ∈ S}.
-/
def toSubtype {α : Type*} [DecidableEq α] (S : Finset α) (A : Finset α) (h : A ⊆ S) : Finset {x // x ∈ S} :=
  A.attach.map (subSubsetEmbedding h)

/-
The cardinality of the subtype version of A is the same as the cardinality of A.
-/
lemma toSubtype_card {α : Type*} [DecidableEq α] (S : Finset α) (A : Finset α) (h : A ⊆ S) :
    (toSubtype S A h).card = A.card := by
  simp [toSubtype, Finset.card_map, Finset.card_attach]

/-
The mapping to subtypes is injective.
-/
lemma toSubtype_inj {α : Type*} [DecidableEq α] (S : Finset α) (A B : Finset α) (hA : A ⊆ S) (hB : B ⊆ S) :
    toSubtype S A hA = toSubtype S B hB ↔ A = B := by
  constructor
  · intro h
    ext x
    simp [toSubtype] at h
    -- If x ∈ A, then ⟨x, hA x⟩ ∈ toSubtype S A hA.
    -- So ⟨x, hA x⟩ ∈ toSubtype S B hB.
    -- This means there exists y ∈ B such that ⟨y, hB y⟩ = ⟨x, hA x⟩.
    -- So y = x, thus x ∈ B.
    -- Similarly for the other direction.
    replace h := congr_arg ( Finset.image ( fun x : { x // x ∈ S } => ( x : α ) ) ) h ; simp_all +decide [ Finset.ext_iff ] ;
    unfold subSubsetEmbedding at h; specialize h x; aesop;
  · intro h
    subst h
    rfl

/-
The Erdős-Ko-Rado theorem holds for any finite type.
-/
lemma erdos_ko_rado_fintype {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ)
    (hrm : r ≤ Fintype.card α / 2) (G : Finset (Finset α))
    (hG_size : ∀ A ∈ G, A.card = r)
    (hG_inter : (G : Set (Finset α)).Intersecting) :
    G.card ≤ (Fintype.card α - 1).choose (r - 1) := by
      -- Let's map each element of G to its image under the equivalence between α and Fin (Fintype.card α).
      set G_image := Finset.image (fun s : Finset α => Finset.image (fun x : α => Fintype.equivFin α x) s) G with hG_image_def
      have hG_image_card : G_image.card = G.card := by
        rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using Finset.image_injective ( Fintype.equivFin α |> Equiv.injective ) hxy ]
      have hG_image_inter : (G_image : Set (Finset (Fin (Fintype.card α)))).Intersecting := by
        intro A hA B hB hAB; obtain ⟨ s, hs, rfl ⟩ := Finset.mem_image.mp hA; obtain ⟨ t, ht, rfl ⟩ := Finset.mem_image.mp hB; simp_all +decide [ Finset.ext_iff ] ;
        exact absurd ( hG_inter hs ht ) ( by rw [ Finset.disjoint_left ] at *; aesop ) ;
      have hG_image_size : ∀ A ∈ G_image, A.card = r := by
        simp +zetaDelta at *;
        exact fun s hs => by rw [ Finset.card_image_of_injective _ ( Fintype.equivFin α |> Equiv.injective ), hG_size s hs ] ;
      have hG_image_subset : G_image ⊆ Finset.powersetCard r (Finset.univ : Finset (Fin (Fintype.card α))) := by
        exact fun x hx => Finset.mem_powersetCard.mpr ⟨ Finset.subset_univ _, hG_image_size x hx ⟩
      have hG_image_card_le : G_image.card ≤ Nat.choose (Fintype.card α - 1) (r - 1) := by
        convert erdos_ko_rado_range ( Fintype.card α ) r hrm G_image hG_image_size hG_image_inter using 1
      rw [hG_image_card] at hG_image_card_le; exact hG_image_card_le;

/-
Map a set in SuperSets to a subset of the subtype of A.
-/
def superSetsToSubtype {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) (k : ℕ)
    (B : Finset (Fin n)) (hB : B ∈ SuperSets F A k) : Finset {x // x ∈ A} :=
  toSubtype A B (by
    rw [SuperSets, Finset.mem_filter] at hB
    rw [Finset.mem_powersetCard] at hB
    exact hB.1.1)

/-
The family of supersets mapped to the subtype of A.
-/
def SuperSetsSubtype {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) (k : ℕ) : Finset (Finset {x // x ∈ A}) :=
  (SuperSets F A k).attach.map ⟨λ ⟨B, hB⟩ => superSetsToSubtype F A k B hB, by
    intro ⟨B1, hB1⟩ ⟨B2, hB2⟩ eq
    simp [superSetsToSubtype] at eq
    apply Subtype.ext
    have h1 : B1 ⊆ A := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hB1).1).1
    have h2 : B2 ⊆ A := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hB2).1).1
    exact (toSubtype_inj A B1 B2 h1 h2).mp eq⟩

/-
The subtype version of SuperSets is intersecting.
-/
lemma SuperSetsSubtype_intersecting {n : ℕ} (F : Finset (Finset (Fin n))) (hF : UnionFree F)
    (A : Finset (Fin n)) (hA : A ∈ F) (k : ℕ) :
    (SuperSetsSubtype F A k : Set (Finset {x // x ∈ A})).Intersecting := by
      unfold SuperSetsSubtype;
      intro x hx y hy; simp_all +decide
      rcases hx with ⟨ a, ha, rfl ⟩ ; rcases hy with ⟨ b, hb, rfl ⟩ ; simp_all +decide [ Finset.disjoint_left, superSetsToSubtype ] ;
      -- Since $a$ and $b$ are in $SuperSets F A k$, they are both subsets of $A$ and contain some element from the difference family.
      obtain ⟨x, hx⟩ : ∃ x, x ∈ a ∧ x ∈ b := by
        have := super_sets_intersecting F hF A hA k; simp_all +decide [ Set.Intersecting ] ;
        exact Finset.not_disjoint_iff.mp ( this ha hb );
      exact ⟨ x, by rw [ SuperSets ] at ha hb; rw [ Finset.mem_filter ] at ha hb; exact Finset.mem_powersetCard.mp ha.1 |>.1 hx.1, by unfold toSubtype; aesop ⟩

/-
The cardinality of the subtype version of SuperSets is the same as the original.
-/
lemma SuperSetsSubtype_card {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) (k : ℕ) :
    (SuperSetsSubtype F A k).card = (SuperSets F A k).card := by
  rw [SuperSetsSubtype]
  rw [Finset.card_map]
  rw [Finset.card_attach]

/-
Every set in the subtype version of SuperSets has size |A| - k.
-/
lemma SuperSetsSubtype_size {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) (k : ℕ) :
    ∀ B' ∈ SuperSetsSubtype F A k, B'.card = A.card - k := by
      intro B' hB'
      obtain ⟨B, hB, rfl⟩ := Finset.mem_map.mp hB'
      simp [superSetsToSubtype];
      rw [ toSubtype_card ];
      exact Finset.mem_powersetCard.mp ( Finset.mem_filter.mp B.2 |>.1 ) |>.2

/-
The size of SuperSets is bounded by binom(|A|-1, |A|-k-1).
-/
lemma super_sets_bound {n : ℕ} (F : Finset (Finset (Fin n))) (hF : UnionFree F)
    (A : Finset (Fin n)) (hA : A ∈ F) (k : ℕ) (hjk : A.card ≤ 2 * k) :
    (SuperSets F A k).card ≤ (A.card - 1).choose (A.card - k - 1) := by
      by_cases h : A.card ≤ k <;> simp_all +decide [ Nat.sub_sub ];
      · refine' Finset.card_le_one.mpr _;
        unfold SuperSets; aesop;
      · convert erdos_ko_rado_fintype ( A.card - k ) _ ( SuperSetsSubtype F A k ) _ _ using 1;
        · exact Eq.symm (SuperSetsSubtype_card F A k);
        · simp +decide [ Nat.sub_sub, Fintype.card_subtype ];
        · rw [ Fintype.card_subtype ] ; norm_num ; omega;
        · exact fun A_2 a ↦ SuperSetsSubtype_size F A k A_2 a;
        · convert SuperSetsSubtype_intersecting F hF A hA k using 1

/-
For $0\le j\le n$ set
\[
x_j=x_j(\cF):=\bigl|\cF\cap \bin{[n]}{j}\bigr|.
\]
-/
def x_j {n : ℕ} (F : Finset (Finset (Fin n))) (j : ℕ) : ℕ :=
  (F.filter (λ A => A.card = j)).card

/-
$S_j$ is the set of elements $\pi(i)$ for $i < j$. Wait, the paper says "set of the first $t$ elements of $\pi$". Usually this means $\{\pi(1), \dots, \pi(t)\}$.
Let's be precise. $\pi$ is a permutation of $[n]$. $S_t = \{\pi(1), \dots, \pi(t)\}$.
In Lean, `Equiv.Perm (Fin n)` maps `Fin n` to `Fin n`.
If we view `p` as the sequence $p(0), p(1), \dots, p(n-1)$, then the first $j$ elements are $\{p(0), \dots, p(j-1)\}$.
So `prefix_set p j` should be the image of `{0, ..., j-1}` under `p`.
My previous definition `(Finset.univ.filter (λ x => x.val < j)).map p.toEmbedding` was actually mapping `{0, ..., j-1}` via `p`, which is correct.
Wait, `p.toEmbedding` is the embedding corresponding to `p`.
So `prefix_set p j = {p(0), ..., p(j-1)}`.
Let's stick to that.
The previous definition `(Finset.univ.filter (λ x => x.val < j)).map p.toEmbedding` is correct.
Wait, I wrote `(Finset.univ.filter (λ x => p x < j))` in the thought block above, which is wrong (that would be the set of $x$ such that $p(x) < j$).
I will use the correct definition.
-/
def prefix_set {n : ℕ} (p : Equiv.Perm (Fin n)) (j : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (λ x => p x < j)).map (Equiv.refl (Fin n)).toEmbedding

/-
For each chain, if $\cF\cap\{S_k,S_{k+1},\dots,S_{2k}\}$ is nonempty, \emph{star} the smallest member of $\cF$ on the chain
(with respect to inclusion, equivalently with respect to size). Otherwise star nothing.
-/
def IsStarred {n : ℕ} (F : Finset (Finset (Fin n))) (p : Equiv.Perm (Fin n)) (A : Finset (Fin n)) (k : ℕ) : Prop :=
  A ∈ F ∧
  (∃ j, k ≤ j ∧ j ≤ 2 * k ∧ prefix_set p j = A ∧
    ∀ t, k ≤ t → t < j → prefix_set p t ∉ F)

/-
Call a $k$-subset $D\subseteq A$ \emph{bad} if there exists $B\in\cF$ with $D\subseteq B\subsetneq A$ and $|B|\ge k$.
-/
def is_bad_subset {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) (D : Finset (Fin n)) (k : ℕ) : Prop :=
  D ⊆ A ∧ D.card = k ∧ ∃ B ∈ F, D ⊆ B ∧ B ⊂ A

/-
The number of bad $k$-subsets of $A$ is at most $\binom{|A|-1}{k}$.
-/
lemma bad_subsets_count {n : ℕ} (F : Finset (Finset (Fin n))) (hF : UnionFree F)
    (A : Finset (Fin n)) (hA : A ∈ F) (k : ℕ) (hk : 1 ≤ k) (hjk : A.card ≤ 2 * k) :
    ((Finset.powersetCard k A).filter (λ D => is_bad_subset F A D k)).card ≤ (A.card - 1).choose k := by
      -- By the Erdős–Ko–Rado theorem, the number of $(A.card - k)$-subsets of $A$ that are not disjoint from any member of $\mathcal{E}$ is at most $\binom{A.card - 1}{A.card - k - 1}$.
      have h_erdos_ko_rado : (Finset.filter (fun S => S ⊆ A ∧ S.card = A.card - k ∧ ∃ E ∈ Finset.image (fun B => A \ B) (Finset.filter (fun B => k ≤ B.card ∧ B ⊂ A) F), E ⊆ S) (Finset.powersetCard (A.card - k) A)).card ≤ Nat.choose (A.card - 1) ((A.card - k) - 1) := by
        convert super_sets_bound F hF A hA k hjk using 1;
        congr! 1;
        ext; simp [SuperSets];
        unfold DifferenceFamily; aesop;
      -- Each bad $k$-subset $D$ of $A$ corresponds to a unique $(A.card - k)$-subset $S$ of $A$ that is not disjoint from any member of $\mathcal{E}$.
      have h_bad_subset_to_S : Finset.filter (fun D => is_bad_subset F A D k) (Finset.powersetCard k A) ⊆ Finset.image (fun S => A \ S) (Finset.filter (fun S => S ⊆ A ∧ S.card = A.card - k ∧ ∃ E ∈ Finset.image (fun B => A \ B) (Finset.filter (fun B => k ≤ B.card ∧ B ⊂ A) F), E ⊆ S) (Finset.powersetCard (A.card - k) A)) := by
        intro D hD; simp_all +decide [ Finset.subset_iff, is_bad_subset ] ;
        refine' ⟨ A \ D, _, _ ⟩ <;> simp_all +decide [ Finset.card_sdiff, Finset.subset_iff ];
        exact ⟨ by rw [ Finset.inter_eq_left.mpr hD.1.1, hD.1.2 ], by obtain ⟨ B, hB₁, hB₂, hB₃ ⟩ := hD.2.2.2; exact ⟨ B, ⟨ hB₁, by linarith [ Finset.card_le_card hB₂ ], hB₃ ⟩, by aesop ⟩ ⟩;
      refine le_trans ( Finset.card_le_card h_bad_subset_to_S ) <| Finset.card_image_le.trans ?_;
      by_cases h : A.card ≤ k <;> simp_all +decide
      · contrapose! h_bad_subset_to_S; simp_all +decide [ Finset.subset_iff ] ;
        rw [ Nat.choose_eq_zero_of_lt ] at h_bad_subset_to_S <;> norm_num at *;
        · grind;
        · omega;
      · refine le_trans h_erdos_ko_rado ?_;
        rw [ Nat.choose_symm_of_eq_add ] ; omega

/-
At most one set is starred per permutation.
-/
lemma starred_unique {n : ℕ} (F : Finset (Finset (Fin n))) (p : Equiv.Perm (Fin n)) (k : ℕ) :
    (F.filter (λ A => IsStarred F p A k)).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_;
      unfold IsStarred;
      grind

/-
The prefix set for $j$ is contained in the prefix set for $k$ if $j \le k$.
-/
lemma prefix_set_mono {n : ℕ} (p : Equiv.Perm (Fin n)) (j k : ℕ) (h : j ≤ k) :
    prefix_set p j ⊆ prefix_set p k := by
      unfold prefix_set;
      grind

/-
The size of the prefix set $S_j$ is $j$.
-/
lemma prefix_set_card {n : ℕ} (p : Equiv.Perm (Fin n)) (j : ℕ) (hj : j ≤ n) :
    (prefix_set p j).card = j := by
      -- Since `p` is a permutation, the set `{x | p x < j}` has exactly `j` elements.
      have h_card : (Finset.filter (fun x => p x < j) Finset.univ).card = j := by
        rw [ Finset.card_eq_of_bijective ];
        use fun i hi => p.symm ⟨ i, by linarith ⟩;
        · exact fun x hx => ⟨ p x, Finset.mem_filter.mp hx |>.2, p.symm_apply_apply x ⟩;
        · aesop;
        · aesop;
      unfold prefix_set; aesop;

/-
If $S_k$ is not bad, then $A$ is starred.
-/
lemma not_bad_implies_starred {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) (hA : A ∈ F)
    (k : ℕ) (hjk : A.card ≤ 2 * k) (hAk : k ≤ A.card)
    (p : Equiv.Perm (Fin n))
    (h_prefix : prefix_set p A.card = A)
    (h_not_bad : ¬ is_bad_subset F A (prefix_set p k) k) :
    IsStarred F p A k := by
      refine' ⟨ hA, A.card, hAk, hjk, h_prefix, _ ⟩;
      intros t ht1 ht2 ht3
      have hB : prefix_set p t ⊆ A := by
        exact h_prefix ▸ prefix_set_mono p _ _ ht2.le |> Finset.Subset.trans <| by aesop;
      have hB_card : prefix_set p t ≠ A := by
        have hB_card : (prefix_set p t).card < A.card := by
          rw [ prefix_set_card ] <;> linarith [ show t ≤ n from le_trans ht2.le ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ];
        grind
      have hB_k : k ≤ (prefix_set p t).card := by
        rw [ prefix_set_card ] <;> try linarith;
        exact le_trans ( Nat.le_of_lt ht2 ) ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )
      have hB_bad : is_bad_subset F A (prefix_set p k) k := by
        refine' ⟨ _, _, _ ⟩;
        · exact Finset.Subset.trans ( prefix_set_mono p _ _ ht1 ) hB;
        · convert prefix_set_card p k _ ; linarith [ show k ≤ n from le_trans hAk ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ;
        · refine' ⟨ _, ht3, _, _ ⟩ <;> simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
          · exact fun x hx => Finset.mem_map.mpr <| by obtain ⟨ y, hy, rfl ⟩ := Finset.mem_map.mp hx; exact ⟨ y, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by linarith [ Finset.mem_filter.mp hy ] ⟩, rfl ⟩ ;
          · exact Finset.exists_of_ssubset ( lt_of_le_of_ne hB hB_card ) |> Exists.imp fun x hx => by aesop;
      contradiction

/-
The set of permutations of $[n]$ whose prefix of length $j$ is the set $A$.
-/
def permutations_with_prefix {n : ℕ} (A : Finset (Fin n)) (j : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (λ p => prefix_set p j = A)

/-
The number of embeddings from $\{0, \dots, j-1\}$ to $[n]$ whose image is $A$ is $j!$.
-/
noncomputable def embeddings_with_range {n : ℕ} (A : Finset (Fin n)) (j : ℕ) : Finset (Fin j ↪ Fin n) :=
  Finset.univ.filter (λ f => Finset.univ.map f = A)

lemma embeddings_with_range_card {n : ℕ} (A : Finset (Fin n)) (j : ℕ) (hA : A.card = j) :
    (embeddings_with_range A j).card = j.factorial := by
      unfold embeddings_with_range;
      rw [ show ( { f : Fin j ↪ Fin n | Finset.map f ( Finset.univ ) = A } : Finset _ ) = Finset.image ( fun e : Fin j ↪ A => ⟨ fun i => e i |>.1, fun i j h => by simpa using e.injective <| Subtype.ext h ⟩ ) ( Finset.univ : Finset ( Fin j ↪ A ) ) from ?_, Finset.card_image_of_injective ];
      · simp +decide [ Finset.card_univ ];
        rw [ hA, Nat.descFactorial_self ];
      · intro e₁ e₂ h; ext i; replace h := congr_arg ( fun f => f.toFun i ) h; aesop;
      · ext aesop;
        simp +zetaDelta at *;
        constructor <;> intro h;
        · use ⟨ fun i => ⟨ aesop i, by replace h := Finset.ext_iff.mp h ( aesop i ) ; aesop ⟩, fun i j hij => aesop.injective <| by simpa using hij ⟩ ; aesop;
        · refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _ <;> aesop

/-
Combining two embeddings with disjoint ranges yields an injective function.
-/
def combine_embeddings {n j : ℕ} (hj : j ≤ n) (f : Fin j ↪ Fin n) (g : Fin (n - j) ↪ Fin n) : Fin n → Fin n :=
  λ x => Fin.addCases f g (Fin.cast (Nat.add_sub_of_le hj).symm x)

lemma combine_embeddings_injective {n j : ℕ} (hj : j ≤ n) (f : Fin j ↪ Fin n) (g : Fin (n - j) ↪ Fin n)
    (h_disjoint : Disjoint (Set.range f) (Set.range g)) :
    Function.Injective (combine_embeddings hj f g) := by
      intro x y hxy;
      unfold combine_embeddings at hxy;
      cases' x with x hx ; cases' y with y hy ; simp_all +decide [ Fin.addCases ];
      split_ifs at hxy <;> simp_all +decide [ Set.disjoint_left ];
      · exact False.elim <| h_disjoint _ _ hxy.symm;
      · omega

/-
Construct a permutation from two embeddings with disjoint ranges by combining them.
-/
noncomputable def combine_embeddings_perm {n j : ℕ} (hj : j ≤ n) (f : Fin j ↪ Fin n) (g : Fin (n - j) ↪ Fin n)
    (h_disjoint : Disjoint (Set.range f) (Set.range g)) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (combine_embeddings hj f g) (by
    have inj := combine_embeddings_injective hj f g h_disjoint
    exact Finite.injective_iff_bijective.mp inj)

/-
If f maps to A and g maps to the complement of A, their ranges are disjoint.
-/
lemma disjoint_ranges_of_embeddings {n : ℕ} (A : Finset (Fin n)) (j : ℕ)
    (f : Fin j ↪ Fin n) (g : Fin (n - j) ↪ Fin n)
    (hf : f ∈ embeddings_with_range A j)
    (hg : g ∈ embeddings_with_range (Finset.univ \ A) (n - j)) :
    Disjoint (Set.range f) (Set.range g) := by
      simp_all +decide [ embeddings_with_range ];
      simp_all +decide [ Finset.ext_iff, Set.disjoint_left ]

/-
The prefix set of the inverse of the combined permutation is the range of the first embedding.
-/
lemma prefix_set_symm_combine_embeddings {n j : ℕ} (hj : j ≤ n) (f : Fin j ↪ Fin n) (g : Fin (n - j) ↪ Fin n)
    (h_disjoint : Disjoint (Set.range f) (Set.range g)) :
    prefix_set (combine_embeddings_perm hj f g h_disjoint).symm j = Finset.univ.map f := by
      unfold prefix_set combine_embeddings_perm;
      -- To prove the equality of the two sets, we show each set is a subset of the other.
      apply Finset.ext
      intro x
      simp
      constructor;
      · intro hx;
        -- Since $x$ is in the range of $f$, there exists some $a \in \text{Fin } j$ such that $f(a) = x$.
        obtain ⟨a, ha⟩ : ∃ a : Fin j, f a = x := by
          have h_exists : ∃ y : Fin n, combine_embeddings hj f g y = x := by
            exact ⟨ _, Equiv.apply_symm_apply ( Equiv.ofBijective ( combine_embeddings hj f g ) ⟨ combine_embeddings_injective hj f g h_disjoint, Finite.injective_iff_surjective.mp ( combine_embeddings_injective hj f g h_disjoint ) ⟩ ) x ⟩
          obtain ⟨ y, rfl ⟩ := h_exists;
          unfold combine_embeddings at hx ⊢;
          unfold Fin.addCases at * ; aesop;
        use a;
      · rintro ⟨ a, rfl ⟩;
        have h_inv : Equiv.symm (Equiv.ofBijective (combine_embeddings hj f g) (by
        exact Finite.injective_iff_bijective.mp ( combine_embeddings_injective hj f g h_disjoint ))) (f a) = Fin.cast (by
        rw [ Nat.add_sub_of_le hj ]) (Fin.castAdd (n - j) a) := by
          exact Equiv.symm_apply_eq _ |>.2 <| by simp +decide [ combine_embeddings ] ;
        generalize_proofs at *;
        aesop

/-
The number of embeddings from {0, ..., j-1} to {0, ..., n-1} with image A is j!.
-/
lemma card_embeddings_with_range {n : ℕ} (A : Finset (Fin n)) (j : ℕ) (hA : A.card = j) :
    (embeddings_with_range A j).card = j.factorial := by
      convert embeddings_with_range_card A j hA using 1

/-
Map a permutation with prefix A to a pair of embeddings.
-/
def perm_to_embeddings_fwd {n : ℕ} (A : Finset (Fin n)) (j : ℕ) (hj : j ≤ n) (p : permutations_with_prefix A j) :
    embeddings_with_range A j × embeddings_with_range (Finset.univ \ A) (n - j) :=
  let h : j + (n - j) = n := Nat.add_sub_of_le hj
  let q := p.1.symm
  let iso := Fin.castOrderIso h
  let f : Fin j ↪ Fin n := (Fin.castAddOrderEmb (n - j)).toEmbedding.trans (iso.toEmbedding.trans q.toEmbedding)
  let g : Fin (n - j) ↪ Fin n := (Fin.natAddOrderEmb j).toEmbedding.trans (iso.toEmbedding.trans q.toEmbedding)
  have hf : Finset.univ.map f = A := by
    -- Since $p$ is in the permutations_with_prefix $A$ $j$, the prefix set of $p$ is $A$.
    have h_prefix : prefix_set p.val j = A := by
      exact Finset.mem_filter.mp p.2 |>.2;
    convert h_prefix using 1;
    refine' Finset.ext fun x => _;
    simp +zetaDelta at *;
    unfold prefix_set; simp +decide [ Finset.mem_filter ] ;
    constructor <;> intro h;
    · aesop;
    · use ⟨ p.val x, h ⟩;
      simp +decide [ Fin.cast, Fin.castAdd ]
  have hg : Finset.univ.map g = Finset.univ \ A := by
    have hg_card : (Finset.univ.map g).card = (Finset.univ \ A).card := by
      simp +decide [ Finset.card_sdiff, * ];
      rw [ ← hf, Finset.card_map ] ; aesop;
    refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) ( by aesop );
    simp +zetaDelta at *;
    obtain ⟨ a, rfl ⟩ := hx; intro H; replace hf := Finset.ext_iff.mp hf ( Equiv.symm p ( Fin.cast h ( Fin.natAdd j a ) ) ) ; simp_all +decide [ Finset.mem_map, Finset.mem_univ ] ;
    obtain ⟨ b, hb ⟩ := hf; replace hb := congr_arg Fin.val hb; simp_all +decide
    linarith [ Fin.is_lt b, Fin.is_lt a ]
  (⟨f, by simp [embeddings_with_range, hf]⟩, ⟨g, by simp [embeddings_with_range, hg]⟩)

/-
Map a pair of embeddings to a permutation with prefix A.
-/
noncomputable def perm_to_embeddings_inv {n : ℕ} (A : Finset (Fin n)) (j : ℕ) (hj : j ≤ n)
    (pair : embeddings_with_range A j × embeddings_with_range (Finset.univ \ A) (n - j)) :
    permutations_with_prefix A j :=
  let f := pair.1.val
  let g := pair.2.val
  let h_disjoint : Disjoint (Set.range f) (Set.range g) := disjoint_ranges_of_embeddings A j f g pair.1.property pair.2.property
  let q := combine_embeddings_perm hj f g h_disjoint
  let p := q.symm
  ⟨p, by
    -- prefix_set p j = p^{-1}({0..j-1}) = q({0..j-1})
    -- q({0..j-1}) is the image of {0..j-1} under combine_embeddings hj f g
    -- which is exactly range f
    -- range f is A
    -- By definition of $p$, we know that $p$ is the inverse of $q$, so $p$ maps the first $j$ elements to $A$.
    have hp_prefix : prefix_set (q.symm) j = A := by
      convert prefix_set_symm_combine_embeddings hj f g h_disjoint using 1;
      exact Eq.symm ( Finset.mem_filter.mp pair.1.property |>.2 );
    exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hp_prefix ⟩⟩

/-
The set of permutations with prefix A is equivalent to the product of embeddings with range A and embeddings with range A^c.
-/
noncomputable def permutations_equiv_embeddings {n : ℕ} (A : Finset (Fin n)) (j : ℕ) (hj : j ≤ n) (hA : A.card = j) :
    permutations_with_prefix A j ≃ embeddings_with_range A j × embeddings_with_range (Finset.univ \ A) (n - j) :=
  Equiv.mk (perm_to_embeddings_fwd A j hj) (perm_to_embeddings_inv A j hj) (by
  intro p;
  unfold perm_to_embeddings_fwd perm_to_embeddings_inv;
  unfold combine_embeddings_perm;
  convert Subtype.ext ?_;
  convert Equiv.symm_symm _;
  ext x; simp +decide [ combine_embeddings ] ;
  cases' lt_or_ge x.val j with hx hx <;> simp +decide [ hx, Fin.addCases ];
  split_ifs <;> simp_all +decide [ Fin.cast ]) (by
  intro p;
  unfold perm_to_embeddings_fwd perm_to_embeddings_inv;
  simp +decide [ combine_embeddings_perm ];
  unfold combine_embeddings; aesop;)

/-
The number of permutations with prefix A is j! * (n-j)!.
-/
lemma card_permutations_with_prefix {n : ℕ} (A : Finset (Fin n)) (j : ℕ) (hj : j ≤ n) (hA : A.card = j) :
    (permutations_with_prefix A j).card = j.factorial * (n - j).factorial := by
      convert Fintype.card_prod ( embeddings_with_range A j ) ( embeddings_with_range ( Finset.univ \ A ) ( n - j ) ) using 1;
      · convert Fintype.card_congr ( permutations_equiv_embeddings A j hj hA ) using 1;
        rw [ Fintype.card_coe ];
      · rw [ Fintype.card_coe, Fintype.card_coe, card_embeddings_with_range, card_embeddings_with_range ];
        · simp +decide [ Finset.card_sdiff, * ];
        · exact hA

/-
Definitions for embeddings with subrange condition.
-/
def canonical_prefix_fin (j k : ℕ) : Finset (Fin j) := Finset.univ.filter (λ x => x < k)

noncomputable def embeddings_with_range_and_subrange {n : ℕ} (A : Finset (Fin n)) (D : Finset (Fin n)) (j k : ℕ) : Finset (Fin j ↪ Fin n) :=
  (embeddings_with_range A j).filter (λ f => Finset.map f (canonical_prefix_fin j k) = D)

/-
Map an embedding with subrange condition to a pair of embeddings.
-/
def embeddings_split_fwd {n : ℕ} (A : Finset (Fin n)) (D : Finset (Fin n)) (j k : ℕ)
    (hk : k ≤ j) (hDA : D ⊆ A)
    (f : embeddings_with_range_and_subrange A D j k) :
    embeddings_with_range D k × embeddings_with_range (A \ D) (j - k) :=
  let f' := f.1
  let g1 : Fin k ↪ Fin n := (Fin.castLEEmb hk).trans f'
  let h : k + (j - k) = j := Nat.add_sub_of_le hk
  let iso := Fin.castOrderIso h
  let g2 : Fin (j - k) ↪ Fin n := (Fin.natAddOrderEmb k).toEmbedding.trans (iso.toEmbedding.trans f')
  have hg1 : Finset.map g1 Finset.univ = D := by
    -- g1 is f restricted to {0..k-1}.
    -- The condition in embeddings_with_range_and_subrange says f({0..k-1}) = D.
    have h_cond : Finset.map f' (canonical_prefix_fin j k) = D := (Finset.mem_filter.mp f.2).2
    -- canonical_prefix_fin j k is exactly the image of Fin.castLEEmb hk.
    convert h_cond using 1;
    ext; simp [g1, canonical_prefix_fin];
    constructor <;> rintro ⟨ a, ha ⟩;
    · grind;
    · exact ⟨ ⟨ a, ha.1 ⟩, by simpa [ Fin.castLE ] using ha.2 ⟩
  have hg2 : Finset.map g2 Finset.univ = A \ D := by
    -- g2 is f restricted to {k..j-1}.
    -- range f is A.
    -- f({0..k-1}) is D.
    -- So f({k..j-1}) is A \ D.
    have h_disjoint : Disjoint (Finset.map g1 Finset.univ) (Finset.map g2 Finset.univ) := by
      simp +decide [ Finset.disjoint_left ];
      intro a x; intro H; have := f'.injective H; simp_all +decide [ Fin.ext_iff ] ;
      grind;
    have h_union : Finset.map g1 Finset.univ ∪ Finset.map g2 Finset.univ = A := by
      have h_union : Finset.map g1 Finset.univ ∪ Finset.map g2 Finset.univ = Finset.map f' Finset.univ := by
        ext x; simp [g1, g2];
        constructor <;> intro h;
        · aesop;
        · obtain ⟨ a, rfl ⟩ := h;
          by_cases ha : a.val < k;
          · exact Or.inl ⟨ ⟨ a, ha ⟩, rfl ⟩;
          · refine Or.inr ⟨ ⟨ a - k, by
              exact tsub_lt_tsub_iff_right ( le_of_not_gt ha ) |>.2 a.2 ⟩, ?_ ⟩
            generalize_proofs at *;
            congr;
            exact Fin.ext ( by simp +decide [ Nat.add_sub_of_le ( show k ≤ ( a : ℕ ) from le_of_not_gt ha ) ] );
      convert h_union using 1;
      exact Eq.symm ( Finset.mem_filter.mp ( Finset.mem_filter.mp f.2 |>.1 ) |>.2 );
    rw [ ← h_union, ← hg1, Finset.union_sdiff_cancel_left h_disjoint ]
  (⟨g1, by simp [embeddings_with_range, hg1]⟩, ⟨g2, by simp [embeddings_with_range, hg2]⟩)

/-
Combining two embeddings with disjoint ranges yields an injective function.
-/
def combine_embeddings_general {β : Type*} {k l : ℕ} (f1 : Fin k ↪ β) (f2 : Fin l ↪ β) : Fin (k + l) → β :=
  Fin.addCases f1 f2

lemma combine_embeddings_general_injective {β : Type*} [DecidableEq β] {k l : ℕ}
    (f1 : Fin k ↪ β) (f2 : Fin l ↪ β)
    (h_disjoint : Disjoint (Set.range f1) (Set.range f2)) :
    Function.Injective (combine_embeddings_general f1 f2) := by
      intro x y hxy;
      unfold combine_embeddings_general at hxy;
      cases x using Fin.addCases <;> cases y using Fin.addCases <;> simp_all +decide [ Fin.addCases ];
      · exact False.elim ( h_disjoint.le_bot ⟨ ⟨ _, hxy ⟩, ⟨ _, rfl ⟩ ⟩ );
      · exact False.elim ( h_disjoint.le_bot ⟨ ⟨ _, hxy.symm ⟩, ⟨ _, rfl ⟩ ⟩ )

/-
Map a pair of embeddings to an embedding with subrange condition.
-/
def embeddings_split_inv {n : ℕ} (A : Finset (Fin n)) (D : Finset (Fin n)) (j k : ℕ)
    (hk : k ≤ j) (hDA : D ⊆ A)
    (pair : embeddings_with_range D k × embeddings_with_range (A \ D) (j - k)) :
    embeddings_with_range_and_subrange A D j k :=
  let f1 := pair.1.val
  let f2 := pair.2.val
  let h_add : k + (j - k) = j := Nat.add_sub_of_le hk
  let f_fun : Fin j → Fin n := (combine_embeddings_general f1 f2) ∘ (Fin.cast h_add.symm)
  have h_inj : Function.Injective f_fun := by
    have h_disjoint : Disjoint (Set.range f1) (Set.range f2) := by
      have h_disjoint : Finset.univ.map f1 = D ∧ Finset.univ.map f2 = A \ D := by
        exact ⟨ Finset.mem_filter.mp pair.1.2 |>.2, Finset.mem_filter.mp pair.2.2 |>.2 ⟩;
      simp_all +decide [ Finset.ext_iff, Set.disjoint_left ];
    exact Function.Injective.comp ( combine_embeddings_general_injective f1 f2 h_disjoint ) ( Fin.cast_injective _ )
  let f : Fin j ↪ Fin n := ⟨f_fun, h_inj⟩
  have h_range : Finset.map f Finset.univ = A := by
    have h_range : Finset.map f1 Finset.univ = D ∧ Finset.map f2 Finset.univ = (A \ D) := by
      exact ⟨ Finset.mem_filter.mp pair.1.2 |>.2, Finset.mem_filter.mp pair.2.2 |>.2 ⟩;
    -- Since these two maps are disjoint and their union is A, we can conclude that the range of f is A.
    have h_union : Finset.map f1 Finset.univ ∪ Finset.map f2 Finset.univ = A := by
      grind;
    convert h_union using 1;
    ext x; simp [f, f_fun, combine_embeddings_general];
    simp +decide [ Fin.addCases, Fin.cast ];
    constructor;
    · rintro ⟨ a, ha ⟩ ; split_ifs at ha <;> [ exact Or.inl ⟨ _, ha ⟩ ; exact Or.inr ⟨ _, ha ⟩ ];
    · rintro ( ⟨ a, rfl ⟩ | ⟨ a, rfl ⟩ );
      · exact ⟨ ⟨ a, by linarith [ Fin.is_lt a ] ⟩, by aesop ⟩;
      · use ⟨ k + a, by linarith [ Fin.is_lt a, Nat.sub_add_cancel hk ] ⟩ ; aesop
  have h_subrange : Finset.map f (canonical_prefix_fin j k) = D := by
    -- The image of the canonical prefix under f is the image of f1, which is D.
    have h_image : Finset.map f (canonical_prefix_fin j k) = Finset.map f1 Finset.univ := by
      ext x; simp [f, f_fun, combine_embeddings_general];
      constructor <;> intro h;
      · obtain ⟨ a, ha, rfl ⟩ := h;
        use ⟨ a.val, by
          exact Finset.mem_filter.mp ha |>.2 ⟩
        generalize_proofs at *;
        simp +decide [ Fin.addCases, Fin.cast ];
        exact fun h => False.elim <| h.not_gt ‹_›;
      · obtain ⟨ a, rfl ⟩ := h; use Fin.castLEEmb hk a; simp +decide [ Fin.addCases ] ;
        exact ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by simp +decide [ Fin.castLE ] ⟩, by simp +decide [ Fin.ext_iff ] ⟩;
    convert h_image using 1;
    exact Eq.symm ( Finset.mem_filter.mp pair.1.2 |>.2 )
  ⟨f, by simp [embeddings_with_range_and_subrange, embeddings_with_range, h_range, h_subrange]⟩

/-
The set of embeddings with subrange condition is equivalent to the product of two sets of embeddings.
-/
def embeddings_equiv_split {n : ℕ} (A : Finset (Fin n)) (D : Finset (Fin n)) (j k : ℕ)
    (hk : k ≤ j) (hDA : D ⊆ A) :
    embeddings_with_range_and_subrange A D j k ≃
    embeddings_with_range D k × embeddings_with_range (A \ D) (j - k) :=
  Equiv.mk (embeddings_split_fwd A D j k hk hDA) (embeddings_split_inv A D j k hk hDA) (by
  intro f
  simp [embeddings_split_inv, embeddings_split_fwd];
  ext x;
  by_cases hx : x.val < k <;> simp_all +decide [ Fin.castLEEmb ];
  · simp +decide [ combine_embeddings_general ];
    simp +decide [ Fin.addCases, hx ];
    congr!;
  · simp +decide [ combine_embeddings_general ];
    simp +decide [ Fin.addCases, Fin.castLE, Fin.natAdd, hx ]) (by
  intro x; exact (by
  simp +decide [ embeddings_split_inv, embeddings_split_fwd ];
  congr;
  · ext i; simp [combine_embeddings_general];
    simp +decide [ Fin.addCases, Fin.castLE ];
  · ext; simp +decide [ Fin.natAdd, combine_embeddings_general ] ;
    simp +decide [ Fin.addCases ]))

/-
The number of embeddings with subrange condition is k! * (j-k)!.
-/
lemma card_embeddings_with_range_and_subrange {n : ℕ} (A : Finset (Fin n)) (D : Finset (Fin n))
    (j k : ℕ) (hk : k ≤ j) (hA : A.card = j) (hD : D.card = k) (hDA : D ⊆ A) :
    (embeddings_with_range_and_subrange A D j k).card = k.factorial * (j - k).factorial := by
      convert Fintype.card_congr ( embeddings_equiv_split A D j k hk hDA ) using 1;
      · rw [ Fintype.card_coe ];
      · rw [ Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, card_embeddings_with_range, card_embeddings_with_range ];
        · grind;
        · exact hD

/-
Definition of permutations with prefix and subprefix.
-/
def permutations_with_prefix_and_subprefix {n : ℕ} (A : Finset (Fin n)) (D : Finset (Fin n)) (j k : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  (permutations_with_prefix A j).filter (λ p => prefix_set p k = D)

/-
The set of permutations with prefix A and subprefix D is equivalent to the product of embeddings with subrange condition and embeddings with range A^c.
-/
noncomputable def permutations_equiv_embeddings_subprefix {n : ℕ} (A : Finset (Fin n)) (D : Finset (Fin n)) (j k : ℕ)
    (hj : j ≤ n) (hk : k ≤ j) (hA : A.card = j) :
    { p // p ∈ permutations_with_prefix_and_subprefix A D j k } ≃
    { f // f ∈ embeddings_with_range_and_subrange A D j k } × { g // g ∈ embeddings_with_range (Finset.univ \ A) (n - j) } :=
  let base_equiv := permutations_equiv_embeddings A j hj hA
  let P (p : { x // x ∈ permutations_with_prefix A j }) : Prop := prefix_set p.1 k = D
  let Q (pair : { x // x ∈ embeddings_with_range A j } × { x // x ∈ embeddings_with_range (Finset.univ \ A) (n - j) }) : Prop :=
    Finset.map pair.1.1 (canonical_prefix_fin j k) = D
  have h_iff : ∀ p, P p ↔ Q (base_equiv p) := by
    intro p
    simp [P, Q, base_equiv];
    have h_equiv : ∀ p : { x // x ∈ permutations_with_prefix A j }, prefix_set p.val k = Finset.map (↑((permutations_equiv_embeddings A j hj hA) p).1) (canonical_prefix_fin j k) := by
      intro p
      simp [prefix_set, permutations_equiv_embeddings];
      ext x; simp [perm_to_embeddings_fwd];
      constructor <;> intro hx;
      · use ⟨p.val x, by
          exact lt_of_lt_of_le hx hk⟩
        generalize_proofs at *;
        simp +zetaDelta at *;
        exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hx ⟩;
      · obtain ⟨ a, ha, rfl ⟩ := hx; simp +decide [ Fin.castAdd, Fin.castLE ] ;
        exact Finset.mem_filter.mp ha |>.2;
    rw [ h_equiv p ]
  let subtype_equiv := Equiv.subtypeEquiv base_equiv h_iff
  let split_equiv : { pair : { x // x ∈ embeddings_with_range A j } × { x // x ∈ embeddings_with_range (Finset.univ \ A) (n - j) } // Q pair } ≃
                    { f : { x // x ∈ embeddings_with_range A j } // Finset.map f.1 (canonical_prefix_fin j k) = D } × { x // x ∈ embeddings_with_range (Finset.univ \ A) (n - j) } :=
    Equiv.mk
      (λ ⟨⟨f, g⟩, h⟩ => (⟨f, h⟩, g))
      (λ ⟨f, g⟩ => ⟨(f.1, g), f.2⟩)
      (by intro ⟨⟨f, g⟩, h⟩; simp)
      (by intro ⟨f, g⟩; simp)
  let refine_equiv : { f : { x // x ∈ embeddings_with_range A j } // Finset.map f.1 (canonical_prefix_fin j k) = D } ≃
                     { f // f ∈ embeddings_with_range_and_subrange A D j k } :=
    Equiv.mk
      (λ ⟨⟨f, hf⟩, h⟩ => ⟨f, by
        rw [embeddings_with_range_and_subrange, Finset.mem_filter]
        exact ⟨hf, h⟩⟩)
      (λ ⟨f, hf⟩ => ⟨⟨f, (Finset.mem_filter.mp hf).1⟩, (Finset.mem_filter.mp hf).2⟩)
      (by intro ⟨⟨f, hf⟩, h⟩; simp)
      (by intro ⟨f, hf⟩; simp)
  let final_equiv := Equiv.trans split_equiv (Equiv.prodCongr refine_equiv (Equiv.refl _))
  let domain_equiv : { p // p ∈ permutations_with_prefix_and_subprefix A D j k } ≃ { p : { x // x ∈ permutations_with_prefix A j } // P p } :=
    Equiv.mk
      (λ ⟨p, hp⟩ => ⟨⟨p, (Finset.mem_filter.mp hp).1⟩, (Finset.mem_filter.mp hp).2⟩)
      (λ ⟨⟨p, hp1⟩, hp2⟩ => ⟨p, Finset.mem_filter.mpr ⟨hp1, hp2⟩⟩)
      (by intro ⟨p, hp⟩; simp)
      (by intro ⟨⟨p, hp1⟩, hp2⟩; simp)
  domain_equiv.trans (subtype_equiv.trans final_equiv)

/-
The number of permutations with prefix A and subprefix D is k! * (j-k)! * (n-j)!.
-/
lemma card_permutations_with_prefix_and_subprefix {n : ℕ} (A : Finset (Fin n)) (D : Finset (Fin n))
    (j k : ℕ) (hj : j ≤ n) (hk : k ≤ j) (hA : A.card = j) (hD : D.card = k) (hDA : D ⊆ A) :
    (permutations_with_prefix_and_subprefix A D j k).card = k.factorial * (j - k).factorial * (n - j).factorial := by
      have h_card : (permutations_with_prefix_and_subprefix A D j k).card = (embeddings_with_range_and_subrange A D j k).card * (embeddings_with_range (Finset.univ \ A) (n - j)).card := by
        convert Fintype.card_prod _ _ using 1;
        convert Fintype.card_congr ( permutations_equiv_embeddings_subprefix A D j k hj hk hA ) using 1;
        · rw [ Fintype.card_coe ];
        · rw [ Fintype.card_coe, Fintype.card_coe ];
      rw [ h_card, card_embeddings_with_range_and_subrange A D j k hk hA hD hDA, card_embeddings_with_range ];
      simp +decide [ Finset.card_sdiff, * ]

/-
Definitions for bad subsets and permutations.
-/
noncomputable def bad_k_subsets {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) (k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.powersetCard k A).filter (λ D => is_bad_subset F A D k)

noncomputable def permutations_where_Sk_is_bad {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) (j k : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  (permutations_with_prefix A j).filter (λ p => prefix_set p k ∈ bad_k_subsets F A k)

/-
The number of permutations where the k-prefix is bad is the number of bad k-subsets times the number of permutations with a fixed k-prefix.
-/
lemma card_permutations_where_Sk_is_bad {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) (j k : ℕ)
    (hj : j ≤ n) (hk : k ≤ j) (hA : A.card = j) :
    (permutations_where_Sk_is_bad F A j k).card =
    (bad_k_subsets F A k).card * k.factorial * (j - k).factorial * (n - j).factorial := by
      have h_card : ∀ D ∈ bad_k_subsets F A k, (permutations_with_prefix_and_subprefix A D j k).card = k.factorial * (j - k).factorial * (n - j).factorial := by
        intro D hD
        apply card_permutations_with_prefix_and_subprefix A D j k hj hk hA (by
        unfold bad_k_subsets at hD; aesop;) (by
        exact Finset.mem_powersetCard.mp ( Finset.mem_filter.mp hD |>.1 ) |>.1);
      have h_card : (permutations_where_Sk_is_bad F A j k).card = Finset.sum (bad_k_subsets F A k) (fun D => (permutations_with_prefix_and_subprefix A D j k).card) := by
        rw [ show permutations_where_Sk_is_bad F A j k = Finset.biUnion ( bad_k_subsets F A k ) ( fun D => permutations_with_prefix_and_subprefix A D j k ) from ?_, Finset.card_biUnion ];
        · intros D hD E hE hDE; simp_all +decide [ Finset.disjoint_left ] ;
          intro p hp hp'; simp_all +decide [ permutations_with_prefix_and_subprefix ] ;
        · unfold permutations_where_Sk_is_bad permutations_with_prefix_and_subprefix; aesop;
      rw [ h_card, Finset.sum_congr rfl ‹_›, Finset.sum_const, Finset.card_eq_sum_ones, smul_eq_mul, mul_assoc, mul_assoc ];
      ring

/-
The number of permutations where A is starred is at least k/j * (n! / binom(n,j)).
-/
noncomputable def permutations_starred {n : ℕ} (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) (k : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (λ p => IsStarred F p A k)

lemma card_starred_ge {n : ℕ} (F : Finset (Finset (Fin n))) (hF : UnionFree F)
    (A : Finset (Fin n)) (hA : A ∈ F) (k : ℕ) (hk : 1 ≤ k) (hjk : A.card ≤ 2 * k) (hAk : k ≤ A.card) :
    (permutations_starred F A k).card * A.card * (n.choose A.card) ≥ k * n.factorial := by
      -- The number of permutations where A is starred is at least $(j! (n-j)! - |bad| k! (j-k)! (n-j)!)$.
      have h_starred_count : (permutations_starred F A k).card ≥ (A.card.factorial * (n - A.card).factorial) - ((bad_k_subsets F A k).card * k.factorial * (A.card - k).factorial * (n - A.card).factorial) := by
        have h_starred_count : (permutations_starred F A k).card ≥ (permutations_with_prefix A A.card).card - ((permutations_where_Sk_is_bad F A A.card k).card) := by
          refine' Nat.sub_le_of_le_add _;
          have h_starred_count : (permutations_with_prefix A A.card) ⊆ (permutations_starred F A k) ∪ (permutations_where_Sk_is_bad F A A.card k) := by
            intro p hp;
            by_cases h : prefix_set p k ∈ bad_k_subsets F A k <;> simp_all +decide [ permutations_starred, permutations_where_Sk_is_bad ];
            apply not_bad_implies_starred F A hA k hjk hAk p (by
            exact Finset.mem_filter.mp hp |>.2) (by
            exact fun h' => h <| Finset.mem_filter.mpr ⟨ Finset.mem_powersetCard.mpr ⟨ by
              exact h'.1, by
              exact prefix_set_card p k ( by linarith [ show A.card ≤ n from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ] ) ⟩, h' ⟩);
          exact le_trans ( Finset.card_le_card h_starred_count ) ( Finset.card_union_le _ _ );
        convert h_starred_count using 2;
        · rw [ card_permutations_with_prefix ];
          · exact le_trans ( Finset.card_le_univ _ ) ( by norm_num );
          · rfl;
        · convert Eq.symm ( card_permutations_where_Sk_is_bad F A A.card k _ _ _ ) using 1 <;> norm_num [ Nat.factorial_ne_zero ];
          · exact le_trans ( Finset.card_le_univ _ ) ( by simp );
          · linarith;
      -- Using $|bad| \le \binom{j-1}{k}$, we get $\binom{j}{k} - |bad| \ge \binom{j-1}{k-1}$.
      have h_binom : (A.card.choose k) - (bad_k_subsets F A k).card ≥ (A.card - 1).choose (k - 1) := by
        have h_binom : (bad_k_subsets F A k).card ≤ (A.card - 1).choose k := by
          convert bad_subsets_count F hF A hA k hk hjk using 1;
        rcases k with ( _ | k ) <;> rcases A with ⟨ ⟨ _, _ ⟩ ⟩ <;> simp_all +decide [ Nat.choose ];
        exact le_tsub_of_add_le_left ( by linarith );
      -- So $|starred| \ge (n-j)! k! (j-k)! \binom{j-1}{k-1} = (n-j)! k (j-1)!$.
      have h_starred_final : (permutations_starred F A k).card ≥ (n - A.card).factorial * k * (A.card - 1).factorial := by
        have h_starred_final : (A.card.factorial * (n - A.card).factorial) - ((bad_k_subsets F A k).card * k.factorial * (A.card - k).factorial * (n - A.card).factorial) ≥ (n - A.card).factorial * k * (A.card - 1).factorial := by
          -- Using the binomial coefficient identity, we can rewrite the inequality.
          have h_binom_identity : (A.card.choose k) * (n - A.card).factorial * k.factorial * (A.card - k).factorial - ((bad_k_subsets F A k).card * k.factorial * (A.card - k).factorial * (n - A.card).factorial) ≥ (A.card - 1).choose (k - 1) * (n - A.card).factorial * k.factorial * (A.card - k).factorial := by
            refine' le_trans ( Nat.mul_le_mul_right _ ( Nat.mul_le_mul_right _ ( Nat.mul_le_mul_right _ h_binom ) ) ) _;
            simp +decide [ mul_assoc, mul_comm, mul_left_comm, tsub_mul ];
            rw [ Nat.mul_sub_left_distrib ] ; ring_nf ; norm_num;
          convert h_binom_identity using 1;
          · rw [ ← Nat.choose_mul_factorial_mul_factorial ( show k ≤ A.card from hAk ) ] ; ring_nf;
          · rcases k with ( _ | k ) <;> rcases A with ⟨ ⟨ _, _ ⟩ ⟩ <;> simp_all +decide [ Nat.factorial_succ, mul_assoc, mul_comm, mul_left_comm ];
            rw [ ← mul_assoc, ← mul_assoc, ← Nat.choose_mul_factorial_mul_factorial ( by linarith : k ≤ _ ) ] ; ring;
        exact h_starred_final.trans h_starred_count;
      -- Multiplying by $j \binom{n}{j} = j \frac{n!}{j!(n-j)!} = \frac{n!}{(j-1)!(n-j)!}$, we get $|starred| \cdot j \binom{n}{j} \ge (n-j)! k (j-1)! \frac{n!}{(j-1)!(n-j)!} = k n!$.
      have h_final : (n - A.card).factorial * k * (A.card - 1).factorial * A.card * (Nat.choose n A.card) ≥ k * Nat.factorial n := by
        rw [ ← Nat.choose_mul_factorial_mul_factorial ( show A.card ≤ n from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ];
        cases a : A.card <;> simp_all +decide [ Nat.factorial_succ, mul_assoc, mul_comm, mul_left_comm ];
      exact h_final.trans ( by gcongr )

/-
The sum of the number of starred sets over all permutations equals the sum of the number of permutations where a set is starred over all sets.
-/
noncomputable def starred_sets {n : ℕ} (F : Finset (Finset (Fin n))) (p : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Finset (Fin n)) :=
  F.filter (λ A => IsStarred F p A k)

lemma sum_starred_card_eq_sum_perm_starred_card {n : ℕ} (F : Finset (Finset (Fin n))) (k : ℕ) :
    ∑ p : Equiv.Perm (Fin n), (starred_sets F p k).card =
    ∑ A ∈ F, (permutations_starred F A k).card := by
      simp +decide only [starred_sets, Finset.card_filter, permutations_starred];
      exact Finset.sum_comm

/-
Kleitman's chain inequality: k * sum_{j=k}^{2k} x_j / (j * binom(n, j)) <= 1.
-/
theorem kleitman_inequality {n : ℕ} (F : Finset (Finset (Fin n))) (hF : UnionFree F) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * ∑ j ∈ Finset.Icc k (2 * k), (x_j F j : ℝ) / (j * n.choose j) ≤ 1 := by
      -- We sum the number of starred sets over all permutations.
      have h_sum_starred : ∑ p : Equiv.Perm (Fin n), (Finset.card (starred_sets F p k)) ≤ Nat.factorial n := by
        have h_starred_unique : ∀ p : Equiv.Perm (Fin n), (starred_sets F p k).card ≤ 1 := by
          intro p;
          convert starred_unique F p k;
        exact le_trans ( Finset.sum_le_sum fun _ _ => h_starred_unique _ ) ( by simp +decide [ Finset.card_univ, Fintype.card_perm ] );
      -- On the other hand, the sum equals $\sum_{A \in F} |\{p \mid A \text{ is starred in } p\}|$.
      have h_sum_starred_eq : ∑ p : Equiv.Perm (Fin n), (Finset.card (starred_sets F p k)) = ∑ A ∈ F, (Finset.card (permutations_starred F A k)) := by
        exact sum_starred_card_eq_sum_perm_starred_card F k;
      -- For a fixed $A$ with size $j \in [k, 2k]$, the number of permutations where $A$ is starred is at least $\frac{k \cdot n!}{j \binom{n}{j}}$.
      have h_starred_ge : ∀ A ∈ F, A.card ∈ Finset.Icc k (2 * k) → (Finset.card (permutations_starred F A k)) ≥ (k : ℝ) * (Nat.factorial n) / (A.card * (Nat.choose n A.card)) := by
        intros A hA hA_card
        have := card_starred_ge F hF A hA k hk (by
        linarith [ Finset.mem_Icc.mp hA_card ]) (by
        linarith [ Finset.mem_Icc.mp hA_card ])
        generalize_proofs at *;
        rw [ ge_iff_le, div_le_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.factorial_pos n, Nat.choose_pos ( show A.card ≤ n from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ;
      -- Summing this over all $A \in F$ with size $j$, we get $x_j \frac{k \cdot n!}{j \binom{n}{j}}$.
      have h_sum_starred_ge : ∑ A ∈ F, (Finset.card (permutations_starred F A k)) ≥ ∑ j ∈ Finset.Icc k (2 * k), (x_j F j : ℝ) * (k : ℝ) * (Nat.factorial n) / (j * (Nat.choose n j)) := by
        have h_sum_starred_ge : ∑ A ∈ F, (Finset.card (permutations_starred F A k)) ≥ ∑ j ∈ Finset.Icc k (2 * k), ∑ A ∈ F.filter (fun A => A.card = j), (k : ℝ) * (Nat.factorial n) / (j * (Nat.choose n j)) := by
          have h_sum_starred_ge : ∑ A ∈ F, (Finset.card (permutations_starred F A k)) ≥ ∑ A ∈ F.filter (fun A => A.card ∈ Finset.Icc k (2 * k)), (k : ℝ) * (Nat.factorial n) / (A.card * (Nat.choose n A.card)) := by
            push_cast [ Finset.sum_filter ];
            gcongr ; aesop;
          refine le_trans ?_ h_sum_starred_ge;
          simp +decide only [Finset.sum_filter];
          rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ];
        simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
        convert h_sum_starred_ge using 3 ; ring!;
      simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      norm_num [ ← mul_assoc, ← Finset.sum_mul _ _ _ ] at *;
      rw [ ← @Nat.cast_le ℝ ] at * ; push_cast at * ; nlinarith [ show 0 < ( n ! : ℝ ) by positivity ]

/-
Definition of the linear program for Kleitman's bound.
-/
def is_feasible_LP (n : ℕ) (x : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ j → j ≤ n → 0 ≤ x j ∧ x j ≤ n.choose j) ∧
  (∀ k, 1 ≤ k → k ≤ n / 2 → ∑ j ∈ Finset.Icc k (2 * k), x j / (j * n.choose j) ≤ 1 / k)

noncomputable def OPT (n : ℕ) : ℝ :=
  sSup { s | ∃ x, is_feasible_LP n x ∧ s = ∑ j ∈ Finset.range (n + 1), x j }

/-
If F is union-free, then |F| is at most the optimal value of the linear program.
-/
lemma LP_upper_bound {n : ℕ} (F : Finset (Finset (Fin n))) (hF : UnionFree F) : (F.card : ℝ) ≤ OPT n := by
  -- By definition of $x_j$, we know that $F.card = \sum_{j=0}^n x_j$.
  have h_sum : (F.card : ℝ) = ∑ j ∈ Finset.range (n + 1), (x_j F j : ℝ) := by
    rw_mod_cast [ show F = Finset.biUnion ( Finset.range ( n + 1 ) ) ( fun j => F.filter ( fun A => A.card = j ) ) from ?_, Finset.card_biUnion ];
    · refine' Finset.sum_congr rfl fun j hj => _;
      exact congr_arg Finset.card ( Finset.ext fun x => by aesop );
    · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
    · ext A; simp [Finset.mem_biUnion];
      exact fun hA => Nat.lt_succ_of_le ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) );
  refine' h_sum ▸ le_csSup _ _;
  · exact ⟨ ∑ j ∈ Finset.range ( n + 1 ), n.choose j, by rintro s ⟨ x, hx, rfl ⟩ ; exact Finset.sum_le_sum fun i hi => hx.1 i ( Nat.zero_le i ) ( Nat.le_of_lt_succ ( Finset.mem_range.mp hi ) ) |>.2 ⟩;
  · refine' ⟨ _, _, rfl ⟩;
    -- By definition of $x_j$, we know that $0 \leq x_j \leq \binom{n}{j}$ for all $j$.
    have h_bounds : ∀ j, 0 ≤ j → j ≤ n → 0 ≤ (x_j F j : ℝ) ∧ (x_j F j : ℝ) ≤ n.choose j := by
      intros j hj_nonneg hj_le_n
      simp [x_j];
      exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun A => Finset.card A = j ) F ⊆ Finset.powersetCard j ( Finset.univ : Finset ( Fin n ) ) from fun x hx => Finset.mem_powersetCard.mpr ⟨ Finset.subset_univ _, by aesop ⟩ ) ) ( by simp +decide [ Finset.card_univ ] );
    refine' ⟨ fun j hj₁ hj₂ => h_bounds j hj₁ hj₂, fun k hk₁ hk₂ => _ ⟩;
    have := kleitman_inequality F hF k hk₁;
    rwa [ le_div_iff₀' ( by positivity ) ]

/-
Definition of dual feasibility for the linear program.
-/
def is_dual_feasible (n : ℕ) (Y : ℕ → ℝ) (Z : ℕ → ℝ) : Prop :=
  (∀ k, Y k ≥ 0) ∧ (∀ j, Z j ≥ 0) ∧
  (∀ k, k = 0 ∨ k > n / 2 → Y k = 0) ∧
  (∀ j, j > n → Z j = 0) ∧
  (∀ j, 0 ≤ j → j ≤ n →
    (∑ k ∈ Finset.Icc ((j + 1) / 2) (min j (n / 2)), Y k / (j * n.choose j)) + Z j / n.choose j ≥ 1)

/-
The objective function of the dual linear program.
-/
noncomputable def dual_obj (n : ℕ) (Y : ℕ → ℝ) (Z : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range (n + 1), Z j) + (∑ k ∈ Finset.Icc 1 (n / 2), Y k / k)

/-
Restricted version of the sum exchange lemma where $j$ ranges from 1 to $n$.
-/
lemma sum_exchange_restricted (n : ℕ) (Y : ℕ → ℝ) (x : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 (n / 2), Y k * (∑ j ∈ Finset.Icc k (2 * k), x j / (j * n.choose j)) =
    ∑ j ∈ Finset.Icc 1 n, (x j / (j * n.choose j)) * (∑ k ∈ Finset.Icc ((j + 1) / 2) (min j (n / 2)), Y k) := by
      simp +decide only [mul_comm, Finset.mul_sum _ _ _];
      erw [ Finset.sum_sigma', Finset.sum_sigma' ];
      apply Finset.sum_bij (fun p hp => ⟨p.snd, p.fst⟩) _ _ _ _ <;> simp +contextual [ Finset.mem_sigma, Finset.mem_Icc ];
      · grind;
      · grind;
      · exact fun b hb₁ hb₂ hb₃ hb₄ hb₅ => ⟨ b.snd, b.fst, ⟨ ⟨ by omega, by omega ⟩, by omega, by omega ⟩, rfl ⟩

/-
Any primal feasible solution is bounded by the dual objective value.
-/
lemma weak_duality_lemma {n : ℕ} {x : ℕ → ℝ} {Y Z : ℕ → ℝ}
    (hx : is_feasible_LP n x) (h_dual : is_dual_feasible n Y Z) :
    ∑ j ∈ Finset.range (n + 1), x j ≤ dual_obj n Y Z := by
      have := h_dual.2.2.2.2;
      -- Apply the dual feasibility condition to each term in the sum.
      have h_dual_bound : ∀ j ∈ Finset.range (n + 1), x j ≤ x j * (∑ k ∈ Finset.Icc ((j + 1) / 2) (min j (n / 2)), Y k / (j * n.choose j)) + x j * (Z j / n.choose j) := by
        exact fun j hj => by nlinarith only [ this j ( Nat.zero_le j ) ( Finset.mem_range_succ_iff.mp hj ), hx.1 j ( Nat.zero_le j ) ( Finset.mem_range_succ_iff.mp hj ) ] ;
      -- Apply the dual feasibility condition to each term in the sum and rearrange.
      have h_sum_dual_bound : ∑ j ∈ Finset.range (n + 1), x j ≤ ∑ k ∈ Finset.Icc 1 (n / 2), Y k * (∑ j ∈ Finset.Icc k (2 * k), x j / (j * n.choose j)) + ∑ j ∈ Finset.range (n + 1), x j * (Z j / n.choose j) := by
        refine le_trans ( Finset.sum_le_sum h_dual_bound ) ?_;
        norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _ ];
        convert sum_exchange_restricted n Y x |> le_of_eq using 1;
        · convert sum_exchange_restricted n Y x |> Eq.symm using 1;
          erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        · convert sum_exchange_restricted n Y x using 1;
          exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum _ _ _ ] ;
      -- Apply the sum exchange lemma to rewrite the first term in the sum.
      have h_sum_exchange : ∑ k ∈ Finset.Icc 1 (n / 2), Y k * (∑ j ∈ Finset.Icc k (2 * k), x j / (j * n.choose j)) ≤ ∑ k ∈ Finset.Icc 1 (n / 2), Y k / k := by
        have h_sum_exchange : ∀ k ∈ Finset.Icc 1 (n / 2), Y k * (∑ j ∈ Finset.Icc k (2 * k), x j / (j * n.choose j)) ≤ Y k / k := by
          intros k hk
          have h_sum_bound : ∑ j ∈ Finset.Icc k (2 * k), x j / (j * n.choose j) ≤ 1 / k := by
            have := hx.2 k ( by linarith [ Finset.mem_Icc.mp hk ] ) ( by linarith [ Finset.mem_Icc.mp hk, Nat.div_mul_le_self n 2 ] ) ; aesop;
          simpa only [ mul_one_div ] using mul_le_mul_of_nonneg_left h_sum_bound ( h_dual.1 k |> le_trans ( by norm_num ) );
        exact Finset.sum_le_sum h_sum_exchange;
      -- Apply the dual feasibility condition to each term in the second sum.
      have h_sum_Z_bound : ∑ j ∈ Finset.range (n + 1), x j * (Z j / n.choose j) ≤ ∑ j ∈ Finset.range (n + 1), Z j := by
        refine Finset.sum_le_sum fun j hj => ?_;
        have := hx.1 j ( Nat.zero_le j ) ( Finset.mem_range_succ_iff.mp hj );
        rw [ mul_div, div_le_iff₀ ] <;> nlinarith [ show ( n.choose j : ℝ ) ≥ 1 by exact_mod_cast Nat.choose_pos ( Finset.mem_range_succ_iff.mp hj ), h_dual.2.1 j ];
      convert h_sum_dual_bound.trans ( add_le_add h_sum_exchange h_sum_Z_bound ) using 1;
      unfold dual_obj; ring;

/-
Weak duality: the optimal value of the primal is at most the value of the dual objective for any dual feasible solution.
-/
theorem weak_duality {n : ℕ} {Y Z : ℕ → ℝ} (h_dual : is_dual_feasible n Y Z) :
    OPT n ≤ dual_obj n Y Z := by
      apply csSup_le;
      · refine' ⟨ _, ⟨ fun _ => 0, _, rfl ⟩ ⟩ ; unfold is_feasible_LP ; aesop;
      · rintro _ ⟨ x, hx, rfl ⟩ ; exact weak_duality_lemma hx h_dual;

/-
Definitions of the dual variables $Y$ and $Z$ for the specific solution constructed in Lemma 4. $B_k$ is a helper term.
-/
noncomputable def B_term (n k : ℕ) : ℝ := (k : ℝ) * n.choose k - ((k - 1 : ℕ) : ℝ) * n.choose (k - 1)

noncomputable def Y_sol (n : ℕ) (k : ℕ) : ℝ :=
  if k = 0 then 0
  else if k > n / 2 then 0
  else
    if k % 2 == 0 then
      B_term n k
    else
      B_term n k + Y_sol n ((k - 1) / 2)
termination_by k
decreasing_by
  simp_wf
  omega

/-
The base term $B_k$ is non-negative for $k \le n/2$.
-/
lemma B_term_nonneg {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n / 2) : 0 ≤ B_term n k := by
  unfold B_term;
  rcases k with ( _ | k ) <;> norm_num at *;
  norm_cast;
  nlinarith [ Nat.div_mul_le_self n 2, Nat.succ_mul_choose_eq n k, Nat.choose_succ_succ n k ]

/-
The dual variables $Y_k$ are non-negative.
-/
lemma Y_sol_nonneg {n k : ℕ} : 0 ≤ Y_sol n k := by
  induction' k using Nat.strong_induction_on with k ih generalizing n;
  unfold Y_sol; split_ifs <;> norm_num;
  · exact B_term_nonneg ( Nat.pos_of_ne_zero ‹_› ) ( by linarith );
  · exact add_nonneg ( B_term_nonneg ( Nat.pos_of_ne_zero ‹_› ) ( by omega ) ) ( ih _ ( by omega ) )

/-
Identities for sums of $Y_k$ over blocks $[t, 2t]$ and $[t, 2t+1]$.
-/
lemma block_sum_identities {n t : ℕ} (ht : 1 ≤ t) (h2t : 2 * t ≤ n / 2) :
    (∑ k ∈ Finset.Icc t (2 * t), Y_sol n k = (2 * t : ℝ) * n.choose (2 * t)) ∧
    (2 * t + 1 ≤ n / 2 → ∑ k ∈ Finset.Icc t (2 * t + 1), Y_sol n k = ((2 * t + 1 : ℕ) : ℝ) * n.choose (2 * t + 1) + Y_sol n t) := by
      -- By definition of $Y_sol$, we know that $\sum_{k=t}^{2t} Y_k = 2t \binom{n}{2t}$.
      have h_sum_even : ∑ k ∈ Finset.Icc t (2 * t), Y_sol n k = 2 * t * (Nat.choose n (2 * t) : ℝ) := by
        induction' t with t ih generalizing n <;> simp_all +decide [ Nat.mul_succ ];
        by_cases ht : 1 ≤ t <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
        · have h_sum_even : ∑ k ∈ Finset.Icc t (2 * t + 1), Y_sol n k = (2 * t + 1) * (Nat.choose n (2 * t + 1) : ℝ) + Y_sol n t := by
            have h_sum_even : ∑ k ∈ Finset.Icc t (2 * t), Y_sol n k = 2 * t * (Nat.choose n (2 * t) : ℝ) := by
              exact ih ( by omega );
            have h_sum_even : Y_sol n (2 * t + 1) = (2 * t + 1) * (Nat.choose n (2 * t + 1) : ℝ) - 2 * t * (Nat.choose n (2 * t) : ℝ) + Y_sol n t := by
              rw [ Y_sol ] ; norm_num [ Nat.add_div ] ; ring_nf;
              rw [ if_neg ( by linarith ) ] ; unfold B_term ; ring_nf;
              norm_num ; ring;
            erw [ Finset.sum_Ico_succ_top ( by linarith ), ‹∑ k ∈ Finset.Icc t ( 2 * t ), Y_sol n k = _›, h_sum_even ] ; ring;
          have h_sum_even : ∑ k ∈ Finset.Icc (t + 1) (2 * t + 2), Y_sol n k = ∑ k ∈ Finset.Icc t (2 * t + 1), Y_sol n k - Y_sol n t + Y_sol n (2 * t + 2) := by
            erw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ ];
            · ring;
            · linarith;
            · linarith;
          have h_sum_even : Y_sol n (2 * t + 2) = (2 * t + 2) * (Nat.choose n (2 * t + 2) : ℝ) - (2 * t + 1) * (Nat.choose n (2 * t + 1) : ℝ) := by
            -- By definition of $Y_sol$, we know that $Y_sol n (2 * t + 2) = B_term n (2 * t + 2)$.
            have h_Y_sol_even : Y_sol n (2 * t + 2) = B_term n (2 * t + 2) := by
              rw [ Y_sol ] ; simp +decide
              exact fun h => False.elim <| h.not_ge h2t;
            exact h_Y_sol_even.trans ( by unfold B_term; norm_num );
          rw [ show ( Finset.Ioc t ( 2 * t + 2 ) : Finset ℕ ) = Finset.Icc ( t + 1 ) ( 2 * t + 2 ) by ext; aesop ] ; linarith!;
        · unfold Y_sol; norm_num; ring_nf;
          unfold B_term; split_ifs <;> norm_num [ Nat.choose_two_right ] ; ring_nf;
          · omega;
          · omega;
          · linarith;
          · unfold Y_sol; norm_num; ring;
      refine' ⟨ h_sum_even, fun h => _ ⟩;
      erw [ Finset.sum_Ico_succ_top ( by linarith ), h_sum_even ];
      rw [ Y_sol ]; ring_nf;
      norm_num [ Nat.add_mod, Nat.mul_mod, B_term ] ; ring_nf;
      rw [ if_neg ( by linarith ) ] ; ring

/-
The sum of $Y_k$ starting from $\lceil m/2 \rceil$ equals the bound.
-/
lemma sum_Y_mid {m : ℕ} (hm : m ≥ 1) :
    let n := 2 * m
    let t := (m + 1) / 2
    ∑ k ∈ Finset.Icc t m, Y_sol n k = (2 * t : ℝ) * n.choose (2 * t) := by
      rcases Nat.even_or_odd' m with ⟨ c, rfl | rfl ⟩ <;> simp +arith +decide [ *, Nat.add_div ];
      · convert block_sum_identities ( show 1 ≤ c by linarith ) ( show 2 * c ≤ ( 4 * c ) / 2 by omega ) |>.1 using 1;
      · have h_sum : ∑ x ∈ Finset.Icc (c + 1) (2 * c + 1), Y_sol (4 * c + 2) x = ∑ x ∈ Finset.Icc c (2 * c + 1), Y_sol (4 * c + 2) x - Y_sol (4 * c + 2) c := by
          rw [ eq_sub_iff_add_eq', ← Finset.sum_erase_add _ _ ( show c ∈ Finset.Icc c ( 2 * c + 1 ) from Finset.mem_Icc.mpr ⟨ le_rfl, by linarith ⟩ ), add_comm ];
          rcongr x ; aesop ;
        have h_sum : ∑ x ∈ Finset.Icc c (2 * c + 1), Y_sol (4 * c + 2) x = (2 * c + 1 : ℝ) * (4 * c + 2).choose (2 * c + 1) + Y_sol (4 * c + 2) c := by
          have h_sum : ∀ t, 1 ≤ t → 2 * t + 1 ≤ (4 * c + 2) / 2 → ∑ x ∈ Finset.Icc t (2 * t + 1), Y_sol (4 * c + 2) x = (2 * t + 1 : ℝ) * (4 * c + 2).choose (2 * t + 1) + Y_sol (4 * c + 2) t := by
            intros t ht ht'; have := block_sum_identities ( show 1 ≤ t from ht ) ( show 2 * t ≤ ( 4 * c + 2 ) / 2 from by omega ) ; aesop;
          rcases c with ( _ | c ) <;> simp_all +arith +decide
          · unfold Y_sol; norm_num [ Finset.Icc_eq_cons_Ioc ] ;
            unfold B_term Y_sol; norm_num;
          · exact_mod_cast h_sum ( c + 1 ) ( by linarith ) ( by omega );
        have h_binom : (2 * c + 1 : ℝ) * (4 * c + 2).choose (2 * c + 1) = (2 * c + 2 : ℝ) * (4 * c + 2).choose (2 * c + 2) := by
          norm_cast; nlinarith [ Nat.succ_mul_choose_eq ( 4 * c + 2 ) ( 2 * c + 1 ), Nat.choose_succ_succ ( 4 * c + 2 ) ( 2 * c + 1 ) ] ;
        linarith

/-
Block sum identity for the extended dual variables.
-/
noncomputable def Y_tilde (n : ℕ) (k : ℕ) : ℝ :=
  if k = 0 then 0
  else
    if k % 2 == 0 then
      B_term n k
    else
      B_term n k + Y_tilde n ((k - 1) / 2)
termination_by k
decreasing_by
  simp_wf
  omega

/-
`Y_sol` and `Y_tilde` agree for $k \le n/2$.
-/
lemma Y_sol_eq_Y_tilde {n k : ℕ} (hk : k ≤ n / 2) : Y_sol n k = Y_tilde n k := by
  induction' k using Nat.strongRecOn with k ih generalizing n;
  unfold Y_sol Y_tilde;
  grind +ring

/-
Loose upper bound on $Y\_tilde_k$.
-/
lemma Y_tilde_loose_bound {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n / 2) :
    Y_tilde n k ≤ (2 * k : ℝ) * n.choose k := by
      induction' k using Nat.strong_induction_on with k ihizing n;
      unfold Y_tilde;
      split_ifs <;> simp_all +decide [ B_term ];
      · nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( n.choose k : ℝ ) ≥ 0 by positivity, show ( n.choose ( k - 1 ) : ℝ ) ≥ 0 by positivity ];
      · -- Since $k$ is odd, we have $Y_tilde n ((k - 1) / 2) \leq 2 * ((k - 1) / 2) * Nat.choose n ((k - 1) / 2)$ by the induction hypothesis.
        have h_ind : Y_tilde n ((k - 1) / 2) ≤ 2 * ((k - 1) / 2) * Nat.choose n ((k - 1) / 2) := by
          rcases Nat.even_or_odd' k with ⟨ c, rfl | rfl ⟩ <;> norm_num at *;
          exact if hc : 1 ≤ c then ihizing c ( by linarith ) hc ( by omega ) else by interval_cases c ; unfold Y_tilde; norm_num;
        -- Since $k$ is odd, we have $(k - 1) * \binom{n}{(k - 1) / 2} \leq k * \binom{n}{k}$.
        have h_odd : (k - 1) * Nat.choose n ((k - 1) / 2) ≤ k * Nat.choose n k := by
          rcases Nat.even_or_odd' k with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide
          have h_odd : Nat.choose n (2 * c + 1) ≥ Nat.choose n c := by
            have h_odd : ∀ i j : ℕ, i ≤ j → j ≤ n / 2 → Nat.choose n i ≤ Nat.choose n j := by
              intros i j hij hjn
              induction' hij with j hj ih;
              · norm_num;
              · exact le_trans ( ih ( Nat.le_of_succ_le hjn ) ) ( Nat.choose_le_succ_of_lt_half_left ( by linarith [ Nat.div_mul_le_self n 2 ] ) );
            exact h_odd _ _ ( by linarith ) ( by linarith );
          nlinarith [ Nat.choose_pos ( show c ≤ n by linarith [ Nat.div_mul_le_self n 2 ] ) ];
        rcases k with ( _ | _ | k ) <;> simp_all +decide
        · linarith;
        · nlinarith [ ( by norm_cast : ( k + 1 : ℝ ) * Nat.choose n ( ( k + 1 ) / 2 ) ≤ ( k + 1 + 1 ) * Nat.choose n ( k + 1 + 1 ) ), Nat.div_mul_le_self ( k + 1 ) 2 ]

/-
The sum of B_k/k telescopes to binom(n, m) + sum_{j=1}^{m-1} binom(n, j)/(j+1).
-/
lemma sum_Bk_div_k {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) :
    ∑ k ∈ Finset.Icc 1 m, B_term n k / k = n.choose m + ∑ j ∈ Finset.Icc 1 (m - 1), (n.choose j : ℝ) / (j + 1) := by
      -- By definition of $B_k$, we can split the sum into two parts.
      have h_split : ∑ k ∈ Finset.Icc 1 m, (B_term n k : ℝ) / (k : ℝ) = ∑ k ∈ Finset.Icc 1 m, (n.choose k : ℝ) - ∑ k ∈ Finset.Icc 1 m, ((k - 1 : ℝ) * n.choose (k - 1) / (k : ℝ)) := by
        rw [ ← Finset.sum_sub_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rcases x with ( _ | x ) <;> norm_num [ Nat.choose ] at * ; ring_nf;
        unfold B_term; norm_num [ hn, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_choose ] ; ring_nf;
        nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( 1 + x : ℝ ) ≠ 0 ) ( Nat.choose ( m * 2 ) ( 1 + x ) : ℝ ) ];
      -- The second sum can be reindexed to start from 1.
      have h_reindex : ∑ k ∈ Finset.Icc 1 m, ((k - 1 : ℝ) * n.choose (k - 1) / (k : ℝ)) = ∑ j ∈ Finset.Icc 1 (m - 1), ((j : ℝ) * n.choose j / (j + 1 : ℝ)) := by
        erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, add_assoc ];
        cases m <;> norm_num [ add_comm, add_left_comm, Finset.sum_range_succ' ] at *;
      -- Recognize that the sum $\sum_{j=1}^{m-1} \frac{j \binom{n}{j}}{j+1}$ can be rewritten using the identity $\frac{j}{j+1} = 1 - \frac{1}{j+1}$.
      have h_identity : ∑ j ∈ Finset.Icc 1 (m - 1), ((j : ℝ) * n.choose j / (j + 1 : ℝ)) = ∑ j ∈ Finset.Icc 1 (m - 1), ((n.choose j : ℝ) - (n.choose j / (j + 1 : ℝ))) := by
        exact Finset.sum_congr rfl fun x hx => by rw [ sub_div' ] ; ring ; positivity;
      rcases m with ( _ | _ | m ) <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ]

/-
For t <= m/2, Y_t <= 2t * binom(n, t).
-/
lemma Y_bound_small_t {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) (t : ℕ) (ht : 1 ≤ t) (htm : t ≤ m / 2) :
    Y_sol n t ≤ (2 * t : ℝ) * n.choose t := by
      have h_upper_bound : ∀ t : ℕ, 1 ≤ t → t ≤ n / 2 → Y_tilde n t ≤ 2 * t * n.choose t := by
        exact fun t a a_1 ↦ Y_tilde_loose_bound a a_1;
      exact le_trans ( Y_sol_eq_Y_tilde ( by omega ) |> le_of_eq ) ( h_upper_bound t ht ( by omega ) )

/-
The sum of binom(n, j)/(j+1) for j < m is at most 2^n / (n+1).
-/
lemma sum_binom_div_j_plus_1 {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) :
    ∑ j ∈ Finset.range m, (n.choose j : ℝ) / (j + 1) ≤ (2 ^ n : ℝ) / (n + 1) := by
      -- Using the identity $\binom{n}{j} / (j + 1) = \binom{n + 1}{j + 1} / (n + 1)$, we can rewrite the sum.
      have h_identity : ∑ j ∈ Finset.range m, (n.choose j : ℝ) / (j + 1) = (1 / (n + 1 : ℝ)) * ∑ j ∈ Finset.range m, (n + 1).choose (j + 1) := by
        norm_num [ Finset.mul_sum _ _ _ ];
        refine Finset.sum_congr rfl fun i hi => ?_;
        rw [ inv_mul_eq_div, div_eq_div_iff ] <;> norm_cast ; linarith [ Nat.succ_mul_choose_eq n i, Nat.choose_succ_succ n i ];
      -- The sum of binomial coefficients $\sum_{j=0}^{m-1} \binom{n+1}{j+1}$ is at most $2^{n+1} / 2$.
      have h_sum_bound : ∑ j ∈ Finset.range m, (n + 1).choose (j + 1) ≤ 2 ^ (n + 1) / 2 := by
        have h_sum_bound : ∑ j ∈ Finset.range (m + 1), (n + 1).choose j ≤ 2 ^ (n + 1) / 2 := by
          have h_sum_bound : ∑ j ∈ Finset.range (m + 1), (n + 1).choose j + ∑ j ∈ Finset.Ico (m + 1) (n + 2), (n + 1).choose j = 2 ^ (n + 1) := by
            rw [ Finset.sum_range_add_sum_Ico _ ( by linarith ) ] ; rw [ Nat.sum_range_choose ] ;
          have h_sum_bound : ∑ j ∈ Finset.Ico (m + 1) (n + 2), (n + 1).choose j ≥ ∑ j ∈ Finset.range (m + 1), (n + 1).choose j := by
            rw [ Finset.sum_Ico_eq_sum_range ];
            rw [ show n + 2 - ( m + 1 ) = m + 1 by omega ] ; rw [ ← Finset.sum_range_reflect ] ;
            norm_num [ hn ];
            exact Finset.sum_le_sum fun i hi => by rw [ Nat.choose_symm_of_eq_add ] ; linarith [ Nat.sub_add_cancel ( show i ≤ m from Finset.mem_range_succ_iff.mp hi ) ] ;
          rw [ Nat.le_div_iff_mul_le ] <;> linarith;
        simp_all +decide [ Finset.sum_range_succ' ];
        grind;
      -- Substitute the bound from h_sum_bound into h_identity.
      have h_final : (1 / (n + 1 : ℝ)) * (∑ j ∈ Finset.range m, (n + 1).choose (j + 1)) ≤ (1 / (n + 1 : ℝ)) * (2 ^ (n + 1) / 2) := by
        gcongr ; norm_cast;
        rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self ( 2 ^ ( n + 1 ) ) 2 ];
      convert h_final using 1 ; ring;

/-
The dual objective is bounded by binom(n, m) + 2^n/(n+1) + sum_{t=1}^{m/2} binom(n, t).
-/
lemma sum_Y_div_k_bound {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) :
    ∑ k ∈ Finset.Icc 1 m, Y_sol n k / k ≤ (n.choose m : ℝ) + (2 ^ n : ℝ) / (n + 1) + ∑ t ∈ Finset.Icc 1 (m / 2), (n.choose t : ℝ) := by
      -- Split the sum into two parts: one for even $k$ and one for odd $k$.
      have h_split : ∑ k ∈ Finset.Icc 1 m, Y_sol n k / (k : ℝ) = ∑ k ∈ Finset.Icc 1 m, B_term n k / (k : ℝ) + ∑ k ∈ Finset.filter (fun k => k % 2 ≠ 0) (Finset.Icc 1 m), Y_sol n ((k - 1) / 2) / (k : ℝ) := by
        have h_split : ∀ k ∈ Finset.Icc 1 m, Y_sol n k = B_term n k + (if k % 2 ≠ 0 then Y_sol n ((k - 1) / 2) else 0) := by
          intro k hk; rw [ Y_sol ] ; split_ifs <;> simp_all +decide ;
          · linarith;
          · linarith;
        rw [ Finset.sum_congr rfl fun x hx => by rw [ h_split x hx ] ] ; simp +decide [ Finset.sum_add_distrib, add_div, Finset.sum_filter ] ;
        exact Finset.sum_congr rfl fun x hx => by split_ifs <;> ring;
      -- The second part is sum_{t=0}^{(m-1)/2} Y_t / (2t+1).
      have h_odd : ∑ k ∈ Finset.filter (fun k => k % 2 ≠ 0) (Finset.Icc 1 m), Y_sol n ((k - 1) / 2) / (k : ℝ) ≤ ∑ t ∈ Finset.Icc 1 (m / 2), Y_sol n t / (2 * t : ℝ) := by
        have h_odd : ∑ k ∈ Finset.filter (fun k => k % 2 ≠ 0) (Finset.Icc 1 m), Y_sol n ((k - 1) / 2) / (k : ℝ) = ∑ t ∈ Finset.Icc 0 ((m - 1) / 2), Y_sol n t / (2 * t + 1 : ℝ) := by
          refine' Finset.sum_bij ( fun x hx => ( x - 1 ) / 2 ) _ _ _ _ <;> norm_num;
          · intros; omega;
          · intro a₁ ha₁₁ ha₁₂ ha₁₃ a₂ ha₂₁ ha₂₂ ha₂₃ h; omega;
          · exact fun b hb => ⟨ 2 * b + 1, ⟨ ⟨ by linarith, by omega ⟩, by norm_num ⟩, by omega ⟩;
          · intro a ha₁ ha₂ ha₃; rw [ ← Nat.mod_add_div a 2 ] ; norm_num [ ha₃ ] ; ring;
        rw [h_odd];
        erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, Finset.sum_range_succ' ];
        rw [ add_comm, Finset.sum_range_succ' ] ; norm_num [ add_comm, add_left_comm, mul_add ];
        rw [ show Y_sol n 0 = 0 from _ ];
        · rw [ zero_add ];
          exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.div_le_div_right ( Nat.sub_le _ _ ) ) ) fun _ _ _ => div_nonneg ( Y_sol_nonneg ) ( by positivity ) ) ( Finset.sum_le_sum fun _ _ => div_le_div_of_nonneg_left ( Y_sol_nonneg ) ( by positivity ) ( by linarith ) );
        · unfold Y_sol; norm_num;
      -- By Y_bound_small_t, Y_t <= 2t * binom(n, t).
      have h_Y_bound : ∀ t ∈ Finset.Icc 1 (m / 2), Y_sol n t / (2 * t : ℝ) ≤ (n.choose t : ℝ) := by
        intros t ht
        have h_Y_bound : Y_sol n t ≤ (2 * t : ℝ) * n.choose t := by
          apply Y_bound_small_t hm hn t (Finset.mem_Icc.mp ht).left (Finset.mem_Icc.mp ht).right;
        rwa [ div_le_iff₀' ( mul_pos zero_lt_two ( Nat.cast_pos.mpr ( Finset.mem_Icc.mp ht |>.1 ) ) ) ];
      -- By sum_Bk_div_k, sum B_k/k = binom(n, m) + sum_{j=1}^{m-1} binom(n, j)/(j+1).
      have h_sum_Bk_div_k : ∑ k ∈ Finset.Icc 1 m, B_term n k / (k : ℝ) = (n.choose m : ℝ) + ∑ j ∈ Finset.Icc 1 (m - 1), (n.choose j : ℝ) / (j + 1) := by
        convert sum_Bk_div_k hm hn using 1;
      -- By sum_binom_div_j_plus_1, sum_{j=1}^{m-1} binom(n, j)/(j+1) ≤ 2^n/(n+1).
      have h_sum_binom_div_j_plus_1 : ∑ j ∈ Finset.Icc 1 (m - 1), (n.choose j : ℝ) / (j + 1) ≤ (2 ^ n : ℝ) / (n + 1) := by
        have h_sum_binom_div_j_plus_1 : ∑ j ∈ Finset.range m, (n.choose j : ℝ) / (j + 1) ≤ (2 ^ n : ℝ) / (n + 1) := by
          convert sum_binom_div_j_plus_1 hm hn using 1;
        exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( fun x hx => Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp hx, Nat.sub_add_cancel hm ] ) ) fun _ _ _ => by positivity ) h_sum_binom_div_j_plus_1;
      nlinarith [ show ( ∑ t ∈ Finset.Icc 1 ( m / 2 ), Y_sol n t / ( 2 * t : ℝ ) ) ≤ ∑ t ∈ Finset.Icc 1 ( m / 2 ), ( n.choose t : ℝ ) by exact Finset.sum_le_sum h_Y_bound, show ( ∑ t ∈ Finset.Icc 1 ( m / 2 ), ( n.choose t : ℝ ) ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _, show ( 2 ^ n : ℝ ) ≥ 0 by positivity, show ( n + 1 : ℝ ) ≥ 1 by norm_cast; linarith, mul_div_cancel₀ ( 2 ^ n : ℝ ) ( by positivity : ( n + 1 : ℝ ) ≠ 0 ) ]

/-
The sum of binomial coefficients up to k (where 3k <= n) is at most 2 * binom(n, k).
-/
lemma sum_binom_tail_bound {n k : ℕ} (hk : 1 ≤ k) (hkn : 3 * k ≤ n) :
    ∑ i ∈ Finset.range (k + 1), n.choose i ≤ 2 * n.choose k := by
      -- We show that the terms decrease geometrically by induction on $i$.
      have h_geo_decran2 : ∀ i ∈ Finset.range k, Nat.choose n i ≤ Nat.choose n (i + 1) / 2 := by
        intro i hi
        have h_ratio : Nat.choose n i ≤ Nat.choose n (i + 1) / 2 := by
          have h_ratio_ge : Nat.choose n i * 2 ≤ Nat.choose n (i + 1) := by
            nlinarith! [ Finset.mem_range.mp hi, Nat.succ_mul_choose_eq n i, Nat.choose_succ_succ n i ]
          rwa [ Nat.le_div_iff_mul_le zero_lt_two ]
        exact h_ratio;
      induction hk <;> simp_all +decide [ Finset.sum_range_succ ];
      · linarith [ Nat.div_mul_le_self n 2 ];
      · grind

/-
The dual objective is bounded by binom(n, m) + 2^n/(n+1) + 2 * binom(n, m/2).
-/
lemma objective_eval {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) :
    ∑ k ∈ Finset.Icc 1 m, Y_sol n k / k ≤ (n.choose m : ℝ) + (2 ^ n : ℝ) / (n + 1) + 2 * n.choose (m / 2) := by
      by_cases h_case : m / 2 ≥ 1 ∧ 3 * (m / 2) ≤ n;
      · have := sum_binom_tail_bound h_case.1 h_case.2;
        have := sum_Y_div_k_bound hm hn;
        refine le_trans this ?_;
        erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num;
        exact_mod_cast Nat.le_succ_of_le ‹_›;
      · rcases m with ( _ | _ | m ) <;> simp_all +decide [ Nat.div_eq_of_lt ];
        · unfold Y_sol; norm_num [ B_term ] ;
          unfold Y_sol; norm_num [ B_term ] ;
        · grind

/-
Z_final is non-negative.
-/
noncomputable def Z_final (n : ℕ) (j : ℕ) : ℝ :=
  if j = 0 then 1
  else if j = n / 2 + 1 ∧ (n / 2) % 2 == 0 then Y_sol n (n / 4) / (n / 2 + 1)
  else 0

lemma Z_final_nonneg {n : ℕ} : ∀ j, 0 ≤ Z_final n j := by
  intro j
  unfold Z_final;
  split_ifs <;> [ positivity; exact div_nonneg ( Y_sol_nonneg ) ( by positivity ) ; positivity ]

/-
B_term n m equals 2m/(m+1) * binom(n, m).
-/
lemma B_term_eq {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) :
    B_term n m = (2 * m : ℝ) / (m + 1) * n.choose m := by
      unfold B_term
      field_simp
      ring_nf;
      rw [ hn ] ; rcases m with ( _ | m ) <;> norm_num [ Nat.succ_mul_choose_eq ] at * ; ring_nf;
      rw [ show 1 + m = m + 1 by ring, Nat.cast_choose, Nat.cast_choose ] <;> try linarith;
      rw [ show 2 + m * 2 - ( m + 1 ) = m + 1 by rw [ Nat.sub_eq_of_eq_add ] ; ring, show 2 + m * 2 - m = m + 2 by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; push_cast [ Nat.factorial_succ ] ; ring_nf;
      -- Combine like terms and simplify the expression.
      field_simp
      ring

/-
LHS(m+1) >= RHS(m+1).
-/
noncomputable def LHS (n m j : ℕ) : ℝ := ∑ k ∈ Finset.Icc (j / 2) m, Y_sol n k

noncomputable def RHS (n j : ℕ) : ℝ := (j : ℝ) * n.choose j

lemma base_case {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) : LHS n m (m + 1) ≥ RHS n (m + 1) := by
  -- Let's split into cases based on whether m is even or odd.
  by_cases h_even : Even m;
  · -- If m is even, m=2t. j=m+1=2t+1. floor(j/2)=t=m/2.
    obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t := even_iff_two_dvd.mp h_even;
    -- By definition of $LHS$ and $RHS$, we have:
    simp [LHS, RHS];
    have := sum_Y_mid ( show 1 ≤ 2 * t by linarith ) ; simp_all +decide [ Nat.add_div ] ;
    have := Nat.succ_mul_choose_eq ( 2 * ( 2 * t ) ) ( 2 * t ) ; ( have := Nat.succ_mul_choose_eq ( 2 * ( 2 * t ) ) ( 2 * t + 1 ) ; ( norm_cast at * ; simp_all +decide [ Nat.choose_succ_succ, mul_assoc ] ; ) );
    grind;
  · obtain ⟨ k, rfl ⟩ : ∃ k, m = 2 * k + 1 := by exact Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => h_even <| even_iff_two_dvd.mpr <| Nat.dvd_of_mod_eq_zero h );
    -- By definition of $LHS$ and $RHS$, we know that $LHS(n, m, m+1) = \sum_{k=(m+1)/2}^m Y_k$ and $RHS(n, m+1) = (m+1) \binom{n}{m+1}$.
    simp [LHS, RHS];
    have h_sum : ∑ k ∈ Finset.Icc ((2 * k + 1 + 1) / 2) (2 * k + 1), Y_sol n k = (2 * k + 1 + 1) * n.choose (2 * k + 1 + 1) := by
      convert sum_Y_mid ( show 1 ≤ 2 * k + 1 from by linarith ) using 1 ; aesop;
      norm_num [ Nat.add_div, hn ] ; ring_nf
    linarith

/-
The dual inequality holds for j = m + 1.
-/
lemma dual_ineq_m_plus_1 {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) :
    ∑ k ∈ Finset.Icc ((m + 1) / 2) m, Y_sol n k ≥ ((m + 1) : ℝ) * n.choose (m + 1) := by
      convert base_case hm hn using 1 ; ring_nf;
      unfold RHS; norm_num [ hn ] ; ring;

/-
Y_m is at least 2m/(m+1) * binom(n, m).
-/
lemma Y_m_ge_val {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) :
    Y_sol n m ≥ (2 * m : ℝ) / (m + 1) * n.choose m := by
      -- By definition of Y_sol, we know that Y_sol n m is either B_term n m or B_term n m plus some non-negative term.
      have h_Y_sol_def : Y_sol n m = B_term n m + (if m % 2 == 1 then Y_sol n ((m - 1) / 2) else 0) := by
        rw [ Y_sol ];
        grind;
      -- By definition of Y_sol, we know that Y_sol n m is either B_term n m or B_term n m plus some non-negative term. Since B_term n m is equal to (2 * m : ℝ) / (m + 1) * n.choose m by B_term_eq, and Y_sol n ((m - 1) / 2) is non-negative, the inequality holds.
      rw [h_Y_sol_def]
      have h_B_term : B_term n m = (2 * m : ℝ) / (m + 1) * n.choose m := by
        convert B_term_eq hm hn using 1
      rw [h_B_term]
      simp
      split_ifs <;> [ exact Y_sol_nonneg; exact le_rfl ]

/-
For odd m, LHS(m+2) = LHS(m+1).
-/
lemma LHS_eq_odd {n m : ℕ} (hm : m % 2 = 1) : LHS n m (m + 2) = LHS n m (m + 1) := by
  unfold LHS; push_cast [ Nat.add_div ] ; aesop;

/-
For even m, LHS(m+2) = LHS(m+1) - Y_{m/2}.
-/
lemma LHS_eq_even {n m : ℕ} (he : m % 2 = 0) (hm : m ≥ 1) : LHS n m (m + 2) = LHS n m (m + 1) - Y_sol n (m / 2) := by
  unfold LHS;
  simp +arith +decide [ Nat.add_div, he, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
  rw [ Finset.Icc_eq_cons_Ioc ( by linarith [ Nat.mod_add_div m 2 ] ), Finset.sum_cons ] ; aesop

/-
RHS(m+1) - RHS(m+2) = 2 * binom(n, m+1).
-/
lemma RHS_diff_eq {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) :
    RHS n (m + 1) - RHS n (m + 2) = 2 * n.choose (m + 1) := by
      -- Using the identity for binomial coefficients, we can rewrite RHS(m+2).
      have h_rhs_m2 : RHS n (m + 2) = (2 * m - (m + 2) + 1) * (2 * m).choose (m + 1) := by
        unfold RHS; norm_num [ hn ] ; ring_nf;
        field_simp;
        rw [ Nat.add_comm 2 m, Nat.add_comm 1 m ] ; norm_cast ; rw [ Nat.choose_succ_right_eq ] ; ring_nf;
        rw [ show m * 2 - ( 1 + m ) = m - 1 by omega ];
      simp_all +decide [ RHS ];
      ring

/-
A relation between $\binom{2m}{m+1}$ and $\binom{2m}{m}$.
-/
lemma binom_relation (m : ℕ) : (m + 1) * (2 * m).choose (m + 1) = m * (2 * m).choose m := by
  nlinarith [ Nat.succ_mul_choose_eq ( 2 * m ) m, Nat.choose_succ_succ ( 2 * m ) m ]

/-
An auxiliary inequality for binomial coefficients.
-/
lemma binom_ineq_aux (m : ℕ) (hm : m ≥ 4) : 2 * (2 * m).choose m ≥ (m + 1) * (2 * m).choose (m / 2) := by
  -- Let's rewrite the inequality in terms of factorials.
  have h_factorial : 2 * (Nat.factorial (2 * m)) / (Nat.factorial m * Nat.factorial m) ≥ (m + 1) * (Nat.factorial (2 * m)) / (Nat.factorial (m / 2) * Nat.factorial (2 * m - m / 2)) := by
    -- We can cancel out the common term $(2m)!$ in the numerator and denominator.
    suffices h_cancel : 2 * (Nat.factorial (m / 2) * Nat.factorial (2 * m - m / 2)) ≥ (m + 1) * (Nat.factorial m * Nat.factorial m) by
      rw [ ge_iff_le, Nat.div_le_iff_le_mul_add_pred ] <;> norm_num;
      · nlinarith [ Nat.div_add_mod ( 2 * ( 2 * m ) ! ) ( m ! * m ! ), Nat.mod_lt ( 2 * ( 2 * m ) ! ) ( by positivity : 0 < m ! * m ! ), Nat.sub_add_cancel ( show 1 ≤ ( m / 2 ) ! * ( 2 * m - m / 2 ) ! from Nat.mul_pos ( Nat.factorial_pos _ ) ( Nat.factorial_pos _ ) ), Nat.factorial_pos ( 2 * m ) ] ;
      · exact ⟨ Nat.factorial_pos _, Nat.factorial_pos _ ⟩;
    rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩ <;> norm_num [ Nat.mul_succ, Nat.factorial ] at *;
    · rw [ show 2 * ( 2 * k ) - k = 3 * k by rw [ Nat.sub_eq_of_eq_add ] ; ring ];
      induction' k with k ih <;> norm_num [ Nat.factorial_succ, Nat.mul_succ ] at *;
      rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.factorial_succ, Nat.mul_succ ];
      ring_nf at *;
      nlinarith [ pow_nonneg ( Nat.zero_le k ) 3, pow_nonneg ( Nat.zero_le k ) 4, pow_nonneg ( Nat.zero_le k ) 5, pow_nonneg ( Nat.zero_le k ) 6, pow_nonneg ( Nat.zero_le k ) 7, pow_nonneg ( Nat.zero_le k ) 8, pow_nonneg ( Nat.zero_le k ) 9, pow_nonneg ( Nat.zero_le k ) 10, pow_nonneg ( Nat.zero_le k ) 11, pow_nonneg ( Nat.zero_le k ) 12, pow_nonneg ( Nat.zero_le k ) 13 ];
    · norm_num [ Nat.add_div ] at *;
      rw [ show 2 * ( 2 * k ) + 2 - k = 3 * k + 2 by rw [ Nat.sub_eq_of_eq_add ] ; ring ];
      induction' k with k ih <;> norm_num [ Nat.factorial_succ, Nat.mul_succ ] at *;
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.factorial_succ, Nat.mul_succ ];
      ring_nf at *;
      nlinarith [ pow_nonneg ( Nat.zero_le k ) 3, pow_nonneg ( Nat.zero_le k ) 4, pow_nonneg ( Nat.zero_le k ) 5, pow_nonneg ( Nat.zero_le k ) 6, pow_nonneg ( Nat.zero_le k ) 7, pow_nonneg ( Nat.zero_le k ) 8, pow_nonneg ( Nat.zero_le k ) 9, pow_nonneg ( Nat.zero_le k ) 10, pow_nonneg ( Nat.zero_le k ) 11, pow_nonneg ( Nat.zero_le k ) 12, pow_nonneg ( Nat.zero_le k ) 13, pow_nonneg ( Nat.zero_le k ) 14, pow_nonneg ( Nat.zero_le k ) 15 ];
  convert h_factorial using 1 <;> norm_num [ Nat.choose_eq_factorial_div_factorial ( show m ≤ 2 * m by linarith ), Nat.choose_eq_factorial_div_factorial ( show m / 2 ≤ 2 * m by omega ) ];
  · rw [ ← Nat.mul_div_assoc ];
    · grind;
    · exact Nat.factorial_mul_factorial_dvd_factorial ( by linarith );
  · rw [ Nat.mul_div_assoc _ ( Nat.factorial_mul_factorial_dvd_factorial ( by omega ) ) ]

/-
2 * binom(n, m+1) >= m * binom(n, m/2) for m >= 4.
-/
lemma binom_ineq_even_case {n m : ℕ} (hm : m ≥ 4) (hn : n = 2 * m) :
    2 * n.choose (m + 1) ≥ m * n.choose (m / 2) := by
      subst hn;
      nlinarith [ binom_relation m, binom_ineq_aux m hm ]

/-
LHS(j+2) = LHS(j) - Y_{j/2}.
-/
lemma LHS_recurrence {n m j : ℕ} (hn : n = 2 * m) (hj : j + 2 ≤ 2 * m + 2) :
    LHS n m (j + 2) = LHS n m j - (if j / 2 < (j + 2) / 2 then Y_sol n (j / 2) else 0) := by
      unfold LHS at *; simp +decide [ * ];
      erw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Nat.div_lt_iff_lt_mul ];
      · rw [ Finset.sum_range_succ, sub_sub ];
        rw [ Finset.sum_range_succ ];
      · omega;
      · omega

/-
LHS(m+2) >= RHS(m+2) for m >= 4.
-/
lemma LHS_ge_RHS_base {n m : ℕ} (hm : m ≥ 4) (hn : n = 2 * m) :
    LHS n m (m + 2) ≥ RHS n (m + 2) := by
      -- Case m odd:
      by_cases hmo : m % 2 = 1;
      · -- Since $j = m + 2$ is greater than $m$, we can use the fact that $RHS$ is decreasing for $j > m$.
        have h_RHS_decreasing : ∀ j, m < j → j ≤ n → RHS n (j + 1) ≤ RHS n j := by
          intros j hj1 hj2
          have h_decreasing : (j + 1 : ℝ) * n.choose (j + 1) ≤ (j : ℝ) * n.choose j := by
            norm_cast;
            nlinarith [ Nat.succ_mul_choose_eq n j, Nat.choose_succ_succ n j ];
          unfold RHS; aesop;
        have := base_case ( by linarith ) hn; have := h_RHS_decreasing ( m + 1 ) ( by linarith ) ( by linarith ) ; simp_all +decide [ LHS ] ;
        convert this.trans ‹_› using 1 ; congr ; omega;
      · -- By the base case, we know that LHS(m+1) ≥ RHS(m+1).
        have h_base : LHS n m (m + 1) ≥ RHS n (m + 1) := by
          convert dual_ineq_m_plus_1 ( by linarith ) hn using 1;
          unfold RHS; aesop;
        -- By the properties of the binomial coefficients and the definitions of LHS and RHS, we can show that LHS(m+2) ≥ RHS(m+2).
        have h_ineq : RHS n (m + 1) - RHS n (m + 2) ≥ Y_sol n (m / 2) := by
          have h_ineq : RHS n (m + 1) - RHS n (m + 2) = 2 * n.choose (m + 1) := by
            convert RHS_diff_eq ( by linarith ) hn using 1;
          have h_ineq : Y_sol n (m / 2) ≤ m * n.choose (m / 2) := by
            convert Y_bound_small_t ( by linarith ) hn ( m / 2 ) ( Nat.div_pos ( by linarith ) ( by linarith ) ) ( Nat.div_le_div_right ( by linarith ) ) using 1 ; ring_nf;
            rw [ Nat.cast_div ( Nat.dvd_of_mod_eq_zero ( by simpa using hmo ) ) ] <;> ring_nf ; norm_num;
          have h_ineq : 2 * n.choose (m + 1) ≥ m * n.choose (m / 2) := by
            convert binom_ineq_even_case hm hn using 1;
          linarith [ ( by norm_cast : ( m : ℝ ) * n.choose ( m / 2 ) ≤ 2 * n.choose ( m + 1 ) ) ];
        have h_eq : LHS n m (m + 2) = LHS n m (m + 1) - Y_sol n (m / 2) := by
          apply LHS_eq_even;
          · exact Nat.mod_two_ne_one.mp hmo;
          · linarith;
        linarith [ show Y_sol n ( m / 2 ) ≥ 0 from Y_sol_nonneg ]

/-
LHS(m+2) >= RHS(m+2) for even m >= 4.
-/
lemma LHS_ge_RHS_base_even {n m : ℕ} (hm : m ≥ 4) (hn : n = 2 * m) :
    LHS n m (m + 2) ≥ RHS n (m + 2) := by
      exact LHS_ge_RHS_base hm hn

/-
LHS(m+2) >= RHS(m+2) for odd m.
-/
lemma LHS_ge_RHS_base_odd {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) (ho : m % 2 = 1) :
    LHS n m (m + 2) ≥ RHS n (m + 2) := by
      have h_lhs_ge_rhs : LHS n m (m + 1) ≥ RHS n (m + 1) := by
        exact base_case hm hn
      have h_rhs_decreasing : RHS n (m + 1) ≥ RHS n (m + 2) := by
        by_cases hmn : m < n / 2 <;> simp_all +decide
        unfold RHS; norm_num [ Nat.choose_succ_succ, two_mul ] ; ring_nf;
        rw [ show 2 + m = m + 2 by ring, show 1 + m = m + 1 by ring ] ; norm_cast ; simp +arith +decide [ mul_comm ] ; ring_nf ;
        rw [ show 2 + m = m + 1 + 1 by ring, show 1 + m = m + 1 by ring ] ; nlinarith only [ hm, Nat.succ_mul_choose_eq ( m * 2 ) ( m + 1 ), Nat.choose_succ_succ ( m * 2 ) ( m + 1 ) ] ;
      have h_lhs_eq : LHS n m (m + 2) = LHS n m (m + 1) := by
        exact LHS_eq_odd ho
      linarith [h_lhs_ge_rhs, h_rhs_decreasing, h_lhs_eq]

/-
LHS(m+2) >= RHS(m+2) for m >= 4.
-/
lemma LHS_ge_RHS_base_final {n m : ℕ} (hm : m ≥ 4) (hn : n = 2 * m) :
    LHS n m (m + 2) ≥ RHS n (m + 2) := by
      rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩;
      · apply LHS_ge_RHS_base_even hm hn;
      · apply LHS_ge_RHS_base_odd (by linarith) hn;
        simp

/-
The dual constraint holds for j = m + 1.
-/
lemma dual_constraint_m_plus_1 {m : ℕ} (hm : m ≥ 1) :
    let n := 2 * m
    let j := m + 1
    (∑ k ∈ Finset.Icc ((j + 1) / 2) (min j (n / 2)), Y_sol n k / (j * n.choose j)) + Z_final n j / n.choose j ≥ 1 := by
      -- By definition of $Y_sol$ and $Z_final$, we can split into cases based on whether $m$ is even or odd.
      by_cases heven : m % 2 = 0;
      · -- Since $m$ is even, we have $Y_{m/2} + \sum_{k=m/2+1}^m Y_k = (m+1) \binom{n}{m+1}$.
        have h_sum : Y_sol (2 * m) (m / 2) + ∑ k ∈ Finset.Icc (m / 2 + 1) m, Y_sol (2 * m) k = (m + 1) * Nat.choose (2 * m) (m + 1) := by
          have h_sum : Y_sol (2 * m) (m / 2) + ∑ k ∈ Finset.Icc (m / 2 + 1) m, Y_sol (2 * m) k = ∑ k ∈ Finset.Icc (m / 2) m, Y_sol (2 * m) k := by
            erw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Nat.div_mul_cancel ( Nat.dvd_of_mod_eq_zero heven ) ];
            · rw [ Finset.sum_range_succ, Finset.sum_range_succ ] ; ring;
            · omega;
            · exact Nat.div_le_self _ _;
          have h_sum : ∑ k ∈ Finset.Icc (m / 2) m, Y_sol (2 * m) k = (2 * (m / 2) : ℝ) * Nat.choose (2 * m) (2 * (m / 2)) := by
            have h_sum : ∑ k ∈ Finset.Icc (m / 2) m, Y_sol (2 * m) k = ∑ k ∈ Finset.Icc (m / 2) (2 * (m / 2)), Y_sol (2 * m) k := by
              rw [ Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero heven ) ];
            have h_sum : ∑ k ∈ Finset.Icc (m / 2) (2 * (m / 2)), Y_sol (2 * m) k = (2 * (m / 2) : ℝ) * Nat.choose (2 * m) (2 * (m / 2)) := by
              have := block_sum_identities (by linarith [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heven)]) (by
              omega : 2 * (m / 2) ≤ 2 * m / 2)
              rw [ this.1, Nat.cast_div ( Nat.dvd_of_mod_eq_zero heven ) ] <;> norm_num [ Nat.mul_div_assoc, heven ]
            generalize_proofs at *;
            aesop;
          rw [ ‹Y_sol ( 2 * m ) ( m / 2 ) + ∑ k ∈ Finset.Icc ( m / 2 + 1 ) m, Y_sol ( 2 * m ) k = ∑ k ∈ Finset.Icc ( m / 2 ) m, Y_sol ( 2 * m ) k›, h_sum ] ; norm_num [ Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero heven ) ] ; ring_nf;
          field_simp;
          rw_mod_cast [ Nat.add_comm 1 m, Nat.choose_succ_right_eq ] ; ring_nf;
          rw [ Nat.mul_two, Nat.add_sub_cancel ] ; ring;
        -- By dividing both sides of h_sum by (m + 1) * binom(2m, m + 1), we obtain the desired inequality.
        have h_div : (Y_sol (2 * m) (m / 2) + ∑ k ∈ Finset.Icc (m / 2 + 1) m, Y_sol (2 * m) k) / ((m + 1) * Nat.choose (2 * m) (m + 1)) = 1 := by
          rw [ h_sum, div_self <| by exact mul_ne_zero ( by positivity ) <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| by linarith ];
        convert h_div.ge using 1;
        unfold Z_final; norm_num [ Nat.add_div, heven ] ; ring_nf;
        norm_num [ Nat.add_mod, Nat.mul_mod, heven ] ; ring_nf;
        rw [ show m * 2 / 4 = m / 2 by omega ] ; ring_nf;
        norm_num [ add_comm, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
        exact Or.inl ( by rw [ ← mul_inv ] ; ring );
      · unfold Z_final;
        -- Since $m$ is odd, we have $LHS n m (m + 1) \geq RHS n (m + 1)$.
        have h_ineq : (∑ k ∈ Finset.Icc ((m + 1) / 2) m, Y_sol (2 * m) k) ≥ ((m + 1) : ℝ) * (2 * m).choose (m + 1) := by
          convert dual_ineq_m_plus_1 hm rfl using 1;
        simp_all +decide [ ← Finset.sum_div _ _ _, Nat.mul_div_cancel_left _ ( by positivity : 0 < 2 ) ];
        rw [ le_div_iff₀ ( mul_pos ( by positivity ) ( Nat.cast_pos.mpr ( Nat.choose_pos ( by linarith ) ) ) ) ] ; convert h_ineq using 1 ; norm_num [ Nat.add_div, heven ];
        grind

/-
The sum of B_k telescopes.
-/
lemma sum_Bk_telescope {n m t : ℕ} (hn : n = 2 * m) (ht : 1 ≤ t) (htm : t ≤ m) :
    ∑ k ∈ Finset.Icc t m, B_term n k = (m : ℝ) * n.choose m - (t - 1 : ℝ) * n.choose (t - 1) := by
      erw [ Finset.sum_Ico_eq_sub _ _ ];
      · rw [ show ( ∑ k ∈ Finset.range ( m + 1 ), B_term n k ) = ↑m * ↑ ( n.choose m ) from ?_, show ( ∑ k ∈ Finset.range t, B_term n k ) = ( ↑t - 1 ) * ↑ ( n.choose ( t - 1 ) ) from ?_ ];
        · induction ht <;> simp_all +decide [ Finset.sum_range_succ ];
          · unfold B_term; norm_num;
          · rename_i k hk ih; rw [ ih ( by linarith ) ] ; unfold B_term; ring_nf;
            cases k <;> norm_num at * ; linarith;
        · have h_telescope : ∀ t, ∑ k ∈ Finset.range (t + 1), B_term n k = t * (n.choose t : ℝ) := by
            intro t; induction t <;> simp_all +decide [ Finset.sum_range_succ ] ; ring_nf;
            · unfold B_term; norm_num;
            · unfold B_term; ring_nf;
              norm_num ; ring;
          exact h_telescope m;
      · linarith

/-
LHS(j) >= Y_m for j <= 2m.
-/
lemma LHS_ge_Y_m_lemma {n m j : ℕ} (hj : j ≤ 2 * m) :
    LHS n m j ≥ Y_sol n m := by
  unfold LHS
  have h_mem : m ∈ Finset.Icc (j / 2) m := by
    rw [Finset.mem_Icc]
    constructor
    · apply Nat.div_le_of_le_mul
      linarith
    · exact le_rfl
  apply Finset.single_le_sum
  · intros k _
    exact Y_sol_nonneg
  · exact h_mem

/-
Y_m is at least binom(n, m).
-/
lemma Y_m_ge_binom {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) :
    Y_sol n m ≥ n.choose m := by
      -- We know $Y_m \ge B_m$ and $B_m = \frac{2m}{m+1} \binom{n}{m}$.
      have h_B_m : Y_sol n m ≥ (2 * m : ℝ) / (m + 1) * n.choose m := by
        exact Y_m_ge_val hm hn;
      exact le_trans ( le_mul_of_one_le_left ( Nat.cast_nonneg _ ) ( by rw [ le_div_iff₀ ] <;> norm_cast <;> linarith ) ) h_B_m

/-
Binomial coefficients decay exponentially relative to a reference point k, with rate determined by the ratio at k.
-/
lemma binom_decay {n k j : ℕ} (hk : k ≤ j) (hjn : j ≤ n) :
    (n.choose j : ℝ) ≤ (n.choose k : ℝ) * ((n - k : ℝ) / (k + 1)) ^ (j - k) := by
      have h_binom_ratio : ∀ {j : ℕ}, k ≤ j → j ≤ n → (n.choose j : ℝ) ≤ (n.choose k : ℝ) * ((n - k : ℝ) / (k + 1)) ^ (j - k) := by
        intros j hk hjn
        induction' hk with j hj ih;
        · norm_num +zetaDelta at *;
        · have h_binom_ratio_step : (n.choose (j + 1) : ℝ) = (n.choose j : ℝ) * ((n - j : ℝ) / (j + 1)) := by
            rw [ mul_div, eq_div_iff ] <;> norm_cast;
            rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast ; rw [ Nat.choose_succ_right_eq ];
          have h_binom_ratio_step : (n.choose (j + 1) : ℝ) ≤ (n.choose j : ℝ) * ((n - k : ℝ) / (k + 1)) := by
            exact h_binom_ratio_step.symm ▸ mul_le_mul_of_nonneg_left ( by rw [ div_le_div_iff₀ ] <;> nlinarith only [ show ( k : ℝ ) ≤ j by norm_cast, show ( j : ℝ ) + 1 ≤ n by norm_cast ] ) ( Nat.cast_nonneg _ );
          convert h_binom_ratio_step.trans ( mul_le_mul_of_nonneg_right ( ih ( Nat.le_of_succ_le hjn ) ) ( div_nonneg ( sub_nonneg.mpr <| Nat.cast_le.mpr <| by linarith ) <| by positivity ) ) using 1 ; rw [ Nat.succ_sub hj ] ; ring_nf;
          simpa only [ pow_succ' ] using by ring;
      exact h_binom_ratio hk hjn

/-
Binomial coefficients decrease after the midpoint.
-/
lemma binom_decreasing_after_m {n m k : ℕ} (hn : n = 2 * m) (hm : m ≤ k) (hkn : k < n) :
    n.choose (k + 1) ≤ n.choose k := by
      have := @Nat.choose_succ_right_eq n k;
      nlinarith [ Nat.sub_add_cancel hkn.le ]

/-
The ratio at k2=1.15m is at most 0.75.
-/
lemma ratio_bound_1 {m : ℕ} (hm : m ≥ 100) (n : ℕ) (hn : n = 2 * m) :
    let k2 := 115 * m / 100
    (n - k2 : ℝ) / (k2 + 1) ≤ 0.75 := by
      -- Substitute n = 2m and k2 = 115m/100 into the inequality.
      field_simp [hn];
      norm_num [ hn ];
      field_simp;
      norm_cast; linarith [ Nat.div_add_mod ( 115 * m ) 100, Nat.mod_lt ( 115 * m ) ( by decide : 0 < 100 ) ] ;

/-
The ratio at k1=1.07m is at most 0.88.
-/
lemma ratio_bound_2 {m : ℕ} (hm : m ≥ 100) (n : ℕ) (hn : n = 2 * m) :
    let k1 := 107 * m / 100
    (n - k1 : ℝ) / (k1 + 1) ≤ 0.88 := by
      field_simp;
      norm_num [ hn ];
      rw [ mul_div, div_add', le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_add_mod ( 107 * m ) 100, Nat.mod_lt ( 107 * m ) ( by norm_num : 0 < 100 ) ]

/-
Binomial coefficients are bounded by the central coefficient for k >= m.
-/
lemma binom_le_of_ge_mid {n m k : ℕ} (hn : n = 2 * m) (hm : m ≤ k) (hkn : k ≤ n) :
    n.choose k ≤ n.choose m := by
  induction' k with k ih
  · simp at hm
    rw [hm]
  · by_cases h : m ≤ k
    · have h_le : n.choose (k + 1) ≤ n.choose k := by
        apply binom_decreasing_after_m hn h (Nat.lt_of_succ_le hkn)
      exact le_trans h_le (ih h (Nat.le_of_succ_le hkn))
    · have h_eq : k + 1 = m := by linarith
      rw [h_eq]

/-
Binomial decay from j to k2 with ratio 0.75.
-/
lemma decay_j_to_k2 {m : ℕ} (hm : m ≥ 100) (n : ℕ) (hn : n = 2 * m) (j : ℕ) (hj : j > 13 * m / 10) (hjn : j ≤ n) :
    let k2 := 115 * m / 100
    (n.choose j : ℝ) ≤ (n.choose k2 : ℝ) * (0.75) ^ (j - k2) := by
      have h_decay : let k2 := 115 * m / 100;
        (n.choose j : ℝ) ≤ (n.choose k2 : ℝ) * ((n - k2 : ℝ) / (k2 + 1)) ^ (j - k2) := by
          apply_rules [ binom_decay ];
          omega;
      exact h_decay.trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( div_nonneg ( sub_nonneg.mpr <| mod_cast by omega ) <| by positivity ) ( by have := ratio_bound_1 hm n hn; norm_num at *; linarith ) _ ) <| Nat.cast_nonneg _ )

/-
Binomial decay from k2 to k1 with ratio 0.88.
-/
lemma decay_k2_to_k1 {m : ℕ} (hm : m ≥ 100) (n : ℕ) (hn : n = 2 * m) :
    let k1 := 107 * m / 100
    let k2 := 115 * m / 100
    (n.choose k2 : ℝ) ≤ (n.choose k1 : ℝ) * (0.88) ^ (k2 - k1) := by
      -- Apply `binom_decay` from k1 to k2.
      have h_binom_decay : let k1 := 107 * m / 100; let k2 := 115 * m / 100; (n.choose k2 : ℝ) ≤ (n.choose k1 : ℝ) * ((n - k1 : ℝ) / (k1 + 1)) ^ (k2 - k1) := by
        apply_rules [ binom_decay ];
        · omega;
        · omega;
      refine le_trans h_binom_decay ?_;
      gcongr;
      · exact div_nonneg ( sub_nonneg_of_le ( mod_cast by omega ) ) ( by positivity );
      · convert ratio_bound_2 hm n hn using 1

/-
Stronger arithmetic bound for decay factors.
-/
lemma decay_bound_stronger {m : ℕ} (hm : m ≥ 200) :
    (0.88 : ℝ) ^ (8 * m / 100) * (0.75 : ℝ) ^ (15 * m / 100) ≤ 0.88 / (2 * m) := by
      induction' m using Nat.strong_induction_on with m ih;
      by_cases hm200 : m ≥ 400;
      · have := ih ( m - 200 ) ( Nat.sub_lt ( by linarith ) ( by linarith ) ) ( by linarith [ Nat.sub_add_cancel ( by linarith : 200 ≤ m ) ] );
        rw [ Nat.cast_sub ( by linarith ) ] at this;
        rw [ show ( 8 * m / 100 : ℕ ) = ( 8 * ( m - 200 ) / 100 ) + 16 by omega, show ( 15 * m / 100 : ℕ ) = ( 15 * ( m - 200 ) / 100 ) + 30 by omega ] ; norm_num [ pow_add ] at *;
        rw [ le_div_iff₀ ] at * <;> nlinarith [ ( by norm_cast : ( 400 : ℝ ) ≤ m ) ];
      · interval_cases m <;> norm_num

/-
For j > 1.3m, binom(n, j) is at most binom(n, m) / (2m).
-/
lemma binom_large_j_bound {m : ℕ} (hm : m ≥ 200) (n : ℕ) (hn : n = 2 * m) (j : ℕ) (hj : j > 13 * m / 10) (hjn : j ≤ n) :
    (n.choose j : ℝ) ≤ (n.choose m : ℝ) / (2 * m) := by
      have h_ratio2 : (n.choose j : ℝ) ≤ (n.choose (115 * m / 100) : ℝ) * (0.75 : ℝ) ^ (j - 115 * m / 100) := by
        convert decay_j_to_k2 ( by linarith ) n hn j hj hjn using 1;
      have h_ratio1 : (n.choose (115 * m / 100) : ℝ) ≤ (n.choose (107 * m / 100) : ℝ) * (0.88 : ℝ) ^ (115 * m / 100 - 107 * m / 100) := by
        apply_rules [ decay_k2_to_k1 ];
        linarith;
      have h_combined : (n.choose j : ℝ) ≤ (n.choose m : ℝ) * (0.88 : ℝ) ^ (8 * m / 100) * (0.75 : ℝ) ^ (15 * m / 100 + 1) := by
        have h_combined : (n.choose (107 * m / 100) : ℝ) ≤ (n.choose m : ℝ) := by
          exact_mod_cast binom_le_of_ge_mid hn ( by omega ) ( by omega );
        refine le_trans h_ratio2 <| le_trans ( mul_le_mul_of_nonneg_right h_ratio1 <| by positivity ) ?_;
        refine' mul_le_mul _ _ _ _ <;> try positivity;
        · exact mul_le_mul h_combined ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( by omega ) ) ( by positivity ) ( by positivity );
        · exact pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( by omega );
      have := decay_bound_stronger hm;
      norm_num [ pow_add ] at * ; ring_nf at * ; nlinarith [ inv_mul_cancel₀ ( by positivity : ( m : ℝ ) ≠ 0 ) ] ;

/-
For j > 1.3m, Y_m dominates RHS(j).
-/
lemma dual_ineq_large_j_part2 {m : ℕ} (hm : m ≥ 200) (n : ℕ) (hn : n = 2 * m) :
    ∀ j, 13 * m / 10 < j → j ≤ n → Y_sol n m ≥ RHS n j := by
      have h_rhs_le_binom : ∀ j, 13 * m / 10 < j → j ≤ n → RHS n j ≤ (n.choose m : ℝ) := by
        intros j hj₁ hj₂
        have h_binom_large_j_bound : (n.choose j : ℝ) ≤ (n.choose m : ℝ) / (2 * m) := by
          exact binom_large_j_bound hm n hn j hj₁ hj₂;
        exact le_trans ( mul_le_mul_of_nonneg_left h_binom_large_j_bound <| Nat.cast_nonneg _ ) <| by rw [ mul_div, div_le_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod ( 13 * m ) 10, Nat.mod_lt ( 13 * m ) ( by decide : 0 < 10 ) ] ;
      exact fun j hj₁ hj₂ => le_trans ( h_rhs_le_binom j hj₁ hj₂ ) ( Y_m_ge_binom ( by linarith ) hn )

/-
For $k \in [m/2, 0.7m)$, the ratio of consecutive binomial coefficients is at least 1.5.
-/
lemma binom_ratio_step {n m k : ℕ} (hn : n = 2 * m) (hk1 : m / 2 ≤ k) (hk2 : k < 7 * m / 10) :
    (n.choose (k + 1) : ℝ) ≥ 1.5 * n.choose k := by
      rw [ Nat.cast_choose, Nat.cast_choose ];
      · rw [ show n - k = n - ( k + 1 ) + 1 by omega ] ; push_cast [ Nat.factorial_succ ] ; ring_nf ; norm_num;
        field_simp;
        norm_cast ; omega;
      · omega;
      · omega

/-
$\binom{n}{0.7m} \ge \binom{n}{m/2} * 1.5^{0.2m}$.
-/
lemma binom_growth_iter {n m : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) :
    (n.choose (7 * m / 10) : ℝ) ≥ (n.choose (m / 2) : ℝ) * (1.5 : ℝ) ^ (7 * m / 10 - m / 2) := by
      -- Apply the binomial ratio step repeatedly from $k = m/2$ to $k = 7m/10 - 1$.
      have h_ratio_step : ∀ j ∈ Finset.Icc (m / 2) (7 * m / 10 - 1), (n.choose (j + 1) : ℝ) ≥ 1.5 * (n.choose j : ℝ) := by
        intros j hj
        have h_ratio_step : (n.choose (j + 1) : ℝ) ≥ 1.5 * (n.choose j : ℝ) := by
          apply binom_ratio_step hn (Finset.mem_Icc.mp hj).left (by
          exact lt_of_le_of_lt ( Finset.mem_Icc.mp hj |>.2 ) ( Nat.pred_lt ( ne_bot_of_gt ( Nat.div_pos ( by linarith ) ( by norm_num ) ) ) ))
        exact h_ratio_step;
      -- Apply induction on the number of steps to show the inequality holds.
      have h_induction : ∀ k, k ≤ 7 * m / 10 - m / 2 → (n.choose (m / 2 + k) : ℝ) ≥ (n.choose (m / 2) : ℝ) * (1.5 : ℝ) ^ k := by
        intro k hk; induction' k with k ih <;> norm_num [ pow_succ, mul_assoc ] at *;
        specialize ih ( Nat.le_of_succ_le hk ) ; specialize h_ratio_step ( m / 2 + k ) ( by omega ) ( by omega ) ; ring_nf at *; linarith;
      convert h_induction ( 7 * m / 10 - m / 2 ) le_rfl using 1 ; rw [ Nat.add_sub_of_le ( by omega ) ]

/-
For $m \ge 200$, $m \le 1.5^{\lfloor m/5 \rfloor}$.
-/
lemma linear_le_exp_bound_nat {m : ℕ} (hm : m ≥ 200) :
    (m : ℝ) ≤ (1.5 : ℝ) ^ (m / 5) := by
      -- By induction on $k$, we can show that $800 \leq 1.5^k * 800$ for all $k \geq 40$.
      have h_ind : ∀ k ≥ 40, (800 : ℝ) ≤ 1.5 ^ k * 800 := by
        exact fun k hk => le_mul_of_one_le_left ( by norm_num ) ( one_le_pow₀ ( by norm_num ) );
      contrapose! h_ind;
      use 40 - 1;
      revert h_ind; norm_num [ Nat.cast_pow ] ; norm_cast;
      induction' m using Nat.strong_induction_on with m ih;
      by_cases hm' : m < 400;
      · interval_cases m <;> norm_num;
      · have := ih ( m - 5 ) ( Nat.sub_lt ( by linarith ) ( by linarith ) ) ( Nat.le_sub_of_add_le ( by linarith ) ) ; norm_num at *;
        rw [ show m / 5 = ( m - 5 ) / 5 + 1 by omega ] ; norm_num [ pow_succ' ] at * ; rw [ Nat.cast_sub ( by linarith ) ] at * ; linarith [ ( by norm_cast : ( 400 : ℝ ) ≤ m ) ] ;

/-
The growth factor $1.5^{0.2m}$ is at least $m$.
-/
lemma growth_factor_bound {m : ℕ} (hm : m ≥ 200) :
    (m : ℝ) ≤ (1.5 : ℝ) ^ (7 * m / 10 - m / 2) := by
      -- Combine the previous results to conclude the proof.
      have h_combined : (m : ℝ) ≤ (1.5 : ℝ) ^ (m / 5 : ℕ) := by
        exact linear_le_exp_bound_nat hm
      have h_final : (m : ℝ) ≤ (1.5 : ℝ) ^ (7 * m / 10 - m / 2 : ℕ) := by
        exact h_combined.trans ( pow_le_pow_right₀ ( by norm_num ) ( by omega ) )
      exact_mod_cast h_final

/-
For $m \ge 200$, $m \binom{n}{m/2} \le \binom{n}{1.3m}$.
-/
lemma binom_ratio_bound {n m : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) :
    (m : ℝ) * n.choose (m / 2) ≤ n.choose (13 * m / 10) := by
      rw [ hn ] at *; norm_cast at *; simp_all +decide
      have h2 : (2 * m).choose (13 * m / 10) ≥ (2 * m).choose (7 * m / 10) := by
        have h_symm : (2 * m).choose (13 * m / 10) = (2 * m).choose (2 * m - 13 * m / 10) := by
          rw [ Nat.choose_symm ( by omega ) ]
        generalize_proofs at *; (
        have h_symm : 2 * m - 13 * m / 10 ≥ 7 * m / 10 ∧ 2 * m - 13 * m / 10 ≤ 2 * m / 2 := by
          omega
        generalize_proofs at *; (
        have h_binom_growth : ∀ k l : ℕ, k ≤ l → l ≤ 2 * m / 2 → (2 * m).choose k ≤ (2 * m).choose l := by
          intros k l hkl hlm
          induction' hkl with k l hkl ih
          generalize_proofs at *; (
          grind);
          exact le_trans ( hkl ( Nat.le_of_succ_le hlm ) ) ( Nat.choose_le_succ_of_lt_half_left ( by omega ) )
        generalize_proofs at *; (
        grind)))
      generalize_proofs at *; (
      have h3 : (2 * m).choose (7 * m / 10) ≥ (2 * m).choose (m / 2) * (1.5 : ℝ) ^ (7 * m / 10 - m / 2) := by
        have := binom_growth_iter ( by linarith : 200 ≤ m ) rfl; aesop;
      have h4 : (1.5 : ℝ) ^ (7 * m / 10 - m / 2) ≥ m := by
        convert growth_factor_bound hm using 1
      generalize_proofs at *; (
      exact_mod_cast ( by nlinarith [ ( by norm_cast : ( 200 : ℝ ) ≤ m ), ( by norm_cast : ( Nat.choose ( 2 * m ) ( 7 * m / 10 ) : ℝ ) ≤ Nat.choose ( 2 * m ) ( 13 * m / 10 ) ) ] : ( m : ℝ ) * Nat.choose ( 2 * m ) ( m / 2 ) ≤ Nat.choose ( 2 * m ) ( 13 * m / 10 ) )))

/-
The maximum size of a union-free family in the power set of [n].
-/
noncomputable def MaxUnionFree (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter UnionFree).sup Finset.card

/-
The term $2^n/(n+1)$ is little-o of $\binom{n}{n/2}$.
-/
lemma pow_two_div_n_little_o_binom_half :
    (fun (n : ℕ) => (2 : ℝ) ^ n / (n + 1 : ℝ)) =o[Filter.atTop] (fun (n : ℕ) => (Nat.choose n (n / 2) : ℝ)) := by
      rw [ Asymptotics.isLittleO_iff_tendsto' ];
      · -- We'll use the fact that $\binom{2m}{m} \sim \frac{4^m}{\sqrt{\pi m}}$ as $m \to \infty$.
        have h_binom : Filter.Tendsto (fun m : ℕ => (Nat.choose (2 * m) m : ℝ) / (4 ^ m / Real.sqrt (Real.pi * m))) Filter.atTop (nhds 1) := by
          have h_stirling : Filter.Tendsto (fun m : ℕ => (Nat.factorial (2 * m) : ℝ) / ((Nat.factorial m) ^ 2 * (4 ^ m / Real.sqrt (Real.pi * m)))) Filter.atTop (nhds 1) := by
            have h_binom : Filter.Tendsto (fun m : ℕ => (Nat.factorial (2 * m) : ℝ) / ((Nat.factorial m) ^ 2 * (4 ^ m / Real.sqrt (Real.pi * m)))) Filter.atTop (nhds 1) := by
              have h_stirling : Filter.Tendsto (fun m : ℕ => (Nat.factorial m : ℝ) / (Real.sqrt (2 * Real.pi * m) * (m / Real.exp 1) ^ m)) Filter.atTop (nhds 1) := by
                have := @Stirling.factorial_isEquivalent_stirling;
                rw [ Asymptotics.IsEquivalent ] at this;
                rw [ Asymptotics.isLittleO_iff_tendsto' ] at this;
                · have := this.const_add 1; simp_all +decide [ mul_comm, mul_left_comm ] ;
                  refine' this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ add_div' ] ; ring ; positivity );
                · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn h using absurd h <| by positivity;
              have h_stirling_2m : Filter.Tendsto (fun m : ℕ => (Nat.factorial (2 * m) : ℝ) / (Real.sqrt (2 * Real.pi * (2 * m)) * ((2 * m) / Real.exp 1) ^ (2 * m))) Filter.atTop (nhds 1) := by
                exact_mod_cast h_stirling.comp ( Filter.tendsto_id.nsmul_atTop two_pos );
              convert h_stirling_2m.div ( h_stirling.pow 2 ) _ using 2 <;> norm_num;
              field_simp
              ring_nf;
              norm_num [ pow_mul' ];
            convert h_binom using 1;
          convert h_stirling using 2 ; norm_num [ two_mul, Nat.cast_choose ] ; ring;
        -- Using the fact that $\binom{2m}{m} \sim \frac{4^m}{\sqrt{\pi m}}$, we can show that $\frac{2^{2m}}{2m+1} \cdot \frac{\sqrt{\pi m}}{4^m} \to 0$ as $m \to \infty$.
        have h_lim : Filter.Tendsto (fun m : ℕ => (2 ^ (2 * m) / (2 * m + 1) : ℝ) * (Real.sqrt (Real.pi * m) / 4 ^ m)) Filter.atTop (nhds 0) := by
          norm_num [ pow_mul ];
          -- We can factor out $\sqrt{m}$ and use the fact that $\frac{1}{m}$ tends to $0$ as $m$ tends to infinity.
          have h_factor : Filter.Tendsto (fun m : ℕ => Real.sqrt Real.pi / (2 * Real.sqrt m + 1 / Real.sqrt m)) Filter.atTop (nhds 0) := by
            exact tendsto_const_nhds.div_atTop ( Filter.Tendsto.atTop_add ( Filter.Tendsto.const_mul_atTop zero_lt_two <| by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) <| tendsto_const_nhds.div_atTop <| by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
          refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm using by rw [ div_eq_div_iff ] <;> first | positivity | ring_nf ; norm_num [ hm.ne', le_of_lt hm ] );
        have h_lim : Filter.Tendsto (fun m : ℕ => (2 ^ (2 * m) / (2 * m + 1) : ℝ) / (Nat.choose (2 * m) m)) Filter.atTop (nhds 0) := by
          have := h_lim.div h_binom;
          simp_all +decide [ division_def ];
          refine' this.congr' _;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm using by simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( Real.sqrt_pos.mpr Real.pi_pos ), ne_of_gt ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr hm ) ), ne_of_gt ( pow_pos ( zero_lt_four' ℝ ) m ) ] ;
        rw [ Metric.tendsto_nhds ] at *;
        intro ε hε; rcases Filter.eventually_atTop.mp ( h_lim ε hε ) with ⟨ N, hN ⟩ ; refine' Filter.eventually_atTop.mpr ⟨ 2 * N, fun n hn => _ ⟩ ; rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
        · exact hN k hn;
        · have := hN k ( by linarith ) ; norm_num [ Nat.add_div ] at *;
          refine' lt_of_le_of_lt _ this;
          rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith;
          norm_num [ two_mul, add_assoc, Nat.factorial ];
          field_simp;
          rw [ abs_of_nonneg, abs_of_nonneg ] <;> ring_nf <;> norm_cast <;> norm_num;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| Nat.div_le_self _ _

/-
Identity expressing $\binom{n}{n/4}$ in terms of $\binom{n}{n/2}$ and a product of ratios.
-/
lemma binom_ratio_identity (n : ℕ) (h : n / 4 ≤ n / 2) :
    (Nat.choose n (n / 4) : ℝ) = (Nat.choose n (n / 2) : ℝ) * ∏ k ∈ Finset.Ico (n / 4) (n / 2), ((k + 1 : ℝ) / (n - k : ℝ)) := by
      -- By repeatedly applying the identity, we can express $\binom{n}{n/4}$ in terms of $\binom{n}{n/2}$ and a product of ratios.
      have h_seq : ∀ (i j : ℕ), i ≤ j → j ≤ n → (Nat.choose n i : ℝ) = (Nat.choose n j : ℝ) * (∏ k ∈ Finset.Ico i j, (k + 1 : ℝ) / (n - k)) := by
        intros i j hij hjn
        induction' hij with k hk ih;
        · norm_num +zetaDelta at *;
        · rw [ Finset.prod_Ico_succ_top ( by linarith [ Nat.succ_le_succ hk ] ), mul_comm ];
          rw [ ih ( Nat.le_of_succ_le hjn ), mul_comm ];
          rw [ mul_assoc, show ( Nat.choose n ( k + 1 ) : ℝ ) = ( Nat.choose n k : ℝ ) * ( n - k ) / ( k + 1 ) from ?_ ];
          · field_simp;
            rw [ mul_div_cancel_right₀ _ ( sub_ne_zero_of_ne ( by norm_cast; linarith ) ) ];
          · rw [ eq_div_iff ] <;> norm_cast;
            rw [ Int.subNatNat_of_le ( by linarith ) ] ; push_cast [ Nat.choose_succ_right_eq ] ; ring;
      grind

/-
For $n \ge 32$ and $k \le 3n/8$, the ratio $\frac{k+1}{n-k}$ is at most 0.65.
-/
lemma ratio_bound_precise' (n k : ℕ) (hn : 32 ≤ n) (hk_upper : k ≤ 3 * n / 8) :
    (k + 1 : ℝ) / (n - k : ℝ) ≤ 0.65 := by
      rw [ div_le_iff₀ ];
      · norm_num; linarith [ show ( k : ℝ ) ≤ 3 * n / 8 by rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self ( 3 * n ) 8 ], show ( n : ℝ ) ≥ 32 by norm_cast ] ;
      · exact sub_pos_of_lt ( by norm_cast; omega )

/-
The product of ratios $\frac{k+1}{n-k}$ for $k$ from $n/4$ to $n/2-1$.
-/
noncomputable def ratio_product (n : ℕ) : ℝ := ∏ k ∈ Finset.Ico (n / 4) (n / 2), ((k + 1 : ℝ) / (n - k : ℝ))

/-
The product of ratios is bounded by $0.65^{n/8}$.
-/
lemma ratio_product_bound (n : ℕ) (hn : 32 ≤ n) :
    ratio_product n ≤ (0.65 : ℝ) ^ (n / 8) := by
      -- Split the product into two parts: from n/4 to 3n/8 and from 3n/8+1 to n/2-1.
      have h_split : ratio_product n = (∏ k ∈ Finset.Ico (n / 4) (3 * n / 8), ((k + 1 : ℝ) / (n - k))) * (∏ k ∈ Finset.Ico (3 * n / 8) (n / 2), ((k + 1 : ℝ) / (n - k))) := by
        rw [ ← Finset.prod_union ( Finset.disjoint_right.mpr fun x hx => by aesop ) ];
        rw [ Finset.Ico_union_Ico_eq_Ico ];
        · rfl;
        · omega;
        · omega;
      -- Apply the bounds to each part of the product.
      have h_part1 : ∏ k ∈ Finset.Ico (n / 4) (3 * n / 8), ((k + 1 : ℝ) / (n - k)) ≤ (0.65) ^ (3 * n / 8 - n / 4) := by
        have h_part1 : ∀ k ∈ Finset.Ico (n / 4) (3 * n / 8), ((k + 1 : ℝ) / (n - k)) ≤ 0.65 := by
          intros k hk
          apply ratio_bound_precise' n k hn (by
          linarith [ Finset.mem_Ico.mp hk ]);
        convert Finset.prod_le_prod ?_ h_part1 <;> norm_num;
        · rw [ ← div_pow ];
        · exact fun _ _ _ => div_nonneg ( by positivity ) ( sub_nonneg_of_le ( by norm_cast; omega ) )
      have h_part2 : ∏ k ∈ Finset.Ico (3 * n / 8) (n / 2), ((k + 1 : ℝ) / (n - k)) ≤ 1 ^ (n / 2 - 3 * n / 8) := by
        exact le_trans ( Finset.prod_le_one ( fun _ _ => div_nonneg ( by positivity ) ( sub_nonneg.mpr ( Nat.cast_le.mpr ( by linarith [ Finset.mem_Ico.mp ‹_›, Nat.div_mul_le_self n 2, Nat.div_mul_le_self ( 3 * n ) 8 ] ) ) ) ) fun _ _ => div_le_one_of_le₀ ( by linarith [ Finset.mem_Ico.mp ‹_›, Nat.div_mul_le_self n 2, Nat.div_mul_le_self ( 3 * n ) 8, show ( ↑‹ℕ› : ℝ ) + 1 ≤ n - ( ↑‹ℕ› : ℝ ) by exact le_tsub_of_add_le_left ( by norm_cast; linarith [ Finset.mem_Ico.mp ‹_›, Nat.div_mul_le_self n 2, Nat.div_mul_le_self ( 3 * n ) 8 ] ) ] ) ( sub_nonneg.mpr ( Nat.cast_le.mpr ( by linarith [ Finset.mem_Ico.mp ‹_›, Nat.div_mul_le_self n 2, Nat.div_mul_le_self ( 3 * n ) 8 ] ) ) ) ) ( by norm_num );
      refine le_trans ( h_split.le.trans ( mul_le_mul h_part1 h_part2 ?_ ?_ ) ) ?_ <;> norm_num at *;
      · exact div_nonneg ( Finset.prod_nonneg fun _ _ => by positivity ) ( Finset.prod_nonneg fun _ _ => sub_nonneg_of_le ( by norm_cast; linarith [ Finset.mem_Ico.mp ‹_›, Nat.div_mul_le_self n 2 ] ) );
      · exact pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( by omega )

/-
$\binom{n}{n/4}$ is little-o of $\binom{n}{n/2}$.
-/
lemma binom_quarter_little_o_binom_half :
    (fun (n : ℕ) => (Nat.choose n (n / 4) : ℝ)) =o[Filter.atTop] (fun (n : ℕ) => (Nat.choose n (n / 2) : ℝ)) := by
      -- By definition of $ratio_product$, we have $\binom{n}{n/4} = \binom{n}{n/2} \cdot ratio_product n$.
      have h_ratio_product : ∀ n : ℕ, (n.choose (n / 4) : ℝ) = (n.choose (n / 2) : ℝ) * ratio_product n := by
        intro n
        rw [binom_ratio_identity];
        · rfl;
        · omega;
      -- Since $0.65 < 1$, $0.65^{n/8} \to 0$ as $n \to \infty$.
      have h_lim : Filter.Tendsto (fun n : ℕ => (0.65 : ℝ) ^ (n / 8)) Filter.atTop (nhds 0) := by
        exact tendsto_pow_atTop_nhds_zero_of_lt_one ( by norm_num ) ( by norm_num ) |> Filter.Tendsto.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ 8 * x, fun n hn => by linarith [ Nat.div_add_mod n 8, Nat.mod_lt n ( by norm_num : 0 < 8 ) ] ⟩;
      -- By definition of $ratio_product$, we have $\binom{n}{n/4} \leq \binom{n}{n/2} \cdot 0.65^{n/8}$ for $n \geq 32$.
      have h_bound : ∀ n : ℕ, 32 ≤ n → (n.choose (n / 4) : ℝ) ≤ (n.choose (n / 2) : ℝ) * (0.65 : ℝ) ^ (n / 8) := by
        exact fun n hn => by rw [ h_ratio_product ] ; exact mul_le_mul_of_nonneg_left ( ratio_product_bound n hn ) ( Nat.cast_nonneg _ ) ;
      rw [ Asymptotics.isLittleO_iff_tendsto' ];
      · refine' squeeze_zero_norm' _ h_lim;
        filter_upwards [ Filter.eventually_ge_atTop 32 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ div_le_iff₀ ( Nat.cast_pos.mpr <| Nat.choose_pos <| by omega ) ] ; linarith [ h_bound n hn ] ;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn h using absurd h <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| by omega;

/-
The size of the largest union-free family is at least $\binom{n}{n/2}$.
-/
lemma max_union_free_ge_binom (n : ℕ) : (n.choose (n / 2) : ℝ) ≤ MaxUnionFree n := by
  refine' mod_cast le_trans _ ( Finset.le_sup <| show Finset.powersetCard ( n / 2 ) Finset.univ ∈ Finset.filter UnionFree ( Finset.univ : Finset ( Finset ( Finset ( Fin n ) ) ) ) from _ );
  · norm_num [ Finset.card_univ ];
  · simp_all +decide [ UnionFree ];
    intro A hA B hB C hC hAB hBC hAC h; have := Finset.card_union_add_card_inter A B; simp_all +decide ;
    have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : A ∩ B ⊆ A ) ; ( have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : A ∩ B ⊆ B ) ; aesop; )

/-
Upper bound on $Y_k$: $Y_k \le 2k \binom{n}{k}$.
-/
lemma Y_sol_upper_bound (n k : ℕ) : Y_sol n k ≤ 2 * k * n.choose k := by
  by_cases hk : k ≤ n / 2;
  · by_cases hk : 1 ≤ k;
    · convert Y_tilde_loose_bound hk ‹_› using 1;
      (expose_names; exact Y_sol_eq_Y_tilde hk_1);
    · unfold Y_sol; aesop;
  · -- Since $k > n / 2$, by definition of $Y_sol$, we have $Y_sol n k = 0$.
    have h_Y_sol_zero : Y_sol n k = 0 := by
      unfold Y_sol; aesop;
    exact h_Y_sol_zero.symm ▸ by positivity;

/-
Recurrence relation for LHS: $LHS(j) - LHS(j+2) = Y_{j/2}$.
-/
lemma LHS_recurrence_simpler {n m j : ℕ} (hj : j / 2 < m) :
    LHS n m j - LHS n m (j + 2) = Y_sol n (j / 2) := by
      unfold LHS; norm_num [ Nat.add_div ] ;
      erw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ hj.le ];
      · rw [ Finset.sum_range_succ, add_sub_cancel_left ];
      · linarith [ Nat.div_mul_le_self j 2 ]

/-
$\binom{n}{0.7m}$ is at least $m$ times $\binom{n}{0.65m}$.
-/
lemma binom_growth_065_070 {m : ℕ} (hm : m ≥ 200) (n : ℕ) (hn : n = 2 * m) :
    (n.choose (7 * m / 10) : ℝ) ≥ (m : ℝ) * n.choose (13 * m / 20) := by
      have h_ratio_growth : (Nat.choose n (7 * m / 10) : ℝ) ≥ (Nat.choose n (13 * m / 20) : ℝ) * (∏ k ∈ Finset.Ico (13 * m / 20) (7 * m / 10), ((n - k : ℝ) / (k + 1))) := by
        have h_ratio_growth : ∀ {a b : ℕ}, a ≤ b → b ≤ n → (Nat.choose n b : ℝ) ≥ (Nat.choose n a : ℝ) * (∏ k ∈ Finset.Ico a b, ((n - k : ℝ) / (k + 1))) := by
          intros a b hab hbn
          induction' hab with b hb ih;
          · norm_num;
          · rw [ Finset.prod_Ico_succ_top ( by linarith [ Nat.succ_le_succ hb ] ) ];
            have h_ratio_growth_step : (Nat.choose n (b + 1) : ℝ) ≥ (Nat.choose n b : ℝ) * ((n - b : ℝ) / (b + 1)) := by
              rw [ mul_div, ge_iff_le, div_le_iff₀ ] <;> norm_cast <;> try linarith;
              rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast;
              rw [ ← Nat.choose_succ_right_eq ];
            simpa only [ ← mul_assoc ] using le_trans ( mul_le_mul_of_nonneg_right ( ih ( Nat.le_of_succ_le hbn ) ) ( div_nonneg ( sub_nonneg.mpr ( Nat.cast_le.mpr ( by linarith ) ) ) ( by positivity ) ) ) h_ratio_growth_step;
        exact h_ratio_growth ( by omega ) ( by omega );
      -- The product of the ratios is at least (1.85 : ℝ) ^ (7 * m / 10 - 13 * m / 20).
      have h_prod_ratio : ∏ k ∈ Finset.Ico (13 * m / 20) (7 * m / 10), ((n - k : ℝ) / (k + 1)) ≥ (1.85 : ℝ) ^ (7 * m / 10 - 13 * m / 20) := by
        have h_prod_ratio : ∀ k ∈ Finset.Ico (13 * m / 20) (7 * m / 10), ((n - k : ℝ) / (k + 1)) ≥ 1.85 := by
          norm_num [ hn ];
          intro k hk₁ hk₂; rw [ le_div_iff₀ ] <;> linarith [ show ( k : ℝ ) + 1 ≤ 7 * m / 10 by exact le_div_iff₀' ( by positivity ) |>.2 <| by norm_cast; linarith [ Nat.div_mul_le_self ( 7 * m ) 10 ], show ( m : ℝ ) ≥ 200 by norm_cast ] ;
        refine' le_trans _ ( Finset.prod_le_prod _ h_prod_ratio ) ; norm_num;
        · rw [ ← div_pow ];
        · norm_num +zetaDelta at *;
      -- Since $1.85^{0.05m}$ grows exponentially and $m$ grows linearly, for $m \geq 200$, $1.85^{0.05m} \geq m$.
      have h_exp_growth : ∀ m : ℕ, 200 ≤ m → (1.85 : ℝ) ^ (7 * m / 10 - 13 * m / 20) ≥ m := by
        intro m hm
        have h_exp_growth : (1.85 : ℝ) ^ (m / 20) ≥ m := by
          induction' m using Nat.strong_induction_on with m ih;
          by_cases hm' : m < 400;
          · interval_cases m <;> norm_num;
          · have := ih ( m - 20 ) ( Nat.sub_lt ( by linarith ) ( by linarith ) ) ( Nat.le_sub_of_add_le ( by linarith ) ) ; norm_num at *;
            rw [ show m / 20 = ( m - 20 ) / 20 + 1 by omega ] ; norm_num [ pow_add ] at * ; rw [ Nat.cast_sub ( by linarith ) ] at * ; nlinarith [ ( by norm_cast : ( 400 :ℝ ) ≤ m ) ] ;
        exact le_trans h_exp_growth ( pow_le_pow_right₀ ( by norm_num ) ( by omega ) );
      nlinarith [ h_exp_growth m hm, show ( 0 : ℝ ) ≤ Nat.choose n ( 13 * m / 20 ) by positivity ]

/-
For $j \in [m+2, 1.3m]$, $\binom{n}{j} \ge m \binom{n}{j/2}$.
-/
lemma binom_ineq_range {n m j : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) (hj1 : m + 2 ≤ j) (hj2 : j ≤ 13 * m / 10) :
    (n.choose j : ℝ) ≥ (m : ℝ) * n.choose (j / 2) := by
      -- By Lemma binom_growth_065_070, we have $\binom{n}{0.7m} \ge m \binom{n}{0.65m}$.
      have h_binom_growth : (Nat.choose n (7 * m / 10) : ℝ) ≥ (m : ℝ) * (Nat.choose n (13 * m / 20) : ℝ) := by
        exact binom_growth_065_070 hm n hn;
      -- Since $j \in [m+2, 1.3m]$, we have $\binom{n}{j} \ge \binom{n}{\lfloor 1.3m \rfloor}$.
      have h_binom_ge_floor : (Nat.choose n j : ℝ) ≥ (Nat.choose n (13 * m / 10) : ℝ) := by
        have h_binom_ge_floor : ∀ k, m + 2 ≤ k → k ≤ 13 * m / 10 → (Nat.choose n k : ℝ) ≥ (Nat.choose n (13 * m / 10) : ℝ) := by
          intros k hk1 hk2
          have h_binom_ge_floor : ∀ k, m + 2 ≤ k → k ≤ 13 * m / 10 → (Nat.choose n k : ℝ) ≥ (Nat.choose n (k + 1) : ℝ) := by
            intros k hk1 hk2
            have h_binom_ge_floor : (Nat.choose n k : ℝ) ≥ (Nat.choose n (k + 1) : ℝ) := by
              have h_binom_ge_floor : (Nat.choose n k : ℝ) * (n - k) ≥ (Nat.choose n (k + 1) : ℝ) * (k + 1) := by
                have := Nat.choose_succ_right_eq n k;
                norm_cast;
                rw [ Int.subNatNat_of_le ( by omega ) ] ; norm_cast ; aesop
              nlinarith [ show ( k : ℝ ) ≥ m + 2 by norm_cast, show ( n : ℝ ) = 2 * m by norm_cast, show ( k : ℝ ) ≤ 13 * m / 10 by rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self ( 13 * m ) 10 ] ];
            exact h_binom_ge_floor;
          have h_binom_ge_floor : ∀ k, m + 2 ≤ k → k ≤ 13 * m / 10 → ∀ l, k ≤ l → l ≤ 13 * m / 10 → (Nat.choose n k : ℝ) ≥ (Nat.choose n l : ℝ) := by
            intros k hk1 hk2 l hkl hlk
            induction' hkl with l hl ih;
            · grind;
            · exact le_trans ( h_binom_ge_floor l ( by linarith [ Nat.succ_le_succ hl ] ) ( by linarith ) ) ( ih ( by linarith ) );
          exact h_binom_ge_floor k hk1 hk2 _ hk2 le_rfl;
        exact h_binom_ge_floor j hj1 hj2;
      -- Since $j \in [m+2, 1.3m]$, we have $\binom{n}{j/2} \le \binom{n}{\lfloor 0.65m \rfloor}$.
      have h_binom_le_floor : (Nat.choose n (j / 2) : ℝ) ≤ (Nat.choose n (13 * m / 20) : ℝ) := by
        have h_binom_le_floor : j / 2 ≤ 13 * m / 20 := by
          omega;
        have h_binom_le_floor : ∀ k, k ≤ 13 * m / 20 → (Nat.choose n k : ℝ) ≤ (Nat.choose n (13 * m / 20) : ℝ) := by
          intros k hk_le_floor
          have h_binom_le_floor : ∀ k, k ≤ 13 * m / 20 → k ≤ n / 2 → (Nat.choose n k : ℝ) ≤ (Nat.choose n (13 * m / 20) : ℝ) := by
            intros k hk_le_floor hk_le_half
            have h_binom_le_floor : ∀ k, k ≤ 13 * m / 20 → k ≤ n / 2 → (Nat.choose n k : ℝ) ≤ (Nat.choose n (k + 1) : ℝ) := by
              intros k hk_le_floor hk_le_half
              have h_binom_le_floor : (Nat.choose n (k + 1) : ℝ) = (Nat.choose n k : ℝ) * (n - k) / (k + 1) := by
                rw [ eq_div_iff ] <;> norm_cast;
                rw [ Int.subNatNat_of_le ( by omega ) ] ; norm_cast ; rw [ Nat.choose_succ_right_eq ];
              rw [ h_binom_le_floor, le_div_iff₀ ] <;> try linarith [ show ( k : ℝ ) ≤ 13 * m / 20 by exact le_trans ( Nat.cast_le.mpr hk_le_floor ) ( by rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self ( 13 * m ) 20 ] ), show ( n : ℝ ) = 2 * m by exact_mod_cast hn ] ;
              exact mul_le_mul_of_nonneg_left ( by rw [ le_sub_iff_add_le ] ; norm_cast; omega ) ( Nat.cast_nonneg _ );
            have h_binom_le_floor : ∀ k, k ≤ 13 * m / 20 → k ≤ n / 2 → ∀ l, k ≤ l → l ≤ 13 * m / 20 → (Nat.choose n k : ℝ) ≤ (Nat.choose n l : ℝ) := by
              intros k hk_le_floor hk_le_half l hkl hl_le_floor
              induction' hkl with l hl ih;
              · norm_num +zetaDelta at *;
              · exact le_trans ( ih ( Nat.le_of_succ_le hl_le_floor ) ) ( h_binom_le_floor _ ( Nat.le_of_succ_le hl_le_floor ) ( by omega ) );
            exact h_binom_le_floor k hk_le_floor hk_le_half _ hk_le_floor le_rfl;
          exact h_binom_le_floor k hk_le_floor ( by omega ) |> le_trans ( by norm_num ) ;
        exact h_binom_le_floor _ ‹_›;
      -- By Lemma binom_symm_large, we have $\binom{n}{\lfloor 1.3m \rfloor} = \binom{n}{\lceil 0.7m \rceil}$.
      have h_binom_symm : (Nat.choose n (13 * m / 10) : ℝ) = (Nat.choose n (2 * m - 13 * m / 10) : ℝ) := by
        rw [ hn, Nat.choose_symm ( by omega ) ];
      -- Since $2m - 13m/10 \geq 7m/10$, we have $\binom{n}{2m - 13m/10} \geq \binom{n}{7m/10}$.
      have h_binom_ge_7m10 : (Nat.choose n (2 * m - 13 * m / 10) : ℝ) ≥ (Nat.choose n (7 * m / 10) : ℝ) := by
        have h_binom_ge_7m10 : ∀ k, 7 * m / 10 ≤ k → k ≤ 2 * m - 13 * m / 10 → (Nat.choose n k : ℝ) ≥ (Nat.choose n (7 * m / 10) : ℝ) := by
          intros k hk1 hk2
          have h_binom_ge_7m10 : ∀ i, 7 * m / 10 ≤ i → i < 2 * m - 13 * m / 10 → (Nat.choose n (i + 1) : ℝ) ≥ (Nat.choose n i : ℝ) := by
            intros i hi1 hi2
            have h_binom_ge_7m10 : (Nat.choose n (i + 1) : ℝ) = (Nat.choose n i : ℝ) * (n - i) / (i + 1) := by
              rw [ eq_div_iff ] <;> norm_cast;
              rw [ Int.subNatNat_of_le ( by omega ) ] ; norm_cast ; rw [ Nat.choose_succ_right_eq ];
            rw [ h_binom_ge_7m10, ge_iff_le, le_div_iff₀ ] <;> norm_num [ hn ];
            · exact mul_le_mul_of_nonneg_left ( by rw [ le_sub_iff_add_le ] ; norm_cast; omega ) ( Nat.cast_nonneg _ );
            · positivity;
          grind;
        exact h_binom_ge_7m10 _ ( by omega ) ( by omega );
      nlinarith [ ( by norm_cast : ( 200 : ℝ ) ≤ m ) ]

/-
Bound on $Y_{j/2}$ relative to $\binom{n}{j}$ for small $j$.
-/
lemma Y_le_RHS_diff_small_j {n m j : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) (hj1 : m + 2 ≤ j) (hj2 : j ≤ 13 * m / 10) :
    Y_sol n (j / 2) ≤ 4 * n.choose j := by
      -- From `binom_ineq_range`, we have $\binom{n}{j} \ge m \binom{n}{j/2}$.
      have h_binom_ineq_range : (n.choose j : ℝ) ≥ (m : ℝ) * n.choose (j / 2) := by
        convert binom_ineq_range hm hn hj1 hj2 using 1;
      -- From `Y_sol_upper_bound`, we have $Y_{j/2} \le 2(j/2) \binom{n}{j/2} = j \binom{n}{j/2}$.
      have h_Y_sol_upper_bound : Y_sol n (j / 2) ≤ (j : ℝ) * n.choose (j / 2) := by
        have := Y_sol_upper_bound n ( j / 2 );
        exact this.trans ( mul_le_mul_of_nonneg_right ( by norm_cast; linarith [ Nat.div_mul_le_self j 2 ] ) ( Nat.cast_nonneg _ ) );
      nlinarith [ show ( j : ℝ ) ≤ 4 * m by norm_cast; omega, show ( m : ℝ ) ≥ 200 by norm_cast, show ( n.choose ( j / 2 ) : ℝ ) ≥ 0 by positivity ]

/-
The gap $RHS(j) - RHS(j+2)$ is at least $4 \binom{n}{j}$.
-/
lemma RHS_gap_ge_4_binom {n m j : ℕ} (hn : n = 2 * m) (hj : j ≥ m + 2) (hjn : j + 2 ≤ n) :
    RHS n j - RHS n (j + 2) ≥ 4 * n.choose j := by
      -- The gap $RHS(j) - RHS(j+2)$ is given by $\binom{n}{j} \frac{n(2j+1-n)}{j+1}$.
      have h_gap : RHS n j - RHS n (j + 2) = (n.choose j : ℝ) * (n * (2 * j + 1 - n) / (j + 1)) := by
        unfold RHS; norm_num; ring_nf;
        rw [ show 2 + j = j + 2 by ring ] ; rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith;
        rw [ show n - j = n - ( j + 2 ) + 2 by omega ] ; norm_num [ Nat.factorial ] ; ring_nf;
        field_simp
        ring_nf;
        rw [ Nat.cast_sub ( by linarith ) ] ; push_cast ; ring;
      -- We need to show that $\frac{n(2j+1-n)}{j+1} \ge 4$.
      have h_ratio : (n * (2 * j + 1 - n) / (j + 1) : ℝ) ≥ 4 := by
        rw [ ge_iff_le, le_div_iff₀ ] <;> nlinarith only [ show ( j : ℝ ) ≥ m + 2 by exact_mod_cast hj, show ( n : ℝ ) = 2 * m by exact_mod_cast hn, show ( j : ℝ ) + 2 ≤ n by exact_mod_cast hjn ];
      nlinarith [ show ( 0 : ℝ ) ≤ n.choose j by positivity ] ;

/-
Inductive step for the dual feasibility inequality for j in the range [m+2, 1.3m].
-/
lemma LHS_ge_RHS_step_small_j {n m j : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) (hj1 : m + 2 ≤ j) (hj2 : j ≤ 13 * m / 10) (h_even : j % 2 = 0) (h_prev : LHS n m j ≥ RHS n j) :
    LHS n m (j + 2) ≥ RHS n (j + 2) := by
      -- By the gap inequality, we have RHS(j) - RHS(j+2) ≥ 4 * binom(n, j).
      have h_gap : RHS n j - RHS n (j + 2) ≥ 4 * n.choose j := by
        apply RHS_gap_ge_4_binom hn (by linarith) (by linarith [Nat.div_mul_le_self (13 * m) 10]);
      -- By the previous step, we have LHS(j) - LHS(j+2) = Y_{j/2}.
      have h_diff : LHS n m j - LHS n m (j + 2) = Y_sol n (j / 2) := by
        convert LHS_recurrence_simpler _ using 1
        generalize_proofs at *; (
        omega)
      generalize_proofs at *; (
      -- By the previous step, we have Y_{j/2} ≤ 4 * binom(n, j).
      have h_Y_le : Y_sol n (j / 2) ≤ 4 * n.choose j := by
        exact Y_le_RHS_diff_small_j hm hn hj1 hj2
      generalize_proofs at *; (
      linarith [ show ( Y_sol n ( j / 2 ) : ℝ ) ≥ 0 from mod_cast Y_sol_nonneg ] ;))

/-
LHS(j) >= RHS(j) for j > 1.3m.
-/
lemma LHS_ge_RHS_large_j {n m j : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) (hj : j > 13 * m / 10) (hjn : j ≤ n) :
    LHS n m j ≥ RHS n j := by
      -- By the lemma dual_ineq_large_j_part2, we have Y_sol n m ≥ RHS n j.
      have h_Y_ge_RHS : Y_sol n m ≥ RHS n j := by
        apply dual_ineq_large_j_part2 hm n hn j hj hjn |> fun h => by
          exact h;
      generalize_proofs at *; (
      exact le_trans h_Y_ge_RHS ( LHS_ge_Y_m_lemma ( by linarith ) ))

/-
General inductive step: if LHS(j) >= RHS(j), then LHS(j+2) >= RHS(j+2).
-/
lemma LHS_ge_RHS_step_general {n m j : ℕ} (hm : m ≥ 200) (hn : n = 2 * m)
    (hj : m + 2 ≤ j) (hjn : j + 2 ≤ n) (h_even : j % 2 = 0)
    (h_prev : LHS n m j ≥ RHS n j) :
    LHS n m (j + 2) ≥ RHS n (j + 2) := by
      by_cases h_large : j + 2 > 13 * m / 10;
      · apply LHS_ge_RHS_large_j hm hn (by
        assumption) (by
        linarith [ Nat.div_mul_le_self ( 13 * m ) 10 ]);
      · apply LHS_ge_RHS_step_small_j hm hn hj (by omega) h_even h_prev

/-
Inductive step for small j, without parity assumption.
-/
lemma LHS_ge_RHS_step_small_j_no_parity {n m j : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) (hj1 : m + 2 ≤ j) (hj2 : j ≤ 13 * m / 10) (h_prev : LHS n m j ≥ RHS n j) :
    LHS n m (j + 2) ≥ RHS n (j + 2) := by
      -- By the recurrence relation for LHS, we have LHS n m (j + 2) = LHS n m j - Y_sol n (j / 2).
      have h_recurrence : LHS n m (j + 2) = LHS n m j - Y_sol n (j / 2) := by
        rw [ ← LHS_recurrence_simpler ];
        exact Eq.symm (sub_sub_self (LHS n m j) (LHS n m (j + 2)));
        omega;
      -- By combining the results from the previous steps, we can conclude the proof.
      have h_combined : LHS n m j - Y_sol n (j / 2) ≥ RHS n j - 4 * n.choose j := by
        exact sub_le_sub h_prev ( Y_le_RHS_diff_small_j hm hn hj1 hj2 );
      exact h_recurrence ▸ h_combined.trans' ( by linarith [ RHS_gap_ge_4_binom hn hj1 ( by omega ) ] )

/-
General inductive step without parity assumption.
-/
lemma LHS_ge_RHS_step_general_no_parity {n m j : ℕ} (hm : m ≥ 200) (hn : n = 2 * m)
    (hj : m + 2 ≤ j) (hjn : j + 2 ≤ n)
    (h_prev : LHS n m j ≥ RHS n j) :
    LHS n m (j + 2) ≥ RHS n (j + 2) := by
      by_cases h_large : j + 2 > 13 * m / 10;
      · -- Apply the lemma LHS_ge_RHS_large_j to j + 2.
        apply LHS_ge_RHS_large_j hm hn (by linarith) (by linarith);
      · exact LHS_ge_RHS_step_small_j_no_parity hm hn hj ( by omega ) h_prev

/-
The gap between RHS(m+1) and RHS(m+3) is at least 4 * binom(n, m+1).
-/
lemma RHS_gap_m_plus_1_strong {n m : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) :
    RHS n (m + 1) - RHS n (m + 3) >= 4 * n.choose (m + 1) := by
      -- By simplifying, we can see that the difference is at least 4 times the binomial coefficient.
      have h_diff : (m + 1 : ℝ) * n.choose (m + 1) - (m + 3 : ℝ) * n.choose (m + 3) ≥ 4 * n.choose (m + 1) := by
        -- Substitute the ratio into the inequality.
        have h_ratio : (n.choose (m + 3) : ℝ) = (n.choose (m + 1) : ℝ) * (m - 1) * (m - 2) / ((m + 2) * (m + 3)) := by
          rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith;
          field_simp;
          rw [ show n - ( m + 1 ) = m - 1 by omega, show n - ( m + 3 ) = m - 3 by omega ] ; rcases m with ( _ | _ | _ | m ) <;> norm_num [ Nat.factorial ] at * ; ring_nf;
          norm_num [ add_comm 3 m ] ; ring;
        rw [ eq_div_iff ] at h_ratio <;> nlinarith [ ( by norm_cast : ( 200 : ℝ ) ≤ m ), pow_two ( m : ℝ ) ];
      convert h_diff using 1;
      unfold RHS; norm_cast;

/-
Inequality for binomial coefficients in the odd case.
-/
lemma binom_ineq_odd_case {n m : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) :
    4 * n.choose (m + 1) ≥ (m + 1) * n.choose ((m + 1) / 2) := by
      -- By the properties of binomial coefficients, we know that $\binom{2m}{m+1} \geq \binom{2m}{(m+1)/2}$.
      have h_binom : Nat.choose (2 * m) (m + 1) ≥ Nat.choose (2 * m) ((m + 1) / 2) := by
        -- Apply the lemma that binomial coefficients are increasing up to the middle term.
        have h_inc : ∀ k l : ℕ, k ≤ l → l ≤ m → Nat.choose (2 * m) k ≤ Nat.choose (2 * m) l := by
          intros k l hkl hlm;
          induction' hkl with k hk ih;
          · rfl;
          · exact le_trans ( ih ( Nat.le_of_succ_le hlm ) ) ( Nat.le_of_lt_succ ( by nlinarith [ Nat.succ_mul_choose_eq ( 2 * m ) k, Nat.choose_succ_succ ( 2 * m ) k ] ) );
        have h_symm : Nat.choose (2 * m) (m + 1) = Nat.choose (2 * m) (m - 1) := by
          rw [ Nat.choose_symm_of_eq_add ] ; omega;
        exact h_symm.symm ▸ h_inc _ _ ( by omega ) ( by omega );
      -- By the lemma `binom_ratio_bound`, we know that $m \cdot \binom{2m}{m/2} \leq \binom{2m}{1.3m}$.
      have h_binom_ratio : (m : ℝ) * Nat.choose (2 * m) (m / 2) ≤ Nat.choose (2 * m) (13 * m / 10) := by
        convert binom_ratio_bound hm hn using 1;
        · rw [ hn ];
        · rw [ hn ];
      -- By the lemma `binom_ratio_bound`, we know that $\binom{2m}{1.3m} \leq \binom{2m}{m+1}$.
      have h_binom_ratio_le : Nat.choose (2 * m) (13 * m / 10) ≤ Nat.choose (2 * m) (m + 1) := by
        -- Since $13m/10 \geq m+1$, we have $\binom{2m}{13m/10} \leq \binom{2m}{m+1}$ by the properties of binomial coefficients.
        have h_binom_le : ∀ k, m + 1 ≤ k → k ≤ 2 * m → Nat.choose (2 * m) k ≤ Nat.choose (2 * m) (m + 1) := by
          intros k hk1 hk2
          have h_binom_le : ∀ i, m + 1 ≤ i → i < 2 * m → Nat.choose (2 * m) i ≥ Nat.choose (2 * m) (i + 1) := by
            intros i hi1 hi2
            have h_binom_le : Nat.choose (2 * m) i ≥ Nat.choose (2 * m) (i + 1) := by
              have h_ratio : (Nat.choose (2 * m) (i + 1) : ℝ) / (Nat.choose (2 * m) i : ℝ) ≤ 1 := by
                rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num [ Nat.choose_succ_succ ];
                · have := Nat.choose_succ_right_eq ( 2 * m ) i;
                  nlinarith [ Nat.sub_add_cancel hi2.le ];
                · exact Nat.choose_pos ( by linarith )
              rw [ div_le_iff₀ ] at h_ratio <;> norm_cast at * <;> linarith [ Nat.choose_pos ( by linarith : i ≤ 2 * m ) ];
            exact h_binom_le;
          have h_binom_le : ∀ i, m + 1 ≤ i → i ≤ k → Nat.choose (2 * m) i ≥ Nat.choose (2 * m) k := by
            intros i hi1 hi2
            induction' hi2 with i hi ih;
            · grind;
            · exact le_trans ( h_binom_le i ( by linarith [ Nat.succ_le_succ hi ] ) ( by linarith ) ) ( ih ( by linarith [ Nat.succ_le_succ hi ] ) ( by linarith ) );
          exact h_binom_le _ le_rfl hk1 |> le_trans <| by norm_num;
        exact h_binom_le _ ( by omega ) ( by omega );
      norm_cast at *;
      rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩ <;> simp +arith +decide [ *] at *;
      · grind;
      · norm_num [ Nat.add_div ] at *;
        have := Nat.succ_mul_choose_eq ( 4 * k + 2 ) k; ( have := Nat.succ_mul_choose_eq ( 4 * k + 2 ) ( k + 1 ) ; ( norm_num [ Nat.choose_succ_succ ] at * ; nlinarith; ) )

/-
Base case for the induction: LHS(m+3) >= RHS(m+3).
-/
lemma LHS_ge_RHS_base_m_plus_3 {n m : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) :
    LHS n m (m + 3) ≥ RHS n (m + 3) := by
      have h_ind_step : LHS n m (m + 1) ≥ RHS n (m + 1) := by
        convert dual_ineq_m_plus_1 _ _ using 1;
        · unfold RHS; aesop;
        · linarith;
        · exact hn;
      have h_ind_step : LHS n m (m + 3) = LHS n m (m + 1) - Y_sol n ((m + 1) / 2) := by
        convert LHS_recurrence hn _ using 1;
        · grind +ring;
        · linarith;
      have h_ind_step : RHS n (m + 1) - RHS n (m + 3) ≥ 4 * n.choose (m + 1) := by
        convert RHS_gap_m_plus_1_strong hm hn using 1;
      have h_ind_step : Y_sol n ((m + 1) / 2) ≤ 4 * n.choose (m + 1) := by
        have h_ind_step : Y_sol n ((m + 1) / 2) ≤ 2 * ((m + 1) / 2) * n.choose ((m + 1) / 2) := by
          have h_ind_step : Y_sol n ((m + 1) / 2) ≤ 2 * ((m + 1) / 2) * n.choose ((m + 1) / 2) := by
            have := Y_sol_upper_bound n ((m + 1) / 2)
            exact this.trans ( mul_le_mul_of_nonneg_right ( by rw [ mul_div ] ; rw [ le_div_iff₀ ] <;> norm_cast ; omega ) <| Nat.cast_nonneg _ );
          convert h_ind_step using 1;
        have h_ind_step : (m + 1) * n.choose ((m + 1) / 2) ≤ 4 * n.choose (m + 1) := by
          have h_ind_step : 4 * n.choose (m + 1) ≥ (m + 1) * n.choose ((m + 1) / 2) := by
            have := binom_ineq_odd_case hm hn
            exact this
          generalize_proofs at *; (
          exact h_ind_step);
        exact le_trans ‹_› ( by rw [ mul_div_cancel₀ _ ( by positivity ) ] ; exact_mod_cast by linarith );
      grind

/-
LHS(j) >= RHS(j) for all even j >= m+2.
-/
lemma LHS_ge_RHS_all_even {n m : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) :
    ∀ j, m + 2 ≤ j → j ≤ n → j % 2 = 0 → LHS n m j ≥ RHS n j := by
      intro j hj₁ hj₂ hj;
      by_cases h_even : m % 2 = 0;
      · induction' j using Nat.strong_induction_on with j ih;
        by_cases hj_cases : j = m + 2 ∨ j = m + 4;
        · rcases hj_cases with ( rfl | rfl );
          · exact LHS_ge_RHS_base_even ( by linarith ) ( by linarith )
          · apply LHS_ge_RHS_step_general_no_parity;
            · grind;
            · exact hn;
            · linarith;
            · linarith;
            · exact LHS_ge_RHS_base_even ( by linarith ) ( by linarith );
        · -- Since $j$ is even and greater than $m+4$, we can write $j = k + 2$ for some $k$ such that $m+2 \leq k < j$.
          obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := by
            exact ⟨ j - 2, by rw [ Nat.sub_add_cancel ( by linarith ) ] ⟩;
          exact LHS_ge_RHS_step_general hm hn ( by omega ) ( by omega ) ( by omega ) ( ih k ( by omega ) ( by omega ) ( by omega ) ( by omega ) );
      · -- Since $m$ is odd, we can write $j = m + 1 + 2k$ for some $k \geq 1$.
        obtain ⟨k, rfl⟩ : ∃ k, j = m + 1 + 2 * k := by
          exact ⟨ ( j - ( m + 1 ) ) / 2, by omega ⟩;
        induction' k with k ih;
        · linarith;
        · rcases k with ( _ | k ) <;> simp_all +arith +decide [ Nat.add_mod ];
          · exact LHS_ge_RHS_base_m_plus_3 hm ( by linarith );
          · have := LHS_ge_RHS_step_general_no_parity ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ( ih ( by linarith ) ) ; aesop;

/-
LHS(j+1) >= RHS(j) for odd j > 1.3m.
-/
lemma LHS_ge_RHS_odd_large_j {n m j : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) (hj : j > 13 * m / 10) (hjn : j ≤ n) (hj_odd : j % 2 = 1) :
    LHS n m (j + 1) ≥ RHS n j := by
      -- By definition of $LHS$ and $RHS$, we know that $LHS(j+1) \ge Y_m$ and $Y_m \ge RHS(j)$.
      have hLHS_ge_Ym : LHS n m (j + 1) ≥ Y_sol n m := by
        apply_rules [ LHS_ge_Y_m_lemma ];
        · omega
      have hYm_ge_RHS : Y_sol n m ≥ RHS n j := by
        apply_rules [ dual_ineq_large_j_part2 ];
      exact hYm_ge_RHS.trans hLHS_ge_Ym

/-
The gap between RHS(j-1) and RHS(j) is at least 4 * binom(n, j-1) for j >= m+3.
-/
lemma RHS_gap_odd_j_part1 {n m j : ℕ} (hn : n = 2 * m) (hj : j ≥ m + 3) (hjn : j ≤ n) :
    RHS n (j - 1) - RHS n j ≥ 4 * n.choose (j - 1) := by
      rcases j with ( _ | _ | j ) <;> simp_all +decide [ RHS ];
      have := Nat.succ_mul_choose_eq ( 2 * m ) ( j + 1 );
      rw [ Nat.choose_succ_succ ] at this;
      norm_cast;
      rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith only [ this, hj, hjn ]

/-
LHS(j) is at least RHS(j) for all j >= m+2.
-/
lemma LHS_ge_RHS_all {n m : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) :
    ∀ j, m + 2 ≤ j → j ≤ n → LHS n m j ≥ RHS n j := by
      -- For odd $j > 1.3m$, we have $LHS(j+1) \geq RHS(j)$ by the lemma `LHS_ge_RHS_odd_large_j`.
      have h_odd_large : ∀ j, 13 * m / 10 < j → j ≤ n → j % 2 = 1 → LHS n m (j + 1) ≥ RHS n j := by
        intros j hj1 hj2 hj3
        apply LHS_ge_RHS_odd_large_j hm hn hj1 hj2 hj3;
      -- For odd $j \in [m+2, 1.3m]$, we can use the lemma `LHS_ge_RHS_step_small_j_no_parity` to show $LHS(j) \geq RHS(j)$.
      have h_odd_small : ∀ j, m + 2 ≤ j → j ≤ 13 * m / 10 → LHS n m j ≥ RHS n j := by
        intros j hj1 hj2
        induction' j using Nat.strong_induction_on with j ih;
        rcases hj1 with ( _ | _ | j ) <;> simp_all +arith +decide;
        · exact LHS_ge_RHS_base_final ( by linarith ) ( by linarith );
        · convert LHS_ge_RHS_base_m_plus_3 _ _ using 1;
          · grind;
          · rfl;
        · exact LHS_ge_RHS_step_small_j_no_parity ( by linarith ) ( by linarith ) ( by linarith ) ( by linarith ) ( ih _ ( by linarith ) ( by linarith ) ( by linarith ) );
      -- By combining the results for even and odd j, we can conclude that LHS n m j ≥ RHS n j for all j in the range m+2 to n.
      intros j hj1 hj2
      by_cases hj_even : j % 2 = 0;
      · exact LHS_ge_RHS_all_even hm hn j hj1 hj2 hj_even;
      · by_cases hj_large : j > 13 * m / 10;
        · specialize h_odd_large j hj_large hj2 ( by simpa using hj_even );
          refine le_trans h_odd_large ?_;
          refine' Finset.sum_le_sum_of_subset_of_nonneg _ _;
          · exact Finset.Icc_subset_Icc ( by omega ) le_rfl;
          · exact fun _ _ _ => Y_sol_nonneg;
        · exact h_odd_small j hj1 ( le_of_not_gt hj_large )

/-
Inequality between binomial coefficients for m >= 200.
-/
lemma binom_ineq_very_loose {n m : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) :
    2 * n.choose (m + 1) ≥ (m + 1) * n.choose ((m + 1) / 2) := by
      -- For $j \in [m+2, 1.3m]$, $\binom{n}{j} \ge m \binom{n}{j/2}$.
      have h_binom_ineq_range : ∀ j, m + 2 ≤ j → j ≤ 13 * m / 10 → (Nat.choose n j : ℝ) ≥ m * Nat.choose n (j / 2) := by
        intros j hj1 hj2
        apply binom_ineq_range hm hn hj1 hj2;
      -- Applying the inequality from `h_binom_ineq_range` with $j = m + 1$.
      specialize h_binom_ineq_range (m + 1 + 1) (by linarith) (by
      omega);
      norm_cast at * ; simp_all +decide [ Nat.add_div ];
      have := Nat.succ_mul_choose_eq ( 2 * m ) ( m + 1 ) ; simp_all +decide [ Nat.choose_succ_succ, mul_comm ];
      split_ifs at * <;> simp_all +decide [ Nat.add_mod ];
      · cases Nat.mod_two_eq_zero_or_one m <;> simp_all +decide;
      · nlinarith [ Nat.zero_le ( Nat.choose ( m * 2 ) ( m / 2 + 1 ) ) ];
      · have := Nat.succ_mul_choose_eq ( m * 2 ) ( m / 2 ) ; simp_all +decide [ Nat.choose_succ_succ, mul_comm ];
        nlinarith [ Nat.div_mul_cancel ( show 2 ∣ m from Nat.dvd_of_mod_eq_zero ‹_› ) ]

/-
The gap at the base case m+1 is large enough to cover Y.
-/
lemma RHS_gap_ge_Y_base {n m : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) :
    RHS n (m + 1) - RHS n (m + 2) ≥ Y_sol n ((m + 1) / 2) := by
      -- By combining the results from the binomial coefficient inequality and the upper bound on $Y_{(m+1)/2}$, we can conclude the proof.
      have h_diff : RHS n (m + 1) - RHS n (m + 2) = 2 * n.choose (m + 1) := by
        convert RHS_diff_eq ( by linarith ) hn using 1;
      have h_Y_upper : Y_sol n ((m + 1) / 2) ≤ 2 * ((m + 1) / 2) * n.choose ((m + 1) / 2) := by
        have h_Y_upper : Y_sol n ((m + 1) / 2) ≤ 2 * ((m + 1) / 2) * n.choose ((m + 1) / 2) := by
          have := Y_sol_upper_bound n ((m + 1) / 2)
          exact this.trans ( mul_le_mul_of_nonneg_right ( by rw [ mul_div ] ; rw [ le_div_iff₀ ] <;> norm_cast ; omega ) ( Nat.cast_nonneg _ ) );
        convert h_Y_upper using 1;
      have h_binom_ineq : 2 * n.choose (m + 1) ≥ (m + 1) * n.choose ((m + 1) / 2) := by
        exact binom_ineq_very_loose hm hn;
      -- By combining the results from the binomial coefficient inequality and the upper bound on $Y_{(m+1)/2}$, we can conclude the proof using the fact that $2 * ((m + 1) / 2) \leq m + 1$.
      have h_combined : Y_sol n ((m + 1) / 2) ≤ (m + 1) * n.choose ((m + 1) / 2) := by
        exact h_Y_upper.trans ( by nlinarith only [ show ( n.choose ( ( m + 1 ) / 2 ) : ℝ ) ≥ 0 by positivity ] );
      exact h_combined.trans ( by rw [ h_diff ] ; exact_mod_cast h_binom_ineq )

/-
The gap in RHS is at least Y for large odd j.
-/
lemma RHS_gap_ge_Y_large_j {n m j : ℕ} (hm : m ≥ 200) (hn : n = 2 * m)
    (hj1 : m + 3 ≤ j) (hj2 : j ≤ 13 * m / 10) (hj_odd : j % 2 = 1) :
    RHS n (j - 1) - RHS n j ≥ Y_sol n ((j - 1) / 2) := by
      -- By combining the inequalities from RHS_gap_odd_j_part1 and Y_le_RHS_diff_small_j, we get the desired result.
      have h_combined : RHS n (j - 1) - RHS n j ≥ 4 * n.choose (j - 1) ∧ 4 * n.choose (j - 1) ≥ Y_sol n ((j - 1) / 2) := by
        apply And.intro;
        · convert RHS_gap_odd_j_part1 hn ( by linarith ) ( by omega ) using 1;
        · have := @Y_le_RHS_diff_small_j n m ( j - 1 ) ?_ ?_ ?_ <;> norm_num at *;
          · exact this ( by omega );
          · linarith;
          · exact hn;
          · omega;
      exact h_combined.2.trans h_combined.1

/-
The gap in RHS is at least Y for odd j in the range.
-/
lemma RHS_gap_ge_Y_odd_j {n m j : ℕ} (hm : m ≥ 200) (hn : n = 2 * m)
    (hj1 : m + 2 ≤ j) (hj2 : j ≤ 13 * m / 10) (hj_odd : j % 2 = 1) :
    RHS n (j - 1) - RHS n j ≥ Y_sol n ((j - 1) / 2) := by
      by_cases h_case : j = m + 2;
      · cases Nat.mod_two_eq_zero_or_one m <;> simp_all +arith +decide
        exact RHS_gap_ge_Y_base hm rfl;
      · exact mod_cast RHS_gap_ge_Y_large_j hm hn ( by omega ) ( by omega ) hj_odd

/-
Decomposition of sum of Y into sum of B and sum of Y_t.
-/
lemma sum_Y_decomposition {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) :
    ∑ k ∈ Finset.Icc 1 m, Y_sol n k = (m : ℝ) * n.choose m + ∑ t ∈ Finset.Icc 1 ((m - 1) / 2), Y_sol n t := by
      -- Let's split the sum into even and odd indices.
      have h_split : ∑ k ∈ Finset.Icc 1 m, Y_sol n k = ∑ k ∈ Finset.filter (fun k => k % 2 = 0) (Finset.Icc 1 m), B_term n k + ∑ k ∈ Finset.filter (fun k => k % 2 = 1) (Finset.Icc 1 m), (B_term n k + Y_sol n ((k - 1) / 2)) := by
        have h_split : ∑ k ∈ Finset.Icc 1 m, Y_sol n k = ∑ k ∈ Finset.filter (fun k => k % 2 = 0) (Finset.Icc 1 m), Y_sol n k + ∑ k ∈ Finset.filter (fun k => k % 2 = 1) (Finset.Icc 1 m), Y_sol n k := by
          rw [ Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext x ; aesop;
        rw [ h_split ];
        refine' congrArg₂ ( · + · ) _ _;
        · refine' Finset.sum_congr rfl fun x hx => _;
          unfold Y_sol; aesop;
        · refine' Finset.sum_congr rfl fun x hx => _;
          rw [ Y_sol ] ; aesop;
      -- Let's simplify the sums over even and odd indices.
      have h_even_odd : ∑ k ∈ Finset.filter (fun k => k % 2 = 0) (Finset.Icc 1 m), B_term n k + ∑ k ∈ Finset.filter (fun k => k % 2 = 1) (Finset.Icc 1 m), B_term n k = m * n.choose m := by
        have h_even_odd : ∑ k ∈ Finset.Icc 1 m, B_term n k = m * n.choose m := by
          convert sum_Bk_telescope hn ( by linarith : 1 ≤ 1 ) ( by linarith ) using 1 ; norm_num;
        rw [ ← h_even_odd, Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; aesop;
      -- Let's simplify the sum over odd indices.
      have h_odd_sum : ∑ k ∈ Finset.filter (fun k => k % 2 = 1) (Finset.Icc 1 m), Y_sol n ((k - 1) / 2) = ∑ t ∈ Finset.Icc 0 ((m - 1) / 2), Y_sol n t := by
        apply Finset.sum_bij (fun k hk => (k - 1) / 2);
        · simp +zetaDelta at *;
          exact fun a ha₁ ha₂ ha₃ => Nat.div_le_div_right ( Nat.sub_le_sub_right ha₂ 1 );
        · grind;
        · simp +zetaDelta at *;
          exact fun b hb => ⟨ 2 * b + 1, ⟨ ⟨ by linarith, by omega ⟩, by norm_num [ Nat.add_mod ] ⟩, by omega ⟩;
        · exact fun a ha ↦ rfl;
      simp_all +decide [ Finset.sum_add_distrib ];
      rw [ ← add_assoc, h_even_odd ];
      erw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] <;> norm_num;
      unfold Y_sol; norm_num;

/-
LHS(m+1) equals RHS(m+1) for odd m.
-/
lemma LHS_eq_RHS_odd_m {n m : ℕ} (hm : m ≥ 200) (hn : n = 2 * m) (ho : m % 2 = 1) :
    LHS n m (m + 1) = RHS n (m + 1) := by
      -- Using the decomposition of the sum of Y_sol, we have:
      have h_sum_Y_sol : ∑ k ∈ Finset.Icc 1 m, Y_sol n k = (m : ℝ) * n.choose m + ∑ t ∈ Finset.Icc 1 ((m - 1) / 2), Y_sol n t := by
        convert sum_Y_decomposition ( by linarith ) hn using 1;
      -- Using the decomposition of the sum of Y_sol, we can rewrite LHS(m+1) as:
      have h_LHS_m_plus_1 : LHS n m (m + 1) = (m : ℝ) * n.choose m := by
        convert congr_arg₂ ( · - · ) h_sum_Y_sol rfl using 1;
        any_goals exact ∑ k ∈ Finset.Icc 1 ( ( m - 1 ) / 2 ), Y_sol n k;
        · rw [ show ( Finset.Icc 1 m : Finset ℕ ) = Finset.Icc 1 ( ( m - 1 ) / 2 ) ∪ Finset.Icc ( ( m - 1 ) / 2 + 1 ) m from ?_, Finset.sum_union ];
          · unfold LHS; simp +decide [ add_comm, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ;
            rw [ show ( m + 1 ) / 2 = 1 + ( m - 1 ) / 2 by omega ];
          · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp hx₁, Finset.mem_Icc.mp hx₂ ] ;
          · exact Eq.symm ( Finset.Ico_union_Ico_eq_Ico ( by omega ) ( by omega ) );
        · ring
      generalize_proofs at *; simp_all +decide [ LHS ] ;
      unfold RHS; norm_num [ Nat.cast_choose, hn ] ; ring_nf;
      rw [ Nat.add_comm 1 m, Nat.cast_choose, Nat.cast_choose ] <;> try linarith [ Nat.mod_add_div m 2 ] ; ; ring_nf;
      rw [ show m * 2 - m = m by rw [ Nat.sub_eq_of_eq_add ] ; ring, show m * 2 - ( 1 + m ) = m - 1 by rw [ Nat.sub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ m ) ] ] ; ring_nf;
      field_simp;
      cases m <;> norm_num [ Nat.factorial ] at * ; ring_nf at *;
      simpa [ Nat.add_comm 1, Nat.factorial_succ ] using by ring;

/-
LHS(j+1) >= RHS(j) for odd j.
-/
lemma LHS_ge_RHS_odd_small_j {n m j : ℕ} (hm : m ≥ 200) (hn : n = 2 * m)
    (hj1 : m + 2 ≤ j) (hj2 : j ≤ 13 * m / 10) (hj_odd : j % 2 = 1) :
    LHS n m (j + 1) ≥ RHS n j := by
      have h_gap : RHS n (j - 1) - RHS n j ≥ Y_sol n ((j - 1) / 2) := by
        apply RHS_gap_ge_Y_odd_j hm hn hj1 hj2 hj_odd;
      -- Apply the lemma that states the gap in RHS is at least Y and use it to conclude the proof. We'll use the induction hypothesis to show that LHS(j-1) ≥ RHS(j-1).
      have h_ind : LHS n m (j + 1) = LHS n m (j - 1) - Y_sol n ((j - 1) / 2) := by
        convert LHS_recurrence hn _ using 1;
        rotate_left;
        rotate_left;
        exact j - 1;
        · omega;
        · rw [ show j - 1 + 2 = j + 1 by omega ];
        · grind +ring;
      have h_ind : LHS n m (j - 1) ≥ RHS n (j - 1) := by
        have h_ind : ∀ j, m + 2 ≤ j → j ≤ 13 * m / 10 → LHS n m j ≥ RHS n j := by
          intros j hj1 hj2
          apply LHS_ge_RHS_all hm hn j hj1 (by
          omega);
        by_cases hj : j - 1 ≥ m + 2;
        · exact h_ind _ hj ( Nat.le_trans ( Nat.sub_le _ _ ) hj2 );
        · norm_num [ show j = m + 2 by omega ] at *;
          convert LHS_eq_RHS_odd_m hm hn hj_odd |> le_of_eq using 1;
          · convert LHS_eq_RHS_odd_m hm hn hj_odd |> Eq.symm using 1;
          · exact LHS_eq_RHS_odd_m hm hn hj_odd ▸ rfl;
      grind

/-
Bound for the sum of Z variables.
-/
lemma sum_Z_final_bound {n m : ℕ} (hm : m ≥ 1) (hn : n = 2 * m) :
    ∑ j ∈ Finset.range (n + 1), Z_final n j ≤ 1 + n.choose (m / 2) := by
      -- The sum of Y variables at m/2 for steps where m is even.
      have h_sum_Y_m_div_2 : ∀ j, j ∈ Finset.range (n + 1) → Z_final n j ≤ if j = m + 1 ∧ m % 2 = 0 then Y_sol n (m / 2) / (m + 1) else if j = 0 then 1 else 0 := by
        intro j hj; unfold Z_final; split_ifs <;> norm_num;
        · omega;
        · rw [ show n / 4 = m / 2 by omega ] ; rw [ show ( n : ℝ ) / 2 = m by norm_num [ hn, mul_div_cancel_left₀ ] ] ;
        · grind +ring;
        · grind;
      refine le_trans ( Finset.sum_le_sum h_sum_Y_m_div_2 ) ?_;
      by_cases he : m % 2 = 0 <;> simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', he ];
      split_ifs <;> norm_num [ hn ];
      rw [ add_comm ];
      refine' add_le_add_left ( div_le_of_le_mul₀ _ _ _ ) _ <;> norm_cast <;> norm_num;
      refine' le_trans ( Y_sol_upper_bound _ _ ) _ ; ring_nf ;
      norm_cast ; nlinarith [ Nat.div_mul_cancel ( Nat.dvd_of_mod_eq_zero he ), Nat.choose_pos ( show m / 2 ≤ m * 2 by linarith [ Nat.div_mul_le_self m 2 ] ) ]

/-
Project a set of Fin (n+1) to a set of Fin n by keeping elements less than n.
-/
def project_set {n : ℕ} (A : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter (λ x => Fin.castSucc x ∈ A)

/-
Decomposition of the family into two subfamilies based on the last element.
-/
def family_zero {n : ℕ} (F : Finset (Finset (Fin (n + 1)))) : Finset (Finset (Fin n)) :=
  (F.filter (λ A => Fin.last n ∉ A)).image project_set

def family_one {n : ℕ} (F : Finset (Finset (Fin (n + 1)))) : Finset (Finset (Fin n)) :=
  (F.filter (λ A => Fin.last n ∈ A)).image project_set

/-
Injectivity of projection for sets not containing the last element.
-/
lemma project_set_inj_on_zero {n : ℕ} (A B : Finset (Fin (n + 1)))
    (hA : Fin.last n ∉ A) (hB : Fin.last n ∉ B) (h : project_set A = project_set B) : A = B := by
      ext x; by_cases hx : x.val < n <;> simp_all +decide [ Finset.ext_iff, project_set ] ;
      · convert h ⟨ x, hx ⟩ using 1;
      · cases x using Fin.lastCases <;> aesop

/-
Injectivity of projection for sets containing the last element.
-/
lemma project_set_inj_on_one {n : ℕ} (A B : Finset (Fin (n + 1)))
    (hA : Fin.last n ∈ A) (hB : Fin.last n ∈ B) (h : project_set A = project_set B) : A = B := by
      ext x; by_cases hx : x = Fin.last n <;> simp_all +decide [ Finset.ext_iff ] ;
      convert h ⟨ x, lt_of_le_of_ne ( Fin.le_last _ ) ( by simpa [ Fin.ext_iff ] using hx ) ⟩ using 1 <;> simp +decide [ *, project_set ]

/-
The projection of the subfamily not containing the last element is union-free.
-/
lemma family_zero_union_free {n : ℕ} (F : Finset (Finset (Fin (n + 1)))) (hF : UnionFree F) :
    UnionFree (family_zero F) := by
      intro A hA B hB C hC hdiff hsub hne;
      -- Let $A', B', C' \in \text{family\_zero } F$ such that $A' \cup B' = C'$.
      obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hC;
      -- Since $A', B', C' \in F$ and $F$ is union-free, we have $A' \cup B' \neq C'$.
      have h_union : A' ∪ B' ≠ C' := by
        have h_union : A' ≠ B' ∧ A' ≠ C' ∧ B' ≠ C' := by
          exact ⟨ fun h => hdiff <| h ▸ rfl, fun h => hne <| h ▸ rfl, fun h => hsub <| h ▸ rfl ⟩;
        exact fun h => hF A' ( Finset.mem_filter.mp hA' |>.1 ) B' ( Finset.mem_filter.mp hB' |>.1 ) C' ( Finset.mem_filter.mp hC' |>.1 ) ( by aesop ) ( by aesop ) ( by aesop ) h;
      contrapose! h_union; simp_all +decide [ Finset.ext_iff, project_set ] ;
      intro a; induction a using Fin.lastCases <;> simp_all +decide

/-
The projection of the subfamily containing the last element is union-free.
-/
lemma family_one_union_free {n : ℕ} (F : Finset (Finset (Fin (n + 1)))) (hF : UnionFree F) :
    UnionFree (family_one F) := by
      intro A hA B hB C hC hdiff hsub hne;
      -- By definition of $family_one$, there exist $A', B', C' \in F$ such that $A = project_set A'$, $B = project_set B'$, and $C = project_set C'$, and $Fin.last n \in A'$, $Fin.last n \in B'$, $Fin.last n \in C'$.
      obtain ⟨A', hA', hA_last⟩ : ∃ A' ∈ F, Fin.last n ∈ A' ∧ A = project_set A' := by
        unfold family_one at hA; aesop;
      obtain ⟨B', hB', hB_last⟩ : ∃ B' ∈ F, Fin.last n ∈ B' ∧ B = project_set B' := by
        unfold family_one at hB; aesop;
      obtain ⟨C', hC', hC_last⟩ : ∃ C' ∈ F, Fin.last n ∈ C' ∧ C = project_set C' := by
        unfold family_one at hC; aesop;
      -- Since $A' \cup B' = C'$, we have $A \cup B = C$.
      have h_union_eq : A' ∪ B' = C' → A ∪ B = C := by
        simp_all +decide [ Finset.ext_iff, project_set ];
      contrapose! h_union_eq; have := hF A' hA' B' hB' C' hC'; simp_all +decide ;
      exact this ( by aesop_cat ) ( by aesop_cat ) ( by aesop_cat ) ( by
        ext x; by_cases hx : x = Fin.last n <;> simp_all +decide [ Finset.ext_iff, project_set ] ;
        convert h_union_eq ⟨ x.val, lt_of_le_of_ne ( Nat.le_of_lt_succ x.2 ) ( by simpa [ Fin.ext_iff ] using hx ) ⟩ using 1 )

/-
Cardinality of the projected family zero equals the cardinality of the filtered subfamily.
-/
lemma card_family_zero {n : ℕ} (F : Finset (Finset (Fin (n + 1)))) :
    (family_zero F).card = (F.filter (λ A => Fin.last n ∉ A)).card := by
      rw [ show family_zero F = Finset.image project_set ( F.filter fun A => Fin.last n∉A ) from rfl, Finset.card_image_of_injOn ];
      exact fun x hx y hy hxy => project_set_inj_on_zero _ _ ( by aesop ) ( by aesop ) hxy

/-
Cardinality of the projected family one equals the cardinality of the filtered subfamily.
-/
lemma card_family_one {n : ℕ} (F : Finset (Finset (Fin (n + 1)))) :
    (family_one F).card = (F.filter (λ A => Fin.last n ∈ A)).card := by
      convert Finset.card_image_of_injOn _;
      intros A hA B hB h; have := project_set_inj_on_one A B; aesop;

/-
Recursive bound for the size of union-free families for odd n.
-/
lemma max_union_free_odd_bound (m : ℕ) : MaxUnionFree (2 * m + 1) ≤ 2 * MaxUnionFree (2 * m) := by
  refine' Finset.sup_le fun F hF => _;
  -- By definition of $F$, we can split it into two subfamilies based on the presence of the last element.
  have h_split : F.card = (F.filter (fun A => Fin.last (2 * m) ∉ A)).card + (F.filter (fun A => Fin.last (2 * m) ∈ A)).card := by
    rw [ Finset.card_filter, Finset.card_filter ];
    simpa only [ ← Finset.sum_add_distrib ] using Finset.card_eq_sum_ones F ▸ by congr; ext; aesop;
  -- By definition of $F$, we know that both subfamilies are union-free.
  have h_union_free : UnionFree (family_zero F) ∧ UnionFree (family_one F) := by
    exact ⟨ family_zero_union_free F ( Finset.mem_filter.mp hF |>.2 ), family_one_union_free F ( Finset.mem_filter.mp hF |>.2 ) ⟩;
  -- By definition of $MaxUnionFree$, we know that the cardinality of any union-free family in $[2m]$ is at most $MaxUnionFree (2 * m)$.
  have h_max_union_free : ∀ F : Finset (Finset (Fin (2 * m))), UnionFree F → F.card ≤ MaxUnionFree (2 * m) := by
    exact fun F hF => Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hF ⟩ );
  linarith [ h_max_union_free ( family_zero F ) h_union_free.1, h_max_union_free ( family_one F ) h_union_free.2, card_family_zero F, card_family_one F ]

/-
Dual feasibility inequality for j <= m.
-/
lemma dual_feasible_le_m {m : ℕ} :
    let n := 2 * m
    ∀ j, 1 ≤ j → j ≤ m →
      (∑ k ∈ Finset.Icc ((j + 1) / 2) j, Y_sol n k) ≥ (j : ℝ) * n.choose j := by
        have := @block_sum_identities;
        field_simp;
        intro j hj₁ hj₂; specialize @this ( 2 * m ) ( j / 2 ) ; rcases Nat.even_or_odd' j with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
        · grind;
        · rcases k with ( _ | k ) <;> norm_num [ Nat.add_div ] at *;
          · unfold Y_sol; norm_num [ Nat.choose_two_right ] ; ring_nf; norm_cast;
            unfold B_term Y_sol; norm_num [ Nat.choose_two_right ] ; ring_nf; norm_cast;
            aesop;
          · erw [ Finset.sum_Ico_eq_sub _ _ ] at * <;> norm_num at *;
            · have := this ( by linarith ) |>.2 ( by linarith ) ; erw [ Finset.sum_Ico_eq_sub _ _ ] at this <;> norm_num [ Finset.sum_range_succ ] at * ; linarith;
              linarith;
            · linarith;
            · linarith

/-
The main inequality of dual feasibility holds for all j.
-/
lemma dual_main_ineq {m : ℕ} (hm : m ≥ 200) :
    let n := 2 * m
    ∀ j, 0 ≤ j → j ≤ n →
      (∑ k ∈ Finset.Icc ((j + 1) / 2) (min j m), Y_sol n k / (j * n.choose j)) + Z_final n j / n.choose j ≥ 1 := by
        field_simp;
        intro j hj₁ hj₂;
        by_cases hj : j = 0;
        · unfold Z_final; aesop;
        · by_cases hj3 : j ≤ m;
          · have := dual_feasible_le_m j ( Nat.pos_of_ne_zero hj ) hj3;
            rw [ ← Finset.sum_div _ _ _, min_eq_left hj3 ];
            exact le_add_of_le_of_nonneg ( by rw [ one_le_div ( mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hj ) ) ( Nat.cast_pos.mpr ( Nat.choose_pos ( by linarith ) ) ) ) ] ; linarith ) ( div_nonneg ( by unfold Z_final; aesop ) ( Nat.cast_nonneg _ ) );
          · by_cases hj4 : j = m + 1;
            · have := dual_constraint_m_plus_1 ( by linarith : m ≥ 1 ) ; aesop;
            · by_cases hj5 : j % 2 = 1;
              · by_cases hj6 : j ≤ 13 * m / 10;
                · have := LHS_ge_RHS_odd_small_j hm rfl ( by omega ) ( by omega ) hj5;
                  unfold LHS RHS Z_final at *;
                  rw [ ← Finset.sum_div _ _ _ ];
                  rw [ min_eq_right ( by omega ) ];
                  rw [ if_neg hj, if_neg ( by omega ) ] ; norm_num;
                  rwa [ one_le_div ( mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hj ) ) ( Nat.cast_pos.mpr ( Nat.choose_pos ( by linarith ) ) ) ) ];
                · have := LHS_ge_RHS_odd_large_j hm rfl ( show j > 13 * m / 10 from lt_of_not_ge hj6 ) hj₂ hj5; simp_all +decide [ LHS ] ;
                  unfold RHS at this; simp_all +decide [ ← Finset.sum_div _ _ _ ] ;
                  rw [ div_add_div, le_div_iff₀ ] <;> norm_cast at * <;> simp_all +decide
                  · rw [ min_eq_right ( by linarith ) ];
                    exact le_add_of_le_of_nonneg ( mul_le_mul_of_nonneg_right this ( Nat.cast_nonneg _ ) ) ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( by unfold Z_final; aesop ) );
                  · exact ⟨ Nat.pos_of_ne_zero hj, Nat.choose_pos ( by linarith ) ⟩;
                  · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
                  · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith;
              · have := LHS_ge_RHS_all ( show m ≥ 200 by linarith ) ( show 2 * m = 2 * m by linarith ) j ( by omega ) ( by omega ) ; simp_all +decide [ LHS, RHS, Z_final ] ;
                rw [ ← Finset.sum_div _ _ _, le_div_iff₀ ] <;> norm_cast at * <;> simp_all +decide [ Nat.add_div ];
                · rw [ min_eq_right ( by linarith ) ] ; exact this;
                · exact ⟨ Nat.pos_of_ne_zero hj, Nat.choose_pos ( by linarith ) ⟩

/-
The constructed solution (Y, Z) is dual feasible for m >= 200.
-/
lemma dual_feasible_sol {m : ℕ} (hm : m ≥ 200) :
    let n := 2 * m
    is_dual_feasible n (Y_sol n) (Z_final n) := by
      constructor;
      · exact fun k ↦ Y_sol_nonneg;
      · refine' ⟨ fun j => _, fun k hk => _, fun j hj => _, fun j hj₁ hj₂ => _ ⟩;
        · apply_rules [ Z_final_nonneg ];
        · cases hk <;> unfold Y_sol <;> aesop;
        · unfold Z_final;
          grind;
        · convert dual_main_ineq hm j hj₁ hj₂ using 1;
          grind

/-
Upper bound for MaxUnionFree for even n.
-/
lemma kleitman_upper_bound_even :
    ∃ C, ∀ m, m ≥ 200 →
      (MaxUnionFree (2 * m) : ℝ) ≤ (2 * m).choose m + 2 ^ (2 * m) / (2 * m + 1) + C * (2 * m).choose (m / 2) := by
        have h_upper_bound : ∀ m ≥ 200, (MaxUnionFree (2 * m)) ≤ (Nat.choose (2 * m) m : ℝ) + (2 ^ (2 * m)) / (2 * m + 1 : ℝ) + 3 * (Nat.choose (2 * m) (m / 2) : ℝ) + 1 := by
          intro m hm;
          -- By combining the results from LP_upper_bound, weak_duality, dual_feasible_sol, and objective_eval, we can conclude the proof.
          have h_combined : (MaxUnionFree (2 * m) : ℝ) ≤ (dual_obj (2 * m) (Y_sol (2 * m)) (Z_final (2 * m))) := by
            have h_max_le_opt : (MaxUnionFree (2 * m) : ℝ) ≤ (OPT (2 * m)) := by
              have := @LP_upper_bound ( 2 * m );
              convert this _ _;
              convert rfl;
              rotate_left;
              exact Classical.choose ( Finset.exists_max_image ( Finset.filter UnionFree ( Finset.univ : Finset ( Finset ( Finset ( Fin ( 2 * m ) ) ) ) ) ) ( fun F => F.card ) ( Finset.filter_nonempty_iff.mpr ⟨ ∅, by simp +decide [ UnionFree ] ⟩ ) );
              · have := Classical.choose_spec ( Finset.exists_max_image ( Finset.filter UnionFree ( Finset.univ : Finset ( Finset ( Finset ( Fin ( 2 * m ) ) ) ) ) ) ( fun F => F.card ) ( Finset.filter_nonempty_iff.mpr ⟨ ∅, by simp +decide [ UnionFree ] ⟩ ) ) ; aesop;
              · exact Classical.choose_spec ( Finset.exists_max_image ( Finset.filter UnionFree ( Finset.univ : Finset ( Finset ( Finset ( Fin ( 2 * m ) ) ) ) ) ) ( fun F => F.card ) ( Finset.filter_nonempty_iff.mpr ⟨ ∅, by simp +decide [ UnionFree ] ⟩ ) ) |>.2 |> fun h => le_antisymm ( Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Classical.choose_spec ( Finset.exists_max_image ( Finset.filter UnionFree ( Finset.univ : Finset ( Finset ( Finset ( Fin ( 2 * m ) ) ) ) ) ) ( fun F => F.card ) ( Finset.filter_nonempty_iff.mpr ⟨ ∅, by simp +decide [ UnionFree ] ⟩ ) ) |>.1 |> Finset.mem_filter.mp |>.2 ⟩ ) ) ( Finset.sup_le fun F hF => Finset.mem_filter.mp hF |>.2 |> fun h => Classical.choose_spec ( Finset.exists_max_image ( Finset.filter UnionFree ( Finset.univ : Finset ( Finset ( Finset ( Fin ( 2 * m ) ) ) ) ) ) ( fun F => F.card ) ( Finset.filter_nonempty_iff.mpr ⟨ ∅, by simp +decide [ UnionFree ] ⟩ ) ) |>.2 F ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h ⟩ ) );
            refine le_trans h_max_le_opt ?_;
            apply_rules [ weak_duality ];
            apply dual_feasible_sol; assumption;
          convert h_combined.trans _ using 1;
          have := objective_eval ( by linarith : 1 ≤ m ) rfl;
          have := sum_Z_final_bound ( by linarith : 1 ≤ m ) rfl;
          unfold dual_obj;
          norm_num [ Nat.mul_div_cancel_left ] at *;
          nlinarith [ show ( 0 : ℝ ) ≤ 2 ^ ( 2 * m ) by positivity, show ( 0 : ℝ ) ≤ ( 2 * m + 1 ) * ( Nat.choose ( 2 * m ) ( m / 2 ) : ℝ ) by positivity, div_mul_cancel₀ ( 2 ^ ( 2 * m ) : ℝ ) ( by positivity : ( 2 * m + 1 : ℝ ) ≠ 0 ) ];
        have h_error_term : ∀ m ≥ 200, 1 ≤ (Nat.choose (2 * m) (m / 2) : ℝ) := by
          exact fun m hm => mod_cast Nat.choose_pos ( by omega );
        exact ⟨ 4, fun m hm => by nlinarith [ h_upper_bound m hm, h_error_term m hm ] ⟩

/-
Asymptotic behavior of MaxUnionFree.
-/
theorem erdos_447 :
    (fun n => (MaxUnionFree n : ℝ)) ~[atTop] (fun n => (n.choose (n / 2) : ℝ)) := by
      have h_upper_bound : ∃ C : ℝ, ∀ m, m ≥ 200 → (MaxUnionFree (2 * m) : ℝ) ≤ (2 * m).choose m + 2 ^ (2 * m) / (2 * m + 1) + C * (2 * m).choose (m / 2) := by
        convert kleitman_upper_bound_even using 1;
      -- By combining the upper and lower bounds, we can apply the squeeze theorem.
      have h_squeeze : Filter.Tendsto (fun m => (MaxUnionFree (2 * m) : ℝ) / (2 * m).choose m) Filter.atTop (nhds 1) := by
        have h_even_bound : Filter.Tendsto (fun m : ℕ => (2 * m).choose m / (2 * m).choose m + 2 ^ (2 * m) / (2 * m + 1) / (2 * m).choose m + h_upper_bound.choose * (2 * m).choose (m / 2) / (2 * m).choose m) Filter.atTop (nhds 1) := by
          have h_even_bound : Filter.Tendsto (fun m : ℕ => (2 ^ (2 * m) / (2 * m + 1) : ℝ) / (2 * m).choose m) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun m : ℕ => (2 * m).choose (m / 2) / (2 * m).choose m : ℕ → ℝ) Filter.atTop (nhds 0) := by
            constructor;
            · have := pow_two_div_n_little_o_binom_half;
              rw [ Asymptotics.isLittleO_iff_tendsto' ] at this;
              · convert this.comp ( Filter.tendsto_id.nsmul_atTop two_pos ) using 2 ; norm_num;
              · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn h using absurd h <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| Nat.div_le_self _ _;
            · have := binom_quarter_little_o_binom_half;
              rw [ Asymptotics.isLittleO_iff_tendsto' ] at this;
              · convert this.comp ( Filter.tendsto_id.nsmul_atTop two_pos ) using 2 ; norm_num [ Nat.mul_div_assoc ];
                norm_num [ show 2 * ‹ℕ› / 4 = ‹ℕ› / 2 by omega ];
              · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn h using absurd h <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| Nat.div_le_self _ _;
          simpa [ mul_div_assoc ] using Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm; rw [ div_self <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| by linarith ] ) ) h_even_bound.1 ) ( h_even_bound.2.const_mul _ );
        have h_even_bound : ∀ᶠ m in Filter.atTop, (MaxUnionFree (2 * m) : ℝ) / (2 * m).choose m ≤ (2 * m).choose m / (2 * m).choose m + 2 ^ (2 * m) / (2 * m + 1) / (2 * m).choose m + h_upper_bound.choose * (2 * m).choose (m / 2) / (2 * m).choose m := by
          filter_upwards [ Filter.eventually_ge_atTop 200 ] with m hm using by rw [ ← add_div, ← add_div, div_le_div_iff_of_pos_right ( Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith ) ] ; exact h_upper_bound.choose_spec m hm;
        refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ‹_› _ _;
        · filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm;
          rw [ one_le_div ( Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith ) ];
          convert max_union_free_ge_binom ( 2 * m ) using 1;
          norm_num [ Nat.mul_div_cancel_left ];
        · exact h_even_bound;
      have h_odd_bound : Filter.Tendsto (fun m => (MaxUnionFree (2 * m + 1) : ℝ) / (2 * m + 1).choose m) Filter.atTop (nhds 1) := by
        have h_odd_bound : Filter.Tendsto (fun m => (2 * MaxUnionFree (2 * m) : ℝ) / (2 * m + 1).choose m) Filter.atTop (nhds 1) := by
          have h_odd_bound : Filter.Tendsto (fun m => (2 * (MaxUnionFree (2 * m) : ℝ) / (2 * m).choose m) * ((2 * m).choose m / (2 * m + 1).choose m)) Filter.atTop (nhds 1) := by
            have h_odd_bound : Filter.Tendsto (fun m => ((2 * m).choose m : ℝ) / ((2 * m + 1).choose m)) Filter.atTop (nhds (1 / 2)) := by
              -- We can simplify the expression inside the limit.
              suffices h_simplify : Filter.Tendsto (fun m => (2 * m + 1 - m : ℝ) / (2 * m + 1)) Filter.atTop (nhds (1 / 2)) by
                refine h_simplify.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.congr' ?_;
                filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm;
                rw [ Function.comp_apply, Nat.cast_choose, Nat.cast_choose ] <;> try linarith;
                field_simp;
                norm_num [ two_mul, Nat.factorial ] ; ring_nf;
                rw [ show 1 + m * 2 - m = m + 1 by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; push_cast [ Nat.factorial_succ ] ; ring;
              rw [ Metric.tendsto_nhds ] ; norm_num;
              exact fun ε hε => ⟨ ⌈ε⁻¹⌉₊ + 1, fun x hx => abs_lt.mpr ⟨ by nlinarith [ Nat.le_ceil ( ε⁻¹ ), mul_inv_cancel₀ ( ne_of_gt hε ), div_mul_cancel₀ ( 2 * x + 1 - x ) ( by linarith : ( 2 * x + 1 ) ≠ 0 ) ], by nlinarith [ Nat.le_ceil ( ε⁻¹ ), mul_inv_cancel₀ ( ne_of_gt hε ), div_mul_cancel₀ ( 2 * x + 1 - x ) ( by linarith : ( 2 * x + 1 ) ≠ 0 ) ] ⟩ ⟩;
            convert h_squeeze.const_mul 2 |> Filter.Tendsto.mul <| h_odd_bound using 2 <;> ring;
          refine h_odd_bound.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with m hm using by rw [ div_mul_div_cancel₀ ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| by linarith ) ] );
        have h_odd_bound : ∀ m, m ≥ 200 → (MaxUnionFree (2 * m + 1) : ℝ) ≤ 2 * MaxUnionFree (2 * m) := by
          exact fun m hm => mod_cast max_union_free_odd_bound m |> le_trans <| by norm_num;
        have h_odd_bound : Filter.Tendsto (fun m => (MaxUnionFree (2 * m + 1) : ℝ) / (2 * m + 1).choose m) Filter.atTop (nhds 1) := by
          have h_lower_bound : ∀ m, m ≥ 200 → (MaxUnionFree (2 * m + 1) : ℝ) ≥ (2 * m + 1).choose m := by
            intros m hm
            have h_lower_bound : (MaxUnionFree (2 * m + 1) : ℝ) ≥ (2 * m + 1).choose m := by
              have h_lower_bound : (Nat.choose (2 * m + 1) m : ℝ) ≤ MaxUnionFree (2 * m + 1) := by
                convert max_union_free_ge_binom ( 2 * m + 1 ) using 1;
                norm_num [ Nat.add_div ]
              exact_mod_cast h_lower_bound;
            convert h_lower_bound using 1
          have h_squeeze : ∀ m, m ≥ 200 → (MaxUnionFree (2 * m + 1) : ℝ) / (2 * m + 1).choose m ≥ 1 := by
            exact fun m hm => by rw [ ge_iff_le ] ; rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith ) ] ; linarith [ h_lower_bound m hm ] ;
          have h_squeeze : ∀ m, m ≥ 200 → (MaxUnionFree (2 * m + 1) : ℝ) / (2 * m + 1).choose m ≤ (2 * MaxUnionFree (2 * m) : ℝ) / (2 * m + 1).choose m := by
            exact fun m hm => by gcongr ; exact h_odd_bound m hm;
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ‹_› ( Filter.eventually_atTop.mpr ⟨ 200, fun m hm => by aesop ⟩ ) ( Filter.eventually_atTop.mpr ⟨ 200, fun m hm => by aesop ⟩ );
        convert h_odd_bound using 1;
      have h_even_bound : Filter.Tendsto (fun n => (MaxUnionFree n : ℝ) / (n.choose (n / 2))) Filter.atTop (nhds 1) := by
        rw [ Filter.tendsto_atTop' ] at *;
        intro s hs; obtain ⟨ a₁, ha₁ ⟩ := h_squeeze s hs; obtain ⟨ a₂, ha₂ ⟩ := h_odd_bound s hs; use 2 * a₁ + 2 * a₂; intro b hb; rcases Nat.even_or_odd' b with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ Nat.add_div ] ;
        · exact ha₁ c ( by linarith );
        · exact ha₂ c ( by linarith );
      rw [ Asymptotics.isEquivalent_iff_exists_eq_mul ];
      exact ⟨ _, h_even_bound, by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Pi.mul_apply, div_mul_cancel₀ _ ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| Nat.div_le_self _ _ ) ] ⟩

end Erdos447

namespace Erdos487

open scoped Nat
open scoped Classical
open Asymptotics Filter
open Erdos447

/-
Definition of lower asymptotic density of a set A of natural numbers.
-/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N => ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ)) Filter.atTop

/-
Definitions of arithmetic functions: Omega(n) (total number of prime factors), tau(n) (number of divisors), and v2(n) (exponent of 2).
-/
def Om (n : ℕ) : ℕ := (Nat.factorization n).sum (fun _ k => k)

def tauu (n : ℕ) : ℕ := (Nat.divisors n).card

def v2 (n : ℕ) : ℕ := padicValNat 2 n

/-
Helper definitions for the reduction to odd integers: A_t is the subset of A with v_2(a) = t, and B_t is A_t scaled down by 2^t.
-/
def At (A : Set ℕ) (t : ℕ) : Set ℕ := {a ∈ A | v2 a = t}

def Bt (A : Set ℕ) (t : ℕ) : Set ℕ := (At A t).image (fun n => n / 2^t)

/-
If B_t(A) contains an lcm-triple, then A contains an lcm-triple.
-/
lemma lcm_triple_preservation (A : Set ℕ) (t : ℕ)
  (b1 b2 b3 : ℕ) (h1 : b1 ∈ Bt A t) (h2 : b2 ∈ Bt A t) (h3 : b3 ∈ Bt A t)
  (h_distinct : b1 ≠ b2 ∧ b2 ≠ b3 ∧ b1 ≠ b3)
  (h_lcm : Nat.lcm b1 b2 = b3) :
  ∃ a1 ∈ A, ∃ a2 ∈ A, ∃ a3 ∈ A, a1 ≠ a2 ∧ a2 ≠ a3 ∧ a1 ≠ a3 ∧ Nat.lcm a1 a2 = a3 := by
    obtain ⟨ x, hx, rfl ⟩ := h1;
    obtain ⟨ y, hy, rfl ⟩ := h2
    obtain ⟨ z, hz, rfl ⟩ := h3;
    refine' ⟨ x, hx.1, y, hy.1, z, hz.1, _, _, _, _ ⟩ <;> simp_all +decide
    · grind;
    · grind;
    · unfold At at * ; aesop;
    · have h_lcm_eq : x = 2^t * (x / 2^t) ∧ y = 2^t * (y / 2^t) ∧ z = 2^t * (z / 2^t) := by
        have h_lcm_eq : 2^t ∣ x ∧ 2^t ∣ y ∧ 2^t ∣ z := by
          exact ⟨ Nat.dvd_trans ( pow_dvd_pow _ <| show t ≤ padicValNat 2 x from hx.2.ge ) <| Nat.ordProj_dvd _ _, Nat.dvd_trans ( pow_dvd_pow _ <| show t ≤ padicValNat 2 y from hy.2.ge ) <| Nat.ordProj_dvd _ _, Nat.dvd_trans ( pow_dvd_pow _ <| show t ≤ padicValNat 2 z from hz.2.ge ) <| Nat.ordProj_dvd _ _ ⟩;
        exact ⟨ Eq.symm ( Nat.mul_div_cancel' h_lcm_eq.1 ), Eq.symm ( Nat.mul_div_cancel' h_lcm_eq.2.1 ), Eq.symm ( Nat.mul_div_cancel' h_lcm_eq.2.2 ) ⟩;
      rw [ h_lcm_eq.1, h_lcm_eq.2.1, h_lcm_eq.2.2, Nat.lcm_mul_left ] ; norm_num [ h_lcm ]

/-
Every element in B_t is odd (assuming A contains no zeros).
-/
lemma Bt_odd (A : Set ℕ) (t : ℕ) (hA : ∀ a ∈ A, a ≠ 0) : ∀ b ∈ Bt A t, Odd b := by
  intro b hb; obtain ⟨ a, ha, rfl ⟩ := hb; simp +decide
  -- By definition of $At$, we know that $v2 a = t$, which means $a$ is divisible by $2^t$ but not by $2^{t+1}$.
  have h_div : 2 ^ t ∣ a ∧ ¬2 ^ (t + 1) ∣ a := by
    have h_div : padicValNat 2 a = t := by
      exact ha.2;
    exact ⟨ h_div ▸ Nat.ordProj_dvd _ _, h_div ▸ Nat.pow_succ_factorization_not_dvd ( hA a ha.1 ) ( by decide ) ⟩;
  exact Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => h_div.2 <| by convert Nat.mul_dvd_mul_left ( 2 ^ t ) ( Nat.dvd_of_mod_eq_zero h ) using 1; rw [ Nat.mul_div_cancel' h_div.1 ] )

/-
The sum of reciprocals of elements in A intersected with (2^(k-1), 2^k] is at least the cardinality divided by 2^k.
-/
lemma sum_recip_dyadic_bound (A : Set ℕ) (k : ℕ) :
  ∑ a ∈ (Finset.Ioc (2^(k-1)) (2^k)).filter (· ∈ A), (1 : ℝ) / a ≥ ((Finset.Ioc (2^(k-1)) (2^k)).filter (· ∈ A)).card / (2^k : ℝ) := by
    have h_le : ∀ a ∈ Finset.filter (fun x => x ∈ A) (Finset.Ioc (2 ^ (k - 1)) (2 ^ k)), (1 / a : ℝ) ≥ (1 / 2 ^ k : ℝ) := by
      field_simp;
      exact fun x hx => by rw [ one_le_div ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero fun h => by aesop ) ] ; exact_mod_cast Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2;
    simpa [ div_eq_mul_inv ] using Finset.sum_le_sum h_le |> le_trans ( by norm_num )

/-
Definition of b_k as the number of elements of A in {1, ..., 2^k}.
-/
noncomputable def bk (A : Set ℕ) (k : ℕ) : ℕ := ((Finset.Icc 1 (2^k)).filter (· ∈ A)).card

/-
Algebraic lemma: lower bound for the sum involving b_k.
-/
lemma sum_density_lower_bound (b : ℕ → ℕ) (δ' : ℝ) (k1 K : ℕ) (hk1 : k1 + 1 < K)
  (h_density : ∀ k, k1 ≤ k → k < K → (b k : ℝ) ≥ δ' * 2^k) :
  ∑ k ∈ Finset.Icc (k1 + 1) K, ((b k : ℝ) - b (k - 1)) / 2^k ≥ (δ' / 2) * (K - k1 - 2) - (b k1 : ℝ) / 2^(k1+1) := by
    -- Applying the summation by parts formula.
    have h_sum_parts : ∀ N : ℕ, k1 + 1 ≤ N → N < K → ∑ k ∈ Finset.Icc (k1 + 1) N, (b k - b (k - 1) : ℝ) / 2 ^ k = b N / 2 ^ N - b k1 / 2 ^ (k1 + 1) + ∑ k ∈ Finset.Icc (k1 + 1) (N - 1), (b k : ℝ) / 2 ^ (k + 1) := by
      field_simp;
      intro N hN₁ hN₂; induction hN₁ <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc), pow_succ' ] at * ; ring;
      field_simp;
      rename_i m hm ih; rw [ Finset.sum_Ioc_succ_top ( by linarith ) ] ; simp_all +decide [ pow_succ' ] ; ring_nf;
      convert congr_arg ( · + ( b ( 1 + m ) : ℝ ) * 2 ^ k1 - ( b m : ℝ ) * 2 ^ k1 ) ( ih ( by linarith ) ) using 1 <;> ring_nf;
      · norm_num [ mul_assoc, ← mul_pow ];
      · rw [ show ( Finset.Ioc k1 m : Finset ℕ ) = Finset.Ioc k1 ( m - 1 ) ∪ { m } from ?_, Finset.sum_union ] <;> norm_num ; ring_nf;
        · simp +zetaDelta at *;
        · exact fun _ => by linarith;
        · exact Eq.symm (Finset.insert_Ioc_sub_one_right_eq_Ioc hm);
    -- Applying the summation by parts formula to the sum up to K-1.
    have h_sum_parts_K_minus_1 : ∑ k ∈ Finset.Icc (k1 + 1) (K - 1), (b k - b (k - 1) : ℝ) / 2 ^ k = (b (K - 1) : ℝ) / 2 ^ (K - 1) - (b k1 : ℝ) / 2 ^ (k1 + 1) + ∑ k ∈ Finset.Icc (k1 + 1) (K - 2), (b k : ℝ) / 2 ^ (k + 1) := by
      exact h_sum_parts _ ( Nat.le_sub_one_of_lt hk1 ) ( Nat.sub_lt ( by linarith ) ( by linarith ) );
    -- Applying the density condition to the sum up to K-1.
    have h_density_sum : ∑ k ∈ Finset.Icc (k1 + 1) (K - 2), (b k : ℝ) / 2 ^ (k + 1) ≥ (δ' / 2) * (K - k1 - 2) := by
      have h_density_sum : ∀ k ∈ Finset.Icc (k1 + 1) (K - 2), (b k : ℝ) / 2 ^ (k + 1) ≥ δ' / 2 := by
        intro k hk; rw [ ge_iff_le ] ; rw [ div_le_div_iff₀ ] <;> first | positivity | have := h_density k ( by linarith [ Finset.mem_Icc.mp hk ] ) ( by linarith [ Finset.mem_Icc.mp hk, Nat.sub_add_cancel ( by linarith : 2 ≤ K ) ] ) ; ring_nf at * ; nlinarith [ pow_pos ( zero_lt_two' ℝ ) k ] ;
      refine' le_trans _ ( Finset.sum_le_sum h_density_sum ) ; norm_num [ mul_comm ];
      rw [ Nat.cast_sub <| by omega, Nat.cast_add, Nat.cast_sub <| by omega ] ; push_cast ; ring_nf ; norm_num;
    rcases K with ( _ | _ | K ) <;> simp_all +decide [ (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
    rw [ Finset.sum_Ioc_succ_top ] <;> norm_num;
    · refine le_trans h_density_sum ?_;
      rw [ h_sum_parts_K_minus_1 ] ; ring_nf ; norm_num;
      exact le_add_of_nonneg_of_le ( by positivity ) ( Finset.sum_le_sum fun _ _ => by ring_nf; norm_num );
    · linarith

/-
If A has positive lower density, then b_k(A) is bounded below by delta' * 2^k for large k.
-/
lemma bk_lower_bound (A : Set ℕ) (hA : lowerDensity A > 0) :
  ∃ k1 δ', δ' > 0 ∧ ∀ k ≥ k1, (bk A k : ℝ) ≥ δ' * 2^k := by
    -- By definition of liminf, there exists $N_1$ such that for all $N \ge N_1$, $|A \cap \{1, \dots, N\}|/N \ge \delta'$.
    obtain ⟨N1, hN1⟩ : ∃ N1, ∀ N ≥ N1, ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ) ≥ lowerDensity A / 2 := by
      have h_liminf : Filter.liminf (fun N => ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ)) Filter.atTop ≥ lowerDensity A := by
        unfold lowerDensity; aesop;
      rw [ Filter.liminf_eq ] at h_liminf;
      contrapose! h_liminf;
      refine' lt_of_le_of_lt ( csSup_le _ _ ) _;
      exact lowerDensity A / 2;
      · exact ⟨ 0, Filter.Eventually.of_forall fun n => by positivity ⟩;
      · exact fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ N, hN ⟩ ; obtain ⟨ M, hM₁, hM₂ ⟩ := h_liminf N; linarith [ hN M hM₁ ] ;
      · linarith;
    refine' ⟨ Nat.log 2 N1 + 1, lowerDensity A / 2, half_pos hA, fun k hk => _ ⟩;
    have := hN1 ( 2 ^ k ) ( by linarith [ Nat.lt_pow_of_log_lt one_lt_two ( by linarith : Nat.log 2 N1 < k ) ] ) ; rw [ ge_iff_le, le_div_iff₀ ] at this <;> norm_cast at * ; aesop;

theorem helper {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) : y < b ^ x ↔ Nat.log b y < x := by
  simp_all only [ne_eq]
  apply Iff.intro
  · intro a
    rw [Nat.log_lt_iff_lt_pow]
    simp_all only
    exact hb
    exact hy
  · intro a
    rw [Nat.log_lt_iff_lt_pow] at a
    simp_all only
    exact hb
    exact hy

/-
Lemma 2: A harmonic lower bound from lower density. If A has positive lower density, then the sum of reciprocals of A up to N is at least c log N.
-/
lemma harmonic_lower_bound (A : Set ℕ) (hA : lowerDensity A > 0) :
  ∃ N0 c, c > 0 ∧ ∀ N ≥ N0, ∑ a ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / a ≥ c * Real.log N := by
    -- Use `bk_lower_bound` to get $k1, \delta'$.
    obtain ⟨k1, δ', hδ'_pos, hk1⟩ : ∃ k1 δ', δ' > 0 ∧ ∀ k ≥ k1, (bk A k : ℝ) ≥ δ' * 2^k := by
      exact bk_lower_bound A hA;
    -- Let $N$ be large. Let $K = \lfloor \log_2 N \rfloor$.
    obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, ∀ N ≥ N0, ∑ k ∈ Finset.Icc (k1 + 1) (Nat.log 2 N), ((bk A k : ℝ) - bk A (k - 1)) / 2^k ≥ (δ' / 2) * (Nat.log 2 N - k1 - 2) - (bk A k1 : ℝ) / 2^(k1+1) := by
      use 2 ^ ( k1 + 2 );
      intro N hN
      have h_log : Nat.log 2 N ≥ k1 + 2 := by
        exact Nat.le_log_of_pow_le ( by norm_num ) hN;
      exact sum_density_lower_bound (bk A) δ' k1 (Nat.log 2 N) h_log fun k a a_1 => hk1 k a;
    -- The sum becomes $\sum_{k=k_1+1}^K \frac{b_k - b_{k-1}}{2^k}$.
    have h_sum_bound : ∀ N ≥ 2^(k1 + 1), ∑ a ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / a ≥ ∑ k ∈ Finset.Icc (k1 + 1) (Nat.log 2 N), ((bk A k : ℝ) - bk A (k - 1)) / 2^k := by
      intros N hN
      have h_sum_bound : ∑ a ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / a ≥ ∑ k ∈ Finset.Icc (k1 + 1) (Nat.log 2 N), ∑ a ∈ (Finset.Ioc (2^(k-1)) (2^k)).filter (· ∈ A), (1 : ℝ) / a := by
        rw [ ← Finset.sum_biUnion ];
        · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity;
          simp +contextual [ Finset.subset_iff ];
          exact fun x k hk₁ hk₂ hk₃ hk₄ hx => ⟨ Nat.pos_of_ne_zero ( by aesop ), hk₄.trans ( Nat.pow_le_of_le_log ( by aesop ) ( by linarith ) ) ⟩;
        · intros k hk l hl hkl; simp_all +decide [ Finset.disjoint_left ] ;
          intro a ha₁ ha₂ ha₃ ha₄; contrapose! hkl;
          exact le_antisymm ( Nat.le_of_not_lt fun h => by linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( Nat.le_sub_one_of_lt h ) ] ) ( Nat.le_of_not_lt fun h => by linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( Nat.le_sub_one_of_lt h ) ] );
      refine le_trans ?_ h_sum_bound;
      refine Finset.sum_le_sum fun k hk => ?_;
      refine' le_trans _ ( sum_recip_dyadic_bound A k );
      · gcongr;
        rw [ sub_le_iff_le_add' ];
        norm_cast;
        rw [ show bk A k = ( Finset.filter ( fun x => x ∈ A ) ( Finset.Icc 1 ( 2 ^ k ) ) ).card from rfl, show bk A ( k - 1 ) = ( Finset.filter ( fun x => x ∈ A ) ( Finset.Icc 1 ( 2 ^ ( k - 1 ) ) ) ).card from rfl ];
        rw [ ← Finset.card_union_of_disjoint ];
        · refine' Finset.card_mono _;
          intro x hx; by_cases hx' : x ≤ 2 ^ ( k - 1 ) <;> aesop;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
    -- Since $K \approx \log N$, the result follows.
    obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, ∀ N ≥ N1, (δ' / 2) * (Nat.log 2 N - k1 - 2) - (bk A k1 : ℝ) / 2^(k1 + 1) ≥ (δ' / 8) * Real.log N := by
      -- We'll use that $Nat.log 2 N \geq \frac{\log N}{\log 2}$ for large $N$.
      have h_log_bound : ∃ N1 : ℕ, ∀ N ≥ N1, (Nat.log 2 N : ℝ) ≥ (Real.log N) / (Real.log 2) - 1 := by
        use 2
        intro N hN
        rw [ ge_iff_le ]
        rw [ div_sub_one, div_le_iff₀ ] <;> norm_num [ Real.log_pos ]
        ring_nf
        rw [ ← Real.log_rpow, ← Real.log_mul, Real.log_le_log_iff ] <;> norm_cast <;> try positivity
        rw [ ← pow_succ, Nat.le_iff_lt_or_eq, helper ] <;> norm_num
        linarith
      obtain ⟨ N1, hN1 ⟩ := h_log_bound;
      -- We'll use that $Real.log N$ grows faster than any linear function in $N$.
      have h_log_growth : Filter.Tendsto (fun N : ℕ => (δ' / 2) * ((Real.log N) / (Real.log 2) - 1 - k1 - 2) - (bk A k1 : ℝ) / 2^(k1 + 1) - (δ' / 8) * Real.log N) Filter.atTop Filter.atTop := by
        ring_nf;
        -- We can factor out the common term $\delta'$ and use the fact that $\log N$ grows faster than any linear function in $N$.
        have h_log_growth : Filter.Tendsto (fun N : ℕ => Real.log N * (δ' * (Real.log 2)⁻¹ * (1 / 2) - δ' * (1 / 8))) Filter.atTop Filter.atTop := by
          exact Filter.Tendsto.atTop_mul_const ( by nlinarith [ show ( Real.log 2 ) ⁻¹ > 1 by exact one_lt_inv₀ ( Real.log_pos one_lt_two ) |>.2 ( Real.log_two_lt_d9.trans_le ( by norm_num ) ) ] ) ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        rw [ Filter.tendsto_atTop_atTop ] at *;
        exact fun b => by obtain ⟨ i, hi ⟩ := h_log_growth ( b + 3 * δ' / 2 + δ' * k1 / 2 + ( bk A k1 : ℝ ) * 2⁻¹ ^ k1 * ( 1 / 2 ) ) ; exact ⟨ i, fun a ha => by linarith [ hi a ha ] ⟩ ;
      exact Filter.eventually_atTop.mp ( h_log_growth.eventually_ge_atTop 0 ) |> fun ⟨ N2, hN2 ⟩ => ⟨ Max.max N1 N2, fun N hN => by nlinarith [ hN1 N ( le_trans ( le_max_left _ _ ) hN ), hN2 N ( le_trans ( le_max_right _ _ ) hN ) ] ⟩;
    exact ⟨ Max.max N0 ( Max.max N1 ( 2 ^ ( k1 + 1 ) ) ), δ' / 8, by positivity, fun N hN => le_trans ( hN1 N ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hN ) ) ( le_trans ( hN0 N ( le_trans ( le_max_left _ _ ) hN ) ) ( h_sum_bound N ( le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hN ) ) ) ⟩

/-
Definitions of U_n and Phi_n. U_n is the set of pairs (p, k) where p is a prime factor of n and 1 <= k <= v_p(n). Phi_n(d) is the subset of U_n corresponding to the divisor d.
-/
def Un (n : ℕ) : Finset ((_ : ℕ) × ℕ) :=
  (Nat.factorization n).support.sigma (fun p => Finset.Icc 1 (Nat.factorization n p))

def Phi_n (n d : ℕ) : Finset ((_ : ℕ) × ℕ) :=
  (Nat.factorization n).support.sigma (fun p => Finset.Icc 1 (Nat.factorization d p))

/-
Lemma 3: Divisors as subsets; lcm as union. Phi_n maps divisors to subsets of U_n, is injective, and preserves lcm as union.
-/
lemma divisors_to_subsets (n : ℕ) (hn : n ≠ 0) :
  (∀ d, d ∣ n → Phi_n n d ⊆ Un n) ∧
  ({d | d ∣ n}.InjOn (Phi_n n)) ∧
  (∀ d1 d2, d1 ∣ n → d2 ∣ n → Phi_n n (Nat.lcm d1 d2) = Phi_n n d1 ∪ Phi_n n d2) := by
    refine' ⟨ _, _, _ ⟩;
    · intro d hd x hx
      simp_all +decide [ Phi_n, Un ]
      exact le_trans hx.2.2 ( Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 hd _ )
    · intro d1 hd1 d2 hd2 h_eq;
      -- Since the factorizations are equal, we can conclude that d1 = d2.
      have h_factorization_eq : d1.factorization = d2.factorization := by
        ext p; by_cases hp : p ∈ n.primeFactors <;> simp_all +decide [ Finset.ext_iff, Phi_n ] ;
        · -- Apply the hypothesis `h_eq` with `a = (p, d1.factorization p + 1)` and `a = (p, d2.factorization p + 1)`.
          have h1 := h_eq ⟨p, d1.factorization p + 1⟩ hp.left hp.right (by linarith)
          have h2 := h_eq ⟨p, d2.factorization p + 1⟩ hp.left hp.right (by linarith);
          grind +ring;
        · by_cases hp : Nat.Prime p <;> simp_all +decide
          rw [ Nat.factorization_eq_zero_of_not_dvd ( fun h => ‹¬p ∣ n› <| dvd_trans h hd1 ), Nat.factorization_eq_zero_of_not_dvd ( fun h => ‹¬p ∣ n› <| dvd_trans h hd2 ) ];
      rw [ ← Nat.factorization_prod_pow_eq_self ( Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos hd1 ( Nat.pos_of_ne_zero hn ) ) ), ← Nat.factorization_prod_pow_eq_self ( Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos hd2 ( Nat.pos_of_ne_zero hn ) ) ), h_factorization_eq ];
    · intro d1 d2 hd1 hd2;
      ext ⟨ p, k ⟩ ; simp +decide [ Phi_n ] ;
      rw [ Nat.factorization_lcm ] <;> aesop

/-
Lemma 4: From lcm-triple-free to union-free. If A is lcm-triple-free, then the family of subsets corresponding to divisors of n in A is union-free.
-/
lemma lcmfree_to_unionfree (A : Set ℕ)
  (h_lcm_free : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → b ≠ c → a ≠ c → Nat.lcm a b ≠ c)
  (n : ℕ) (hn : n ≠ 0) :
  UnionFree (((Nat.divisors n).filter (· ∈ A)).image (Phi_n n)) := by
    intro x hx y hy z hz hxy hyz hxz h_union
    obtain ⟨d_x, hd_x⟩ := Finset.mem_image.mp hx
    obtain ⟨d_y, hd_y⟩ := Finset.mem_image.mp hy
    obtain ⟨d_z, hd_z⟩ := Finset.mem_image.mp hz
    have h_lcm : Nat.lcm d_x d_y = d_z := by
      have h_lcm : Phi_n n (Nat.lcm d_x d_y) = Phi_n n d_x ∪ Phi_n n d_y := by
        apply (divisors_to_subsets n hn).2.2 d_x d_y (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd_x.1 |>.1)) (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd_y.1 |>.1));
      have h_lcm : ∀ d1 d2, d1 ∣ n → d2 ∣ n → Phi_n n d1 = Phi_n n d2 → d1 = d2 := by
        have := divisors_to_subsets n hn; aesop;
      apply h_lcm;
      · exact Nat.lcm_dvd ( Nat.dvd_of_mem_divisors ( Finset.mem_filter.mp hd_x.1 |>.1 ) ) ( Nat.dvd_of_mem_divisors ( Finset.mem_filter.mp hd_y.1 |>.1 ) );
      · exact Nat.dvd_of_mem_divisors ( Finset.mem_filter.mp hd_z.1 |>.1 );
      · grind +ring;
    grind

/-
Lemma 5: A binomial upper bound. There exists a constant C0 such that the central binomial coefficient of k is at most C0 * 2^k / sqrt(k).
-/
lemma central_binom_bound :
  ∃ C0, ∀ k ≥ 1, (Nat.choose k (k / 2) : ℝ) ≤ C0 * (2^k / Real.sqrt k) := by
    -- We'll use the fact that $\binom{2m}{m} \leq \frac{4^m}{\sqrt{3m+1}}$ for all $m \geq 0$.
    have h_binom_bound : ∀ m : ℕ, (Nat.choose (2 * m) m : ℝ) ≤ (4 ^ m) / Real.sqrt (3 * m + 1) := by
      intro m
      have h_stirling : (Nat.choose (2 * m) m : ℝ) ≤ (4 ^ m) / Real.sqrt (3 * m + 1) := by
        have h_binom : (Nat.choose (2 * m) m : ℝ) ^ 2 ≤ (4 ^ (2 * m)) / (3 * m + 1) := by
          field_simp;
          induction' m with m ih <;> norm_num [ Nat.cast_succ, Nat.mul_succ, pow_succ', pow_mul' ] at *;
          have h_binom_succ : (Nat.choose (2 * m + 2) (m + 1) : ℝ) = (Nat.choose (2 * m) m : ℝ) * (2 * m + 1) * 2 / (m + 1) := by
            rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith;
            norm_num [ two_mul, add_assoc, Nat.factorial ] ; ring_nf;
            rw [ show 2 + m * 2 - ( 1 + m ) = m + 1 by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; norm_num [ Nat.factorial_succ ] ; ring_nf;
            -- Combine and simplify the fractions
            field_simp
            ring;
          rw [ h_binom_succ, div_mul_div_comm, div_mul_eq_mul_div, div_le_iff₀ ] <;> ring_nf at * <;> try positivity;
          nlinarith [ pow_nonneg ( Nat.cast_nonneg m : ( 0 : ℝ ) ≤ m ) 3 ]
        convert Real.le_sqrt_of_sq_le h_binom using 1 ; norm_num [ pow_mul' ];
      convert h_stirling using 1;
    -- Let's choose $C0 = 2$.
    use 2;
    intro k hk; rcases Nat.even_or_odd' k with ⟨ c, rfl | rfl ⟩ <;> norm_num at *;
    · refine le_trans ( h_binom_bound c ) ?_ ; ring_nf ; norm_num [ pow_mul' ];
      field_simp;
      rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith ) ) ) ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg ( 1 + c * 3 ), Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.mul_self_sqrt ( show 0 ≤ 1 + ( c : ℝ ) * 3 by positivity ), Real.sqrt_nonneg c, Real.mul_self_sqrt ( show 0 ≤ ( c : ℝ ) by positivity ) ];
    · have := h_binom_bound ( c + 1 ) ; norm_num [ Nat.add_div, Nat.mul_succ, pow_succ', pow_mul ] at *;
      rw [ show ( 2 * c + 2 : ℕ ) = 2 * c + 1 + 1 by ring, Nat.choose_succ_succ ] at this ; ring_nf at * ; norm_num at *;
      refine le_trans ?_ ( this.trans ?_ );
      · exact le_add_of_nonneg_right ( Nat.cast_nonneg _ );
      · gcongr <;> norm_num

/-
Definitions of arithmetic functions g, d_odd, and f.
-/
noncomputable def g_val (p k : ℕ) : ℝ :=
  if p = 2 then 0
  else if k = 1 then 0
  else (2 : ℝ) ^ (k - 2)

noncomputable def g_func : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (Nat.factorization n).prod (fun p k => g_val p k), by simp⟩

noncomputable def d_odd_func : ArithmeticFunction ℝ :=
  ⟨fun n => if Odd n then (tauu n : ℝ) else 0, by simp⟩

noncomputable def f_func : ArithmeticFunction ℝ :=
  ⟨fun n => if Odd n then (2 : ℝ) ^ Om n else 0, by simp⟩

/-
The arithmetic function g is multiplicative.
-/
lemma g_func_multiplicative : ArithmeticFunction.IsMultiplicative g_func := by
  constructor;
  · unfold g_func; norm_num;
  · intro m n hmn
    unfold g_func
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn];
    rw [ Finsupp.prod_add_index_of_disjoint ];
    exact hmn.disjoint_primeFactors

/-
The arithmetic function d_odd is multiplicative.
-/
lemma d_odd_func_multiplicative : ArithmeticFunction.IsMultiplicative d_odd_func := by
  unfold d_odd_func;
  constructor;
  · aesop;
  · intro m n hmn; simp +decide [ * ] ;
    split_ifs <;> simp_all +decide [ Nat.odd_iff, Nat.mul_mod ];
    unfold tauu; norm_cast;
    exact Nat.Coprime.card_divisors_mul hmn

/-
The arithmetic function f is multiplicative.
-/
lemma f_func_multiplicative : ArithmeticFunction.IsMultiplicative f_func := by
  constructor;
  · unfold f_func; norm_num;
    unfold Om; norm_num;
  · intro m n hmn
    by_cases hm : Even m <;> by_cases hn : Even n <;> simp +decide [ f_func ];
    · exact absurd ( Nat.dvd_gcd ( even_iff_two_dvd.mp hm ) ( even_iff_two_dvd.mp hn ) ) ( by aesop );
    · grind;
    · simp_all +decide [ Nat.even_iff, Nat.odd_iff, Nat.mul_mod ];
    · simp_all +decide [ Nat.even_iff, Nat.odd_iff, Om ];
      rw [ ← pow_add, Nat.factorization_mul ( by aesop ) ( by aesop ), Finsupp.sum_add_index' ] <;> aesop

set_option maxHeartbeats 1000000 in
/-
Identity for the convolution sum at odd prime powers.
-/
lemma sum_g_odd_prime (p k : ℕ) (hp : Nat.Prime p) (hp_odd : p ≠ 2) :
  ∑ j ∈ Finset.range (k + 1), (j + 1 : ℝ) * g_func (p ^ (k - j)) = (2 : ℝ) ^ k := by
    -- Let's simplify the expression using the definition of `g_func`.
    suffices h_simp : ∑ j ∈ Finset.range (k + 1), (j + 1) * (if k - j = 0 then 1 else if k - j = 1 then 0 else (2 : ℝ) ^ (k - j - 2)) = 2 ^ k by
      unfold g_func;
      convert h_simp using 2 ; norm_num [ g_val ] ; ring_nf;
      split_ifs <;> simp_all +decide [ hp.ne_zero ];
      · ring;
      · erw [ Finsupp.prod_of_support_subset ] <;> norm_num [ hp.ne_zero, hp_odd ];
        any_goals exact { p };
        · rw [ Finset.prod_singleton ] ; aesop;
        · intro q hq; contrapose! hq; simp_all +decide
        · aesop;
    induction' k using Nat.strong_induction_on with k ih;
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ Finset.sum_range_succ', pow_succ' ];
    · norm_num +zetaDelta at *;
    · have H₁ := ih k ( by linarith ) ; have H₂ := ih ( k + 1 ) ( by linarith ) ; simp_all +decide [ Finset.sum_range_succ', pow_succ' ] ;
      rcases k with ( _ | _ | k ) <;> norm_num [ Finset.sum_add_distrib, add_mul, mul_assoc, pow_succ' ] at *;
      norm_num [ Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm, Finset.sum_ite ] at *;
      linarith

/-
The functions f and d_odd * g agree on prime powers.
-/
lemma f_eq_d_odd_mul_g_prime_pow (p k : ℕ) (hp : Nat.Prime p) :
  f_func (p ^ k) = (d_odd_func * g_func) (p ^ k) := by
    -- Apply the lemma sum_g_odd_prime to conclude the proof for prime powers.
    have h_prime_pow : ∀ p k : ℕ, Nat.Prime p → ∑ j ∈ Finset.range (k + 1), (d_odd_func (p ^ j) : ℝ) * (g_func (p ^ (k - j)) : ℝ) = (f_func (p ^ k) : ℝ) := by
      intro p k hp;
      by_cases hp2 : p = 2 <;> simp_all +decide [ d_odd_func, f_func ];
      · simp +decide [ Nat.odd_iff, g_func ];
        unfold tauu Om g_val; aesop;
      · -- Apply the lemma sum_g_odd_prime to conclude the proof for odd primes.
        have := sum_g_odd_prime p k hp hp2; simp_all +decide [ tauu, Om ];
        convert this using 2;
        · rw [ if_pos ( by exact Odd.pow ( by simpa using hp.eq_two_or_odd'.resolve_left hp2 ) ), Nat.divisors_prime_pow hp ] ; aesop;
        · simp +decide [ hp.even_iff, hp2, parity_simps ];
    rw [ ← h_prime_pow p k hp, ArithmeticFunction.mul_apply ];
    rw [ Nat.sum_divisorsAntidiagonal fun i j => d_odd_func i * g_func j ];
    norm_num [ Nat.divisors_prime_pow hp ];
    exact Finset.sum_congr rfl fun x hx => by rw [ Nat.div_eq_of_eq_mul_left ( pow_pos hp.pos _ ) ] ; rw [ ← pow_add, Nat.sub_add_cancel ( Finset.mem_range_succ_iff.mp hx ) ] ;

/-
The function f is equal to the Dirichlet convolution of d_odd and g.
-/
lemma f_eq_d_odd_mul_g : f_func = d_odd_func * g_func := by
  apply ArithmeticFunction.ext;
  -- By definition of multiplicative functions, if two multiplicative functions agree on prime powers, they are equal everywhere.
  have h_mul_eq : ∀ (f g : ArithmeticFunction ℝ), ArithmeticFunction.IsMultiplicative f → ArithmeticFunction.IsMultiplicative g → (∀ p k, Nat.Prime p → f (p ^ k) = g (p ^ k)) → f = g := by
    intros f g hf hg hfg;
    exact (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers f hf g hg).mpr hfg;
  exact fun n => congr_arg ( fun f => f n ) ( h_mul_eq _ _ ( f_func_multiplicative ) ( d_odd_func_multiplicative.mul g_func_multiplicative ) fun p k hp => f_eq_d_odd_mul_g_prime_pow p k hp ) ▸ rfl

/-
The sum of the divisor function is O(N log N).
-/
lemma sum_tau_bound : (fun N => ∑ n ∈ Finset.range (N + 1), (tauu n : ℝ)) =O[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
  -- The sum of the divisor function $\tau(n)$ over $n \leq N$ is $O(N \log N)$.
  have h_sum_divisors : ∀ N : ℕ, (∑ n ∈ Finset.range (N + 1), (tauu n : ℝ)) ≤ (N + 1) * (Real.log (N + 1) + 1) := by
    intro N;
    -- We'll use the fact that $\sum_{n \leq N} � \�tau(n) \leq \sum_{d \leq N �}� \left\lfloor \frac{N}{d} \right\rfloor$.
    have h_sum_divisors_le_floor : ∑ n ∈ Finset.range (N + 1), (tauu n : ℝ) ≤ ∑ d ∈ Finset.Ico 1 (N + 1), (N / d : ℝ) := by
      -- We'll use the fact that $\sum_{n \leq N} \tau(n)$ is equal to $\sum_{d \leq N} \left\lfloor \frac{N}{d} \right\rfloor$.
      have h_sum_divisors_eq : ∑ n ∈ Finset.range (N + 1), (tauu n : ℝ) = ∑ d ∈ Finset.Ico 1 (N + 1), (Nat.floor (N / d) : ℝ) := by
        induction N <;> simp_all +decide [ Finset.sum_range_succ, Nat.succ_div ];
        simp +decide [ Finset.sum_add_distrib, Finset.sum_Ico_succ_top, Nat.div_eq_of_lt ];
        unfold tauu; aesop;
      exact h_sum_divisors_eq.le.trans ( Finset.sum_le_sum fun x hx => by rw [ le_div_iff₀ ] <;> norm_cast <;> nlinarith [ Finset.mem_Ico.mp hx, Nat.div_mul_le_self N x, Nat.floor_le ( show 0 ≤ N / x from Nat.zero_le _ ) ] );
    -- We'll use the fact � that� $\sum_{d=1}^{N} \frac{1}{d} \leq \log N + 1$.
    have h_harmonic : ∑ d ∈ Finset.Ico 1 (N + 1), (1 / (d : ℝ)) ≤ Real.log N + 1 := by
      have h_sum_divisors_le_harmonic : ∀ N : ℕ, N ≥ 1 → ∑ x ∈ Finset.Ico 1 (N + 1), (1 / (x : ℝ)) ≤ Real.log N + 1 := by
        intros N hN; induction' hN with N hN ih <;> norm_num [ Finset.sum_Ico_succ_top ] at *;
        field_simp;
        have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( N : ℝ ) / ( N + 1 ) ) ; rw [ Real.log_div ( by positivity ) ( by positivity ) ] at this ; norm_num at * ; nlinarith [ mul_div_cancel₀ ( N : ℝ ) ( by positivity : ( N + 1 : ℝ ) ≠ 0 ) ] ;
      exact if hN : 1 ≤ N then h_sum_divisors_le_harmonic N hN else by aesop;
    rcases N.eq_zero_or_pos with hN | hN <;> simp_all +decide [ div_eq_mul_inv ];
    exact h_sum_divisors_le_floor.trans ( by rw [ ← Finset.mul_sum _ _ _ ] ; nlinarith [ Real.log_nonneg ( show ( N:ℝ ) ≥ 1 by norm_cast ), Real.log_le_log ( by positivity ) ( show ( N:ℝ ) + 1 ≥ N by linarith ) ] );
  refine' Asymptotics.IsBigO.of_bound 8 _;
  filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN ; rw [ Real.norm_of_nonneg <| Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ] ; rw [ Real.norm_of_nonneg <| by positivity ] ; specialize h_sum_divisors N ; rcases N with ( _ | _ | N ) <;> norm_num at *;
  have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( N + 1 + 1 + 1 : ℝ ) / ( N + 1 + 1 ) ) ; rw [ Real.log_div ( by positivity ) ( by positivity ) ] at this ; ring_nf at * ; norm_num at *;
  nlinarith [ Real.log_inv ( 2 + N : ℝ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < ( 2 + N : ℝ ) ) ), mul_inv_cancel₀ ( by linarith : ( 2 + N : ℝ ) ≠ 0 ), Real.log_pos ( by linarith : ( 2 + N : ℝ ) > 1 ), Real.log_le_log ( by linarith ) ( by linarith : ( 3 + N : ℝ ) ≥ ( 2 + N : ℝ ) ) ]

/-
The arithmetic function g is non-negative.
-/
lemma g_func_nonneg (n : ℕ) : 0 ≤ g_func n := by
  unfold g_func;
  unfold g_val;
  norm_num +zetaDelta at *;
  split_ifs <;> norm_num [ Finsupp.prod ];
  exact Finset.prod_nonneg fun _ _ => by split_ifs <;> positivity;

/-
Identity for the sum of a Dirichlet convolution.
-/
lemma sum_convolution_eq {f g : ArithmeticFunction ℝ} (N : ℕ) :
  ∑ n ∈ Finset.range (N + 1), (f * g) n = ∑ q ∈ Finset.range (N + 1), g q * ∑ m ∈ Finset.range (N / q + 1), f m := by
    simp +decide only [ArithmeticFunction.mul_apply];
    simp +decide only [Nat.divisorsAntidiagonal, Finset.sum_sigma'];
    rw [ show ( Finset.range ( N + 1 ) ).sigma ( fun a => Finset.filterMap ( fun x => if x * ( a / x ) = a then some ( x, a / x ) else none ) ( Finset.Icc 1 a ) _ ) = Finset.biUnion ( Finset.range ( N + 1 ) ) ( fun x => Finset.image ( fun m => ⟨ x * m, ( m, x ) ⟩ ) ( Finset.Icc 1 ( N / x ) ) ) from ?_, Finset.sum_biUnion ];
    · simp +decide [ mul_comm, Finset.mul_sum _ _ _ ];
      exact Finset.sum_congr rfl fun i hi => by erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num;
    · intros x hx y hy hxy; simp [Finset.disjoint_left, Finset.mem_image];
      grind;
    · -- To prove equality of finite � sets�, we show each set is a subset of the other.
      apply Finset.ext
      intro p
      simp [Finset.mem_sigma, Finset.mem_biUnion, Finset.mem_image];
      constructor;
      · rintro ⟨ h₁, a, ⟨ ha₁, ha₂ ⟩, ha₃, ha₄ ⟩;
        use p.fst / a, by
          nlinarith [ Nat.div_mul_le_self p.fst a ], a, by
          exact ⟨ ha₁, by rw [ Nat.le_div_iff_mul_le ( Nat.div_pos ( by linarith ) ( by linarith ) ) ] ; nlinarith ⟩
        generalize_proofs at *;
        grind;
      · rintro ⟨ a, ha, b, hb, rfl ⟩;
        rcases a with ( _ | a ) <;> rcases b with ( _ | b ) <;> norm_num at *;
        exact ⟨ by nlinarith [ Nat.div_mul_le_self N ( a + 1 ) ], b + 1, ⟨ by linarith, by nlinarith ⟩, by rw [ Nat.mul_div_cancel' ] ; exact dvd_mul_left _ _, rfl, by rw [ Nat.mul_div_cancel _ ( by linarith ) ] ⟩

/-
The sum of g(p^k)/p^k is bounded by 1 + 3/p^2 for odd primes p.
-/
lemma prime_sum_bound (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    Summable (fun k => g_func (p ^ k) / (p ^ k : ℝ)) ∧
    ∑' k, g_func (p ^ k) / (p ^ k : ℝ) ≤ 1 + 3 / (p ^ 2 : ℝ) := by
      constructor;
      · refine' summable_nat_add_iff 2 |>.1 _;
        -- We'll use the fact that $g(p^k) = 2^{k-2}$ for $k \geq 2$.
        have h_g_p_k : ∀ k ≥ 2, g_func (p ^ k) = (2 : ℝ) ^ (k - 2) := by
          unfold g_func;
          unfold g_val; aesop;
        norm_num [ h_g_p_k ];
        ring_nf;
        simpa only [ mul_assoc, ← mul_pow ] using Summable.mul_left _ ( summable_geometric_of_lt_one ( by positivity ) ( by rw [ inv_mul_lt_iff₀ ( by norm_cast; linarith [ hp.pos ] ) ] ; norm_cast; linarith [ hp.two_le, show p > 2 from lt_of_le_of_ne hp.two_le ( Ne.symm hp_odd ) ] ) );
      · -- For an odd prime $p$, $g(p^0)=1$, $g(p^1)=0$, and $g(p^k)=2^{k-2}$ for $k \ge 2$.
        have h_g_prime_power (k : ℕ) : g_func (p ^ k) = if k = 0 then 1 else if k = 1 then 0 else (2 : ℝ) ^ (k - 2) := by
          unfold g_func;
          unfold g_val; aesop;
        -- The sum of the geometric series $\sum_{k=2}^\infty \frac{2^{k-2}} �{�p^k}$ is $\frac{1}{p^2} \sum_{j=0}^\in �fty� \left(\frac{2}{p}\right)^j = \frac{1}{p^2} \cdot \frac{1}{1 - \frac{2}{p}} = \frac{1}{p(p-2)}$.
        have h_geo_series : ∑' k : ℕ, (if k = 0 then 1 else if k = 1 then 0 else (2 : ℝ) ^ (k - 2)) / (p ^ k : ℝ) = 1 + (1 / (p ^ 2 : ℝ)) * (1 / (1 - 2 / p)) := by
          rw [ ← Summable.sum_add_tsum_nat_add 2 ];
          · norm_num [ Finset.sum_range_succ' ];
            rw [ ← tsum_geometric_of_lt_one ( by positivity ) ( show ( 2 : ℝ ) / p < 1 by rw [ div_lt_iff₀ ( Nat.cast_pos.mpr hp.pos ) ] ; norm_cast; linarith [ show p > 2 from lt_of_le_of_ne hp.two_le ( Ne.symm hp_odd ) ] ) ] ; rw [ ← tsum_mul_left ] ; congr ; ext i ; ring_nf;
            grind;
          · rw [ ← summable_nat_add_iff 2 ];
            norm_num [ pow_add, ← div_div ];
            norm_num [ Nat.succ_inj ];
            simpa only [ ← div_pow ] using Summable.mul_right _ ( summable_geometric_of_lt_one ( by positivity ) ( by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ hp.two_le, show p > 2 from lt_of_le_of_ne hp.two_le ( Ne.symm hp_odd ) ] ) );
        simp_all +decide [ division_def ];
        rw [ ← mul_inv, mul_comm ];
        rw [ inv_le_comm₀ ] <;> norm_num <;> nlinarith only [ show ( p : ℝ ) ≥ 3 by norm_cast; contrapose! hp_odd; interval_cases p <;> trivial, inv_mul_cancel₀ ( show ( p : ℝ ) ≠ 0 by norm_cast; exact hp.ne_zero ), inv_mul_cancel₀ ( show ( p ^ 2 : ℝ ) ≠ 0 by norm_cast; exact pow_ne_zero 2 hp.ne_zero ) ]

/-
The product of (1 + 3/p^2) is bounded.
-/
lemma prod_one_plus_inv_sq_bound : ∃ C, ∀ (S : Finset ℕ), (∀ p ∈ S, p ≥ 1) → ∏ p ∈ S, (1 + 3 / (p ^ 2 : ℝ)) ≤ C := by
  use Real.exp ( ∑' p : ℕ, ( 3 / ( p : ℝ ) ^ 2 ) );
  intros S hS_pos
  have h_prod_le_exp : (∏ p ∈ S, (1 + 3 / (p : ℝ) ^ 2)) ≤ Real.exp (∑ p ∈ S, (3 / (p : ℝ) ^ 2)) := by
    rw [ Real.exp_sum ] ; exact Finset.prod_le_prod ( fun _ _ => by positivity ) fun _ _ => by rw [ add_comm ] ; exact Real.add_one_le_exp _;
  exact h_prod_le_exp.trans ( Real.exp_le_exp.mpr <| Summable.sum_le_tsum _ ( fun _ _ => by positivity ) <| by simpa using Summable.mul_left _ <| Real.summable_one_div_nat_pow.2 one_lt_two )

/-
The sum of a non-negative multiplicative function is bounded by the product of its prime power sums.
-/
lemma sum_le_prod_of_multiplicative_bounded (f : ℕ → ℝ) (hf_pos : ∀ n, 0 ≤ f n)
    (hf_mul : ∀ m n, m.Coprime n → f (m * n) = f m * f n) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n ≤
    ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (∑ k ∈ Finset.range (Nat.log p N + 1), f (p ^ k)) := by
      by_contra h_contra;
      -- Let $S = \{p \in \mathbb{P} \mid p \le N\}$.
      set S : Finset ℕ := Finset.filter Nat.Prime (Finset.range (N + 1)) with hS_def;
      -- By definition of $S$, we know that every $n \in \{1, \ldots, N\}$ can be written as $n = \prod_{p \in S} p^{e_p}$ where $0 \leq e_p \le �q� \lfloor \log_p N \rfloor$.
      have h_factorization : ∀ n ∈ Finset.Icc 1 N, ∃ e : ℕ → ℕ, (∀ p, p ∉ S → e p = 0) ∧ (∀ p ∈ S, e p ≤ Nat.log p N) ∧ n = ∏ p ∈ S, p ^ e p := by
        intro n hn
        use fun p => Nat.factorization n p
        simp [hS_def];
        refine' ⟨ _, _, _ ⟩;
        · intro p hp; by_cases hp_prime : Nat.Prime p <;> simp_all +decide [ Nat.factorization_eq_zero_iff ] ;
          exact Or.inl ( Nat.not_dvd_of_pos_of_lt hn.1 ( by linarith ) );
        · exact fun p hp₁ hp₂ => Nat.le_log_of_pow_le hp₂.one_lt <| Nat.le_trans ( Nat.le_of_dvd ( Finset.mem_Icc.mp hn |>.1 ) <| Nat.ordProj_dvd _ _ ) <| Finset.mem_Icc.mp hn |>.2;
        · conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hn ] : n ≠ 0 ) ] ;
          rw [ Finsupp.prod_of_support_subset ] <;> norm_num;
          exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_trans ( Nat.le_of_mem_primeFactors hp ) ( Finset.mem_Icc.mp hn |>.2 ) ) ), Nat.prime_of_mem_primeFactors hp ⟩;
      -- By definition of $f$, we know that $f(n) = \prod_{p \in S} f(p^{e_p})$ for any $n = \prod_{p \in S} p^{e_p}$.
      have h_f_factorization : ∀ n ∈ Finset.Icc 1 N, ∀ e : ℕ → ℕ, (∀ p, p ∉ S → e p = 0) ∧ (∀ p ∈ S, e p ≤ Nat.log p N) ∧ n = ∏ p ∈ S, p ^ e p → f n = ∏ p ∈ S, f (p ^ e p) := by
        intros n hn e he
        have h_f_factorization_step : ∀ (ps : Finset ℕ), (∀ p ∈ ps, Nat.Prime p) → (∀ p ∈ ps, e p ≤ Nat.log p N) → f (∏ p ∈ ps, p ^ e p) = ∏ p ∈ ps, f (p ^ e p) := by
          intros ps hps_prime hps_log; induction' ps using Finset.induction with p ps hps ih; simp_all +decide
          · by_cases h : f 1 = 0;
            · have h_f_zero : ∀ n, 1 ≤ n → n ≤ N → f n = 0 := by
                exact fun n hn hn' => by simpa [ h ] using hf_mul n 1 ( by norm_num ) ;
              exact False.elim <| h_contra.not_ge <| by rw [ Finset.sum_eq_zero fun x hx => h_f_zero x ( Finset.mem_Icc.mp hx |>.1 ) ( Finset.mem_Icc.mp hx |>.2 ) ] ; exact Finset.prod_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf_pos _;
            · simpa [ h ] using hf_mul 1 1 ( by norm_num );
          · rw [ Finset.prod_insert hps, hf_mul ];
            · rw [ Finset.prod_insert hps, ih ( fun q hq => hps_prime q ( Finset.mem_insert_of_mem hq ) ) ( fun q hq => hps_log q ( Finset.mem_insert_of_mem hq ) ) ];
            · exact Nat.Coprime.prod_right fun q hq => Nat.Coprime.pow _ _ <| by have := Nat.coprime_primes ( hps_prime p <| Finset.mem_insert_self _ _ ) ( hps_prime q <| Finset.mem_insert_of_mem hq ) ; aesop;
        rw [ he.2.2, h_f_factorization_step S ( fun p hp => Finset.mem_filter.mp hp |>.2 ) ( fun p hp => he.2.1 p hp ) ];
      refine' h_contra _;
      choose! e he using h_factorization;
      rw [ Finset.prod_sum ];
      refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
      case refine'_2 => exact Finset.image ( fun n => fun p hp => e n p ) ( Finset.Icc 1 N );
      · rw [ Finset.sum_image ];
        · refine' Finset.sum_le_sum fun n hn => _;
          convert h_f_factorization n hn ( fun p => e n p ) ( he n hn ) |> le_of_eq using 1;
          conv_rhs => rw [ ← Finset.prod_attach ] ;
        · intros n hn m hm hnm;
          rw [ he n hn |>.2.2, he m hm |>.2.2 ];
          exact Finset.prod_congr rfl fun p hp => congr_arg _ ( congr_fun ( congr_fun hnm p ) hp );
      · exact Finset.image_subset_iff.mpr fun n hn => Finset.mem_pi.mpr fun p hp => Finset.mem_range.mpr ( Nat.lt_succ_of_le ( he n hn |>.2.1 p hp ) );
      · exact fun _ _ _ => Finset.prod_nonneg fun _ _ => hf_pos _

/-
The sum of g(q)/q is bounded.
-/
lemma sum_g_div_q_bound : ∃ C, ∀ N, ∑ q ∈ Finset.range (N + 1), g_func q / q ≤ C := by
  -- By definition of $g_func$, we know that $g_func(q) = 0$ for $q = 0$.
  use ∑' q : ℕ, g_func q / (q : ℝ);
  have h_sum_le_prod : Summable (fun q : ℕ => g_func q / (q : ℝ)) := by
    have h_sum_g_bounded : Summable (fun q : ℕ => (g_func q : ℝ) / (q : ℝ)) := by
      have h_sum_g_bounded : Summable (fun q : ℕ => (g_func (q : ℕ) : ℝ) / (q : ℝ)) := by
        have := @prod_one_plus_inv_sq_bound
        have h_sum_le_prod : ∀ N : ℕ, ∑ q ∈ Finset.range (N + 1), (g_func q : ℝ) / q ≤ ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 + 3 / (p ^ 2 : ℝ)) := by
          intro N
          have h_sum_le_prod : ∑ q ∈ Finset.Icc 1 N, (g_func q : ℝ) / q ≤ ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (∑ k ∈ Finset.range (Nat.log p N + 1), (g_func (p ^ k) : ℝ) / p ^ k) := by
            convert sum_le_prod_of_multiplicative_bounded _ _ _ _ using 1;
            · norm_num [ div_eq_mul_inv ];
            · exact fun n => div_nonneg ( g_func_nonneg n ) ( Nat.cast_nonneg n );
            · intro m n hmn
              have h_mul : g_func (m * n) = g_func m * g_func n := by
                have := g_func_multiplicative; aesop;
              by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp_all +decide [ mul_div_mul_comm ];
          have h_sum_le_prod : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), ∑ k ∈ Finset.range (Nat.log p N + 1), (g_func (p ^ k) : ℝ) / p ^ k ≤ 1 + 3 / (p ^ 2 : ℝ) := by
            intros p hp
            by_cases hp2 : p = 2;
            · unfold g_func; norm_num [ hp2 ] ; ring_nf; norm_num;
              norm_num [ Finsupp.prod ];
              rw [ add_comm, Finset.sum_eq_single 0 ] <;> norm_num [ Finsupp.support_single_ne_zero ];
              intro b hb hb'; rw [ Finsupp.support_single_ne_zero ] <;> aesop;
            · have := prime_sum_bound p ( Finset.mem_filter.mp hp |>.2 ) hp2;
              exact le_trans ( Summable.sum_le_tsum ( Finset.range ( Nat.log p N + 1 ) ) ( fun _ _ => div_nonneg ( g_func_nonneg _ ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ) this.1 ) this.2;
          refine le_trans ?_ ( le_trans ‹_› <| Finset.prod_le_prod ?_ h_sum_le_prod );
          · erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
          · exact fun p hp => Finset.sum_nonneg fun _ _ => div_nonneg ( g_func_nonneg _ ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ );
        rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
        · rw [ ← Filter.tendsto_add_atTop_iff_nat 1 ] ; exact fun h => absurd ( h.eventually_gt_atTop ( this.choose : ℝ ) ) fun h' => by obtain ⟨ N, hN ⟩ := h'.exists; exact not_le_of_gt hN <| le_trans ( h_sum_le_prod N ) <| this.choose_spec _ fun p hp => Nat.Prime.pos <| by aesop;
        · exact fun n => div_nonneg ( g_func_nonneg n ) ( Nat.cast_nonneg n )
      exact h_sum_g_bounded;
    convert h_sum_g_bounded using 1;
  exact fun N => Summable.sum_le_tsum ( Finset.range ( N + 1 ) ) ( fun _ _ => div_nonneg ( g_func_nonneg _ ) ( Nat.cast_nonneg _ ) ) h_sum_le_prod

/-
The sum of f is bounded by the convolution of g and tau.
-/
lemma sum_f_le_sum_g_mul_sum_tau (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), f_func n ≤
    ∑ q ∈ Finset.range (N + 1), g_func q * ∑ m ∈ Finset.range (N / q + 1), (tauu m : ℝ) := by
      rw [ f_eq_d_odd_mul_g ];
      rw [ sum_convolution_eq ];
      gcongr;
      · (expose_names; exact g_func_nonneg i);
      · unfold d_odd_func; aesop

/-
There exists a constant C such that the sum of tau(n) is bounded by C * N * (log N + 1) for all N >= 1.
-/
lemma sum_tau_explicit_bound : ∃ C, ∀ N ≥ 1, ∑ n ∈ Finset.range (N + 1), (tauu n : ℝ) ≤ C * N * (Real.log N + 1) := by
  have := sum_tau_bound;
  rw [ Asymptotics.isBigO_iff' ] at this;
  obtain ⟨ C, hC₀, hC ⟩ := this; erw [ Filter.eventually_atTop ] at hC; obtain ⟨ N₀, hN₀ ⟩ := hC; use Max.max C ( ∑ n ∈ Finset.range ( N₀ + 1 ), ( tauu n : ℝ ) ) ; intro N hN; rcases le_or_gt N N₀ with hN' | hN' <;> simp_all +decide [ mul_assoc ] ;
  · refine' le_trans _ ( mul_le_mul_of_nonneg_right ( le_max_right _ _ ) ( by positivity ) );
    exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( by linarith ) ) fun _ _ _ => Nat.cast_nonneg _ ) ( le_mul_of_one_le_right ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) ( by nlinarith [ Real.log_nonneg ( show ( N : ℝ ) ≥ 1 by norm_cast ), show ( N : ℝ ) ≥ 1 by norm_cast ] ) );
  · refine' le_trans ( le_of_abs_le ( hN₀ N hN'.le ) ) _;
    rw [ abs_of_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr hN ) ) ] ; exact mul_le_mul ( le_max_left _ _ ) ( by nlinarith [ Real.log_nonneg ( Nat.one_le_cast.mpr hN ) ] ) ( by positivity ) ( by positivity ) ;

/-
The sum of f(n) is bounded by C * N * (log N + 1).
-/
lemma sum_f_explicit_bound : ∃ C, ∀ N ≥ 1, ∑ n ∈ Finset.range (N + 1), f_func n ≤ C * N * (Real.log N + 1) := by
  -- By combining the results from sum_f_le_sum_g_mul_sum_tau and sum_tau_explicit_bound, we can conclude the proof.
  obtain ⟨C1, hC1⟩ := sum_tau_explicit_bound
  obtain ⟨C2, hC2⟩ := sum_g_div_q_bound
  use C1 * C2;
  intros N hN
  have h_sum_g_mul_sum_tau : ∑ n ∈ Finset.range (N + 1), f_func n ≤ ∑ q ∈ Finset.range (N + 1), g_func q * (C1 * (N / q) * (Real.log N + 1)) := by
    refine le_trans ( sum_f_le_sum_g_mul_sum_tau N ) ?_;
    refine Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left ?_ <| ?_;
    · by_cases hq0 : q = 0;
      · aesop;
      · refine le_trans ( hC1 ( N / q ) ( Nat.div_pos ( by linarith [ Finset.mem_range.mp hq ] ) ( Nat.pos_of_ne_zero hq0 ) ) ) ?_;
        gcongr <;> norm_cast;
        · exact mul_nonneg ( by have := hC1 1 le_rfl; norm_num [ Finset.sum_range_succ, tauu ] at this; nlinarith [ Real.log_nonneg one_le_two ] ) ( by positivity );
        · specialize hC1 1 ; norm_num at hC1 ; linarith [ show ( ∑ n ∈ Finset.range 2, ( tauu n : ℝ ) ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ];
        · rw [ le_div_iff₀ ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hq0 ) ) ] ; norm_cast ; linarith [ Nat.div_mul_le_self N q ];
        · exact Nat.div_pos ( by linarith [ Finset.mem_range.mp hq ] ) ( Nat.pos_of_ne_zero hq0 );
        · exact Nat.div_le_self _ _;
    · exact g_func_nonneg q;
  refine le_trans h_sum_g_mul_sum_tau ?_;
  convert mul_le_mul_of_nonneg_left ( hC2 N ) ( show 0 ≤ C1 * ↑N * ( Real.log ↑N + 1 ) by exact mul_nonneg ( mul_nonneg ( show 0 ≤ C1 by have := hC1 1 le_rfl; norm_num [ Finset.sum_range_succ, tauu ] at this; nlinarith ) ( Nat.cast_nonneg _ ) ) ( add_nonneg ( Real.log_natCast_nonneg _ ) zero_le_one ) ) using 1 ; ring_nf;
  · rw [ Finset.mul_sum _ _ _, Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_congr rfl fun _ _ => by ring;
  · ring

/-
A summatory bound for $2^{\Om(n)}$ over odd integers.
Define $f(n)=2^{\Om(n)}$ if $n$ is odd and $f(n)=0$ if $n$ is even.
Then
\[
\sum_{n\le N} f(n)\ \ll\ N\log N.
\]
-/
lemma sum_2Omega_odd : (fun N => ∑ n ∈ Finset.range (N + 1), f_func n) =O[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
  choose! C hC using sum_f_explicit_bound;
  refine' Asymptotics.IsBigO.of_bound ( |C| + |C| ) _;
  filter_upwards [ Filter.eventually_ge_atTop 3 ] with N hN;
  rw [ Real.norm_of_nonneg ( Finset.sum_nonneg fun _ _ => ?_ ), Real.norm_of_nonneg ( by positivity ) ];
  · refine le_trans ( hC N ( by linarith ) ) ?_;
    cases abs_cases C <;> nlinarith [ show ( N : ℝ ) * Real.log N ≥ N by nlinarith [ show ( N : ℝ ) ≥ 3 by norm_cast, Real.le_log_iff_exp_le ( by positivity : 0 < ( N : ℝ ) ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( N : ℝ ) ≥ 3 by norm_cast ] ], show ( N : ℝ ) ≥ 3 by norm_cast ];
  · unfold f_func; aesop;

/-
h(n) is bounded by C * 2^Omega(n) / sqrt(Omega(n)) for odd n >= 3.
-/
noncomputable def h_func (n : ℕ) : ℝ :=
  if Odd n then ((Om n).choose ((Om n) / 2) : ℝ) else 0

lemma h_func_bound_exists : ∃ C, ∀ n, Odd n → n ≥ 3 → h_func n ≤ C * (2 ^ (Om n) / Real.sqrt (Om n)) := by
  -- Apply Lemma~\ref{lem:central_binom_bound} with a pre-factored $2^k$.
  obtain ⟨C0, hC0⟩ := central_binom_bound;
  -- Let $k = \Omega(n)$. Then $h(n) = \binom{k}{k/2} \le C_0 2^k / \sqrt{k}$.
  use C0;
  intros n hn hn_ge_3
  have h_om : Om n ≥ 1 := by
    exact Finset.sum_pos ( fun p hp => Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp ) ) ⟨ Nat.minFac _, Nat.mem_primeFactors.mpr ⟨ Nat.minFac_prime ( by linarith ), Nat.minFac_dvd _, by linarith ⟩ ⟩
  generalize_proofs at *; (
  unfold h_func; aesop;)

/-
$h(n) \le 2^{\Omega(n)}$ for all $n$.
-/
lemma h_func_le_two_pow_Om (n : ℕ) : h_func n ≤ (2 : ℝ) ^ Om n := by
  by_cases hn : Odd n <;> simp_all +decide [ h_func ];
  · rw_mod_cast [ ← Nat.sum_range_choose ] ; exact Finset.single_le_sum ( fun x _ => Nat.zero_le _ ) ( Finset.mem_range.mpr <| Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.div_add_mod ( Om n ) 2, Nat.mod_lt ( Om n ) two_pos ] ) ;
  · exact if_neg ( by simpa using hn ) |> fun h => h.symm ▸ by norm_num;

/-
The sum of $h(n)$ for $\Omega(n) < L$ is bounded by $(N+1) 2^L$.
-/
lemma sum_h_lt_L_bound (N L : ℕ) :
    ∑ n ∈ (Finset.range (N + 1)).filter (λ n => Odd n ∧ Om n < L), h_func n ≤ (N + 1 : ℝ) * (2 : ℝ) ^ L := by
      refine' le_trans ( Finset.sum_le_sum fun i hi => show h_func i ≤ 2 ^ L from _ ) _;
      · refine' le_trans ( h_func_le_two_pow_Om i ) _;
        exact pow_le_pow_right₀ ( by norm_num ) ( by linarith [ Finset.mem_filter.mp hi ] );
      · norm_num [ Finset.sum_const ];
        exact_mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num )

/-
Let $C_h$ be the constant such that $h(n) \le C_h 2^{\Omega(n)} / \sqrt{\Omega(n)}$ for odd $n \ge 3$.
-/
noncomputable def C_h : ℝ := h_func_bound_exists.choose

lemma h_func_le_C_h (n : ℕ) (hn_odd : Odd n) (hn_ge_3 : n ≥ 3) :
    h_func n ≤ C_h * (2 ^ (Om n) / Real.sqrt (Om n)) :=
  h_func_bound_exists.choose_spec n hn_odd hn_ge_3

/-
The sum of $h(n)$ for $\Omega(n) \ge L$ is bounded by $\frac{C_h}{\sqrt{L}} \sum f(n)$.
-/
lemma sum_h_ge_L_bound (N L : ℕ) (hL : L ≥ 1) :
    ∑ n ∈ (Finset.range (N + 1)).filter (λ n => Odd n ∧ Om n ≥ L), h_func n ≤
    (C_h / Real.sqrt L) * ∑ n ∈ Finset.range (N + 1), f_func n := by
      -- By `h_func_le_C_h`, $h(n) \le C_h \frac{2^{\Omega(n)}}{\sqrt{\Omega(n)}} \le C_h \frac{2^{\Omega(n)}}{\sqrt{L}}$.
      have h_bound : ∀ n, Odd n → L ≤ Om n → (h_func n) ≤ (C_h / Real.sqrt L) * (f_func n) := by
        intros n hn_odd hn_L
        have h_le_C_h : h_func n ≤ C_h * (2 ^ (Om n) / Real.sqrt (Om n)) := by
          by_cases hn_ge_3 : n ≥ 3;
          · convert h_func_le_C_h n hn_odd hn_ge_3 using 1;
          · interval_cases n <;> simp_all +decide [ Om ];
        have h_bound : (2 ^ (Om n) / Real.sqrt (Om n)) ≤ (2 ^ (Om n) / Real.sqrt L) := by
          gcongr;
        have h_f_eq : f_func n = (2 : ℝ) ^ (Om n) := by
          unfold f_func; aesop;
        convert h_le_C_h.trans ( mul_le_mul_of_nonneg_left h_bound <| show 0 ≤ C_h by exact le_of_not_gt fun h => by have := h_func_le_C_h 3 ( by decide ) ( by decide ) ; norm_num [ h_func, Om ] at this ; nlinarith [ Real.sqrt_nonneg 1, Real.sq_sqrt zero_le_one ] ) using 1 ; rw [ h_f_eq ] ; ring;
      field_simp;
      rw [ Finset.sum_mul _ _ _ ];
      refine' le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( h_bound i ( Finset.mem_filter.mp hi |>.2.1 ) ( Finset.mem_filter.mp hi |>.2.2 ) ) ( Real.sqrt_nonneg _ ) ) _;
      norm_num [ div_mul_eq_mul_div, Finset.mul_sum _ _ _ ];
      field_simp;
      exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( show 0 ≤ C_h by exact le_of_not_gt fun h => by have := h_func_le_C_h 3 ( by decide ) ( by decide ) ; norm_num [ h_func, Om ] at this ; linarith ) ( show 0 ≤ f_func _ by exact by unfold f_func; aesop )

/-
Define $L(N) = \lfloor \frac{1}{2} \log \log N \rfloor$.
-/
noncomputable def L_nat (N : ℕ) : ℕ := Nat.floor (Real.log (Real.log N) / 2)

/-
$L(N) \to \infty$ as $N \to \infty$.
-/
lemma L_nat_tendsto : Filter.Tendsto L_nat Filter.atTop Filter.atTop := by
  -- Since $\log(\log N)$ tends to infinity as $N$ tends to infinity, dividing by 2 and taking the floor will also tend to infinity.
  have h_log_log_inf : Filter.Tendsto (fun N => Real.log (Real.log N)) Filter.atTop Filter.atTop := by
    exact Real.tendsto_log_atTop.comp Real.tendsto_log_atTop;
  rw [ Filter.tendsto_atTop_atTop ] at *;
  exact fun b => by obtain ⟨ i, hi ⟩ := h_log_log_inf ( 2 * ( b + 1 ) ) ; exact ⟨ ⌈i⌉₊ + 1, fun a ha => Nat.le_floor <| by linarith [ hi a <| Nat.le_of_ceil_le <| by linarith ] ⟩ ;

/-
Eventually $L(N) \ge 1$.
-/
lemma L_nat_ge_one : ∀ᶠ N in Filter.atTop, 1 ≤ L_nat N := by
  -- Since $L_nat N$ tends to infinity as $N$ tends to infinity, there exists some $N₀$ such that for all $N \geq N₀$, $L_nat N \geq 1$.
  have hL_nat_inf : Filter.Tendsto L_nat Filter.atTop Filter.atTop := by
    convert L_nat_tendsto;
  exact hL_nat_inf.eventually_ge_atTop 1

/-
$(N+1) 2^{L(N)} = o(N \log N)$.
-/
lemma part1_bound_asymptotics : (fun (N : ℕ) => (N + 1 : ℝ) * (2 : ℝ) ^ (L_nat N)) =o[Filter.atTop] (fun (N : ℕ) => (N : ℝ) * Real.log N) := by
  -- Using the fact that $(N+1) * 2^{L(N)} \leq (N+1) * (\log N)^{\frac{\log 2}{2}}$ and $\frac{\log 2}{2} < 1$, we can show that $(N+1) * (\log N)^{\frac{\log 2}{2}} = o(N \log N)$.
  have h_exp : (fun N : ℕ => (N + 1 : ℝ) * (Real.log N) ^ (Real.log 2 / 2)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ) * Real.log N) := by
    -- We can factor out $N$ and use the fact that $(\log N)^{\frac{\log 2}{2}} / \log N$ tends to $0$ as $N$ tends to infinity.
    have h_factor : Filter.Tendsto (fun N : ℕ => (1 + 1 / (N : ℝ)) * (Real.log N) ^ (Real.log 2 / 2 - 1)) Filter.atTop (nhds 0) := by
      simpa using Filter.Tendsto.mul ( tendsto_const_nhds.add ( tendsto_inverse_atTop_nhds_zero_nat ) ) ( tendsto_rpow_neg_atTop ( show 0 < - ( Real.log 2 / 2 - 1 ) by linarith [ Real.log_lt_sub_one_of_pos zero_lt_two ( by norm_num ) ] ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    rw [ Asymptotics.isLittleO_iff_tendsto' ];
    · refine h_factor.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN;
      rw [ Real.rpow_sub_one ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hN ) ] ; ring_nf;
      simpa [ show N ≠ 0 by linarith ] using by ring;
    · filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN using by intro h; exact absurd h <| ne_of_gt <| mul_pos ( Nat.cast_pos.mpr <| pos_of_gt hN ) <| Real.log_pos <| Nat.one_lt_cast.mpr hN;
  -- Using the fact that $2^{L(N)} \leq (\log N)^{\frac{\log 2}{2}}$, we can bound the expression.
  have h_bound : ∀ N : ℕ, N ≥ 3 → (2 : ℝ) ^ L_nat N ≤ (Real.log N) ^ (Real.log 2 / 2) := by
    intro N hN
    have h_log : L_nat N ≤ Real.log (Real.log N) / 2 := by
      exact Nat.floor_le ( div_nonneg ( Real.log_nonneg ( Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( N : ℝ ) ≥ 3 by norm_cast ] ) ) ) ) zero_le_two );
    rw [ Real.le_rpow_iff_log_le ] <;> norm_num;
    · nlinarith [ Real.log_pos one_lt_two ];
    · exact Real.log_pos <| by norm_cast; linarith;
  rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> norm_num at *;
  · refine' squeeze_zero_norm' _ h_exp;
    filter_upwards [ Filter.eventually_ge_atTop 3 ] with N hN using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_left ( h_bound N hN ) ( by positivity ) ) ( by positivity ) ;
  · exact ⟨ 3, by intros; norm_cast at *; aesop ⟩;
  · exact ⟨ 3, by rintro N hN ( rfl | rfl | h ) <;> norm_cast at * ⟩

/-
$\frac{C_h}{\sqrt{L(N)}} \sum f(n) = o(N \log N)$.
-/
lemma part2_bound_asymptotics :
    (fun N => (C_h / Real.sqrt (L_nat N)) * ∑ n ∈ Finset.range (N + 1), f_func n) =o[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
      -- We know that $L(N) \to \infty$ as $N \to \infty$.
      have h_L_nat_tendsto : Filter.Tendsto L_nat Filter.atTop Filter.atTop := by
        exact L_nat_tendsto;
      -- We know that $\sum_{n \leq N} f(n) = O(N \log N)$ by `sum_2Omega_odd`.
      have h_sum_f_O : (fun N => ∑ n ∈ Finset.range (N + 1), f_func n) =O[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
        convert sum_2Omega_odd using 1;
      -- We know that $C_h / \sqrt{L(N)} \to 0$ as $N \to \infty$.
      have h_C_h_div_sqrt_L_nat_zero : Filter.Tendsto (fun N => C_h / Real.sqrt (L_nat N)) Filter.atTop (nhds 0) := by
        exact tendsto_const_nhds.div_atTop ( by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop.comp h_L_nat_tendsto );
      rw [ Asymptotics.isLittleO_iff_tendsto' ];
      · rw [ Asymptotics.isBigO_iff' ] at h_sum_f_O;
        obtain ⟨ c, hc₀, hc ⟩ := h_sum_f_O;
        refine' squeeze_zero_norm' _ _;
        use fun N => |C_h / Real.sqrt ( L_nat N )| * c;
        · filter_upwards [ hc, Filter.eventually_gt_atTop 1 ] with N hN hN' ; simp_all +decide [ abs_div ];
          rw [ div_le_iff₀ ( mul_pos ( by positivity ) ( abs_pos.mpr ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr hN' ) ) ) ) ) ] ; nlinarith [ show 0 ≤ |C_h| / |Real.sqrt ( L_nat N )| by positivity ];
        · simpa using Filter.Tendsto.mul ( h_C_h_div_sqrt_L_nat_zero.abs ) tendsto_const_nhds;
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN h using by rw [ show N = 0 by exact_mod_cast absurd h ( by exact ne_of_gt ( mul_pos ( Nat.cast_pos.mpr <| pos_of_gt hN ) <| Real.log_pos <| Nat.one_lt_cast.mpr hN ) ) ] ; norm_num;;

/-
The sum of $h(n)$ is $o(N \log N)$.
-/
lemma sum_central_binom_odd : (fun (N : ℕ) => ∑ n ∈ Finset.range (N + 1), h_func n) =o[Filter.atTop] (fun (N : ℕ) => (N : ℝ) * Real.log N) := by
  have h_split_sum : ∀ N : ℕ, (∑ n ∈ Finset.range (N + 1), h_func n) ≤ (∑ n ∈ (Finset.range (N + 1)).filter (λ n => Odd n ∧ Om n < L_nat N), h_func n) + (∑ n ∈ (Finset.range (N + 1)).filter (λ n => Odd n ∧ Om n ≥ L_nat N), h_func n) := by
    intro N
    have h_sum_split : ∑ n ∈ Finset.range (N + 1), h_func n ≤ ∑ n ∈ Finset.filter (fun n => Odd n) (Finset.range (N + 1)), h_func n := by
      rw [ Finset.sum_filter ];
      exact Finset.sum_le_sum fun x hx => by unfold h_func; aesop;
    have h_sum_split' : ∑ n ∈ Finset.filter (fun n => Odd n) (Finset.range (N + 1)), h_func n = ∑ n ∈ Finset.filter (fun n => Odd n ∧ Om n < L_nat N) (Finset.range (N + 1)), h_func n + ∑ n ∈ Finset.filter (fun n => Odd n ∧ Om n ≥ L_nat N) (Finset.range (N + 1)), h_func n := by
      rw [ ← Finset.sum_union ];
      · rcongr n ; by_cases hn : L_nat N ≤ Om n <;> aesop;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
    linarith [h_sum_split, h_sum_split'];
  have h_sum_lt : (fun N : ℕ => (N + 1 : ℝ) * (2 : ℝ) ^ (L_nat N)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ) * Real.log N) := by
    exact part1_bound_asymptotics

  have h_sum_ge : (fun N : ℕ => (C_h / Real.sqrt (L_nat N)) * ∑ n ∈ Finset.range (N + 1), f_func n) =o[Filter.atTop] (fun N : ℕ => (N : ℝ) * Real.log N) := by
    convert part2_bound_asymptotics using 1;
  have h_sum_bound : ∀ᶠ N in Filter.atTop, (∑ n ∈ Finset.range (N + 1), h_func n) ≤ (N + 1 : ℝ) * (2 : ℝ) ^ (L_nat N) + (C_h / Real.sqrt (L_nat N)) * ∑ n ∈ Finset.range (N + 1), f_func n := by
    filter_upwards [ Filter.eventually_ge_atTop 3, L_nat_ge_one ] with N hN₁ hN₂ using le_trans ( h_split_sum N ) ( add_le_add ( sum_h_lt_L_bound N ( L_nat N ) ) ( sum_h_ge_L_bound N ( L_nat N ) hN₂ ) ) |> le_trans <| by norm_num [ mul_assoc, mul_comm, mul_left_comm ] ;
  rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> norm_num at *;
  · refine' squeeze_zero_norm' _ ( by simpa using h_sum_lt.add h_sum_ge );
    field_simp;
    filter_upwards [ Filter.eventually_ge_atTop h_sum_bound.choose, Filter.eventually_gt_atTop 1 ] with n hn hn' using by rw [ Real.norm_of_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => by unfold h_func; positivity ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( Nat.one_le_cast.mpr hn'.le ) ) ) ) ] ; exact div_le_div_of_nonneg_right ( by simpa only [ div_mul_eq_mul_div ] using h_sum_bound.choose_spec n hn ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( Nat.one_le_cast.mpr hn'.le ) ) ) ;
  · exact ⟨ 2, by intros; norm_cast at *; aesop ⟩;
  · exact ⟨ 2, by intros; norm_cast at *; aesop ⟩;
  · exact ⟨ 2, by rintro N hN ( rfl | rfl | h ) <;> norm_cast at * ⟩

/-
There exists a constant $C_K$ such that for all $n$, the size of any union-free family is at most $C_K \binom{n}{\lfloor n/2 \rfloor}$.
-/
lemma kleitman_uniform : ∃ C_K : ℝ, C_K > 0 ∧ ∀ n, (MaxUnionFree n : ℝ) ≤ C_K * (n.choose (n / 2) : ℝ) := by
  -- By `erdos_447`, `MaxUnionFree n ~ binom n (n/2)`.
  have h_ratio : Filter.Tendsto (fun n : ℕ => (MaxUnionFree n : ℝ) / (n.choose (n / 2) : ℝ)) Filter.atTop (nhds 1) := by
    have := @erdos_447;
    rw [ Asymptotics.IsEquivalent ] at this;
    rw [ Asymptotics.isLittleO_iff_tendsto' ] at this <;> norm_num at *;
    · simpa using this.add_const 1 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ sub_div, div_self <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| Nat.div_le_self _ _ ] ; ring );
    · exact ⟨ 1, fun n hn hn' => absurd hn' <| ne_of_gt <| Nat.choose_pos <| Nat.div_le_self _ _ ⟩;
  -- A convergent sequence is bounded away from zero.
  obtain ⟨C_K, hC_K⟩ : ∃ C_K > 0, ∀ᶠ n in Filter.atTop, (MaxUnionFree n : ℝ) / (n.choose (n / 2)) ≤ C_K := by
    exact ⟨ 2, by norm_num, h_ratio.eventually ( ge_mem_nhds <| by norm_num ) ⟩;
  -- By combining the results for large and small n, we can conclude the existence of such a C_K.
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, (MaxUnionFree n : ℝ) / (n.choose (n / 2)) ≤ C_K := by
    exact Filter.eventually_atTop.mp hC_K.2;
  -- Let $C_K'$ be the maximum of $C_K$ and the maximum of $(MaxUnionFree n : ℝ) / (n.choose (n / 2))$ for $n < N$.
  obtain ⟨C_K', hC_K'⟩ : ∃ C_K' > 0, ∀ n < N, (MaxUnionFree n : ℝ) / (n.choose (n / 2)) ≤ C_K' := by
    have h_finite : Set.Finite (Set.image (fun n => (MaxUnionFree n : ℝ) / (n.choose (n / 2))) (Set.Iio N)) := by
      exact Set.Finite.image _ <| Set.finite_Iio N;
    exact ⟨ Max.max ( h_finite.bddAbove.choose + 1 ) 1, by positivity, fun n hn => le_trans ( h_finite.bddAbove.choose_spec <| Set.mem_image_of_mem _ hn ) <| le_max_of_le_left <| by linarith ⟩;
  use Max.max C_K C_K';
  exact ⟨ lt_max_of_lt_left hC_K.1, fun n => if hn : n < N then by have := hC_K'.2 n hn; rw [ div_le_iff₀ ( Nat.cast_pos.mpr <| Nat.choose_pos <| Nat.div_le_self _ _ ) ] at this; nlinarith [ le_max_right C_K C_K' ] else by have := hN n ( le_of_not_gt hn ) ; rw [ div_le_iff₀ ( Nat.cast_pos.mpr <| Nat.choose_pos <| Nat.div_le_self _ _ ) ] at this; nlinarith [ le_max_left C_K C_K' ] ⟩

/-
$I(N) = \sum_{a \in A, a \le N} |\{m \le N/a : m \text{ odd}\}|$.
-/
noncomputable def I_N (A : Set ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ (Finset.range (N + 1)).filter Odd, ((Nat.divisors n).filter (· ∈ A)).card

lemma I_N_equality (A : Set ℕ) (hA_odd : ∀ a ∈ A, Odd a) (N : ℕ) :
  I_N A N = ∑ a ∈ (Finset.range (N + 1)).filter (· ∈ A), ((Finset.range (N / a + 1)).filter Odd).card := by
    unfold I_N;
    simp +decide only [Finset.card_filter, Finset.sum_filter];
    -- By interchanging the order of summation, we can rewrite the left-hand side.
    have h_interchange : ∑ a ∈ Finset.range (N + 1), (if Odd a then ∑ i ∈ Nat.divisors a, if i ∈ A then 1 else 0 else 0) = ∑ i ∈ Finset.filter (fun i => i ∈ A) (Finset.range (N + 1)), ∑ a ∈ Finset.filter (fun a => Odd a) (Finset.range (N + 1)), (if i ∣ a then 1 else 0) := by
      simp +decide only [Finset.sum_filter, ← Finset.sum_product'];
      rw [ Finset.sum_product, Finset.sum_comm ];
      refine' Finset.sum_congr rfl fun y hy => _;
      split_ifs <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
      congr 1 with x ; simp +decide [ Nat.dvd_iff_mod_eq_zero ];
      exact ⟨ fun h => ⟨ ⟨ Nat.lt_succ_of_le ( Nat.le_trans ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop ) ) ( Nat.dvd_of_mod_eq_zero h.1.1 ) ) ( Nat.le_of_lt_succ hy ) ), h.2 ⟩, h.1.1 ⟩, fun h => ⟨ ⟨ h.2, by aesop ⟩, h.1.2 ⟩ ⟩;
    rw [ h_interchange, Finset.sum_filter ];
    refine' Finset.sum_congr rfl fun x hx => _;
    split_ifs <;> simp_all +decide
    refine' Finset.card_bij ( fun y hy => y / x ) _ _ _ <;> simp_all +decide
    · intro a ha₁ ha₂ ha₃; rw [ Nat.div_lt_iff_lt_mul <| Nat.pos_of_dvd_of_pos ha₃ <| Nat.pos_of_ne_zero <| by aesop ] ;
      exact ⟨ by nlinarith [ Nat.div_add_mod N x, Nat.mod_lt N ( Nat.pos_of_dvd_of_pos ha₃ ( Nat.pos_of_ne_zero ( by aesop ) ) ) ], by exact ha₂.of_dvd_nat ( Nat.div_dvd_of_dvd ha₃ ) ⟩;
    · exact fun b hb hb_odd => ⟨ x * b, ⟨ ⟨ by nlinarith [ Nat.div_mul_le_self N x ], by simp [ *, parity_simps ] ⟩, by simp +decide ⟩, by rw [ Nat.mul_div_cancel_left _ ( Nat.pos_of_ne_zero ( by specialize hA_odd x ‹_›; aesop ) ) ] ⟩

/-
$I(N) \ge \sum_{a \in A, a \le N} (\frac{N}{2a} - 1)$.
-/
lemma I_N_lower_bound (A : Set ℕ) (hA_odd : ∀ a ∈ A, Odd a) (N : ℕ) :
  (I_N A N : ℝ) ≥ ∑ a ∈ (Finset.range (N + 1)).filter (· ∈ A), ((N / a : ℝ) / 2 - 1) := by
    -- By definition of $I_N$, we have $I_N(A, N) = \sum_{a \in A, a \le N} |\{m \le N/a : m \text{ odd}\}|$.
    have h_I_N_def : (I_N A N : ℝ) = ∑ a ∈ (Finset.range (N + 1)).filter (· ∈ A), ((Finset.range (N / a + 1)).filter Odd).card := by
      convert congr_arg _ ( I_N_equality A hA_odd N ) using 1;
    rw [h_I_N_def];
    push_cast [ Finset.sum_div _ _ _ ];
    gcongr;
    field_simp;
    rename_i a ha;
    refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr <| show Finset.card ( Finset.filter Odd ( Finset.range ( N / a + 1 ) ) ) ≥ N / a / 2 from _ ) zero_le_two );
    · rw [ div_sub', div_le_iff₀ ] <;> norm_cast <;> norm_num at *;
      · norm_cast; nlinarith [ Nat.div_add_mod N a, Nat.mod_lt N ( Nat.pos_of_ne_zero ( by specialize hA_odd a ha.2; aesop : a ≠ 0 ) ), Nat.div_add_mod ( N / a ) 2, Nat.mod_lt ( N / a ) two_pos ] ;
      · exact Nat.pos_of_ne_zero fun h => by simpa [ h ] using hA_odd a ha.2;
      · exact Nat.ne_of_gt ( Nat.pos_of_ne_zero fun h => by simpa [ h ] using hA_odd a ha.2 );
    · refine' le_trans _ ( Finset.card_mono <| show Finset.image ( fun x => 2 * x + 1 ) ( Finset.range ( N / a / 2 ) ) ⊆ Finset.filter Odd ( Finset.range ( N / a + 1 ) ) from _ );
      · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      · grind

/-
Let $C_K$ be the constant from Kleitman's uniform bound.
-/
noncomputable def C_K_val : ℝ := kleitman_uniform.choose

lemma C_K_pos : C_K_val > 0 := kleitman_uniform.choose_spec.1

lemma MaxUnionFree_le_C_K (n : ℕ) : (MaxUnionFree n : ℝ) ≤ C_K_val * (n.choose (n / 2) : ℝ) := kleitman_uniform.choose_spec.2 n

set_option maxHeartbeats 1000000 in
/-
If $A$ is lcm-triple free, then $|A \cap \Div(n)| \le \text{MaxUnionFree}(\Omega(n))$.
-/
lemma card_A_cap_Div_le_MaxUnionFree (A : Set ℕ)
  (h_lcm_free : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → b ≠ c → a ≠ c → Nat.lcm a b ≠ c)
  (n : ℕ) (hn : n ≠ 0) :
  ((Nat.divisors n).filter (· ∈ A)).card ≤ MaxUnionFree (Om n) := by
    -- Since $A \cap \Div(n)$ is lcm-triple-free, the family of subsets $\{\Phi_n(d) \mid d \in A \cap \Div(n)\}$ is union-free.
    have h_union_free : UnionFree (Finset.image (fun d => Phi_n n d) (Nat.divisors n ∩ Finset.filter (· ∈ A) (Finset.range (n + 1)))) := by
      convert lcmfree_to_unionfree A h_lcm_free n hn using 1;
      ext; simp [Finset.mem_image];
      exact ⟨ fun ⟨ a, ha, ha' ⟩ => ⟨ a, ⟨ ⟨ ha.1.1, ha.1.2 ⟩, ha.2.2 ⟩, ha' ⟩, fun ⟨ a, ha, ha' ⟩ => ⟨ a, ⟨ ⟨ ha.1.1, ha.1.2 ⟩, Nat.lt_succ_of_le ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hn ) ha.1.1 ), ha.2 ⟩, ha' ⟩ ⟩;
    -- Since $\Phi_n$ is injective, the cardinality of the image of $A \cap \Div(n)$ under $\Phi_n$ is equal to the cardinality of $A \cap \Div(n)$.
    have h_card_eq : (Finset.image (fun d => Phi_n n d) (Nat.divisors n ∩ Finset.filter (· ∈ A) (Finset.range (n + 1)))).card = ((Nat.divisors n).filter (· ∈ A)).card := by
      have h_inj : ∀ d1 d2, d1 ∈ Nat.divisors n → d2 ∈ Nat.divisors n → Phi_n n d1 = Phi_n n d2 → d1 = d2 := by
        intros d1 d2 hd1 hd2 h_eq
        have := divisors_to_subsets n hn
        aesop;
      rw [ Finset.card_image_of_injOn fun x hx y hy hxy => h_inj x y ( by aesop ) ( by aesop ) hxy ];
      congr 1 with x ; simp +decide [ Nat.lt_succ_iff ];
      exact fun hx _ hx' => Nat.le_of_dvd ( Nat.pos_of_ne_zero hn ) hx;
    refine' h_card_eq ▸ _;
    -- Since the image of the divisors under Phi_n is a union-free family, its cardinality is bounded by the maximum size of a union-free family on a set of size Om n.
    have h_card_le_max : ∀ (F : Finset (Finset ((p : ℕ) × ℕ))), F ⊆ Finset.powerset (Un n) → UnionFree F → F.card ≤ MaxUnionFree (Om n) := by
      intros F hF_sub hF_union_free
      have h_card_le_max : F.card ≤ MaxUnionFree (Om n) := by
        have h_card_le_max : ∃ (f : Fin (Om n) → ((p : ℕ) × ℕ)), Finset.image f Finset.univ = Un n := by
          have h_card_le_max : Finset.card (Un n) = Om n := by
            unfold Un Om; aesop;
          have h_card_le_max : Nonempty (Fin (Om n) ≃ Un n) := by
            exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ h_card_le_max ] ⟩;
          obtain ⟨ f ⟩ := h_card_le_max;
          use fun i => f i |>.1;
          ext x; simp [Finset.mem_image];
          exact ⟨ fun ⟨ a, ha ⟩ => ha ▸ Subtype.mem _, fun hx => ⟨ f.symm ⟨ x, hx ⟩, by simp +decide ⟩ ⟩
        obtain ⟨f, hf⟩ := h_card_le_max;
        have h_card_le_max : ∃ (F' : Finset (Finset (Fin (Om n)))), F'.card = F.card ∧ UnionFree F' := by
          use Finset.image (fun s => Finset.filter (fun i => f i ∈ s) Finset.univ) F;
          rw [ Finset.card_image_of_injOn ];
          · simp_all +decide [ Finset.subset_iff, UnionFree ];
            intro A hA B hB C hC hAB hBC hAC h_union; specialize hF_union_free A hA B hB C hC; simp_all +decide [ Finset.ext_iff ] ;
            grind;
          · intro s hs t ht h_eq; simp_all +decide [ Finset.ext_iff ] ;
            grind;
        obtain ⟨F', hF'_card, hF'_union_free⟩ := h_card_le_max;
        exact (by
        exact hF'_card ▸ Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hF'_union_free ⟩ ) |> le_trans <| by unfold MaxUnionFree; aesop;);
      exact h_card_le_max;
    apply h_card_le_max _ ?_ h_union_free;
    exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_powerset.mpr <| divisors_to_subsets n hn |>.1 x <| Nat.dvd_of_mem_divisors <| Finset.mem_filter.mp hx |>.1 |> fun h => by aesop;

/-
If $A$ is lcm-triple free, then $I(N) \le C_K \sum_{n \le N} h(n)$.
-/
lemma I_N_upper_bound_explicit (A : Set ℕ)
  (h_lcm_free : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → b ≠ c → a ≠ c → Nat.lcm a b ≠ c)
  (N : ℕ) :
  (I_N A N : ℝ) ≤ C_K_val * ∑ n ∈ Finset.range (N + 1), h_func n := by
    -- By definition of $I_N$, we have $I_N(A, N) = \sum_{n \le N, n \text{ odd}} |\{m \le N/n : m \text{ odd}\}|$.
    have h_I_N_def : I_N A N = ∑ n ∈ (Finset.range (N + 1)).filter Odd, ((Nat.divisors n).filter (· ∈ A)).card := by
      rfl;
    -- By definition of $h_func$, we have $|A \cap \Div(n)| \le C_K h(n)$ for all odd $n$.
    have h_card_le_C_K_h : ∀ n ∈ (Finset.range (N + 1)).filter Odd, ((Nat.divisors n).filter (· ∈ A)).card ≤ C_K_val * h_func n := by
      intros n hn_odd
      have h_card_le_C_K_h : ((Nat.divisors n).filter (· ∈ A)).card ≤ C_K_val * (Nat.choose (Om n) ((Om n) / 2) : ℝ) := by
        have h_card_le_C_K_h : ((Nat.divisors n).filter (· ∈ A)).card ≤ MaxUnionFree (Om n) := by
          by_cases hn : n = 0 <;> simp_all +decide [ card_A_cap_Div_le_MaxUnionFree ];
        exact le_trans ( Nat.cast_le.mpr h_card_le_C_K_h ) ( MaxUnionFree_le_C_K _ );
      unfold h_func; aesop;
    rw [ h_I_N_def, Finset.mul_sum _ _ _ ] ; exact le_trans ( mod_cast Finset.sum_le_sum fun n hn => h_card_le_C_K_h n <| by aesop ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( le_of_lt <| C_K_pos ) <| by unfold h_func; positivity ) ;

/-
If $A$ is lcm-triple free, then $I(N) = o(N \log N)$.
-/
lemma I_N_upper_bound_asymptotic (A : Set ℕ)
  (h_lcm_free : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → b ≠ c → a ≠ c → Nat.lcm a b ≠ c) :
  (fun N => (I_N A N : ℝ)) =o[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
    -- By `I_N_upper_bound_explicit`, $I(N) \le C_K \sum_{n \le N} h(n)$.
    have h_upper_bound : ∀ N : ℕ, (I_N A N : ℝ) ≤ C_K_val * ∑ n ∈ Finset.range (N + 1), h_func n := by
      exact fun N => I_N_upper_bound_explicit A h_lcm_free N;
    have h_sum_h_asymptotic : (fun N => C_K_val * ∑ n ∈ Finset.range (N + 1), h_func n) =o[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
      have h_sum_h_asymptotic : (fun N => ∑ n ∈ Finset.range (N + 1), h_func n) =o[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
        convert sum_central_binom_odd using 1;
      exact h_sum_h_asymptotic.const_mul_left _;
    rw [ Asymptotics.isLittleO_iff ] at *;
    intro c hc; filter_upwards [ h_sum_h_asymptotic hc ] with N hN; rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ) ] ; exact le_trans ( h_upper_bound N ) ( le_trans ( le_abs_self _ ) hN ) ;

/-
$H_A(N) = \sum_{a \in A, a \le N} 1/a$.
-/
noncomputable def log_density_sum (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ a ∈ (Finset.range (N + 1)).filter (· ∈ A), (1 : ℝ) / a

/-
Definitions of upper and lower logarithmic density.
-/
noncomputable def upper_log_density (A : Set ℕ) : ℝ :=
  (Filter.atTop).limsup (fun N => log_density_sum A N / Real.log N)

noncomputable def lower_log_density (A : Set ℕ) : ℝ :=
  (Filter.atTop).liminf (fun N => log_density_sum A N / Real.log N)

/-
If a set has positive lower density, it has positive lower logarithmic density.
-/
lemma lower_log_density_pos (A : Set ℕ) (hA : lowerDensity A > 0) :
    lower_log_density A > 0 := by
      -- By `harmonic_lower_bound`, there exists $c > 0$ such that for large $N$, $\sum_{a \in A, a \le N} 1/a \ge c \log N$.
      obtain ⟨c, hc_pos, hc⟩ : ∃ c > 0, ∀ᶠ N in Filter.atTop, log_density_sum A N ≥ c * Real.log N := by
        obtain ⟨N0, c, hc_pos, hc⟩ : ∃ N0 c, c > 0 ∧ ∀ N ≥ N0, ∑ a ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / a ≥ c * Real.log N := by
          convert harmonic_lower_bound A hA using 1;
        refine' ⟨ c, hc_pos, Filter.eventually_atTop.mpr ⟨ N0 + 1, fun N hN => le_trans ( hc N ( by linarith ) ) _ ⟩ ⟩;
        refine' Finset.sum_le_sum_of_subset_of_nonneg _ _;
        · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ] ), Finset.mem_filter.mp hx |>.2 ⟩;
        · exact fun _ _ _ => by positivity;
      refine' lt_of_lt_of_le ( half_pos hc_pos ) _;
      refine' le_csSup _ _ <;> norm_num;
      · use 1 + ∑ a ∈ Finset.range ( Nat.succ 1 ), ( 1 : ℝ ) / a + 1;
        rintro x ⟨ N, hN ⟩ ; specialize hN ( N + 2 ) ( by linarith ) ; norm_num [ Finset.sum_range_succ ] at *;
        refine le_trans hN ?_;
        refine' div_le_of_le_mul₀ _ _ _ <;> norm_num;
        · exact Real.log_nonneg ( by linarith );
        · refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => by positivity ) _;
          induction' N with N ih <;> norm_num [ Finset.sum_range_succ ] at *;
          · have := Real.log_two_gt_d9 ; norm_num at * ; linarith;
          · refine' le_trans ( add_le_add_right ( show ∑ x ∈ Finset.range N, ( x : ℝ ) ⁻¹ + ( N : ℝ ) ⁻¹ + ( N + 1 : ℝ ) ⁻¹ + ( N + 2 : ℝ ) ⁻¹ ≤ 3 * Real.log ( N + 2 ) from _ ) _ ) _;
            · refine' Nat.recOn N _ _ <;> norm_num [ Finset.sum_range_succ ] at *;
              · have := Real.log_two_gt_d9 ; norm_num at * ; linarith;
              · intro n hn; rw [ show ( n : ℝ ) + 1 + 2 = ( n + 2 ) * ( 1 + 1 / ( n + 2 ) ) by rw [ mul_add, mul_div_cancel₀ _ ( by positivity ) ] ; ring ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; ring_nf at *;
                refine' add_le_add hn _;
                rw [ inv_eq_one_div, div_le_iff₀ ] <;> nlinarith only [ Real.log_inv ( 1 + ( 2 + n : ℝ ) ⁻¹ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( 1 + ( 2 + n : ℝ ) ⁻¹ ) ) ), Real.log_le_sub_one_of_pos ( by positivity : 0 < ( 1 + ( 2 + n : ℝ ) ⁻¹ ) ), inv_pos.mpr ( by positivity : 0 < ( 1 + ( 2 + n : ℝ ) ⁻¹ ) ), mul_inv_cancel₀ ( by positivity : ( 1 + ( 2 + n : ℝ ) ⁻¹ ) ≠ 0 ), inv_pos.mpr ( by positivity : 0 < ( 2 + n : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( 2 + n : ℝ ) ≠ 0 ) ];
            · rw [ show ( N + 1 + 2 : ℝ ) = ( N + 2 ) * ( 1 + 1 / ( N + 2 ) ) by rw [ mul_add, mul_div_cancel₀ _ ( by linarith ) ] ; ring, Real.log_mul ( by linarith ) ( by positivity ) ] ; ring_nf ; norm_num;
              nlinarith [ Real.log_inv ( 1 + ( 2 + N : ℝ ) ⁻¹ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( 1 + ( 2 + N : ℝ ) ⁻¹ ) ) ), inv_mul_cancel₀ ( by positivity : ( 1 + ( 2 + N : ℝ ) ⁻¹ ) ≠ 0 ), inv_pos.mpr ( by positivity : 0 < ( 2 + N : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( 2 + N : ℝ ) ≠ 0 ), inv_pos.mpr ( by positivity : 0 < ( 3 + N : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( 3 + N : ℝ ) ≠ 0 ) ];
      · exact Filter.eventually_atTop.mp ( hc.and ( Filter.eventually_gt_atTop 1 ) ) |> fun ⟨ N, hN ⟩ => ⟨ N + 2, fun n hn => by rw [ le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) ] ; nlinarith [ hN n ( by linarith ), Real.log_nonneg <| show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] ⟩

/-
The number of integers $n \in \{1, \dots, N\}$ such that $v_2(n) \ge T$ is at most $N/2^T$.
-/
lemma card_v2_ge_T (N T : ℕ) : ((Finset.Icc 1 N).filter (fun n => T ≤ v2 n)).card ≤ N / 2^T := by
  -- The set of numbers with $v_2(n) \geq T$ is exactly the set of multiples of $2^T$ in $\{1, \dots, N\}$.
  have h_mult : Finset.filter (fun n => T ≤ v2 n) (Finset.Icc 1 N) ⊆ Finset.image (fun m => 2^T * m) (Finset.Icc 1 (N / 2^T)) := by
    intro n hnaesop;
    -- Since $T \leq v2 n$, we have $2^T \mid n$.
    have h_div : 2 ^ T ∣ n := by
      exact dvd_trans ( pow_dvd_pow _ ( Finset.mem_filter.mp hnaesop |>.2 ) ) ( Nat.ordProj_dvd _ _ );
    exact Finset.mem_image.mpr ⟨ n / 2 ^ T, Finset.mem_Icc.mpr ⟨ Nat.div_pos ( Nat.le_of_dvd ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hnaesop |>.1 ) |>.1 ) h_div ) ( pow_pos ( by decide ) _ ), Nat.div_le_div_right ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hnaesop |>.1 ) |>.2 ) ⟩, by rw [ Nat.mul_div_cancel' h_div ] ⟩;
  exact le_trans ( Finset.card_le_card h_mult ) ( Finset.card_image_le.trans ( by simp ) )

/-
If the counting function of A is at least the counting function of B minus C*N, then the lower density of A is at least the lower density of B minus C.
-/
lemma lowerDensity_diff_bound (A B : Set ℕ) (C : ℝ)
    (h : ∀ N ≥ 1, ((Finset.Icc 1 N).filter (· ∈ A)).card ≥ ((Finset.Icc 1 N).filter (· ∈ B)).card - C * N) :
    lowerDensity A ≥ lowerDensity B - C := by
      -- Then $\frac{|A \cap [1,N]|}{N} \ge \frac{|B \cap [1,N]|}{N} - C$.
      have h_ineq : ∀ N ≥ 1, ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ) ≥ ((Finset.Icc 1 N).filter (· ∈ B)).card / (N : ℝ) - C := by
        intro N hN; rw [ ge_iff_le ] ; rw [ div_sub', div_le_div_iff_of_pos_right ] <;> first | positivity | linarith [ h N hN ] ;
      -- Taking liminf: $\underline{d}(A) \ge \underline{d}(B) - C$.
      have h_liminf : Filter.liminf (fun N => ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ)) Filter.atTop ≥ Filter.liminf (fun N => ((Finset.Icc 1 N).filter (· ∈ B)).card / (N : ℝ)) Filter.atTop - C := by
        rw [ Filter.liminf_eq, Filter.liminf_eq ];
        refine' sub_le_iff_le_add.mpr ( csSup_le _ _ );
        · exact ⟨ 0, Filter.eventually_atTop.mpr ⟨ 1, fun N hN => by positivity ⟩ ⟩;
        · intro b hb;
          refine' le_trans _ ( add_le_add_right ( le_csSup _ <| show b - C ∈ _ from _ ) _ );
          · linarith;
          · exact ⟨ 1, fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ N, hN ⟩ ; exact le_trans ( hN _ le_rfl ) ( div_le_one_of_le₀ ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num ) ) ( by positivity ) ) ⟩;
          · filter_upwards [ hb, Filter.eventually_ge_atTop 1 ] with n hn hn' using by linarith [ h_ineq n hn' ] ;
      convert h_liminf using 1

/-
The lower density of the union of A_t for t < T is at least the lower density of A minus 1/2^T.
-/
lemma lowerDensity_union_At_ge (A : Set ℕ) (T : ℕ) :
    lowerDensity (⋃ t ∈ Finset.range T, At A t) ≥ lowerDensity A - (1 / 2 ^ T : ℝ) := by
      convert lowerDensity_diff_bound _ _ ( 1 / 2 ^ T ) _ using 1;
      intro N hN
      have h_card_diff : ((Finset.Icc 1 N).filter (· ∈ A)).card ≤ ((Finset.Icc 1 N).filter (· ∈ ⋃ t ∈ Finset.range T, At A t)).card + ((Finset.Icc 1 N).filter (fun n => T ≤ v2 n)).card := by
        have h_card_ge : ((Finset.Icc 1 N).filter (· ∈ A)).card ≤ ((Finset.Icc 1 N).filter (fun n => n ∈ A ∧ v2 n < T)).card + ((Finset.Icc 1 N).filter (fun n => n ∈ A ∧ T ≤ v2 n)).card := by
          rw [ ← Finset.card_union_of_disjoint ];
          · exact Finset.card_mono fun x hx => by by_cases h : v2 x < T <;> aesop;
          · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
        refine le_trans h_card_ge ?_;
        gcongr;
        · intro n hn; simp_all +decide [ At ] ;
        · exact fun x hx => hx.2;
      -- By definition of $At$, we know that $|(A \setminus S) \cap \{1,\dots,N\}| \le |\{n \le N \mid v_2(n) \ge T\}| \le N/2^T$.
      have h_card_diff_le : ((Finset.Icc 1 N).filter (fun n => T ≤ v2 n)).card ≤ N / 2 ^ T := by
        exact card_v2_ge_T N T;
      field_simp;
      rw [ sub_le_iff_le_add ] ; norm_cast ; nlinarith [ Nat.div_mul_le_self N ( 2 ^ T ), pow_pos ( zero_lt_two' ℕ ) T ] ;

/-
If A has positive lower density, there exists T such that the union of A_t for t < T has positive lower density.
-/
lemma exists_T_union_pos (A : Set ℕ) (hA : lowerDensity A > 0) :
    ∃ T, lowerDensity (⋃ t ∈ Finset.range T, At A t) > 0 := by
      obtain ⟨T, hT⟩ : ∃ T : ℕ, (1 / 2 ^ T : ℝ) < lowerDensity A := by
        simpa using exists_pow_lt_of_lt_one hA one_half_lt_one
      generalize_proofs at *; (exact ⟨ T, by
        have := lowerDensity_union_At_ge A T; norm_num at *; linarith; ⟩ )

set_option maxHeartbeats 1000000 in
/-
Upper logarithmic density is finitely subadditive.
-/
lemma upper_log_density_subadd {ι : Type*} (s : Finset ι) (f : ι → Set ℕ) :
    upper_log_density (⋃ i ∈ s, f i) ≤ ∑ i ∈ s, upper_log_density (f i) := by
      unfold upper_log_density;
      -- The logarithmic density sum is subadditive: $S_{\cup A_i}(N) \le \sum S_{A_i}(N)$.
      have h_subadd : ∀ N, log_density_sum (⋃ i ∈ s, f i) N ≤ ∑ i ∈ s, log_density_sum (f i) N := by
        intro N;
        induction s using Finset.induction <;> simp_all +decide [ log_density_sum ];
        refine' le_trans _ ( add_le_add_left ‹_› _ );
        rw [ ← Finset.sum_union_inter ];
        exact le_add_of_le_of_nonneg ( Finset.sum_le_sum_of_subset_of_nonneg ( fun x hx => by aesop ) fun _ _ _ => by positivity ) ( Finset.sum_nonneg fun _ _ => by positivity );
      by_cases h : ∀ i ∈ s, Filter.IsBoundedUnder ( · ≤ · ) Filter.atTop ( fun N => log_density_sum ( f i ) N / Real.log N ) <;> simp_all +decide [ Filter.limsup_eq];
      · -- Since the logarithmic density sum is subadditive, we can apply the fact that the limsup of a sum is less than or equal to the sum of the limsups.
        have h_limsup_subadd : ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, log_density_sum (⋃ i ∈ s, f i) N / Real.log N ≤ ∑ i ∈ s, (sInf {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → log_density_sum (f i) b / Real.log ↑b ≤ a} + ε / s.card) := by
          intro ε ε_pos
          have h_limsup_subadd : ∀ i ∈ s, ∃ N₀, ∀ N ≥ N₀, log_density_sum (f i) N / Real.log N ≤ sInf {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → log_density_sum (f i) b / Real.log ↑b ≤ a} + ε / s.card := by
            intro i hi;
            have := exists_lt_of_csInf_lt ( show { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → log_density_sum ( f i ) b / Real.log b ≤ a }.Nonempty from ?_ ) ( show sInf { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → log_density_sum ( f i ) b / Real.log b ≤ a } < sInf { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → log_density_sum ( f i ) b / Real.log b ≤ a } + ε / s.card from lt_add_of_pos_right _ ( div_pos ε_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ i, hi ⟩ ) ) ) );
            · rcases this with ⟨ a, ⟨ N₀, hN₀ ⟩, ha ⟩ ; exact ⟨ N₀, fun N hN => le_trans ( hN₀ N hN ) ha.le ⟩ ;
            · obtain ⟨ M, hM ⟩ := h i hi;
              exact ⟨ M, by rcases Filter.eventually_atTop.mp hM with ⟨ N, hN ⟩ ; exact ⟨ ⌈N⌉₊, fun n hn => hN n <| Nat.le_of_ceil_le hn ⟩ ⟩;
          choose! N₀ hN₀ using h_limsup_subadd;
          use Finset.sup s N₀ + 2;
          intro N hN
          have h_sum : log_density_sum (⋃ i ∈ s, f i) N / Real.log N ≤ ∑ i ∈ s, log_density_sum (f i) N / Real.log N := by
            rw [ ← Finset.sum_div _ _ _ ] ; gcongr ; aesop;
          exact h_sum.trans ( Finset.sum_le_sum fun i hi => hN₀ i hi N ( by linarith [ Finset.le_sup ( f := N₀ ) hi ] ) );
        refine' le_of_forall_pos_le_add fun ε εpos => _;
        rcases h_limsup_subadd ε εpos with ⟨ N₀, hN₀ ⟩ ; refine' csInf_le _ _;
        · exact ⟨ 0, by rintro x ⟨ N, hN ⟩ ; exact le_trans ( div_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( Real.log_natCast_nonneg _ ) ) ( hN _ le_rfl ) ⟩;
        · use N₀; intro N hN; specialize hN₀ N hN; simp_all +decide [ Finset.sum_add_distrib ] ;
          by_cases hs : s = ∅ <;> simp_all +decide [ mul_div_cancel₀ ];
          exact le_trans hN₀ εpos.le;
      · rw [ Real.sInf_def ];
        rw [ Real.sSup_def ];
        split_ifs <;> simp_all +decide [ not_le, IsBoundedUnder, IsBounded ];
        · obtain ⟨ x, hx₁, hx₂ ⟩ := h;
          contrapose! hx₂;
          obtain ⟨ M, hM ⟩ := ‹ ( - { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → log_density_sum ( ⋃ i ∈ s, f i ) b / Real.log b ≤ a } ).Nonempty ∧ BddAbove ( - { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → log_density_sum ( ⋃ i ∈ s, f i ) b / Real.log b ≤ a } ) ›.1;
          obtain ⟨ N, hN ⟩ := hM;
          use -M, N + 1;
          intro n hn;
          refine' le_trans _ ( hN n ( by linarith ) );
          gcongr;
          refine' Finset.sum_le_sum_of_subset_of_nonneg _ _;
          · simp +contextual [ Finset.subset_iff ];
            exact fun i hi hi' => ⟨ x, hx₁, hi' ⟩;
          · exact fun _ _ _ => by positivity;
        · exact Finset.sum_nonneg fun i _ => by apply_rules [ Real.sInf_nonneg ] ; rintro x ⟨ N, hN ⟩ ; exact le_trans ( div_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( Real.log_natCast_nonneg _ ) ) ( hN _ le_rfl ) ;

theorem helper2 (a b : ℕ) : Finset.Ico a b.succ = Finset.Icc a b := by
  simp_all only [Nat.succ_eq_add_one]
  rfl

/-
Relation between logarithmic density sums of A_t and B_t.
-/
lemma log_density_sum_Bt_relation (A : Set ℕ) (t N : ℕ) :
    log_density_sum (At A t) N = (1 / 2 ^ t : ℝ) * log_density_sum (Bt A t) (N / 2 ^ t) := by
      -- By definition of $At$ and $Bt$, we can rewrite the left-hand side of the equation.
      have h_rewrite : log_density_sum (At A t) N = ∑ a ∈ (Finset.Icc 1 N).filter (fun a => v2 a = t ∧ a ∈ A), (1 : ℝ) / a := by
        unfold log_density_sum At;
        rw [ Finset.range_eq_Ico, helper2 ];
        simp +decide [ and_comm, Finset.sum_filter ];
        rw [ Finset.Icc_eq_cons_Ioc, Finset.sum_cons ] <;> aesop;
      -- Let's rewrite the sum over $B_t$ in terms of the sum over $A_t$.
      have h_rewrite_Bt : ∑ b ∈ (Finset.Icc 1 (N / 2^t)).filter (fun b => Odd b ∧ ∃ a ∈ A, v2 a = t ∧ a = 2^t * b), (1 : ℝ) / b = ∑ a ∈ (Finset.Icc 1 N).filter (fun a => v2 a = t ∧ a ∈ A), (2^t : ℝ) / a := by
        apply Finset.sum_bij (fun b hb => 2^t * b);
        · simp +zetaDelta at *;
          exact fun a ha₁ ha₂ ha₃ ha₄ ha₅ => ⟨ ⟨ Nat.mul_pos ( pow_pos ( by decide ) _ ) ha₁, by nlinarith [ Nat.div_mul_le_self N ( 2 ^ t ), pow_pos ( by decide : 0 < 2 ) t ] ⟩, ha₅, ha₄ ⟩;
        · aesop;
        · intro b hb
          obtain ⟨hb_range, hb_prop⟩ := Finset.mem_filter.mp hb
          obtain ⟨hb_v2, hb_A⟩ := hb_prop
          have hb_div : b % 2^t = 0 := by
            exact Nat.mod_eq_zero_of_dvd <| hb_v2 ▸ Nat.ordProj_dvd _ _
          have hb_odd : Odd (b / 2^t) := by
            have hb_odd : ¬(2 ∣ b / 2^t) := by
              rw [ Nat.dvd_div_iff_mul_dvd ];
              · rw [ ← hb_v2 ] ; exact Nat.pow_succ_factorization_not_dvd ( by linarith [ Finset.mem_Icc.mp hb_range ] ) Nat.prime_two;
              · exact Nat.dvd_of_mod_eq_zero hb_div;
            simpa [ ← even_iff_two_dvd ] using hb_odd
          have hb_lt : b / 2^t ≤ N / 2^t := by
            exact Nat.div_le_div_right ( Finset.mem_Icc.mp hb_range |>.2 )
          use b / 2^t
          simp [hb_odd, hb_lt];
          exact ⟨ ⟨ Nat.div_pos ( Nat.le_of_dvd ( Finset.mem_Icc.mp hb_range |>.1 ) ( Nat.dvd_of_mod_eq_zero hb_div ) ) ( pow_pos ( by decide ) _ ), by rwa [ Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero hb_div ) ], by rw [ Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero hb_div ) ] ; exact hb_v2 ⟩, Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero hb_div ) ⟩;
        · simp +contextual [ div_eq_mul_inv, mul_comm, mul_left_comm ];
      -- By definition of $Bt$, we can rewrite the left-hand side of the equation.
      have h_rewrite_Bt : log_density_sum (Bt A t) (N / 2^t) = ∑ b ∈ (Finset.Icc 1 (N / 2^t)).filter (fun b => Odd b ∧ ∃ a ∈ A, v2 a = t ∧ a = 2^t * b), (1 : ℝ) / b := by
        have h_rewrite_Bt : Finset.filter (fun b => b ∈ Bt A t) (Finset.Icc 1 (N / 2^t)) = Finset.filter (fun b => Odd b ∧ ∃ a ∈ A, v2 a = t ∧ a = 2^t * b) (Finset.Icc 1 (N / 2^t)) := by
          ext; simp [Bt, At];
          intro _ _; constructor <;> intro h <;> rcases h with ⟨ x, hx₁, hx₂ ⟩ <;> simp_all +decide
          · rw [ ← hx₂, Nat.mul_div_cancel' ];
            · have h_odd : ¬(2 ∣ x / 2 ^ t) := by
                rw [ Nat.Prime.dvd_iff_one_le_factorization ] <;> norm_num;
                · rw [ Nat.factorization_div ] <;> norm_num;
                  · exact Nat.sub_eq_zero_of_le ( hx₁.2 ▸ Nat.le_refl _ );
                  · exact hx₁.2 ▸ Nat.ordProj_dvd _ _;
                · exact Nat.le_of_not_lt fun h => by rw [ Nat.div_eq_of_lt h ] at hx₂; linarith;
              exact ⟨ Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => h_odd <| Nat.dvd_of_mod_eq_zero h ), hx₁ ⟩;
            · exact hx₁.2 ▸ Nat.ordProj_dvd _ _;
          · exact ⟨ _, ⟨ hx₁, hx₂ ⟩, Nat.mul_div_cancel_left _ ( pow_pos ( by decide ) _ ) ⟩;
        convert congr_arg ( fun s : Finset ℕ => ∑ b ∈ s, ( 1 : ℝ ) / b ) h_rewrite_Bt using 1;
        unfold log_density_sum;
        erw [ Finset.sum_filter, Finset.sum_filter ] ; erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ] ;
      simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ]

/-
The limsup of a stretched sequence is equal to the limsup of the original sequence.
-/
lemma limsup_stretch {α : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    (u : ℕ → α) (k : ℕ) (hk : k > 0) :
    Filter.limsup (fun n => u (n / k)) Filter.atTop = Filter.limsup u Filter.atTop := by
      rw [ Filter.limsup_eq, Filter.limsup_eq ];
      congr! 3;
      simp +zetaDelta at *;
      constructor <;> rintro ⟨ a, ha ⟩;
      · exact ⟨ a * k, fun b hb => by simpa using ha ( b * k ) ( by nlinarith ) |> le_trans ( by simp +decide [hk] ) ⟩;
      · exact ⟨ a * k, fun b hb => ha _ ( Nat.le_div_iff_mul_le hk |>.2 ( by linarith ) ) ⟩

/-
The ratio of log(N/k) to log N tends to 1.
-/
lemma log_ratio_tendsto_one (k : ℕ) (hk : k > 0) :
    Filter.Tendsto (fun N => Real.log (N / k) / Real.log N) Filter.atTop (nhds 1) := by
      -- We can use the fact that $\log(N/k) = \log N - \log k$ to rewrite the limit expression.
      suffices h_log_div : Filter.Tendsto (fun N => (Real.log N - Real.log k) / Real.log N) Filter.atTop (nhds 1) by
        refine h_log_div.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN using by rw [ Real.log_div hN.ne' ( by positivity ) ] );
      ring_nf;
      exact le_trans ( Filter.Tendsto.sub ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx; rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) ) ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop ) ) ) ( by norm_num )

set_option maxHeartbeats 1000000 in
/-
If a sequence u is non-negative and v tends to 1, then limsup (u * v) = limsup u.
-/
lemma limsup_mul_tendsto_one {u v : ℕ → ℝ} (hu : 0 ≤ᶠ[Filter.atTop] u)
    (hv : Filter.Tendsto v Filter.atTop (nhds 1)) :
    Filter.limsup (u * v) Filter.atTop = Filter.limsup u Filter.atTop := by
      by_contra h_contra;
      have h_liminf : ∀ ε > 0, ∃ N, ∀ n ≥ N, (1 - ε) * u n ≤ u n * v n ∧ u n * v n ≤ (1 + ε) * u n := by
        intro ε hε_pos
        obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, |v n - 1| < ε := by
          exact Metric.tendsto_atTop.mp hv ε hε_pos;
        obtain ⟨ M, hM ⟩ := Filter.eventually_atTop.mp hu;
        exact ⟨ Max.max N M, fun n hn => ⟨ by nlinarith [ abs_lt.mp ( hN n ( le_trans ( le_max_left _ _ ) hn ) ), show 0 ≤ u n from hM n ( le_trans ( le_max_right _ _ ) hn ) ], by nlinarith [ abs_lt.mp ( hN n ( le_trans ( le_max_left _ _ ) hn ) ), show 0 ≤ u n from hM n ( le_trans ( le_max_right _ _ ) hn ) ] ⟩ ⟩;
      have h_liminf : ∀ ε > 0, Filter.limsup (u * v) Filter.atTop ≤ (1 + ε) * Filter.limsup u Filter.atTop := by
        intros ε hε_pos
        obtain ⟨N, hN⟩ := h_liminf ε hε_pos;
        by_cases h : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u <;> simp_all +decide [ Filter.limsup_eq ];
        · refine' le_of_forall_pos_le_add fun δ δ_pos => _;
          obtain ⟨a, ha⟩ : ∃ a, (∃ a_1, ∀ (b : ℕ), a_1 ≤ b → u b ≤ a) ∧ a < sInf {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → u b ≤ a} + δ / (1 + ε) := by
            exact exists_lt_of_csInf_lt ( show { a : ℝ | ∃ a_1, ∀ b : ℕ, a_1 ≤ b → u b ≤ a }.Nonempty from by rcases h with ⟨ M, hM ⟩ ; exact ⟨ M, by rcases Filter.eventually_atTop.mp hM with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => hN n hn ⟩ ⟩ ) ( lt_add_of_pos_right _ <| div_pos δ_pos <| by positivity );
          refine' le_trans ( csInf_le _ _ ) _;
          exact ( 1 + ε ) * a;
          · obtain ⟨ N', hN' ⟩ := Filter.eventually_atTop.mp ( hu.and ( hv.eventually ( lt_mem_nhds zero_lt_one ) ) );
            exact ⟨ 0, by rintro x ⟨ N, hN ⟩ ; exact le_trans ( mul_nonneg ( hN' _ ( le_max_left _ _ ) |>.1 ) ( hN' _ ( le_max_left _ _ ) |>.2.le ) ) ( hN _ ( le_max_right _ _ ) ) ⟩;
          · exact ⟨ Max.max N ha.1.choose, fun n hn => by nlinarith [ hN n ( le_trans ( le_max_left _ _ ) hn ), ha.1.choose_spec n ( le_trans ( le_max_right _ _ ) hn ) ] ⟩;
          · nlinarith [ mul_div_cancel₀ δ ( by linarith : ( 1 + ε ) ≠ 0 ) ];
        · simp_all +decide [ IsBoundedUnder, IsBounded ];
          rw [ show { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → u b * v b ≤ a } = ∅ from _ ] <;> norm_num;
          · rw [ show { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → u b ≤ a } = ∅ from _ ] <;> norm_num;
            exact Set.eq_empty_of_forall_notMem fun x hx => by obtain ⟨ N, hN ⟩ := hx; obtain ⟨ n, hn₁, hn₂ ⟩ := h x N; linarith [ hN n hn₁ ] ;
          · ext a;
            contrapose! h_contra;
            obtain ⟨ M, hM ⟩ := h_contra.resolve_right ( by tauto ) |> And.left;
            obtain ⟨ N, hN ⟩ := h_liminf ( 1 / 2 ) ( by norm_num );
            obtain ⟨ n, hn₁, hn₂ ⟩ := h ( a * 2 + 1 ) ( Max.max M N ) ; nlinarith [ hN n ( le_trans ( le_max_right M N ) hn₁ ), hM n ( le_trans ( le_max_left M N ) hn₁ ) ];
      have h_liminf : Filter.limsup (u * v) Filter.atTop ≤ Filter.limsup u Filter.atTop := by
        have h_liminf : Filter.Tendsto (fun ε : ℝ => (1 + ε) * Filter.limsup u Filter.atTop) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Filter.limsup u Filter.atTop)) := by
          exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
        exact le_of_tendsto_of_tendsto tendsto_const_nhds h_liminf ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => by aesop );
      have h_liminf : ∀ ε > 0, Filter.limsup u Filter.atTop ≤ (1 + ε) * Filter.limsup (u * v) Filter.atTop := by
        intros ε hε_pos
        have h_liminf : ∀ᶠ n in Filter.atTop, u n ≤ (1 + ε) * (u n * v n) := by
          have h_liminf : ∀ᶠ n in Filter.atTop, v n ≥ 1 / (1 + ε) := by
            exact hv.eventually ( le_mem_nhds <| by rw [ div_lt_iff₀ ] <;> linarith );
          filter_upwards [ hu, h_liminf ] with n hn hn' using by rw [ ge_iff_le, div_le_iff₀ ] at hn' <;> nlinarith [ mul_nonneg hn ( show 0 ≤ ε by linarith ) ] ;
        rw [ Filter.limsup_eq, Filter.limsup_eq ];
        rw [ ← smul_eq_mul, ← Real.sInf_smul_of_nonneg ];
        · refine' le_csInf _ _ <;> norm_num;
          · have h_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (u * v) := by
              by_cases h_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u;
              · obtain ⟨ M, hM ⟩ := h_bdd;
                have h_bdd_above : ∃ N, ∀ n ≥ N, |v n| ≤ 2 := by
                  exact Filter.eventually_atTop.mp ( hv.eventually ( Metric.closedBall_mem_nhds _ zero_lt_one ) ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun n hn => abs_le.mpr ⟨ by linarith [ abs_le.mp ( hN n hn ) ], by linarith [ abs_le.mp ( hN n hn ) ] ⟩ ⟩;
                obtain ⟨ N, hN ⟩ := h_bdd_above;
                obtain ⟨ N', hN' ⟩ := Filter.eventually_atTop.mp ( hu.and hM );
                exact ⟨ 2 * M, Filter.eventually_atTop.mpr ⟨ Max.max N N', fun n hn => by have := hN' n ( le_trans ( le_max_right _ _ ) hn ) ; have := hN n ( le_trans ( le_max_left _ _ ) hn ) ; norm_num at *; nlinarith [ abs_le.mp this ] ⟩ ⟩;
              · simp_all +decide [ IsBoundedUnder, IsBounded ];
                rw [ Filter.limsup_eq ] at h_contra;
                rw [ Real.sInf_def ] at h_contra;
                rw [ Real.sSup_def ] at h_contra ; aesop;
            obtain ⟨ M, hM ⟩ := h_bdd; exact ⟨ M, by rcases Filter.eventually_atTop.mp hM with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => hN n hn ⟩ ⟩ ;
          · rintro _ ⟨ a, ⟨ N, hN ⟩, rfl ⟩;
            refine' csInf_le _ _;
            · exact ⟨ 0, by rintro x ⟨ M, hM ⟩ ; exact le_trans ( hu.and ( Filter.eventually_ge_atTop M ) |> Filter.Eventually.exists |> Classical.choose_spec |> And.left ) ( hM _ ( hu.and ( Filter.eventually_ge_atTop M ) |> Filter.Eventually.exists |> Classical.choose_spec |> And.right ) ) ⟩;
            · exact Filter.eventually_atTop.mp ( h_liminf.and ( Filter.eventually_ge_atTop N ) ) |> fun ⟨ M, hM ⟩ => ⟨ M, fun n hn => by have := hM n hn; norm_num at *; nlinarith [ hN n ( by linarith ) ] ⟩;
        · positivity;
      have h_liminf : Filter.limsup u Filter.atTop ≤ Filter.limsup (u * v) Filter.atTop := by
        have h_liminf : Filter.Tendsto (fun ε : ℝ => (1 + ε) * Filter.limsup (u * v) Filter.atTop) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Filter.limsup (u * v) Filter.atTop)) := by
          exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
        exact le_of_tendsto_of_tendsto tendsto_const_nhds h_liminf ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => by aesop );
      exact h_contra <| le_antisymm ‹_› ‹_›

theorem helper3 (a b : ℕ) : Finset.Icc a.succ b = Finset.Ioc a b := by
  simp_all only [Nat.succ_eq_add_one]
  ext a_1 : 1
  simp_all only [Finset.mem_Icc, Finset.mem_Ioc, and_congr_left_iff]
  intro a_2
  rfl

/-
The logarithmic density sum is bounded by log N + 1.
-/
lemma log_density_sum_le_log (A : Set ℕ) (N : ℕ) (hN : N ≥ 1) :
    log_density_sum A N ≤ Real.log N + 1 := by
      -- The sum of reciprocals of natural numbers up to $N$ is at most $\log N + 1$.
      have h_harmonic_bound : ∀ N : ℕ, N ≥ 1 → ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n ≤ Real.log N + 1 := by
        intro N hN
        induction' hN with N hN ih;
        · norm_num +zetaDelta at *;
        · norm_num [ Finset.sum_Ioc_succ_top, helper3 ] at *;
          rw [ show ( N : ℝ ) + 1 = N * ( 1 + ( N : ℝ ) ⁻¹ ) by nlinarith only [ mul_inv_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ) ], Real.log_mul ( by positivity ) ( by positivity ) ];
          nlinarith [ inv_pos.mpr ( by positivity : 0 < ( N : ℝ ) * ( 1 + ( N : ℝ ) ⁻¹ ) ), mul_inv_cancel₀ ( by positivity : ( N : ℝ ) * ( 1 + ( N : ℝ ) ⁻¹ ) ≠ 0 ), Real.log_inv ( 1 + ( N : ℝ ) ⁻¹ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( 1 + ( N : ℝ ) ⁻¹ ) ) ), mul_inv_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( 1 + ( N : ℝ ) ⁻¹ ) ≠ 0 ) ];
      refine le_trans ?_ ( h_harmonic_bound N hN );
      refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
      rotate_left;
      exact Finset.filter ( fun n => n ∈ A ) ( Finset.Icc 1 N );
      · exact Finset.filter_subset _ _;
      · exact fun _ _ _ => by positivity;
      · unfold log_density_sum;
        erw [ Finset.sum_filter, Finset.sum_filter ] ; erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ]

/-
If A has positive lower density, there exists t such that A_t has positive upper logarithmic density.
-/
lemma exists_t_upper_log_density_At_pos (A : Set ℕ) (h : lowerDensity A > 0) :
    ∃ t, upper_log_density (At A t) > 0 := by
      -- Obtain `T` from `exists_T_union_pos`.
      obtain ⟨T, hT⟩ : ∃ T, lowerDensity (⋃ t ∈ Finset.range T, At A t) > 0 := exists_T_union_pos A h
      generalize_proofs at *;
      set U : Set ℕ := ⋃ t ∈ Finset.range T, At A t
      generalize_proofs at *; (
      -- By `lower_log_density_pos`, `lower_log_density U > 0`.
      have h_lower_log_density_U_pos : lower_log_density U > 0 := by
        exact lower_log_density_pos U hT;
      -- Since `lower_log_density U ≤ upper_log_density U` (liminf ≤ limsup), `upper_log_density U > 0`.
      have h_upper_log_density_U_pos : upper_log_density U > 0 := by
        refine' lt_of_lt_of_le h_lower_log_density_U_pos _;
        -- By definition of `lower_log_density` and `upper_log_density`, we know that `lower_log_density U ≤ upper_log_density U`.
        apply Filter.liminf_le_limsup; exact (by
        use 1 + 1 / Real.log 2;
        simp +zetaDelta at *;
        refine' ⟨ 2, fun n hn => _ ⟩ ; rw [ div_le_iff₀ ( Real.log_pos <| by norm_cast ) ] ; have := log_density_sum_le_log ( ⋃ t, ⋃ ( _ : t < T ), At A t ) n ( by linarith ) ; norm_num at *;
        nlinarith [ inv_pos.mpr ( Real.log_pos one_lt_two ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ), Real.log_le_log ( by positivity ) ( by norm_cast : ( 2 : ℝ ) ≤ n ) ]);
        refine' ⟨ 0, Filter.eventually_atTop.mpr ⟨ 2, fun N hN => div_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ⟩ ⟩;
      exact not_forall_not.mp fun h' => h_upper_log_density_U_pos.not_ge <| le_trans ( upper_log_density_subadd ( Finset.range T ) ( fun t => At A t ) ) <| by simpa using Finset.sum_nonpos fun t ht => le_of_not_gt <| h' t;)

/-
If a set of odd integers has positive upper logarithmic density, it contains an lcm-triple.
-/
lemma lcm_triple_of_upper_log_density_pos (A : Set ℕ) (hA_odd : ∀ a ∈ A, Odd a)
    (h_pos : upper_log_density A > 0) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ Nat.lcm a b = c := by
      by_contra h_contra
      have h_upper_log_density : upper_log_density A = 0 := by
        have h_upper_log_density : Filter.Tendsto (fun N => log_density_sum A N / Real.log N) Filter.atTop (nhds 0) := by
          have h_I_N_zero : (fun N => (I_N A N : ℝ)) =o[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
            apply_rules [ I_N_upper_bound_asymptotic ];
            exact fun a ha b hb c hc hab hbc hca => fun h => h_contra ⟨ a, ha, b, hb, c, hc, hab, hbc, hca, h ⟩;
          have h_I_N_bound : ∀ N ≥ 1, (I_N A N : ℝ) ≥ (N / 2 : ℝ) * log_density_sum A N - N := by
            intros N hN
            have h_I_N_bound : (I_N A N : ℝ) ≥ ∑ a ∈ (Finset.range (N + 1)).filter (· ∈ A), ((N / a : ℝ) / 2 - 1) := by
              convert I_N_lower_bound A hA_odd N using 1;
            simp_all +decide [ log_density_sum ];
            convert h_I_N_bound.trans _ using 1;
            · rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by ring;
            · exact add_le_add_left ( mod_cast le_trans ( Finset.card_le_card ( show Finset.filter ( fun x => x ∈ A ) ( Finset.range ( N + 1 ) ) ⊆ Finset.Icc 1 N from fun x hx => Finset.mem_Icc.mpr ⟨ Nat.pos_of_ne_zero fun h => by simpa [ h ] using hA_odd x <| Finset.mem_filter.mp hx |>.2, Nat.le_of_lt_succ <| Finset.mem_range.mp <| Finset.mem_filter.mp hx |>.1 ⟩ ) ) <| by simp +arith +decide ) _;
          have h_I_N_bound : ∀ᶠ N in Filter.atTop, (log_density_sum A N : ℝ) ≤ 2 * (I_N A N : ℝ) / N + 2 := by
            filter_upwards [ Filter.eventually_ge_atTop 1 ] with N hN using by rw [ div_add', le_div_iff₀ ] <;> first | positivity | nlinarith [ h_I_N_bound N hN ] ;
          have h_I_N_bound : Filter.Tendsto (fun N => (2 * (I_N A N : ℝ) / N + 2) / Real.log N) Filter.atTop (nhds 0) := by
            have h_I_N_bound : Filter.Tendsto (fun N => (2 * (I_N A N : ℝ) / N) / Real.log N) Filter.atTop (nhds 0) := by
              rw [ Asymptotics.isLittleO_iff_tendsto' ] at h_I_N_zero;
              · convert h_I_N_zero.const_mul 2 using 2 <;> ring;
              · filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN hN' using absurd hN' <| ne_of_gt <| mul_pos ( Nat.cast_pos.mpr <| pos_of_gt hN ) <| Real.log_pos <| Nat.one_lt_cast.mpr hN;
            simpa [ add_div ] using h_I_N_bound.add ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) );
          refine' squeeze_zero_norm' _ h_I_N_bound;
          filter_upwards [ ‹∀ᶠ N in Filter.atTop, log_density_sum A N ≤ 2 * ↑ ( I_N A N ) / ↑ N + 2›, Filter.eventually_ge_atTop 1 ] with N hN₁ hN₂ using by rw [ Real.norm_of_nonneg ( div_nonneg ( show 0 ≤ log_density_sum A N from Finset.sum_nonneg fun _ _ => by positivity ) ( Real.log_natCast_nonneg _ ) ) ] ; exact div_le_div_of_nonneg_right hN₁ ( Real.log_natCast_nonneg _ ) ;
        convert h_upper_log_density.limsup_eq using 1;
      linarith

/-
The ratio of the logarithmic density sum to log N is bounded.
-/
lemma log_density_ratio_bounded (A : Set ℕ) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun N => log_density_sum A N / Real.log N) := by
      refine' ⟨ 2, Filter.eventually_atTop.mpr ⟨ 3, fun N hN => _ ⟩ ⟩;
      have := log_density_sum_le_log A N ( by linarith );
      exact div_le_of_le_mul₀ ( Real.log_nonneg ( by norm_cast; linarith ) ) ( by positivity ) ( by linarith [ show 1 ≤ Real.log N from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( N : ℝ ) ≥ 3 by norm_cast ] ) ] )

/-
The limsup of `log_density_sum A (N/k) / log(N/k)` is equal to the upper logarithmic density of A.
-/
lemma limsup_log_density_stretch_aux (A : Set ℕ) (k : ℕ) (hk : k > 0) :
    Filter.limsup (fun N => log_density_sum A (N / k) / Real.log (N / k)) Filter.atTop = upper_log_density A := by
      -- Extend the sequence to be defined for real numbers by taking the floor of N/k.
      set u : ℕ → ℝ := fun N => log_density_sum A N / Real.log N;
      -- Apply `limsup_stretch` to the sequence `u(N) = log_density_sum A N / log N`.
      have h_limsup_stretch : Filter.limsup (fun N => u (Nat.floor (N / k))) Filter.atTop = Filter.limsup u Filter.atTop := by
        convert limsup_stretch u k hk using 1;
      have h_limsup_stretch : Filter.limsup (fun N => u (Nat.floor (N / k)) * (Real.log (Nat.floor (N / k)) / Real.log (N / k))) Filter.atTop = Filter.limsup u Filter.atTop := by
        have h_limsup_stretch : Filter.Tendsto (fun N => Real.log (Nat.floor (N / k)) / Real.log (N / k)) Filter.atTop (nhds 1) := by
          have h_log_floor : Filter.Tendsto (fun x : ℝ => Real.log (Nat.floor x) / Real.log x) Filter.atTop (nhds 1) := by
            have h_log_floor : Filter.Tendsto (fun x : ℝ => Real.log (x - 1) / Real.log x) Filter.atTop (nhds 1) := by
              have h_log_floor : Filter.Tendsto (fun x : ℝ => (Real.log x + Real.log (1 - 1 / x)) / Real.log x) Filter.atTop (nhds 1) := by
                ring_nf;
                exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.sub ( tendsto_inv_atTop_zero ) ) ( by norm_num ) ) ( tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop ) ) ) ( by norm_num );
              refine h_log_floor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ one_sub_div ( by linarith ) ] ; rw [ Real.log_div ] <;> ring_nf <;> linarith );
            refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' h_log_floor tendsto_const_nhds _ _;
            · filter_upwards [ Filter.eventually_gt_atTop 2 ] with x hx using div_le_div_of_nonneg_right ( Real.log_le_log ( by linarith ) ( by linarith [ Nat.lt_floor_add_one x ] ) ) ( Real.log_nonneg ( by linarith ) );
            · filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using div_le_one_of_le₀ ( Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) <| Nat.floor_le <| by linarith ) <| Real.log_nonneg <| by linarith;
          convert h_log_floor.comp ( show Filter.Tendsto ( fun N : ℕ => ( N : ℝ ) / k ) Filter.atTop Filter.atTop from Filter.Tendsto.atTop_div_const ( Nat.cast_pos.mpr hk ) tendsto_natCast_atTop_atTop ) using 2;
          norm_num [ Nat.floor_div_natCast ];
        have h_limsup_stretch : Filter.limsup (fun N => u (Nat.floor (N / k)) * (Real.log (Nat.floor (N / k)) / Real.log (N / k))) Filter.atTop = Filter.limsup (fun N => u (Nat.floor (N / k))) Filter.atTop := by
          have h_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun N => u (Nat.floor (N / k))) := by
            have h_limsup_stretch : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u := by
              exact log_density_ratio_bounded A;
            obtain ⟨ M, hM ⟩ := h_limsup_stretch;
            norm_num +zetaDelta at *;
            obtain ⟨ N, hN ⟩ := hM;
            exact ⟨ M, Filter.eventually_atTop.mpr ⟨ N * k, fun n hn => hN _ <| Nat.le_div_iff_mul_le hk |>.2 <| by nlinarith ⟩ ⟩
          apply_rules [ limsup_mul_tendsto_one ];
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN using div_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( Real.log_natCast_nonneg _ );
        linarith;
      convert h_limsup_stretch using 1;
      refine' Filter.limsup_congr _;
      filter_upwards [ Filter.eventually_gt_atTop ( k * 2 ) ] with N hN ; rw [ div_mul_div_cancel₀ ] ; aesop;
      exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.le_floor <| Nat.le_div_iff_mul_le hk |>.2 <| by linarith;

/-
The upper logarithmic density of a set A is equal to the limsup of `log_density_sum A (N/k) / log N`.
-/
lemma limsup_log_density_stretch (A : Set ℕ) (k : ℕ) (hk : k > 0) :
    Filter.limsup (fun N => log_density_sum A (N / k) / Real.log N) Filter.atTop = upper_log_density A := by
      have h_stretch : Filter.limsup (fun N => log_density_sum A (N / k) / Real.log (N / k) * (Real.log (N / k) / Real.log N)) Filter.atTop = upper_log_density A := by
        have h_stretch : Filter.limsup (fun N => log_density_sum A (N / k) / Real.log (N / k)) Filter.atTop = upper_log_density A := by
          convert limsup_log_density_stretch_aux A k hk using 1;
        convert limsup_mul_tendsto_one _ _ using 2;
        · exact h_stretch.symm;
        · filter_upwards [ Filter.eventually_gt_atTop ( k : ℕ ) ] with N hN using div_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( Real.log_nonneg <| by rw [ le_div_iff₀ <| by positivity ] ; norm_cast ; linarith );
        · have := log_ratio_tendsto_one k hk;
          exact this.comp tendsto_natCast_atTop_atTop;
      refine' h_stretch ▸ Filter.limsup_congr ( by filter_upwards [ Filter.eventually_gt_atTop k ] with N hN using by rw [ div_mul_div_cancel₀ ( ne_of_gt <| Real.log_pos <| by rw [ lt_div_iff₀ <| by positivity ] ; norm_cast ; linarith ) ] )

/-
The upper logarithmic density of $B_t$ is $2^t$ times the upper logarithmic density of $A_t$.
-/
lemma upper_log_density_Bt (A : Set ℕ) (t : ℕ) :
    upper_log_density (Bt A t) = (2^t : ℝ) * upper_log_density (At A t) := by
      -- We have `log_density_sum (At A t) N = (1/2^t) * log_density_sum (Bt A t) (N/2^t)`.
      -- Dividing by `log N`, we get `(1/2^t) * (log_density_sum (Bt A t) (N/2^t) / log N)`.
      have h_div : ∀ N ≥ 1, log_density_sum (At A t) N = (1 / 2^t : ℝ) * log_density_sum (Bt A t) (N / 2^t) := by
        intros N hN
        rw [log_density_sum_Bt_relation];
      -- Taking limsup, we get `upper_log_density (At A t) = (1/2^t) * limsup (log_density_sum (Bt A t) (N/2^t) / log N)`.
      have h_limsup : Filter.limsup (fun N => log_density_sum (At A t) N / Real.log N) Filter.atTop = (1 / 2^t : ℝ) * Filter.limsup (fun N => log_density_sum (Bt A t) (N / 2^t) / Real.log N) Filter.atTop := by
        have h_limsup : Filter.limsup (fun N => (1 / 2^t : ℝ) * (log_density_sum (Bt A t) (N / 2^t) / Real.log N)) Filter.atTop = (1 / 2^t : ℝ) * Filter.limsup (fun N => log_density_sum (Bt A t) (N / 2^t) / Real.log N) Filter.atTop := by
          norm_num [ Filter.limsup_eq ];
          rw [ ← smul_eq_mul, ← Real.sInf_smul_of_nonneg ];
          · congr with x ; simp +decide [ div_eq_inv_mul ];
            constructor <;> rintro ⟨ a, ha ⟩;
            · exact ⟨ x / ( 2 ^ t ) ⁻¹, ⟨ a, fun b hb => by rw [ le_div_iff₀ ( by positivity ) ] ; linarith [ ha b hb ] ⟩, by simp +decide [ div_eq_inv_mul ] ⟩;
            · exact ⟨ ha.1.choose, fun n hn => by rw [ ← ha.2 ] ; exact mul_le_mul_of_nonneg_left ( ha.1.choose_spec n hn ) ( by positivity ) ⟩;
          · positivity;
        exact Eq.trans ( Filter.limsup_congr <| by filter_upwards [ Filter.eventually_ge_atTop 1 ] with N hN using by rw [ h_div N hN ] ; ring ) h_limsup;
      -- By `limsup_log_density_stretch`, the limsup is `upper_log_density (Bt A t)`.
      have h_limsup_final : Filter.limsup (fun N => log_density_sum (Bt A t) (N / 2^t) / Real.log N) Filter.atTop = upper_log_density (Bt A t) := by
        convert limsup_log_density_stretch ( Bt A t ) ( 2 ^ t ) ( by positivity ) using 1;
      unfold upper_log_density at * ; aesop

/-
If a set A has positive lower density, it contains an lcm-triple.
-/
theorem erdos_487 (A : Set ℕ) (hA : lowerDensity A > 0) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ Nat.lcm a b = c := by
      by_contra! h;
      -- Let $A' = A \setminus \{0\}$. Then $\ldens(A') = \ldens(A) > 0$.
      set A' : Set ℕ := A \ {0}
      have hA'_pos : lowerDensity A' > 0 := by
        convert hA using 1;
        refine' Filter.liminf_congr _;
        norm_num +zetaDelta at *;
        exact ⟨ 1, fun n hn => by rw [ Finset.filter_congr fun x hx => by aesop ] ⟩;
      -- By `exists_t_upper_log_density_At_pos`, there exists $t$ such that `upper_log_density (At A' t) > 0`.
      obtain ⟨t, ht⟩ : ∃ t, upper_log_density (At A' t) > 0 := by
        -- Apply `exists_t_upper_log_density_At_pos` to `A'` with the given `hA'_pos`.
        apply exists_t_upper_log_density_At_pos; assumption;
      -- Since $A'$ has no zero, `Bt A' t` consists of odd integers by `Bt_odd`.
      have hBt_odd : ∀ b ∈ Bt A' t, Odd b := by
        apply Bt_odd; aesop;
      -- By `lcm_triple_of_upper_log_density_pos`, `Bt A' t` contains distinct $x,y,z$ with $[x,y]=z$.
      obtain ⟨x, hx, y, hy, z, hz, hxyz⟩ : ∃ x ∈ Bt A' t, ∃ y ∈ Bt A' t, ∃ z ∈ Bt A' t, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ Nat.lcm x y = z := by
        apply lcm_triple_of_upper_log_density_pos;
        · assumption;
        · rw [ upper_log_density_Bt ] ; aesop;
      -- By `lcm_triple_preservation`, $A'$ contains distinct $a,b,c$ with $[a,b]=c$.
      obtain ⟨a, ha, b, hb, c, hc, habc⟩ : ∃ a ∈ A', ∃ b ∈ A', ∃ c ∈ A', a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ v2 a = t ∧ v2 b = t ∧ v2 c = t ∧ Nat.lcm a b = c := by
        obtain ⟨a, ha, b, hb, c, hc, habc⟩ : ∃ a ∈ A', ∃ b ∈ A', ∃ c ∈ A', a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ v2 a = t ∧ v2 b = t ∧ v2 c = t ∧ Nat.lcm a b = c := by
          have := lcm_triple_preservation A' t
          grind;
        exact ⟨ a, ha, b, hb, c, hc, habc ⟩;
      exact h a ha.1 b hb.1 c hc.1 habc.1 habc.2.1 habc.2.2.1 habc.2.2.2.2.2.2

#print axioms erdos_487
-- 'Erdos487.erdos_487' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos487
