/-

This is a Lean formalization of a solution to Erdős Problem 447.
https://www.erdosproblems.com/forum/thread/447

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
2 * binom(n, m+1) >= m * binom(n, m/2) for m >= 4.
-/
noncomputable section AristotleLemmas

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

end AristotleLemmas

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
Identities for sums of Y_k over blocks [t, 2t] and [t, 2t+1].
-/
lemma block_sum_identities_proven {n t : ℕ} (ht : 1 ≤ t) (h2t : 2 * t ≤ n / 2) :
    (∑ k ∈ Finset.Icc t (2 * t), Y_sol n k = (2 * t : ℝ) * n.choose (2 * t)) ∧
    (2 * t + 1 ≤ n / 2 → ∑ k ∈ Finset.Icc t (2 * t + 1), Y_sol n k = ((2 * t + 1 : ℕ) : ℝ) * n.choose (2 * t + 1) + Y_sol n t) := by
      exact block_sum_identities ht h2t

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
        have := @block_sum_identities_proven;
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

#print axioms erdos_447
-- 'Erdos447.erdos_447' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos447
