/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 497.
https://www.erdosproblems.com/forum/thread/497

Informal authors:
- Daniel Kleitman

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos497.md
-/
/-
Formalization of the paper 'Counting Antichains in the Boolean Lattice'.
The main result is `erdos_497`, which states that the number of antichains A(n) in the Boolean
lattice satisfies log₂(A(n)) ~ binom(n, ⌊n/2⌋) as n → ∞.
This confirms the asymptotic formula A(n) = 2^{(1+o(1))binom(n, ⌊n/2⌋)}.
The proof utilizes the graph container method and supersaturation results for comparable pairs.
-/

import Mathlib
import ErdosProblems.Erdos1023

namespace Erdos497

set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

open scoped Classical

open Equiv
open Filter
open Finset
open Nat
open Real

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.style.cases false
set_option linter.style.induction false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.style.refine false
set_option linter.style.setOption false

/-
Definitions of PP(n), antichains, and A(n).
-/

/-- The powerset of [n], denoted 𝒫(n) in the text. -/
def PP (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.powerset

/-- The set of all antichains in 𝒫(n). -/
noncomputable def antichains (n : ℕ) : Finset (Finset (Finset (Fin n))) :=
  (PP n).powerset.filter (fun ℱ => IsAntichain (· ⊆ ·) (ℱ : Set (Finset (Fin n))))

/-- A(n) denotes the number of antichains in 𝒫(n). -/
noncomputable def A (n : ℕ) : ℕ :=
  (antichains n).card

/-
Definition of G_n and the equivalence between antichains and independent sets.
-/
/--
Let G_n be the graph with vertex set 𝒫(n) in which distinct A,B are adjacent if and only if A ⊂ B or
B ⊂ A.
-/
def G (n : ℕ) : SimpleGraph (Finset (Fin n)) :=
  SimpleGraph.fromRel (· ⊆ ·)

/-- An antichain in 𝒫(n) is equivalently an independent set in G_n. -/
theorem antichain_iff_independent_set (n : ℕ) (ℱ : Finset (Finset (Fin n))) :
    ℱ ∈ antichains n ↔ (G n).IsIndepSet (ℱ : Set (Finset (Fin n))) := by
  -- By definition of antichains, ℱ is an antichain if and only if for any two distinct elements A
  -- and B in ℱ, neither is a subset of the other.
  simp [antichains, IsAntichain];
  simp +decide [ Set.Pairwise, G ];
  unfold PP; aesop;

/-
Asymptotic behavior of the central binomial coefficient.
-/

/-- Let m = ⌊n/2⌋ and N = bin(n, m). Then N = Θ(2^n / √n) as n → ∞. -/
theorem central_binomial_coefficient_asymptotic :
    (fun n : ℕ => ((n.choose (n / 2)) : ℝ)) =Θ[atTop] (fun n => (2 : ℝ) ^ n / Real.sqrt n) := by
  have h_equiv :
      Asymptotics.IsEquivalent atTop
        (fun n : ℕ => ((n.choose (n / 2)) : ℝ))
        (fun n => Real.sqrt (2 / Real.pi) * ((2 : ℝ) ^ n) / Real.sqrt (n : ℝ)) :=
    Erdos1023.kleitman_bound_many.symm.trans Erdos1023.many_sqrt_two_div_pi
  have htheta :
      (fun n : ℕ => ((n.choose (n / 2)) : ℝ)) =Θ[atTop]
        (fun n => Real.sqrt (2 / Real.pi) * ((2 : ℝ) ^ n / Real.sqrt (n : ℝ))) := by
    convert h_equiv.isTheta using 1
    ext n
    ring
  exact (Asymptotics.isTheta_const_mul_right
    (show Real.sqrt (2 / Real.pi) ≠ 0 by positivity)).mp htheta

/-
Definitions of Chain, Symmetric Chain, and Symmetric Chain Decomposition.
-/

/-- A chain in 𝒫(n) is a family C₀ ⊂ C₁ ⊂ ⋯ ⊂ C_t.
    We represent a chain as a Finset of Finsets. -/
def IsChain' {n : ℕ} (ℱ : Finset (Finset (Fin n))) : Prop :=
  IsChain (· ⊆ ·) (ℱ : Set (Finset (Fin n)))

/--
A chain is symmetric if for some k ≤ n/2 it contains exactly one set of each size k, k+1, ..., n-k.
-/
def IsSymmetricChain (n : ℕ) (C : Finset (Finset (Fin n))) : Prop :=
  IsChain' C ∧ ∃ k, k ≤ n / 2 ∧ C.image card = Icc k (n - k)

/-- A symmetric chain decomposition (SCD) of 𝒫(n) is a partition of 𝒫(n) into symmetric chains. -/
def IsSymmetricChainDecomposition (n : ℕ) (X : Finset (Finset (Finset (Fin n)))) : Prop :=
  (∀ C ∈ X, IsSymmetricChain n C) ∧
  (X : Set (Finset (Finset (Fin n)))).PairwiseDisjoint id ∧
  X.biUnion id = PP n

/-
Definitions of embedding functions and chain lifting operations.
-/

def embed (n : ℕ) (A : Finset (Fin n)) : Finset (Fin (n+1)) :=
  A.map Fin.castSuccEmb

def embed_plus (n : ℕ) (A : Finset (Fin n)) : Finset (Fin (n+1)) :=
  insert (Fin.last n) (embed n A)

def chain_top {n : ℕ} (C : Finset (Finset (Fin n))) : Finset (Fin n) :=
  C.sup id

def lift_chain_0 (n : ℕ) (C : Finset (Finset (Fin n))) : Finset (Finset (Fin (n+1))) :=
  (C.image (embed n)) ∪ {embed_plus n (chain_top C)}

def lift_chain_1 (n : ℕ) (C : Finset (Finset (Fin n))) : Finset (Finset (Fin (n+1))) :=
  (C.erase (chain_top C)).image (embed_plus n)

/-
Embedding preserves subsets.
-/

lemma embed_mono {n : ℕ} {A B : Finset (Fin n)} (h : A ⊆ B) : embed n A ⊆ embed n B := by
  unfold embed; aesop;

/-
Embedding into the plus construction preserves subsets.
-/

lemma embed_subset_embed_plus {n : ℕ} {A B : Finset (Fin n)} (h : A ⊆ B) :
    embed n A ⊆ embed_plus n B := by
  unfold embed embed_plus;
  simp_all +decide [ Finset.subset_iff, Finset.mem_map ];
  exact fun x hx => Finset.mem_map.mpr ⟨ x, h hx, rfl ⟩

/-
Every element in a chain is a subset of its top element (union).
-/

lemma chain_top_max {n : ℕ} {C : Finset (Finset (Fin n))} (A : Finset (Fin n)) (hA : A ∈ C) :
    A ⊆ chain_top C := by
  exact Finset.subset_iff.2 fun x hx => Finset.mem_sup.2 ⟨ A, hA, hx ⟩

/-
Cardinality of embedding.
-/
lemma card_embed {n : ℕ} (A : Finset (Fin n)) : (embed n A).card = A.card := by
  -- Since `Fin.castSuccEmb` is injective, the cardinality of the image of `A` under `embed n` is
  -- equal to the cardinality of `A`.
  have h_inj : Function.Injective (Fin.castSuccEmb : Fin n → Fin (n + 1)) := by
    exact fun a b h => by simpa [ Fin.ext_iff ] using h;
  convert Finset.card_image_of_injective _ h_inj;
  ext; simp [embed]

/-
Cardinality of embedding plus new element.
-/
lemma card_embed_plus {n : ℕ} (A : Finset (Fin n)) : (embed_plus n A).card = A.card + 1 := by
  -- The cardinality of the embedded set is the same as the original set since it's just a renaming
  -- of elements. The cardinality of the embedded plus set is the same as the original set augmented
  -- with one more element.
  have h_card : (embed_plus n A).card = (embed n A).card + 1 := by
    convert Finset.card_insert_of_notMem _;
    unfold embed; aesop;
  rw [ h_card, card_embed ]

/-
The top element of a non-empty chain is in the chain.
-/
lemma chain_top_mem {n : ℕ} {C : Finset (Finset (Fin n))} (hC : IsChain' C) (hne : C.Nonempty) :
    chain_top C ∈ C := by
  have := Finset.exists_maximal hne;
  obtain ⟨ i, hi ⟩ := this;
  convert hi.1;
  refine' le_antisymm _ _;
  · exact Finset.sup_le fun x hx => hi.2 hx |> fun h => by cases hC.total hx hi.1 <;> aesop;
  · exact Finset.le_sup ( f := id ) hi.1

/-
lift_chain_0 produces a chain.
-/
lemma lift_chain_0_is_chain (n : ℕ) (C : Finset (Finset (Fin n))) (hC : IsChain' C) :
    IsChain' (lift_chain_0 n C) := by
  -- To show that the lifted chain is a chain, we need to verify that the elements are ordered by
  -- subset. The elements of the lifted chain are the embeddings of the chain and the embedding plus
  -- the top element.
  have h_lifted_chain_order : ∀ A B :
      Finset (Fin (n + 1)), A ∈ lift_chain_0 n C → B ∈ lift_chain_0 n C → A ⊆ B ∨ B ⊆ A := by
    unfold lift_chain_0;
    simp +decide [ Finset.mem_image ];
    rintro A B ( rfl | ⟨ a, ha, rfl ⟩ ) ( rfl | ⟨ b, hb, rfl ⟩ ) <;> simp_all +decide [ IsChain' ];
    · unfold embed_plus embed;
      simp +decide [ Finset.subset_iff ];
      exact fun x hx => Finset.le_sup ( f := id ) hb hx;
    · exact Or.inl ( by simpa using chain_top_max _ ha |> fun h => embed_subset_embed_plus h );
    · cases hC.total ha hb <;> [ left; right ] <;> (expose_names; exact embed_mono h);
  exact fun A hA B hB hAB => h_lifted_chain_order A B hA hB |> Or.rec ( fun h => by tauto ) fun h =>
    by tauto;

/-
A symmetric chain is non-empty.
-/
lemma symmetric_chain_nonempty {n : ℕ} {C : Finset (Finset (Fin n))}
    (hC : IsSymmetricChain n C) : C.Nonempty := by
  -- Since the image of a nonempty set under a function is nonempty, and the image of C under card
  -- is nonempty, C must be nonempty.
  by_contra h_empty;
  obtain ⟨ k, hk ⟩ := hC.2;
  rcases k with ( _ | k ) <;> rcases n with ( _ | n ) <;> simp_all +decide;
  · exact absurd hk.symm ( Finset.Nonempty.ne_empty ⟨ 0, Finset.mem_Icc.mpr ⟨ Nat.zero_le _,
    Nat.zero_le _ ⟩ ⟩ );
  · exact absurd hk.2.symm ( Finset.Nonempty.ne_empty ⟨ _, Finset.mem_Icc.mpr ⟨ le_rfl,
    by omega ⟩ ⟩ )

/-
The cardinality of the top element of a symmetric chain is n - k.
-/
lemma chain_top_card {n : ℕ} {C : Finset (Finset (Fin n))}
    (k : ℕ) (hk : C.image card = Icc k (n - k)) (hC : IsChain' C) (hne : C.Nonempty) :
    (chain_top C).card = n - k := by
  -- Since $C$ is a chain, the top element is the maximum element in terms of cardinality.
  have h_top_max : ∀ A ∈ C, A ⊆ chain_top C := by
    exact fun A a => chain_top_max A a;
  -- Since $C$ is a chain, the top element is the maximum element in terms of cardinality, so its
  -- cardinality must be $n - k$.
  have h_top_card : (chain_top C).card ∈ Finset.Icc k (n - k) := by
    exact hk ▸ Finset.mem_image_of_mem _ ( chain_top_mem hC hne );
  have h_top_card_max : ∀ A ∈ C, A.card ≤ (chain_top C).card := by
    exact fun A hA => Finset.card_le_card <| h_top_max A hA;
  exact le_antisymm ( Finset.mem_Icc.mp h_top_card |>.2 ) ( by
    obtain ⟨ A, hA ⟩ :=
      Finset.mem_image.mp
        ( hk.symm ▸
          Finset.mem_Icc.mpr
            ⟨ by linarith [ Finset.mem_Icc.mp h_top_card ], le_rfl ⟩ );
    linarith [ h_top_card_max A hA.1 ] )

/-
Cardinality image of lift_chain_0 with assumptions.
-/
lemma lift_chain_0_card_image (n : ℕ) (C : Finset (Finset (Fin n)))
    (k : ℕ) (hk : C.image card = Icc k (n - k)) (hC : IsChain' C) (hk_le : k ≤ n / 2) :
    (lift_chain_0 n C).image card = Icc k ((n + 1) - k) := by
  -- By definition of `lift_chain_0`, we have that its image under the cardinality function is the
  -- union of the image of `C` and the singleton set `{chain_top C |+| 1}`.
  ext i; simp [lift_chain_0, card_embed, card_embed_plus];
  constructor;
  · rintro ( rfl | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ Finset.ext_iff ];
    · -- By definition of chain_top, its cardinality is n - k.
      have h_chain_top_card : (chain_top C).card = n - k := by
        apply chain_top_card;
        · ext; aesop;
        · assumption;
        · exact Exists.elim ( hk k |>.2 ⟨ le_rfl, Nat.le_sub_of_add_le ( by omega ) ⟩ ) fun x hx =>
          ⟨ x, hx.1 ⟩;
      omega;
    · exact ⟨ hk _ |>.1 ⟨ a, ha, rfl ⟩ |>.1, le_trans ( hk _ |>.1 ⟨ a, ha,
      rfl ⟩ |>.2 ) ( Nat.sub_le_sub_right ( Nat.le_succ _ ) _ ) ⟩;
  · by_cases hi : i = n - k + 1;
    · have :=
      chain_top_card k hk hC ( symmetric_chain_nonempty <| show IsSymmetricChain n C from
        ⟨ hC, k, hk_le, hk ⟩ ) ;
        aesop;
    · intro hi';
      -- Since $i$ is not equal to $n - k + 1$, it must be that $i \leq n - k$.
      have hi_le : i ≤ n - k := by
        omega;
      replace hk := Finset.ext_iff.mp hk i; aesop;

/-
lift_chain_0 preserves symmetry.
-/
theorem lift_chain_0_is_symmetric (n : ℕ) (C : Finset (Finset (Fin n)))
    (hC : IsSymmetricChain n C) :
    IsSymmetricChain (n + 1) (lift_chain_0 n C) := by
  -- From hC, we have IsChain' C and exists k, k <= n/2 and C.image card = Icc k (n-k).
  obtain ⟨h_chain, k, hk_le, hk_image⟩ := hC;
  refine ⟨ lift_chain_0_is_chain n C h_chain, k, ?_, ?_ ⟩;
  · omega;
  · convert lift_chain_0_card_image n C k hk_image h_chain hk_le using 1

/-
lift_chain_1 produces a chain.
-/
lemma lift_chain_1_is_chain (n : ℕ) (C : Finset (Finset (Fin n))) (hC : IsChain' C) :
    IsChain' (lift_chain_1 n C) := by
  have h_chain : ∀ A B :
      Finset (Fin (n + 1)), A ∈ (C.erase (chain_top C)).image (embed_plus n)
        → B ∈ (C.erase (chain_top C)).image (embed_plus n) → A ≠ B → A ⊆ B ∨ B ⊆ A := by
    intro A B hA hB hne; obtain ⟨ A', hA', rfl ⟩ :=
      Finset.mem_image.mp hA; obtain ⟨ B', hB', rfl ⟩ :=
        Finset.mem_image.mp hB; simp_all +decide [ IsChain' ] ;
    cases hC.total hA'.2 hB'.2 <;> simp_all +decide [ Finset.subset_iff ];
    · simp_all +decide [ embed_plus ];
      simp_all +decide [ Finset.ext_iff, embed ];
    · right; intro x hx; simp_all +decide [ embed_plus ] ;
      unfold embed at *; aesop;
  exact fun ⦃x⦄ a ⦃y⦄ => h_chain x y a

/-
Cardinality image of lift_chain_1.
-/
lemma lift_chain_1_card_image (n : ℕ) (C : Finset (Finset (Fin n)))
    (k : ℕ) (hk : C.image card
      = Icc k (n - k)) (hC : IsChain' C) (hne : (lift_chain_1 n C).Nonempty) :
    (lift_chain_1 n C).image card = Icc (k + 1) ((n + 1) - (k + 1)) := by
  -- Let's unfold the definition of `lift_chain_1`
  unfold lift_chain_1;
  -- By definition of `embed_plus`, we know that `Finset.card (embed_plus n A) = A.card + 1` for any
  -- `A`.
  have h_card_embed_plus : ∀ A : Finset (Fin n), (embed_plus n A).card = A.card + 1 := by
    exact fun A => card_embed_plus A;
  -- By definition of `chain_top`, we know that `chain_top C ∈ C` and `Finset.card (chain_top C) = n
  -- - k`.
  have h_chain_top : chain_top C ∈ C ∧ (chain_top C).card = n - k := by
    apply And.intro;
    · apply chain_top_mem hC;
      contrapose! hne; aesop;
    · apply chain_top_card k hk hC;
      contrapose! hne; aesop;
  -- Let's simplify the image of the cardinality function under the embedding plus operation.
  have h_image_card :
      Finset.image Finset.card (Finset.image (embed_plus n) (C.erase (chain_top C)))
        = Finset.image (fun x =>
        x + 1) (Finset.image Finset.card (C.erase (chain_top C))) := by
    ext; aesop;
  -- By definition of `C.erase (chain_top C)`, we know that its image under the cardinality function
  -- is `Finset.Icc k (n - k) \ {n - k}`.
  have h_image_erase :
      Finset.image Finset.card (C.erase (chain_top C)) = Finset.Icc k (n - k) \ {n - k} := by
    simp +decide [ ← hk ];
    ext; simp
    constructor;
    · rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ;
      exact
        ⟨ ⟨ a, ha₂, rfl ⟩,
          by
            rintro h
            exact ha₁ <|
              Finset.eq_of_subset_of_card_le ( chain_top_max a ha₂ ) <| by aesop ⟩ ;
    · grind;
  simp_all +decide [ Finset.ext_iff ];
  exact fun a => ⟨ fun ⟨ b, hb₁, hb₂ ⟩ => ⟨ by linarith, by omega ⟩, fun hb =>
    ⟨ a - 1, ⟨ ⟨ by omega, by omega ⟩, by omega ⟩, by omega ⟩ ⟩

/-
lift_chain_1 preserves symmetry if the result is non-empty.
-/
theorem lift_chain_1_is_symmetric (n : ℕ) (C : Finset (Finset (Fin n)))
    (hC : IsSymmetricChain n C) (hne : (lift_chain_1 n C).Nonempty) :
    IsSymmetricChain (n + 1) (lift_chain_1 n C) := by
  -- By definition of `lift_chain_1`, we know that it produces a chain.
  have h_chain : IsChain' (lift_chain_1 n C) := by
    exact lift_chain_1_is_chain n C hC.1;
  -- By definition of `IsSymmetricChain`, we know that `C.image card = Icc k (n - k)` for some `k`.
  obtain ⟨k, hk⟩ := hC;
  -- By definition of `IsSymmetricChain`, we know that `lift_chain_1 n C` has the correct
  -- cardinality image.
  obtain ⟨k', hk'⟩ := hk;
  have h_card_image : (lift_chain_1 n C).image card = Icc (k' + 1) ((n + 1) - (k' + 1)) := by
    convert lift_chain_1_card_image n C k' hk'.2 k hne using 1;
  -- We need to show that $k' + 1 \leq \frac{n + 1}{2}$.
  have h_k'_plus_1_le : k' + 1 ≤ (n + 1) / 2 := by
    -- Since $C$ is a symmetric chain, we know that $n - k' \geq k' + 1$.
    have h_n_minus_k'_ge_k'_plus_1 : n - k' ≥ k' + 1 := by
      contrapose! hne; aesop;
    omega;
  exact ⟨ h_chain, k' + 1, h_k'_plus_1_le, h_card_image ⟩

/-
Definition of lifting a chain and an SCD to the next dimension.
-/
def lift_chain (n : ℕ) (C : Finset (Finset (Fin n))) : Finset (Finset (Finset (Fin (n+1)))) :=
  if (lift_chain_1 n C).Nonempty then {lift_chain_0 n C, lift_chain_1 n C} else {lift_chain_0 n C}

def lift_SCD (n : ℕ) (X : Finset (Finset (Finset (Fin n)))) :
    Finset (Finset (Finset (Fin (n+1)))) :=
  X.biUnion (lift_chain n)

/-
Every chain in the lifted SCD is a symmetric chain.
-/
theorem lift_SCD_is_symmetric (n : ℕ) (X : Finset (Finset (Finset (Fin n))))
    (hX : ∀ C ∈ X, IsSymmetricChain n C) :
    ∀ C' ∈ lift_SCD n X, IsSymmetricChain (n + 1) C' := by
  -- Let C' be in lift_SCD n X. Then C' is in lift_chain n C for some C in X.
  intro C' hC'
  obtain ⟨C, hCX, hC'⟩ : ∃ C ∈ X, C' ∈ lift_chain n C := by
    exact mem_biUnion.mp hC';
  -- By definition of `lift_chain`, if `C'` is in `lift_chain n C`, then `C'` is either
  -- `lift_chain_0 n C` or `lift_chain_1 n C`.
  by_cases hC'' : C' = lift_chain_0 n C;
  · exact hC''.symm ▸ lift_chain_0_is_symmetric n C ( hX C hCX );
  · convert lift_chain_1_is_symmetric n C ( hX C hCX ) _ using 1;
    · unfold lift_chain at hC'; aesop;
    · unfold lift_chain at hC'; aesop;

/-
The union of the lifted chains covers exactly the embeddings of the original chain.
-/
lemma lift_chain_union_eq (n : ℕ) (C : Finset (Finset (Fin n)))
    (hC : IsChain' C) (hne : C.Nonempty) :
    (lift_chain n C).biUnion id = (C.image (embed n)) ∪ (C.image (embed_plus n)) := by
  rw [lift_chain];
  split_ifs <;> simp_all +decide [ Finset.ext_iff, lift_chain_1, lift_chain_0 ];
  · intro a; constructor;
    · rintro ( h | ⟨ x, hx, hx' ⟩ | ⟨ x, hx, hx' ⟩ );
      · exact Or.inr ⟨ chain_top C, chain_top_mem hC hne, fun x => by aesop ⟩;
      · exact Or.inl ⟨ x, hx, hx' ⟩;
      · grind;
    · rintro ( ⟨ x, hx, hx' ⟩ | ⟨ x, hx, hx' ⟩ );
      · exact Or.inr <| Or.inl ⟨ x, hx, fun y => by specialize hx' y; aesop ⟩;
      · by_cases hx'' : x = chain_top C;
        · aesop;
        · grind;
  · intro a;
    constructor;
    · rintro ( h | ⟨ b, hb, h ⟩ );
      · exact Or.inr ⟨ chain_top C, chain_top_mem hC hne, fun x => by specialize h x; aesop ⟩;
      · exact Or.inl ⟨ b, hb, h ⟩;
    · rintro ( ⟨ x, hx, hx' ⟩ | ⟨ x, hx, hx' ⟩ ) <;> simp_all +decide [ Fin.forall_fin_succ ];
      · exact Or.inr ⟨ x, hx, hx'.1, hx'.2 ⟩;
      · by_cases h : x = chain_top C <;> simp_all +decide [ Finset.ext_iff ];
        grind

/-
Recursive structure of the powerset.
-/
lemma PP_succ_eq (n : ℕ) :
    PP (n + 1) = (PP n).image (embed n) ∪ (PP n).image (embed_plus n) := by
  ext; simp [embed, embed_plus, PP];
  by_cases h : Fin.last n ∈ ‹Finset (Fin (n + 1))› <;> simp_all +decide [ Finset.ext_iff ];
  · right;
    use Finset.univ.filter (fun x => Fin.castSucc x ∈ ‹Finset (Fin (n + 1))›);
    intro a; induction a using Fin.lastCases <;> aesop;
  · left;
    use Finset.univ.filter (fun x => Fin.castSucc x ∈ ‹Finset (Fin (n + 1))›);
    intro a; induction a using Fin.lastCases <;> aesop;

/-
lift_chain_0 and lift_chain_1 are disjoint.
-/
lemma lift_chain_0_inter_lift_chain_1_eq_empty (n : ℕ) (C : Finset (Finset (Fin n))) :
    Disjoint (lift_chain_0 n C) (lift_chain_1 n C) := by
  norm_num [ Finset.disjoint_left, lift_chain_0, lift_chain_1 ];
  constructor;
  · intro x hx₁ hx₂ hx₃
    simp_all +decide [ Finset.ext_iff, embed_plus ] ;
    obtain ⟨ y, hy ⟩ := hx₁; specialize hx₃ ( Fin.castSucc y ) ; simp_all +decide
    simp_all +decide [ Finset.mem_map, embed ];
  · intro a ha x hx hx' H; have :=
    congr_arg ( fun s => s.card ) H; simp_all +decide [ card_embed ] ;
    unfold embed_plus embed at H; simp_all +decide [ Finset.ext_iff ] ;
    specialize H ( Fin.last n ) ; aesop

/-
The union of the lifted SCD is the powerset of n+1.
-/
lemma lift_SCD_union_eq (n : ℕ) (X : Finset (Finset (Finset (Fin n))))
    (hX_union : X.biUnion id = PP n)
    (hX_chain : ∀ C ∈ X, IsChain' C)
    (hX_nonempty : ∀ C ∈ X, C.Nonempty) :
    (lift_SCD n X).biUnion id = PP (n + 1) := by
  -- By definition of $lift_SCD$, we know that $(lift_SCD n X).biUnion id = \bigcup_{C \in X}
  -- (lift_chain n C).biUnion id$.
  have h_lift_union :
      (lift_SCD n X).biUnion id = Finset.biUnion X fun C => (lift_chain n C).biUnion id := by
    unfold lift_SCD; aesop;
  -- By definition of $lift_chain$, we know that $(lift_chain n C).biUnion id = (C.image (embed n))
  -- ∪ (C.image (embed_plus n))$.
  have h_lift_chain_union :
      ∀ C ∈ X, (lift_chain n C).biUnion id = (C.image (embed n)) ∪ (C.image (embed_plus n)) := by
    exact fun C a => lift_chain_union_eq n C (hX_chain C a) (hX_nonempty C a);
  rw [ h_lift_union, Finset.biUnion_congr rfl h_lift_chain_union ];
  convert congr_arg ( fun s => s.image ( embed n ) ∪ s.image ( embed_plus n ) ) hX_union using 1;
  · simp +decide [ Finset.ext_iff ];
    grind;
  · exact PP_succ_eq n

/-
If two chains are disjoint, their lifted versions cover disjoint sets of subsets.
-/
lemma lift_chain_disjoint_of_disjoint (n : ℕ) (C1 C2 : Finset (Finset (Fin n)))
    (h_disjoint : Disjoint C1 C2) (hC1 : IsChain' C1) (hC1_ne : C1.Nonempty)
    (hC2 : IsChain' C2) (hC2_ne : C2.Nonempty) :
    Disjoint ((lift_chain n C1).biUnion id) ((lift_chain n C2).biUnion id) := by
  refine' disjoint_iff_inf_le.mpr _;
  intro x hx;
  have hx_cases :
      x ∈ (C1.image (embed n)) ∪ (C1.image (embed_plus n))
        ∧ x ∈ (C2.image (embed n)) ∪ (C2.image (embed_plus n)) := by
    have hx_cases :
        (lift_chain n C1).biUnion id = (C1.image (embed n)) ∪ (C1.image (embed_plus n))
          ∧ (lift_chain n C2).biUnion id = (C2.image (embed n)) ∪ (C2.image (embed_plus n)) := by
      exact ⟨ lift_chain_union_eq n C1 hC1 hC1_ne, lift_chain_union_eq n C2 hC2 hC2_ne ⟩;
    grind;
  simp_all +decide [ Finset.disjoint_left, Finset.mem_image ];
  rcases hx_cases with ⟨ ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩, ⟨ b, hb, hb' ⟩ | ⟨ b, hb, hb' ⟩ ⟩<;>
    simp_all +decide [ Finset.ext_iff, embed, embed_plus ];
  · -- Since $a$ and $b$ are subsets of $\{0, 1, ..., n-1\}$, and their images under $Fin.castSucc$
    -- are equal, it follows that $a = b$.
    have h_eq : a = b := by
      ext x; specialize hb' ( Fin.castSucc x ) ; aesop;
    aesop;
  · specialize hb' ( Fin.last n ) ; aesop;
  · specialize hb' ( Fin.last n ) ; simp_all +decide
  · -- Since $a$ and $b$ are distinct elements in $C1$ and $C2$ respectively, and $C1$ and $C2$ are
    -- disjoint, this leads to a contradiction.
    have h_contradiction : a = b := by
      ext x; specialize hb' ( Fin.castSucc x ) ; aesop;
    aesop

/-
The lifted SCD consists of pairwise disjoint chains.
-/
lemma lift_SCD_pairwise_disjoint (n : ℕ) (X : Finset (Finset (Finset (Fin n))))
    (hX : (X : Set (Finset (Finset (Fin n)))).PairwiseDisjoint id)
    (hX_chain : ∀ C ∈ X, IsChain' C)
    (hX_nonempty : ∀ C ∈ X, C.Nonempty) :
    (lift_SCD n X : Set (Finset (Finset (Fin (n + 1))))).PairwiseDisjoint id := by
  intro C' hC' C'' hC'' hne; simp_all +decide [ Finset.disjoint_left ] ;
  -- Let's obtain the chains C1 and C2 in X such that C' is either lift_chain_0 n C1 or lift_chain_1
  -- n C1, and similarly for C''.
  obtain ⟨C1, hC1, hC1'⟩ : ∃ C1 ∈ X, C' ∈ lift_chain n C1 := by
    unfold lift_SCD at hC'; aesop;
  obtain ⟨C2, hC2, hC2'⟩ : ∃ C2 ∈ X, C'' ∈ lift_chain n C2 := by
    unfold lift_SCD at hC''; aesop;
  by_cases hC1C2 : C1 = C2;
  · simp_all +decide [ lift_chain ];
    split_ifs at hC1' hC2' <;> simp_all +decide
    cases hC1' <;> cases hC2' <;> simp_all +decide
    · exact fun x hx₁ hx₂ =>
      Finset.disjoint_left.mp ( lift_chain_0_inter_lift_chain_1_eq_empty n C2 ) hx₁ hx₂;
    · intro a ha hb; have :=
      lift_chain_0_inter_lift_chain_1_eq_empty n C2; simp_all +decide [ Finset.disjoint_left ] ;
  · have h_disjoint_lift : Disjoint ((lift_chain n C1).biUnion id) ((lift_chain n C2).biUnion id)
    := by
      apply lift_chain_disjoint_of_disjoint n C1 C2 (hX hC1 hC2 hC1C2) (hX_chain C1 hC1)
        (hX_nonempty C1 hC1) (hX_chain C2 hC2) (hX_nonempty C2 hC2);
    simp_all +decide [ Finset.disjoint_left ];
    exact fun a ha ha' => h_disjoint_lift _ hC1' ha _ hC2' ha'

/-
Existence of a Symmetric Chain Decomposition for P(n).
-/
/-- For every n, the poset (𝒫(n), ⊆) has a symmetric chain decomposition. -/
theorem exists_SCD (n : ℕ) : ∃ X, IsSymmetricChainDecomposition n X := by
  induction' n with n ih;
  · exists { { ∅ } };
    constructor <;> norm_num;
    · constructor <;> norm_num [ IsChain', IsSymmetricChain ];
    · decide +revert;
  · obtain ⟨ X, hX ⟩ := ih;
    refine' ⟨ _, _, _, _ ⟩;
    exact lift_SCD n X;
    · exact fun C hC => lift_SCD_is_symmetric n X ( fun C hC => hX.1 C hC ) C hC;
    · convert lift_SCD_pairwise_disjoint n X _ _ _ using 1;
      · exact hX.2.1;
      · exact fun C hC => hX.1 C hC |>.1;
      · exact fun C hC => symmetric_chain_nonempty ( hX.1 C hC );
    · apply_rules [ lift_SCD_union_eq ];
      · exact hX.2.2;
      · exact fun C hC => hX.1 C hC |>.1;
      · exact fun C hC => symmetric_chain_nonempty ( hX.1 C hC )

/-
Number of chains in an SCD.
-/
/-- Let m = ⌊n/2⌋ and N = bin(n, m). Every SCD of 𝒫(n) consists of exactly N chains. -/
theorem card_SCD (n : ℕ) (X : Finset (Finset (Finset (Fin n))))
    (hX : IsSymmetricChainDecomposition n X) :
    X.card = n.choose (n / 2) := by
  -- In any symmetric chain, the interval of sizes k, k+1, ..., n-k contains m.
  -- Thus each chain contains exactly one set of size m.
  -- Since the decomposition is a partition, distinct chains contain distinct m-sets.
  have h_chain_card : ∀ C ∈ X, ∃! m : Finset (Fin n), m.card = n / 2 ∧ m ∈ C := by
    intro C hC
    obtain ⟨k, hk⟩ : ∃ k, k ≤ n / 2 ∧ C.image card = Icc k (n - k) := by
      exact hX.1 C hC |>.2;
    -- Since $k \leq n / 2$, there exists a unique $m \in C$ such that $m.card = n / 2$.
    obtain ⟨m, hm⟩ : ∃ m ∈ C, m.card = n / 2 := by
      exact Finset.mem_image.mp ( hk.2.symm ▸ Finset.mem_Icc.mpr ⟨ by omega, by omega ⟩ )
        |> fun ⟨ m, hm₁, hm₂ ⟩ =>
        ⟨ m, hm₁, hm₂ ⟩;
    have h_unique : ∀ m' ∈ C, m'.card = n / 2 → m' = m := by
      intro m' hm' hm'_card
      have h_subset : m' ⊆ m ∨ m ⊆ m' := by
        have := hX.1 C hC;
        have := this.1;
        exact this.total hm' hm.1 |> Or.imp ( fun h => by tauto ) fun h => by tauto;
      cases h_subset <;> have := Finset.eq_of_subset_of_card_le ‹_› <;> aesop;
    exact ⟨ m, ⟨ hm.2, hm.1 ⟩, fun m' hm' => h_unique m' hm'.2 hm'.1 ⟩;
  -- Therefore, the set of m-sets in the decomposition is exactly the set of all m-sets in 𝒫(n).
  have h_m_set_eq : (Finset.biUnion X (fun C => Finset.filter (fun m =>
    m.card = n / 2) C)) = Finset.powersetCard (n / 2) (Finset.univ :
      Finset (Fin n)) := by
    ext m;
    have := hX.2.2; simp_all +decide [ Finset.ext_iff ] ;
    exact ⟨ fun ⟨ C, hC₁, hC₂, hC₃ ⟩ => hC₃, fun hC₃ => by
      obtain ⟨ C, hC₁, hC₂ ⟩ := this m |>.2 ( Finset.mem_powerset.mpr <| Finset.subset_univ m );
      exact ⟨ C, hC₁, hC₂, hC₃ ⟩ ⟩;
  -- Since each chain contains exactly one m-set, the number of chains is equal to the number of
  -- m-sets.
  have h_chain_count :
      X.card = (Finset.biUnion X (fun C => Finset.filter (fun m => m.card = n / 2) C)).card := by
    rw [ Finset.card_biUnion ];
    · rw [ Finset.sum_congr rfl fun x hx => Finset.card_eq_one.mpr <| by
      obtain ⟨ m, hm₁, hm₂ ⟩ := h_chain_card x hx;
      exact ⟨ m, by aesop ⟩ ] ; aesop;
    · intro C hC D hD hCD; have := hX.2.1 hC hD hCD; simp_all +decide [ Finset.disjoint_left ] ;
  rw [ h_chain_count, h_m_set_eq, Finset.card_powersetCard, Finset.card_fin ]

/-
Definition of comparable pairs.
-/
/-- The set of ordered pairs (A, B) in 𝒜 such that A ⊂ B. -/
def comparable_pairs {n : ℕ} (𝒜 : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (𝒜 ×ˢ 𝒜).filter (fun p => p.1 ⊂ p.2)

/-
The number of bad pairs is the sum of bin(t_C, 2).
-/
/-- The set of bad pairs for an SCD X and family 𝒜. -/
def bad_pairs (n : ℕ) (X : Finset (Finset (Finset (Fin n)))) (𝒜 : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (comparable_pairs 𝒜).filter (fun p => ∃ C ∈ X, p.1 ∈ C ∧ p.2 ∈ C)

lemma bad_pairs_card_eq_sum (n : ℕ) (X : Finset (Finset (Finset (Fin n))))
    (hX : IsSymmetricChainDecomposition n X) (𝒜 : Finset (Finset (Fin n))) :
    (bad_pairs n X 𝒜).card = ∑ C ∈ X, (𝒜 ∩ C).card.choose 2 := by
  unfold bad_pairs;
  have h_partition :
      ∀ C ∈ X, (Finset.filter (fun p =>
        p.1 ∈ C ∧ p.2 ∈ C) (comparable_pairs 𝒜)).card = Nat.choose (𝒜 ∩ C).card 2 := by
    intro C hC
    have h_chain : IsChain' C := by
      exact hX.1 C hC |>.1;
    -- Since $C$ is a chain, any two elements in $A \cap C$ are comparable.
    have h_comparable : ∀ A B :
        Finset (Fin n), A ∈ 𝒜 ∩ C → B ∈ 𝒜 ∩ C → A ≠ B → (A ⊂ B ∨ B ⊂ A) := by
      intros A B hA hB hAB
      have h_comparable : A ⊆ B ∨ B ⊆ A := by
        have :=
          h_chain ( Finset.mem_of_mem_inter_right hA ) ( Finset.mem_of_mem_inter_right hB ) ; aesop;
      grind;
    have h_comparable_pairs :
        Finset.filter (fun p => p.1 ∈ C ∧ p.2 ∈ C) (comparable_pairs 𝒜) = Finset.image (fun p =>
          (p.1, p.2)) (Finset.filter (fun p => p.1 ⊂ p.2) (Finset.offDiag (𝒜 ∩ C))) := by
      ext ⟨A, B⟩; simp [comparable_pairs];
      grind +ring;
    have h_comparable_pairs_card :
        Finset.card (Finset.filter (fun p =>
          p.1 ⊂ p.2) (Finset.offDiag (𝒜 ∩ C))) = Finset.card (Finset.offDiag (𝒜 ∩ C)) / 2 := by
      have h_comparable_pairs_card :
          Finset.card (Finset.filter (fun p =>
            p.1 ⊂ p.2) (Finset.offDiag (𝒜 ∩ C))) = Finset.card (Finset.filter (fun p =>
              p.2 ⊂ p.1) (Finset.offDiag (𝒜 ∩ C))) := by
        rw [ Finset.card_filter, Finset.card_filter ];
        apply Finset.sum_bij (fun p hp => (p.2, p.1));
        · grind;
        · grind;
        · aesop;
        · grind;
      have h_comparable_pairs_card :
          Finset.card (Finset.filter (fun p =>
            p.1 ⊂ p.2) (Finset.offDiag (𝒜 ∩ C))) + Finset.card (Finset.filter (fun p =>
              p.2 ⊂ p.1) (Finset.offDiag (𝒜 ∩ C))) = Finset.card (Finset.offDiag (𝒜 ∩ C)) := by
        rw [ ← Finset.card_union_of_disjoint ];
        · congr with p ; aesop;
        · simp +contextual [ Finset.disjoint_left, Finset.mem_filter ];
          exact fun a b ha ha' hb hb' hab h₁ h₂ =>
            hab <| Finset.Subset.antisymm ( h₁.subset ) ( h₂.subset );
      grind;
    simp_all +decide [ Nat.choose_two_right, Finset.offDiag_card ];
    rw [ Nat.mul_sub_left_distrib, Nat.mul_one ];
  rw [ ← Finset.sum_congr rfl h_partition, ← Finset.card_biUnion ];
  · congr with p ; aesop;
  · intro C hC D hD hCD; simp_all +decide [ Finset.disjoint_left ] ;
    intro a b hab ha hb ha' hb'; have := hX.2.1 hC hD; simp_all +decide [ Finset.disjoint_left ] ;

/-
Algebraic inequality for the number of bad pairs.
-/
lemma sum_choose_two_ge_x (n : ℕ) (X : Finset (Finset (Finset (Fin n))))
    (hX_card : X.card = n.choose (n / 2))
    (𝒜 : Finset (Finset (Fin n)))
    (x : ℕ)
    (h_card : 𝒜.card ≥ n.choose (n / 2) + x)
    (h_partition : X.biUnion id = PP n)
    (h_disjoint : (X : Set (Finset (Finset (Fin n)))).PairwiseDisjoint id) :
    ∑ C ∈ X, (𝒜 ∩ C).card.choose 2 ≥ x := by
  -- Since $|A| \geq N + x$, we have $\sum_{C \in X} |A \cap C| = |A|$.
  have h_sum_card : ∑ C ∈ X, (𝒜 ∩ C).card = 𝒜.card := by
    rw [ ← Finset.card_biUnion ];
    · convert congr_arg Finset.card ( show 𝒜 ∩ PP n = 𝒜 from ?_ ) using 1;
      · rw [ ← h_partition, Finset.inter_biUnion ];
        rfl;
      · exact Finset.inter_eq_left.mpr fun x hx => Finset.mem_powerset.mpr <| Finset.subset_univ _;
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hzx hzy =>
      Finset.disjoint_left.mp ( h_disjoint hx hy hxy ) ( Finset.mem_inter.mp hzx |>.2 ) (
        Finset.mem_inter.mp hzy |>.2 );
  -- Since $\binom{t}{2} \geq t - 1$ for all $t \geq 0$, we have $\sum_{C \in X} \binom{|A \cap
  -- C|}{2} \geq \sum_{C \in X} (|A \cap C| - 1)$.
  have h_binom_ge_sub_one : ∀ C ∈ X, (𝒜 ∩ C).card.choose 2 ≥ (𝒜 ∩ C).card - 1 := by
    intro C hC;
      rcases k : Finset.card ( 𝒜 ∩ C ) with ( _ | _ | k ) <;> simp_all +decide [ Nat.choose ] ;
    grind;
  refine' le_trans _ ( Finset.sum_le_sum h_binom_ge_sub_one );
  have h_sum_card_sub_one : ∑ C ∈ X, (𝒜 ∩ C).card - ∑ C ∈ X, 1 ≥ x := by
    simp_all +decide
    exact le_tsub_of_add_le_left h_card;
  refine le_trans h_sum_card_sub_one ?_;
  rw [ Nat.sub_le_iff_le_add ];
  simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_le_sum fun i hi => by omega;

/-
Every SCD has at least x bad ordered pairs from A.
-/
lemma bad_pairs_lower_bound (n : ℕ) (X : Finset (Finset (Finset (Fin n))))
    (hX : IsSymmetricChainDecomposition n X)
    (hX_card : X.card = n.choose (n / 2))
    (𝒜 : Finset (Finset (Fin n)))
    (x : ℕ)
    (h_card : 𝒜.card ≥ n.choose (n / 2) + x) :
    (bad_pairs n X 𝒜).card ≥ x := by
  rw [bad_pairs_card_eq_sum n X hX 𝒜]
  apply sum_choose_two_ge_x n X hX_card 𝒜 x h_card hX.2.2 hX.2.1

/-
Action of a permutation on a set.
-/
def permute_set {n : ℕ} (σ : Perm (Fin n)) (A : Finset (Fin n)) : Finset (Fin n) :=
  A.map σ.toEmbedding

/-
Action of a permutation on a family of sets.
-/
def permute_family {n : ℕ} (σ : Perm (Fin n)) (𝒜 : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  𝒜.map ⟨fun A => permute_set σ A, Finset.map_injective σ.toEmbedding⟩

/-
Permuting a set preserves its cardinality.
-/
lemma card_permute_set {n : ℕ} (σ : Perm (Fin n)) (A : Finset (Fin n)) :
    (permute_set σ A).card = A.card := by
  unfold permute_set; aesop;

lemma permute_set_eq_iff {n : ℕ} (σ : Perm (Fin n)) (U : Finset (Fin n)) :
    permute_set σ U = U ↔ ∀ x, σ x ∈ U ↔ x ∈ U := by
  constructor
  · intro h x
    constructor
    · intro hx
      have hx' : σ x ∈ permute_set σ U := by simpa [h]
      rw [permute_set] at hx'
      obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx'
      have hyx : y = x := σ.injective hxy
      simpa [hyx] using hy
    · intro hx
      have : σ x ∈ permute_set σ U := by
        rw [permute_set]
        exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
      simpa [h] using this
  · intro h
    ext y
    constructor
    · intro hy
      rw [permute_set] at hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      exact (h x).2 hx
    · intro hy
      rw [permute_set]
      refine Finset.mem_map.mpr ⟨σ.symm y, ?_, by simp⟩
      exact (h (σ.symm y)).1 (by simpa using hy)

/-
Permuting a family of sets preserves its cardinality.
-/
lemma card_permute_family {n : ℕ} (σ : Perm (Fin n)) (𝒜 : Finset (Finset (Fin n))) :
    (permute_family σ 𝒜).card = 𝒜.card := by
  unfold permute_family; aesop;

/-
For any permutation, the permuted family has at least x bad pairs in the fixed SCD.
-/
lemma bad_pairs_lower_bound_perm (n : ℕ) (X : Finset (Finset (Finset (Fin n))))
    (hX : IsSymmetricChainDecomposition n X)
    (hX_card : X.card = n.choose (n / 2))
    (𝒜 : Finset (Finset (Fin n)))
    (x : ℕ)
    (h_card : 𝒜.card ≥ n.choose (n / 2) + x)
    (σ : Perm (Fin n)) :
    (bad_pairs n X (permute_family σ 𝒜)).card ≥ x := by
  apply bad_pairs_lower_bound n X hX hX_card (permute_family σ 𝒜) x
  rw [card_permute_family]
  exact h_card

/-
The number of chains covering sizes a and b is at most bin(n, a) and bin(n, b).
-/
def num_chains_covering (n : ℕ) (X : Finset (Finset (Finset (Fin n)))) (a b : ℕ) : ℕ :=
  (X.filter (fun C => (∃ A ∈ C, A.card = a) ∧ (∃ B ∈ C, B.card = b))).card

lemma num_chains_covering_le_choose (n : ℕ) (X : Finset (Finset (Finset (Fin n))))
    (hX : IsSymmetricChainDecomposition n X) (a b : ℕ) :
    num_chains_covering n X a b ≤ n.choose a ∧ num_chains_covering n X a b ≤ n.choose b := by
  unfold num_chains_covering;
  constructor;
  · -- Each chain can cover at most one set of size $a$, so the number of chains covering size $a$
    -- is at most the number of sets of size $a$.
    have h_card_chains_covering_a : (Finset.filter (fun C =>
      ∃ A ∈ C, A.card = a) X).card ≤ (Finset.powersetCard a (Finset.univ :
        Finset (Fin n))).card := by
      have h_card_chains_covering_a : Finset.card (Finset.biUnion (Finset.filter (fun C =>
        ∃ A ∈ C, A.card = a) X) (fun C => C.filter (fun A =>
          A.card = a))) ≤ Finset.card (Finset.powersetCard a (Finset.univ :
          Finset (Fin n))) := by
        refine Finset.card_le_card ?_;
        grind;
      refine le_trans ?_ h_card_chains_covering_a;
      rw [ Finset.card_biUnion ];
      · refine' le_trans _ ( Finset.sum_le_sum fun x hx => Nat.one_le_iff_ne_zero.mpr _ );
        · norm_num;
        · aesop;
      · intro C hC D hD hCD; simp_all +decide [ Finset.disjoint_left ] ;
        intro A hA hA' hA''; have := hX.2.1 hC.1 hD.1; simp_all +decide [ Finset.disjoint_left ] ;
    exact le_trans ( Finset.card_le_card fun x hx =>
      by aesop ) ( h_card_chains_covering_a.trans ( by simp +decide [ Finset.card_univ ] ) );
  · -- Each chain in the set {C ∈ X | (∃ A ∈ C, A.card = a) ∧ ∃ B ∈ C, B.card = b} must contain at
    -- least one subset of size b.
    have h_subset_b :
        ∀ C ∈ {C ∈ X | (∃ A ∈ C, A.card = a) ∧ ∃ B ∈ C, B.card = b}, ∃ B ∈ C, B.card = b := by
      aesop;
    -- Since there are at most bin(n, b) subsets of size b in X, and each chain in the set contains
    -- at least one such subset, the number of chains in the set is at most bin(n, b).
    have h_card_b :
        (Finset.biUnion {C ∈ X | (∃ A ∈ C, A.card = a) ∧ ∃ B ∈ C, B.card = b} (fun C =>
          Finset.filter (fun B => B.card = b) C)).card ≤ Nat.choose n b := by
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.powersetCard b ( Finset.univ : Finset ( Fin n ) );
      · intro x hx; aesop;
      · simp +decide [ Finset.card_univ ];
    rw [ Finset.card_biUnion ] at h_card_b;
    · refine le_trans ?_ h_card_b;
      exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun x hx => Finset.card_pos.mpr <| by
        obtain ⟨ B, hB₁, hB₂ ⟩ := h_subset_b x hx;
        exact ⟨ B, Finset.mem_filter.mpr ⟨ hB₁, hB₂ ⟩ ⟩ );
    · intros C hC D hD hCD; simp_all +decide [ Finset.disjoint_left ] ;
      intro B hB hB' hB''; have := hX.2.1 hC.1 hD.1; simp_all +decide [ Finset.disjoint_left ] ;

/-
Definition of a pair landing in the same chain under a permutation.
-/
def pair_in_same_chain (n : ℕ) (X : Finset (Finset (Finset (Fin n)))) (A B : Finset (Fin n)) (σ :
  Perm (Fin n)) :
    Prop :=
  ∃ C ∈ X, permute_set σ A ∈ C ∧ permute_set σ B ∈ C

/-
Definitions of bad pair and the count of permutations mapping a pair to the same chain.
-/
def is_bad_pair {n : ℕ} (A B : Finset (Fin n)) : Prop :=
  A = ∅ ∧ B = univ

noncomputable def count_pair_in_same_chain (n : ℕ) (X : Finset (Finset (Finset (Fin n)))) (A B :
  Finset (Fin n)) :
    ℕ :=
  (univ.filter (fun σ => pair_in_same_chain n X A B σ)).card

/-
Definition of the container algorithm step and the function f(S).
degree_in G A v is the degree of v in the induced subgraph G[A].
container_algorithm runs the process described in the proof:
Iteratively remove high-degree vertices. If the vertex is in S, remove it and its neighbors. If not
in S, remove only the vertex.
-/
def degree_in {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
  (v : V) :
    ℕ :=
  (A.filter (G.Adj v ·)).card

def container_algorithm {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (S : Finset V) (A : Finset V) : Finset V :=
  if h : (A.filter (fun v => degree_in G A v ≥ Δ)).Nonempty then
    let v := (A.filter (fun v => degree_in G A v ≥ Δ)).min' h
    if v ∈ S then
      container_algorithm G Δ S (A \ (insert v (Finset.univ.filter (G.Adj v ·))))
    else
      container_algorithm G Δ S (A.erase v)
  else
    A
termination_by A.card
decreasing_by
refine' Finset.card_lt_card _;
simp +decide [ Finset.ssubset_def, Finset.subset_iff ];
exact ⟨ fun _ _ _ _ => by
  assumption, v, Finset.mem_filter.mp ( Finset.min'_mem _ h ) |>.1, fun _ _ =>
    False.elim ( ‹¬_› rfl ) ⟩;
  (
exact Finset.card_erase_lt_of_mem ( Finset.mem_filter.mp ( Finset.min'_mem _ h ) |>.1 ))

/-
Definition of the process that generates S and A from an independent set I.
generate_S_and_A runs the algorithm:
If v ∈ I, add v to S and remove v and neighbors from A.
If v ∉ I, remove v from A.
get_S extracts the final set S.
-/
def generate_S_and_A {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) (S_acc : Finset V) (A : Finset
      V) : Finset V × Finset V :=
  if h : (A.filter (fun v => degree_in G A v ≥ Δ)).Nonempty then
    let v := (A.filter (fun v => degree_in G A v ≥ Δ)).min' h
    if v ∈ I then
      generate_S_and_A G Δ I (insert v S_acc) (A \ (insert v (Finset.univ.filter (G.Adj v ·))))
    else
      generate_S_and_A G Δ I S_acc (A.erase v)
  else
    (S_acc, A)
termination_by A.card
decreasing_by
  refine' Finset.card_lt_card _;
  simp +decide [ Finset.ssubset_def, Finset.subset_iff ];
  exact ⟨ fun _ _ _ _ => by
    assumption, v, Finset.mem_filter.mp ( Finset.min'_mem _ h ) |>.1, fun _ _ =>
      False.elim ( ‹¬_› rfl ) ⟩;
    (
  exact Finset.card_erase_lt_of_mem ( Finset.mem_filter.mp ( Finset.min'_mem _ h ) |>.1 ))

def get_S {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) : Finset V :=
  (generate_S_and_A G Δ I ∅ Finset.univ).1

/-
The set S returned by the container algorithm is a subset of the input independent set I.
-/
lemma get_S_subset_I {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) :
    get_S G Δ I ⊆ I := by
      -- By induction on the recursive calls of `generate_S_and_A`, we can show that the first
      -- component is always a subset of `I`.
      have h_ind : ∀ (S_acc : Finset V) (A :
          Finset V), S_acc ⊆ I → (generate_S_and_A G Δ I S_acc A).1 ⊆ I := by
        intro S_acc A hS_acc
        induction' n : A.card using Nat.strong_induction_on with n ih generalizing S_acc A;
        unfold generate_S_and_A;
        field_simp;
        split_ifs <;> simp_all +decide [ Finset.subset_iff ];
        · convert ih _ _ _ _ _ rfl using 1;
          · rw [ ← n, Finset.card_sdiff ];
            refine' Nat.sub_lt _ _;
            · exact Finset.card_pos.mpr ( by
              obtain ⟨ v, hv ⟩ := ‹ { v ∈ A | Δ ≤ degree_in G A v }.Nonempty ›;
              exact ⟨ v, Finset.mem_filter.mp hv |>.1 ⟩ );
            · refine' Finset.card_pos.mpr ⟨ _, Finset.mem_inter.mpr ⟨ Finset.mem_insert_self _ _,
              _ ⟩ ⟩;
              exact Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1;
          · grind;
        · exact ih _ ( by
          rw [ Finset.card_erase_of_mem ( Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1 ) ];
          exact Nat.sub_lt ( Finset.card_pos.mpr ⟨ _,
            Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1 ⟩ ) zero_lt_one
            |> LT.lt.trans_le
            <| by linarith ) _ _ hS_acc rfl;
      exact h_ind ∅ _ ( Finset.empty_subset _ )

/-
The quantity (Δ+1)|S| + |A| is non-increasing during the algorithm.
-/
lemma generate_S_and_A_size_bound {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) (S_acc : Finset V) (A : Finset
      V) :
    let res := generate_S_and_A G Δ I S_acc A
    (Δ + 1) * res.1.card + res.2.card ≤ (Δ + 1) * S_acc.card + A.card := by
      induction' h : Finset.card A using Nat.strong_induction_on with k ih generalizing S_acc A;
      unfold generate_S_and_A;
      by_cases h : Finset.Nonempty ( Finset.filter ( fun v => degree_in G A v ≥ Δ ) A )<;>
        simp_all +decide;
      · split_ifs;
        · refine' le_trans ( ih _ _ _ _ rfl ) _;
          · refine' lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr _ ) ) _;
            exact A;
            · simp +decide [ Finset.subset_iff ];
              exact ⟨ fun x hx hx' hx'' => hx, fun hx =>
                False.elim <| hx <| Finset.mem_filter.mp ( Finset.min'_mem _ h ) |>.1 ⟩;
            · linarith;
          · rw [ Finset.card_sdiff ];
            have h_removed :
                Δ + 1 ≤
                  (insert (Finset.min' (Finset.filter (fun v => degree_in G A v ≥ Δ) A) h)
                    (Finset.univ.filter (G.Adj (Finset.min' (Finset.filter (fun v =>
                      degree_in G A v ≥ Δ) A) h) ·)) ∩ A).card := by
              let v := Finset.min' (Finset.filter (fun v => degree_in G A v ≥ Δ) A) h
              have hv := Finset.min'_mem (Finset.filter (fun v => degree_in G A v ≥ Δ) A) h
              have hvA : v ∈ A := (Finset.mem_filter.mp hv).1
              have hdeg : Δ ≤ degree_in G A v := (Finset.mem_filter.mp hv).2
              have hsub :
                  insert v (A.filter (G.Adj v ·)) ⊆
                    insert v (Finset.univ.filter (G.Adj v ·)) ∩ A := by
                intro x hx
                rw [Finset.mem_inter]
                rw [Finset.mem_insert] at hx ⊢
                rcases hx with rfl | hx
                · exact ⟨Or.inl rfl, hvA⟩
                · exact ⟨Or.inr (by simpa using (Finset.mem_filter.mp hx).2),
                    (Finset.mem_filter.mp hx).1⟩
              have hsmall :
                  degree_in G A v + 1 ≤
                    (insert v (Finset.univ.filter (G.Adj v ·)) ∩ A).card := by
                change (A.filter (G.Adj v ·)).card + 1 ≤
                  (insert v (Finset.univ.filter (G.Adj v ·)) ∩ A).card
                rw [← Finset.card_insert_of_notMem (s := A.filter (G.Adj v ·))]
                · exact Finset.card_le_card hsub
                · simp
              exact (Nat.succ_le_succ hdeg).trans hsmall
            refine' le_trans ( add_le_add_right ( Nat.sub_le_sub_left h_removed A.card ) _ ) _;
            · by_cases h : Finset.min' ( Finset.filter ( fun v =>
              degree_in G A v ≥ Δ ) A ) ‹_› ∈ S_acc<;>
              simp_all +decide [ Finset.card_insert_of_notMem ];
              linarith [ Nat.sub_add_cancel ( show Δ + 1 ≤ k from by
                                                have h_deg :
                                                    degree_in G A (Finset.min' (Finset.filter (fun
                                                      v =>
                                                      degree_in G A v ≥ Δ) A) ‹_›) ≥ Δ := by
                                                  exact Finset.mem_filter.mp ( Finset.min'_mem _
                                                    ‹_› ) |>.2;
                                                have h_deg :
                                                    degree_in G A (Finset.min' (Finset.filter (fun
                                                      v =>
                                                      degree_in G A v
                                                        ≥ Δ) A) ‹_›) < Finset.card A := by
                                                  refine' lt_of_lt_of_le ( Finset.card_lt_card (
                                                    Finset.filter_ssubset.mpr _ ) ) _;
                                                  · exact ⟨ _, Finset.min'_mem _ ‹_›
                                                    |> Finset.mem_filter.mp |>.1, by simp +decide ⟩;
                                                  · rfl;
                                                linarith ) ];
        · have :=
          ih ( Finset.card ( A.erase ( Finset.min' ( Finset.filter ( fun v =>
            Δ
              ≤ degree_in G A v ) A ) h ) ) ) ?_ S_acc ( A.erase ( Finset.min' ( Finset.filter (
                fun v =>
              Δ ≤ degree_in G A v ) A ) h ) ) ?_;
          · exact this.trans ( add_le_add_right ( by
              have hAcard : A.card = k := by assumption
              exact ( Finset.card_le_card ( Finset.erase_subset _ _ ) ).trans ( le_of_eq hAcard ) )
                _ );
          · exact lt_of_lt_of_le ( Finset.card_erase_lt_of_mem ( Finset.mem_filter.mp (
            Finset.min'_mem _ h ) |>.1 ) ) ( by linarith );
          · rfl;
      · grind

/-
The generated S set is contained in the union of the accumulator and the independent set I.
-/
lemma generate_S_subset_union {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) (S_acc : Finset V) (A : Finset
      V) :
    (generate_S_and_A G Δ I S_acc A).1 ⊆ S_acc ∪ I := by
      induction' A using Finset.strongInduction with A ih generalizing S_acc;
      unfold generate_S_and_A;
      norm_num +zetaDelta at *;
      split_ifs;
      · refine' Finset.Subset.trans ( ih _ _ _ ) _;
        · simp +decide [ Finset.ssubset_def, Finset.subset_iff ];
          exact ⟨ fun x hx hx' hx'' =>
            hx, _, Finset.min'_mem _ ‹_› |> Finset.mem_filter.mp |>.1, fun _ => by tauto ⟩;
        · grind;
      · exact ih _ ( Finset.erase_ssubset
        <| Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1 ) _;
      · exact Finset.subset_union_left

/-
The accumulator set is a subset of the generated S set.
-/
lemma S_acc_subset_generate_S {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) (S_acc : Finset V) (A : Finset
      V) :
    S_acc ⊆ (generate_S_and_A G Δ I S_acc A).1 := by
      induction' h : A.card using Nat.strong_induction_on with k ih generalizing S_acc A;
      unfold generate_S_and_A;
      field_simp;
      split_ifs <;> simp_all +decide [ Finset.subset_iff ];
      · intro x hx;
        convert ih _ _ _ _ rfl ( Finset.mem_insert_of_mem hx ) using 1;
        refine' lt_of_lt_of_le ( Finset.card_lt_card _ ) _;
        exact A;
        · simp +decide [ Finset.ssubset_def, Finset.subset_iff ];
          exact ⟨ fun _ _ _ _ =>
            by assumption, _, Finset.min'_mem _ ‹_› |> Finset.mem_filter.mp |>.1, fun _ _ =>
              by tauto ⟩;
        · linarith;
      · exact ih _ ( by
        rw [ Finset.card_erase_of_mem ( Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1 ) ];
        exact Nat.sub_lt ( Finset.card_pos.mpr ⟨ _,
          Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1 ⟩ ) zero_lt_one
          |> LT.lt.trans_le
          <| by simp +decide [ h ] ) _ _ rfl

/-
The independent set I restricted to A is covered by the new elements in S and the final set A,
assuming S_acc and A are disjoint.
-/
lemma generate_S_and_A_invariant {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) (S_acc : Finset V) (A : Finset
      V)
    (hI : G.IsIndepSet (I : Set V)) (h_disjoint : Disjoint S_acc A) :
    let res := generate_S_and_A G Δ I S_acc A
    I ∩ A ⊆ (res.1 \ S_acc) ∪ res.2 := by
      induction' n : A.card using Nat.strong_induction_on with n ih generalizing S_acc A;
      unfold generate_S_and_A;
      split_ifs <;> simp_all +decide [ Finset.subset_iff ];
      split_ifs;
      · intro x hx hx';
        by_cases hx'' : x = Finset.min' ( Finset.filter ( fun v => Δ ≤ degree_in G A v ) A ) ‹_›;
        · refine' Or.inl ⟨ _, _ ⟩;
          · exact S_acc_subset_generate_S _ _ _ _ _ |> fun h =>
            h ( Finset.mem_insert_self _ _ ) |> fun h => hx''.symm ▸ h;
          · exact fun h => Finset.disjoint_left.mp h_disjoint h hx';
        · convert ih _ _ _ _ _ rfl hx _ using 1;
          · grind;
          · refine' lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr _ ) ) _;
            exact A;
            · simp_all +decide [ Finset.subset_iff ];
              exact fun h => False.elim <| h <| Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1;
            · rw [ n ];
          · simp_all +decide [ Finset.disjoint_left ];
          · simp_all +decide [ Finset.disjoint_left, SimpleGraph.adj_comm ];
            (expose_names; exact hI hx h_1 hx'');
      · intro x hxI hx;
        specialize ih ( Finset.card ( A.erase ( Finset.min' _ ‹_› ) ) ) ?_ S_acc ( A.erase (
          Finset.min' _ ‹_› ) ) ?_ ?_ hxI ?_<;>
          simp_all +decide [ Finset.disjoint_left ];
        · rw [ ← n, Finset.card_erase_of_mem ( Finset.min'_mem _ ‹_›
          |> Finset.mem_filter.mp |>.1 ) ] ;
          exact Nat.pred_lt ( ne_bot_of_gt ( Finset.card_pos.mpr ⟨ _, Finset.min'_mem _ ‹_›
            |> Finset.mem_filter.mp |>.1 ⟩ ) );
        · exact fun h => ‹¬_› ( h ▸ hxI )

/-
The container algorithm produces the same set A as the generation process, given consistent inputs.
-/
lemma container_algorithm_eq_generate_A_correct {V : Type*} [Fintype V]
  [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (I : Finset V) (S_acc : Finset V) (A : Finset
      V)
    (h_disjoint : Disjoint S_acc A) (h_S_acc_sub : S_acc ⊆ I) :
    let res := generate_S_and_A G Δ I S_acc A
    container_algorithm G Δ res.1 A = res.2 := by
      induction' A using Finset.strongInduction with A ih generalizing S_acc I Δ G;
      unfold generate_S_and_A container_algorithm;
      split_ifs <;> simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
      split_ifs;
      · convert ih _ _ _ _ _ _ _ _ _ using 1;
        rotate_left;
        exact A \ insert ( Finset.min' ( Finset.filter ( fun v =>
          degree_in G A v
            ≥ Δ ) A ) ‹_› ) ( Finset.univ.filter ( G.Adj ( Finset.min' ( Finset.filter ( fun v =>
            degree_in G A v ≥ Δ ) A ) ‹_› ) · ) );
        grind;
        exact ( Finset.min' ( Finset.filter ( fun v => degree_in G A v ≥ Δ ) A ) ‹_› );
        exact Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1;
        simp +decide [ Finset.mem_sdiff, Finset.mem_insert ];
        exact G;
        (expose_names; exact inst_3);
        exact Δ;
        exact I;
        exact insert ( Finset.min' ( Finset.filter ( fun v => degree_in G A v ≥ Δ ) A ) ‹_› ) S_acc;
        simp +decide [ Finset.disjoint_left, Finset.mem_sdiff, Finset.mem_insert ];
        exact ⟨ fun h => fun _ _ _ => h, fun h => h ( fun x hx hx' hx'' => by
          have := Finset.disjoint_left.mp h_disjoint hx hx';
          contradiction ) ‹_› h_S_acc_sub ⟩;
      · rename_i h₁ h₂ h₃;
        contrapose! h₃;
        exact Finset.mem_of_subset ( S_acc_subset_generate_S G Δ I ( insert _ S_acc ) _ ) (
          Finset.mem_insert_self _ _ );
      · convert ih ( A.erase ( Finset.min' ( Finset.filter ( fun v =>
        degree_in G A v ≥ Δ ) A ) ‹_› ) ) ( fun x hx =>
          Finset.mem_of_mem_erase hx ) _ ( Finset.min'_mem ( Finset.filter ( fun v =>
            degree_in G A v ≥ Δ ) A ) ‹_› |> Finset.mem_filter.mp |>.1 ) _ _ _ _ _ using 1;
        any_goals assumption;
        · have h_subset : (generate_S_and_A G Δ I S_acc (A.erase (Finset.min' (Finset.filter (fun v
          =>
          degree_in G A v ≥ Δ) A) ‹_›))).1 ⊆ S_acc ∪ I := by
            (expose_names;
              exact
                generate_S_subset_union G Δ I S_acc
                  (A.erase ({v ∈ A | degree_in G A v ≥ Δ}.min' h)));
          have := h_subset ‹_›; simp_all +decide [ Finset.subset_iff ] ;
        · (expose_names; exact notMem_erase ({v ∈ A | degree_in G A v ≥ Δ}.min' h) A);
      · convert ih ( A.erase ( Finset.min' ( Finset.filter ( fun v =>
        Δ ≤ degree_in G A v ) A ) ‹_› ) ) ( fun x hx =>
          Finset.mem_of_mem_erase hx ) _ ( Finset.min'_mem ( Finset.filter ( fun v =>
            Δ ≤ degree_in G A v ) A ) ‹_› |> fun h =>
              Finset.mem_filter.mp h |>.1 ) _ _ _ _ _ _ _ using 1;
        · grind;
        · exact h_disjoint.mono_right ( Finset.erase_subset _ _ );
        · assumption

/-
The container algorithm always returns a set where every vertex has degree strictly less than Δ in
the induced subgraph.
-/
def is_low_degree {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (A :
  Finset V) :
    Prop :=
  ∀ v ∈ A, degree_in G A v < Δ

lemma container_algorithm_returns_low_degree {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (S : Finset V) (A : Finset V) :
    is_low_degree G Δ (container_algorithm G Δ S A) := by
      induction' A using Finset.strongInductionOn with A ih generalizing S;
      simp +decide [ is_low_degree ];
      unfold container_algorithm;
      split_ifs <;> simp_all +decide [ Finset.min' ];
      split_ifs;
      · convert ih _ _ _ using 1;
        simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
        exact ⟨ _, Finset.mem_filter.mp ( Finset.min'_mem _ ‹_› ) |>.1, fun _ =>
          False.elim <| ‹¬_› rfl ⟩;
      · exact ih _ ( Finset.erase_ssubset ( Finset.min'_mem _ ‹_› |> fun x =>
        Finset.mem_filter.mp x |>.1 ) ) _

/-
The container algorithm returns a set inducing a subgraph with maximum degree strictly less than Δ.
-/
lemma container_algorithm_max_degree {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : Δ ≥ 1) (S : Finset V) (A : Finset V) :
    (G.induce (container_algorithm G Δ S A)).maxDegree < Δ := by
      let C := container_algorithm G Δ S A
      have hlow : is_low_degree G Δ C := container_algorithm_returns_low_degree G Δ S A
      have hdeg : ∀ v : (C : Set V), (G.induce (C : Set V)).degree v = degree_in G C v := by
        intro v
        unfold SimpleGraph.degree degree_in
        refine Finset.card_bij (fun x hx => (x : V)) ?_ ?_ ?_
        · intro x hx
          simp [SimpleGraph.mem_neighborFinset] at hx ⊢
          exact hx
        · intro x hx y hy hxy
          exact Subtype.ext hxy
        · intro y hy
          refine ⟨⟨y, (Finset.mem_filter.mp hy).1⟩, ?_, rfl⟩
          simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp hy).2
      refine lt_of_le_of_lt ((G.induce (C : Set V)).maxDegree_le_of_forall_degree_le (Δ - 1) ?_) ?_
      · intro v
        rw [hdeg v]
        exact Nat.le_pred_of_lt (hlow v v.2)
      · omega

/-
The Graph Container Lemma: For every independent set I, there is a small subset S such that I is
contained in S ∪ f(S) and f(S) induces a graph with small maximum degree.
-/
theorem graph_container_lemma {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : Δ ≥ 1) :
    ∃ f : Finset V → Finset V,
      ∀ I : Finset V, G.IsIndepSet (I : Set V) →
        ∃ S, S ⊆ I ∧
             S.card ≤ Fintype.card V / (Δ + 1) ∧
             I ⊆ S ∪ f S ∧
             (G.induce (f S)).maxDegree < Δ := by
               refine' ⟨ _, fun I hI => _ ⟩;
               exact fun S => container_algorithm G Δ S Finset.univ;
               refine' ⟨ get_S G Δ I, get_S_subset_I G Δ I, _, _, _ ⟩;
               · have := generate_S_and_A_size_bound G Δ I ∅ Finset.univ;
                 rw [ Nat.le_div_iff_mul_le ] <;> norm_num at * ; linarith!;
               · -- By definition of `get_S`, we know that `get_S G Δ I` is the first component of
                 -- the result of `generate_S_and_A G Δ I ∅ Finset.univ`.
                 have h_generate :
                     let res := generate_S_and_A G Δ I ∅ Finset.univ;
                       get_S G Δ I = res.1
                         ∧ container_algorithm G Δ (get_S G Δ I) Finset.univ = res.2 := by
                   exact
                     ⟨ rfl,
                       container_algorithm_eq_generate_A_correct G Δ I ∅ Finset.univ
                         ( by simp +decide ) ( by simp +decide ) ⟩;
                 have := generate_S_and_A_invariant G Δ I ∅ Finset.univ hI; aesop;
               · exact container_algorithm_max_degree G Δ hΔ (get_S G Δ I) univ

/-
For integers $M\ge 1$ and $1\le t\le M/2$,
\[
\sum_{i=0}^{t}\binom{M}{i}\le \left(\frac{eM}{t}\right)^t.
\]
-/
lemma binom_tail_bound (M : ℕ) (t : ℕ) (hM : M ≥ 1) (ht1 : 1 ≤ t) (ht2 : t ≤ M / 2) :
    (∑ i ∈ range (t + 1), (M.choose i : ℝ)) ≤ (Real.exp 1 * M / t) ^ t := by
      -- The RHS is bounded by $(M/t)^t \sum_{i=0}^M \binom{M}{i} (t/M)^i = (M/t)^t (1 + t/M)^M$.
      have h_rhs_bound : (∑ i ∈ Finset.range (t + 1), (M.choose i : ℝ)) ≤ (M / t :
          ℝ) ^ t * (1 + t / M) ^ M := by
        -- We have $\sum_{i=0}^t \binom{M}{i} \le (M/t)^t \sum_{i=0}^t \binom{M}{i} (t/M)^i$.
        have h_sum_bound : (∑ i ∈ Finset.range (t + 1), (M.choose i : ℝ))
          ≤ (M / t : ℝ) ^ t * (∑ i ∈ Finset.range (t + 1), (M.choose i :
            ℝ) * (t / M) ^ i) := by
          rw [ Finset.mul_sum _ _ _ ];
          -- For each term in the sum, we have $\left(\frac{M}{t}\right)^t
          -- \left(\frac{t}{M}\right)^i \geq 1$ because $t \leq M/2$.
          have h_term : ∀ i ∈ Finset.range (t + 1), (M / t : ℝ) ^ t * (t / M : ℝ) ^ i ≥ 1 := by
            -- Since $t \leq M/2$, we have $t/M \leq 1/2$. Therefore, $(t/M)^i \leq (t/M)^t$ for $i
            -- \leq t$.
            have h_term_bound : ∀ i ∈ Finset.range (t + 1), (t / M : ℝ) ^ i ≥ (t / M : ℝ) ^ t := by
              exact fun i hi =>
                pow_le_pow_of_le_one ( by positivity )
                  ( div_le_one_of_le₀
                    ( by
                      norm_cast
                      linarith [ Nat.div_mul_le_self M 2 ] )
                    ( by positivity ) )
                  ( by linarith [ Finset.mem_range.mp hi ] );
            exact fun i hi => le_trans ( by
              ring_nf;
              norm_num [ show M ≠ 0 by linarith, show t ≠ 0 by linarith ] ) (
                mul_le_mul_of_nonneg_left ( h_term_bound i hi ) ( by positivity ) ) ;
          exact Finset.sum_le_sum fun i hi =>
            by nlinarith only [ h_term i hi, show ( M.choose i : ℝ ) ≥ 0 by positivity ] ;
        refine le_trans h_sum_bound ?_;
        rw [ add_comm 1 _, add_pow ] ; norm_num [ mul_comm ];
        exact mul_le_mul_of_nonneg_left ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono
          ( by linarith [ Nat.div_mul_le_self M 2 ] ) ) fun _ _ _ =>
          mul_nonneg ( pow_nonneg ( by positivity ) _ ) ( Nat.cast_nonneg _ ) ) ( by positivity );
      -- Using $1+u \le e^u$, we have $(1+t/M)^M \le (e^{t/M})^M = e^t$.
      have h_exp_bound : (1 + t / M : ℝ) ^ M ≤ Real.exp t := by
        rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ];
        exact Real.exp_le_exp.mpr ( by
          nlinarith [ Real.log_le_sub_one_of_pos ( by positivity : 0 < ( 1 + t / M : ℝ ) ),
            show ( t : ℝ ) / M ≥ 0 by positivity,
            mul_div_cancel₀ ( t : ℝ ) ( by positivity : ( M : ℝ ) ≠ 0 ) ] );
      convert h_rhs_bound.trans ( mul_le_mul_of_nonneg_left h_exp_bound <| by positivity ) using 1;
      ring_nf
      norm_num [ Real.exp_nat_mul, Real.exp_neg, Real.exp_log ]
      ring

/-
`permute_set` is compatible with permutation multiplication.
-/
lemma permute_set_mul {n : ℕ} (σ τ : Perm (Fin n)) (S : Finset (Fin n)) :
    permute_set (σ * τ) S = permute_set σ (permute_set τ S) := by
      simp +decide [ Finset.ext_iff, permute_set ];
      exact fun a => Eq.to_iff rfl

/-
If $A \subseteq B$ and $A' \subseteq B'$ with matching cardinalities, there is a permutation mapping
$A$ to $A'$ and $B$ to $B'$.
-/
lemma exists_perm_mapping_pair {n : ℕ} {A B A' B' : Finset (Fin n)}
    (hA : A ⊆ B) (hA' : A' ⊆ B') (h_card_A : A.card = A'.card) (h_card_B : B.card = B'.card) :
    ∃ σ : Perm (Fin n), permute_set σ A = A' ∧ permute_set σ B = B' := by
      classical
      let f : ↥A ≃ ↥A' := Fintype.equivOfCardEq (by simpa using h_card_A)
      have h_card_diff : (B \ A).card = (B' \ A').card := by
        rw [Finset.card_sdiff_of_subset hA, Finset.card_sdiff_of_subset hA', h_card_A, h_card_B]
      let g : ↥(B \ A) ≃ ↥(B' \ A') := Fintype.equivOfCardEq
        ((Fintype.card_coe (B \ A)).trans (h_card_diff.trans (Fintype.card_coe (B' \ A')).symm))
      let phi : Fin n → Fin n := fun x =>
        if hxA : x ∈ A then (f ⟨x, hxA⟩ : Fin n)
        else if hxB : x ∈ B then (g ⟨x, by simp [hxB, hxA]⟩ : Fin n)
        else x
      have hphi_maps : B.image phi ⊆ (Finset.univ : Finset (Fin n)) := by
        intro x hx
        simp
      have hphi_inj : Set.InjOn phi (B : Set (Fin n)) := by
        intro x hxB y hyB hxy
        have hxBf : x ∈ B := by simpa using hxB
        have hyBf : y ∈ B := by simpa using hyB
        dsimp [phi] at hxy
        by_cases hxA : x ∈ A
        · by_cases hyA : y ∈ A
          · simp [hxA, hyA] at hxy
            exact hxy
          · simp [hxA, hyA, hyBf] at hxy
            have hxmem : (f ⟨x, hxA⟩ : Fin n) ∈ A' := (f ⟨x, hxA⟩).2
            have hynot : (g ⟨y, by simp [hyBf, hyA]⟩ : Fin n) ∉ A' := by
              exact (Finset.mem_sdiff.mp (g ⟨y, by simp [hyBf, hyA]⟩).2).2
            exact False.elim (hynot (hxy ▸ hxmem))
        · by_cases hyA : y ∈ A
          · simp [hxA, hxBf, hyA] at hxy
            have hxnot : (g ⟨x, by simp [hxBf, hxA]⟩ : Fin n) ∉ A' := by
              exact (Finset.mem_sdiff.mp (g ⟨x, by simp [hxBf, hxA]⟩).2).2
            have hymem : (f ⟨y, hyA⟩ : Fin n) ∈ A' := (f ⟨y, hyA⟩).2
            exact False.elim (hxnot (hxy.symm ▸ hymem))
          · simp [hxA, hxBf, hyA, hyBf] at hxy
            exact hxy
      obtain ⟨e, he⟩ := Finset.exists_equiv_extend_of_card_eq
        (α := Fin n) (β := Fin n) (t := (Finset.univ : Finset (Fin n)))
        (by simp) hphi_maps hphi_inj
      let eu : (Finset.univ : Finset (Fin n)) ≃ Fin n := {
        toFun x := x
        invFun x := ⟨x, Finset.mem_univ x⟩
        left_inv x := by ext; rfl
        right_inv x := by rfl
      }
      let σ : Perm (Fin n) := e.trans eu
      have hσ_on_B : ∀ x ∈ B, σ x = phi x := by
        intro x hx
        exact he x hx
      refine ⟨σ, ?_, ?_⟩
      · refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro y hy
          rw [permute_set] at hy
          obtain ⟨x, hxA, hxy⟩ := Finset.mem_map.mp hy
          subst y
          change σ x ∈ A'
          rw [hσ_on_B x (hA hxA)]
          simp [phi, hxA]
        · rw [card_permute_set, h_card_A]
      · refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro y hy
          rw [permute_set] at hy
          obtain ⟨x, hxB, hxy⟩ := Finset.mem_map.mp hy
          subst y
          change σ x ∈ B'
          rw [hσ_on_B x hxB]
          by_cases hxA : x ∈ A
          · exact hA' (by simp [phi, hxA])
          · simp [phi, hxA, hxB]
            exact (Finset.mem_sdiff.mp (g ⟨x, by simp [hxB, hxA]⟩).2).1
        · rw [card_permute_set, h_card_B]

/-
The number of permutations mapping $(A, B)$ to $(A', B')$ is equal to the number of permutations
mapping $(A, B)$ to itself.
-/
lemma card_filter_perm_map_pair_eq_card_stabilizer_pair {n : ℕ} {A B A' B' : Finset (Fin n)}
    (hA : A ⊆ B) (hA' : A' ⊆ B') (h_card_A : A.card = A'.card) (h_card_B : B.card = B'.card) :
    (univ.filter (fun σ : Perm (Fin n) => permute_set σ A = A' ∧ permute_set σ B = B')).card =
    (univ.filter (fun σ : Perm (Fin n) => permute_set σ A = A ∧ permute_set σ B = B)).card := by
      -- By `exists_perm_mapping_pair`, there exists a permutation $\tau$ such that $\tau(A)=A'$ and
      -- $\tau(B)=B'$.
      obtain ⟨τ, hτ⟩ : ∃ τ : Perm (Fin n), permute_set τ A = A' ∧ permute_set τ B = B' := by
        exact exists_perm_mapping_pair hA hA' h_card_A h_card_B;
      refine' Finset.card_bij ( fun σ _ => τ⁻¹ * σ ) _ _ _ <;> simp_all +decide
      · intro σ hσA hσB; have :=
        congr_arg ( fun x => permute_set ( τ⁻¹ ) x ) hσA; have :=
          congr_arg ( fun x => permute_set ( τ⁻¹ ) x ) hσB; simp_all +decide [ permute_set_mul ] ;
        simp +decide [ ← hτ, permute_set ];
        simp +decide [ Function.comp, Finset.map ];
      · intro σ hσ₁ hσ₂; use τ * σ; simp_all +decide [ permute_set ] ;
        simp_all +decide [ Finset.ext_iff, Equiv.toEmbedding ];
        grind +ring

/-
For $A \subseteq B$, a permutation stabilizes both $A$ and $B$ if and only if it stabilizes both $A$
and $B \setminus A$.
-/
lemma stabilizer_subset_pair_iff {n : ℕ} {A B : Finset (Fin n)} {σ : Perm (Fin n)} (h : A ⊆ B) :
    permute_set σ A = A ∧ permute_set σ B = B ↔ permute_set σ A = A
      ∧ permute_set σ (B \ A) = B \ A := by
      constructor <;> intro h <;> have :=
        h.1 <;> have := h.2 <;> simp_all +decide [ Finset.ext_iff, permute_set ];
      grind +ring

/-
The number of permutations stabilizing two disjoint sets $S$ and $T$ is $|S|! |T|! (n - (|S| +
|T|))!$.
-/
lemma card_stabilizer_disjoint_pair {n : ℕ} {S T : Finset (Fin n)} (h_disjoint : Disjoint S T) :
    (univ.filter (fun σ : Perm (Fin n) => permute_set σ S = S ∧ permute_set σ T = T)).card =
    (Nat.factorial S.card) * (Nat.factorial T.card) * (Nat.factorial (n - (S.card + T.card))) := by
      classical
      let color : Fin n → Fin 3 := fun x => if x ∈ S then 0 else if x ∈ T then 1 else 2
      have hS_color : ∀ x, color x = 0 ↔ x ∈ S := by
        intro x
        dsimp [color]
        by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;> simp [hxS, hxT]
      have hT_color : ∀ x, color x = 1 ↔ x ∈ T := by
        intro x
        dsimp [color]
        by_cases hxS : x ∈ S
        · have hxTfalse : x ∉ T := fun hxT => (Finset.disjoint_left.mp h_disjoint) hxS hxT
          simp [hxS, hxTfalse]
        · by_cases hxT : x ∈ T <;> simp [hxS, hxT]
      have hP : ∀ σ : Perm (Fin n),
          (permute_set σ S = S ∧ permute_set σ T = T) ↔ color ∘ σ = color := by
        intro σ
        constructor
        · intro h
          funext x
          have hS := (permute_set_eq_iff σ S).1 h.1 x
          have hT := (permute_set_eq_iff σ T).1 h.2 x
          dsimp [Function.comp, color]
          by_cases hxS : x ∈ S
          · simp [hxS, hS.2 hxS]
          · have hσS : σ x ∉ S := by intro hbad; exact hxS (hS.1 hbad)
            by_cases hxT : x ∈ T
            · simp [hxS, hσS, hxT, hT.2 hxT]
            · have hσT : σ x ∉ T := by intro hbad; exact hxT (hT.1 hbad)
              simp [hxS, hσS, hxT, hσT]
        · intro h
          constructor
          · rw [permute_set_eq_iff]
            intro x
            rw [← hS_color (σ x), ← hS_color x]
            rw [show color (σ x) = color x by simpa [Function.comp] using congr_fun h x]
          · rw [permute_set_eq_iff]
            intro x
            rw [← hT_color (σ x), ← hT_color x]
            rw [show color (σ x) = color x by simpa [Function.comp] using congr_fun h x]
      have hfilter :
          (univ.filter (fun σ : Perm (Fin n) => permute_set σ S = S ∧ permute_set σ T = T)).card =
            Fintype.card {σ : Perm (Fin n) // color ∘ σ = color} := by
        rw [Fintype.card_subtype]
        congr 1
        ext σ
        simp [hP σ]
      rw [hfilter, DomMulAct.stabilizer_card color]
      have h0 : Fintype.card {x : Fin n // color x = 0} = S.card := by
        rw [Fintype.card_subtype]
        congr 1
        ext x
        simpa using hS_color x
      have h1 : Fintype.card {x : Fin n // color x = 1} = T.card := by
        rw [Fintype.card_subtype]
        congr 1
        ext x
        simpa using hT_color x
      have h2 : Fintype.card {x : Fin n // color x = 2} = n - (S.card + T.card) := by
        rw [Fintype.card_subtype]
        have hcomp : (Finset.univ.filter fun x : Fin n => color x = 2) = Finset.univ \ (S ∪ T) := by
          ext x
          dsimp [color]
          by_cases hxS : x ∈ S
          · simp [hxS]
          · by_cases hxT : x ∈ T <;> simp [hxS, hxT]
        rw [hcomp, Finset.card_sdiff_of_subset (by intro x hx; simp), Finset.card_univ]
        rw [Fintype.card_fin]
        rw [Finset.card_union_of_disjoint h_disjoint]
      rw [Fin.prod_univ_three]
      simp [h0, h1, h2]

/-
The number of permutations of $[n]$ that map $A$ to $A$ and $B$ to $B$ (where $A \subseteq B$) is
$|A|! (|B|-|A|)! (n-|B|)!$.
-/
lemma card_stabilizer_pair {n : ℕ} {A B : Finset (Fin n)} (hA : A ⊆ B) :
    (univ.filter (fun σ : Perm (Fin n) => permute_set σ A = A ∧ permute_set σ B = B)).card =
    (Nat.factorial A.card) * (Nat.factorial (B.card - A.card)) * (Nat.factorial (n - B.card)) := by
      have h_stabilizer : (Finset.univ.filter (fun σ :
          Perm (Fin n) =>
            permute_set σ A = A
              ∧ permute_set σ B = B)).card
                = (Nat.factorial A.card) * (Nat.factorial (B \ A).card) * (Nat.factorial (n -
                  (A.card + (B \ A).card))) := by
        have h_stabilizer : (Finset.univ.filter (fun σ :
            Perm (Fin n) =>
              permute_set σ A = A
                ∧ permute_set σ (B \ A) = B \ A)).card
                  = (Nat.factorial A.card) * (Nat.factorial (B \ A).card) * (Nat.factorial (n -
                    (A.card + (B \ A).card))) := by
          convert card_stabilizer_disjoint_pair _ using 1;
          exact Finset.disjoint_sdiff;
        convert h_stabilizer using 2;
        ext σ; simp +decide [ stabilizer_subset_pair_iff, hA ] ;
      simp_all +decide [ Finset.card_sdiff ];
      rw [ Finset.inter_eq_left.mpr hA, add_tsub_cancel_of_le ( Finset.card_le_card hA ) ]

/-
The number of permutations mapping pair $(A, B)$ to $(A', B')$ is $|A|! (|B|-|A|)! (n-|B|)!$.
-/
lemma card_permutations_mapping_pair (n : ℕ) (A B A' B' : Finset (Fin n))
    (hA : A ⊆ B) (hA' : A' ⊆ B') (h_card_A : A.card = A'.card) (h_card_B : B.card = B'.card) :
    (univ.filter (fun σ : Perm (Fin n) => permute_set σ A = A' ∧ permute_set σ B = B')).card =
    (Nat.factorial A.card) * (Nat.factorial (B.card - A.card)) * (Nat.factorial (n - B.card)) := by
      convert card_filter_perm_map_pair_eq_card_stabilizer_pair hA hA' h_card_A h_card_B using 1;
      convert card_stabilizer_pair hA |> Eq.symm using 1

/-
The number of permutations mapping $(A, B)$ to the same chain is bounded by the number of chains
covering sizes $|A|$ and $|B|$ times the number of permutations mapping $(A, B)$ to a fixed pair
$(A', B')$.
-/
lemma count_permutations_in_same_chain_bound (n : ℕ) (X : Finset (Finset (Finset (Fin n))))
    (hX : IsSymmetricChainDecomposition n X)
    (A B : Finset (Fin n)) (hAB : A ⊆ B) :
    (univ.filter (fun σ : Perm (Fin n) => pair_in_same_chain n X A B σ)).card ≤
    (num_chains_covering n X A.card B.card) * ((Nat.factorial A.card) * (Nat.factorial (B.card -
      A.card)) * (Nat.factorial (n - B.card))) := by
      let K := (Nat.factorial A.card) * (Nat.factorial (B.card - A.card)) *
        (Nat.factorial (n - B.card))
      let chainFilter := X.filter
        (fun C => (∃ A' ∈ C, A'.card = A.card) ∧ (∃ B' ∈ C, B'.card = B.card))
      have h_chain_unique :
          ∀ C ∈ X, ∀ U V : Finset (Fin n), U ∈ C → V ∈ C → U.card = V.card → U = V := by
        intro C hC U V hU hV hcard
        have hchain : IsChain' C := (hX.1 C hC).1
        rcases hchain.total hU hV with hsub | hsub
        · exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
        · exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard])).symm
      have h_partition :
          ∀ C ∈ chainFilter,
            (Finset.univ.filter (fun σ : Perm (Fin n) =>
              pair_in_same_chain n X A B σ ∧
                ∃ A' ∈ C, permute_set σ A = A' ∧
                  ∃ B' ∈ C, permute_set σ B = B')).card ≤ K := by
        intro C hC
        have hCX : C ∈ X := (Finset.mem_filter.mp hC).1
        rcases (Finset.mem_filter.mp hC).2 with ⟨⟨A0, hA0C, hA0card⟩, ⟨B0, hB0C, hB0card⟩⟩
        have hA0subB0 : A0 ⊆ B0 := by
          have hchain : IsChain' C := (hX.1 C hCX).1
          rcases hchain.total hA0C hB0C with hsub | hsub
          · exact hsub
          · have hleBA : B0.card ≤ A0.card := Finset.card_le_card hsub
            have hleAB : A0.card ≤ B0.card := by
              rw [hA0card, hB0card]
              exact Finset.card_le_card hAB
            have heq : B0 = A0 := Finset.eq_of_subset_of_card_le hsub hleAB
            rw [← heq]
        have h_count :
            (Finset.univ.filter (fun σ : Perm (Fin n) =>
              permute_set σ A = A0 ∧ permute_set σ B = B0)).card = K := by
          dsimp [K]
          exact card_permutations_mapping_pair n A B A0 B0 hAB hA0subB0 hA0card.symm hB0card.symm
        refine (Finset.card_le_card ?_).trans_eq h_count
        intro σ hσ
        rcases (Finset.mem_filter.mp hσ).2 with ⟨hpair, A1, hA1C, hA1eq, B1, hB1C, hB1eq⟩
        have hσA_mem : permute_set σ A ∈ C := by rw [hA1eq]; exact hA1C
        have hσB_mem : permute_set σ B ∈ C := by rw [hB1eq]; exact hB1C
        have hσA_eq : permute_set σ A = A0 := by
          apply h_chain_unique C hCX
          · exact hσA_mem
          · exact hA0C
          · rw [card_permute_set, hA0card]
        have hσB_eq : permute_set σ B = B0 := by
          apply h_chain_unique C hCX
          · exact hσB_mem
          · exact hB0C
          · rw [card_permute_set, hB0card]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hσA_eq, hσB_eq⟩
      have h_total :
          (Finset.univ.filter (fun σ : Perm (Fin n) => pair_in_same_chain n X A B σ)).card ≤
            ∑ C ∈ chainFilter,
              (Finset.univ.filter (fun σ : Perm (Fin n) =>
                pair_in_same_chain n X A B σ ∧
                  ∃ A' ∈ C, permute_set σ A = A' ∧
                    ∃ B' ∈ C, permute_set σ B = B')).card := by
        have hsub :
            (Finset.univ.filter (fun σ : Perm (Fin n) => pair_in_same_chain n X A B σ)) ⊆
              Finset.biUnion chainFilter (fun C =>
                Finset.univ.filter (fun σ : Perm (Fin n) =>
                  pair_in_same_chain n X A B σ ∧
                    ∃ A' ∈ C, permute_set σ A = A' ∧
                      ∃ B' ∈ C, permute_set σ B = B')) := by
          intro σ hσ
          rcases (Finset.mem_filter.mp hσ).2 with ⟨C, hCX, hAC, hBC⟩
          have hCfilter : C ∈ chainFilter := by
            refine Finset.mem_filter.mpr ⟨hCX, ?_⟩
            exact ⟨⟨permute_set σ A, hAC, by rw [card_permute_set]⟩,
              ⟨permute_set σ B, hBC, by rw [card_permute_set]⟩⟩
          refine Finset.mem_biUnion.mpr ⟨C, hCfilter, ?_⟩
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ σ, (Finset.mem_filter.mp hσ).2,
              permute_set σ A, hAC, rfl, permute_set σ B, hBC, rfl⟩
        exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      dsimp [num_chains_covering, chainFilter, K] at h_total h_partition ⊢
      exact h_total.trans (Finset.sum_le_card_nsmul _ _ _ fun C hC => h_partition C hC)

/-
For $a < b \le n$, unless $a=0$ and $b=n$, the maximum of $\binom{b}{a}$ and $\binom{n-a}{b-a}$ is
at least $\lfloor n/2 \rfloor + 1$.
-/
lemma self_le_choose_of_pos_lt {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    n ≤ n.choose k := by
  revert k
  induction n with
  | zero =>
      intro k hk0 hkn
      omega
  | succ n ih =>
      intro k hk0 hkn
      rcases k with _ | k
      · omega
      by_cases hk_last : k + 1 = n
      · rw [hk_last, Nat.choose_succ_self_right]
      · rw [Nat.choose_succ_succ]
        have h1 : 0 < n.choose k := Nat.choose_pos (by omega : k ≤ n)
        have h2 : n ≤ n.choose (k + 1) := ih (hk0 := Nat.succ_pos _) (hkn := by omega)
        exact (Nat.succ_le_succ h2).trans (by
          have h1' : 1 ≤ n.choose k := Nat.succ_le_of_lt h1
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            Nat.add_le_add_left h1' (n.choose (k + 1)))

lemma max_binom_ge_m_plus_one (n : ℕ) (a b : ℕ) (hab : a < b) (hb : b ≤ n)
    (h_not_bad : ¬ (a = 0 ∧ b = n)) :
    max (b.choose a) ((n - a).choose (b - a)) ≥ n / 2 + 1 := by
      by_cases ha : a = 0;
      · rcases b with ( _ | _ | b ) <;> simp_all +arith +decide
        · omega;
        · refine' Or.inr _;
          induction' hb with n hn ih <;> simp +arith +decide [ Nat.choose ] at *;
          rcases eq_or_ne ( b + 2 ) n<;>
            simp_all +arith +decide [ Nat.div_le_iff_le_mul_add_pred ];
          · subst_vars; simp +arith +decide
          · linarith [ Nat.div_mul_le_self n 2, Nat.div_mul_le_self ( n + 1 ) 2,
            Nat.div_add_mod n 2,
            Nat.mod_lt n two_pos, Nat.div_add_mod ( n + 1 ) 2, Nat.mod_lt ( n + 1 ) two_pos,
              Nat.choose_pos ( by linarith : b + 1
            ≤ n ) ];
      · by_cases hb : b ≤ n / 2;
        · refine' le_max_of_le_right _;
          refine' le_trans _ ( Nat.choose_le_choose _ ( show n - a ≥ b - a + ( n / 2 ) from _ ) );
          · refine' Nat.le_induction _ _ _ ( show b - a ≥ 1 from Nat.sub_pos_of_lt hab )<;>
            intros<;>
            simp_all +decide
            · grind;
          · omega;
        · -- Since $b > n/2$, we have $\binom{b}{a} \geq b$.
          have h_binom_b_a : b.choose a ≥ b := by
            exact self_le_choose_of_pos_lt (by omega) hab
          exact le_max_of_le_left ( by omega )

/-
The number of permutations mapping a non-bad pair $(A, B)$ to the same chain is at most $n! /
(m+1)$.
-/
lemma count_pair_in_same_chain_le_mul (n : ℕ) (X : Finset (Finset (Finset (Fin n))))
    (hX : IsSymmetricChainDecomposition n X)
    (A B : Finset (Fin n)) (hAB : A ⊂ B) (h_not_bad : ¬ is_bad_pair A B) :
    (univ.filter (fun σ : Perm (Fin n) =>
      pair_in_same_chain n X A B σ)).card * (n / 2 + 1) ≤ Nat.factorial n := by
      -- By `count_permutations_in_same_chain_bound`, the count is at most `N_{chains} * a! * (b -
      -- a)! * (n - b)!`, where `N_{chains} = num_chains_covering n X a b`.
      have h_count_bound : (Finset.univ.filter (fun σ :
          Equiv.Perm (Fin n) =>
            pair_in_same_chain n X A B σ)).card * (n / 2 + 1)
              ≤ (num_chains_covering n X A.card B.card) * (Nat.factorial A.card) * (Nat.factorial
                (B.card - A.card)) * (Nat.factorial (n - B.card)) * (n / 2 + 1) := by
        refine' Nat.mul_le_mul_right _ _;
        convert count_permutations_in_same_chain_bound n X hX A B hAB.subset using 1 ; ring;
      -- We want to show $N_{chains} \cdot (m+1) \le \frac{n!}{a! (b-a)! (n-b)!}$.
      have h_ineq :
          (num_chains_covering n X A.card B.card) * (n / 2 + 1)
            ≤ Nat.choose n B.card * Nat.choose B.card A.card ∨
          (num_chains_covering n X A.card B.card) * (n / 2 + 1)
            ≤ Nat.choose n A.card * Nat.choose (n - A.card) (B.card - A.card) := by
        have h_ineq :
            max (Nat.choose B.card A.card) (Nat.choose (n - A.card) (B.card - A.card))
              ≥ n / 2 + 1 := by
          apply max_binom_ge_m_plus_one n A.card B.card (Finset.card_lt_card hAB)
          · exact le_trans ( Finset.card_le_univ _ ) ( by norm_num )
          · rintro ⟨ hA, hB ⟩
            simp_all +decide
            exact h_not_bad ( by
              rw [ Finset.eq_of_subset_of_card_le ( Finset.subset_univ B ) ( by aesop ) ]
              exact ⟨ rfl, rfl ⟩ )
        have h_ineq :
            (num_chains_covering n X A.card B.card) ≤ Nat.choose n B.card
              ∧ (num_chains_covering n X A.card B.card) ≤ Nat.choose n A.card := by
          exact And.symm (num_chains_covering_le_choose n X hX (#A) #B);
        cases max_cases ( Nat.choose B.card A.card ) ( Nat.choose ( n - A.card ) ( B.card - A.card
          ) )<;>
          [ left;
          right ]<;>
            nlinarith [ Nat.choose_pos ( show A.card ≤ B.card from Finset.card_le_card hAB.1 ) ] ;
      cases' h_ineq with h h<;>
        simp_all +decide [ Nat.choose_eq_factorial_div_factorial ( show A.card ≤ B.card from
          Finset.card_le_card hAB.1 ) ];
      · refine le_trans ( Nat.mul_le_mul_right _ h_count_bound ) ?_;
        convert Nat.mul_le_mul_right ( ( #A ) ! * ( #B - #A ) ! * ( n - #B ) ! ) h using 1 ; ring;
        rw [ ← Nat.choose_mul_factorial_mul_factorial ( show #B ≤ n from
          le_trans ( Finset.card_le_univ _ ) ( by
          norm_num ) ) ];
          ring_nf;
        rw [ ← Nat.mul_div_assoc ];
        · exact Eq.symm ( Nat.div_eq_of_eq_mul_left ( Nat.mul_pos ( Nat.factorial_pos _ ) (
          Nat.factorial_pos _ ) ) ( by ring ) );
        · exact Nat.factorial_mul_factorial_dvd_factorial ( Finset.card_le_card hAB.1 );
      · refine le_trans ( Nat.mul_le_mul_right _ h_count_bound ) ?_;
        convert Nat.mul_le_mul_right ( ( A.card ! * ( B.card - A.card ) ! * ( n - B.card ) ! ) ) h
          using 1 ;
          ring;
        rw [ ← Nat.choose_mul_factorial_mul_factorial ( show #A ≤ n from
          le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ),
            ← Nat.choose_mul_factorial_mul_factorial ( show #B - #A
            ≤ n - #A from
            Nat.sub_le_sub_right ( Finset.card_le_univ _ |> le_trans <| by
          norm_num ) _ ) ];
          ring_nf;
        rw [ Nat.sub_sub, add_comm ];
        rw [ Nat.sub_add_cancel ( show #A ≤ #B from Finset.card_le_card hAB.1 ) ]

/-
The sum of bad pairs over all permutations equals the sum of counts of permutations mapping each
comparable pair to the same chain.
-/
lemma sum_bad_pairs_eq_sum_count (n : ℕ) (X : Finset (Finset (Finset (Fin n))))
    (A : Finset (Finset (Fin n))) :
    ∑ σ : Perm (Fin n), (bad_pairs n X (permute_family σ A)).card =
    ∑ p ∈ comparable_pairs A, count_pair_in_same_chain n X p.1 p.2 := by
      unfold count_pair_in_same_chain bad_pairs comparable_pairs;
        simp +decide [ Finset.sum_filter, Finset.sum_product ] ;
      simp +decide only [card_filter, sum_filter, sum_product];
      -- By commutativity of addition, we can interchange the order of summation.
      have h_comm : ∑ σ : Perm (Fin n), ∑ A₁ ∈ A, ∑ A₂ ∈ A, (if A₁ ⊂ A₂ then if ∃ C ∈ X,
        permute_set σ A₁ ∈ C
        ∧ permute_set σ A₂ ∈ C then 1 else 0 else 0) = ∑ A₁ ∈ A, ∑ A₂ ∈ A, ∑ σ :
          Perm (Fin n), (if A₁ ⊂ A₂ then if ∃ C ∈ X, permute_set σ A₁ ∈ C
            ∧ permute_set σ A₂ ∈ C then 1 else 0 else 0) := by
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
      convert h_comm using 1;
      · unfold permute_family; simp +decide [ Finset.sum_map ] ;
        congr! 3;
        unfold permute_set; aesop;
      · simp +decide [ pair_in_same_chain ];
        simp +decide only [card_filter];
        convert rfl

/-
If $\emptyset$ and $[n]$ are in $\mathcal{A}$, then $|P| \ge 2|\mathcal{A}| - 3$.
-/
lemma comparable_pairs_card_ge_of_mem_empty_univ {n : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (h_empty : ∅ ∈ 𝒜) (h_univ : Finset.univ ∈ 𝒜) (h_ne : ∅ ≠ (Finset.univ : Finset (Fin n))) :
    (comparable_pairs 𝒜).card ≥ 2 * 𝒜.card - 3 := by
      -- If $\emptyset$ and $[n]$ are in $\mathcal{A}$, then $(\emptyset, [n]) \in P$.
      have h_pair : (∅, univ) ∈ comparable_pairs 𝒜 := by
        exact Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ h_empty, h_univ ⟩,
          Finset.ssubset_univ_iff.mpr ( by aesop ) ⟩;
      -- For every $A \in \mathcal{A} \setminus \{\emptyset, [n]\}$, we have $\emptyset \subset A
      -- \subset [n]$.
      have h_subset :
          ∀ A ∈ 𝒜 \ {∅, univ}, (∅, A) ∈ comparable_pairs 𝒜 ∧ (A, univ) ∈ comparable_pairs 𝒜 := by
        simp_all +decide [ comparable_pairs ];
        exact fun A hA hA' hA'' =>
          ⟨ Finset.nonempty_of_ne_empty hA', lt_of_le_of_ne ( Finset.subset_univ _ ) hA'' ⟩;
      -- Since these pairs are distinct, we can count them as follows: $(\emptyset, [n])$ is unique,
      -- $(\emptyset, A)$ has second element $A \ne [n]$, and $(A, [n])$ has first element $A \ne
      -- \emptyset$.
      have h_distinct :
          (Finset.image (fun A => (∅, A)) (𝒜 \ {∅, univ}) ∪ Finset.image (fun A =>
            (A, univ)) (𝒜 \ {∅, univ}) ∪ {(∅, univ)}) ⊆ comparable_pairs 𝒜 := by
        grind;
      refine le_trans ?_ ( Finset.card_mono h_distinct );
      rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ]<;>
        norm_num [ Finset.card_image_of_injective, Function.Injective, h_ne ];
      · grind;
      · norm_num [ Finset.disjoint_left ];
        grind +ring

/-
Theorem [Supersaturation for comparable pairs]
Let $m=\lfloor n/2\rfloor$ and $N=\bin{n}{m}$.
If $\cA\subseteq \PP(n)$ has $|\cA|\ge N+x$, then $\cA$ contains at least $(m+1)x$ ordered pairs
$(A,B)$ with $A,B\in\cA$ and $A\subset B$.
-/
theorem supersaturation (n : ℕ) (𝒜 : Finset (Finset (Fin n)))
    (x : ℕ) (h_card : 𝒜.card ≥ n.choose (n / 2) + x) :
    (comparable_pairs 𝒜).card ≥ (n / 2 + 1) * x := by
      by_cases hx : x = 0;
      · aesop;
      · induction' x using Nat.strong_induction_on with x ih generalizing n 𝒜;
        by_cases h_empty_univ : (∅, Finset.univ) ∈ comparable_pairs 𝒜;
        · by_cases hx : x = 1 ∨ x = 2;
          · have h_card_ge_two : (comparable_pairs 𝒜).card ≥ 2 * 𝒜.card - 3 := by
              apply comparable_pairs_card_ge_of_mem_empty_univ;
              · exact Finset.mem_product.mp ( Finset.mem_filter.mp h_empty_univ |>.1 ) |>.1;
              · exact Finset.mem_product.mp ( Finset.mem_filter.mp h_empty_univ |>.1 ) |>.2;
              · cases n <;> simp_all +decide [ Finset.ext_iff ];
                cases hx <;> simp_all +decide [ comparable_pairs ];
            rcases hx with ( rfl | rfl ) <;> norm_num at *;
            · rcases n with ( _ | _ | n ) <;> simp +arith +decide [ Nat.choose ] at *;
              · exact ⟨ _, h_empty_univ ⟩;
              · exact ⟨ _, h_empty_univ ⟩;
              · have h_binom_ge : n.choose (n / 2 + 1) + n.choose (n / 2) ≥ n + 1 := by
                  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩<;>
                    simp +arith +decide [ Nat.choose ] at *;
                  · have h_binom_ge : ∀ k : ℕ, k ≥ 1
                    → 2 * k + 1 ≤ (2 * k).choose k + (2 * k).choose (k + 1) := by
                      intro k hk; induction hk <;> simp +arith +decide [ Nat.choose ] at *;
                      linarith [ Nat.choose_pos ( by linarith : ‹_› ≤ 2 * ‹_› + 1 ) ];
                    exact if hk : 1 ≤ k then h_binom_ge k hk else by interval_cases k ; trivial;
                  · norm_num [ Nat.add_div ] at *;
                    exact Nat.recOn k ( by norm_num ) fun n ihn => by
                      simp +arith +decide [ Nat.choose ] at ihn ⊢;
                      linarith
                linarith [ Nat.div_mul_le_self n 2, Nat.choose_pos ( show n / 2 ≤ n + 1 from
                  by linarith [ Nat.div_mul_le_self n 2 ] ) ];
            · have h_binom_ge_m_plus_one : n.choose (n / 2) ≥ n / 2 + 1 := by
                rcases n with ( _ | _ | n ) <;> simp +arith +decide [ Nat.choose ] at *;
                rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩<;>
                  simp +arith +decide [ Nat.choose ] at *;
                · exact Nat.recOn k ( by norm_num ) fun n ihn => by
                    simp +arith +decide [ Nat.choose ] at ihn ⊢;
                    linarith
                · norm_num [ Nat.add_div ];
                  exact Nat.recOn k ( by norm_num ) fun n ihn => by
                    simp +arith +decide [ Nat.choose ] at ihn ⊢;
                    linarith
              linarith;
          · -- If $x \geq 3$, let $\mathcal{A}' = \mathcal{A} \setminus \{\emptyset, [n]\}$.
            set 𝒜' := 𝒜 \ {∅, Finset.univ} with h𝒜'_def;
            -- By the induction hypothesis, $|P(\mathcal{A}')| \geq (m+1)(x-2)$.
            have h_ind : (comparable_pairs 𝒜').card ≥ (n / 2 + 1) * (x - 2) := by
              apply ih (x - 2);
              · omega;
              · grind;
              · omega;
            -- The pairs in $\mathcal{A}$ include $P(\mathcal{A}')$, $(\emptyset, [n])$, and for
            -- each $A \in \mathcal{A}'$, $(\emptyset, A)$ and $(A, [n])$.
            have h_pairs :
                comparable_pairs 𝒜 ⊇ comparable_pairs 𝒜' ∪ {(∅,
                  Finset.univ)} ∪ Finset.image (fun A =>
                  (∅, A)) (𝒜' \ {∅}) ∪ Finset.image (fun A =>
                    (A, Finset.univ)) (𝒜' \ {Finset.univ}) := by
              intro p hp; simp_all +decide
              rcases hp with ( rfl | hp | ⟨ a, ⟨ ⟨ ha₁, ha₂, ha₃ ⟩, ha₄ ⟩, rfl ⟩ | ⟨ a, ⟨ ⟨ ha₁,
                ha₂,
                ha₃ ⟩, ha₄ ⟩, rfl ⟩ )<;>
                simp_all +decide [ comparable_pairs ];
              · exact Finset.nonempty_of_ne_empty ha₂;
              · exact lt_of_le_of_ne ( Finset.subset_univ _ ) ha₃;
            -- Therefore, $|P(\mathcal{A})| \geq |P(\mathcal{A}')| + 1 + 2|\mathcal{A}'|$.
            have h_card_pairs :
                (comparable_pairs 𝒜).card ≥ (comparable_pairs 𝒜').card + 1 + 2 * (𝒜'.card) := by
              refine le_trans ?_ ( Finset.card_mono h_pairs );
              rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
                Finset.card_union_of_disjoint ]<;>
                norm_num [ Finset.disjoint_right ];
              · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ]<;>
                norm_num [ Function.Injective ];
                grind;
              · simp +decide [ comparable_pairs ];
                aesop;
              · unfold comparable_pairs; aesop;
              · unfold comparable_pairs; aesop;
            -- Since $|\mathcal{A}'| \geq N + x - 2$, we have $2|\mathcal{A}'| \geq 2(N + x - 2)$.
            have h_card_A' : 2 * (𝒜'.card) ≥ 2 * (n.choose (n / 2) + x - 2) := by
              grind;
            rcases x with ( _ | _ | x ) <;> simp_all +decide;
            -- Since $n.choose (n / 2) \geq n / 2 + 1$, we can substitute this into the inequality.
            have h_binom_ge : n.choose (n / 2) ≥ n / 2 + 1 := by
              rcases n with ( _ | _ | n ) <;> simp +arith +decide [ Nat.choose ] at *;
              rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩<;>
                simp +arith +decide [ Nat.choose ] at *;
              · exact Nat.recOn k ( by norm_num ) fun n ihn => by
                  simp +arith +decide [ Nat.choose ] at ihn ⊢;
                  linarith
              · norm_num [ Nat.add_div ];
                exact Nat.recOn k ( by norm_num ) fun n ihn => by
                  simp +arith +decide [ Nat.choose ] at ihn ⊢;
                  linarith
            linarith
        · -- Since there are no bad pairs, for all $p \in P$, $\text{count}(p) \le \frac{n!}{m+1}$.
          have h_count_le :
              ∀ p ∈ comparable_pairs 𝒜,
                count_pair_in_same_chain n (Classical.choose (exists_SCD n)) p.1 p.2
                ≤ Nat.factorial n / (n / 2 + 1) := by
            intros p hp
            have h_count_le :
                count_pair_in_same_chain n (Classical.choose (exists_SCD n)) p.1 p.2 * (n / 2 + 1)
                  ≤ Nat.factorial n := by
              apply count_pair_in_same_chain_le_mul;
              · exact Classical.choose_spec ( exists_SCD n );
              · exact Finset.mem_filter.mp hp |>.2;
              · unfold is_bad_pair; aesop;
            rwa [ Nat.le_div_iff_mul_le ( Nat.succ_pos _ ) ];
          -- By `bad_pairs_lower_bound`, $\sum_{\sigma} \#\text{bad}(\sigma(\cA)) \ge n! x$.
          have h_sum_bad_pairs : ∑ σ :
              Perm (Fin n),
                (bad_pairs n (Classical.choose (exists_SCD n)) (permute_family σ 𝒜)).card
                ≥ Nat.factorial n * x := by
            have := Classical.choose_spec ( exists_SCD n );
            have :=
              bad_pairs_lower_bound_perm n ( Classical.choose ( exists_SCD n ) ) this ( card_SCD n
                ( Classical.choose ( exists_SCD n ) ) this ) 𝒜 x h_card;
            exact le_trans ( by simp +decide [ Finset.card_univ, Fintype.card_perm ] ) (
              Finset.sum_le_sum fun σ _ =>
              this σ );
          -- By `sum_bad_pairs_eq_sum_count`, this sum equals $\sum_{p \in P} \text{count}(p)$.
          have h_sum_count : ∑ σ :
              Perm (Fin n),
                (bad_pairs n (Classical.choose (exists_SCD n)) (permute_family σ 𝒜)).card
                = ∑ p ∈ comparable_pairs 𝒜,
                  count_pair_in_same_chain n (Classical.choose (exists_SCD n)) p.1 p.2 := by
            apply sum_bad_pairs_eq_sum_count;
          have := Finset.sum_le_sum h_count_le; simp_all +decide [ mul_comm ] ;
          nlinarith [ Nat.factorial_pos n, Nat.div_mul_le_self ( n ! ) ( n / 2 + 1 ),
            Nat.div_add_mod ( n ! ) ( n / 2 + 1 ), Nat.mod_lt ( n ! ) ( Nat.succ_pos ( n / 2 ) ) ]

/-
The number of edges in the induced subgraph of G_n on U is equal to the number of comparable pairs
in U.
-/
lemma card_edges_induce_G_eq_card_comparable_pairs (n : ℕ) (U : Finset (Finset (Fin n))) :
    ((G n).induce (U : Set (Finset (Fin n)))).edgeFinset.card = (comparable_pairs U).card := by
      unfold G comparable_pairs
      refine' Eq.symm ( Finset.card_bij (fun p hp =>
        s(⟨p.1, (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1⟩,
          ⟨p.2, (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2⟩)) _ _ _ );
      · simp +contextual [ SimpleGraph.fromRel_adj ];
        exact fun a b hp hq hq' =>
          ⟨ ne_of_lt hq', Or.inl <| by simpa [ Finset.subset_iff ] using hq'.1 ⟩;
      · simp +contextual
        rintro a b ha hb hab c d hc hd hcd ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ )<;>
          simp_all +decide [ Finset.ssubset_def ];
      · simp +decide [ SimpleGraph.fromRel ];
        rintro ⟨ a, b ⟩ h;
          cases' h with h₁ h₂;
          simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ] ;
        cases' h₂ with h₂ h₂
        · exact
            ⟨ a, b, ⟨ ⟨ a.2, b.2 ⟩, h₂, by
              contrapose! h₁
              aesop ⟩, Or.inl ⟨ rfl, rfl ⟩ ⟩
        · exact
            ⟨ b, a, ⟨ ⟨ b.2, a.2 ⟩, h₂, by
              contrapose! h₁
              aesop ⟩, Or.inr ⟨ rfl, rfl ⟩ ⟩

/-
Lemma [Low maximum degree forces near-extremal size]
Let m = floor(n/2) and N = bin(n, m).
Fix epsilon in (0,1] and set Delta = epsilon * n / 10.
If U subset PP(n) satisfies Delta(G_n[U]) < Delta, then for all n >= 2 we have |U| <= (1+epsilon)N.
-/
lemma low_degree_forces_near_extremal_size (n : ℕ) (ε : ℝ) (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1)
    (U : Finset (Finset (Fin n)))
    (h_delta : ((G n).induce (U : Set (Finset (Fin n)))).maxDegree < ε * n / 10)
    (hn : n ≥ 2) :
    (U.card : ℝ) ≤ (1 + ε) * (n.choose (n / 2)) := by
      have h_supersaturation :
          (comparable_pairs U).card ≥ (n / 2 + 1) * (U.card - n.choose (n / 2)) := by
        by_cases h_card : U.card ≥ n.choose (n / 2);
        · have := supersaturation n U ( U.card - n.choose ( n / 2 ) ) ?_ <;> aesop;
        · grind;
      -- By the properties of the induced subgraph and the maximum degree, we have |U| * Δ(G[U]) ≥ 2
      -- * (comparable_pairs U).card.
      have h_card_edges : (U.card : ℝ) * (ε * n / 10) ≥ 2 * (comparable_pairs U).card := by
        have h_card_edges : (U.card : ℝ) * (SimpleGraph.maxDegree (SimpleGraph.induce (U :
            Set (Finset (Fin n))) (G n))) ≥ 2 * (comparable_pairs U).card := by
          have h_card_edges : (U.card : ℝ) * (SimpleGraph.maxDegree (SimpleGraph.induce (U : Set
            (Finset (Fin n))) (G n)))
            ≥ 2 * ((SimpleGraph.induce (U : Set (Finset (Fin n))) (G n)).edgeFinset.card :
              ℝ) := by
            have :=
              SimpleGraph.sum_degrees_eq_twice_card_edges ( SimpleGraph.induce ( U : Set ( Finset (
                Fin n ) ) ) ( G n ) );
            have h_card_edges : ∀ v : U,
              (SimpleGraph.degree (SimpleGraph.induce (U : Set (Finset (Fin n))) (G n)) v)
              ≤ (SimpleGraph.maxDegree (SimpleGraph.induce (U :
                Set (Finset (Fin n))) (G n))) := by
              exact fun v => SimpleGraph.degree_le_maxDegree (SimpleGraph.induce (↑U) (G n)) v;
            exact_mod_cast this ▸ le_trans ( Finset.sum_le_sum fun _ _ =>
              h_card_edges _ ) ( by simp +decide );
          convert h_card_edges using 1;
          rw [ card_edges_induce_G_eq_card_comparable_pairs ];
        exact h_card_edges.trans ( mul_le_mul_of_nonneg_left h_delta.le <| Nat.cast_nonneg _ );
      contrapose! h_card_edges;
      refine' lt_of_lt_of_le _ ( mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr h_supersaturation )
        zero_le_two );
      rw [ Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub ];
      · rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
        · nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( Nat.choose ( 2 * k ) k : ℝ )
          ≥ 1 by exact_mod_cast Nat.choose_pos ( by linarith ),
            mul_le_mul_of_nonneg_left hε_le_one ( show ( 0 : ℝ )
          ≤ k by positivity ), mul_le_mul_of_nonneg_left hε_le_one ( show ( 0 : ℝ )
            ≤ #U by positivity ) ];
        · norm_num [ Nat.add_div ] at *;
          nlinarith [ mul_le_mul_of_nonneg_left hε_le_one ( show ( 0 : ℝ )
            ≤ #U by positivity ), mul_le_mul_of_nonneg_left hε_le_one ( show ( 0 : ℝ )
              ≤ ( 2 * k + 1 ).choose k by positivity ), show ( Nat.choose ( 2 * k + 1 ) k : ℝ )
                ≥ 1 by exact_mod_cast Nat.choose_pos ( by linarith ) ];
      · exact_mod_cast ( by nlinarith : ( n.choose ( n / 2 ) : ℝ ) ≤ #U )

/-
The number of antichains A(n) is at least 2^(bin(n, n/2)).
-/
lemma lower_bound_A (n : ℕ) : (2 : ℝ) ^ (n.choose (n / 2)) ≤ A n := by
  -- The set of all subsets of $\{A \subseteq [n] : |A| = \lfloor n/2 \rfloor\}$ is an antichain.
  have h_antichain : ∀ (S :
      Finset (Finset (Fin n))), (∀ A ∈ S, A.card = n / 2) → (G n).IsIndepSet S := by
    intros S hS; intro A hA B hB hAB; simp_all +decide [ G ] ;
    exact ⟨ fun h =>
      hAB <| Finset.eq_of_subset_of_card_le h <| by linarith [ hS A hA, hS B hB ], fun h =>
        hAB <| Eq.symm <| Finset.eq_of_subset_of_card_le h <| by linarith [ hS A hA, hS B hB ] ⟩;
  -- The number of subsets of $\{A \subseteq [n] : |A| = \lfloor n/2 \rfloor\}$ is
  -- $2^{\binom{n}{\lfloor n/2 \rfloor}}$.
  have h_num_subsets : (Finset.powerset (Finset.filter (fun A : Finset (Fin n) =>
    A.card = n / 2) (Finset.univ :
      Finset (Finset (Fin n))))).card = 2 ^ (Nat.choose n (n / 2)) := by
    rw [ Finset.card_powerset,
      show ( Finset.univ.filter fun A : Finset ( Fin n ) => Finset.card A = n / 2 )
          = Finset.powersetCard ( n / 2 ) ( Finset.univ : Finset ( Fin n ) ) by
        ext
        simp +decide [ Finset.mem_powersetCard ] ]
    simp +decide [ Finset.card_univ ]
  refine' mod_cast h_num_subsets ▸ _;
  have h_num_subsets : (Finset.powerset (Finset.filter (fun A : Finset (Fin n) =>
    A.card
      = n / 2) (Finset.univ : Finset (Finset (Fin n))))).card
        ≤ (Finset.filter (fun S : Finset (Finset (Fin n)) =>
      (G n).IsIndepSet (S : Set (Finset (Fin n)))) (Finset.powerset (Finset.univ :
      Finset (Finset (Fin n))))).card := by
    refine Finset.card_le_card ?_;
    grind;
  convert h_num_subsets using 1;
  refine' Finset.card_bij ( fun S _ => S ) _ _ _ <;> simp +decide
  · exact fun a ha => (fun n ℱ => (antichain_iff_independent_set n ℱ).mp) n a ha;
  · exact fun b a => (fun n ℱ => (antichain_iff_independent_set n ℱ).mpr) n b a

/-
If every independent set is contained in S union f(S) for some small S, then the number of
independent sets is bounded by the number of such S times 2^M.
-/
lemma count_independent_sets_via_container (n : ℕ) (k : ℕ) (M : ℝ)
    (f : Finset (Finset (Fin n)) → Finset (Finset (Fin n)))
    (h_container : ∀ I : Finset (Finset (Fin n)), (G n).IsIndepSet (I : Set (Finset (Fin n))) →
        ∃ S : Finset (Finset (Fin n)), S ⊆ I ∧ S.card ≤ k ∧ I ⊆ S ∪ f S)
    (h_size : ∀ S : Finset (Finset (Fin n)), S.card ≤ k → (f S).card ≤ M) :
    (A n : ℝ) ≤ (∑ s ∈ range (k + 1), ((PP n).card.choose s : ℝ)) * (2 : ℝ) ^ M := by
      -- By definition of $A(n)$, we know that
      have h_A_def : (A n : ℝ) ≤ (Finset.card (Finset.filter (fun I => (G n).IsIndepSet (I :
          Set (Finset (Fin n)))) (Finset.powerset (PP n)))) := by
        -- The cardinality of a Finset is equal to the cardinality of the corresponding set.
        simp [A];
        rw [ Finset.card_filter ];
        rw [ Finset.sum_image ];
        · simp +decide [ antichains ];
          simp +decide [ IsAntichain, G ];
          simp +decide [ SimpleGraph.isIndepSet_iff, Set.Pairwise ];
          exact Finset.card_mono fun x hx => by aesop;
        · intro x hx y hy; aesop;
      -- Every independent set $I$ is a subset of $S \cup f(S)$ for some $S \in \mathcal{S}$ with $S
      -- \subseteq I$.
      have h_indep_subset : Finset.filter (fun I => (G n).IsIndepSet (I :
          Set (Finset (Fin n)))) (Finset.powerset (PP n)) ⊆ Finset.biUnion (Finset.powersetCard k
            (PP n) ∪ Finset.biUnion (Finset.range k) (fun s =>
            Finset.powersetCard s (PP n))) (fun S => Finset.image (fun T =>
              S ∪ T) (Finset.powerset (f S))) := by
        intro I hI;
        obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ :=
          h_container ( Finset.filter ( fun x => x ∈ I ) ( PP n ) ) ( by
          simp +zetaDelta at *;
          exact fun x hx y hy hxy => hI.2 hx.2 hy.2 hxy );
        simp_all +decide [ Finset.subset_iff ];
        use S, by
          exact if h : S.card = k then Or.inl ⟨ fun x hx =>
            hS₁ hx |>.1, h ⟩ else Or.inr ⟨ lt_of_le_of_ne hS₂ h, fun x hx =>
              hS₁ hx |>.1 ⟩, Finset.filter (fun x => x ∈ I) (f S), by
          aesop;
        grind;
      refine le_trans h_A_def <| le_trans ( Nat.cast_le.mpr
        <| Finset.card_le_card h_indep_subset ) ?_;
      refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) _;
      refine' le_trans ( Nat.cast_le.mpr <| Finset.sum_le_sum fun x hx => Finset.card_image_le ) _;
      refine' le_trans ( Nat.cast_le.mpr <| Finset.sum_le_sum fun x hx => _ ) _;
      use fun S => 2 ^ ( f S |> Finset.card );
      · simp +decide [ Finset.card_image_of_injective, Function.Injective ];
      · refine' le_trans ( Nat.cast_le.mpr <| Finset.sum_le_sum fun x hx =>
        pow_le_pow_right₀ ( by norm_num ) <| show Finset.card ( f x ) ≤ ⌊M⌋₊ from
        Nat.le_floor <| h_size x (by
            rw [Finset.mem_union] at hx
            rcases hx with hx | hx
            · exact le_of_eq (Finset.mem_powersetCard.mp hx).2
            · rw [Finset.mem_biUnion] at hx
              rcases hx with ⟨s, hs, hxs⟩
              rw [(Finset.mem_powersetCard.mp hxs).2]
              exact Nat.le_of_lt (Finset.mem_range.mp hs)) ) _;
          · norm_num [ Finset.sum_union, Finset.sum_biUnion ];
            gcongr;
            · have hbiUnion :
                  (Finset.biUnion (Finset.range k) (fun s => Finset.powersetCard s (PP n))).card ≤
                    ∑ s ∈ Finset.range k, (PP n).card.choose s := by
                refine Finset.card_biUnion_le.trans ?_
                exact Finset.sum_le_sum fun s hs => by
                  rw [Finset.card_powersetCard]
              have hsmall_card :
                  (Finset.powersetCard k (PP n) ∪
                    Finset.biUnion (Finset.range k) (fun s => Finset.powersetCard s (PP n))).card ≤
                    ∑ s ∈ Finset.range (k + 1), (PP n).card.choose s := by
                refine (Finset.card_union_le _ _).trans ?_
                rw [Finset.card_powersetCard, Finset.sum_range_succ, add_comm]
                exact Nat.add_le_add_right hbiUnion ((PP n).card.choose k)
              exact_mod_cast hsmall_card
            · exact_mod_cast Real.rpow_le_rpow_of_exponent_le one_le_two ( Nat.floor_le ( show 0
              ≤ M by exact le_trans ( Nat.cast_nonneg _ ) ( h_size ∅ ( by norm_num ) ) ) )

/-
The number of antichains is bounded by the number of containers times the maximum size of a
container.
-/
lemma count_independent_sets_via_container_bound (n : ℕ) (k : ℕ) (M : ℝ)
    (f : Finset (Finset (Fin n)) → Finset (Finset (Fin n)))
    (h_container : ∀ I : Finset (Finset (Fin n)), (G n).IsIndepSet (I : Set (Finset (Fin n))) →
        ∃ S : Finset (Finset (Fin n)), S ⊆ I ∧ S.card ≤ k ∧ I ⊆ S ∪ f S)
    (h_size : ∀ S : Finset (Finset (Fin n)), S.card ≤ k → (f S).card ≤ M) :
    (A n : ℝ) ≤ (∑ s ∈ range (k + 1), ((PP n).card.choose s : ℝ)) * (2 : ℝ) ^ M := by
      convert count_independent_sets_via_container n k M f _ _ using 1;
      · -- Apply the container lemma with Δ = εn/10.
        apply h_container;
      · assumption

/-
Definition of epsilon(n) = n^(-1/3).
-/
noncomputable def epsilon (n : ℕ) : ℝ := (n : ℝ) ^ (-(1:ℝ)/3)

/-
Definition of Delta(n) = epsilon(n) * n / 10.
-/
noncomputable def Delta (n : ℕ) : ℝ := (epsilon n) * n / 10

/-
epsilon(n) is at most 1 for n >= 1.
-/
lemma epsilon_le_one (n : ℕ) (h : n ≥ 1) : epsilon n ≤ 1 := by
  exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast h ) ( show ( - ( 1 : ℝ ) / 3 )
    ≤ 0 by norm_num ) ) ( by norm_num )

/-
Delta(n) is at least 1 for n >= 1000.
-/
lemma Delta_ge_one (n : ℕ) (h : n ≥ 1000) : Delta n ≥ 1 := by
  -- Substitute $n = 1000$ into the expression for $\Delta(n)$ and simplify.
  have h_delta_1000 : (1000 : ℝ) ^ (2 / 3 : ℝ) / 10 ≥ 1 := by
    rw [ show ( 1000 : ℝ ) = 10 ^ 3 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul ]<;>
      norm_num;
  -- Since $n \geq 1000$, we have $n^{2/3} \geq 1000^{2/3}$.
  have h_n_ge_1000 : (n : ℝ) ^ (2 / 3 : ℝ) ≥ (1000 : ℝ) ^ (2 / 3 : ℝ) := by
    exact Real.rpow_le_rpow ( by norm_num ) ( mod_cast h ) ( by norm_num );
  exact le_trans h_delta_1000 ( by
    rw [ show Delta n = ( n : ℝ ) ^ ( 2 / 3 : ℝ ) / 10 by
      unfold Delta epsilon
      rw [ ← Real.rpow_add_one ] <;> ring_nf
      positivity ]
    gcongr )

/-
Define a linear order on Finset (Fin n) using binary encoding.
-/
noncomputable instance (n : ℕ) : LinearOrder (Finset (Fin n)) :=
  LinearOrder.lift' (fun s => ∑ i ∈ s, 2 ^ (i : ℕ)) (fun s t h => by
    dsimp at h
    -- This is injectivity of binary representation
    -- By the uniqueness of binary representation, if the sums of the elements in s and t are equal,
    -- then the sets s and t must be equal.
    have h_unique_binary : ∀ (s t : Finset ℕ), (∑ i ∈ s, 2 ^ i) = (∑ i ∈ t, 2 ^ i) → s = t := by
      intro s t h;
      have h_unique_binary : ∀ (s t : Finset ℕ), (∑ i ∈ s, 2 ^ i) = (∑ i ∈ t, 2 ^ i) → s = t := by
        intro s t h
        have h_binary_eq :
            Nat.ofDigits 2 (List.map (fun i =>
              if i ∈ s then 1 else 0) (List.range (Nat.max (Finset.sup s id) (Finset.sup t id) +
                1)))
                = Nat.ofDigits 2 (List.map (fun i =>
                if i ∈ t then 1 else 0) (List.range (Nat.max (Finset.sup s id) (Finset.sup t id) +
                  1))) := by
          have h_binary_eq :
              ∑ i ∈ Finset.range (Nat.max (Finset.sup s id) (Finset.sup t id) + 1),
                (if i ∈ s then 2 ^ i else 0)
                = ∑ i ∈ Finset.range (Nat.max (Finset.sup s id) (Finset.sup t id) + 1),
                  (if i ∈ t then 2 ^ i else 0) := by
            simp_all +decide
            rw [ Finset.inter_eq_right.mpr, Finset.inter_eq_right.mpr ];
            · exact h;
            · exact fun x hx =>
              Finset.mem_range.mpr ( Nat.lt_succ_of_le ( le_max_of_le_right ( Finset.le_sup ( f :=
              id ) hx ) ) );
            · exact fun x hx =>
              Finset.mem_range.mpr ( Nat.lt_succ_of_le ( le_max_of_le_left ( Finset.le_sup ( f :=
              id ) hx ) ) );
          convert h_binary_eq using 1;
          · induction ( Nat.max ( Finset.sup s id ) ( Finset.sup t id ) + 1 ) <;> simp_all +decide
            simp_all +decide [ Nat.ofDigits_append, List.range_succ ];
            simp +decide [ Finset.range_add_one, Finset.inter_comm ];
            grind;
          · induction ( Nat.max ( Finset.sup s id ) ( Finset.sup t id ) + 1 ) <;> simp_all +decide
            simp_all +decide [ Nat.ofDigits_append, List.range_succ ];
            simp +decide [ Finset.range_add_one, Finset.inter_comm ];
            by_cases h : ‹_› ∈ t <;> simp +decide [ h, Finset.sum_insert ];
            ring
        have h_binary_eq_digits :
            List.map (fun i =>
              if i ∈ s then 1 else 0) (List.range (Nat.max (Finset.sup s id) (Finset.sup t id) + 1))
                = List.map (fun i =>
                if i ∈ t then 1 else 0) (List.range (Nat.max (Finset.sup s id) (Finset.sup t id) +
                  1)) := by
          have h_binary_eq_digits : ∀ (l1 l2 :
              List ℕ), (∀ i ∈ l1, i = 0 ∨ i = 1) → (∀ i ∈ l2, i = 0 ∨ i = 1)
                → List.length l1 = List.length l2 → Nat.ofDigits 2 l1 = Nat.ofDigits 2 l2
                  → l1 = l2 := by
            intros l1 l2 hl1 hl2 hlen hsum;
              induction' l1 with d1 l1 ih generalizing l2<;>
                induction' l2 with d2 l2 ih'<;>
                simp_all +decide [ Nat.ofDigits ] ;
            grind;
          exact h_binary_eq_digits _ _ ( fun i hi => by
            rw [ List.mem_map ] at hi;
            rcases hi with ⟨ j, hj, rfl ⟩ ;
              by_cases hj' : j ∈ s <;> simp +decide [ hj' ] ) ( fun i hi => by
            rw [ List.mem_map ] at hi;
            rcases hi with ⟨ j, hj, rfl ⟩ ;
              by_cases hj' : j ∈ t <;> simp +decide [ hj' ] ) ( by simp +decide ) h_binary_eq;
        ext i
        replace h_binary_eq_digits := congr_arg ( fun l => l[i]! ) h_binary_eq_digits
        by_cases hi : i < Nat.max ( Finset.sup s id ) ( Finset.sup t id ) + 1
        · simp_all +decide
          split_ifs at h_binary_eq_digits <;> tauto
        · have hi_out : ¬ i < Nat.max ( Finset.sup s id ) ( Finset.sup t id ) + 1 := hi
          constructor
          · intro hi'
            exact False.elim <| hi_out <| Nat.lt_succ_of_le <|
              le_trans ( Finset.le_sup ( f := id ) hi' ) <| Nat.le_max_left _ _
          · intro hi'
            exact False.elim <| hi_out <| Nat.lt_succ_of_le <|
              le_trans ( Finset.le_sup ( f := id ) hi' ) <| Nat.le_max_right _ _
      exact h_unique_binary s t h;
    convert h_unique_binary ( s.image ( fun x : Fin n => x.val ) ) ( t.image ( fun x : Fin n =>
      x.val ) ) _ using 1;
    · rw [ Finset.image_injective ( fun x y hxy => by simpa [ Fin.ext_iff ] using hxy ) |> fun h =>
      h.eq_iff ];
    · rwa [ Finset.sum_image <| by
      intros a ha b hb hab;
      simpa [ Fin.ext_iff ] using hab, Finset.sum_image <| by
      intros a ha b hb hab;
      simpa [ Fin.ext_iff ] using hab ])

/-
The number of antichains is bounded by the sum of binomial coefficients times 2^((1+epsilon)N).
-/
lemma num_independent_sets_bound (n : ℕ) (ε : ℝ) (Δ : ℕ)
    (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1)
    (hΔ_pos : 1 ≤ Δ) (hΔ_le : (Δ : ℝ) ≤ ε * n / 10)
    (hn : n ≥ 2) :
    (A n : ℝ)
      ≤ (∑ s ∈ range ((PP n).card / (Δ + 1) + 1),
        ((PP n).card.choose s : ℝ)) * (2 : ℝ) ^ ((1 + ε) * (n.choose (n / 2))) := by
      have :=
        @count_independent_sets_via_container_bound n ( Fintype.card ( Finset ( Fin n ) ) / ( Δ + 1
          ) ) ( ( 1 + ε ) * ( n.choose ( n / 2 ) ) );
      obtain ⟨f, hf⟩ : ∃ f : Finset (Finset (Fin n))
        → Finset (Finset (Fin n)), (∀ I : Finset (Finset (Fin n)),
          (G n).IsIndepSet (I : Set (Finset (Fin n)))
          → ∃ S : Finset (Finset (Fin n)), S ⊆ I
        ∧ S.card ≤ Fintype.card (Finset (Fin n)) / (Δ + 1) ∧ I ⊆ S ∪ f S)
          ∧ (∀ S : Finset (Finset (Fin n)), S.card ≤ Fintype.card (Finset (Fin n)) / (Δ + 1)
            → (f S).card ≤ (1 + ε) * (n.choose (n / 2))) := by
        obtain ⟨f, hf⟩ : ∃ f : Finset (Finset (Fin n))
          → Finset (Finset (Fin n)), (∀ I : Finset (Finset (Fin n)),
            (G n).IsIndepSet (I : Set (Finset (Fin n)))
            → ∃ S : Finset (Finset (Fin n)), S ⊆ I
          ∧ S.card ≤ Fintype.card (Finset (Fin n)) / (Δ + 1) ∧ I ⊆ S ∪ f S
            ∧ ((G n).induce (f S)).maxDegree < Δ) := by
          convert graph_container_lemma ( G n ) Δ hΔ_pos using 1;
        use fun S => if h : (f S).card ≤ (1 + ε) * (n.choose (n / 2)) then f S else ∅;
        constructor;
        · intro I hI; obtain ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩ :=
          hf I hI; use S; split_ifs <;> simp_all +decide
          have :=
            low_degree_forces_near_extremal_size n ε hε_pos hε_le_one ( f S ) ?_ ?_<;>
              norm_num at *;
          · linarith;
          · exact lt_of_lt_of_le ( Nat.cast_lt.mpr hS₄ ) ( by simpa using hΔ_le );
          · linarith;
        · intro S hS; split_ifs <;> norm_num;
          · linarith;
          · positivity;
      convert this f hf.1 hf.2 using 1

/-
Definition of Delta_nat(n) as the floor of Delta(n).
-/
noncomputable def Delta_nat (n : ℕ) : ℕ := Nat.floor (Delta n)

/-
Delta_nat(n) is at least 1 for n >= 1000.
-/
lemma Delta_nat_ge_one (n : ℕ) (h : n ≥ 1000) : Delta_nat n ≥ 1 := by
  exact Nat.floor_pos.mpr ( by exact le_trans ( by norm_num ) ( Delta_ge_one n h ) )

/-
Definitions of M_n and t_n, and proof that t_n <= M_n / 2 for large n.
-/
def M_n (n : ℕ) : ℕ := 2 ^ n

noncomputable def t_n (n : ℕ) : ℕ := M_n n / (Delta_nat n + 1)

lemma t_n_le_half_M_n (n : ℕ) (h : n ≥ 1000) : t_n n ≤ M_n n / 2 := by
  -- By definition of $Delta_nat$, we know that $Delta_nat n \geq 1$ for $n \geq 1000$.
  have h_Delta_nat_ge_one : (Delta_nat n : ℝ) ≥ 1 := by
    exact_mod_cast Nat.floor_pos.mpr ( Delta_ge_one n h |> le_trans ( by norm_num ) );
  exact Nat.div_le_div_left ( by norm_cast at *; linarith ) ( by norm_num )

/-
t_n is at least 1 for large n.
-/
lemma t_n_ge_one (n : ℕ) (h : n ≥ 1000) : 1 ≤ t_n n := by
  refine' Nat.div_pos _ ( Nat.succ_pos _ );
  refine' Nat.succ_le_of_lt ( Nat.floor_lt ( _ ) |>.2 _ );
  · exact div_nonneg ( mul_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( Nat.cast_nonneg _
    ) ) ( by norm_num );
  · unfold Delta M_n; norm_num [ epsilon ];
    rw [ Real.rpow_neg ( by positivity ) ];
    rw [ inv_mul_eq_div, div_div, div_lt_iff₀ ] <;> norm_num;
    · refine' lt_of_lt_of_le _ ( le_mul_of_one_le_right _ _ );
      · exact mod_cast Nat.recOn n ( by norm_num ) fun n ih => by
          rw [ pow_succ' ];
          linarith [ Nat.one_le_pow n 2 zero_lt_two ]
      · positivity;
      · exact one_le_mul_of_one_le_of_one_le ( Real.one_le_rpow ( by
        norm_cast;
        linarith ) ( by norm_num ) ) ( by norm_num );
    · positivity

/-
The function x * log2(eM/x) is increasing for x <= M.
-/
lemma x_log_mono (M : ℝ) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ M) :
    x * Real.logb 2 (Real.exp 1 * M / x) ≤ y * Real.logb 2 (Real.exp 1 * M / y) := by
      -- By definition of $f$, we know that its derivative is non-negative.
      have h_deriv_nonneg :
          ∀ t ∈ Set.Icc x M, deriv (fun t =>
            t * (Real.logb 2 (Real.exp 1 * M)) - t * (Real.logb 2 t)) t ≥ 0 := by
        intro t ht
        have ht_pos : 0 < t := lt_of_lt_of_le hx ht.1
        have hM_pos : 0 < M := lt_of_lt_of_le ht_pos ht.2
        have hderiv :
            deriv (fun u => u * (Real.logb 2 (Real.exp 1 * M)) - u * (Real.logb 2 u)) t =
              (Real.log M - Real.log t) / Real.log 2 := by
          unfold Real.logb
          rw [Real.log_mul (Real.exp_ne_zero _) hM_pos.ne', Real.log_exp]
          rw [show (fun u : ℝ =>
            u * ((1 + Real.log M) / Real.log 2) - u * (Real.log u / Real.log 2))
              = (fun u : ℝ =>
                ((1 + Real.log M) / Real.log 2) * u - (Real.log 2)⁻¹ * (u * Real.log u)) by
                funext u
                ring]
          rw [deriv_fun_sub]
          · rw [deriv_const_mul_field ((1 + Real.log M) / Real.log 2)]
            rw [deriv_const_mul_field ((Real.log 2)⁻¹)]
            rw [Real.deriv_mul_log ht_pos.ne', deriv_id'']
            field_simp [Real.log_pos one_lt_two]
            ring
          · fun_prop
          · exact DifferentiableAt.const_mul (Real.hasDerivAt_mul_log ht_pos.ne').differentiableAt _
        rw [hderiv]
        exact div_nonneg (sub_nonneg.mpr (Real.log_le_log ht_pos ht.2)) (le_of_lt (Real.log_pos
          one_lt_two))
      by_contra h_contra;
      -- Apply the mean value theorem to the interval [x, y].
      obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y, deriv (fun t =>
        t * (Real.logb 2 (Real.exp 1 * M)) - t * (Real.logb 2 t)) c = ( (fun t =>
          t * (Real.logb 2 (Real.exp 1 * M)) - t * (Real.logb 2 t)) y - (fun t =>
            t * (Real.logb 2 (Real.exp 1 * M)) - t * (Real.logb 2 t)) x ) / (y - x) := by
        apply_rules [ exists_deriv_eq_slope ];
        · exact hxy.lt_of_ne ( by rintro rfl; norm_num at h_contra );
        · field_simp;
          exact continuousOn_of_forall_continuousAt fun t ht =>
            ContinuousAt.mul continuousAt_id <| ContinuousAt.sub continuousAt_const
              <| ContinuousAt.div_const ( Real.continuousAt_log <| by linarith [ ht.1 ] ) _;
        · exact fun t ht =>
            DifferentiableAt.differentiableWithinAt ( by
              norm_num [ Real.logb, mul_comm, show t ≠ 0 by linarith [ ht.1 ] ] );
      simp_all +decide [ Real.logb_div ( ne_of_gt ( show 0 < Real.exp 1 * M from
        mul_pos ( Real.exp_pos _ ) ( by linarith ) ) ) ( ne_of_gt hx ),
          Real.logb_div ( ne_of_gt ( show 0
          < Real.exp 1 * M from
          mul_pos ( Real.exp_pos _ ) ( by linarith ) ) ) ( ne_of_gt ( by linarith [ hc.1.1 ] : 0
            < y ) ) ];
      rw [ eq_div_iff ] at hc
      · have hder := h_deriv_nonneg c (by linarith [hc.1.1]) (by linarith [hc.1.2, hy])
        have hyx_pos : 0 < y - x := by linarith [hc.1.1, hc.1.2]
        nlinarith [hder, hyx_pos, hc.2, h_contra]
      · linarith [hc.1.1, hc.1.2]

/-
Definition of the refined logarithmic bound.
-/
noncomputable def log_sum_bound_refined (n : ℕ) : ℝ :=
  ((M_n n : ℝ) / (Delta_nat n + 1 : ℝ)) * Real.logb 2 (Real.exp 1 * (Delta_nat n + 1 : ℝ))

/-
The sum of binomial coefficients is bounded by 2 raised to the refined log bound.
-/
lemma sum_binom_le_pow_log_bound (n : ℕ) (h : n ≥ 1000) :
    (∑ s ∈ range (t_n n + 1), ((M_n n).choose s : ℝ)) ≤ (2 : ℝ) ^ (log_sum_bound_refined n) := by
      have h_log : (Real.logb 2 (∑ s ∈ Finset.range (t_n n + 1), ((M_n n).choose s :
          ℝ))) ≤ log_sum_bound_refined n := by
        have h_log : Real.logb 2 (∑ s ∈ Finset.range (t_n n + 1), ((M_n n).choose s : ℝ))
          ≤ (t_n n : ℝ) * Real.logb 2 (Real.exp 1 * (M_n n :
            ℝ) / t_n n) := by
          have := binom_tail_bound ( M_n n ) ( t_n n ) ?_ ?_ ?_ <;> norm_cast at *;
          · rw [ Real.logb, Real.logb, mul_div ];
            gcongr;
            simpa using Real.log_le_log ( Nat.cast_pos.mpr <| Finset.sum_pos ( fun _ _ =>
              Nat.choose_pos <| by
                linarith [ Finset.mem_range.mp ‹_›,
                  show t_n n ≤ M_n n from Nat.div_le_self _ _ ] ) <| by norm_num ) this;
          · exact Nat.one_le_pow _ _ ( by decide );
          · exact t_n_ge_one n h;
          · exact t_n_le_half_M_n n h;
        have h_log_mono : (t_n n : ℝ) * Real.logb 2 (Real.exp 1 * (M_n n : ℝ) / t_n n)
          ≤ ((M_n n : ℝ) / (Delta_nat n + 1 : ℝ)) * Real.logb 2 (Real.exp 1 * (Delta_nat n + 1 :
            ℝ)) := by
          convert x_log_mono ( M_n n : ℝ ) ( t_n n : ℝ ) ( ( M_n n : ℝ ) / ( Delta_nat n + 1 ) ) _
            _ _ using 1<;>
            norm_num;
          · norm_num [ div_div_eq_mul_div, mul_div_cancel_left₀, M_n ];
            exact Or.inl ( by rw [ mul_right_comm, mul_div_cancel_right₀ _ ( by positivity ) ] );
          · exact t_n_ge_one n h;
          · rw [ le_div_iff₀ ] <;> norm_cast <;> norm_num [ t_n, M_n ];
            exact Nat.div_mul_le_self _ _;
          · exact div_le_self ( Nat.cast_nonneg _ ) ( by linarith );
        convert h_log.trans h_log_mono using 1;
      contrapose! h_log;
      rwa [ Real.lt_logb_iff_rpow_lt ( by norm_num )
        ( by exact lt_of_le_of_lt ( by positivity ) h_log ) ]

/-
The ratio of Delta_nat(n) to n^(2/3) tends to 1/10.
-/
lemma Delta_nat_div_pow_tendsto : Filter.Tendsto (fun n => (Delta_nat n : ℝ) / (n : ℝ)^(2/3 :
    ℝ)) Filter.atTop (nhds (1/10)) := by
  -- We'll use the fact that $\Delta_nat(n) \approx \frac{n^{2/3}}{10}$ for large $n$.
  have h_approx : Filter.Tendsto (fun n : ℕ => (Delta_nat n : ℝ) / (n : ℝ) ^ (2 / 3 :
      ℝ)) Filter.atTop (nhds (1 / 10)) := by
    have h_floor : ∀ n : ℕ, n ≥ 1000 → |(Delta_nat n : ℝ) - (n : ℝ) ^ (2 / 3 : ℝ) / 10| ≤ 1 := by
      intro n hn
      have h_floor : (Delta_nat n : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) / 10
        ∧ (n : ℝ) ^ (2 / 3 : ℝ) / 10 < (Delta_nat n + 1 :
          ℝ) := by
        unfold Delta_nat Delta epsilon; norm_num [ ← Real.rpow_add ] ; ring_nf ; norm_num;
        rw [ ← Real.rpow_add_one ] <;> norm_num ; ring_nf ; norm_num;
        · exact ⟨ Nat.floor_le <| by positivity, by linarith [ Nat.lt_floor_add_one
          <| ( n : ℝ ) ^ ( 2 / 3 : ℝ ) * ( 1 / 10 ) ] ⟩;
        · linarith;
      exact abs_sub_le_iff.mpr ⟨ by linarith, by linarith ⟩
    -- Using the fact that $|(Delta_nat n : ℝ) - (n : ℝ) ^ (2 / 3 : ℝ) / 10| ≤ 1$, we can bound the
    -- expression.
    have h_bound : ∀ n : ℕ, n ≥ 1000
      → |((Delta_nat n : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ)) - (1 / 10)| ≤ 1 / (n : ℝ) ^ (2 / 3 :
        ℝ) := by
      intro n hn;
        rw [ abs_le ] ;
        constructor<;>
          nlinarith [ abs_le.mp ( h_floor n hn ), show ( n : ℝ ) ^ ( 2 / 3 : ℝ )
            > 0 by positivity,
              div_mul_cancel₀ ( ( Delta_nat n : ℝ ) : ℝ ) ( show ( n : ℝ ) ^ ( 2 / 3 : ℝ ) ≠ 0 by
                positivity ),
                div_mul_cancel₀ ( 1 : ℝ ) ( show ( n : ℝ ) ^ ( 2 / 3 : ℝ ) ≠ 0 by positivity ) ] ;
    exact tendsto_iff_norm_sub_tendsto_zero.mpr
      <| squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1000, fun n hn =>
      by simpa using h_bound n hn ⟩ ) <| tendsto_inv_atTop_zero.comp
        <| tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop;
  convert h_approx using 1

/-
Delta_nat(n) is Theta(n^(2/3)).
-/
lemma Delta_nat_is_Theta : (fun n => (Delta_nat n : ℝ)) =Θ[atTop] (fun n => (n : ℝ)^(2/3 : ℝ)) := by
  have h_deltaías : Filter.Tendsto (fun n : ℕ => (Delta_nat n : ℝ) / (n : ℝ)^(2/3 :
      ℝ)) Filter.atTop (nhds (1/10)) := by
    convert Delta_nat_div_pow_tendsto using 1;
  have h_deltaías_growth : ∀ᶠ n in Filter.atTop, (Delta_nat n : ℝ) / (n : ℝ)^(2/3 : ℝ) ≥ 1/20
    ∧ (Delta_nat n : ℝ) / (n : ℝ)^(2/3 :
      ℝ) ≤ 1/5 := by
    exact h_deltaías.eventually ( Icc_mem_nhds ( by norm_num ) ( by norm_num ) );
  refine' ⟨ _, _ ⟩;
  · exact Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow h_deltaías;
  · rw [ Asymptotics.isBigO_iff ];
    use 20;
      filter_upwards [ h_deltaías_growth, Filter.eventually_gt_atTop 0 ] with n hn hn';
      rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by
      positivity ) ];
      rw [ ge_iff_le ] at *; rw [ le_div_iff₀ ( by
      positivity ) ] at *;
      linarith;

/-
Delta_nat(n) is Theta(n^(2/3)).
-/
lemma Delta_nat_is_Theta_new : Asymptotics.IsTheta Filter.atTop (fun n =>
  (Delta_nat n : ℝ)) (fun n =>
  (n : ℝ)^(2/3 :
    ℝ)) := by
  convert Delta_nat_is_Theta using 1

/-
Delta_nat(n) + 1 is Theta(n^(2/3)).
-/
lemma Delta_nat_plus_one_is_Theta : (fun n => (Delta_nat n + 1 : ℝ)) =Θ[atTop] (fun n =>
  (n : ℝ)^(2/3 :
    ℝ)) := by
  -- Since $\Delta_{nat}(n) \to \infty$, we have $\Delta_{nat}(n) + 1 \sim \Delta_{nat}(n)$, so
  -- $\Delta_{nat}(n) + 1 = \Theta(n^{2/3})$.
  have Delta_nat_similar : Filter.Tendsto (fun n => (Delta_nat n + 1 : ℝ) / (Delta_nat n :
      ℝ)) Filter.atTop (nhds 1) := by
    have h_delta_nat_tendsto : Filter.Tendsto (fun n => (Delta_nat n :
        ℝ)) Filter.atTop Filter.atTop := by
      have := Delta_nat_div_pow_tendsto;
      -- Since $n^{2/3}$ tends to infinity as $n$ tends to infinity, and their ratio tends to
      -- $1/10$, it follows that $Delta_nat n$ must also tend to infinity.
      have h_n_pow_tendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (2 / 3 :
          ℝ)) Filter.atTop Filter.atTop := by
        exact tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp
          <| tendsto_natCast_atTop_atTop;
      have h_delta_nat_tendsto : Filter.Tendsto (fun n : ℕ =>
        ((Delta_nat n : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ)) * (n : ℝ) ^ (2 / 3 :
          ℝ)) Filter.atTop Filter.atTop := by
        apply_rules [ Filter.Tendsto.pos_mul_atTop, this ];
        norm_num;
      exact h_delta_nat_tendsto.congr' ( by
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
        rw [ div_mul_cancel₀ _ ( by positivity ) ] );
    norm_num [ add_div ];
    exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by
      filter_upwards [ h_delta_nat_tendsto.eventually_ne_atTop 0 ] with n hn;
      aesop ) ) ( tendsto_inv_atTop_zero.comp h_delta_nat_tendsto ) ) ( by norm_num );
  have Delta_nat_plus_one_is_Theta : (fun n => (Delta_nat n + 1 : ℝ)) =Θ[atTop] (fun n =>
    (Delta_nat n :
      ℝ)) := by
    refine' ⟨ _, _ ⟩;
    · rw [ Asymptotics.isBigO_iff ];
      exact ⟨ 2, by
        filter_upwards [ Delta_nat_similar.eventually ( Metric.ball_mem_nhds _ zero_lt_one ) ]
          with n hn
        rw [ Real.norm_of_nonneg ( by positivity ), Real.norm_of_nonneg ( by positivity ) ]
        rw [ div_eq_mul_inv ] at hn
        nlinarith [ abs_lt.mp hn,
          inv_mul_cancel₀ ( show ( Delta_nat n : ℝ ) ≠ 0 from by
            intro h
            norm_num [ h ] at hn ) ] ⟩;
    · rw [ Asymptotics.isBigO_iff ];
      exact ⟨ 1, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => by
        rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ),
          Real.norm_of_nonneg ( add_nonneg ( Nat.cast_nonneg _ ) zero_le_one ) ];
        linarith ⟩ ⟩;
  exact Delta_nat_plus_one_is_Theta.trans ( by simpa using Delta_nat_is_Theta_new )

/-
The log factor in the bound is Theta(log n).
-/
lemma log_Delta_nat_plus_one_is_Theta_log_n :
    (fun n => Real.logb 2 (Real.exp 1 * (Delta_nat n + 1))) =Θ[atTop] (fun n => Real.log n) := by
      -- Using the properties of logarithms, we can simplify the expression.
      have h_log_simplify : Filter.Tendsto (fun n :
          ℕ =>
            Real.log (Real.exp 1 * ((Delta_nat n) + 1)) / Real.log n) Filter.atTop (nhds (2 / 3))
              := by
        -- We'll use the fact that $\log(\Delta_n + 1) \sim \frac{2}{3} \log n$ as $n \to \infty$.
        have h_log_delta : Filter.Tendsto (fun n :
            ℕ => Real.log (Delta_nat n + 1) / Real.log n) Filter.atTop (nhds (2 / 3)) := by
          -- We'll use the fact that $\log(\Delta_n + 1) = \log(n^{2/3}) + \log(1/10 + 1/n^{2/3})$.
          have h_log_approx : Filter.Tendsto (fun n : ℕ => Real.log (Delta_nat n + 1) - (2 / 3 :
              ℝ) * Real.log n) Filter.atTop (nhds (Real.log (1 / 10))) := by
            -- We'll use the fact that $\Delta_nat(n) \approx \frac{n^{2/3}}{10}$ for large $n$.
            have h_delta_approx : Filter.Tendsto (fun n => (Delta_nat n + 1 : ℝ) / n^(2/3 :
                ℝ)) Filter.atTop (nhds (1 / 10)) := by
              convert Delta_nat_div_pow_tendsto.add ( tendsto_inv_atTop_zero.comp (
                tendsto_rpow_atTop ( by
                norm_num : ( 0 : ℝ )
                  < 2 / 3 ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) ) using 2;
                ring_nf;
              · rfl;
              · norm_num;
            have := h_delta_approx.log;
            exact this ( by norm_num ) |> fun h =>
              h.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [
                Real.log_div ( by positivity ) ( by positivity ),
                Real.log_rpow ( by positivity ) ] );
          have :=
            h_log_approx.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
          simpa using this.add_const ( 2 / 3 : ℝ ) |> Filter.Tendsto.congr' ( by
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx;
            rw [ Function.comp_apply, sub_div, mul_div_cancel_right₀ _ ( ne_of_gt <| Real.log_pos
              <| Nat.one_lt_cast.mpr hx ) ] ;
              ring );
        rw [ Filter.tendsto_congr' ( by
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
          rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] ) ];
        simpa [ add_div ] using Filter.Tendsto.add ( tendsto_inv_atTop_zero.comp (
          Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) h_log_delta;
      have h_log_simplify : Filter.Tendsto (fun n :
          ℕ =>
            Real.logb 2 (Real.exp 1 * ((Delta_nat n) + 1)) / Real.log n) Filter.atTop (nhds (2 / 3
              / Real.log 2)) := by
        convert h_log_simplify.div_const ( Real.log 2 ) using 2 ; norm_num [ Real.logb ] ; ring;
      refine' ⟨ _, _ ⟩;
      · rw [ Asymptotics.isBigO_iff ];
        have := h_log_simplify.bddAbove_range;
        obtain ⟨ c, hc ⟩ :=
          this;
            use c;
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
            rw [ Real.norm_of_nonneg ( Real.logb_nonneg ( by norm_num ) <| by
          nlinarith [ Real.add_one_le_exp 1, show ( Delta_nat n : ℝ )
            ≥ 0 by positivity ] ), Real.norm_of_nonneg ( Real.log_nonneg
              <| Nat.one_le_cast.mpr hn.le ) ];
          have :=
            hc ⟨ n, rfl ⟩ ;
              rw [ div_le_iff₀ <| Real.log_pos <| Nat.one_lt_cast.mpr hn ] at this;
              linarith;
      · have := h_log_simplify.inv₀ ; norm_num at *;
        refine' Asymptotics.IsBigO.of_bound ( Real.log 2 / ( 2 / 3 ) + 1 ) _;
        filter_upwards [ this.eventually ( gt_mem_nhds <| show Real.log 2 / ( 2 / 3 )
          < Real.log 2 / ( 2 / 3 ) + 1 by linarith ),
            Filter.eventually_gt_atTop 1 ] with n hn hn'
        rw [ Real.norm_of_nonneg <| Real.log_nonneg <| Nat.one_le_cast.mpr <| by linarith,
          Real.norm_of_nonneg <| Real.logb_nonneg ( by norm_num ) <| by
            nlinarith [ Real.add_one_le_exp 1, show ( Delta_nat n :ℝ ) ≥ 0 by positivity ] ]
        rw [ div_lt_iff₀ <| Real.logb_pos ( by norm_num ) <| by
          nlinarith [ Real.add_one_le_exp 1, show ( Delta_nat n :ℝ ) ≥ 0 by positivity ] ] at hn
        linarith

/-
The simplified term (2^n / n^(2/3) * log n) is little-o of (2^n / sqrt n).
-/
lemma simplified_term_is_little_o :
    (fun n => (2:ℝ)^n / (n:ℝ)^(2/3:ℝ) * Real.log n) =o[atTop] (fun n => (2:ℝ)^n / Real.sqrt n) := by
      -- We can divide both sides by $2^n$ and use the fact that $n^{-1/6} \log n \to 0$ as $n \to
      -- \infty$.
      have h_div : Filter.Tendsto (fun n : ℝ => n ^ (-1 / 6 :
          ℝ) * Real.log n) Filter.atTop (nhds 0) := by
        -- Let $y = \log x$, therefore the expression becomes $\frac{y}{e^{y/6}}$.
        suffices h_log : Filter.Tendsto (fun y : ℝ =>
          y * Real.exp (-y / 6)) Filter.atTop (nhds 0) by
          have h_subst : Filter.Tendsto (fun n :
              ℝ => Real.log n * Real.exp (-Real.log n / 6)) Filter.atTop (nhds 0) := by
            exact h_log.comp Real.tendsto_log_atTop;
          refine h_subst.congr' ( by
            filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
            rw [ Real.rpow_def_of_pos hn ] ; ring_nf );
        -- Let $z = \frac{y}{6}$, therefore the expression becomes $\frac{6z}{e^z}$.
        suffices h_z : Filter.Tendsto (fun z : ℝ => 6 * z * Real.exp (-z)) Filter.atTop (nhds 0) by
          convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by
            norm_num : 0 < ( 6⁻¹ : ℝ ) ) ) using 2;
            norm_num ; ring_nf;
        simpa [ mul_assoc ] using Filter.Tendsto.const_mul 6 (
          Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
      refine' Asymptotics.isLittleO_iff.mpr _;
      intro c hc;
        filter_upwards
          [ h_div.eventually ( Metric.ball_mem_nhds _ hc ), Filter.eventually_gt_atTop 0 ] with x
            hx₁ hx₂;
        norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg hx₂.le ] at *;
      convert mul_le_mul_of_nonneg_right hx₁.le ( show 0
        ≤ |2 ^ x| / |x ^ ( 1 / 2 : ℝ )| by positivity ) using 1 ;
        ring_nf;
      rw [ show ( 2 / 3 : ℝ ) = 1 / 6 + 1 / 2 by norm_num, Real.rpow_add hx₂ ] ; norm_num ; ring

/-
log_sum_bound_refined is Theta of the simplified term.
-/
lemma log_sum_bound_refined_is_Theta_simplified :
    (fun n => log_sum_bound_refined n) =Θ[atTop] (fun n =>
      (2:ℝ)^n / (n:ℝ)^(2/3:ℝ) * Real.log n) := by
      -- Apply the fact that the product of two functions that are Θ of each other is Θ of the
      -- product of their Θ functions.
      have h_prod : (fun n : ℕ => (M_n n : ℝ) / (Delta_nat n + 1)) =Θ[atTop] (fun n : ℕ =>
        (2 : ℝ) ^ n / n ^ (2 / 3 :
          ℝ)) := by
        -- Apply the fact that the product of two functions that are Θ of each other is Θ of the
        -- product of their Θ functions. Use the lemmas Delta_nat_plus_one_is_Theta and
        -- log_Delta_nat_plus_one_is_Theta_log_n.
        have h_prod : (fun n : ℕ => (1 : ℝ) / (Delta_nat n + 1)) =Θ[atTop] (fun n : ℕ =>
          (1 : ℝ) / n ^ (2 / 3 :
            ℝ)) := by
          have h_prod : (fun n : ℕ => (Delta_nat n + 1 : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)^(2/3 :
              ℝ)) := by
            exact Delta_nat_plus_one_is_Theta;
          convert h_prod.inv using 1;
          · norm_num +zetaDelta at *;
          · norm_num;
        -- Apply the fact that the product of two functions that are Θ of each other is Θ of the
        -- product of their Θ functions. Use the lemma Asymptotics.IsTheta.mul.
        have h_prod : (fun n : ℕ => (M_n n : ℝ) * (1 / (Delta_nat n + 1))) =Θ[atTop] (fun n : ℕ =>
          (2 : ℝ) ^ n * (1 / n ^ (2 / 3 :
            ℝ))) := by
          apply_rules [ Asymptotics.IsTheta.mul ];
          unfold M_n; norm_num [ Asymptotics.IsTheta ] ;
          exact Asymptotics.isBigO_refl _ _;
        simpa only [ mul_one_div ] using h_prod;
      have h_log : (fun n : ℕ => Real.logb 2 (Real.exp 1 * (Delta_nat n + 1))) =Θ[atTop] (fun n :
          ℕ => Real.log n) := by
        convert log_Delta_nat_plus_one_is_Theta_log_n using 1;
      convert h_prod.mul h_log using 1

/-
The logarithmic term in the upper bound is little-o of N.
-/
lemma log_sum_bound_refined_is_little_o_N :
    Asymptotics.IsLittleO Filter.atTop log_sum_bound_refined (fun n => (n.choose (n / 2) : ℝ)) := by
      -- By transitivity of asymptotic relations, we can combine the results to conclude the proof.
      have h_trans :
          (fun n => log_sum_bound_refined n) =o[atTop] (fun n => (2:ℝ)^n / Real.sqrt n) := by
        have := simplified_term_is_little_o;
        have h_log_sum_bound_refined :
            (fun n => log_sum_bound_refined n) =Θ[atTop] (fun n =>
              (2:ℝ)^n / (n:ℝ)^(2/3:ℝ) * Real.log n) := by
          convert log_sum_bound_refined_is_Theta_simplified using 1;
        convert h_log_sum_bound_refined.trans_isLittleO _ using 1;
        convert this.comp_tendsto tendsto_natCast_atTop_atTop using 1;
        · exact funext fun n => by rw [ Function.comp_apply ] ; norm_num;
        · exact funext fun n => by rw [ Function.comp_apply ] ; norm_num;
      refine' h_trans.trans_isBigO _;
      -- We'll use the fact that $\binom{n}{n/2} = \Theta(\frac{2^n}{\sqrt{n}})$.
      have h_binom : (fun n => (Nat.choose n (n / 2) :
          ℝ)) =Θ[atTop] (fun n => (2:ℝ)^n / Real.sqrt n) := by
        convert central_binomial_coefficient_asymptotic using 1;
      exact h_binom.symm.isBigO

/-
epsilon(n) tends to 0 as n tends to infinity.
-/
lemma epsilon_tendsto_zero : Filter.Tendsto epsilon Filter.atTop (nhds 0) := by
  convert tendsto_rpow_neg_atTop ( by
    norm_num : ( 0 : ℝ ) < 1 / 3 ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop using 2;
    norm_num [ epsilon ];
  exact funext fun x => by unfold epsilon; norm_num;

/-
The number A(n) of antichains in PP(n) satisfies A(n) = 2^((1+o(1))N).
-/
theorem erdos_497 :
    Asymptotics.IsEquivalent Filter.atTop (fun n => Real.logb 2 (A n)) (fun n =>
      (n.choose (n / 2) : ℝ)) := by
      refine' Asymptotics.isEquivalent_of_tendsto_one _;
      have h_log_A : ∀ᶠ n in Filter.atTop, (n.choose (n / 2) : ℝ) ≤ Real.logb 2 (A n)
        ∧ Real.logb 2 (A n) ≤ (1 + epsilon n) * (n.choose (n / 2) :
          ℝ) + log_sum_bound_refined n := by
          filter_upwards [ Filter.eventually_ge_atTop 1000 ] with n hn;
          constructor;
          · rw [ Real.le_logb_iff_rpow_le ] <;> norm_cast;
            · exact_mod_cast lower_bound_A n;
            · exact Finset.card_pos.mpr ⟨ ∅, Finset.mem_filter.mpr ⟨ Finset.mem_univ _,
              by simp +decide ⟩ ⟩;
          · have h_upper_bound : (A n : ℝ)
            ≤ (2 : ℝ) ^ (log_sum_bound_refined n) * (2 : ℝ) ^ ((1 + epsilon n) * (n.choose (n / 2)
              : ℝ)) := by
              have h_upper_bound : (A n : ℝ)
                ≤ (∑ s ∈ range (t_n n + 1),
                  ((M_n n).choose s : ℝ)) * (2 : ℝ) ^ ((1 + epsilon n) * (n.choose (n / 2) :
                  ℝ)) := by
                convert num_independent_sets_bound n ( epsilon n ) ( Delta_nat n ) _ _ _ _ _ using
                  1;
                any_goals linarith [ Delta_nat_ge_one n hn ];
                · unfold t_n M_n PP; norm_num;
                · exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _;
                · exact epsilon_le_one n ( by linarith );
                · exact Nat.floor_le ( by exact div_nonneg ( mul_nonneg ( Real.rpow_nonneg (
                  Nat.cast_nonneg _ ) _ ) ( Nat.cast_nonneg _ ) ) ( by norm_num ) );
              refine le_trans h_upper_bound ?_;
              gcongr;
              convert sum_binom_le_pow_log_bound n hn using 1;
            rw [ logb_le_iff_le_rpow ] <;> norm_num;
            · convert h_upper_bound using 1 ; rw [ Real.rpow_add ] <;> ring_nf ; norm_num;
            · exact Finset.card_pos.mpr ⟨ ∅, Finset.mem_filter.mpr ⟨ Finset.mem_univ _,
              by simp +decide ⟩ ⟩;
      -- Using the bounds from `h_log_A`, we can show that the ratio of the logarithms tends to 1.
      have h_ratio : Filter.Tendsto (fun n =>
        ((1 + epsilon n) * (n.choose (n / 2) : ℝ) + log_sum_bound_refined n) / (n.choose (n / 2) :
          ℝ)) Filter.atTop (nhds 1) := by
        have h_ratio : Filter.Tendsto (fun n =>
          (1 + epsilon n) + log_sum_bound_refined n / (n.choose (n / 2) :
            ℝ)) Filter.atTop (nhds 1) := by
          have h_ratio : Filter.Tendsto (fun n =>
            epsilon n) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun n =>
              log_sum_bound_refined n / (n.choose (n / 2) :
              ℝ)) Filter.atTop (nhds 0) := by
            exact ⟨ epsilon_tendsto_zero,
              by simpa using log_sum_bound_refined_is_little_o_N.tendsto_div_nhds_zero ⟩;
          simpa using Filter.Tendsto.add ( tendsto_const_nhds.add h_ratio.1 ) h_ratio.2;
        refine h_ratio.congr' ( by
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
          rw [ add_div, mul_div_cancel_right₀ _ ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt
            <| Nat.choose_pos <| Nat.div_le_self _ _ ) ] );
      refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_ratio _ _;
      · filter_upwards [ h_log_A, Filter.eventually_gt_atTop 0 ] with n hn hn'
        rw [ Pi.div_apply,
          le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.choose_pos <| Nat.div_le_self _ _ ) ]
        linarith
      · filter_upwards [ h_log_A, Filter.eventually_gt_atTop 0 ] with n hn hn' using
        div_le_div_of_nonneg_right hn.2
        <| Nat.cast_nonneg _

#print axioms erdos_497
-- 'Erdos497.erdos_497' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos497
