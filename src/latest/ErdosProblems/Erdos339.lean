/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file formalizes the affirmative resolution of Erdős Problem 339.

Mathematical proof and formalization notes: ../../../tex/339.tex
Primary source: Hegyvári--Hennecart--Plagne, J. Reine Angew. Math. 560 (2003), 199--220.
-/

import ErdosProblems.Erdos868
import Util.Density

open Filter Function
open scoped Pointwise BigOperators

namespace Erdos339

/-- Sums of exactly `r` pairwise distinct elements of `A`. -/
def restrictedSums (r : ℕ) (A : Set ℕ) : Set ℕ :=
  {n | ∃ f : Fin r → ℕ, Injective f ∧ (∀ i, f i ∈ A) ∧ ∑ i, f i = n}

/-- A Boolean matrix recording which positions in a representation are equal. -/
abbrev EqPattern (r : ℕ) := Fin r → Fin r → Bool

/-- The sums whose representing tuple has equality matrix `p`. -/
def patternSums (r : ℕ) (A : Set ℕ) (p : EqPattern r) : Set ℕ :=
  {n | ∃ f : Fin r → ℕ,
    (∀ i, f i ∈ A) ∧ (∀ i j, (f i = f j) ↔ p i j = true) ∧ ∑ i, f i = n}

/-- The elements of `S` below `N`, as a finset. -/
noncomputable def prefixFinset (S : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (· ∈ S)

@[simp] lemma mem_prefixFinset {S : Set ℕ} {N n : ℕ} :
    n ∈ prefixFinset S N ↔ n ∈ S ∧ n < N := by
  simp [prefixFinset, and_comm]

lemma prefix_mono_set {S T : Set ℕ} (hST : S ⊆ T) (N : ℕ) :
    prefixFinset S N ⊆ prefixFinset T N := by
  intro n hn
  exact mem_prefixFinset.2 ⟨hST (mem_prefixFinset.1 hn).1, (mem_prefixFinset.1 hn).2⟩

lemma prefix_mono_cutoff (S : Set ℕ) {M N : ℕ} (hMN : M ≤ N) :
    prefixFinset S M ⊆ prefixFinset S N := by
  intro n hn
  exact mem_prefixFinset.2
    ⟨(mem_prefixFinset.1 hn).1, (mem_prefixFinset.1 hn).2.trans_le hMN⟩

lemma prefix_card_eq_ncard (S : Set ℕ) (N : ℕ) :
    (prefixFinset S N).card = (S ∩ Set.Iio N).ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  congr
  ext n
  simp [prefixFinset, and_comm]

/-- Force every coordinate in `s` to be unequal to all other coordinates. -/
def isolatedPattern {r : ℕ} (p : EqPattern r) (s : Finset (Fin r)) : EqPattern r :=
  fun i j ↦ if i ∈ s ∨ j ∈ s then decide (i = j) else p i j

@[simp] lemma isolatedPattern_empty {r : ℕ} (p : EqPattern r) :
    isolatedPattern p ∅ = p := by
  funext i j
  simp [isolatedPattern]

lemma isolatedPattern_insert {r : ℕ} (p : EqPattern r) (s : Finset (Fin r))
    (i : Fin r) :
    isolatedPattern (isolatedPattern p s) {i} = isolatedPattern p (insert i s) := by
  funext a b
  simp only [isolatedPattern, Finset.mem_singleton, Finset.mem_insert]
  split_ifs with h₁ h₂ h₃ <;> simp_all

lemma patternSums_isolated_univ_subset_restrictedSums {r : ℕ} {A : Set ℕ}
    (p : EqPattern r) :
    patternSums r A (isolatedPattern p Finset.univ) ⊆ restrictedSums r A := by
  rintro n ⟨f, hfA, hfp, hsum⟩
  refine ⟨f, ?_, hfA, hsum⟩
  intro i j hij
  have hp : isolatedPattern p Finset.univ i j = true := (hfp i j).1 hij
  simpa [isolatedPattern] using hp

def sumExcept {r : ℕ} (f : Fin r → ℕ) (i : Fin r) : ℕ :=
  ∑ j ∈ (Finset.univ.erase i), f j

lemma sumExcept_add {r : ℕ} (f : Fin r → ℕ) (i : Fin r) :
    sumExcept f i + f i = ∑ j, f j := by
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

lemma sum_update_eq_sumExcept_add {r : ℕ} (f : Fin r → ℕ) (i : Fin r) (x : ℕ) :
    (∑ j, update f i x j) = sumExcept f i + x := by
  rw [← Finset.sum_erase_add (Finset.univ) (update f i x) (Finset.mem_univ i)]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update, Finset.ne_of_mem_erase hj]
  · simp

lemma update_has_isolatedPattern {r : ℕ} {p : EqPattern r} {f : Fin r → ℕ}
    (hfp : ∀ a b, (f a = f b) ↔ p a b = true) (i : Fin r) {x : ℕ}
    (hx : x ∉ Finset.univ.image f) :
    ∀ a b, (update f i x a = update f i x b) ↔ isolatedPattern p {i} a b = true := by
  intro a b
  by_cases hai : a = i <;> by_cases hbi : b = i
  · subst a
    subst b
    simp [isolatedPattern]
  · subst a
    have hne : x ≠ f b := by
      intro hxb
      apply hx
      exact Finset.mem_image.2 ⟨b, Finset.mem_univ _, hxb.symm⟩
    have hib : i ≠ b := Ne.symm hbi
    simp [isolatedPattern, hbi, hib, hne]
  · subst b
    have hne : f a ≠ x := by
      intro hax
      apply hx
      exact Finset.mem_image.2 ⟨a, Finset.mem_univ _, hax⟩
    simp [isolatedPattern, hai, hne]
  · simp [isolatedPattern, hai, hbi, hfp a b]

/-! ## A finite forbidden-pair estimate -/

/-- All sums `v b + x` with `b` in a finite type and `x ∈ X`. -/
noncomputable def fullSums {β : Type*} [Fintype β] (v : β → ℕ) (X : Finset ℕ) :
    Finset ℕ := by
  classical
  exact Finset.univ.biUnion fun b ↦ X.image fun x ↦ v b + x

/-- The sums `v b + x` for which `x` is not one of the forbidden partners of `b`. -/
noncomputable def allowedSums {β : Type*} [Fintype β] (v : β → ℕ) (X : Finset ℕ)
    (F : β → Finset ℕ) : Finset ℕ := by
  classical
  exact Finset.univ.biUnion fun b ↦ (X \ F b).image fun x ↦ v b + x

lemma card_fullSums_le_card_allowedSums {β : Type*} [Fintype β]
    (v : β → ℕ) (hv : Injective v) (X : Finset ℕ) (F : β → Finset ℕ) (k : ℕ)
    (hFcard : ∀ b, (F b).card ≤ k) (hX : k + 1 ≤ X.card) :
    (fullSums v X).card ≤ (1 + k * (k + 1)) * (allowedSums v X F).card := by
  classical
  let badSums : Finset ℕ :=
    Finset.univ.biUnion fun b : β ↦ (F b).image fun x ↦ v b + x
  have hfull : fullSums v X ⊆ allowedSums v X F ∪ badSums := by
    intro y hy
    rcases Finset.mem_biUnion.1 hy with ⟨b, _, hyb⟩
    rcases Finset.mem_image.1 hyb with ⟨x, hxX, rfl⟩
    by_cases hxF : x ∈ F b
    · exact Finset.mem_union_right _ <| Finset.mem_biUnion.2
        ⟨b, Finset.mem_univ _, Finset.mem_image.2 ⟨x, hxF, rfl⟩⟩
    · exact Finset.mem_union_left _ <| Finset.mem_biUnion.2
        ⟨b, Finset.mem_univ _, Finset.mem_image.2
          ⟨x, Finset.mem_sdiff.2 ⟨hxX, hxF⟩, rfl⟩⟩
  have hbad : badSums.card ≤ Fintype.card β * k := by
    apply Finset.card_biUnion_le_card_mul
    intro b _
    exact (Finset.card_image_le.trans (hFcard b))
  obtain ⟨T, hTX, hTcard⟩ := Finset.exists_subset_card_eq hX
  let good (t : ℕ) : Finset β := Finset.univ.filter fun b ↦ t ∉ F b
  have hcover : (Finset.univ : Finset β) ⊆ T.biUnion good := by
    intro b _
    have hnsub : ¬T ⊆ F b := by
      intro hsub
      have hc := Finset.card_le_card hsub
      rw [hTcard] at hc
      exact (Nat.not_succ_le_self k) (hc.trans (hFcard b))
    obtain ⟨t, htT, htF⟩ := Finset.not_subset.1 hnsub
    exact Finset.mem_biUnion.2 ⟨t, htT, by simp [good, htF]⟩
  have hgood (t : ℕ) (ht : t ∈ T) : (good t).card ≤ (allowedSums v X F).card := by
    let imageGood : Finset ℕ := (good t).image fun b ↦ v b + t
    have himage : imageGood ⊆ allowedSums v X F := by
      intro y hy
      rcases Finset.mem_image.1 hy with ⟨b, hb, rfl⟩
      have htX : t ∈ X := hTX ht
      have htF : t ∉ F b := (Finset.mem_filter.1 hb).2
      exact Finset.mem_biUnion.2 ⟨b, Finset.mem_univ _, Finset.mem_image.2
        ⟨t, Finset.mem_sdiff.2 ⟨htX, htF⟩, rfl⟩⟩
    have hinj : Set.InjOn (fun b : β ↦ v b + t) (good t : Set β) := by
      intro a _ b _ hab
      apply hv
      exact Nat.add_right_cancel hab
    calc
      (good t).card = imageGood.card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ (allowedSums v X F).card := Finset.card_le_card himage
  have hβ : Fintype.card β ≤ (k + 1) * (allowedSums v X F).card := by
    calc
      Fintype.card β = (Finset.univ : Finset β).card := by simp
      _ ≤ (T.biUnion good).card := Finset.card_le_card hcover
      _ ≤ T.card * (allowedSums v X F).card :=
        Finset.card_biUnion_le_card_mul T good _ hgood
      _ = (k + 1) * (allowedSums v X F).card := by rw [hTcard]
  calc
    (fullSums v X).card ≤ (allowedSums v X F ∪ badSums).card :=
      Finset.card_le_card hfull
    _ ≤ (allowedSums v X F).card + badSums.card := Finset.card_union_le _ _
    _ ≤ (allowedSums v X F).card + Fintype.card β * k :=
      Nat.add_le_add_left hbad _
    _ ≤ (allowedSums v X F).card + ((k + 1) * (allowedSums v X F).card) * k :=
      Nat.add_le_add_left (Nat.mul_le_mul_right k hβ) _
    _ = (1 + k * (k + 1)) * (allowedSums v X F).card := by ring_nf

/-! ## Splitting one coordinate of an equality pattern -/

lemma patternSums_step {r N : ℕ} {A : Set ℕ} (p : EqPattern r) (i : Fin r)
    (hXcard : r + 1 ≤ (prefixFinset A N).card) :
    (prefixFinset (patternSums r A p) N).card ≤
      (1 + r * (r + 1)) *
        (prefixFinset (patternSums r A (isolatedPattern p {i})) (2 * N)).card := by
  classical
  let P : Finset ℕ := prefixFinset (patternSums r A p) N
  have hex (n : {n // n ∈ P}) : ∃ f : Fin r → ℕ,
      (∀ j, f j ∈ A) ∧ (∀ a b, (f a = f b) ↔ p a b = true) ∧ ∑ j, f j = n := by
    exact (mem_prefixFinset.1 n.property).1
  let w : {n // n ∈ P} → Fin r → ℕ := fun n ↦ Classical.choose (hex n)
  have hw (n : {n // n ∈ P}) :
      (∀ j, w n j ∈ A) ∧ (∀ a b, (w n a = w n b) ↔ p a b = true) ∧
        ∑ j, w n j = n :=
    Classical.choose_spec (hex n)
  have hw_le (n : {n // n ∈ P}) (j : Fin r) : w n j ≤ n := by
    rw [← (hw n).2.2]
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  have hw_lt (n : {n // n ∈ P}) (j : Fin r) : w n j < N :=
    (hw_le n j).trans_lt (mem_prefixFinset.1 n.property).2
  let base (n : {n // n ∈ P}) : ℕ := sumExcept (w n) i
  have hbase_add (n : {n // n ∈ P}) : base n + w n i = n := by
    change sumExcept (w n) i + w n i = n
    rw [sumExcept_add, (hw n).2.2]
  let B : Finset ℕ := Finset.univ.image base
  have hbase_mem (n : {n // n ∈ P}) : base n ∈ B := by
    exact Finset.mem_image.2 ⟨n, Finset.mem_univ _, rfl⟩
  have hsource (b : {b // b ∈ B}) : ∃ n : {n // n ∈ P}, base n = b := by
    simpa [B] using b.property
  let source (b : {b // b ∈ B}) : {n // n ∈ P} := Classical.choose (hsource b)
  have hsource_eq (b : {b // b ∈ B}) : base (source b) = b :=
    Classical.choose_spec (hsource b)
  let X : Finset ℕ := prefixFinset A N
  let F (b : {b // b ∈ B}) : Finset ℕ := Finset.univ.image (w (source b))
  have hFcard (b : {b // b ∈ B}) : (F b).card ≤ r := by
    simpa [F] using (Finset.card_image_le :
      (Finset.univ.image (w (source b))).card ≤ Finset.univ.card)
  have hPfull : P ⊆ fullSums (fun b : {b // b ∈ B} ↦ b.1) X := by
    intro n hn
    let ns : {n // n ∈ P} := ⟨n, hn⟩
    let b : {b // b ∈ B} := ⟨base ns, hbase_mem ns⟩
    apply Finset.mem_biUnion.2
    refine ⟨b, Finset.mem_univ _, Finset.mem_image.2 ⟨w ns i, ?_, ?_⟩⟩
    · exact mem_prefixFinset.2 ⟨(hw ns).1 i, hw_lt ns i⟩
    · change base ns + w ns i = n
      exact hbase_add ns
  have hallowed :
      allowedSums (fun b : {b // b ∈ B} ↦ b.1) X F ⊆
        prefixFinset (patternSums r A (isolatedPattern p {i})) (2 * N) := by
    intro y hy
    rcases Finset.mem_biUnion.1 hy with ⟨b, _, hyb⟩
    rcases Finset.mem_image.1 hyb with ⟨x, hx, rfl⟩
    have hxX : x ∈ X := (Finset.mem_sdiff.1 hx).1
    have hxF : x ∉ F b := (Finset.mem_sdiff.1 hx).2
    let f' : Fin r → ℕ := update (w (source b)) i x
    have hf'A : ∀ j, f' j ∈ A := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [f'] using (mem_prefixFinset.1 hxX).1
      · simpa [f', Function.update, hji] using (hw (source b)).1 j
    have hf'pattern : ∀ a c,
        (f' a = f' c) ↔ isolatedPattern p {i} a c = true := by
      exact update_has_isolatedPattern (hw (source b)).2.1 i (by simpa [F] using hxF)
    have hf'sum : (∑ j, f' j) = b.1 + x := by
      change (∑ j, update (w (source b)) i x j) = b.1 + x
      rw [sum_update_eq_sumExcept_add]
      change base (source b) + x = b.1 + x
      rw [hsource_eq b]
    apply mem_prefixFinset.2
    refine ⟨⟨f', hf'A, hf'pattern, hf'sum⟩, ?_⟩
    have hb_lt : b.1 < N := by
      rw [← hsource_eq b]
      exact (Nat.le_add_right _ _).trans_lt
        ((hbase_add (source b)) ▸ (mem_prefixFinset.1 (source b).property).2)
    simpa [two_mul] using Nat.add_lt_add hb_lt (mem_prefixFinset.1 hxX).2
  calc
    P.card ≤ (fullSums (fun b : {b // b ∈ B} ↦ b.1) X).card :=
      Finset.card_le_card hPfull
    _ ≤ (1 + r * (r + 1)) *
        (allowedSums (fun b : {b // b ∈ B} ↦ b.1) X F).card :=
      card_fullSums_le_card_allowedSums _ Subtype.val_injective _ _ r hFcard
        (by simpa [X] using hXcard)
    _ ≤ (1 + r * (r + 1)) *
        (prefixFinset (patternSums r A (isolatedPattern p {i})) (2 * N)).card :=
      Nat.mul_le_mul_left _ (Finset.card_le_card hallowed)

lemma patternSums_isolate_finset {r : ℕ} {A : Set ℕ} (p : EqPattern r)
    (s : Finset (Fin r)) {N : ℕ} (hXcard : r + 1 ≤ (prefixFinset A N).card) :
    (prefixFinset (patternSums r A p) N).card ≤
      (1 + r * (r + 1)) ^ s.card *
        (prefixFinset (patternSums r A (isolatedPattern p s)) (2 ^ s.card * N)).card := by
  classical
  induction s using Finset.induction_on generalizing N with
  | empty => simp [isolatedPattern_empty]
  | @insert i s hi ih =>
      have hNM : N ≤ 2 ^ s.card * N := by
        have hpow : 1 ≤ 2 ^ s.card := Nat.one_le_pow _ _ (by omega)
        have hmul := Nat.mul_le_mul_right N hpow
        simpa [mul_comm] using hmul
      have hXcard' : r + 1 ≤ (prefixFinset A (2 ^ s.card * N)).card :=
        hXcard.trans <| Finset.card_le_card (prefix_mono_cutoff A hNM)
      have hstep := patternSums_step (A := A) (N := 2 ^ s.card * N)
        (isolatedPattern p s) i hXcard'
      calc
        (prefixFinset (patternSums r A p) N).card ≤
            (1 + r * (r + 1)) ^ s.card *
              (prefixFinset (patternSums r A (isolatedPattern p s))
                (2 ^ s.card * N)).card := ih hXcard
        _ ≤ (1 + r * (r + 1)) ^ s.card *
              ((1 + r * (r + 1)) *
                (prefixFinset
                  (patternSums r A (isolatedPattern (isolatedPattern p s) {i}))
                  (2 * (2 ^ s.card * N))).card) :=
            Nat.mul_le_mul_left _ hstep
        _ = (1 + r * (r + 1)) ^ (insert i s).card *
              (prefixFinset (patternSums r A (isolatedPattern p (insert i s)))
                (2 ^ (insert i s).card * N)).card := by
            rw [Finset.card_insert_of_notMem hi, isolatedPattern_insert]
            simp only [pow_succ]
            ring_nf

lemma patternSums_le_restrictedSums {r N : ℕ} {A : Set ℕ} (p : EqPattern r)
    (hXcard : r + 1 ≤ (prefixFinset A N).card) :
    (prefixFinset (patternSums r A p) N).card ≤
      (1 + r * (r + 1)) ^ r *
        (prefixFinset (restrictedSums r A) (2 ^ r * N)).card := by
  have h := patternSums_isolate_finset (A := A) p Finset.univ hXcard
  simpa using h.trans <| Nat.mul_le_mul_left _ <|
    Finset.card_le_card <| prefix_mono_set
      (patternSums_isolated_univ_subset_restrictedSums p) _

/-! ## The finite equality-pattern cover -/

lemma mem_nsmul_iff_tuple {r n : ℕ} {A : Set ℕ} :
    n ∈ r • A ↔ ∃ f : Fin r → ℕ, (∀ i, f i ∈ A) ∧ ∑ i, f i = n := by
  simpa using Set.mem_fintype_sum (fun _ : Fin r ↦ A) n

lemma nsmul_subset_iUnion_patternSums {r : ℕ} {A : Set ℕ} :
    r • A ⊆ ⋃ p : EqPattern r, patternSums r A p := by
  intro n hn
  rw [mem_nsmul_iff_tuple] at hn
  rcases hn with ⟨f, hfA, hsum⟩
  let p : EqPattern r := fun i j ↦ decide (f i = f j)
  exact Set.mem_iUnion.2 ⟨p, f, hfA, by simp [p], hsum⟩

noncomputable def patternUnionPrefix (r : ℕ) (A : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact Finset.univ.biUnion fun p : EqPattern r ↦ prefixFinset (patternSums r A p) N

lemma prefix_nsmul_subset_patternUnionPrefix {r N : ℕ} {A : Set ℕ} :
    prefixFinset (r • A) N ⊆ patternUnionPrefix r A N := by
  classical
  intro n hn
  obtain ⟨p, hp⟩ := Set.mem_iUnion.1 <|
    nsmul_subset_iUnion_patternSums (mem_prefixFinset.1 hn).1
  exact Finset.mem_biUnion.2 ⟨p, Finset.mem_univ _,
    mem_prefixFinset.2 ⟨hp, (mem_prefixFinset.1 hn).2⟩⟩

lemma nsmul_prefix_le_restricted_prefix {r N : ℕ} {A : Set ℕ}
    (hXcard : r + 1 ≤ (prefixFinset A N).card) :
    (prefixFinset (r • A) N).card ≤
      Fintype.card (EqPattern r) * (1 + r * (r + 1)) ^ r *
        (prefixFinset (restrictedSums r A) (2 ^ r * N)).card := by
  classical
  calc
    (prefixFinset (r • A) N).card ≤ (patternUnionPrefix r A N).card :=
      Finset.card_le_card prefix_nsmul_subset_patternUnionPrefix
    _ ≤ Fintype.card (EqPattern r) *
          ((1 + r * (r + 1)) ^ r *
            (prefixFinset (restrictedSums r A) (2 ^ r * N)).card) := by
      apply Finset.card_biUnion_le_card_mul
      intro p _
      exact patternSums_le_restrictedSums p hXcard
    _ = Fintype.card (EqPattern r) * (1 + r * (r + 1)) ^ r *
          (prefixFinset (restrictedSums r A) (2 ^ r * N)).card := by ring_nf

/-! ## Consequences of the asymptotic-basis hypothesis -/

lemma infinite_of_isAsymptoticAddBasisOfOrder {r : ℕ} {A : Set ℕ}
    (hA : A.IsAsymptoticAddBasisOfOrder r) : A.Infinite := by
  intro hAfin
  have hsumFinAll : ∀ n : ℕ, (n • A).Finite := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [succ_nsmul]
        exact ih.add hAfin
  have hsumFin : (r • A).Finite := hsumFinAll r
  obtain ⟨M, hM⟩ := hsumFin.bddAbove
  obtain ⟨n, hnA, hnM⟩ :=
    ((Set.isAsymptoticAddBasisOfOrder_iff_atTop.1 hA).and
      (Filter.eventually_gt_atTop M)).exists
  exact (not_le_of_gt hnM) (hM hnA)

lemma eventually_large_prefix_of_infinite {r : ℕ} {A : Set ℕ} (hA : A.Infinite) :
    ∀ᶠ N in atTop, r + 1 ≤ (prefixFinset A N).card := by
  obtain ⟨T, hTA, hTfin, hTcard⟩ := hA.exists_subset_ncard_eq (r + 1)
  obtain ⟨M, hM⟩ := hTfin.bddAbove
  filter_upwards [Filter.eventually_ge_atTop (M + 1)] with N hN
  have hsub : hTfin.toFinset ⊆ prefixFinset A N := by
    intro x hx
    have hxT : x ∈ T := by simpa using hx
    exact mem_prefixFinset.2 ⟨hTA hxT, (Nat.lt_succ_of_le (hM hxT)).trans_le hN⟩
  calc
    r + 1 = hTfin.toFinset.card := by
      rw [← Set.ncard_eq_toFinset_card T hTfin, hTcard]
    _ ≤ (prefixFinset A N).card := Finset.card_le_card hsub

lemma basis_prefix_card_lower_bound {r : ℕ} {A : Set ℕ}
    (hA : A.IsAsymptoticAddBasisOfOrder r) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, N - N₀ ≤ (prefixFinset (r • A) N).card := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 <|
    Set.isAsymptoticAddBasisOfOrder_iff_atTop.1 hA
  refine ⟨N₀, fun N hNN₀ ↦ ?_⟩
  have hsub : Finset.Ico N₀ N ⊆ prefixFinset (r • A) N := by
    intro n hn
    have hn' : N₀ ≤ n ∧ n < N := by simpa using hn
    exact mem_prefixFinset.2 ⟨hN₀ n hn'.1, hn'.2⟩
  simpa using Finset.card_le_card hsub

lemma partialDensity_nat_eq_prefix_card (S : Set ℕ) (N : ℕ) :
    S.partialDensity Set.univ N =
      (prefixFinset S N).card / (N : ℝ) := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  rw [← prefix_card_eq_ncard]
  simp

/-!
## Erdős Problem 339

The theorem uses the standard definition from `Erdos868`: `A` is an asymptotic additive
basis of order `r` when its unrestricted `r`-fold sumset is cofinite.  The conclusion concerns
exactly `r` pairwise distinct summands, as specified by `restrictedSums`.
-/

theorem erdos_339 {A : Set ℕ} {r : ℕ} (hA : A.IsAsymptoticAddBasisOfOrder r) :
    0 < (restrictedSums r A).lowerDensity := by
  let q : ℕ := 2 ^ r
  let K : ℕ := Fintype.card (EqPattern r) * (1 + r * (r + 1)) ^ r
  have hq : 0 < q := by
    dsimp [q]
    exact pow_pos (by omega) _
  have hK : 0 < K := by
    dsimp [K]
    exact Nat.mul_pos Fintype.card_pos (pow_pos (by omega) _)
  have hAinf : A.Infinite := infinite_of_isAsymptoticAddBasisOfOrder hA
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 <|
    eventually_large_prefix_of_infinite (r := r) hAinf
  obtain ⟨N₀, hN₀⟩ := basis_prefix_card_lower_bound hA
  let L : ℕ := max N₀ N₁
  have hN₀L : N₀ ≤ L := Nat.le_max_left _ _
  have hN₁L : N₁ ≤ L := Nat.le_max_right _ _
  let D : ℕ := 4 * q * K
  have hD : 0 < D := by
    dsimp [D]
    exact Nat.mul_pos (Nat.mul_pos (by omega) hq) hK
  have heventual : ∀ᶠ M in atTop,
      (1 : ℝ) / D ≤ (restrictedSums r A).partialDensity Set.univ M := by
    filter_upwards [Filter.eventually_ge_atTop ((2 * L + 1) * (2 * q))] with M hM
    let N : ℕ := M / (2 * q)
    have htwoq : 0 < 2 * q := Nat.mul_pos (by omega) hq
    have hNlarge : 2 * L + 1 ≤ N := by
      apply (Nat.le_div_iff_mul_le htwoq).2
      exact hM
    have hNN₀ : N₀ ≤ N := hN₀L.trans (by omega)
    have hNN₁ : N₁ ≤ N := hN₁L.trans (by omega)
    have hAc : r + 1 ≤ (prefixFinset A N).card := hN₁ N hNN₁
    have hbasic : N - N₀ ≤
        K * (prefixFinset (restrictedSums r A) (q * N)).card := by
      calc
        N - N₀ ≤ (prefixFinset (r • A) N).card := hN₀ N hNN₀
        _ ≤ K * (prefixFinset (restrictedSums r A) (q * N)).card := by
          simpa [K, q] using nsmul_prefix_le_restricted_prefix (A := A) hAc
    have hqNM : q * N ≤ M := by
      have htwoqNM : (2 * q) * N ≤ M := by
        simpa [N] using Nat.mul_div_le M (2 * q)
      exact (Nat.mul_le_mul_right N (Nat.le_mul_of_pos_left q (by omega))).trans htwoqNM
    have hprefixMono :
        (prefixFinset (restrictedSums r A) (q * N)).card ≤
          (prefixFinset (restrictedSums r A) M).card :=
      Finset.card_le_card (prefix_mono_cutoff _ hqNM)
    have hcount : N - N₀ ≤
        K * (prefixFinset (restrictedSums r A) M).card :=
      hbasic.trans (Nat.mul_le_mul_left K hprefixMono)
    have hMlt : M < (N + 1) * (2 * q) := by
      apply (Nat.div_lt_iff_lt_mul htwoq).1
      simp [N]
    have hNrel : N + 1 ≤ 2 * (N - N₀) := by omega
    have hMcount : M ≤ D * (prefixFinset (restrictedSums r A) M).card := by
      calc
        M ≤ (N + 1) * (2 * q) := Nat.le_of_lt hMlt
        _ ≤ (2 * (N - N₀)) * (2 * q) := Nat.mul_le_mul_right _ hNrel
        _ = 4 * q * (N - N₀) := by ring_nf
        _ ≤ 4 * q *
              (K * (prefixFinset (restrictedSums r A) M).card) :=
          Nat.mul_le_mul_left (4 * q) hcount
        _ = D * (prefixFinset (restrictedSums r A) M).card := by
          simp only [D]
          ring_nf
    have hMpos : 0 < M :=
      lt_of_lt_of_le (Nat.mul_pos (by omega) htwoq) hM
    rw [partialDensity_nat_eq_prefix_card]
    apply (div_le_div_iff₀ (Nat.cast_pos.2 hD) (Nat.cast_pos.2 hMpos)).2
    have hMcount' : (M : ℝ) ≤
        (D : ℝ) * ((prefixFinset (restrictedSums r A) M).card : ℝ) := by
      exact_mod_cast hMcount
    simpa [mul_comm] using hMcount'
  have hlower : (1 : ℝ) / D ≤ (restrictedSums r A).lowerDensity := by
    rw [Set.lowerDensity]
    exact le_liminf_of_le
      (isCoboundedUnder_ge_of_le (x := 1) atTop
        (fun M ↦ Set.partialDensity_le_one (restrictedSums r A) Set.univ M))
      heventual
  exact (div_pos one_pos (Nat.cast_pos.2 hD)).trans_le hlower

end Erdos339

#print axioms Erdos339.erdos_339
