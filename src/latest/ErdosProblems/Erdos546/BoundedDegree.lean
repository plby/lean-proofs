/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos546.Basic
import ErdosProblems.Erdos546.Numeric

/-!
# The bounded-degree sparse-pair lemma

This file gives the greedy bounded-degree embedding input used in the dyadic
sparsification argument.  All density assertions are expressed by natural
number cross-multiplication, and the final copy is non-induced.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos546

open Finset
open SimpleGraph

/-! ## Trimming a finite set without increasing an average -/

private lemma sum_nonneg_of_nonneg {α : Type*} (s : Finset α) (w : α → ℚ)
    (hw : ∀ x ∈ s, 0 ≤ w x) :
    0 ≤ ∑ x ∈ s, w x := by
  exact Finset.sum_nonneg fun x hx ↦ hw x hx

/-- A finite family of nonnegative weights has a `t`-subset whose average is
at most the average on the whole family.  The division-free form is useful
over `ℕ` after casting. -/
private lemma exists_subset_card_eq_mul_sum_le
    {α : Type*} (w : α → ℚ) (X : Finset α) (t : ℕ)
    (hw : ∀ x ∈ X, 0 ≤ w x) (ht : t ≤ X.card) :
    ∃ A ⊆ X, A.card = t ∧
      (X.card : ℚ) * (∑ x ∈ A, w x) ≤
        (t : ℚ) * (∑ x ∈ X, w x) := by
  classical
  induction X using Finset.induction_on generalizing t with
  | empty =>
      have ht0 : t = 0 := by simpa using ht
      subst t
      exact ⟨∅, by simp⟩
  | @insert a X ha ih =>
      by_cases ht0 : t = 0
      · subst t
        exact ⟨∅, by simp⟩
      by_cases htall : t = (insert a X).card
      · subst t
        refine ⟨insert a X, by simp, rfl, ?_⟩
        simp
      have htpos : 0 < t := Nat.pos_of_ne_zero ht0
      have ht' : t - 1 ≤ X.card := by simpa [Finset.card_insert_of_notMem ha] using ht
      have htX : t ≤ X.card := by
        rw [Finset.card_insert_of_notMem ha] at ht htall
        omega
      have hwa : 0 ≤ w a := hw a (by simp)
      have hwX : ∀ x ∈ X, 0 ≤ w x := fun x hx ↦ hw x (by simp [hx])
      have hsumX : 0 ≤ ∑ x ∈ X, w x := sum_nonneg_of_nonneg X w hwX
      let n : ℚ := X.card
      let z : ℚ := ∑ x ∈ X, w x
      by_cases havg : (X.card : ℚ) * w a ≤ ∑ x ∈ X, w x
      · obtain ⟨A, hAX, hAcard, hAavg⟩ := ih (t - 1) hwX ht'
        refine ⟨insert a A, ?_, ?_, ?_⟩
        · intro x hx
          simp only [mem_insert] at hx ⊢
          exact hx.elim (fun h ↦ h ▸ Or.inl rfl) (fun h ↦ Or.inr (hAX h))
        · have haA : a ∉ A := fun h ↦ ha (hAX h)
          simp [Finset.card_insert_of_notMem haA, hAcard, Nat.sub_add_cancel htpos]
        · have haA : a ∉ A := fun h ↦ ha (hAX h)
          simp only [Finset.card_insert_of_notMem ha,
            sum_insert haA, sum_insert ha]
          push_cast at hAavg havg ⊢
          have hAsum_le : (∑ x ∈ A, w x) ≤ ∑ x ∈ X, w x :=
            Finset.sum_le_sum_of_subset_of_nonneg hAX fun i hi _ ↦ hwX i hi
          have hcard : (t : ℚ) ≤ (X.card : ℚ) + 1 := by
            rw [Finset.card_insert_of_notMem ha] at ht
            exact_mod_cast ht
          have htcast : ((t - 1 : ℕ) : ℚ) = (t : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ t)]
            norm_num
          rw [htcast] at hAavg
          by_cases hX0 : X.card = 0
          · exact (by omega : False).elim
          · have hXpos : (0 : ℚ) < X.card := by exact_mod_cast Nat.pos_of_ne_zero hX0
            have hfac : (0 : ℚ) ≤ (X.card : ℚ) + 1 - t := by
              exact sub_nonneg.mpr hcard
            have h1 := mul_le_mul_of_nonneg_left havg hfac
            have h2 := mul_le_mul_of_nonneg_left hAavg
              (show (0 : ℚ) ≤ (X.card : ℚ) + 1 by positivity)
            nlinarith
      · obtain ⟨A, hAX, hAcard, hAavg⟩ := ih t hwX htX
        refine ⟨A, hAX.trans (by simp), hAcard, ?_⟩
        simp only [Finset.card_insert_of_notMem ha, sum_insert ha]
        push_cast at hAavg havg ⊢
        have hAsum : 0 ≤ ∑ x ∈ A, w x :=
          sum_nonneg_of_nonneg A w fun x hx ↦ hwX x (hAX hx)
        have hcardpos : (0 : ℚ) < X.card := by
          exact_mod_cast (lt_of_lt_of_le htpos htX)
        nlinarith

private lemma crossEdgeCount_eq_sum_left {N : ℕ} (H : SimpleGraph (Fin N))
    [DecidableRel H.Adj]
    (X Y : Finset (Fin N)) :
    crossEdgeCount H X Y = ∑ x ∈ X, (Y.filter fun y ↦ H.Adj x y).card := by
  classical
  rw [crossEdgeCount, SimpleGraph.interedges_def]
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hxy : H.Adj x y <;> simp [hxy]

private lemma crossEdgeCount_eq_sum_right {N : ℕ} (H : SimpleGraph (Fin N))
    [DecidableRel H.Adj] (X Y : Finset (Fin N)) :
    crossEdgeCount H X Y = ∑ y ∈ Y, (X.filter fun x ↦ H.Adj x y).card := by
  calc
    crossEdgeCount H X Y = crossEdgeCount H Y X := crossEdgeCount_comm H X Y
    _ = ∑ y ∈ Y, (X.filter fun x ↦ H.Adj y x).card :=
      crossEdgeCount_eq_sum_left H Y X
    _ = ∑ y ∈ Y, (X.filter fun x ↦ H.Adj x y).card := by
      apply Finset.sum_congr rfl
      intro y hy
      congr 1
      ext x
      simp [H.adj_comm]

/-- Sparse unequal sets can be trimmed to equal prescribed size without
increasing their denominator-free density. -/
lemma exists_equal_sparse_subsets {N k t : ℕ} (H : SimpleGraph (Fin N))
    {X Y : Finset (Fin N)} (hX : t ≤ X.card) (hY : t ≤ Y.card)
    (hSparse : k * crossEdgeCount H X Y ≤ X.card * Y.card) :
    ∃ A B : Finset (Fin N), A ⊆ X ∧ B ⊆ Y ∧ A.card = t ∧ B.card = t ∧
      k * crossEdgeCount H A B ≤ A.card * B.card := by
  classical
  by_cases ht0 : t = 0
  · subst t
    exact ⟨∅, ∅, by simp [crossEdgeCount]⟩
  have htpos : 0 < t := Nat.pos_of_ne_zero ht0
  let wx : Fin N → ℚ := fun x ↦ ((Y.filter fun y ↦ H.Adj x y).card : ℚ)
  have hwx : ∀ x ∈ X, 0 ≤ wx x := by intro x hx; simp [wx]
  obtain ⟨A, hAX, hAcard, hAavg⟩ :=
    exists_subset_card_eq_mul_sum_le wx X t hwx hX
  let wy : Fin N → ℚ := fun y ↦ ((A.filter fun x ↦ H.Adj x y).card : ℚ)
  have hwy : ∀ y ∈ Y, 0 ≤ wy y := by intro y hy; simp [wy]
  obtain ⟨B, hBY, hBcard, hBavg⟩ :=
    exists_subset_card_eq_mul_sum_le wy Y t hwy hY
  refine ⟨A, B, hAX, hBY, hAcard, hBcard, ?_⟩
  have hsumX : (∑ x ∈ A, wx x) = (crossEdgeCount H A Y : ℚ) := by
    simp only [wx, ← Nat.cast_sum]
    exact_mod_cast (crossEdgeCount_eq_sum_left H A Y).symm
  have hsumXY : (∑ x ∈ X, wx x) = (crossEdgeCount H X Y : ℚ) := by
    simp only [wx, ← Nat.cast_sum]
    exact_mod_cast (crossEdgeCount_eq_sum_left H X Y).symm
  have hsumY : (∑ y ∈ B, wy y) = (crossEdgeCount H A B : ℚ) := by
    simp only [wy, ← Nat.cast_sum]
    exact_mod_cast (crossEdgeCount_eq_sum_right H A B).symm
  have hsumYA : (∑ y ∈ Y, wy y) = (crossEdgeCount H A Y : ℚ) := by
    simp only [wy, ← Nat.cast_sum]
    exact_mod_cast (crossEdgeCount_eq_sum_right H A Y).symm
  rw [hsumX, hsumXY] at hAavg
  rw [hsumY, hsumYA] at hBavg
  have hsparseQ : (k : ℚ) * crossEdgeCount H X Y ≤ X.card * Y.card := by
    exact_mod_cast hSparse
  have hXpos : (0 : ℚ) < X.card := by exact_mod_cast (lt_of_lt_of_le htpos hX)
  have hYpos : (0 : ℚ) < Y.card := by exact_mod_cast (lt_of_lt_of_le htpos hY)
  have hAc : (A.card : ℚ) = t := by exact_mod_cast hAcard
  have hBc : (B.card : ℚ) = t := by exact_mod_cast hBcard
  have hfinalQ : (k : ℚ) * crossEdgeCount H A B ≤ A.card * B.card := by
    have h1 := mul_le_mul_of_nonneg_left hAavg (show (0 : ℚ) ≤ k * t by positivity)
    have h2 := mul_le_mul_of_nonneg_left hBavg
      (show (0 : ℚ) ≤ k * X.card by positivity)
    have h3 := mul_le_mul_of_nonneg_left hsparseQ
      (show (0 : ℚ) ≤ t * t by positivity)
    rw [hAc, hBc]
    have hchain :
        ((X.card : ℚ) * Y.card) * ((k : ℚ) * crossEdgeCount H A B) ≤
          ((X.card : ℚ) * Y.card) * ((t : ℚ) * t) := by
      calc
        ((X.card : ℚ) * Y.card) * ((k : ℚ) * crossEdgeCount H A B) =
            (k : ℚ) * X.card * (Y.card * crossEdgeCount H A B) := by ring
        _ ≤ (k : ℚ) * X.card * (t * crossEdgeCount H A Y) := h2
        _ = (k : ℚ) * t * (X.card * crossEdgeCount H A Y) := by ring
        _ ≤ (k : ℚ) * t * (t * crossEdgeCount H X Y) := h1
        _ = (t : ℚ) * t * (k * crossEdgeCount H X Y) := by ring
        _ ≤ (t : ℚ) * t * (X.card * Y.card) := h3
        _ = ((X.card : ℚ) * Y.card) * ((t : ℚ) * t) := by ring
    exact (mul_le_mul_iff_of_pos_left (mul_pos hXpos hYpos)).mp hchain
  exact_mod_cast hfinalQ

/-! ## A bad set produces a disjoint sparse pair -/

private lemma crossEdgeCount_mono {N : ℕ} (H : SimpleGraph (Fin N))
    {X X' Y Y' : Finset (Fin N)} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    crossEdgeCount H X Y ≤ crossEdgeCount H X' Y' := by
  classical
  exact Finset.card_le_card (H.interedges_mono hX hY)

private lemma mul_crossEdgeCount_eq_sum_singleton_left {N L : ℕ}
    (H : SimpleGraph (Fin N))
    (X Y : Finset (Fin N)) :
    L * crossEdgeCount H X Y =
      ∑ x ∈ X, L * crossEdgeCount H {x} Y := by
  classical
  rw [crossEdgeCount_eq_sum_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  rw [crossEdgeCount_eq_sum_left]
  simp

/-- If at least `s` vertices of `C` have fewer than a `1/L` fraction of
their possible neighbours in `W`, then (with a factor-two reserve in both
the density and the size of `W`) there is a disjoint equal `K`-sparse pair. -/
lemma sparse_pair_of_many_bad {N K L s : ℕ} (H : SimpleGraph (Fin N))
    (C W Bad : Finset (Fin N))
    (hBadC : Bad ⊆ C) (hsBad : s ≤ Bad.card) (hW : 2 * s ≤ W.card)
    (hKL : 2 * K ≤ L)
    (hbad : ∀ x ∈ Bad, L * crossEdgeCount H {x} W < W.card) :
    ∃ A B : Finset (Fin N), A ⊆ C ∧ B ⊆ W ∧ Disjoint A B ∧
      A.card = s ∧ B.card = s ∧
      K * crossEdgeCount H A B ≤ A.card * B.card := by
  classical
  by_cases hs0 : s = 0
  · subst s
    exact ⟨∅, ∅, by simp [crossEdgeCount]⟩
  obtain ⟨X, hXBad, hXcard⟩ := Finset.exists_subset_card_eq hsBad
  let Y := W \ X
  have hXY : Disjoint X Y := Finset.disjoint_sdiff
  have hYcard : Y.card = W.card - (W ∩ X).card := by
    simp [Y, Finset.card_sdiff, Finset.inter_comm]
  have hinter : (W ∩ X).card ≤ s := by
    rw [← hXcard]
    exact Finset.card_le_card Finset.inter_subset_right
  have hsY : s ≤ Y.card := by omega
  have hsumlt :
      ∑ x ∈ X, L * crossEdgeCount H {x} W <
        ∑ _x ∈ X, W.card := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (hbad i (hXBad hi)).le
    · obtain ⟨x, hx⟩ : X.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        have : s = 0 := by simpa [h] using hXcard.symm
        exact hs0 this
      exact ⟨x, hx, hbad x (hXBad hx)⟩
  have hcrosslt : L * crossEdgeCount H X W < s * W.card := by
    calc
      L * crossEdgeCount H X W =
          ∑ x ∈ X, L * crossEdgeCount H {x} W :=
        mul_crossEdgeCount_eq_sum_singleton_left H X W
      _ < ∑ _x ∈ X, W.card := hsumlt
      _ = s * W.card := by simp [hXcard]
  have hmono : crossEdgeCount H X Y ≤ crossEdgeCount H X W :=
    crossEdgeCount_mono H (Subset.rfl) Finset.sdiff_subset
  have hsparseXY : K * crossEdgeCount H X Y ≤ X.card * Y.card := by
    rw [hXcard, hYcard]
    have htwice :
        2 * (K * crossEdgeCount H X Y) < s * W.card := by
      calc
        2 * (K * crossEdgeCount H X Y) =
            (2 * K) * crossEdgeCount H X Y := by ring
        _ ≤ L * crossEdgeCount H X Y :=
          Nat.mul_le_mul_right _ hKL
        _ ≤ L * crossEdgeCount H X W :=
          Nat.mul_le_mul_left L hmono
        _ < s * W.card := hcrosslt
    have hroom : s * W.card ≤ 2 * (s * (W.card - (W ∩ X).card)) := by
      have hwcore : W.card ≤ 2 * (W.card - (W ∩ X).card) := by omega
      have := Nat.mul_le_mul_left s hwcore
      nlinarith
    omega
  obtain ⟨A, B, hAX, hBY, hAcard, hBcard, hsparse⟩ :=
    exists_equal_sparse_subsets H (t := s) (X := X) (Y := Y)
      (by simp [hXcard]) hsY hsparseXY
  exact ⟨A, B, hAX.trans (hXBad.trans hBadC), hBY.trans Finset.sdiff_subset,
    hXY.mono hAX hBY, hAcard, hBcard, hsparse⟩

/-! ## Greedy candidate sets -/

private def initialSegment {f : ℕ} (i : ℕ) : Finset (Fin f) :=
  Finset.univ.filter fun v ↦ v.val < i

private noncomputable def remainingNeighbors {f : ℕ} (F : SimpleGraph (Fin f))
    (i : ℕ) (v : Fin f) : Finset (Fin f) := by
  classical
  exact Finset.univ.filter fun u ↦ i ≤ u.val ∧ F.Adj u v

private noncomputable def candidates {f N : ℕ} (F : SimpleGraph (Fin f))
    (H : SimpleGraph (Fin N)) (U : Finset (Fin N))
    (φ : Fin f → Fin N) (i : ℕ) (v : Fin f) : Finset (Fin N) := by
  classical
  exact U.filter fun x ↦
    ∀ u ∈ initialSegment i, F.Adj u v → H.Adj (φ u) x

private lemma mem_candidates {f N : ℕ} (F : SimpleGraph (Fin f))
    (H : SimpleGraph (Fin N)) (U : Finset (Fin N))
    (φ : Fin f → Fin N) (i : ℕ) (v : Fin f) (x : Fin N) :
    x ∈ candidates F H U φ i v ↔
      x ∈ U ∧ ∀ u ∈ initialSegment i, F.Adj u v → H.Adj (φ u) x := by
  classical
  simp [candidates]

private noncomputable def neighborRestriction {N : ℕ} (H : SimpleGraph (Fin N))
    (x : Fin N) (C : Finset (Fin N)) : Finset (Fin N) := by
  classical
  exact C.filter fun y ↦ H.Adj x y

private def PartialCopy {f N : ℕ} (F : SimpleGraph (Fin f))
    (H : SimpleGraph (Fin N)) (U : Finset (Fin N))
    (φ : Fin f → Fin N) (i : ℕ) : Prop :=
  Set.InjOn φ (↑(initialSegment (f := f) i) : Set (Fin f)) ∧
    (∀ ⦃u v⦄, u ∈ initialSegment i → v ∈ initialSegment i →
      F.Adj u v → H.Adj (φ u) (φ v)) ∧
    ∀ v ∈ initialSegment i, φ v ∈ U

@[simp] private lemma mem_prefix {f i : ℕ} (v : Fin f) :
    v ∈ initialSegment i ↔ v.val < i := by
  simp [initialSegment]

@[simp] private lemma initialSegment_zero {f : ℕ} :
    initialSegment (f := f) 0 = ∅ := by
  ext v
  simp

private lemma initialSegment_succ {f i : ℕ} (hi : i < f) :
    initialSegment (f := f) (i + 1) =
      insert (⟨i, hi⟩ : Fin f) (initialSegment i) := by
  ext v
  simp only [mem_prefix, Finset.mem_insert]
  constructor
  · intro hv
    by_cases hvi : v.val = i
    · left
      exact Fin.ext hvi
    · right
      omega
  · rintro (rfl | hv)
    · simp
    · omega

@[simp] private lemma candidates_zero {f N : ℕ} (F : SimpleGraph (Fin f))
    (H : SimpleGraph (Fin N)) (U : Finset (Fin N)) (φ : Fin f → Fin N)
    (v : Fin f) :
    candidates F H U φ 0 v = U := by
  ext x
  simp [candidates]

private lemma candidates_succ {f N i : ℕ} (F : SimpleGraph (Fin f))
    [DecidableRel F.Adj]
    (H : SimpleGraph (Fin N)) (U : Finset (Fin N)) (φ : Fin f → Fin N)
    (hi : i < f) (x : Fin N) (v : Fin f) :
    candidates F H U (Function.update φ ⟨i, hi⟩ x) (i + 1) v =
      if F.Adj ⟨i, hi⟩ v then
        neighborRestriction H x (candidates F H U φ i v)
      else candidates F H U φ i v := by
  classical
  by_cases hiv : F.Adj (⟨i, hi⟩ : Fin f) v
  · simp only [hiv, if_true]
    ext y
    simp only [neighborRestriction, Finset.mem_filter, candidates,
      initialSegment_succ hi, Finset.mem_insert]
    constructor
    · rintro ⟨hyU, hall⟩
      refine ⟨⟨hyU, ?_⟩, ?_⟩
      · intro u hu huv
        have hne : u ≠ (⟨i, hi⟩ : Fin f) := by
          intro h
          have hval : u.val = i := by simpa using congrArg Fin.val h
          have huval := (mem_prefix (v := u)).mp hu
          omega
        simpa [Function.update, hne] using hall u (by simp [hu]) huv
      · have := hall (⟨i, hi⟩ : Fin f) (by simp) hiv
        simpa using this
    · rintro ⟨⟨hyU, hall⟩, hxy⟩
      refine ⟨hyU, ?_⟩
      intro u hu huv
      rcases hu with rfl | hu
      · simpa using hxy
      · have hne : u ≠ (⟨i, hi⟩ : Fin f) := by
          intro h
          have hval : u.val = i := by simpa using congrArg Fin.val h
          have huval := (mem_prefix (v := u)).mp hu
          omega
        simpa [Function.update, hne] using hall u hu huv
  · simp only [hiv, if_false]
    ext y
    simp only [candidates, initialSegment_succ hi, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hyU, hall⟩
      refine ⟨hyU, ?_⟩
      intro u hu huv
      have hne : u ≠ (⟨i, hi⟩ : Fin f) := by
        intro h
        have hval : u.val = i := by simpa using congrArg Fin.val h
        have huval := (mem_prefix (v := u)).mp hu
        omega
      simpa [Function.update, hne] using hall u (by simp [hu]) huv
    · rintro ⟨hyU, hall⟩
      refine ⟨hyU, ?_⟩
      intro u hu huv
      rcases hu with rfl | hu
      · exact (hiv huv).elim
      · have hne : u ≠ (⟨i, hi⟩ : Fin f) := by
          intro h
          have hval : u.val = i := by simpa using congrArg Fin.val h
          have huval := (mem_prefix (v := u)).mp hu
          omega
        simpa [Function.update, hne] using hall u hu huv

private lemma remainingNeighbors_succ {f i : ℕ} (F : SimpleGraph (Fin f))
    [DecidableRel F.Adj]
    (hi : i < f) (v : Fin f) (_hiv : i < v.val) :
    (remainingNeighbors F i v).card =
      (remainingNeighbors F (i + 1) v).card +
        (if F.Adj (⟨i, hi⟩ : Fin f) v then 1 else 0) := by
  classical
  let a : Fin f := ⟨i, hi⟩
  by_cases hadj : F.Adj a v
  · have heq : remainingNeighbors F i v =
        insert a (remainingNeighbors F (i + 1) v) := by
      ext u
      simp only [remainingNeighbors, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · rintro ⟨hiu, huv⟩
        by_cases hui : u.val = i
        · left
          exact Fin.ext hui
        · right
          exact ⟨by omega, huv⟩
      · rintro (rfl | ⟨hiu, huv⟩)
        · exact ⟨le_rfl, hadj⟩
        · exact ⟨by omega, huv⟩
    have hnot : a ∉ remainingNeighbors F (i + 1) v := by
      simp [remainingNeighbors, a]
    rw [heq, Finset.card_insert_of_notMem hnot]
    have hadj' : F.Adj (⟨i, hi⟩ : Fin f) v := by simpa [a] using hadj
    simp [hadj']
  · have heq' : remainingNeighbors F i v = remainingNeighbors F (i + 1) v := by
      ext u
      simp only [remainingNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hiu, huv⟩
        refine ⟨?_, huv⟩
        by_contra h
        have hui : u.val = i := by omega
        have : u = a := Fin.ext hui
        subst u
        exact hadj huv
      · rintro ⟨hiu, huv⟩
        exact ⟨by omega, huv⟩
    rw [heq']
    have hadj' : ¬F.Adj (⟨i, hi⟩ : Fin f) v := by simpa [a] using hadj
    simp [hadj']

private lemma remainingNeighbors_card_le_degree {f i : ℕ}
    (F : SimpleGraph (Fin f)) [DecidableRel F.Adj] (v : Fin f) :
    (remainingNeighbors F i v).card ≤ F.degree v := by
  rw [← F.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro u hu
  simp only [remainingNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  exact (F.mem_neighborFinset v u).mpr hu.2.symm

private lemma card_initialSegment {f i : ℕ} (hi : i ≤ f) :
    (initialSegment (f := f) i).card = i := by
  classical
  calc
    (initialSegment (f := f) i).card = (Finset.univ : Finset (Fin i)).card := by
      apply Finset.card_bij (fun v hv ↦ ⟨v.val, (mem_prefix v).mp hv⟩)
      · simp
      · intro a ha b hb hab
        have hv : a.val = b.val := congrArg (fun z : Fin i ↦ z.val) hab
        exact Fin.ext hv
      · intro b hb
        let v : Fin f := ⟨b.val, b.isLt.trans_le hi⟩
        refine ⟨v, ?_, Fin.ext rfl⟩
        exact (mem_prefix v).mpr b.isLt
    _ = i := Finset.card_fin i

-- The version of `badChoices` used below carries the current vertex explicitly,
-- avoiding any proof dependence in its definition.
private noncomputable def badChoicesAt {f N : ℕ} (F : SimpleGraph (Fin f))
    (H : SimpleGraph (Fin N)) (U : Finset (Fin N)) (φ : Fin f → Fin N)
    (i L : ℕ) (cur v : Fin f) : Finset (Fin N) := by
  classical
  let C := candidates F H U φ i v
  exact (candidates F H U φ i cur).filter fun x ↦
    L * crossEdgeCount H {x} C < C.card

private lemma mem_badChoicesAt {f N : ℕ} (F : SimpleGraph (Fin f))
    (H : SimpleGraph (Fin N)) (U : Finset (Fin N)) (φ : Fin f → Fin N)
    (i L : ℕ) (cur v : Fin f) (x : Fin N) :
    x ∈ badChoicesAt F H U φ i L cur v ↔
      x ∈ candidates F H U φ i cur ∧
        L * crossEdgeCount H {x} (candidates F H U φ i v) <
          (candidates F H U φ i v).card := by
  classical
  simp [badChoicesAt]

private def CandidateInvariant {f N : ℕ} (F : SimpleGraph (Fin f))
    (H : SimpleGraph (Fin N)) (U : Finset (Fin N))
    (L s i : ℕ) (φ : Fin f → Fin N) : Prop :=
  ∀ v : Fin f, i ≤ v.val →
    L ^ (remainingNeighbors F i v).card * s ≤ (candidates F H U φ i v).card

private lemma succ_le_pow {L k : ℕ} (hL : 2 ≤ L) : k + 1 ≤ L ^ k := by
  have hk : k < 2 ^ k := Nat.lt_two_pow_self
  have hp : 2 ^ k ≤ L ^ k := Nat.pow_le_pow_left hL k
  omega

private lemma cancel_candidate_factor {L r s c n : ℕ} (hL : 0 < L)
    (h₁ : L ^ (r + 1) * s ≤ c) (h₂ : c ≤ L * n) :
    L ^ r * s ≤ n := by
  apply Nat.le_of_mul_le_mul_left (c := L) (hc := hL)
  calc
    L * (L ^ r * s) = L ^ (r + 1) * s := by rw [pow_succ']; ring
    _ ≤ c := h₁
    _ ≤ L * n := h₂

private lemma candidates_subset {f N : ℕ} (F : SimpleGraph (Fin f))
    (H : SimpleGraph (Fin N)) (U : Finset (Fin N))
    (φ : Fin f → Fin N) (i : ℕ) (v : Fin f) :
    candidates F H U φ i v ⊆ U := by
  classical
  intro x hx
  exact (Finset.mem_filter.mp hx).1

private lemma crossEdgeCount_singleton_left {N : ℕ} (H : SimpleGraph (Fin N))
    (x : Fin N) (C : Finset (Fin N)) :
    crossEdgeCount H {x} C = (neighborRestriction H x C).card := by
  classical
  rw [crossEdgeCount_eq_sum_left]
  simp [neighborRestriction]

/-! ## The greedy bounded-degree embedding -/

/-- If no disjoint equal `K`-sparse pair occurs inside `U`, then every graph
of maximum degree at most `D` embeds, provided the candidate reservoir has the
standard `L^D` size.  This is the exact greedy engine behind the public dyadic
contrapositive below. -/
theorem isContained_of_no_sparse_pair {f N K L s D : ℕ}
    (F : SimpleGraph (Fin f)) [DecidableRel F.Adj] (H : SimpleGraph (Fin N))
    (U : Finset (Fin N))
    (hL : 2 ≤ L) (hKL : 2 * K ≤ L) (hfs : f ≤ s)
    (hdeg : F.maxDegree ≤ D) (hsize : L ^ D * s ≤ U.card)
    (hNoSparse : ∀ A B : Finset (Fin N), A ⊆ U → B ⊆ U → Disjoint A B →
      A.card = s → B.card = s →
      ¬ K * crossEdgeCount H A B ≤ A.card * B.card) :
    F ⊑ H.induce (↑U : Set (Fin N)) := by
  classical
  by_cases hf0 : f = 0
  · subst f
    exact SimpleGraph.IsContained.of_isEmpty
  have hspos : 0 < s := lt_of_lt_of_le (Nat.pos_of_ne_zero hf0) hfs
  have hUpos : 0 < U.card :=
    lt_of_lt_of_le (Nat.mul_pos (by positivity) hspos) hsize
  obtain ⟨u₀, hu₀⟩ := Finset.card_pos.mp hUpos
  have hbuild : ∀ i : ℕ, i ≤ f →
      ∃ φ : Fin f → Fin N,
        PartialCopy F H U φ i ∧ CandidateInvariant F H U L s i φ := by
    intro i hi
    induction i with
    | zero =>
        let φ : Fin f → Fin N := fun _ ↦ u₀
        refine ⟨φ, ?_, ?_⟩
        · constructor
          · intro a ha
            simp at ha
          · constructor
            · intro a b ha
              simp at ha
            · intro a ha
              simp at ha
        · intro v hv
          rw [candidates_zero]
          have hrdeg := remainingNeighbors_card_le_degree (i := 0) F v
          have hdv : F.degree v ≤ D := (F.degree_le_maxDegree v).trans hdeg
          have hpow : L ^ (remainingNeighbors F 0 v).card ≤ L ^ D :=
            Nat.pow_le_pow_right (by omega) (hrdeg.trans hdv)
          exact (Nat.mul_le_mul_right s hpow).trans hsize
    | succ i ih =>
        have hif : i < f := by omega
        obtain ⟨φ, hpartial, hinv⟩ := ih (by omega)
        let cur : Fin f := ⟨i, hif⟩
        let C := candidates F H U φ i cur
        let R := remainingNeighbors F i cur
        let Bad : Fin f → Finset (Fin N) := fun v ↦
          badChoicesAt F H U φ i L cur v
        have hBadlt : ∀ v ∈ R, (Bad v).card < s := by
          intro v hvR
          have hvdata : i ≤ v.val ∧ F.Adj v cur := by
            simpa [R, remainingNeighbors] using hvR
          have hvfuture : i < v.val := by
            rcases hvdata with ⟨hiv, hadj⟩
            by_contra h
            have hval : v.val = i := by omega
            have hvc : v = cur := Fin.ext hval
            subst v
            exact F.irrefl hadj
          have hCvInv := hinv v hvdata.1
          have hcurmem : cur ∈ remainingNeighbors F i v := by
            simp [remainingNeighbors, cur, hvdata.2.symm]
          have hrempos : 0 < (remainingNeighbors F i v).card :=
            Finset.card_pos.mpr ⟨cur, hcurmem⟩
          have hLpow : L ≤ L ^ (remainingNeighbors F i v).card := by
            have := Nat.pow_le_pow_right (by omega : 0 < L) hrempos
            simpa using this
          have hCvTwo : 2 * s ≤ (candidates F H U φ i v).card := by
            calc
              2 * s ≤ L * s := Nat.mul_le_mul_right s hL
              _ ≤ L ^ (remainingNeighbors F i v).card * s :=
                Nat.mul_le_mul_right s hLpow
              _ ≤ (candidates F H U φ i v).card := hCvInv
          by_contra hbadcard
          have hsBad : s ≤ (Bad v).card := by omega
          obtain ⟨A, B, hAC, hBCv, hAB, hAc, hBc, hsp⟩ :=
            sparse_pair_of_many_bad H C (candidates F H U φ i v) (Bad v)
              (by
                intro x hx
                exact (mem_badChoicesAt F H U φ i L cur v x).mp hx |>.1)
              hsBad hCvTwo hKL (by
                intro x hx
                exact (mem_badChoicesAt F H U φ i L cur v x).mp hx |>.2)
          exact hNoSparse A B
            (hAC.trans (candidates_subset F H U φ i cur))
            (hBCv.trans (candidates_subset F H U φ i v)) hAB hAc hBc hsp
        let Used := (initialSegment (f := f) i).image φ
        let Forbidden := Used ∪ R.biUnion Bad
        have hUsed : Used.card ≤ i := by
          calc
            Used.card ≤ (initialSegment (f := f) i).card := Finset.card_image_le
            _ = i := card_initialSegment (by omega)
        have hManyBad : (R.biUnion Bad).card ≤ R.card * (s - 1) := by
          calc
            (R.biUnion Bad).card ≤ ∑ v ∈ R, (Bad v).card :=
              Finset.card_biUnion_le
            _ ≤ ∑ _v ∈ R, (s - 1) := by
              apply Finset.sum_le_sum
              intro v hv
              have := hBadlt v hv
              omega
            _ = R.card * (s - 1) := by simp
        have hForbidden : Forbidden.card ≤ i + R.card * (s - 1) := by
          exact (Finset.card_union_le Used (R.biUnion Bad)).trans
            (Nat.add_le_add hUsed hManyBad)
        have hCInv : L ^ R.card * s ≤ C.card := by
          simpa [C, R] using hinv cur (by simp [cur])
        have hiS : i < s := hif.trans_le hfs
        have hsmall : i + R.card * (s - 1) < (R.card + 1) * s := by
          have h₁ : i < s := hiS
          have h₂ : R.card * (s - 1) ≤ R.card * s :=
            Nat.mul_le_mul_left R.card (Nat.sub_le s 1)
          nlinarith
        have hpow : R.card + 1 ≤ L ^ R.card := succ_le_pow hL
        have hForbidLt : Forbidden.card < C.card :=
          hForbidden.trans_lt <| hsmall.trans_le <|
            (Nat.mul_le_mul_right s hpow).trans hCInv
        have hnsub : ¬ C ⊆ Forbidden := by
          intro hsub
          exact (not_lt_of_ge (Finset.card_le_card hsub)) hForbidLt
        obtain ⟨x, hxC, hxForbidden⟩ := Finset.not_subset.mp hnsub
        have hxUsed : x ∉ Used := fun hx ↦ hxForbidden (Finset.mem_union_left _ hx)
        have hxBad : ∀ v ∈ R, x ∉ Bad v := by
          intro v hv hx
          apply hxForbidden
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hv, hx⟩)
        let φ' : Fin f → Fin N := Function.update φ cur x
        refine ⟨φ', ?_, ?_⟩
        · constructor
          · intro a ha b hb hab
            rw [initialSegment_succ hif] at ha hb
            simp only [Finset.coe_insert] at ha hb
            rcases ha with rfl | ha <;> rcases hb with rfl | hb
            · rfl
            · exfalso
              have hneB : b ≠ cur := by
                intro h
                subst b
                have := (mem_prefix cur).mp hb
                simp [cur] at this
              have hcurEq : (⟨i, hif⟩ : Fin f) = cur := rfl
              rw [hcurEq] at hab
              have heq : x = φ b := by
                simpa [φ', Function.update, hneB] using hab
              apply hxUsed
              apply Finset.mem_image.mpr
              refine ⟨b, hb, ?_⟩
              exact heq.symm
            · exfalso
              have hneA : a ≠ cur := by
                intro h
                subst a
                have := (mem_prefix cur).mp ha
                simp [cur] at this
              have hcurEq : (⟨i, hif⟩ : Fin f) = cur := rfl
              rw [hcurEq] at hab
              have heq : φ a = x := by
                simpa [φ', Function.update, hneA] using hab
              apply hxUsed
              apply Finset.mem_image.mpr
              refine ⟨a, ha, ?_⟩
              exact heq
            · have hneA : a ≠ cur := by
                intro h
                subst a
                have := (mem_prefix cur).mp ha
                simp [cur] at this
              have hneB : b ≠ cur := by
                intro h
                subst b
                have := (mem_prefix cur).mp hb
                simp [cur] at this
              have : φ a = φ b := by simpa [φ', Function.update, hneA, hneB] using hab
              exact hpartial.1 ha hb this
          · constructor
            · intro a b ha hb hab
              rw [initialSegment_succ hif] at ha hb
              simp only [Finset.mem_insert] at ha hb
              rcases ha with rfl | ha <;> rcases hb with rfl | hb
              · exact (F.irrefl hab).elim
              · have hxy : H.Adj (φ b) x := by
                  have hall := (mem_candidates F H U φ i cur x).mp hxC |>.2 b hb hab.symm
                  exact hall
                have hneB : b ≠ cur := by
                  intro h
                  subst b
                  have := (mem_prefix cur).mp hb
                  simp [cur] at this
                have hcurEq : (⟨i, hif⟩ : Fin f) = cur := rfl
                rw [hcurEq]
                simpa [φ', Function.update, hneB, H.adj_comm] using hxy
              · have hxy := (mem_candidates F H U φ i cur x).mp hxC |>.2 a ha hab
                have hneA : a ≠ cur := by
                  intro h
                  subst a
                  have := (mem_prefix cur).mp ha
                  simp [cur] at this
                have hcurEq : (⟨i, hif⟩ : Fin f) = cur := rfl
                rw [hcurEq]
                simpa [φ', Function.update, hneA] using hxy
              · have hneA : a ≠ cur := by
                  intro h
                  subst a
                  have := (mem_prefix cur).mp ha
                  simp [cur] at this
                have hneB : b ≠ cur := by
                  intro h
                  subst b
                  have := (mem_prefix cur).mp hb
                  simp [cur] at this
                simpa [φ', Function.update, hneA, hneB] using
                  hpartial.2.1 ha hb hab
            · intro v hv
              rw [initialSegment_succ hif] at hv
              simp only [Finset.mem_insert] at hv
              rcases hv with rfl | hv
              · have hxU := candidates_subset F H U φ i cur hxC
                simpa [φ', cur] using hxU
              · have hne : v ≠ cur := by
                  intro h
                  subst v
                  have := (mem_prefix cur).mp hv
                  simp [cur] at this
                simpa [φ', Function.update, hne] using hpartial.2.2 v hv
        · intro v hv
          have hold := hinv v (by omega)
          by_cases hadj : F.Adj cur v
          · have hvR : v ∈ R := by
              simp [R, remainingNeighbors, cur, hadj.symm]
              omega
            have hgood :
                (candidates F H U φ i v).card ≤
                  L * crossEdgeCount H {x} (candidates F H U φ i v) := by
              have hnot := hxBad v hvR
              have hnlt : ¬ L * crossEdgeCount H {x}
                    (candidates F H U φ i v) <
                  (candidates F H U φ i v).card := by
                intro hlt
                apply hnot
                exact (mem_badChoicesAt F H U φ i L cur v x).mpr ⟨hxC, hlt⟩
              omega
            rw [crossEdgeCount_singleton_left] at hgood
            have hrem := remainingNeighbors_succ F hif v (by omega)
            have hcand := candidates_succ F H U φ hif x v
            have hadj' : F.Adj (⟨i, hif⟩ : Fin f) v := by simpa [cur] using hadj
            rw [if_pos hadj'] at hcand
            change L ^ (remainingNeighbors F (i + 1) v).card * s ≤
              (candidates F H U (Function.update φ (⟨i, hif⟩ : Fin f) x)
                (i + 1) v).card
            rw [hcand]
            have hpowold :
                L ^ ((remainingNeighbors F (i + 1) v).card + 1) * s ≤
                  (candidates F H U φ i v).card := by
              rw [if_pos hadj'] at hrem
              rw [← hrem]
              exact hold
            exact cancel_candidate_factor (by omega) hpowold hgood
          · have hrem := remainingNeighbors_succ F hif v (by omega)
            have hcand := candidates_succ F H U φ hif x v
            have hadj' : ¬F.Adj (⟨i, hif⟩ : Fin f) v := by simpa [cur] using hadj
            rw [if_neg hadj'] at hcand
            rw [if_neg hadj'] at hrem
            rw [hrem] at hold
            simpa [φ', cur, hcand] using hold
  obtain ⟨φ, hpartial, _hinv⟩ := hbuild f le_rfl
  let ψ : Fin f → {x // x ∈ (↑U : Set (Fin N))} := fun v ↦
    ⟨φ v, hpartial.2.2 v ((mem_prefix v).mpr v.isLt)⟩
  refine ⟨⟨{ toFun := ψ, map_rel' := ?_ }, ?_⟩⟩
  · intro a b hab
    simpa [ψ, SimpleGraph.induce] using hpartial.2.1
      ((mem_prefix a).mpr a.isLt) ((mem_prefix b).mpr b.isLt) hab
  · intro a b hab
    apply hpartial.1
    · exact (mem_prefix a).mpr a.isLt
    · exact (mem_prefix b).mpr b.isLt
    · exact Subtype.ext_iff.mp hab

/-! ## Rounded dyadic sparse-pair contrapositive -/

/-- Rounded form of Sudakov's bounded-degree lemma.  If the induced graph on
`U` is `F`-free, then `U` contains disjoint equal blocks of the exact floor
size `|U| / 2^((Q+5)D)` and ordered cross-density at most `2^(-(Q+3))`.

The hypotheses `15 ≤ Q` and `1 ≤ D` match the later sparsification ledger;
the greedy proof itself only needs their much weaker positivity consequences.
-/
theorem exists_disjoint_pairSparse_of_not_isContained_induce
    {f N Q D : ℕ} (F : SimpleGraph (Fin f)) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin N)) (U : Finset (Fin N))
    (_hQ : 15 ≤ Q) (_hD : 1 ≤ D) (hdeg : F.maxDegree ≤ D)
    (hlarge : f * 2 ^ ((Q + 5) * D) ≤ U.card)
    (hfree : ¬ F ⊑ H.induce (↑U : Set (Fin N))) :
    ∃ A B : Finset (Fin N),
      A ⊆ U ∧ B ⊆ U ∧ Disjoint A B ∧
      A.card = U.card / 2 ^ ((Q + 5) * D) ∧
      B.card = U.card / 2 ^ ((Q + 5) * D) ∧
      PairSparse (Q + 3) H A B := by
  classical
  let P := 2 ^ ((Q + 5) * D)
  let K := 2 ^ (Q + 3)
  let L := 2 ^ (Q + 4)
  let s := U.card / P
  have hP : 0 < P := by positivity
  have hL : 2 ≤ L := by
    dsimp [L]
    exact (show 2 ^ 1 ≤ 2 ^ (Q + 4) by
      apply Nat.pow_le_pow_right (by norm_num)
      omega)
  have hKL : 2 * K ≤ L := by
    apply le_of_eq
    dsimp [K, L]
    conv_rhs => rw [show Q + 4 = (Q + 3) + 1 by omega, pow_succ]
    ring
  have hfs : f ≤ s := by
    apply (Nat.le_div_iff_mul_le hP).2
    simpa [P] using hlarge
  have hpow : L ^ D ≤ P := by
    dsimp [L, P]
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    exact Nat.mul_le_mul_right D (by omega)
  have hsize : L ^ D * s ≤ U.card := by
    calc
      L ^ D * s ≤ P * s := Nat.mul_le_mul_right s hpow
      _ ≤ U.card := by simpa [s] using Nat.mul_div_le U.card P
  by_contra hpair
  apply hfree
  apply isContained_of_no_sparse_pair F H U hL hKL hfs hdeg hsize
  intro A B hAU hBU hAB hAc hBc hsparse
  apply hpair
  refine ⟨A, B, hAU, hBU, hAB, ?_, ?_, ?_⟩
  · simpa [s, P] using hAc
  · simpa [s, P] using hBc
  · simpa [PairSparse, K] using hsparse

/-- Ambient freeness implies the induced-freeness hypothesis of the rounded
bounded-degree sparse-pair lemma. -/
theorem exists_disjoint_pairSparse_of_not_isContained
    {f N Q D : ℕ} (F : SimpleGraph (Fin f)) [DecidableRel F.Adj]
    (H : SimpleGraph (Fin N)) (U : Finset (Fin N))
    (hQ : 15 ≤ Q) (hD : 1 ≤ D) (hdeg : F.maxDegree ≤ D)
    (hlarge : f * 2 ^ ((Q + 5) * D) ≤ U.card)
    (hfree : ¬ F ⊑ H) :
    ∃ A B : Finset (Fin N),
      A ⊆ U ∧ B ⊆ U ∧ Disjoint A B ∧
      A.card = U.card / 2 ^ ((Q + 5) * D) ∧
      B.card = U.card / 2 ^ ((Q + 5) * D) ∧
      PairSparse (Q + 3) H A B := by
  apply exists_disjoint_pairSparse_of_not_isContained_induce F H U hQ hD hdeg hlarge
  intro hcopy
  exact hfree (hcopy.trans (SimpleGraph.Embedding.induce (↑U : Set (Fin N))).isContained)

end Erdos546
