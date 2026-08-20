/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Defs

/-!
# Finite greedy selection lemmas

This file collects the elementary distinct-representative arguments used when building
alternating paths.  The hypotheses here are deliberately stronger than Hall's condition:
every candidate set has enough elements for the choices that remain.  This is exactly the
form in which the common-neighbour estimates in the proof of Erdős Problem 518 occur.
-/

namespace Erdos518

universe u v

variable {A : Type u} {B : Type v}

/-- `xs` is an ordered system of representatives for the ordered list `Cs` of candidate
sets. -/
def IsRepresentativeList (Cs : List (Finset A)) (xs : List A) : Prop :=
  List.Forall₂ (fun C x ↦ x ∈ C) Cs xs

lemma IsRepresentativeList.length_eq {Cs : List (Finset A)} {xs : List A}
    (h : IsRepresentativeList Cs xs) : Cs.length = xs.length :=
  List.Forall₂.length_eq h

@[simp] lemma isRepresentativeList_nil :
    IsRepresentativeList ([] : List (Finset A)) ([] : List A) :=
  .nil

@[simp] lemma isRepresentativeList_cons {C : Finset A} {Cs : List (Finset A)}
    {x : A} {xs : List A} :
    IsRepresentativeList (C :: Cs) (x :: xs) ↔ x ∈ C ∧ IsRepresentativeList Cs xs := by
  simp [IsRepresentativeList]

/-- Greedy distinct representatives under the positional "remaining demand" bound.

At position `i`, there are `Cs.length - i` representatives still to be chosen (including
the current one).  The proof chooses from the end of the list towards the beginning. -/
theorem exists_nodup_representativeList_of_remaining :
    ∀ (Cs : List (Finset A)),
      (∀ i : Fin Cs.length, Cs.length - i.1 ≤ (Cs.get i).card) →
        ∃ xs : List A, xs.Nodup ∧ IsRepresentativeList Cs xs
  | [], _ => ⟨[], by simp, .nil⟩
  | C :: Cs, hcard => by
      classical
      have htail : ∀ i : Fin Cs.length,
          Cs.length - i.1 ≤ (Cs.get i).card := by
        intro i
        have h := hcard i.succ
        simpa using h
      obtain ⟨xs, hxs, hrep⟩ :=
        exists_nodup_representativeList_of_remaining Cs htail
      have hlen : xs.length = Cs.length := hrep.length_eq.symm
      have hC : Cs.length + 1 ≤ C.card := by
        have h := hcard ⟨0, by simp⟩
        simpa using h
      have hsmall : xs.toFinset.card < C.card := by
        rw [List.toFinset_card_of_nodup hxs, hlen]
        omega
      have hnsub : ¬ C ⊆ xs.toFinset := by
        intro hsub
        have := Finset.card_le_card hsub
        omega
      obtain ⟨x, hxC, hxxs⟩ := Finset.not_subset.mp hnsub
      refine ⟨x :: xs, ?_, ?_⟩
      · exact List.nodup_cons.mpr ⟨by simpa using hxxs, hxs⟩
      · exact .cons hxC hrep

/-- Uniform-cardinality form of greedy selection for an ordered family. -/
theorem exists_nodup_representativeList (Cs : List (Finset A))
    (hcard : ∀ C ∈ Cs, Cs.length ≤ C.card) :
    ∃ xs : List A, xs.Nodup ∧ IsRepresentativeList Cs xs := by
  apply exists_nodup_representativeList_of_remaining Cs
  intro i
  exact (Nat.sub_le _ _).trans (hcard _ (Cs.get_mem i))

/-- Uniform-cardinality form for a family indexed by `Fin n`. -/
theorem exists_injective_representatives_fin {n : ℕ} (C : Fin n → Finset A)
    (hcard : ∀ i, n ≤ (C i).card) :
    ∃ f : Fin n → A, Function.Injective f ∧ ∀ i, f i ∈ C i := by
  classical
  let Cs : List (Finset A) := List.ofFn C
  have hCs : ∀ D ∈ Cs, Cs.length ≤ D.card := by
    intro D hD
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hD
    simpa [Cs] using hcard i
  obtain ⟨xs, hxs, hrep⟩ := exists_nodup_representativeList Cs hCs
  have hlen : xs.length = n := by
    rw [← hrep.length_eq]
    simp [Cs]
  let f : Fin n → A := fun i ↦ xs.get ⟨i.1, by simpa [hlen] using i.2⟩
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    let i' : Fin xs.length := ⟨i.1, by simpa [hlen] using i.2⟩
    let j' : Fin xs.length := ⟨j.1, by simpa [hlen] using j.2⟩
    have hij' : i' = j' := hxs.get_inj_iff.mp (by simpa [f, i', j'] using hij)
    have hval : i'.val = j'.val := congrArg (fun k : Fin xs.length ↦ k.val) hij'
    exact Fin.ext hval
  · intro i
    have hi := List.Forall₂.get hrep (i := i.1) (by simp [Cs])
      (by simpa [hlen] using i.2)
    simpa [Cs, f] using hi

/-- A finite family indexed by an arbitrary finset has distinct representatives when every
candidate set has size at least the number of indices. -/
theorem exists_injective_representatives_on {I : Type u} (s : Finset I)
    (C : I → Finset A) (hcard : ∀ i ∈ s, s.card ≤ (C i).card) :
    ∃ f : s → A, Function.Injective f ∧ ∀ i : s, f i ∈ C i.1 := by
  classical
  let e : Fin s.card ≃ s := s.equivFin.symm
  obtain ⟨g, hg, hmem⟩ := exists_injective_representatives_fin
    (fun i ↦ C (e i)) (fun i ↦ hcard (e i) (e i).property)
  let f : s → A := fun i ↦ g (e.symm i)
  refine ⟨f, ?_, ?_⟩
  · exact hg.comp e.symm.injective
  · intro i
    simpa [f] using hmem (e.symm i)

/-- Indexed one-endpoint version of the sharp greedy argument. -/
theorem exists_injective_common_and_endpoint_fin {n : ℕ}
    (common : Fin n → Finset A) (endpoint : Finset A)
    (hcommon : ∀ i, n ≤ (common i).card) (hendpoint : n + 1 ≤ endpoint.card) :
    ∃ f : Fin n → A, ∃ z : A,
      Function.Injective f ∧ (∀ i, f i ∈ common i) ∧ z ∈ endpoint ∧ ∀ i, z ≠ f i := by
  classical
  obtain ⟨f, hf, hfmem⟩ := exists_injective_representatives_fin common hcommon
  let used : Finset A := Finset.univ.image f
  have hused : used.card = n := by
    change (Finset.univ.image f).card = n
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hnsub : ¬ endpoint ⊆ used := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [hused] at hle
    omega
  obtain ⟨z, hzE, hzused⟩ := Finset.not_subset.mp hnsub
  refine ⟨f, z, hf, hfmem, hzE, ?_⟩
  intro i hzi
  apply hzused
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hzi.symm⟩

/-- Indexed two-endpoint version.  The two endpoint representatives are distinct from one
another and from all common-set representatives. -/
theorem exists_injective_endpoints_and_common_fin {n : ℕ}
    (left right : Finset A) (common : Fin n → Finset A)
    (hcommon : ∀ i, n ≤ (common i).card)
    (hleft : n + 2 ≤ left.card) (hright : n + 2 ≤ right.card) :
    ∃ x₀ : A, ∃ f : Fin n → A, ∃ x₁ : A,
      Function.Injective f ∧ (∀ i, f i ∈ common i) ∧ x₀ ∈ left ∧ x₁ ∈ right ∧
        (∀ i, x₀ ≠ f i) ∧ (∀ i, x₁ ≠ f i) ∧ x₀ ≠ x₁ := by
  classical
  obtain ⟨f, hf, hfmem⟩ := exists_injective_representatives_fin common hcommon
  let used : Finset A := Finset.univ.image f
  have hused : used.card = n := by
    change (Finset.univ.image f).card = n
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hnsubLeft : ¬ left ⊆ used := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [hused] at hle
    omega
  obtain ⟨x₀, hx₀L, hx₀used⟩ := Finset.not_subset.mp hnsubLeft
  have husedInsert : (insert x₀ used).card = n + 1 := by
    rw [Finset.card_insert_of_notMem hx₀used, hused]
  have hnsubRight : ¬ right ⊆ insert x₀ used := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [husedInsert] at hle
    omega
  obtain ⟨x₁, hx₁R, hx₁used⟩ := Finset.not_subset.mp hnsubRight
  refine ⟨x₀, f, x₁, hf, hfmem, hx₀L, hx₁R, ?_, ?_, ?_⟩
  · intro i hxi
    apply hx₀used
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hxi.symm⟩
  · intro i hxi
    apply hx₁used
    simp only [Finset.mem_insert]
    exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hxi.symm⟩)
  · intro h
    apply hx₁used
    exact Finset.mem_insert.mpr (Or.inl h.symm)

/-- Select representatives for a list of common-neighbour sets, and then a further distinct
representative from an endpoint set.  Notice the sharp asymmetric bounds: `k` common sets
need size `k`, whereas the endpoint set needs size `k + 1`. -/
theorem exists_nodup_common_and_endpoint (common : List (Finset A)) (endpoint : Finset A)
    (hcommon : ∀ C ∈ common, common.length ≤ C.card)
    (hendpoint : common.length + 1 ≤ endpoint.card) :
    ∃ xs : List A, ∃ z : A,
      (xs ++ [z]).Nodup ∧ IsRepresentativeList common xs ∧ z ∈ endpoint := by
  classical
  obtain ⟨xs, hxs, hrep⟩ := exists_nodup_representativeList common hcommon
  have hlen : xs.length = common.length := hrep.length_eq.symm
  have hsmall : xs.toFinset.card < endpoint.card := by
    rw [List.toFinset_card_of_nodup hxs, hlen]
    omega
  have hnsub : ¬ endpoint ⊆ xs.toFinset := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨z, hzE, hzxs⟩ := Finset.not_subset.mp hnsub
  refine ⟨xs, z, ?_, hrep, hzE⟩
  exact hxs.append (by simp) (List.disjoint_singleton.mpr (by simpa using hzxs))

/-- Two-endpoint version.  This is the selection pattern for a path
`x₀,y₀,x₁,…,yₖ,xₖ₊₁`: first select the internal common neighbours, then the
two endpoints. -/
theorem exists_nodup_endpoints_and_common (left right : Finset A)
    (common : List (Finset A))
    (hcommon : ∀ C ∈ common, common.length ≤ C.card)
    (hleft : common.length + 2 ≤ left.card)
    (hright : common.length + 2 ≤ right.card) :
    ∃ x₀ : A, ∃ xs : List A, ∃ x₁ : A,
      (x₀ :: xs ++ [x₁]).Nodup ∧ x₀ ∈ left ∧
        IsRepresentativeList common xs ∧ x₁ ∈ right := by
  classical
  obtain ⟨xs, hxs, hrep⟩ := exists_nodup_representativeList common hcommon
  have hlen : xs.length = common.length := hrep.length_eq.symm
  have hsmallLeft : xs.toFinset.card < left.card := by
    rw [List.toFinset_card_of_nodup hxs, hlen]
    omega
  have hnsubLeft : ¬ left ⊆ xs.toFinset := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨x₀, hx₀L, hx₀xs⟩ := Finset.not_subset.mp hnsubLeft
  have hused : (x₀ :: xs).toFinset.card = common.length + 1 := by
    simp only [List.toFinset_cons]
    rw [Finset.card_insert_of_notMem hx₀xs, List.toFinset_card_of_nodup hxs, hlen]
  have hnsubRight : ¬ right ⊆ (x₀ :: xs).toFinset := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [hused] at hle
    omega
  obtain ⟨x₁, hx₁R, hx₁used⟩ := Finset.not_subset.mp hnsubRight
  refine ⟨x₀, xs, x₁, ?_, hx₀L, hrep, hx₁R⟩
  have hprefix : (x₀ :: xs).Nodup :=
    List.nodup_cons.mpr ⟨by simpa using hx₀xs, hxs⟩
  exact hprefix.append (by simp)
    (List.disjoint_singleton.mpr (by simpa using hx₁used))

/-- Candidate sets for the internal vertices of an alternating path through `ys`: the
entries are the intersections of the candidate sets belonging to consecutive vertices. -/
def sequentialCommonCandidates [DecidableEq A] (N : B → Finset A) :
    List B → List (Finset A)
  | [] => []
  | [_] => []
  | y :: y' :: ys => (N y ∩ N y') :: sequentialCommonCandidates N (y' :: ys)

@[simp] lemma sequentialCommonCandidates_nil [DecidableEq A] (N : B → Finset A) :
    sequentialCommonCandidates N [] = [] := rfl

@[simp] lemma sequentialCommonCandidates_singleton [DecidableEq A]
    (N : B → Finset A) (y : B) :
    sequentialCommonCandidates N [y] = [] := rfl

@[simp] lemma sequentialCommonCandidates_cons_cons [DecidableEq A] (N : B → Finset A)
    (y y' : B) (ys : List B) :
    sequentialCommonCandidates N (y :: y' :: ys) =
      (N y ∩ N y') :: sequentialCommonCandidates N (y' :: ys) := rfl

lemma length_sequentialCommonCandidates [DecidableEq A] (N : B → Finset A) (ys : List B) :
    (sequentialCommonCandidates N ys).length = ys.length - 1 := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
      cases ys with
      | nil => simp
      | cons y' ys =>
          simp only [sequentialCommonCandidates_cons_cons, List.length_cons]
          simp only [List.length_cons] at ih
          rw [ih]
          omega

/-- Sequential one-endpoint specialization.  It gives pairwise distinct internal common
neighbours and one final endpoint representative. -/
theorem exists_nodup_sequential_common_and_endpoint [DecidableEq A] (N : B → Finset A)
    (ys : List B) (endpoint : Finset A)
    (hcommon : ∀ C ∈ sequentialCommonCandidates N ys,
      (sequentialCommonCandidates N ys).length ≤ C.card)
    (hendpoint : (sequentialCommonCandidates N ys).length + 1 ≤ endpoint.card) :
    ∃ xs : List A, ∃ z : A,
      (xs ++ [z]).Nodup ∧
        IsRepresentativeList (sequentialCommonCandidates N ys) xs ∧ z ∈ endpoint :=
  exists_nodup_common_and_endpoint _ _ hcommon hendpoint

/-- Sequential two-endpoint specialization.  The result directly supplies all `A`-vertices
needed to alternate through the ordered list `ys`. -/
theorem exists_nodup_sequential_endpoints_and_common [DecidableEq A] (N : B → Finset A)
    (ys : List B) (left right : Finset A)
    (hcommon : ∀ C ∈ sequentialCommonCandidates N ys,
      (sequentialCommonCandidates N ys).length ≤ C.card)
    (hleft : (sequentialCommonCandidates N ys).length + 2 ≤ left.card)
    (hright : (sequentialCommonCandidates N ys).length + 2 ≤ right.card) :
    ∃ x₀ : A, ∃ xs : List A, ∃ x₁ : A,
      (x₀ :: xs ++ [x₁]).Nodup ∧ x₀ ∈ left ∧
        IsRepresentativeList (sequentialCommonCandidates N ys) xs ∧ x₁ ∈ right :=
  exists_nodup_endpoints_and_common _ _ _ hcommon hleft hright

/-! ## Splitting a list into prescribed blocks -/

/-- If the prescribed block sizes sum to the length of a list, `splitLengths` is an exact
ordered partition with precisely those sizes. -/
theorem splitLengths_exact (l : List A) (sizes : List ℕ) (hsum : sizes.sum = l.length) :
    let blocks := sizes.splitLengths l
    blocks.length = sizes.length ∧ blocks.flatten = l ∧ blocks.map List.length = sizes := by
  dsimp only
  refine ⟨List.length_splitLengths l sizes, ?_, ?_⟩
  · exact List.flatten_splitLengths l sizes (by omega)
  · exact List.map_splitLengths_length l sizes (by omega)

/-- Splitting a duplicate-free list into prescribed blocks gives duplicate-free, pairwise
disjoint blocks. -/
theorem splitLengths_nodup_pairwise_disjoint (l : List A) (sizes : List ℕ)
    (hsum : sizes.sum = l.length) (hl : l.Nodup) :
    (∀ block ∈ sizes.splitLengths l, block.Nodup) ∧
      (sizes.splitLengths l).Pairwise List.Disjoint := by
  apply List.nodup_flatten.mp
  rw [List.flatten_splitLengths l sizes (by omega)]
  exact hl

end Erdos518
