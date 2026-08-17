/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos877.Core

/-!
# Elementary supersaturation for Schur triples

This file develops the finite counting lemma used by the enumeration
argument.  We count triples with two distinct summands; this is the
3-uniform part of the Schur hypergraph.
-/

open Finset

namespace Erdos877
namespace Enumeration

/-- Unordered representations `x + y = z` in `A`, oriented by `x < y`. -/
noncomputable def pairsAt (A : Finset ℕ) (z : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun p ↦ p.1 < p.2 ∧ p.1 + p.2 = z

/-- All distinct-summand Schur triples, represented by their ordered-smallest
two entries. -/
noncomputable def schurPairs (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun p ↦ p.1 < p.2 ∧ p.1 + p.2 ∈ A

@[simp] theorem mem_pairsAt {A : Finset ℕ} {z : ℕ} {p : ℕ × ℕ} :
    p ∈ pairsAt A z ↔ p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2 ∧ p.1 + p.2 = z := by
  classical
  simp [pairsAt, and_assoc]

@[simp] theorem mem_schurPairs {A : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ schurPairs A ↔
      p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2 ∧ p.1 + p.2 ∈ A := by
  classical
  simp [schurPairs, and_assoc]

theorem pairsAt_subset_schurPairs {A : Finset ℕ} {z : ℕ} (hz : z ∈ A) :
    pairsAt A z ⊆ schurPairs A := by
  intro p hp
  rw [mem_pairsAt] at hp
  exact mem_schurPairs.mpr ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2 ▸ hz⟩

theorem pairsAt_disjoint {A : Finset ℕ} {z w : ℕ} (hzw : z ≠ w) :
    Disjoint (pairsAt A z) (pairsAt A w) := by
  rw [Finset.disjoint_left]
  intro p hpz hpw
  exact hzw ((mem_pairsAt.mp hpz).2.2.2.symm.trans (mem_pairsAt.mp hpw).2.2.2)

/-- Entries of `A` strictly below `z`. -/
noncomputable def below (A : Finset ℕ) (z : ℕ) : Finset ℕ :=
  A.filter (fun x ↦ x < z)

/-- Reflection in `z/2` of the entries of `A` below `z`. -/
noncomputable def reflectedBelow (A : Finset ℕ) (z : ℕ) : Finset ℕ :=
  (below A z).image (fun x ↦ z - x)

@[simp] theorem mem_below {A : Finset ℕ} {z x : ℕ} :
    x ∈ below A z ↔ x ∈ A ∧ x < z := by
  classical
  simp [below]

theorem card_reflectedBelow (A : Finset ℕ) (z : ℕ) :
    (reflectedBelow A z).card = (below A z).card := by
  classical
  rw [reflectedBelow, Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  have hxz := (mem_below.mp hx).2.le
  have hyz := (mem_below.mp hy).2.le
  have hcancel : (z - y) + x = (z - y) + y := by
    calc
      (z - y) + x = (z - x) + x :=
        congrArg (fun t ↦ t + x) hxy.symm
      _ = z := Nat.sub_add_cancel hxz
      _ = (z - y) + y := (Nat.sub_add_cancel hyz).symm
  exact Nat.add_left_cancel hcancel

theorem below_subset_range_succ (A : Finset ℕ) (z : ℕ) :
    below A z ⊆ Finset.range (z + 1) := by
  intro x hx
  have hxz : x < z := (mem_below.mp hx).2
  exact Finset.mem_range.mpr (by omega : x < z + 1)

theorem reflectedBelow_subset_range_succ (A : Finset ℕ) (z : ℕ) :
    reflectedBelow A z ⊆ Finset.range (z + 1) := by
  classical
  intro x hx
  rw [reflectedBelow, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact Finset.mem_range.mpr (by omega : z - y < z + 1)

/-- The intersection of a prefix with its reflection has the usual
inclusion--exclusion lower bound. -/
theorem two_mul_card_below_le_add_inter (A : Finset ℕ) (z : ℕ) :
    2 * (below A z).card ≤
      (z + 1) + (below A z ∩ reflectedBelow A z).card := by
  classical
  have hunion : (below A z ∪ reflectedBelow A z).card ≤ z + 1 := by
    simpa using Finset.card_le_card
      (Finset.union_subset (below_subset_range_succ A z)
        (reflectedBelow_subset_range_succ A z))
  have hinc := Finset.card_union_add_card_inter (below A z) (reflectedBelow A z)
  rw [card_reflectedBelow] at hinc
  omega

/-- Endpoints occurring in a family of pairs. -/
noncomputable def pairEndpoints (P : Finset (ℕ × ℕ)) : Finset ℕ :=
  P.biUnion fun p ↦ {p.1, p.2}

theorem card_pairEndpoints_le (P : Finset (ℕ × ℕ)) :
    (pairEndpoints P).card ≤ 2 * P.card := by
  classical
  calc
    (pairEndpoints P).card ≤ ∑ p ∈ P, ({p.1, p.2} : Finset ℕ).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact (Finset.card_insert_le _ _).trans (by simp)
    _ = 2 * P.card := by simp [Nat.mul_comm]

/-- Every reflected-prefix point other than a possible midpoint is an
endpoint of one of the oriented representations of `z`. -/
theorem inter_subset_endpoints_union_midpoint (A : Finset ℕ) (z : ℕ) :
    below A z ∩ reflectedBelow A z ⊆
      pairEndpoints (pairsAt A z) ∪ {z / 2} := by
  classical
  intro x hx
  obtain ⟨hxA, hxz⟩ := mem_below.mp (Finset.mem_inter.mp hx).1
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).2
  have hydata := mem_below.mp hy
  by_cases hxy : x = y
  · rw [Finset.mem_union, Finset.mem_singleton]
    right
    subst x
    have : z = y + y := by omega
    omega
  · rw [Finset.mem_union]
    left
    rw [pairEndpoints, Finset.mem_biUnion]
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · refine ⟨(x, y), mem_pairsAt.mpr ⟨hxA, hydata.1, hlt, ?_⟩, by simp⟩
      omega
    · refine ⟨(y, x), mem_pairsAt.mpr ⟨hydata.1, hxA, hgt, ?_⟩, by simp⟩
      omega

/-- The elementary reflection estimate at a fixed target `z`. -/
theorem two_mul_card_below_le_add_pairsAt (A : Finset ℕ) (z : ℕ) :
    2 * (below A z).card ≤ (z + 1) + (2 * (pairsAt A z).card + 1) := by
  classical
  have hinter : (below A z ∩ reflectedBelow A z).card ≤
      2 * (pairsAt A z).card + 1 := by
    calc
      _ ≤ (pairEndpoints (pairsAt A z) ∪ {z / 2}).card :=
        Finset.card_le_card (inter_subset_endpoints_union_midpoint A z)
      _ ≤ (pairEndpoints (pairsAt A z)).card + ({z / 2} : Finset ℕ).card :=
        Finset.card_union_le _ _
      _ ≤ 2 * (pairsAt A z).card + 1 := by
        simpa using Nat.add_le_add (card_pairEndpoints_le (pairsAt A z))
          (le_refl 1)
  exact (two_mul_card_below_le_add_inter A z).trans
    (Nat.add_le_add_left hinter (z + 1))

/-! ## Passing from one target to a dense set -/

/-- A strictly increasing list of naturals rises by at least the increase of
its index. -/
theorem sortedLT_getElem_add_le {L : List ℕ} (hL : L.Pairwise (· < ·))
    {i j : ℕ} (hi : i < L.length) (hj : j < L.length) (hij : i ≤ j) :
    j - i + L[i] ≤ L[j] := by
  have hstep : ∀ k : ℕ, ∀ hk : i + k < L.length,
      k + L[i] ≤ L[i + k] := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : i + k < L.length := by omega
        have hlt : L[i + k] < L[i + k + 1] := by
          exact (List.pairwise_iff_getElem.mp hL) (i + k) (i + k + 1)
            hk' (by omega) (by omega)
        have hind := ih hk'
        have hnext : k + 1 + L[i] ≤ L[i + k + 1] := by omega
        simpa [Nat.add_assoc] using hnext
  have hjEq : i + (j - i) = j := Nat.add_sub_of_le hij
  simpa [hjEq] using hstep (j - i) (by simpa [hjEq] using hj)

/-- The first `i` entries of the sorted enumeration of `A` all belong to the
strict prefix below entry `i`. -/
theorem sort_take_toFinset_subset_below (A : Finset ℕ) {i : ℕ}
    (hi : i < A.card) :
    ((A.sort (· ≤ ·)).take i).toFinset ⊆
      below A ((A.sort (· ≤ ·))[i]'(by simpa using hi)) := by
  classical
  let L := A.sort (· ≤ ·)
  have hlen : L.length = A.card := by simp [L]
  have hsorted : L.Pairwise (· < ·) := (Finset.sortedLT_sort A).pairwise
  intro x hx
  have hxTake : x ∈ L.take i := by simpa [L] using hx
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hxTake
  have hiL : i < L.length := by simpa [hlen] using hi
  have htakeLen : (L.take i).length = i := by simp [hiL.le]
  have hji : j < i := by simpa [htakeLen] using hj
  have hjL : j < L.length := hji.trans hiL
  have hxL : x = L[j] := by
    simpa [List.getElem_take, hji] using hjx.symm
  rw [mem_below]
  refine ⟨?_, ?_⟩
  · rw [hxL]
    exact (Finset.mem_sort (r := (· ≤ ·))).mp (List.getElem_mem hjL)
  · rw [hxL]
    exact (List.pairwise_iff_getElem.mp hsorted) j i hjL hiL hji

theorem index_le_card_below_sort (A : Finset ℕ) {i : ℕ} (hi : i < A.card) :
    i ≤ (below A ((A.sort (· ≤ ·))[i]'(by simpa using hi))).card := by
  classical
  have hsub := sort_take_toFinset_subset_below A hi
  have hnodup : ((A.sort (· ≤ ·)).take i).Nodup :=
    (Finset.sort_nodup A (· ≤ ·)).take
  calc
    i = ((A.sort (· ≤ ·)).take i).toFinset.card := by
      rw [List.toFinset_card_of_nodup hnodup]
      simp [hi.le]
    _ ≤ _ := Finset.card_le_card hsub

/-- The `i`th member of an `m`-set in `[1,n]` is at most `n-m+i+1`. -/
theorem sort_getElem_le_of_subset_interval {A : Finset ℕ} {n i : ℕ}
    (hA : A ⊆ interval n) (hi : i < A.card) :
    (A.sort (· ≤ ·))[i]'(by simpa using hi) + A.card ≤ n + i + 1 := by
  classical
  let L := A.sort (· ≤ ·)
  have hlen : L.length = A.card := by simp [L]
  have hmpos : 0 < A.card := by omega
  have hlast : A.card - 1 < L.length := by omega
  have hsorted : L.Pairwise (· < ·) := (Finset.sortedLT_sort A).pairwise
  have hgap := sortedLT_getElem_add_le hsorted (by simpa [hlen] using hi)
    hlast (by omega : i ≤ A.card - 1)
  have hlastMem : L[A.card - 1] ∈ A :=
    (Finset.mem_sort (r := (· ≤ ·))).mp (List.getElem_mem hlast)
  have hlastLe : L[A.card - 1] ≤ n := (mem_interval.mp (hA hlastMem)).2
  change L[i] + A.card ≤ n + i + 1
  omega

/-- Quantitative fixed-rank estimate. -/
theorem rank_excess_le_two_mul_pairsAt {A : Finset ℕ} {n i : ℕ}
    (hA : A ⊆ interval n) (hi : i < A.card) :
    i + A.card ≤ n + 3 + 2 *
      (pairsAt A ((A.sort (· ≤ ·))[i]'(by simpa using hi))).card := by
  classical
  let z := (A.sort (· ≤ ·))[i]'(by simpa using hi)
  have hprefix := index_le_card_below_sort A hi
  have hreflect := two_mul_card_below_le_add_pairsAt A z
  have hz := sort_getElem_le_of_subset_interval hA hi
  dsimp [z] at hreflect ⊢
  omega

/-- Total version of the sorted enumeration, convenient as a finset indexer. -/
noncomputable def zAt (A : Finset ℕ) (i : ℕ) : ℕ :=
  (A.sort (· ≤ ·)).getD i 0

theorem zAt_eq_getElem (A : Finset ℕ) {i : ℕ} (hi : i < A.card) :
    zAt A i = (A.sort (· ≤ ·))[i]'(by simpa using hi) := by
  classical
  simp [zAt, hi]

theorem zAt_mem (A : Finset ℕ) {i : ℕ} (hi : i < A.card) : zAt A i ∈ A := by
  classical
  rw [zAt_eq_getElem A hi]
  exact (Finset.mem_sort (r := (· ≤ ·))).mp
    (List.getElem_mem (by simpa using hi))

theorem zAt_injective_on (A : Finset ℕ) {i j : ℕ}
    (hi : i < A.card) (hj : j < A.card) (hij : zAt A i = zAt A j) : i = j := by
  classical
  have hsorted := (Finset.sortedLT_sort A).pairwise
  rw [zAt_eq_getElem A hi, zAt_eq_getElem A hj] at hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have := (List.pairwise_iff_getElem.mp hsorted) i j
      (by simpa using hi) (by simpa using hj) hlt
    omega
  · exact heq
  · have := (List.pairwise_iff_getElem.mp hsorted) j i
      (by simpa using hj) (by simpa using hi) hgt
    omega

theorem rank_excess_le_two_mul_pairsAt_zAt {A : Finset ℕ} {n i : ℕ}
    (hA : A ⊆ interval n) (hi : i < A.card) :
    i + A.card ≤ n + 3 + 2 * (pairsAt A (zAt A i)).card := by
  rw [zAt_eq_getElem A hi]
  exact rank_excess_le_two_mul_pairsAt hA hi

/-- The union of representations whose targets are among the last `k`
members of `A`. -/
noncomputable def tailPairs (A : Finset ℕ) (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico (A.card - k) A.card).biUnion fun i ↦ pairsAt A (zAt A i)

theorem card_tailPairs_eq_sum (A : Finset ℕ) (k : ℕ) :
    (tailPairs A k).card =
      ∑ i ∈ Finset.Ico (A.card - k) A.card, (pairsAt A (zAt A i)).card := by
  classical
  rw [tailPairs, Finset.card_biUnion]
  intro i hi j hj hij
  apply pairsAt_disjoint
  intro hzi
  apply hij
  apply zAt_injective_on A
  · exact (Finset.mem_Ico.mp hi).2
  · exact (Finset.mem_Ico.mp hj).2
  · exact hzi

theorem tailPairs_subset_schurPairs (A : Finset ℕ) (k : ℕ) :
    tailPairs A k ⊆ schurPairs A := by
  classical
  intro p hp
  rw [tailPairs, Finset.mem_biUnion] at hp
  obtain ⟨i, hi, hp⟩ := hp
  exact pairsAt_subset_schurPairs (zAt_mem A (Finset.mem_Ico.mp hi).2) hp

theorem card_Ico_card_sub (m k : ℕ) :
    (Finset.Ico (m - k) m).card = min k m := by
  simp
  omega

/-- A set occupying at least `52%` of `[1,n]` spans quadratically many
distinct-summand Schur triples.  The floor factors are kept explicit so the
statement is purely natural-valued. -/
theorem dense_schurPairs_lower {A : Finset ℕ} {n : ℕ}
    (hn : 400 ≤ n) (hA : A ⊆ interval n) (hdense : 52 * n ≤ 100 * A.card) :
    (n / 200) * (n / 100) ≤ (schurPairs A).card := by
  classical
  let k := n / 200
  let r := n / 100
  have hkA : k ≤ A.card := by
    dsimp [k]
    omega
  have hterm : ∀ i ∈ Finset.Ico (A.card - k) A.card,
      r ≤ (pairsAt A (zAt A i)).card := by
    intro i hi
    have hiUpper : i < A.card := (Finset.mem_Ico.mp hi).2
    have hiLower : A.card - k ≤ i := (Finset.mem_Ico.mp hi).1
    have hrank := rank_excess_le_two_mul_pairsAt_zAt hA hiUpper
    dsimp [k, r] at hiLower ⊢
    omega
  have hcardI : (Finset.Ico (A.card - k) A.card).card = k := by
    rw [card_Ico_card_sub]
    exact min_eq_left hkA
  calc
    k * r = ∑ _i ∈ Finset.Ico (A.card - k) A.card, r := by
      simp [hcardI]
    _ ≤ ∑ i ∈ Finset.Ico (A.card - k) A.card,
        (pairsAt A (zAt A i)).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i hi
    _ = (tailPairs A k).card := (card_tailPairs_eq_sum A k).symm
    _ ≤ (schurPairs A).card :=
      Finset.card_le_card (tailPairs_subset_schurPairs A k)

/-- Near-extremal form used by the final container count.  Here
`17179869184 = 2^34` and `68719476736 = 2^36`.  Thus the density hypothesis is

`|A| / n ≥ 1/2 + 2^(-35)`,

and the conclusion still gives a fixed positive quadratic density of Schur
edges.  The large cutoff only absorbs the three boundary points lost in the
finite reflection estimate. -/
theorem near_half_schurPairs_lower {A : Finset ℕ} {n : ℕ}
    (hn : 206158430208 ≤ n) (hA : A ⊆ interval n)
    (hdense : 17179869185 * n ≤ 34359738368 * A.card) :
    (n / 68719476736) ^ 2 ≤ (schurPairs A).card := by
  classical
  let k := n / 68719476736
  have hkA : k ≤ A.card := by
    dsimp [k]
    omega
  have hterm : ∀ i ∈ Finset.Ico (A.card - k) A.card,
      k ≤ (pairsAt A (zAt A i)).card := by
    intro i hi
    have hiUpper : i < A.card := (Finset.mem_Ico.mp hi).2
    have hiLower : A.card - k ≤ i := (Finset.mem_Ico.mp hi).1
    have hrank := rank_excess_le_two_mul_pairsAt_zAt hA hiUpper
    dsimp [k] at hiLower ⊢
    omega
  have hcardI : (Finset.Ico (A.card - k) A.card).card = k := by
    rw [card_Ico_card_sub]
    exact min_eq_left hkA
  calc
    k ^ 2 = ∑ _i ∈ Finset.Ico (A.card - k) A.card, k := by
      simp [hcardI, pow_two]
    _ ≤ ∑ i ∈ Finset.Ico (A.card - k) A.card,
        (pairsAt A (zAt A i)).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i hi
    _ = (tailPairs A k).card := (card_tailPairs_eq_sum A k).symm
    _ ≤ (schurPairs A).card :=
      Finset.card_le_card (tailPairs_subset_schurPairs A k)

end Enumeration
end Erdos877
