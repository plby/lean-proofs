/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Copyright 2026 Johan Land.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 1112.
Informal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
Formal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
GPT-5.5 and Gemini 3.1 supplied advice and adversarial review.
Source: https://www.erdosproblems.com/1112#post-7375
https://github.com/beetree/math_erdos_1112/tree/63ed94d3e802782aeb521095c17d6109a2dc57b5
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
/-
Multiset subset sums, the consecutive-run predicate, and Graham's growth lemma.

`Finset.subsetSum` in Mathlib is for finsets (distinct elements); the paper's
the subset-sum development works with multisets ("x copies of a, Y copies of b, Z copies of M"),
so we define the multiset version and mirror the API.
-/
import Mathlib

namespace Erdos1112
namespace Proof

/-- All subset sums of a multiset of naturals (submultiset selections,
repetitions of the underlying elements allowed). -/
def subsetSums (S : Multiset ℕ) : Finset ℕ :=
  (S.powerset.map Multiset.sum).toFinset

lemma mem_subsetSums {S : Multiset ℕ} {n : ℕ} :
    n ∈ subsetSums S ↔ ∃ T ≤ S, T.sum = n := by
  simp [subsetSums, Multiset.mem_powerset, eq_comm]

lemma zero_mem_subsetSums (S : Multiset ℕ) : 0 ∈ subsetSums S :=
  mem_subsetSums.mpr ⟨0, S.zero_le, rfl⟩

lemma sum_mem_subsetSums (S : Multiset ℕ) : S.sum ∈ subsetSums S :=
  mem_subsetSums.mpr ⟨S, le_rfl, rfl⟩

@[simp] lemma subsetSums_zero : subsetSums 0 = {0} := by
  ext n
  simp [mem_subsetSums, eq_comm]

lemma subsetSums_mono {S S' : Multiset ℕ} (h : S ≤ S') :
    subsetSums S ⊆ subsetSums S' := by
  intro n hn
  obtain ⟨T, hT, rfl⟩ := mem_subsetSums.mp hn
  exact mem_subsetSums.mpr ⟨T, hT.trans h, rfl⟩

/-- Cons splits subset sums into "x unused" ∪ "x used". -/
lemma subsetSums_cons (x : ℕ) (S : Multiset ℕ) :
    subsetSums (x ::ₘ S) = subsetSums S ∪ (subsetSums S).image (x + ·) := by
  ext n
  simp only [Finset.mem_union, Finset.mem_image, mem_subsetSums]
  constructor
  · rintro ⟨T, hT, rfl⟩
    by_cases hx : x ∈ T
    · right
      refine ⟨(T.erase x).sum, ⟨T.erase x, ?_, rfl⟩, ?_⟩
      · exact Multiset.erase_le_iff_le_cons.mpr hT
      · rw [← Multiset.sum_cons, Multiset.cons_erase hx]
    · left
      refine ⟨T, ?_, rfl⟩
      rw [Multiset.le_iff_count]
      intro y
      have hy := Multiset.le_iff_count.mp hT y
      rcases eq_or_ne y x with rfl | hyx
      · simp [Multiset.count_eq_zero.mpr hx]
      · simpa [Multiset.count_cons_of_ne hyx] using hy
  · rintro (⟨T, hT, rfl⟩ | ⟨m, ⟨T, hT, rfl⟩, rfl⟩)
    · exact ⟨T, hT.trans (Multiset.le_cons_self S x), rfl⟩
    · exact ⟨x ::ₘ T, Multiset.cons_le_cons x hT, by simp⟩

/-- Sums from disjoint pools add. -/
lemma add_mem_subsetSums_add {S T : Multiset ℕ} {u v : ℕ}
    (hu : u ∈ subsetSums S) (hv : v ∈ subsetSums T) :
    u + v ∈ subsetSums (S + T) := by
  obtain ⟨U, hU, rfl⟩ := mem_subsetSums.mp hu
  obtain ⟨V, hV, rfl⟩ := mem_subsetSums.mp hv
  exact mem_subsetSums.mpr ⟨U + V, add_le_add hU hV, by simp⟩

/-- `T` contains `len` consecutive integers starting somewhere. -/
def HasRun (T : Finset ℕ) (len : ℕ) : Prop :=
  ∃ c, ∀ i < len, c + i ∈ T

lemma HasRun.mono {T T' : Finset ℕ} {len : ℕ} (hTT' : T ⊆ T') (h : HasRun T len) :
    HasRun T' len :=
  h.imp fun _c hc i hi => hTT' (hc i hi)

lemma HasRun.of_le {T : Finset ℕ} {len len' : ℕ} (hle : len' ≤ len)
    (h : HasRun T len) : HasRun T len' :=
  h.imp fun _c hc i hi => hc i (lt_of_lt_of_le hi hle)

/-- **Graham's growth lemma**: a run of length `ℓ` plus one fresh copy of
`g ≤ ℓ` extends to a run of length `ℓ + g`. -/
lemma HasRun.cons_of_le {S : Multiset ℕ} {ℓ g : ℕ} (hgl : g ≤ ℓ)
    (h : HasRun (subsetSums S) ℓ) : HasRun (subsetSums (g ::ₘ S)) (ℓ + g) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun i hi => ?_⟩
  rw [subsetSums_cons]
  rcases lt_or_ge i ℓ with h' | h'
  · exact Finset.mem_union_left _ (hc i h')
  · refine Finset.mem_union_right _ ?_
    have hig : g ≤ i := hgl.trans h'
    have : c + i = g + (c + (i - g)) := by omega
    rw [this]
    exact Finset.mem_image_of_mem _ (hc (i - g) (by omega))

end Proof
end Erdos1112
