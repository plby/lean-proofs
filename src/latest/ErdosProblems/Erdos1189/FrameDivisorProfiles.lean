/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Exponent restrictions on arithmetic members of generalized frames.
Informal source: BBMST Lemma 7.1; ranks need not be arithmetic.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CoordinateFibres
import ErdosProblems.Erdos1189.FrameExceptionalCoordinates

namespace Erdos1189

open Finset

def rankPrefix {β : Type*} [Fintype β] (rank : β → ℕ) (i : β) : Finset β :=
  univ.filter (fun j => rank j < rank i)

def rankThrough {β : Type*} [Fintype β] (rank : β → ℕ) (i : β) : Finset β :=
  univ.filter (fun j => rank j ≤ rank i)

lemma rankThrough_eq_insert {β : Type*} [Fintype β] [DecidableEq β]
    (rank : β → ℕ) (hinj : Function.Injective rank) (i : β) :
    rankThrough rank i = insert i (rankPrefix rank i) := by
  ext j
  simp only [rankThrough, rankPrefix, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro h
    rcases h.eq_or_lt with heq | hlt
    · exact Or.inl (hinj heq)
    · exact Or.inr hlt
  · rintro (rfl | hlt)
    · exact le_rfl
    · exact hlt.le

lemma fibreExponent_rankThrough {N : ℕ} (rank : PrimeCoordinate N → ℕ)
    (hinj : Function.Injective rank) (i : PrimeCoordinate N) (p : ℕ) :
    fibreExponent (rankThrough rank i) p =
      fibreExponent (rankPrefix rank i) p + if i.1.val = p then 1 else 0 := by
  classical
  have hi : i ∉ rankPrefix rank i := by simp [rankPrefix]
  rw [rankThrough_eq_insert rank hinj, fibreExponent, filter_insert]
  by_cases hp : i.1.val = p
  · rw [if_pos hp, card_insert_of_notMem (fun h => hi (mem_filter.mp h).1)]
    simp only [hp, if_true, fibreExponent]
  · simp only [hp, if_false, add_zero, fibreExponent]

namespace Grid

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]
variable {H : α → Box q} {A : Finset α} {δ : ℝ}

lemma GeneralizedFrame.fixed_subset_through (frame : GeneralizedFrame H A δ)
    (i : ι) {a : α} :
    fixed (H a) ⊆ rankThrough frame.rank i ∪ (frame.outside i ∩ fixed (H a)) := by
  intro j hj
  by_cases hout : j ∈ frame.outside i
  · exact mem_union_right _ (mem_inter.mpr ⟨hout, hj⟩)
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,
      le_of_not_gt (fun hlt => hout (frame.future i j hlt))⟩)

end Grid

variable {N : ℕ} {D : Finset ℕ} {residue : ℕ → ℕ} {δ : ℝ}

lemma frame_fibreExponent_le (frame : Grid.GeneralizedFrame
    (fun d => congruenceBox N d (residue d)) D δ) (hδ : 0 < δ)
    (i : PrimeCoordinate N) {d : ℕ} (hd : d ∈ frame.families i) {T : ℕ}
    (hT : 1 / δ ≤ (T : ℝ)) (p : ℕ) :
    fibreExponent (Grid.fixed (congruenceBox N d (residue d))) p ≤
      fibreExponent (rankThrough frame.rank i) p + if p ≤ T then T else 0 := by
  have hq : ∀ j : PrimeCoordinate N, 2 ≤ coordinateSize j :=
    fun j => (Nat.prime_of_mem_primeFactors j.1.property).two_le
  let E := frame.outside i ∩ Grid.fixed (congruenceBox N d (residue d))
  have hcard : E.card ≤ T := by
    have h := Grid.fixed_card_lt_inverse_of_measure hδ hq (frame.outside i)
      (congruenceBox N d (residue d)) (frame.measure i d hd)
    exact_mod_cast (h.le.trans hT)
  have hsub := frame.fixed_subset_through i (a := d)
  have hmono := (fibreExponent_mono hsub p).trans
    (fibreExponent_union_le (rankThrough frame.rank i) E p)
  by_cases hp : p ≤ T
  · rw [if_pos hp]
    exact hmono.trans (Nat.add_le_add_left ((fibreExponent_le_card E p).trans hcard) _)
  · have hzero : fibreExponent E p = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨hjE, hjp⟩ := mem_filter.mp hj
      obtain ⟨hjOut, hjFix⟩ := mem_inter.mp hjE
      have hlarge : 1 / δ ≤ (coordinateSize j : ℝ) := by
        have hTp : (T : ℝ) ≤ p := by exact_mod_cast (le_of_not_ge hp)
        simpa only [coordinateSize, hjp] using hT.trans hTp
      exact Grid.coordinate_not_fixed_of_large_measure hδ (fun j => (hq j).trans' (by omega))
        (frame.outside i) (congruenceBox N d (residue d)) (frame.measure i d hd) hjOut hlarge hjFix
    simpa only [hzero, hp, if_false, add_zero] using hmono

def frameExponentBound (rank : PrimeCoordinate N → ℕ) (i : PrimeCoordinate N)
    (T : ℕ) (p : ℕ) : ℕ :=
  fibreExponent (rankPrefix rank i) p + (if i.1.val = p then 1 else 0) +
    if p ≤ T then T else 0

lemma frame_modulus_exponent_le (frame : Grid.GeneralizedFrame
    (fun d => congruenceBox N d (residue d)) D δ) (hδ : 0 < δ) (hN : N ≠ 0)
    (hD : ∀ d ∈ D, d ∣ N) (i : PrimeCoordinate N) {d : ℕ}
    (hd : d ∈ frame.families i) {T : ℕ} (hT : 1 / δ ≤ (T : ℝ)) (p : N.primeFactors) :
    d.factorization p ≤ frameExponentBound frame.rank i T p := by
  have h := frame_fibreExponent_le frame hδ i hd hT p
  rw [fibreExponent_congruenceBox hN (hD d (frame.subset i hd)),
    fibreExponent_rankThrough frame.rank frame.rank_injective] at h
  exact h

end Erdos1189
