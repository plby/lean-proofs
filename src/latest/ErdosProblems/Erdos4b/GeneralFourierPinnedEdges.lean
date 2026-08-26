/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierAffineEdges

/-!
# The pinned collision graph on fixed shift indices

The common primorial cancels from the pinned cross difference at rough
primes. Edges are defined by the literal remaining divisibility, and
the graph has at most one edge per first vertex. Its continuation above
the companion support cutoff is explicitly generic.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def PinnedShiftIndex {K : ℕ} (h : Fin K) := {i : Fin K // i ≠ h}

instance {K : ℕ} (h : Fin K) : Fintype (PinnedShiftIndex h) :=
  inferInstanceAs (Fintype {i : Fin K // i ≠ h})

instance {K : ℕ} (h : Fin K) : DecidableEq (PinnedShiftIndex h) :=
  inferInstanceAs (DecidableEq {i : Fin K // i ≠ h})

def pinnedIndexCrossDifference {K : ℕ} (h : Fin K) (m p₀ : ℕ)
    (i j : PinnedShiftIndex h) : ℤ :=
  (m : ℤ) * p₀ * ((i.val.val : ℤ) - j.val.val) + h.val - i.val.val

def pinnedIndexFourierEdges {K : ℕ} (h : Fin K) (m p₀ p : ℕ) :
    Finset (PinnedShiftIndex h × PinnedShiftIndex h) :=
  Finset.univ.filter (fun ij ↦ (p : ℤ) ∣ pinnedIndexCrossDifference h m p₀ ij.1 ij.2)

theorem fin_natCast_zmod_injective {K p : ℕ} (hKp : K ≤ p) :
    Function.Injective (fun i : Fin K ↦ (i.val : ZMod p)) := by
  intro i j hij
  apply Fin.ext
  exact ((ZMod.natCast_eq_natCast_iff i.val j.val p).mp hij).eq_of_lt_of_lt
    (i.isLt.trans_le hKp) (j.isLt.trans_le hKp)

theorem mem_pinnedIndexFourierEdges_iff {K : ℕ} (h : Fin K) (m p₀ p : ℕ)
    (i j : PinnedShiftIndex h) :
    (i, j) ∈ pinnedIndexFourierEdges h m p₀ p ↔
      (m : ZMod p) * p₀ * ((i.val.val : ZMod p) - j.val.val) + h.val - i.val.val = 0 := by
  simp only [pinnedIndexFourierEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd, pinnedIndexCrossDifference,
    Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast]

theorem pinnedIndexFourierEdges_eq_empty_of_dvd_m
    {K m p₀ p : ℕ} (h : Fin K) (hKp : K ≤ p) (hpm : p ∣ m) :
    pinnedIndexFourierEdges h m p₀ p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨i, j⟩ hij
  have heq := (mem_pinnedIndexFourierEdges_iff h m p₀ p i j).mp hij
  rw [(ZMod.natCast_eq_zero_iff m p).mpr hpm, zero_mul, zero_mul, zero_add] at heq
  have hi : h = i.val := fin_natCast_zmod_injective hKp (sub_eq_zero.mp heq)
  exact i.property hi.symm

theorem pinnedIndexFourierEdges_companion
    {K m p₀ p : ℕ} (h : Fin K) (hKp : K ≤ p)
    (ij : PinnedShiftIndex h × PinnedShiftIndex h)
    (hij : ij ∈ pinnedIndexFourierEdges h m p₀ p) :
    affineFourierCompanionSwitch m p = true := by
  simp only [affineFourierCompanionSwitch, decide_eq_true_eq]
  intro hpm
  rw [pinnedIndexFourierEdges_eq_empty_of_dvd_m h hKp hpm] at hij
  exact Finset.notMem_empty _ hij

theorem card_pinnedIndexFourierEdges_le
    {K m p₀ p : ℕ} (h : Fin K) (hp : p.Prime) (hKp : K ≤ p) (hpp₀ : ¬p ∣ p₀) :
    (pinnedIndexFourierEdges h m p₀ p).card ≤ Fintype.card (PinnedShiftIndex h) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hpm : p ∣ m
  · rw [pinnedIndexFourierEdges_eq_empty_of_dvd_m h hKp hpm]
    exact Nat.zero_le _
  have hm0 : (m : ZMod p) ≠ 0 := fun hz ↦ hpm ((ZMod.natCast_eq_zero_iff m p).mp hz)
  have hp₀0 : (p₀ : ZMod p) ≠ 0 := fun hz ↦ hpp₀ ((ZMod.natCast_eq_zero_iff p₀ p).mp hz)
  have hinj : Set.InjOn (Prod.fst : PinnedShiftIndex h × PinnedShiftIndex h → PinnedShiftIndex h)
      (pinnedIndexFourierEdges h m p₀ p) := by
    intro a ha b hb hab
    apply Prod.ext hab
    apply Subtype.ext
    apply fin_natCast_zmod_injective hKp
    apply mul_left_cancel₀ (mul_ne_zero hm0 hp₀0)
    have hea := (mem_pinnedIndexFourierEdges_iff h m p₀ p a.1 a.2).mp ha
    have heb := (mem_pinnedIndexFourierEdges_iff h m p₀ p b.1 b.2).mp hb
    rw [hab] at hea
    linear_combination -hea + heb
  simpa only [Finset.card_univ] using Finset.card_le_card_of_injOn
    (s := pinnedIndexFourierEdges h m p₀ p) (t := Finset.univ) Prod.fst
    (fun a ha ↦ Finset.mem_univ _) hinj

def truncatedPinnedFourierEdges {K : ℕ} (h : Fin K) (m p₀ Y p : ℕ) :
    Finset (PinnedShiftIndex h × PinnedShiftIndex h) :=
  if p ≤ Y then pinnedIndexFourierEdges h m p₀ p else ∅

def truncatedPinnedFourierCompanion (m Y p : ℕ) : Bool :=
  if p ≤ Y then affineFourierCompanionSwitch m p else true

theorem card_truncatedPinnedFourierEdges_le
    {K w m p₀ Y p : ℕ} (h : Fin K) (hp : p.Prime) (hp₀ : p₀.Prime)
    (hKw : K ≤ w) (hwp : w < p) (hYp₀ : Y < p₀) :
    (truncatedPinnedFourierEdges h m p₀ Y p).card ≤ Fintype.card (PinnedShiftIndex h) := by
  unfold truncatedPinnedFourierEdges
  split_ifs with hpY
  · apply card_pinnedIndexFourierEdges_le h hp (hKw.trans hwp.le)
    intro hdiv
    have heq := (hp₀.dvd_iff_eq hp.ne_one).mp hdiv
    omega
  · exact Nat.zero_le _

theorem truncatedPinnedFourierEdges_companion
    {K w m p₀ Y p : ℕ} (h : Fin K) (hKw : K ≤ w) (hwp : w < p)
    (ij : PinnedShiftIndex h × PinnedShiftIndex h)
    (hij : ij ∈ truncatedPinnedFourierEdges h m p₀ Y p) :
    truncatedPinnedFourierCompanion m Y p = true := by
  unfold truncatedPinnedFourierEdges at hij
  unfold truncatedPinnedFourierCompanion
  split_ifs with hpY
  · exact pinnedIndexFourierEdges_companion h (hKw.trans hwp.le) ij
      (by simpa only [if_pos hpY] using hij)
  · rfl

end

end Erdos4b
