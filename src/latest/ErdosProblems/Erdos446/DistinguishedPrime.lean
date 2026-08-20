/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.PiFiber

/-!
# Erdős Problem 446: the distinguished prime fiber

Fix the two bit masks and all prime coordinates except a slot where the masks
differ.  The close-product condition then confines the remaining prime to the
candidate set from `ClosePrimeCandidates`, whose reciprocal mass has already
been bounded by a short-prime-window estimate.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The selected bit at a slot. -/
def configurationBit {k : ℕ} {b : ℕ → ℕ}
    (c : BlockSlot k b → Bool × Bool) (first : Bool)
    (s : BlockSlot k b) : Bool :=
  if first then (c s).1 else (c s).2

/-- Product of selected prime coordinates away from one distinguished slot. -/
def awayBitProduct {M k : ℕ} {b : ℕ → ℕ} (s : BlockSlot k b)
    (v : PiAway (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s)
    (c : BlockSlot k b → Bool × Bool) (first : Bool) : ℕ :=
  ∏ t, if configurationBit c first t.1 then (v t).1 else 1

theorem slotBitProduct_piInsert {M k : ℕ} {b : ℕ → ℕ}
    (s : BlockSlot k b)
    (q : ↥(primeBlock (M + s.1)))
    (v : PiAway (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s)
    (c : BlockSlot k b → Bool × Bool) (first : Bool) :
    slotBitProduct (piInsert s q v, c) first =
      (if configurationBit c first s then q.1 else 1) *
        awayBitProduct s v c first := by
  rw [slotBitProduct, Finset.prod_filter]
  change (∏ t, if configurationBit c first t then
      (piInsert s q v t).1 else 1) = _
  let f : ∀ t : BlockSlot k b, ↥(primeBlock (M + t.1)) → ℕ :=
    fun t p ↦ if configurationBit c first t then p.1 else 1
  exact prod_piInsert
    (I := BlockSlot k b)
    (A := fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1)))
    (R := ℕ) f s q v

theorem awayBitProduct_pos {M k : ℕ} {b : ℕ → ℕ}
    (s : BlockSlot k b)
    (v : PiAway (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s)
    (c : BlockSlot k b → Bool × Bool) (first : Bool) :
    0 < awayBitProduct s v c first := by
  apply Finset.prod_pos
  intro t ht
  by_cases hbit : configurationBit c first t.1
  · simp only [hbit, if_true]
    exact (mem_primeBlock.mp (v t).2).1.pos
  · simp [hbit]

theorem slotClose_piInsert_iff_candidates {M k : ℕ} {b : ℕ → ℕ}
    (s : BlockSlot k b)
    (q : ↥(primeBlock (M + s.1)))
    (v : PiAway (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s)
    (c : BlockSlot k b → Bool × Bool)
    (hdiff : (c s).1 ≠ (c s).2) :
    SlotClose (piInsert s q v, c) ↔
      if (c s).1 then
        q.1 ∈ closePrimeCandidates (primeBlock (M + s.1))
          (awayBitProduct s v c true) (awayBitProduct s v c false)
      else
        q.1 ∈ closePrimeCandidates (primeBlock (M + s.1))
          (awayBitProduct s v c false) (awayBitProduct s v c true) := by
  cases h1 : (c s).1 <;> cases h2 : (c s).2
  · exact (hdiff (by simp [h1, h2])).elim
  · simp [SlotClose, slotBitProduct_piInsert, configurationBit,
      h1, h2, mem_closePrimeCandidates, q.2, abs_sub_comm]
  · simp [SlotClose, slotBitProduct_piInsert, configurationBit,
      h1, h2, mem_closePrimeCandidates, q.2, abs_sub_comm]
  · exact (hdiff (by simp [h1, h2])).elim

noncomputable def distinguishedFiberWeight {M k : ℕ} {b : ℕ → ℕ}
    (s : BlockSlot k b)
    (v : PiAway (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s)
    (c : BlockSlot k b → Bool × Bool)
    (q : ↥(primeBlock (M + s.1))) : ℝ := by
  classical
  exact if SlotClose (piInsert s q v, c) then 1 / (q.1 : ℝ) else 0

/-- Once all other coordinates and a differing bit pair are fixed, the
remaining reciprocal-prime mass has the short-window bound. -/
theorem distinguishedPrime_fiber_mass_upper
    {N M k : ℕ} {b : ℕ → ℕ}
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin k, N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ))
    (s : BlockSlot k b)
    (v : PiAway (fun t : BlockSlot k b ↦ ↥(primeBlock (M + t.1))) s)
    (c : BlockSlot k b → Bool × Bool)
    (hdiff : (c s).1 ≠ (c s).2) :
    (∑ q : ↥(primeBlock (M + s.1)),
        distinguishedFiberWeight s v c q) ≤
      7 / Real.log (blockEndpoint (M + s.1) : ℝ) := by
  classical
  let u := awayBitProduct s v c true
  let w := awayBitProduct s v c false
  have hu : 0 < u := awayBitProduct_pos s v c true
  have hw : 0 < w := awayBitProduct_pos s v c false
  let Q := if (c s).1 then
      closePrimeCandidates (primeBlock (M + s.1)) u w
    else closePrimeCandidates (primeBlock (M + s.1)) w u
  have hsum :
      (∑ q : ↥(primeBlock (M + s.1)),
        distinguishedFiberWeight s v c q) =
        primeSetMass Q := by
    calc
      (∑ q : ↥(primeBlock (M + s.1)),
          distinguishedFiberWeight s v c q) =
          ∑ q : ↥(primeBlock (M + s.1)),
            if q.1 ∈ Q then 1 / (q.1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [distinguishedFiberWeight,
          slotClose_piInsert_iff_candidates s q v c hdiff]
        simp only [Q, u, w]
        by_cases hfirst : (c s).1 = true <;> simp [hfirst]
      _ = ∑ p ∈ primeBlock (M + s.1),
          if p ∈ Q then 1 / (p : ℝ) else 0 := by
        rw [Finset.sum_subtype (primeBlock (M + s.1))
          (fun p ↦ Iff.rfl)
          (fun p ↦ if p ∈ Q then 1 / (p : ℝ) else 0)]
      _ = primeSetMass Q := by
        rw [primeSetMass, ← Finset.sum_filter]
        congr 1
        ext p
        simp only [Finset.mem_filter]
        constructor
        · exact fun hp ↦ hp.2
        · intro hpQ
          refine ⟨?_, hpQ⟩
          by_cases hfirst : (c s).1 = true
          · have hpCand : p ∈ closePrimeCandidates
                (primeBlock (M + s.1)) u w := by
              simpa [Q, hfirst] using hpQ
            exact (mem_closePrimeCandidates.mp hpCand).1
          · have hpCand : p ∈ closePrimeCandidates
                (primeBlock (M + s.1)) w u := by
              simpa [Q, hfirst] using hpQ
            exact (mem_closePrimeCandidates.mp hpCand).1
  rw [hsum]
  by_cases hfirst : (c s).1
  · rw [show Q = closePrimeCandidates (primeBlock (M + s.1)) u w by
      simp [Q, hfirst]]
    exact closePrimeCandidates_mass_upper hN (hendpoint s.1) hprime
      (Finset.Subset.rfl) hu hw
  · rw [show Q = closePrimeCandidates (primeBlock (M + s.1)) w u by
      simp [Q, hfirst]]
    exact closePrimeCandidates_mass_upper hN (hendpoint s.1) hprime
      (Finset.Subset.rfl) hw hu

end Erdos446
