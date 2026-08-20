/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovLastFailure

/-!
# Erdős Problem 446: splitting the last-failure fiber

This file supplies the order-preserving equivalence which splits an occupancy
vector at a prefix length, together with its exact reciprocal-factorial mass.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- Split a `v`-tuple after its first `h` coordinates. -/
def splitAtCompositionEquiv (v h : ℕ) (hh : h ≤ v) :
    ((Fin h → ℕ) × (Fin (v - h) → ℕ)) ≃ (Fin v → ℕ) :=
  (Fin.appendEquiv h (v - h)).trans
    (Equiv.arrowCongr (finCongr (Nat.add_sub_of_le hh)) (Equiv.refl ℕ))

theorem splitAtCompositionEquiv_apply (v h : ℕ) (hh : h ≤ v)
    (a : Fin h → ℕ) (b : Fin (v - h) → ℕ) (i : Fin v) :
    splitAtCompositionEquiv v h hh (a, b) i =
      Fin.append a b ((finCongr (Nat.add_sub_of_le hh)).symm i) := by
  rfl

theorem ofFn_splitAtCompositionEquiv (v h : ℕ) (hh : h ≤ v)
    (a : Fin h → ℕ) (b : Fin (v - h) → ℕ) :
    List.ofFn (splitAtCompositionEquiv v h hh (a, b)) =
      List.ofFn a ++ List.ofFn b := by
  apply List.ext_getElem
  · simp
    omega
  · intro i hi hi'
    simp only [List.length_ofFn, List.length_append] at hi hi'
    simp only [List.getElem_ofFn]
    by_cases hih : i < h
    · rw [List.getElem_append_left (by simpa using hih),
        List.getElem_ofFn]
      rw [splitAtCompositionEquiv_apply]
      have hfin :
          (finCongr (Nat.add_sub_of_le hh)).symm ⟨i, hi⟩ =
            Fin.castAdd (v - h) ⟨i, hih⟩ := by
        apply Fin.ext
        rfl
      rw [hfin, Fin.append_left]
    · have hivh : h ≤ i := Nat.le_of_not_gt hih
      rw [List.getElem_append_right (by simpa using hivh),
        List.getElem_ofFn]
      rw [splitAtCompositionEquiv_apply]
      have htail : i - h < v - h := by omega
      have hfin :
          (finCongr (Nat.add_sub_of_le hh)).symm ⟨i, hi⟩ =
            Fin.natAdd h ⟨i - h, htail⟩ := by
        apply Fin.ext
        change i = h + (i - h)
        omega
      rw [hfin, Fin.append_right]
      congr 1
      apply Fin.ext
      simp

theorem sum_splitAtCompositionEquiv (v h : ℕ) (hh : h ≤ v)
    (a : Fin h → ℕ) (b : Fin (v - h) → ℕ) :
    (∑ i, splitAtCompositionEquiv v h hh (a, b) i) =
      (∑ i, a i) + ∑ i, b i := by
  rw [← List.sum_ofFn, ofFn_splitAtCompositionEquiv, List.sum_append,
    List.sum_ofFn, List.sum_ofFn]

theorem compositionFactorial_splitAtCompositionEquiv
    (v h : ℕ) (hh : h ≤ v)
    (a : Fin h → ℕ) (b : Fin (v - h) → ℕ) :
    compositionFactorial (splitAtCompositionEquiv v h hh (a, b)) =
      compositionFactorial a * compositionFactorial b := by
  have hlist := congrArg
    (List.map fun n : ℕ ↦ (n.factorial : ℝ))
    (ofFn_splitAtCompositionEquiv v h hh a b)
  have hprod := congrArg List.prod hlist
  simp only [List.map_append, List.prod_append, List.map_ofFn,
    Fin.prod_ofFn] at hprod
  simpa only [compositionFactorial, Function.comp_apply] using hprod

theorem occupancyPrefix_splitAt_left
    (v h : ℕ) (hh : h ≤ v)
    (a : Fin h → ℕ) (b : Fin (v - h) → ℕ) :
    occupancyPrefix (splitAtCompositionEquiv v h hh (a, b)) h = ∑ i, a i := by
  rw [occupancyPrefix_eq_sum_take_ofFn,
    ofFn_splitAtCompositionEquiv, List.take_append_of_le_length]
  · rw [List.take_of_length_le (by simp), List.sum_ofFn]
  · simp

theorem occupancyPrefix_splitAt_add
    (v h : ℕ) (hh : h ≤ v)
    (a : Fin h → ℕ) (b : Fin (v - h) → ℕ)
    {t : ℕ} (ht : t ≤ v - h) :
    occupancyPrefix (splitAtCompositionEquiv v h hh (a, b)) (h + t) =
      (∑ i, a i) + occupancyPrefix b t := by
  have htakeA : (List.ofFn a).take (h + t) = List.ofFn a := by
    apply List.take_of_length_le
    simp
  rw [occupancyPrefix_eq_sum_take_ofFn,
    ofFn_splitAtCompositionEquiv, List.take_append,
    List.length_ofFn, Nat.add_sub_cancel_left, htakeA,
    List.sum_append, List.sum_ofFn, occupancyPrefix_eq_sum_take_ofFn]

/-! ## The fixed last-failure fiber -/

/-- Bad occupancies whose last failed prefix is exactly `h`. -/
noncomputable def lastFailureFiber (k u v h : ℕ) :
    Finset (Fin v → ℕ) := by
  classical
  exact (compositionsOf v k).filter fun c ↦
    ¬ SatisfiesSmirnovBarrier u c ∧ lastFailedPrefix u c = h

theorem mem_lastFailureFiber {k u v h : ℕ} {c : Fin v → ℕ} :
    c ∈ lastFailureFiber k u v h ↔
      (∑ i, c i = k) ∧ ¬ SatisfiesSmirnovBarrier u c ∧
        lastFailedPrefix u c = h := by
  classical
  simp [lastFailureFiber, mem_compositionsOf]

theorem lastFailureFiber_eq_map_product
    {k u v w h : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (hh : 1 ≤ h) (hhv : h ≤ v) (huk : u + h ≤ k) :
    lastFailureFiber k u v h =
      ((compositionsOf h (u + h)) ×ˢ
        smirnovOccupancies (k - (u + h)) 0 (v - h)).map
          (splitAtCompositionEquiv v h hhv).toEmbedding := by
  classical
  ext c
  constructor
  · intro hc
    have hcData := mem_lastFailureFiber.mp hc
    let ab := (splitAtCompositionEquiv v h hhv).symm c
    have habEq : splitAtCompositionEquiv v h hhv ab = c :=
      (splitAtCompositionEquiv v h hhv).apply_symm_apply c
    have hprefixC := occupancyPrefix_lastFailedPrefix_eq
      hw hrel hcData.1 hcData.2.1
    rw [hcData.2.2] at hprefixC
    have haSum : ∑ i, ab.1 i = u + h := by
      rw [← occupancyPrefix_splitAt_left v h hhv ab.1 ab.2,
        habEq, hprefixC]
    have habSum := sum_splitAtCompositionEquiv v h hhv ab.1 ab.2
    rw [habEq, hcData.1] at habSum
    have hbSum : ∑ i, ab.2 i = k - (u + h) := by omega
    have hbBarrier : SatisfiesSmirnovBarrier 0 ab.2 := by
      intro t ht htv
      have hsuf := suffixPrefix_lt_of_lastFailedPrefix
        hw hrel hcData.1 hcData.2.1 ht (by
          simpa [hcData.2.2] using htv)
      rw [hcData.2.2] at hsuf
      have hadd := occupancyPrefix_splitAt_add v h hhv ab.1 ab.2 htv
      have hleft := occupancyPrefix_splitAt_left v h hhv ab.1 ab.2
      rw [habEq] at hadd hleft
      simp only [Nat.zero_add]
      omega
    apply Finset.mem_map.mpr
    refine ⟨ab, ?_, habEq⟩
    exact Finset.mem_product.mpr ⟨mem_compositionsOf.mpr haSum,
      mem_smirnovOccupancies_iff_barrier.mpr
        ⟨mem_compositionsOf.mpr hbSum, hbBarrier⟩⟩
  · intro hc
    obtain ⟨ab, habMem, habEq⟩ := Finset.mem_map.mp hc
    have habEq' : splitAtCompositionEquiv v h hhv (ab.1, ab.2) = c :=
      habEq
    rcases Finset.mem_product.mp habMem with ⟨haMem, hbMem⟩
    have haSum := mem_compositionsOf.mp haMem
    have hbData := mem_smirnovOccupancies_iff_barrier.mp hbMem
    have hbSum := mem_compositionsOf.mp hbData.1
    have hsum := sum_splitAtCompositionEquiv v h hhv ab.1 ab.2
    have hcSum : ∑ i, c i = k := by
      rw [habEq'] at hsum
      omega
    have hexact : occupancyPrefix c h = u + h := by
      rw [← habEq', occupancyPrefix_splitAt_left, haSum]
    have hsuffix : ∀ t : ℕ, 1 ≤ t → t ≤ v - h →
        occupancyPrefix c (h + t) - occupancyPrefix c h < t := by
      intro t ht htv
      have htail := hbData.2 t ht htv
      have hadd := occupancyPrefix_splitAt_add v h hhv ab.1 ab.2 htv
      have hleft := occupancyPrefix_splitAt_left v h hhv ab.1 ab.2
      rw [habEq'] at hadd hleft
      simp only [Nat.zero_add] at htail
      omega
    have hlast : lastFailedPrefix u c = h :=
      lastFailedPrefix_eq_of_exact_suffix hh hhv hexact hsuffix
    have hbad : ¬ SatisfiesSmirnovBarrier u c := by
      intro hgood
      have hlt := hgood h hh hhv
      omega
    exact mem_lastFailureFiber.mpr ⟨hcSum, hbad, hlast⟩

theorem sum_lastFailureFiber_inv_factorial
    {k u v w h : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (hh : 1 ≤ h) (hhv : h ≤ v) (huk : u + h ≤ k) :
    (∑ c ∈ lastFailureFiber k u v h,
      1 / compositionFactorial c) =
      ((h : ℝ) ^ (u + h) / ((u + h).factorial : ℝ)) *
        smirnovOccupancyMass (k - (u + h)) 0 (v - h) := by
  classical
  rw [lastFailureFiber_eq_map_product hw hrel hh hhv huk,
    Finset.sum_map, Finset.sum_product]
  calc
    (∑ a ∈ compositionsOf h (u + h),
        ∑ b ∈ smirnovOccupancies (k - (u + h)) 0 (v - h),
          1 / compositionFactorial
            (splitAtCompositionEquiv v h hhv (a, b))) =
        ∑ a ∈ compositionsOf h (u + h),
          (1 / compositionFactorial a) *
            (∑ b ∈ smirnovOccupancies (k - (u + h)) 0 (v - h),
              1 / compositionFactorial b) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      rw [compositionFactorial_splitAtCompositionEquiv]
      field_simp
    _ = (∑ a ∈ compositionsOf h (u + h),
          1 / compositionFactorial a) *
        (∑ b ∈ smirnovOccupancies (k - (u + h)) 0 (v - h),
          1 / compositionFactorial b) := by
      rw [Finset.sum_mul]
    _ = ((h : ℝ) ^ (u + h) / ((u + h).factorial : ℝ)) *
        smirnovOccupancyMass (k - (u + h)) 0 (v - h) := by
      rw [sum_inv_compositionFactorial_compositionsOf]
      rfl

end Erdos446
