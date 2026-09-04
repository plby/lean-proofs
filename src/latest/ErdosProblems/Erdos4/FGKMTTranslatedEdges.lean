import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Translated anchor intervals

Sampling an anchor in `[1,2Y]` for the forms `n-Y+h_i*p` retains every
target in `[1,Y]`, provided `h_i*p ≤ Y`. No growing initial target block
is discarded.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {k : ℕ}

noncomputable def translatedEdge (h : Fin k → ℕ) (p Y n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 Y).filter (fun q => ∃ i : Fin k, q + Y = n + h i * p)

theorem mem_translatedEdge (h : Fin k → ℕ) (p Y n q : ℕ) :
    q ∈ translatedEdge h p Y n ↔ 1 ≤ q ∧ q ≤ Y ∧ ∃ i : Fin k, q + Y = n + h i * p := by
  classical
  simp only [translatedEdge, Finset.mem_filter, Finset.mem_Icc, and_assoc]

theorem translatedEdge_subset (h : Fin k → ℕ) (p Y n : ℕ) : translatedEdge h p Y n ⊆ Finset.Icc 1 Y :=
  Finset.filter_subset _ _

theorem translatedEdge_card_le (h : Fin k → ℕ) (p Y n : ℕ) : (translatedEdge h p Y n).card ≤ k := by
  classical
  have hsub : translatedEdge h p Y n ⊆ Finset.univ.image (fun i : Fin k => n + h i * p - Y) := by
    intro q hq
    obtain ⟨_, _, i, hi⟩ := (mem_translatedEdge h p Y n q).mp hq
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, by omega⟩
  have hcard : (Finset.univ.image (fun i : Fin k => n + h i * p - Y)).card ≤ k := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := fun i => n + h i * p - Y)
  exact (Finset.card_le_card hsub).trans hcard

theorem translated_anchor_mem (h : Fin k → ℕ) {p Y q : ℕ} (hq0 : 1 ≤ q) (hqY : q ≤ Y)
    (hshift : ∀ i, h i * p ≤ Y) (i : Fin k) :
    q + Y - h i * p ∈ Finset.Icc 1 (2 * Y) ∧
      q ∈ translatedEdge h p Y (q + Y - h i * p) := by
  have hi := hshift i
  constructor
  · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · rw [mem_translatedEdge]
    exact ⟨hq0, hqY, i, by omega⟩

theorem translated_anchor_residue (h : Fin k → ℕ) {p Y q : ℕ}
    (hshift : ∀ i, h i * p ≤ Y) (i j : Fin k) (ell : ℕ) :
    ((q + Y - h i * p : ℕ) : ZMod ell) - (Y : ZMod ell) + (h j : ZMod ell) * (p : ZMod ell) =
      (q : ZMod ell) + ((h j : ZMod ell) - (h i : ZMod ell)) * (p : ZMod ell) := by
  have hle : h i * p ≤ q + Y := by have hh := hshift i; omega
  rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
  ring

theorem translatedEdge_same_source_residue (h : Fin k → ℕ) {p Y n q q' : ℕ}
    (hq : q ∈ translatedEdge h p Y n) (hq' : q' ∈ translatedEdge h p Y n) :
    (q : ZMod p) = (q' : ZMod p) := by
  obtain ⟨_, _, i, hi⟩ := (mem_translatedEdge h p Y n q).mp hq
  obtain ⟨_, _, j, hj⟩ := (mem_translatedEdge h p Y n q').mp hq'
  have hiR := congrArg (fun t : ℕ => (t : ZMod p)) hi
  have hjR := congrArg (fun t : ℕ => (t : ZMod p)) hj
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero] at hiR hjR
  exact add_right_cancel (hiR.trans hjR.symm)

theorem translatedEdge_common_point_unique (h : Fin k → ℕ)
    {p p' Y n n' q q' : ℕ} (hp : p.Prime) (hpp : p'.Prime) (hppne : p' ≠ p)
    (hinj : Function.Injective (fun i => (h i : ZMod p)))
    (hq : q ∈ translatedEdge h p Y n) (hq' : q' ∈ translatedEdge h p Y n)
    (hr : q ∈ translatedEdge h p' Y n') (hr' : q' ∈ translatedEdge h p' Y n') : q = q' := by
  let : Fact p.Prime := ⟨hp⟩
  have hres := translatedEdge_same_source_residue h hq hq'
  obtain ⟨_, _, i, hi⟩ := (mem_translatedEdge h p' Y n' q).mp hr
  obtain ⟨_, _, j, hj⟩ := (mem_translatedEdge h p' Y n' q').mp hr'
  have hiR := congrArg (fun t : ℕ => (t : ZMod p)) hi
  have hjR := congrArg (fun t : ℕ => (t : ZMod p)) hj
  simp only [Nat.cast_add, Nat.cast_mul] at hiR hjR
  have hp'0 : (p' : ZMod p) ≠ 0 := by
    intro hh
    have hd := (ZMod.natCast_eq_zero_iff p' p).mp hh
    exact hppne ((Nat.prime_dvd_prime_iff_eq hp hpp).mp hd).symm
  have hmul : (h i : ZMod p) * (p' : ZMod p) = (h j : ZMod p) * (p' : ZMod p) := by
    apply add_left_cancel (a := (n' : ZMod p))
    rw [← hiR, ← hjR, hres]
  have hij : i = j := hinj (mul_right_cancel₀ hp'0 hmul)
  rw [hij] at hi
  omega

end Erdos4.FGKMT
