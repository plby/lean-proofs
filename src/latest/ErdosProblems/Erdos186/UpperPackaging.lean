/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Foundations

/-!
# Erdős Problem 186: packaging the Pham--Zakharov box theorem

This file states the finite box estimate in the form in which it is used by
Pham and Zakharov.  It does **not** postulate that estimate: the transfer
theorem below takes a proof of `PZBoxBound` as an ordinary argument.

The main result of the file is the completely elementary specialization from
the general integer-box statement to the interval `[1, N]` occurring in the
definition of `F` in `Foundations.lean`.
-/

namespace Erdos186

open Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- A lattice point in dimension `d`. -/
abbrev BoxPoint (d : ℕ) := Fin d → ℤ

/-- A closed axis-parallel integer box.  As in the paper, a box may be empty
when one of its lower endpoints is larger than its upper endpoint. -/
structure IntegerBox (d : ℕ) where
  lower : BoxPoint d
  upper : BoxPoint d

namespace IntegerBox

/-- The finite set of lattice points in an integer box. -/
def carrier {d : ℕ} (B : IntegerBox d) : Finset (BoxPoint d) :=
  Fintype.piFinset fun i ↦ Finset.Icc (B.lower i) (B.upper i)

@[simp] theorem mem_carrier_iff {d : ℕ} {B : IntegerBox d}
    {x : BoxPoint d} :
    x ∈ B.carrier ↔ ∀ i, B.lower i ≤ x i ∧ x i ≤ B.upper i := by
  simp [carrier]

end IntegerBox

/-- The literal distinct-elements nonaveraging condition in `ℤ^d`.
Multiplying by the cardinality avoids division, just as in
`IsNonaveraging` in `Foundations.lean`. -/
def IsBoxNonaveraging {d : ℕ} (A : Finset (BoxPoint d)) : Prop :=
  ∀ a ∈ A, ∀ S : Finset (BoxPoint d),
    S ⊆ A.erase a → 2 ≤ S.card →
      (S.card : ℤ) • a ≠ ∑ x ∈ S, x

/-- The exponent in the Pham--Zakharov box theorem. -/
def boxExponent (d : ℕ) : ℝ :=
  if d = 1 then 1 / 4
  else ((d - 1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)

@[simp] theorem boxExponent_one : boxExponent 1 = (1 / 4 : ℝ) := by
  simp [boxExponent]

/-- The explicit finite Pham--Zakharov box estimate.

For every fixed positive dimension and every positive exponent loss, a
threshold exists such that every nonaveraging subset of every sufficiently
large integer box has the asserted cardinality bound.  This is the exact
finite statement needed below; in particular there is no hidden asymptotic
constant. -/
def PZBoxBound : Prop :=
  ∀ d : ℕ, 0 < d → ∀ ζ : ℝ, 0 < ζ →
    ∃ M : ℕ, ∀ (B : IntegerBox d) (A : Finset (BoxPoint d)),
      A ⊆ B.carrier → IsBoxNonaveraging A → M ≤ B.carrier.card →
        (A.card : ℝ) ≤ (B.carrier.card : ℝ) ^ (boxExponent d + ζ)

namespace OneDimensional

/-- The one-dimensional integer box `[1, N]`. -/
def intervalBox (N : ℕ) : IntegerBox 1 where
  lower := fun _ ↦ 1
  upper := fun _ ↦ N

@[simp] theorem intervalBox_card (N : ℕ) :
    (intervalBox N).carrier.card = N := by
  simp [intervalBox, IntegerBox.carrier]

/-- The natural number `n`, regarded as a point of the one-dimensional
integer lattice. -/
def point (n : ℕ) : BoxPoint 1 := fun _ ↦ n

theorem point_injective : Function.Injective point := by
  intro m n h
  have h0 := congrFun h (0 : Fin 1)
  change (m : ℤ) = (n : ℤ) at h0
  exact Int.ofNat_inj.mp h0

/-- The embedding of natural numbers into the one-dimensional lattice. -/
def pointEmbedding : ℕ ↪ BoxPoint 1 :=
  ⟨point, point_injective⟩

/-- Transport a finite set of naturals into the one-dimensional lattice. -/
def lift (A : Finset ℕ) : Finset (BoxPoint 1) :=
  A.map pointEmbedding

@[simp] theorem card_lift (A : Finset ℕ) : (lift A).card = A.card := by
  simp [lift]

/-- The interval inclusion in `Foundations.lean` transports to inclusion in
the corresponding one-dimensional integer box. -/
theorem lift_subset_intervalBox {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) : lift A ⊆ (intervalBox N).carrier := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hx
  have hnIcc := Finset.mem_Icc.mp (hA hn)
  rw [IntegerBox.mem_carrier_iff]
  intro i
  change (1 : ℤ) ≤ (n : ℤ) ∧ (n : ℤ) ≤ (N : ℤ)
  exact_mod_cast hnIcc

/-- Every finite subset of a mapped set is itself the map of its preimage.
This small lemma makes the transport of the averaging equation explicit. -/
theorem map_preimage_eq_of_subset {A : Finset ℕ} {S : Finset (BoxPoint 1)}
    (hS : S ⊆ lift A) :
    (S.preimage pointEmbedding pointEmbedding.injective.injOn).map
        pointEmbedding = S := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_preimage.mp hn
  · intro hx
    obtain ⟨n, hn, hnpoint⟩ := Finset.mem_map.mp (hS hx)
    refine Finset.mem_map.mpr ⟨n, Finset.mem_preimage.mpr ?_, hnpoint⟩
    simpa [hnpoint] using hx

/-- The embedding into the one-dimensional integer lattice preserves the
nonaveraging condition. -/
theorem isBoxNonaveraging_lift {A : Finset ℕ}
    (hA : IsNonaveraging A) : IsBoxNonaveraging (lift A) := by
  classical
  intro a ha S hS hcard
  obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp ha
  let T : Finset ℕ :=
    S.preimage pointEmbedding pointEmbedding.injective.injOn
  have hS_lift : S ⊆ lift A :=
    hS.trans (Finset.erase_subset _ _)
  have hmap : T.map pointEmbedding = S := by
    exact map_preimage_eq_of_subset hS_lift
  have hTsub : T ⊆ A.erase n := by
    intro t ht
    have het : pointEmbedding t ∈ (lift A).erase (pointEmbedding n) :=
      hS (Finset.mem_preimage.mp ht)
    simpa [lift, ← Finset.map_erase] using het
  have hTcard : T.card = S.card := by
    rw [← hmap]
    simp
  intro heq
  apply hA n hn T hTsub (by simpa [hTcard] using hcard)
  have heq0 := congrFun heq (0 : Fin 1)
  rw [← hmap] at heq0
  have hInt : (T.card : ℤ) * (n : ℤ) = ∑ x ∈ T, (x : ℤ) := by
    simpa [pointEmbedding, point] using heq0
  apply Int.ofNat_inj.mp
  simpa only [Nat.cast_mul, Nat.cast_sum, id_eq] using hInt

end OneDimensional

/-- A proof of the finite Pham--Zakharov box theorem specializes to the
sharp exponent upper bound for the literal extremal function `F`.

The supplied box theorem is used only in dimension one and on the box
`[1, N]`.  The extremizer supplied by `Foundations.lean` is embedded into
`ℤ^1`; the preceding lemmas show that neither cardinality nor the
nonaveraging condition changes. -/
theorem upper_isBigO_of_pzBoxBound (hPZ : PZBoxBound)
    (ε : ℝ) (hε : 0 < ε) :
    (fun N : ℕ ↦ (F N : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ) ^ ((1 / 4 : ℝ) + ε)) := by
  obtain ⟨M, hM⟩ := hPZ 1 Nat.zero_lt_one ε hε
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop M] with N hNM
  obtain ⟨A, hA, hcard⟩ := exists_extremizer N
  have hfinite := hM (OneDimensional.intervalBox N)
    (OneDimensional.lift A)
    (OneDimensional.lift_subset_intervalBox hA.1)
    (OneDimensional.isBoxNonaveraging_lift hA.2)
    (by simpa using hNM)
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (F N : ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _), one_mul,
    OneDimensional.card_lift, hcard, OneDimensional.intervalBox_card,
    boxExponent_one] using hfinite

end


end Erdos186
