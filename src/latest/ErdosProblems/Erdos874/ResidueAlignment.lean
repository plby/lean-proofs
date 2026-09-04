/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.ConvexTranslate
import ErdosProblems.Erdos874.MixedSumPath

/-!
# Integer alignment of modular restricted-sum witnesses

Residue coverage modulo the difference of a long arithmetic progression is
not, by itself, literal integer progression coverage.  This file records the
integer-level alignment statements which do not lose information when passing
from `ZMod q` back to `ℤ`.

The singleton-residue case is lossless.  In the general case, the exact loss
is the span of the quotient coordinates of the chosen lifts; the latter
statement is `ContainsAP.combine_residue_witnesses` in `ResidueSubgroup`.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

private lemma add_restrictedSumsets_disjoint_residueAlignment
    {A B : Finset ℤ} {r s : ℕ} (hAB : Disjoint A B)
    {x y : ℤ} (hx : x ∈ restrictedSumset r A)
    (hy : y ∈ restrictedSumset s B) :
    x + y ∈ restrictedSumset (r + s) (A ∪ B) := by
  obtain ⟨X, hXA, hXcard, hXsum⟩ := mem_restrictedSumset.mp hx
  obtain ⟨Y, hYB, hYcard, hYsum⟩ := mem_restrictedSumset.mp hy
  have hXY : Disjoint X Y := hAB.mono hXA hYB
  exact mem_restrictedSumset.mpr
    ⟨X ∪ Y,
      Finset.union_subset (hXA.trans Finset.subset_union_left)
        (hYB.trans Finset.subset_union_right),
      by rw [Finset.card_union_of_disjoint hXY, hXcard, hYcard],
      by rw [Finset.sum_union hXY, hXsum, hYsum]⟩

/-- Translating a long restricted-sum progression by one fixed restricted
sum preserves its common difference and its full length.  This is the
lossless endpoint used when the residue subgroup has one element. -/
theorem ContainsAP.add_fixed_restrictedSum
    {B T : Finset ℤ} {t u q L : ℕ} (hBT : Disjoint B T)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) L)
    {w : ℤ} (hw : w ∈ restrictedSumset u T) :
    ContainsAP (restrictedSumset (t + u) (B ∪ T)) (q : ℤ) L := by
  obtain ⟨a, ha⟩ := hlong
  refine ⟨a + w, ?_⟩
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_arithmeticProgression.mp hx
  have hbase : a + (q : ℤ) * (i : ℕ) ∈ restrictedSumset t B :=
    ha (mem_arithmeticProgression.mpr ⟨i, hi, rfl⟩)
  have hadd :=
    add_restrictedSumsets_disjoint_residueAlignment hBT hbase hw
  simpa [add_assoc, add_left_comm, add_comm] using hadd

/-- One residue witness never incurs an integer-lift loss.  This is a direct
specialization of `combine_residue_witnesses`, stated without quotient
bounds so that the `h = 1` branch does not inherit the crude ambient bound
`u*N/q`. -/
theorem ContainsAP.combine_one_residue_witness
    {B T : Finset ℤ} {t u d q L : ℕ} (hBT : Disjoint B T)
    (hq : q = d)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) L)
    {w : ℤ} (hw : w ∈ restrictedSumset u T) :
    ContainsAP (restrictedSumset (t + u) (B ∪ T)) (d : ℤ) L := by
  subst q
  exact hlong.add_fixed_restrictedSum hBT hw

/-- A finite, fully integer-level certificate of an aligned complete residue
block.  The witnesses all use the same restricted-sum layer.  Their displayed
integer formulas, rather than merely their residues modulo `q`, are what make
the quotient loss auditable. -/
structure AlignedResidueWitnesses
    (q u h d loss : ℕ) (T : Finset ℤ) where
  factor : q = d * h
  card_pos : 0 < h
  base : ℤ
  lower : ℤ
  upper : ℤ
  witness : Fin h → ℤ
  quotient : Fin h → ℤ
  witness_mem : ∀ j, witness j ∈ restrictedSumset u T
  witness_eq : ∀ j,
    witness j = base + (d : ℤ) * (j : ℕ) + (q : ℤ) * quotient j
  lower_le : ∀ j, lower ≤ quotient j
  le_upper : ∀ j, quotient j ≤ upper
  span_le : (upper - lower).toNat ≤ loss

/-- A complete coset of a finite subgroup represented in one restricted-sum
layer, with all chosen integer lifts confined to one explicit interval.
Unlike an aligned block, this notion is stable under adding blocks for
different cyclic subgroups. -/
structure BoundedCosetWitnesses
    (q u : ℕ) (T : Finset ℤ) (H : AddSubgroup (ZMod q)) where
  coset : ZMod q
  lower : ℤ
  upper : ℤ
  cover : ∀ x ∈ H, ∃ w ∈ restrictedSumset u T,
    (w : ZMod q) = coset + x ∧ lower ≤ w ∧ w ≤ upper

/-- All increments of `s` on the half-open window `[j,j+o)` have one
sign.  Such a window is monotone, so its intermediate values lie between
its two endpoints. -/
def WindowSignUniform (s : ℕ → ℤ) (j o : ℕ) : Prop :=
  (∀ k, j ≤ k → k < j + o → 0 ≤ s (k + 1) - s k) ∨
  (∀ k, j ≤ k → k < j + o → s (k + 1) - s k ≤ 0)

private lemma seq_le_of_nonneg_increments (s : ℕ → ℤ) {a b : ℕ}
    (hab : a ≤ b)
    (hinc : ∀ k, a ≤ k → k < b → 0 ≤ s (k + 1) - s k) :
    s a ≤ s b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      have hstep := hinc b hab (Nat.lt_succ_self b)
      have ih' := ih (fun k hak hkb ↦
        hinc k hak (hkb.trans (Nat.lt_succ_self b)))
      exact ih'.trans (sub_nonneg.mp hstep)

private lemma seq_le_of_nonpos_increments (s : ℕ → ℤ) {a b : ℕ}
    (hab : a ≤ b)
    (hinc : ∀ k, a ≤ k → k < b → s (k + 1) - s k ≤ 0) :
    s b ≤ s a := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      have hstep := hinc b hab (Nat.lt_succ_self b)
      have ih' := ih (fun k hak hkb ↦
        hinc k hak (hkb.trans (Nat.lt_succ_self b)))
      exact (sub_nonpos.mp hstep).trans ih'

/-- A sign-uniform window really is contained in its endpoint interval. -/
theorem between_endpoints_of_windowSignUniform
    (s : ℕ → ℤ) {j o r : ℕ} (hr : r ≤ o)
    (hsign : WindowSignUniform s j o) :
    min (s j) (s (j + o)) ≤ s (j + r) ∧
      s (j + r) ≤ max (s j) (s (j + o)) := by
  rcases hsign with hpos | hneg
  · have hjr : s j ≤ s (j + r) :=
      seq_le_of_nonneg_increments s (by omega) (by
        intro k hjk hkr
        exact hpos k hjk (by omega))
    have hre : s (j + r) ≤ s (j + o) :=
      seq_le_of_nonneg_increments s (by omega) (by
        intro k hkrk hko
        exact hpos k (by omega) hko)
    exact ⟨(min_le_left _ _).trans hjr, hre.trans (le_max_right _ _)⟩
  · have hjr : s (j + r) ≤ s j :=
      seq_le_of_nonpos_increments s (by omega) (by
        intro k hjk hkr
        exact hneg k hjk (by omega))
    have hre : s (j + o) ≤ s (j + r) :=
      seq_le_of_nonpos_increments s (by omega) (by
        intro k hkrk hko
        exact hneg k (by omega) hko)
    exact ⟨(min_le_right _ _).trans hre, hjr.trans (le_max_left _ _)⟩

theorem windowSignUniform_of_hasUniformIncrementSign
    (s : ℕ → ℤ) {j o : ℕ}
    (h : ConvexTranslate.HasUniformIncrementSign s j o) :
    WindowSignUniform s j o := by
  rcases h with h | h
  · left
    intro k hjk hko
    have hsub : j + (k - j) = k := by omega
    simpa [ConvexTranslate.increment, hsub] using h (k - j) (by omega)
  · right
    intro k hjk hko
    have hsub : j + (k - j) = k := by omega
    simpa [ConvexTranslate.increment, hsub] using h (k - j) (by omega)

/-! Residue fibres used to keep the convex chains disjoint. -/

def integerResidueFiber (q : ℕ) (U : Finset ℤ) (r : ZMod q) : Finset ℤ :=
  U.filter fun x ↦ (x : ZMod q) = r

theorem integerResidueFiber_subset (q : ℕ) (U : Finset ℤ) (r : ZMod q) :
    integerResidueFiber q U r ⊆ U :=
  Finset.filter_subset _ _

theorem pairwiseDisjoint_integerResidueFiber
    {ι : Type*} {S : Set ι} {q : ℕ} {U : Finset ℤ} {r : ι → ZMod q}
    (hr : Set.InjOn r S) :
    S.PairwiseDisjoint fun i ↦ integerResidueFiber q U (r i) := by
  intro i hi j hj hij
  change Disjoint (integerResidueFiber q U (r i))
    (integerResidueFiber q U (r j))
  rw [Finset.disjoint_left]
  intro x hxi hxj
  have hri : (x : ZMod q) = r i := (Finset.mem_filter.mp hxi).2
  have hrj : (x : ZMod q) = r j := (Finset.mem_filter.mp hxj).2
  exact hij (hr hi hj (hri.symm.trans hrj))

theorem injective_fin_nsmul (q : ℕ) (delta : ZMod q) :
    Function.Injective (fun r : Fin (addOrderOf delta) ↦ (r : ℕ) • delta) := by
  intro i j hij
  have hmod : (i : ℕ) ≡ (j : ℕ) [MOD addOrderOf delta] :=
    nsmul_eq_nsmul_iff_modEq.mp hij
  exact Fin.ext (hmod.eq_of_lt_of_lt i.isLt j.isLt)

theorem injective_fin_affine_nsmul (q : ℕ) (delta base : ZMod q) :
    Function.Injective
      (fun r : Fin (addOrderOf delta) ↦ base + (r : ℕ) • delta) := by
  intro i j hij
  exact injective_fin_nsmul q delta (add_left_cancel hij)

lemma orderedMixed_window_natAbs_eq_mul
    {q F j o : ℕ} {X Y : Finset ℤ} {z : ℤ}
    (hz : (q : ℤ) * z =
      orderedMixedSum X Y F (j + o) - orderedMixedSum X Y F j) :
    (orderedMixedSum X Y F (j + o) -
      orderedMixedSum X Y F j).natAbs = q * z.natAbs := by
  rw [← hz, Int.natAbs_mul]
  simp

theorem orderedMixed_window_modulus_dvd
    {q F j : ℕ} {X Y : Finset ℤ} {g₀ g : ZMod q}
    (hXY : Disjoint X Y) (hXcard : X.card = F) (hYcard : Y.card = F)
    (hXres : ∀ x ∈ X, (x : ZMod q) = g₀)
    (hYres : ∀ y ∈ Y, (y : ZMod q) = g)
    (hj : j + addOrderOf (g - g₀) ≤ F) :
    (q : ℤ) ∣ orderedMixedSum X Y F (j + addOrderOf (g - g₀)) -
      orderedMixedSum X Y F j := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [Int.cast_sub,
    orderedMixedSum_residue hXY hXcard hYcard hj hXres hYres,
    orderedMixedSum_residue hXY hXcard hYcard (by omega) hXres hYres,
    add_nsmul, addOrderOf_nsmul_eq_zero]
  simp

theorem chain_cumulative_reconstruct
    (s z : ℕ → ℤ) {T o : ℕ} {q : ℤ} (ho : 0 < o)
    (hz : ∀ j, j + o ≤ T → q * z j = s (j + o) - s j)
    (r : Fin o) {k : ℕ} (hk : k ≤ ConvexTranslate.chainEdgeCount T o r) :
    q * ConvexTranslate.cumulative
        (ConvexTranslate.chainQuotient z o r) k =
      s ((r : ℕ) + k * o) - s r := by
  induction k with
  | zero => simp [ConvexTranslate.cumulative]
  | succ k ih =>
      have hk' : k ≤ ConvexTranslate.chainEdgeCount T o r := by omega
      have hmul : (k + 1) * o ≤ T - (r : ℕ) :=
        (Nat.le_div_iff_mul_le ho).mp hk
      have hedge : (r : ℕ) + k * o + o ≤ T := by
        rw [Nat.add_mul] at hmul
        omega
      have hz' := hz ((r : ℕ) + k * o) hedge
      have hidx : (r : ℕ) + (k + 1) * o = (r : ℕ) + k * o + o := by
        rw [Nat.add_mul]
        omega
      rw [ConvexTranslate.cumulative_succ]
      dsimp only [ConvexTranslate.chainQuotient]
      rw [mul_add, ih hk', hidx]
      linarith

/-- One monotone window of the ordered mixed-sum path gives bounded
witnesses for the cyclic subgroup generated by the residue difference.
The selection/packing argument only has to supply the window and its endpoint
width; this constructor performs all fixed-layer and residue bookkeeping. -/
noncomputable def boundedCosetWitnesses_of_orderedMixed_window
    {q F j Z : ℕ} {X Y : Finset ℤ} {g₀ g : ZMod q}
    (hq : 0 < q) (hXY : Disjoint X Y)
    (hXcard : X.card = F) (hYcard : Y.card = F)
    (hXres : ∀ x ∈ X, (x : ZMod q) = g₀)
    (hYres : ∀ y ∈ Y, (y : ZMod q) = g)
    (horder : 0 < addOrderOf (g - g₀))
    (hj : j + addOrderOf (g - g₀) ≤ F)
    (hbetween : ∀ r : Fin (addOrderOf (g - g₀)),
      min (orderedMixedSum X Y F j)
          (orderedMixedSum X Y F (j + addOrderOf (g - g₀))) ≤
        orderedMixedSum X Y F (j + (r : ℕ)) ∧
      orderedMixedSum X Y F (j + (r : ℕ)) ≤
        max (orderedMixedSum X Y F j)
          (orderedMixedSum X Y F (j + addOrderOf (g - g₀))))
    (hwidth :
      (orderedMixedSum X Y F (j + addOrderOf (g - g₀)) -
        orderedMixedSum X Y F j).natAbs ≤ q * Z) :
    BoundedCosetWitnesses q F (X ∪ Y)
      (AddSubgroup.zmultiples (g - g₀)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let delta : ZMod q := g - g₀
  let s : ℕ → ℤ := orderedMixedSum X Y F
  let lo : ℤ := min (s j) (s (j + addOrderOf delta))
  let hi : ℤ := max (s j) (s (j + addOrderOf delta))
  refine
    { coset := F • g₀ + j • delta
      lower := lo
      upper := hi
      cover := ?_ }
  intro x hx
  have hfin : IsOfFinAddOrder delta := isOfFinAddOrder_of_finite delta
  let r : Fin (addOrderOf delta) :=
    (finEquivZMultiples hfin).symm ⟨x, hx⟩
  have hrval : (r : ℕ) • delta = x := by
    simpa [r] using nsmul_finEquivZMultiples_symm_apply hfin ⟨x, hx⟩
  let w : ℤ := s (j + (r : ℕ))
  have hjr : j + (r : ℕ) ≤ F := by
    have hrlt := r.isLt
    dsimp [delta] at hrlt hj
    omega
  have hwmem : w ∈ restrictedSumset F (X ∪ Y) := by
    exact mem_restrictedSumset.mpr
      ⟨orderedMixedSubset X Y F (j + (r : ℕ)),
        orderedMixedSubset_subset hXcard hYcard hjr,
        card_orderedMixedSubset hXY hXcard hYcard hjr, rfl⟩
  have hwres : (w : ZMod q) = F • g₀ + (j + (r : ℕ)) • delta := by
    simpa [w, s, delta] using
      orderedMixedSum_residue hXY hXcard hYcard hjr hXres hYres
  have hbounds := hbetween r
  refine ⟨w, hwmem, ?_, hbounds.1, hbounds.2⟩
  · rw [hwres, add_nsmul, hrval]
    abel

theorem boundedCosetWitnesses_of_orderedMixed_window_diameter
    {q F j Z : ℕ} {X Y : Finset ℤ} {g₀ g : ZMod q}
    (hq : 0 < q) (hXY : Disjoint X Y)
    (hXcard : X.card = F) (hYcard : Y.card = F)
    (hXres : ∀ x ∈ X, (x : ZMod q) = g₀)
    (hYres : ∀ y ∈ Y, (y : ZMod q) = g)
    (horder : 0 < addOrderOf (g - g₀))
    (hj : j + addOrderOf (g - g₀) ≤ F)
    (hbetween : ∀ r : Fin (addOrderOf (g - g₀)),
      min (orderedMixedSum X Y F j)
          (orderedMixedSum X Y F (j + addOrderOf (g - g₀))) ≤
        orderedMixedSum X Y F (j + (r : ℕ)) ∧
      orderedMixedSum X Y F (j + (r : ℕ)) ≤
        max (orderedMixedSum X Y F j)
          (orderedMixedSum X Y F (j + addOrderOf (g - g₀))))
    (hwidth :
      (orderedMixedSum X Y F (j + addOrderOf (g - g₀)) -
        orderedMixedSum X Y F j).natAbs ≤ q * Z) :
    let W := boundedCosetWitnesses_of_orderedMixed_window hq hXY
      hXcard hYcard hXres hYres horder hj hbetween hwidth
    W.upper - W.lower ≤ (q : ℤ) * (Z : ℤ) := by
  dsimp only [boundedCosetWitnesses_of_orderedMixed_window]
  rw [max_sub_min_eq_abs]
  have hwz :
      (((orderedMixedSum X Y F (j + addOrderOf (g - g₀)) -
        orderedMixedSum X Y F j).natAbs : ℕ) : ℤ) ≤
          (q : ℤ) * (Z : ℤ) := by
    exact_mod_cast hwidth
  simpa [Int.natCast_natAbs, abs_sub_comm] using hwz

/-- The complete one-generator alignment theorem.  A convex ordered mixed
path whose every translate of the long `q`-progression lies in the finite
capacity set `U` has a short sign-uniform window.  That window supplies a
bounded fixed-layer witness block for the whole cyclic subgroup generated by
`g-g₀`; its loss obeys the sharp no-order-factor averaging estimate. -/
theorem exists_boundedCosetWitnesses_of_orderedMixed_capacity
    {q F L : ℕ} {X Y U : Finset ℤ} {g₀ g : ZMod q} (a : ℤ)
    (hq : 0 < q) (hXY : Disjoint X Y)
    (hXcard : X.card = F) (hYcard : Y.card = F)
    (hXres : ∀ x ∈ X, (x : ZMod q) = g₀)
    (hYres : ∀ y ∈ Y, (y : ZMod q) = g)
    (hroom : 2 * addOrderOf (g - g₀) ≤ F)
    (hU : ∀ j ≤ F, ∀ k < L,
      a + orderedMixedSum X Y F j + (q : ℤ) * (k : ℤ) ∈ U)
    (hmargin : 2 * U.card <
      (F - 2 * addOrderOf (g - g₀) + 2) * L) :
    ∃ Z : ℕ,
      Z < L ∧
      (F - 2 * addOrderOf (g - g₀) + 2) * Z ≤ 2 * U.card ∧
      ∃ W : BoundedCosetWitnesses q F (X ∪ Y)
          (AddSubgroup.zmultiples (g - g₀)),
        W.upper - W.lower ≤ (q : ℤ) * (Z : ℤ) := by
  let : NeZero q := ⟨hq.ne'⟩
  let delta : ZMod q := g - g₀
  let o := addOrderOf delta
  let s : ℕ → ℤ := orderedMixedSum X Y F
  have ho : 0 < o := addOrderOf_pos delta
  have hroom' : 2 * o ≤ F := by simpa [o, delta] using hroom
  let z : ℕ → ℤ := fun j ↦
    if hj : j + o ≤ F then
      Classical.choose (orderedMixed_window_modulus_dvd hXY hXcard hYcard
        hXres hYres (by simpa [o, delta] using hj))
    else 0
  have hz : ∀ j, j + o ≤ F →
      (q : ℤ) * z j = s (j + o) - s j := by
    intro j hj
    have hdiv := orderedMixed_window_modulus_dvd hXY hXcard hYcard
      hXres hYres (by simpa [o, delta] using hj)
    have hspec := Classical.choose_spec hdiv
    dsimp only [z]
    rw [dif_pos hj]
    simpa [s, o, delta] using hspec.symm
  have hinc : ∀ i j : ℕ, i ≤ j → j < F →
      ConvexTranslate.increment s i ≤ ConvexTranslate.increment s j := by
    intro i j hij hj
    simpa [ConvexTranslate.increment, s] using
      orderedMixedSum_increment_mono hXY hXcard hYcard hij hj
  have hbaseinj : Function.Injective
      (fun r : Fin o ↦ ((a + s r : ℤ) : ZMod q)) := by
    intro r₁ r₂ heq
    have hs : ((s r₁ : ℤ) : ZMod q) = (s r₂ : ℤ) := by
      push_cast at heq
      exact add_left_cancel heq
    have hr₁F : (r₁ : ℕ) ≤ F := by omega
    have hr₂F : (r₂ : ℕ) ≤ F := by omega
    have hs₁ := orderedMixedSum_residue hXY hXcard hYcard hr₁F hXres hYres
    have hs₂ := orderedMixedSum_residue hXY hXcard hYcard hr₂F hXres hYres
    dsimp [s, delta] at hs hs₁ hs₂
    rw [hs₁, hs₂] at hs
    exact injective_fin_nsmul q delta (add_left_cancel hs)
  have hchainres : ∀ r : Fin o, ∀ x,
      x ∈ ConvexTranslate.canonicalChainBlocks s z F o L a (q : ℤ) r →
      (x : ZMod q) = ((a + s r : ℤ) : ZMod q) := by
    intro r x hx
    simp only [ConvexTranslate.canonicalChainBlocks, Finset.mem_biUnion,
      List.mem_toFinset] at hx
    obtain ⟨v, _hv, hxv⟩ := hx
    simp only [ConvexTranslate.affineBlock] at hxv
    obtain ⟨n, _hn, rfl⟩ := Finset.mem_image.mp hxv
    push_cast
    simp
  have hdis : (Set.univ : Set (Fin o)).PairwiseDisjoint
      (ConvexTranslate.canonicalChainBlocks s z F o L a (q : ℤ)) := by
    intro r₁ _hr₁ r₂ _hr₂ hrne
    change Disjoint
      (ConvexTranslate.canonicalChainBlocks s z F o L a (q : ℤ) r₁)
      (ConvexTranslate.canonicalChainBlocks s z F o L a (q : ℤ) r₂)
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    apply hrne
    apply hbaseinj
    exact (hchainres r₁ x hx₁).symm.trans (hchainres r₂ x hx₂)
  obtain ⟨j, hjgood, hjL, hjcost⟩ :=
    ConvexTranslate.exists_small_uniform_window s z F o L a (q : ℤ) U
      ho hroom' (by exact_mod_cast hq) hinc hz (by simpa [s] using hU)
      hdis (by simpa [o, delta] using hmargin)
  let Z := (z j).natAbs
  have hjbound : j + o ≤ F := by
    have hjrange := (ConvexTranslate.mem_goodWindows.mp hjgood).1
    omega
  have hsign : WindowSignUniform s j o :=
    windowSignUniform_of_hasUniformIncrementSign s
      (ConvexTranslate.mem_goodWindows.mp hjgood).2
  have hbetween : ∀ r : Fin o,
      min (orderedMixedSum X Y F j)
          (orderedMixedSum X Y F (j + addOrderOf (g - g₀))) ≤
        orderedMixedSum X Y F (j + (r : ℕ)) ∧
      orderedMixedSum X Y F (j + (r : ℕ)) ≤
        max (orderedMixedSum X Y F j)
          (orderedMixedSum X Y F (j + addOrderOf (g - g₀))) := by
    intro r
    simpa [s, o, delta] using
      between_endpoints_of_windowSignUniform s (Nat.le_of_lt r.isLt) hsign
  have hjbound' : j + addOrderOf (g - g₀) ≤ F := by
    simpa [o, delta] using hjbound
  have hwidthEq :
      (orderedMixedSum X Y F (j + addOrderOf (g - g₀)) -
        orderedMixedSum X Y F j).natAbs = q * Z := by
    apply orderedMixed_window_natAbs_eq_mul
    simpa [s, o, delta, Z] using hz j hjbound
  let W := boundedCosetWitnesses_of_orderedMixed_window hq hXY hXcard
    hYcard hXres hYres (by simpa [o, delta] using ho) hjbound'
    hbetween hwidthEq.le
  refine ⟨Z, ?_, ?_, W, ?_⟩
  · simpa [Z] using hjL
  · simpa [Z, o, delta] using hjcost
  · exact boundedCosetWitnesses_of_orderedMixed_window_diameter hq hXY
      hXcard hYcard hXres hYres (by simpa [o, delta] using ho) hjbound'
      hbetween hwidthEq.le

/-- Add two bounded coset blocks on disjoint supports.  Both the restricted
layer and the actual integer interval add, while the represented subgroup is
the supremum of the two input subgroups. -/
noncomputable def BoundedCosetWitnesses.add
    {q u₁ u₂ : ℕ} {T₁ T₂ : Finset ℤ}
    {H₁ H₂ : AddSubgroup (ZMod q)}
    (W₁ : BoundedCosetWitnesses q u₁ T₁ H₁)
    (W₂ : BoundedCosetWitnesses q u₂ T₂ H₂)
    (hT : Disjoint T₁ T₂) :
    BoundedCosetWitnesses q (u₁ + u₂) (T₁ ∪ T₂) (H₁ ⊔ H₂) := by
  refine
    { coset := W₁.coset + W₂.coset
      lower := W₁.lower + W₂.lower
      upper := W₁.upper + W₂.upper
      cover := ?_ }
  intro x hx
  obtain ⟨x₁, hx₁, x₂, hx₂, hsum⟩ := AddSubgroup.mem_sup.mp hx
  obtain ⟨w₁, hw₁, hcast₁, hlo₁, hhi₁⟩ := W₁.cover x₁ hx₁
  obtain ⟨w₂, hw₂, hcast₂, hlo₂, hhi₂⟩ := W₂.cover x₂ hx₂
  refine ⟨w₁ + w₂,
    add_restrictedSumsets_disjoint_residueAlignment hT hw₁ hw₂, ?_, ?_, ?_⟩
  · push_cast
    rw [hcast₁, hcast₂, ← hsum]
    abel
  · linarith
  · linarith

/-- Convert bounded actual lifts of a complete subgroup coset into the
canonical `d`-ordered residue witnesses.  The single extra `q` in `hdiam`
accounts for reordering the residues from an arbitrary cyclic generator to
the canonical representatives `0,d,...,(h-1)d`.

The hypothesis is an inequality about the interval already proved by the
selector; no modular-to-integer inference is hidden in this conversion. -/
noncomputable def BoundedCosetWitnesses.toAligned
    {q u E : ℕ} {T : Finset ℤ} {H : AddSubgroup (ZMod q)}
    (W : BoundedCosetWitnesses q u T H) (hq : 0 < q)
    (hdiam : W.upper - W.lower + (q : ℤ) ≤ (q : ℤ) * (E : ℤ)) :
    AlignedResidueWitnesses q u (Nat.card H) (q / Nat.card H) E T := by
  letI : NeZero q := ⟨hq.ne'⟩
  let h := Nat.card H
  let d := q / h
  have hh : 0 < h := Nat.card_pos
  have hdiv : h ∣ q := by
    simpa [h] using H.card_addSubgroup_dvd_card
  have hfactor : q = d * h := by
    simpa [d] using (Nat.div_mul_cancel hdiv).symm
  have hmultiple : ∀ j : Fin h, (((d * (j : ℕ) : ℕ) : ZMod q)) ∈ H := by
    have hm := (zmod_subgroup_index_eq_div_card_and_multiples_mem hq H).2
    intro j
    simpa [h, d] using hm j
  have hwexists : ∀ j : Fin h, ∃ w ∈ restrictedSumset u T,
      (w : ZMod q) = W.coset + (((d * (j : ℕ) : ℕ) : ZMod q)) ∧
      W.lower ≤ w ∧ w ≤ W.upper := by
    intro j
    exact W.cover _ (hmultiple j)
  choose w hwmem hwcast hwlo hwhi using hwexists
  let c : ℤ := (W.coset.val : ℕ)
  have hccast : (c : ZMod q) = W.coset := by simp [c]
  have hzexists : ∀ j : Fin h, ∃ z : ℤ,
      w j = c + (d : ℤ) * (j : ℕ) + (q : ℤ) * z := by
    intro j
    have hzero : (((w j - c - (d : ℤ) * (j : ℕ) : ℤ)) : ZMod q) = 0 := by
      rw [Int.cast_sub, Int.cast_sub, hwcast j, hccast]
      push_cast
      simp
    have hqdiv : (q : ℤ) ∣ w j - c - (d : ℤ) * (j : ℕ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
    obtain ⟨z, hz⟩ := hqdiv
    refine ⟨z, ?_⟩
    nlinarith
  choose z hz using hzexists
  let Z : Finset ℤ := Finset.univ.image z
  have hZ : Z.Nonempty := by
    exact (Finset.univ_nonempty : (Finset.univ : Finset (Fin h)).Nonempty).image z
  let zlo : ℤ := Z.min' hZ
  let zhi : ℤ := Z.max' hZ
  have hzlo_mem : zlo ∈ Z := Finset.min'_mem Z hZ
  have hzhi_mem : zhi ∈ Z := Finset.max'_mem Z hZ
  let jlo : Fin h := Classical.choose (Finset.mem_image.mp hzlo_mem)
  have hjlo_spec := Classical.choose_spec (Finset.mem_image.mp hzlo_mem)
  have hjlo : z jlo = zlo := hjlo_spec.2
  let jhi : Fin h := Classical.choose (Finset.mem_image.mp hzhi_mem)
  have hjhi_spec := Classical.choose_spec (Finset.mem_image.mp hzhi_mem)
  have hjhi : z jhi = zhi := hjhi_spec.2
  have hzlo_le : ∀ j : Fin h, zlo ≤ z j := by
    intro j
    exact Finset.min'_le Z _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hle_zhi : ∀ j : Fin h, z j ≤ zhi := by
    intro j
    exact Finset.le_max' Z _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hlohi : zlo ≤ zhi := by
    exact Finset.min'_le Z zhi hzhi_mem
  have hqspan : (q : ℤ) * (zhi - zlo) ≤ W.upper - W.lower + q := by
    have hwhi_bound := hwhi jhi
    have hwlo_bound := hwlo jlo
    have hjhi0 : (0 : ℤ) ≤ (jhi : ℕ) := by positivity
    have hjlo_lt : ((jlo : ℕ) : ℤ) < h := by exact_mod_cast jlo.isLt
    have hd0 : (0 : ℤ) ≤ d := by positivity
    have hh0 : (0 : ℤ) ≤ h := by positivity
    have hqeq : (q : ℤ) = (d : ℤ) * (h : ℤ) := by
      exact_mod_cast hfactor
    rw [hz jhi, hjhi] at hwhi_bound
    rw [hz jlo, hjlo] at hwlo_bound
    nlinarith
  have hspan_le : (zhi - zlo).toNat ≤ E := by
    have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
    have hspanZ : zhi - zlo ≤ (E : ℤ) := by
      have := hqspan.trans hdiam
      nlinarith
    have hspan0 : 0 ≤ zhi - zlo := sub_nonneg.mpr hlohi
    have hcast : (((zhi - zlo).toNat : ℕ) : ℤ) = zhi - zlo :=
      Int.toNat_of_nonneg hspan0
    exact_mod_cast (hcast ▸ hspanZ)
  exact
    { factor := hfactor
      card_pos := hh
      base := c
      lower := zlo
      upper := zhi
      witness := w
      quotient := z
      witness_mem := hwmem
      witness_eq := hz
      lower_le := hzlo_le
      le_upper := hle_zhi
      span_le := hspan_le }

/-- Combining a long `q`-progression with an aligned complete residue block.
The loss appearing in the result is exactly the proved loss stored in the
certificate. -/
theorem ContainsAP.combine_alignedResidueWitnesses
    {B T : Finset ℤ} {t u q h d L K loss : ℕ}
    (hBT : Disjoint B T)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) L)
    (W : AlignedResidueWitnesses q u h d loss T)
    (hfit : loss + K ≤ L) :
    ContainsAP (restrictedSumset (t + u) (B ∪ T)) (d : ℤ) (h * K) := by
  apply ContainsAP.combine_residue_witnesses hBT W.card_pos W.factor hlong
    W.witness W.quotient W.witness_mem W.witness_eq W.lower_le W.le_upper
  exact (Nat.add_le_add_right W.span_le K).trans hfit

/-- A convenient subtraction-free form of the exact quotient-span fit
condition. -/
lemma quotient_span_fit_of_le
    {zlo zhi : ℤ} {loss K L : ℕ}
    (hspan : zhi - zlo ≤ loss) (hlohi : zlo ≤ zhi)
    (hfit : loss + K ≤ L) :
    (zhi - zlo).toNat + K ≤ L := by
  have hnonneg : 0 ≤ zhi - zlo := sub_nonneg.mpr hlohi
  have hspanNat : (zhi - zlo).toNat ≤ loss := by
    have hcast : (((zhi - zlo).toNat : ℕ) : ℤ) = zhi - zlo :=
      Int.toNat_of_nonneg hnonneg
    exact_mod_cast (hcast ▸ hspan)
  omega

/-! ## The finite averaging step for convex translate families -/

/-- If at least `G` candidate windows have total truncated displacement at
most `2*C`, while `G` full displacements of length `L` would exceed that
capacity, one candidate has both an untruncated displacement and the sharp
averaged bound `G * displacement ≤ 2*C`.

This is the purely finite pigeonhole step used after the convex interval
packing estimate.  Keeping it independent of the way the candidates were
constructed makes all rounding in the later `N^(1/4)` specialization
explicit. -/
theorem exists_small_displacement_of_sum_min_le
    {ι : Type*} [DecidableEq ι] (good : Finset ι) (D : ι → ℕ)
    {G L C : ℕ} (hG : G ≤ good.card) (hGpos : 0 < G)
    (hsum : ∑ i ∈ good, min (D i) L ≤ 2 * C)
    (hmargin : 2 * C < G * L) :
    ∃ i ∈ good, D i < L ∧ G * D i ≤ 2 * C := by
  have hgood : good.Nonempty := Finset.card_pos.mp (hGpos.trans_le hG)
  let values := good.image D
  have hvalues : values.Nonempty := hgood.image D
  let m := values.min' hvalues
  have hm_mem : m ∈ values := Finset.min'_mem values hvalues
  obtain ⟨i, hi, hDi⟩ := Finset.mem_image.mp hm_mem
  have hm_le : ∀ j ∈ good, m ≤ D j := by
    intro j hj
    exact Finset.min'_le values (D j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hlower : good.card * min m L ≤ ∑ j ∈ good, min (D j) L := by
    calc
      good.card * min m L = ∑ _j ∈ good, min m L := by simp
      _ ≤ ∑ j ∈ good, min (D j) L := by
        apply Finset.sum_le_sum
        intro j hj
        exact min_le_min_right L (hm_le j hj)
  have hmL : m < L := by
    by_contra hnot
    have hLm : L ≤ m := Nat.le_of_not_gt hnot
    have hmin : min m L = L := min_eq_right hLm
    have : G * L ≤ 2 * C := by
      calc
        G * L ≤ good.card * L := Nat.mul_le_mul_right L hG
        _ = good.card * min m L := by rw [hmin]
        _ ≤ ∑ j ∈ good, min (D j) L := hlower
        _ ≤ 2 * C := hsum
    omega
  have hmin : min m L = m := min_eq_left hmL.le
  have hGm : G * m ≤ 2 * C := by
    calc
      G * m ≤ good.card * m := Nat.mul_le_mul_right m hG
      _ = good.card * min m L := by rw [hmin]
      _ ≤ ∑ j ∈ good, min (D j) L := hlower
      _ ≤ 2 * C := hsum
  refine ⟨i, hi, ?_, ?_⟩
  · simpa [hDi] using hmL
  · simpa [hDi] using hGm

end

end Erdos874
