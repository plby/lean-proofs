/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.OrderQBound
import ErdosProblems.Erdos896.Ford.Abel
import ErdosProblems.Erdos896.Ford.Uk
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Ford's clustered order-statistics regions

This file formalizes the regions in Lemmas 4.3 and 4.4 of Kevin Ford's
*Integers with a divisor in `(y, 2y]`*.  Coordinates in Lean are zero based:
`x i` is Ford's `ξ_(i+1)`.
-/

namespace Erdos896.Ford

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

/-! ## Measure-preserving coordinate operations -/

/-- Concatenation of two real coordinate blocks, as a measurable equivalence. -/
private noncomputable def appendCoordinates (m n : ℕ) :
    ((Fin m → ℝ) × (Fin n → ℝ)) ≃ᵐ (Fin (m + n) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n ↦ ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) ↦ ℝ)
      (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)))

private theorem measurePreserving_appendCoordinates (m n : ℕ) :
    MeasurePreserving (appendCoordinates m n) := by
  exact
    (volume_measurePreserving_piCongrLeft
      (fun _ : Fin (m + n) ↦ ℝ)
      (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))).comp
        (volume_measurePreserving_sumPiEquivProdPi_symm
          (fun _ : Fin m ⊕ Fin n ↦ ℝ))

@[simp]
private theorem appendCoordinates_castAdd (m n : ℕ) (x : Fin m → ℝ)
    (y : Fin n → ℝ) (i : Fin m) :
    appendCoordinates m n (x, y) (Fin.castAdd n i) = x i := by
  simp [appendCoordinates, MeasurableEquiv.piCongrLeft,
    MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft,
    Equiv.sumPiEquivProdPi]

@[simp]
private theorem appendCoordinates_natAdd (m n : ℕ) (x : Fin m → ℝ)
    (y : Fin n → ℝ) (i : Fin n) :
    appendCoordinates m n (x, y) (Fin.natAdd m i) = y i := by
  simp [appendCoordinates, MeasurableEquiv.piCongrLeft,
    MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft,
    Equiv.sumPiEquivProdPi]

private theorem appendCoordinates_apply (m n : ℕ) (x : Fin m → ℝ)
    (y : Fin n → ℝ) (i : Fin (m + n)) :
    appendCoordinates m n (x, y) i =
      if h : i.1 < m then x ⟨i.1, h⟩ else
        y ⟨i.1 - m, by omega⟩ := by
  split_ifs with h
  · have hi : i = Fin.castAdd n ⟨i.1, h⟩ := by ext; simp
    calc
      appendCoordinates m n (x, y) i =
          appendCoordinates m n (x, y) (Fin.castAdd n ⟨i.1, h⟩) :=
        congrArg (fun j ↦ appendCoordinates m n (x, y) j) hi
      _ = x ⟨i.1, h⟩ := appendCoordinates_castAdd m n x y ⟨i.1, h⟩
  · have hi : i = Fin.natAdd m ⟨i.1 - m, by omega⟩ := by ext; simp; omega
    calc
      appendCoordinates m n (x, y) i =
          appendCoordinates m n (x, y) (Fin.natAdd m ⟨i.1 - m, by omega⟩) :=
        congrArg (fun j ↦ appendCoordinates m n (x, y) j) hi
      _ = y ⟨i.1 - m, by omega⟩ :=
        appendCoordinates_natAdd m n x y ⟨i.1 - m, by omega⟩

private theorem measurableSet_appendCoordinates_image {m n : ℕ}
    {A : Set (Fin m → ℝ)} {B : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet (appendCoordinates m n '' (A ×ˢ B)) := by
  have hs : appendCoordinates m n '' (A ×ˢ B) =
      (appendCoordinates m n).symm ⁻¹' (A ×ˢ B) :=
    (appendCoordinates m n).toEquiv.image_eq_preimage_symm (A ×ˢ B)
  rw [hs]
  exact (appendCoordinates m n).symm.measurable (hA.prod hB)

private theorem volume_appendCoordinates_image {m n : ℕ}
    {A : Set (Fin m → ℝ)} {B : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    volume (appendCoordinates m n '' (A ×ˢ B)) = volume A * volume B := by
  have h := (measurePreserving_appendCoordinates m n).symm.measure_preimage
    (s := A ×ˢ B) ((hA.prod hB).nullMeasurableSet)
  rw [Measure.volume_eq_prod, Measure.prod_prod] at h
  have hs : appendCoordinates m n '' (A ×ˢ B) =
      (appendCoordinates m n).symm ⁻¹' (A ×ˢ B) :=
    (appendCoordinates m n).toEquiv.image_eq_preimage_symm (A ×ˢ B)
  rw [hs]
  exact h

/-- Reindex a real coordinate family along a finite equivalence. -/
private noncomputable def reindexCoordinates {m n : ℕ} (e : Fin m ≃ Fin n) :
    (Fin m → ℝ) ≃ᵐ (Fin n → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e

@[simp]
private theorem reindexCoordinates_apply {m n : ℕ} (e : Fin m ≃ Fin n)
    (x : Fin m → ℝ) (i : Fin n) :
    reindexCoordinates e x i = x (e.symm i) := by
  simp [reindexCoordinates, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]

private theorem measurePreserving_reindexCoordinates {m n : ℕ}
    (e : Fin m ≃ Fin n) : MeasurePreserving (reindexCoordinates e) :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin n ↦ ℝ) e

private theorem measurableSet_reindexCoordinates_image {m n : ℕ}
    (e : Fin m ≃ Fin n) {A : Set (Fin m → ℝ)} (hA : MeasurableSet A) :
    MeasurableSet (reindexCoordinates e '' A) := by
  have hs : reindexCoordinates e '' A = (reindexCoordinates e).symm ⁻¹' A :=
    (reindexCoordinates e).toEquiv.image_eq_preimage_symm A
  rw [hs]
  exact (reindexCoordinates e).symm.measurable hA

private theorem volume_reindexCoordinates_image {m n : ℕ}
    (e : Fin m ≃ Fin n) {A : Set (Fin m → ℝ)} (hA : MeasurableSet A) :
    volume (reindexCoordinates e '' A) = volume A := by
  have h := (measurePreserving_reindexCoordinates e).symm.measure_preimage
    (s := A) hA.nullMeasurableSet
  have hs : reindexCoordinates e '' A = (reindexCoordinates e).symm ⁻¹' A :=
    (reindexCoordinates e).toEquiv.image_eq_preimage_symm A
  rw [hs, h]

/-- The Cartesian product of four consecutive coordinate blocks. -/
private noncomputable def fourBlockSet {n₁ n₂ n₃ n₄ : ℕ}
    (A : Set (Fin n₁ → ℝ)) (B : Set (Fin n₂ → ℝ))
    (C : Set (Fin n₃ → ℝ)) (D : Set (Fin n₄ → ℝ)) :
    Set (Fin (n₁ + (n₂ + (n₃ + n₄))) → ℝ) :=
  appendCoordinates n₁ (n₂ + (n₃ + n₄)) ''
    (A ×ˢ (appendCoordinates n₂ (n₃ + n₄) ''
      (B ×ˢ (appendCoordinates n₃ n₄ '' (C ×ˢ D)))))

private theorem measurableSet_fourBlockSet {n₁ n₂ n₃ n₄ : ℕ}
    {A : Set (Fin n₁ → ℝ)} {B : Set (Fin n₂ → ℝ)}
    {C : Set (Fin n₃ → ℝ)} {D : Set (Fin n₄ → ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    MeasurableSet (fourBlockSet A B C D) := by
  unfold fourBlockSet
  exact measurableSet_appendCoordinates_image hA <|
    measurableSet_appendCoordinates_image hB <|
      measurableSet_appendCoordinates_image hC hD

private theorem volume_fourBlockSet {n₁ n₂ n₃ n₄ : ℕ}
    {A : Set (Fin n₁ → ℝ)} {B : Set (Fin n₂ → ℝ)}
    {C : Set (Fin n₃ → ℝ)} {D : Set (Fin n₄ → ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    volume (fourBlockSet A B C D) =
      volume A * (volume B * (volume C * volume D)) := by
  let CD := appendCoordinates n₃ n₄ '' (C ×ˢ D)
  let BCD := appendCoordinates n₂ (n₃ + n₄) '' (B ×ˢ CD)
  have hCD : MeasurableSet CD := measurableSet_appendCoordinates_image hC hD
  have hBCD : MeasurableSet BCD := measurableSet_appendCoordinates_image hB hCD
  have vCD : volume CD = volume C * volume D :=
    volume_appendCoordinates_image hC hD
  have vBCD : volume BCD = volume B * volume CD :=
    volume_appendCoordinates_image hB hCD
  change volume (appendCoordinates n₁ (n₂ + (n₃ + n₄)) '' (A ×ˢ BCD)) = _
  rw [volume_appendCoordinates_image hA hBCD, vBCD, vCD]

private theorem volume_fourBlockSet_toReal {n₁ n₂ n₃ n₄ : ℕ}
    {A : Set (Fin n₁ → ℝ)} {B : Set (Fin n₂ → ℝ)}
    {C : Set (Fin n₃ → ℝ)} {D : Set (Fin n₄ → ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    (volume (fourBlockSet A B C D)).toReal =
      (volume A).toReal * ((volume B).toReal *
        ((volume C).toReal * (volume D).toReal)) := by
  rw [volume_fourBlockSet hA hB hC hD]
  simp only [ENNReal.toReal_mul]

/-- A translated homothetic copy of Ford's order-statistics set. -/
private noncomputable def affineOrderQSet (k : ℕ) (u v a t : ℝ) :
    Set (Fin k → ℝ) :=
  MeasurableEquiv.addLeft (fun _ : Fin k ↦ a) '' scaledOrderQSet k u v t

private theorem measurableSet_scaledOrderQSet (k : ℕ) (u v t : ℝ) :
    MeasurableSet (scaledOrderQSet k u v t) := by
  by_cases ht : t = 0
  · subst t
    unfold scaledOrderQSet
    by_cases hS : (orderQSet k u v).Nonempty
    · rw [Set.zero_smul_set hS]
      exact MeasurableSet.singleton 0
    · rw [Set.not_nonempty_iff_eq_empty.mp hS]
      simp
  · unfold scaledOrderQSet
    exact (MeasurableEquiv.smul₀ t ht).measurableSet_image.mpr
      (measurableSet_orderQSet k u v)

private theorem measurableSet_affineOrderQSet (k : ℕ) (u v a t : ℝ) :
    MeasurableSet (affineOrderQSet k u v a t) := by
  unfold affineOrderQSet
  have hs : MeasurableEquiv.addLeft (fun _ : Fin k ↦ a) ''
      scaledOrderQSet k u v t =
      (MeasurableEquiv.addLeft (fun _ : Fin k ↦ a)).symm ⁻¹'
        scaledOrderQSet k u v t :=
    (MeasurableEquiv.addLeft (fun _ : Fin k ↦ a)).toEquiv.image_eq_preimage_symm _
  rw [hs]
  exact (MeasurableEquiv.addLeft (fun _ : Fin k ↦ a)).symm.measurable
    (measurableSet_scaledOrderQSet k u v t)

private theorem volume_affineOrderQSet (k : ℕ) (u v a : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    (volume (affineOrderQSet k u v a t)).toReal =
      t ^ k * orderQ k u v / (k.factorial : ℝ) := by
  have hp : MeasurePreserving (MeasurableEquiv.addLeft (fun _ : Fin k ↦ a)) := by
    simpa only [MeasurableEquiv.coe_addLeft] using
      (measurePreserving_add_left volume (fun _ : Fin k ↦ a))
  have htranslate :=
    hp.symm.measure_preimage
      (s := scaledOrderQSet k u v t)
      (measurableSet_scaledOrderQSet k u v t).nullMeasurableSet
  have hs : MeasurableEquiv.addLeft (fun _ : Fin k ↦ a) ''
      scaledOrderQSet k u v t =
      (MeasurableEquiv.addLeft (fun _ : Fin k ↦ a)).symm ⁻¹'
        scaledOrderQSet k u v t :=
    (MeasurableEquiv.addLeft (fun _ : Fin k ↦ a)).toEquiv.image_eq_preimage_symm _
  rw [affineOrderQSet, hs, htranslate, volume_scaledOrderQSet_eq k u v ht]

private theorem volume_orderQSet_lt_top (k : ℕ) (u v : ℝ) :
    volume (orderQSet k u v) < ∞ := by
  refine lt_of_le_of_lt
    (measure_mono (show orderQSet k u v ⊆
      Icc (0 : Fin k → ℝ) (1 : Fin k → ℝ) by
        intro x hx
        exact ⟨fun i ↦ (hx.1.1 i).1, fun i ↦ (hx.1.1 i).2⟩))
    (measure_Icc_lt_top (a := (0 : Fin k → ℝ)) (b := (1 : Fin k → ℝ)))

private theorem volume_scaledOrderQSet_lt_top (k : ℕ) (u v t : ℝ) :
    volume (scaledOrderQSet k u v t) < ∞ := by
  unfold scaledOrderQSet
  rw [Measure.addHaar_smul]
  exact ENNReal.mul_lt_top (by simp) (volume_orderQSet_lt_top k u v)

private theorem volume_affineOrderQSet_lt_top (k : ℕ) (u v a t : ℝ) :
    volume (affineOrderQSet k u v a t) < ∞ := by
  have hp : MeasurePreserving (MeasurableEquiv.addLeft (fun _ : Fin k ↦ a)) := by
    simpa only [MeasurableEquiv.coe_addLeft] using
      (measurePreserving_add_left volume (fun _ : Fin k ↦ a))
  have htranslate := hp.symm.measure_preimage
    (s := scaledOrderQSet k u v t)
    (measurableSet_scaledOrderQSet k u v t).nullMeasurableSet
  have hs : MeasurableEquiv.addLeft (fun _ : Fin k ↦ a) ''
      scaledOrderQSet k u v t =
      (MeasurableEquiv.addLeft (fun _ : Fin k ↦ a)).symm ⁻¹'
        scaledOrderQSet k u v t :=
    (MeasurableEquiv.addLeft (fun _ : Fin k ↦ a)).toEquiv.image_eq_preimage_symm _
  rw [affineOrderQSet, hs, htranslate]
  exact volume_scaledOrderQSet_lt_top k u v t

private theorem orderQ_zero (u v : ℝ) : orderQ 0 u v = 1 := by
  have hset : orderQSet 0 u v = orderedSimplex 0 0 1 := by
    ext x
    simp [orderQSet]
  unfold orderQ
  rw [hset, volume_orderedSimplex_toReal 0 (by norm_num)]
  norm_num

private theorem orderQ_one_one_one : orderQ 1 1 1 = 1 := by
  have hset : orderQSet 1 1 1 = orderedSimplex 1 0 1 := by
    ext x
    simp only [orderQSet, mem_setOf_eq]
    constructor
    · exact fun hx ↦ hx.1
    · intro hx
      refine ⟨hx, ?_⟩
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      norm_num
      exact (hx.1 0).1
  unfold orderQ
  rw [hset, volume_orderedSimplex_toReal 1 (by norm_num)]
  norm_num

/-- Endpoint-safe form of a positive-dimensional `Q` bound.  The shift from
`n` to `n+1` is what is needed to absorb the adjacent one-coordinate block
in Lemma 4.3. -/
private theorem orderQ_bound_succ_of_bound
    {C : ℝ} (hC : 0 < C)
    (hQ : ∀ (n : ℕ) (a b : ℝ),
      1 ≤ n → 0 ≤ a → 0 ≤ a + b - (n : ℝ) →
      orderQ n a b ≤
        C * (a + 1) * (a + b - (n : ℝ) + 1) ^ 2 / (n : ℝ))
    (n : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : 0 ≤ a + b - (n : ℝ)) :
    orderQ n a b ≤
      (2 * (C + 1)) * (a + 1) * (a + b - (n : ℝ) + 1) ^ 2 /
        (n + 1 : ℕ) := by
  let A : ℝ := (a + 1) * (a + b - (n : ℝ) + 1) ^ 2
  have ha1 : 1 ≤ a + 1 := by linarith
  have hab1 : 1 ≤ a + b - (n : ℝ) + 1 := by linarith
  have hA : 1 ≤ A := by
    dsimp only [A]
    exact one_le_mul_of_one_le_of_one_le ha1 (one_le_pow₀ hab1)
  cases n with
  | zero =>
      rw [orderQ_zero]
      norm_num
      have hcoef : 1 ≤ 2 * (C + 1) := by linarith
      have hab10 : 1 ≤ a + b + 1 := by
        norm_num at hab
        linarith
      have hsq : 1 ≤ (a + b + 1) ^ 2 := one_le_pow₀ hab10
      have hprod : 1 ≤ 2 * (C + 1) * ((a + 1) * (a + b + 1) ^ 2) :=
        one_le_mul_of_one_le_of_one_le hcoef
          (one_le_mul_of_one_le_of_one_le ha1 hsq)
      simpa only [mul_assoc] using hprod
  | succ n =>
      have hnR : (0 : ℝ) < n + 1 := by positivity
      have hn1R : (0 : ℝ) < n + 2 := by positivity
      have hmain := hQ (n + 1) a b (by omega) ha hab
      have hmainA : orderQ (n + 1) a b ≤ C * A / (n + 1 : ℕ) := by
        simpa only [A, Nat.cast_add, Nat.cast_one, mul_assoc] using hmain
      calc
        orderQ (n + 1) a b ≤ C * A / (n + 1 : ℕ) := hmainA
        _ ≤ 2 * (C + 1) * A / (n + 2 : ℕ) := by
          norm_num only [Nat.cast_add, Nat.cast_one]
          apply (div_le_div_iff₀ hnR hn1R).2
          have hcoef : C * ((n : ℝ) + 2) ≤
              2 * (C + 1) * ((n : ℝ) + 1) := by
            have hn0 : (0 : ℝ) ≤ n := by positivity
            nlinarith
          have := mul_le_mul_of_nonneg_right hcoef (hA.trans' (by norm_num))
          norm_num at this ⊢
          nlinarith
        _ = 2 * (C + 1) * (a + 1) *
            (a + b - (n + 1 : ℕ) + 1) ^ 2 / (n + 2 : ℕ) := by
          simp only [A, Nat.cast_add, Nat.cast_one]
          ring

private theorem orderQ_prefix_cluster_bound
    {C : ℝ} (hC : 0 < C)
    (hQ : ∀ (n : ℕ) (a b : ℝ),
      1 ≤ n → 0 ≤ a → 0 ≤ a + b - (n : ℝ) →
      orderQ n a b ≤
        C * (a + 1) * (a + b - (n : ℝ) + 1) ^ 2 / (n : ℝ))
    {g k u : ℕ} {l : Fin k} (hgl : g ≤ l.1) :
    orderQ (l.1 - g) u ((l.1 : ℝ) + 2 - u) ≤
      (2 * (C + 1)) * (u + 1) * ((g : ℝ) + 3) ^ 2 /
        (l.1 - g + 1 : ℕ) := by
  have hn : l.1 - g + g = l.1 := Nat.sub_add_cancel hgl
  have hnR : ((l.1 - g : ℕ) : ℝ) + g = l.1 := by exact_mod_cast hn
  have hslack : (u : ℝ) + ((l.1 : ℝ) + 2 - u) -
      ((l.1 - g : ℕ) : ℝ) = (g : ℝ) + 2 := by linarith
  have h := orderQ_bound_succ_of_bound hC hQ (l.1 - g) (u : ℝ)
    ((l.1 : ℝ) + 2 - u) (Nat.cast_nonneg u) (by rw [hslack]; positivity)
  rw [hslack] at h
  norm_num at h ⊢
  convert h using 1 <;> ring

private theorem orderQ_suffix_cluster_bound
    {C : ℝ} (hC : 0 < C)
    (hQ : ∀ (n : ℕ) (a b : ℝ),
      1 ≤ n → 0 ≤ a → 0 ≤ a + b - (n : ℝ) →
      orderQ n a b ≤
        C * (a + 1) * (a + b - (n : ℝ) + 1) ^ 2 / (n : ℝ))
    {k u v : ℕ} (l : Fin k) (huvk : k + 1 ≤ u + v) :
    orderQ (k - l.1 - 1) 0 ((u : ℝ) + v - (l.1 + 1 : ℕ)) ≤
      (2 * (C + 1)) * ((u : ℝ) + v - k + 1) ^ 2 /
        (k - l.1 - 1 + 1 : ℕ) := by
  have hn : l.1 + 1 + (k - l.1 - 1) = k := by omega
  have hnR : (l.1 : ℝ) + 1 + ((k - l.1 - 1 : ℕ) : ℝ) = k := by
    exact_mod_cast hn
  have hslack : (0 : ℝ) + ((u : ℝ) + v - (l.1 + 1 : ℕ)) -
      ((k - l.1 - 1 : ℕ) : ℝ) = (u : ℝ) + v - k := by
    norm_num
    linarith
  have hnonneg : 0 ≤ (u : ℝ) + v - k := by
    have huvR : (k : ℝ) + 1 ≤ (u : ℝ) + v := by exact_mod_cast huvk
    linarith
  have h := orderQ_bound_succ_of_bound hC hQ (k - l.1 - 1) 0
    ((u : ℝ) + v - (l.1 + 1 : ℕ)) (by norm_num) (by
      rw [hslack]
      exact hnonneg)
  rw [hslack] at h
  norm_num at h ⊢
  ring_nf at h ⊢
  exact h

private theorem mem_affineOrderQSet_iff {k : ℕ} {u v a t : ℝ}
    (ht : t ≠ 0) (x : Fin k → ℝ) :
    x ∈ affineOrderQSet k u v a t ↔
      (fun i ↦ (x i - a) / t) ∈ orderQSet k u v := by
  unfold affineOrderQSet scaledOrderQSet
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    convert hz using 1
    funext i
    simp only [MeasurableEquiv.coe_addLeft, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    <;> ring
  · intro hx
    refine ⟨t • (fun i ↦ (x i - a) / t), ⟨_, hx, rfl⟩, ?_⟩
    funext i
    simp only [MeasurableEquiv.coe_addLeft, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    <;> ring

/-! ## The cluster in Lemma 4.3 -/

/-- The part of Ford's `Sₖ(u,v)` possessing the cluster (4.4).  The witness
`l : Fin k` represents Ford's one-based integer `l+1`; consequently the
coordinate `ξ_(l-g)` in the paper is `x (l-g)` with zero-based indices. -/
def clusterRegion (g k s u v : ℕ) : Set (Fin k → ℝ) :=
  {x | x ∈ orderQSet k u v ∧
    ∃ l : Fin k, g ≤ l.1 ∧
      (((l.1 : ℝ) + 1 - u) / v ≤ x l) ∧
      (x l ≤ ((l.1 : ℝ) + 2 - u) / v) ∧
      (((l.1 : ℝ) + 1 - u - s) / v ≤
        x ⟨l.1 - g, (Nat.sub_le l.1 g).trans_lt l.isLt⟩)}

/-- The fixed-witness piece of `clusterRegion`. -/
private def clusterSlice (g k s u v : ℕ) (l : Fin k) : Set (Fin k → ℝ) :=
  {x ∈ orderQSet k u v |
    (((l.1 : ℝ) + 1 - u) / v ≤ x l) ∧
    (x l ≤ ((l.1 : ℝ) + 2 - u) / v) ∧
    (((l.1 : ℝ) + 1 - u - s) / v ≤
      x ⟨l.1 - g, (Nat.sub_le l.1 g).trans_lt l.isLt⟩)}

private theorem clusterRegion_eq_iUnion (g k s u v : ℕ) :
    clusterRegion g k s u v =
      ⋃ l : Fin k, if g ≤ l.1 then clusterSlice g k s u v l else ∅ := by
  ext x
  simp only [clusterRegion, clusterSlice, mem_ofPred_eq, mem_iUnion, mem_ite,
    mem_empty_iff_false]
  constructor
  · rintro ⟨hx, l, hgl, hl⟩
    exact ⟨l, ⟨fun _ ↦ ⟨hx, hl⟩, fun hn ↦ hn hgl⟩⟩
  · rintro ⟨l, hl⟩
    have hgl : g ≤ l.1 := by
      by_contra hn
      exact hl.2 hn
    have hs := hl.1 hgl
    exact ⟨hs.1, l, hgl, hs.2⟩

private theorem measurableSet_clusterSlice (g k s u v : ℕ) (l : Fin k) :
    MeasurableSet (clusterSlice g k s u v l) := by
  unfold clusterSlice
  apply (measurableSet_orderQSet k u v).inter
  show MeasurableSet ({x : Fin k → ℝ |
    (((l.1 : ℝ) + 1 - u) / v ≤ x l) ∧
    (x l ≤ ((l.1 : ℝ) + 2 - u) / v) ∧
    (((l.1 : ℝ) + 1 - u - s) / v ≤
      x ⟨l.1 - g, (Nat.sub_le l.1 g).trans_lt l.isLt⟩)} : Set _)
  measurability

private theorem clusterSlice_subset_orderQSet (g k s u v : ℕ) (l : Fin k) :
    clusterSlice g k s u v l ⊆ orderQSet k u v := by
  exact fun _ hx ↦ hx.1

private theorem volume_clusterSlice_lt_top (g k s u v : ℕ) (l : Fin k) :
    volume (clusterSlice g k s u v l) < ∞ := by
  exact lt_of_le_of_lt
    (measure_mono (clusterSlice_subset_orderQSet g k s u v l))
    (volume_orderQSet_lt_top k u v)

/-- Witnesses below the intercept contribute only a coordinate hyperplane. -/
private theorem volume_clusterSlice_zero_of_lt
    {g k s u v : ℕ} {l : Fin k} (hv : 0 < v) (hlu : l.1 + 1 < u) :
    volume (clusterSlice g k s u v l) = 0 := by
  have hsub : clusterSlice g k s u v l ⊆ {x : Fin k → ℝ | x l = 0} := by
    intro x hx
    apply le_antisymm
    · have hvR : (0 : ℝ) < v := by exact_mod_cast hv
      have hnum : (l.1 : ℝ) + 2 - u ≤ 0 := by
        have hcast : (l.1 : ℝ) + 2 ≤ (u : ℝ) := by
          exact_mod_cast (by omega : l.1 + 2 ≤ u)
        linarith
      exact hx.2.2.1.trans (div_nonpos_of_nonpos_of_nonneg hnum hvR.le)
    · exact (hx.1.1.1 l).1
  apply measure_mono_null hsub
  simpa only [MeasureTheory.volume_pi] using
    (Measure.pi_hyperplane (fun _ : Fin k ↦ (volume : Measure ℝ)) l 0)

private theorem volume_clusterRegion_toReal_le_sum_slices
    (g k s u v : ℕ) :
    (volume (clusterRegion g k s u v)).toReal ≤
      ∑ l : Fin k, if g ≤ l.1 then
        (volume (clusterSlice g k s u v l)).toReal else 0 := by
  have hmeasure : volume (clusterRegion g k s u v) ≤
      ∑ l : Fin k, if g ≤ l.1 then
        volume (clusterSlice g k s u v l) else 0 := by
    rw [clusterRegion_eq_iUnion]
    calc
      volume (⋃ l : Fin k, if g ≤ l.1 then clusterSlice g k s u v l else ∅) ≤
          ∑ l : Fin k, volume
            (if g ≤ l.1 then clusterSlice g k s u v l else ∅) :=
        measure_iUnion_fintype_le volume _
      _ = ∑ l : Fin k, if g ≤ l.1 then
          volume (clusterSlice g k s u v l) else 0 := by
        apply Finset.sum_congr rfl
        intro l hl
        split_ifs <;> simp
  have hsum_ne : (∑ l : Fin k, if g ≤ l.1 then
      volume (clusterSlice g k s u v l) else 0) ≠ ∞ := by
    apply (ENNReal.sum_lt_top.mpr _).ne
    intro l hl
    split_ifs
    · exact volume_clusterSlice_lt_top g k s u v l
    · simp
  calc
    (volume (clusterRegion g k s u v)).toReal ≤
        (∑ l : Fin k, if g ≤ l.1 then
          volume (clusterSlice g k s u v l) else 0).toReal :=
      ENNReal.toReal_mono hsum_ne hmeasure
    _ = ∑ l : Fin k, if g ≤ l.1 then
        (volume (clusterSlice g k s u v l)).toReal else 0 := by
      rw [ENNReal.toReal_sum (fun l _ ↦ by
        split_ifs
        · exact (volume_clusterSlice_lt_top g k s u v l).ne
        · simp)]
      apply Finset.sum_congr rfl
      intro l hl
      split_ifs <;> simp

theorem measurableSet_clusterRegion (g k s u v : ℕ) :
    MeasurableSet (clusterRegion g k s u v) := by
  let Rl : Fin k → Set (Fin k → ℝ) := fun l ↦
    {x | (((l.1 : ℝ) + 1 - u) / v ≤ x l) ∧
      (x l ≤ ((l.1 : ℝ) + 2 - u) / v) ∧
      (((l.1 : ℝ) + 1 - u - s) / v ≤
        x ⟨l.1 - g, (Nat.sub_le l.1 g).trans_lt l.isLt⟩)}
  have hRl (l : Fin k) : MeasurableSet (Rl l) := by
    dsimp only [Rl]
    measurability
  rw [show clusterRegion g k s u v = orderQSet k u v ∩
      ⋃ l : Fin k, if g ≤ l.1 then Rl l else ∅ by
    ext x
    simp [clusterRegion, Rl]]
  exact (measurableSet_orderQSet k u v).inter <|
    MeasurableSet.iUnion fun l ↦ by
      split_ifs <;> simp_all

theorem clusterRegion_subset_orderQSet (g k s u v : ℕ) :
    clusterRegion g k s u v ⊆ orderQSet k u v := by
  intro x hx
  exact hx.1

theorem volume_clusterRegion_le_orderQSet (g k s u v : ℕ) :
    volume (clusterRegion g k s u v) ≤ volume (orderQSet k u v) :=
  measure_mono (clusterRegion_subset_orderQSet g k s u v)

/-- The parameter-dependent factor on the right of Ford's Lemma 4.3.
The theorem's absolute implied constant is deliberately not included. -/
noncomputable def clusterVolumeScale (g k s u v : ℕ) : ℝ :=
  (g : ℝ) ^ 2 * (10 * (s + 1 : ℝ)) ^ g / (g.factorial : ℝ) *
    ((u + 1 : ℝ) * ((u : ℝ) + v - k) ^ 2) /
      ((k + 1).factorial : ℝ)

/-- Exact product volume of the four block envelopes for a fixed witness.
This is the unsummed expression before Lemmas 4.1 and 4.2 are applied. -/
noncomputable def clusterWitnessVolume (g k s u v : ℕ) (l : Fin k) : ℝ :=
  let n₁ := l.1 - g
  let n₄ := k - l.1 - 1
  let L : ℝ := (l.1 : ℝ) + 1
  let W₁ : ℝ := L - u + 1
  let W₄ : ℝ := (u : ℝ) + v - L
  ((W₁ / v) ^ n₁ * orderQ n₁ u W₁ / (n₁.factorial : ℝ)) *
    ((((s + 1 : ℝ) / v) ^ g * orderQ g g 1 / (g.factorial : ℝ)) *
    (((1 / (v : ℝ)) * orderQ 1 1 1) *
    ((W₄ / v) ^ n₄ * orderQ n₄ 0 W₄ /
      (n₄.factorial : ℝ))))

/-- The binomial summand which remains after the two uses of Lemma 4.1 in
the proof of Lemma 4.3. -/
noncomputable def clusterAbelSummand (g k u v : ℕ) (l : Fin k) : ℝ :=
  let t := k + 1 - g
  let j := l.1 + 1 - g
  (t.choose j : ℝ) * ((l.1 : ℝ) + 2 - u) ^ (l.1 - g) *
    ((u : ℝ) + v - (l.1 + 1 : ℕ)) ^ (k - l.1 - 1)

/-- The factorial-normalized monomial underlying `clusterAbelSummand`. -/
noncomputable def clusterRawSummand (g k u v : ℕ) (l : Fin k) : ℝ :=
  ((l.1 : ℝ) + 2 - u) ^ (l.1 - g) *
      ((u : ℝ) + v - (l.1 + 1 : ℕ)) ^ (k - l.1 - 1) /
    (((l.1 - g + 1).factorial : ℝ) *
      ((k - l.1 - 1 + 1).factorial : ℝ))

private theorem clusterRawSummand_eq
    {g k u v : ℕ} (l : Fin k) (hgl : g ≤ l.1) :
    clusterRawSummand g k u v l =
      clusterAbelSummand g k u v l / ((k + 1 - g).factorial : ℝ) := by
  let t := k + 1 - g
  let j := l.1 + 1 - g
  have hj : l.1 - g + 1 = j := by dsimp only [j]; omega
  have htj : t - j = k - l.1 := by dsimp only [t, j]; omega
  have hn₄ : k - l.1 - 1 + 1 = k - l.1 := by omega
  have hjt : j ≤ t := by dsimp only [j, t]; omega
  have hfacNat := Nat.choose_mul_factorial_mul_factorial hjt
  have hfac : (t.choose j : ℝ) * (j.factorial : ℝ) *
      ((t - j).factorial : ℝ) = (t.factorial : ℝ) := by
    exact_mod_cast hfacNat
  unfold clusterRawSummand clusterAbelSummand
  dsimp only
  rw [hj, hn₄, ← htj]
  field_simp
  dsimp only [t, j] at hfac
  rw [← hfac]
  ring

private theorem clusterWitnessVolume_le_raw
    {C : ℝ} (hC : 0 < C)
    (hQ : ∀ (n : ℕ) (a b : ℝ),
      1 ≤ n → 0 ≤ a → 0 ≤ a + b - (n : ℝ) →
      orderQ n a b ≤
        C * (a + 1) * (a + b - (n : ℝ) + 1) ^ 2 / (n : ℝ))
    {g k s u v : ℕ} {l : Fin k} (hg : 1 ≤ g) (hgl : g ≤ l.1)
    (hv : 0 < v) (hul : u ≤ l.1 + 1) (huvk : k + 1 ≤ u + v) :
    clusterWitnessVolume g k s u v l ≤
      256 * (C + 1) ^ 2 * (u + 1) * (g : ℝ) ^ 2 *
        ((u : ℝ) + v - k) ^ 2 * (s + 1 : ℝ) ^ g /
          ((g.factorial : ℝ) * (v : ℝ) ^ k) *
        clusterRawSummand g k u v l := by
  let n₁ := l.1 - g
  let n₄ := k - l.1 - 1
  let W₁ : ℝ := (l.1 : ℝ) + 2 - u
  let W₄ : ℝ := (u : ℝ) + v - (l.1 + 1 : ℕ)
  let w : ℝ := (u : ℝ) + v - k
  let D : ℝ := 2 * (C + 1)
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hW₁ : 0 ≤ W₁ := by
    dsimp only [W₁]
    have hulR : (u : ℝ) ≤ (l.1 : ℝ) + 1 := by exact_mod_cast hul
    linarith
  have hW₄ : 0 ≤ W₄ := by
    dsimp only [W₄]
    have hR : (l.1 : ℝ) + 1 ≤ (u : ℝ) + v := by
      exact_mod_cast (by omega : l.1 + 1 ≤ u + v)
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hw : 1 ≤ w := by
    dsimp only [w]
    have hR : (k : ℝ) + 1 ≤ (u : ℝ) + v := by exact_mod_cast huvk
    linarith
  have hD : 0 ≤ D := by dsimp only [D]; linarith
  have hpre := orderQ_prefix_cluster_bound hC hQ
    (g := g) (k := k) (u := u) (l := l) hgl
  have hsuf := orderQ_suffix_cluster_bound hC hQ l huvk
  have hg3 : ((g : ℝ) + 3) ^ 2 ≤ 16 * (g : ℝ) ^ 2 := by
    have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
    nlinarith [sq_nonneg ((g : ℝ) - 1)]
  have hw1 : (w + 1) ^ 2 ≤ 4 * w ^ 2 := by
    nlinarith [sq_nonneg (w - 1)]
  have hpre' : orderQ n₁ u W₁ ≤
      D * (u + 1) * (16 * (g : ℝ) ^ 2) / (n₁ + 1 : ℕ) := by
    dsimp only [n₁, W₁, D]
    refine hpre.trans ?_
    gcongr
  have hsuf' : orderQ n₄ 0 W₄ ≤
      D * (4 * w ^ 2) / (n₄ + 1 : ℕ) := by
    dsimp only [n₄, W₄, D, w]
    refine hsuf.trans ?_
    gcongr
  have hmid := orderQ_le_one g g 1
  have hpre'' : orderQ (l.1 - g) u ((l.1 : ℝ) + 1 - u + 1) ≤
      D * (u + 1) * (16 * (g : ℝ) ^ 2) / (l.1 - g + 1 : ℕ) := by
    dsimp only [n₁, W₁] at hpre'
    convert hpre' using 1 <;> ring
  have hsuf'' : orderQ (k - l.1 - 1) 0
      ((u : ℝ) + v - ((l.1 : ℝ) + 1)) ≤
      D * (4 * w ^ 2) / (k - l.1 - 1 + 1 : ℕ) := by
    dsimp only [n₄, W₄] at hsuf'
    convert hsuf' using 1 <;> norm_num
  have hdim : n₁ + g + 1 + n₄ = k := by
    dsimp only [n₁, n₄]
    omega
  have hqpre0 : 0 ≤ orderQ (l.1 - g) u ((l.1 : ℝ) + 1 - u + 1) :=
    orderQ_nonneg _ _ _
  have hqmid0 : 0 ≤ orderQ g g 1 := orderQ_nonneg _ _ _
  have hqsuf0 : 0 ≤ orderQ (k - l.1 - 1) 0
      ((u : ℝ) + v - ((l.1 : ℝ) + 1)) := orderQ_nonneg _ _ _
  have hscalePre : 0 ≤ ((l.1 : ℝ) + 1 - u + 1) / v := by
    apply div_nonneg
    · dsimp only [W₁] at hW₁
      norm_num only [Nat.cast_add, Nat.cast_one] at hW₁ ⊢
      linarith
    · exact hvR.le
  have hscaleSuf : 0 ≤ ((u : ℝ) + v - ((l.1 : ℝ) + 1)) / v := by
    apply div_nonneg
    · dsimp only [W₄] at hW₄
      norm_num only [Nat.cast_add, Nat.cast_one] at hW₄ ⊢
      exact hW₄
    · exact hvR.le
  calc
    clusterWitnessVolume g k s u v l ≤
        ((W₁ / v) ^ n₁ *
          (D * (u + 1) * (16 * (g : ℝ) ^ 2) / (n₁ + 1 : ℕ)) /
            (n₁.factorial : ℝ)) *
        ((((s + 1 : ℝ) / v) ^ g * 1 / (g.factorial : ℝ)) *
        (((1 / (v : ℝ)) * 1) *
        ((W₄ / v) ^ n₄ * (D * (4 * w ^ 2) / (n₄ + 1 : ℕ)) /
          (n₄.factorial : ℝ)))) := by
      unfold clusterWitnessVolume
      dsimp only [n₁, n₄, W₁, W₄]
      rw [orderQ_one_one_one]
      gcongr <;>
        first | exact hpre'' | exact hmid | exact hsuf'' |
          exact hqpre0 | exact hqmid0 | exact hqsuf0 |
          exact hscalePre | exact hscaleSuf | linarith | positivity | norm_num
    _ = 256 * (C + 1) ^ 2 * (u + 1) * (g : ℝ) ^ 2 * w ^ 2 *
          (s + 1 : ℝ) ^ g /
            ((g.factorial : ℝ) * (v : ℝ) ^ k) *
          clusterRawSummand g k u v l := by
      unfold clusterRawSummand
      dsimp only [D, W₁, W₄, n₁, n₄]
      rw [Nat.factorial_succ, Nat.factorial_succ]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      have hvpow : (v : ℝ) ^ k =
          (v : ℝ) ^ (l.1 - g) * (v : ℝ) ^ g * v *
            (v : ℝ) ^ (k - l.1 - 1) := by
        conv_lhs => rw [← hdim]
        simp only [pow_add, pow_one]
        ring
      simp only [div_pow]
      rw [hvpow]
      field_simp [hvR.ne']
      ring
    _ = 256 * (C + 1) ^ 2 * (u + 1) * (g : ℝ) ^ 2 *
        ((u : ℝ) + v - k) ^ 2 * (s + 1 : ℝ) ^ g /
          ((g.factorial : ℝ) * (v : ℝ) ^ k) *
        clusterRawSummand g k u v l := by rfl

/-- The witness-index sum in Lemma 4.3 is exactly the Abel sum of Lemma 4.2. -/
theorem sum_clusterAbelSummand {g k u v : ℕ} (hgk : g + 1 ≤ k) :
    ∑ l ∈ (Finset.univ : Finset (Fin k)).filter
        (fun l ↦ g ≤ l.1 ∧ u ≤ l.1 + 1),
        clusterAbelSummand g k u v l =
      fordLemmaFourTwoSum (k + 1 - g)
        ((g : ℝ) + 1 - u) ((u : ℝ) + v - k - 1) := by
  classical
  let Ls : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter
    (fun l ↦ g ≤ l.1 ∧ u ≤ l.1 + 1)
  let Js : Finset ℕ := (Finset.Icc 1 (k + 1 - g - 1)).filter
    (fun j ↦ 0 < (g : ℝ) + 1 - u + (j : ℝ))
  change ∑ l ∈ Ls, clusterAbelSummand g k u v l = _
  rw [fordLemmaFourTwoSum]
  change _ = ∑ j ∈ Js, _
  apply Finset.sum_nbij (fun l : Fin k ↦ l.1 + 1 - g)
  · intro l hl
    change l ∈ Ls at hl
    simp only [Ls, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    simp only [Js, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · constructor <;> omega
    · have huR : (u : ℝ) ≤ (l.1 : ℝ) + 1 := by exact_mod_cast hl.2
      have hid : g + (l.1 + 1 - g) = l.1 + 1 := by omega
      have hidR : (g : ℝ) + ((l.1 + 1 - g : ℕ) : ℝ) =
          (l.1 : ℝ) + 1 := by exact_mod_cast hid
      linarith
  · intro l₁ hl₁ l₂ hl₂ heq
    change l₁ ∈ Ls at hl₁
    change l₂ ∈ Ls at hl₂
    simp only [Ls, Finset.mem_filter, Finset.mem_univ, true_and] at hl₁ hl₂
    apply Fin.ext
    change l₁.1 + 1 - g = l₂.1 + 1 - g at heq
    have h₁ : g + (l₁.1 + 1 - g) = l₁.1 + 1 := by omega
    have h₂ : g + (l₂.1 + 1 - g) = l₂.1 + 1 := by omega
    omega
  · intro j hj
    change j ∈ Js at hj
    simp only [Js, Finset.mem_filter, Finset.mem_Icc] at hj
    let l : Fin k := ⟨g + j - 1, by omega⟩
    refine ⟨l, ?_, ?_⟩
    · change l ∈ Ls
      simp only [Ls, Finset.mem_filter, Finset.mem_univ, true_and, l]
      constructor
      · omega
      · have hp := hj.2
        have hpNat : u < g + 1 + j := by
          by_contra hn
          have hnR : (g : ℝ) + 1 + (j : ℝ) ≤ (u : ℝ) := by
            exact_mod_cast (by omega : g + 1 + j ≤ u)
          linarith
        omega
    · dsimp only [l]
      omega
  · intro l hl
    change l ∈ Ls at hl
    simp only [Ls, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    unfold clusterAbelSummand
    dsimp only
    have htj : k + 1 - g - (l.1 + 1 - g) = k - l.1 := by omega
    have hjm : l.1 + 1 - g - 1 = l.1 - g := by omega
    rw [hjm, htj]
    have hjadd : g + (l.1 + 1 - g) = l.1 + 1 := by omega
    have hjaddR : (g : ℝ) + ((l.1 + 1 - g : ℕ) : ℝ) =
        (l.1 : ℝ) + 1 := by exact_mod_cast hjadd
    have hkl : l.1 + (k - l.1) = k := by omega
    have hklR : (l.1 : ℝ) + ((k - l.1 : ℕ) : ℝ) = k := by
      exact_mod_cast hkl
    rw [show (l.1 : ℝ) + 2 - u =
        (g : ℝ) + 1 - u + ((l.1 + 1 - g : ℕ) : ℝ) by linarith]
    rw [show (u : ℝ) + v - (l.1 + 1 : ℕ) =
        (u : ℝ) + v - k - 1 + ((k - l.1 : ℕ) : ℝ) by
      norm_num
      linarith]

/-- Abel's inequality, already specialized to the witness sum of Lemma 4.3. -/
theorem sum_clusterAbelSummand_le_exp
    {g k u v : ℕ} (hgk : g + 1 ≤ k) (huvk : k + 1 ≤ u + v) :
    ∑ l ∈ (Finset.univ : Finset (Fin k)).filter
        (fun l ↦ g ≤ l.1 ∧ u ≤ l.1 + 1),
        clusterAbelSummand g k u v l ≤
      Real.exp 4 * ((v : ℝ) + 1) ^ (k - g) := by
  rw [sum_clusterAbelSummand hgk]
  have ht : 2 ≤ k + 1 - g := by omega
  have hb : 0 ≤ (u : ℝ) + v - k - 1 := by
    have huvkR : (k : ℝ) + 1 ≤ (u : ℝ) + v := by exact_mod_cast huvk
    linarith
  have hab : 0 < (k + 1 - g : ℕ) + ((g : ℝ) + 1 - u) +
      ((u : ℝ) + v - k - 1) := by
    have hkg : g ≤ k + 1 := by omega
    have hcast : ((k + 1 - g : ℕ) : ℝ) = (k : ℝ) + 1 - g := by
      rw [Nat.cast_sub hkg]
      norm_num
    rw [hcast]
    have hv1 : 0 < (v : ℝ) + 1 := by positivity
    linarith
  calc
    fordLemmaFourTwoSum (k + 1 - g) ((g : ℝ) + 1 - u)
        ((u : ℝ) + v - k - 1) ≤
        Real.exp 4 * (((k + 1 - g : ℕ) : ℝ) +
          ((g : ℝ) + 1 - u) + ((u : ℝ) + v - k - 1)) ^
            (k + 1 - g - 1) :=
      lemma_four_two ht hb hab
    _ = Real.exp 4 * ((v : ℝ) + 1) ^ (k - g) := by
      have hkg : g ≤ k + 1 := by omega
      have hcast : ((k + 1 - g : ℕ) : ℝ) = (k : ℝ) + 1 - g := by
        rw [Nat.cast_sub hkg]
        norm_num
      rw [hcast]
      congr 2
      · ring
      · omega

private theorem succ_pow_le_exp_ten_mul_pow {v n : ℕ}
    (hv : 1 ≤ v) (hn : n ≤ 10 * v) :
    ((v + 1 : ℕ) : ℝ) ^ n ≤ (Real.exp 1) ^ 10 * (v : ℝ) ^ n := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hbase : (1 : ℝ) ≤ 1 + (v : ℝ)⁻¹ := by
    exact le_add_of_nonneg_right (inv_nonneg.mpr hvR.le)
  have hmono : (1 + (v : ℝ)⁻¹) ^ n ≤
      (1 + (v : ℝ)⁻¹) ^ (10 * v) :=
    pow_le_pow_right₀ hbase hn
  have hEuler : (1 + (v : ℝ)⁻¹) ^ v ≤ Real.exp 1 :=
    Real.one_add_inv_pow_le_exp
  have hten : (1 + (v : ℝ)⁻¹) ^ (10 * v) ≤ (Real.exp 1) ^ 10 := by
    calc
      (1 + (v : ℝ)⁻¹) ^ (10 * v) =
          ((1 + (v : ℝ)⁻¹) ^ v) ^ 10 := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ (Real.exp 1) ^ 10 := by gcongr
  have hfactor : ((v + 1 : ℕ) : ℝ) =
      (v : ℝ) * (1 + (v : ℝ)⁻¹) := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  calc
    ((v + 1 : ℕ) : ℝ) ^ n =
        (v : ℝ) ^ n * (1 + (v : ℝ)⁻¹) ^ n := by
      rw [hfactor, mul_pow]
    _ ≤ (v : ℝ) ^ n * (1 + (v : ℝ)⁻¹) ^ (10 * v) := by
      gcongr
    _ ≤ (v : ℝ) ^ n * (Real.exp 1) ^ 10 := by gcongr
    _ = (Real.exp 1) ^ 10 * (v : ℝ) ^ n := by ring

theorem sum_clusterAbelSummand_le
    {g k u v : ℕ} (hgk : g + 1 ≤ k) (huvk : k + 1 ≤ u + v)
    (hv : 1 ≤ v) (hkv : k ≤ 10 * v) :
    ∑ l ∈ (Finset.univ : Finset (Fin k)).filter
        (fun l ↦ g ≤ l.1 ∧ u ≤ l.1 + 1),
        clusterAbelSummand g k u v l ≤
      (Real.exp 4 * (Real.exp 1) ^ 10) * (v : ℝ) ^ (k - g) := by
  calc
    ∑ l ∈ (Finset.univ : Finset (Fin k)).filter
        (fun l ↦ g ≤ l.1 ∧ u ≤ l.1 + 1),
        clusterAbelSummand g k u v l ≤
        Real.exp 4 * ((v : ℝ) + 1) ^ (k - g) :=
      sum_clusterAbelSummand_le_exp hgk huvk
    _ = Real.exp 4 * (((v + 1 : ℕ) : ℝ) ^ (k - g)) := by norm_num
    _ ≤ Real.exp 4 * ((Real.exp 1) ^ 10 * (v : ℝ) ^ (k - g)) := by
      gcongr
      exact succ_pow_le_exp_ten_mul_pow hv ((Nat.sub_le k g).trans hkv)
    _ = (Real.exp 4 * (Real.exp 1) ^ 10) * (v : ℝ) ^ (k - g) := by ring

/-- The four independent coordinate blocks used for a fixed witness in (4.4). -/
private noncomputable def clusterBlockEnvelope (g k s u v : ℕ) (l : Fin k)
    (hgl : g ≤ l.1) : Set (Fin k → ℝ) :=
  let n₁ := l.1 - g
  let n₄ := k - l.1 - 1
  let L : ℝ := (l.1 : ℝ) + 1
  let W₁ : ℝ := L - u + 1
  let W₄ : ℝ := (u : ℝ) + v - L
  let A := affineOrderQSet n₁ u W₁ 0 (W₁ / v)
  let B := affineOrderQSet g g 1 ((L - u - s) / v) ((s + 1 : ℝ) / v)
  let C := affineOrderQSet 1 1 1 ((L - u) / v) (1 / (v : ℝ))
  let D := affineOrderQSet n₄ 0 W₄ ((L - u) / v) (W₄ / v)
  have hdim : n₁ + (g + (1 + n₄)) = k := by
    dsimp only [n₁, n₄]
    omega
  reindexCoordinates (finCongr hdim) '' fourBlockSet A B C D

private theorem measurableSet_clusterBlockEnvelope (g k s u v : ℕ) (l : Fin k)
    (hgl : g ≤ l.1) : MeasurableSet (clusterBlockEnvelope g k s u v l hgl) := by
  unfold clusterBlockEnvelope
  dsimp only
  apply measurableSet_reindexCoordinates_image
  exact measurableSet_fourBlockSet
    (measurableSet_affineOrderQSet ..) (measurableSet_affineOrderQSet ..)
    (measurableSet_affineOrderQSet ..) (measurableSet_affineOrderQSet ..)

private theorem volume_clusterBlockEnvelope (g k s u v : ℕ) (l : Fin k)
    (hgl : g ≤ l.1) (hv : 0 < v) (hul : u ≤ l.1 + 1)
    (huvk : k + 1 ≤ u + v) :
    let n₁ := l.1 - g
    let n₄ := k - l.1 - 1
    let L : ℝ := (l.1 : ℝ) + 1
    let W₁ : ℝ := L - u + 1
    let W₄ : ℝ := (u : ℝ) + v - L
    (volume (clusterBlockEnvelope g k s u v l hgl)).toReal =
      ((W₁ / v) ^ n₁ * orderQ n₁ u W₁ / (n₁.factorial : ℝ)) *
      ((((s + 1 : ℝ) / v) ^ g * orderQ g g 1 / (g.factorial : ℝ)) *
      (((1 / (v : ℝ)) * orderQ 1 1 1) *
      ((W₄ / v) ^ n₄ * orderQ n₄ 0 W₄ /
        (n₄.factorial : ℝ)))) := by
  dsimp only
  unfold clusterBlockEnvelope
  dsimp only
  rw [volume_reindexCoordinates_image _
      (measurableSet_fourBlockSet
        (measurableSet_affineOrderQSet ..) (measurableSet_affineOrderQSet ..)
        (measurableSet_affineOrderQSet ..) (measurableSet_affineOrderQSet ..)),
    volume_fourBlockSet_toReal
      (measurableSet_affineOrderQSet ..) (measurableSet_affineOrderQSet ..)
      (measurableSet_affineOrderQSet ..) (measurableSet_affineOrderQSet ..),
    volume_affineOrderQSet _ _ _ _ (by
      apply div_nonneg
      · have hulR : (u : ℝ) ≤ (l.1 : ℝ) + 1 := by exact_mod_cast hul
        linarith
      · positivity),
    volume_affineOrderQSet _ _ _ _ (by positivity :
      0 ≤ ((s + 1 : ℝ) / v)),
    volume_affineOrderQSet _ _ _ _ (by positivity :
      0 ≤ (1 / (v : ℝ))),
    volume_affineOrderQSet _ _ _ _ (by
      have : (0 : ℝ) ≤ (u : ℝ) + v - ((l.1 : ℝ) + 1) := by
        apply sub_nonneg.mpr
        exact_mod_cast (by omega : l.1 + 1 ≤ u + v)
      positivity)]
  norm_num

private theorem fixedCluster_subset_clusterBlockEnvelope
    {g k s u v : ℕ} {l : Fin k} (hg : 1 ≤ g) (hgl : g ≤ l.1)
    (hv : 0 < v) (hul : u ≤ l.1 + 1) (huvk : k + 1 ≤ u + v) :
    clusterSlice g k s u v l ⊆
      clusterBlockEnvelope g k s u v l hgl := by
  intro x hx
  let n₁ := l.1 - g
  let n₄ := k - l.1 - 1
  let L : ℝ := (l.1 : ℝ) + 1
  let W₁ : ℝ := L - u + 1
  let W₄ : ℝ := (u : ℝ) + v - L
  let t₁ : ℝ := W₁ / v
  let t₂ : ℝ := (s + 1 : ℝ) / v
  let t₃ : ℝ := 1 / (v : ℝ)
  let t₄ : ℝ := W₄ / v
  let a₂ : ℝ := (L - u - s) / v
  let a₃ : ℝ := (L - u) / v
  let x₁ : Fin n₁ → ℝ := fun i ↦ x ⟨i.1, by dsimp only [n₁] at i ⊢; omega⟩
  let x₂ : Fin g → ℝ := fun i ↦
    x ⟨n₁ + i.1, by dsimp only [n₁] at i ⊢; omega⟩
  let x₃ : Fin 1 → ℝ := fun _ ↦ x l
  let x₄ : Fin n₄ → ℝ := fun i ↦
    x ⟨l.1 + 1 + i.1, by dsimp only [n₄] at i ⊢; omega⟩
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hW₁ : 0 < W₁ := by
    dsimp only [W₁, L]
    have hulR : (u : ℝ) ≤ (l.1 : ℝ) + 1 := by exact_mod_cast hul
    linarith
  have hW₄ : 0 < W₄ := by
    dsimp only [W₄, L]
    have hleR : (l.1 : ℝ) + 1 < (u : ℝ) + v := by
      exact_mod_cast (by omega : l.1 + 1 < u + v)
    linarith
  have ht₁ : 0 < t₁ := div_pos hW₁ hvR
  have ht₂ : 0 < t₂ := by dsimp only [t₂]; positivity
  have ht₃ : 0 < t₃ := by dsimp only [t₃]; positivity
  have ht₄ : 0 < t₄ := div_pos hW₄ hvR
  have hx₁ : x₁ ∈ affineOrderQSet n₁ u W₁ 0 t₁ := by
    apply (mem_affineOrderQSet_iff ht₁.ne' x₁).2
    simp only [sub_zero]
    constructor
    · constructor
      · intro i
        constructor
        · exact div_nonneg (hx.1.1.1 _).1 ht₁.le
        · apply (div_le_one ht₁).2
          have hm : x ⟨i.1, by dsimp only [n₁] at i ⊢; omega⟩ ≤ x l :=
            hx.1.1.2 (by
              change i.1 ≤ l.1
              dsimp only [n₁] at i
              omega)
          exact hm.trans <| hx.2.2.1.trans_eq (by dsimp only [t₁, W₁, L]; ring)
      · intro i j hij
        apply (div_le_div_iff_of_pos_right ht₁).2
        exact hx.1.1.2 (by simp only [Fin.mk_le_mk]; exact hij)
    · intro i
      have hq := hx.1.2 ⟨i.1, by dsimp only [n₁] at i ⊢; omega⟩
      dsimp only [x₁, t₁]
      apply (div_le_div_iff₀ hW₁ (div_pos hW₁ hvR)).2
      rw [div_eq_mul_inv]
      have hq' := (div_le_iff₀ hvR).mp hq
      field_simp [hvR.ne']
      nlinarith [hW₁]
  have hx₂ : x₂ ∈ affineOrderQSet g g 1 a₂ t₂ := by
    apply (mem_affineOrderQSet_iff ht₂.ne' x₂).2
    constructor
    · constructor
      · intro i
        constructor
        · apply div_nonneg
          · apply sub_nonneg.mpr
            have hm : x ⟨l.1 - g, (Nat.sub_le l.1 g).trans_lt l.isLt⟩ ≤
                x ⟨n₁ + i.1, by dsimp only [n₁] at i ⊢; omega⟩ :=
              hx.1.1.2 (by simp only [Fin.mk_le_mk]; dsimp only [n₁]; omega)
            exact hx.2.2.2.trans hm
          · exact ht₂.le
        · apply (div_le_one ht₂).2
          dsimp only [x₂, a₂, t₂, L, n₁]
          have hm : x ⟨l.1 - g + i.1, by omega⟩ ≤ x l :=
            hx.1.1.2 (by
              change l.1 - g + i.1 ≤ l.1
              omega)
          apply (sub_le_iff_le_add).2
          rw [← add_div]
          apply (le_div_iff₀ hvR).2
          have hm' := mul_le_mul_of_nonneg_right hm hvR.le
          have hl' := (le_div_iff₀ hvR).mp hx.2.2.1
          norm_num only [Nat.cast_add, Nat.cast_one] at hl' ⊢
          nlinarith
      · intro i j hij
        apply (div_le_div_iff_of_pos_right ht₂).2
        exact sub_le_sub_right (hx.1.1.2 (by
          simp only [Fin.mk_le_mk]
          exact Nat.add_le_add_left hij n₁)) _
    · intro i
      have hi : (i.1 : ℝ) + 1 - (g : ℝ) ≤ 0 := by
        apply sub_nonpos.mpr
        exact_mod_cast (by omega : i.1 + 1 ≤ g)
      have hm : x ⟨l.1 - g, (Nat.sub_le l.1 g).trans_lt l.isLt⟩ ≤
          x ⟨n₁ + i.1, by dsimp only [n₁] at i ⊢; omega⟩ :=
        hx.1.1.2 (by simp only [Fin.mk_le_mk]; dsimp only [n₁]; omega)
      simpa only [div_one] using hi.trans
        (div_nonneg (sub_nonneg.mpr (hx.2.2.2.trans hm)) ht₂.le)
  have hx₃ : x₃ ∈ affineOrderQSet 1 1 1 a₃ t₃ := by
    apply (mem_affineOrderQSet_iff ht₃.ne' x₃).2
    constructor
    · constructor
      · intro i
        constructor
        · exact div_nonneg (sub_nonneg.mpr hx.2.1) ht₃.le
        · apply (div_le_one ht₃).2
          apply (sub_le_iff_le_add).2
          dsimp only [x₃, a₃, t₃, L]
          rw [← add_div]
          apply (le_div_iff₀ hvR).2
          have hl' := (le_div_iff₀ hvR).mp hx.2.2.1
          norm_num only [Nat.cast_add, Nat.cast_one] at hl' ⊢
          nlinarith
      · intro i j hij
        exact le_rfl
    · intro i
      norm_num
      exact div_nonneg (sub_nonneg.mpr hx.2.1) ht₃.le
  have hx₄ : x₄ ∈ affineOrderQSet n₄ 0 W₄ a₃ t₄ := by
    apply (mem_affineOrderQSet_iff ht₄.ne' x₄).2
    constructor
    · constructor
      · intro i
        constructor
        · apply div_nonneg
          · apply sub_nonneg.mpr
            have hq := hx.1.2 ⟨l.1 + 1 + i.1, by dsimp only [n₄] at i ⊢; omega⟩
            dsimp only [a₃, L]
            have hq' := (div_le_iff₀ hvR).mp hq
            apply (div_le_iff₀ hvR).2
            norm_num only [Fin.val_mk, Nat.cast_add, Nat.cast_one] at hq' ⊢
            nlinarith
          · exact ht₄.le
        · apply (div_le_one ht₄).2
          dsimp only [x₄, a₃, t₄, W₄, L]
          have hb := (hx.1.1.1 ⟨l.1 + 1 + i.1,
            by dsimp only [n₄] at i ⊢; omega⟩).2
          field_simp [hvR.ne']
          nlinarith
      · intro i j hij
        apply (div_le_div_iff_of_pos_right ht₄).2
        exact sub_le_sub_right (hx.1.1.2 (by
          simp only [Fin.mk_le_mk]
          exact Nat.add_le_add_left hij (l.1 + 1))) _
    · intro i
      have hq := hx.1.2 ⟨l.1 + 1 + i.1, by dsimp only [n₄] at i ⊢; omega⟩
      dsimp only [x₄, a₃, t₄]
      have hq' := (div_le_iff₀ hvR).mp hq
      have hnormalize :
          (x ⟨l.1 + 1 + i.1, by dsimp only [n₄] at i ⊢; omega⟩ -
              (L - (u : ℝ)) / v) / (W₄ / v) =
            (x ⟨l.1 + 1 + i.1, by dsimp only [n₄] at i ⊢; omega⟩ * v -
              (L - (u : ℝ))) / W₄ := by
        field_simp [hvR.ne', hW₄.ne']
      rw [hnormalize]
      apply (div_le_div_iff_of_pos_right hW₄).2
      norm_num only [Fin.val_mk, Nat.cast_add, Nat.cast_one] at hq' ⊢
      dsimp only [L] at hq' ⊢
      nlinarith
  let z₃₄ := appendCoordinates 1 n₄ (x₃, x₄)
  let z₂₃₄ := appendCoordinates g (1 + n₄) (x₂, z₃₄)
  let z := appendCoordinates n₁ (g + (1 + n₄)) (x₁, z₂₃₄)
  have hz₃₄ : z₃₄ ∈ appendCoordinates 1 n₄ ''
      (affineOrderQSet 1 1 1 a₃ t₃ ×ˢ
        affineOrderQSet n₄ 0 W₄ a₃ t₄) :=
    ⟨(x₃, x₄), ⟨hx₃, hx₄⟩, rfl⟩
  have hz₂₃₄ : z₂₃₄ ∈ appendCoordinates g (1 + n₄) ''
      (affineOrderQSet g g 1 a₂ t₂ ×ˢ
        (appendCoordinates 1 n₄ ''
          (affineOrderQSet 1 1 1 a₃ t₃ ×ˢ
            affineOrderQSet n₄ 0 W₄ a₃ t₄))) :=
    ⟨(x₂, z₃₄), ⟨hx₂, hz₃₄⟩, rfl⟩
  have hz : z ∈ fourBlockSet
      (affineOrderQSet n₁ u W₁ 0 t₁)
      (affineOrderQSet g g 1 a₂ t₂)
      (affineOrderQSet 1 1 1 a₃ t₃)
      (affineOrderQSet n₄ 0 W₄ a₃ t₄) := by
    exact ⟨(x₁, z₂₃₄), ⟨hx₁, hz₂₃₄⟩, rfl⟩
  unfold clusterBlockEnvelope
  dsimp only
  refine ⟨z, hz, ?_⟩
  have hn₁g : n₁ + g = l.1 := by
    dsimp only [n₁]
    exact Nat.sub_add_cancel hgl
  have hl₄ : l.1 + 1 + n₄ = k := by
    dsimp only [n₄]
    omega
  funext i
  simp only [reindexCoordinates_apply, z, z₂₃₄, z₃₄,
    appendCoordinates_apply, finCongr_symm_apply_coe]
  split_ifs with h₁ h₂ h₃
  · dsimp only [x₁]
  · dsimp only [x₂]
    apply congrArg x
    apply Fin.ext
    exact Nat.add_sub_of_le (Nat.le_of_not_gt h₁)
  · dsimp only [x₃]
    apply congrArg x
    apply Fin.ext
    omega
  · dsimp only [x₄]
    apply congrArg x
    apply Fin.ext
    change l.1 + 1 + (i.1 - n₁ - g - 1) = i.1
    omega

private theorem volume_clusterBlockEnvelope_lt_top
    (g k s u v : ℕ) (l : Fin k) (hgl : g ≤ l.1) :
    volume (clusterBlockEnvelope g k s u v l hgl) < ∞ := by
  unfold clusterBlockEnvelope
  dsimp only
  rw [volume_reindexCoordinates_image _
      (measurableSet_fourBlockSet
        (measurableSet_affineOrderQSet ..) (measurableSet_affineOrderQSet ..)
        (measurableSet_affineOrderQSet ..) (measurableSet_affineOrderQSet ..)),
    volume_fourBlockSet
      (measurableSet_affineOrderQSet ..) (measurableSet_affineOrderQSet ..)
      (measurableSet_affineOrderQSet ..) (measurableSet_affineOrderQSet ..)]
  exact ENNReal.mul_lt_top
    (volume_affineOrderQSet_lt_top ..) <| ENNReal.mul_lt_top
      (volume_affineOrderQSet_lt_top ..) <| ENNReal.mul_lt_top
        (volume_affineOrderQSet_lt_top ..) (volume_affineOrderQSet_lt_top ..)

private theorem volume_clusterSlice_le_envelope
    {g k s u v : ℕ} {l : Fin k} (hg : 1 ≤ g) (hgl : g ≤ l.1)
    (hv : 0 < v) (hul : u ≤ l.1 + 1) (huvk : k + 1 ≤ u + v) :
    (volume (clusterSlice g k s u v l)).toReal ≤
      (volume (clusterBlockEnvelope g k s u v l hgl)).toReal := by
  exact ENNReal.toReal_mono
    (volume_clusterBlockEnvelope_lt_top g k s u v l hgl).ne
    (measure_mono
      (fixedCluster_subset_clusterBlockEnvelope hg hgl hv hul huvk))

/-- Exact pre-Abel bound for the clustered region, with every null boundary
slice removed. -/
theorem volume_clusterRegion_le_sum_witnessVolumes
    {g k s u v : ℕ} (hg : 1 ≤ g) (hv : 0 < v) (huvk : k + 1 ≤ u + v) :
    (volume (clusterRegion g k s u v)).toReal ≤
      ∑ l : Fin k, if g ≤ l.1 then
        if u ≤ l.1 + 1 then clusterWitnessVolume g k s u v l else 0
      else 0 := by
  refine (volume_clusterRegion_toReal_le_sum_slices g k s u v).trans ?_
  apply Finset.sum_le_sum
  intro l hl
  by_cases hgl : g ≤ l.1
  · simp only [hgl, if_pos]
    by_cases hul : u ≤ l.1 + 1
    · simp only [hul, if_pos]
      calc
        (volume (clusterSlice g k s u v l)).toReal ≤
            (volume (clusterBlockEnvelope g k s u v l hgl)).toReal :=
          volume_clusterSlice_le_envelope hg hgl hv hul huvk
        _ = clusterWitnessVolume g k s u v l := by
          rw [volume_clusterBlockEnvelope g k s u v l hgl hv hul huvk]
          rfl
    · simp only [hul, if_neg]
      rw [volume_clusterSlice_zero_of_lt hv (Nat.lt_of_not_ge hul)]
      simp
  · simp [hgl]

/-- Lemma 4.3 after the four-block decomposition and Abel summation.  The
only remaining analytic input is the uniform order-statistics estimate from
Lemma 4.1, supplied as `hQ`.  Keeping this implication separate makes the
endpoint cases `n = 0` in the first and fourth blocks explicit. -/
theorem clusterRegion_volume_bound_of_orderQ
    {C : ℝ} (hC : 0 < C)
    (hQ : ∀ (n : ℕ) (a b : ℝ),
      1 ≤ n → 0 ≤ a → 0 ≤ a + b - (n : ℝ) →
      orderQ n a b ≤
        C * (a + 1) * (a + b - (n : ℝ) + 1) ^ 2 / (n : ℝ))
    {g k s u v : ℕ} (hg : 1 ≤ g) (hgk : g + 1 ≤ k)
    (hv : 1 ≤ v) (hkv : k ≤ 10 * v) (huvk : k + 1 ≤ u + v) :
    (volume (clusterRegion g k s u v)).toReal ≤
      (256 * (C + 1) ^ 2 * (u + 1) * (g : ℝ) ^ 2 *
        ((u : ℝ) + v - k) ^ 2 * (s + 1 : ℝ) ^ g /
          ((g.factorial : ℝ) * (v : ℝ) ^ k)) *
        ((Real.exp 4 * (Real.exp 1) ^ 10) * (v : ℝ) ^ (k - g) /
          ((k + 1 - g).factorial : ℝ)) := by
  classical
  let Ls : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter
    (fun l ↦ g ≤ l.1 ∧ u ≤ l.1 + 1)
  let A : ℝ := 256 * (C + 1) ^ 2 * (u + 1) * (g : ℝ) ^ 2 *
    ((u : ℝ) + v - k) ^ 2 * (s + 1 : ℝ) ^ g /
      ((g.factorial : ℝ) * (v : ℝ) ^ k)
  have hv0 : 0 < v := lt_of_lt_of_le Nat.zero_lt_one hv
  have hw : (0 : ℝ) ≤ (u : ℝ) + v - k := by
    have huvkR : (k : ℝ) + 1 ≤ (u : ℝ) + v := by exact_mod_cast huvk
    linarith
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hvol := volume_clusterRegion_le_sum_witnessVolumes
    (g := g) (k := k) (s := s) (u := u) (v := v) hg hv0 huvk
  have hvol' : (volume (clusterRegion g k s u v)).toReal ≤
      ∑ l ∈ Ls, clusterWitnessVolume g k s u v l := by
    refine hvol.trans_eq ?_
    simp only [Ls, Finset.sum_filter, Finset.mem_univ, true_and]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hgl : g ≤ l.1 <;> by_cases hul : u ≤ l.1 + 1 <;>
      simp [hgl, hul]
  calc
    (volume (clusterRegion g k s u v)).toReal ≤
        ∑ l ∈ Ls, clusterWitnessVolume g k s u v l := hvol'
    _ ≤ ∑ l ∈ Ls, A * clusterRawSummand g k u v l := by
      apply Finset.sum_le_sum
      intro l hl
      have hl' := (Finset.mem_filter.mp hl).2
      exact clusterWitnessVolume_le_raw hC hQ hg hl'.1 hv0 hl'.2 huvk
    _ = A * (∑ l ∈ Ls, clusterAbelSummand g k u v l) /
          ((k + 1 - g).factorial : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro l hl
      have hgl := (Finset.mem_filter.mp hl).2.1
      rw [clusterRawSummand_eq l hgl]
      ring
    _ ≤ A * ((Real.exp 4 * (Real.exp 1) ^ 10) *
          (v : ℝ) ^ (k - g)) / ((k + 1 - g).factorial : ℝ) := by
      gcongr
      simpa only [Ls] using sum_clusterAbelSummand_le hgk huvk hv hkv
    _ = (256 * (C + 1) ^ 2 * (u + 1) * (g : ℝ) ^ 2 *
          ((u : ℝ) + v - k) ^ 2 * (s + 1 : ℝ) ^ g /
            ((g.factorial : ℝ) * (v : ℝ) ^ k)) *
          ((Real.exp 4 * (Real.exp 1) ^ 10) * (v : ℝ) ^ (k - g) /
            ((k + 1 - g).factorial : ℝ)) := by
      dsimp only [A]
      ring

private theorem factorial_power_ratio_bound
    {g k v : ℕ} (hg : 1 ≤ g) (hgk : g + 1 ≤ k)
    (hv : 1 ≤ v) (hkv : k ≤ 10 * v) :
    (v : ℝ) ^ (k - g) /
        ((v : ℝ) ^ k * ((k + 1 - g).factorial : ℝ)) ≤
      2 * (10 : ℝ) ^ g / ((k + 1).factorial : ℝ) := by
  have factorial_ratio_nat : k * k.factorial ≤
      k ^ g * (k + 1 - g).factorial := by
    induction g with
    | zero => omega
    | succ g ih =>
        by_cases hg0 : g = 0
        · subst g
          simp
        · have hgpos : 1 ≤ g := by omega
          have hgk' : g + 1 ≤ k := by omega
          have hold := ih hgpos hgk'
          calc
            k * k.factorial ≤ k ^ g * (k + 1 - g).factorial := hold
            _ = k ^ g * ((k - g + 1) * (k - g).factorial) := by
              rw [show k + 1 - g = k - g + 1 by omega, Nat.factorial_succ]
            _ ≤ k ^ g * (k * (k - g).factorial) := by
              gcongr
              omega
            _ = k ^ (g + 1) * (k + 1 - (g + 1)).factorial := by
              rw [pow_succ, show k + 1 - (g + 1) = k - g by omega]
              ring
  have hfac : (k : ℝ) * (k.factorial : ℝ) ≤
      (k : ℝ) ^ g * ((k + 1 - g).factorial : ℝ) := by
    exact_mod_cast factorial_ratio_nat
  have hkR : (1 : ℝ) ≤ k := by
    exact_mod_cast (by omega : 1 ≤ k)
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hbase : (k : ℝ) ≤ 10 * v := by exact_mod_cast hkv
  have hpow : (k : ℝ) ^ g ≤ (10 : ℝ) ^ g * (v : ℝ) ^ g := by
    calc
      (k : ℝ) ^ g ≤ (10 * (v : ℝ)) ^ g := by gcongr
      _ = (10 : ℝ) ^ g * (v : ℝ) ^ g := by rw [mul_pow]
  have hvpow : (v : ℝ) ^ k =
      (v : ℝ) ^ (k - g) * (v : ℝ) ^ g := by
    rw [← pow_add]
    congr 1
    omega
  have hden₁ : 0 < (v : ℝ) ^ k * ((k + 1 - g).factorial : ℝ) := by
    positivity
  have hden₂ : 0 < ((k + 1).factorial : ℝ) := by positivity
  apply (div_le_div_iff₀ hden₁ hden₂).2
  rw [Nat.factorial_succ]
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    (v : ℝ) ^ (k - g) *
        (((k : ℝ) + 1) * (k.factorial : ℝ)) ≤
        (v : ℝ) ^ (k - g) *
          ((2 * k) * (k.factorial : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ (v : ℝ) ^ (k - g) *
        (2 * ((k : ℝ) ^ g * ((k + 1 - g).factorial : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      convert mul_le_mul_of_nonneg_left hfac
        (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;> ring
    _ ≤ (v : ℝ) ^ (k - g) *
        (2 * ((10 : ℝ) ^ g * (v : ℝ) ^ g *
          ((k + 1 - g).factorial : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = 2 * (10 : ℝ) ^ g *
        ((v : ℝ) ^ k * ((k + 1 - g).factorial : ℝ)) := by
      rw [hvpow]
      ring

/-- Ford's Lemma 4.3 with its published scale, conditional only on the
uniform `Q` estimate of Lemma 4.1. -/
theorem clusterRegion_volume_scale_bound_of_orderQ
    {C : ℝ} (hC : 0 < C)
    (hQ : ∀ (n : ℕ) (a b : ℝ),
      1 ≤ n → 0 ≤ a → 0 ≤ a + b - (n : ℝ) →
      orderQ n a b ≤
        C * (a + 1) * (a + b - (n : ℝ) + 1) ^ 2 / (n : ℝ))
    {g k s u v : ℕ} (hg : 1 ≤ g) (hgk : g + 1 ≤ k)
    (hv : 1 ≤ v) (hkv : k ≤ 10 * v) (huvk : k + 1 ≤ u + v) :
    (volume (clusterRegion g k s u v)).toReal ≤
      (512 * (Real.exp 4 * (Real.exp 1) ^ 10) * (C + 1) ^ 2) *
        clusterVolumeScale g k s u v := by
  have hraw := clusterRegion_volume_bound_of_orderQ
    (g := g) (k := k) (s := s) (u := u) (v := v)
    hC hQ hg hgk hv hkv huvk
  have hratio := factorial_power_ratio_bound hg hgk hv hkv
  have hbase : 0 ≤ 256 * (C + 1) ^ 2 * (u + 1) * (g : ℝ) ^ 2 *
      ((u : ℝ) + v - k) ^ 2 * (s + 1 : ℝ) ^ g /
        (g.factorial : ℝ) := by positivity
  calc
    (volume (clusterRegion g k s u v)).toReal ≤ _ := hraw
    _ = (256 * (C + 1) ^ 2 * (u + 1) * (g : ℝ) ^ 2 *
          ((u : ℝ) + v - k) ^ 2 * (s + 1 : ℝ) ^ g /
            (g.factorial : ℝ)) *
        (Real.exp 4 * (Real.exp 1) ^ 10) *
        ((v : ℝ) ^ (k - g) /
          ((v : ℝ) ^ k * ((k + 1 - g).factorial : ℝ))) := by ring
    _ ≤ (256 * (C + 1) ^ 2 * (u + 1) * (g : ℝ) ^ 2 *
          ((u : ℝ) + v - k) ^ 2 * (s + 1 : ℝ) ^ g /
            (g.factorial : ℝ)) *
        (Real.exp 4 * (Real.exp 1) ^ 10) *
        (2 * (10 : ℝ) ^ g / ((k + 1).factorial : ℝ)) := by
      gcongr
    _ = (512 * (Real.exp 4 * (Real.exp 1) ^ 10) * (C + 1) ^ 2) *
        clusterVolumeScale g k s u v := by
      unfold clusterVolumeScale
      rw [mul_pow]
      ring

/-! ## The prefix-sum region in Lemma 4.4 -/

/-- The left side of Ford's defining inequalities for `T(k,v,γ)`. -/
noncomputable def prefixExpSum {k : ℕ} (v : ℕ) (x : Fin k → ℝ)
    (j : Fin k) : ℝ :=
  ∑ i ∈ Finset.Iic j, (2 : ℝ) ^ ((v : ℝ) * x i)

/-- Ford's region `T(k,v,γ)` from Lemma 4.4. -/
noncomputable def orderStatisticRegion (k v γ : ℕ) : Set (Fin k → ℝ) :=
  {x | x ∈ orderedSimplex k 0 1 ∧
    ∀ j : Fin k, (2 : ℝ) ^ ((j.1 + 1 : ℝ) - γ) ≤ prefixExpSum v x j}

/-- Source-name alias for Ford's `T(k,v,γ)`. -/
noncomputable abbrev fordT := orderStatisticRegion

/-- The displacement of an order statistic from the affine barrier used in
the minimum alternative (4.6) of Ford's proof. -/
noncomputable def fordDefect {k : ℕ} (v γ : ℕ) (x : Fin k → ℝ)
    (i : Fin k) : ℝ :=
  x i - (((i.1 + 1 : ℕ) : ℝ) - γ) / v

/-- Exact finite-dimensional dichotomy preceding (4.6).  If a point of
`T(k,v,γ)` misses the affine `Q`-barrier with parameter `γ+r`, a
minimizing defect lies in one of the half-open integer strips indexed by an
integer `h ≥ r+1`. -/
theorem fordT_orderQ_or_defectBucket
    {k v γ r : ℕ} (hv : 0 < v) {x : Fin k → ℝ}
    (hx : x ∈ fordT k v γ) :
    x ∈ orderQSet k (γ + r) v ∨
      ∃ h : ℕ, r + 1 ≤ h ∧ ∃ l : Fin k,
        (∀ i : Fin k, fordDefect v γ x l ≤ fordDefect v γ x i) ∧
        (-((h : ℝ) / v) ≤ fordDefect v γ x l) ∧
        (fordDefect v γ x l < (1 - (h : ℝ)) / v) := by
  classical
  by_cases hQx : x ∈ orderQSet k (γ + r) v
  · exact Or.inl hQx
  · right
    have hbarrier : ¬ ∀ i : Fin k,
        ((((i.1 + 1 : ℕ) : ℝ) - (γ + r : ℕ)) / v) ≤ x i := by
      intro h
      apply hQx
      refine ⟨hx.1, ?_⟩
      intro i
      norm_num only [Nat.cast_add, Nat.cast_one] at h ⊢
      exact h i
    push_neg at hbarrier
    obtain ⟨j, hj⟩ := hbarrier
    obtain ⟨l, -, hl⟩ := Finset.exists_min_image
      (Finset.univ : Finset (Fin k)) (fordDefect v γ x) ⟨j, by simp⟩
    let d : ℝ := fordDefect v γ x l
    let y : ℝ := -(v : ℝ) * d
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv
    have hjdef : fordDefect v γ x j < -((r : ℝ) / v) := by
      unfold fordDefect
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hcast : (((γ + r : ℕ) : ℝ)) = (γ : ℝ) + r := by norm_num
      rw [hcast] at hj
      norm_num only [Nat.cast_add, Nat.cast_one] at hj
      apply (sub_lt_iff_lt_add).2
      calc
        x j < (((j.1 : ℝ) + 1 - ((γ : ℝ) + r)) / v) := hj
        _ = -((r : ℝ) / v) + ((j.1 : ℝ) + 1 - γ) / v := by ring
    have hldef : d ≤ fordDefect v γ x j := by
      dsimp only [d]
      exact hl j (by simp)
    have hyr : (r : ℝ) < y := by
      dsimp only [y]
      have := hldef.trans_lt hjdef
      have this' : d < -(r : ℝ) / v := by simpa only [neg_div] using this
      have hmul := (lt_div_iff₀ hvR).1 this'
      nlinarith
    have hy0 : 0 ≤ y := (Nat.cast_nonneg r).trans hyr.le
    let h : ℕ := ⌈y⌉₊
    have hrh : r + 1 ≤ h := by
      dsimp only [h]
      have : r < ⌈y⌉₊ := Nat.lt_ceil.mpr hyr
      omega
    refine ⟨h, hrh, l, ?_, ?_, ?_⟩
    · intro i
      exact hl i (by simp)
    · have hyh : y ≤ (h : ℝ) := by
        dsimp only [h]
        exact Nat.le_ceil y
      dsimp only [y, d] at hyh
      rw [show -((h : ℝ) / v) = (-(h : ℝ)) / v by ring]
      apply (div_le_iff₀ hvR).2
      nlinarith
    · have hhy : (h : ℝ) < y + 1 := by
        dsimp only [h]
        exact Nat.ceil_lt_add_one hy0
      dsimp only [y, d] at hhy
      apply (lt_div_iff₀ hvR).2
      nlinarith

/-- The conclusion (4.7), together with a defect strip from (4.6), is
membership in the clustered region used by Lemma 4.3.  Its cluster width is
`2^m`; enlarging the exact slack `2m-h` to `2m` gives Ford's convenient
summable majorant. -/
theorem defectBucket_extraction_mem_clusterRegion
    {k v γ h m : ℕ} (hv : 0 < v) (hh : 6 ≤ h) {x : Fin k → ℝ}
    (hx : x ∈ fordT k v γ) {l : Fin k}
    (hmin : ∀ i : Fin k, fordDefect v γ x l ≤ fordDefect v γ x i)
    (hlower : -((h : ℝ) / v) ≤ fordDefect v γ x l)
    (hupper : fordDefect v γ x l < (1 - (h : ℝ)) / v)
    (hmh : h - 3 ≤ m) (hml : 2 ^ m ≤ l.1)
    (hextract : (((l.1 : ℝ) + 1 - γ - 2 * m) / v) ≤
      x ⟨l.1 - 2 ^ m, (Nat.sub_le _ _).trans_lt l.isLt⟩) :
    x ∈ clusterRegion (2 ^ m) k (2 * m) (γ + h) v := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hQx : x ∈ orderQSet k (((γ + h : ℕ) : ℝ)) v := by
    refine ⟨hx.1, ?_⟩
    intro i
    have hi := hlower.trans (hmin i)
    unfold fordDefect at hi
    norm_num only [Nat.cast_add, Nat.cast_one] at hi ⊢
    apply (div_le_iff₀ hvR).2
    have hi' := (div_le_iff₀ hvR).1 <|
      show (-((h : ℝ))) / v ≤
          x i - (((i.1 : ℝ) + 1 - γ) / v) by
        simpa only [neg_div] using hi
    rw [show (x i - (((i.1 : ℝ) + 1 - γ) / v)) * v =
        x i * v - ((i.1 : ℝ) + 1 - γ) by field_simp] at hi'
    nlinarith
  refine ⟨hQx, l, hml, ?_, ?_, ?_⟩
  · unfold fordDefect at hlower
    norm_num only [Nat.cast_add, Nat.cast_one] at hlower ⊢
    apply (div_le_iff₀ hvR).2
    have hlower' := (div_le_iff₀ hvR).1 <|
      show (-((h : ℝ))) / v ≤
          x l - (((l.1 : ℝ) + 1 - γ) / v) by
        simpa only [neg_div] using hlower
    rw [show (x l - (((l.1 : ℝ) + 1 - γ) / v)) * v =
        x l * v - ((l.1 : ℝ) + 1 - γ) by field_simp] at hlower'
    nlinarith
  · exact le_of_lt <| by
      unfold fordDefect at hupper
      norm_num only [Nat.cast_add, Nat.cast_one] at hupper ⊢
      apply (lt_div_iff₀ hvR).2
      have hupper' := (lt_div_iff₀ hvR).1 hupper
      rw [show (x l - (((l.1 : ℝ) + 1 - γ) / v)) * v =
          x l * v - ((l.1 : ℝ) + 1 - γ) by field_simp] at hupper'
      nlinarith
  · calc
      (((l.1 : ℝ) + 1 - (γ + h : ℕ) - (2 * m : ℕ)) / v) ≤
          (((l.1 : ℝ) + 1 - γ - 2 * (m : ℝ)) / v) := by
        apply div_le_div_of_nonneg_right _ hvR.le
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        linarith
      _ ≤ x ⟨l.1 - 2 ^ m, (Nat.sub_le _ _).trans_lt l.isLt⟩ := hextract

private lemma cluster_nat_le_two_pow (m : ℕ) : m ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2 ^ m :=
        Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
      omega

/-- The finite cluster cover used for the second alternative in Lemma 4.4.
The extraction inequalities force `h ≤ k+3` and `m ≤ k`, so no
infinite-union limiting argument is needed. -/
def fordClusterCover (k v γ r : ℕ) : Set (Fin k → ℝ) :=
  ⋃ h : Fin (k + 4), if r + 1 ≤ h.1 then
    ⋃ m : Fin (k + 1),
      if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
        clusterRegion (2 ^ m.1) k (2 * m.1) (γ + h.1) v
      else ∅
    else ∅

theorem measurableSet_fordClusterCover (k v γ r : ℕ) :
    MeasurableSet (fordClusterCover k v γ r) := by
  unfold fordClusterCover
  apply MeasurableSet.iUnion
  intro h
  split_ifs
  · apply MeasurableSet.iUnion
    intro m
    split_ifs
    · exact measurableSet_clusterRegion ..
    · exact MeasurableSet.empty
  · exact MeasurableSet.empty

private theorem volume_clusterRegion_lt_top (g k s u v : ℕ) :
    volume (clusterRegion g k s u v) < ∞ :=
  (volume_clusterRegion_le_orderQSet g k s u v).trans_lt
    (volume_orderQSet_lt_top k u v)

/-- Finite subadditivity for Ford's cluster cover, already converted to
ordinary real volumes for subsequent use of Lemma 4.3. -/
theorem volume_fordClusterCover_toReal_le_sum (k v γ r : ℕ) :
    (volume (fordClusterCover k v γ r)).toReal ≤
      ∑ h : Fin (k + 4), if r + 1 ≤ h.1 then
        ∑ m : Fin (k + 1),
          if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
            (volume (clusterRegion (2 ^ m.1) k (2 * m.1)
              (γ + h.1) v)).toReal
          else 0
        else 0 := by
  have hmeasure : volume (fordClusterCover k v γ r) ≤
      ∑ h : Fin (k + 4), if r + 1 ≤ h.1 then
        ∑ m : Fin (k + 1),
          if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
            volume (clusterRegion (2 ^ m.1) k (2 * m.1)
              (γ + h.1) v)
          else 0
        else 0 := by
    unfold fordClusterCover
    calc
      volume (⋃ h : Fin (k + 4), if r + 1 ≤ h.1 then
          ⋃ m : Fin (k + 1),
            if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
              clusterRegion (2 ^ m.1) k (2 * m.1) (γ + h.1) v
            else ∅
          else ∅) ≤
          ∑ h : Fin (k + 4), volume
            (if r + 1 ≤ h.1 then
              ⋃ m : Fin (k + 1),
                if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
                  clusterRegion (2 ^ m.1) k (2 * m.1) (γ + h.1) v
                else ∅
              else ∅) := measure_iUnion_fintype_le volume _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro h hh
        by_cases hrh : r + 1 ≤ h.1
        · simp only [hrh, if_pos]
          refine (measure_iUnion_fintype_le
            (volume : Measure (Fin k → ℝ))
            (fun m : Fin (k + 1) ↦
              if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
                clusterRegion (2 ^ m.1) k (2 * m.1) (γ + h.1) v
              else ∅)).trans_eq ?_
          apply Finset.sum_congr rfl
          intro m hm
          split_ifs <;> simp
        · simp [hrh]
  have hsum_ne : (∑ h : Fin (k + 4), if r + 1 ≤ h.1 then
      ∑ m : Fin (k + 1),
        if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
          volume (clusterRegion (2 ^ m.1) k (2 * m.1)
            (γ + h.1) v)
        else 0
      else 0) ≠ ∞ := by
    apply (ENNReal.sum_lt_top.mpr _).ne
    intro h hh
    split_ifs
    · apply ENNReal.sum_lt_top.mpr
      intro m hm
      split_ifs
      · exact volume_clusterRegion_lt_top ..
      · simp
    · simp
  calc
    (volume (fordClusterCover k v γ r)).toReal ≤
        (∑ h : Fin (k + 4), if r + 1 ≤ h.1 then
          ∑ m : Fin (k + 1),
            if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
              volume (clusterRegion (2 ^ m.1) k (2 * m.1)
                (γ + h.1) v)
            else 0
          else 0).toReal := ENNReal.toReal_mono hsum_ne hmeasure
    _ = _ := by
      rw [ENNReal.toReal_sum (fun h _ ↦ by
        split_ifs
        · exact (ENNReal.sum_lt_top.mpr fun m hm ↦ by
            split_ifs
            · exact volume_clusterRegion_lt_top ..
            · simp).ne
        · simp)]
      apply Finset.sum_congr rfl
      intro h hh
      split_ifs
      · rw [ENNReal.toReal_sum (fun m _ ↦ by
          split_ifs
          · exact (volume_clusterRegion_lt_top ..).ne
          · simp)]
        apply Finset.sum_congr rfl
        intro m hm
        split_ifs <;> simp
      · simp

theorem ukPrefixExpSum_eq_prefixExpSum {k : ℕ} (v : ℕ)
    (x : Fin k → ℝ) (j : Fin k) :
    ukPrefixExpSum v x j = prefixExpSum v x j := by
  rfl

/-- The independent integral layer and the cluster layer use the same
prefix-sum region. -/
theorem ukPrefixRegion_eq_fordT (k v gamma : ℕ) :
    ukPrefixRegion k v gamma = fordT k v gamma := by
  ext x
  simp only [ukPrefixRegion, orderStatisticRegion, mem_inter_iff, mem_iInter,
    mem_ofPred_eq, ukPrefixExpSum_eq_prefixExpSum]

theorem measurable_prefixExpSum {k v : ℕ} (j : Fin k) :
    Measurable (fun x : Fin k → ℝ ↦ prefixExpSum v x j) := by
  unfold prefixExpSum
  fun_prop

theorem measurableSet_orderStatisticRegion (k v γ : ℕ) :
    MeasurableSet (orderStatisticRegion k v γ) := by
  unfold orderStatisticRegion
  apply (measurableSet_orderedSimplex k 0 1).inter
  show MeasurableSet ({x : Fin k → ℝ |
    ∀ j : Fin k, (2 : ℝ) ^ ((j.1 + 1 : ℝ) - γ) ≤ prefixExpSum v x j} : Set _)
  rw [show {x : Fin k → ℝ |
      ∀ j : Fin k, (2 : ℝ) ^ ((j.1 + 1 : ℝ) - γ) ≤ prefixExpSum v x j} =
      ⋂ j : Fin k, {x : Fin k → ℝ |
        (2 : ℝ) ^ ((j.1 + 1 : ℝ) - γ) ≤ prefixExpSum v x j} by
    ext x
    simp]
  exact MeasurableSet.iInter fun j ↦
    measurableSet_le measurable_const (measurable_prefixExpSum (v := v) j)

theorem measurableSet_fordT (k v γ : ℕ) :
    MeasurableSet (fordT k v γ) :=
  measurableSet_orderStatisticRegion k v γ

theorem orderStatisticRegion_subset_orderedSimplex (k v γ : ℕ) :
    orderStatisticRegion k v γ ⊆ orderedSimplex k 0 1 := by
  intro x hx
  exact hx.1

theorem volume_fordT_le_orderedSimplex (k v γ : ℕ) :
    volume (fordT k v γ) ≤ volume (orderedSimplex k 0 1) :=
  measure_mono (orderStatisticRegion_subset_orderedSimplex k v γ)

/-- Ford's integer `b = k-v`. -/
def orderStatisticExcess (k v : ℕ) : ℤ := k - v

/-- The piecewise factor `Y` in Ford's Lemma 4.4. -/
noncomputable def orderStatisticY (k v γ : ℕ) : ℝ :=
  let b := orderStatisticExcess k v
  if (γ : ℤ) + 5 ≤ b then (b : ℝ)
  else (((γ : ℤ) + 5 - b : ℤ) : ℝ) ^ 2 * (γ + 1 : ℝ)

/-- The double-exponential denominator `2^(2^(b-γ))` in Lemma 4.4,
where `b = k-v`.  Both powers are real powers, so this remains positive
when `b-γ` is negative. -/
noncomputable def orderStatisticDoubleExp (k v γ : ℕ) : ℝ :=
  (2 : ℝ) ^ ((2 : ℝ) ^
    (((orderStatisticExcess k v - (γ : ℤ) : ℤ) : ℝ)))

theorem orderStatisticDoubleExp_pos (k v γ : ℕ) :
    0 < orderStatisticDoubleExp k v γ := by
  unfold orderStatisticDoubleExp
  positivity

/-- The parameter-dependent factor on the right of Ford's Lemma 4.4.
The theorem's absolute implied constant is deliberately not included. -/
noncomputable def fordTVolumeScale (k v γ : ℕ) : ℝ :=
  orderStatisticY k v γ /
    (orderStatisticDoubleExp k v γ * ((k + 1).factorial : ℝ))

theorem orderStatisticY_pos {k v γ : ℕ} (hk : 1 ≤ k) :
    0 < orderStatisticY k v γ := by
  by_cases h : (γ : ℤ) + 5 ≤ orderStatisticExcess k v
  · simp only [orderStatisticY, h, if_pos]
    exact_mod_cast (lt_of_lt_of_le (by omega : (0 : ℤ) < (γ : ℤ) + 5) h)
  · have hd : (0 : ℤ) < (γ : ℤ) + 5 - orderStatisticExcess k v := by omega
    have hdR : (0 : ℝ) < (((γ : ℤ) + 5 - orderStatisticExcess k v : ℤ) : ℝ) := by
      exact_mod_cast hd
    have hγ : (0 : ℝ) < (γ : ℝ) + 1 := by positivity
    simp only [orderStatisticY, h, if_neg]
    exact mul_pos (sq_pos_of_pos hdR) hγ

theorem fordTVolumeScale_pos {k v γ : ℕ} (hk : 1 ≤ k) :
    0 < fordTVolumeScale k v γ := by
  unfold fordTVolumeScale
  exact div_pos (orderStatisticY_pos hk) <|
    mul_pos (orderStatisticDoubleExp_pos k v γ) <| by positivity

/-! ## The two pieces in the proof of Lemma 4.4 -/

/-- Ford's integer `r = max(5,b-γ)`, represented without a signed
intermediate because the maximum is positive. -/
def orderStatisticR (k v γ : ℕ) : ℕ := max 5 (k - (v + γ))

/-- The first alternative (4.5), intersected with `T`.  Non-strict
barriers are used so that the complementary minimum strip has no missing
boundary; in the large-excess case the extra boundary is null. -/
def fordGoodPart (k v γ : ℕ) : Set (Fin k → ℝ) :=
  fordT k v γ ∩
    orderQSet k (((γ + orderStatisticR k v γ : ℕ) : ℝ)) v

theorem measurableSet_fordGoodPart (k v γ : ℕ) :
    MeasurableSet (fordGoodPart k v γ) :=
  (measurableSet_fordT k v γ).inter (measurableSet_orderQSet ..)

theorem volume_fordGoodPart_le_orderQSet (k v γ : ℕ) :
    volume (fordGoodPart k v γ) ≤
      volume (orderQSet k (((γ + orderStatisticR k v γ : ℕ) : ℝ)) v) :=
  measure_mono inter_subset_right

/-- The exact finite cover behind Ford's decomposition `T = V₁ ∪ V₂`.
The difficult dyadic extraction is `uk_prefix_cluster_extraction`; all
remaining work here identifies its conclusion with the regions of Lemma
4.3 and records the forced finite ranges of `h` and `m`. -/
theorem fordT_subset_goodPart_union_clusterCover
    {k v γ : ℕ} (hv : 0 < v) :
    fordT k v γ ⊆ fordGoodPart k v γ ∪
      fordClusterCover k v γ (orderStatisticR k v γ) := by
  intro x hx
  rcases fordT_orderQ_or_defectBucket
      (r := orderStatisticR k v γ) hv hx with hgood | hbad
  · apply Or.inl
    refine ⟨hx, ?_⟩
    convert hgood using 1 <;> norm_num
  · rcases hbad with ⟨h, hrh, l, hmin, hlower, hupper⟩
    have hr5 : 5 ≤ orderStatisticR k v γ := by
      unfold orderStatisticR
      omega
    have hh : 6 ≤ h := by omega
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv
    have hl : x l < (((l.1 : ℝ) + 2 - γ - h) / v) := by
      unfold fordDefect at hupper
      norm_num only [Nat.cast_add, Nat.cast_one] at hupper ⊢
      apply (lt_div_iff₀ hvR).2
      have hupper' := (lt_div_iff₀ hvR).1 hupper
      rw [show (x l - (((l.1 : ℝ) + 1 - γ) / v)) * v =
          x l * v - ((l.1 : ℝ) + 1 - γ) by field_simp] at hupper'
      nlinarith
    have hp : (2 : ℝ) ^ (((l.1 : ℝ) + 1) - γ) ≤
        ukPrefixExpSum v x l := by
      rw [ukPrefixExpSum_eq_prefixExpSum]
      exact hx.2 l
    obtain ⟨m, hmh, hml, hextract⟩ :=
      uk_prefix_cluster_extraction hv hh hx.1.2 hl hp
    have hcluster := defectBucket_extraction_mem_clusterRegion
      hv hh hx hmin hlower hupper hmh hml hextract
    have hmK : m < k :=
      (cluster_nat_le_two_pow m).trans_lt (hml.trans_lt l.isLt)
    have hhBound : h < k + 4 := by omega
    have hmBound : m < k + 1 := by omega
    let hf : Fin (k + 4) := ⟨h, hhBound⟩
    let mf : Fin (k + 1) := ⟨m, hmBound⟩
    apply Or.inr
    unfold fordClusterCover
    refine mem_iUnion.2 ⟨hf, ?_⟩
    rw [if_pos (show orderStatisticR k v γ + 1 ≤ hf.1 by
      dsimp only [hf]; exact hrh)]
    refine mem_iUnion.2 ⟨mf, ?_⟩
    rw [if_pos (show hf.1 - 3 ≤ mf.1 ∧ 2 ^ mf.1 + 1 ≤ k by
      dsimp only [hf, mf]; constructor
      · exact hmh
      · omega)]
    exact hcluster

theorem fordGoodPart_subset_orderedSimplex (k v γ : ℕ) :
    fordGoodPart k v γ ⊆ orderedSimplex k 0 1 := by
  intro x hx
  exact hx.1.1

theorem fordClusterCover_subset_orderedSimplex (k v γ r : ℕ) :
    fordClusterCover k v γ r ⊆ orderedSimplex k 0 1 := by
  intro x hx
  unfold fordClusterCover at hx
  rcases mem_iUnion.1 hx with ⟨h, hh⟩
  by_cases hrh : r + 1 ≤ h.1
  · rw [if_pos hrh] at hh
    rcases mem_iUnion.1 hh with ⟨m, hm⟩
    by_cases hhm : h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k
    · rw [if_pos hhm] at hm
      exact hm.1.1
    · simp only [if_neg hhm, Set.mem_empty_iff_false] at hm
  · simp [hrh] at hh

private theorem volume_orderedSimplex_zero_one_lt_top (k : ℕ) :
    volume (orderedSimplex k 0 1) < ∞ := by
  rw [volume_orderedSimplex k (by norm_num : (0 : ℝ) ≤ 1)]
  simp

/-- Measure subadditivity for the exact `V₁ ∪ V₂` cover. -/
theorem volume_fordT_toReal_le_goodPart_add_clusterCover
    {k v γ : ℕ} (hv : 0 < v) :
    (volume (fordT k v γ)).toReal ≤
      (volume (fordGoodPart k v γ)).toReal +
        (volume (fordClusterCover k v γ
          (orderStatisticR k v γ))).toReal := by
  have hgoodtop : volume (fordGoodPart k v γ) < ∞ :=
    (measure_mono (fordGoodPart_subset_orderedSimplex k v γ)).trans_lt
      (volume_orderedSimplex_zero_one_lt_top k)
  have hcovertop : volume (fordClusterCover k v γ
      (orderStatisticR k v γ)) < ∞ :=
    (measure_mono (fordClusterCover_subset_orderedSimplex k v γ _)).trans_lt
      (volume_orderedSimplex_zero_one_lt_top k)
  have hmeasure : volume (fordT k v γ) ≤
      volume (fordGoodPart k v γ) +
        volume (fordClusterCover k v γ (orderStatisticR k v γ)) :=
    (measure_mono (fordT_subset_goodPart_union_clusterCover hv)).trans
      (measure_union_le _ _)
  calc
    (volume (fordT k v γ)).toReal ≤
        (volume (fordGoodPart k v γ) +
          volume (fordClusterCover k v γ
            (orderStatisticR k v γ))).toReal :=
      ENNReal.toReal_mono (ENNReal.add_lt_top.2 ⟨hgoodtop, hcovertop⟩).ne hmeasure
    _ = _ := ENNReal.toReal_add hgoodtop.ne hcovertop.ne

/-- In the branch `b ≥ γ+5`, the first alternative forces the last
coordinate to equal one and hence has zero volume. -/
theorem volume_fordGoodPart_zero
    {k v γ : ℕ} (hk : 1 ≤ k) (hv : 0 < v)
    (hlarge : v + γ + 5 ≤ k) :
    volume (fordGoodPart k v γ) = 0 := by
  let i : Fin k := ⟨k - 1, by omega⟩
  have hr : orderStatisticR k v γ = k - (v + γ) := by
    unfold orderStatisticR
    rw [max_eq_right]
    omega
  have hsum : v + γ + orderStatisticR k v γ = k := by
    rw [hr]
    omega
  have hsub : fordGoodPart k v γ ⊆ {x : Fin k → ℝ | x i = 1} := by
    intro x hx
    have hlow := hx.2.2 i
    have hupp := (hx.2.1.1 i).2
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv
    have hi : i.1 + 1 = k := by dsimp only [i]; omega
    have hsumR : (v : ℝ) + γ + orderStatisticR k v γ = k := by
      exact_mod_cast hsum
    apply le_antisymm hupp
    calc
      (1 : ℝ) = (((i.1 : ℝ) + 1 -
          (γ + orderStatisticR k v γ : ℕ)) / v) := by
        symm
        apply (div_eq_one_iff_eq hvR.ne').2
        have hiR : (i.1 : ℝ) + 1 = k := by exact_mod_cast hi
        norm_num only [Nat.cast_add, Nat.cast_one] at hsumR ⊢
        linarith
      _ ≤ x i := hlow
  apply measure_mono_null hsub
  simpa only [MeasureTheory.volume_pi] using
    (Measure.pi_hyperplane (fun _ : Fin k ↦ (volume : Measure ℝ)) i 1)

/-- The `Q`-part of Lemma 4.4, conditional only on Lemma 4.1. -/
theorem fordGoodPart_volume_bound_of_orderQ
    {C : ℝ} (hC : 0 < C)
    (hQ : ∀ (n : ℕ) (a b : ℝ),
      1 ≤ n → 0 ≤ a → 0 ≤ a + b - (n : ℝ) →
      orderQ n a b ≤
        C * (a + 1) * (a + b - (n : ℝ) + 1) ^ 2 / (n : ℝ))
    {k v γ : ℕ} (hk : 1 ≤ k) :
    (volume (fordGoodPart k v γ)).toReal ≤
      2 * C * ((γ + orderStatisticR k v γ : ℕ) + 1 : ℕ) *
        (((γ + orderStatisticR k v γ : ℕ) : ℝ) + v - k + 1) ^ 2 /
        ((k + 1).factorial : ℝ) := by
  let u := γ + orderStatisticR k v γ
  have hu : 0 ≤ (u : ℝ) := by positivity
  have huk : k ≤ u + v := by
    dsimp only [u, orderStatisticR]
    omega
  have hw : 0 ≤ (u : ℝ) + v - k := by
    apply sub_nonneg.mpr
    exact_mod_cast huk
  have hQ' := hQ k u v hk hu hw
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  calc
    (volume (fordGoodPart k v γ)).toReal ≤
        (volume (orderQSet k u v)).toReal := by
      exact ENNReal.toReal_mono (volume_orderQSet_lt_top k u v).ne
        (volume_fordGoodPart_le_orderQSet k v γ)
    _ = orderQ k u v / (k.factorial : ℝ) := volume_orderQSet_eq ..
    _ ≤ (C * (u + 1) * ((u : ℝ) + v - k + 1) ^ 2 / k) /
          (k.factorial : ℝ) := by gcongr
    _ ≤ 2 * C * (u + 1) * ((u : ℝ) + v - k + 1) ^ 2 /
          ((k + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hC0 : 0 ≤ C := hC.le
      have hu1 : 0 ≤ (u : ℝ) + 1 := by positivity
      have hw1 : 0 ≤ ((u : ℝ) + v - k + 1) ^ 2 := sq_nonneg _
      field_simp
      nlinarith
    _ = 2 * C * ((γ + orderStatisticR k v γ : ℕ) + 1 : ℕ) *
          (((γ + orderStatisticR k v γ : ℕ) : ℝ) + v - k + 1) ^ 2 /
          ((k + 1).factorial : ℝ) := by
      dsimp only [u]
      norm_num

/-! ## The factorial decay in the cluster parameter -/

private lemma cluster_two_mul_le_pow {m : ℕ} (hm : 4 ≤ m) :
    2 * m ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [pow_succ]
      have hp : 2 ≤ 2 ^ m := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

private lemma cluster_strong_linear_le_pow {m : ℕ} (hm : 20 ≤ m) :
    1536 * (10 * (2 * m + 1)) ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [pow_succ]
      have hp : 30720 ≤ 2 ^ m := by
        calc 30720 ≤ 2 ^ 20 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega

private lemma cluster_factorialCoefficient_large {m : ℕ} (hm : 20 ≤ m) :
    (((2 ^ m : ℕ) : ℝ) ^ 2 *
        (10 * (2 * m + 1 : ℕ) : ℕ) ^ (2 ^ m) /
          (((2 ^ m).factorial : ℕ) : ℝ)) ≤
      1 / (256 : ℝ) ^ (2 ^ m) := by
  let g : ℕ := 2 ^ m
  let A : ℕ := 10 * (2 * m + 1)
  have hg : 1 ≤ g := by
    dsimp only [g]
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hAg : 1536 * A ≤ g := by
    dsimp only [A, g]
    exact cluster_strong_linear_le_pow hm
  have hme : 2 * m ≤ g := cluster_two_mul_le_pow (by omega)
  have hAexp : (A : ℝ) * Real.exp 1 ≤ (g : ℝ) / 512 := by
    have hAgR : 1536 * (A : ℝ) ≤ g := by exact_mod_cast hAg
    have hA0 : (0 : ℝ) ≤ A := by positivity
    have he := Real.exp_one_lt_three.le
    nlinarith
  have hpow : ((A : ℝ) * Real.exp 1) ^ g ≤ ((g : ℝ) / 512) ^ g := by
    gcongr
  have htwo : (g : ℝ) ^ 2 ≤ (2 : ℝ) ^ g := by
    have hcast : (g : ℝ) ^ 2 = (2 : ℝ) ^ (2 * m) := by
      dsimp only [g]
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      calc
        ((2 : ℝ) ^ m) ^ 2 = (2 : ℝ) ^ (m * 2) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (2 * m) := by congr 1; omega
    rw [hcast]
    exact pow_le_pow_right₀ (by norm_num) hme
  have hmain : (g : ℝ) ^ 2 * (A : ℝ) ^ g * (256 : ℝ) ^ g ≤
      ((g : ℝ) / Real.exp 1) ^ g := by
    have hepos : 0 < (Real.exp 1) ^ g := by positivity
    rw [div_pow]
    apply (le_div_iff₀ hepos).2
    calc
      (g : ℝ) ^ 2 * (A : ℝ) ^ g * (256 : ℝ) ^ g *
          (Real.exp 1) ^ g =
        (((A : ℝ) * Real.exp 1) ^ g) *
          ((g : ℝ) ^ 2 * (256 : ℝ) ^ g) := by rw [mul_pow]; ring
      _ ≤ (((g : ℝ) / 512) ^ g) *
          ((2 : ℝ) ^ g * (256 : ℝ) ^ g) := by gcongr
      _ = (g : ℝ) ^ g := by
        rw [← mul_pow, div_pow]
        norm_num
  have hstirling : ((g : ℝ) / Real.exp 1) ^ g ≤ (g.factorial : ℝ) := by
    have hs := Stirling.le_factorial_stirling g
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * g) := by
      rw [Real.one_le_sqrt]
      have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
      have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg
      nlinarith
    exact (le_mul_of_one_le_left (by positivity) hsqrt).trans hs
  have hnum : (g : ℝ) ^ 2 * (A : ℝ) ^ g * (256 : ℝ) ^ g ≤
      (g.factorial : ℝ) := hmain.trans hstirling
  have hfac : (0 : ℝ) < (g.factorial : ℝ) := by positivity
  have h256 : (0 : ℝ) < (256 : ℝ) ^ g := by positivity
  dsimp only [g, A] at hnum ⊢
  apply (div_le_iff₀ hfac).2
  rw [one_div, inv_mul_eq_div]
  apply (le_div_iff₀ h256).2
  simpa [mul_assoc] using hnum

/-- An absolute constant absorbing the finitely many small cluster scales. -/
noncomputable def clusterFactorialConstant : ℝ := (500 : ℝ) ^ 1100000 + 1

private lemma cluster_factorialCoefficient_small {m : ℕ} (hm : m < 20) :
    (((2 ^ m : ℕ) : ℝ) ^ 2 *
        (10 * (2 * m + 1 : ℕ) : ℕ) ^ (2 ^ m) /
          (((2 ^ m).factorial : ℕ) : ℝ)) ≤
      (500 : ℝ) ^ 1100000 / (256 : ℝ) ^ (2 ^ m) := by
  let g : ℕ := 2 ^ m
  let A : ℕ := 10 * (2 * m + 1)
  have hg : g ≤ 524288 := by
    dsimp only [g]
    calc 2 ^ m ≤ 2 ^ 19 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 524288 := by norm_num
  have hA : A ≤ 500 := by dsimp only [A]; omega
  have hg2 : (g : ℝ) ^ 2 ≤ (500 : ℝ) ^ 5 := by
    have hgR : (g : ℝ) ≤ 524288 := by exact_mod_cast hg
    calc
      (g : ℝ) ^ 2 ≤ (524288 : ℝ) ^ 2 := by gcongr
      _ ≤ (500 : ℝ) ^ 5 := by norm_num
  have hApow : (A : ℝ) ^ g ≤ (500 : ℝ) ^ g := by
    gcongr
    exact_mod_cast hA
  have h256pow : (256 : ℝ) ^ g ≤ (500 : ℝ) ^ g := by
    gcongr
    norm_num
  have hexp : g + 5 + g ≤ 1100000 := by omega
  have hnum : (g : ℝ) ^ 2 * (A : ℝ) ^ g * (256 : ℝ) ^ g ≤
      (500 : ℝ) ^ 1100000 := by
    calc
      (g : ℝ) ^ 2 * (A : ℝ) ^ g * (256 : ℝ) ^ g ≤
          (500 : ℝ) ^ 5 * (500 : ℝ) ^ g * (500 : ℝ) ^ g := by gcongr
      _ = (500 : ℝ) ^ (g + 5 + g) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ (500 : ℝ) ^ 1100000 := pow_le_pow_right₀ (by norm_num) hexp
  have hfac : (1 : ℝ) ≤ (g.factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero g)
  have hfacpos : (0 : ℝ) < (g.factorial : ℝ) := lt_of_lt_of_le zero_lt_one hfac
  have h256pos : (0 : ℝ) < (256 : ℝ) ^ g := by positivity
  dsimp only [g, A] at hnum
  apply (div_le_iff₀ hfacpos).2
  calc
    ((2 ^ m : ℕ) : ℝ) ^ 2 *
          ((10 * (2 * m + 1) : ℕ) : ℝ) ^ (2 ^ m) ≤
        (500 : ℝ) ^ 1100000 / (256 : ℝ) ^ (2 ^ m) := by
      apply (le_div_iff₀ h256pos).2
      simpa [mul_assoc] using hnum
    _ ≤ (500 : ℝ) ^ 1100000 / (256 : ℝ) ^ (2 ^ m) *
          (g.factorial : ℝ) := le_mul_of_one_le_right (by positivity) hfac

/-- The double-exponential factorial decay used in Ford's Lemma 4.4. -/
theorem cluster_factorialCoefficient_bound (m : ℕ) :
    (((2 ^ m : ℕ) : ℝ) ^ 2 *
        (10 * (2 * m + 1 : ℕ) : ℕ) ^ (2 ^ m) /
          (((2 ^ m).factorial : ℕ) : ℝ)) ≤
      clusterFactorialConstant / (256 : ℝ) ^ (2 ^ m) := by
  by_cases hm : 20 ≤ m
  · calc
      _ ≤ 1 / (256 : ℝ) ^ (2 ^ m) := cluster_factorialCoefficient_large hm
      _ ≤ clusterFactorialConstant / (256 : ℝ) ^ (2 ^ m) := by
        unfold clusterFactorialConstant
        gcongr
        have hp : 0 ≤ (500 : ℝ) ^ 1100000 := by positivity
        simpa only [zero_add, add_comm] using add_le_add_right hp 1
  · have hs := cluster_factorialCoefficient_small (by omega : m < 20)
    calc
      _ ≤ (500 : ℝ) ^ 1100000 / (256 : ℝ) ^ (2 ^ m) := hs
      _ ≤ clusterFactorialConstant / (256 : ℝ) ^ (2 ^ m) := by
        unfold clusterFactorialConstant
        gcongr
        linarith

private lemma cluster_denominator_ratio_bound {d m : ℕ} (hdm : d ≤ m + 2) :
    (2 : ℝ) ^ (2 ^ d) / (256 : ℝ) ^ (2 ^ m) ≤
      ((1 : ℝ) / 2) ^ (m + 2 - d) := by
  let q := m + 2 - d
  have hdq : d + q = m + 2 := by dsimp only [q]; omega
  have hpowd : 2 ^ d ≤ 2 ^ (m + 2) :=
    Nat.pow_le_pow_right (by norm_num) hdm
  have hmq : q ≤ 2 ^ (m + 2) := by
    calc
      q ≤ m + 2 := Nat.sub_le _ _
      _ ≤ 2 ^ (m + 2) := cluster_nat_le_two_pow (m + 2)
  have hexp : 2 ^ d + q ≤ 8 * 2 ^ m := by
    rw [show 8 * 2 ^ m = 2 ^ (m + 3) by
      rw [show 8 = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega]
    rw [pow_succ]
    omega
  have hp : (2 : ℝ) ^ (2 ^ d + q) ≤ (2 : ℝ) ^ (8 * 2 ^ m) :=
    pow_le_pow_right₀ (by norm_num) hexp
  have hden : (256 : ℝ) ^ (2 ^ m) = (2 : ℝ) ^ (8 * 2 ^ m) := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_mul]
  dsimp only [q] at hp ⊢
  rw [div_pow, one_pow, hden]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hp

/-- A summable polynomial-geometric majorant for the two finite cover indices. -/
noncomputable def clusterGeomMajorant (n : ℕ) : ℝ :=
  ((n : ℝ) + 7) ^ 3 * ((1 : ℝ) / 2) ^ n

private lemma clusterGeomMajorant_nonneg (n : ℕ) :
    0 ≤ clusterGeomMajorant n := by
  unfold clusterGeomMajorant
  positivity

private lemma summable_clusterGeomMajorant : Summable clusterGeomMajorant := by
  have hnorm : ‖(1 : ℝ) / 2‖ < 1 := by norm_num
  have h0 : Summable (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n) :=
    summable_geometric_of_norm_lt_one hnorm
  have h1 : Summable (fun n : ℕ ↦ (n : ℝ) * ((1 : ℝ) / 2) ^ n) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm)
  have h2 : Summable (fun n : ℕ ↦ (n : ℝ) ^ 2 * ((1 : ℝ) / 2) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hnorm
  have h3 : Summable (fun n : ℕ ↦ (n : ℝ) ^ 3 * ((1 : ℝ) / 2) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 3 hnorm
  have h := h3.add (h2.mul_left 21) |>.add (h1.mul_left 147) |>.add
    (h0.mul_left 343)
  convert h using 1
  funext n
  simp only [clusterGeomMajorant]
  ring

noncomputable def clusterGeomConstant : ℝ :=
  2 * (1 + ∑' n : ℕ, clusterGeomMajorant n)

private lemma clusterGeomConstant_pos : 0 < clusterGeomConstant := by
  unfold clusterGeomConstant
  have hsum : 0 ≤ ∑' n : ℕ, clusterGeomMajorant n :=
    tsum_nonneg clusterGeomMajorant_nonneg
  positivity

private lemma cluster_sum_reindexed_le_tsum
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) (g : ℕ → ℝ)
    (hf : Set.InjOn f s) (hg : Summable g) (hg0 : ∀ n, 0 ≤ g n) :
    ∑ k ∈ s, g (f k) ≤ ∑' n, g n := by
  let t := s.image f
  have hsum : ∑ k ∈ s, g (f k) = ∑ n ∈ t, g n := by
    apply Finset.sum_bij (fun k _ ↦ f k)
    · intro k hk
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    · intro k₁ hk₁ k₂ hk₂ heq
      exact hf hk₁ hk₂ heq
    · intro n hn
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
      exact ⟨k, hk, rfl⟩
    · intros
      rfl
  rw [hsum]
  exact hg.sum_le_tsum t (fun n _ ↦ hg0 n)

private lemma cluster_sum_geometric_sub_le_two
    (s : Finset ℕ) (a : ℕ) (ha : ∀ n ∈ s, a ≤ n) :
    ∑ n ∈ s, ((1 : ℝ) / 2) ^ (n - a) ≤ 2 := by
  calc
    _ ≤ ∑' n : ℕ, ((1 : ℝ) / 2) ^ n := by
      apply cluster_sum_reindexed_le_tsum s (fun n ↦ n - a)
      · intro x hx y hy hxy
        have hx' := ha x hx
        have hy' := ha y hy
        dsimp only at hxy
        omega
      · exact summable_geometric_two
      · intro n
        positivity
    _ = 2 := tsum_geometric_two

/-- The finite sum of the Lemma 4.3 scales occurring in the exact cover. -/
noncomputable def clusterCoverScaleSum (k v γ r : ℕ) : ℝ :=
  ∑ h : Fin (k + 4), if r + 1 ≤ h.1 then
    ∑ m : Fin (k + 1),
      if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
        clusterVolumeScale (2 ^ m.1) k (2 * m.1) (γ + h.1) v
      else 0
    else 0

private lemma clusterVolumeScale_dyadic_le (k v γ h m : ℕ) :
    clusterVolumeScale (2 ^ m) k (2 * m) (γ + h) v ≤
      clusterFactorialConstant / (256 : ℝ) ^ (2 ^ m) *
        (((γ + h + 1 : ℕ) : ℝ) *
          (((γ + h : ℕ) : ℝ) + v - k) ^ 2) /
            ((k + 1).factorial : ℝ) := by
  have hc := cluster_factorialCoefficient_bound m
  have htail : 0 ≤ (((γ : ℝ) + h + 1) *
      ((γ : ℝ) + h + v - k) ^ 2) /
        ((k + 1).factorial : ℝ) := by positivity
  unfold clusterVolumeScale
  norm_num only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one] at hc ⊢
  calc
    ((2 : ℝ) ^ m) ^ 2 * (10 * (2 * (m : ℝ) + 1)) ^ (2 ^ m) /
          (((2 ^ m).factorial : ℕ) : ℝ) *
        (((γ : ℝ) + h + 1) * ((γ : ℝ) + h + v - k) ^ 2) /
          ((k + 1).factorial : ℝ) ≤
      (clusterFactorialConstant / (256 : ℝ) ^ (2 ^ m)) *
        (((γ : ℝ) + h + 1) * ((γ : ℝ) + h + v - k) ^ 2) /
          ((k + 1).factorial : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

private lemma clusterVolumeScale_large_pointwise
    {k v γ b d h m : ℕ} (hb : k = v + b) (hd : b = γ + d)
    (hb5 : 5 ≤ b) (hd5 : 5 ≤ d) (hdh : d + 1 ≤ h) (hhm : h - 3 ≤ m) :
    clusterVolumeScale (2 ^ m) k (2 * m) (γ + h) v ≤
      clusterFactorialConstant *
        ((b : ℝ) / (2 : ℝ) ^ (2 ^ d) / ((k + 1).factorial : ℝ)) *
          clusterGeomMajorant (h - (d + 1)) *
            ((1 : ℝ) / 2) ^ (m - (h - 3)) := by
  let e := h - (d + 1)
  let t := m - (h - 3)
  have hhe : h = d + 1 + e := by dsimp only [e]; omega
  have hmt : m = h - 3 + t := by dsimp only [t]; omega
  have hh3 : 3 ≤ h := by omega
  have hmd : d ≤ m + 2 := by omega
  have hqt : m + 2 - d = e + t := by
    dsimp only [e, t]
    omega
  have hpoly : (((γ + h + 1 : ℕ) : ℝ) *
      (((γ + h : ℕ) : ℝ) + v - k) ^ 2) ≤
        (b : ℝ) * ((e : ℝ) + 7) ^ 3 := by
    have hbR : (5 : ℝ) ≤ b := by exact_mod_cast hb5
    have hfirst : ((γ + h + 1 : ℕ) : ℝ) ≤
        (b : ℝ) * ((e : ℝ) + 7) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hbEq : (b : ℝ) = γ + d := by exact_mod_cast hd
      have hhEq : (h : ℝ) = d + 1 + e := by exact_mod_cast hhe
      have he0 : (0 : ℝ) ≤ e := by positivity
      nlinarith
    have hdiff : (((γ + h : ℕ) : ℝ) + v - k) = (e : ℝ) + 1 := by
      norm_num only [Nat.cast_add]
      have hbEq : (b : ℝ) = γ + d := by exact_mod_cast hd
      have hkEq : (k : ℝ) = v + b := by exact_mod_cast hb
      have hhEq : (h : ℝ) = d + 1 + e := by exact_mod_cast hhe
      linarith
    rw [hdiff]
    have he7 : 0 ≤ (e : ℝ) + 7 := by positivity
    have hsquare : ((e : ℝ) + 1) ^ 2 ≤ ((e : ℝ) + 7) ^ 2 := by
      nlinarith [sq_nonneg ((e : ℝ) + 1), sq_nonneg ((e : ℝ) + 7)]
    calc
      ((γ + h + 1 : ℕ) : ℝ) * ((e : ℝ) + 1) ^ 2 ≤
          ((b : ℝ) * ((e : ℝ) + 7)) * ((e : ℝ) + 7) ^ 2 := by gcongr
      _ = (b : ℝ) * ((e : ℝ) + 7) ^ 3 := by ring
  have hratio := cluster_denominator_ratio_bound hmd
  rw [hqt] at hratio
  have hD : 0 < (2 : ℝ) ^ (2 ^ d) := by positivity
  have hF : 0 < ((k + 1).factorial : ℝ) := by positivity
  have hCF : 0 ≤ clusterFactorialConstant := by
    unfold clusterFactorialConstant
    positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hE : 0 ≤ ((e : ℝ) + 7) ^ 3 := by positivity
  calc
    clusterVolumeScale (2 ^ m) k (2 * m) (γ + h) v ≤
        clusterFactorialConstant / (256 : ℝ) ^ (2 ^ m) *
          (((γ + h + 1 : ℕ) : ℝ) *
            (((γ + h : ℕ) : ℝ) + v - k) ^ 2) /
              ((k + 1).factorial : ℝ) :=
      clusterVolumeScale_dyadic_le k v γ h m
    _ ≤ clusterFactorialConstant / (256 : ℝ) ^ (2 ^ m) *
          ((b : ℝ) * ((e : ℝ) + 7) ^ 3) /
            ((k + 1).factorial : ℝ) := by gcongr
    _ = clusterFactorialConstant *
          ((b : ℝ) / (2 : ℝ) ^ (2 ^ d) /
            ((k + 1).factorial : ℝ)) *
          (((e : ℝ) + 7) ^ 3 *
            ((2 : ℝ) ^ (2 ^ d) / (256 : ℝ) ^ (2 ^ m))) := by
      field_simp
    _ ≤ clusterFactorialConstant *
          ((b : ℝ) / (2 : ℝ) ^ (2 ^ d) /
            ((k + 1).factorial : ℝ)) *
          (((e : ℝ) + 7) ^ 3 * (((1 : ℝ) / 2) ^ (e + t))) := by
      gcongr
    _ = clusterFactorialConstant *
        ((b : ℝ) / (2 : ℝ) ^ (2 ^ d) / ((k + 1).factorial : ℝ)) *
          clusterGeomMajorant (h - (d + 1)) *
            ((1 : ℝ) / 2) ^ (m - (h - 3)) := by
      rw [pow_add]
      unfold clusterGeomMajorant
      dsimp only [e, t]
      ring

private lemma clusterCoverScaleSum_large
    {k v γ : ℕ} (hlarge : v + γ + 5 ≤ k) :
    clusterCoverScaleSum k v γ (orderStatisticR k v γ) ≤
      clusterFactorialConstant * clusterGeomConstant *
        (((k - v : ℕ) : ℝ) /
          (2 : ℝ) ^ (2 ^ (k - v - γ)) /
            ((k + 1).factorial : ℝ)) := by
  let b := k - v
  let d := b - γ
  have hvk : v ≤ k := by omega
  have hb : k = v + b := by dsimp only [b]; omega
  have hd : b = γ + d := by dsimp only [d, b]; omega
  have hb5 : 5 ≤ b := by dsimp only [b]; omega
  have hd5 : 5 ≤ d := by dsimp only [d, b]; omega
  have hr : orderStatisticR k v γ = d := by
    unfold orderStatisticR
    rw [max_eq_right (by omega : 5 ≤ k - (v + γ))]
    dsimp only [d, b]
    omega
  let T : ℝ := clusterFactorialConstant *
    ((b : ℝ) / (2 : ℝ) ^ (2 ^ d) / ((k + 1).factorial : ℝ))
  have hT : 0 ≤ T := by
    dsimp only [T]
    have hCF : 0 ≤ clusterFactorialConstant := by
      unfold clusterFactorialConstant
      positivity
    positivity
  have hinner (h : Fin (k + 4)) (hdh : d + 1 ≤ h.1) :
      (∑ m : Fin (k + 1),
        if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
          clusterVolumeScale (2 ^ m.1) k (2 * m.1) (γ + h.1) v
        else 0) ≤
      T * clusterGeomMajorant (h.1 - (d + 1)) * 2 := by
    let M : Finset (Fin (k + 1)) := Finset.univ.filter fun m ↦
      h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k
    have hgeom : (∑ m ∈ M, ((1 : ℝ) / 2) ^ (m.1 - (h.1 - 3))) ≤ 2 := by
      calc
        _ ≤ ∑' n : ℕ, ((1 : ℝ) / 2) ^ n := by
          apply cluster_sum_reindexed_le_tsum M
            (fun m ↦ m.1 - (h.1 - 3))
          · intro x hx y hy hxy
            have hx' : h.1 - 3 ≤ x.1 := (Finset.mem_filter.mp hx).2.1
            have hy' : h.1 - 3 ≤ y.1 := (Finset.mem_filter.mp hy).2.1
            dsimp only at hxy
            apply Fin.ext
            omega
          · exact summable_geometric_two
          · intro n
            positivity
        _ = 2 := tsum_geometric_two
    calc
      (∑ m : Fin (k + 1),
          if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
            clusterVolumeScale (2 ^ m.1) k (2 * m.1) (γ + h.1) v
          else 0) =
          ∑ m ∈ M,
            clusterVolumeScale (2 ^ m.1) k (2 * m.1) (γ + h.1) v := by
        simp only [M, Finset.sum_filter, Finset.mem_univ, true_and]
      _ ≤ ∑ m ∈ M,
          T * clusterGeomMajorant (h.1 - (d + 1)) *
            ((1 : ℝ) / 2) ^ (m.1 - (h.1 - 3)) := by
        apply Finset.sum_le_sum
        intro m hm
        exact clusterVolumeScale_large_pointwise hb hd hb5 hd5 hdh
          (Finset.mem_filter.mp hm).2.1
      _ = T * clusterGeomMajorant (h.1 - (d + 1)) *
          (∑ m ∈ M, ((1 : ℝ) / 2) ^ (m.1 - (h.1 - 3))) := by
        rw [Finset.mul_sum]
      _ ≤ T * clusterGeomMajorant (h.1 - (d + 1)) * 2 := by
        exact mul_le_mul_of_nonneg_left hgeom <|
          mul_nonneg hT (clusterGeomMajorant_nonneg _)
  let H : Finset (Fin (k + 4)) := Finset.univ.filter fun h ↦ d + 1 ≤ h.1
  have hmaj : (∑ h ∈ H, clusterGeomMajorant (h.1 - (d + 1))) ≤
      ∑' n : ℕ, clusterGeomMajorant n := by
    apply cluster_sum_reindexed_le_tsum H (fun h ↦ h.1 - (d + 1))
    · intro x hx y hy hxy
      have hx' : d + 1 ≤ x.1 := (Finset.mem_filter.mp hx).2
      have hy' : d + 1 ≤ y.1 := (Finset.mem_filter.mp hy).2
      dsimp only at hxy
      apply Fin.ext
      omega
    · exact summable_clusterGeomMajorant
    · exact clusterGeomMajorant_nonneg
  rw [hr]
  unfold clusterCoverScaleSum
  calc
    (∑ h : Fin (k + 4), if d + 1 ≤ h.1 then
        ∑ m : Fin (k + 1),
          if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
            clusterVolumeScale (2 ^ m.1) k (2 * m.1) (γ + h.1) v
          else 0
        else 0) ≤
      ∑ h ∈ H, T * clusterGeomMajorant (h.1 - (d + 1)) * 2 := by
        calc
          _ ≤ ∑ h : Fin (k + 4), if d + 1 ≤ h.1 then
              T * clusterGeomMajorant (h.1 - (d + 1)) * 2 else 0 := by
            apply Finset.sum_le_sum
            intro h hh
            split_ifs with hdh
            · exact hinner h hdh
            · exact le_rfl
          _ = _ := by
            simp only [H, Finset.sum_filter, Finset.mem_univ, true_and]
    _ = T * 2 * (∑ h ∈ H, clusterGeomMajorant (h.1 - (d + 1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ ≤ T * 2 * (∑' n : ℕ, clusterGeomMajorant n) := by gcongr
    _ ≤ clusterFactorialConstant * clusterGeomConstant *
        (((k - v : ℕ) : ℝ) / (2 : ℝ) ^ (2 ^ (k - v - γ)) /
          ((k + 1).factorial : ℝ)) := by
      have htarget : clusterFactorialConstant * clusterGeomConstant *
          (((k - v : ℕ) : ℝ) / (2 : ℝ) ^ (2 ^ (k - v - γ)) /
            ((k + 1).factorial : ℝ)) = T * clusterGeomConstant := by
        dsimp only [T, b, d]
        ring
      rw [htarget]
      change T * 2 * (∑' n : ℕ, clusterGeomMajorant n) ≤
        T * clusterGeomConstant
      rw [show T * 2 * (∑' n : ℕ, clusterGeomMajorant n) =
          T * (2 * (∑' n : ℕ, clusterGeomMajorant n)) by ring]
      apply mul_le_mul_of_nonneg_left _ hT
      unfold clusterGeomConstant
      have hsum : 0 ≤ ∑' n : ℕ, clusterGeomMajorant n :=
        tsum_nonneg clusterGeomMajorant_nonneg
      nlinarith

private lemma orderStatisticY_eq_small
    {k v γ : ℕ} (hsmall : k < v + γ + 5) :
    orderStatisticY k v γ =
      (((γ + 5 + v - k : ℕ) : ℝ) ^ 2 * (γ + 1 : ℝ)) := by
  have hif : ¬(γ : ℤ) + 5 ≤ orderStatisticExcess k v := by
    unfold orderStatisticExcess
    omega
  rw [orderStatisticY, if_neg hif]
  have hle : k ≤ γ + 5 + v := by omega
  unfold orderStatisticExcess
  norm_num only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_ofNat,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.cast_sub hle]
  ring

private lemma orderStatisticDoubleExp_le_small
    {k v γ : ℕ} (hsmall : k < v + γ + 5) :
    orderStatisticDoubleExp k v γ ≤ (2 : ℝ) ^ (16 : ℕ) := by
  have hrZ : orderStatisticExcess k v - (γ : ℤ) ≤ 4 := by
    unfold orderStatisticExcess
    omega
  have hrR : (((orderStatisticExcess k v - (γ : ℤ) : ℤ) : ℝ)) ≤ 4 := by
    exact_mod_cast hrZ
  have hinner : (2 : ℝ) ^
      (((orderStatisticExcess k v - (γ : ℤ) : ℤ) : ℝ)) ≤ 16 := by
    calc
      _ ≤ (2 : ℝ) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hrR
      _ = 16 := by norm_num
  unfold orderStatisticDoubleExp
  calc
    (2 : ℝ) ^ ((2 : ℝ) ^
        (((orderStatisticExcess k v - (γ : ℤ) : ℤ) : ℝ))) ≤
      (2 : ℝ) ^ (16 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hinner
    _ = (2 : ℝ) ^ (16 : ℕ) := Real.rpow_natCast 2 16

private lemma cluster_small_denominator_ratio
    {k v γ e t : ℕ} (hsmall : k < v + γ + 5) :
    orderStatisticDoubleExp k v γ /
        (256 : ℝ) ^ (2 ^ (e + 3 + t)) ≤
      ((1 : ℝ) / 2) ^ (e + t) := by
  let q := e + t
  have hq : q ≤ 2 ^ q := cluster_nat_le_two_pow q
  have hqone : 1 ≤ 2 ^ q :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hexp : 16 + q ≤ 8 * 2 ^ (e + 3 + t) := by
    rw [show e + 3 + t = q + 3 by dsimp only [q]; omega, pow_add]
    norm_num
    omega
  have hD := orderStatisticDoubleExp_le_small hsmall
  have hpow : (2 : ℝ) ^ (16 + q) ≤
      (2 : ℝ) ^ (8 * 2 ^ (e + 3 + t)) :=
    pow_le_pow_right₀ (by norm_num) hexp
  have hden : (256 : ℝ) ^ (2 ^ (e + 3 + t)) =
      (2 : ℝ) ^ (8 * 2 ^ (e + 3 + t)) := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_mul]
  have hnum : orderStatisticDoubleExp k v γ * (2 : ℝ) ^ q ≤
      (256 : ℝ) ^ (2 ^ (e + 3 + t)) := by
    rw [hden]
    calc
      orderStatisticDoubleExp k v γ * (2 : ℝ) ^ q ≤
          (2 : ℝ) ^ 16 * (2 : ℝ) ^ q := by gcongr
      _ = (2 : ℝ) ^ (16 + q) := (pow_add (2 : ℝ) 16 q).symm
      _ ≤ _ := hpow
  rw [div_pow, one_pow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa [q, mul_comm] using hnum

private lemma clusterVolumeScale_small_pointwise
    {k v γ h m : ℕ} (hsmall : k < v + γ + 5)
    (hh : 6 ≤ h) (hhm : h - 3 ≤ m) :
    clusterVolumeScale (2 ^ m) k (2 * m) (γ + h) v ≤
      clusterFactorialConstant *
        (orderStatisticY k v γ / orderStatisticDoubleExp k v γ /
          ((k + 1).factorial : ℝ)) *
        clusterGeomMajorant (h - 6) *
          ((1 : ℝ) / 2) ^ (m - (h - 3)) := by
  let a := γ + 5 + v - k
  let e := h - 6
  let t := m - (h - 3)
  have ha : 1 ≤ a := by dsimp only [a]; omega
  have hhe : h = 6 + e := by dsimp only [e]; omega
  have hmt : m = e + 3 + t := by dsimp only [e, t]; omega
  have hY : orderStatisticY k v γ = (a : ℝ) ^ 2 * (γ + 1 : ℝ) := by
    simpa only [a] using orderStatisticY_eq_small hsmall
  have hpoly : (((γ + h + 1 : ℕ) : ℝ) *
      (((γ + h : ℕ) : ℝ) + v - k) ^ 2) ≤
        orderStatisticY k v γ * ((e : ℝ) + 7) ^ 3 := by
    rw [hY]
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hfirst : ((γ + h + 1 : ℕ) : ℝ) ≤
        ((γ : ℝ) + 1) * ((e : ℝ) + 7) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hhR : (h : ℝ) = 6 + e := by exact_mod_cast hhe
      have hγ0 : (0 : ℝ) ≤ γ := by positivity
      have he0 : (0 : ℝ) ≤ e := by positivity
      nlinarith
    have hdiff : (((γ + h : ℕ) : ℝ) + v - k) = (a : ℝ) + e + 1 := by
      norm_num only [Nat.cast_add]
      have haR' : (a : ℝ) = γ + 5 + v - k := by
        dsimp only [a]
        norm_num only [Nat.cast_sub (by omega : k ≤ γ + 5 + v), Nat.cast_add,
          Nat.cast_ofNat]
      have hhR : (h : ℝ) = 6 + e := by exact_mod_cast hhe
      linarith
    rw [hdiff]
    have hsecond : (a : ℝ) + e + 1 ≤ (a : ℝ) * ((e : ℝ) + 2) := by
      have he0 : (0 : ℝ) ≤ e := by positivity
      nlinarith
    have hsquare : ((a : ℝ) + e + 1) ^ 2 ≤
        ((a : ℝ) * ((e : ℝ) + 2)) ^ 2 := by gcongr
    have hep : 0 ≤ (e : ℝ) + 7 := by positivity
    calc
      ((γ + h + 1 : ℕ) : ℝ) * ((a : ℝ) + e + 1) ^ 2 ≤
          (((γ : ℝ) + 1) * ((e : ℝ) + 7)) *
            (((a : ℝ) * ((e : ℝ) + 2)) ^ 2) := by gcongr
      _ = (a : ℝ) ^ 2 * ((γ : ℝ) + 1) * ((e : ℝ) + 7) *
          ((e : ℝ) + 2) ^ 2 := by ring
      _ ≤ (a : ℝ) ^ 2 * ((γ : ℝ) + 1) * ((e : ℝ) + 7) *
          ((e : ℝ) + 7) ^ 2 := by gcongr <;> norm_num
      _ = ((a : ℝ) ^ 2 * ((γ : ℝ) + 1)) * ((e : ℝ) + 7) ^ 3 := by ring
  have hratio := cluster_small_denominator_ratio
    (k := k) (v := v) (γ := γ) (e := e) (t := t) hsmall
  rw [← hmt] at hratio
  have hD : 0 < orderStatisticDoubleExp k v γ :=
    orderStatisticDoubleExp_pos k v γ
  have hF : 0 < ((k + 1).factorial : ℝ) := by positivity
  have hY0 : 0 ≤ orderStatisticY k v γ := by rw [hY]; positivity
  have hCF0 : 0 ≤ clusterFactorialConstant := by
    unfold clusterFactorialConstant
    positivity
  have hcoef0 : 0 ≤ clusterFactorialConstant *
      (orderStatisticY k v γ / orderStatisticDoubleExp k v γ /
        ((k + 1).factorial : ℝ)) := by positivity
  calc
    clusterVolumeScale (2 ^ m) k (2 * m) (γ + h) v ≤
        clusterFactorialConstant / (256 : ℝ) ^ (2 ^ m) *
          (((γ + h + 1 : ℕ) : ℝ) *
            (((γ + h : ℕ) : ℝ) + v - k) ^ 2) /
              ((k + 1).factorial : ℝ) :=
      clusterVolumeScale_dyadic_le k v γ h m
    _ ≤ clusterFactorialConstant / (256 : ℝ) ^ (2 ^ m) *
          (orderStatisticY k v γ * ((e : ℝ) + 7) ^ 3) /
            ((k + 1).factorial : ℝ) := by
      gcongr
    _ = clusterFactorialConstant *
          (orderStatisticY k v γ / orderStatisticDoubleExp k v γ /
            ((k + 1).factorial : ℝ)) *
          (((e : ℝ) + 7) ^ 3 *
            (orderStatisticDoubleExp k v γ / (256 : ℝ) ^ (2 ^ m))) := by
      field_simp
    _ ≤ clusterFactorialConstant *
          (orderStatisticY k v γ / orderStatisticDoubleExp k v γ /
            ((k + 1).factorial : ℝ)) *
          (((e : ℝ) + 7) ^ 3 * (((1 : ℝ) / 2) ^ (e + t))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hratio (by positivity)) hcoef0
    _ = clusterFactorialConstant *
        (orderStatisticY k v γ / orderStatisticDoubleExp k v γ /
          ((k + 1).factorial : ℝ)) *
        clusterGeomMajorant (h - 6) *
          ((1 : ℝ) / 2) ^ (m - (h - 3)) := by
      rw [pow_add]
      unfold clusterGeomMajorant
      dsimp only [e, t]
      ring

private lemma clusterCoverScaleSum_small
    {k v γ : ℕ} (hsmall : k < v + γ + 5) :
    clusterCoverScaleSum k v γ (orderStatisticR k v γ) ≤
      clusterFactorialConstant * clusterGeomConstant *
        (orderStatisticY k v γ / orderStatisticDoubleExp k v γ /
          ((k + 1).factorial : ℝ)) := by
  have hr : orderStatisticR k v γ = 5 := by
    unfold orderStatisticR
    rw [max_eq_left]
    omega
  let T : ℝ := clusterFactorialConstant *
    (orderStatisticY k v γ / orderStatisticDoubleExp k v γ /
      ((k + 1).factorial : ℝ))
  have hT : 0 ≤ T := by
    dsimp only [T]
    have hCF : 0 ≤ clusterFactorialConstant := by
      unfold clusterFactorialConstant
      positivity
    have hY : 0 ≤ orderStatisticY k v γ := by
      rw [orderStatisticY_eq_small hsmall]
      positivity
    exact mul_nonneg hCF <|
      div_nonneg (div_nonneg hY (orderStatisticDoubleExp_pos k v γ).le)
        (by positivity)
  have hinner (h : Fin (k + 4)) (hh : 6 ≤ h.1) :
      (∑ m : Fin (k + 1),
        if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
          clusterVolumeScale (2 ^ m.1) k (2 * m.1) (γ + h.1) v
        else 0) ≤
      T * clusterGeomMajorant (h.1 - 6) * 2 := by
    let M : Finset (Fin (k + 1)) := Finset.univ.filter fun m ↦
      h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k
    have hgeom : (∑ m ∈ M, ((1 : ℝ) / 2) ^ (m.1 - (h.1 - 3))) ≤ 2 := by
      calc
        _ ≤ ∑' n : ℕ, ((1 : ℝ) / 2) ^ n := by
          apply cluster_sum_reindexed_le_tsum M
            (fun m ↦ m.1 - (h.1 - 3))
          · intro x hx y hy hxy
            have hx' : h.1 - 3 ≤ x.1 := (Finset.mem_filter.mp hx).2.1
            have hy' : h.1 - 3 ≤ y.1 := (Finset.mem_filter.mp hy).2.1
            dsimp only at hxy
            apply Fin.ext
            omega
          · exact summable_geometric_two
          · intro n
            positivity
        _ = 2 := tsum_geometric_two
    calc
      (∑ m : Fin (k + 1),
          if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
            clusterVolumeScale (2 ^ m.1) k (2 * m.1) (γ + h.1) v
          else 0) =
          ∑ m ∈ M,
            clusterVolumeScale (2 ^ m.1) k (2 * m.1) (γ + h.1) v := by
        simp only [M, Finset.sum_filter, Finset.mem_univ, true_and]
      _ ≤ ∑ m ∈ M,
          T * clusterGeomMajorant (h.1 - 6) *
            ((1 : ℝ) / 2) ^ (m.1 - (h.1 - 3)) := by
        apply Finset.sum_le_sum
        intro m hm
        exact clusterVolumeScale_small_pointwise hsmall hh
          (Finset.mem_filter.mp hm).2.1
      _ = T * clusterGeomMajorant (h.1 - 6) *
          (∑ m ∈ M, ((1 : ℝ) / 2) ^ (m.1 - (h.1 - 3))) := by
        rw [Finset.mul_sum]
      _ ≤ T * clusterGeomMajorant (h.1 - 6) * 2 := by
        exact mul_le_mul_of_nonneg_left hgeom <|
          mul_nonneg hT (clusterGeomMajorant_nonneg _)
  let H : Finset (Fin (k + 4)) := Finset.univ.filter fun h ↦ 6 ≤ h.1
  have hmaj : (∑ h ∈ H, clusterGeomMajorant (h.1 - 6)) ≤
      ∑' n : ℕ, clusterGeomMajorant n := by
    apply cluster_sum_reindexed_le_tsum H (fun h ↦ h.1 - 6)
    · intro x hx y hy hxy
      have hx' : 6 ≤ x.1 := (Finset.mem_filter.mp hx).2
      have hy' : 6 ≤ y.1 := (Finset.mem_filter.mp hy).2
      dsimp only at hxy
      apply Fin.ext
      omega
    · exact summable_clusterGeomMajorant
    · exact clusterGeomMajorant_nonneg
  rw [hr]
  unfold clusterCoverScaleSum
  calc
    (∑ h : Fin (k + 4), if 5 + 1 ≤ h.1 then
        ∑ m : Fin (k + 1),
          if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
            clusterVolumeScale (2 ^ m.1) k (2 * m.1) (γ + h.1) v
          else 0
        else 0) ≤
      ∑ h ∈ H, T * clusterGeomMajorant (h.1 - 6) * 2 := by
        calc
          _ ≤ ∑ h : Fin (k + 4), if 6 ≤ h.1 then
              T * clusterGeomMajorant (h.1 - 6) * 2 else 0 := by
            apply Finset.sum_le_sum
            intro h hh
            split_ifs with hh6
            · exact hinner h hh6
            · exact le_rfl
          _ = _ := by
            simp only [H, Finset.sum_filter, Finset.mem_univ, true_and]
    _ = T * 2 * (∑ h ∈ H, clusterGeomMajorant (h.1 - 6)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ ≤ T * 2 * (∑' n : ℕ, clusterGeomMajorant n) := by gcongr
    _ ≤ clusterFactorialConstant * clusterGeomConstant *
        (orderStatisticY k v γ / orderStatisticDoubleExp k v γ /
          ((k + 1).factorial : ℝ)) := by
      have htarget : clusterFactorialConstant * clusterGeomConstant *
          (orderStatisticY k v γ / orderStatisticDoubleExp k v γ /
            ((k + 1).factorial : ℝ)) = T * clusterGeomConstant := by
        dsimp only [T]
        ring
      rw [htarget]
      rw [show T * 2 * (∑' n : ℕ, clusterGeomMajorant n) =
          T * (2 * (∑' n : ℕ, clusterGeomMajorant n)) by ring]
      apply mul_le_mul_of_nonneg_left _ hT
      unfold clusterGeomConstant
      have hsum : 0 ≤ ∑' n : ℕ, clusterGeomMajorant n :=
        tsum_nonneg clusterGeomMajorant_nonneg
      nlinarith

/-- The complete finite cover sum, at the scale in Ford's Lemma 4.4. -/
theorem clusterCoverScaleSum_bound {k v γ : ℕ} (hk : 1 ≤ k) :
    clusterCoverScaleSum k v γ (orderStatisticR k v γ) ≤
      clusterFactorialConstant * clusterGeomConstant * fordTVolumeScale k v γ := by
  by_cases hlarge : v + γ + 5 ≤ k
  · have h := clusterCoverScaleSum_large hlarge
    have hvk : v ≤ k := by omega
    have hif : (γ : ℤ) + 5 ≤ orderStatisticExcess k v := by
      unfold orderStatisticExcess
      omega
    have hYeq : orderStatisticY k v γ = ((k - v : ℕ) : ℝ) := by
      simp only [orderStatisticY, hif, if_pos]
      unfold orderStatisticExcess
      norm_num only [Int.cast_sub, Int.cast_natCast, Nat.cast_sub hvk]
    have hDeq : orderStatisticDoubleExp k v γ =
        (2 : ℝ) ^ (2 ^ (k - v - γ)) := by
      unfold orderStatisticDoubleExp orderStatisticExcess
      rw [show (k : ℤ) - (v : ℤ) - (γ : ℤ) =
          ((k - v - γ : ℕ) : ℤ) by omega]
      norm_num only [Int.cast_natCast]
      rw [show (2 : ℝ) ^ ((k - v - γ : ℕ) : ℝ) =
          (((2 ^ (k - v - γ) : ℕ) : ℕ) : ℝ) by
        rw [Real.rpow_natCast]
        norm_num]
      rw [Real.rpow_natCast]
    unfold fordTVolumeScale
    rw [hYeq, hDeq]
    convert h using 1 <;> field_simp
  · have h := clusterCoverScaleSum_small (by omega : k < v + γ + 5)
    unfold fordTVolumeScale
    convert h using 1 <;> field_simp

private theorem fordClusterCover_volume_bound_of_orderQ
    {C : ℝ} (hC : 0 < C)
    (hQ : ∀ (n : ℕ) (a b : ℝ),
      1 ≤ n → 0 ≤ a → 0 ≤ a + b - (n : ℝ) →
      orderQ n a b ≤
        C * (a + 1) * (a + b - (n : ℝ) + 1) ^ 2 / (n : ℝ))
    {k v γ : ℕ} (hk : 1 ≤ k) (hkv : k ≤ 10 * v) :
    (volume (fordClusterCover k v γ (orderStatisticR k v γ))).toReal ≤
      (512 * (Real.exp 4 * (Real.exp 1) ^ 10) * (C + 1) ^ 2) *
        clusterFactorialConstant * clusterGeomConstant * fordTVolumeScale k v γ := by
  let K : ℝ := 512 * (Real.exp 4 * (Real.exp 1) ^ 10) * (C + 1) ^ 2
  have hv : 1 ≤ v := by omega
  have hsum := volume_fordClusterCover_toReal_le_sum
    k v γ (orderStatisticR k v γ)
  have hterm (h : Fin (k + 4)) (hrh : orderStatisticR k v γ + 1 ≤ h.1)
      (m : Fin (k + 1)) (hm : h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k) :
      (volume (clusterRegion (2 ^ m.1) k (2 * m.1) (γ + h.1) v)).toReal ≤
        K * clusterVolumeScale (2 ^ m.1) k (2 * m.1) (γ + h.1) v := by
    have huvk : k + 1 ≤ γ + h.1 + v := by
      have hr : k - (v + γ) ≤ orderStatisticR k v γ := by
        unfold orderStatisticR
        omega
      omega
    exact clusterRegion_volume_scale_bound_of_orderQ hC hQ
      (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num)))
      hm.2 hv hkv huvk
  calc
    (volume (fordClusterCover k v γ (orderStatisticR k v γ))).toReal ≤
        ∑ h : Fin (k + 4),
          if orderStatisticR k v γ + 1 ≤ h.1 then
            ∑ m : Fin (k + 1),
              if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
                (volume (clusterRegion (2 ^ m.1) k (2 * m.1)
                  (γ + h.1) v)).toReal
              else 0
          else 0 := hsum
    _ ≤ ∑ h : Fin (k + 4),
          if orderStatisticR k v γ + 1 ≤ h.1 then
            ∑ m : Fin (k + 1),
              if h.1 - 3 ≤ m.1 ∧ 2 ^ m.1 + 1 ≤ k then
                K * clusterVolumeScale (2 ^ m.1) k (2 * m.1)
                  (γ + h.1) v
              else 0
          else 0 := by
      apply Finset.sum_le_sum
      intro h hh
      split_ifs with hrh
      · apply Finset.sum_le_sum
        intro m hm
        split_ifs with hmm
        · exact hterm h hrh m hmm
        · exact le_rfl
      · exact le_rfl
    _ = K * clusterCoverScaleSum k v γ (orderStatisticR k v γ) := by
      unfold clusterCoverScaleSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      split_ifs
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        split_ifs <;> simp
      · simp
    _ ≤ K * (clusterFactorialConstant * clusterGeomConstant *
          fordTVolumeScale k v γ) := by
      apply mul_le_mul_of_nonneg_left (clusterCoverScaleSum_bound hk)
      dsimp only [K]
      positivity
    _ = (512 * (Real.exp 4 * (Real.exp 1) ^ 10) * (C + 1) ^ 2) *
        clusterFactorialConstant * clusterGeomConstant * fordTVolumeScale k v γ := by
      dsimp only [K]
      ring

private theorem fordGoodPart_volume_bound_small_of_orderQ
    {C : ℝ} (hC : 0 < C)
    (hQ : ∀ (n : ℕ) (a b : ℝ),
      1 ≤ n → 0 ≤ a → 0 ≤ a + b - (n : ℝ) →
      orderQ n a b ≤
        C * (a + 1) * (a + b - (n : ℝ) + 1) ^ 2 / (n : ℝ))
    {k v γ : ℕ} (hk : 1 ≤ k) (hsmall : k < v + γ + 5) :
    (volume (fordGoodPart k v γ)).toReal ≤
      (48 * 65536 * C) * fordTVolumeScale k v γ := by
  let a := γ + 5 + v - k
  have ha : 1 ≤ a := by dsimp only [a]; omega
  have hr : orderStatisticR k v γ = 5 := by
    unfold orderStatisticR
    rw [max_eq_left]
    omega
  have haR : (((γ + 5 : ℕ) : ℝ) + v - k) = (a : ℝ) := by
    dsimp only [a]
    norm_num only [Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_sub (by omega : k ≤ γ + 5 + v)]
  have hgood := fordGoodPart_volume_bound_of_orderQ hC hQ (k := k) (v := v)
    (γ := γ) hk
  rw [hr] at hgood
  have hY := orderStatisticY_eq_small hsmall
  have hD := orderStatisticDoubleExp_le_small hsmall
  have hD' : orderStatisticDoubleExp k v γ ≤ 65536 := by
    norm_num at hD ⊢
    exact hD
  have hγ : ((γ + 5 + 1 : ℕ) : ℝ) ≤ 6 * ((γ + 1 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    have hγ0 : (0 : ℝ) ≤ γ := by positivity
    linarith
  have ha4 : ((a : ℝ) + 1) ^ 2 ≤ 4 * (a : ℝ) ^ 2 := by
    have haR1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith [sq_nonneg ((a : ℝ) - 1)]
  have hF : 0 < ((k + 1).factorial : ℝ) := by positivity
  have hbase0 : 0 ≤ 48 * C * orderStatisticY k v γ /
      ((k + 1).factorial : ℝ) := by
    rw [hY]
    positivity
  calc
    (volume (fordGoodPart k v γ)).toReal ≤
        2 * C * ((γ + 5 : ℕ) + 1 : ℕ) *
          (((γ + 5 : ℕ) : ℝ) + v - k + 1) ^ 2 /
            ((k + 1).factorial : ℝ) := hgood
    _ = 2 * C * ((γ + 5 + 1 : ℕ) : ℝ) * ((a : ℝ) + 1) ^ 2 /
          ((k + 1).factorial : ℝ) := by rw [haR]
    _ ≤ 2 * C * (6 * ((γ + 1 : ℕ) : ℝ)) * (4 * (a : ℝ) ^ 2) /
          ((k + 1).factorial : ℝ) := by gcongr
    _ = 48 * C * orderStatisticY k v γ /
          ((k + 1).factorial : ℝ) := by
      rw [hY]
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ (48 * C * orderStatisticY k v γ /
          ((k + 1).factorial : ℝ)) *
        (65536 / orderStatisticDoubleExp k v γ) := by
      exact le_mul_of_one_le_right hbase0 <|
        (le_div_iff₀ (orderStatisticDoubleExp_pos k v γ)).2 (by
          simpa only [one_mul] using hD')
    _ = (48 * 65536 * C) * fordTVolumeScale k v γ := by
      unfold fordTVolumeScale
      field_simp

/-- The absolute constant obtained from Lemma 4.1, the clustered-region
estimate, and the two geometric cover sums. -/
noncomputable def fordTConstant (C : ℝ) : ℝ :=
  48 * 65536 * C +
    (512 * (Real.exp 4 * (Real.exp 1) ^ 10) * (C + 1) ^ 2) *
      clusterFactorialConstant * clusterGeomConstant

private lemma fordTConstant_pos {C : ℝ} (hC : 0 < C) :
    0 < fordTConstant C := by
  unfold fordTConstant
  have hCF : 0 < clusterFactorialConstant := by
    unfold clusterFactorialConstant
    positivity
  have hCG : 0 < clusterGeomConstant := clusterGeomConstant_pos
  positivity

private theorem fordT_volume_bound_of_orderQ
    {C : ℝ} (hC : 0 < C)
    (hQ : ∀ (n : ℕ) (a b : ℝ),
      1 ≤ n → 0 ≤ a → 0 ≤ a + b - (n : ℝ) →
      orderQ n a b ≤
        C * (a + 1) * (a + b - (n : ℝ) + 1) ^ 2 / (n : ℝ))
    {k v γ : ℕ} (hk : 1 ≤ k) (hkv : k ≤ 10 * v) :
    (volume (fordT k v γ)).toReal ≤ fordTConstant C * fordTVolumeScale k v γ := by
  have hv : 0 < v := by omega
  have hsplit := volume_fordT_toReal_le_goodPart_add_clusterCover
    (k := k) (v := v) (γ := γ) hv
  have hcover := fordClusterCover_volume_bound_of_orderQ hC hQ
    (k := k) (v := v) (γ := γ) hk hkv
  have hgood : (volume (fordGoodPart k v γ)).toReal ≤
      (48 * 65536 * C) * fordTVolumeScale k v γ := by
    by_cases hlarge : v + γ + 5 ≤ k
    · rw [volume_fordGoodPart_zero hk hv hlarge, ENNReal.toReal_zero]
      have hs : 0 ≤ fordTVolumeScale k v γ := (fordTVolumeScale_pos hk).le
      positivity
    · exact fordGoodPart_volume_bound_small_of_orderQ hC hQ hk (by omega)
  calc
    (volume (fordT k v γ)).toReal ≤
        (volume (fordGoodPart k v γ)).toReal +
          (volume (fordClusterCover k v γ
            (orderStatisticR k v γ))).toReal := hsplit
    _ ≤ (48 * 65536 * C) * fordTVolumeScale k v γ +
        ((512 * (Real.exp 4 * (Real.exp 1) ^ 10) * (C + 1) ^ 2) *
          clusterFactorialConstant * clusterGeomConstant) *
            fordTVolumeScale k v γ := add_le_add hgood hcover
    _ = fordTConstant C * fordTVolumeScale k v γ := by
      unfold fordTConstant
      ring

/-- Ford's Lemma 4.4: the volume of `T(k,v,γ)` has the stated
double-exponential order-statistic bound, with an absolute constant. -/
theorem fordT_volume_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (k v γ : ℕ),
      1 ≤ k → k ≤ 10 * v →
      (volume (fordT k v γ)).toReal ≤
        C * orderStatisticY k v γ /
          (orderStatisticDoubleExp k v γ * ((k + 1).factorial : ℝ)) := by
  obtain ⟨C, hC, hQ⟩ := ford_orderQ_bound
  refine ⟨fordTConstant C, fordTConstant_pos hC, ?_⟩
  intro k v γ hk hkv
  have h := fordT_volume_bound_of_orderQ hC hQ
    (k := k) (v := v) (γ := γ) hk hkv
  unfold fordTVolumeScale at h
  calc
    (volume (fordT k v γ)).toReal ≤
        fordTConstant C *
          (orderStatisticY k v γ /
            (orderStatisticDoubleExp k v γ * ((k + 1).factorial : ℝ))) := h
    _ = fordTConstant C * orderStatisticY k v γ /
          (orderStatisticDoubleExp k v γ * ((k + 1).factorial : ℝ)) := by ring

end Erdos896.Ford
