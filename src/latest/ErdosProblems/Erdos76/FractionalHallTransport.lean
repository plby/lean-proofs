/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences

/-!
# Fractional Hall transport with one forbidden diagonal

The small-universal-set branch of Gruslys--Letzter case D7 uses a
capacitated fractional matching in the complete bipartite graph with the
diagonal removed, together with one extra left vertex adjacent to every
right vertex.  This file proves that finite transport lemma without an LP
oracle.  Integral capacities are cloned and matched by Hall's theorem; real
capacities are obtained from floor/ceiling approximations and compactness.
-/

open Finset Filter Set
open scoped BigOperators Topology

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A cloned left token.  `none` is the extra unrestricted source, while
`some i` is forbidden from using right fiber `i`. -/
abbrev HallLeftToken (r : Option I → ℕ) := Σ x, Fin (r x)

/-- A cloned right capacity token. -/
abbrev HallRightToken (c : I → ℕ) := Σ x, Fin (c x)

/-- The allowed right tokens for one cloned left token. -/
def offDiagonalAllowed (c : I → ℕ) {r : Option I → ℕ}
    (x : HallLeftToken r) : Finset (HallRightToken c) :=
  Finset.univ.filter fun y ↦ match x.1 with
    | none => True
    | some i => y.1 ≠ i

@[simp] lemma mem_offDiagonalAllowed {c : I → ℕ} {r : Option I → ℕ}
    (x : HallLeftToken r) (y : HallRightToken c) :
    y ∈ offDiagonalAllowed c x ↔ match x.1 with
      | none => True
      | some i => y.1 ≠ i := by
  simp [offDiagonalAllowed]

private def hallRightFiberEquiv (c : I → ℕ) (i : I) :
    {y : HallRightToken c // y.1 = i} ≃ Fin (c i) where
  toFun y := Fin.cast (congrArg c y.property) y.1.2
  invFun q := ⟨⟨i, q⟩, rfl⟩
  left_inv y := by
    rcases y with ⟨⟨j, q⟩, hji⟩
    cases hji
    rfl
  right_inv q := rfl

private lemma card_hallRightFiber (c : I → ℕ) (i : I) :
    ((Finset.univ : Finset (HallRightToken c)).filter
      (fun y ↦ y.1 = i)).card = c i := by
  let e : {y : HallRightToken c // y ∈
      ((Finset.univ : Finset (HallRightToken c)).filter
        (fun y ↦ y.1 = i))} ≃ Fin (c i) :=
    { toFun := fun y ↦ Fin.cast
        (congrArg c (Finset.mem_filter.mp y.property).2) y.1.2
      invFun := fun q ↦ ⟨⟨i, q⟩, by simp⟩
      left_inv := by
        rintro ⟨⟨j, q⟩, hj⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        cases hj
        rfl
      right_inv := fun _ ↦ rfl }
  rw [← Fintype.card_coe, Fintype.card_congr e]
  simp

private lemma card_hallRightExcluding (c : I → ℕ) (i : I) :
    ((Finset.univ : Finset (HallRightToken c)).filter
      (fun y ↦ y.1 ≠ i)).card = (∑ j, c j) - c i := by
  let same := (Finset.univ : Finset (HallRightToken c)).filter
    (fun y ↦ y.1 = i)
  have hcompl : (Finset.univ : Finset (HallRightToken c)).filter
      (fun y ↦ y.1 ≠ i) = sameᶜ := by
    ext y
    simp [same]
  rw [hcompl, Finset.card_compl, card_hallRightFiber]
  simp [HallRightToken]

private lemma card_hallLeftFiber (r : Option I → ℕ) (src : Option I) :
    ((Finset.univ : Finset (HallLeftToken r)).filter
      (fun x ↦ x.1 = src)).card = r src := by
  let e : {x : HallLeftToken r // x ∈
      ((Finset.univ : Finset (HallLeftToken r)).filter
        (fun x ↦ x.1 = src))} ≃ Fin (r src) :=
    { toFun := fun x ↦ Fin.cast
        (congrArg r (Finset.mem_filter.mp x.property).2) x.1.2
      invFun := fun q ↦ ⟨⟨src, q⟩, by simp⟩
      left_inv := by
        rintro ⟨⟨j, q⟩, hj⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        cases hj
        rfl
      right_inv := fun _ ↦ rfl }
  rw [← Fintype.card_coe, Fintype.card_congr e]
  simp

private lemma card_finset_le_leftFiber {r : Option I → ℕ}
    {S : Finset (HallLeftToken r)} {src : Option I}
    (hsrc : ∀ x ∈ S, x.1 = src) : S.card ≤ r src := by
  calc
    S.card ≤ ((Finset.univ : Finset (HallLeftToken r)).filter
        (fun x ↦ x.1 = src)).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hsrc x hx
    _ = r src := card_hallLeftFiber r src

/-- Integral Hall transport.  The output records how many cloned tokens of
each source use each right fiber. -/
theorem exists_offDiagonalTransport_nat (r : Option I → ℕ) (c : I → ℕ)
    (htotal : (∑ src, r src) ≤ ∑ j, c j)
    (hsingle : ∀ i, r (some i) ≤ (∑ j, c j) - c i) :
    ∃ N : Option I → I → ℕ,
      (∀ src, ∑ j, N src j = r src) ∧
      (∀ i, N (some i) i = 0) ∧
      (∀ j, (∑ src, N src j) ≤ c j) := by
  classical
  let allowed : HallLeftToken r → Finset (HallRightToken c) :=
    offDiagonalAllowed c
  have hHall : ∀ S : Finset (HallLeftToken r),
      S.card ≤ (S.biUnion allowed).card := by
    intro S
    let labels : Finset (Option I) := S.image Sigma.fst
    by_cases htwo : 2 ≤ labels.card
    · have hfull : S.biUnion allowed = Finset.univ := by
        ext y
        simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
        have herase : (labels.erase (some y.1)).Nonempty := by
          rw [← Finset.card_pos]
          by_cases hmem : some y.1 ∈ labels
          · rw [Finset.card_erase_of_mem hmem]
            omega
          · simp only [Finset.erase_eq_self.mpr hmem]
            omega
        obtain ⟨src, hsrc⟩ := herase
        have hsrcLabel : src ∈ labels := Finset.mem_of_mem_erase hsrc
        have hsrcNe : src ≠ some y.1 := Finset.ne_of_mem_erase hsrc
        obtain ⟨x, hxS, hxsrc⟩ := Finset.mem_image.mp hsrcLabel
        refine ⟨x, hxS, ?_⟩
        rcases src with _ | i
        · simpa [allowed, offDiagonalAllowed, hxsrc]
        · have hiy : i ≠ y.1 := by
            intro h
            apply hsrcNe
            simp [h]
          simpa [allowed, offDiagonalAllowed, hxsrc] using hiy.symm
      rw [hfull, Finset.card_univ]
      calc
        S.card ≤ Fintype.card (HallLeftToken r) := Finset.card_le_univ S
        _ = ∑ src, r src := by simp [HallLeftToken]
        _ ≤ ∑ j, c j := htotal
        _ = Fintype.card (HallRightToken c) := by simp [HallRightToken]
    · have hlabels : labels.card ≤ 1 := by omega
      by_cases hS : S.Nonempty
      · obtain ⟨x, hxS⟩ := hS
        rcases hx : x.1 with _ | i
        · have hfull : S.biUnion allowed = Finset.univ := by
            ext y
            simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
            refine ⟨x, hxS, ?_⟩
            simp [allowed, offDiagonalAllowed, hx]
          rw [hfull, Finset.card_univ]
          calc
            S.card ≤ Fintype.card (HallLeftToken r) := Finset.card_le_univ S
            _ = ∑ src, r src := by simp [HallLeftToken]
            _ ≤ ∑ j, c j := htotal
            _ = Fintype.card (HallRightToken c) := by simp [HallRightToken]
        · have hsource : ∀ q ∈ S, q.1 = some i := by
            intro q hqS
            have hqLabel : q.1 ∈ labels :=
              Finset.mem_image.mpr ⟨q, hqS, rfl⟩
            have hxLabel : x.1 ∈ labels :=
              Finset.mem_image.mpr ⟨x, hxS, rfl⟩
            have heq := Finset.card_le_one.mp hlabels q.1 hqLabel x.1 hxLabel
            simpa only [hx] using heq
          let excluding := (Finset.univ : Finset (HallRightToken c)).filter
            (fun y ↦ y.1 ≠ i)
          have hunion : S.biUnion allowed = excluding := by
            ext y
            constructor
            · intro hy
              obtain ⟨q, hqS, hyq⟩ := Finset.mem_biUnion.mp hy
              have hqi := hsource q hqS
              simpa [excluding, allowed, offDiagonalAllowed, hqi] using hyq
            · intro hy
              refine Finset.mem_biUnion.mpr ⟨x, hxS, ?_⟩
              simpa [excluding, allowed, offDiagonalAllowed, hx] using hy
          rw [hunion, card_hallRightExcluding]
          exact (card_finset_le_leftFiber hsource).trans (hsingle i)
      · simp only [Finset.not_nonempty_iff_eq_empty] at hS
        simp [hS]
  obtain ⟨f, hf, hallowed⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' allowed).mp hHall
  let N : Option I → I → ℕ := fun src j ↦
    ((Finset.univ : Finset (HallLeftToken r)).filter fun x ↦
      x.1 = src ∧ (f x).1 = j).card
  refine ⟨N, ?_, ?_, ?_⟩
  · intro src
    calc
      (∑ j, N src j) =
          ∑ j, ∑ x : HallLeftToken r,
            if x.1 = src ∧ (f x).1 = j then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        simp [N]
      _ = ∑ x : HallLeftToken r, ∑ j,
            if x.1 = src ∧ (f x).1 = j then 1 else 0 :=
        Finset.sum_comm
      _ = ∑ x : HallLeftToken r, if x.1 = src then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hxs : x.1 = src
        · simp [hxs]
        · simp [hxs]
      _ = r src := by
        rw [← card_hallLeftFiber r src]
        simp
  · intro i
    change ((Finset.univ : Finset (HallLeftToken r)).filter fun x ↦
      x.1 = some i ∧ (f x).1 = i).card = 0
    rw [Finset.card_eq_zero]
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxi, hfi⟩
      have ha := hallowed x
      rw [mem_offDiagonalAllowed, hxi] at ha
      exact (ha hfi).elim
    · intro hx
      simpa using hx
  · intro j
    let T := (Finset.univ : Finset (HallLeftToken r)).filter fun x ↦
      (f x).1 = j
    have hsum : (∑ src, N src j) = T.card := by
      calc
        (∑ src, N src j) =
            ∑ src, ∑ x : HallLeftToken r,
              if x.1 = src ∧ (f x).1 = j then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro src _
          simp [N]
        _ = ∑ x : HallLeftToken r, ∑ src,
              if x.1 = src ∧ (f x).1 = j then 1 else 0 :=
          Finset.sum_comm
        _ = ∑ x : HallLeftToken r, if (f x).1 = j then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hxj : (f x).1 = j
          · simp [hxj]
          · simp [hxj]
        _ = T.card := by simp [T]
    rw [hsum]
    rw [← Fintype.card_coe]
    let emb : {x : HallLeftToken r // x ∈ T} ↪
        {y : HallRightToken c // y.1 = j} :=
      ⟨fun x ↦ ⟨f x.1, (Finset.mem_filter.mp x.property).2⟩,
        fun x y hxy ↦ by
          apply Subtype.ext
          apply hf
          exact congrArg Subtype.val hxy⟩
    calc
      Fintype.card {x : HallLeftToken r // x ∈ T} ≤
          Fintype.card {y : HallRightToken c // y.1 = j} :=
        Fintype.card_le_of_injective emb emb.injective
      _ = Fintype.card (Fin (c j)) :=
        Fintype.card_congr (hallRightFiberEquiv c j)
      _ = c j := by simp

/-! ## Passage to arbitrary real capacities -/

/-- Lower rational approximation with denominator `k+1`. -/
def hallLowerApprox (x : ℝ) (k : ℕ) : ℝ :=
  (Nat.floor (((k + 1 : ℕ) : ℝ) * x) : ℝ) / (k + 1 : ℕ)

/-- Upper rational approximation with denominator `k+1`. -/
def hallUpperApprox (x : ℝ) (k : ℕ) : ℝ :=
  (Nat.ceil (((k + 1 : ℕ) : ℝ) * x) : ℝ) / (k + 1 : ℕ)

lemma hallLowerApprox_nonneg (x : ℝ) (k : ℕ) :
    0 ≤ hallLowerApprox x k := by
  unfold hallLowerApprox
  positivity

lemma hallLowerApprox_le {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    hallLowerApprox x k ≤ x := by
  unfold hallLowerApprox
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  apply (div_le_iff₀ hk).mpr
  simpa [mul_comm] using
    (Nat.floor_le (mul_nonneg (by positivity) hx) :
      (Nat.floor (((k + 1 : ℕ) : ℝ) * x) : ℝ) ≤
        ((k + 1 : ℕ) : ℝ) * x)

lemma hallLowerApprox_lt_add_inv {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    x < hallLowerApprox x k + 1 / (k + 1 : ℕ) := by
  unfold hallLowerApprox
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  calc
    x = (((k + 1 : ℕ) : ℝ) * x) / (k + 1 : ℕ) := by
      field_simp
    _ < ((Nat.floor (((k + 1 : ℕ) : ℝ) * x) : ℝ) + 1) /
        (k + 1 : ℕ) :=
      (div_lt_div_iff_of_pos_right hk).mpr (Nat.lt_floor_add_one _)
    _ = (Nat.floor (((k + 1 : ℕ) : ℝ) * x) : ℝ) /
          (k + 1 : ℕ) + 1 / (k + 1 : ℕ) := by ring

lemma hallUpperApprox_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ hallUpperApprox x k := by
  unfold hallUpperApprox
  positivity

lemma le_hallUpperApprox {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    x ≤ hallUpperApprox x k := by
  unfold hallUpperApprox
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  apply (le_div_iff₀ hk).mpr
  simpa [mul_comm] using
    (Nat.le_ceil (((k + 1 : ℕ) : ℝ) * x))

lemma hallUpperApprox_lt_add_inv {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    hallUpperApprox x k < x + 1 / (k + 1 : ℕ) := by
  unfold hallUpperApprox
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  apply (div_lt_iff₀ hk).mpr
  calc
    (Nat.ceil (((k + 1 : ℕ) : ℝ) * x) : ℝ) <
        ((k + 1 : ℕ) : ℝ) * x + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg (by positivity) hx)
    _ = (x + 1 / (k + 1 : ℕ)) * (k + 1 : ℕ) := by
      field_simp

lemma tendsto_hallLowerApprox (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (hallLowerApprox x) atTop (𝓝 x) := by
  have hlow : Tendsto (fun k : ℕ ↦ x - 1 / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 x) := by
    simpa only [Nat.cast_add, Nat.cast_one, sub_zero] using
      tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hupp : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
  · intro k
    linarith [hallLowerApprox_lt_add_inv hx k]
  · exact fun k ↦ hallLowerApprox_le hx k

lemma tendsto_hallUpperApprox (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (hallUpperApprox x) atTop (𝓝 x) := by
  have hlow : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x) := tendsto_const_nhds
  have hupp : Tendsto (fun k : ℕ ↦ x + 1 / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 x) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_zero] using
      tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
  · exact fun k ↦ le_hallUpperApprox hx k
  · exact fun k ↦ (hallUpperApprox_lt_add_inv hx k).le

/-- Fractional Hall transport in the complete bipartite graph minus its
diagonal, with one unrestricted source `none`.  Source masses are saturated,
right capacities are respected, and diagonal entries vanish exactly. -/
theorem exists_offDiagonalTransport_real
    (d : Option I → ℝ) (c : I → ℝ)
    (hd : ∀ src, 0 ≤ d src) (hc : ∀ i, 0 ≤ c i)
    (htotal : (∑ src, d src) ≤ ∑ i, c i)
    (hsingle : ∀ i, d (some i) ≤ (∑ j, c j) - c i) :
    ∃ μ : Option I → I → ℝ,
      (∀ src i, 0 ≤ μ src i) ∧
      (∀ src, ∑ i, μ src i = d src) ∧
      (∀ i, μ (some i) i = 0) ∧
      (∀ i, (∑ src, μ src i) ≤ c i) := by
  classical
  let r : ℕ → Option I → ℕ := fun k src ↦
    Nat.floor (((k + 1 : ℕ) : ℝ) * d src)
  let q : ℕ → I → ℕ := fun k i ↦
    Nat.ceil (((k + 1 : ℕ) : ℝ) * c i)
  have htotalNat : ∀ k, (∑ src, r k src) ≤ ∑ i, q k i := by
    intro k
    apply_mod_cast show (∑ src, (r k src : ℝ)) ≤
      ∑ i, (q k i : ℝ) from ?_
    calc
      (∑ src, (r k src : ℝ)) ≤
          ∑ src, ((k + 1 : ℕ) : ℝ) * d src := by
        apply Finset.sum_le_sum
        intro src _
        exact Nat.floor_le (mul_nonneg (by positivity) (hd src))
      _ = ((k + 1 : ℕ) : ℝ) * ∑ src, d src := by
        rw [Finset.mul_sum]
      _ ≤ ((k + 1 : ℕ) : ℝ) * ∑ i, c i :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
      _ = ∑ i, ((k + 1 : ℕ) : ℝ) * c i := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i, (q k i : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.le_ceil _
  have hsingleNat : ∀ k i,
      r k (some i) ≤ (∑ j, q k j) - q k i := by
    intro k i
    have hdecomp : (∑ j, q k j) =
        (∑ j ∈ (Finset.univ : Finset I).erase i, q k j) + q k i := by
      simpa [add_comm] using
        (Finset.sum_erase_add (Finset.univ : Finset I) (q k)
          (Finset.mem_univ i)).symm
    rw [hdecomp, Nat.add_sub_cancel_right]
    apply_mod_cast show (r k (some i) : ℝ) ≤
      ∑ j ∈ (Finset.univ : Finset I).erase i, (q k j : ℝ) from ?_
    have hsumErase : (∑ j ∈ (Finset.univ : Finset I).erase i, c j) =
        (∑ j, c j) - c i := by
      have h := Finset.sum_erase_add (Finset.univ : Finset I) c
        (Finset.mem_univ i)
      simpa using (eq_sub_of_add_eq h)
    calc
      (r k (some i) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * d (some i) :=
        Nat.floor_le (mul_nonneg (by positivity) (hd _))
      _ ≤ ((k + 1 : ℕ) : ℝ) * ((∑ j, c j) - c i) :=
        mul_le_mul_of_nonneg_left (hsingle i) (by positivity)
      _ = ∑ j ∈ (Finset.univ : Finset I).erase i,
          ((k + 1 : ℕ) : ℝ) * c j := by
        rw [← hsumErase, Finset.mul_sum]
      _ ≤ ∑ j ∈ (Finset.univ : Finset I).erase i, (q k j : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        exact Nat.le_ceil _
  have hex : ∀ k, ∃ N : Option I → I → ℕ,
      (∀ src, ∑ j, N src j = r k src) ∧
      (∀ i, N (some i) i = 0) ∧
      (∀ j, (∑ src, N src j) ≤ q k j) := by
    intro k
    exact exists_offDiagonalTransport_nat (r k) (q k) (htotalNat k)
      (hsingleNat k)
  choose N hrow hdiag hcol using hex
  let μk : ℕ → Option I → I → ℝ := fun k src i ↦
    (N k src i : ℝ) / (k + 1 : ℕ)
  let M : ℝ := ∑ src, d src + 1
  let K : Set (Option I → I → ℝ) :=
    Set.Icc (fun _ _ ↦ 0) (fun _ _ ↦ M)
  have hμkK : ∀ k, μk k ∈ K := by
    intro k
    constructor
    · intro src i
      dsimp only [μk]
      positivity
    · intro src i
      have hden : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      have hentry : N k src i ≤ ∑ j, N k src j :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      have hentryR : (N k src i : ℝ) ≤
          (Nat.floor (((k + 1 : ℕ) : ℝ) * d src) : ℝ) := by
        exact_mod_cast hentry.trans_eq (hrow k src)
      have happrox : μk k src i ≤ d src := by
        dsimp only [μk, r] at hentryR ⊢
        apply (div_le_iff₀ hden).mpr
        calc
          (N k src i : ℝ) ≤
              (Nat.floor (((k + 1 : ℕ) : ℝ) * d src) : ℝ) := hentryR
          _ ≤ ((k + 1 : ℕ) : ℝ) * d src :=
            Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (hd src))
          _ = d src * (k + 1 : ℕ) := by ring
      have hsrcSum : d src ≤ ∑ x, d x :=
        Finset.single_le_sum (fun x _ ↦ hd x) (Finset.mem_univ src)
      exact happrox.trans (hsrcSum.trans (le_add_of_nonneg_right zero_le_one))
  obtain ⟨μ, hμK, φ, hφ, hlim⟩ :=
    (isCompact_Icc : IsCompact K).tendsto_subseq hμkK
  refine ⟨μ, ?_, ?_, ?_, ?_⟩
  · intro src i
    exact hμK.1 src i
  · intro src
    have hrows : Tendsto
        (fun n ↦ ∑ i, μk (φ n) src i) atTop (𝓝 (∑ i, μ src i)) := by
      apply tendsto_finsetSum
      intro i _
      simpa only [Function.comp_apply] using
        (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim src) i)
    have heq : ∀ n, (∑ i, μk (φ n) src i) =
        hallLowerApprox (d src) (φ n) := by
      intro n
      dsimp only [μk, hallLowerApprox, r]
      rw [← Finset.sum_div]
      congr 1
      exact_mod_cast hrow (φ n) src
    have htarget := (tendsto_hallLowerApprox (d src) (hd src)).comp
      hφ.tendsto_atTop
    exact tendsto_nhds_unique hrows
      (htarget.congr' (Filter.Eventually.of_forall fun n ↦ (heq n).symm))
  · intro i
    have hpoint := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim (some i)) i
    have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds
    have heq : ∀ n, μk (φ n) (some i) i = 0 := by
      intro n
      dsimp only [μk]
      rw [hdiag]
      norm_num
    exact tendsto_nhds_unique hpoint
      (hzero.congr' (Filter.Eventually.of_forall fun n ↦ (heq n).symm))
  · intro i
    have hcols : Tendsto
        (fun n ↦ ∑ src, μk (φ n) src i) atTop
        (𝓝 (∑ src, μ src i)) := by
      apply tendsto_finsetSum
      intro src _
      simpa only [Function.comp_apply] using
        (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim src) i)
    have hcaps := (tendsto_hallUpperApprox (c i) (hc i)).comp
      hφ.tendsto_atTop
    apply le_of_tendsto_of_tendsto' hcols hcaps
    intro n
    have hden : (0 : ℝ) < ((φ n + 1 : ℕ) : ℝ) := by positivity
    dsimp only [μk, hallUpperApprox, q]
    rw [← Finset.sum_div]
    exact (div_le_div_iff_of_pos_right hden).mpr (by exact_mod_cast hcol (φ n) i)

end

end Erdos76
