/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.CentralExtractor

/-!
# Endpoint orientation for the density endgame of Erdős Problem 874

This file proves the endpoint orientation that is implicit in the second
pigeonhole comparison of Deshouillers--Freiman.  The proof continuously
replaces the first `u` outer entries by the last `u` outer entries.  At the
first replacement where the left endpoints of the two dense layers cross,
the pigeonhole comparison can be applied on the two sides of the crossing.
The replacement gap is at most `N - 1`, whereas the central restricted-sum
layer has width much larger than `N / 2` at the eventual scales.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The mixed outer supports -/

/-- At time `t`, use the `t` largest outer entries and the remaining
`u - t` smallest outer entries. -/
def mixedOuterIndex (K t i : ℕ) : ℕ :=
  if i < t then K - 1 - i else i

def mixedOuterFinset {N : ℕ} {A : Finset ℤ}
    (D : OrderedCentralBlock N A) (t : ℕ) : Finset ℤ :=
  Finset.image (fun i ↦ D.a (mixedOuterIndex A.card t i))
    (Finset.range D.u)

def mixedOuterSum (a : ℕ → ℤ) (K u t : ℕ) : ℤ :=
  orderedInitialSum a u +
    ∑ i ∈ Finset.range t, (a (K - 1 - i) - a i)

private theorem mixedOuterIndex_lt
    {K u t i : ℕ} (hcentral : 2 * u + 1 < K)
    (ht : t ≤ u) (hi : i < u) : mixedOuterIndex K t i < K := by
  unfold mixedOuterIndex
  split_ifs <;> omega

private theorem mixedOuterIndex_injective
    {K u t i j : ℕ} (hcentral : 2 * u + 1 < K)
    (ht : t ≤ u) (hi : i < u) (hj : j < u)
    (hij : mixedOuterIndex K t i = mixedOuterIndex K t j) : i = j := by
  unfold mixedOuterIndex at hij
  split_ifs at hij <;> omega

theorem OrderedCentralBlock.card_mixedOuterFinset
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    {t : ℕ} (ht : t ≤ D.u) :
    (mixedOuterFinset D t).card = D.u := by
  unfold mixedOuterFinset
  rw [Finset.card_image_iff.mpr]
  · exact Finset.card_range _
  · intro i hi j hj ha
    apply mixedOuterIndex_injective D.central_nonempty ht
        (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
    exact D.separated.eq_of_eq D.q_pos
      (mixedOuterIndex_lt D.central_nonempty ht (Finset.mem_range.mp hi))
      (mixedOuterIndex_lt D.central_nonempty ht (Finset.mem_range.mp hj)) ha

theorem OrderedCentralBlock.mixedOuterFinset_subset
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    {t : ℕ} (ht : t ≤ D.u) : mixedOuterFinset D t ⊆ A := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact D.entry_mem (mixedOuterIndex_lt D.central_nonempty ht
    (Finset.mem_range.mp hi))

theorem OrderedCentralBlock.mixedOuter_disjoint_central
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    {t : ℕ} (ht : t ≤ D.u) :
    Disjoint (mixedOuterFinset D t) D.centralFinset := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hy
  have hiu := Finset.mem_range.mp hi
  have hjT := Finset.mem_range.mp hj
  have hidx := mixedOuterIndex_lt D.central_nonempty ht hiu
  have hcentralIdx : D.u + j < A.card := by omega
  have heq : mixedOuterIndex A.card t i = D.u + j :=
    D.separated.eq_of_eq D.q_pos hidx hcentralIdx (hix.trans hjx.symm)
  unfold mixedOuterIndex at heq
  split_ifs at heq <;> omega

private theorem sum_mixedOuterFinset
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    {t : ℕ} (ht : t ≤ D.u) :
    ∑ x ∈ mixedOuterFinset D t, x =
      ∑ i ∈ Finset.range D.u, D.a (mixedOuterIndex A.card t i) := by
  rw [mixedOuterFinset, Finset.sum_image]
  intro i hi j hj ha
  apply mixedOuterIndex_injective D.central_nonempty ht
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
  exact D.separated.eq_of_eq D.q_pos
    (mixedOuterIndex_lt D.central_nonempty ht (Finset.mem_range.mp hi))
    (mixedOuterIndex_lt D.central_nonempty ht (Finset.mem_range.mp hj)) ha

private theorem sum_selected_zero (a : ℕ → ℤ) (K u : ℕ) :
    ∑ i ∈ Finset.range u, a (mixedOuterIndex K 0 i) =
      orderedInitialSum a u := by
  simp [mixedOuterIndex, orderedInitialSum]

private theorem sum_selected_succ
    (a : ℕ → ℤ) {K u t : ℕ} (ht : t < u) :
    (∑ i ∈ Finset.range u, a (mixedOuterIndex K (t + 1) i)) =
      (∑ i ∈ Finset.range u, a (mixedOuterIndex K t i)) +
        (a (K - 1 - t) - a t) := by
  let S : Finset ℕ := (Finset.range u).erase t
  have htmem : t ∈ Finset.range u := Finset.mem_range.mpr ht
  have htS : t ∉ S := by simp [S]
  have hsplit : insert t S = Finset.range u := by
    simp [S, htmem]
  have htnew : mixedOuterIndex K (t + 1) t = K - 1 - t := by
    simp [mixedOuterIndex]
  have htold : mixedOuterIndex K t t = t := by
    simp [mixedOuterIndex]
  calc
    (∑ i ∈ Finset.range u, a (mixedOuterIndex K (t + 1) i)) =
        a (mixedOuterIndex K (t + 1) t) +
          ∑ i ∈ S, a (mixedOuterIndex K (t + 1) i) := by
            rw [← hsplit, Finset.sum_insert htS]
    _ = a (K - 1 - t) +
          ∑ i ∈ S, a (mixedOuterIndex K t i) := by
            rw [htnew]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            have hit : i ≠ t := (Finset.mem_erase.mp hi).1
            by_cases hitlt : i < t
            · have hisucc : i < t + 1 := by omega
              simp [mixedOuterIndex, hitlt, hisucc]
            · have hnotSucc : ¬i < t + 1 := by omega
              simp [mixedOuterIndex, hitlt, hnotSucc]
    _ = (a t + ∑ i ∈ S, a (mixedOuterIndex K t i)) +
          (a (K - 1 - t) - a t) := by ring
    _ = (∑ i ∈ Finset.range u, a (mixedOuterIndex K t i)) +
          (a (K - 1 - t) - a t) := by
            rw [← hsplit, Finset.sum_insert htS, htold]

theorem OrderedCentralBlock.sum_mixedOuterFinset_eq
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    {t : ℕ} (ht : t ≤ D.u) :
    ∑ x ∈ mixedOuterFinset D t, x =
      mixedOuterSum D.a A.card D.u t := by
  rw [sum_mixedOuterFinset D ht]
  induction t with
  | zero => simp [mixedOuterSum, sum_selected_zero]
  | succ t ih =>
      have htu : t < D.u := by omega
      rw [sum_selected_succ D.a htu, ih (by omega)]
      simp only [mixedOuterSum, Finset.sum_range_succ]
      ring

@[simp] theorem mixedOuterSum_zero (a : ℕ → ℤ) (K u : ℕ) :
    mixedOuterSum a K u 0 = orderedInitialSum a u := by
  simp [mixedOuterSum]

theorem mixedOuterSum_succ (a : ℕ → ℤ) (K u t : ℕ) :
    mixedOuterSum a K u (t + 1) = mixedOuterSum a K u t +
      (a (K - 1 - t) - a t) := by
  simp [mixedOuterSum, Finset.sum_range_succ]
  ring

theorem mixedOuterSum_eq_terminal
    (a : ℕ → ℤ) {K u : ℕ} :
    mixedOuterSum a K u u = orderedTerminalSum a K u := by
  simp only [mixedOuterSum, orderedInitialSum, orderedTerminalSum,
    Finset.sum_sub_distrib]
  ring

/-! ## The abstract two-sided crossing argument -/

/-- If every intermediate outer support gives disjoint translates of two
locally dense layers, the first crossing of their left endpoints forces the
central layer width to be at most half of one replacement gap plus the two
local-density errors. -/
theorem endpoint_order_of_mixed_shift_crossing
    {X Y : Finset ℤ}
    {mX MX mY MY residue G q N : ℤ} {R u : ℕ}
    (hq : 0 < q)
    (hdensityX : HasLocalDensity X mX MX residue q R)
    (hdensityY : HasLocalDensity Y mY MY residue q R)
    (hmX : Int.ModEq q mX residue)
    (hMX : Int.ModEq q MX residue)
    (hmY : Int.ModEq q mY residue)
    (hMY : Int.ModEq q MY residue)
    (hXwidth : mX + q * (2 * R : ℕ) ≤ MX)
    (hYwidth : mY + q * (2 * R : ℕ) ≤ MY)
    (F : ℕ → ℤ)
    (hFzero : F 0 = G)
    (hFmod : ∀ t ≤ u, Int.ModEq q (F t) G)
    (hdisjoint : ∀ t ≤ u,
      Disjoint (translateFinset (F t) X) (translateFinset G Y))
    (hstep : ∀ t < u, F (t + 1) - F t ≤ N - 1)
    (hbase : mX ≤ mY)
    (hwidthMono : MX - mX ≤ MY - mY)
    (hscale : N - 1 + 2 * ((2 * (R : ℤ) - 1) * q) <
      2 * (MX - mX)) :
    F u + mX ≤ G + mY := by
  by_contra hnot
  have huCross : G + mY < F u + mX := lt_of_not_ge hnot
  have hex : ∃ n : ℕ, G + mY < F n + mX := ⟨u, huCross⟩
  let n : ℕ := Nat.find hex
  have hnCross : G + mY < F n + mX := Nat.find_spec hex
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0, hFzero] at hnCross
    linarith
  have hnu : n ≤ u := by
    apply Nat.find_min'
    exact huCross
  let t : ℕ := n - 1
  have htn : t + 1 = n := by dsimp [t]; omega
  have htu : t < u := by omega
  have htBefore : F t + mX ≤ G + mY := by
    by_contra ht
    have ht' : G + mY < F t + mX := lt_of_not_ge ht
    have hnle : n ≤ t := Nat.find_min' hex ht'
    dsimp [t] at hnle
    omega
  have htAfter : G + mY ≤ F (t + 1) + mX := by
    rw [htn]
    exact hnCross.le
  have common_mod (r : ℕ) (hr : r ≤ u) : Int.ModEq q (F r) G :=
    hFmod r hr
  have forward_cross_residue :
      (G + mY - F t) % q = residue % q := by
    have h' : Int.ModEq q (G + mY - F t) residue := by
      convert ((Int.ModEq.refl G).add hmY).sub (common_mod t htu.le)
        using 1 <;> ring
    exact h'
  have forward_align : q ∣ (F t + MX) - (G + mY) := by
    have hmod : Int.ModEq q (F t + MX) (G + mY) :=
      ((common_mod t htu.le).add hMX).trans
        ((Int.ModEq.refl G).add hmY).symm
    rw [← neg_sub]
    exact dvd_neg.mpr (Int.modEq_iff_dvd.mp hmod)
  have hforward := second_pigeonhole_bound_of_localDensity hq
    hdensityX hdensityY forward_cross_residue hmY htBefore hYwidth
    forward_align (hdisjoint t htu.le)
  have reverse_cross_residue :
      (F (t + 1) + mX - G) % q = residue % q := by
    have h' : Int.ModEq q (F (t + 1) + mX - G) residue := by
      convert ((common_mod (t + 1) (by omega)).add hmX).sub
        (Int.ModEq.refl G) using 1 <;> ring
    exact h'
  have reverse_align : q ∣ (G + MY) - (F (t + 1) + mX) := by
    exact Int.modEq_iff_dvd.mp
      (((common_mod (t + 1) (by omega)).add hmX).trans
        (((Int.ModEq.refl G).add hMY).symm))
  have hreverse := second_pigeonhole_bound_of_localDensity hq
    hdensityY hdensityX reverse_cross_residue hmX htAfter hXwidth
    reverse_align (hdisjoint (t + 1) (by omega)).symm
  dsimp [SecondPigeonholeBound] at hforward hreverse
  have hgap := hstep t htu
  linarith

/-! ## The ordered central-block specialization -/

/-- The finite endpoint-orientation theorem used by the DF99 density
endgame.  Its last hypothesis is exactly the scale inequality supplied by
`central_orientation_signed_gap_int`. -/
theorem OrderedCentralBlock.left_endpoints_ordered_of_orientation_scale
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    (hA : IsBoundedAdmissible N A)
    (hcongr : ∀ i < A.card,
      Int.ModEq (D.q : ℤ) (D.a i) (D.a D.u))
    (hlocal : 4 * D.R + 3 + D.q ≤ D.L - D.u)
    (hscale : (N : ℤ) - 1 +
        2 * ((2 * (D.R : ℤ) - 1) * (D.q : ℤ)) <
      2 * (D.q : ℤ) * (D.L - D.u : ℕ) *
        ((A.card - 2 * D.u - (D.L - D.u) : ℕ) : ℤ)) :
    orderedTerminalSum D.a A.card D.u +
          centralInitialSum D.a D.u (D.L - D.u) ≤
      orderedInitialSum D.a D.u +
          centralInitialSum D.a D.u (D.L - D.u + D.q) := by
  let s : ℕ := D.L - D.u
  let T : ℕ := A.card - 2 * D.u
  let V : Finset ℤ := D.centralFinset
  let X : Finset ℤ := restrictedSumset s V
  let Y : Finset ℤ := restrictedSumset (s + D.q) V
  let mX : ℤ := centralInitialSum D.a D.u s
  let MX : ℤ := centralTerminalSum D.a A.card D.u s
  let mY : ℤ := centralInitialSum D.a D.u (s + D.q)
  let MY : ℤ := centralTerminalSum D.a A.card D.u (s + D.q)
  let residue : ℤ := (s : ℤ) * D.a D.u
  let G : ℤ := orderedInitialSum D.a D.u
  let F : ℕ → ℤ := fun t ↦ mixedOuterSum D.a A.card D.u t
  have hcard := D.card_decomposition
  have htheta := D.theta_cases
  have huL := D.u_le_L
  have hqpos : 0 < D.q := D.q_pos
  have hKT : A.card = 2 * D.u + T := by dsimp [T]; omega
  have hTform : T = 2 * s + D.q + D.θ := by
    dsimp [T, s]
    omega
  have hsT : s ≤ T := by omega
  have hsqT : s + D.q ≤ T := by omega
  have hVeq : V = centralBlock D.a A.card D.u := rfl
  have hdensityX : HasLocalDensity X mX MX residue
      (D.q : ℤ) D.R := by
    dsimp [X, mX, MX, residue]
    rw [hVeq]
    apply centralBlock_hasLocalDensity hqpos D.central_nonempty D.separated
      hcongr D.central_span
    · omega
    · simpa [s] using hlocal
  have hdensityY0 : HasLocalDensity Y mY MY
      (((s + D.q : ℕ) : ℤ) * D.a D.u) (D.q : ℤ) D.R := by
    dsimp [Y, mY, MY]
    rw [hVeq]
    apply centralBlock_hasLocalDensity hqpos D.central_nonempty D.separated
      hcongr D.central_span
    · omega
    · simpa [s] using (show 4 * D.R + 3 + D.q ≤ s + D.q by
        dsimp [s] at hlocal ⊢
        omega)
  have hdrop : Int.ModEq (D.q : ℤ)
      (((s + D.q : ℕ) : ℤ) * D.a D.u) residue := by
    dsimp [residue]
    rw [Int.modEq_iff_dvd]
    refine ⟨-(D.a D.u), ?_⟩
    push_cast
    ring
  have hdensityY : HasLocalDensity Y mY MY residue
      (D.q : ℤ) D.R := by
    intro z hz hlo hhi
    apply hdensityY0 z (hz.trans hdrop.symm) hlo hhi
  have hsumMod : ∀ n : ℕ, n ≤ T →
      Int.ModEq (D.q : ℤ) (centralInitialSum D.a D.u n)
        ((n : ℤ) * D.a D.u) := by
    intro n hn
    have h := Int.ModEq.sum (s := Finset.range n)
      (f := fun i : ℕ ↦ D.a (D.u + i))
      (g := fun _i : ℕ ↦ D.a D.u)
      (fun i hi ↦ hcongr (D.u + i) (by
        have hi' := Finset.mem_range.mp hi
        omega))
    simpa [centralInitialSum, Finset.sum_const, nsmul_eq_mul] using h
  have hterminalMod : ∀ n : ℕ, n ≤ T →
      Int.ModEq (D.q : ℤ) (centralTerminalSum D.a A.card D.u n)
        ((n : ℤ) * D.a D.u) := by
    intro n hn
    have h := Int.ModEq.sum (s := Finset.range n)
      (f := fun i : ℕ ↦ D.a (A.card - D.u - 1 - i))
      (g := fun _i : ℕ ↦ D.a D.u)
      (fun i hi ↦ hcongr (A.card - D.u - 1 - i) (by
        have hi' := Finset.mem_range.mp hi
        omega))
    simpa [centralTerminalSum, Finset.sum_const, nsmul_eq_mul] using h
  have hmX : Int.ModEq (D.q : ℤ) mX residue := by
    simpa [mX, residue] using hsumMod s hsT
  have hMX : Int.ModEq (D.q : ℤ) MX residue := by
    simpa [MX, residue] using hterminalMod s hsT
  have hmY : Int.ModEq (D.q : ℤ) mY residue := by
    have hraw : Int.ModEq (D.q : ℤ) mY
        (((s + D.q : ℕ) : ℤ) * D.a D.u) := by
      simpa [mY] using hsumMod (s + D.q) hsqT
    exact hraw.trans hdrop
  have hMY : Int.ModEq (D.q : ℤ) MY residue := by
    have hraw : Int.ModEq (D.q : ℤ) MY
        (((s + D.q : ℕ) : ℤ) * D.a D.u) := by
      simpa [MY] using hterminalMod (s + D.q) hsqT
    exact hraw.trans hdrop
  have width_of (n : ℕ) (hn : n ≤ T)
      (hR : 2 * D.R ≤ n * (T - n)) :
      centralInitialSum D.a D.u n + (D.q : ℤ) * (2 * D.R : ℕ) ≤
        centralTerminalSum D.a A.card D.u n := by
    have hwidth := central_endpoint_width (a := D.a) (K := A.card)
      (q := D.q) (u := D.u) (T := T) (s := n)
      hqpos hKT hn D.separated
    have hprodZ : ((2 * D.R : ℕ) : ℤ) ≤
        (n : ℤ) * ((T - n : ℕ) : ℤ) := by exact_mod_cast hR
    have hqZ : (0 : ℤ) < D.q := by exact_mod_cast hqpos
    have hscaled := mul_le_mul_of_nonneg_left hprodZ hqZ.le
    push_cast at hscaled
    nlinarith
  have hprodX : 2 * D.R ≤ s * (T - s) := by
    have hRle : 2 * D.R ≤ s := by dsimp [s] at hlocal ⊢; omega
    have hfactor : 1 ≤ T - s := by omega
    nlinarith
  have hprodY : 2 * D.R ≤ (s + D.q) * (T - (s + D.q)) := by
    have hRle : 2 * D.R ≤ s + D.q := by
      dsimp [s] at hlocal ⊢
      omega
    have hfactor : 1 ≤ T - (s + D.q) := by
      rcases htheta with hθ | hθ <;> omega
    nlinarith
  have hXwidth : mX + (D.q : ℤ) * (2 * D.R : ℕ) ≤ MX := by
    simpa [mX, MX] using width_of s hsT hprodX
  have hYwidth : mY + (D.q : ℤ) * (2 * D.R : ℕ) ≤ MY := by
    simpa [mY, MY] using width_of (s + D.q) hsqT hprodY
  have hGmod : Int.ModEq (D.q : ℤ) G
      ((D.u : ℤ) * D.a D.u) := by
    have h := Int.ModEq.sum (s := Finset.range D.u)
      (f := fun i : ℕ ↦ D.a i) (g := fun _i : ℕ ↦ D.a D.u)
      (fun i hi ↦ hcongr i (by
        have hi' := Finset.mem_range.mp hi
        omega))
    simpa [G, orderedInitialSum, Finset.sum_const, nsmul_eq_mul] using h
  have hFzero : F 0 = G := by simp [F, G]
  have hFmod : ∀ t ≤ D.u, Int.ModEq (D.q : ℤ) (F t) G := by
    intro t ht
    have h := Int.ModEq.sum (s := Finset.range D.u)
      (f := fun i : ℕ ↦ D.a (mixedOuterIndex A.card t i))
      (g := fun _i : ℕ ↦ D.a D.u)
      (fun i hi ↦ hcongr (mixedOuterIndex A.card t i)
        (mixedOuterIndex_lt D.central_nonempty ht (Finset.mem_range.mp hi)))
    have hsum : Int.ModEq (D.q : ℤ) (F t)
        ((D.u : ℤ) * D.a D.u) := by
      have heq : F t =
          ∑ i ∈ Finset.range D.u,
            D.a (mixedOuterIndex A.card t i) := by
        dsimp [F]
        rw [← sum_mixedOuterFinset D ht, D.sum_mixedOuterFinset_eq ht]
      rw [heq]
      simpa [Finset.sum_const, nsmul_eq_mul] using h
    exact hsum.trans hGmod.symm
  have hdisjoint : ∀ t ≤ D.u,
      Disjoint (translateFinset (F t) X) (translateFinset G Y) := by
    intro t ht
    have h0 := translated_restrictedSumsets_disjoint_of_admissible
      (A := A) (V := V) (B := mixedOuterFinset D t)
      (C := D.initialFinset) (r := s) (s := s + D.q)
      hA.2 D.centralFinset_subset (D.mixedOuterFinset_subset ht)
      D.initialFinset_subset (D.mixedOuter_disjoint_central ht)
      D.initial_disjoint_central
      (by rw [D.card_mixedOuterFinset ht]; omega)
      (by rw [D.card_initialFinset]; omega)
      (by rw [D.card_mixedOuterFinset ht, D.card_initialFinset]; omega)
    rw [D.sum_mixedOuterFinset_eq ht, D.sum_initialFinset] at h0
    simpa [F, G, X, Y] using h0
  have hstep : ∀ t < D.u, F (t + 1) - F t ≤ (N : ℤ) - 1 := by
    intro t ht
    have htop : D.a (A.card - 1 - t) ≤ (N : ℤ) :=
      D.entry_le_ambient hA (by omega)
    have hbot : (1 : ℤ) ≤ D.a t := D.one_le_entry hA (by omega)
    rw [show F (t + 1) = F t +
        (D.a (A.card - 1 - t) - D.a t) by
      simpa [F] using mixedOuterSum_succ D.a A.card D.u t]
    linarith
  have hbase : mX ≤ mY := by
    have hnonneg : 0 ≤
        ∑ i ∈ Finset.range D.q, D.a (D.u + s + i) := by
      apply Finset.sum_nonneg
      intro i hi
      have hone := D.one_le_entry hA (i := D.u + s + i) (by
        have hi' := Finset.mem_range.mp hi
        have hisT : s + i < T := by omega
        omega)
      omega
    have hmYeq : mY = mX +
        ∑ i ∈ Finset.range D.q, D.a (D.u + s + i) := by
      dsimp [mX, mY, centralInitialSum]
      rw [Finset.sum_range_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega
    rw [hmYeq]
    exact le_add_of_nonneg_right hnonneg
  have hwidthMono : MX - mX ≤ MY - mY := by
    simpa [MX, mX, MY, mY, s] using D.central_endpoint_width_mono
  have hwidthLower :
      (D.q : ℤ) * (s : ℤ) * ((T - s : ℕ) : ℤ) ≤ MX - mX := by
    simpa [MX, mX] using central_endpoint_width (a := D.a) (K := A.card)
      (q := D.q) (u := D.u) (T := T) (s := s)
      hqpos hKT hsT D.separated
  have hscale' : (N : ℤ) - 1 +
      2 * ((2 * (D.R : ℤ) - 1) * (D.q : ℤ)) <
        2 * (MX - mX) := by
    nlinarith [hscale, hwidthLower]
  have horient := endpoint_order_of_mixed_shift_crossing
    (X := X) (Y := Y) (mX := mX) (MX := MX) (mY := mY) (MY := MY)
    (residue := residue) (G := G) (q := (D.q : ℤ)) (N := (N : ℤ))
    (R := D.R) (u := D.u) (by exact_mod_cast hqpos)
    hdensityX hdensityY hmX hMX hmY hMY hXwidth hYwidth F hFzero
    hFmod hdisjoint hstep hbase hwidthMono hscale'
  have hFu : F D.u = orderedTerminalSum D.a A.card D.u := by
    simpa [F] using mixedOuterSum_eq_terminal D.a
  simpa [hFu, G, mX, mY, s] using horient

/-- The orientation repair closes the former final hypothesis of the
concrete density-endgame constructor. -/
theorem densityEndgameData_of_orderedCentralBlock_orientation_scale
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    (hA : IsBoundedAdmissible N A)
    (hcongr : ∀ i < A.card,
      Int.ModEq (D.q : ℤ) (D.a i) (D.a D.u))
    (hlocal : 4 * D.R + 3 + D.q ≤ D.L - D.u)
    (hscale : (N : ℤ) - 1 +
        2 * ((2 * (D.R : ℤ) - 1) * (D.q : ℤ)) <
      2 * (D.q : ℤ) * (D.L - D.u : ℕ) *
        ((A.card - 2 * D.u - (D.L - D.u) : ℕ) : ℤ)) :
    Nonempty (DensityEndgameData N A) := by
  apply densityEndgameData_of_orderedCentralBlock D hA hcongr hlocal
  exact D.left_endpoints_ordered_of_orientation_scale
    hA hcongr hlocal hscale

/-- Finite checked bridge from the extracted central block and its scale
estimates to the exact upper-bound endgame. -/
theorem OrderedCentralBlock.hasDensityEndgame_of_orientation_scale
    {N : ℕ} {A : Finset ℤ} (D : OrderedCentralBlock N A)
    (hA : IsBoundedAdmissible N A)
    (hcongr : ∀ i < A.card,
      Int.ModEq (D.q : ℤ) (D.a i) (D.a D.u))
    (hlocal : 4 * D.R + 3 + D.q ≤ D.L - D.u)
    (hscale : (N : ℤ) - 1 +
        2 * ((2 * (D.R : ℤ) - 1) * (D.q : ℤ)) <
      2 * (D.q : ℤ) * (D.L - D.u : ℕ) *
        ((A.card - 2 * D.u - (D.L - D.u) : ℕ) : ℤ)) :
    HasDensityEndgame N A := by
  exact (densityEndgameData_of_orderedCentralBlock_orientation_scale
    D hA hcongr hlocal hscale).some.hasDensityEndgame

/-! ## Eventual adapter -/

theorem ExtractedCentralBlock.hasDensityEndgame
    {N : ℕ} {A : Finset ℤ} (E : ExtractedCentralBlock N A)
    (hA : IsBoundedAdmissible N A) : HasDensityEndgame N A :=
  E.toOrderedCentralBlock.hasDensityEndgame_of_orientation_scale hA
    E.congruent E.local_room E.orientation_scale

/-- Any eventual extractor of the explicit structural payload immediately
gives the sharp density endgame for all maximizing admissible sets. -/
theorem eventually_maximizers_density_endgame_of_extracted
    (hdata : ∀ᶠ N : ℕ in Filter.atTop, ∀ A : Finset ℤ,
      IsBoundedAdmissible N A → A.card = k N →
        Nonempty (ExtractedCentralBlock N A)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ A : Finset ℤ,
      IsBoundedAdmissible N A → A.card = k N →
        HasDensityEndgame N A := by
  filter_upwards [hdata] with N hN
  intro A hA hcard
  exact (hN A hA hcard).some.hasDensityEndgame hA

/-- The checked structure extractor, endpoint-orientation repair, and density
endgame combine into the sharp eventual maximizer statement. -/
theorem eventually_maximizers_density_endgame
    (hstructure : HasEventuallyLargeSetStructure) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ A : Finset ℤ,
      IsBoundedAdmissible N A → A.card = k N →
        HasDensityEndgame N A :=
  eventually_maximizers_density_endgame_of_extracted
    (eventually_extractedCentralBlock hstructure)


end

end Erdos874
