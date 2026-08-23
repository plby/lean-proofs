/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos721.LocalRieszSmoothing

/-!
# The local Chang--Sanders spectrum controller

This file extracts a maximal subset dissociated relative to an auxiliary
large spectrum.  Maximality says that every target frequency is a signed
sum of the extracted frequencies and one auxiliary frequency.  The local
Riesz-product estimate then bounds the number of extracted frequencies by
the logarithm of a *relative* density, with no dependence on the rank of the
ambient Bohr carrier.
-/

namespace Erdos721

open AddChar Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal Indicator mu NNReal Pointwise

namespace CyclicLocalChangSanders

variable {N : ℕ} [NeZero N]

open CyclicFourier CyclicLocalChang CyclicLocalRieszSmoothing

lemma neg_mem_addSpan {Delta : Finset (ZMod N)} {s : ZMod N}
    (hs : s ∈ Delta.addSpan) : -s ∈ Delta.addSpan := by
  rw [Finset.mem_addSpan] at hs ⊢
  obtain ⟨epsilon, hepsilon, heq⟩ := hs
  refine ⟨fun a ↦ -epsilon a, ?_, ?_⟩
  · intro a
    rcases hepsilon a with h | h | h
    · right; right; simp [h]
    · right; left; simp [h]
    · left; simp [h]
  · simp_rw [neg_zsmul]
    rw [Finset.sum_neg_distrib, heq]

lemma zero_mem_addSpan (Delta : Finset (ZMod N)) :
    (0 : ZMod N) ∈ Delta.addSpan := by
  rw [Finset.mem_addSpan]
  exact ⟨fun _ ↦ 0, by simp, by simp⟩

/-- If adjoining `r` destroys global dissociativity, then `r` was already
in the signed span. -/
lemma mem_addSpan_of_not_addDissociated_insert
    (Delta : Finset (ZMod N)) {r : ZMod N} (hr : r ∉ Delta)
    (hDelta : AddDissociated (Delta : Set (ZMod N)))
    (hfail : ¬ AddDissociated ((insert r Delta : Finset (ZMod N)) :
      Set (ZMod N))) :
    r ∈ Delta.addSpan := by
  obtain ⟨t, u, ht, hu, htu, hne, hsum⟩ :=
    not_addDissociated_iff_exists_disjoint.mp hfail
  by_cases hrt : r ∈ t
  · have hru : r ∉ u := fun hru ↦ Finset.disjoint_left.mp htu hrt hru
    have htDelta : t.erase r ⊆ Delta := by
      intro a ha
      have haInsert := ht (by simpa only [Finset.mem_coe] using
        (Finset.mem_of_mem_erase ha))
      have har : a ≠ r := (Finset.mem_erase.mp ha).1
      simpa [har] using haInsert
    have huDelta : u ⊆ Delta := by
      intro a ha
      have haInsert := hu (by simpa only [Finset.mem_coe] using ha)
      have har : a ≠ r := by
        intro har
        subst a
        exact hru ha
      simpa [har] using haInsert
    have hrearrange :
        r = (∑ a ∈ u, a) - ∑ a ∈ t.erase r, a := by
      have herase := Finset.sum_erase_eq_sub (f := fun a : ZMod N ↦ a) hrt
      rw [herase]
      rw [hsum]
      abel
    rw [hrearrange]
    exact Finset.sum_sub_sum_mem_addSpan huDelta htDelta
  · have htDelta : t ⊆ Delta := by
      intro a ha
      have haInsert := ht (by simpa only [Finset.mem_coe] using ha)
      have har : a ≠ r := by
        intro har
        subst a
        exact hrt ha
      simpa [har] using haInsert
    by_cases hru : r ∈ u
    · have huDelta : u.erase r ⊆ Delta := by
        intro a ha
        have haInsert := hu (by simpa only [Finset.mem_coe] using
          (Finset.mem_of_mem_erase ha))
        have har : a ≠ r := (Finset.mem_erase.mp ha).1
        simpa [har] using haInsert
      have hrearrange :
          r = (∑ a ∈ t, a) - ∑ a ∈ u.erase r, a := by
        have herase := Finset.sum_erase_eq_sub (f := fun a : ZMod N ↦ a) hru
        rw [herase]
        rw [← hsum]
        abel
      rw [hrearrange]
      exact Finset.sum_sub_sum_mem_addSpan htDelta huDelta
    · have huDelta : u ⊆ Delta := by
        intro a ha
        have haInsert := hu (by simpa only [Finset.mem_coe] using ha)
        have har : a ≠ r := by
          intro har
          subst a
          exact hru ha
        simpa [har] using haInsert
      have hfailDelta : ¬ AddDissociated (Delta : Set (ZMod N)) :=
        not_addDissociated_iff_exists_disjoint.mpr
          ⟨t, u, by simpa only [Finset.coe_subset] using htDelta,
            by simpa only [Finset.coe_subset] using huDelta,
            htu, hne, hsum⟩
      exact False.elim (hfailDelta hDelta)

/-- Failure of relative dissociativity after adjoining `r` expresses `r`
as a signed sum of the old frequencies plus one frequency from `Q` or
`-Q`. -/
lemma mem_addSpan_add_union_neg_of_not_spectrallyDissociated_insert
    (Q Delta : Finset (ZMod N)) {r : ZMod N} (hr : r ∉ Delta)
    (hQzero : (0 : ZMod N) ∈ Q)
    (hDelta : SpectrallyDissociated Q Delta)
    (hfail : ¬ SpectrallyDissociated Q (insert r Delta)) :
    r ∈ Delta.addSpan + (Q ∪ -Q) := by
  by_cases hglobal :
      AddDissociated (((insert r Delta : Finset (ZMod N))) : Set (ZMod N))
  · have hspectral : ¬ (∀ q ∈ (insert r Delta).addSpan,
        q ∈ Q → q = 0) := by
      intro hspectral
      exact hfail ⟨hglobal, hspectral⟩
    push Not at hspectral
    obtain ⟨q, hqSpan, hqQ, hq0⟩ := hspectral
    rw [Finset.mem_addSpan] at hqSpan
    obtain ⟨epsilon, hepsilon, heq⟩ := hqSpan
    let s : ZMod N := ∑ a ∈ Delta, epsilon a • a
    have hsSpan : s ∈ Delta.addSpan := by
      rw [Finset.mem_addSpan]
      exact ⟨epsilon, hepsilon, rfl⟩
    have hsum : epsilon r • r + s = q := by
      rw [← heq]
      simp only [s, Finset.sum_insert hr]
    rcases hepsilon r with hneg | hzero | hone
    · have hrEq : r = s + -q := by
        rw [hneg] at hsum
        simp only [neg_one_zsmul] at hsum
        have hnegR : -r = q - s := (eq_sub_iff_add_eq).2 hsum
        have hrSub : r = s - q := by
          calc
            r = -(-r) := by simp
            _ = -(q - s) := by rw [hnegR]
            _ = s - q := by abel
        simpa only [sub_eq_add_neg] using hrSub
      rw [hrEq]
      apply Finset.add_mem_add hsSpan
      simp [hqQ]
    · have hqEq : q = s := by
        rw [hzero] at hsum
        simp only [zero_zsmul, zero_add] at hsum
        exact hsum.symm
      exact False.elim (hq0 (hDelta.2 q (hqEq ▸ hsSpan) hqQ))
    · have hrEq : r = -s + q := by
        rw [hone] at hsum
        simp only [one_zsmul] at hsum
        have hrSub : r = q - s := (eq_sub_iff_add_eq).2 hsum
        calc
          r = q - s := hrSub
          _ = -s + q := by abel
      rw [hrEq]
      apply Finset.add_mem_add (neg_mem_addSpan hsSpan)
      simp [hqQ]
  · have hrSpan := mem_addSpan_of_not_addDissociated_insert
      Delta hr hDelta.1 hglobal
    simpa only [add_zero] using
      Finset.add_mem_add hrSpan (Finset.mem_union_left (-Q) hQzero)

/-- A maximal relatively dissociated subset spans the target set modulo one
auxiliary frequency. -/
theorem exists_maximal_spectrallyDissociated
    (Gamma Q : Finset (ZMod N)) (hQzero : (0 : ZMod N) ∈ Q) :
    ∃ Delta : Finset (ZMod N),
      Delta ⊆ Gamma ∧
      SpectrallyDissociated Q Delta ∧
      Gamma ⊆ Delta.addSpan + (Q ∪ -Q) := by
  classical
  let candidates : Finset (Finset (ZMod N)) :=
    Gamma.powerset.filter fun Delta ↦ SpectrallyDissociated Q Delta
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, spectrallyDissociated_empty]
  obtain ⟨Delta, hDeltaMax⟩ := candidates.exists_maximal hcandidates
  have hDeltaMem : Delta ∈ candidates := hDeltaMax.1
  have hDeltaData : Delta ⊆ Gamma ∧ SpectrallyDissociated Q Delta := by
    simpa only [candidates, Finset.mem_filter, Finset.mem_powerset] using hDeltaMem
  refine ⟨Delta, hDeltaData.1, hDeltaData.2, ?_⟩
  intro r hrGamma
  by_cases hrDelta : r ∈ Delta
  · simpa only [add_zero] using
      Finset.add_mem_add (Finset.subset_addSpan hrDelta)
        (Finset.mem_union_left (-Q) hQzero)
  · have hfail : ¬ SpectrallyDissociated Q (insert r Delta) := by
      intro hinsert
      have hinsertMem : insert r Delta ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.insert_subset hrGamma hDeltaData.1, hinsert⟩
      exact hDeltaMax.not_gt hinsertMem (Finset.ssubset_insert hrDelta)
    exact mem_addSpan_add_union_neg_of_not_spectrallyDissociated_insert
      Q Delta hrDelta hQzero hDeltaData.2 hfail

lemma SpectrallyDissociated.subset
    {Q Delta E : Finset (ZMod N)} (hE : E ⊆ Delta)
    (hDelta : SpectrallyDissociated Q Delta) :
    SpectrallyDissociated Q E := by
  constructor
  · exact AddDissociated.subset (by
      simpa only [Finset.coe_subset] using hE) hDelta.1
  · intro r hrSpan hrQ
    exact hDelta.2 r (addSpan_mono hE hrSpan) hrQ

lemma zero_mem_relativeLargeSpectrum
    {V : Finset (ZMod N)} (hV : V.Nonempty) {eta : ℝ} (heta : eta ≤ 1) :
    (0 : ZMod N) ∈ CyclicChang.relativeLargeSpectrum V eta := by
  rw [← CyclicSpectralSmoothing.largeSpectrum_probabilityWeight_eq_relativeLargeSpectrum
    hV, CyclicFourier.mem_largeSpectrum, CyclicFourier.fourier_zero,
    CyclicSpectralSmoothing.average_probabilityWeight hV]
  simpa using heta

/-- Quantitative local Chang--Sanders generator.  The integer `m` is an
a-priori entropy cutoff.  The smoothing parameters only have to handle an
`m`-element subset; if a larger relatively dissociated set existed, such a
subset would contradict the local Chang entropy estimate. -/
theorem exists_localChangSanders_generator
    (B : CyclicBohr.Set N)
    (X S V Gamma : Finset (ZMod N))
    (hX : X.Nonempty) (hXS : X ⊆ S) (hVnonempty : V.Nonempty)
    (m : ℕ) {eta rho delta epsilon : ℝ}
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) (hrho : 0 ≤ rho)
    (hscale : (m : ℝ) * rho ≤ delta)
    (hV : V ⊆ (B.dilate rho).carrier)
    (hstable : ∀ z ∈ B.dilate delta,
      (Finset.expect Finset.univ fun x : ZMod N ↦
        |CyclicBohr.uniformWeight S (x - z) -
          CyclicBohr.uniformWeight S x|) ≤ epsilon)
    (hGamma : Gamma ⊆ CyclicChang.relativeLargeSpectrum X eta)
    (hcutoff :
      2 * (Real.log ((S.card : ℝ) / X.card) + Real.log 4) / eta ^ 2 < m)
    (hepsilon : 2 ^ m * epsilon ≤ 1) :
    ∃ Delta : Finset (ZMod N),
      Delta ⊆ Gamma ∧
      Delta.card < m ∧
      Gamma ⊆ Delta.addSpan +
        (CyclicChang.relativeLargeSpectrum V (1 / 3) ∪
          -CyclicChang.relativeLargeSpectrum V (1 / 3)) := by
  let Q := CyclicChang.relativeLargeSpectrum V (1 / 3)
  have hQzero : (0 : ZMod N) ∈ Q := by
    apply zero_mem_relativeLargeSpectrum hVnonempty
    norm_num
  obtain ⟨Delta, hDeltaGamma, hDeltaDiss, hspan⟩ :=
    exists_maximal_spectrallyDissociated Gamma Q hQzero
  refine ⟨Delta, hDeltaGamma, ?_, hspan⟩
  by_contra hcard
  have hmcard : m ≤ Delta.card := by omega
  obtain ⟨E, hEDelta, hEcard⟩ := Finset.exists_subset_card_eq hmcard
  have hEDiss : SpectrallyDissociated Q E :=
    SpectrallyDissociated.subset hEDelta hDeltaDiss
  have hEspec : E ⊆ CyclicChang.relativeLargeSpectrum X eta :=
    hEDelta.trans (hDeltaGamma.trans hGamma)
  have hElocal : LocallyDissociated S E (Real.log 4) := by
    apply locallyDissociated_of_narrow_dilate B S V E
      (hX.mono hXS) hVnonempty hrho (by norm_num : (0 : ℝ) ≤ 1 / 3)
    · simpa only [hEcard] using hscale
    · exact hV
    · exact hstable
    · exact hEDiss
    · simpa only [hEcard] using one_third_pow_mul_two_pow_le_one m
    · simpa only [hEcard] using hepsilon
  have hbound := locallyDissociated_card_bound X S hX hXS
    heta0 heta1 E hEspec hElocal
  rw [hEcard] at hbound
  exact (not_lt_of_ge hbound) hcutoff

/-! ## The auxiliary spectrum is approximately annihilated -/

lemma fourier_sub (f g : ZMod N → ℂ) (r : ZMod N) :
    CyclicFourier.fourier (fun x ↦ f x - g x) r =
      CyclicFourier.fourier f r - CyclicFourier.fourier g r := by
  unfold CyclicFourier.fourier CyclicFourier.average
  simp only [mul_sub, Finset.sum_sub_distrib]

lemma fourier_translated_uniformWeight
    (V : Finset (ZMod N)) (z r : ZMod N) :
    CyclicFourier.fourier
        (fun x ↦ (CyclicBohr.uniformWeight V (x - z) : ℂ)) r =
      (starRingEnd ℂ) (CyclicBohr.character r z) *
        CyclicFourier.fourier
          (CyclicSpectralSmoothing.probabilityWeight V) r := by
  let f : ZMod N → ℂ := fun x ↦
    (starRingEnd ℂ) (CyclicBohr.character r x) *
      (CyclicBohr.uniformWeight V (x - z) : ℂ)
  unfold CyclicFourier.fourier
  change CyclicFourier.average f = _
  rw [← CyclicFourier.average_add_left f z]
  rw [show (fun x ↦ f (z + x)) = fun x ↦
      (starRingEnd ℂ) (CyclicBohr.character r z) *
        ((starRingEnd ℂ) (CyclicBohr.character r x) *
          CyclicSpectralSmoothing.probabilityWeight V x) by
    funext x
    unfold f
    rw [show z + x - z = x by abel,
      CyclicBohr.character_add, map_mul,
      CyclicLocalRieszSmoothing.probabilityWeight_eq_ofReal_uniformWeight]
    ring]
  rw [CyclicFourier.average_const_mul]

/-- Translating a finite set translates its normalized probability weight.
The formula is stated in the form used by `fourier_translated_uniformWeight`.
-/
lemma probabilityWeight_vadd_finset
    (V : Finset (ZMod N)) (z x : ZMod N) :
    CyclicSpectralSmoothing.probabilityWeight (z +ᵥ V) x =
      (CyclicBohr.uniformWeight V (x - z) : ℂ) := by
  rw [CyclicLocalRieszSmoothing.probabilityWeight_eq_ofReal_uniformWeight]
  congr 1
  unfold CyclicBohr.uniformWeight
  have hmem : x ∈ z +ᵥ V ↔ x - z ∈ V := by
    rw [Finset.mem_vadd_finset]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x - z, hx, by simp [vadd_eq_add]⟩
  rw [Finset.card_vadd_finset, if_congr hmem rfl rfl]

/-- Fourier translation formula for the normalized probability weight of a
translated finite set. -/
lemma fourier_probabilityWeight_vadd_finset
    (V : Finset (ZMod N)) (z r : ZMod N) :
    CyclicFourier.fourier
        (CyclicSpectralSmoothing.probabilityWeight (z +ᵥ V)) r =
      (starRingEnd ℂ) (CyclicBohr.character r z) *
        CyclicFourier.fourier
          (CyclicSpectralSmoothing.probabilityWeight V) r := by
  rw [show CyclicSpectralSmoothing.probabilityWeight (z +ᵥ V) =
      fun x ↦ (CyclicBohr.uniformWeight V (x - z) : ℂ) by
    funext x
    exact probabilityWeight_vadd_finset V z x]
  exact fourier_translated_uniformWeight V z r

/-- Translation preserves the modulus of every normalized Fourier
coefficient. -/
lemma norm_fourier_probabilityWeight_vadd_finset
    (V : Finset (ZMod N)) (z r : ZMod N) :
    ‖CyclicFourier.fourier
        (CyclicSpectralSmoothing.probabilityWeight (z +ᵥ V)) r‖ =
      ‖CyclicFourier.fourier
        (CyclicSpectralSmoothing.probabilityWeight V) r‖ := by
  rw [fourier_probabilityWeight_vadd_finset, norm_mul, RCLike.norm_conj,
    CyclicBohr.norm_character, one_mul]

/-- Translation preserves Chang's relative large spectrum.  This is the
bridge used in the local Sanders argument: Croot--Sisask smooths with the
translate `z +ᵥ V`, while local Chang is applied to the dense base set `V`.
-/
theorem relativeLargeSpectrum_vadd_finset
    (V : Finset (ZMod N)) (hV : V.Nonempty) (z : ZMod N) (eta : ℝ) :
    CyclicChang.relativeLargeSpectrum (z +ᵥ V) eta =
      CyclicChang.relativeLargeSpectrum V eta := by
  have hzV : (z +ᵥ V).Nonempty := by simpa using hV
  rw [← CyclicSpectralSmoothing.largeSpectrum_probabilityWeight_eq_relativeLargeSpectrum
      hzV eta,
    ← CyclicSpectralSmoothing.largeSpectrum_probabilityWeight_eq_relativeLargeSpectrum
      hV eta]
  ext r
  simp only [CyclicFourier.mem_largeSpectrum,
    norm_fourier_probabilityWeight_vadd_finset]

lemma norm_fourier_le_expect_norm (f : ZMod N → ℂ) (r : ZMod N) :
    ‖CyclicFourier.fourier f r‖ ≤
      Finset.expect Finset.univ (fun x : ZMod N ↦ ‖f x‖) := by
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold CyclicFourier.fourier CyclicFourier.average
  rw [Fintype.expect_eq_sum_div_card, ZMod.card]
  calc
    ‖(N : ℂ)⁻¹ * ∑ x : ZMod N,
        (starRingEnd ℂ) (CyclicBohr.character r x) * f x‖ ≤
        ‖(N : ℂ)⁻¹‖ * ∑ x : ZMod N,
          ‖(starRingEnd ℂ) (CyclicBohr.character r x) * f x‖ := by
      rw [norm_mul]
      gcongr
      exact norm_sum_le _ _
    _ = (N : ℝ)⁻¹ * ∑ x : ZMod N, ‖f x‖ := by
      simp only [norm_inv, Complex.norm_natCast, abs_of_pos hN, norm_mul,
        RCLike.norm_conj, CyclicBohr.norm_character, one_mul]
    _ = (∑ x : ZMod N, ‖f x‖) / N := by
      rw [div_eq_mul_inv]
      ring

/-- Translation stability of the narrow uniform probability annihilates
its relative large spectrum. -/
theorem norm_one_sub_character_le_of_mem_relativeLargeSpectrum
    (V : Finset (ZMod N)) (hV : V.Nonempty)
    {eta epsilon : ℝ} (heta : 0 < eta) {z r : ZMod N}
    (hr : r ∈ CyclicChang.relativeLargeSpectrum V eta)
    (htranslate :
      Finset.expect Finset.univ (fun x : ZMod N ↦
        |CyclicBohr.uniformWeight V (x - z) -
          CyclicBohr.uniformWeight V x|) ≤ epsilon) :
    ‖1 - CyclicBohr.character r z‖ ≤ epsilon / eta := by
  let translated : ZMod N → ℂ := fun x ↦
    (CyclicBohr.uniformWeight V (x - z) : ℂ)
  let base : ZMod N → ℂ := fun x ↦
    (CyclicBohr.uniformWeight V x : ℂ)
  have hbase : base = CyclicSpectralSmoothing.probabilityWeight V := by
    funext x
    exact (CyclicLocalRieszSmoothing.probabilityWeight_eq_ofReal_uniformWeight
      V x).symm
  have hcoeff : eta ≤
      ‖CyclicFourier.fourier
        (CyclicSpectralSmoothing.probabilityWeight V) r‖ := by
    have hr' : r ∈ CyclicFourier.largeSpectrum
        (CyclicSpectralSmoothing.probabilityWeight V) eta := by
      rwa [CyclicSpectralSmoothing.largeSpectrum_probabilityWeight_eq_relativeLargeSpectrum
        hV]
    exact CyclicFourier.mem_largeSpectrum.mp hr'
  have hfourierDiff :
      CyclicFourier.fourier translated r - CyclicFourier.fourier base r =
        ((starRingEnd ℂ) (CyclicBohr.character r z) - 1) *
          CyclicFourier.fourier
            (CyclicSpectralSmoothing.probabilityWeight V) r := by
    rw [hbase, fourier_translated_uniformWeight]
    ring
  have hdiff :
      ‖CyclicFourier.fourier translated r - CyclicFourier.fourier base r‖ ≤
        epsilon := by
    rw [← fourier_sub]
    calc
      ‖CyclicFourier.fourier (fun x ↦ translated x - base x) r‖ ≤
          Finset.expect Finset.univ
            (fun x : ZMod N ↦ ‖translated x - base x‖) :=
        norm_fourier_le_expect_norm _ _
      _ = Finset.expect Finset.univ (fun x : ZMod N ↦
          |CyclicBohr.uniformWeight V (x - z) -
            CyclicBohr.uniformWeight V x|) := by
        apply Finset.expect_congr rfl
        intro x hx
        simp only [translated, base, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
      _ ≤ epsilon := htranslate
  have hproduct :
      ‖1 - CyclicBohr.character r z‖ *
          ‖CyclicFourier.fourier
            (CyclicSpectralSmoothing.probabilityWeight V) r‖ ≤ epsilon := by
    calc
      ‖1 - CyclicBohr.character r z‖ *
          ‖CyclicFourier.fourier
            (CyclicSpectralSmoothing.probabilityWeight V) r‖ =
          ‖CyclicFourier.fourier translated r -
            CyclicFourier.fourier base r‖ := by
        rw [hfourierDiff, norm_mul]
        congr 1
        symm
        calc
          ‖(starRingEnd ℂ) (CyclicBohr.character r z) - 1‖ =
              ‖CyclicBohr.character r z - 1‖ := by
            calc
              ‖(starRingEnd ℂ) (CyclicBohr.character r z) - 1‖ =
                  ‖(starRingEnd ℂ)
                    (CyclicBohr.character r z - 1)‖ := by simp
              _ = ‖CyclicBohr.character r z - 1‖ :=
                RCLike.norm_conj _
          _ = ‖1 - CyclicBohr.character r z‖ := norm_sub_rev _ _
      _ ≤ epsilon := hdiff
  rw [le_div_iff₀ heta]
  exact hproduct.trans' (mul_le_mul_of_nonneg_left hcoeff (norm_nonneg _))

/-! ## Combining the extracted and auxiliary frequencies -/

/-- Intersecting the Bohr set on the extracted frequencies with a Bohr set
controlling the auxiliary spectrum controls the entire target spectrum. -/
theorem exists_bohr_controlling_of_span_add_aux
    (Gamma Q Delta : Finset (ZMod N)) (W : CyclicBohr.Set N)
    (m : ℕ) {sigma tau : ℝ} (hsigma : 0 ≤ sigma)
    (hDeltaCard : Delta.card < m)
    (hspan : Gamma ⊆ Delta.addSpan + (Q ∪ -Q))
    (hQcontrol : ∀ q ∈ Q ∪ -Q, ∀ x ∈ W,
      ‖1 - CyclicBohr.character q x‖ ≤ tau) :
    ∃ C : CyclicBohr.Set N,
      C.rank ≤ W.rank + m ∧
      W.frequencies ⊆ C.frequencies ∧
      C.radius = min sigma W.radius ∧
      ∀ r ∈ Gamma, ∀ x ∈ C,
        ‖1 - CyclicBohr.character r x‖ ≤ (m : ℝ) * sigma + tau := by
  let L := CyclicBohr.Set.ofFrequencies Delta sigma hsigma
  let C := L.meet W
  refine ⟨C, ?_, ?_, rfl, ?_⟩
  · calc
      C.rank ≤ L.rank + W.rank := CyclicBohr.Set.rank_meet_le L W
      _ = Delta.card + W.rank := by rfl
      _ ≤ W.rank + m := by omega
  · exact Finset.subset_union_right
  · intro r hr x hx
    obtain ⟨s, hs, q, hq, rfl⟩ := Finset.mem_add.mp (hspan hr)
    have hxL : x ∈ L := by
      change x ∈ L.carrier
      exact CyclicBohr.Set.carrier_meet_subset_left L W hx
    have hxW : x ∈ W := by
      change x ∈ W.carrier
      exact CyclicBohr.Set.carrier_meet_subset_right L W hx
    have hsControl :
        ‖1 - CyclicBohr.character s x‖ ≤ (m : ℝ) * sigma := by
      have hs' : s ∈ L.signedSpan := by
        change s ∈ (Delta.addSpan : Set (ZMod N))
        simpa only [Finset.mem_coe] using hs
      have hraw := CyclicBohr.Set.norm_one_sub_character_le_rank_mul hs' hxL
      have hcardReal : (Delta.card : ℝ) ≤ m := by
        exact_mod_cast (Nat.le_of_lt hDeltaCard)
      calc
        ‖1 - CyclicBohr.character s x‖ ≤ L.rank * L.radius := hraw
        _ = (Delta.card : ℝ) * sigma := by rfl
        _ ≤ (m : ℝ) * sigma :=
          mul_le_mul_of_nonneg_right hcardReal hsigma
    rw [CyclicBohr.character_add_index]
    exact (CyclicBohr.norm_one_sub_mul_of_norm_le_one
      (by rw [CyclicBohr.norm_character])).trans
        (add_le_add hsControl (hQcontrol q hq x hxW))

/-- A completely constructed rank-free local spectral controller.  The
base set `T` is only measured relative to the narrow ambient carrier
`(H.dilate zeta).carrier`.  Two successive regular dilates provide the
translation-stable carrier used by the local Riesz-product argument and the
still narrower carrier which annihilates its auxiliary spectrum.

The integer `m` is the entropy cutoff, `ell` controls the final auxiliary
error, and `sigma` is the radius assigned to the extracted frequencies.
-/
noncomputable def rankFreeControllerRadius
    (H : CyclicBohr.Set N) (m ell : ℕ) (zeta sigma : ℝ) : ℝ :=
  min sigma
    ((400 * (ell : ℝ) * (H.rank : ℝ))⁻¹ *
      (((400 * ((2 ^ m : ℕ) : ℝ) * (H.rank : ℝ))⁻¹ / (m : ℝ)) *
        ((2 * zeta) * H.radius)))

theorem exists_rankFree_localSpectrum_controller
    (H : CyclicBohr.Set N) (T : Finset (ZMod N)) (m ell : ℕ)
    {zeta eta sigma : ℝ}
    (hHradius : 0 < H.radius) (hHrank : 0 < H.rank)
    (hm : 0 < m) (hell : 0 < ell) (hzeta : 0 < zeta)
    (hT : T.Nonempty) (hTsub : T ⊆ (H.dilate zeta).carrier)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) (hsigma : 0 < sigma)
    (hcutoff :
      2 * (Real.log
          (((H.dilate (2 * zeta)).carrier.card : ℝ) / T.card) +
        Real.log 4) / eta ^ 2 < m) :
    ∃ C : CyclicBohr.Set N,
      C.rank ≤ H.rank + m ∧
      H.frequencies ⊆ C.frequencies ∧
      C.radius = rankFreeControllerRadius H m ell zeta sigma ∧
      0 < C.radius ∧
      ∀ r ∈ CyclicChang.relativeLargeSpectrum T eta, ∀ x ∈ C,
        ‖1 - CyclicBohr.character r x‖ ≤
          (m : ℝ) * sigma + 3 / (5 * ell) := by
  let B : CyclicBohr.Set N := H.dilate (2 * zeta)
  have hBradius : 0 < B.radius := by
    dsimp only [B]
    simp only [CyclicBohr.Set.radius_dilate,
      abs_of_pos (by positivity : 0 < (2 * zeta : ℝ))]
    positivity
  have hBrank : 0 < B.rank := by
    simpa only [B, CyclicBohr.Set.rank_dilate] using hHrank
  have hpow : 0 < (2 ^ m : ℕ) := pow_pos (by norm_num) _
  obtain ⟨t, delta, htlow, hthigh, hdeltaFormula, hdelta, hdeltat,
      hstable⟩ :=
    CyclicBohr.exists_uniformWeight_translation_stable_dilate_fine
      B (2 ^ m) hBradius hBrank hpow
  let S : Finset (ZMod N) := (B.dilate t).carrier
  have hTsubS : T ⊆ S := by
    intro x hx
    have hx' := hTsub hx
    rw [CyclicBohr.Set.mem_carrier] at hx' ⊢
    intro r hr
    have hr' : r ∈ H.frequencies := by
      simpa only [S, B, CyclicBohr.Set.frequencies_dilate] using hr
    calc
      ‖1 - CyclicBohr.character r x‖ ≤
          (H.dilate zeta).radius := hx' r (by simpa using hr')
      _ ≤ (B.dilate t).radius := by
        simp only [B, CyclicBohr.Set.radius_dilate,
          abs_of_pos hzeta, abs_of_nonneg (by linarith : 0 ≤ t),
          abs_of_pos (by positivity : 0 < 2 * zeta)]
        have ha : 0 ≤ zeta * H.radius :=
          mul_nonneg hzeta.le H.radius_nonneg
        have ht : 0 ≤ 2 * t - 1 := by linarith
        nlinarith [mul_nonneg ht ha]
  have hS : S.Nonempty := (B.dilate t).carrier_nonempty
  let rho : ℝ := delta / m
  have hrho : 0 < rho := div_pos hdelta (by positivity)
  have hscale : (m : ℝ) * rho ≤ delta := by
    dsimp only [rho]
    have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    calc
      (m : ℝ) * (delta / (m : ℝ)) = delta := by field_simp
      _ ≤ delta := le_rfl
  let Bnarrow : CyclicBohr.Set N := B.dilate rho
  have hBnarrowRadius : 0 < Bnarrow.radius := by
    dsimp only [Bnarrow]
    simp only [CyclicBohr.Set.radius_dilate, abs_of_pos hrho]
    positivity
  have hBnarrowRank : 0 < Bnarrow.rank := by
    simpa only [Bnarrow, CyclicBohr.Set.rank_dilate] using hBrank
  obtain ⟨v, xi, hvlow, hvhigh, hxiFormula, hxi, hxiv, hstableV⟩ :=
    CyclicBohr.exists_uniformWeight_translation_stable_dilate_fine
      Bnarrow ell hBnarrowRadius hBnarrowRank hell
  let V : Finset (ZMod N) := (Bnarrow.dilate v).carrier
  have hV : V.Nonempty := (Bnarrow.dilate v).carrier_nonempty
  have hVsub : V ⊆ (B.dilate rho).carrier := by
    have hmono := CyclicBohr.Set.dilate_mono Bnarrow
      (by linarith : 0 ≤ v) hvhigh
    simpa only [V, Bnarrow, CyclicBohr.carrier_dilate_one] using hmono
  let Gamma := CyclicChang.relativeLargeSpectrum T eta
  have hSsubB : S ⊆ B.carrier := by
    have hmono := CyclicBohr.Set.dilate_mono B
      (by linarith : 0 ≤ t) hthigh
    simpa only [S, CyclicBohr.carrier_dilate_one] using hmono
  have hcutoffS :
      2 * (Real.log ((S.card : ℝ) / T.card) + Real.log 4) /
          eta ^ 2 < (m : ℝ) := by
    have hTcard : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
    have hScard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have hBcard : (0 : ℝ) < B.carrier.card := by
      exact_mod_cast B.carrier_nonempty.card_pos
    have hratio : (S.card : ℝ) / T.card ≤
        (B.carrier.card : ℝ) / T.card := by
      gcongr
    have hlog : Real.log ((S.card : ℝ) / T.card) ≤
        Real.log ((B.carrier.card : ℝ) / T.card) :=
      Real.log_le_log (div_pos hScard hTcard) hratio
    calc
      2 * (Real.log ((S.card : ℝ) / T.card) + Real.log 4) /
          eta ^ 2 ≤
        2 * (Real.log ((B.carrier.card : ℝ) / T.card) + Real.log 4) /
          eta ^ 2 := by gcongr
      _ < (m : ℝ) := by simpa only [B] using hcutoff
  obtain ⟨Delta, hDeltaGamma, hDeltaCard, hspan⟩ :=
    exists_localChangSanders_generator B T S V Gamma hT hTsubS hV m
      heta0 heta1 hrho.le hscale hVsub
      (by simpa only [S] using hstable) (by rfl) hcutoffS (by
        norm_num [Nat.cast_pow])
  let Q := CyclicChang.relativeLargeSpectrum V (1 / 3)
  let W : CyclicBohr.Set N := Bnarrow.dilate xi
  have hQcontrol : ∀ q ∈ Q ∪ -Q, ∀ x ∈ W,
      ‖1 - CyclicBohr.character q x‖ ≤ 3 / (5 * ell) := by
    intro q hq x hx
    have hbase (r : ZMod N) (hr : r ∈ Q) :
        ‖1 - CyclicBohr.character r x‖ ≤ 3 / (5 * ell) := by
      have hraw := norm_one_sub_character_le_of_mem_relativeLargeSpectrum
        V hV (by norm_num : (0 : ℝ) < 1 / 3) hr
        (hstableV x (by simpa only [W] using hx))
      convert hraw using 1 <;> field_simp
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hbase q hq
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_neg.mp hq
      rw [CyclicBohr.Set.character_neg_index]
      calc
        ‖1 - (starRingEnd ℂ) (CyclicBohr.character r x)‖ =
            ‖1 - CyclicBohr.character r x‖ := by
          simpa using RCLike.norm_conj
            (1 - CyclicBohr.character r x)
        _ ≤ 3 / (5 * ell) := hbase r hr
  obtain ⟨C, hCrank, hWfreqC, hCradius, hCcontrol⟩ :=
    exists_bohr_controlling_of_span_add_aux Gamma Q Delta W m
      hsigma.le hDeltaCard (by simpa only [Q] using hspan) hQcontrol
  refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [W, Bnarrow, B, CyclicBohr.Set.rank_dilate] using hCrank
  · simpa only [W, Bnarrow, B, CyclicBohr.Set.frequencies_dilate] using hWfreqC
  · rw [hCradius]
    congr 1
    simp only [W, Bnarrow, B, CyclicBohr.Set.radius_dilate,
      abs_of_pos hxi, abs_of_pos hrho,
      abs_of_pos (by positivity : 0 < (2 * zeta : ℝ))]
    rw [hxiFormula]
    simp only [Bnarrow, B, CyclicBohr.Set.rank_dilate]
    dsimp only [rho]
    rw [hdeltaFormula]
    simp only [B, CyclicBohr.Set.rank_dilate]
  · rw [hCradius]
    exact lt_min hsigma (by
      dsimp only [W]
      simp only [CyclicBohr.Set.radius_dilate, abs_of_pos hxi]
      positivity)
  · simpa only [Gamma] using hCcontrol

/-! ## A controller over a prescribed stable carrier -/

/-- Radius of the local spectral controller when the translation-stable
carrier has already been selected.  In contrast with
`rankFreeControllerRadius`, this definition contains no preliminary
regularization loss: `delta` is the stability scale of the supplied carrier
itself. -/
noncomputable def stableCarrierControllerRadius
    (B : CyclicBohr.Set N) (m ell : ℕ) (delta sigma : ℝ) : ℝ :=
  min sigma
    ((400 * (ell : ℝ) * (B.rank : ℝ))⁻¹ *
      ((delta / (m : ℝ)) * B.radius))

/-- Local Chang--Sanders with a prescribed translation-stable carrier.

This is the source-accurate interface used after Croot--Sisask in the
Bloom--Sisask iteration.  Its entropy hypothesis compares `T` directly with
the supplied carrier `S`; consequently the rank increment does not contain
the rank of `B`.  The only later regularization is the auxiliary-spectrum
annihilator, whose scale is recorded explicitly in the returned radius. -/
theorem exists_localSpectrum_controller_of_stableCarrier
    (B : CyclicBohr.Set N) (T S : Finset (ZMod N)) (m ell : ℕ)
    {eta sigma delta : ℝ}
    (hBradius : 0 < B.radius) (hBrank : 0 < B.rank)
    (hm : 0 < m) (hell : 0 < ell) (hdelta : 0 < delta)
    (hT : T.Nonempty) (hTsubS : T ⊆ S)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1) (hsigma : 0 < sigma)
    (hstable : ∀ z ∈ B.dilate delta,
      (Finset.expect Finset.univ fun x : ZMod N ↦
        |CyclicBohr.uniformWeight S (x - z) -
          CyclicBohr.uniformWeight S x|) ≤
        1 / (5 * ((2 ^ m : ℕ) : ℝ)))
    (hcutoff :
      2 * (Real.log ((S.card : ℝ) / T.card) + Real.log 4) /
        eta ^ 2 < m) :
    ∃ C : CyclicBohr.Set N,
      C.rank ≤ B.rank + m ∧
      B.frequencies ⊆ C.frequencies ∧
      C.radius = stableCarrierControllerRadius B m ell delta sigma ∧
      0 < C.radius ∧
      ∀ r ∈ CyclicChang.relativeLargeSpectrum T eta, ∀ x ∈ C,
        ‖1 - CyclicBohr.character r x‖ ≤
          (m : ℝ) * sigma + 3 / (5 * ell) := by
  let rho : ℝ := delta / m
  have hrho : 0 < rho := div_pos hdelta (by positivity)
  have hscale : (m : ℝ) * rho ≤ delta := by
    dsimp only [rho]
    have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    calc
      (m : ℝ) * (delta / (m : ℝ)) = delta := by field_simp
      _ ≤ delta := le_rfl
  let Bnarrow : CyclicBohr.Set N := B.dilate rho
  have hBnarrowRadius : 0 < Bnarrow.radius := by
    dsimp only [Bnarrow]
    simp only [CyclicBohr.Set.radius_dilate, abs_of_pos hrho]
    positivity
  have hBnarrowRank : 0 < Bnarrow.rank := by
    simpa only [Bnarrow, CyclicBohr.Set.rank_dilate] using hBrank
  obtain ⟨v, xi, hvlow, hvhigh, hxiFormula, hxi, hxiv, hstableV⟩ :=
    CyclicBohr.exists_uniformWeight_translation_stable_dilate_fine
      Bnarrow ell hBnarrowRadius hBnarrowRank hell
  let V : Finset (ZMod N) := (Bnarrow.dilate v).carrier
  have hV : V.Nonempty := (Bnarrow.dilate v).carrier_nonempty
  have hVsub : V ⊆ (B.dilate rho).carrier := by
    have hmono := CyclicBohr.Set.dilate_mono Bnarrow
      (by linarith : 0 ≤ v) hvhigh
    simpa only [V, Bnarrow, CyclicBohr.carrier_dilate_one] using hmono
  let Gamma := CyclicChang.relativeLargeSpectrum T eta
  obtain ⟨Delta, hDeltaGamma, hDeltaCard, hspan⟩ :=
    exists_localChangSanders_generator B T S V Gamma hT hTsubS hV m
      heta0 heta1 hrho.le hscale hVsub hstable (by rfl) hcutoff (by
        norm_num [Nat.cast_pow])
  let Q := CyclicChang.relativeLargeSpectrum V (1 / 3)
  let W : CyclicBohr.Set N := Bnarrow.dilate xi
  have hQcontrol : ∀ q ∈ Q ∪ -Q, ∀ x ∈ W,
      ‖1 - CyclicBohr.character q x‖ ≤ 3 / (5 * ell) := by
    intro q hq x hx
    have hbase (r : ZMod N) (hr : r ∈ Q) :
        ‖1 - CyclicBohr.character r x‖ ≤ 3 / (5 * ell) := by
      have hraw := norm_one_sub_character_le_of_mem_relativeLargeSpectrum
        V hV (by norm_num : (0 : ℝ) < 1 / 3) hr
        (hstableV x (by simpa only [W] using hx))
      convert hraw using 1 <;> field_simp
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hbase q hq
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_neg.mp hq
      rw [CyclicBohr.Set.character_neg_index]
      calc
        ‖1 - (starRingEnd ℂ) (CyclicBohr.character r x)‖ =
            ‖1 - CyclicBohr.character r x‖ := by
          simpa using RCLike.norm_conj
            (1 - CyclicBohr.character r x)
        _ ≤ 3 / (5 * ell) := hbase r hr
  obtain ⟨C, hCrank, hWfreqC, hCradius, hCcontrol⟩ :=
    exists_bohr_controlling_of_span_add_aux Gamma Q Delta W m
      hsigma.le hDeltaCard (by simpa only [Q] using hspan) hQcontrol
  refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [W, Bnarrow, CyclicBohr.Set.rank_dilate] using hCrank
  · simpa only [W, Bnarrow, CyclicBohr.Set.frequencies_dilate] using hWfreqC
  · rw [hCradius]
    congr 1
    simp only [W, Bnarrow, CyclicBohr.Set.radius_dilate,
      abs_of_pos hxi, abs_of_pos hrho]
    rw [hxiFormula]
    simp only [Bnarrow, CyclicBohr.Set.rank_dilate]
    rfl
  · rw [hCradius]
    exact lt_min hsigma (by
      dsimp only [W]
      simp only [CyclicBohr.Set.radius_dilate, abs_of_pos hxi]
      positivity)
  · simpa only [Gamma] using hCcontrol

end CyclicLocalChangSanders
end Erdos721
