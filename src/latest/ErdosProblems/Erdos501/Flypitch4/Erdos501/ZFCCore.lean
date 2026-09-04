/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

(F1) The positive-measure selection lemma (Lemmas 2.1, 2.2) and (F2) the certificate interface
(Definition 3.1) of the paper.
-/
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Group.Measure
import ErdosProblems.Erdos501.Flypitch4.Erdos501.StdSemantics

set_option relaxedAutoImplicit true

/-!
# The ZFC core: (F1) positive-measure selection, and (F2) the certificate interface

Units (F1)–(F2) of the paper's plan are theorems of ordinary (Mathlib) measure theory, with no
forcing:

* **(F1) Lemma 2.1 (positive-measure selection)**, `measure_Q_pos`.  Let `μ` be a σ-finite measure
  on `S`, `E ⊆ S × S` measurable with all horizontal sections `E^s = {t | (t, s) ∈ E}` of measure
  `≤ K < ∞`, and `C ⊆ S` measurable with `μ C = ∞`.  Then
  `Q(C) = {t ∈ C | μ(C \ E_t) = ∞}` (with `E_t = {s | (t, s) ∈ E}` the vertical section) has
  positive measure.  Proof by double counting: if `Q(C)` were null, a piece `D ⊆ C \ Q(C)` with
  `K < μ D < ∞` and a bound `k` on `μ(C \ E_t)` for `t ∈ D_k ⊆ D` (`μ D_k = d > K`) give, for every
  finite piece `C' ⊆ C` of measure `M`, `M · d ≤ (μ ⊗ μ)(E ∩ (D_k × C')) + k · d ≤ K · M + k · d`,
  which is impossible for `M` large since `d > K`.
* **(F1) Lemma 2.2**, `measure_diff_eq_top_of_mem_Q`: for `t ∈ Q(C)`, removing from `C` the two
  sections through `t` and a null set leaves a set of infinite measure.
* **(F2) Definition 3.1**, the structure `Certificate A`: a *certificate* for a family
  `A : ℝ → Set ℝ` consists of a probability space `(Ω, ν)`, a set `Z ⊆ Ω` meeting every Borel set of
  positive measure (the paper's `ν*(Z) = 1`), and Borel maps `x m : Ω → ℝ`, `U m : Ω → Set ℝ`
  (`m : ℤ`) — the paper's `x_m` and open envelopes `U(c_m(·))` — with (P2) `x m` pushes `ν` to
  Lebesgue measure on `[m, m+1)`, (P3) `λ(U m z) < 1`, (P4) `A (x m z) ⊆ U m z` for `z ∈ Z`.
  Instead of Borel *codes* `c_m` for the envelopes we require the joint measurability of
  `{(z, y) | y ∈ U m z}`, which is exactly what the codes are used for.
* **(F2) Theorem 3.2** (`exists_infinite_independent_of_certificate`): a certificate for `A`
  yields an infinite `X ⊆ ℝ` with `x ∉ A y` for all distinct `x, y ∈ X` — the interface that unit
  (F6) targets; proved by the recursion of the paper's Section 3 on the σ-finite space `ℤ × Ω`
  with `μ = counting ⊗ ν`, using Lemmas 2.1, 2.2 and (3.1).
-/

open MeasureTheory Set
open scoped ENNReal

namespace Flypitch.Erdos501.ZFCCore

variable {S : Type*} [MeasurableSpace S] (μ : Measure S)

/-! ### (F1) Lemma 2.1: positive-measure selection -/

/-- The set `Q(C) = {t ∈ C | μ(C \ E_t) = ∞}`, `E_t = {s | (t, s) ∈ E}`. -/
def Q (E : Set (S × S)) (C : Set S) : Set S := {t ∈ C | μ (C \ Prod.mk t ⁻¹' E) = ∞}

lemma measurable_measure_diff_section [SFinite μ] {E : Set (S × S)} (hE : MeasurableSet E)
    {C : Set S} (hC : MeasurableSet C) :
    Measurable fun t => μ (C \ Prod.mk t ⁻¹' E) := by
  have h : (fun t => μ (C \ Prod.mk t ⁻¹' E)) = fun t => μ (Prod.mk t ⁻¹' ((univ ×ˢ C) \ E)) := by
    funext t; congr 1; ext s; simp
  rw [h]
  exact measurable_measure_prodMk_left ((MeasurableSet.univ.prod hC).diff hE)

lemma measurableSet_Q [SFinite μ] {E : Set (S × S)} (hE : MeasurableSet E) {C : Set S}
    (hC : MeasurableSet C) : MeasurableSet (Q μ E C) :=
  hC.inter ((measurable_measure_diff_section μ hE hC) (measurableSet_singleton ∞))

/-- **(F1) Lemma 2.1 (positive-measure selection).**  If `μ` is σ-finite, `E ⊆ S × S` is
measurable with horizontal sections of measure `≤ K < ∞`, and `μ C = ∞`, then
`Q(C) = {t ∈ C | μ(C \ E_t) = ∞}` has positive measure. -/
theorem measure_Q_pos [SigmaFinite μ] {E : Set (S × S)} (hE : MeasurableSet E) {K : ℝ≥0∞}
    (hK : K ≠ ∞) (hsec : ∀ s, μ ((fun t => (t, s)) ⁻¹' E) ≤ K)
    {C : Set S} (hC : MeasurableSet C) (hCinf : μ C = ∞) : 0 < μ (Q μ E C) := by
  classical
  by_contra hQ0
  rw [not_lt, nonpos_iff_eq_zero] at hQ0
  have hfm := measurable_measure_diff_section μ hE hC
  have hQm : MeasurableSet (Q μ E C) := measurableSet_Q μ hE hC
  -- `C \ Q(C)` has infinite measure; take `D ⊆ C \ Q(C)` with `K < μ D < ∞`
  have hCQ : μ (C \ Q μ E C) = ∞ := by rw [measure_diff_null hQ0, hCinf]
  obtain ⟨D, hDm, hDsub, hKD, hDfin⟩ :=
    Measure.exists_subset_measure_lt_top (hC.diff hQm) (by rw [hCQ]; exact hK.lt_top)
  have hfD : ∀ t ∈ D, μ (C \ Prod.mk t ⁻¹' E) ≠ ∞ := fun t ht h => (hDsub ht).2 ⟨(hDsub ht).1, h⟩
  -- `D_k = {t ∈ D | μ(C \ E_t) ≤ k}` increases to `D`; pick `k` with `μ D_k > K`
  let Dk : ℕ → Set S := fun k => {t ∈ D | μ (C \ Prod.mk t ⁻¹' E) ≤ k}
  have hDkm : ∀ k, MeasurableSet (Dk k) := fun k => hDm.inter (hfm measurableSet_Iic)
  have hDk_mono : Monotone Dk := fun k l hkl t ht => ⟨ht.1, ht.2.trans (by exact_mod_cast hkl)⟩
  have hDkU : (⋃ k, Dk k) = D := by
    ext t
    simp only [mem_iUnion, mem_setOf_eq, Dk]
    constructor
    · rintro ⟨k, ht, -⟩; exact ht
    · intro ht
      obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (hfD t ht)
      exact ⟨k, ht, hk.le⟩
  obtain ⟨k, hk⟩ : ∃ k, K < μ (Dk k) := by
    rw [← hDkU, hDk_mono.measure_iUnion] at hKD
    exact lt_iSup_iff.mp hKD
  set d := μ (Dk k) with hd
  have hdfin : d ≠ ∞ := ((measure_mono fun t (ht : t ∈ Dk k) => ht.1).trans_lt hDfin).ne
  set δ := d - K with hδ
  have hδ0 : δ ≠ 0 := (tsub_pos_iff_lt.mpr hk).ne'
  have hδtop : δ ≠ ∞ := (tsub_le_self.trans_lt hdfin.lt_top).ne
  have hdKδ : d = K + δ := (add_tsub_cancel_of_le hk.le).symm
  -- a finite piece `C' ⊆ C` of measure `M > k·d/δ`
  obtain ⟨C', hC'm, hC'sub, hMlt, hMfin⟩ := Measure.exists_subset_measure_lt_top hC
    (show (k * d) / δ < μ C by
      rw [hCinf]
      exact ENNReal.div_lt_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) hdfin) hδ0)
  set M := μ C' with hM
  -- the double counting: `M · d ≤ K · M + k · d`
  have hkey : M * d ≤ K * M + k * d := by
    set W : Set (S × S) := (univ ×ˢ C') ∩ E with hW
    have hWm : MeasurableSet W := (MeasurableSet.univ.prod hC'm).inter hE
    have hlow : ∀ t ∈ Dk k, M ≤ μ (Prod.mk t ⁻¹' W) + k := by
      intro t ht
      have h1 : Prod.mk t ⁻¹' W = C' ∩ Prod.mk t ⁻¹' E := by ext s; simp [W]
      calc M = μ C' := rfl
        _ ≤ μ (C' ∩ Prod.mk t ⁻¹' E) + μ (C' \ Prod.mk t ⁻¹' E) := measure_le_inter_add_diff _ _ _
        _ ≤ μ (Prod.mk t ⁻¹' W) + k := by
          rw [h1]
          exact add_le_add_right ((measure_mono (diff_subset_diff_left hC'sub)).trans ht.2) _
    have hgm : Measurable fun t => μ (Prod.mk t ⁻¹' W) := measurable_measure_prodMk_left hWm
    have hup : ∀ s, (μ.restrict (Dk k)) ((fun t => (t, s)) ⁻¹' W) ≤ C'.indicator (fun _ => K) s := by
      intro s
      by_cases hs : s ∈ C'
      · rw [indicator_of_mem hs]
        calc (μ.restrict (Dk k)) ((fun t => (t, s)) ⁻¹' W) ≤ μ ((fun t => (t, s)) ⁻¹' W) :=
              Measure.restrict_apply_le _ _
          _ ≤ μ ((fun t => (t, s)) ⁻¹' E) := measure_mono fun t ht => ht.2
          _ ≤ K := hsec s
      · rw [indicator_of_notMem hs]
        have h0 : (fun t => (t, s)) ⁻¹' W = ∅ := by ext t; simp [W, hs]
        rw [h0, measure_empty]
    calc M * d = ∫⁻ _ in Dk k, M ∂μ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ t in Dk k, (μ (Prod.mk t ⁻¹' W) + k) ∂μ := setLIntegral_mono (hgm.add_const _) hlow
      _ = ∫⁻ t in Dk k, μ (Prod.mk t ⁻¹' W) ∂μ + k * d := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      _ = ((μ.restrict (Dk k)).prod μ) W + k * d := by rw [Measure.prod_apply hWm]
      _ = (∫⁻ s, (μ.restrict (Dk k)) ((fun t => (t, s)) ⁻¹' W) ∂μ) + k * d := by
          rw [Measure.prod_apply_symm hWm]
      _ ≤ (∫⁻ s, C'.indicator (fun _ => K) s ∂μ) + k * d :=
          add_le_add_left (lintegral_mono hup) _
      _ = K * M + k * d := by rw [lintegral_indicator_const hC'm]
  -- hence `M · δ ≤ k · d`, contradicting `k · d / δ < M`
  have hMδ : M * δ ≤ k * d := by
    have h1 : M * d = K * M + M * δ := by rw [hdKδ, mul_add, mul_comm M K]
    rw [h1] at hkey
    exact (ENNReal.add_le_add_iff_left (ENNReal.mul_ne_top hK hMfin.ne)).mp hkey
  have hlt : k * d < M * δ :=
    calc k * d = (k * d) / δ * δ := (ENNReal.div_mul_cancel hδ0 hδtop).symm
      _ < M * δ := (ENNReal.mul_lt_mul_iff_left hδ0 hδtop).mpr hMlt
  exact absurd hMδ (not_le.mpr hlt)

/-- **(F1) Lemma 2.2.**  For `t ∈ Q(C)`, removing from `C` the vertical section `E_t`, a set `F`
of finite measure (e.g. the horizontal section `E^t`, of measure `≤ K`) and a null set `N` leaves a
set of infinite measure. -/
theorem measure_diff_eq_top_of_mem_Q {E : Set (S × S)} {C : Set S} {t : S} (ht : t ∈ Q μ E C)
    {F : Set S} (hF : μ F ≠ ∞) {N : Set S} (hN : μ N = 0) :
    μ (C \ (Prod.mk t ⁻¹' E ∪ F ∪ N)) = ∞ := by
  have h1 : C \ (Prod.mk t ⁻¹' E ∪ F ∪ N) = ((C \ Prod.mk t ⁻¹' E) \ F) \ N := by
    ext s; simp only [mem_diff, mem_union, not_or]; tauto
  rw [h1, measure_diff_null hN]
  apply top_le_iff.mp
  calc (∞ : ℝ≥0∞) = μ (C \ Prod.mk t ⁻¹' E) - μ F := by
        rw [ht.2]; exact (ENNReal.sub_eq_top_iff.mpr ⟨rfl, hF⟩).symm
    _ ≤ μ ((C \ Prod.mk t ⁻¹' E) \ F) := le_measure_diff

/-! ### (F2) Definition 3.1: the certificate interface -/

/-- **Definition 3.1 (certificate).**  A certificate for the family `A : ℝ → Set ℝ` on the
measurable space `Ω`: a probability measure `ν`, a set `Z ⊆ Ω` meeting every Borel set of
positive measure (`ν*(Z) = 1`), and for `m : ℤ` measurable maps `x m : Ω → ℝ` and envelopes
`U m : Ω → Set ℝ` (jointly measurable) such that

* (P2) `x m` pushes `ν` forward to Lebesgue measure on `[m, m + 1)`,
* (P3) `λ(U m z) < 1` for every `z`,
* (P4) `A (x m z) ⊆ U m z` for every `z ∈ Z` and `m`. -/
structure Certificate (A : ℝ → Set ℝ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- the probability measure on the profile space -/
  ν : Measure Ω
  isProbabilityMeasure : IsProbabilityMeasure ν
  /-- the set of (actual) profiles -/
  Z : Set Ω
  /-- (3.1): `Z` meets every Borel set of positive measure (`ν*(Z) = 1`) -/
  full : ∀ B : Set Ω, MeasurableSet B → 0 < ν B → (Z ∩ B).Nonempty
  /-- the test points `x m z ∈ [m, m + 1)` -/
  x : ℤ → Ω → ℝ
  measurable_x : ∀ m, Measurable (x m)
  /-- (P2): the law of `x m` is Lebesgue measure on `[m, m + 1)` -/
  map_x : ∀ m, ν.map (x m) = volume.restrict (Ico (m : ℝ) (m + 1))
  /-- the envelopes `U m z = U(c_m(z))` -/
  U : ℤ → Ω → Set ℝ
  measurableSet_U : ∀ m, MeasurableSet {p : Ω × ℝ | p.2 ∈ U m p.1}
  /-- (P3): every envelope has Lebesgue measure `< 1` -/
  volume_U_lt_one : ∀ m z, volume (U m z) < 1
  /-- (P4): the envelope of an actual profile covers the corresponding set of the family -/
  subset_U : ∀ m, ∀ z ∈ Z, A (x m z) ⊆ U m z

/-! ### (F2) Theorem 3.2: a certificate yields an infinite independent set -/

/-- Lebesgue measure of a Borel set is the sum of the measures of its pieces on `[m, m + 1)`. -/
lemma tsum_volume_inter_Ico (B : Set ℝ) (hB : MeasurableSet B) :
    ∑' m : ℤ, volume (B ∩ Ico (m : ℝ) (m + 1)) = volume B := by
  rw [← measure_iUnion ((pairwise_disjoint_Ico_intCast ℝ).mono fun i j h =>
      h.mono inter_subset_right inter_subset_right) (fun m => hB.inter measurableSet_Ico),
    ← inter_iUnion, iUnion_Ico_intCast, inter_univ]

/-- **(F2) Theorem 3.2.**  A certificate for `A` yields an infinite set `X ⊆ ℝ` that is independent
for `A` (`x ∉ A y` for all distinct `x, y ∈ X`).  This is the interface that unit (F6) (Theorem 5.1)
targets inside the forcing model.  Proof: on the σ-finite space `S = ℤ × Ω` with `μ = counting ⊗ ν`,
the Borel relation `E = {(t, s) | x(t) ∈ U(s)}` has horizontal sections of measure
`λ(U(s)) < 1` (by (P2), (P3)) and the fibres of `x` are null; the recursion picks
`t_j = (m_j, z_j) ∈ Q(C_j)` with `z_j ∈ Z` (Lemma 2.1 and (3.1)) and removes the two sections
through `t_j` and the fibre of `x(t_j)` (Lemma 2.2); independence follows from (P4). -/
theorem exists_infinite_independent_of_certificate {A : ℝ → Set ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (cert : Certificate A Ω) : ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by
  classical
  have := cert.isProbabilityMeasure
  -- the σ-finite space `S = ℤ × Ω`, `μ = counting ⊗ ν`
  let μ : Measure (ℤ × Ω) := (Measure.count : Measure ℤ).prod cert.ν
  have hμ : ∀ s : Set (ℤ × Ω), MeasurableSet s → μ s = ∑' m : ℤ, cert.ν (Prod.mk m ⁻¹' s) := by
    intro s hs
    show (Measure.count.prod cert.ν) s = _
    rw [Measure.prod_apply hs, lintegral_count]
  -- the test points and envelopes on `S`
  let xx : ℤ × Ω → ℝ := fun t => cert.x t.1 t.2
  have hxx : Measurable xx := measurable_from_prod_countable_right fun m => cert.measurable_x m
  let UU : ℤ × Ω → Set ℝ := fun s => cert.U s.1 s.2
  have hUm : ∀ s, MeasurableSet (UU s) := fun s =>
    (cert.measurableSet_U s.1).preimage (measurable_prodMk_left (x := s.2))
  -- (P2) on `S`: `ν (x m ⁻¹' B) = λ (B ∩ [m, m+1))`, hence `μ (xx ⁻¹' B) = λ B`
  have hP2 : ∀ (B : Set ℝ), MeasurableSet B → μ (xx ⁻¹' B) = volume B := by
    intro B hB
    rw [hμ _ (hxx hB)]
    have h1 : ∀ m : ℤ, cert.ν (Prod.mk m ⁻¹' (xx ⁻¹' B)) = volume (B ∩ Ico (m : ℝ) (m + 1)) := by
      intro m
      have : Prod.mk m ⁻¹' (xx ⁻¹' B) = cert.x m ⁻¹' B := rfl
      rw [this, ← Measure.map_apply (cert.measurable_x m) hB, cert.map_x m,
        Measure.restrict_apply hB]
    simp_rw [h1]
    exact tsum_volume_inter_Ico B hB
  -- the Borel relation `E = {(t, s) | x(t) ∈ U(s)}`
  let E : Set ((ℤ × Ω) × (ℤ × Ω)) := {p | xx p.1 ∈ UU p.2}
  have hE : MeasurableSet E := by
    have h : E = ⋃ (m : ℤ) (m' : ℤ), ({p : (ℤ × Ω) × (ℤ × Ω) | p.1.1 = m} ∩ {p | p.2.1 = m'} ∩
        {p | cert.x m p.1.2 ∈ cert.U m' p.2.2}) := by
      ext ⟨⟨m, z⟩, ⟨m', z'⟩⟩
      simp [E, xx, UU]
    rw [h]
    refine MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun m' => ?_
    refine ((measurable_fst.fst (measurableSet_singleton m)).inter
      (measurable_snd.fst (measurableSet_singleton m'))).inter ?_
    exact (cert.measurableSet_U m').preimage
      (measurable_snd.snd.prodMk ((cert.measurable_x m).comp measurable_fst.snd))
  -- horizontal sections have measure `λ(U(s)) < 1`
  have hsec : ∀ s, μ ((fun t => (t, s)) ⁻¹' E) ≤ 1 := by
    intro s
    have h1 : (fun t => (t, s)) ⁻¹' E = xx ⁻¹' UU s := rfl
    rw [h1, hP2 _ (hUm s)]
    exact (cert.volume_U_lt_one s.1 s.2).le
  -- fibres of `xx` are null
  have hfib : ∀ a : ℝ, μ (xx ⁻¹' {a}) = 0 := fun a => by
    rw [hP2 _ (measurableSet_singleton a)]; exact Real.volume_singleton
  -- the recursion: from a good set `C` (measurable, `μ C = ∞`) pick `t ∈ Q(C)` with `t.2 ∈ Z`
  have hpick : ∀ C : Set (ℤ × Ω), MeasurableSet C → μ C = ∞ →
      ∃ t : ℤ × Ω, t ∈ Q μ E C ∧ t.2 ∈ cert.Z := by
    intro C hC hCinf
    have hQpos := measure_Q_pos μ hE ENNReal.one_ne_top hsec hC hCinf
    have hQm := measurableSet_Q μ hE hC
    rw [hμ _ hQm] at hQpos
    obtain ⟨m, hm⟩ : ∃ m : ℤ, 0 < cert.ν (Prod.mk m ⁻¹' Q μ E C) := by
      by_contra h
      simp only [not_exists, not_lt, nonpos_iff_eq_zero] at h
      rw [ENNReal.tsum_eq_zero.mpr h] at hQpos
      exact lt_irrefl _ hQpos
    obtain ⟨z, hzZ, hzQ⟩ := cert.full _ (hQm.preimage measurable_prodMk_left) hm
    exact ⟨(m, z), hzQ, hzZ⟩
  -- the good sets and the step
  let Good := {C : Set (ℤ × Ω) // MeasurableSet C ∧ μ C = ∞}
  choose pick hpickQ hpickZ using fun C : Good => hpick C.1 C.2.1 C.2.2
  let removed : ℤ × Ω → Set (ℤ × Ω) := fun t =>
    Prod.mk t ⁻¹' E ∪ (fun t' => (t', t)) ⁻¹' E ∪ xx ⁻¹' {xx t}
  have hremoved : ∀ t, MeasurableSet (removed t) := fun t =>
    ((hE.preimage measurable_prodMk_left).union (hE.preimage measurable_prodMk_right)).union
      (hxx (measurableSet_singleton _))
  let next : Good → Good := fun C =>
    ⟨C.1 \ removed (pick C), (C.2.1.diff (hremoved _)),
      measure_diff_eq_top_of_mem_Q μ (hpickQ C)
        ((hsec (pick C)).trans_lt ENNReal.one_lt_top).ne (hfib (xx (pick C)))⟩
  let Cs : ℕ → Good := fun n => Nat.rec ⟨univ, MeasurableSet.univ, by
    rw [hμ _ MeasurableSet.univ]; simp⟩ (fun _ C => next C) n
  let ts : ℕ → ℤ × Ω := fun n => pick (Cs n)
  have hCs_succ : ∀ n, (Cs (n + 1)).1 = (Cs n).1 \ removed (ts n) := fun n => rfl
  have hts_mem : ∀ n, ts n ∈ (Cs n).1 := fun n => (hpickQ (Cs n)).1
  have hCs_anti : ∀ n k, (Cs (n + k)).1 ⊆ (Cs n).1 := by
    intro n k
    induction k with
    | zero => exact subset_refl _
    | succ k ih =>
      refine (show (Cs (n + k + 1)).1 ⊆ (Cs (n + k)).1 from ?_).trans ih
      rw [hCs_succ]
      exact diff_subset
  have hnotin : ∀ i j, i < j → ts j ∉ removed (ts i) := by
    intro i j hij
    obtain ⟨k, rfl⟩ : ∃ k, j = (i + 1) + k := ⟨j - (i + 1), by omega⟩
    have := hCs_anti (i + 1) k (hts_mem _)
    rw [hCs_succ] at this
    exact this.2
  -- the independent set
  have hne : ∀ i j, i < j → xx (ts j) ≠ xx (ts i) := fun i j hij h =>
    hnotin i j hij (Or.inr h)
  have hinj : Function.Injective fun n => xx (ts n) := by
    intro i j h
    by_contra hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hne i j hlt h.symm
    · exact hne j i hlt h
  refine ⟨range fun n => xx (ts n), infinite_range_of_injective hinj, ?_⟩
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij hmem
  have hij' : i ≠ j := fun h => hij (by rw [h])
  -- `xx (ts i) ∈ A (xx (ts j)) ⊆ UU (ts j)` since `(ts j).2 ∈ Z`; contradiction with `(ts i, ts j) ∉ E`
  have hU : xx (ts i) ∈ UU (ts j) := cert.subset_U _ _ (hpickZ (Cs j)) hmem
  rcases lt_or_gt_of_ne hij' with hlt | hlt
  · exact hnotin i j hlt (Or.inl (Or.inl hU))
  · exact hnotin j i hlt (Or.inl (Or.inr hU))

/-! ### The logical decomposition (1.1) of the paper, in the ground model -/

/-- **(1.1), first line, in the ground model**: if every bounded family of outer measure `< 1` admits a
certificate, then Erdős #501 (first question) holds — the DeepMind proposition `erdos501_deepmind`.
(Unit (F6) produces the certificates *inside the forcing extension*; the transfer of this line into
the extension is unit (F7) of the audit.) -/
theorem erdos501_deepmind_of_certificate (Ω : Type*) [MeasurableSpace Ω]
    (h : ∀ A : ℝ → Set ℝ, (∀ x, Bornology.IsBounded (A x)) →
      (∀ x, volume.toOuterMeasure (A x) < 1) → Nonempty (Certificate A Ω)) :
    erdos501_deepmind := fun A hb hm =>
  let ⟨c⟩ := h A hb hm
  exists_infinite_independent_of_certificate c

/-! ### An ingredient of (F6): the test points `x_m(z) = m + ρ(z 0)` satisfy (P2) -/

/-- **(P2) for the profile test points.**  If `ρ : 2^ω → ℝ` pushes the coin measure `κ` forward to
Lebesgue measure on `[0, 1)`, then on the profile space `2^P = ℕ → 2^ω` (with the product measure
`κ^ℕ`) the test map `z ↦ m + ρ (z 0)` has law Lebesgue measure on `[m, m + 1)` — the paper's
`x_m(z) = m + ρ(z↾D)` with `D = {0}`.  (The construction of a measure-preserving `ρ`, e.g. binary
expansion, is a separate ground-model lemma.) -/
theorem map_profileTest {κ : Measure (ℕ → Bool)} [IsProbabilityMeasure κ]
    {ρ : (ℕ → Bool) → ℝ} (hρm : Measurable ρ) (hρ : κ.map ρ = volume.restrict (Ico (0 : ℝ) 1))
    (m : ℤ) :
    (Measure.infinitePi (fun _ : ℕ => κ)).map (fun z : ℕ → (ℕ → Bool) => (m : ℝ) + ρ (z 0)) =
      volume.restrict (Ico (m : ℝ) (m + 1)) := by
  have h0 : (Measure.infinitePi (fun _ : ℕ => κ)).map (fun z : ℕ → (ℕ → Bool) => z 0) = κ :=
    Measure.infinitePi_map_eval _ 0
  have hcomp : (fun z : ℕ → (ℕ → Bool) => (m : ℝ) + ρ (z 0)) =
      (fun t : ℝ => t + m) ∘ ρ ∘ (fun z : ℕ → (ℕ → Bool) => z 0) := by
    funext z; simp [add_comm]
  rw [hcomp, ← Measure.map_map (measurable_add_const _) (hρm.comp (measurable_pi_apply 0)),
    ← Measure.map_map hρm (measurable_pi_apply 0), h0, hρ]
  -- translate Lebesgue measure on `[0, 1)` by `m`
  have h1 : (volume.map (fun t : ℝ => t + m)).restrict (Ico (m : ℝ) (m + 1)) =
      (volume.restrict ((fun t : ℝ => t + m) ⁻¹' Ico (m : ℝ) (m + 1))).map (fun t : ℝ => t + m) :=
    Measure.restrict_map (measurable_add_const _) measurableSet_Ico
  rw [MeasureTheory.map_add_right_eq_self, preimage_add_const_Ico, sub_self,
    show (m : ℝ) + 1 - m = 1 by ring] at h1
  exact h1.symm

end Flypitch.Erdos501.ZFCCore
