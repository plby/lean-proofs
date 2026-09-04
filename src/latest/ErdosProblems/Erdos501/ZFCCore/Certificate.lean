/-
  Erdős problem 501 — the ZFC core, Section 3 of the profile-certificate draft.

  * `Erdos501.Certificate`  — Definition 3.1 (profile certificate).
      The "open envelope" `U(c_m(z))` is represented abstractly as a
      Lebesgue-measurable set `V m z ⊆ ℝ` (this is the only structure the
      ZFC core uses; the forcing module supplies such `V` from open codes).
  * `Erdos501.Free`         — the positive assertion `Free_ω(𝒜)`.
  * `Erdos501.prof_imp_free` — Theorem 3.2:  a certificate yields an infinite
      independent set.  Provable in ZFC.
-/
import ErdosProblems.Erdos501.ZFCCore.Selection
import ErdosProblems.Erdos501.ZFCCore.IcoPartition
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

open MeasureTheory Set
open scoped ENNReal

namespace Erdos501

/-- `Free_ω(𝒜)` : there is an infinite `X ⊆ ℝ` with `a ∉ A b` for distinct `a,b ∈ X`. -/
def Free (A : ℝ → Set ℝ) : Prop :=
  ∃ X : Set ℝ, X.Infinite ∧ ∀ ⦃a⦄, a ∈ X → ∀ ⦃b⦄, b ∈ X → a ≠ b → a ∉ A b

/-- **Definition 3.1** (profile certificate).  A witness structure whose mere
existence forces `Free_ω(𝒜)` in ZFC.  `Ω` is a probability space; `Z ⊆ Ω`
meets every positive-measure set (this is the content of `ν*(Z) = 1` that the
core uses); `x m` is Lebesgue-distributed on the block `[m, m+1)`; `V m z` is
the measurable "envelope" of measure `< 1` containing `A (x m z)` for `z ∈ Z`. -/
structure Certificate (A : ℝ → Set ℝ) where
  Ω : Type
  mΩ : MeasurableSpace Ω
  ν : Measure Ω
  isProb : IsProbabilityMeasure ν
  Z : Set Ω
  x : ℤ → Ω → ℝ
  V : ℤ → Ω → Set ℝ
  /-- (P1) `Z` meets every positive-measure measurable set (content of `ν*(Z)=1`). -/
  hZmeets : ∀ B : Set Ω, MeasurableSet B → 0 < ν B → ∃ z ∈ Z, z ∈ B
  /-- (P2a) each `x m` is measurable. -/
  hxmeas : ∀ m, Measurable (x m)
  /-- (P2b) `x m` is Lebesgue-distributed on the block `[m, m+1)`. -/
  hxdist : ∀ (m : ℤ) (B : Set ℝ), MeasurableSet B →
    ν (x m ⁻¹' B) = volume (B ∩ Set.Ico (m : ℝ) ((m : ℝ) + 1))
  /-- (P3a) the envelopes are jointly measurable. -/
  hVmeas : ∀ m, MeasurableSet {p : ℝ × Ω | p.1 ∈ V m p.2}
  /-- (P3b) each envelope has measure `< 1`. -/
  hVvol : ∀ m z, volume (V m z) < 1
  /-- (P4) over `Z`, the envelope contains the set it must forbid. -/
  hP4 : ∀ (m : ℤ), ∀ z ∈ Z, A (x m z) ⊆ V m z

/-- `Prof(𝒜)` : a profile certificate exists. -/
def Prof (A : ℝ → Set ℝ) : Prop := Nonempty (Certificate A)

/-- Each envelope `V m z` is a measurable subset of `ℝ`. -/
theorem Certificate.measurableSet_V {A : ℝ → Set ℝ} (cert : Certificate A) (m : ℤ) (z : cert.Ω) :
    MeasurableSet (cert.V m z) :=
  (cert.hVmeas m).preimage (measurable_id.prodMk measurable_const)

/-- **Theorem 3.2** (ZFC core).  A profile certificate yields an infinite
independent set.  No forcing, no CH. -/
theorem prof_imp_free {A : ℝ → Set ℝ} (cert : Certificate A) : Free A := by
  classical
  obtain ⟨Ω, mΩ, ν, hprob, Z, xf, Vf, hZmeets, hxmeas, hxdist, hVmeas, hVvol, hP4⟩ := cert
  let : MeasurableSpace Ω := mΩ
  have : IsProbabilityMeasure ν := hprob
  -- Discrete σ-algebra on ℤ.
  let : MeasurableSpace ℤ := ⊤
  have : MeasurableSingletonClass ℤ := ⟨fun _ => trivial⟩
  -- Envelopes are measurable as sets of reals.
  have hVsec : ∀ (m : ℤ) (z : Ω), MeasurableSet (Vf m z) :=
    fun m z => (hVmeas m).preimage (measurable_id.prodMk measurable_const)
  -- The σ-finite base space `S = ℤ × Ω`, `μ = count × ν`.
  set μ : Measure (ℤ × Ω) := (Measure.count).prod ν with hμ_def
  have : SigmaFinite (Measure.count : Measure ℤ) := inferInstance
  have : SigmaFinite μ := by rw [hμ_def]; infer_instance
  -- The point map and the envelope-as-set map.
  set xS : ℤ × Ω → ℝ := fun t => xf t.1 t.2 with hxS_def
  set VS : ℤ × Ω → Set ℝ := fun s => Vf s.1 s.2 with hVS_def
  have hxSmeas : Measurable xS := by
    have hf : Measurable (fun p : Ω × ℤ => xf p.2 p.1) :=
      measurable_from_prod_countable_left (fun m => hxmeas m)
    exact hf.comp measurable_swap
  have hVSmeas : ∀ s : ℤ × Ω, MeasurableSet (VS s) := fun s => hVsec s.1 s.2
  -- The Borel forbidding graph `E = {(t,s) | xS t ∈ VS s}`.
  set E : Set ((ℤ × Ω) × (ℤ × Ω)) := {p | xS p.1 ∈ VS p.2} with hE_def
  have hMem : MeasurableSet {q : ℝ × (ℤ × Ω) | q.1 ∈ VS q.2} := by
    have hEq : {q : ℝ × (ℤ × Ω) | q.1 ∈ VS q.2}
        = ⋃ m : ℤ, ((fun q : ℝ × (ℤ × Ω) => q.2.1) ⁻¹' {m})
            ∩ ((fun q : ℝ × (ℤ × Ω) => (q.1, q.2.2)) ⁻¹' {p : ℝ × Ω | p.1 ∈ Vf m p.2}) := by
      ext q
      simp only [VS, mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
      constructor
      · intro h; exact ⟨q.2.1, rfl, h⟩
      · rintro ⟨m, hm, h⟩; rw [hm]; exact h
    rw [hEq]
    refine MeasurableSet.iUnion (fun m => ?_)
    refine MeasurableSet.inter ?_ ?_
    · exact (measurableSet_singleton m).preimage (measurable_fst.comp measurable_snd)
    · exact (hVmeas m).preimage (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hE : MeasurableSet E := hMem.preimage ((hxSmeas.comp measurable_fst).prodMk measurable_snd)
  have hEmem : ∀ a b : ℤ × Ω, ((a, b) ∈ E) ↔ (xS a ∈ VS b) := fun a b => Iff.rfl
  ------------------------------------------------------------------
  -- Column bound `μ (E^s) ≤ 1`  (uses P2, P3, and the Ico partition).
  ------------------------------------------------------------------
  have hEcol : ∀ s : ℤ × Ω, μ {t | (t, s) ∈ E} ≤ 1 := by
    intro s
    have hWmeas : MeasurableSet (VS s) := hVSmeas s
    have hmeasset : MeasurableSet {t : ℤ × Ω | xS t ∈ VS s} := hxSmeas hWmeas
    have h1 : μ {t : ℤ × Ω | xS t ∈ VS s} = ∑' m : ℤ, ν (xf m ⁻¹' (VS s)) := by
      rw [hμ_def, Measure.prod_apply hmeasset, lintegral_count]
      rfl
    have h2 : ∀ m : ℤ, ν (xf m ⁻¹' (VS s))
        = volume (VS s ∩ Set.Ico (m : ℝ) ((m : ℝ) + 1)) :=
      fun m => hxdist m (VS s) hWmeas
    have h3 : ∑' m : ℤ, volume (VS s ∩ Set.Ico (m : ℝ) ((m : ℝ) + 1)) = volume (VS s) := by
      have hdisj : Pairwise (Function.onFun Disjoint
          fun m : ℤ => VS s ∩ Set.Ico (m : ℝ) ((m : ℝ) + 1)) := by
        intro m n hmn
        exact (pairwise_disjoint_Ico_int hmn).mono inter_subset_right inter_subset_right
      rw [← measure_iUnion hdisj (fun m => hWmeas.inter measurableSet_Ico),
        ← inter_iUnion, iUnion_Ico_int, inter_univ]
    have hcol_eq : {t : ℤ × Ω | (t, s) ∈ E} = {t : ℤ × Ω | xS t ∈ VS s} := rfl
    rw [hcol_eq, h1]
    calc ∑' m : ℤ, ν (xf m ⁻¹' (VS s))
        = ∑' m : ℤ, volume (VS s ∩ Set.Ico (m : ℝ) ((m : ℝ) + 1)) := by simp_rw [h2]
      _ = volume (VS s) := h3
      _ ≤ 1 := le_of_lt (hVvol s.1 s.2)
  ------------------------------------------------------------------
  -- Null fibers of `xS`  (uses P2 and `volume {a} = 0`).
  ------------------------------------------------------------------
  have hfiber : ∀ a : ℝ, μ {s | xS s = a} = 0 := by
    intro a
    have hmeasset : MeasurableSet {t : ℤ × Ω | xS t = a} := hxSmeas (measurableSet_singleton a)
    have h1 : μ {t : ℤ × Ω | xS t = a} = ∑' m : ℤ, ν (xf m ⁻¹' {a}) := by
      rw [hμ_def, Measure.prod_apply hmeasset, lintegral_count]
      rfl
    have h2 : ∀ m : ℤ, ν (xf m ⁻¹' {a}) = 0 := by
      intro m
      rw [hxdist m {a} (measurableSet_singleton a)]
      exact measure_mono_null inter_subset_left (by simp)
    rw [h1]
    simp only [h2, tsum_zero]
  ------------------------------------------------------------------
  -- `μ S = ∞`.
  ------------------------------------------------------------------
  have hSinf : μ (Set.univ : Set (ℤ × Ω)) = ∞ := by
    rw [hμ_def, ← Set.univ_prod_univ, Measure.prod_prod,
      Measure.count_apply_infinite Set.infinite_univ, measure_univ,
      ENNReal.top_mul one_ne_zero]
  ------------------------------------------------------------------
  -- The recursion engine (Lemmas 2.1 + 2.2).
  ------------------------------------------------------------------
  set Good : Set (ℤ × Ω) → Prop := fun C => MeasurableSet C ∧ μ C = ∞ with hGood_def
  have hgood_univ : Good (Set.univ : Set (ℤ × Ω)) := ⟨MeasurableSet.univ, hSinf⟩
  have step : ∀ C : Set (ℤ × Ω), Good C →
      ∃ t : ℤ × Ω, ∃ C' : Set (ℤ × Ω),
        Good C' ∧ t.2 ∈ Z ∧ t ∈ C ∧
        C' = C \ ({s | (t, s) ∈ E} ∪ {s | (s, t) ∈ E} ∪ {s | xS s = xS t}) := by
    intro C hC
    obtain ⟨hCmeas, hCinf⟩ := hC
    have hQpos := pos_measure_Q (μ := μ) hE (K := 1) ENNReal.one_ne_top hEcol hCmeas hCinf
    set Q : Set (ℤ × Ω) := {t | t ∈ C ∧ μ {s | s ∈ C ∧ (t, s) ∉ E} = ∞} with hQ_def
    have hQmeas : MeasurableSet Q := measurableSet_Q (μ := μ) hE hCmeas
    obtain ⟨m, hm⟩ : ∃ m : ℤ, 0 < ν (Prod.mk m ⁻¹' Q) := by
      by_contra hcon
      push_neg at hcon
      have hall : ∀ m, ν (Prod.mk m ⁻¹' Q) = 0 := fun m => le_antisymm (hcon m) bot_le
      have hz : μ Q = 0 := by
        rw [hμ_def, Measure.prod_apply hQmeas, lintegral_count]
        simp only [hall, tsum_zero]
      exact (pos_iff_ne_zero.mp hQpos) hz
    have hsecmeas : MeasurableSet (Prod.mk m ⁻¹' Q) := hQmeas.preimage measurable_prodMk_left
    obtain ⟨z, hzZ, hzQ⟩ := hZmeets _ hsecmeas hm
    have htQ : (m, z) ∈ Q := hzQ
    obtain ⟨hC'meas, hC'inf⟩ := infinite_measure_preservation (μ := μ) hE (K := 1)
      ENNReal.one_ne_top hEcol hxSmeas hfiber hCmeas (m, z) htQ.2
    exact ⟨(m, z), _, ⟨hC'meas, hC'inf⟩, hzZ, htQ.1, rfl⟩
  -- Package `step` as a data-carrying function.
  have stepData : ∀ C : {C : Set (ℤ × Ω) // Good C},
      { p : (ℤ × Ω) × {C : Set (ℤ × Ω) // Good C} //
          p.1.2 ∈ Z ∧ p.1 ∈ C.1 ∧
          p.2.1 = C.1 \ ({s | (p.1, s) ∈ E} ∪ {s | (s, p.1) ∈ E} ∪ {s | xS s = xS p.1}) } :=
    fun C => Classical.choice (nonempty_subtype.mpr (by
      obtain ⟨t, C', hC'good, hzZ, htC, hC'eq⟩ := step C.1 C.2
      exact ⟨(t, ⟨C', hC'good⟩), hzZ, htC, hC'eq⟩))
  -- Build the sequence of shrinking sets and chosen points.
  set seq : ℕ → {C : Set (ℤ × Ω) // Good C} :=
    fun n => Nat.rec ⟨Set.univ, hgood_univ⟩ (fun _ C => (stepData C).1.2) n with hseq_def
  set tpt : ℕ → ℤ × Ω := fun n => (stepData (seq n)).1.1 with htpt_def
  have hseqsucc : ∀ n, seq (n + 1) = (stepData (seq n)).1.2 := fun n => rfl
  have hspec : ∀ n, (tpt n).2 ∈ Z ∧ (tpt n) ∈ (seq n).1 ∧
      (seq (n + 1)).1 = (seq n).1 \
        ({s | (tpt n, s) ∈ E} ∪ {s | (s, tpt n) ∈ E} ∪ {s | xS s = xS (tpt n)}) := by
    intro n
    have h := (stepData (seq n)).2
    rw [hseqsucc]
    exact h
  -- The candidate independent set.
  set y : ℕ → ℝ := fun n => xS (tpt n) with hy_def
  -- Antitone shrinking.
  have hanti : Antitone (fun n => (seq n).1) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [(hspec n).2.2]
    exact diff_subset
  -- Pairwise independence.
  have hpair : ∀ i j, i < j → y j ∉ A (y i) ∧ y i ∉ A (y j) ∧ y i ≠ y j := by
    intro i j hij
    have hji : tpt j ∈ (seq (i + 1)).1 := hanti (Nat.succ_le_iff.mpr hij) (hspec j).2.1
    rw [(hspec i).2.2] at hji
    have hnot : tpt j ∉ ({s | (tpt i, s) ∈ E} ∪ {s | (s, tpt i) ∈ E} ∪ {s | xS s = xS (tpt i)}) :=
      hji.2
    simp only [mem_union, not_or, mem_setOf_eq] at hnot
    obtain ⟨⟨hrow, hcol⟩, hfib⟩ := hnot
    have hyi_not : y i ∉ VS (tpt j) := fun hmem => hrow ((hEmem (tpt i) (tpt j)).mpr hmem)
    have hyj_not : y j ∉ VS (tpt i) := fun hmem => hcol ((hEmem (tpt j) (tpt i)).mpr hmem)
    have hAi : A (y i) ⊆ VS (tpt i) := hP4 (tpt i).1 (tpt i).2 (hspec i).1
    have hAj : A (y j) ⊆ VS (tpt j) := hP4 (tpt j).1 (tpt j).2 (hspec j).1
    exact ⟨fun hmem => hyj_not (hAi hmem), fun hmem => hyi_not (hAj hmem), fun h => hfib h.symm⟩
  -- `y` is injective.
  have hyinj : Function.Injective y := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hpair a b h).2.2 hab
    · exact (hpair b a h).2.2 hab.symm
  -- Assemble `Free A` with `X = range y`.
  refine ⟨Set.range y, Set.infinite_range_of_injective hyinj, ?_⟩
  rintro a ⟨p, rfl⟩ b ⟨q, rfl⟩ hab
  have hpq : p ≠ q := fun h => hab (congrArg y h)
  rcases lt_or_gt_of_ne hpq with h | h
  · exact (hpair p q h).2.1
  · exact (hpair q p h).1

end Erdos501
