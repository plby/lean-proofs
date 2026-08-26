/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Measurable selection of profiles from the fullness lemma (infrastructure for the recursion of
Theorem 3.2 on names, step S6 of `PLAN.md`).
-/
import ErdosProblems.Erdos501.Flypitch4.Erdos501.Envelopes

set_option relaxedAutoImplicit true

/-!
# Measurable selection from fullness (towards step S6)

The recursion of Theorem 3.2 (`ZFCCore.exists_infinite_independent_of_certificate`) picks at each
stage a profile in `Ż ∩ B` for a Borel set `B` of profiles of positive measure.  Run on names in
the ground model, this becomes: given a Borel `B' ⊆ 2^T × 2^P` read from the countable support
`T`, and the pairwise disjoint petals `π a` (`a ∈ J`, `J` uncountable), choose *measurably*, for
almost every generic point `x` with `ν(B'_{x↾T}) > 0`, an index `a = sel x ∈ J` with
`(x↾T, x ∘ π a) ∈ B'`, the choice taking only countably many values (`exists_selection_of_fullness`).

Ingredients: the fullness lemma (`fullness`: `‖ν(Ḃ) > ε‖ ≤ ⨆ a ∈ J, ‖ż_a ∈ Ḃ‖`), the fact that
every supremum in the measure algebra is a countable supremum (`exists_countable_iSup_eq`, from
the essential unions of `MeasureAlgebra.lean`), and the measurable "first index" selection from a
countable cover (`firstIndex`).
-/

open MeasureTheory ProbabilityTheory Set Flypitch bSet Lattice
open scoped ENNReal Flypitch

namespace Flypitch.MeasureAlgebra

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- **Every supremum in the measure algebra is a countable supremum.** -/
theorem exists_countable_iSup_eq {ι : Type*} [Nonempty ι] (s : ι → MeasureAlgebra μ) :
    ∃ f : ℕ → ι, ⨆ i, s i = ⨆ n, s (f n) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set S : Set (MeasureAlgebra μ) := range s with hS
  -- the essential family of `S`, and an index for each of its members
  have hmem : ∀ t : MSet X, t ∈ essFamily S → ∃ i, s i = mk μ t.1 t.2 := by
    intro t ht
    have := essFamily_subset S ht
    simp only [reps, hS, mem_setOf_eq, mem_range] at this
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi⟩
  choose idx hidx using hmem
  let I : Set ι := {i | ∃ (t : MSet X) (ht : t ∈ essFamily S), idx t ht = i} ∪ {i₀}
  have hI : I.Countable := by
    refine Set.Countable.union ?_ (countable_singleton _)
    have : {i | ∃ (t : MSet X) (ht : t ∈ essFamily S), idx t ht = i} =
        range (fun t : essFamily S => idx t.1 t.2) := by
      ext i; simp only [mem_setOf_eq, mem_range, Subtype.exists]
    rw [this]
    haveI : Countable (essFamily S) := (essFamily_countable S).to_subtype
    exact countable_range _
  obtain ⟨f, hf⟩ := hI.exists_eq_range ⟨i₀, Or.inr rfl⟩
  refine ⟨f, le_antisymm ?_ (iSup_le fun n => le_iSup _ (f n))⟩
  -- `⨆ i, s i = sSup' S = mk (⋃ essFamily S)`
  have h1 : (⨆ i, s i) = sSup' S := rfl
  rw [h1, sSup']
  have h2 : sUnion' (essFamily S) = ⋃ t : essFamily S, t.1.1 := by
    ext x; simp [sUnion']
  have hc : Countable (essFamily S) := (essFamily_countable S).to_subtype
  have h3 : mk μ (sUnion' (essFamily S)) (measurableSet_sUnion' (essFamily_countable S)) =
      ⨆ t : essFamily S, mk μ t.1.1 t.1.2 := by
    rw [iSup_mk]
    exact mk_congr h2
  rw [h3]
  refine iSup_le fun t => ?_
  rw [← hidx t.1 t.2]
  have hmem' : idx t.1 t.2 ∈ range f := by
    rw [← hf]; exact Or.inl ⟨t.1, t.2, rfl⟩
  obtain ⟨n, hn⟩ := hmem'
  rw [← hn]
  exact le_iSup (fun n => s (f n)) n

end Flypitch.MeasureAlgebra

namespace Flypitch.Erdos501.RandomForcing

variable {ι : Type}

/-! ### Measurable "first index" selection from a countable cover -/

section firstIndex

variable {X : Type*} [MeasurableSpace X]

/-- The auxiliary cover `S n ∪ (⋃ k, S k)ᶜ`, which always contains every point. -/
def firstIndexAux (S : ℕ → Set X) (n : ℕ) : Set X := S n ∪ (⋃ k, S k)ᶜ

omit [MeasurableSpace X] in
lemma exists_mem_firstIndexAux (S : ℕ → Set X) (x : X) : ∃ n, x ∈ firstIndexAux S n := by
  classical
  by_cases h : ∃ k, x ∈ S k
  · obtain ⟨k, hk⟩ := h; exact ⟨k, Or.inl hk⟩
  · exact ⟨0, Or.inr (by simpa using h)⟩

open Classical in
/-- The first index `n` with `x ∈ S n` (and `0` if there is none). -/
noncomputable def firstIndex (S : ℕ → Set X) (x : X) : ℕ :=
  Nat.find (exists_mem_firstIndexAux S x)

omit [MeasurableSpace X] in
open Classical in
lemma mem_firstIndex {S : ℕ → Set X} {x : X} (h : ∃ n, x ∈ S n) : x ∈ S (firstIndex S x) := by
  have hx : x ∈ ⋃ k, S k := mem_iUnion.mpr h
  have := Nat.find_spec (exists_mem_firstIndexAux S x)
  rcases this with h1 | h1
  · exact h1
  · exact absurd hx h1

open Classical in
lemma measurable_firstIndex {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n)) :
    Measurable (firstIndex S) :=
  measurable_find (exists_mem_firstIndexAux S) fun n =>
    (hS n).union (MeasurableSet.iUnion hS).compl

omit [MeasurableSpace X] in
open Classical in
/-- `firstIndex` only depends on the memberships `x ∈ S n`. -/
lemma firstIndex_congr {S : ℕ → Set X} {x y : X} (h : ∀ n, x ∈ S n ↔ y ∈ S n) :
    firstIndex S x = firstIndex S y := by
  unfold firstIndex
  apply Nat.find_congr'
  intro n
  simp only [firstIndexAux, mem_union, mem_compl_iff, mem_iUnion, not_exists, h]

end firstIndex

/-! ### Fullness with countably many petals -/

variable (T : Set ι) {B' : Set ((T → (ℕ → Bool)) × (ℕ → (ℕ → Bool)))}

/-- The event "the profile of the petal `π` lies in `B'`". -/
def petalEvent (B' : Set ((T → (ℕ → Bool)) × (ℕ → (ℕ → Bool)))) (π : ℕ → ι) :
    Set (RandomAlgebra.Ω ι) :=
  {x | (T.domRestrict x, fun n => x (π n)) ∈ B'}

lemma measurableSet_petalEvent (hB' : MeasurableSet B') (π : ℕ → ι) :
    MeasurableSet (petalEvent T B' π) :=
  (T.measurable_restrict.prodMk (measurable_pi_lambda _ fun n => measurable_pi_apply (π n))) hB'

/-- The event "the section `B'_{x↾T}` has positive measure". -/
def posEvent (B' : Set ((T → (ℕ → Bool)) × (ℕ → (ℕ → Bool)))) : Set (RandomAlgebra.Ω ι) :=
  {x | 0 < Measure.infinitePi (fun _ : ℕ => RandomAlgebra.cantorMeasure)
    (Prod.mk (T.domRestrict x) ⁻¹' B')}

lemma measurableSet_posEvent (hB' : MeasurableSet B') : MeasurableSet (posEvent T B') :=
  measurableSet_lt measurable_const ((measurable_measure_prodMk_left hB').comp T.measurable_restrict)

/-- **Fullness with countably many petals**: for uncountably many pairwise disjoint petals
`π a` (`a ∈ J`) and a Borel `B'` read from a countable `T`, there is a *sequence* `a k ∈ J` with
`‖ν(Ḃ) > 0‖ ≤ ⨆ k, ‖ż_{a k} ∈ Ḃ‖`, i.e. `[posEvent] ≤ [⋃ k, petalEvent (π (a k))]`. -/
theorem exists_seq_of_fullness (hB' : MeasurableSet B') {A : Type} {J : Set A}
    (hJ : ¬ J.Countable) {π : A → ℕ → ι} (hπ : ∀ a, Function.Injective (π a))
    (hdisj : ∀ a b, a ≠ b → Disjoint (Set.range (π a)) (Set.range (π b))) (hT : T.Countable) :
    ∃ a : ℕ → A, (∀ k, a k ∈ J) ∧
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (posEvent T B') (measurableSet_posEvent T hB') ≤
        MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (⋃ k, petalEvent T B' (π (a k)))
          (MeasurableSet.iUnion fun k => measurableSet_petalEvent T hB' (π (a k))) := by
  classical
  have hJne : J.Nonempty := by
    by_contra h
    exact hJ (by rw [not_nonempty_iff_eq_empty.mp h]; exact countable_empty)
  haveI : Nonempty J := hJne.to_subtype
  -- for each `k`, the fullness lemma with `ε = 1/k`, and its countable sup
  have hfull : ∀ k : ℕ, ∃ a : ℕ → J,
      measGtP T hB' ((k : ℝ≥0∞)⁻¹) ≤
        ⨆ n, MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (petalEvent T B' (π (a n)))
          (measurableSet_petalEvent T hB' (π (a n))) := by
    intro k
    have h := fullness T hB' hJ hπ hdisj hT (ε := (k : ℝ≥0∞)⁻¹)
      (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top k))
    obtain ⟨f, hf⟩ := MeasureAlgebra.exists_countable_iSup_eq
      (fun a : J => profileName (π a) ∈ᴮ borelNameP T hB')
    refine ⟨f, ?_⟩
    rw [hf] at h
    refine h.trans (iSup_mono fun n => ?_)
    rw [mem_borelNameP_profileName]
    exact le_rfl
  choose a ha using hfull
  -- diagonal enumeration
  refine ⟨fun k => (a (Nat.unpair k).1 (Nat.unpair k).2).1, fun k => (a _ _).2, ?_⟩
  -- `posEvent = ⋃ k, {x | 1/k < ν(B'_{x↾T})}`
  have hpos : posEvent T B' = ⋃ k : ℕ, {x | ((k : ℝ≥0∞)⁻¹) <
      Measure.infinitePi (fun _ : ℕ => RandomAlgebra.cantorMeasure)
        (Prod.mk (T.domRestrict x) ⁻¹' B')} := by
    ext x
    simp only [posEvent, mem_setOf_eq, mem_iUnion]
    constructor
    · intro h
      exact ENNReal.exists_inv_nat_lt (ne_of_gt h)
    · rintro ⟨k, hk⟩
      exact lt_of_le_of_lt (zero_le) hk
  have e1 : MeasureAlgebra.mk (RandomAlgebra.μ_random ι) (posEvent T B')
      (measurableSet_posEvent T hB') =
      ⨆ k : ℕ, MeasureAlgebra.mk (RandomAlgebra.μ_random ι) {x | ((k : ℝ≥0∞)⁻¹) <
        Measure.infinitePi (fun _ : ℕ => RandomAlgebra.cantorMeasure)
          (Prod.mk (T.domRestrict x) ⁻¹' B')}
        (measurableSet_lt measurable_const
          ((measurable_measure_prodMk_left hB').comp T.measurable_restrict)) := by
    rw [MeasureAlgebra.iSup_mk]
    exact MeasureAlgebra.mk_congr hpos
  have e2 : (⨆ k : ℕ, MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      (petalEvent T B' (π ((a (Nat.unpair k).1 (Nat.unpair k).2).1)))
      (measurableSet_petalEvent T hB' _)) =
      MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
        (⋃ k, petalEvent T B' (π ((a (Nat.unpair k).1 (Nat.unpair k).2).1)))
        (MeasurableSet.iUnion fun k => measurableSet_petalEvent T hB' _) :=
    MeasureAlgebra.iSup_mk _ _
  rw [e1, ← e2]
  refine iSup_le fun k => ?_
  have hk : measGtP T hB' ((k : ℝ≥0∞)⁻¹) = MeasureAlgebra.mk (RandomAlgebra.μ_random ι)
      {x | ((k : ℝ≥0∞)⁻¹) < Measure.infinitePi (fun _ : ℕ => RandomAlgebra.cantorMeasure)
        (Prod.mk (T.domRestrict x) ⁻¹' B')}
      (measurableSet_lt measurable_const
        ((measurable_measure_prodMk_left hB').comp T.measurable_restrict)) := rfl
  rw [← hk]
  refine (ha k).trans (iSup_le fun n => ?_)
  refine le_iSup_of_le (Nat.pair k n) ?_
  simp only [Nat.unpair_pair]
  exact le_rfl


/-- The petal event only depends on the coordinates in `T` and in the petal. -/
lemma petalEvent_congr {π : ℕ → ι} {x y : RandomAlgebra.Ω ι} (h : EqOn x y (T ∪ range π)) :
    x ∈ petalEvent T B' π ↔ y ∈ petalEvent T B' π := by
  have h1 : T.domRestrict x = T.domRestrict y := by
    funext i; exact h (Or.inl i.2)
  have h2 : (fun n => x (π n)) = fun n => y (π n) := by
    funext n; exact h (Or.inr ⟨n, rfl⟩)
  simp only [petalEvent, mem_setOf_eq, h1, h2]

/-- The positivity event only depends on the coordinates in `T`. -/
lemma posEvent_congr {x y : RandomAlgebra.Ω ι} (h : EqOn x y T) :
    x ∈ posEvent T B' ↔ y ∈ posEvent T B' := by
  have h1 : T.domRestrict x = T.domRestrict y := by
    funext i; exact h i.2
  simp only [posEvent, mem_setOf_eq, h1]

/-- **Measurable selection from fullness.**  There are a sequence `a k ∈ J` of petal indices and
a measurable selector `sel : Ω ι → ℕ` (depending only on the coordinates in `T` and in the petals
`π (a k)`) such that for a.e. `x` with `ν(B'_{x↾T}) > 0`, the profile of the petal `π (a (sel x))`
lies in `B'`. -/
theorem exists_selection_of_fullness (hB' : MeasurableSet B') {A : Type} {J : Set A}
    (hJ : ¬ J.Countable) {π : A → ℕ → ι} (hπ : ∀ a, Function.Injective (π a))
    (hdisj : ∀ a b, a ≠ b → Disjoint (Set.range (π a)) (Set.range (π b))) (hT : T.Countable) :
    ∃ (a : ℕ → A) (sel : RandomAlgebra.Ω ι → ℕ), (∀ k, a k ∈ J) ∧ Measurable sel ∧
      (∀ x y : RandomAlgebra.Ω ι, EqOn x y (T ∪ ⋃ k, range (π (a k))) → sel x = sel y) ∧
      ∀ᵐ x ∂(RandomAlgebra.μ_random ι), x ∈ posEvent T B' →
        x ∈ petalEvent T B' (π (a (sel x))) := by
  obtain ⟨a, haJ, hle⟩ := exists_seq_of_fullness T hB' hJ hπ hdisj hT
  refine ⟨a, firstIndex (fun k => petalEvent T B' (π (a k))), haJ,
    measurable_firstIndex fun k => measurableSet_petalEvent T hB' (π (a k)), ?_, ?_⟩
  · intro x y hxy
    refine firstIndex_congr fun k => petalEvent_congr T ?_
    exact hxy.mono (union_subset_union_right _ (subset_iUnion (fun k => range (π (a k))) k))
  · rw [MeasureAlgebra.mk_le_mk, MeasureAlgebra.ae_le_set_iff_ae_imp] at hle
    filter_upwards [hle] with x hx hpos
    exact mem_firstIndex (mem_iUnion.mp (hx hpos))

end Flypitch.Erdos501.RandomForcing
