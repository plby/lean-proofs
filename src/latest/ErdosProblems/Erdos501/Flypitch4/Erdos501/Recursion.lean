/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The recursion of Theorem 3.2 on names, part 1 (step S6 of `PLAN.md`): the σ-finite space
`ℤ × 2^P` of the profiles, the test map, the truncated envelopes, the relation `E`, the
parametrized good sets `Q(C)`, and one selection step.
-/
import ErdosProblems.Erdos501.Flypitch4.Erdos501.Selection
import ErdosProblems.Erdos501.Flypitch4.Erdos501.ZFCCore

set_option relaxedAutoImplicit true

/-!
# The recursion of Theorem 3.2 on names, part 1 (step S6)

We set up the ground-model objects of the paper's Theorem 3.2 *parametrized by the generic point*
`x : Ω ι` (through the root reading `x↾R`), and prove the measurability facts needed to run the
recursion pointwise in `x` with measurable choices:

* the σ-finite space `SS = ℤ × Prof` (`Prof = ℕ → 2^ω` the profiles) with `μS = counting ⊗ νP`,
  and the test map `xx (m, z) = m + binExp (z 0)`, which pushes `μS` forward to Lebesgue measure
  (`μS_preimage_xx`, from `map_profileTest_binExp`);
* the truncated envelopes `envSet E t (m, z) = ⋃ₙ (E (t, z) m n)` (empty outside the cover event),
  of Lebesgue measure `< 1` (`volume_envSet_lt_one`), and the relation
  `Erel E = {(t, s, s') | xx s ∈ envSet E t s'}`, jointly measurable (`measurableSet_Erel`);
* for a jointly measurable family `C : Ω ι → Set SS`, the good sets
  `QX E C x = Q μS (ErelX E x) (C x)` (Lemma 2.1 of `ZFCCore.lean`, `QX_pos`), jointly measurable
  (`measurableSet_QX_graph`), and their sections `sectionSet E C T m ⊆ 2^T × Prof` when `C`
  depends only on the coordinates in `T` (`mem_sectionSet_iff`);
* **one selection step** (`exists_stage_selection`): a countable list of candidates
  `cand k = (m, a) ∈ ℤ × J` and a measurable selector `sel` (depending only on the coordinates in
  `T` and in the candidates' petals) such that for a.e. `x` with `μS (C x) = ∞`, the point
  `((cand (sel x)).1, ĝ ∘ π (cand (sel x)).2)` lies in `QX E C x`.
-/

open MeasureTheory ProbabilityTheory Set Flypitch bSet Lattice
open scoped ENNReal Flypitch

namespace Flypitch.Erdos501.RandomForcing

open ZFCCore

variable {ι : Type}

/-! ### The σ-finite space `ℤ × 2^P` and the test map -/

/-- Profiles: sequences of reals. -/
abbrev Prof : Type := ℕ → (ℕ → Bool)

/-- The product measure on profiles. -/
noncomputable def νP : Measure Prof := Measure.infinitePi (fun _ : ℕ => RandomAlgebra.cantorMeasure)

instance : IsProbabilityMeasure νP := by unfold νP; infer_instance

/-- The σ-finite space `S = ℤ × 2^P`. -/
abbrev SS : Type := ℤ × Prof

/-- The σ-finite measure `counting ⊗ νP` on `S`. -/
noncomputable def μS : Measure SS := (Measure.count : Measure ℤ).prod νP

instance : SigmaFinite μS := by unfold μS; infer_instance

lemma μS_apply {s : Set SS} (hs : MeasurableSet s) : μS s = ∑' m : ℤ, νP (Prod.mk m ⁻¹' s) := by
  show (Measure.count.prod νP) s = _
  rw [Measure.prod_apply hs, lintegral_count]

/-- The test map `xx (m, z) = m + binExp (z 0)`. -/
noncomputable def xx (s : SS) : ℝ := (s.1 : ℝ) + binExp (s.2 0)

lemma measurable_test (m : ℤ) : Measurable fun z : Prof => (m : ℝ) + binExp (z 0) := by
  have h0 : Measurable fun z : Prof => z 0 := measurable_pi_apply 0
  exact measurable_const.add (measurable_binExp.comp h0)

lemma measurable_xx : Measurable xx :=
  measurable_from_prod_countable_right fun m => measurable_test m

/-- (P2) on `S`: `μS (xx ⁻¹' B) = λ B`. -/
theorem μS_preimage_xx {B : Set ℝ} (hB : MeasurableSet B) : μS (xx ⁻¹' B) = volume B := by
  rw [μS_apply (measurable_xx hB)]
  have h1 : ∀ m : ℤ, νP (Prod.mk m ⁻¹' (xx ⁻¹' B)) = volume (B ∩ Ico (m : ℝ) (m + 1)) := by
    intro m
    have : Prod.mk m ⁻¹' (xx ⁻¹' B) = (fun z : Prof => (m : ℝ) + binExp (z 0)) ⁻¹' B := rfl
    rw [this, ← Measure.map_apply (measurable_test m) hB]
    show (νP.map (fun z : Prof => (m : ℝ) + binExp (z 0))) B = _
    rw [νP, map_profileTest_binExp m, Measure.restrict_apply hB]
  simp_rw [h1]
  exact tsum_volume_inter_Ico B hB

lemma μS_preimage_xx_singleton (r : ℝ) : μS (xx ⁻¹' {r}) = 0 := by
  rw [μS_preimage_xx (measurableSet_singleton r)]; exact Real.volume_singleton

lemma μS_univ : μS (univ : Set SS) = ∞ := by
  rw [μS_apply MeasurableSet.univ]
  simp only [preimage_univ, measure_univ, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]

/-! ### The truncated envelopes and the relation `E` -/

variable {R : Set ι}

/-- Root readings. -/
abbrev Root (R : Set ι) : Type := R → (ℕ → Bool)

/-- The endpoint sequences of the envelope data `E`, at `m`. -/
def aE (E : Root R × Prof → ℤ → ℕ → ℝ × ℝ) (m : ℤ) (n : ℕ) (p : Root R × Prof) : ℝ := (E p m n).1
def bE (E : Root R × Prof → ℤ → ℕ → ℝ × ℝ) (m : ℤ) (n : ℕ) (p : Root R × Prof) : ℝ := (E p m n).2

variable {E : Root R × Prof → ℤ → ℕ → ℝ × ℝ}

lemma measurable_aE (hE : Measurable E) (m : ℤ) (n : ℕ) : Measurable (aE E m n) :=
  measurable_fst.comp ((measurable_pi_apply n).comp ((measurable_pi_apply m).comp hE))

lemma measurable_bE (hE : Measurable E) (m : ℤ) (n : ℕ) : Measurable (bE E m n) :=
  measurable_snd.comp ((measurable_pi_apply n).comp ((measurable_pi_apply m).comp hE))

open Classical in
/-- The truncated envelope: the open set `⋃ₙ (E (t, z) m n)` when the cover event holds at
`(t, z)` (for the given `m`), and `∅` otherwise. -/
noncomputable def envSet (E : Root R × Prof → ℤ → ℕ → ℝ × ℝ) (t : Root R) (s : SS) : Set ℝ :=
  if (t, s.2) ∈ coverEvent (aE E s.1) (bE E s.1) then
    ⋃ n, Ioo (aE E s.1 n (t, s.2)) (bE E s.1 n (t, s.2)) else ∅

open Classical in
lemma mem_envSet_iff (t : Root R) (s : SS) (r : ℝ) :
    r ∈ envSet E t s ↔ (t, s.2) ∈ coverEvent (aE E s.1) (bE E s.1) ∧
      ∃ n, aE E s.1 n (t, s.2) < r ∧ r < bE E s.1 n (t, s.2) := by
  unfold envSet
  split_ifs with h
  · simp [h]
  · simp [h]

/-- (P3): the envelopes have Lebesgue measure `< 1`. -/
theorem volume_envSet_lt_one (t : Root R) (s : SS) : volume (envSet E t s) < 1 := by
  classical
  unfold envSet
  split_ifs with h
  · exact volume_iUnion_Ioo_lt_one h
  · simp

lemma measurableSet_envSet (t : Root R) (s : SS) :
    MeasurableSet (envSet E t s) := by
  classical
  unfold envSet
  split_ifs
  · exact MeasurableSet.iUnion fun n => measurableSet_Ioo
  · exact MeasurableSet.empty

/-- Joint measurability of `r ∈ envSet E t s`. -/
lemma measurableSet_envGraph (hE : Measurable E) :
    MeasurableSet {q : (Root R × SS) × ℝ | q.2 ∈ envSet E q.1.1 q.1.2} := by
  classical
  have e : {q : (Root R × SS) × ℝ | q.2 ∈ envSet E q.1.1 q.1.2} =
      ⋃ m : ℤ, ({q : (Root R × SS) × ℝ | q.1.2.1 = m} ∩
        ({q | (q.1.1, q.1.2.2) ∈ coverEvent (aE E m) (bE E m)} ∩
          ⋃ n, {q | aE E m n (q.1.1, q.1.2.2) < q.2} ∩ {q | q.2 < bE E m n (q.1.1, q.1.2.2)})) := by
    ext ⟨⟨t, m, z⟩, r⟩
    simp only [mem_setOf_eq, mem_envSet_iff, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨h1, n, h2, h3⟩; exact ⟨m, rfl, h1, n, h2, h3⟩
    · rintro ⟨m', rfl, h1, n, h2, h3⟩; exact ⟨h1, n, h2, h3⟩
  rw [e]
  have hφ : Measurable fun q : (Root R × SS) × ℝ => (q.1.1, q.1.2.2) :=
    measurable_fst.fst.prodMk measurable_fst.snd.snd
  refine MeasurableSet.iUnion fun m => ?_
  refine (measurable_fst.snd.fst (measurableSet_singleton m)).inter ?_
  refine ((measurableSet_coverEvent (measurable_aE hE m) (measurable_bE hE m)).preimage hφ).inter ?_
  refine MeasurableSet.iUnion fun n => ?_
  exact (measurableSet_lt ((measurable_aE hE m n).comp hφ) measurable_snd).inter
    (measurableSet_lt measurable_snd ((measurable_bE hE m n).comp hφ))

/-- The relation `E`, parametrized by the root reading: `{(t, s, s') | xx s ∈ envSet E t s'}`. -/
def Erel (E : Root R × Prof → ℤ → ℕ → ℝ × ℝ) : Set (Root R × (SS × SS)) :=
  {q | xx q.2.1 ∈ envSet E q.1 q.2.2}

lemma measurableSet_Erel (hE : Measurable E) : MeasurableSet (Erel E) :=
  (measurableSet_envGraph hE).preimage
    ((measurable_fst.prodMk measurable_snd.snd).prodMk (measurable_xx.comp measurable_snd.fst))

/-- The relation `E` at the generic point `x`, read from the root: `Prod.mk (x↾R) ⁻¹' Erel E`. -/
def ErelX (E : Root R × Prof → ℤ → ℕ → ℝ × ℝ) (x : RandomAlgebra.Ω ι) : Set (SS × SS) :=
  Prod.mk (R.domRestrict x) ⁻¹' Erel E

lemma measurableSet_ErelX (hE : Measurable E) (x : RandomAlgebra.Ω ι) :
    MeasurableSet (ErelX E x) :=
  (measurableSet_Erel hE).preimage measurable_prodMk_left

lemma measurableSet_ErelX_graph (hE : Measurable E) :
    MeasurableSet {p : RandomAlgebra.Ω ι × (SS × SS) | p.2 ∈ ErelX E p.1} :=
  (measurableSet_Erel hE).preimage ((R.measurable_restrict.comp measurable_fst).prodMk measurable_snd)

lemma ErelX_congr {x y : RandomAlgebra.Ω ι} (h : EqOn x y R) : ErelX E x = ErelX E y := by
  have : R.domRestrict x = R.domRestrict y := by funext i; exact h i.2
  simp only [ErelX, this]

lemma mem_ErelX_iff (x : RandomAlgebra.Ω ι) (s s' : SS) :
    (s, s') ∈ ErelX E x ↔ xx s ∈ envSet E (R.domRestrict x) s' := Iff.rfl

/-- The horizontal sections of `E` have `μS`-measure `< 1`. -/
theorem μS_section_ErelX_le_one (x : RandomAlgebra.Ω ι) (s' : SS) :
    μS ((fun s => (s, s')) ⁻¹' ErelX E x) ≤ 1 := by
  have h : (fun s => (s, s')) ⁻¹' ErelX E x = xx ⁻¹' envSet E (R.domRestrict x) s' := rfl
  rw [h, μS_preimage_xx (measurableSet_envSet _ _)]
  exact (volume_envSet_lt_one _ _).le

/-! ### The parametrized good sets `Q(C)` -/

/-- The good set at the generic point `x`: `Q μS (ErelX E x) (C x)`. -/
def QX (E : Root R × Prof → ℤ → ℕ → ℝ × ℝ) (C : RandomAlgebra.Ω ι → Set SS)
    (x : RandomAlgebra.Ω ι) : Set SS :=
  Q μS (ErelX E x) (C x)

variable {C : RandomAlgebra.Ω ι → Set SS}

lemma measurableSet_C_of_graph (hC : MeasurableSet {p : RandomAlgebra.Ω ι × SS | p.2 ∈ C p.1})
    (x : RandomAlgebra.Ω ι) : MeasurableSet (C x) :=
  hC.preimage (measurable_prodMk_left (x := x))

/-- Joint measurability of the good sets. -/
lemma measurableSet_QX_graph (hE : Measurable E)
    (hC : MeasurableSet {p : RandomAlgebra.Ω ι × SS | p.2 ∈ C p.1}) :
    MeasurableSet {p : RandomAlgebra.Ω ι × SS | p.2 ∈ QX E C p.1} := by
  have e : {p : RandomAlgebra.Ω ι × SS | p.2 ∈ QX E C p.1} =
      {p | p.2 ∈ C p.1} ∩ (fun p : RandomAlgebra.Ω ι × SS =>
        μS (Prod.mk p ⁻¹' {q : (RandomAlgebra.Ω ι × SS) × SS |
          q.2 ∈ C q.1.1 ∧ (q.1.2, q.2) ∉ ErelX E q.1.1})) ⁻¹' {∞} := by
    ext ⟨x, s⟩
    simp only [QX, Q, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
    have : Prod.mk (x, s) ⁻¹' {q : (RandomAlgebra.Ω ι × SS) × SS |
        q.2 ∈ C q.1.1 ∧ (q.1.2, q.2) ∉ ErelX E q.1.1} = C x \ Prod.mk s ⁻¹' ErelX E x := by
      ext s'; simp
    rw [this]
  rw [e]
  refine hC.inter ?_
  refine measurable_measure_prodMk_left ?_ (measurableSet_singleton ∞)
  refine (hC.preimage (measurable_fst.fst.prodMk measurable_snd)).inter ?_
  exact ((measurableSet_ErelX_graph hE).preimage
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).compl

/-- Lemma 2.1, fibrewise: if `μS (C x) = ∞` then `μS (QX E C x) > 0`. -/
theorem QX_pos (hE : Measurable E) (hC : MeasurableSet {p : RandomAlgebra.Ω ι × SS | p.2 ∈ C p.1})
    (x : RandomAlgebra.Ω ι) (hinf : μS (C x) = ∞) : 0 < μS (QX E C x) :=
  measure_Q_pos μS (measurableSet_ErelX hE x) ENNReal.one_ne_top (μS_section_ErelX_le_one x)
    (measurableSet_C_of_graph hC x) hinf

/-- Some section of the good set has positive `νP`-measure. -/
theorem exists_section_pos (hE : Measurable E)
    (hC : MeasurableSet {p : RandomAlgebra.Ω ι × SS | p.2 ∈ C p.1})
    (x : RandomAlgebra.Ω ι) (hinf : μS (C x) = ∞) :
    ∃ m : ℤ, 0 < νP (Prod.mk m ⁻¹' QX E C x) := by
  have hQpos := QX_pos hE hC x hinf
  have hQm : MeasurableSet (QX E C x) := measurableSet_C_of_graph (measurableSet_QX_graph hE hC) x
  rw [μS_apply hQm] at hQpos
  by_contra h
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at h
  rw [ENNReal.tsum_eq_zero.mpr h] at hQpos
  exact lt_irrefl _ hQpos

lemma QX_congr {x y : RandomAlgebra.Ω ι} (hR : EqOn x y R) (hCxy : C x = C y) :
    QX E C x = QX E C y := by
  simp only [QX, ErelX_congr hR, hCxy]

/-! ### The sections of the good sets, as Borel sets over `2^T × 2^P` -/

variable (E C) (T : Set ι)

/-- The section at `m` of the good set, as a subset of `2^T × Prof` (via the extension `extT`). -/
def sectionSet (m : ℤ) : Set ((T → (ℕ → Bool)) × Prof) :=
  {p | (m, p.2) ∈ QX E C (extT T p.1)}

variable {E C T}

lemma measurableSet_sectionSet (hE : Measurable E)
    (hC : MeasurableSet {p : RandomAlgebra.Ω ι × SS | p.2 ∈ C p.1}) (m : ℤ) :
    MeasurableSet (sectionSet E C T m) :=
  (measurableSet_QX_graph hE hC).preimage
    (((measurable_extT T).comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))

lemma eqOn_extT_restrict (x : RandomAlgebra.Ω ι) : EqOn (extT T (T.domRestrict x)) x T := by
  intro i hi
  simp [extT, hi]

/-- For `C` depending only on the coordinates in `T ⊇ R`, the section set reads the good set:
`(x↾T, z) ∈ sectionSet E C T m ↔ (m, z) ∈ QX E C x`. -/
lemma mem_sectionSet_iff (hRT : R ⊆ T)
    (hinv : ∀ x y : RandomAlgebra.Ω ι, EqOn x y T → C x = C y) (x : RandomAlgebra.Ω ι) (m : ℤ)
    (z : Prof) : (T.domRestrict x, z) ∈ sectionSet E C T m ↔ (m, z) ∈ QX E C x := by
  simp only [sectionSet, mem_setOf_eq]
  rw [QX_congr ((eqOn_extT_restrict x).mono hRT) (hinv _ _ (eqOn_extT_restrict x))]

lemma preimage_sectionSet (hRT : R ⊆ T)
    (hinv : ∀ x y : RandomAlgebra.Ω ι, EqOn x y T → C x = C y) (x : RandomAlgebra.Ω ι) (m : ℤ) :
    Prod.mk (T.domRestrict x) ⁻¹' sectionSet E C T m = Prod.mk m ⁻¹' QX E C x := by
  ext z; exact mem_sectionSet_iff hRT hinv x m z


/-! ### One selection step of the recursion -/

/-- A fixed enumeration of `ℤ`. -/
noncomputable def intEnum : ℕ ≃ ℤ := (Denumerable.eqv ℤ).symm

/-- **One selection step.**  Given the jointly measurable family `C` depending only on the
coordinates in the countable `T ⊇ R`, and uncountably many pairwise disjoint petals `π a`
(`a ∈ J`), there are a countable list of candidates `cand k = (m, a)`, `a ∈ J`, and a measurable
selector `sel` depending only on the coordinates in `T` and in the candidates' petals, such that
for a.e. `x` with `μS (C x) = ∞`, `((cand (sel x)).1, ĝ ∘ π (cand (sel x)).2) ∈ QX E C x`. -/
theorem exists_stage_selection (hE : Measurable E)
    (hC : MeasurableSet {p : RandomAlgebra.Ω ι × SS | p.2 ∈ C p.1})
    {T : Set ι} (hT : T.Countable) (hRT : R ⊆ T)
    (hinv : ∀ x y : RandomAlgebra.Ω ι, EqOn x y T → C x = C y)
    {D : Type} {J : Set D} (hJ : ¬ J.Countable) {π : D → ℕ → ι}
    (hπ : ∀ a, Function.Injective (π a))
    (hdisj : ∀ a b, a ≠ b → Disjoint (Set.range (π a)) (Set.range (π b))) :
    ∃ (cand : ℕ → ℤ × D) (sel : RandomAlgebra.Ω ι → ℕ), (∀ k, (cand k).2 ∈ J) ∧ Measurable sel ∧
      (∀ x y : RandomAlgebra.Ω ι, EqOn x y (T ∪ ⋃ k, range (π (cand k).2)) → sel x = sel y) ∧
      ∀ᵐ x ∂(RandomAlgebra.μ_random ι), μS (C x) = ∞ →
        ((cand (sel x)).1, fun n => x (π (cand (sel x)).2 n)) ∈ QX E C x := by
  classical
  -- for each `i : ℕ` (coding `m = intEnum i`), a selection from fullness for the section set
  have hsel : ∀ i : ℕ, ∃ (a : ℕ → D) (s : RandomAlgebra.Ω ι → ℕ), (∀ k, a k ∈ J) ∧ Measurable s ∧
      (∀ x y : RandomAlgebra.Ω ι, EqOn x y (T ∪ ⋃ k, range (π (a k))) → s x = s y) ∧
      ∀ᵐ x ∂(RandomAlgebra.μ_random ι), x ∈ posEvent T (sectionSet E C T (intEnum i)) →
        x ∈ petalEvent T (sectionSet E C T (intEnum i)) (π (a (s x))) := fun i =>
    exists_selection_of_fullness T (measurableSet_sectionSet hE hC (intEnum i)) hJ hπ hdisj hT
  choose a s haJ hsmeas hsinv hsae using hsel
  -- the index of the first section of positive measure
  let mIdx : RandomAlgebra.Ω ι → ℕ :=
    firstIndex fun i => posEvent T (sectionSet E C T (intEnum i))
  have hmIdx : Measurable mIdx :=
    measurable_firstIndex fun i => measurableSet_posEvent T (measurableSet_sectionSet hE hC _)
  refine ⟨fun k => (intEnum (Nat.unpair k).1, a (Nat.unpair k).1 (Nat.unpair k).2),
    fun x => Nat.pair (mIdx x) (s (mIdx x) x), fun k => haJ _ _, ?_, ?_, ?_⟩
  · -- measurability of the selector
    have h1 : Measurable fun x => (mIdx x, s (mIdx x) x) := by
      refine hmIdx.prodMk ?_
      have hG : Measurable fun q : ℕ × RandomAlgebra.Ω ι => s q.1 q.2 :=
        measurable_from_prod_countable_right fun i => hsmeas i
      exact hG.comp (hmIdx.prodMk measurable_id)
    exact (measurable_of_countable (Function.uncurry Nat.pair)).comp h1
  · -- invariance of the selector
    intro x y hxy
    have hT' : EqOn x y T := hxy.mono subset_union_left
    have h1 : mIdx x = mIdx y :=
      firstIndex_congr fun i => posEvent_congr T hT'
    have h2 : s (mIdx x) x = s (mIdx x) y := by
      refine hsinv (mIdx x) x y (hxy.mono ?_)
      refine union_subset_union_right _ ?_
      refine iUnion_subset fun k => ?_
      have := subset_iUnion (fun k => range (π (intEnum (Nat.unpair k).1, a (Nat.unpair k).1
        (Nat.unpair k).2).2)) (Nat.pair (mIdx x) k)
      simpa only [Nat.unpair_pair] using this
    simp only [h1] at h2 ⊢
    rw [h2]
  · -- a.e. correctness
    have hae := (ae_all_iff.mpr hsae)
    filter_upwards [hae] with x hx hinf
    obtain ⟨m, hm⟩ := exists_section_pos hE hC x hinf
    have hpos : ∃ i, x ∈ posEvent T (sectionSet E C T (intEnum i)) := by
      refine ⟨intEnum.symm m, ?_⟩
      simp only [posEvent, mem_setOf_eq, Equiv.apply_symm_apply,
        preimage_sectionSet hRT hinv x m]
      exact hm
    have hmem := mem_firstIndex hpos
    have hpet := hx (mIdx x) hmem
    simp only [Nat.unpair_pair]
    rw [petalEvent, mem_setOf_eq, mem_sectionSet_iff hRT hinv] at hpet
    exact hpet


/-! ### The recursion -/

section recursion

/-- The data of a stage of the recursion: the current family of sets `C`, jointly measurable and
depending only on the coordinates in a countable `T ⊇ R`. -/
structure Stage (R : Set ι) where
  C : RandomAlgebra.Ω ι → Set SS
  hC : MeasurableSet {p : RandomAlgebra.Ω ι × SS | p.2 ∈ C p.1}
  T : Set ι
  hT : T.Countable
  hRT : R ⊆ T
  hinv : ∀ x y : RandomAlgebra.Ω ι, EqOn x y T → C x = C y

variable (R) in
/-- The initial stage: `C = univ`, `T = R`. -/
def stage0 (hR : R.Countable) : Stage R where
  C := fun _ => univ
  hC := by simp only [mem_univ, setOf_true]; exact MeasurableSet.univ
  T := R
  hT := hR
  hRT := le_rfl
  hinv := fun _ _ _ => rfl

variable {D : Type} {J : Set D} {π : D → ℕ → ι}

/-- The point chosen from a candidate list and a selector: `((cand (sel x)).1, ĝ ∘ π (cand (sel x)).2)`. -/
def tpt (π : D → ℕ → ι) (cand : ℕ → ℤ × D) (sel : RandomAlgebra.Ω ι → ℕ) (x : RandomAlgebra.Ω ι) :
    SS :=
  ((cand (sel x)).1, fun n => x (π (cand (sel x)).2 n))

lemma measurable_tpt (cand : ℕ → ℤ × D) {sel : RandomAlgebra.Ω ι → ℕ} (hsel : Measurable sel) :
    Measurable (tpt π cand sel) := by
  have hG : Measurable fun q : ℕ × RandomAlgebra.Ω ι =>
      (((cand q.1).1, fun n => q.2 (π (cand q.1).2 n)) : SS) := by
    refine measurable_from_prod_countable_right fun k => ?_
    show Measurable fun y : RandomAlgebra.Ω ι => (((cand k).1, fun n => y (π (cand k).2 n)) : SS)
    exact measurable_const.prodMk (measurable_pi_lambda _ fun n => measurable_pi_apply _)
  exact hG.comp (hsel.prodMk measurable_id)

/-- The set removed at a step: `E_t ∪ E^t ∪ xx⁻¹{xx t}`. -/
def removedX (E : Root R × Prof → ℤ → ℕ → ℝ × ℝ) (x : RandomAlgebra.Ω ι) (t : SS) : Set SS :=
  Prod.mk t ⁻¹' ErelX E x ∪ (fun s => (s, t)) ⁻¹' ErelX E x ∪ xx ⁻¹' {xx t}

lemma measurableSet_removedX_graph (hE : Measurable E) {f : RandomAlgebra.Ω ι → SS}
    (hf : Measurable f) :
    MeasurableSet {p : RandomAlgebra.Ω ι × SS | p.2 ∈ removedX E p.1 (f p.1)} := by
  have e : {p : RandomAlgebra.Ω ι × SS | p.2 ∈ removedX E p.1 (f p.1)} =
      ({p | (f p.1, p.2) ∈ ErelX E p.1} ∪ {p | (p.2, f p.1) ∈ ErelX E p.1}) ∪
        {p | xx p.2 = xx (f p.1)} := by
    ext ⟨x, s⟩; simp [removedX]
  rw [e]
  refine MeasurableSet.union (MeasurableSet.union ?_ ?_) ?_
  · exact (measurableSet_ErelX_graph hE).preimage
      (measurable_fst.prodMk ((hf.comp measurable_fst).prodMk measurable_snd))
  · exact (measurableSet_ErelX_graph hE).preimage
      (measurable_fst.prodMk (measurable_snd.prodMk (hf.comp measurable_fst)))
  · exact measurableSet_eq_fun (measurable_xx.comp measurable_snd)
      (measurable_xx.comp (hf.comp measurable_fst))

variable (hE : Measurable E) (hJ : ¬ J.Countable) (hπ : ∀ a, Function.Injective (π a))
  (hdisj : ∀ a b, a ≠ b → Disjoint (Set.range (π a)) (Set.range (π b)))

include hE hJ hπ hdisj in
/-- The choice (candidates and selector) at a stage. -/
noncomputable def choiceOf (st : Stage R) : (ℕ → ℤ × D) × (RandomAlgebra.Ω ι → ℕ) :=
  ⟨Classical.choose (exists_stage_selection hE st.hC st.hT st.hRT st.hinv hJ hπ hdisj),
    Classical.choose (Classical.choose_spec
      (exists_stage_selection hE st.hC st.hT st.hRT st.hinv hJ hπ hdisj))⟩

include hE hJ hπ hdisj in
lemma choiceOf_spec (st : Stage R) :
    (∀ k, ((choiceOf hE hJ hπ hdisj st).1 k).2 ∈ J) ∧
    Measurable (choiceOf hE hJ hπ hdisj st).2 ∧
    (∀ x y : RandomAlgebra.Ω ι, EqOn x y (st.T ∪ ⋃ k, range (π ((choiceOf hE hJ hπ hdisj st).1 k).2)) →
      (choiceOf hE hJ hπ hdisj st).2 x = (choiceOf hE hJ hπ hdisj st).2 y) ∧
    ∀ᵐ x ∂(RandomAlgebra.μ_random ι), μS (st.C x) = ∞ →
      tpt π (choiceOf hE hJ hπ hdisj st).1 (choiceOf hE hJ hπ hdisj st).2 x ∈ QX E st.C x :=
  Classical.choose_spec (Classical.choose_spec
    (exists_stage_selection hE st.hC st.hT st.hRT st.hinv hJ hπ hdisj))

include hE hJ hπ hdisj in
/-- The step of the recursion. -/
noncomputable def stepStage (st : Stage R) : Stage R where
  C := fun x => st.C x \ removedX E x (tpt π (choiceOf hE hJ hπ hdisj st).1
    (choiceOf hE hJ hπ hdisj st).2 x)
  hC := st.hC.diff (measurableSet_removedX_graph hE
    (measurable_tpt _ (choiceOf_spec hE hJ hπ hdisj st).2.1))
  T := st.T ∪ ⋃ k, range (π ((choiceOf hE hJ hπ hdisj st).1 k).2)
  hT := st.hT.union (countable_iUnion fun k => countable_range _)
  hRT := st.hRT.trans subset_union_left
  hinv := by
    intro x y hxy
    have h1 : st.C x = st.C y := st.hinv x y (hxy.mono subset_union_left)
    have h2 : ErelX E x = ErelX E y := ErelX_congr (hxy.mono (st.hRT.trans subset_union_left))
    have h3 : (choiceOf hE hJ hπ hdisj st).2 x = (choiceOf hE hJ hπ hdisj st).2 y :=
      (choiceOf_spec hE hJ hπ hdisj st).2.2.1 x y hxy
    have h4 : tpt π (choiceOf hE hJ hπ hdisj st).1 (choiceOf hE hJ hπ hdisj st).2 x =
        tpt π (choiceOf hE hJ hπ hdisj st).1 (choiceOf hE hJ hπ hdisj st).2 y := by
      simp only [tpt, h3]
      congr 1
      funext n
      apply hxy
      exact Or.inr (mem_iUnion.mpr ⟨(choiceOf hE hJ hπ hdisj st).2 y, ⟨n, rfl⟩⟩)
    simp only [removedX, h1, h2, h4]

variable (hR : R.Countable)

include hE hJ hπ hdisj hR in
/-- The stages of the recursion. -/
noncomputable def stage : ℕ → Stage R
  | 0 => stage0 R hR
  | j + 1 => stepStage hE hJ hπ hdisj (stage j)

/-- The point chosen at stage `j`. -/
noncomputable def tj (j : ℕ) (x : RandomAlgebra.Ω ι) : SS :=
  tpt π (choiceOf hE hJ hπ hdisj (stage hE hJ hπ hdisj hR j)).1
    (choiceOf hE hJ hπ hdisj (stage hE hJ hπ hdisj hR j)).2 x

lemma stage_zero_C (x : RandomAlgebra.Ω ι) : (stage hE hJ hπ hdisj hR 0).C x = univ := rfl

lemma stage_succ_C (j : ℕ) (x : RandomAlgebra.Ω ι) :
    (stage hE hJ hπ hdisj hR (j + 1)).C x =
      (stage hE hJ hπ hdisj hR j).C x \ removedX E x (tj hE hJ hπ hdisj hR j x) := rfl

lemma stage_C_anti (i k : ℕ) (x : RandomAlgebra.Ω ι) :
    (stage hE hJ hπ hdisj hR (i + k)).C x ⊆ (stage hE hJ hπ hdisj hR i).C x := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [← Nat.add_assoc, stage_succ_C]
    exact diff_subset.trans ih

/-- **The recursion is good almost everywhere**: for a.e. `x`, at every stage `μS (C_j x) = ∞`
and the chosen point lies in the good set `Q(C_j x)`. -/
theorem ae_good : ∀ᵐ x ∂(RandomAlgebra.μ_random ι), ∀ j,
    μS ((stage hE hJ hπ hdisj hR j).C x) = ∞ ∧
    tj hE hJ hπ hdisj hR j x ∈ QX E (stage hE hJ hπ hdisj hR j).C x := by
  have h := ae_all_iff.mpr fun j => (choiceOf_spec hE hJ hπ hdisj (stage hE hJ hπ hdisj hR j)).2.2.2
  filter_upwards [h] with x hx
  intro j
  induction j with
  | zero =>
    have h0 : μS ((stage hE hJ hπ hdisj hR 0).C x) = ∞ := by rw [stage_zero_C]; exact μS_univ
    exact ⟨h0, hx 0 h0⟩
  | succ j ih =>
    have hinf : μS ((stage hE hJ hπ hdisj hR (j + 1)).C x) = ∞ := by
      rw [stage_succ_C]
      exact measure_diff_eq_top_of_mem_Q μS ih.2
        ((μS_section_ErelX_le_one x _).trans_lt ENNReal.one_lt_top).ne
        (μS_preimage_xx_singleton _)
    exact ⟨hinf, hx (j + 1) hinf⟩

/-- For good `x` and `i < j`, the point chosen at stage `j` avoids the set removed at stage `i`. -/
theorem tj_not_mem_removedX {x : RandomAlgebra.Ω ι}
    (hx : ∀ j, μS ((stage hE hJ hπ hdisj hR j).C x) = ∞ ∧
      tj hE hJ hπ hdisj hR j x ∈ QX E (stage hE hJ hπ hdisj hR j).C x)
    {i j : ℕ} (hij : i < j) :
    tj hE hJ hπ hdisj hR j x ∉ removedX E x (tj hE hJ hπ hdisj hR i x) := by
  have hmem : tj hE hJ hπ hdisj hR j x ∈ (stage hE hJ hπ hdisj hR j).C x := (hx j).2.1
  obtain ⟨k, rfl⟩ : ∃ k, j = (i + 1) + k := ⟨j - (i + 1), by omega⟩
  have hsub := stage_C_anti hE hJ hπ hdisj hR (i + 1) k x
  have h := hsub hmem
  rw [stage_succ_C] at h
  exact h.2

end recursion

end Flypitch.Erdos501.RandomForcing
