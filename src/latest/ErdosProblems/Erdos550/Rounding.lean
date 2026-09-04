import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Decomposition of the exact null-blocker rounding theorem (Theorem 4.1)

This file develops the measure-theoretic machinery used to prove
`Erdos550.exact_rounding` (stated in `NullBlocker.lean`).  We work on the product
probability space `∀ i, Ω i` with measure `MeasureTheory.Measure.pi μ`.

For a point `ω` of the product space and a vertex `x`, `compatCount ω x` counts
the coordinates `i` with `ω i ∈ A i x`.  Condition (N1) gives a *termwise*
inequality `μ {compatCount = ?? ≤ q-2} ≤ μ {compatCount = q}`
(`measure_U_le_measure_Y`), obtained from the pointwise bound
`1_{t≤q-2} + t ≤ (q-1) + 1_{t=q}` and `∫ t = ∑ ρ_i`.  Together with the `a`-set
bound (`ae_no_aset_compatible`) this controls the integral of the count of
`{compatCount ≤ q-2}` vertices, and a Markov + integer-valued argument yields an
outcome with at most `a-1` such vertices and the blocking pattern.
-/

open MeasureTheory Finset Function
open scoped ENNReal

namespace Erdos550

section Rounding

variable {q : ℕ} {X : Type*} [Countable X]
  {Ω : Fin q → Type*} [∀ i, MeasurableSpace (Ω i)]
  (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
  (A : ∀ i, X → Set (Ω i))

/-- The "all-coordinates-compatible" box for a vertex `x`. -/
def Box (x : X) : Set (∀ i, Ω i) := Set.univ.pi (fun i => A i x)

open Classical in
/-- Number of coordinates `i` at which `ω i ∈ A i x`. -/
noncomputable def compatCount (ω : ∀ i, Ω i) (x : X) : ℕ :=
  (Finset.univ.filter (fun i => ω i ∈ A i x)).card

/-- Marginal of the product measure on a single coordinate. -/
lemma pi_marginal (i : Fin q) (B : Set (Ω i)) (hB : MeasurableSet B) :
    Measure.pi μ {ω | ω i ∈ B} = μ i B := by
  convert! ( MeasureTheory.MeasurePreserving.measure_preimage ?_ ?_ ) using 1;
  · exact measurePreserving_eval μ i;
  · exact hB.nullMeasurableSet

omit [Countable X] in
/-- The product measure of a box is the product of the marginal measures. -/
lemma measure_box (x : X) :
    Measure.pi μ (Box A x) = ∏ i, μ i (A i x) :=
  Measure.pi_pi μ _

/-
`compatCount ω x = q` exactly describes the box `Box A x`.
-/
omit [Countable X] [∀ i, MeasurableSpace (Ω i)] in
lemma compatCount_eq_q_iff (ω : ∀ i, Ω i) (x : X) :
    compatCount A ω x = q ↔ ω ∈ Box A x := by
  constructor;
  · unfold compatCount;
    exact fun h => fun i _ => by_contra fun hi => absurd h ( by rw [ Finset.card_filter ] ; exact ne_of_lt ( lt_of_lt_of_le ( Finset.sum_lt_sum ( fun a _ => by aesop ) ⟨ i, Finset.mem_univ i, by aesop ⟩ ) ( by simp +decide ) ) );
  · intro hω; unfold Box at hω; simp_all +decide [ compatCount ] ;

/-
`compatCount · x` is a measurable function of `ω`.
-/
omit [Countable X] in
lemma measurable_compatCount (x : X) (hA : ∀ i x, MeasurableSet (A i x)) :
    Measurable (fun ω => compatCount A ω x) := by
  convert! Finset.measurable_sum Finset.univ fun i _ => measurable_const.indicator ( hA i x |> MeasurableSet.preimage <| measurable_pi_apply i ) using 1;
  ext ω; simp +decide [ compatCount, Set.indicator ] ;
  rw [ Finset.sum_boole ];
  · norm_cast;
  · infer_instance

/-
The integral of `compatCount · x` is the sum of the marginal densities.
-/
omit [Countable X] in
lemma lintegral_compatCount (x : X) (hA : ∀ i x, MeasurableSet (A i x)) :
    ∫⁻ ω, (compatCount A ω x : ℝ≥0∞) ∂(Measure.pi μ) = ∑ i, μ i (A i x) := by
  convert! MeasureTheory.lintegral_finset_sum _ _;
  case convert_6 => exact fun i ω => Set.indicator { ω | ω i ∈ A i x } ( fun _ => 1 ) ω;
  · simp +decide [ compatCount, Set.indicator ];
  · rw [ MeasureTheory.lintegral_indicator ];
    · simp only [MeasureTheory.setLIntegral_one];
      rw [ ← pi_marginal ] ; aesop;
    · exact measurable_pi_apply _ ( hA _ _ );
  · exact fun i _ => Measurable.indicator ( measurable_const ) ( measurableSet_preimage ( measurable_pi_apply i ) ( hA i x ) )

/-
**Termwise balance from (N1).**  The measure of the set of outcomes where `x`
misses at least two coordinates is at most the measure of the set where `x`
matches all coordinates.
-/
omit [Countable X] in
lemma measure_U_le_measure_Y (hq : 2 ≤ q) (x : X) (hA : ∀ i x, MeasurableSet (A i x))
    (hN1x : (q : ℝ≥0∞) - 1 ≤ ∑ i, μ i (A i x)) :
    Measure.pi μ {ω | compatCount A ω x ≤ q - 2}
      ≤ Measure.pi μ {ω | compatCount A ω x = q} := by
  -- By the properties of the product measure, we can rewrite the integrals in terms of the marginals.
  have h_integral : ∫⁻ ω, (if (compatCount A ω x) ≤ q - 2 then 1 else 0) ∂Measure.pi μ + ∫⁻ ω, (compatCount A ω x : ℝ≥0∞) ∂Measure.pi μ ≤ ∫⁻ ω, (((q - 1 : ℕ) : ℝ≥0∞)) ∂Measure.pi μ + ∫⁻ ω, (if (compatCount A ω x) = q then 1 else 0) ∂Measure.pi μ := by
    rw [ ← MeasureTheory.lintegral_add_left', ← MeasureTheory.lintegral_add_left' ];
    · refine' MeasureTheory.lintegral_mono fun ω => _;
      have hc : compatCount A ω x ≤ q := by
        exact le_trans (Finset.card_le_univ _) (by simp)
      have hn : (if compatCount A ω x ≤ q - 2 then 1 else 0) + compatCount A ω x ≤
          q - 1 + (if compatCount A ω x = q then 1 else 0) := by
        split_ifs <;> omega
      simpa only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
        (Nat.mono_cast (α := ℝ≥0∞) hn)
    · exact aemeasurable_const;
    · refine' Measurable.aemeasurable _;
      exact Measurable.ite ( measurableSet_le ( measurable_compatCount A x hA ) measurable_const ) measurable_const measurable_const;
  convert! ENNReal.le_of_add_le_add_right _ _ using 1;
  exact ∑ i, μ i ( A i x );
  · exact ne_of_lt ( lt_of_le_of_lt ( Finset.sum_le_sum fun _ _ => MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide [ MeasureTheory.IsProbabilityMeasure.measure_univ ] ) );
  · convert! h_integral.trans _ using 1;
    · rw [ lintegral_compatCount ];
      · rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
        change ( Measure.pi μ ) { ω | compatCount A ω x ≤ q - 2 } + ∑ i, μ i ( A i x ) = ∫⁻ ω in { ω | compatCount A ω x ≤ q - 2 }, 1 ∂Measure.pi μ + ∑ i, μ i ( A i x );
        · simp +decide;
        · exact measurableSet_le ( measurable_compatCount A x hA ) measurable_const;
        · norm_num [ Filter.EventuallyEq, Set.indicator ];
      · assumption;
    · rw [ add_comm, MeasureTheory.lintegral_const ] ; norm_num;
      gcongr;
      rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
      change ∫⁻ ω in { ω | compatCount A ω x = q }, 1 ∂Measure.pi μ ≤ _;
      · simp +decide;
      · convert! measurableSet_eq_fun ( measurable_compatCount A x hA ) measurable_const using 1;
      · norm_num [ Filter.EventuallyEq, Set.indicator ]

/-- **Step 1.**  Under (N2), almost surely no `a`-subset of `X` is entirely
"all-compatible": for a.e. `ω` and every `S` of size `a`, some `x ∈ S` misses
some coordinate. -/
lemma ae_no_aset_compatible {a : ℕ}
    (hN2 : ∀ S : Finset X, S.card = a → ∃ i, μ i (⋂ x ∈ S, A i x) = 0) :
    ∀ᵐ ω ∂(Measure.pi μ), ∀ S : Finset X, S.card = a →
      ∃ x ∈ S, ∃ i, ω i ∉ A i x := by
  have h_all : ∀ S : Finset X, S.card = a → ∀ᵐ ω ∂Measure.pi μ, ∃ x ∈ S, ∃ i, ω i ∉ A i x := by
    intro S hS;
    obtain ⟨ i, hi ⟩ := hN2 S hS;
    have h_pi_zero : Measure.pi μ (Set.univ.pi (fun j => if j = i then ⋂ x ∈ S, A j x else Set.univ)) = 0 := by
      rw [ MeasureTheory.Measure.pi_pi ];
      rw [ Finset.prod_eq_zero ( Finset.mem_univ i ) ] ; aesop;
    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_pi_zero ] with ω hω;
    contrapose! hω; aesop;
  rw [ MeasureTheory.ae_all_iff ] ; aesop

omit [Countable X] in
/-- **Step 5.**  Given for each edge a "blocker" coordinate `j` with null common
neighbourhood, almost surely every edge fails to be contained in the blocker's
positive set. -/
lemma ae_blocking {ι : Type*} [Countable ι] (E : ι → Finset X) (j : ι → Fin q)
    (hA : ∀ i x, MeasurableSet (A i x))
    (hnull : ∀ e, μ (j e) (⋂ x ∈ E e, A (j e) x) = 0) :
    ∀ᵐ ω ∂(Measure.pi μ), ∀ e, ∃ x ∈ E e, ω (j e) ∉ A (j e) x := by
  refine' MeasureTheory.ae_all_iff.2 fun e => MeasureTheory.measure_mono_null ?_ ( pi_marginal μ ( j e ) _ ?_ |> fun h ↦ h.symm ▸ hnull e );
  · simp +contextual [ Set.subset_def ];
  · exact MeasurableSet.biInter ( Finset.countable_toSet _ ) fun x hx => hA _ _

/-- The `ℝ≥0∞`-valued count of vertices missing at least two coordinates. -/
noncomputable def Ucard (ω : ∀ i, Ω i) : ℝ≥0∞ :=
  ∑' x : X, if compatCount A ω x ≤ q - 2 then 1 else 0

/-- The `ℝ≥0∞`-valued count of vertices matching all coordinates. -/
noncomputable def Ycard (ω : ∀ i, Ω i) : ℝ≥0∞ :=
  ∑' x : X, if compatCount A ω x = q then 1 else 0

/-
The integral of `Ucard` is the sum over vertices of the `U`-event measures.
-/
omit [∀ i, IsProbabilityMeasure (μ i)] in
lemma lintegral_Ucard (hA : ∀ i x, MeasurableSet (A i x)) :
    ∫⁻ ω, Ucard A ω ∂(Measure.pi μ)
      = ∑' x : X, Measure.pi μ {ω | compatCount A ω x ≤ q - 2} := by
  convert! MeasureTheory.lintegral_tsum _;
  · rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
    · exact (setLIntegral_one _).symm;
    · exact measurableSet_le ( measurable_compatCount _ _ hA ) measurable_const;
    · norm_num [ Filter.EventuallyEq, Set.indicator ];
  · infer_instance;
  · intro x;
    refine' Measurable.aemeasurable _;
    exact Measurable.ite ( measurableSet_le ( measurable_compatCount A x hA ) measurable_const ) measurable_const measurable_const

/-
The integral of `Ycard` is the sum over vertices of the `Y`-event measures.
-/
omit [∀ i, IsProbabilityMeasure (μ i)] in
lemma lintegral_Ycard (hA : ∀ i x, MeasurableSet (A i x)) :
    ∫⁻ ω, Ycard A ω ∂(Measure.pi μ)
      = ∑' x : X, Measure.pi μ {ω | compatCount A ω x = q} := by
  rw [ show Ycard A = fun ω => ∑' x : X, if compatCount A ω x = q then 1 else 0 from rfl, MeasureTheory.lintegral_tsum ];
  · congr! 2;
    rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
    · exact setLIntegral_one _;
    · exact measurableSet_eq_fun ( measurable_compatCount _ _ hA ) measurable_const;
    · norm_num [ Filter.EventuallyEq, Set.indicator ];
  · intro x;
    refine' Measurable.aemeasurable _;
    exact Measurable.ite ( measurableSet_eq_fun ( measurable_compatCount A x hA ) measurable_const ) measurable_const measurable_const

/-
Almost surely, at most `a-1` vertices match all coordinates.
-/
lemma Ycard_ae_le {a : ℕ}
    (hN2 : ∀ S : Finset X, S.card = a → ∃ i, μ i (⋂ x ∈ S, A i x) = 0) :
    ∀ᵐ ω ∂(Measure.pi μ), Ycard A ω ≤ ((a : ℕ) - 1 : ℕ) := by
  filter_upwards [ ae_no_aset_compatible μ A hN2 ] with ω h;
  by_cases ha : a = 0;
  · aesop;
  · have h_s_encard : ∀ S : Finset X, (∀ x ∈ S, compatCount A ω x = q) → S.card ≤ a - 1 := by
      intro S hS; contrapose! h; simp_all +decide [ compatCount_eq_q_iff ] ;
      obtain ⟨ T, hT ⟩ := Finset.exists_subset_card_eq h;
      exact ⟨ T, by rw [ hT.2, Nat.succ_eq_add_one, Nat.sub_add_cancel ( Nat.pos_of_ne_zero ha ) ], fun x hx i => hS x ( hT.1 hx ) i ( Set.mem_univ i ) ⟩;
    by_cases h_finite : Set.Finite {x : X | compatCount A ω x = q};
    · have hsum : ∑' x : X, (if compatCount A ω x = q then 1 else 0) = ∑ x ∈ h_finite.toFinset, (1 : ℝ≥0∞) := by
        rw [ tsum_eq_sum ];
        exacts [ Finset.sum_congr rfl fun x hx => if_pos <| h_finite.mem_toFinset.mp hx, fun x hx => if_neg <| fun hx' => hx <| h_finite.mem_toFinset.mpr hx' ];
      have hcard : h_finite.toFinset.card ≤ a - 1 :=
        h_s_encard _ fun x hx => h_finite.mem_toFinset.mp hx
      calc
        Ycard A ω = (h_finite.toFinset.card : ℝ≥0∞) := by
          unfold Ycard
          rw [hsum]
          simp
        _ ≤ ((a : ℕ) - 1 : ℕ) := by exact_mod_cast hcard
    · contrapose! h_s_encard;
      obtain ⟨ S, hS ⟩ := Set.Infinite.exists_subset_card_eq h_finite ( a - 1 + 1 );
      exact ⟨ S, fun x hx => hS.1 hx, by rw [ hS.2 ] ; exact Nat.lt_succ_self _ ⟩

/-
The integral of `Ucard` is at most `a-1`.
-/
lemma lintegral_Ucard_le {a : ℕ} (hq : 2 ≤ q) (hA : ∀ i x, MeasurableSet (A i x))
    (hN1 : ∀ x : X, (q : ℝ≥0∞) - 1 ≤ ∑ i, μ i (A i x))
    (hN2 : ∀ S : Finset X, S.card = a → ∃ i, μ i (⋂ x ∈ S, A i x) = 0) :
    ∫⁻ ω, Ucard A ω ∂(Measure.pi μ) ≤ ((a : ℕ) - 1 : ℕ) := by
  refine' le_trans _ ( show ∫⁻ ω : ( i : Fin q ) → Ω i, Ycard A ω ∂Measure.pi μ ≤ ↑ ( a - 1 ) from _ );
  · rw [ Erdos550.lintegral_Ucard μ A hA, Erdos550.lintegral_Ycard μ A hA ];
    exact ENNReal.tsum_le_tsum fun x => Erdos550.measure_U_le_measure_Y μ A hq x hA ( hN1 x );
  · refine' le_trans ( MeasureTheory.lintegral_mono_ae _ ) _;
    refine' fun ω => ↑ ( a - 1 );
    · convert! Ycard_ae_le μ A hN2 using 1;
    · simp +decide

/-
`Ucard` is integer-or-infinite valued: for every `ω` it is `≤ a-1` or `≥ a`.
-/
omit [Countable X] [∀ i, MeasurableSpace (Ω i)] in
lemma Ucard_dichotomy {a : ℕ} (ω : ∀ i, Ω i) :
    Ucard A ω ≤ ((a : ℕ) - 1 : ℕ) ∨ (a : ℝ≥0∞) ≤ Ucard A ω := by
  by_contra h;
  simp_all +decide [ Ucard ];
  rw [ ENNReal.tsum_eq_iSup_sum ] at h;
  -- By definition of supremum, there exists a finite subset $s$ such that the sum over $s$ is greater than $a - 1$.
  obtain ⟨s, hs⟩ : ∃ s : Finset X, ∑ x ∈ s, (if compatCount A ω x ≤ q - 2 then 1 else 0) > a - 1 := by
    rcases exists_lt_of_lt_ciSup h.1 with ⟨ s, hs ⟩ ; exact ⟨ s, by exact_mod_cast hs ⟩;
  refine' h.2.not_ge _;
  refine' le_trans _ ( le_ciSup _ s );
  · simp +zetaDelta only [sum_boole, Nat.cast_le] at *;
    exact Nat.le_of_pred_lt hs;
  · exact OrderTop.bddAbove _

/-
**The probabilistic core.**  There is an outcome `ω` such that at most `a-1`
vertices miss at least two coordinates, and the blocking pattern holds for every
edge.
-/
set_option maxHeartbeats 1000000 in
lemma exists_good_outcome {a : ℕ} (hq : 2 ≤ q) (ha : 1 ≤ a)
    (hA : ∀ i x, MeasurableSet (A i x))
    (hN1 : ∀ x : X, (q : ℝ≥0∞) - 1 ≤ ∑ i, μ i (A i x))
    (hN2 : ∀ S : Finset X, S.card = a → ∃ i, μ i (⋂ x ∈ S, A i x) = 0)
    {ι : Type*} [Countable ι] (E : ι → Finset X) (j : ι → Fin q)
    (hnull : ∀ e, μ (j e) (⋂ x ∈ E e, A (j e) x) = 0) :
    ∃ ω : ∀ i, Ω i,
      {x : X | compatCount A ω x ≤ q - 2}.Finite ∧
      {x : X | compatCount A ω x ≤ q - 2}.ncard ≤ a - 1 ∧
      ∀ e, ∃ x ∈ E e, ω (j e) ∉ A (j e) x := by
  have hgood_pos : 0 < (Measure.pi μ) {ω | Ucard A ω ≤ ((a : ℕ) - 1 : ℕ)} := by
    have hgood_pos : (Measure.pi μ) {ω | (a : ℝ≥0∞) ≤ Ucard A ω} < 1 := by
      have h_measure_lt_one : (Measure.pi μ) {ω | (a : ℝ≥0∞) ≤ Ucard A ω} ≤ (∫⁻ ω, Ucard A ω ∂(Measure.pi μ)) / (a : ℝ≥0∞) := by
        convert! MeasureTheory.meas_ge_le_lintegral_div _ _ _ using 1;
        · refine' Measurable.aemeasurable _;
          convert! Measurable.ennreal_tsum _;
          · infer_instance;
          · exact fun x => Measurable.ite ( measurableSet_le ( measurable_compatCount A x hA ) measurable_const ) measurable_const measurable_const;
        · aesop;
        · exact ENNReal.natCast_ne_top a;
      refine' lt_of_le_of_lt h_measure_lt_one _;
      rw [ ENNReal.div_lt_iff ] <;> norm_num;
      · exact lt_of_le_of_lt ( lintegral_Ucard_le μ A hq hA hN1 hN2 ) ( by norm_cast; omega );
      · exact Or.inl ( ne_of_gt ha );
    have hgood_pos : (Measure.pi μ) {ω | Ucard A ω ≤ ((a : ℕ) - 1 : ℕ)} ≥ (Measure.pi μ) Set.univ - (Measure.pi μ) {ω | (a : ℝ≥0∞) ≤ Ucard A ω} := by
      refine' tsub_le_iff_left.mpr _;
      refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ );
      grind +suggestions;
    refine' lt_of_lt_of_le _ hgood_pos;
    simp_all +decide;
  obtain ⟨ω, hω⟩ : ∃ ω ∈ {ω | Ucard A ω ≤ ((a : ℕ) - 1 : ℕ)}, ∀ e, ∃ x ∈ E e, ω (j e) ∉ A (j e) x := by
    have := ae_blocking μ A E j hA hnull;
    contrapose! this;
    exact fun h => hgood_pos.ne' <| MeasureTheory.measure_mono_null ( fun x hx => by aesop ) h;
  refine' ⟨ ω, _, _, hω.2 ⟩;
  · have h_finite : ∑' x : X, (if compatCount A ω x ≤ q - 2 then 1 else 0 : ℝ≥0∞) ≤ (a - 1 : ℕ) := by
      exact hω.1;
    contrapose! h_finite;
    obtain ⟨S, hSsub, hScard⟩ := h_finite.exists_subset_card_eq (a - 1 + 1)
    rw [ENNReal.tsum_eq_iSup_sum]
    have hbdd : BddAbove (Set.range fun T : Finset X ↦
        ∑ x ∈ T, (if compatCount A ω x ≤ q - 2 then 1 else 0 : ℝ≥0∞)) := by
      refine ⟨⊤, ?_⟩
      rintro _ ⟨T, rfl⟩
      exact le_top
    refine lt_of_lt_of_le ?_ (le_ciSup hbdd S)
    have hsum :
        (∑ x ∈ S, if compatCount A ω x ≤ q - 2 then 1 else 0 : ℝ≥0∞) =
          (a : ℝ≥0∞) := by
      calc
        (∑ x ∈ S, if compatCount A ω x ≤ q - 2 then 1 else 0 : ℝ≥0∞) =
            ∑ x ∈ S, (1 : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxgood : compatCount A ω x ≤ q - 2 := hSsub (by simpa using hx)
          simp [hxgood]
        _ = (S.card : ℝ≥0∞) := by simp
        _ = (a : ℝ≥0∞) := by
          norm_cast
          omega
    rw [hsum]
    exact_mod_cast (show a - 1 < a by omega)
  · have h_card : (Set.ncard {x | compatCount A ω x ≤ q - 2}) ≤ Ucard A ω := by
      by_cases h : Set.Finite { x : X | compatCount A ω x ≤ q - 2 } <;> simp_all +decide [ Ucard ];
      · rw [ tsum_eq_sum ];
        any_goals exact h.toFinset;
        · simp +decide;
          rw [ ← Set.ncard_coe_finset ] ; aesop;
        · simp +contextual [ h.mem_toFinset ];
      · simp +decide [ h.ncard ];
    exact_mod_cast h_card.trans hω.1

/-
If at most one coordinate can be missing (`compatCount ≥ q-1`), then any two
missing coordinates coincide.
-/
omit [Countable X] [∀ i, MeasurableSpace (Ω i)] in
lemma missing_unique (ω : ∀ i, Ω i) (x : X)
    (hge : q - 1 ≤ compatCount A ω x) {k l : Fin q}
    (hk : ω k ∉ A k x) (hl : ω l ∉ A l x) : k = l := by
  contrapose! hge;
  refine' lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ _, _ ⟩ ) ) _;
  exact Finset.univ \ { k };
  · grind +splitIndPred;
  · simp_all +decide [ Finset.ext_iff ];
    grind;
  · simp +decide [ Finset.card_sdiff ]

end Rounding

end Erdos550
