import Mathlib
import ErdosProblems.Erdos550.Rounding
import ErdosProblems.Erdos550.NullBlocker
import ErdosProblems.Erdos550.CubeEncoding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Shadow hypergraph / finite-transfer machinery

Infrastructure for the shadow-hypergraph compactness core of the null-blocker
compactness theorem (`thm:compactness`, lemmas `lem:fdlimit`–`lem:finitetransfer`
of the paper).
-/

open MeasureTheory Finset
open scoped ENNReal
open Filter Topology

namespace Erdos550

/-- The real-valued minimal impurity `e(x) = min_i ρ_i(x)` of a cube system. -/
noncomputable def cimp (q : ℕ) (ρ : Fin q → ProbabilityMeasure (ℕ → Bool))
    (x : ℕ) : ℝ :=
  ⨅ i, cdens q ρ i {x}

/-
**Product-sum bound** (`eq:productsum`).  On a countable exact system
satisfying (N2), the total mass of the all-coordinates boxes is at most `a-1`.
-/
lemma limit_productsum_bound (q : ℕ) (a : ℕ)
    {X : Type*} [Countable X]
    {Ω : Fin q → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ∀ i, X → Set (Ω i)) (hA : ∀ i x, MeasurableSet (A i x))
    (hN2 : ∀ S : Finset X, S.card = a → ∃ i, μ i (⋂ x ∈ S, A i x) = 0) :
    (∑' x : X, ∏ i, μ i (A i x)) ≤ ((a - 1 : ℕ) : ℝ≥0∞) := by
  have h_sum_zero : ∫⁻ ω, ∑' x : X, (if compatCount A ω x = q then 1 else 0) ∂(Measure.pi μ) ≤ ↑(a - 1) := by
    refine' le_trans ( MeasureTheory.lintegral_mono_ae _ ) _;
    use fun ω => ( a - 1 : ℕ );
    · convert! Ycard_ae_le μ A hN2 using 1;
    · simp +decide [  ];
  convert! h_sum_zero using 1;
  convert! ( lintegral_Ycard μ A hA ).symm using 1;
  congr! 1;
  ext x; rw [ ← measure_box μ A x ] ; congr; ext ω; simp +decide [ compatCount_eq_q_iff ] ;

/-
**Impurity summability** (`eq:esummable`).  On a countable exact system
satisfying (N1) and (N2), the minimal impurity `e(x) = min_i ρ_i(x)` is summable.
-/
lemma limit_impurity_summable (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (_ha : 1 ≤ a)
    {X : Type*} [Countable X]
    {Ω : Fin q → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ∀ i, X → Set (Ω i)) (hA : ∀ i x, MeasurableSet (A i x))
    (hN1 : ∀ x : X, ((q : ℝ≥0∞) - 1) ≤ ∑ i, μ i (A i x))
    (hN2 : ∀ S : Finset X, S.card = a → ∃ i, μ i (⋂ x ∈ S, A i x) = 0) :
    Summable (fun x : X => ⨅ i, (μ i (A i x)).toReal) := by
  convert! Summable.of_nonneg_of_le _ _ _;
  use fun x => 2 ^ ( q - 1 ) * ( ∏ i, ( μ i ( A i x ) |> ENNReal.toReal ) ) + if ( ⨅ i, ( μ i ( A i x ) |> ENNReal.toReal ) ) > 1 / 2 then 1 else 0;
  · exact fun x => Real.iInf_nonneg fun i => ENNReal.toReal_nonneg;
  · intro x;
    split_ifs;
    · refine' le_add_of_nonneg_of_le ( mul_nonneg ( pow_nonneg zero_le_two _ ) ( Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg ) ) _;
      exact le_trans ( ciInf_le ( Finite.bddBelow_range _ ) ⟨ 0, by linarith ⟩ ) ( ENNReal.toReal_le_of_le_ofReal zero_le_one <| by exact le_trans ( MeasureTheory.measure_mono <| Set.subset_univ _ ) <| by simp +decide );
    · -- Let $h x$ be a coordinate achieving the min, so $e x = (μ (h x) (A (h x) x)).toReal$.
      obtain ⟨i, hi⟩ : ∃ i, (μ i (A i x)).toReal = ⨅ i, (μ i (A i x)).toReal := by
        exact ( IsCompact.sInf_mem ( Set.finite_range _ |> Set.Finite.isCompact ) <| Set.nonempty_of_mem <| Set.mem_range_self <| ⟨ 0, by linarith ⟩ );
      -- By (N1), $\sum_{j \neq i} (1 - \rho_j) \leq e x$ where $\rho_j = (\mu j (A j x)).toReal$.
      have h_sum : ∑ j ∈ Finset.univ.erase i, (1 - (μ j (A j x)).toReal) ≤ (μ i (A i x)).toReal := by
        have h_sum : ∑ j ∈ Finset.univ.erase i, (μ j (A j x)).toReal ≥ (q - 1 : ℝ) - (μ i (A i x)).toReal := by
          have := hN1 x;
          rw [ ← ENNReal.toReal_sum ] at *;
          · rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ i ), add_comm ] at this;
            rw [ ge_iff_le, tsub_le_iff_right ];
            convert! ENNReal.toReal_mono _ this using 1;
            · rw [ ENNReal.toReal_sub_of_le ] <;> norm_num;
              linarith;
            · rw [ add_comm, ENNReal.toReal_add ] <;> norm_num;
            · exact ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ MeasureTheory.measure_lt_top _ _, ENNReal.sum_lt_top.mpr fun j hj => MeasureTheory.measure_lt_top _ _ ⟩ );
          · exact fun _ _ => MeasureTheory.measure_ne_top _ _;
        simp +zetaDelta only [sum_sub_distrib, sum_const, mem_univ, card_erase_of_mem, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sum_erase_eq_sub, tsub_le_iff_right, add_sub_cancel, ge_iff_le] at *;
        rw [ Nat.cast_pred ] <;> linarith;
      -- Since $\rho_j \geq 1 - e x$ for every $j \neq i$, we have $\prod_{j \neq i} \rho_j \geq (1 - e x)^{q-1}$.
      have h_prod : ∏ j ∈ Finset.univ.erase i, (μ j (A j x)).toReal ≥ (1 - (μ i (A i x)).toReal) ^ (q - 1) := by
        have h_prod : ∀ j ∈ Finset.univ.erase i, (μ j (A j x)).toReal ≥ 1 - (μ i (A i x)).toReal := by
          intro j hj;
          contrapose! h_sum;
          refine' lt_of_lt_of_le _ ( Finset.single_le_sum ( fun a _ => sub_nonneg.2 <| ENNReal.toReal_le_of_le_ofReal zero_le_one <| _ ) hj );
          · linarith;
          · exact le_trans ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide );
        refine' le_trans _ ( Finset.prod_le_prod _ h_prod ) <;> norm_num;
        exact fun _ _ => hi.symm ▸ le_trans ( ciInf_le ( Finite.bddBelow_range _ ) i ) ( ENNReal.toReal_le_of_le_ofReal zero_le_one ( by exact le_trans ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide ) ) );
      rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ i ) ];
      refine' le_trans _ ( le_add_of_nonneg_right _ );
      · rw [ ← hi ];
        refine' le_trans _ ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left h_prod <| ENNReal.toReal_nonneg ) <| by positivity );
        rw [ mul_left_comm, ← mul_pow ];
        exact le_mul_of_one_le_right ( ENNReal.toReal_nonneg ) ( one_le_pow₀ ( by linarith ) );
      · norm_num;
  · refine' Summable.add _ _;
    · have h_prod_summable : Summable (fun x => ∏ i, (μ i (A i x)).toReal) := by
        convert! ENNReal.summable_toReal _;
        rotate_left;
        use fun x => ∏ i, μ i ( A i x );
        · exact ne_of_lt ( lt_of_le_of_lt ( limit_productsum_bound q a μ A hA hN2 ) ( ENNReal.coe_lt_top ) );
        · rw [ ENNReal.toReal_prod ];
      exact h_prod_summable.mul_left _;
    · have h_finite : Set.Finite {x : X | (⨅ i, (μ i (A i x)).toReal) > 1 / 2} := by
        have h_finite : Set.Finite {x : X | (1 / 2 : ℝ) ^ q ≤ ∏ i, (μ i (A i x)).toReal} := by
          have h_finite : Summable (fun x : X => ∏ i, (μ i (A i x)).toReal) := by
            convert! ENNReal.summable_toReal _;
            rotate_left;
            use fun x => ∏ i, μ i ( A i x );
            · exact ne_of_lt ( lt_of_le_of_lt ( limit_productsum_bound q a μ A hA hN2 ) ( ENNReal.coe_lt_top ) );
            · rw [ ENNReal.toReal_prod ];
          convert! h_finite.tendsto_cofinite_zero.eventually ( gt_mem_nhds <| show 0 < ( 1 / 2 : ℝ ) ^ q by positivity ) using 1 ; aesop;
        refine' h_finite.subset fun x hx => _;
        refine' le_trans _ ( Finset.prod_le_prod _ fun i _ => show ( μ i ( A i x ) |> ENNReal.toReal ) ≥ 1 / 2 from _ ) <;> norm_num;
        · rw [ ← inv_pow, inv_eq_one_div ];
        · exact le_trans hx.out.le ( ciInf_le ( Finite.bddBelow_range _ ) _ );
      refine' summable_of_ne_finset_zero _;
      exacts [ h_finite.toFinset, fun x hx => if_neg <| by simpa using! hx ]

/-- **Coordinate relabelling pushforward.**  Given a relabelling map `s : ℕ → ℕ`
and a threshold `t`, there is a pushforward system `ρ'` on `ℕ → Bool` whose
cylinder masses over labels `< t` reproduce the original masses at `s`-images,
and whose coordinates `≥ t` are dead. -/
lemma exists_pushforward_relabel (q t : ℕ) (s : ℕ → ℕ)
    (ρ : Fin q → ProbabilityMeasure (ℕ → Bool)) :
    ∃ ρ' : Fin q → ProbabilityMeasure (ℕ → Bool),
      (∀ (i : Fin q) (S : Finset ℕ), (∀ x ∈ S, x < t) →
        cdens q ρ' i S = cdens q ρ i (S.image s)) ∧
      (∀ (i : Fin q) (ℓ : ℕ), t ≤ ℓ → cdens q ρ' i {ℓ} = 0) := by
  classical
  set F : (ℕ → Bool) → (ℕ → Bool) := fun σ x => if x < t then σ (s x) else false with hF
  have hFmeas : Measurable F := by
    apply measurable_pi_lambda
    intro x
    by_cases hx : x < t
    · simp only [hF, hx, if_true]; exact measurable_pi_apply (s x)
    · simp only [hF, hx, if_false]; exact measurable_const
  have hprob : ∀ i, IsProbabilityMeasure ((ρ i).toMeasure.map F) := fun i =>
    Measure.isProbabilityMeasure_map hFmeas.aemeasurable
  refine ⟨fun i => ⟨(ρ i).toMeasure.map F, hprob i⟩, ?_, ?_⟩
  · intro i S hS
    unfold cdens
    have hmeas : MeasurableSet {σ : ℕ → Bool | ∀ x ∈ S, σ x = true} := by
      have hrw : {σ : ℕ → Bool | ∀ x ∈ S, σ x = true}
          = ⋂ x ∈ S, {σ : ℕ → Bool | σ x = true} := by ext σ; simp
      rw [hrw]
      exact MeasurableSet.biInter S.countable_toSet (fun x _ =>
        measurableSet_eq_fun (measurable_pi_apply x) measurable_const)
    congr 1
    show ((ρ i).toMeasure.map F) {σ | ∀ x ∈ S, σ x = true}
        = (ρ i).toMeasure {σ | ∀ x ∈ S.image s, σ x = true}
    rw [Measure.map_apply hFmeas hmeas]
    congr 1
    ext σ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hF, Finset.mem_image]
    constructor
    · rintro h y ⟨x, hxS, rfl⟩
      have hxt := hS x hxS
      have := h x hxS
      rwa [if_pos hxt] at this
    · intro h x hxS
      rw [if_pos (hS x hxS)]
      exact h (s x) ⟨x, hxS, rfl⟩
  · intro i ℓ hℓ
    unfold cdens
    have hset : {σ : ℕ → Bool | ∀ x ∈ ({ℓ} : Finset ℕ), σ x = true} = {σ | σ ℓ = true} := by
      ext σ; simp
    have hmeas : MeasurableSet {σ : ℕ → Bool | ∀ x ∈ ({ℓ} : Finset ℕ), σ x = true} := by
      rw [hset]; exact measurableSet_eq_fun (measurable_pi_apply ℓ) measurable_const
    have hpre : F ⁻¹' {σ : ℕ → Bool | ∀ x ∈ ({ℓ} : Finset ℕ), σ x = true} = ∅ := by
      ext σ
      simp only [Set.mem_preimage, hset, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      rw [hF] at h
      simp only [if_neg (by omega : ¬ ℓ < t)] at h
      exact Bool.false_ne_true h
    show (((ρ i).toMeasure.map F) {σ | ∀ x ∈ ({ℓ} : Finset ℕ), σ x = true}).toReal = 0
    rw [Measure.map_apply hFmeas hmeas, hpre, measure_empty, ENNReal.toReal_zero]

/-
`cimp` is nonnegative.
-/
lemma cimp_nonneg (q : ℕ) (ρ : Fin q → ProbabilityMeasure (ℕ → Bool)) (x : ℕ) :
    0 ≤ cimp q ρ x := by
  exact Real.iInf_nonneg fun i => cdens_nonneg q ρ i { x }

/-
`cimp` is a lower bound for every coordinate density.
-/
lemma cimp_le (q : ℕ) (ρ : Fin q → ProbabilityMeasure (ℕ → Bool)) (i : Fin q)
    (x : ℕ) : cimp q ρ x ≤ cdens q ρ i {x} := by
  exact ciInf_le ( Finite.bddBelow_range fun i => cdens q ρ i { x } ) i

/-
The minimal impurity is attained at some coordinate (a "home").
-/
lemma exists_cimp_eq (q : ℕ) (hq : 1 ≤ q)
    (ρ : Fin q → ProbabilityMeasure (ℕ → Bool)) (x : ℕ) :
    ∃ i, cimp q ρ x = cdens q ρ i {x} := by
  unfold cimp;
  convert! Finset.exists_min_image Finset.univ ( fun i => cdens q ρ i { x } ) ⟨ ⟨ 0, hq ⟩, Finset.mem_univ _ ⟩ using 1;
  ext i; simp +decide only [mem_univ, forall_const, true_and] ;
  fconstructor;
  · exact fun h j => le_trans ( h.1 ) ( ciInf_le ( Finite.bddBelow_range fun i => cdens q ρ i { x } ) j );
  · exact fun h => ⟨ le_csInf ⟨ _, Set.mem_range_self i ⟩ <| Set.forall_mem_range.2 h, csInf_le ⟨ 0, Set.forall_mem_range.2 fun _ => cdens_nonneg q ρ _ _ ⟩ <| Set.mem_range_self i ⟩

/-
**Union bound for dropped vertices.**  The cylinder mass over `P` exceeds the
mass over `P ∪ Q` by at most the total complement mass of the dropped coordinates.
-/
lemma cdens_inter_drop (q : ℕ) (ρ : Fin q → ProbabilityMeasure (ℕ → Bool))
    (i : Fin q) (P Q : Finset ℕ) :
    cdens q ρ i P ≤ cdens q ρ i (P ∪ Q) + ∑ y ∈ Q, (1 - cdens q ρ i {y}) := by
  unfold cdens;
  have h_subset : (ρ i).toMeasure {σ : ℕ → Bool | ∀ x ∈ P, σ x = true} ≤ (ρ i).toMeasure {σ : ℕ → Bool | ∀ x ∈ P ∪ Q, σ x = true} + ∑ y ∈ Q, (ρ i).toMeasure {σ : ℕ → Bool | σ y = false} := by
    refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ ) |> le_trans <| add_le_add ( le_refl _ ) ( MeasureTheory.measure_biUnion_finset_le _ _ );
    intro σ hσ; by_cases h : ∃ x ∈ Q, σ x = false <;> aesop;
  convert! ENNReal.toReal_mono _ h_subset using 1;
  · rw [ ENNReal.toReal_add, ENNReal.toReal_sum ];
    · congr! 2;
      rw [ show { σ : ℕ → Bool | σ _ = false } = ( Set.univ \ { σ : ℕ → Bool | σ _ = true } ) by ext; aesop, MeasureTheory.measure_diff ] <;> norm_num;
      · rw [ ENNReal.toReal_sub_of_le ] <;> norm_num;
        exact le_trans ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by norm_num );
      · exact measurableSet_eq_fun ( measurable_pi_apply _ ) measurable_const |> MeasurableSet.nullMeasurableSet;
    · exact fun x hx => MeasureTheory.measure_ne_top _ _;
    · exact MeasureTheory.measure_ne_top _ _;
    · simp +zetaDelta at *;
  · simp +zetaDelta at *

/-
**Home complement bound.**  If `i₀` is a home of `x` and `j ≠ i₀`, then the
complement mass of coordinate `j` at `x` is at most `e(x) + ε`.
-/
lemma home_complement_bound (q : ℕ) (ρ : Fin q → ProbabilityMeasure (ℕ → Bool))
    (x : ℕ) (ε : ℝ) (i₀ j : Fin q)
    (hA1 : (q : ℝ) - 1 - ε ≤ ∑ i, cdens q ρ i {x})
    (hhome : cimp q ρ x = cdens q ρ i₀ {x}) (hj : j ≠ i₀) :
    1 - cdens q ρ j {x} ≤ cimp q ρ x + ε := by
  rcases q with ( _ | q ) <;> simp_all +decide only [tsub_le_iff_right];
  · fin_cases i₀;
  · have h_sum : ∑ i ∈ Finset.univ.erase i₀, (1 - cdens (q + 1) ρ i {x}) ≤ ε + cdens (q + 1) ρ i₀ {x} := by
      simp_all +decide [ Finset.sum_sub_distrib ];
      linarith;
    linarith [ Finset.single_le_sum ( fun i _ => sub_nonneg.mpr ( cdens_le_one ( q + 1 ) ρ i { x } ) ) ( Finset.mem_erase_of_ne_of_mem hj ( Finset.mem_univ j ) ) ]

/-
**Ultrafilter dichotomy on `ℕ`.**  Along an ultrafilter, an integer sequence
either recurs to a fixed value or tends to infinity.
-/
lemma ultrafilter_nat_dichotomy (U : Ultrafilter ℕ) (f : ℕ → ℕ) :
    (∃ v, {n | f n = v} ∈ U) ∨ Tendsto f (↑U) atTop := by
  by_contra! h;
  obtain ⟨M, hM⟩ : ∃ M, {n | f n < M} ∈ U := by
    simp_all +decide [ Filter.tendsto_atTop ];
    exact ⟨ h.2.choose, h.2.choose_spec ⟩;
  -- Since ${n | f n < M} \in U$, we can partition it into finitely many sets ${n | f n = v}$ for $v < M$.
  have h_partition : {n | f n < M} = ⋃ v ∈ Finset.range M, {n | f n = v} := by
    ext n; simp [Finset.mem_range];
  have h_finite_union : ∀ {S : Finset ℕ}, (⋃ v ∈ S, {n | f n = v}) ∈ U → ∃ v ∈ S, {n | f n = v} ∈ U := by
    intros S hS; induction S using Finset.induction <;> simp_all +decide [  ] ;
  exact absurd ( h_finite_union ( h_partition ▸ hM ) ) ( by aesop )

/-
**Moving tail** (`lem:orderedimpurity`, `eq:movingtail`).  Along the
ultrafilter, the impurity of an escaping (label → ∞) in-range vertex tends to `0`.
-/
lemma moving_tail (q : ℕ) (ρ : ℕ → Fin q → ProbabilityMeasure (ℕ → Bool))
    (U : Ultrafilter ℕ) (t : ℕ → ℕ) (e_lim : ℕ → ℝ) (hsum : Summable e_lim)
    (hconv : ∀ ℓ, Tendsto (fun n => cimp q (ρ n) ℓ) (↑U) (𝓝 (e_lim ℓ)))
    (hmono : ∀ n ℓ₁ ℓ₂, ℓ₁ ≤ ℓ₂ → ℓ₂ < t n → cimp q (ρ n) ℓ₂ ≤ cimp q (ρ n) ℓ₁)
    (y : ℕ → ℕ) (hyesc : Tendsto y (↑U) atTop)
    (hyrange : ∀ᶠ n in (↑U : Filter ℕ), y n < t n) :
    Tendsto (fun n => cimp q (ρ n) (y n)) (↑U) (𝓝 0) := by
  rw [ Metric.tendsto_nhds ] at *;
  intro ε hε
  obtain ⟨L, hL⟩ : ∃ L, e_lim L < ε := by
    exact ( hsum.tendsto_atTop_zero.eventually ( gt_mem_nhds hε ) ) |> fun h => h.exists;
  filter_upwards [ hyesc.eventually_ge_atTop L, hyrange, hconv L |> fun h => h.eventually ( gt_mem_nhds hL ) ] with n hn₁ hn₂ hn₃ using by simpa [ abs_of_nonneg ( cimp_nonneg q ( ρ n ) _ ) ] using! lt_of_le_of_lt ( hmono n L ( y n ) hn₁ hn₂ ) hn₃;

/-
**Impurity-decreasing enumeration.**  The vertices of a finite ground set `V`
can be enumerated by `[0, |V|)` in order of nonincreasing impurity.
-/
lemma exists_impurity_enum (q : ℕ) (V : Finset ℕ)
    (ρ : Fin q → ProbabilityMeasure (ℕ → Bool)) :
    ∃ s : ℕ → ℕ,
      Set.InjOn s (Set.Iio V.card) ∧
      (∀ ℓ, ℓ < V.card → s ℓ ∈ V) ∧
      (∀ x ∈ V, ∃ ℓ, ℓ < V.card ∧ s ℓ = x) ∧
      (∀ ℓ₁ ℓ₂, ℓ₁ ≤ ℓ₂ → ℓ₂ < V.card →
        cimp q ρ (s ℓ₂) ≤ cimp q ρ (s ℓ₁)) := by
  obtain ⟨l, hl⟩ : ∃ l : List ℕ, l.length = V.card ∧ (∀ x ∈ l, x ∈ V) ∧ (∀ x ∈ V, x ∈ l) ∧ List.Pairwise (fun x y => cimp q ρ y ≤ cimp q ρ x) l := by
    obtain ⟨l, hl⟩ : ∃ l : List ℕ, l.Perm V.toList ∧ List.Pairwise (fun x y => cimp q ρ y ≤ cimp q ρ x) l := by
      have h_merge_sort : ∀ (l : List ℕ) (cmp : ℕ → ℕ → Bool), (∀ x y, cmp x y = true ↔ cimp q ρ y ≤ cimp q ρ x) → List.Pairwise (fun x y => cimp q ρ y ≤ cimp q ρ x) (List.mergeSort l (fun x y => cmp x y)) := by
        intros l cmp hcmp
        have h_merge_sort : List.Pairwise (fun x y => cmp x y = true) (List.mergeSort l (fun x y => cmp x y)) := by
          apply_rules [ List.pairwise_mergeSort ];
          · grind;
          · grind;
        exact h_merge_sort.imp fun x => by aesop;
      use List.mergeSort V.toList (fun x y => decide (cimp q ρ y ≤ cimp q ρ x));
      exact ⟨ List.mergeSort_perm _ _, h_merge_sort _ _ fun x y => by simp +decide ⟩;
    exact ⟨ l, by simpa using! hl.1.length_eq, fun x hx => by simpa using! hl.1.subset hx, fun x hx => by simpa using! hl.1.symm.subset <| by simpa using! hx, hl.2 ⟩;
  refine' ⟨ fun ℓ => l[ℓ]?.getD 0, _, _, _, _ ⟩ <;> simp_all +decide [ Set.InjOn ];
  · have h_unique : List.Nodup l := by
      have h_card : l.toFinset.card = V.card := by
        exact congr_arg Finset.card ( Finset.ext fun x => by aesop );
      rw [ List.nodup_iff_injective_get ];
      intro i j hij; have := Finset.card_image_iff.mp ( by aesop : Finset.card ( Finset.image l.get Finset.univ ) = Finset.card Finset.univ ) ; aesop;
    exact fun i hi j hj hij => by have := List.nodup_iff_injective_get.mp h_unique hij; aesop;
  · intro x hx; have := List.mem_iff_getElem.mp ( hl.2.2.1 x hx ) ; aesop;
  · intro ℓ₁ ℓ₂ h₁ h₂; have := List.pairwise_iff_get.mp hl.2.2.2; simp_all +decide [  ] ;
    by_cases h₃ : ℓ₁ < l.length <;> by_cases h₄ : ℓ₂ < l.length <;> simp_all +decide [  ];
    · cases lt_or_eq_of_le h₁ <;> [ exact this ⟨ ℓ₁, by linarith ⟩ ⟨ ℓ₂, by linarith ⟩ ‹_› ; aesop ];
    · linarith

/-
**Almost-sure canonical cofiniteness.**  On a countable exact system, for
almost every sampled outcome the set of "noncanonical" vertices (those that are
in their home event or miss some non-home coordinate) is finite.
-/
lemma exists_position_dichotomy (U : Ultrafilter ℕ) (k : ℕ) (e : ℕ → Fin k → ℕ) :
    ∃ (R : Finset (Fin k)) (v : Fin k → ℕ),
      (∀ p ∈ R, {n | e n p = v p} ∈ U) ∧
      (∀ p, p ∉ R → Tendsto (fun n => e n p) (↑U) atTop) := by
  classical
  refine ⟨Finset.univ.filter (fun p => ∃ w, {n | e n p = w} ∈ U),
    fun p => if h : ∃ w, {n | e n p = w} ∈ U then h.choose else 0, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simpa only [dif_pos hp] using! hp.choose_spec
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases ultrafilter_nat_dichotomy U (fun n => e n p) with h | h
    · exact absurd h hp
    · exact h

lemma ae_noncanonical_finite (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    {X : Type*} [Countable X]
    {Ω : Fin q → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ∀ i, X → Set (Ω i)) (hA : ∀ i x, MeasurableSet (A i x))
    (hN1 : ∀ x : X, ((q : ℝ≥0∞) - 1) ≤ ∑ i, μ i (A i x))
    (hN2 : ∀ S : Finset X, S.card = a → ∃ i, μ i (⋂ x ∈ S, A i x) = 0)
    (h : X → Fin q) (hhome : ∀ x i, μ (h x) (A (h x) x) ≤ μ i (A i x)) :
    ∀ᵐ ω ∂(Measure.pi μ),
      {x : X | ω (h x) ∈ A (h x) x ∨ ∃ j, j ≠ h x ∧ ω j ∉ A j x}.Finite := by
  have h_summable : Summable (fun x : X => (μ (h x) (A (h x) x)).toReal) := by
    convert! limit_impurity_summable q hq a ha μ A hA hN1 hN2 using 1;
    ext x;
    refine' le_antisymm _ _;
    · refine' le_csInf _ _;
      · exact ⟨ _, ⟨ h x, rfl ⟩ ⟩;
      · rintro _ ⟨ i, rfl ⟩ ; exact ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( hhome x i ) ;
    · exact ciInf_le ( Finite.bddBelow_range _ ) _;
  have h_summable_measure : ∑' x, (Measure.pi μ {ω | ω (h x) ∈ A (h x) x ∨ ∃ j, j ≠ h x ∧ ω j ∉ A j x}) ≠ ⊤ := by
    have h_summable_measure : ∀ x, (Measure.pi μ {ω | ω (h x) ∈ A (h x) x ∨ ∃ j, j ≠ h x ∧ ω j ∉ A j x}) ≤ 2 * ENNReal.ofReal ((μ (h x) (A (h x) x)).toReal) := by
      intro x
      have h_bound : (Measure.pi μ) {ω : ∀ i, Ω i | ω (h x) ∈ A (h x) x ∨ ∃ j, j ≠ h x ∧ ω j ∉ A j x} ≤ (μ (h x)) (A (h x) x) + ∑ j ∈ Finset.univ.erase (h x), (1 - (μ j) (A j x)) := by
        refine' le_trans ( MeasureTheory.measure_mono _ ) _;
        exact { ω : ∀ i, Ω i | ω ( h x ) ∈ A ( h x ) x } ∪ ⋃ j ∈ Finset.univ.erase ( h x ), { ω : ∀ i, Ω i | ω j ∉ A j x };
        · simp +decide [ Set.subset_def ];
        · refine' le_trans ( MeasureTheory.measure_union_le _ _ ) ( add_le_add _ _ );
          · convert! pi_marginal μ ( h x ) ( A ( h x ) x ) ( hA ( h x ) x ) |> le_of_eq using 1;
          · refine' le_trans ( MeasureTheory.measure_biUnion_finset_le _ _ ) _;
            refine' Finset.sum_le_sum fun i _ => _;
            have h_measure_compl : (Measure.pi μ) {ω : ∀ i, Ω i | ω i ∉ A i x} = (μ i) (A i x)ᶜ := by
              convert! pi_marginal μ i ( A i x ) ᶜ ( hA i x |> MeasurableSet.compl ) using 1;
            rw [ h_measure_compl, MeasureTheory.measure_compl ] <;> aesop;
      have h_bound : ∑ j ∈ Finset.univ.erase (h x), (1 - (μ j) (A j x)) ≤ ENNReal.ofReal ((μ (h x) (A (h x) x)).toReal) := by
        have h_bound : ∑ j ∈ Finset.univ.erase (h x), (1 - (μ j) (A j x)) ≤ (q - 1 : ENNReal) - ∑ j ∈ Finset.univ.erase (h x), (μ j) (A j x) := by
          rw [ ENNReal.sub_eq_of_eq_add ];
          · simp +zetaDelta at *;
          · rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl fun _ _ => tsub_add_cancel_of_le <| MeasureTheory.measure_mono ( Set.subset_univ _ ) |> le_trans <| by simp +decide ] ; simp +decide [ Finset.card_erase_of_mem <| Finset.mem_univ <| h x ];
        refine' le_trans h_bound _;
        simp_all +decide only [ne_eq, measure_ne_top, not_false_eq_true, ENNReal.ofReal_toReal, tsub_le_iff_right];
        convert! hN1 x using 1 ; ring;
      refine' le_trans ‹_› _;
      convert! add_le_add_left h_bound ( μ ( h x ) ( A ( h x ) x ) ) using 1 ; ring;
      rw [ two_mul, ENNReal.ofReal_toReal ];
      exact MeasureTheory.measure_ne_top _ _;
    refine' ne_of_lt ( lt_of_le_of_lt ( ENNReal.tsum_le_tsum h_summable_measure ) _ );
    rw [ ENNReal.tsum_mul_left ];
    rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num [ h_summable ];
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top ( ENNReal.ofReal_lt_top );
  exact ae_finite_setOf_mem h_summable_measure

/-
**Good canonical outcome.**  As `exists_good_outcome`, but the chosen outcome
is additionally canonical-cofinite for a given home function.
-/
set_option maxHeartbeats 1000000 in
lemma exists_good_canonical_outcome (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    {X : Type*} [Countable X]
    {Ω : Fin q → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ∀ i, X → Set (Ω i)) (hA : ∀ i x, MeasurableSet (A i x))
    (hN1 : ∀ x : X, (q : ℝ≥0∞) - 1 ≤ ∑ i, μ i (A i x))
    (hN2 : ∀ S : Finset X, S.card = a → ∃ i, μ i (⋂ x ∈ S, A i x) = 0)
    {ι : Type*} [Countable ι] (E : ι → Finset X) (j : ι → Fin q)
    (hnull : ∀ e, μ (j e) (⋂ x ∈ E e, A (j e) x) = 0)
    (hh : X → Fin q) (hhome : ∀ x i, μ (hh x) (A (hh x) x) ≤ μ i (A i x)) :
    ∃ ω : ∀ i, Ω i,
      {x : X | compatCount A ω x ≤ q - 2}.Finite ∧
      {x : X | compatCount A ω x ≤ q - 2}.ncard ≤ a - 1 ∧
      (∀ e, ∃ x ∈ E e, ω (j e) ∉ A (j e) x) ∧
      {x : X | ω (hh x) ∈ A (hh x) x ∨ ∃ j', j' ≠ hh x ∧ ω j' ∉ A j' x}.Finite := by
  have h_pos : 0 < (Measure.pi μ) {ω | Ucard A ω ≤ ((a : ℕ) - 1 : ℕ)} := by
    have h_nonempty : (Measure.pi μ) {ω | Ucard A ω ≥ a} ≤ (a - 1 : ℝ≥0∞) / a := by
      have := @MeasureTheory.meas_ge_le_lintegral_div;
      refine' le_trans ( this _ _ _ ) _;
      · refine' Measurable.aemeasurable _;
        refine' Measurable.ennreal_tsum _;
        intro x;
        exact Measurable.ite ( measurableSet_le ( measurable_compatCount A x hA ) measurable_const ) measurable_const measurable_const;
      · positivity;
      · exact ENNReal.natCast_ne_top _;
      · gcongr;
        convert! Erdos550.lintegral_Ucard_le μ A hq hA hN1 hN2 using 1;
        cases a <;> aesop;
    have h_nonempty : (Measure.pi μ) {ω | Ucard A ω ≤ (a - 1 : ℕ)} ≥ 1 - (a - 1 : ℝ≥0∞) / a := by
      refine' le_trans ( tsub_le_tsub_left h_nonempty _ ) _;
      rw [ tsub_le_iff_right ];
      refine' le_trans _ ( MeasureTheory.measure_union_le _ _ );
      refine' le_trans _ ( MeasureTheory.measure_mono _ );
      rotate_left;
      exact Set.univ;
      · grind +suggestions;
      · simp +decide [  ];
    refine' lt_of_lt_of_le _ h_nonempty;
    rcases a with ( _ | _ | a ) <;> norm_num at *;
    rw [ ENNReal.div_lt_iff ] <;> norm_cast <;> norm_num;
  have h_inter_pos : 0 < (Measure.pi μ) ({ω | Ucard A ω ≤ ((a : ℕ) - 1 : ℕ)} ∩ {ω | ∀ e, ∃ x ∈ E e, ω (j e) ∉ A (j e) x} ∩ {ω | {x | ω (hh x) ∈ A (hh x) x ∨ ∃ j', j' ≠ hh x ∧ ω j' ∉ A j' x}.Finite}) := by
    have h_inter_pos : (Measure.pi μ) ({ω | Ucard A ω ≤ ((a : ℕ) - 1 : ℕ)} \ ({ω | ∀ e, ∃ x ∈ E e, ω (j e) ∉ A (j e) x} ∩ {ω | {x | ω (hh x) ∈ A (hh x) x ∨ ∃ j', j' ≠ hh x ∧ ω j' ∉ A j' x}.Finite})) = 0 := by
      refine' MeasureTheory.measure_mono_null _ _;
      exact { ω | ¬∀ e, ∃ x ∈ E e, ω ( j e ) ∉ A ( j e ) x } ∪ { ω | ¬ { x | ω ( hh x ) ∈ A ( hh x ) x ∨ ∃ j', j' ≠ hh x ∧ ω j' ∉ A j' x }.Finite };
      · grind;
      · refine' MeasureTheory.measure_union_null _ _;
        · convert! Erdos550.ae_blocking μ A E j hA hnull using 1;
        · exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) ( ae_noncanonical_finite q hq a ha μ A hA hN1 hN2 hh hhome );
    simp_all +decide only [ENNReal.natCast_sub, Nat.cast_one, ne_eq, gt_iff_lt];
    rw [ MeasureTheory.measure_congr ];
    convert! h_pos using 1;
    rw [ MeasureTheory.ae_eq_set ];
    simp_all +decide [ Set.diff_eq_empty.mpr ];
  obtain ⟨ ω, hω ⟩ := MeasureTheory.nonempty_of_measure_ne_zero h_inter_pos.ne';
  refine' ⟨ ω, _, _, hω.1.2, hω.2 ⟩;
  · have := hω.1.1;
    contrapose! this;
    simp +decide only [ENNReal.natCast_sub, Nat.cast_one, Set.mem_ofPred_eq, not_le];
    refine' lt_of_lt_of_le _ ( ENNReal.tsum_le_tsum fun x => show ( if compatCount A ω x ≤ q - 2 then 1 else 0 : ENNReal ) ≥ if x ∈ { x | compatCount A ω x ≤ q - 2 } then 1 else 0 from _ );
    · rw [ ENNReal.tsum_eq_iSup_sum ];
      refine' lt_of_lt_of_le _ ( le_ciSup _ ( this.exists_subset_card_eq ( a + 1 ) |> Classical.choose ) );
      · rw [ Finset.sum_congr rfl fun x hx => if_pos <| Classical.choose_spec ( this.exists_subset_card_eq ( a + 1 ) ) |>.1 hx ] ; simp +decide [ Classical.choose_spec ( this.exists_subset_card_eq ( a + 1 ) ) |>.2 ];
        exact_mod_cast Nat.lt_succ_of_le ( Nat.pred_le _ );
      · simp +decide [  ];
    · simp +decide [ Set.mem_setOf_eq ];
  · by_cases h : Set.Finite { x : X | compatCount A ω x ≤ q - 2 } <;> simp_all +decide [ Set.ncard_def ];
    have h_card : Ucard A ω = ∑ x ∈ h.toFinset, if compatCount A ω x ≤ q - 2 then 1 else 0 := by
      rw [ Ucard ];
      rw [ tsum_eq_sum ];
      simp +contextual [ h.mem_toFinset ];
    simp_all +decide [  ];
    convert! hω.1.1 using 1;
    rw [ Set.Finite.encard_eq_coe_toFinset_card h ] ; norm_cast;
    rw [ Finset.filter_true_of_mem fun x hx => by simpa using! h.mem_toFinset.mp hx ] ; norm_cast

/-- **Rounding with home property** (Theorem 4.1, full statement).  As
`exact_rounding`, but additionally the colouring agrees with a given home
(minimizing) coordinate for all but finitely many vertices. -/
theorem exact_rounding_home
    (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    (X : Type*) [Countable X]
    (Ω : Fin q → Type*) [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ∀ i, X → Set (Ω i)) (hA : ∀ i x, MeasurableSet (A i x))
    (D : Fin q → Set (Finset X)) (_hDne : ∀ i, ∀ E ∈ D i, E.Nonempty)
    (hN1 : ∀ x : X, ((q : ℝ≥0∞) - 1) ≤ ∑ i, μ i (A i x))
    (hN2 : ∀ S : Finset X, S.card = a → ∃ i, μ i (⋂ x ∈ S, A i x) = 0)
    (hN3 : ∀ i : Fin q, ∀ E ∈ D i, ∃ j, j ≠ i ∧ μ j (⋂ x ∈ E, A j x) = 0)
    (h : X → Fin q) (hhome : ∀ x i, μ (h x) (A (h x) x) ≤ μ i (A i x)) :
    ∃ (Z : Finset X) (φ : X → Fin q), Z.card ≤ a - 1 ∧
      (∀ i : Fin q, ∀ E ∈ D i, ¬ (∀ x ∈ E, x ∉ Z ∧ φ x = i)) ∧
      {x : X | φ x ≠ h x}.Finite := by
  classical
  obtain ⟨ω, hfin, hncard, hblock, hcanon⟩ :=
    exists_good_canonical_outcome q hq a ha μ A hA hN1 hN2
      (ι := Σ i : Fin q, {E : Finset X // E ∈ D i})
      (fun e => e.2.1) (fun e => Classical.choose (hN3 e.1 e.2.1 e.2.2))
      (fun e => (Classical.choose_spec (hN3 e.1 e.2.1 e.2.2)).2) h hhome
  refine ⟨hfin.toFinset,
    fun x => if hx : ∃ k, ω k ∉ A k x then Classical.choose hx else ⟨0, by omega⟩,
    ?_, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact hncard
  · intro i E hE hmono
    set e : (Σ i : Fin q, {E : Finset X // E ∈ D i}) := ⟨i, ⟨E, hE⟩⟩ with he
    obtain ⟨x₀, hx₀E, hmiss⟩ := hblock e
    obtain ⟨hx₀Z, hφ⟩ := hmono x₀ hx₀E
    have hge : q - 1 ≤ compatCount A ω x₀ := by
      rw [Set.Finite.mem_toFinset] at hx₀Z
      simp only [Set.mem_setOf_eq] at hx₀Z
      omega
    have hex : ∃ k, ω k ∉ A k x₀ := ⟨Classical.choose (hN3 e.1 e.2.1 e.2.2), hmiss⟩
    have hφx : Classical.choose hex = i := by
      have : (if hx : ∃ k, ω k ∉ A k x₀ then Classical.choose hx else ⟨0, by omega⟩) = i := hφ
      rwa [dif_pos hex] at this
    have hmissi : ω i ∉ A i x₀ := by
      have hspec := Classical.choose_spec hex
      rwa [hφx] at hspec
    have hjcol_ne : Classical.choose (hN3 e.1 e.2.1 e.2.2) ≠ i :=
      (Classical.choose_spec (hN3 e.1 e.2.1 e.2.2)).1
    exact hjcol_ne (missing_unique A ω x₀ hge hmiss hmissi)
  · -- home property
    refine hcanon.subset ?_
    intro x hx
    rw [Set.mem_setOf_eq] at hx ⊢
    by_contra hcan
    push_neg at hcan
    obtain ⟨hcan1, hcan2⟩ := hcan
    -- `x` is canonical: only `h x` is missing
    have hcan1' : ω (h x) ∉ A (h x) x := hcan1
    have hcan2' : ∀ j', j' ≠ h x → ω j' ∈ A j' x := hcan2
    have hex : ∃ k, ω k ∉ A k x := ⟨h x, hcan1'⟩
    have hfilter : (Finset.univ.filter (fun i => ω i ∈ A i x)) = Finset.univ.erase (h x) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · intro hi; refine ⟨?_, trivial⟩; rintro rfl; exact hcan1' hi
      · intro hi; exact hcan2' i hi.1
    have hge : q - 1 ≤ compatCount A ω x := by
      rw [compatCount, hfilter, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
    have hchoose : Classical.choose hex = h x :=
      missing_unique A ω x hge (Classical.choose_spec hex) hcan1'
    have hφx : (if hx : ∃ k, ω k ∉ A k x then Classical.choose hx else ⟨0, by omega⟩) = h x := by
      rw [dif_pos hex]; exact hchoose
    exact hx hφx

/-
Along an ultrafilter, a sequence valued in a finite type recurs to a fixed
value.
-/
lemma exists_ultrafilter_eventually_eq {α : Type*} [Finite α] [Nonempty α]
    (U : Ultrafilter ℕ) (g : ℕ → α) : ∃ c, {n | g n = c} ∈ U := by
  by_contra! h_contra;
  obtain ⟨c, hc⟩ : ∃ c : Finset α, c.Nonempty ∧ (∀ x ∈ c, {n | g n = x} ∉ U) ∧ (⋃ x ∈ c, {n | g n = x}) ∈ U := by
    obtain ⟨c, hc⟩ : ∃ c : Finset α, (⋃ x ∈ c, {n | g n = x}) ∈ U := by
      obtain ⟨c, hc⟩ : ∃ c : Finset α, (⋃ x ∈ c, {n | g n = x}) = Set.univ := by
        exact ⟨ Set.Finite.toFinset ( Set.toFinite ( Set.range g ) ), by ext n; simp +decide ⟩;
      exact ⟨ c, hc.symm ▸ Filter.univ_mem ⟩;
    exact ⟨ c, Finset.nonempty_of_ne_empty ( by rintro rfl; simp +decide at hc ), fun x hx => h_contra x, hc ⟩;
  induction' hc.1 using Finset.Nonempty.cons_induction with x hx ih;
  · aesop;
  · simp_all +decide [ Finset.mem_cons ]

/-
The minimal impurity `cimp` is continuous under weak convergence (a finite
infimum of continuous cylinder masses).
-/
lemma cimp_tendsto {q : ℕ} (ρ : ℕ → Fin q → ProbabilityMeasure (ℕ → Bool))
    (L : Fin q → ProbabilityMeasure (ℕ → Bool)) (U : Ultrafilter ℕ)
    (hcd : ∀ (i : Fin q) (S : Finset ℕ),
      Tendsto (fun n => cdens q (ρ n) i S) (↑U) (𝓝 (cdens q L i S)))
    (ℓ : ℕ) :
    Tendsto (fun n => cimp q (ρ n) ℓ) (↑U) (𝓝 (cimp q L ℓ)) := by
  rcases q with ( _ | q ) <;> simp_all +decide [ cimp ];
  have h_cont_inf : Continuous (fun v : Fin (q + 1) → ℝ => ⨅ i, v i) := by
    have : ∀ v : Fin (q + 1) → ℝ, ⨅ i, v i = Finset.min' (Finset.univ.image v) (by
    exact ⟨ v 0, Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ⟩) := by
      all_goals generalize_proofs at *;
      intro v; rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
      · exact fun i => Finset.min'_le _ _ <| Finset.mem_image_of_mem _ <| Finset.mem_univ _;
      · exact fun w hw => by rcases Finset.mem_image.mp ( Finset.min'_mem ( Finset.image v Finset.univ ) ( by solve_by_elim ) ) with ⟨ i, _, hi ⟩ ; exact ⟨ i, hi ▸ hw ⟩ ;
    simp +decide [ this, Finset.min' ];
    refine' continuous_iff_continuousAt.mpr _;
    intro v; exact (by
    refine' tendsto_order.2 ⟨ _, _ ⟩ <;> intro x hx <;> simp_all +decide only [inf'_lt_iff, mem_univ, true_and, lt_inf'_iff, forall_const, eventually_all];
    · exact fun i => IsOpen.mem_nhds ( isOpen_lt continuous_const <| continuous_apply i ) <| hx i;
    · obtain ⟨ i, hi ⟩ := hx; filter_upwards [ IsOpen.mem_nhds ( isOpen_lt ( continuous_apply i ) continuous_const ) hi ] with b hb; exact ⟨ i, hb ⟩ ;);
  exact h_cont_inf.continuousAt.tendsto.comp ( tendsto_pi_nhds.mpr fun i => hcd i { ℓ } )

/-- The persistent ground set: labels that lie in `range (t n)` for `U`-many `n`. -/
def XsetU (t : ℕ → ℕ) (U : Ultrafilter ℕ) : Set ℕ := {ℓ | {n | ℓ < t n} ∈ (U : Filter ℕ)}

/-
**(N1) on the persistent set.**  Persistent vertices carry limit density `≥ q-1`.
-/
lemma shadow_N1 (q : ℕ) (ρ' : ℕ → Fin q → ProbabilityMeasure (ℕ → Bool)) (t : ℕ → ℕ)
    (ε : ℕ → ℝ) (U : Ultrafilter ℕ) (hεU : Tendsto ε (↑U) (𝓝 0))
    (L : Fin q → ProbabilityMeasure (ℕ → Bool))
    (hcd : ∀ (i : Fin q) (S : Finset ℕ),
      Tendsto (fun n => cdens q (ρ' n) i S) (↑U) (𝓝 (cdens q L i S)))
    (hA1' : ∀ n ℓ, ℓ < t n → (q : ℝ) - 1 - ε n ≤ ∑ i, cdens q (ρ' n) i {ℓ})
    (x : ↑(XsetU t U)) :
    (q : ℝ≥0∞) - 1 ≤ ∑ i, (L i).toMeasure {σ | σ (x : ℕ) = true} := by
  have h_persistent : ∀ i, (L i).toMeasure {σ : ℕ → Bool | σ x = true} = ENNReal.ofReal (cdens q L i {↑x}) := by
    intro i
    simp [cdens];
  have h_persistent : (q : ℝ) - 1 ≤ ∑ i, cdens q L i {↑x} := by
    have h_persistent : Filter.Tendsto (fun n => ∑ i, cdens q (ρ' n) i {↑x}) (↑U) (𝓝 (∑ i, cdens q L i {↑x})) := by
      exact tendsto_finset_sum _ fun i _ => hcd i _;
    have h_persistent : ∀ᶠ n in (U : Filter ℕ), (q : ℝ) - 1 - ε n ≤ ∑ i, cdens q (ρ' n) i {↑x} := by
      exact Filter.mem_of_superset x.2 fun n hn => hA1' n _ hn;
    have := le_of_tendsto_of_tendsto ( Filter.Tendsto.sub tendsto_const_nhds hεU ) ‹_› h_persistent; aesop;
  convert! ENNReal.ofReal_le_ofReal h_persistent using 1;
  rw [ ENNReal.ofReal_sum_of_nonneg ];
  · aesop;
  · exact fun _ _ => cdens_nonneg _ _ _ _

/-
**(N2) on the persistent set.**  Every `a`-subset is null in some colour.
-/
lemma shadow_N2 (q : ℕ) (a : ℕ) (ρ' : ℕ → Fin q → ProbabilityMeasure (ℕ → Bool))
    (t : ℕ → ℕ) (ε : ℕ → ℝ) (_hε0 : ∀ n, 0 ≤ ε n)
    (U : Ultrafilter ℕ) (hεU : Tendsto ε (↑U) (𝓝 0))
    (L : Fin q → ProbabilityMeasure (ℕ → Bool))
    (hcd : ∀ (i : Fin q) (S : Finset ℕ),
      Tendsto (fun n => cdens q (ρ' n) i S) (↑U) (𝓝 (cdens q L i S)))
    (hA2' : ∀ n (S : Finset ℕ), (∀ x ∈ S, x < t n) → S.card = a →
      ∃ i, cdens q (ρ' n) i S ≤ ε n)
    (S : Finset ↑(XsetU t U)) (hScard : S.card = a) :
    ∃ i, (L i).toMeasure (⋂ x ∈ S, {σ | σ (x : ℕ) = true}) = 0 := by
  -- By the ultrafilter property, there exists an i such that {n | cdens q (ρ' n) i S ≤ ε n} ∈ U.
  obtain ⟨i, hi⟩ : ∃ i, {n | cdens q (ρ' n) i (S.map (Function.Embedding.subtype (XsetU t U))) ≤ ε n} ∈ U := by
    have h_union : ⋃ i : Fin q, {n | cdens q (ρ' n) i (S.map (Function.Embedding.subtype (XsetU t U))) ≤ ε n} ∈ U := by
      refine' Filter.mem_of_superset _ _;
      exact ⋂ x ∈ S, { n | ( x : ℕ ) < t n };
      · exact Filter.biInter_mem ( Finset.finite_toSet S ) |>.2 fun x hx => x.2;
      · intro n hn; specialize hA2' n ( S.map ( Function.Embedding.subtype ( XsetU t U ) ) ) ; aesop;
    contrapose! h_union;
    have h_finite_union : ∀ (s : Finset (Fin q)), (⋃ i ∈ s, {n | cdens q (ρ' n) i (S.map (Function.Embedding.subtype (XsetU t U))) ≤ ε n}) ∉ U := by
      intro s hs; induction s using Finset.induction <;> simp_all +decide [  ] ;
    simpa using! h_finite_union Finset.univ;
  -- By the ultrafilter property, we have that `cdens q L i (S.map (Function.Embedding.subtype (XsetU t U))) ≤ 0`.
  have h_cdens_zero : cdens q L i (S.map (Function.Embedding.subtype (XsetU t U))) ≤ 0 := by
    exact le_of_tendsto_of_tendsto ( hcd i _ ) hεU ( Filter.eventually_of_mem hi fun n hn => hn );
  use i;
  convert! ENNReal.ofReal_eq_zero.mpr h_cdens_zero using 1;
  convert! ( ENNReal.ofReal_toReal _ ) |> Eq.symm;
  · convert! cdens_eq_inter_toReal q L i S |> Eq.symm using 1;
  · exact MeasureTheory.measure_ne_top _ _

/-- **Shadow finite-transfer core.**  From a relabelled counterexample family on
the Boolean cube (impurity-ordered ground sets `range (t n)`, weak ultrafilter
limit `L`, slacks `→ 0`) satisfying the approximate hypotheses and admitting no
valid colouring, derive a contradiction.  This is the heart of the null-blocker
compactness theorem (`lem:fdlimit`–`lem:finitetransfer`). -/
lemma shadow_finish (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a) (rStar : ℕ)
    (ρ' : ℕ → Fin q → ProbabilityMeasure (ℕ → Bool)) (t : ℕ → ℕ) (ε : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n)
    (U : Ultrafilter ℕ) (hεU : Tendsto ε (↑U) (𝓝 0))
    (L : Fin q → ProbabilityMeasure (ℕ → Bool))
    (hcd : ∀ (i : Fin q) (S : Finset ℕ),
      Tendsto (fun n => cdens q (ρ' n) i S) (↑U) (𝓝 (cdens q L i S)))
    (C' : ℕ → Fin q → Set (Finset ℕ))
    (hEdge' : ∀ n i, ∀ E ∈ C' n i, E.Nonempty ∧ E.card ≤ rStar ∧ ∀ x ∈ E, x < t n)
    (hA1' : ∀ n ℓ, ℓ < t n → (q : ℝ) - 1 - ε n ≤ ∑ i, cdens q (ρ' n) i {ℓ})
    (hA2' : ∀ n (S : Finset ℕ), (∀ x ∈ S, x < t n) → S.card = a →
      ∃ i, cdens q (ρ' n) i S ≤ ε n)
    (hA3' : ∀ n i, ∀ E ∈ C' n i, ∃ j, j ≠ i ∧ cdens q (ρ' n) j E ≤ ε n)
    (hmono : ∀ n ℓ₁ ℓ₂, ℓ₁ ≤ ℓ₂ → ℓ₂ < t n → cimp q (ρ' n) ℓ₂ ≤ cimp q (ρ' n) ℓ₁)
    (hdead : ∀ n (i : Fin q) ℓ, t n ≤ ℓ → cdens q (ρ' n) i {ℓ} = 0)
    (hNoValid' : ∀ n (Z : Finset ℕ) (φ : ℕ → Fin q), (∀ x ∈ Z, x < t n) →
      Z.card ≤ a - 1 → ∃ i, ∃ E ∈ C' n i, ∀ x ∈ E, x ∉ Z ∧ φ x = i) :
    False := by
  classical
  have hqne : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  set Xs : Set ℕ := XsetU t U with hXs
  set μ : Fin q → Measure (ℕ → Bool) := fun i => (L i).toMeasure with hμ
  have hμprob : ∀ i, IsProbabilityMeasure (μ i) := fun i => by rw [hμ]; infer_instance
  set A : Fin q → ↑Xs → Set (ℕ → Bool) := fun _ x => {σ | σ (x : ℕ) = true} with hA
  have hAmeas : ∀ i (x : ↑Xs), MeasurableSet (A i x) := fun i x =>
    measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have hcdμ : ∀ (j : Fin q) (x : ↑Xs), (μ j (A j x)).toReal = cdens q L j {(x : ℕ)} := by
    intro j x; simp only [hμ, hA, cdens]; congr 2; ext σ; simp
  -- (N1), (N2) on the persistent set.
  have hN1 : ∀ x : ↑Xs, (q : ℝ≥0∞) - 1 ≤ ∑ i, μ i (A i x) :=
    shadow_N1 q ρ' t ε U hεU L hcd hA1'
  have hN2 : ∀ S : Finset ↑Xs, S.card = a → ∃ i, μ i (⋂ x ∈ S, A i x) = 0 :=
    shadow_N2 q a ρ' t ε hε0 U hεU L hcd hA2'
  -- Finite homes and their ultrafilter stabilisation.
  set chome' : ℕ → ℕ → Fin q := fun n ℓ => (exists_cimp_eq q (by omega) (ρ' n) ℓ).choose
    with hchome'_def
  have hchome' : ∀ n ℓ, cimp q (ρ' n) ℓ = cdens q (ρ' n) (chome' n ℓ) {ℓ} :=
    fun n ℓ => (exists_cimp_eq q (by omega) (ρ' n) ℓ).choose_spec
  set hh : ↑Xs → Fin q :=
    fun x => (exists_ultrafilter_eventually_eq U (fun n => chome' n (x : ℕ))).choose with hh_def
  have hhrec : ∀ x : ↑Xs, {n | chome' n (x : ℕ) = hh x} ∈ (U : Filter ℕ) :=
    fun x => (exists_ultrafilter_eventually_eq U (fun n => chome' n (x : ℕ))).choose_spec
  have hhmin : ∀ (x : ↑Xs) (i : Fin q), μ (hh x) (A (hh x) x) ≤ μ i (A i x) := by
    intro x i
    rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _), hcdμ, hcdμ]
    refine le_of_tendsto_of_tendsto (hcd (hh x) {(x : ℕ)}) (hcd i {(x : ℕ)}) ?_
    filter_upwards [hhrec x] with n hn
    rw [← hn, ← hchome' n (x : ℕ)]
    exact cimp_le q (ρ' n) i (x : ℕ)
  -- Exact rounding with the home property on the limit system.
  set D : Fin q → Set (Finset ↑Xs) :=
    fun i => {E | E.Nonempty ∧ ∃ j, j ≠ i ∧ μ j (⋂ x ∈ E, A j x) = 0} with hD
  obtain ⟨Zstar, φstar, hZcard, hblock, hHomeFin⟩ :=
    exact_rounding_home q hq a ha (↑Xs) (fun _ => ℕ → Bool) μ A hAmeas D
      (fun i E hE => hE.1) hN1 hN2 (fun i E hE => hE.2) hh hhmin
  -- A numeric threshold above which `φstar` agrees with the home.
  set L₀ : ℕ := hHomeFin.toFinset.sup (fun x => (x : ℕ)) + 1 with hL₀def
  have hL₀ : ∀ x : ↑Xs, L₀ ≤ (x : ℕ) → φstar x = hh x := by
    intro x hx
    by_contra hne
    have hxmem : x ∈ hHomeFin.toFinset := by rw [Set.Finite.mem_toFinset]; exact hne
    have hle : (x : ℕ) ≤ hHomeFin.toFinset.sup (fun x => (x : ℕ)) := Finset.le_sup hxmem
    omega
  -- The finite colourings.
  set φn : ℕ → ℕ → Fin q :=
    fun n ℓ => if h : ℓ ∈ Xs ∧ ℓ < L₀ then φstar ⟨ℓ, h.1⟩ else chome' n ℓ with hφn_def
  set Zℕ : Finset ℕ := Zstar.map (Function.Embedding.subtype Xs) with hZℕ
  have hZℕcard : Zℕ.card ≤ a - 1 := by rw [hZℕ, Finset.card_map]; exact hZcard
  have hviol : ∀ n, ∃ i, ∃ E ∈ C' n i,
      ∀ x ∈ E, x ∉ (Zℕ.filter (· < t n)) ∧ φn n x = i := by
    intro n
    refine hNoValid' n (Zℕ.filter (· < t n)) (φn n) ?_ ?_
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · exact le_trans (Finset.card_filter_le _ _) hZℕcard
  choose iv Ev hEvmem hEvviol using hviol
  -- Stabilise the colour, blocker and cardinality along `U`.
  obtain ⟨i₀, hi₀⟩ := exists_ultrafilter_eventually_eq U iv
  set bj : ℕ → Fin q := fun n => (hA3' n (iv n) (Ev n) (hEvmem n)).choose with hbj_def
  have hbjspec : ∀ n, bj n ≠ iv n ∧ cdens q (ρ' n) (bj n) (Ev n) ≤ ε n :=
    fun n => (hA3' n (iv n) (Ev n) (hEvmem n)).choose_spec
  obtain ⟨j₀, hj₀⟩ := exists_ultrafilter_eventually_eq U bj
  have hji : j₀ ≠ i₀ := by
    obtain ⟨n, hn⟩ := Filter.nonempty_of_mem (Filter.inter_mem hi₀ hj₀)
    have hne := (hbjspec n).1
    rw [hn.1, hn.2] at hne
    exact hne
  obtain ⟨kc, hkc⟩ := exists_ultrafilter_eventually_eq U
    (fun n => (⟨(Ev n).card, Nat.lt_succ_of_le (hEdge' n (iv n) (Ev n) (hEvmem n)).2.1⟩ :
      Fin (rStar + 1)))
  set k : ℕ := kc.val with hk_def
  have hk : {n | (Ev n).card = k} ∈ (U : Filter ℕ) := by
    refine Filter.mem_of_superset hkc ?_
    intro n hn
    have := congrArg Fin.val hn
    simpa [hk_def] using! this
  -- Enumerate the edges and split positions into recurring / escaping.
  set e : ℕ → Fin k → ℕ :=
    fun n p => if h : (Ev n).card = k then (Ev n).orderEmbOfFin h p else 0 with he_def
  obtain ⟨R, v, hrec, hesc⟩ := exists_position_dichotomy U k e
  -- Membership facts.
  have hemem : ∀ n, (Ev n).card = k → ∀ p, e n p ∈ Ev n := by
    intro n hn p; rw [he_def]; simp only [dif_pos hn]; exact Finset.orderEmbOfFin_mem _ _ _
  have helt : ∀ n, (Ev n).card = k → ∀ p, e n p < t n := by
    intro n hn p; exact (hEdge' n (iv n) (Ev n) (hEvmem n)).2.2 _ (hemem n hn p)
  -- Persistent recurring values lie in `Xs`.
  have hvXs : ∀ p ∈ R, v p ∈ Xs := by
    intro p hp
    rw [hXs, XsetU, Set.mem_setOf_eq]
    refine Filter.mem_of_superset (Filter.inter_mem (hrec p hp) hk) ?_
    rintro n ⟨hn1, hn2⟩
    have := helt n hn2 p
    rw [hn1] at this; exact this
  -- The limit impurity and its summability/continuity.
  have hconv : ∀ ℓ, Tendsto (fun n => cimp q (ρ' n) ℓ) (↑U) (𝓝 (cimp q L ℓ)) :=
    cimp_tendsto ρ' L U hcd
  have hsum : Summable (fun ℓ => cimp q L ℓ) := by
    have hsub : Summable (fun x : ↑Xs => cimp q L (x : ℕ)) := by
      refine (limit_impurity_summable q hq a ha μ A hAmeas hN1 hN2).congr (fun x => ?_)
      unfold cimp
      exact iInf_congr (fun i => hcdμ i x)
    have hzero : ∀ ℓ ∉ Xs, cimp q L ℓ = 0 := by
      intro ℓ hℓ
      have hUc : {n | t n ≤ ℓ} ∈ (U : Filter ℕ) := by
        have hnot : {n | ℓ < t n} ∉ U := by
          intro hmem
          rw [hXs, XsetU, Set.mem_setOf_eq] at hℓ
          exact hℓ (Ultrafilter.mem_coe.mpr hmem)
        have hc : {n | ℓ < t n}ᶜ ∈ U := (U.mem_or_compl_mem _).resolve_left hnot
        refine Filter.mem_of_superset (Ultrafilter.mem_coe.mpr hc) ?_
        intro n hn; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hn
        exact hn
      have hcd0 : ∀ i, cdens q L i {ℓ} = 0 := by
        intro i
        have h0 : Tendsto (fun n => cdens q (ρ' n) i {ℓ}) (↑U) (𝓝 0) := by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [hUc] with n hn using (hdead n i ℓ hn).symm
        exact tendsto_nhds_unique (hcd i {ℓ}) h0
      unfold cimp; simp only [hcd0]; exact ciInf_const
    have heq : (fun ℓ => cimp q L ℓ) = Xs.indicator (fun ℓ => cimp q L ℓ) := by
      funext ℓ
      by_cases h : ℓ ∈ Xs
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, hzero ℓ h]
    rw [heq]
    exact (summable_subtype_iff_indicator (f := fun ℓ => cimp q L ℓ)).mp hsub
  -- Escaping positions have finite-home `i₀` and vanishing impurity.
  have hescHome : ∀ p, p ∉ R → ∀ᶠ n in (U : Filter ℕ),
      cimp q (ρ' n) (e n p) = cdens q (ρ' n) i₀ {e n p} := by
    intro p hp
    filter_upwards [(hesc p hp).eventually_ge_atTop L₀, hi₀, hk] with n hnL hni hnk
    have hmem := hemem n hnk p
    have hφ := (hEvviol n (e n p) hmem).2
    rw [hni] at hφ
    have hbranch : φn n (e n p) = chome' n (e n p) := by
      rw [hφn_def]; simp only; rw [dif_neg (by rintro ⟨_, hlt⟩; omega)]
    rw [hbranch] at hφ
    rw [hchome' n (e n p), hφ]
  have hescTail : ∀ p, p ∉ R → Tendsto (fun n => cimp q (ρ' n) (e n p)) (↑U) (𝓝 0) := by
    intro p hp
    refine moving_tail q ρ' U t (fun ℓ => cimp q L ℓ) hsum hconv hmono (fun n => e n p)
      (hesc p hp) ?_
    filter_upwards [hk] with n hnk using helt n hnk p
  -- The drop bound, valid `U`-eventually.
  set Q : Finset (Fin k) := Finset.univ \ R with hQ
  have hrecAll : ∀ᶠ n in (U : Filter ℕ), ∀ p ∈ R, e n p = v p := by
    rw [Filter.eventually_all_finset]; exact fun p hp => hrec p hp
  have hescHomeAll : ∀ᶠ n in (U : Filter ℕ),
      ∀ p ∈ Q, cimp q (ρ' n) (e n p) = cdens q (ρ' n) i₀ {e n p} := by
    rw [Filter.eventually_all_finset]
    exact fun p hp => hescHome p (by simpa [hQ, Finset.mem_sdiff] using! hp)
  have hbound : ∀ᶠ n in (U : Filter ℕ),
      cdens q (ρ' n) j₀ (R.image v)
        ≤ ε n + ∑ p ∈ Q, (cimp q (ρ' n) (e n p) + ε n) := by
    filter_upwards [hi₀, hj₀, hk, hrecAll, hescHomeAll] with n hni hnj hnk hrecn hhomen
    -- `e n` is injective and enumerates `Ev n`.
    have hinj : Function.Injective (e n) := by
      intro p p' hpp'
      have : (Ev n).orderEmbOfFin hnk p = (Ev n).orderEmbOfFin hnk p' := by
        simpa only [he_def, dif_pos hnk] using! hpp'
      exact (Ev n).orderEmbOfFin hnk |>.injective this
    have hEveq : Finset.univ.image (e n) = Ev n := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy; obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hy; exact hemem n hnk p
      · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hnk]
    have hRv : R.image (e n) = R.image v := Finset.image_congr (fun p hp => hrecn p hp)
    -- `Ev n = (R.image v) ∪ (Q.image (e n))`.
    have hunion : (R.image v) ∪ (Q.image (e n)) = Ev n := by
      rw [← hRv, ← Finset.image_union, hQ, Finset.union_sdiff_of_subset (Finset.subset_univ R),
        hEveq]
    -- The blocker bound on `Ev n`.
    have hblk : cdens q (ρ' n) j₀ (Ev n) ≤ ε n := by
      have := (hbjspec n).2; rwa [hnj] at this
    -- Drop the escaping coordinates.
    have hdrop := cdens_inter_drop q (ρ' n) j₀ (R.image v) (Q.image (e n))
    rw [hunion] at hdrop
    -- Bound the complement sum termwise.
    have step1 : ∑ y ∈ Q.image (e n), (1 - cdens q (ρ' n) j₀ {y})
        ≤ ∑ p ∈ Q, (1 - cdens q (ρ' n) j₀ {e n p}) := by
      apply Finset.sum_image_le_of_nonneg
      intro y _
      have hle1 : cdens q (ρ' n) j₀ {y} ≤ 1 := cdens_le_one q (ρ' n) j₀ {y}
      linarith
    have step2 : ∑ p ∈ Q, (1 - cdens q (ρ' n) j₀ {e n p})
        ≤ ∑ p ∈ Q, (cimp q (ρ' n) (e n p) + ε n) := by
      refine Finset.sum_le_sum (fun p hp => ?_)
      exact home_complement_bound q (ρ' n) (e n p) (ε n) i₀ j₀
        (hA1' n (e n p) (helt n hnk p)) (hhomen p hp) hji
    linarith [hdrop, hblk, le_trans step1 step2]
  -- Pass to the limit: the persistent edge is null in colour `j₀`.
  have hRHS : Tendsto (fun n => ε n + ∑ p ∈ Q, (cimp q (ρ' n) (e n p) + ε n)) (↑U) (𝓝 0) := by
    have hsumtail : Tendsto (fun n => ∑ p ∈ Q, (cimp q (ρ' n) (e n p) + ε n)) (↑U) (𝓝 0) := by
      have h0 : (0 : ℝ) = ∑ p ∈ Q, (0 : ℝ) := by simp
      rw [h0]
      refine tendsto_finset_sum _ (fun p hp => ?_)
      have hpR : p ∉ R := by simpa [hQ, Finset.mem_sdiff] using! hp
      simpa using! (hescTail p hpR).add hεU
    simpa using! hεU.add hsumtail
  have hnull : cdens q L j₀ (R.image v) = 0 := by
    have hle : cdens q L j₀ (R.image v) ≤ 0 :=
      le_of_tendsto_of_tendsto (hcd j₀ (R.image v)) hRHS hbound
    exact le_antisymm hle (cdens_nonneg q L j₀ (R.image v))
  -- `R.image v` is nonempty (otherwise the empty cylinder mass `1` would be `0`).
  have hcd_empty : cdens q L j₀ (∅ : Finset ℕ) = 1 := by
    simp only [cdens]; norm_num
  have hEne : (R.image v).Nonempty := by
    rcases (R.image v).eq_empty_or_nonempty with h | h
    · rw [h, hcd_empty] at hnull; norm_num at hnull
    · exact h
  -- The persistent edge as a finset of `↑Xs`.
  set Estar : Finset ↑Xs := R.attach.image (fun p => (⟨v p.1, hvXs p.1 p.2⟩ : ↑Xs)) with hEstar
  have hmapeq : Estar.map (Function.Embedding.subtype Xs) = R.image v := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [hEstar, Finset.mem_image] at hz
      obtain ⟨p, _, rfl⟩ := hz
      exact Finset.mem_image.mpr ⟨p.1, p.2, rfl⟩
    · intro hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      rw [Finset.mem_map]
      refine ⟨⟨v w, hvXs w hw⟩, ?_, rfl⟩
      rw [hEstar, Finset.mem_image]
      exact ⟨⟨w, hw⟩, Finset.mem_attach _ _, rfl⟩
  have hEne' : Estar.Nonempty := by
    rw [← Finset.map_nonempty (f := Function.Embedding.subtype Xs), hmapeq]; exact hEne
  have hμ0 : μ j₀ (⋂ x ∈ Estar, A j₀ x) = 0 := by
    have htoReal : (μ j₀ (⋂ x ∈ Estar, A j₀ x)).toReal = 0 := by
      have hee := cdens_eq_inter_toReal q L j₀ Estar
      simp only [hμ, hA]
      rw [hee, hmapeq, hnull]
    rcases (ENNReal.toReal_eq_zero_iff _).1 htoReal with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  -- The final contradiction with `hblock`.
  refine hblock i₀ Estar ⟨hEne', j₀, hji, hμ0⟩ ?_
  intro x hx
  simp only [hEstar, Finset.mem_image, Finset.mem_attach, true_and] at hx
  obtain ⟨p, rfl⟩ := hx
  set p₀ := p.1 with hp₀
  have hp₀R : p₀ ∈ R := p.2
  obtain ⟨n, ⟨⟨hn1, hn2⟩, hn3⟩, hn4⟩ := Filter.nonempty_of_mem
    (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (hrec p₀ hp₀R) hi₀) hk)
      (hhrec ⟨v p₀, hvXs p₀ hp₀R⟩))
  have hvmem : v p₀ ∈ Ev n := by rw [← hn1]; exact hemem n hn3 p₀
  have hvlt : v p₀ < t n := by rw [← hn1]; exact helt n hn3 p₀
  obtain ⟨hvZ, hvφ⟩ := hEvviol n (v p₀) hvmem
  rw [hn2] at hvφ
  -- `φstar ⟨v p₀,_⟩ = i₀`.
  have hφstar : φstar (⟨v p₀, hvXs p₀ hp₀R⟩ : ↑Xs) = i₀ := by
    by_cases hcase : v p₀ ∈ Xs ∧ v p₀ < L₀
    · have : φn n (v p₀) = φstar ⟨v p₀, hcase.1⟩ := by
        rw [hφn_def]; simp only [dif_pos hcase]
      rw [this] at hvφ
      simpa using! hvφ
    · have hge : L₀ ≤ v p₀ := by
        rcases not_and_or.mp hcase with h | h
        · exact absurd (hvXs p₀ hp₀R) h
        · omega
      have hbr : φn n (v p₀) = chome' n (v p₀) := by
        rw [hφn_def]; simp only; rw [dif_neg (by rintro ⟨_, hlt⟩; omega)]
      rw [hbr] at hvφ
      have hhi : hh (⟨v p₀, hvXs p₀ hp₀R⟩ : ↑Xs) = i₀ := by rw [← hn4, hvφ]
      rw [hL₀ ⟨v p₀, hvXs p₀ hp₀R⟩ hge, hhi]
  refine ⟨?_, hφstar⟩
  -- `⟨v p₀,_⟩ ∉ Zstar`.
  intro hmem
  have hvZℕ : v p₀ ∈ Zℕ := by
    rw [hZℕ]; exact Finset.mem_map.mpr ⟨⟨v p₀, hvXs p₀ hp₀R⟩, hmem, rfl⟩
  exact hvZ (Finset.mem_filter.mpr ⟨hvZℕ, hvlt⟩)

end Erdos550
