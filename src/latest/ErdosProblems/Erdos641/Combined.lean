/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos641.ChromaticCounting

/-!
# Simultaneously avoiding the two JSS obstructions

The dense-prefix demand cylinders use less than one half of the finite
sample space, while the chromatic cylinders use less than one quarter.
Their union therefore cannot cover the sample space.
-/

open Finset Fintype Filter
open scoped BigOperators Classical

namespace Erdos641

open SimpleGraph
open Erdos182

noncomputable section

/-- The demand family used at a shifted layer and a positive candidate-set
size `z+1`. -/
def jssDenseDemandFamily {n : ℕ} (default : JSSOutcome n)
    (j : Fin (prsLayerCount n - 1)) (z : Fin (prsBadCutoff n j))
    (S : Finset (JSSVertex n)) :
    Finset (CoordinateDemand (JSSCoordinate n) (JSSVertex n)) :=
  prefixJSSCoordinateDemands default (jssSuccessorLayer j)
    (prsBadEdgeCount (z.val + 1)) S

/-- One dense-prefix cylinder union, intersected with the admissible sample
space so that its relative cardinality has the intended denominator. -/
def jssDenseDemandBad {n : ℕ} (default : JSSOutcome n)
    (j : Fin (prsLayerCount n - 1)) (z : Fin (prsBadCutoff n j)) :
    Finset (JSSOutcome n) :=
  jssOutcomeSpace n ∩
    prsDemandUnion jssAllowed (z.val + 1)
      (jssDenseDemandFamily default j z)

/-- Union of all shifted-layer dense-prefix demand events. -/
def jssDenseDemandBadUnion {n : ℕ} (default : JSSOutcome n) :
    Finset (JSSOutcome n) :=
  (Finset.univ : Finset
    (PRSBadIndex (prsLayerCount n - 1) (prsBadCutoff n))).biUnion
      fun e ↦ jssDenseDemandBad default e.1 e.2

/-- The PRS geometric error is eventually smaller than one half. -/
lemma eventually_prs_error_lt_half :
    ∀ᶠ n : ℕ in atTop,
      2 * (prsLayerCount n : ℝ) * Real.exp (-(prsY n / 2)) < 1 / 2 := by
  have hdecay : Tendsto
      (fun x : ℝ ↦ 2 * (x ^ (1 : ℝ) * Real.exp (-(1 / 2 : ℝ) * x)))
      atTop (nhds 0) := by
    have htwo : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    simpa using htwo.mul
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2) (by norm_num))
  have hcomp : Tendsto
      (fun n : ℕ ↦ 2 * prsY n * Real.exp (-(prsY n / 2)))
      atTop (nhds 0) := by
    have heq :
        (fun n : ℕ ↦ 2 * prsY n * Real.exp (-(prsY n / 2))) =
          (fun n : ℕ ↦ 2 * (prsY n ^ (1 : ℝ) *
            Real.exp (-(1 / 2 : ℝ) * prsY n))) := by
      funext n
      rw [Real.rpow_one]
      rw [show -(prsY n / 2) = -(1 / 2 : ℝ) * prsY n by ring]
      ring
    rw [heq]
    change Tendsto
      ((fun x : ℝ ↦ 2 * (x ^ (1 : ℝ) *
        Real.exp (-(1 / 2 : ℝ) * x))) ∘ prsY) atTop (nhds 0)
    exact hdecay.comp tendsto_prsY_atTop
  have hevent : ∀ᶠ n : ℕ in atTop,
      2 * prsY n * Real.exp (-(prsY n / 2)) < 1 / 2 :=
    hcomp.eventually (Iio_mem_nhds (by norm_num))
  have hLtop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hevent, hLtop.eventually_ge_atTop 1] with n hsmall hL
  have hC := prsLayerCount_le_prsY hL
  have hnonneg : 0 ≤ Real.exp (-(prsY n / 2)) := (Real.exp_pos _).le
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 2)) hnonneg)
    hsmall

/-- Quantitative relative-cardinality estimate for one shifted dense-demand
event. -/
lemma jssDenseDemandBad_ratio_le {n : ℕ} (default : JSSOutcome n)
    (hcard : Fintype.card (JSSVertex n) ≤ n)
    (hlayer : ∀ i < prsLayerCount n, 0 < prsLayerSize n i)
    (hseparate : ∀ i, i + 1 < prsLayerCount n →
      4000 * prsLayerSize n (i + 1) ≤ prsLayerSize n i)
    (honeEvent : ∀ i, 1 ≤ i → i < prsLayerCount n →
      ∀ x, 1 ≤ x → x ≤ 1000 * prsLayerSize n i →
        (n.choose x : ℝ) *
            ((x.choose 2).choose (prsBadEdgeCount x) : ℝ) /
              (prsLayerSize n (i - 1) : ℝ) ^ prsBadEdgeCount x ≤
          Real.exp (-(x : ℝ) * prsY n / 2))
    (hspace : (jssOutcomeSpace n).Nonempty)
    (j : Fin (prsLayerCount n - 1)) (z : Fin (prsBadCutoff n j)) :
    ((jssDenseDemandBad default j z).card : ℝ) /
        (jssOutcomeSpace n).card ≤
      Real.exp (-((((z : ℕ) + 1 : ℕ) : ℝ) * prsY n / 2)) := by
  classical
  let x := z.val + 1
  let r := prsBadEdgeCount x
  let b := prsLayerSize n j.val
  let family : Finset (JSSVertex n) →
      Finset (CoordinateDemand (JSSCoordinate n) (JSSVertex n)) :=
    jssDenseDemandFamily default j z
  have hfamily : ∀ S ∈ (Finset.univ : Finset (JSSVertex n)).powersetCard x,
      (family S).card ≤ (x.choose 2).choose r := by
    intro S hS
    have hScard := (Finset.mem_powersetCard.mp hS).2
    by_cases hprefix : S ⊆ jssPrefix n (jssSuccessorLayer j)
    · simpa [family, jssDenseDemandFamily,
        prefixJSSCoordinateDemands, hprefix, x, r, hScard] using
        card_candidateJSSCoordinateDemands_le_choose default S
          (prsBadEdgeCount x)
    · simp [family, jssDenseDemandFamily,
        prefixJSSCoordinateDemands, hprefix]
  have hdemandCard : ∀ S ∈
      (Finset.univ : Finset (JSSVertex n)).powersetCard x,
      ∀ d ∈ family S, d.coords.card = r := by
    intro S hS d hd
    have hScard := (Finset.mem_powersetCard.mp hS).2
    simpa [family, jssDenseDemandFamily, x, r, hScard] using
      coords_card_of_mem_prefixJSSCoordinateDemands default
        (jssSuccessorLayer j) S (prsBadEdgeCount x) hd
  have hlower : ∀ S ∈
      (Finset.univ : Finset (JSSVertex n)).powersetCard x,
      ∀ d ∈ family S, ∀ c ∈ d.coords, b ≤ (jssAllowed c).card := by
    intro S hS d hd c hc
    have hScard := (Finset.mem_powersetCard.mp hS).2
    apply allowed_card_lower_of_mem_prefixJSSCoordinateDemands default
      (jssSuccessorLayer j) S (prsBadEdgeCount x)
      (prsLayerSize n j.val) (fun k hk ↦ ?_) (by
        simpa [family, jssDenseDemandFamily, x, r, hScard] using hd) hc
    have hk' : k.val < j.val + 1 := by
      change k.val < (jssSuccessorLayer j).val at hk
      simpa using hk
    have hmono : prsLayerSize n k.val ≥ prsLayerSize n j.val :=
      prsLayerSize_antitone_below
        (fun a ha ↦ by
          have hs := hseparate a ha
          omega)
        (Nat.le_of_lt_succ hk') (by omega)
    exact hmono
  have hraw := card_bad_candidate_sets_mul_pow_le
    jssAllowed x r b family hfamily hdemandCard hlower
  have hcount : (jssDenseDemandBad default j z).card * b ^ r ≤
      (Fintype.card (JSSVertex n)).choose x * (x.choose 2).choose r *
        (jssOutcomeSpace n).card := by
    calc
      (jssDenseDemandBad default j z).card * b ^ r ≤
          (prsDemandUnion jssAllowed x family).card * b ^ r := by
        apply Nat.mul_le_mul_right
        apply Finset.card_le_card
        change jssOutcomeSpace n ∩ prsDemandUnion jssAllowed x family ⊆
          prsDemandUnion jssAllowed x family
        exact Finset.inter_subset_right
      _ ≤ (Fintype.card (JSSVertex n)).choose x *
          (x.choose 2).choose r * (jssOutcomeSpace n).card := by
        simpa [prsDemandUnion, jssOutcomeSpace, jssDenseDemandBad,
          family, x, r, b] using hraw
  have hbpos : 0 < b := hlayer j.val (by omega)
  have hspacepos : (0 : ℝ) < (jssOutcomeSpace n).card := by
    exact_mod_cast Finset.card_pos.mpr hspace
  have hdenompos : (0 : ℝ) < (b : ℝ) ^ r := by
    positivity
  have hratio :
      ((jssDenseDemandBad default j z).card : ℝ) /
          (jssOutcomeSpace n).card ≤
        ((Fintype.card (JSSVertex n)).choose x *
            (x.choose 2).choose r : ℕ) / (b : ℝ) ^ r := by
    rw [div_le_div_iff₀ hspacepos hdenompos]
    norm_num only [Nat.cast_mul, Nat.cast_pow]
    exact_mod_cast (by simpa [Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hcount)
  have hj : j.val + 1 < prsLayerCount n := by omega
  have hz : x ≤ 1000 * prsLayerSize n (j.val + 1) := by
    dsimp [x]
    exact z.isLt
  have hone := honeEvent (j.val + 1) (by omega) hj x (by omega) hz
  have hcoeff :
      ((Fintype.card (JSSVertex n)).choose x *
          (x.choose 2).choose r : ℕ) / (b : ℝ) ^ r ≤
        Real.exp (-((x : ℝ) * prsY n / 2)) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow]
    calc
      ((Fintype.card (JSSVertex n)).choose x : ℝ) *
            ((x.choose 2).choose r : ℝ) / (b : ℝ) ^ r ≤
          (n.choose x : ℝ) * ((x.choose 2).choose r : ℝ) /
            (b : ℝ) ^ r := by
        gcongr
      _ ≤ Real.exp (-(x : ℝ) * prsY n / 2) := by
        simpa [x, r, b] using hone
      _ = Real.exp (-((x : ℝ) * prsY n / 2)) := by
        congr 1
        ring
  exact hratio.trans (by simpa [x] using hcoeff)

/-- The union of every dense-prefix demand event occupies less than one half
of the admissible sample space. -/
lemma jssDenseDemandBadUnion_ratio_lt_half {n : ℕ}
    (default : JSSOutcome n)
    (hcard : Fintype.card (JSSVertex n) ≤ n)
    (hcount : 2 ≤ prsLayerCount n)
    (hlayer : ∀ i < prsLayerCount n, 0 < prsLayerSize n i)
    (hseparate : ∀ i, i + 1 < prsLayerCount n →
      4000 * prsLayerSize n (i + 1) ≤ prsLayerSize n i)
    (honeEvent : ∀ i, 1 ≤ i → i < prsLayerCount n →
      ∀ x, 1 ≤ x → x ≤ 1000 * prsLayerSize n i →
        (n.choose x : ℝ) *
            ((x.choose 2).choose (prsBadEdgeCount x) : ℝ) /
              (prsLayerSize n (i - 1) : ℝ) ^ prsBadEdgeCount x ≤
          Real.exp (-(x : ℝ) * prsY n / 2))
    (herror : 2 * (prsLayerCount n : ℝ) *
      Real.exp (-(prsY n / 2)) < 1 / 2)
    (hspace : (jssOutcomeSpace n).Nonempty) :
    ((jssDenseDemandBadUnion default).card : ℝ) /
        (jssOutcomeSpace n).card < 1 / 2 := by
  classical
  let L := prsLayerCount n - 1
  let cutoff : Fin L → ℕ := prsBadCutoff n
  let event : PRSBadIndex L cutoff → Finset (JSSOutcome n) :=
    fun e ↦ jssDenseDemandBad default e.1 e.2
  have hspacepos : (0 : ℝ) < (jssOutcomeSpace n).card := by
    exact_mod_cast Finset.card_pos.mpr hspace
  have hcardUnion : (jssDenseDemandBadUnion default).card ≤
      ∑ e : PRSBadIndex L cutoff, (event e).card := by
    simpa [jssDenseDemandBadUnion, event, L, cutoff] using
      (Finset.card_biUnion_le :
        ((Finset.univ : Finset (PRSBadIndex L cutoff)).biUnion event).card ≤
          ∑ e : PRSBadIndex L cutoff, (event e).card)
  have hhalf : Real.exp (-(prsY n / 2)) ≤ (1 / 2 : ℝ) := by
    have hcountR : (2 : ℝ) ≤ prsLayerCount n := by exact_mod_cast hcount
    have hmul : 2 * 2 * Real.exp (-(prsY n / 2)) ≤
        2 * (prsLayerCount n : ℝ) * Real.exp (-(prsY n / 2)) := by
      gcongr
    linarith [Real.exp_pos (-(prsY n / 2))]
  calc
    ((jssDenseDemandBadUnion default).card : ℝ) /
        (jssOutcomeSpace n).card ≤
      (↑(∑ e : PRSBadIndex L cutoff, (event e).card) : ℝ) /
        (jssOutcomeSpace n).card := by
          apply div_le_div_of_nonneg_right _ hspacepos.le
          exact_mod_cast hcardUnion
    _ = ∑ e : PRSBadIndex L cutoff,
          ((event e).card : ℝ) / (jssOutcomeSpace n).card := by
      norm_num only [Nat.cast_sum]
      simp_rw [Finset.sum_div]
    _ = ∑ j : Fin L, ∑ z : Fin (cutoff j),
          ((jssDenseDemandBad default j z).card : ℝ) /
            (jssOutcomeSpace n).card := by
      rw [Fintype.sum_sigma]
    _ ≤ ∑ _j : Fin L, 2 * Real.exp (-(prsY n / 2)) := by
      apply Finset.sum_le_sum
      intro j _hj
      calc
        (∑ z : Fin (cutoff j),
            ((jssDenseDemandBad default j z).card : ℝ) /
              (jssOutcomeSpace n).card) ≤
          ∑ z : Fin (cutoff j),
            Real.exp (-((((z : ℕ) + 1 : ℕ) : ℝ) * prsY n / 2)) := by
              apply Finset.sum_le_sum
              intro z _hz
              exact jssDenseDemandBad_ratio_le default hcard hlayer hseparate
                honeEvent hspace j z
        _ = ∑ x ∈ Finset.range (cutoff j),
            Real.exp (-(((x + 1 : ℕ) : ℝ) * prsY n / 2)) := by
              exact Fin.sum_univ_eq_sum_range
                (fun x : ℕ ↦ Real.exp
                  (-(((x + 1 : ℕ) : ℝ) * prsY n / 2))) (cutoff j)
        _ ≤ 2 * Real.exp (-(prsY n / 2)) :=
          sum_exp_neg_succ_mul_half_le (cutoff j) (prsY n) hhalf
    _ = 2 * (L : ℝ) * Real.exp (-(prsY n / 2)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    _ ≤ 2 * (prsLayerCount n : ℝ) * Real.exp (-(prsY n / 2)) := by
      gcongr
      exact_mod_cast Nat.sub_le (prsLayerCount n) 1
    _ < 1 / 2 := herror

/-- For every positive number of colors, sufficiently large JSS instances
contain an admissible outcome which is both 4-regular-subgraph-free and not
colorable with those colors. -/
theorem eventually_exists_regularFree_not_colorable (q : ℕ) (hq : 0 < q) :
    ∀ᶠ n : ℕ in atTop, ∃ ω : JSSOutcome n,
      ∃ hω : ω ∈ jssOutcomeSpace n,
        IsRegularSubgraphFree (jssGraph ω hω) 4 ∧
          ¬ Nonempty ((jssGraph ω hω).Coloring (Fin q)) := by
  filter_upwards [eventually_two_le_prsLayerCount,
      eventually_prsLayerSize_bounds, eventually_card_JSSVertex_le,
      eventually_four_thousand_mul_prsLayerSize_succ_le,
      eventually_prsLayer_tail_le, eventually_card_jssStrictTail_le_layer,
      eventually_prs_error_lt_half, eventually_prs_badEvent_choose_bound,
      tendsto_prsLayerCount_atTop.eventually_ge_atTop
        (q * (chromaticRepetitions q + 1))] with
      n hcount hlayerBounds hcard hseparate htail htailCard herror
        honeEvent hcolorCount
  classical
  have hlayer : ∀ i < prsLayerCount n, 0 < prsLayerSize n i :=
    fun i hi ↦ (hlayerBounds i hi).1
  have hallowed : ∀ c : JSSCoordinate n, (jssAllowed c).Nonempty := by
    intro c
    apply Finset.card_pos.mp
    rw [card_jssAllowed]
    exact hlayer c.targetLayer c.targetLayer.isLt
  choose target htarget using hallowed
  let default : JSSOutcome n := fun c _hc ↦ target c
  have hdefault : default ∈ jssOutcomeSpace n := by
    rw [mem_jssOutcomeSpace]
    intro c
    exact htarget c
  have hspace : (jssOutcomeSpace n).Nonempty := ⟨default, hdefault⟩
  have hdense := jssDenseDemandBadUnion_ratio_lt_half default hcard hcount
    hlayer hseparate honeEvent herror hspace
  have hchrom := chromaticBad_ratio_lt_one_quarter hq hlayer hseparate
    htailCard hspace
  let bad : Finset (JSSOutcome n) :=
    jssDenseDemandBadUnion default ∪
      chromaticBad n q (chromaticRepetitions q)
  have hspacepos : (0 : ℝ) < (jssOutcomeSpace n).card := by
    exact_mod_cast Finset.card_pos.mpr hspace
  have hbadRatio : (bad.card : ℝ) / (jssOutcomeSpace n).card < 1 := by
    calc
      (bad.card : ℝ) / (jssOutcomeSpace n).card ≤
          (((jssDenseDemandBadUnion default).card +
            (chromaticBad n q (chromaticRepetitions q)).card : ℕ) : ℝ) /
              (jssOutcomeSpace n).card := by
        apply div_le_div_of_nonneg_right _ hspacepos.le
        exact_mod_cast (Finset.card_union_le
          (jssDenseDemandBadUnion default)
          (chromaticBad n q (chromaticRepetitions q)))
      _ = ((jssDenseDemandBadUnion default).card : ℝ) /
            (jssOutcomeSpace n).card +
          ((chromaticBad n q (chromaticRepetitions q)).card : ℝ) /
            (jssOutcomeSpace n).card := by
        norm_num only [Nat.cast_add]
        ring
      _ < 1 / 2 + 1 / 4 := add_lt_add hdense hchrom
      _ < 1 := by norm_num
  have hbadCard : bad.card < (jssOutcomeSpace n).card := by
    rw [div_lt_one hspacepos] at hbadRatio
    exact_mod_cast hbadRatio
  have hnsub : ¬ jssOutcomeSpace n ⊆ bad := by
    intro hsub
    exact (Nat.not_lt_of_ge (Finset.card_le_card hsub)) hbadCard
  obtain ⟨ω, hω, hωbad⟩ : ∃ ω, ω ∈ jssOutcomeSpace n ∧ ω ∉ bad := by
    by_contra hnone
    apply hnsub
    intro ω hω
    by_contra hnot
    exact hnone ⟨ω, hω, hnot⟩
  have havoidDemand : ∀ (j : Fin (prsLayerCount n - 1))
      (z : Fin (prsBadCutoff n j)),
      ω ∉ prsDemandUnion jssAllowed (z.val + 1)
        (jssDenseDemandFamily default j z) := by
    intro j z hmem
    apply hωbad
    apply Finset.mem_union_left
    rw [jssDenseDemandBadUnion]
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨j, z⟩, Finset.mem_univ _, ?_⟩
    exact Finset.mem_inter.mpr ⟨hω, hmem⟩
  have havoidDense : ∀ j : Fin (prsLayerCount n - 1),
      ¬ DenseJSSPrefixBadAt (jssGraph ω hω) (jssSuccessorLayer j) := by
    intro j hbadDense
    obtain ⟨x, hx, hxcut, hxmem⟩ :=
      mem_prsDemandUnion_of_denseJSSPrefixBadAt ω default hω
        (jssSuccessorLayer j) hbadDense
    have hxcut' : x ≤ 1000 * prsLayerSize n (j.val + 1) := by
      simpa using hxcut
    let z : Fin (prsBadCutoff n j) := ⟨x - 1, by
      rw [prsBadCutoff]
      omega⟩
    apply havoidDemand j z
    have hz : z.val + 1 = x := by
      dsimp [z]
      omega
    change ω ∈ prsDemandUnion jssAllowed (z.val + 1)
      (fun S ↦ prefixJSSCoordinateDemands default (jssSuccessorLayer j)
        (prsBadEdgeCount (z.val + 1)) S)
    rw [hz]
    exact hxmem
  have hregular : IsRegularSubgraphFree (jssGraph ω hω) 4 :=
    isRegularSubgraphFree_four_of_avoids_dense hcount htail ω hω havoidDense
  have hnotColor : ¬ Nonempty ((jssGraph ω hω).Coloring (Fin q)) := by
    rintro ⟨C⟩
    apply hωbad
    apply Finset.mem_union_right
    exact mem_chromaticBad_of_coloring hq hlayer hcolorCount ω hω C
  exact ⟨ω, hω, hregular, hnotColor⟩

end

end Erdos641
