import ErdosProblems.Erdos380.AntiSieve

/-!
# A product-cutoff version of the residue-class sieve

Montgomery uncertainty can be summed over any chosen family of subsets,
not only subsets of one cardinality.  This permits the usual squarefree
product cutoff in the denominator of an upper-bound sieve.
-/

open scoped BigOperators Function

namespace Erdos380

/-- A member of an arbitrary finite family of subsets. -/
abbrev selectedSubsets {I : Type*} (family : Finset (Finset I)) :=
  {s : Finset I // s ∈ family}

/-- A nonzero product frequency on one selected subset of the full
modulus family. -/
abbrev selectedResidueFrequencies
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)] (family : Finset (Finset I)) :=
  Σ T : selectedSubsets family,
    {a : residueVectors (fun i : {i // i ∈ T.1} => modulus i.1) //
      a ∈ allNonzeroResidueFrequencies}

/-- Extend a frequency on a subset by zero in every unselected CRT
component. -/
noncomputable def extendSelectedResidueFrequency
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)] {family : Finset (Finset I)}
    (u : selectedResidueFrequencies modulus family) : residueVectors modulus :=
  fun i => if hi : i ∈ u.1.1 then u.2.1 ⟨i, hi⟩ else 0

/-- The circle point associated to a subset frequency, viewed in the full
CRT family by extension by zero. -/
noncomputable def selectedResidueFrequencyPoint
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)] {family : Finset (Finset I)}
    (u : selectedResidueFrequencies modulus family) : UnitAddCircle :=
  productResidueFrequencyPoint (extendSelectedResidueFrequency modulus u)

/-- Extending a subset frequency by zero does not change its circle
point. -/
lemma productResidueFrequencyPoint_extendSelectedResidueFrequency
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)] {family : Finset (Finset I)}
    (u : selectedResidueFrequencies modulus family) :
    selectedResidueFrequencyPoint modulus u =
      productResidueFrequencyPoint u.2.1 := by
  classical
  unfold selectedResidueFrequencyPoint productResidueFrequencyPoint
    extendSelectedResidueFrequency
  let F : I → UnitAddCircle := fun i =>
    ZMod.toAddCircle (if hi : i ∈ u.1.1 then u.2.1 ⟨i, hi⟩ else 0)
  change (∑ i : I, F i) = ∑ i : {i // i ∈ u.1.1}, ZMod.toAddCircle (u.2.1 i)
  calc
    (∑ i : I, F i) = ∑ i ∈ u.1.1, F i := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) fun i _hi hiT => by
        simp [F, hiT]
    _ = ∑ i : {i // i ∈ u.1.1}, F i :=
      Finset.sum_subtype u.1.1 (by simp) F
    _ = ∑ i : {i // i ∈ u.1.1}, ZMod.toAddCircle (u.2.1 i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [F, i.2]

/-- Extension by zero remembers both the chosen subset and all its
nonzero component frequencies. -/
theorem extendSelectedResidueFrequency_injective
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)] {family : Finset (Finset I)} :
    Function.Injective
      (extendSelectedResidueFrequency modulus :
        selectedResidueFrequencies modulus family → residueVectors modulus) := by
  classical
  rintro ⟨T, a⟩ ⟨U, b⟩ hab
  have ha : ∀ i, a.1 i ≠ 0 := by
    simpa only [allNonzeroResidueFrequencies, Finset.mem_filter,
      Finset.mem_univ, true_and] using a.2
  have hb : ∀ i, b.1 i ≠ 0 := by
    simpa only [allNonzeroResidueFrequencies, Finset.mem_filter,
      Finset.mem_univ, true_and] using b.2
  have hTUfin : T.1 = U.1 := by
    ext i
    constructor
    · intro hiT
      by_contra hiU
      have hiEq := congrFun hab i
      have hz : a.1 ⟨i, hiT⟩ = 0 := by
        simpa [extendSelectedResidueFrequency, hiT, hiU] using hiEq
      exact ha ⟨i, hiT⟩ hz
    · intro hiU
      by_contra hiT
      have hiEq := congrFun hab i
      have hz : b.1 ⟨i, hiU⟩ = 0 := by
        simpa [extendSelectedResidueFrequency, hiT, hiU] using hiEq.symm
      exact hb ⟨i, hiU⟩ hz
  have hTU : T = U := Subtype.ext hTUfin
  subst U
  have hab' : a = b := by
    apply Subtype.ext
    funext i
    have hiEq := congrFun hab i.1
    simpa [extendSelectedResidueFrequency, i.2] using hiEq
  rw [hab']

/-- Subset frequencies give distinct points of the additive circle. -/
theorem selectedResidueFrequencyPoint_injective
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus)) {family : Finset (Finset I)} :
    Function.Injective
      (selectedResidueFrequencyPoint modulus :
        selectedResidueFrequencies modulus family → UnitAddCircle) := by
  intro a b hab
  apply extendSelectedResidueFrequency_injective modulus
  apply productResidueFrequencyPoint_injective modulus hcoprime
  exact hab

private lemma cutoff_prod_union_le_mul_prod
    {I : Type*} [DecidableEq I] (f : I → ℕ)
    (hf : ∀ i, 1 ≤ f i) (S T : Finset I) :
    (∏ i ∈ S ∪ T, f i) ≤ (∏ i ∈ S, f i) * (∏ i ∈ T, f i) := by
  calc
    (∏ i ∈ S ∪ T, f i) =
        (∏ i ∈ S, f i) * (∏ i ∈ T \ S, f i) := by
      rw [← Finset.prod_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union]
    _ ≤ (∏ i ∈ S, f i) * (∏ i ∈ T, f i) := by
      have hsub : (∏ i ∈ T \ S, f i) ≤ ∏ i ∈ T, f i :=
        Finset.prod_le_prod_of_subset_of_one_le'
          (s := T \ S) (t := T) (f := f) Finset.sdiff_subset
          (fun i _hi _ => hf i)
      exact Nat.mul_le_mul_left _ hsub

/-- Frequencies belonging to possibly different selected subsets are
`1 / N`-separated whenever the product of the two subset moduli is at most
`N`.  This is the cross-subset spacing step in Tao's Corollary 2.8. -/
theorem one_div_le_dist_selectedResidueFrequencyPoint
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus)) {family : Finset (Finset I)} {N : ℕ}
    (hproduct : ∀ T U : selectedSubsets family,
      (∏ i ∈ T.1, modulus i) * (∏ i ∈ U.1, modulus i) ≤ N)
    {a b : selectedResidueFrequencies modulus family} (hab : a ≠ b) :
    (1 : ℝ) / N ≤
      dist (selectedResidueFrequencyPoint modulus a)
        (selectedResidueFrequencyPoint modulus b) := by
  classical
  let S : Finset I := a.1.1 ∪ b.1.1
  let Q : ℕ := ∏ i ∈ S, modulus i
  have hmodpos : ∀ i, 0 < modulus i :=
    fun i => Nat.pos_of_ne_zero (NeZero.ne (modulus i))
  have hQpos : 0 < Q := by
    unfold Q S
    exact Finset.prod_pos fun i _ => hmodpos i
  have hQle : Q ≤ N := by
    calc
      Q ≤ (∏ i ∈ a.1.1, modulus i) *
          (∏ i ∈ b.1.1, modulus i) := by
        exact cutoff_prod_union_le_mul_prod modulus (fun i => hmodpos i)
          a.1.1 b.1.1
      _ ≤ N := hproduct a.1 b.1
  have hNpos : 0 < N := lt_of_lt_of_le hQpos hQle
  have haOutside : ∀ i, i ∉ S →
      extendSelectedResidueFrequency modulus a i = 0 := by
    intro i hiS
    have hiA : i ∉ a.1.1 := fun hi => hiS (Finset.mem_union_left _ hi)
    simp [extendSelectedResidueFrequency, hiA]
  have hbOutside : ∀ i, i ∉ S →
      extendSelectedResidueFrequency modulus b i = 0 := by
    intro i hiS
    have hiB : i ∉ b.1.1 := fun hi => hiS (Finset.mem_union_right _ hi)
    simp [extendSelectedResidueFrequency, hiB]
  have haZero : Q • selectedResidueFrequencyPoint modulus a = 0 := by
    exact prod_nsmul_productResidueFrequencyPoint_eq_zero_of_eq_zero_outside
      modulus S (extendSelectedResidueFrequency modulus a) haOutside
  have hbZero : Q • selectedResidueFrequencyPoint modulus b = 0 := by
    exact prod_nsmul_productResidueFrequencyPoint_eq_zero_of_eq_zero_outside
      modulus S (extendSelectedResidueFrequency modulus b) hbOutside
  have hdiffZero : Q • (selectedResidueFrequencyPoint modulus a -
      selectedResidueFrequencyPoint modulus b) = 0 := by
    rw [nsmul_sub, haZero, hbZero, sub_zero]
  have hfinite : IsOfFinAddOrder
      (selectedResidueFrequencyPoint modulus a -
        selectedResidueFrequencyPoint modulus b) :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨Q, hQpos, hdiffZero⟩
  have hdiff : selectedResidueFrequencyPoint modulus a -
      selectedResidueFrequencyPoint modulus b ≠ 0 :=
    sub_ne_zero.mpr ((selectedResidueFrequencyPoint_injective
      modulus hcoprime).ne hab)
  have horder : addOrderOf (selectedResidueFrequencyPoint modulus a -
      selectedResidueFrequencyPoint modulus b) ≤ Q :=
    addOrderOf_le_of_nsmul_eq_zero hQpos hdiffZero
  have hunit : (1 : ℝ) ≤
      (addOrderOf (selectedResidueFrequencyPoint modulus a -
        selectedResidueFrequencyPoint modulus b) : ℝ) *
        ‖selectedResidueFrequencyPoint modulus a -
          selectedResidueFrequencyPoint modulus b‖ := by
    simpa [nsmul_eq_mul] using
      AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder hfinite hdiff
  have hQdist : (1 : ℝ) / Q ≤
      dist (selectedResidueFrequencyPoint modulus a)
        (selectedResidueFrequencyPoint modulus b) := by
    have hQposReal : (0 : ℝ) < Q := by exact_mod_cast hQpos
    rw [dist_eq_norm, div_le_iff₀ hQposReal]
    calc
      (1 : ℝ) ≤
          (addOrderOf (selectedResidueFrequencyPoint modulus a -
            selectedResidueFrequencyPoint modulus b) : ℝ) *
            ‖selectedResidueFrequencyPoint modulus a -
              selectedResidueFrequencyPoint modulus b‖ := hunit
      _ ≤ (Q : ℝ) * ‖selectedResidueFrequencyPoint modulus a -
            selectedResidueFrequencyPoint modulus b‖ := by
        gcongr
      _ = ‖selectedResidueFrequencyPoint modulus a -
            selectedResidueFrequencyPoint modulus b‖ * Q := by ring
  have hQleReal : (Q : ℝ) ≤ N := by exact_mod_cast hQle
  exact (one_div_le_one_div_of_le (by exact_mod_cast hQpos) hQleReal).trans hQdist

/-- Sum Montgomery uncertainty over all selected subsets and apply one
large-sieve inequality to the resulting cross-subset frequency family.
The hypothesis on products is the square-root cutoff in Corollary 2.8,
written without a natural-number square root. -/
theorem montgomery_uncertainty_selected_Ioc_le_largeSieve
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (family : Finset (Finset I)) (m0 N : ℕ) (hsubsets : Nonempty (selectedSubsets family))
    (hproduct : ∀ T U : selectedSubsets family,
      (∏ i ∈ T.1, modulus i) * (∏ i ∈ U.1, modulus i) ≤ N)
    (g : ℕ → ℂ)
    (hg : ∀ n ∈ Finset.Ioc m0 (m0 + N),
      (∃ i, (n : ZMod (modulus i)) ∈ vanishing i) → g n = 0)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i) :
    (∑ T : selectedSubsets family,
        ∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) *
        ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2 ≤
      ((N : ℝ) + N) *
        ∑ n ∈ Finset.Ioc m0 (m0 + N), ‖g n‖ ^ 2 := by
  classical
  let A := selectedResidueFrequencies modulus family
  let point : A → UnitAddCircle :=
    selectedResidueFrequencyPoint modulus
  let T₀ : selectedSubsets family := Classical.choice hsubsets
  have hT₀pos : 0 < ∏ i ∈ T₀.1, modulus i :=
    Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (modulus i))
  have hNpos : 0 < N :=
    lt_of_lt_of_le (Nat.mul_pos hT₀pos hT₀pos) (hproduct T₀ T₀)
  have hdelta : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hsep : ∀ r s : A, r ≠ s →
      (1 : ℝ) / N ≤ dist (point r) (point s) := by
    intro r s hrs
    exact one_div_le_dist_selectedResidueFrequencyPoint
      modulus hcoprime hproduct hrs
  have huncertainty (T : selectedSubsets family) :
      (∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) *
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2 ≤
        ∑ a : {a : residueVectors
            (fun i : {i // i ∈ T.1} => modulus i.1) //
            a ∈ allNonzeroResidueFrequencies},
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
            BoundedGaps.Maynard.unitAddCircleAddChar
              (n • point ⟨T, a⟩)‖ ^ 2 := by
    have hlocal := montgomery_uncertainty_integer_sum
      (modulus := fun i : {i // i ∈ T.1} => modulus i.1)
      (fun i => vanishing i.1) (Finset.Ioc m0 (m0 + N)) g
      (by
        intro n hn hremoved
        obtain ⟨i, hi⟩ := hremoved
        exact hg n hn ⟨i.1, hi⟩)
      (fun i => hnonempty i.1) (fun i => hproper i.1)
    calc
      (∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) *
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2 =
          (∏ i : {i // i ∈ T.1},
            residueRemovalRatio modulus vanishing i.1) *
            ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2 := by
        rw [Finset.prod_coe_sort]
      _ ≤ ∑ a ∈ allNonzeroResidueFrequencies,
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
            productResidueAddChar a
              (residueVectorOfNat
                (fun i : {i // i ∈ T.1} => modulus i.1) n)‖ ^ 2 := by
        simpa only [residueRemovalRatio] using hlocal
      _ = ∑ a : {a : residueVectors
            (fun i : {i // i ∈ T.1} => modulus i.1) //
            a ∈ allNonzeroResidueFrequencies},
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
            BoundedGaps.Maynard.unitAddCircleAddChar
              (n • point ⟨T, a⟩)‖ ^ 2 := by
        simp_rw [point,
          productResidueFrequencyPoint_extendSelectedResidueFrequency]
        calc
          (∑ a ∈ allNonzeroResidueFrequencies,
              ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
                productResidueAddChar a
                  (residueVectorOfNat
                    (fun i : {i // i ∈ T.1} => modulus i.1) n)‖ ^ 2) =
              ∑ a ∈ allNonzeroResidueFrequencies,
                ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
                  BoundedGaps.Maynard.unitAddCircleAddChar
                    (n • productResidueFrequencyPoint a)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _ha
            apply congrArg fun z : ℂ => ‖z‖ ^ 2
            apply Finset.sum_congr rfl
            intro n _hn
            rw [productResidueAddChar_residueVectorOfNat]
          _ = ∑ a : {a : residueVectors
                (fun i : {i // i ∈ T.1} => modulus i.1) //
                a ∈ allNonzeroResidueFrequencies},
              ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
                BoundedGaps.Maynard.unitAddCircleAddChar
                  (n • productResidueFrequencyPoint a.1)‖ ^ 2 := by
            symm
            exact Finset.sum_coe_sort
              (allNonzeroResidueFrequencies
                (modulus := fun i : {i // i ∈ T.1} => modulus i.1))
              (fun a : residueVectors
                  (fun i : {i // i ∈ T.1} => modulus i.1) =>
                ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
                  BoundedGaps.Maynard.unitAddCircleAddChar
                    (n • productResidueFrequencyPoint a)‖ ^ 2)
  have hsumUncertainty :
      (∑ T : selectedSubsets family,
          ∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) *
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2 ≤
        ∑ a : A,
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
            BoundedGaps.Maynard.unitAddCircleAddChar (n • point a)‖ ^ 2 := by
    rw [Finset.sum_mul]
    calc
      (∑ T : selectedSubsets family,
          (∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) *
            ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n‖ ^ 2) ≤
          ∑ T : selectedSubsets family,
            ∑ a : {a : residueVectors
                (fun i : {i // i ∈ T.1} => modulus i.1) //
                a ∈ allNonzeroResidueFrequencies},
              ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
                BoundedGaps.Maynard.unitAddCircleAddChar
                  (n • point ⟨T, a⟩)‖ ^ 2 := by
        exact Finset.sum_le_sum fun T _hT => huncertainty T
      _ = ∑ a : A,
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N), g n *
            BoundedGaps.Maynard.unitAddCircleAddChar (n • point a)‖ ^ 2 := by
        rw [Fintype.sum_sigma]
  have hlarge :=
    BoundedGaps.Maynard.sum_norm_sq_unitAddCircleAddChar_Ioc_le
      point hdelta hsep m0 N g
  have hinvDelta : ((1 : ℝ) / (N : ℝ))⁻¹ = (N : ℝ) := by
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
    field_simp
  exact hsumUncertainty.trans (by
    simpa only [hinvDelta] using hlarge)

/-- Corollary 2.8 specialized to the indicator of the integers surviving
all prescribed residue-class deletions. -/
theorem residueClassSurvivors_selected_ratio_mul_sq_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (family : Finset (Finset I)) (m0 N : ℕ) (hsubsets : Nonempty (selectedSubsets family))
    (hproduct : ∀ T U : selectedSubsets family,
      (∏ i ∈ T.1, modulus i) * (∏ i ∈ U.1, modulus i) ≤ N)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i) :
    (∑ T : selectedSubsets family,
        ∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) *
        (residueClassSurvivors vanishing m0 N).card ^ 2 ≤
      ((N : ℝ) + N) *
        (residueClassSurvivors vanishing m0 N).card := by
  classical
  let E := residueClassSurvivors vanishing m0 N
  let g : ℕ → ℂ := fun n => if n ∈ E then 1 else 0
  have hg : ∀ n ∈ Finset.Ioc m0 (m0 + N),
      (∃ i, (n : ZMod (modulus i)) ∈ vanishing i) → g n = 0 := by
    intro n _hn hremoved
    have hnE : n ∉ E := by
      intro hnE
      have havoid := (Finset.mem_filter.mp hnE).2
      obtain ⟨i, hi⟩ := hremoved
      exact havoid i hi
    simp [g, hnE]
  have hlarge := montgomery_uncertainty_selected_Ioc_le_largeSieve
    modulus hcoprime vanishing family m0 N hsubsets hproduct g hg
      hnonempty hproper
  have hEsubset : E ⊆ Finset.Ioc m0 (m0 + N) := by
    intro n hn
    have hn' := hn
    simp only [E, residueClassSurvivors, Finset.mem_filter] at hn'
    exact hn'.1
  have hfilter :
      (Finset.Ioc m0 (m0 + N)).filter (fun n => n ∈ E) = E := by
    ext n
    constructor
    · intro hn
      exact (Finset.mem_filter.mp hn).2
    · intro hn
      exact Finset.mem_filter.mpr ⟨hEsubset hn, hn⟩
  have hsum : (∑ n ∈ Finset.Ioc m0 (m0 + N), g n) = (E.card : ℂ) := by
    change (∑ n ∈ Finset.Ioc m0 (m0 + N),
      if n ∈ E then (1 : ℂ) else 0) = (E.card : ℂ)
    rw [Finset.sum_boole, hfilter]
  have hnorm (n : ℕ) :
      ‖g n‖ ^ 2 = if n ∈ E then (1 : ℝ) else 0 := by
    by_cases hn : n ∈ E <;> simp [g, hn]
  have henergy :
      (∑ n ∈ Finset.Ioc m0 (m0 + N), ‖g n‖ ^ 2) = (E.card : ℝ) := by
    simp_rw [hnorm]
    rw [Finset.sum_boole, hfilter]
  rw [hsum, henergy] at hlarge
  simpa only [E, Complex.norm_natCast] using hlarge

/-- The cardinality form of Corollary 2.8, after cancelling one factor of
the survivor count. -/
theorem residueClassSurvivors_card_le_selected_ratio
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (family : Finset (Finset I)) (m0 N : ℕ) (hsubsets : Nonempty (selectedSubsets family))
    (hproduct : ∀ T U : selectedSubsets family,
      (∏ i ∈ T.1, modulus i) * (∏ i ∈ U.1, modulus i) ≤ N)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i) :
    ((residueClassSurvivors vanishing m0 N).card : ℝ) ≤
      ((N : ℝ) + N) /
        (∑ T : selectedSubsets family,
          ∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) := by
  classical
  let R : ℝ := ∑ T : selectedSubsets family,
    ∏ i ∈ T.1, residueRemovalRatio modulus vanishing i
  let C : ℝ := (N : ℝ) + N
  let M : ℝ := (residueClassSurvivors vanishing m0 N).card
  have hratioPos (i : I) : 0 < residueRemovalRatio modulus vanishing i := by
    unfold residueRemovalRatio
    exact div_pos
      (by exact_mod_cast Finset.card_pos.mpr (hnonempty i))
      (by exact_mod_cast Nat.sub_pos_of_lt (hproper i))
  let T₀ : selectedSubsets family := Classical.choice hsubsets
  have hRpos : 0 < R := by
    unfold R
    apply Finset.sum_pos
    · intro T _hT
      exact Finset.prod_pos fun i _ => hratioPos i
    · exact ⟨T₀, Finset.mem_univ _⟩
  change M ≤ C / R
  by_cases hMzero : M = 0
  · rw [hMzero]
    positivity
  · have hMpos : 0 < M := lt_of_le_of_ne (by positivity) (Ne.symm hMzero)
    have hraw := residueClassSurvivors_selected_ratio_mul_sq_le
      modulus hcoprime vanishing family m0 N hsubsets hproduct
        hnonempty hproper
    have hcancel : R * M ≤ C := by
      apply le_of_mul_le_mul_right _ hMpos
      simpa only [R, C, M, pow_two, mul_assoc] using hraw
    exact (le_div_iff₀ hRpos).2 (by simpa only [mul_comm] using hcancel)


/-- Keep exactly the subsets whose product of moduli is at most `Q`. -/
noncomputable def productCutoffFamily
    {I : Type*} [Fintype I] [DecidableEq I] (modulus : I → ℕ) (Q : ℕ) :
    Finset (Finset I) :=
  Finset.univ.filter fun T => (∏ i ∈ T, modulus i) ≤ Q

/-- The squarefree-product cutoff version of the upper-bound sieve. -/
theorem residueClassSurvivors_card_le_productCutoff
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Nat.Coprime on modulus))
    (vanishing : ∀ i, Finset (ZMod (modulus i)))
    (m0 N Q : ℕ) (hQ : 1 ≤ Q) (hQN : Q ^ 2 ≤ N)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < modulus i) :
    ((residueClassSurvivors vanishing m0 N).card : ℝ) ≤
      ((N : ℝ) + N) /
        (∑ T ∈ productCutoffFamily modulus Q,
          ∏ i ∈ T, residueRemovalRatio modulus vanishing i) := by
  classical
  have hempty : (∅ : Finset I) ∈ productCutoffFamily modulus Q := by
    simpa [productCutoffFamily] using hQ
  have hprod (T U : selectedSubsets (productCutoffFamily modulus Q)) :
      (∏ i ∈ T.1, modulus i) * (∏ i ∈ U.1, modulus i) ≤ N := by
    have hT := (Finset.mem_filter.mp T.2).2
    have hU := (Finset.mem_filter.mp U.2).2
    exact (Nat.mul_le_mul hT hU).trans (by simpa [pow_two] using hQN)
  have h := residueClassSurvivors_card_le_selected_ratio
    modulus hcoprime vanishing (productCutoffFamily modulus Q) m0 N
    ⟨⟨∅, hempty⟩⟩ hprod hnonempty hproper
  have hsum : (∑ T : selectedSubsets (productCutoffFamily modulus Q),
      ∏ i ∈ T.1, residueRemovalRatio modulus vanishing i) =
      ∑ T ∈ productCutoffFamily modulus Q,
        ∏ i ∈ T, residueRemovalRatio modulus vanishing i :=
    Finset.sum_coe_sort (productCutoffFamily modulus Q)
      (fun T : Finset I => ∏ i ∈ T, residueRemovalRatio modulus vanishing i)
  rwa [hsum] at h

end Erdos380
