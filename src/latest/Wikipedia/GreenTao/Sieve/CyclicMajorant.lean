import Wikipedia.GreenTao.Sieve.MultivariateFourierExpansion

/-!
# The global cyclic Selberg majorant

The prime weight is localized to `greenTaoInterval` in order to unwrap a
positive cyclic progression at the end of the proof.  Its transference
majorant does not need the same localization: outside the interval the prime
weight is zero, so any nonnegative majorant is sufficient.

Keeping the smooth Selberg majorant on the whole standard residue system
removes interval indicators from the linear-forms estimate.  This file
defines that global cyclic majorant, proves pointwise domination from the
existing localized theorem, and reindexes every Boolean CFZ subproduct as a
product over its selected subtype.  The latter is the exact interface needed
to apply the generic finite divisor and Fourier expansions to every exponent
tested by `HasLinearFormsCondition`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The smooth Selberg majorant evaluated on the standard representative of
a W-tricked cyclic residue, without interval localization. -/
noncomputable def SmoothSieveCutoff.cyclicMajorant
    {N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    (R W b : ℕ) (n : ZMod N) : ℝ :=
  χ.majorant R W (wTrickedValue W b n)

theorem SmoothSieveCutoff.cyclicMajorant_nonneg
    {N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 ≤ R) (W b : ℕ) (n : ZMod N) :
    0 ≤ χ.cyclicMajorant R W b n :=
  χ.majorant_nonneg hR W (wTrickedValue W b n)

/-- On the extraction interval the global and localized Selberg majorants
are literally equal. -/
theorem SmoothSieveCutoff.wTrickedMajorant_eq_cyclicMajorant
    {N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    (R W b : ℕ) {n : ZMod N}
    (hn : n.val ∈ greenTaoInterval N) :
    χ.wTrickedMajorant R W b n =
      χ.cyclicMajorant R W b n := by
  simp [SmoothSieveCutoff.wTrickedMajorant,
    Wikipedia.SzemeredisTheorem.wTrickedMajorant,
    SmoothSieveCutoff.cyclicMajorant,
    SmoothSieveCutoff.majorant, hn]

/-- Any pointwise majorization by the localized majorant automatically gives
majorization by the global one.  On the support interval the two agree; off
the interval the localized prime weight vanishes and the global majorant is
nonnegative. -/
theorem wTrickedPrimeWeight_le_cyclicMajorant_of_le_localized
    {N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    {α : ℝ} {R W b : ℕ} (hR : 1 ≤ R)
    (hlocalized :
      ∀ n : ZMod N,
        wTrickedPrimeWeight α W b n ≤
          χ.wTrickedMajorant R W b n) :
    ∀ n : ZMod N,
      wTrickedPrimeWeight α W b n ≤
        χ.cyclicMajorant R W b n := by
  intro n
  by_cases hn : n.val ∈ greenTaoInterval N
  · rw [← χ.wTrickedMajorant_eq_cyclicMajorant R W b hn]
    exact hlocalized n
  · rw [wTrickedPrimeWeight]
    simp only [hn, false_and, if_false]
    exact χ.cyclicMajorant_nonneg hR W b n

/-- The finite type of CFZ forms selected by a Boolean linear-forms
exponent. -/
abbrev SelectedCFZFormIndex {k : ℕ}
    (e : LinearFormsExponent k) :=
  {q : CFZFormIndex k // e q.1 q.2 = true}

/-- A Boolean CFZ subproduct is exactly the product over the subtype of
selected forms. -/
theorem linearFormsProduct_eq_prod_selected
    {k N : ℕ} [NeZero N]
    (ν : ZMod N → ℝ) (e : LinearFormsExponent k)
    (x : CubePoint k N) :
    linearFormsProduct k N ν e x =
      ∏ q : SelectedCFZFormIndex e,
        ν (apLinearForm k N q.1.1 q.1.2 x) := by
  classical
  rw [linearFormsProduct]
  calc
    (∏ j : Fin k, ∏ ω : DeletedCube k j,
        if e j ω then
          ν (apLinearForm k N j ω x)
        else 1) =
        ∏ q : CFZFormIndex k,
          if e q.1 q.2 then
            ν (apLinearForm k N q.1 q.2 x)
          else 1 := by
      exact
        (Fintype.prod_sigma
          (fun q : CFZFormIndex k =>
            if e q.1 q.2 then
              ν (apLinearForm k N q.1 q.2 x)
            else 1)).symm
    (∏ q : CFZFormIndex k,
        if e q.1 q.2 then
          ν (apLinearForm k N q.1 q.2 x)
        else 1) =
        ∏ q ∈
            (Finset.univ.filter fun q : CFZFormIndex k =>
              e q.1 q.2 = true),
          ν (apLinearForm k N q.1 q.2 x) := by
      rw [Finset.prod_filter]
    _ =
        ∏ q : SelectedCFZFormIndex e,
          ν (apLinearForm k N q.1.1 q.1.2 x) := by
      exact Finset.prod_subtype
        (Finset.univ.filter fun q : CFZFormIndex k =>
          e q.1 q.2 = true)
        (by simp)
        (fun q : CFZFormIndex k =>
          ν (apLinearForm k N q.1 q.2 x))

/-- Evaluating the global cyclic majorant on a CFZ form is the natural
W-tricked value used by the divisor expansion. -/
theorem SmoothSieveCutoff.cyclicMajorant_apLinearForm
    {k N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    (R W b : ℕ) (q : CFZFormIndex k)
    (x : CubePoint k N) :
    χ.cyclicMajorant R W b
        (apLinearForm k N q.1 q.2 x) =
      χ.majorant R W
        (cfzWTrickedLinearValue W b q x) :=
  rfl

/-- The exact selected-family form of a cyclic-majorant subproduct. -/
theorem linearFormsProduct_cyclicMajorant_eq_prod_selected
    {k N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    (R W b : ℕ) (e : LinearFormsExponent k)
    (x : CubePoint k N) :
    linearFormsProduct k N
        (χ.cyclicMajorant R W b) e x =
      ∏ q : SelectedCFZFormIndex e,
        χ.majorant R W
          (cfzWTrickedLinearValue W b q.1 x) := by
  rw [linearFormsProduct_eq_prod_selected]
  apply Fintype.prod_congr
  intro q
  rfl

/-- Exact paired-divisor expansion for every Boolean subproduct tested by
the cyclic linear-forms condition.  Unlike the full-family specialization
in `LinearFormsExpansion`, the indexing type here is the subtype selected by
the exponent `e`; no unselected Selberg factor is introduced. -/
theorem SmoothSieveCutoff.mean_linearFormsProduct_cyclicMajorant_eq_divisorExpansion
    {k N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    {R W b : ℕ} (hR : 1 < R) (hb : 0 < b)
    (e : LinearFormsExponent k) :
    mean
        (linearFormsProduct k N
          (χ.cyclicMajorant R W b) e) =
      normalizedSelbergScale χ.normalizer R W ^
          Fintype.card (SelectedCFZFormIndex e) *
        ((Real.log R ^ 2) ^
            Fintype.card (SelectedCFZFormIndex e) *
          ∑ z ∈ smoothDivisorFamilyChoices
              (SelectedCFZFormIndex e) R,
            smoothDivisorFamilyCoefficient χ.toFun R z *
              pairedDivisibilityDensity
                (fun q : SelectedCFZFormIndex e =>
                  cfzWTrickedLinearValue
                    (k := k) (N := N) W b q.1) z) := by
  classical
  rw [show
      linearFormsProduct k N
          (χ.cyclicMajorant R W b) e =
        fun x : CubePoint k N =>
          ∏ q : SelectedCFZFormIndex e,
            χ.majorant R W
              (cfzWTrickedLinearValue W b q.1 x) by
    funext x
    exact
      linearFormsProduct_cyclicMajorant_eq_prod_selected
        χ R W b e x]
  simpa only [SmoothSieveCutoff.majorant] using
    mean_prod_normalizedSelbergMajorant_eq_divisorExpansion
      χ.toFun χ.normalizer hR χ.zero_of_one_le
      (fun q : SelectedCFZFormIndex e =>
        cfzWTrickedLinearValue
          (k := k) (N := N) W b q.1)
      (fun q x => cfzWTrickedLinearValue_pos W hb q.1 x)

/-- Exact multivariate Fourier integral for every cyclic-majorant subproduct.
This is the direct arithmetic side of `HasLinearFormsCondition`: the
remaining sieve estimate may now fix an arbitrary exponent `e` and work
uniformly on its genuinely selected CFZ family. -/
theorem SmoothSieveCutoff.mean_linearFormsProduct_cyclicMajorant_eq_fourierIntegral
    {k N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    {R W b : ℕ} (hR : 1 < R) (hb : 0 < b)
    (e : LinearFormsExponent k) :
    (mean
        (linearFormsProduct k N
          (χ.cyclicMajorant R W b) e) : ℂ) =
      (normalizedSelbergScale χ.normalizer R W : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        (((Real.log R ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
          ∫ tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ),
            χ.divisorExpansionFourierIntegrand R
              (fun z =>
                pairedDivisibilityDensity
                  (fun q : SelectedCFZFormIndex e =>
                    cfzWTrickedLinearValue
                      (k := k) (N := N) W b q.1) z)
              tu ∂(MeasureTheory.volume.prod
                MeasureTheory.volume)) := by
  classical
  have hmean :=
    χ.mean_linearFormsProduct_cyclicMajorant_eq_divisorExpansion
      (k := k) (N := N) (R := R) (W := W) (b := b)
      hR hb e
  have hsum :=
    χ.sum_smoothDivisorFamilyCoefficient_eq_integral R
      (fun z =>
        pairedDivisibilityDensity
          (fun q : SelectedCFZFormIndex e =>
            cfzWTrickedLinearValue
              (k := k) (N := N) W b q.1) z)
  calc
    (mean
        (linearFormsProduct k N
          (χ.cyclicMajorant R W b) e) : ℂ) =
        ((normalizedSelbergScale χ.normalizer R W ^
              Fintype.card (SelectedCFZFormIndex e) *
            ((Real.log R ^ 2) ^
                Fintype.card (SelectedCFZFormIndex e) *
              ∑ z ∈ smoothDivisorFamilyChoices
                  (SelectedCFZFormIndex e) R,
                smoothDivisorFamilyCoefficient χ.toFun R z *
                  pairedDivisibilityDensity
                    (fun q : SelectedCFZFormIndex e =>
                      cfzWTrickedLinearValue
                        (k := k) (N := N) W b q.1) z) : ℝ) : ℂ) := by
      exact congrArg (fun x : ℝ => (x : ℂ)) hmean
    _ =
        (normalizedSelbergScale χ.normalizer R W : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
          (((Real.log R ^ 2 : ℝ) : ℂ) ^
              Fintype.card (SelectedCFZFormIndex e) *
            ((∑ z ∈ smoothDivisorFamilyChoices
                  (SelectedCFZFormIndex e) R,
                smoothDivisorFamilyCoefficient χ.toFun R z *
                  pairedDivisibilityDensity
                    (fun q : SelectedCFZFormIndex e =>
                      cfzWTrickedLinearValue
                        (k := k) (N := N) W b q.1) z : ℝ) : ℂ)) := by
      norm_cast
    _ = _ := by
      rw [hsum]

end Wikipedia.SzemeredisTheorem
