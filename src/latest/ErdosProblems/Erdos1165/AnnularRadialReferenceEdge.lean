/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialOneStepRow
import ErdosProblems.Erdos1165.AnnularRadialTerminalRow
import ErdosProblems.Erdos1165.AnnularRadialProfileWords
import ErdosProblems.Erdos1165.AnnularRadialChainLower

/-!
# Scalar reference rows for the chronological radial word

The literal radial word sees one endpoint-integrated stopped row at each
successive different-boundary hit.  This file packages the ideal label-chain
row and its uniform large-scale lower approximation.  Unsupported label
pairs have weight zero, so the resulting comparison is valid for all pairs;
no pathwise adjacency premise is hidden in the row theorem.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AnnularRadialReferenceEdge

open AnnularRadialLabelWord AnnularRadialOneStepRow
  AnnularRadialTerminalRow AnnularOffspringKernelRadial
  AnnularRadialProfileWords AnnularRadialChainLower
  ExcursionTransition MarkedBoundaryVisitKernel ThickPoint

noncomputable section

/-- The ideal nearest-neighbour label-chain row.  Regular levels use the
critical half row.  At level `n`, an inward child has mass `1-p_n` and the
outward terminal decision has mass `p_n`; the return from `n+1` is certain. -/
def annularIdealEdge (n : ℕ) :
    Fin (n + 2) → Fin (n + 2) → ℝ≥0∞ := fun source target ↦
  if (source : ℕ) = 0 then 0
  else if (source : ℕ) < n then
    if Nat.dist (source : ℕ) (target : ℕ) = 1 then
      ENNReal.ofReal (1 / 2 : ℝ)
    else 0
  else if (source : ℕ) = n then
    if (target : ℕ) = n + 1 then
      ENNReal.ofReal (1 - terminalSuccess n)
    else if (target : ℕ) + 1 = n then
      ENNReal.ofReal (terminalSuccess n)
    else 0
  else if (target : ℕ) = n then 1 else 0

/-- The row paid for by the proved potential estimates.  A regular decision
loses `1-n⁻⁶`; a terminal decision loses `1-n⁻⁵`. -/
def annularLowerEdge (n : ℕ) :
    Fin (n + 2) → Fin (n + 2) → ℝ≥0∞ := fun source target ↦
  if (source : ℕ) = 0 then 0
  else if (source : ℕ) < n then
    if Nat.dist (source : ℕ) (target : ℕ) = 1 then
      ENNReal.ofReal ((1 - 1 / (n : ℝ) ^ 6) / 2)
    else 0
  else if (source : ℕ) = n then
    if (target : ℕ) = n + 1 then
      ENNReal.ofReal
        ((1 - 1 / (n : ℝ) ^ 5) * (1 - terminalSuccess n))
    else if (target : ℕ) + 1 = n then
      ENNReal.ofReal
        ((1 - 1 / (n : ℝ) ^ 5) * terminalSuccess n)
    else 0
  else if (target : ℕ) = n then 1 else 0

private theorem dist_eq_one_cases {a b : ℕ} (h : Nat.dist a b = 1) :
    b = a + 1 ∨ b + 1 = a := by
  unfold Nat.dist at h
  by_cases hab : a ≤ b
  · have hzero : a - b = 0 := Nat.sub_eq_zero_of_le hab
    rw [hzero, Nat.zero_add] at h
    exact Or.inl (by omega)
  · have hba : b ≤ a := by omega
    have hzero : b - a = 0 := Nat.sub_eq_zero_of_le hba
    rw [hzero, Nat.add_zero] at h
    exact Or.inr (by omega)

/-- The actual endpoint-summed chronological row dominates
`annularLowerEdge`, uniformly in the entrance point and the center. -/
theorem eventually_annularLowerEdge_le_endpoint_sum :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 2 ≤ n) (center : Point)
      (source target : Fin (n + 2)) (start : Point),
      start ∈ radialBoundary n center source →
      annularLowerEdge n source target ≤
        ∑ endpoint : RadialBoundaryPoint n center target,
          skeletonExitKernel (otherRadialBoundaries n center source)
            start endpoint.1 := by
  filter_upwards
      [eventually_radialOneStepKernelENNReal_internal_lower_inv_pow_six,
        eventually_radialOneStepKernelENNReal_terminal_lower_inv_pow_five,
        eventually_ge_atTop 2]
      with n hinternal hterminal hn
  intro _ center source target start hstart
  rw [sum_skeletonExitKernel_otherRadialBoundaries_eq]
  by_cases hsource0 : (source : ℕ) = 0
  · simp [annularLowerEdge, hsource0]
  by_cases hsourceInternal : (source : ℕ) < n
  · rw [annularLowerEdge, if_neg hsource0, if_pos hsourceInternal]
    by_cases hadjacent : Nat.dist (source : ℕ) (target : ℕ) = 1
    · rw [if_pos hadjacent]
      rcases dist_eq_one_cases hadjacent with hin | hout
      · have hsourcePos : 0 < (source : ℕ) := by omega
        have hsourceBound : (source : ℕ) + 1 ≤ n := by omega
        have htarget : target =
            ⟨(source : ℕ) + 1, by omega⟩ := Fin.ext (by simpa using hin)
        have hsource : (⟨(source : ℕ), by omega⟩ : Fin (n + 2)) = source :=
          Fin.eta source _
        have hstart' : start ∈ radialBoundary n center
            (⟨(source : ℕ), by omega⟩ : Fin (n + 2)) := by
          rw [hsource]
          exact hstart
        calc
          ENNReal.ofReal ((1 - 1 / (n : ℝ) ^ 6) / 2) ≤
              radialOneStepKernelENNReal n center
                ⟨(source : ℕ), by omega⟩
                ⟨(source : ℕ) + 1, by omega⟩ start :=
            (hinternal (source : ℕ) hsourcePos hsourceBound
              center start (by simpa [radialBoundary] using hstart')).1
          _ = radialOneStepKernelENNReal n center source target start := by
            congr 2
            exact hin.symm
      · have hsourcePos : 0 < (source : ℕ) := by omega
        have hsourceBound : (source : ℕ) + 1 ≤ n := by omega
        have htarget : target =
            ⟨(source : ℕ) - 1, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        have hsource : (⟨(source : ℕ), by omega⟩ : Fin (n + 2)) = source :=
          Fin.eta source _
        have hstart' : start ∈ radialBoundary n center
            (⟨(source : ℕ), by omega⟩ : Fin (n + 2)) := by
          rw [hsource]
          exact hstart
        calc
          ENNReal.ofReal ((1 - 1 / (n : ℝ) ^ 6) / 2) ≤
              radialOneStepKernelENNReal n center
                ⟨(source : ℕ), by omega⟩
                ⟨(source : ℕ) - 1, by omega⟩ start :=
            (hinternal (source : ℕ) hsourcePos hsourceBound
              center start (by simpa [radialBoundary] using hstart')).2
          _ = radialOneStepKernelENNReal n center source target start := by
            congr 2
            omega
    · simp [hadjacent]
  · have hsourceGe : n ≤ (source : ℕ) := by omega
    by_cases hsourceTerminal : (source : ℕ) = n
    · rw [annularLowerEdge, if_neg hsource0, if_neg hsourceInternal,
        if_pos hsourceTerminal]
      have hsourceEq : source = ⟨n, by omega⟩ := Fin.ext hsourceTerminal
      by_cases htargetIn : (target : ℕ) = n + 1
      · rw [if_pos htargetIn]
        have htargetEq : target = ⟨n + 1, by omega⟩ := Fin.ext htargetIn
        simpa [hsourceEq, htargetEq] using
          (hterminal center start (by simpa [hsourceEq] using hstart)).1
      · rw [if_neg htargetIn]
        by_cases htargetOut : (target : ℕ) + 1 = n
        · rw [if_pos htargetOut]
          have htargetEq : target = ⟨n - 1, by omega⟩ := by
            apply Fin.ext
            change (target : ℕ) = n - 1
            omega
          simpa [hsourceEq, htargetEq] using
            (hterminal center start (by simpa [hsourceEq] using hstart)).2
        · simp [htargetOut]
    · have hsourceInner : (source : ℕ) = n + 1 := by omega
      rw [annularLowerEdge, if_neg hsource0, if_neg hsourceInternal,
        if_neg hsourceTerminal]
      by_cases htarget : (target : ℕ) = n
      · rw [if_pos htarget]
        have hsourceEq : source = ⟨n + 1, by omega⟩ := Fin.ext hsourceInner
        have htargetEq : target = ⟨n, by omega⟩ := Fin.ext htarget
        simpa [hsourceEq, htargetEq] using
          (radialOneStepKernelENNReal_terminal_return_eq_one
            hn center start (by simpa [hsourceEq] using hstart)).ge
      · simp [htarget]

/-- The common factor charged to every transition of a bounded radial word. -/
def annularCommonRowLoss (n : ℕ) : ℝ := 1 - 1 / (n : ℝ) ^ 5

lemma annularCommonRowLoss_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ annularCommonRowLoss n := by
  unfold annularCommonRowLoss
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 5 := one_le_pow₀ hnR
  exact sub_nonneg.mpr ((div_le_one (by positivity)).2 hpow)

lemma annularCommonRowLoss_le_one (n : ℕ) :
    annularCommonRowLoss n ≤ 1 := by
  unfold annularCommonRowLoss
  exact sub_le_self _ (by positivity)

private lemma inv_pow_six_le_inv_pow_five {n : ℕ} (hn : 1 ≤ n) :
    1 / (n : ℝ) ^ 6 ≤ 1 / (n : ℝ) ^ 5 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ 5 ≤ (n : ℝ) ^ 6 := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (by positivity) hnR
  exact one_div_le_one_div_of_le (by positivity) hpow

/-- Each proved row contains one copy of the common loss times its ideal
counterpart.  For the deterministic terminal return we deliberately charge
the common loss as well; this only makes the later uniform word bound easier. -/
theorem commonLoss_mul_annularIdealEdge_le_annularLowerEdge
    {n : ℕ} (hn : 2 ≤ n) (source target : Fin (n + 2)) :
    ENNReal.ofReal (annularCommonRowLoss n) *
        annularIdealEdge n source target ≤
      annularLowerEdge n source target := by
  have hloss0 := annularCommonRowLoss_nonneg (show 1 ≤ n by omega)
  have hloss1 := annularCommonRowLoss_le_one n
  have herr := inv_pow_six_le_inv_pow_five (show 1 ≤ n by omega)
  have hn0 : n ≠ 0 := by omega
  by_cases hsource0 : (source : ℕ) = 0
  · simp [annularIdealEdge, annularLowerEdge, hsource0]
  by_cases hsourceInternal : (source : ℕ) < n
  · simp only [annularIdealEdge, annularLowerEdge, hsource0,
      hsourceInternal, ↓reduceIte]
    by_cases hadjacent : Nat.dist (source : ℕ) (target : ℕ) = 1
    · simp only [hadjacent, ↓reduceIte, ← ENNReal.ofReal_mul hloss0]
      apply ENNReal.ofReal_le_ofReal
      unfold annularCommonRowLoss
      nlinarith
    · simp [hadjacent]
  · by_cases hsourceTerminal : (source : ℕ) = n
    · simp only [annularIdealEdge, annularLowerEdge, hsource0,
        hsourceInternal, hsourceTerminal, ↓reduceIte]
      by_cases htargetIn : (target : ℕ) = n + 1
      · simp only [htargetIn, ↓reduceIte]
        simp only [hn0, lt_self_iff_false, ↓reduceIte]
        rw [← ENNReal.ofReal_mul hloss0]
        rfl
      · simp only [htargetIn, ↓reduceIte]
        by_cases htargetOut : (target : ℕ) + 1 = n
        · simp only [htargetOut, ↓reduceIte]
          simp only [hn0, lt_self_iff_false, ↓reduceIte]
          rw [← ENNReal.ofReal_mul hloss0]
          rfl
        · simp [htargetOut]
    · have hsourceInner : (source : ℕ) = n + 1 := by omega
      simp only [annularIdealEdge, annularLowerEdge, hsource0,
        hsourceInternal, hsourceTerminal, ↓reduceIte]
      by_cases htarget : (target : ℕ) = n
      · simp only [htarget, ↓reduceIte, mul_one]
        simpa using ENNReal.ofReal_le_one.mpr hloss1
      · simp [htarget]

/-- Pointwise scaled row bounds multiply down an arbitrary finite label
chain. -/
theorem commonLoss_pow_mul_idealReference_le_lowerReference
    {n : ℕ} (hn : 2 ≤ n) :
    ∀ (source : Fin (n + 2)) (targets : List (Fin (n + 2))),
      (ENNReal.ofReal (annularCommonRowLoss n)) ^ targets.length *
          radialChainReference (annularIdealEdge n) source targets ≤
        radialChainReference (annularLowerEdge n) source targets
  | source, [] => by simp [radialChainReference]
  | source, target :: tail => by
      rw [List.length_cons, pow_succ, radialChainReference,
        radialChainReference]
      have hhead := commonLoss_mul_annularIdealEdge_le_annularLowerEdge
        hn source target
      have htail := commonLoss_pow_mul_idealReference_le_lowerReference
        hn target tail
      calc
        ENNReal.ofReal (annularCommonRowLoss n) ^ tail.length *
              ENNReal.ofReal (annularCommonRowLoss n) *
              (annularIdealEdge n source target *
                radialChainReference (annularIdealEdge n) target tail) =
            (ENNReal.ofReal (annularCommonRowLoss n) *
                annularIdealEdge n source target) *
              (ENNReal.ofReal (annularCommonRowLoss n) ^ tail.length *
                radialChainReference (annularIdealEdge n) target tail) := by
          ac_rfl
        _ ≤ annularLowerEdge n source target *
              radialChainReference (annularLowerEdge n) target tail :=
          mul_le_mul hhead htail bot_le bot_le

/-- The common loss remains at least one half over the generous bounded-word
cutoff `8 n³+1`. -/
theorem half_le_commonLoss_pow_profileRadialWordMaxTransitions
    {n : ℕ} (hn : 5 ≤ n) :
    (1 / 2 : ℝ) ≤
      annularCommonRowLoss n ^ profileRadialWordMaxTransitions n := by
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by positivity
  have hpowThree : (1 : ℝ) ≤ (n : ℝ) ^ 3 := by
    have : (1 : ℝ) ≤ n := by linarith
    exact one_le_pow₀ this
  have hdegree :
      2 * ((profileRadialWordMaxTransitions n : ℕ) : ℝ) ≤
        (n : ℝ) ^ 5 := by
    rw [show ((profileRadialWordMaxTransitions n : ℕ) : ℝ) =
        8 * (n : ℝ) ^ 3 + 1 by
      simp [profileRadialWordMaxTransitions]]
    have hnSq : (25 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hnCube0 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
    have htwentyFive : 25 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 5 := by
      calc
        25 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hnSq hnCube0
        _ = (n : ℝ) ^ 5 := by ring
    nlinarith
  have hepsilon : 1 / (n : ℝ) ^ 5 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have hnOne : (1 : ℝ) ≤ n := by linarith
    exact one_le_pow₀ hnOne
  have hlinear : (1 / 2 : ℝ) ≤
      1 - (profileRadialWordMaxTransitions n : ℕ) *
        (1 / (n : ℝ) ^ 5) := by
    have hratio :
        ((profileRadialWordMaxTransitions n : ℕ) : ℝ) /
            (n : ℝ) ^ 5 ≤ 1 / 2 := by
      rw [div_le_iff₀ (pow_pos hnPos 5)]
      nlinarith
    push_cast
    rw [show ((profileRadialWordMaxTransitions n : ℕ) : ℝ) *
        (1 / (n : ℝ) ^ 5) =
          ((profileRadialWordMaxTransitions n : ℕ) : ℝ) /
            (n : ℝ) ^ 5 by ring]
    linarith
  exact hlinear.trans
    (AppendixDecoupling.one_sub_nat_mul_le_pow_one_sub
      hepsilon (profileRadialWordMaxTransitions n))

/-- Every bounded radial word keeps at least half of its ideal reference
mass after all regular and terminal row errors are charged. -/
theorem ofReal_half_mul_idealReference_le_lowerReference
    {n : ℕ} (hn : 5 ≤ n)
    (word : BoundedRadialLabelWord n (profileRadialWordMaxTransitions n)) :
    ENNReal.ofReal (1 / 2 : ℝ) *
        radialChainReference (annularIdealEdge n)
          (word.2.level ⟨0, by omega⟩) word.2.toList.tail ≤
      radialChainReference (annularLowerEdge n)
        (word.2.level ⟨0, by omega⟩) word.2.toList.tail := by
  have hloss0 := annularCommonRowLoss_nonneg (show 1 ≤ n by omega)
  have hloss1 := annularCommonRowLoss_le_one n
  have hlength : word.2.toList.tail.length = (word.1 : ℕ) := by
    have := word.2.length_toList
    simpa using congrArg (fun l : List (Fin (n + 2)) ↦ l.tail.length) rfl
  have hwordBound : (word.1 : ℕ) ≤ profileRadialWordMaxTransitions n := by
    omega
  have hpowReal := half_le_commonLoss_pow_profileRadialWordMaxTransitions hn
  have hpowENN : ENNReal.ofReal (1 / 2 : ℝ) ≤
      ENNReal.ofReal (annularCommonRowLoss n) ^ word.2.toList.tail.length := by
    calc
      ENNReal.ofReal (1 / 2 : ℝ) ≤
          ENNReal.ofReal
            (annularCommonRowLoss n ^ profileRadialWordMaxTransitions n) :=
        ENNReal.ofReal_le_ofReal hpowReal
      _ = ENNReal.ofReal (annularCommonRowLoss n) ^
          profileRadialWordMaxTransitions n := by
        rw [ENNReal.ofReal_pow hloss0]
      _ ≤ ENNReal.ofReal (annularCommonRowLoss n) ^
          word.2.toList.tail.length := by
        apply pow_le_pow_of_le_one bot_le
          (ENNReal.ofReal_le_one.mpr hloss1)
        simpa only [hlength] using hwordBound
  calc
    ENNReal.ofReal (1 / 2 : ℝ) *
          radialChainReference (annularIdealEdge n)
            (word.2.level ⟨0, by omega⟩) word.2.toList.tail ≤
        ENNReal.ofReal (annularCommonRowLoss n) ^ word.2.toList.tail.length *
          radialChainReference (annularIdealEdge n)
            (word.2.level ⟨0, by omega⟩) word.2.toList.tail :=
      mul_le_mul_of_nonneg_right hpowENN bot_le
    _ ≤ _ := commonLoss_pow_mul_idealReference_le_lowerReference
      (show 2 ≤ n by omega) _ _

end

end Erdos1165.AnnularRadialReferenceEdge
