import ErdosProblems.Erdos622.TwoLargeForest
import ErdosProblems.Erdos622.ShiftedGaussian
import ErdosProblems.Erdos622.ShiftedWindowCount
import ErdosProblems.Erdos622.OriginalSideForest
import ErdosProblems.Erdos622.CompactBoundedForest
import ErdosProblems.Erdos622.BoundedInternal
import ErdosProblems.Erdos622.IntermediateImbalance

namespace Erdos622
namespace TwoLargeFinish

open Filter Finset Real Set
open scoped BigOperators Topology SimpleGraph

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Adapter from the raw powerset-filter form returned by the sampling
lemmas to the named event count used by the finish endpoints.  Keeping this
conversion in one module avoids elaboration differences between independently
generated decidability instances at downstream call sites. -/
lemma almostBipartiteCount_le_of_filter_count_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : Finset V → Prop} {b : ℝ}
    (h : ((((Finset.univ : Finset V).powerset.filter P).card : ℝ)) ≤ b) :
    (almostBipartiteCount (Finset.univ : Finset V) P : ℝ) ≤ b := by
  simpa only [almostBipartiteCount, almostBipartiteEvent] using h

lemma matching_floor_induce_internalGraph'
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A S : Finset V} {u : ℝ}
    (hu : 0 ≤ u)
    (h : RandomCover.HasMatchingAtLeast (internalGraph G A) S u) :
    ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A) ⌊u⌋₊ := by
  apply RandomCover.HasMatchingAtLeast.induce_internalGraph
  obtain ⟨N, hNmatching, hNS, hNcard⟩ := h
  exact ⟨N, hNmatching, hNS, (Nat.floor_le hu).trans hNcard⟩

lemma matching_floor_capacity'
    {c : ℕ} {s eps sigma : ℝ}
    (hs : 0 < s) (hsigma : 0 < sigma)
    (hepsc : eps * c ≤ sigma * s / 2)
    (hlarge : 1 ≤ sigma * s / 2) :
    ((c : ℝ) / s / 4 - sigma) * s ≤
      (⌊(1 / 4 - eps) * (c : ℝ)⌋₊ : ℝ) := by
  have hthreshold :
      ((c : ℝ) / s / 4 - sigma) * s + 1 ≤
        (1 / 4 - eps) * (c : ℝ) := by
    field_simp [ne_of_gt hs]
    nlinarith
  have hfloor := Nat.lt_floor_add_one ((1 / 4 - eps) * (c : ℝ))
  linarith

lemma reciprocal_four_mem_compact
    {K M₀ : ℕ} (hK : 0 < K) (hM₀ : 0 < M₀) {beta : ℝ}
    (hbeta : beta ∈ Set.Icc (1 / (4 * K : ℝ)) (M₀ : ℝ)) :
    4 / beta ∈
      Set.Icc (min (1 / (4 * K : ℝ)) (4 / (M₀ : ℝ)))
        (max (M₀ : ℝ) (16 * K : ℝ)) := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hM₀real : (0 : ℝ) < M₀ := by exact_mod_cast hM₀
  have heta₀ : (0 : ℝ) < 1 / (4 * K : ℝ) := by positivity
  have hbetaPos : 0 < beta := heta₀.trans_le hbeta.1
  constructor
  · apply (min_le_right _ _).trans
    rw [div_le_div_iff₀ hM₀real hbetaPos]
    nlinarith [hbeta.2]
  · apply le_max_of_le_right
    calc
      4 / beta ≤ 4 / (1 / (4 * K : ℝ)) := by
        rw [div_le_div_iff₀ hbetaPos heta₀]
        nlinarith [hbeta.1]
      _ = 16 * K := by field_simp [hKreal.ne'] <;> norm_num

theorem four_failure_count_le'
    {V : Type*} [Fintype V] [DecidableEq V]
    (F₁ F₂ F₃ F₄ : Finset V → Prop) {δ₁ δ₂ δ₃ δ₄ : ℝ}
    (h₁ : (almostBipartiteCount (Finset.univ : Finset V) F₁ : ℝ) ≤
      δ₁ * (2 : ℝ) ^ Fintype.card V)
    (h₂ : (almostBipartiteCount (Finset.univ : Finset V) F₂ : ℝ) ≤
      δ₂ * (2 : ℝ) ^ Fintype.card V)
    (h₃ : (almostBipartiteCount (Finset.univ : Finset V) F₃ : ℝ) ≤
      δ₃ * (2 : ℝ) ^ Fintype.card V)
    (h₄ : (almostBipartiteCount (Finset.univ : Finset V) F₄ : ℝ) ≤
      δ₄ * (2 : ℝ) ^ Fintype.card V) :
    (almostBipartiteCount (Finset.univ : Finset V)
      (fun S ↦ F₁ S ∨ F₂ S ∨ F₃ S ∨ F₄ S) : ℝ) ≤
        (δ₁ + δ₂ + δ₃ + δ₄) * (2 : ℝ) ^ Fintype.card V := by
  have h12 := almostBipartiteCount_or_le
    (Finset.univ : Finset V) F₁ F₂
  have h34 := almostBipartiteCount_or_le
    (Finset.univ : Finset V) F₃ F₄
  have houter := almostBipartiteCount_or_le
    (Finset.univ : Finset V) (fun S ↦ F₁ S ∨ F₂ S)
      (fun S ↦ F₃ S ∨ F₄ S)
  have houter' :
      almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ F₁ S ∨ F₂ S ∨ F₃ S ∨ F₄ S) ≤
        almostBipartiteCount (Finset.univ : Finset V)
            (fun S ↦ F₁ S ∨ F₂ S) +
          almostBipartiteCount (Finset.univ : Finset V)
            (fun S ↦ F₃ S ∨ F₄ S) := by
    simpa only [or_assoc] using houter
  norm_cast at houter'
  have hleft :
      (almostBipartiteCount (Finset.univ : Finset V)
        (fun S ↦ F₁ S ∨ F₂ S) : ℝ) ≤
          (δ₁ + δ₂) * (2 : ℝ) ^ Fintype.card V := by
    calc
      _ ≤ (almostBipartiteCount (Finset.univ : Finset V) F₁ : ℝ) +
          almostBipartiteCount (Finset.univ : Finset V) F₂ := by exact_mod_cast h12
      _ ≤ _ := add_le_add h₁ h₂
      _ = _ := by ring
  have hright :
      (almostBipartiteCount (Finset.univ : Finset V)
        (fun S ↦ F₃ S ∨ F₄ S) : ℝ) ≤
          (δ₃ + δ₄) * (2 : ℝ) ^ Fintype.card V := by
    calc
      _ ≤ (almostBipartiteCount (Finset.univ : Finset V) F₃ : ℝ) +
          almostBipartiteCount (Finset.univ : Finset V) F₄ := by exact_mod_cast h34
      _ ≤ _ := add_le_add h₃ h₄
      _ = _ := by ring
  calc
    _ ≤ (almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ F₁ S ∨ F₂ S) : ℝ) +
        almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ F₃ S ∨ F₄ S) := by exact_mod_cast houter'
    _ ≤ _ := add_le_add hleft hright
    _ = _ := by ring

theorem goodSample_count_of_three_forest_failures'
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {A B T A₀ B₀ : Finset V}
    (P F₁ F₂ F₃ F₄ : Finset V → Prop)
    {leftBalanced leftOriginal right : ℕ}
    {R δ₁ δ₂ δ₃ δ₄ : ℝ}
    (hcut : IsCut A B) (hTA : T ⊆ A)
    (hA₀ : A₀ = A \ T) (hB₀ : B₀ = B ∪ T)
    (hleftBalanced : ∀ S, ¬ F₁ S →
      ContainsLinearForestWith (G.induce (S : Set V))
        (restrictedPart S A₀) leftBalanced)
    (hleftOriginal : ∀ S, ¬ F₂ S →
      ContainsLinearForestWith (G.induce (S : Set V))
        (restrictedPart S A) leftOriginal)
    (hright : ∀ S, ¬ F₃ S →
      ContainsLinearForestWith (G.induce (S : Set V))
        (restrictedPart S B₀) right)
    (hwindows : ∀ S, P S → ¬ F₄ S →
      (S ∩ A₀).card + 2 * (S ∩ T).card ≤
          (S ∩ B₀).card + max leftBalanced leftOriginal ∧
        (S ∩ B₀).card ≤
          (S ∩ A₀).card + max (2 * (S ∩ T).card) right)
    (hwindow : R ≤
      (almostBipartiteCount (Finset.univ : Finset V) P : ℝ))
    (h₁ : (almostBipartiteCount (Finset.univ : Finset V) F₁ : ℝ) ≤
      δ₁ * (2 : ℝ) ^ Fintype.card V)
    (h₂ : (almostBipartiteCount (Finset.univ : Finset V) F₂ : ℝ) ≤
      δ₂ * (2 : ℝ) ^ Fintype.card V)
    (h₃ : (almostBipartiteCount (Finset.univ : Finset V) F₃ : ℝ) ≤
      δ₃ * (2 : ℝ) ^ Fintype.card V)
    (h₄ : (almostBipartiteCount (Finset.univ : Finset V) F₄ : ℝ) ≤
      δ₄ * (2 : ℝ) ^ Fintype.card V) :
    R - (δ₁ + δ₂ + δ₃ + δ₄) *
        (2 : ℝ) ^ Fintype.card V ≤
      (almostBipartiteCount (Finset.univ : Finset V)
        (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  let Failure : Finset V → Prop := fun S ↦ F₁ S ∨ F₂ S ∨ F₃ S ∨ F₄ S
  have hfailure := four_failure_count_le' F₁ F₂ F₃ F₄ h₁ h₂ h₃ h₄
  apply AlmostBipartiteRegimeCounts.goodSample_count_of_window_failure
    G P Failure R (δ₁ + δ₂ + δ₃ + δ₄) _ hwindow hfailure
  intro S _hS hPS hnot
  apply TwoLargeForest.IsKGoodSample.of_balanced_transfer_three_forests
    hcut hTA hA₀ hB₀
    (hleftBalanced S (by intro h; exact hnot (Or.inl h)))
    (hleftOriginal S (by intro h; exact hnot (Or.inr (Or.inl h))))
    (hright S (by intro h; exact hnot (Or.inr (Or.inr (Or.inl h)))))
  · exact (hwindows S hPS (by intro h; exact hnot (Or.inr (Or.inr (Or.inr h))))).1
  · exact (hwindows S hPS (by intro h; exact hnot (Or.inr (Or.inr (Or.inr h))))).2

theorem swapped_large_finish
    {delta delta₀ margin eta M rho sigma eps : ℝ}
    {K₀ n : ℕ}
    (G : SimpleGraph (Fin (2 * n)))
    (A B T A₀ B₀ C D : Finset (Fin (2 * n)))
    (JB : SimpleGraph (Fin (2 * n)))
    (hdelta : 0 < delta) (hdelta₀ : delta₀ = delta / 4)
    (hmargin : 0 < margin)
    (heta : 0 < eta) (hetaDef : eta ≤ 4 / (D.card / Real.sqrt n))
    (hMbound : 4 / (D.card / Real.sqrt n) ≤ M)
    (hrho : 0 < rho) (hsigma : 0 < sigma) (htwoSigma : 2 * sigma ≤ rho)
    (hepsQuarter : eps < 1 / 4)
    (hnpos : 0 < n) (hnRound : 1 ≤ sigma * Real.sqrt n / 2)
    (hAB : IsAlmostBipartiteCut G A B)
    (hTA : T ⊆ A) (hTcard : T.card = A.card - n)
    (hA₀ : A₀ = A \ T) (hB₀ : B₀ = B ∪ T)
    (hcut₀ : IsCut A₀ B₀) (hA₀card : A₀.card = n)
    (hB₀card : B₀.card = n)
    (hD : IsMinimumVertexCoverOn G B₀ D)
    (hJBG : JB ≤ G) (hJBsupp : JB.support ⊆ (A₀ : Set (Fin (2 * n))))
    (hdUpper : A.card - n ≤ Nat.sqrt n)
    (hkappaUpper : ((A.card - n : ℕ) : ℝ) / Real.sqrt n ≤ 1)
    (hleftCapBeta :
      (1 / ((D.card : ℝ) / Real.sqrt n) - sigma) * Real.sqrt n ≤
        K₀)
    (hleftInternalBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun
          S : Finset (Fin (2 * n)) ↦
        ¬ ContainsLinearForestWith (JB.induce (S : Set (Fin (2 * n))))
          Finset.univ K₀).card : ℝ)) ≤
        delta₀ * (2 : ℝ) ^ (2 * n))
    (hmatchingBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun
          S : Finset (Fin (2 * n)) ↦
        ¬ RandomCover.HasMatchingAtLeast (internalGraph G B₀) S
          ((1 / 4 - eps) * D.card)).card : ℝ)) ≤
        delta₀ * (2 : ℝ) ^ (2 * n))
    (hepsD : eps * (D.card : ℝ) ≤ sigma * Real.sqrt n / 2)
    (htransferBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun
          S : Finset (Fin (2 * n)) ↦
        sigma / 2 * (Nat.sqrt n : ℝ) ≤
          |SamplingSuitable.intersectionCount T S -
            (T.card : ℝ) / 2|).card : ℝ)) ≤
        delta₀ * (2 : ℝ) ^ (2 * n))
    (horiginalBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun
          S : Finset (Fin (2 * n)) ↦
        ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
          (restrictedPart S A) (20 * (A.card - n))).card : ℝ)) ≤
        delta₀ * (2 : ℝ) ^ (2 * n))
    (hnWindow : ∀ alpha ∈ Set.Icc eta M,
        ∀ kappa ∈ Set.Icc (0 : ℝ) 1,
          (1 / 2 : ℝ) + margin / 2 <
            (almostBipartiteCount
              (Finset.univ : Finset (Fin (2 * n)))
              (fun S ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
                ((S ∩ B₀).card + (n - (S ∩ A₀).card)) ∈
                  Set.Icc
                    (-((max (alpha / 4 - kappa) (15 * kappa) - rho) *
                      Real.sqrt 2))
                    ((max (1 / alpha) kappa - rho) * Real.sqrt 2)) : ℝ) /
              (2 : ℝ) ^ (2 * n)) :
    ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
      (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
        (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  let beta : ℝ := (D.card : ℝ) / Real.sqrt n
  let alpha : ℝ := 4 / beta
  let kappa : ℝ := ((A.card - n : ℕ) : ℝ) / Real.sqrt n
  have hbeta : 0 < beta := by
    dsimp [beta]
    have hDpos : 0 < D.card := by
      by_contra hz
      have : D.card = 0 := Nat.eq_zero_of_not_pos hz
      simp [this] at hetaDef
      linarith
    positivity
  have halpha : alpha ∈ Set.Icc eta M := by
    exact ⟨hetaDef, hMbound⟩
  have hkappa : kappa ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨by dsimp [kappa]; positivity, hkappaUpper⟩
  have hwindowCount := hnWindow alpha halpha kappa hkappa
  let left : ℕ := K₀
  let right : ℕ := ⌊(1 / 4 - eps) * (D.card : ℝ)⌋₊
  have hleftCap : (alpha / 4 - sigma) * Real.sqrt n ≤ left := by
    dsimp [alpha, beta, left]
    convert hleftCapBeta using 1 <;> field_simp [hsqrt.ne']
  have hrightCap : (1 / alpha - sigma) * Real.sqrt n ≤ right := by
    have hcap := matching_floor_capacity' hsqrt hsigma hepsD hnRound
    dsimp [alpha, beta, right]
    convert hcap using 1 <;> field_simp [hsqrt.ne']
  have hthresholdNonneg : 0 ≤ (1 / 4 - eps) * (D.card : ℝ) :=
    mul_nonneg (by linarith) (by positivity)
  let P : Finset (Fin (2 * n)) → Prop := fun S ↦
    BinomialCLT.standardizedBinomialPoint (2 * n)
      ((S ∩ B₀).card + (n - (S ∩ A₀).card)) ∈
        Set.Icc
          (-((max (alpha / 4 - kappa) (15 * kappa) - rho) * Real.sqrt 2))
          ((max (1 / alpha) kappa - rho) * Real.sqrt 2)
  let F₁ : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ ContainsLinearForestWith (JB.induce (S : Set (Fin (2 * n))))
      Finset.univ left
  let F₂ : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
      (restrictedPart S A) (20 * (A.card - n))
  let F₃ : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ RandomCover.HasMatchingAtLeast (internalGraph G B₀) S
      ((1 / 4 - eps) * (D.card : ℝ))
  let F₄ : Finset (Fin (2 * n)) → Prop := fun S ↦
    sigma / 2 * (Nat.sqrt n : ℝ) ≤
      |SamplingSuitable.intersectionCount T S - (T.card : ℝ) / 2|
  have hwindowRaw :
      ((1 / 2 : ℝ) + margin / 2) * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) P : ℝ) := by
    have hp : 0 < (2 : ℝ) ^ (2 * n) := by positivity
    have hm := (lt_div_iff₀ hp).mp hwindowCount
    exact (by simpa [P] using hm.le)
  have hwindows : ∀ S, P S → ¬ F₄ S →
      (S ∩ A₀).card + 2 * (S ∩ T).card ≤
          (S ∩ B₀).card + max left (20 * (A.card - n)) ∧
        (S ∩ B₀).card ≤
          (S ∩ A₀).card + max (2 * (S ∩ T).card) right := by
    intro S hPS hnF₄
    have hx : (S ∩ A₀).card ≤ n := by
      exact (Finset.card_le_card Finset.inter_subset_right).trans_eq hA₀card
    have htransferPoint :
        |(((2 * (S ∩ T).card : ℕ) : ℝ) -
            ((A.card - n : ℕ) : ℝ))| ≤
          sigma * Real.sqrt n := by
      have hsmall :
          |((S ∩ T).card : ℝ) - (A.card - n : ℕ) / 2| <
            sigma / 2 * (Nat.sqrt n : ℝ) := by
        rw [← hTcard]
        simpa [F₄, SamplingSuitable.intersectionCount] using
          (lt_of_not_ge hnF₄)
      have hsmall' :
          |((S ∩ T).card : ℝ) - (A.card - n : ℕ) / 2| <
            sigma / 2 * Real.sqrt n :=
        hsmall.trans_le (mul_le_mul_of_nonneg_left
          Real.nat_sqrt_le_real_sqrt (by positivity))
      have heq :
          ((2 * (S ∩ T).card : ℕ) : ℝ) - (A.card - n : ℕ) =
            2 * (((S ∩ T).card : ℝ) - (A.card - n : ℕ) / 2) := by
        push_cast
        ring
      rw [heq, abs_mul]
      norm_num
      nlinarith
    exact AlmostBipartiteRegimeCounts.shrunken_capacity_window_nat_bounds
      (d := A.card - n) (leftBalanced := left)
      (leftOriginal := 20 * (A.card - n)) (right := right)
      (α := alpha) (κ := kappa) (ρ := rho) (σ := sigma)
      hnpos hx (heta.trans_le halpha.1) (by rfl) hsigma.le htwoSigma
      htransferPoint (by simpa [P] using hPS) hleftCap (by norm_num) hrightCap
  have hgood := goodSample_count_of_three_forest_failures'
    G P F₁ F₂ F₃ F₄
    (leftBalanced := left) (leftOriginal := 20 * (A.card - n))
    (right := right) (δ₁ := delta₀) (δ₂ := delta₀)
    (δ₃ := delta₀) (δ₄ := delta₀)
    hAB.1 hTA hA₀ hB₀
    (fun S hn ↦ ContainsLinearForestWith.mono_induce_of_support
      hJBG hJBsupp (by simpa [F₁] using hn))
    (fun S hn ↦ by simpa [F₂] using hn)
    (fun S hn ↦ matching_floor_induce_internalGraph' hthresholdNonneg
      (by simpa [F₃] using hn))
    hwindows hwindowRaw
    (by simpa [almostBipartiteCount, almostBipartiteEvent, F₁, left,
        Fintype.card_fin] using hleftInternalBad)
    (by simpa [almostBipartiteCount, almostBipartiteEvent, F₂,
        Fintype.card_fin] using horiginalBad)
    (by simpa [almostBipartiteCount, almostBipartiteEvent, F₃,
        Fintype.card_fin] using hmatchingBad)
    (by simpa [almostBipartiteCount, almostBipartiteEvent, F₄,
        Fintype.card_fin] using htransferBad)
  rw [Fintype.card_fin] at hgood
  apply le_trans ?_ hgood
  have hp : 0 < (2 : ℝ) ^ (2 * n) := by positivity
  rw [hdelta₀]
  nlinarith [mul_pos hmargin hp]

/-- Endpoint for the reversed bounded-internal orientation when the transfer
is below the auxiliary square-root threshold.  The original-side forest is
then unnecessary: it is represented by the identically false failure event
and the zero forest, while the compact forest supplies the balanced-left
capacity and the minimum-cover matching supplies the balanced-right one. -/
theorem swapped_small_finish
    {delta delta₀ margin rho sigma eps alpha kappa : ℝ}
    {n left : ℕ}
    (G : SimpleGraph (Fin (2 * n)))
    (A B T A₀ B₀ D : Finset (Fin (2 * n)))
    (JB : SimpleGraph (Fin (2 * n)))
    (hdelta : 0 < delta) (hdelta₀ : delta₀ = delta / 4)
    (hmargin : 0 < margin)
    (hrho : 0 < rho) (hsigma : 0 < sigma)
    (htwoSigma : 2 * sigma ≤ rho) (hepsQuarter : eps < 1 / 4)
    (hnpos : 0 < n) (hnRound : 1 ≤ sigma * Real.sqrt n / 2)
    (hAB : IsAlmostBipartiteCut G A B)
    (hTA : T ⊆ A) (hTcard : T.card = A.card - n)
    (hA₀ : A₀ = A \ T) (hB₀ : B₀ = B ∪ T)
    (hA₀card : A₀.card = n)
    (hJBG : JB ≤ G) (hJBsupp : JB.support ⊆ (A₀ : Set (Fin (2 * n))))
    (halpha : 0 < alpha)
    (hkappa : kappa = ((A.card - n : ℕ) : ℝ) / Real.sqrt n)
    (hkappaAlpha : kappa ≤ alpha / 64)
    (hleftCap : (alpha / 4 - sigma) * Real.sqrt n ≤ left)
    (hepsD : eps * (D.card : ℝ) ≤ sigma * Real.sqrt n / 2)
    (hrightCap :
      (1 / alpha - sigma) * Real.sqrt n ≤
        (⌊(1 / 4 - eps) * (D.card : ℝ)⌋₊ : ℝ))
    (hleftInternalBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun
          S : Finset (Fin (2 * n)) ↦
        ¬ ContainsLinearForestWith (JB.induce (S : Set (Fin (2 * n))))
          Finset.univ left).card : ℝ)) ≤
        delta₀ * (2 : ℝ) ^ (2 * n))
    (hmatchingBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun
          S : Finset (Fin (2 * n)) ↦
        ¬ RandomCover.HasMatchingAtLeast (internalGraph G B₀) S
          ((1 / 4 - eps) * D.card)).card : ℝ)) ≤
        delta₀ * (2 : ℝ) ^ (2 * n))
    (htransferBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun
          S : Finset (Fin (2 * n)) ↦
        sigma / 2 * (Nat.sqrt n : ℝ) ≤
          |SamplingSuitable.intersectionCount T S -
            (T.card : ℝ) / 2|).card : ℝ)) ≤
        delta₀ * (2 : ℝ) ^ (2 * n))
    (hwindowCount :
      (1 / 2 : ℝ) + margin / 2 <
        (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
            ((S ∩ B₀).card + (n - (S ∩ A₀).card)) ∈
              Set.Icc
                (-((max (alpha / 4 - kappa) (15 * kappa) - rho) *
                  Real.sqrt 2))
                ((max (1 / alpha) kappa - rho) * Real.sqrt 2)) : ℝ) /
          (2 : ℝ) ^ (2 * n)) :
    ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
      (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
        (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  let right : ℕ := ⌊(1 / 4 - eps) * (D.card : ℝ)⌋₊
  have hthresholdNonneg : 0 ≤ (1 / 4 - eps) * (D.card : ℝ) :=
    mul_nonneg (by linarith) (by positivity)
  let P : Finset (Fin (2 * n)) → Prop := fun S ↦
    BinomialCLT.standardizedBinomialPoint (2 * n)
      ((S ∩ B₀).card + (n - (S ∩ A₀).card)) ∈
        Set.Icc
          (-((max (alpha / 4 - kappa) (15 * kappa) - rho) * Real.sqrt 2))
          ((max (1 / alpha) kappa - rho) * Real.sqrt 2)
  let F₁ : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ ContainsLinearForestWith (JB.induce (S : Set (Fin (2 * n))))
      Finset.univ left
  let F₂ : Finset (Fin (2 * n)) → Prop := fun _ ↦ False
  let F₃ : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ RandomCover.HasMatchingAtLeast (internalGraph G B₀) S
      ((1 / 4 - eps) * (D.card : ℝ))
  let F₄ : Finset (Fin (2 * n)) → Prop := fun S ↦
    sigma / 2 * (Nat.sqrt n : ℝ) ≤
      |SamplingSuitable.intersectionCount T S - (T.card : ℝ) / 2|
  have hwindowRaw :
      ((1 / 2 : ℝ) + margin / 2) * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) P : ℝ) := by
    have hp : 0 < (2 : ℝ) ^ (2 * n) := by positivity
    have hm := (lt_div_iff₀ hp).mp hwindowCount
    exact (by simpa [P] using hm.le)
  have hwindows : ∀ S, P S → ¬ F₄ S →
      (S ∩ A₀).card + 2 * (S ∩ T).card ≤
          (S ∩ B₀).card + max left 0 ∧
        (S ∩ B₀).card ≤
          (S ∩ A₀).card + max (2 * (S ∩ T).card) right := by
    intro S hPS hnF₄
    have hx : (S ∩ A₀).card ≤ n :=
      (Finset.card_le_card Finset.inter_subset_right).trans_eq hA₀card
    have htransferPoint :
        |(((2 * (S ∩ T).card : ℕ) : ℝ) -
            ((A.card - n : ℕ) : ℝ))| ≤
          sigma * Real.sqrt n := by
      have hsmall :
          |((S ∩ T).card : ℝ) - (A.card - n : ℕ) / 2| <
            sigma / 2 * (Nat.sqrt n : ℝ) := by
        rw [← hTcard]
        simpa [F₄, SamplingSuitable.intersectionCount] using
          (lt_of_not_ge hnF₄)
      have hsmall' :
          |((S ∩ T).card : ℝ) - (A.card - n : ℕ) / 2| <
            sigma / 2 * Real.sqrt n :=
        hsmall.trans_le (mul_le_mul_of_nonneg_left
          Real.nat_sqrt_le_real_sqrt (by positivity))
      have heq :
          ((2 * (S ∩ T).card : ℕ) : ℝ) - (A.card - n : ℕ) =
            2 * (((S ∩ T).card : ℝ) - (A.card - n : ℕ) / 2) := by
        push_cast
        ring
      rw [heq, abs_mul]
      norm_num
      nlinarith
    have hw :=
      AlmostBipartiteRegimeCounts.shrunken_capacity_window_small_transfer_nat_bounds
        (d := A.card - n) (leftBalanced := left) (right := right)
        (α := alpha) (κ := kappa) (ρ := rho) (σ := sigma)
        hnpos hx halpha hkappa hkappaAlpha hsigma.le htwoSigma
        htransferPoint (by simpa [P] using hPS) hleftCap hrightCap
    simpa using hw
  have hgood := goodSample_count_of_three_forest_failures'
    G P F₁ F₂ F₃ F₄
    (leftBalanced := left) (leftOriginal := 0) (right := right)
    (δ₁ := delta₀) (δ₂ := delta₀)
    (δ₃ := delta₀) (δ₄ := delta₀)
    hAB.1 hTA hA₀ hB₀
    (fun S hn ↦ ContainsLinearForestWith.mono_induce_of_support
      hJBG hJBsupp (by simpa [F₁] using hn))
    (fun S _ ↦ ContainsLinearForestWith.zero _ _)
    (fun S hn ↦ matching_floor_induce_internalGraph' hthresholdNonneg
      (by simpa [F₃, right] using hn))
    hwindows hwindowRaw
    (by simpa [almostBipartiteCount, almostBipartiteEvent, F₁,
        Fintype.card_fin] using hleftInternalBad)
    (by
      have hdelta₀nonneg : 0 ≤ delta₀ := by rw [hdelta₀]; positivity
      have hnonneg : 0 ≤ delta₀ * (2 : ℝ) ^ (2 * n) := by positivity
      simpa [F₂, almostBipartiteCount, almostBipartiteEvent] using hnonneg)
    (by simpa [almostBipartiteCount, almostBipartiteEvent, F₃,
        Fintype.card_fin] using hmatchingBad)
    (by simpa [almostBipartiteCount, almostBipartiteEvent, F₄,
        Fintype.card_fin] using htransferBad)
  rw [Fintype.card_fin] at hgood
  apply le_trans ?_ hgood
  have hp : 0 < (2 : ℝ) ^ (2 * n) := by positivity
  rw [hdelta₀]
  nlinarith [mul_pos hmargin hp]

/-- Endpoint for the forward bounded-internal orientation when the transfer
exceeds the auxiliary square-root threshold.  The balanced-left capacity is
provided by the minimum-cover matching, the balanced-right capacity by the
bounded internal forest, and the original-left capacity by the ambient
original-side forest. -/
theorem forward_large_finish
    {delta delta₀ margin rho sigma eps alpha kappa : ℝ}
    {n right : ℕ}
    (G : SimpleGraph (Fin (2 * n)))
    (A B T A₀ B₀ C : Finset (Fin (2 * n)))
    (JB : SimpleGraph (Fin (2 * n)))
    (hdelta₀ : delta₀ = delta / 4) (hmargin : 0 < margin)
    (hsigma : 0 < sigma) (htwoSigma : 2 * sigma ≤ rho)
    (hnpos : 0 < n)
    (hAB : IsAlmostBipartiteCut G A B)
    (hTA : T ⊆ A) (hTcard : T.card = A.card - n)
    (hA₀ : A₀ = A \ T) (hB₀ : B₀ = B ∪ T)
    (hA₀card : A₀.card = n)
    (hkappa : kappa = ((A.card - n : ℕ) : ℝ) / Real.sqrt n)
    (halpha : 0 < alpha)
    (hleftCap : (alpha / 4 - sigma) * Real.sqrt n ≤
      (Nat.floor ((1 / 4 - eps) * (C.card : ℝ)) : ℝ))
    (hrightCap : (1 / alpha - sigma) * Real.sqrt n ≤ right)
    (hthresholdNonneg : 0 ≤ (1 / 4 - eps) * (C.card : ℝ))
    (hwindowCount :
      (1 / 2 : ℝ) + margin / 2 <
        (almostBipartiteCount
          (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
            ((S ∩ B₀).card + (n - (S ∩ A₀).card)) ∈
              Set.Icc
                (-((max (alpha / 4 - kappa) (15 * kappa) - rho) *
                  Real.sqrt 2))
                ((max (1 / alpha) kappa - rho) * Real.sqrt 2)) : ℝ) /
          (2 : ℝ) ^ (2 * n))
    (hmatchingBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun
          S : Finset (Fin (2 * n)) ↦
        ¬ RandomCover.HasMatchingAtLeast (internalGraph G A₀) S
          ((1 / 4 - eps) * C.card)).card : ℝ)) ≤
        delta₀ * (2 : ℝ) ^ (2 * n))
    (horiginalBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun
          S : Finset (Fin (2 * n)) ↦
        ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
          (restrictedPart S A) (20 * (A.card - n))).card : ℝ)) ≤
        delta₀ * (2 : ℝ) ^ (2 * n))
    (hJBG : JB ≤ G) (hJBsupp : JB.support ⊆ (B₀ : Set (Fin (2 * n))))
    (hrightBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun
          S : Finset (Fin (2 * n)) ↦
        ¬ ContainsLinearForestWith (JB.induce (S : Set (Fin (2 * n))))
          Finset.univ right).card : ℝ)) ≤
        delta₀ * (2 : ℝ) ^ (2 * n))
    (htransferBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun
          S : Finset (Fin (2 * n)) ↦
        sigma / 2 * (Nat.sqrt n : ℝ) ≤
          |SamplingSuitable.intersectionCount T S -
            (T.card : ℝ) / 2|).card : ℝ)) ≤
        delta₀ * (2 : ℝ) ^ (2 * n)) :
    ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
      (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
        (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  let left : ℕ := ⌊(1 / 4 - eps) * (C.card : ℝ)⌋₊
  let P : Finset (Fin (2 * n)) → Prop := fun S ↦
    BinomialCLT.standardizedBinomialPoint (2 * n)
      ((S ∩ B₀).card + (n - (S ∩ A₀).card)) ∈
        Set.Icc
          (-((max (alpha / 4 - kappa) (15 * kappa) - rho) * Real.sqrt 2))
          ((max (1 / alpha) kappa - rho) * Real.sqrt 2)
  let F₁ : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ RandomCover.HasMatchingAtLeast (internalGraph G A₀) S
      ((1 / 4 - eps) * (C.card : ℝ))
  let F₂ : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
      (restrictedPart S A) (20 * (A.card - n))
  let F₃ : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ ContainsLinearForestWith (JB.induce (S : Set (Fin (2 * n))))
      Finset.univ right
  let F₄ : Finset (Fin (2 * n)) → Prop := fun S ↦
    sigma / 2 * (Nat.sqrt n : ℝ) ≤
      |SamplingSuitable.intersectionCount T S - (T.card : ℝ) / 2|
  have hwindowRaw :
      ((1 / 2 : ℝ) + margin / 2) * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) P : ℝ) := by
    have hp : 0 < (2 : ℝ) ^ (2 * n) := by positivity
    have hm := (lt_div_iff₀ hp).mp hwindowCount
    exact (by simpa [P] using hm.le)
  have hwindows : ∀ S, P S → ¬ F₄ S →
      (S ∩ A₀).card + 2 * (S ∩ T).card ≤
          (S ∩ B₀).card + max left (20 * (A.card - n)) ∧
        (S ∩ B₀).card ≤
          (S ∩ A₀).card + max (2 * (S ∩ T).card) right := by
    intro S hPS hnF₄
    have hx : (S ∩ A₀).card ≤ n :=
      (Finset.card_le_card Finset.inter_subset_right).trans_eq hA₀card
    have htransferPoint :
        |(((2 * (S ∩ T).card : ℕ) : ℝ) -
            ((A.card - n : ℕ) : ℝ))| ≤ sigma * Real.sqrt n := by
      have hsmall :
          |((S ∩ T).card : ℝ) - (A.card - n : ℕ) / 2| <
            sigma / 2 * (Nat.sqrt n : ℝ) := by
        rw [← hTcard]
        simpa [F₄, SamplingSuitable.intersectionCount] using
          (lt_of_not_ge hnF₄)
      have hsmall' :
          |((S ∩ T).card : ℝ) - (A.card - n : ℕ) / 2| <
            sigma / 2 * Real.sqrt n :=
        hsmall.trans_le (mul_le_mul_of_nonneg_left
          Real.nat_sqrt_le_real_sqrt (by positivity))
      have heq :
          ((2 * (S ∩ T).card : ℕ) : ℝ) - (A.card - n : ℕ) =
            2 * (((S ∩ T).card : ℝ) - (A.card - n : ℕ) / 2) := by
        push_cast
        ring
      rw [heq, abs_mul]
      norm_num
      nlinarith
    exact AlmostBipartiteRegimeCounts.shrunken_capacity_window_nat_bounds
      (d := A.card - n) (leftBalanced := left)
      (leftOriginal := 20 * (A.card - n)) (right := right)
      (α := alpha) (κ := kappa) (ρ := rho) (σ := sigma)
      hnpos hx halpha hkappa hsigma.le htwoSigma htransferPoint
      (by simpa [P] using hPS) hleftCap (by norm_num) hrightCap
  have hgood := goodSample_count_of_three_forest_failures'
    G P F₁ F₂ F₃ F₄
    (leftBalanced := left) (leftOriginal := 20 * (A.card - n))
    (right := right) (δ₁ := delta₀) (δ₂ := delta₀)
    (δ₃ := delta₀) (δ₄ := delta₀)
    hAB.1 hTA hA₀ hB₀
    (fun S hn ↦ matching_floor_induce_internalGraph' hthresholdNonneg
      (by simpa [F₁] using hn))
    (fun S hn ↦ by simpa [F₂] using hn)
    (fun S hn ↦ ContainsLinearForestWith.mono_induce_of_support
      hJBG hJBsupp (by simpa [F₃] using hn))
    hwindows hwindowRaw
    (by simpa [almostBipartiteCount, almostBipartiteEvent, F₁, left,
        Fintype.card_fin] using hmatchingBad)
    (by simpa [almostBipartiteCount, almostBipartiteEvent, F₂,
        Fintype.card_fin] using horiginalBad)
    (by simpa [almostBipartiteCount, almostBipartiteEvent, F₃,
        Fintype.card_fin] using hrightBad)
    (by simpa [almostBipartiteCount, almostBipartiteEvent, F₄,
        Fintype.card_fin] using htransferBad)
  rw [Fintype.card_fin] at hgood
  apply le_trans ?_ hgood
  have hp : 0 < (2 : ℝ) ^ (2 * n) := by positivity
  rw [hdelta₀]
  nlinarith [mul_pos hmargin hp]

end
end TwoLargeFinish
end Erdos622
