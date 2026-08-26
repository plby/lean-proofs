import ErdosProblems.Erdos520.CaichMainDecomposition
import ErdosProblems.Erdos520.CaichCoreMainPNT
import ErdosProblems.Erdos520.CaichConcreteSmoothingReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Exact thin-block partition of Caich's averaged main term

The endpoint chain below is capped at the test point `x`.  Hence its last
endpoint is literally `x`, even when the ambient aligned schedule overshoots
the test point.  The averaged main term is partitioned exactly into the core
and upper boundary strip of every capped block, and the core is then split
into near- and long-ratio blocks.
-/

/-- The initial averaged main term is additive over adjacent prime blocks. -/
theorem caichInitialSmoothedMain_add
    (X : ℝ) (omega : Omega) (x : ℕ)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    caichInitialSmoothedMain X omega x a c =
      caichInitialSmoothedMain X omega x a b +
        caichInitialSmoothedMain X omega x b c := by
  classical
  have hunion : freshPrimes a c =
      freshPrimes a b ∪ freshPrimes b c := by
    ext p
    simp only [mem_freshPrimes, Finset.mem_union]
    constructor
    · rintro ⟨hp, hap, hpc⟩
      by_cases hpb : p ≤ b
      · exact Or.inl ⟨hp, hap, hpb⟩
      · exact Or.inr ⟨hp, by omega, hpc⟩
    · rintro (⟨hp, hap, hpb⟩ | ⟨hp, hbp, hpc⟩)
      · exact ⟨hp, hap, hpb.trans hbc⟩
      · exact ⟨hp, hab.trans_lt hbp, hpc⟩
  have hdisj : Disjoint (freshPrimes a b) (freshPrimes b c) := by
    rw [Finset.disjoint_left]
    intro p hpab hpbc
    have hpab' := mem_freshPrimes.mp hpab
    have hpbc' := mem_freshPrimes.mp hpbc
    omega
  unfold caichInitialSmoothedMain
  rw [hunion, Finset.sum_union hdisj]

/-- Telescoping additivity along any monotone finite endpoint chain. -/
theorem caichInitialSmoothedMain_eq_sum_chain
    (X : ℝ) (omega : Omega) (x : ℕ)
    (endpoint : ℕ → ℕ) (N : ℕ) (hmono : Monotone endpoint) :
    caichInitialSmoothedMain X omega x (endpoint 0) (endpoint N) =
      ∑ j ∈ Finset.range N,
        caichInitialSmoothedMain X omega x (endpoint j) (endpoint (j + 1)) := by
  induction N with
  | zero =>
      unfold caichInitialSmoothedMain
      rw [show freshPrimes (endpoint 0) (endpoint 0) = ∅ by
        ext p
        simp only [mem_freshPrimes, Finset.notMem_empty, iff_false]
        omega]
      simp
  | succ N ih =>
      rw [caichInitialSmoothedMain_add X omega x
        (hmono (Nat.zero_le N)) (hmono (Nat.le_succ N)), ih,
        Finset.sum_range_succ]

/-- Pointwise cap of an ambient thin schedule at the test point. -/
def caichCappedThinEndpoint (x : ℕ) (endpoint : ℕ → ℕ) (j : ℕ) : ℕ :=
  min (endpoint j) x

theorem monotone_caichCappedThinEndpoint
    (x : ℕ) {endpoint : ℕ → ℕ} (hmono : Monotone endpoint) :
    Monotone (caichCappedThinEndpoint x endpoint) := by
  intro i j hij
  exact min_le_min (hmono hij) le_rfl

@[simp] theorem caichCappedThinEndpoint_eq_left
    {x : ℕ} {endpoint : ℕ → ℕ} {j : ℕ} (h : endpoint j ≤ x) :
    caichCappedThinEndpoint x endpoint j = endpoint j :=
  min_eq_left h

@[simp] theorem caichCappedThinEndpoint_eq_testPoint
    {x : ℕ} {endpoint : ℕ → ℕ} {j : ℕ} (h : x ≤ endpoint j) :
    caichCappedThinEndpoint x endpoint j = x :=
  min_eq_right h

/-- Exact core-plus-boundary decomposition over a capped endpoint chain
whose final endpoint reaches `x`. -/
theorem caichInitialSmoothedMain_eq_sum_capped_core_boundary
    {X : ℝ} (hX : 0 < X) (omega : Omega) {x : ℕ} (hx : 0 < x)
    (endpoint : ℕ → ℕ) (N : ℕ)
    (hmono : Monotone endpoint)
    (hone : ∀ j ≤ N, 1 ≤ endpoint j)
    (hfinal : x ≤ endpoint N) :
    caichInitialSmoothedMain X omega x
        (caichCappedThinEndpoint x endpoint 0) x =
      ∑ j ∈ Finset.range N,
        (caichCoreAveragedBlockMain X omega x
            (caichCappedThinEndpoint x endpoint j)
            (caichCappedThinEndpoint x endpoint (j + 1)) +
          caichBoundaryAveragedBlockMain X omega x
            (caichCappedThinEndpoint x endpoint j)
            (caichCappedThinEndpoint x endpoint (j + 1))) := by
  let capped : ℕ → ℕ := caichCappedThinEndpoint x endpoint
  have hcappedMono : Monotone capped :=
    monotone_caichCappedThinEndpoint x hmono
  have hcappedFinal : capped N = x :=
    caichCappedThinEndpoint_eq_testPoint hfinal
  have hchain :=
    caichInitialSmoothedMain_eq_sum_chain X omega x capped N hcappedMono
  rw [hcappedFinal] at hchain
  rw [hchain]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j < N := Finset.mem_range.mp hj
  have hleft : 1 ≤ capped j := by
    dsimp only [capped, caichCappedThinEndpoint]
    exact le_min (hone j hjN.le) (by omega)
  exact caichInitialSmoothedMain_eq_core_add_boundary
    hX omega x hx hleft (hcappedMono (Nat.le_succ j))

/-- Full deterministic schedule cleanup.  The main term is the near-block
cardinality times the selected block-energy maximum; the long-ratio and
upper-boundary pieces remain the two explicit residuals consumed by
`L^(12)` and `L^(2)` respectively. -/
theorem caichInitialSmoothedMain_le_nearMax_add_residuals
    {X C : ℝ} {x ell : ℕ}
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (endpoint : ℕ → ℕ) (N : ℕ)
    (near : ℕ → Prop) [DecidablePred near]
    (blockIndex : ℕ → ℕ)
    (hX : 0 < X) (hx : 0 < x) (hC : 0 ≤ C) (omega : Omega)
    (hmono : Monotone endpoint)
    (hone : ∀ j ≤ N, 1 ≤ endpoint j)
    (hfinal : x ≤ endpoint N)
    (hJ : ∀ j ∈ Finset.range N, near j → blockIndex j ≤ J ell)
    (hright : ∀ j ∈ Finset.range N, near j →
      2 ≤ caichCappedThinEndpoint x endpoint (j + 1))
    (hU : ∀ j ∈ Finset.range N, near j →
      realSmoothBlockEnergy
          (caichCappedThinEndpoint x endpoint j)
          (caichCappedThinEndpoint x endpoint (j + 1)) omega ≤
        U ell (blockIndex j) omega)
    (hshort : ∀ j ∈ Finset.range N, near j → ∀ z ∈
      Ioc
        ((x : ℝ) /
          (caichCappedThinEndpoint x endpoint (j + 1) : ℝ))
        ((x : ℝ) / (caichCappedThinEndpoint x endpoint j : ℝ)),
      caichShortWindowReciprocalMass X x
          (caichCappedThinEndpoint x endpoint j)
          (caichCappedThinEndpoint x endpoint (j + 1)) z ≤
        C / (X * Real.log
          (caichCappedThinEndpoint x endpoint (j + 1) : ℝ))) :
    caichInitialSmoothedMain X omega x
        (caichCappedThinEndpoint x endpoint 0) x ≤
      (((Finset.range N).filter near).card : ℝ) * C * (x : ℝ) *
          caichBlockEnergyMax J U ell omega +
        caichLongRatioAveragedMain X omega x (Finset.range N)
          (caichCappedThinEndpoint x endpoint)
          (fun j ↦ caichCappedThinEndpoint x endpoint (j + 1)) near +
        caichBoundaryAveragedMain X omega x (Finset.range N)
          (caichCappedThinEndpoint x endpoint)
          (fun j ↦ caichCappedThinEndpoint x endpoint (j + 1)) := by
  let left : ℕ → ℕ := caichCappedThinEndpoint x endpoint
  let right : ℕ → ℕ := fun j ↦ caichCappedThinEndpoint x endpoint (j + 1)
  have hdecomp := caichInitialSmoothedMain_eq_sum_capped_core_boundary
    hX omega hx endpoint N hmono hone hfinal
  have hpartition := caichNear_add_longRatio_eq_coreSum
    X omega x (Finset.range N) left right near
  have hnear := caichNearRatioAveragedMain_le_card_mul_blockEnergyMax
    J U (Finset.range N) left right near blockIndex hX hx hC omega hJ
    (fun j hj hjNear ↦ by
      dsimp only [left, caichCappedThinEndpoint]
      exact le_min (hone j (Finset.mem_range.mp hj).le) (by omega))
    (fun j hj hjNear ↦
      (monotone_caichCappedThinEndpoint x hmono) (Nat.le_succ j))
    hright hU hshort
  rw [hdecomp]
  unfold caichBoundaryAveragedMain
  dsimp only [left, right] at hpartition hnear ⊢
  rw [Finset.sum_add_distrib, ← hpartition]
  linarith

/-! ## Literal normalized `L^(12)` and `L^(2)` residuals -/

/-- Caich's long-ratio residual, normalized by the test point. -/
noncomputable def caichScheduledL12
    (X : ℝ) (omega : Omega) (x : ℕ)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (near : ℕ → Prop) [DecidablePred near] : ℝ :=
  caichLongRatioAveragedMain X omega x blocks left right near / (x : ℝ)

/-- Caich's upper-boundary residual, normalized by the test point. -/
noncomputable def caichScheduledL2
    (X : ℝ) (omega : Omega) (x : ℕ)
    (blocks : Finset ℕ) (left right : ℕ → ℕ) : ℝ :=
  caichBoundaryAveragedMain X omega x blocks left right / (x : ℝ)

theorem caichScheduledL12_nonneg
    {X : ℝ} (hX : 0 ≤ X) (omega : Omega) {x : ℕ} (hx : 0 < x)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (near : ℕ → Prop) [DecidablePred near] :
    0 ≤ caichScheduledL12 X omega x blocks left right near := by
  unfold caichScheduledL12
  exact div_nonneg
    (caichLongRatioAveragedMain_nonneg hX omega x blocks left right near)
    (by positivity)

theorem caichScheduledL2_nonneg
    {X : ℝ} (hX : 0 ≤ X) (omega : Omega) {x : ℕ} (hx : 0 < x)
    (blocks : Finset ℕ) (left right : ℕ → ℕ) :
    0 ≤ caichScheduledL2 X omega x blocks left right := by
  unfold caichScheduledL2
  exact div_nonneg
    (caichBoundaryAveragedMain_nonneg hX omega x blocks left right)
    (by positivity)

/-- Any scheduled core/boundary cleanup whose near coefficient fits inside
`ell * log ell` gives the exact pointwise domination required by
`caichUnaccountedMainDominatedAtScale`.  The two lambda terms can be chosen
to be zero because the strict-cutoff core was bounded directly by the
running block maximum. -/
theorem caichUnaccountedSmoothedMain_le_scheduledL12_add_L2
    {X A : ℝ} {x a ell : ℕ}
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (near : ℕ → Prop) [DecidablePred near]
    (hX : 0 ≤ X) (hx : 0 < x) (omega : Omega)
    (hmax : 0 ≤ caichBlockEnergyMax J U ell omega)
    (hbudget : A ≤ caichAuxiliaryLogFactor ell)
    (hcleanup : caichInitialSmoothedMain X omega x a x ≤
      A * (x : ℝ) * caichBlockEnergyMax J U ell omega +
        caichLongRatioAveragedMain X omega x blocks left right near +
        caichBoundaryAveragedMain X omega x blocks left right) :
    caichUnaccountedSmoothedMain X J U ell omega x a x ≤
      caichScheduledL12 X omega x blocks left right near +
        caichScheduledL2 X omega x blocks left right := by
  let M : ℝ := caichBlockEnergyMax J U ell omega
  let L12 : ℝ := caichLongRatioAveragedMain
    X omega x blocks left right near
  let L2 : ℝ := caichBoundaryAveragedMain X omega x blocks left right
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hnear : A * (x : ℝ) * M ≤
      caichAuxiliaryLogFactor ell * (x : ℝ) * M := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget (by positivity)) hmax
  have htotal : caichInitialSmoothedMain X omega x a x ≤
      caichAuxiliaryLogFactor ell * (x : ℝ) * M + L12 + L2 := by
    calc
      caichInitialSmoothedMain X omega x a x ≤
          A * (x : ℝ) * M + L12 + L2 := by
        simpa only [M, L12, L2] using! hcleanup
      _ ≤ caichAuxiliaryLogFactor ell * (x : ℝ) * M + L12 + L2 := by
        gcongr
  have hdiv := div_le_div_of_nonneg_right htotal hxR.le
  have hnormalize :
      (caichAuxiliaryLogFactor ell * (x : ℝ) * M + L12 + L2) /
          (x : ℝ) =
        caichAuxiliaryLogFactor ell * M + L12 / (x : ℝ) + L2 / (x : ℝ) := by
    field_simp
  rw [hnormalize] at hdiv
  unfold caichUnaccountedSmoothedMain
  apply max_le
  · exact add_nonneg
      (caichScheduledL12_nonneg hX omega hx blocks left right near)
      (caichScheduledL2_nonneg hX omega hx blocks left right)
  · unfold caichScheduledL12 caichScheduledL2
    dsimp only [M, L12, L2] at hdiv ⊢
    unfold caichAuxiliaryLogFactor at hdiv
    linarith

/-- Capped-schedule specialization of the preceding pointwise domination.
This is the direct deterministic input for the concrete five-auxiliary
assembly, with `lambda2 = lambda3 = 0`. -/
theorem caichUnaccountedSmoothedMain_le_cappedScheduledL12_add_L2
    {X C : ℝ} {x ell : ℕ}
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (endpoint : ℕ → ℕ) (N : ℕ)
    (near : ℕ → Prop) [DecidablePred near]
    (blockIndex : ℕ → ℕ)
    (hX : 0 < X) (hx : 0 < x) (hC : 0 ≤ C) (omega : Omega)
    (hmono : Monotone endpoint)
    (hone : ∀ j ≤ N, 1 ≤ endpoint j)
    (hfinal : x ≤ endpoint N)
    (hJ : ∀ j ∈ Finset.range N, near j → blockIndex j ≤ J ell)
    (hright : ∀ j ∈ Finset.range N, near j →
      2 ≤ caichCappedThinEndpoint x endpoint (j + 1))
    (hU : ∀ j ∈ Finset.range N, near j →
      realSmoothBlockEnergy
          (caichCappedThinEndpoint x endpoint j)
          (caichCappedThinEndpoint x endpoint (j + 1)) omega ≤
        U ell (blockIndex j) omega)
    (hshort : ∀ j ∈ Finset.range N, near j → ∀ z ∈
      Ioc
        ((x : ℝ) /
          (caichCappedThinEndpoint x endpoint (j + 1) : ℝ))
        ((x : ℝ) / (caichCappedThinEndpoint x endpoint j : ℝ)),
      caichShortWindowReciprocalMass X x
          (caichCappedThinEndpoint x endpoint j)
          (caichCappedThinEndpoint x endpoint (j + 1)) z ≤
        C / (X * Real.log
          (caichCappedThinEndpoint x endpoint (j + 1) : ℝ)))
    (hmax : 0 ≤ caichBlockEnergyMax J U ell omega)
    (hbudget : (((Finset.range N).filter near).card : ℝ) * C ≤
      caichAuxiliaryLogFactor ell) :
    caichUnaccountedSmoothedMain X J U ell omega x
        (caichCappedThinEndpoint x endpoint 0) x ≤
      caichScheduledL12 X omega x (Finset.range N)
          (caichCappedThinEndpoint x endpoint)
          (fun j ↦ caichCappedThinEndpoint x endpoint (j + 1)) near +
        caichScheduledL2 X omega x (Finset.range N)
          (caichCappedThinEndpoint x endpoint)
          (fun j ↦ caichCappedThinEndpoint x endpoint (j + 1)) := by
  let blocks := Finset.range N
  let left : ℕ → ℕ := caichCappedThinEndpoint x endpoint
  let right : ℕ → ℕ := fun j ↦ caichCappedThinEndpoint x endpoint (j + 1)
  have hcleanup := caichInitialSmoothedMain_le_nearMax_add_residuals
    J U endpoint N near blockIndex hX hx hC omega hmono hone hfinal
      hJ hright hU hshort
  exact caichUnaccountedSmoothedMain_le_scheduledL12_add_L2
    J U blocks left right near hX.le hx omega hmax hbudget
      (by simpa only [blocks, left, right] using! hcleanup)

end Problem520
end Erdos
