import ErdosProblems.Erdos520.AlignedIntegerGeometry
import ErdosProblems.Erdos520.AEInterpolation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter MeasureTheory
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Global assembly of the aligned root-exponential test mesh

The concentration argument is naturally indexed by the outer blocks
`(X_(ell-1), X_ell]`, whereas interpolation uses one global sequence of
root-exponential test points.  This file supplies the exact bridge between
the two indexings.

For `K >= 1`, `alignedOuterLevel K x` is the least outer level whose right
endpoint is at least `x`.  Consequently every sufficiently large global test
index belongs to the finite test family at precisely its aligned outer level.
-/

/-- Every aligned outer endpoint dominates its own level once `K >= 1`. -/
theorem self_le_alignedOuterEndpoint {K ell : ℕ} (hK : 1 ≤ K) :
    ell ≤ alignedOuterEndpoint K ell := by
  have hpow : ell ≤ ell ^ K := by
    cases ell with
    | zero => simp
    | succ ell =>
        exact le_self_pow₀ (by omega) (by omega : K ≠ 0)
  calc
    ell ≤ 2 ^ ell := (Nat.lt_two_pow_self (n := ell)).le
    _ ≤ 2 ^ (ell ^ K) := Nat.pow_le_pow_right (by norm_num) hpow
    _ = alignedOuterExponent K ell := rfl
    _ ≤ 2 ^ alignedOuterExponent K ell :=
      (Nat.lt_two_pow_self (n := alignedOuterExponent K ell)).le
    _ = alignedOuterEndpoint K ell := rfl

/-- The aligned outer endpoints are cofinal in the natural numbers. -/
theorem tendsto_alignedOuterEndpoint_atTop {K : ℕ} (hK : 1 ≤ K) :
    Tendsto (alignedOuterEndpoint K) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro ell
  filter_upwards [eventually_ge_atTop ell] with L hL
  exact (self_le_alignedOuterEndpoint hK).trans
    (alignedOuterEndpoint_mono K hL)

/-- There is an aligned outer endpoint above every natural input. -/
theorem exists_le_alignedOuterEndpoint {K : ℕ} (hK : 1 ≤ K) (x : ℕ) :
    ∃ ell, x ≤ alignedOuterEndpoint K ell :=
  ⟨x, self_le_alignedOuterEndpoint hK⟩

/-- Least aligned outer level whose right endpoint is at least `x`.

The fallback branch makes the definition total at `K = 0`; all geometric
properties below are stated under the intended hypothesis `1 <= K`.
-/
noncomputable def alignedOuterLevel (K x : ℕ) : ℕ :=
  by
    classical
    exact if h : ∃ ell, x ≤ alignedOuterEndpoint K ell then Nat.find h else 0

/-- The right endpoint at the least aligned level is at least the input. -/
theorem le_alignedOuterEndpoint_outerLevel
    {K : ℕ} (hK : 1 ≤ K) (x : ℕ) :
    x ≤ alignedOuterEndpoint K (alignedOuterLevel K x) := by
  classical
  let h : ∃ ell, x ≤ alignedOuterEndpoint K ell :=
    exists_le_alignedOuterEndpoint hK x
  rw [alignedOuterLevel, dif_pos h]
  exact Nat.find_spec h

/-- Minimality of `alignedOuterLevel`, in the direction used below. -/
theorem alignedOuterLevel_le_of_le_endpoint
    {K : ℕ} (hK : 1 ≤ K) {x ell : ℕ}
    (hx : x ≤ alignedOuterEndpoint K ell) :
    alignedOuterLevel K x ≤ ell := by
  classical
  let h : ∃ L, x ≤ alignedOuterEndpoint K L :=
    exists_le_alignedOuterEndpoint hK x
  rw [alignedOuterLevel, dif_pos h]
  exact Nat.find_min' h hx

/-- If the least level is positive, the input lies strictly beyond the
preceding outer endpoint. -/
theorem previous_alignedOuterEndpoint_lt_of_outerLevel_pos
    {K x : ℕ} (hK : 1 ≤ K) (hlevel : 0 < alignedOuterLevel K x) :
    alignedOuterEndpoint K (alignedOuterLevel K x - 1) < x := by
  by_contra hnot
  have hx : x ≤ alignedOuterEndpoint K (alignedOuterLevel K x - 1) := by
    omega
  have hminimal := alignedOuterLevel_le_of_le_endpoint hK hx
  omega

/-- Passing the endpoint of level `ell` forces the least containing level to
be strictly larger than `ell`. -/
theorem lt_alignedOuterLevel_of_endpoint_lt
    {K x ell : ℕ} (hK : 1 ≤ K)
    (hx : alignedOuterEndpoint K ell < x) :
    ell < alignedOuterLevel K x := by
  by_contra hnot
  have hlevel : alignedOuterLevel K x ≤ ell := by omega
  have hupper := le_alignedOuterEndpoint_outerLevel hK x
  have hmono := alignedOuterEndpoint_mono K hlevel
  omega

/-- The least aligned outer level tends to infinity with its input. -/
theorem tendsto_alignedOuterLevel_atTop {K : ℕ} (hK : 1 ≤ K) :
    Tendsto (alignedOuterLevel K) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro ell
  filter_upwards [eventually_gt_atTop (alignedOuterEndpoint K ell)] with x hx
  exact (lt_alignedOuterLevel_of_endpoint_lt hK hx).le

/-- For positive `m`, the root-exponential test points form a cofinal
natural-valued sequence. -/
theorem tendsto_alignedRootExpTestPoint_atTop {m : ℕ} (hm : 0 < m) :
    Tendsto (alignedRootExpTestPoint m) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro x
  let i₀ := alignedRootExpTestIndexBound 1 m x
  filter_upwards [eventually_ge_atTop i₀] with i hi
  have hpast : alignedOuterEndpoint 1 x <
      alignedRootExpTestPoint m i₀ := by
    exact alignedOuterEndpoint_lt_testPoint_indexBound
      (K := 1) (m := m) (ell := x) hm
  have hmono : alignedRootExpTestPoint m i₀ ≤
      alignedRootExpTestPoint m i :=
    alignedRootExpTestPoint_mono m hi
  exact (self_le_alignedOuterEndpoint (K := 1) (by omega)).trans
    (hpast.le.trans hmono)

/-- The aligned outer level of the global test sequence is itself cofinal. -/
theorem tendsto_alignedOuterLevel_rootExpTestPoint_atTop
    {K m : ℕ} (hK : 1 ≤ K) (hm : 0 < m) :
    Tendsto
      (fun i => alignedOuterLevel K (alignedRootExpTestPoint m i))
      atTop atTop :=
  (tendsto_alignedOuterLevel_atTop hK).comp
    (tendsto_alignedRootExpTestPoint_atTop hm)

/-- Every sufficiently large global root-exponential test index belongs to
the finite aligned test family at its least containing outer level. -/
theorem eventually_mem_alignedRootExpTests_outerLevel
    {K m : ℕ} (hK : 1 ≤ K) (hm : 0 < m) :
    ∀ᶠ i : ℕ in atTop,
      i ∈ alignedRootExpTests K m
        (alignedOuterLevel K (alignedRootExpTestPoint m i)) := by
  let i₀ := alignedRootExpTestIndexBound K m 4
  filter_upwards [eventually_ge_atTop i₀] with i hi
  let x := alignedRootExpTestPoint m i
  let ell := alignedOuterLevel K x
  have hpast₀ : alignedOuterEndpoint K 4 <
      alignedRootExpTestPoint m i₀ := by
    exact alignedOuterEndpoint_lt_testPoint_indexBound
      (K := K) (m := m) (ell := 4) hm
  have hpast : alignedOuterEndpoint K 4 < x := by
    exact hpast₀.trans_le (alignedRootExpTestPoint_mono m hi)
  have hell : 5 ≤ ell := by
    dsimp only [ell]
    exact lt_alignedOuterLevel_of_endpoint_lt hK hpast
  have hlevelPos : 0 < ell := by omega
  have hlower : alignedOuterEndpoint K (ell - 1) < x := by
    exact previous_alignedOuterEndpoint_lt_of_outerLevel_pos hK hlevelPos
  have hupper : x ≤ alignedOuterEndpoint K ell := by
    exact le_alignedOuterEndpoint_outerLevel hK x
  exact mem_alignedRootExpTests_of_mem_outerBlock hm hell hlower hupper

/-- Pull an almost-sure eventual bound over the finite tests at each aligned
scale back to the single global root-exponential sequence.

The comparison with `scale` is deterministic and only required eventually;
this is the form in which a scale-specific threshold is normally compared to
the final critical scale.
-/
theorem aeTestPointBound_alignedRootExp_of_ae_scales
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {M : Ω → ℕ → ℝ} {scale : ℕ → ℝ} {K m : ℕ}
    (hK : 1 ≤ K) (hm : 0 < m)
    (u : ℕ → ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hcompare : ∀ᶠ i : ℕ in atTop,
      u (alignedOuterLevel K (alignedRootExpTestPoint m i)) i ≤
        D * scale (alignedRootExpTestPoint m i))
    (hscales : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        |M omega (alignedRootExpTestPoint m i)| ≤ u ell i) :
    AETestPointBound μ M scale (alignedRootExpTestPoint m) := by
  filter_upwards [hscales] with omega homega
  refine ⟨D, hD, ?_⟩
  have hpull : ∀ᶠ i : ℕ in atTop,
      ∀ r ∈ alignedRootExpTests K m
          (alignedOuterLevel K (alignedRootExpTestPoint m i)),
        |M omega (alignedRootExpTestPoint m r)| ≤
          u (alignedOuterLevel K (alignedRootExpTestPoint m i)) r :=
    (tendsto_alignedOuterLevel_rootExpTestPoint_atTop hK hm).eventually homega
  filter_upwards [hpull,
      eventually_mem_alignedRootExpTests_outerLevel hK hm,
      hcompare] with i hi hmem hcomparison
  exact (hi i hmem).trans hcomparison

/-- The preceding assembly lemma specialized to the critical scale used in
the statement of Erdős #520. -/
theorem aeTestPointBound_criticalScale_alignedRootExp_of_ae_scales
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {M : Ω → ℕ → ℝ} {η : ℝ} {K m : ℕ}
    (hK : 1 ≤ K) (hm : 0 < m)
    (u : ℕ → ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hcompare : ∀ᶠ i : ℕ in atTop,
      u (alignedOuterLevel K (alignedRootExpTestPoint m i)) i ≤
        D * criticalScale η (alignedRootExpTestPoint m i))
    (hscales : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ i ∈ alignedRootExpTests K m ell,
        |M omega (alignedRootExpTestPoint m i)| ≤ u ell i) :
    AETestPointBound μ M (criticalScale η)
      (alignedRootExpTestPoint m) :=
  aeTestPointBound_alignedRootExp_of_ae_scales
    hK hm u D hD hcompare hscales

end Problem520
end Erdos
