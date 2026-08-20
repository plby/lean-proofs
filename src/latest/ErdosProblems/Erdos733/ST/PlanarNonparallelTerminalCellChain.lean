import ErdosProblems.Erdos733.ST.Preamble
import Mathlib.Tactic


open Classical
noncomputable section

-- [TABLET NODE: PlanarNonparallelTerminalCellChain]
lemma PlanarNonparallelTerminalCellChain
    (x dA dB : EuclideanSpace ℝ (Fin 2)) (t k : ℝ)
    (Q : Set (EuclideanSpace ℝ (Fin 2)))
    (quadrantGate : EuclideanSpace ℝ (Fin 2)) (s r : ℝ)
    (ht : 0 < t) (hk : 0 < k)
    (hli : LinearIndependent ℝ ![dA, dB])
    (hs : 0 < s) (hr : 0 < r)
    (hkr : r = k * s) (hsum_eq : s + r = t / 2)
    (hquadrantGate : quadrantGate = x + s • dA + r • dB)
    (hQconvex : Convex ℝ Q)
    (hquadrantGateQ : quadrantGate ∈ Q)
    (hyQ : (x + t • dB) ∈ Q)
    (hQsector : Q \ ({x + t • dB} : Set _) ⊆
      {q | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ k * a ≤ b ∧ a + b < t ∧
        q = x + a • dA + b • dB}) :
    ∃ Side Bridge : Set (EuclideanSpace ℝ (Fin 2)),
      ∃ terminalGate sideSource : EuclideanSpace ℝ (Fin 2),
        IsOpen Side ∧ Convex ℝ Side ∧ IsCompact (closure Side) ∧
        IsOpen Bridge ∧ Convex ℝ Bridge ∧ IsCompact (closure Bridge) ∧
        terminalGate ∈ closure Side ∧ terminalGate ∉ Side ∧
        sideSource ∈ closure Side ∧ sideSource ∉ Side ∧
        sideSource ∈ closure Bridge ∧ sideSource ∉ Bridge ∧
        quadrantGate ∈ closure Bridge ∧ quadrantGate ∉ Bridge ∧
        terminalGate ≠ sideSource ∧ sideSource ≠ quadrantGate ∧
        segment ℝ terminalGate sideSource ⊆
          Side ∪ ({terminalGate, sideSource} : Set _) ∧
        openSegment ℝ terminalGate sideSource ⊆ Side ∧
        segment ℝ sideSource quadrantGate ⊆
          Bridge ∪ ({sideSource, quadrantGate} : Set _) ∧
        openSegment ℝ sideSource quadrantGate ⊆ Bridge ∧
        segment ℝ sideSource quadrantGate ∩ Q = ({quadrantGate} : Set _) ∧
        closure Side ∩ closure Bridge = ({sideSource} : Set _) ∧
        closure Side ∩ closure Q = ∅ ∧
        closure Bridge ∩ closure Q = ({quadrantGate} : Set _) ∧
        segment ℝ quadrantGate (x + t • dB) ⊆ Q ∧
        (∀ z ∈ closure Side, ∃ a b : ℝ,
          0 < a ∧ 0 < b ∧ a + b < t ∧ b < k * a ∧
            s + 2 * (r / 100) ≤ a ∧ a ≤ s + 4 * (r / 100) ∧
            r - 4 * (r / 100) ≤ b ∧ b ≤ r - 2 * (r / 100) ∧
            z = x + a • dA + b • dB) ∧
        (∀ z ∈ closure Bridge, ∃ a b : ℝ,
          0 < a ∧ 0 < b ∧ a + b < t ∧ b ≤ k * a ∧
            s ≤ a ∧ a ≤ s + 2 * (r / 100) ∧
            r - 2 * (r / 100) ≤ b ∧ b ≤ r ∧
            z = x + a • dA + b • dB) ∧
        ∃ delta : ℝ, 0 < delta ∧ delta = r / 100 ∧
          sideSource = x + (s + 2 * delta) • dA +
            (r - 2 * delta) • dB ∧
          terminalGate = x + (s + 4 * delta) • dA +
            (r - 4 * delta) • dB := by
-- BODY
  let E := EuclideanSpace ℝ (Fin 2)
  let C := Fin 2 → ℝ
  let basis : Fin 2 → E := ![dA, dB]
  let L : C →ₗ[ℝ] E := Fintype.linearCombination ℝ basis
  have hL_apply (z : C) : L z = z 0 • dA + z 1 • dB := by
    dsimp [L]
    rw [Fintype.linearCombination_apply, Fin.sum_univ_two]
    simp [basis]
  have hL_inj : Function.Injective L := by
    simpa [L, basis] using hli.fintypeLinearCombination_injective
  have hdim : Module.finrank ℝ C = Module.finrank ℝ E := by
    simp [C, E, EuclideanSpace]
  let e : C ≃ₗ[ℝ] E := L.linearEquivOfInjective hL_inj hdim
  let eL : C ≃L[ℝ] E := e.toContinuousLinearEquiv
  let chart : C ≃ₜ E := eL.toHomeomorph.trans (Homeomorph.addLeft x)
  have hchart_apply (z : C) : chart z = x + L z := by
    rfl
  have hsum : s + r < t := by
    rw [hsum_eq]
    linarith
  let q0 : C := ![s, r]
  have hchartq : chart q0 = quadrantGate := by
    rw [hchart_apply, hL_apply]
    simpa [q0, add_assoc] using hquadrantGate.symm
  subst quadrantGate
  let delta : ℝ := r / 100
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  let one : C := ![1, -1]
  let cB : C := q0 + delta • one
  let cS : C := q0 + (3 * delta) • one
  let qC : C := q0
  let sideC : C := q0 + (2 * delta) • one
  let gateC : C := q0 + (4 * delta) • one
  let BridgeC : Set C := Metric.ball cB delta
  let SideC : Set C := Metric.ball cS delta
  let Bridge : Set E := chart '' BridgeC
  let Side : Set E := chart '' SideC
  let quadrantGate : E := chart qC
  let sideSource : E := chart sideC
  let terminalGate : E := chart gateC
  have hq00 : q0 0 = s := by dsimp [q0]
  have hq01 : q0 1 = r := by dsimp [q0]
  have hone0 : one 0 = 1 := by dsimp [one]
  have hone1 : one 1 = -1 := by dsimp [one]
  have hcB0 : cB 0 = s + delta := by
    change q0 0 + delta * one 0 = s + delta
    rw [hq00, hone0]
    ring
  have hcB1 : cB 1 = r - delta := by
    change q0 1 + delta * one 1 = r - delta
    rw [hq01, hone1]
    ring
  have hcS0 : cS 0 = s + 3 * delta := by
    change q0 0 + (3 * delta) * one 0 = s + 3 * delta
    rw [hq00, hone0]
    ring
  have hcS1 : cS 1 = r - 3 * delta := by
    change q0 1 + (3 * delta) * one 1 = r - 3 * delta
    rw [hq01, hone1]
    ring
  have hqC0 : qC 0 = s := by
    dsimp [qC, q0]
  have hqC1 : qC 1 = r := by
    dsimp [qC, q0]
  have hsideC0 : sideC 0 = s + 2 * delta := by
    change q0 0 + (2 * delta) * one 0 = s + 2 * delta
    rw [hq00, hone0]
    ring
  have hsideC1 : sideC 1 = r - 2 * delta := by
    change q0 1 + (2 * delta) * one 1 = r - 2 * delta
    rw [hq01, hone1]
    ring
  have hgateC0 : gateC 0 = s + 4 * delta := by
    change q0 0 + (4 * delta) * one 0 = s + 4 * delta
    rw [hq00, hone0]
    ring
  have hgateC1 : gateC 1 = r - 4 * delta := by
    change q0 1 + (4 * delta) * one 1 = r - 4 * delta
    rw [hq01, hone1]
    ring
  have hquadrant_q : quadrantGate = chart q0 := by
    rfl
  have hquadrant_formula :
      quadrantGate = x + s • dA + r • dB :=
    hquadrant_q.trans hchartq
  have hone_norm : ‖one‖ = 1 := by
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonempty]
      intro i
      fin_cases i <;> norm_num [one]
    · calc
        1 = ‖one (0 : Fin 2)‖ := by norm_num [one]
        _ ≤ ‖one‖ := norm_le_pi_norm one (0 : Fin 2)
  have hdelta_norm : ‖delta • one‖ = delta := by
    rw [norm_smul, hone_norm, mul_one, Real.norm_eq_abs, abs_of_pos hdelta]
  have hq_closedBridge : qC ∈ Metric.closedBall cB delta := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [show qC - cB = -(delta • one) by simp [qC, cB]]
    simpa using hdelta_norm.le
  have hside_closedBridge : sideC ∈ Metric.closedBall cB delta := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [show sideC - cB = delta • one by
      dsimp [sideC, cB]
      module]
    exact hdelta_norm.le
  have hside_closedSide : sideC ∈ Metric.closedBall cS delta := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [show sideC - cS = -(delta • one) by
      dsimp [sideC, cS]
      module]
    simpa using hdelta_norm.le
  have hgate_closedSide : gateC ∈ Metric.closedBall cS delta := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [show gateC - cS = delta • one by
      dsimp [gateC, cS]
      module]
    exact hdelta_norm.le
  have hclosureBridge :
      closure Bridge = chart '' Metric.closedBall cB delta := by
    calc
      closure Bridge = closure (chart '' BridgeC) := rfl
      _ = chart '' closure BridgeC := (chart.image_closure BridgeC).symm
      _ = chart '' Metric.closedBall cB delta := by
        rw [show closure BridgeC = Metric.closedBall cB delta by
          exact closure_ball cB hdelta.ne']
  have hclosureSide :
      closure Side = chart '' Metric.closedBall cS delta := by
    calc
      closure Side = closure (chart '' SideC) := rfl
      _ = chart '' closure SideC := (chart.image_closure SideC).symm
      _ = chart '' Metric.closedBall cS delta := by
        rw [show closure SideC = Metric.closedBall cS delta by
          exact closure_ball cS hdelta.ne']
  have hBridgeOpen : IsOpen Bridge := by
    exact chart.isOpenMap _ Metric.isOpen_ball
  have hSideOpen : IsOpen Side := by
    exact chart.isOpenMap _ Metric.isOpen_ball
  have hBridgeConvex : Convex ℝ Bridge := by
    have hlin : Convex ℝ (L '' BridgeC) :=
      (convex_ball cB delta).linear_image L
    have htrans : Convex ℝ ((fun z : E => x + z) '' (L '' BridgeC)) :=
      hlin.translate x
    simpa only [Bridge, chart, hchart_apply, Set.image_image,
      Function.comp_apply] using htrans
  have hSideConvex : Convex ℝ Side := by
    have hlin : Convex ℝ (L '' SideC) :=
      (convex_ball cS delta).linear_image L
    have htrans : Convex ℝ ((fun z : E => x + z) '' (L '' SideC)) :=
      hlin.translate x
    simpa only [Side, chart, hchart_apply, Set.image_image,
      Function.comp_apply] using htrans
  have hBridgeCompact : IsCompact (closure Bridge) := by
    rw [hclosureBridge]
    exact (isCompact_closedBall cB delta).image chart.continuous
  have hSideCompact : IsCompact (closure Side) := by
    rw [hclosureSide]
    exact (isCompact_closedBall cS delta).image chart.continuous
  have hqBridgeClosure : quadrantGate ∈ closure Bridge := by
    rw [hclosureBridge]
    exact ⟨qC, hq_closedBridge, rfl⟩
  have hsideBridgeClosure : sideSource ∈ closure Bridge := by
    rw [hclosureBridge]
    exact ⟨sideC, hside_closedBridge, rfl⟩
  have hsideSideClosure : sideSource ∈ closure Side := by
    rw [hclosureSide]
    exact ⟨sideC, hside_closedSide, rfl⟩
  have hgateSideClosure : terminalGate ∈ closure Side := by
    rw [hclosureSide]
    exact ⟨gateC, hgate_closedSide, rfl⟩
  have hq_notBridge : quadrantGate ∉ Bridge := by
    rintro ⟨z, hz, hEq⟩
    have hzq : z = qC := chart.injective (hEq.trans rfl)
    subst z
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [show qC - cB = -(delta • one) by simp [qC, cB],
      norm_neg, hdelta_norm] at hz
    exact (lt_irrefl delta hz)
  have hside_notBridge : sideSource ∉ Bridge := by
    rintro ⟨z, hz, hEq⟩
    have hzq : z = sideC := chart.injective (hEq.trans rfl)
    subst z
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [show sideC - cB = delta • one by
      dsimp [sideC, cB]
      module, hdelta_norm] at hz
    exact (lt_irrefl delta hz)
  have hside_notSide : sideSource ∉ Side := by
    rintro ⟨z, hz, hEq⟩
    have hzq : z = sideC := chart.injective (hEq.trans rfl)
    subst z
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [show sideC - cS = -(delta • one) by
      dsimp [sideC, cS]
      module, norm_neg, hdelta_norm] at hz
    exact (lt_irrefl delta hz)
  have hgate_notSide : terminalGate ∉ Side := by
    rintro ⟨z, hz, hEq⟩
    have hzq : z = gateC := chart.injective (hEq.trans rfl)
    subst z
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [show gateC - cS = delta • one by
      dsimp [gateC, cS]
      module, hdelta_norm] at hz
    exact (lt_irrefl delta hz)
  have coord_bounds (c z : C) (hz : z ∈ Metric.closedBall c delta)
      (i : Fin 2) : c i - delta ≤ z i ∧ z i ≤ c i + delta := by
    have hnorm : ‖z - c‖ ≤ delta := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      exact hz
    have hcomp : ‖(z - c) i‖ ≤ delta :=
      (norm_le_pi_norm (z - c) i).trans hnorm
    rw [Real.norm_eq_abs] at hcomp
    have habs := (abs_le.mp hcomp)
    change -delta ≤ z i - c i ∧ z i - c i ≤ delta at habs
    constructor <;> linarith
  let Half : Set E :=
    {z | k * (chart.symm z) 0 ≤ (chart.symm z) 1}
  have hHalfClosed : IsClosed Half := by
    let f : E → ℝ := fun z => k * (chart.symm z) 0
    let g : E → ℝ := fun z => (chart.symm z) 1
    have hf : Continuous f := by
      dsimp [f]
      fun_prop
    have hg : Continuous g := by
      dsimp [g]
      fun_prop
    exact isClosed_le hf hg
  have hQHalf : Q ⊆ Half := by
    intro z hzQ
    by_cases hzy : z = x + t • dB
    · subst z
      let y0 : C := ![0, t]
      have hcharty : chart y0 = x + t • dB := by
        rw [hchart_apply, hL_apply]
        simp [y0]
      change k * (chart.symm (x + t • dB)) 0 ≤
        (chart.symm (x + t • dB)) 1
      rw [← hcharty]
      simp [y0, le_of_lt ht]
    · have hzDiff : z ∈ Q \ ({x + t • dB} : Set E) := ⟨hzQ, by simpa⟩
      obtain ⟨a, b, _ha, _hb, hab, _habsum, hz⟩ := hQsector hzDiff
      let ab : C := ![a, b]
      have hchartab : chart ab = z := by
        rw [hchart_apply, hL_apply]
        simpa [ab, add_assoc] using hz.symm
      change k * (chart.symm z) 0 ≤ (chart.symm z) 1
      rw [← hchartab]
      simpa [ab] using hab
  have hQclosureHalf : closure Q ⊆ Half :=
    closure_minimal hQHalf hHalfClosed
  have hsideBridgeIntersection :
      closure Side ∩ closure Bridge = ({sideSource} : Set E) := by
    ext z
    constructor
    · rintro ⟨hzS, hzB⟩
      rw [hclosureSide] at hzS
      rw [hclosureBridge] at hzB
      rcases hzS with ⟨zS, hzS, rfl⟩
      rcases hzB with ⟨zB, hzB, hEq⟩
      have hzBS : zB = zS := chart.injective hEq
      subst zB
      have hS0 := coord_bounds cS zS hzS 0
      have hS1 := coord_bounds cS zS hzS 1
      have hB0 := coord_bounds cB zS hzB 0
      have hB1 := coord_bounds cB zS hzB 1
      have hzC : zS = sideC := by
        funext i
        have hi : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by omega
        rcases hi with rfl | rfl
        · rw [hcS0] at hS0
          rw [hcB0] at hB0
          rw [hsideC0]
          linarith
        · rw [hcS1] at hS1
          rw [hcB1] at hB1
          rw [hsideC1]
          linarith
      subst zS
      simp [sideSource]
    · intro hz
      have hz' : z = sideSource := by simpa using hz
      subst z
      exact ⟨hsideSideClosure, hsideBridgeClosure⟩
  have hSideQIntersection :
      closure Side ∩ closure Q = (∅ : Set E) := by
    ext z
    constructor
    · rintro ⟨hzS, hzQ⟩
      rw [hclosureSide] at hzS
      rcases hzS with ⟨zS, hzS, rfl⟩
      have hS0 := coord_bounds cS zS hzS 0
      have hS1 := coord_bounds cS zS hzS 1
      have hhalf := hQclosureHalf hzQ
      change k * (chart.symm (chart zS)) 0 ≤
        (chart.symm (chart zS)) 1 at hhalf
      have hhalf' : k * zS 0 ≤ zS 1 := by
        simpa only [Homeomorph.symm_apply_apply] using hhalf
      rw [hcS0] at hS0
      rw [hcS1] at hS1
      have hkdelta : 0 < k * delta := mul_pos hk hdelta
      exfalso
      rw [hkr] at hS1
      nlinarith [mul_le_mul_of_nonneg_left hS0.1 (le_of_lt hk)]
    · intro hz
      exact False.elim (by simpa using hz)
  have hBridgeQIntersection :
      closure Bridge ∩ closure Q = ({quadrantGate} : Set E) := by
    ext z
    constructor
    · rintro ⟨hzB, hzQ⟩
      rw [hclosureBridge] at hzB
      rcases hzB with ⟨zB, hzB, rfl⟩
      have hB0 := coord_bounds cB zB hzB 0
      have hB1 := coord_bounds cB zB hzB 1
      have hhalf := hQclosureHalf hzQ
      change k * (chart.symm (chart zB)) 0 ≤
        (chart.symm (chart zB)) 1 at hhalf
      have hhalf' : k * zB 0 ≤ zB 1 := by
        simpa only [Homeomorph.symm_apply_apply] using hhalf
      rw [hcB0] at hB0
      rw [hcB1] at hB1
      have hz0ge : s ≤ zB 0 := by linarith [hB0.1]
      have hz1le : zB 1 ≤ r := by linarith [hB1.2]
      have hkz0le : k * zB 0 ≤ k * s := by
        rw [← hkr]
        exact hhalf'.trans hz1le
      have hz0le : zB 0 ≤ s := by
        by_contra hz0not
        have hz0lt : s < zB 0 := lt_of_not_ge hz0not
        exact (not_lt_of_ge hkz0le) (mul_lt_mul_of_pos_left hz0lt hk)
      have hz0eq : zB 0 = s := le_antisymm hz0le hz0ge
      have hz1ge : r ≤ zB 1 := by
        rw [hkr, ← hz0eq]
        exact hhalf'
      have hz1eq : zB 1 = r := le_antisymm hz1le hz1ge
      have hzC : zB = qC := by
        funext i
        have hi : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by omega
        rcases hi with rfl | rfl
        · simpa [hqC0] using hz0eq
        · simpa [hqC1] using hz1eq
      subst zB
      simp [quadrantGate]
    · intro hz
      have hz' : z = quadrantGate := by simpa using hz
      subst z
      have hqGate0 : quadrantGate ∈ Q := by
        rw [hquadrant_formula]
        exact hquadrantGateQ
      exact ⟨hqBridgeClosure, subset_closure hqGate0⟩
  have hchart_affine (a b : C) (theta : ℝ) :
      (1 - theta) • chart a + theta • chart b =
        chart ((1 - theta) • a + theta • b) := by
    simp only [hchart_apply, map_add, map_smul]
    module
  have hOpenGateSide :
      openSegment ℝ terminalGate sideSource ⊆ Side := by
    rw [openSegment_eq_image]
    rintro z ⟨theta, htheta, rfl⟩
    change (1 - theta) • chart gateC + theta • chart sideC ∈ Side
    rw [hchart_affine]
    refine ⟨(1 - theta) • gateC + theta • sideC, ?_, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hcoord :
        (1 - theta) • gateC + theta • sideC - cS =
          (1 - 2 * theta) • (delta • one) := by
      dsimp [gateC, sideC, cS]
      module
    rw [hcoord, norm_smul, hdelta_norm, Real.norm_eq_abs]
    have habs : |1 - 2 * theta| < 1 := by
      rw [abs_lt]
      constructor <;> nlinarith [htheta.1, htheta.2]
    simpa only [one_mul] using mul_lt_mul_of_pos_right habs hdelta
  have hGateSide :
      segment ℝ terminalGate sideSource ⊆
        Side ∪ ({terminalGate, sideSource} : Set E) := by
    rw [segment_eq_image]
    rintro z ⟨theta, htheta, rfl⟩
    rcases eq_or_lt_of_le htheta.1 with h0 | h0
    · right
      left
      subst theta
      simp
    · rcases eq_or_lt_of_le htheta.2 with h1 | h1
      · right
        right
        have : theta = 1 := h1
        subst theta
        simp
      · left
        apply hOpenGateSide
        rw [openSegment_eq_image]
        exact ⟨theta, ⟨h0, h1⟩, rfl⟩
  have hOpenSideQ :
      openSegment ℝ sideSource quadrantGate ⊆ Bridge := by
    rw [openSegment_eq_image]
    rintro z ⟨theta, htheta, rfl⟩
    change (1 - theta) • chart sideC + theta • chart qC ∈ Bridge
    rw [hchart_affine]
    refine ⟨(1 - theta) • sideC + theta • qC, ?_, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hcoord :
        (1 - theta) • sideC + theta • qC - cB =
          (1 - 2 * theta) • (delta • one) := by
      dsimp [sideC, qC, cB]
      module
    rw [hcoord, norm_smul, hdelta_norm, Real.norm_eq_abs]
    have habs : |1 - 2 * theta| < 1 := by
      rw [abs_lt]
      constructor <;> nlinarith [htheta.1, htheta.2]
    simpa only [one_mul] using mul_lt_mul_of_pos_right habs hdelta
  have hSideQ :
      segment ℝ sideSource quadrantGate ⊆
        Bridge ∪ ({sideSource, quadrantGate} : Set E) := by
    rw [segment_eq_image]
    rintro z ⟨theta, htheta, rfl⟩
    rcases eq_or_lt_of_le htheta.1 with h0 | h0
    · right
      left
      subst theta
      simp
    · rcases eq_or_lt_of_le htheta.2 with h1 | h1
      · right
        right
        have : theta = 1 := h1
        subst theta
        simp
      · left
        apply hOpenSideQ
        rw [openSegment_eq_image]
        exact ⟨theta, ⟨h0, h1⟩, rfl⟩
  have hSideQInter :
      segment ℝ sideSource quadrantGate ∩ Q =
        ({quadrantGate} : Set E) := by
    ext z
    constructor
    · rintro ⟨hzseg, hzQ⟩
      have hzClosure : z ∈ closure Bridge := by
        have hzCases := hSideQ hzseg
        rcases hzCases with hzB | hzEnd
        · exact subset_closure hzB
        · rcases hzEnd with rfl | rfl
          · exact hsideBridgeClosure
          · exact hqBridgeClosure
      have hzInter : z ∈ closure Bridge ∩ closure Q :=
        ⟨hzClosure, subset_closure hzQ⟩
      rw [hBridgeQIntersection] at hzInter
      simpa using hzInter
    · intro hz
      have hz' : z = quadrantGate := by simpa using hz
      subst z
      constructor
      · exact right_mem_segment ℝ sideSource quadrantGate
      · rw [hquadrant_formula]
        exact hquadrantGateQ
  have hgate_ne_side : terminalGate ≠ sideSource := by
    intro hEq
    have hC : gateC = sideC := chart.injective hEq
    have hfun := congrFun hC 0
    rw [hgateC0, hsideC0] at hfun
    linarith only [hfun, hdelta]
  have hside_ne_q : sideSource ≠ quadrantGate := by
    intro hEq
    have hC : sideC = qC := chart.injective hEq
    have hfun := congrFun hC 0
    rw [hsideC0, hqC0] at hfun
    linarith only [hfun, hdelta]
  have hqGate : quadrantGate ∈ Q := by
    rw [hquadrant_formula]
    exact hquadrantGateQ
  have hQsegment :
      segment ℝ quadrantGate (x + t • dB) ⊆ Q :=
    hQconvex.segment_subset hqGate hyQ
  have hside_repr :
      sideSource = x + (s + 2 * delta) • dA +
        (r - 2 * delta) • dB := by
    rw [show sideSource = chart sideC by rfl, hchart_apply, hL_apply,
      hsideC0, hsideC1]
    simp only [add_assoc]
  have hgate_repr :
      terminalGate = x + (s + 4 * delta) • dA +
        (r - 4 * delta) • dB := by
    rw [show terminalGate = chart gateC by rfl, hchart_apply, hL_apply,
      hgateC0, hgateC1]
    simp only [add_assoc]
  have hSideCoefficients :
      ∀ z ∈ closure Side, ∃ a b : ℝ,
        0 < a ∧ 0 < b ∧ a + b < t ∧ b < k * a ∧
          s + 2 * (r / 100) ≤ a ∧ a ≤ s + 4 * (r / 100) ∧
          r - 4 * (r / 100) ≤ b ∧ b ≤ r - 2 * (r / 100) ∧
          z = x + a • dA + b • dB := by
    intro z hz
    rw [hclosureSide] at hz
    rcases hz with ⟨zS, hzS, rfl⟩
    have hS0 := coord_bounds cS zS hzS 0
    have hS1 := coord_bounds cS zS hzS 1
    rw [hcS0] at hS0
    rw [hcS1] at hS1
    have hdelta_eq : delta = r / 100 := rfl
    have hkdelta : 0 < k * delta := mul_pos hk hdelta
    have hka : k * (s + 3 * delta - delta) ≤ k * zS 0 :=
      mul_le_mul_of_nonneg_left hS0.1 (le_of_lt hk)
    refine ⟨zS 0, zS 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith only [hS0.1, hs, hdelta]
    · linarith only [hS1.1, hdelta_eq, hr]
    · linarith only [hS0.2, hS1.2, hdelta_eq, hsum_eq, hs, hr]
    · rw [hkr] at hS1
      linarith only [hS1.2, hka, hdelta, hkdelta]
    · rw [← hdelta_eq]
      linarith
    · rw [← hdelta_eq]
      linarith
    · rw [← hdelta_eq]
      linarith
    · rw [← hdelta_eq]
      linarith
    · rw [hchart_apply, hL_apply]
      simp only [add_assoc]
  have hBridgeCoefficients :
      ∀ z ∈ closure Bridge, ∃ a b : ℝ,
        0 < a ∧ 0 < b ∧ a + b < t ∧ b ≤ k * a ∧
          s ≤ a ∧ a ≤ s + 2 * (r / 100) ∧
          r - 2 * (r / 100) ≤ b ∧ b ≤ r ∧
          z = x + a • dA + b • dB := by
    intro z hz
    rw [hclosureBridge] at hz
    rcases hz with ⟨zB, hzB, rfl⟩
    have hB0 := coord_bounds cB zB hzB 0
    have hB1 := coord_bounds cB zB hzB 1
    rw [hcB0] at hB0
    rw [hcB1] at hB1
    have hdelta_eq : delta = r / 100 := rfl
    refine ⟨zB 0, zB 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith only [hB0.1, hs]
    · linarith only [hB1.1, hdelta_eq, hr]
    · linarith only [hB0.2, hB1.2, hdelta_eq, hsum_eq, hs, hr]
    · calc
        zB 1 ≤ r := by linarith
        _ = k * s := hkr
        _ ≤ k * zB 0 :=
          mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hk)
    · linarith
    · rw [← hdelta_eq]
      linarith
    · rw [← hdelta_eq]
      linarith
    · linarith
    · rw [hchart_apply, hL_apply]
      simp only [add_assoc]
  rw [← hquadrant_formula]
  refine ⟨Side, Bridge, terminalGate, sideSource,
    hSideOpen, hSideConvex, hSideCompact,
    hBridgeOpen, hBridgeConvex, hBridgeCompact, hgateSideClosure,
    hgate_notSide, hsideSideClosure, hside_notSide, hsideBridgeClosure,
    hside_notBridge, hqBridgeClosure, hq_notBridge, hgate_ne_side,
    hside_ne_q, hGateSide, hOpenGateSide, hSideQ, hOpenSideQ,
    hSideQInter, hsideBridgeIntersection, hSideQIntersection,
    hBridgeQIntersection, hQsegment, hSideCoefficients, hBridgeCoefficients,
    delta, hdelta, rfl, hside_repr, hgate_repr⟩
