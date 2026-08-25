import Util.IncidenceGeometry.PlanarNonparallelHalfOpenTerminalTriangle
import Util.IncidenceGeometry.PlanarNonparallelTerminalCellChain
import Util.IncidenceGeometry.StraightSegmentPolygonalArc
import Util.IncidenceGeometry.CollinearAdjacentSubsegmentsMeetAtEndpoint
import Mathlib.Tactic

open Classical
noncomputable section

private lemma ordinaryAdjacentEdgesTerminalArcPackage :
    ∀ (SelectedSide Vin : Set (EuclideanSpace ℝ (Fin 2)))
      (h terminalGate dA dB : EuclideanSpace ℝ (Fin 2)) (q : ℝ),
      IsOpen Vin → Convex ℝ Vin → Vin ⊆ SelectedSide → h ∈ Vin →
      dB ≠ 0 → 0 < q → h = terminalGate + q • dA →
      LinearIndependent ℝ ![dA, dB] →
      ∃ predecessor approach : PolygonalArc,
        ∃ lastGate : EuclideanSpace ℝ (Fin 2),
          predecessor.carrier ⊆ SelectedSide ∩ Vin ∧
          approach.carrier ⊆ SelectedSide ∩ Vin ∧
          predecessor.target = lastGate ∧ approach.source = lastGate ∧
          predecessor.carrier ∩ approach.carrier = ({lastGate} : Set _) ∧
          approach.target = h ∧
          approach.carrier ∩ segment ℝ h terminalGate = ({h} : Set _) ∧
          Disjoint predecessor.carrier (segment ℝ h terminalGate) := by
  intro SelectedSide Vin h terminalGate dA dB q hVinOpen hVinConvex
    hVinSelected hhVin hdBne hq hhFormula hliScaled
  obtain ⟨epsH, hepsH, hballHVin⟩ :=
    (Metric.isOpen_iff.mp hVinOpen) h hhVin
  let tau : ℝ := epsH / (4 * (‖dB‖ + 1))
  have htau : 0 < tau := by dsimp [tau]; positivity
  let lastGate : EuclideanSpace ℝ (Fin 2) := h - tau • dB
  let predecessorSource : EuclideanSpace ℝ (Fin 2) := h - (2 * tau) • dB
  have hlast_ne_h : lastGate ≠ h := by
    intro heq
    have hzero : tau • dB = 0 := by
      dsimp [lastGate] at heq
      exact sub_eq_self.mp heq
    exact (smul_ne_zero htau.ne' hdBne) hzero
  have hpred_ne_last : predecessorSource ≠ lastGate := by
    intro heq
    have hzero : tau • dB = 0 := by
      dsimp [predecessorSource, lastGate] at heq
      have heq' : (2 * tau) • dB = tau • dB := sub_right_inj.mp heq
      calc
        tau • dB = (2 * tau) • dB - tau • dB := by module
        _ = 0 := by rw [heq']; simp
    exact (smul_ne_zero htau.ne' hdBne) hzero
  have hpred_ne_h : predecessorSource ≠ h := by
    intro heq
    have hzero : (2 * tau) • dB = 0 := by
      dsimp [predecessorSource] at heq
      exact sub_eq_self.mp heq
    exact (smul_ne_zero (by positivity : (2 * tau) ≠ 0) hdBne) hzero
  have hlastBall : lastGate ∈ Metric.ball h epsH := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : lastGate - h = -(tau • dB) := by simp [lastGate]
    rw [hdiff, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htau]
    dsimp [tau]
    have hden : 0 < 4 * (‖dB‖ + 1) := by positivity
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    exact mul_lt_mul_of_pos_left (by nlinarith only [norm_nonneg dB]) hepsH
  have hpredBall : predecessorSource ∈ Metric.ball h epsH := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : predecessorSource - h = -((2 * tau) • dB) := by
      simp [predecessorSource]
    rw [hdiff, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * tau)]
    dsimp [tau]
    have hden : 0 < 4 * (‖dB‖ + 1) := by positivity
    rw [show 2 * (epsH / (4 * (‖dB‖ + 1))) * ‖dB‖ =
        epsH * (2 * ‖dB‖) / (4 * (‖dB‖ + 1)) by ring]
    apply (div_lt_iff₀ hden).2
    exact mul_lt_mul_of_pos_left (by nlinarith only [norm_nonneg dB]) hepsH
  have hhBall : h ∈ Metric.ball h epsH := Metric.mem_ball_self hepsH
  have hpredSegmentVin : segment ℝ predecessorSource lastGate ⊆ Vin :=
    ((convex_ball h epsH).segment_subset hpredBall hlastBall).trans hballHVin
  have happSegmentVin : segment ℝ lastGate h ⊆ Vin :=
    ((convex_ball h epsH).segment_subset hlastBall hhBall).trans hballHVin
  obtain ⟨predecessor, _, hpredTarget, hpredCarrier, _⟩ :=
    StraightSegmentPolygonalArc predecessorSource lastGate hpred_ne_last
  obtain ⟨approach, happSource, happTarget, happCarrier, _⟩ :=
    StraightSegmentPolygonalArc lastGate h hlast_ne_h
  have hlastMid :
      AffineMap.lineMap predecessorSource h (1 / 2 : ℝ) = lastGate := by
    dsimp [predecessorSource, lastGate]
    simp only [AffineMap.lineMap_apply]
    norm_num
    module
  let u0 : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let u1 : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  let u2 : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have hPredApproachSegments :
      segment ℝ predecessorSource lastGate ∩ segment ℝ lastGate h =
        ({lastGate} : Set _) := by
    have hu01 : u0 < u1 := by change (0 : ℝ) < 1 / 2; norm_num
    have hu12 : u1 < u2 := by change (1 / 2 : ℝ) < 1; norm_num
    have hinter := CollinearAdjacentSubsegmentsMeetAtEndpoint
      predecessorSource h hpred_ne_h u0 u1 u2 hu01 hu12
    rw [← hlastMid]
    simpa [u0, u1, u2] using hinter
  have hPredApproach :
      predecessor.carrier ∩ approach.carrier = ({lastGate} : Set _) := by
    simpa [hpredCarrier, happCarrier] using hPredApproachSegments
  let basis : Fin 2 → EuclideanSpace ℝ (Fin 2) := ![dA, dB]
  let L : (Fin 2 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Fintype.linearCombination ℝ basis
  have hLapply (z : Fin 2 → ℝ) : L z = z 0 • dA + z 1 • dB := by
    dsimp [L]
    rw [Fintype.linearCombination_apply, Fin.sum_univ_two]
    simp [basis]
  have hLinj : Function.Injective L := by
    simpa [L, basis] using hliScaled.fintypeLinearCombination_injective
  have hLIApproachTerminal :
      LinearIndependent ℝ ![lastGate - h, terminalGate - h] := by
    have hfirst : lastGate - h ≠ 0 := sub_ne_zero.mpr hlast_ne_h
    rw [LinearIndependent.pair_iff' hfirst]
    intro c hc
    have hvec : (-q) • dA = (-c * tau) • dB := by
      have hlastvec : lastGate - h = (-tau) • dB := by simp [lastGate]
      have hgatevec : terminalGate - h = (-q) • dA := by
        rw [hhFormula]
        module
      rw [hlastvec, hgatevec] at hc
      calc
        (-q) • dA = c • ((-tau) • dB) := hc.symm
        _ = (-c * tau) • dB := by module
    have hLeq : L ![-q, 0] = L ![0, -c * tau] := by
      rw [hLapply, hLapply]
      simpa using hvec
    have hcoords := hLinj hLeq
    have hqzero : -q = 0 := by simpa using congrFun hcoords 0
    exact hq.ne' (neg_eq_zero.mp hqzero)
  have hApproachTerminalSegments :
      segment ℝ lastGate h ∩ segment ℝ h terminalGate = ({h} : Set _) := by
    have hinter := segment_inter_eq_endpoint_of_linearIndependent_sub
      (𝕜 := ℝ) (c := h) (x := lastGate) (y := terminalGate)
      hLIApproachTerminal
    simpa [segment_symm, Set.inter_comm] using hinter
  have hApproachTerminal :
      approach.carrier ∩ segment ℝ h terminalGate = ({h} : Set _) := by
    simpa [happCarrier] using hApproachTerminalSegments
  have hLIPredTerminal :
      LinearIndependent ℝ ![predecessorSource - h, terminalGate - h] := by
    have hfirst : predecessorSource - h ≠ 0 := sub_ne_zero.mpr hpred_ne_h
    rw [LinearIndependent.pair_iff' hfirst]
    intro c hc
    have hvec : (-q) • dA = (-c * (2 * tau)) • dB := by
      have hpredvec : predecessorSource - h = (-(2 * tau)) • dB := by
        simp [predecessorSource]
      have hgatevec : terminalGate - h = (-q) • dA := by
        rw [hhFormula]
        module
      rw [hpredvec, hgatevec] at hc
      calc
        (-q) • dA = c • ((-(2 * tau)) • dB) := hc.symm
        _ = (-c * (2 * tau)) • dB := by module
    have hLeq : L ![-q, 0] = L ![0, -c * (2 * tau)] := by
      rw [hLapply, hLapply]
      simpa using hvec
    have hcoords := hLinj hLeq
    have hqzero : -q = 0 := by simpa using congrFun hcoords 0
    exact hq.ne' (neg_eq_zero.mp hqzero)
  have hPredWholeTerminal :
      segment ℝ predecessorSource h ∩ segment ℝ h terminalGate = ({h} : Set _) := by
    have hinter := segment_inter_eq_endpoint_of_linearIndependent_sub
      (𝕜 := ℝ) (c := h) (x := predecessorSource) (y := terminalGate)
      hLIPredTerminal
    simpa [segment_symm, Set.inter_comm] using hinter
  have hPredSubsetWhole :
      segment ℝ predecessorSource lastGate ⊆ segment ℝ predecessorSource h := by
    apply (convex_segment predecessorSource h).segment_subset
    · exact left_mem_segment ℝ _ _
    · rw [← hlastMid]
      exact openSegment_subset_segment ℝ _ _
        (lineMap_mem_openSegment ℝ predecessorSource h ⟨by norm_num, by norm_num⟩)
  have hhNotPred : h ∉ segment ℝ predecessorSource lastGate := by
    intro hhPred
    have hhApproach : h ∈ segment ℝ lastGate h := right_mem_segment ℝ _ _
    have hhInter : h ∈ ({lastGate} : Set _) := by
      rw [← hPredApproachSegments]
      exact ⟨hhPred, hhApproach⟩
    exact hlast_ne_h (by simpa using hhInter.symm)
  have hPredTerminalDisjoint :
      Disjoint predecessor.carrier (segment ℝ h terminalGate) := by
    rw [Set.disjoint_left]
    intro p hpPred hpTerm
    have hpWhole : p ∈ segment ℝ predecessorSource h :=
      hPredSubsetWhole (by simpa [hpredCarrier] using hpPred)
    have hpInter : p ∈ ({h} : Set _) := by
      rw [← hPredWholeTerminal]
      exact ⟨hpWhole, hpTerm⟩
    have hpEq : p = h := by simpa using hpInter
    subst p
    exact hhNotPred (by simpa [hpredCarrier] using hpPred)
  have hpredSubset : predecessor.carrier ⊆ SelectedSide ∩ Vin := by
    intro p hp
    have hpVin := hpredSegmentVin (by simpa [hpredCarrier] using hp)
    exact ⟨hVinSelected hpVin, hpVin⟩
  have happSubset : approach.carrier ⊆ SelectedSide ∩ Vin := by
    intro p hp
    have hpVin := happSegmentVin (by simpa [happCarrier] using hp)
    exact ⟨hVinSelected hpVin, hpVin⟩
  exact ⟨predecessor, approach, lastGate, hpredSubset, happSubset,
    hpredTarget, happSource, hPredApproach, happTarget,
    hApproachTerminal, hPredTerminalDisjoint⟩


lemma OrdinaryAdjacentEdgesTerminalCollarCompatibility
    (x y d n : EuclideanSpace ℝ (Fin 2))
    (lambda mu nu kappa cap rho : ℝ)
    (SelectedSide Vin Old : Set (EuclideanSpace ℝ (Fin 2)))
    (Bad : Finset (EuclideanSpace ℝ (Fin 2)))
    (hlambda : 0 < lambda) (hlambda_one : lambda < 1)
    (hnu : 0 < nu) (hkappa : 0 < kappa) (hcap : 0 < cap)
    (hkappaSmall : kappa * (|mu| + 1) < nu / 4)
    (hrho : 0 < rho)
    (hd : d ≠ 0)
    (hdn : inner ℝ d n = 0)
    (hnd : inner ℝ n d = 0)
    (hdd : inner ℝ d d = ‖d‖ ^ 2)
    (hnn : inner ℝ n n = ‖d‖ ^ 2)
    (hy : y - x = mu • d + nu • n)
    (hli : LinearIndependent ℝ ![d, y - x])
    (hVinEq : Vin =
      (fun z : EuclideanSpace ℝ (Fin 2) => x + z 0 • d + z 1 • n) ''
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < cap ^ 2 ∧
          0 < z 1 ∧ z 1 < kappa * z 0})
    (hVinOpen : IsOpen Vin)
    (hVinSelected : Vin ⊆ SelectedSide)
    (hNear : ∃ eps : ℝ, 0 < eps ∧
      SelectedSide ∩ Metric.ball x eps ⊆ Vin)
    (hyBall : y ∈ Metric.ball x rho)
    (hsmallCap : 4 * lambda * (1 + |mu| + nu) < cap)
    (hcapRho : 2 * cap * ‖d‖ < rho)
    (hsmallRho : lambda * (‖d‖ + ‖y - x‖) < rho)
    (hOldLocal : Metric.closedBall x rho ∩ Old ⊆
      {z | ∃ c : ℝ, z = x + c • d} ∪
        {z | ∃ c : ℝ, z = x + c • (y - x)})
    (hyOld : y ∈ Old)
    (hBadLocal : Metric.closedBall x rho ∩ (Bad : Set _) ⊆
      ({x, y} : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∃ k : ℝ, 0 < k ∧
      ∃ Q Side Bridge : Set (EuclideanSpace ℝ (Fin 2)),
        ∃ terminalGate sideSource quadrantGate h :
            EuclideanSpace ℝ (Fin 2),
          ∃ predecessor approach : PolygonalArc,
            ∃ lastGate : EuclideanSpace ℝ (Fin 2),
              Convex ℝ Q ∧ IsCompact (closure Q) ∧
              x ∈ closure Q ∧ y ∈ Q ∧ x ∉ Q ∧
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
              quadrantGate ∈ Q ∧ quadrantGate ≠ y ∧
              segment ℝ sideSource quadrantGate ∩ Q = ({quadrantGate} : Set _) ∧
              closure Side ∩ closure Bridge = ({sideSource} : Set _) ∧
              closure Side ∩ closure Q = ∅ ∧
              closure Bridge ∩ closure Q = ({quadrantGate} : Set _) ∧
              segment ℝ quadrantGate y ⊆ Q ∧
              closure Q ⊆ Metric.closedBall x rho ∧
              Q ∩ Old = ({y} : Set _) ∧
              (Q \ ({y} : Set _)) ∩ (Bad : Set _) = ∅ ∧
              closure Side ⊆ Metric.ball x rho ∧
              closure Bridge ⊆ Metric.ball x rho ∧
              (closure Side ∪ closure Bridge) ∩ (Old ∪ (Bad : Set _)) = ∅ ∧
              IsOpen Vin ∧ Convex ℝ Vin ∧ h ∈ Vin ∧
              h ≠ terminalGate ∧ Vin ⊆ SelectedSide ∧
              x ∈ closure Vin ∧
              (∃ eps : ℝ, 0 < eps ∧ SelectedSide ∩ Metric.ball x eps ⊆ Vin) ∧
              Vin ⊆ Metric.ball x rho ∧
              Vin ∩ Q = ∅ ∧ Vin ∩ (Old ∪ (Bad : Set _)) = ∅ ∧
              terminalGate ∈ closure Vin ∧ terminalGate ∉ Vin ∧
              segment ℝ h terminalGate ⊆ Vin ∪ ({terminalGate} : Set _) ∧
              openSegment ℝ h terminalGate ⊆ Vin ∧
              closure Vin ∩ closure Side = ({terminalGate} : Set _) ∧
              closure Vin ∩ closure Bridge = ∅ ∧ Vin ∩ Side = ∅ ∧
              predecessor.carrier ⊆ SelectedSide ∩ Vin ∧
              approach.carrier ⊆ SelectedSide ∩ Vin ∧
              predecessor.target = lastGate ∧ approach.source = lastGate ∧
              predecessor.carrier ∩ approach.carrier = ({lastGate} : Set _) ∧
              approach.target = h ∧
              approach.carrier ∩ segment ℝ h terminalGate = ({h} : Set _) ∧
              Disjoint predecessor.carrier (segment ℝ h terminalGate) ∧
              (∀ z ∈ closure Side ∪ closure Bridge ∪ closure Q,
                kappa * inner ℝ (z - x) d - inner ℝ (z - x) n ≤ 0) ∧
              ∃ gateA gateB : ℝ, 0 < gateA ∧ 0 < gateB ∧
                gateB = kappa * gateA ∧
                terminalGate = x + gateA • d + gateB • n := by
  let dA := lambda • d
  let dB := y - x
  let denom := 24 * (nu - kappa * mu) - kappa * lambda
  let k := 25 * kappa * lambda / denom
  have habsmu : -|mu| ≤ mu ∧ mu ≤ |mu| := by
    exact ⟨neg_abs_le mu, le_abs_self mu⟩
  have hkappa_abs : kappa * |mu| < nu / 4 := by
    have hkappa_pos := hkappa
    nlinarith only [hkappaSmall, hkappa_pos]
  have hkappa_lt : kappa < nu / 4 := by
    have habs_nonneg : 0 ≤ |mu| := abs_nonneg mu
    have hkappa_pos := hkappa
    nlinarith only [hkappaSmall, hkappa_pos, habs_nonneg]
  have hkappa_lambda : kappa * lambda < nu / 4 := by
    nlinarith only [mul_lt_mul_of_pos_left hlambda_one hkappa, hkappa_lt]
  have hnu_mu : 3 * nu / 4 < nu - kappa * mu := by
    have hmul_le : kappa * mu ≤ kappa * |mu| :=
      mul_le_mul_of_nonneg_left habsmu.2 hkappa.le
    linarith only [hkappa_abs, hmul_le]
  have hdenom : 0 < denom := by
    dsimp [denom]
    nlinarith only [hnu_mu, hkappa_lambda, hnu]
  have hkpos : 0 < k := by
    dsimp [k]
    positivity
  have hkdenom : k * denom = 25 * kappa * lambda := by
    dsimp [k]
    field_simp [hdenom.ne']
  have hdenom_large : 25 * nu / 4 < denom := by
    dsimp [denom]
    nlinarith only [hnu_mu, hkappa_lambda, hnu]
  have hk_lt_lambda : k < lambda := by
    by_contra hnot
    have hlk : lambda ≤ k := le_of_not_gt hnot
    have hmul1 : lambda * denom ≤ k * denom :=
      mul_le_mul_of_nonneg_right hlk hdenom.le
    have hmul2 : 25 * kappa * lambda < 25 * nu / 4 * lambda := by
      nlinarith only [mul_lt_mul_of_pos_right hkappa_lt hlambda]
    have hmul3 : 25 * nu / 4 * lambda < denom * lambda :=
      mul_lt_mul_of_pos_right hdenom_large hlambda
    rw [hkdenom] at hmul1
    nlinarith only [hmul1, hmul2, hmul3]
  have hdA_ne : dA ≠ 0 := by
    dsimp [dA]
    exact smul_ne_zero hlambda.ne' hd
  have hliScaled : LinearIndependent ℝ ![dA, dB] := by
    rw [LinearIndependent.pair_iff' hdA_ne]
    intro c hc
    have hpair := hli
    rw [LinearIndependent.pair_iff' hd] at hpair
    apply hpair (c * lambda)
    dsimp [dA, dB] at hc ⊢
    simpa [smul_smul] using hc
  have hdB_ne : dB ≠ 0 := by
    have hpair := hliScaled
    rw [LinearIndependent.pair_iff' hdA_ne] at hpair
    intro hdB0
    apply hpair 0
    simp [hdB0]
  obtain ⟨Q, hQconvex, hQcompact, hxQ, hyQ, hxnotQ, hQwitness,
      hQsector, hQlines⟩ :=
    PlanarNonparallelHalfOpenTerminalTriangle x dA dB 1 k
      (by norm_num) hkpos hliScaled
  rcases hQwitness with
    ⟨quadrantGate, hquadrantQ, hquadrantNe, s, r, hs, hr, hrks,
      hsum, hsumEq, hquadrantFormula⟩
  obtain ⟨Side, Bridge, terminalGate, sideSource,
      hSideOpen, hSideConvex, hSideCompact,
      hBridgeOpen, hBridgeConvex, hBridgeCompact,
      hterminalSideClosure, hterminalNotSide,
      hsourceSideClosure, hsourceNotSide,
      hsourceBridgeClosure, hsourceNotBridge,
      hquadrantBridgeClosure, hquadrantNotBridge,
      hterminalNeSource, hsourceNeQuadrant,
      hterminalSourceSegment, hterminalSourceOpen,
      hsourceQuadrantSegment, hsourceQuadrantOpen,
      hsourceQuadrantQ, hSideBridgeClosure, hSideQClosure,
      hBridgeQClosure, hquadrantYSegment,
      hSideBox, hBridgeBox, delta, hdelta, hdeltaEq,
      hsourceFormula, hterminalFormula⟩ :=
    PlanarNonparallelTerminalCellChain x dA dB 1 k Q quadrantGate s r
      (by norm_num) hkpos hliScaled hs hr hrks hsumEq hquadrantFormula
      hQconvex hquadrantQ hyQ hQsector
  have hsumHalf : s + r = 1 / 2 := by simpa using hsumEq
  have hs_lt_one : s < 1 := by linarith only [hsumHalf, hr]
  have hr_lt_k : r < k := by
    rw [hrks]
    exact mul_lt_of_lt_one_right hkpos hs_lt_one
  let gateA0 := s + 4 * (r / 100)
  let gateB0 := r - 4 * (r / 100)
  have hgateApos : 0 < gateA0 := by dsimp [gateA0]; positivity
  have hgateBpos : 0 < gateB0 := by
    dsimp [gateB0]
    nlinarith only [hr]
  have hk_formula : k * denom = 25 * kappa * lambda := hkdenom
  have hgateAlign : gateB0 * nu =
      kappa * (gateA0 * lambda + gateB0 * mu) := by
    have hbase : 24 * k * nu =
        kappa * (25 * lambda + k * lambda + 24 * k * mu) := by
      dsimp only [denom] at hkdenom
      linear_combination hkdenom
    dsimp only [gateA0, gateB0]
    rw [hrks]
    linear_combination (s / 25) * hbase
  have hterminalActual :
      terminalGate = x + gateA0 • dA + gateB0 • dB := by
    rw [hterminalFormula, hdeltaEq]
  have hterminalChart :
      terminalGate = x + (gateA0 * lambda + gateB0 * mu) • d +
        (gateB0 * nu) • n := by
    rw [hterminalActual]
    dsimp [dA, dB]
    rw [hy]
    module
  have hgateCoordPos : 0 < gateA0 * lambda + gateB0 * mu := by
    have heq : gateA0 * lambda + gateB0 * mu = gateB0 * nu / kappa := by
      apply (eq_div_iff hkappa.ne').2
      simpa [mul_comm] using hgateAlign.symm
    rw [heq]
    exact div_pos (mul_pos hgateBpos hnu) hkappa
  have hterminalBoundary :
      gateB0 * nu = kappa * (gateA0 * lambda + gateB0 * mu) :=
    hgateAlign
  have hnormd_pos : 0 < ‖d‖ := (norm_pos_iff.mpr hd)
  have hnormsq_pos : 0 < ‖d‖ ^ 2 := sq_pos_of_pos hnormd_pos
  have hgateA_lt_one : gateA0 < 1 := by
    dsimp [gateA0]
    nlinarith only [hsumHalf, hr]
  have hgateB_lt_lambda : gateB0 < lambda := by
    dsimp [gateB0]
    nlinarith only [hr, hr_lt_k, hk_lt_lambda]
  have hgateZ0_abs :
      |gateA0 * lambda + gateB0 * mu| < lambda * (1 + |mu|) := by
    calc
      |gateA0 * lambda + gateB0 * mu| ≤
          |gateA0 * lambda| + |gateB0 * mu| := abs_add_le _ _
      _ = gateA0 * lambda + gateB0 * |mu| := by
        rw [abs_mul, abs_mul, abs_of_pos hgateApos, abs_of_pos hlambda,
          abs_of_pos hgateBpos]
      _ < lambda + lambda * |mu| := by
        have h1 : gateA0 * lambda < lambda := by
          nlinarith only [mul_lt_mul_of_pos_right hgateA_lt_one hlambda]
        have h2 : gateB0 * |mu| ≤ lambda * |mu| :=
          mul_le_mul_of_nonneg_right hgateB_lt_lambda.le (abs_nonneg mu)
        linarith only [h1, h2]
      _ = lambda * (1 + |mu|) := by ring
  have hgateZ1_lt : gateB0 * nu < lambda * nu :=
    mul_lt_mul_of_pos_right hgateB_lt_lambda hnu
  have hcoordSumSmall :
      |gateA0 * lambda + gateB0 * mu| + gateB0 * nu < cap / 4 := by
    have hsmall : lambda * (1 + |mu| + nu) < cap / 4 := by
      nlinarith only [hsmallCap]
    nlinarith only [hgateZ0_abs, hgateZ1_lt, hsmall]
  have hgateRadial :
      (gateA0 * lambda + gateB0 * mu) ^ 2 + (gateB0 * nu) ^ 2 < cap ^ 2 := by
    have hsquareAbs :
        |gateA0 * lambda + gateB0 * mu| ^ 2 =
          (gateA0 * lambda + gateB0 * mu) ^ 2 := sq_abs _
    have hsum_pos : 0 ≤
        |gateA0 * lambda + gateB0 * mu| + gateB0 * nu := by
      positivity
    have hsum_sq :
        (gateA0 * lambda + gateB0 * mu) ^ 2 + (gateB0 * nu) ^ 2 ≤
          (|gateA0 * lambda + gateB0 * mu| + gateB0 * nu) ^ 2 := by
      rw [← hsquareAbs]
      nlinarith only [abs_nonneg (gateA0 * lambda + gateB0 * mu),
        mul_nonneg hgateBpos.le hnu.le]
    have hquarter : cap / 4 < cap := by linarith only [hcap]
    have hsq_lt :
        (|gateA0 * lambda + gateB0 * mu| + gateB0 * nu) ^ 2 < cap ^ 2 :=
      (sq_lt_sq₀ hsum_pos hcap.le).2 (hcoordSumSmall.trans hquarter)
    exact hsum_sq.trans_lt hsq_lt
  let phi : EuclideanSpace ℝ (Fin 2) → ℝ := fun p =>
    kappa * inner ℝ (p - x) d - inner ℝ (p - x) n
  have hphi_cont : Continuous phi := by
    dsimp [phi]
    fun_prop
  have hphi_cell (a b : ℝ) :
      phi (x + a • dA + b • dB) =
        ‖d‖ ^ 2 * (kappa * (a * lambda + b * mu) - b * nu) := by
    dsimp [phi, dA, dB]
    rw [show x + a • (lambda • d) + b • (y - x) - x =
      a • (lambda • d) + b • (y - x) by abel]
    rw [hy]
    simp only [inner_add_left, inner_smul_left]
    rw [hdn, hnd, hdd, hnn]
    simp only [starRingEnd_apply, star_trivial]
    ring
  have hphi_y : phi y < 0 := by
    have hyform : y = x + (0 : ℝ) • dA + (1 : ℝ) • dB := by
      dsimp [dB]
      simp
    have hvalue : phi y =
        ‖d‖ ^ 2 * (kappa * ((0 : ℝ) * lambda + 1 * mu) - 1 * nu) := by
      rw [hyform]
      exact hphi_cell 0 1
    rw [hvalue]
    have hnuDiff : kappa * mu - nu < 0 := by
      have hmul_le : kappa * mu ≤ kappa * |mu| :=
        mul_le_mul_of_nonneg_left habsmu.2 hkappa.le
      linarith only [hkappa_abs, hmul_le, hnu]
    simpa using mul_neg_of_pos_of_neg hnormsq_pos hnuDiff
  have hphi_x : phi x = 0 := by simp [phi]
  let basis : Fin 2 → EuclideanSpace ℝ (Fin 2) := ![dA, dB]
  let L : (Fin 2 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Fintype.linearCombination ℝ basis
  have hLapply (z : Fin 2 → ℝ) : L z = z 0 • dA + z 1 • dB := by
    dsimp [L]
    rw [Fintype.linearCombination_apply, Fin.sum_univ_two]
    simp [basis]
  have hLinj : Function.Injective L := by
    simpa [L, basis] using hliScaled.fintypeLinearCombination_injective
  have hcoeff_unique {a b a' b' : ℝ}
      (heq : x + a • dA + b • dB = x + a' • dA + b' • dB) :
      a = a' ∧ b = b' := by
    have hLeq : L ![a, b] = L ![a', b'] := by
      rw [hLapply, hLapply]
      apply add_left_cancel (a := x)
      simpa [add_assoc] using heq
    have hz := hLinj hLeq
    exact ⟨by simpa using congrFun hz 0, by simpa using congrFun hz 1⟩
  have hnuDiff : 0 < nu - kappa * mu := by linarith only [hnu_mu, hnu]
  have hsupport_identity (a b : ℝ) :
      gateA0 * (kappa * (a * lambda + b * mu) - b * nu) =
        (nu - kappa * mu) * (gateB0 * a - gateA0 * b) := by
    have hcoeff : gateA0 * kappa * lambda =
        gateB0 * (nu - kappa * mu) := by
      calc
        gateA0 * kappa * lambda =
            kappa * (gateA0 * lambda + gateB0 * mu) -
              gateB0 * kappa * mu := by ring
        _ = gateB0 * nu - gateB0 * kappa * mu := by rw [← hgateAlign]
        _ = gateB0 * (nu - kappa * mu) := by ring
    calc
      gateA0 * (kappa * (a * lambda + b * mu) - b * nu) =
          (gateA0 * kappa * lambda) * a -
            gateA0 * (nu - kappa * mu) * b := by ring
      _ = (nu - kappa * mu) * (gateB0 * a - gateA0 * b) := by
        rw [hcoeff]
        ring
  have hSidePhi : ∀ z ∈ closure Side, phi z ≤ 0 := by
    intro z hz
    rcases hSideBox z hz with
      ⟨a, b, ha, hb, hab, hbk, haLo, haHi, hbLo, hbHi, rfl⟩
    rw [hphi_cell]
    have hsupport : gateB0 * a ≤ gateA0 * b := by
      calc
        gateB0 * a ≤ gateB0 * gateA0 :=
          mul_le_mul_of_nonneg_left haHi hgateBpos.le
        _ = gateA0 * gateB0 := mul_comm _ _
        _ ≤ gateA0 * b := mul_le_mul_of_nonneg_left hbLo hgateApos.le
    have hid := hsupport_identity a b
    have hexpr : kappa * (a * lambda + b * mu) - b * nu ≤ 0 := by
      have hrhs :
          (nu - kappa * mu) * (gateB0 * a - gateA0 * b) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hnuDiff.le (sub_nonpos.mpr hsupport)
      apply le_of_mul_le_mul_left (a := gateA0) (c := 0) ?_ hgateApos
      calc
        gateA0 * (kappa * (a * lambda + b * mu) - b * nu) =
            (nu - kappa * mu) * (gateB0 * a - gateA0 * b) := hid
        _ ≤ 0 := hrhs
        _ = gateA0 * 0 := by ring
    exact mul_nonpos_of_nonneg_of_nonpos hnormsq_pos.le hexpr
  have hBridgePhi : ∀ z ∈ closure Bridge, phi z < 0 := by
    intro z hz
    rcases hBridgeBox z hz with
      ⟨a, b, ha, hb, hab, hbk, haLo, haHi, hbLo, hbHi, rfl⟩
    rw [hphi_cell]
    have hsupport : gateB0 * a < gateA0 * b := by
      have hgateBLtB : gateB0 < b := by
        dsimp [gateB0]
        nlinarith only [hbLo, hr]
      have haGate : a ≤ gateA0 := by
        dsimp [gateA0]
        nlinarith only [haHi, hr]
      calc
        gateB0 * a < b * a := mul_lt_mul_of_pos_right hgateBLtB ha
        _ ≤ b * gateA0 := mul_le_mul_of_nonneg_left haGate hb.le
        _ = gateA0 * b := mul_comm _ _
    have hid := hsupport_identity a b
    have hexpr : kappa * (a * lambda + b * mu) - b * nu < 0 := by
      have hrhs :
          (nu - kappa * mu) * (gateB0 * a - gateA0 * b) < 0 :=
        mul_neg_of_pos_of_neg hnuDiff (sub_neg.mpr hsupport)
      apply lt_of_mul_lt_mul_left (a := gateA0) (c := 0) ?_ hgateApos.le
      calc
        gateA0 * (kappa * (a * lambda + b * mu) - b * nu) =
            (nu - kappa * mu) * (gateB0 * a - gateA0 * b) := hid
        _ < 0 := hrhs
        _ = gateA0 * 0 := by ring
    exact mul_neg_of_pos_of_neg hnormsq_pos hexpr
  have hVinPhi : ∀ z ∈ Vin, 0 < phi z := by
    intro p hp
    rw [hVinEq] at hp
    rcases hp with ⟨z, ⟨hz0, hzrad, hz1, hzK⟩, rfl⟩
    dsimp [phi]
    rw [show x + z 0 • d + z 1 • n - x = z 0 • d + z 1 • n by abel]
    simp only [inner_add_left, inner_smul_left]
    rw [hdn, hnd, hdd, hnn]
    simp only [starRingEnd_apply, star_trivial]
    nlinarith only [hnormsq_pos, hzK]
  have hclosureVinPhi : ∀ z ∈ closure Vin, 0 ≤ phi z := by
    have hsub : Vin ⊆ {z | 0 ≤ phi z} := fun z hz => (hVinPhi z hz).le
    have hclosed : IsClosed {z | 0 ≤ phi z} :=
      isClosed_le continuous_const hphi_cont
    exact closure_minimal hsub hclosed
  let C : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < cap ^ 2 ∧
      0 < z 1 ∧ z 1 < kappa * z 0}
  have hnormCoord (z : EuclideanSpace ℝ (Fin 2)) :
      ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp
  have hCconvex : Convex ℝ C := by
    rw [convex_iff_add_mem]
    intro z hz w hw a b ha hb hab
    rcases hz with ⟨hz0, hzrad, hz1, hzK⟩
    rcases hw with ⟨hw0, hwrad, hw1, hwK⟩
    have hzball : z ∈ Metric.ball 0 cap := by
      rw [Metric.mem_ball, dist_zero_right]
      apply (sq_lt_sq₀ (norm_nonneg z) hcap.le).1
      simpa [hnormCoord] using hzrad
    have hwball : w ∈ Metric.ball 0 cap := by
      rw [Metric.mem_ball, dist_zero_right]
      apply (sq_lt_sq₀ (norm_nonneg w) hcap.le).1
      simpa [hnormCoord] using hwrad
    have hcombBall := (convex_iff_add_mem.mp
      (convex_ball (0 : EuclideanSpace ℝ (Fin 2)) cap))
      hzball hwball ha hb hab
    have hcombNorm : ‖a • z + b • w‖ ^ 2 < cap ^ 2 := by
      apply (sq_lt_sq₀ (norm_nonneg _) hcap.le).2
      simpa [Metric.mem_ball, dist_zero_right] using hcombBall
    refine ⟨?_, ?_, ?_, ?_⟩
    · change 0 < a * z 0 + b * w 0
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith only [hab, ha0]
        simpa [ha0, hb1] using hw0
      · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        exact add_pos_of_pos_of_nonneg (mul_pos hapos hz0) (mul_nonneg hb hw0.le)
    · simpa [hnormCoord] using hcombNorm
    · change 0 < a * z 1 + b * w 1
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith only [hab, ha0]
        simpa [ha0, hb1] using hw1
      · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        exact add_pos_of_pos_of_nonneg (mul_pos hapos hz1) (mul_nonneg hb hw1.le)
    · change a * z 1 + b * w 1 < kappa * (a * z 0 + b * w 0)
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith only [hab, ha0]
        simpa [ha0, hb1] using hwK
      · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hza' := mul_lt_mul_of_pos_left hzK hapos
        by_cases hb0 : b = 0
        · have ha1 : a = 1 := by linarith only [hab, hb0]
          simpa [ha1, hb0] using hzK
        · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
          have hwb' := mul_lt_mul_of_pos_left hwK hbpos
          calc
            a * z 1 + b * w 1 < a * (kappa * z 0) + b * (kappa * w 0) :=
              add_lt_add hza' hwb'
            _ = kappa * (a * z 0 + b * w 0) := by ring
  let basisDN : Fin 2 → EuclideanSpace ℝ (Fin 2) := ![d, n]
  let LDN : (Fin 2 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Fintype.linearCombination ℝ basisDN
  have hLDNapply (z : Fin 2 → ℝ) : LDN z = z 0 • d + z 1 • n := by
    dsimp [LDN]
    rw [Fintype.linearCombination_apply, Fin.sum_univ_two]
    simp [basisDN]
  have hdnLI : LinearIndependent ℝ ![d, n] := by
    rw [LinearIndependent.pair_iff' hd]
    intro c hc
    have hpair := hli
    rw [LinearIndependent.pair_iff' hd] at hpair
    apply hpair (mu + nu * c)
    calc
      (mu + nu * c) • d = mu • d + nu • (c • d) := by module
      _ = mu • d + nu • n := by rw [hc]
      _ = y - x := hy.symm
  have hLDNinj : Function.Injective LDN := by
    simpa [LDN, basisDN] using hdnLI.fintypeLinearCombination_injective
  have hDN_unique {a b a' b' : ℝ}
      (heq : x + a • d + b • n = x + a' • d + b' • n) :
      a = a' ∧ b = b' := by
    have hLeq : LDN ![a, b] = LDN ![a', b'] := by
      rw [hLDNapply, hLDNapply]
      apply add_left_cancel (a := x)
      simpa [add_assoc] using heq
    have hz := hLDNinj hLeq
    exact ⟨by simpa using congrFun hz 0, by simpa using congrFun hz 1⟩
  have hVinConvex : Convex ℝ Vin := by
    rw [hVinEq]
    rw [convex_iff_add_mem]
    rintro p ⟨zp, hzp, rfl⟩ q ⟨zq, hzq, rfl⟩ a b ha hb hab
    let z := a • zp + b • zq
    have hz : z ∈ C :=
      (convex_iff_add_mem.mp hCconvex) hzp hzq ha hb hab
    refine ⟨z, hz, ?_⟩
    dsimp [z]
    calc
      x + (a * zp 0 + b * zq 0) • d + (a * zp 1 + b * zq 1) • n =
          (a + b) • x + (a * zp 0 + b * zq 0) • d +
            (a * zp 1 + b * zq 1) • n := by rw [hab, one_smul]
      _ = a • (x + zp 0 • d + zp 1 • n) +
          b • (x + zq 0 • d + zq 1 • n) := by module
  have hnormn : ‖n‖ = ‖d‖ := by
    have hnself : inner ℝ n n = ‖n‖ ^ 2 := real_inner_self_eq_norm_sq n
    have hsquares : ‖n‖ ^ 2 = ‖d‖ ^ 2 := by linarith only [hnself, hnn]
    nlinarith only [hsquares, norm_nonneg n, norm_nonneg d]
  have hVinBall : Vin ⊆ Metric.ball x rho := by
    intro p hp
    rw [hVinEq] at hp
    rcases hp with ⟨z, ⟨hz0, hzrad, hz1, hzK⟩, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : (x + z 0 • d + z 1 • n) - x =
        z 0 • d + z 1 • n := by abel
    rw [hdiff]
    have hz0abs : |z 0| < cap := by
      have hz0sq : z 0 ^ 2 < cap ^ 2 := by
        nlinarith only [hzrad, sq_nonneg (z 1)]
      exact (sq_lt_sq.mp hz0sq).trans_eq (abs_of_pos hcap)
    have hz1abs : |z 1| < cap := by
      have hz1sq : z 1 ^ 2 < cap ^ 2 := by
        nlinarith only [hzrad, sq_nonneg (z 0)]
      exact (sq_lt_sq.mp hz1sq).trans_eq (abs_of_pos hcap)
    calc
      ‖z 0 • d + z 1 • n‖ ≤ ‖z 0 • d‖ + ‖z 1 • n‖ := norm_add_le _ _
      _ = |z 0| * ‖d‖ + |z 1| * ‖d‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hnormn]
      _ < cap * ‖d‖ + cap * ‖d‖ := by
        exact add_lt_add
          (mul_lt_mul_of_pos_right hz0abs hnormd_pos)
          (mul_lt_mul_of_pos_right hz1abs hnormd_pos)
      _ = 2 * cap * ‖d‖ := by ring
      _ < rho := hcapRho
  have hdABall : ‖dA‖ < rho := by
    rw [show ‖dA‖ = lambda * ‖d‖ by
      simp [dA, norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]]
    calc
      lambda * ‖d‖ ≤ lambda * (‖d‖ + ‖y - x‖) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (norm_nonneg (y - x))) hlambda.le
      _ < rho := hsmallRho
  have hdBBall : ‖dB‖ < rho := by
    dsimp [dB]
    simpa [Metric.mem_ball, dist_eq_norm] using hyBall
  have hQBall : Q ⊆ Metric.ball x rho := by
    intro p hp
    by_cases hpy : p = y
    · simpa [hpy] using hyBall
    · have hpsector : p ∈ Q \ ({y} : Set _) := by
        exact ⟨hp, by simpa⟩
      have hyform : x + (1 : ℝ) • dB = y := by simp [dB]
      have hpsector' : p ∈ Q \ ({x + (1 : ℝ) • dB} : Set _) := by
        refine ⟨hp, ?_⟩
        intro hpEq
        exact hpsector.2 (hpEq.trans hyform)
      rcases hQsector hpsector' with ⟨a, b, ha, hb, hkab, hab, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm]
      have hdiff : (x + a • dA + b • dB) - x = a • dA + b • dB := by
        abel
      rw [hdiff]
      have haNorm : a * ‖dA‖ < a * rho :=
        mul_lt_mul_of_pos_left hdABall ha
      have hbNorm : b * ‖dB‖ < b * rho :=
        mul_lt_mul_of_pos_left hdBBall hb
      calc
        ‖a • dA + b • dB‖ ≤ ‖a • dA‖ + ‖b • dB‖ := norm_add_le _ _
        _ = a * ‖dA‖ + b * ‖dB‖ := by simp [norm_smul, abs_of_pos ha, abs_of_pos hb]
        _ < a * rho + b * rho := add_lt_add haNorm hbNorm
        _ < rho := by nlinarith only [hab, hrho]
  have hQClosureBall : closure Q ⊆ Metric.closedBall x rho := by
    apply closure_minimal
    · exact fun p hp => Metric.ball_subset_closedBall (hQBall hp)
    · exact Metric.isClosed_closedBall
  have hQOld : Q ∩ Old = ({y} : Set _) := by
    ext p
    constructor
    · rintro ⟨hpQ, hpOld⟩
      have hpClosed : p ∈ Metric.closedBall x rho :=
        hQClosureBall (subset_closure hpQ)
      rcases hOldLocal ⟨hpClosed, hpOld⟩ with hpLine | hpLine
      · rcases hpLine with ⟨c, rfl⟩
        have hlineScaled : x + c • d ∈
            {z | ∃ a : ℝ, z = x + a • dA} := by
          refine ⟨c / lambda, ?_⟩
          dsimp [dA]
          rw [smul_smul]
          congr 2
          field_simp
        have hmem : x + c • d ∈ Q ∩
            ({z | ∃ a : ℝ, z = x + a • dA} ∪
              {z | ∃ b : ℝ, z = x + b • dB}) :=
          ⟨hpQ, Or.inl hlineScaled⟩
        rw [hQlines] at hmem
        simpa [dB] using hmem
      · have hmem : p ∈ Q ∩
            ({z | ∃ a : ℝ, z = x + a • dA} ∪
              {z | ∃ b : ℝ, z = x + b • dB}) :=
          ⟨hpQ, Or.inr hpLine⟩
        rw [hQlines] at hmem
        simpa [dB] using hmem
    · intro hp
      have hpy : p = y := by simpa using hp
      subst p
      exact ⟨by simpa [dB] using hyQ, hyOld⟩
  have hQBad : (Q \ ({y} : Set _)) ∩ (Bad : Set _) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    rcases hp with ⟨⟨hpQ, hpneY⟩, hpBad⟩
    have hpClosed := hQClosureBall (subset_closure hpQ)
    have hpEnds := hBadLocal ⟨hpClosed, hpBad⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpEnds
    rcases hpEnds with rfl | rfl
    · exact hxnotQ hpQ
    · exact hpneY (by simp)
  have hdAnorm : ‖dA‖ = lambda * ‖d‖ := by
    simp [dA, norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
  have hSideBall : closure Side ⊆ Metric.ball x rho := by
    intro p hp
    rcases hSideBox p hp with
      ⟨a, b, ha, hb, hab, hbk, haLo, haHi, hbLo, hbHi, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : (x + a • dA + b • dB) - x = a • dA + b • dB := by
      abel
    rw [hdiff]
    have ha1 : a < 1 := by linarith only [hab, hb]
    have hblambda : b < lambda := by
      have hbr : b < r := by
        nlinarith only [hbHi, hr]
      linarith only [hbr, hr_lt_k, hk_lt_lambda]
    have hnorma : ‖a • dA‖ = a * ‖dA‖ := norm_smul_of_nonneg ha.le dA
    have hnormb : ‖b • dB‖ = b * ‖dB‖ := norm_smul_of_nonneg hb.le dB
    calc
      ‖a • dA + b • dB‖ ≤ ‖a • dA‖ + ‖b • dB‖ := norm_add_le _ _
      _ = a * ‖dA‖ + b * ‖dB‖ := by rw [hnorma, hnormb]
      _ = a * (lambda * ‖d‖) + b * ‖y - x‖ := by rw [hdAnorm]
      _ < lambda * ‖d‖ + lambda * ‖y - x‖ := by
        exact add_lt_add
          (by simpa using (mul_lt_mul_of_pos_right ha1 (mul_pos hlambda hnormd_pos)))
          (by simpa [dB] using (mul_lt_mul_of_pos_right hblambda
            (norm_pos_iff.mpr hdB_ne)))
      _ < rho := by simpa [mul_add] using hsmallRho
  have hBridgeBall : closure Bridge ⊆ Metric.ball x rho := by
    intro p hp
    rcases hBridgeBox p hp with
      ⟨a, b, ha, hb, hab, hbk, haLo, haHi, hbLo, hbHi, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : (x + a • dA + b • dB) - x = a • dA + b • dB := by
      abel
    rw [hdiff]
    have ha1 : a < 1 := by linarith only [hab, hb]
    have hblambda : b < lambda := by
      have hbr : b ≤ r := hbHi
      linarith only [hbr, hr_lt_k, hk_lt_lambda]
    have hnorma : ‖a • dA‖ = a * ‖dA‖ := norm_smul_of_nonneg ha.le dA
    have hnormb : ‖b • dB‖ = b * ‖dB‖ := norm_smul_of_nonneg hb.le dB
    calc
      ‖a • dA + b • dB‖ ≤ ‖a • dA‖ + ‖b • dB‖ := norm_add_le _ _
      _ = a * ‖dA‖ + b * ‖dB‖ := by rw [hnorma, hnormb]
      _ = a * (lambda * ‖d‖) + b * ‖y - x‖ := by rw [hdAnorm]
      _ < lambda * ‖d‖ + lambda * ‖y - x‖ := by
        exact add_lt_add
          (by simpa using (mul_lt_mul_of_pos_right ha1 (mul_pos hlambda hnormd_pos)))
          (by simpa [dB] using (mul_lt_mul_of_pos_right hblambda
            (norm_pos_iff.mpr hdB_ne)))
      _ < rho := by simpa [mul_add] using hsmallRho
  have hCellAvoid (p : EuclideanSpace ℝ (Fin 2)) (a b : ℝ)
      (ha : 0 < a) (hb : 0 < b)
      (hpform : p = x + a • dA + b • dB)
      (hpball : p ∈ Metric.ball x rho) : p ∉ Old ∪ (Bad : Set _) := by
    intro hp
    rcases hp with hpOld | hpBad
    · have hpClosed : p ∈ Metric.closedBall x rho :=
        Metric.ball_subset_closedBall hpball
      rcases hOldLocal ⟨hpClosed, hpOld⟩ with hpLine | hpLine
      · rcases hpLine with ⟨c, hpLine⟩
        have hscaled : (c / lambda) • dA = c • d := by
          dsimp [dA]
          rw [smul_smul, div_mul_cancel₀ c hlambda.ne']
        have hcompare :
            x + a • dA + b • dB =
              x + (c / lambda) • dA + (0 : ℝ) • dB := by
          rw [← hpform, hpLine]
          simp [hscaled]
        exact hb.ne' (hcoeff_unique hcompare).2
      · rcases hpLine with ⟨c, hpLine⟩
        have hcompare :
            x + a • dA + b • dB = x + (0 : ℝ) • dA + c • dB := by
          rw [← hpform, hpLine]
          simp [dB]
        exact ha.ne' (hcoeff_unique hcompare).1
    · have hpClosed : p ∈ Metric.closedBall x rho :=
        Metric.ball_subset_closedBall hpball
      have hpEnds := hBadLocal ⟨hpClosed, hpBad⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpEnds
      rcases hpEnds with hpx | hpy
      · have hcompare :
            x + a • dA + b • dB = x + (0 : ℝ) • dA + (0 : ℝ) • dB := by
          simpa [hpform] using hpx
        exact ha.ne' (hcoeff_unique hcompare).1
      · have hcompare :
            x + a • dA + b • dB = x + (0 : ℝ) • dA + (1 : ℝ) • dB := by
          have hyform : y = x + (0 : ℝ) • dA + (1 : ℝ) • dB := by simp [dB]
          rw [← hpform, hpy, hyform]
        exact ha.ne' (hcoeff_unique hcompare).1
  have hCellsAvoid :
      (closure Side ∪ closure Bridge) ∩ (Old ∪ (Bad : Set _)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    rcases hp with ⟨hpCell, hpForbidden⟩
    rcases hpCell with hpSide | hpBridge
    · rcases hSideBox p hpSide with
        ⟨a, b, ha, hb, _hab, _hbk, _haLo, _haHi, _hbLo, _hbHi, hpform⟩
      exact hCellAvoid p a b ha hb hpform (hSideBall hpSide) hpForbidden
    · rcases hBridgeBox p hpBridge with
        ⟨a, b, ha, hb, _hab, _hbk, _haLo, _haHi, _hbLo, _hbHi, hpform⟩
      exact hCellAvoid p a b ha hb hpform (hBridgeBall hpBridge) hpForbidden
  have hphiTerminal : phi terminalGate = 0 := by
    rw [hterminalActual, hphi_cell]
    rw [← hgateAlign]
    ring
  have hterminalNotVin : terminalGate ∉ Vin := by
    intro hmem
    have := hVinPhi terminalGate hmem
    linarith only [this, hphiTerminal]
  let z0 : ℝ := gateA0 * lambda + gateB0 * mu
  let z1 : ℝ := gateB0 * nu
  let gateC : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![z0, z1]
  have hgateC0 : gateC 0 = z0 := by simp [gateC]
  have hgateC1 : gateC 1 = z1 := by simp [gateC]
  have hgateCBall : gateC ∈ Metric.ball 0 cap := by
    rw [Metric.mem_ball, dist_zero_right]
    apply (sq_lt_sq₀ (norm_nonneg gateC) hcap.le).1
    simpa [gateC, z0, z1, hnormCoord] using hgateRadial
  obtain ⟨epsGate, hepsGate, hgateBallSubset⟩ :=
    (Metric.isOpen_iff.mp Metric.isOpen_ball) gateC hgateCBall
  let q : ℝ := epsGate / (2 * (lambda + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hqlambda_eps : q * lambda < epsGate := by
    dsimp [q]
    rw [div_mul_eq_mul_div]
    have hden : 0 < 2 * (lambda + 1) := by positivity
    apply (div_lt_iff₀ hden).2
    have hscalar : lambda < 2 * (lambda + 1) := by linarith only [hlambda]
    exact mul_lt_mul_of_pos_left hscalar hepsGate
  let hC : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 ![z0 + q * lambda, z1]
  have hhC0 : hC 0 = z0 + q * lambda := by simp [hC]
  have hhC1 : hC 1 = z1 := by simp [hC]
  have hhCdist : dist hC gateC = q * lambda := by
    rw [dist_eq_norm]
    have hcoord0 : (hC - gateC) 0 = q * lambda := by
      rw [PiLp.sub_apply, hhC0, hgateC0]
      ring
    have hcoord1 : (hC - gateC) 1 = 0 := by
      rw [PiLp.sub_apply, hhC1, hgateC1]
      ring
    have hsquare : ‖hC - gateC‖ ^ 2 = (q * lambda) ^ 2 := by
      rw [hnormCoord, hcoord0, hcoord1]
      ring
    nlinarith only [hsquare, norm_nonneg (hC - gateC), mul_pos hq hlambda]
  have hhCBall : hC ∈ Metric.ball 0 cap := by
    apply hgateBallSubset
    simpa [Metric.mem_ball, hhCdist] using hqlambda_eps
  let h : EuclideanSpace ℝ (Fin 2) := x + hC 0 • d + hC 1 • n
  have hz0pos : 0 < z0 := by simpa [z0] using hgateCoordPos
  have hz1pos : 0 < z1 := by dsimp [z1]; positivity
  have hz1boundary : z1 = kappa * z0 := by
    simpa [z0, z1] using hterminalBoundary
  have hhCmem : hC ∈ C := by
    refine ⟨by rw [hhC0]; positivity, ?_, ?_, ?_⟩
    · have hnormlt : ‖hC‖ < cap := by
        simpa [Metric.mem_ball, dist_zero_right] using hhCBall
      have hsquared := (sq_lt_sq₀ (norm_nonneg hC) hcap.le).2 hnormlt
      simpa [hnormCoord] using hsquared
    · simpa [hhC1] using hz1pos
    · rw [hhC0, hhC1, hz1boundary]
      nlinarith only [mul_pos hkappa (mul_pos hq hlambda)]
  have hhVin : h ∈ Vin := by
    rw [hVinEq]
    exact ⟨hC, by simpa [C] using hhCmem, rfl⟩
  have hhFormula : h = terminalGate + q • dA := by
    rw [hterminalChart]
    dsimp [h, hC, z0, z1, dA]
    module
  have hhNeGate : h ≠ terminalGate := by
    intro heq
    have hzero : q • dA = 0 := by
      have heq' : terminalGate + q • dA = terminalGate + 0 := by
        simpa [hhFormula] using heq
      exact add_left_cancel heq'
    exact (smul_ne_zero hq.ne' hdA_ne) hzero
  have hsegmentTerminal :
      segment ℝ h terminalGate ⊆ Vin ∪ ({terminalGate} : Set _) := by
    intro p hp
    rw [segment_eq_image_lineMap] at hp
    rcases hp with ⟨t, ht, rfl⟩
    by_cases ht1 : t = 1
    · right
      simpa [ht1]
    · left
      have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
      let wC : EuclideanSpace ℝ (Fin 2) :=
        AffineMap.lineMap hC gateC t
      have hwCBall : wC ∈ Metric.ball 0 cap :=
        (convex_ball (0 : EuclideanSpace ℝ (Fin 2)) cap).lineMap_mem
          hhCBall hgateCBall ht
      have hwC0 : wC 0 = z0 + (1 - t) * q * lambda := by
        change t * (gateC 0 - hC 0) + hC 0 = z0 + (1 - t) * q * lambda
        rw [hgateC0, hhC0]
        ring
      have hwC1 : wC 1 = z1 := by
        change t * (gateC 1 - hC 1) + hC 1 = z1
        rw [hgateC1, hhC1]
        ring
      have hwCmem : wC ∈ C := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hwC0]
          exact add_pos hz0pos
            (mul_pos (mul_pos (sub_pos.mpr htlt) hq) hlambda)
        · have hnormlt : ‖wC‖ < cap := by
            simpa [Metric.mem_ball, dist_zero_right] using hwCBall
          have hsquared := (sq_lt_sq₀ (norm_nonneg wC) hcap.le).2 hnormlt
          simpa [hnormCoord] using hsquared
        · simpa [hwC1] using hz1pos
        · rw [hwC0, hwC1, hz1boundary]
          apply mul_lt_mul_of_pos_left _ hkappa
          exact lt_add_of_pos_right z0
            (mul_pos (mul_pos (sub_pos.mpr htlt) hq) hlambda)
      rw [hVinEq]
      refine ⟨wC, by simpa [C] using hwCmem, ?_⟩
      change x + wC 0 • d + wC 1 • n = AffineMap.lineMap h terminalGate t
      rw [hwC0, hwC1]
      dsimp [h]
      rw [hhC0, hhC1, hterminalChart]
      simp only [AffineMap.lineMap_apply]
      simp [gateC, z0, z1]
      module
  have hopenTerminal : openSegment ℝ h terminalGate ⊆ Vin := by
    intro p hp
    have hpseg := openSegment_subset_segment ℝ h terminalGate hp
    rcases hsegmentTerminal hpseg with hpVin | hpGate
    · exact hpVin
    · have hpEq : p = terminalGate := by simpa using hpGate
      subst p
      exact False.elim (hhNeGate ((right_mem_openSegment_iff (𝕜 := ℝ)).1 hp))
  have hterminalVinClosure : terminalGate ∈ closure Vin := by
    exact closure_mono hopenTerminal
      (segment_subset_closure_openSegment (right_mem_segment ℝ h terminalGate))
  have hopenXh : openSegment ℝ x h ⊆ Vin := by
    intro p hp
    rw [openSegment_eq_image_lineMap] at hp
    rcases hp with ⟨t, ht, rfl⟩
    let wC : EuclideanSpace ℝ (Fin 2) := t • hC
    have hwCmem : wC ∈ C := by
      rcases hhCmem with ⟨hh0, hhrad, hh1, hhK⟩
      have hnormlt : ‖hC‖ < cap := by
        apply (sq_lt_sq₀ (norm_nonneg hC) hcap.le).1
        simpa [hnormCoord] using hhrad
      have htnorm : ‖wC‖ < cap := by
        dsimp [wC]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
        have hCne : hC ≠ 0 := by
          intro hzero
          rw [hzero] at hh0
          simpa using hh0.ne'
        have hnormpos : 0 < ‖hC‖ := norm_pos_iff.mpr hCne
        have hmul : t * ‖hC‖ < ‖hC‖ := by
          simpa using (mul_lt_mul_of_pos_right ht.2 hnormpos)
        exact hmul.trans hnormlt
      refine ⟨?_, ?_, ?_, ?_⟩
      · change 0 < t * hC 0
        exact mul_pos ht.1 hh0
      · have hsquared := (sq_lt_sq₀ (norm_nonneg wC) hcap.le).2 htnorm
        simpa [hnormCoord] using hsquared
      · change 0 < t * hC 1
        exact mul_pos ht.1 hh1
      · change t * hC 1 < kappa * (t * hC 0)
        calc
          t * hC 1 < t * (kappa * hC 0) := mul_lt_mul_of_pos_left hhK ht.1
          _ = kappa * (t * hC 0) := by ring
    rw [hVinEq]
    refine ⟨wC, by simpa [C] using hwCmem, ?_⟩
    change x + wC 0 • d + wC 1 • n = AffineMap.lineMap x h t
    have hwC0 : wC 0 = t * hC 0 := by simp [wC]
    have hwC1 : wC 1 = t * hC 1 := by simp [wC]
    rw [hwC0, hwC1]
    dsimp [h]
    simp only [AffineMap.lineMap_apply]
    change x + (t * hC 0) • d + (t * hC 1) • n =
      t • ((x + hC 0 • d + hC 1 • n) - x) + x
    module
  have hxVinClosure : x ∈ closure Vin := by
    exact closure_mono hopenXh
      (segment_subset_closure_openSegment (left_mem_segment ℝ x h))
  have hClosureVinSide :
      closure Vin ∩ closure Side = ({terminalGate} : Set _) := by
    ext p
    constructor
    · rintro ⟨hpVin, hpSide⟩
      have hphiNonneg := hclosureVinPhi p hpVin
      have hphiNonpos := hSidePhi p hpSide
      have hphiZero : phi p = 0 := le_antisymm hphiNonpos hphiNonneg
      rcases hSideBox p hpSide with
        ⟨a, b, ha, hb, hab, hbk, haLo, haHi, hbLo, hbHi, hpform⟩
      have hcellZero : kappa * (a * lambda + b * mu) - b * nu = 0 := by
        rw [hpform, hphi_cell] at hphiZero
        exact (mul_eq_zero.mp hphiZero).resolve_left hnormsq_pos.ne'
      have hid := hsupport_identity a b
      have hsupportZero : gateB0 * a - gateA0 * b = 0 := by
        rw [hcellZero, mul_zero] at hid
        exact (mul_eq_zero.mp hid.symm).resolve_left hnuDiff.ne'
      have haeq : a = gateA0 := by
        apply le_antisymm haHi
        by_contra hnot
        have halt : a < gateA0 := lt_of_not_ge hnot
        have hlt : gateB0 * a < gateB0 * gateA0 :=
          mul_lt_mul_of_pos_left halt hgateBpos
        have heq : gateB0 * a = gateA0 * b := sub_eq_zero.mp hsupportZero
        have hbad : gateA0 * b < gateA0 * gateB0 := by
          rw [← heq, mul_comm gateA0 gateB0]
          exact hlt
        exact (not_lt_of_ge (mul_le_mul_of_nonneg_left hbLo hgateApos.le)) hbad
      have hbeq : b = gateB0 := by
        have hfac : gateA0 * (gateB0 - b) = 0 := by
          rw [← hsupportZero]
          rw [haeq]
          ring
        exact (sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left hgateApos.ne')).symm
      have hpEq : p = terminalGate := by
        rw [hpform, hterminalActual, haeq, hbeq]
      simpa [hpEq]
    · intro hp
      have hpEq : p = terminalGate := by simpa using hp
      subst p
      exact ⟨hterminalVinClosure, hterminalSideClosure⟩
  have hClosureVinBridge : closure Vin ∩ closure Bridge = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hnonneg := hclosureVinPhi p hp.1
    have hneg := hBridgePhi p hp.2
    exact (not_lt_of_ge hnonneg) hneg
  have hVinSide : Vin ∩ Side = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hpos := hVinPhi p hp.1
    have hnonpos := hSidePhi p (subset_closure hp.2)
    exact (not_lt_of_ge hnonpos) hpos
  have hkSlope : kappa * lambda < k * (nu - kappa * mu) := by
    have hrel :
        24 * k * (nu - kappa * mu) = kappa * lambda * (k + 25) := by
      dsimp [denom] at hkdenom
      calc
        24 * k * (nu - kappa * mu) =
            k * (24 * (nu - kappa * mu) - kappa * lambda) +
              k * (kappa * lambda) := by ring
        _ = 25 * kappa * lambda + k * (kappa * lambda) := by rw [hkdenom]
        _ = kappa * lambda * (k + 25) := by ring
    have hkl : 24 < k + 25 := by linarith only [hkpos]
    have hmul := mul_lt_mul_of_pos_left hkl (mul_pos hkappa hlambda)
    apply lt_of_mul_lt_mul_left (a := (24 : ℝ)) ?_ (by norm_num)
    calc
      24 * (kappa * lambda) = kappa * lambda * 24 := by ring
      _ < kappa * lambda * (k + 25) := hmul
      _ = 24 * (k * (nu - kappa * mu)) := by rw [← hrel]; ring
  have hQPhi : ∀ p ∈ Q, phi p < 0 := by
    intro p hp
    by_cases hpy : p = y
    · simpa [hpy] using hphi_y
    · have hpsector : p ∈ Q \ ({x + (1 : ℝ) • dB} : Set _) := by
        refine ⟨hp, ?_⟩
        simpa [dB] using hpy
      rcases hQsector hpsector with ⟨a, b, ha, hb, hkab, hab, rfl⟩
      rw [hphi_cell]
      have hmain : kappa * lambda * a < (nu - kappa * mu) * b := by
        have hscaled := mul_lt_mul_of_pos_right hkSlope ha
        have hkb := mul_le_mul_of_nonneg_left hkab hnuDiff.le
        calc
          kappa * lambda * a < k * (nu - kappa * mu) * a := hscaled
          _ = (nu - kappa * mu) * (k * a) := by ring
          _ ≤ (nu - kappa * mu) * b := hkb
      have hexpr : kappa * (a * lambda + b * mu) - b * nu < 0 := by
        rw [show kappa * (a * lambda + b * mu) - b * nu =
          kappa * lambda * a - (nu - kappa * mu) * b by ring]
        exact sub_neg.mpr hmain
      exact mul_neg_of_pos_of_neg hnormsq_pos hexpr
  have hQClosurePhi : ∀ p ∈ closure Q, phi p ≤ 0 := by
    have hsub : Q ⊆ {p | phi p ≤ 0} := fun p hp => (hQPhi p hp).le
    have hclosed : IsClosed {p | phi p ≤ 0} :=
      isClosed_le hphi_cont continuous_const
    exact closure_minimal hsub hclosed
  have hTerminalClosuresPhi :
      ∀ p ∈ closure Side ∪ closure Bridge ∪ closure Q,
        kappa * inner ℝ (p - x) d - inner ℝ (p - x) n ≤ 0 := by
    intro p hp
    change phi p ≤ 0
    rcases hp with (hpSide | hpBridge) | hpQ
    · exact hSidePhi p hpSide
    · exact (hBridgePhi p hpBridge).le
    · exact hQClosurePhi p hpQ
  have hVinQ : Vin ∩ Q = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hpos := hVinPhi p hp.1
    have hneg := hQPhi p hp.2
    exact (not_lt_of_ge hpos.le) hneg
  have hVinOldBad : Vin ∩ (Old ∪ (Bad : Set _)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    rcases hp with ⟨hpVin, hpOld | hpBad⟩
    · have hpClosed : p ∈ Metric.closedBall x rho :=
        Metric.ball_subset_closedBall (hVinBall hpVin)
      rcases hOldLocal ⟨hpClosed, hpOld⟩ with hpLine | hpLine
      · rcases hpLine with ⟨c, hpEq⟩
        rw [hVinEq] at hpVin
        rcases hpVin with ⟨z, ⟨hz0, hzrad, hz1, hzK⟩, hzp⟩
        have hcompare :
            x + z 0 • d + z 1 • n = x + c • d + (0 : ℝ) • n := by
          calc
            x + z 0 • d + z 1 • n = p := hzp
            _ = x + c • d := hpEq
            _ = x + c • d + (0 : ℝ) • n := by simp
        exact hz1.ne' (hDN_unique hcompare).2
      · rcases hpLine with ⟨c, hpEq⟩
        rw [hVinEq] at hpVin
        rcases hpVin with ⟨z, ⟨hz0, hzrad, hz1, hzK⟩, hzp⟩
        have hcompare :
            x + z 0 • d + z 1 • n = x + (c * mu) • d + (c * nu) • n := by
          calc
            x + z 0 • d + z 1 • n = p := hzp
            _ = x + c • (y - x) := hpEq
            _ = x + (c * mu) • d + (c * nu) • n := by rw [hy]; module
        have hcoords := hDN_unique hcompare
        have hcpos : 0 < c := by
          rw [hcoords.2] at hz1
          exact pos_of_mul_pos_left hz1 hnu.le
        have hpPhi : phi p = c * phi y := by
          rw [hpEq]
          dsimp [phi]
          have : x + c • (y - x) - x = c • (y - x) := by module
          rw [this, inner_smul_left, inner_smul_left]
          simp only [starRingEnd_apply, star_trivial]
          ring
        have hpos := hVinPhi p (by
          rw [hVinEq]
          exact ⟨z, ⟨hz0, hzrad, hz1, hzK⟩, hzp⟩)
        rw [hpPhi] at hpos
        exact (not_lt_of_ge hpos.le) (mul_neg_of_pos_of_neg hcpos hphi_y)
    · have hpClosed : p ∈ Metric.closedBall x rho :=
        Metric.ball_subset_closedBall (hVinBall hpVin)
      have hpEnds := hBadLocal ⟨hpClosed, hpBad⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpEnds
      rcases hpEnds with hpx | hpy
      · have hpos := hVinPhi p hpVin
        rw [hpx, hphi_x] at hpos
        exact (lt_irrefl 0) hpos
      · have hpos := hVinPhi p hpVin
        rw [hpy] at hpos
        exact (not_lt_of_ge hpos.le) hphi_y
  obtain ⟨predecessor, approach, lastGate, hpredSubset, happSubset,
      hpredTarget, happSource, hPredApproach, happTarget,
      hApproachTerminal, hPredTerminalDisjoint⟩ :=
    ordinaryAdjacentEdgesTerminalArcPackage SelectedSide Vin h terminalGate dA dB q
      hVinOpen hVinConvex hVinSelected hhVin hdB_ne hq hhFormula hliScaled
  refine ⟨k, hkpos, Q, Side, Bridge, terminalGate, sideSource,
    quadrantGate, h, predecessor, approach, lastGate,
    hQconvex, hQcompact, hxQ, ?_, hxnotQ,
    hSideOpen, hSideConvex, hSideCompact,
    hBridgeOpen, hBridgeConvex, hBridgeCompact,
    hterminalSideClosure, hterminalNotSide,
    hsourceSideClosure, hsourceNotSide,
    hsourceBridgeClosure, hsourceNotBridge,
    hquadrantBridgeClosure, hquadrantNotBridge,
    hterminalNeSource, hsourceNeQuadrant,
    hterminalSourceSegment, hterminalSourceOpen,
    hsourceQuadrantSegment, hsourceQuadrantOpen,
    hquadrantQ, ?_, hsourceQuadrantQ,
    hSideBridgeClosure, hSideQClosure, hBridgeQClosure,
    ?_, hQClosureBall, hQOld, hQBad, hSideBall, hBridgeBall,
    hCellsAvoid, hVinOpen, hVinConvex, hhVin, hhNeGate,
    hVinSelected, hxVinClosure, hNear, hVinBall, hVinQ, hVinOldBad,
    hterminalVinClosure, hterminalNotVin, hsegmentTerminal,
    hopenTerminal, hClosureVinSide, hClosureVinBridge, hVinSide,
    hpredSubset, happSubset, hpredTarget, happSource,
    hPredApproach, happTarget, hApproachTerminal,
    hPredTerminalDisjoint, hTerminalClosuresPhi, z0, z1, hz0pos, hz1pos,
    hz1boundary, ?_⟩
  · simpa [dB] using hyQ
  · simpa [dB] using hquadrantNe
  · simpa [dB] using hquadrantYSegment
  · simpa [z0, z1] using hterminalChart
