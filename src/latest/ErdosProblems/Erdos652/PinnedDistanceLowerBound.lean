import ErdosProblems.Erdos652.RetainedCircleArcFamily
import ErdosProblems.Erdos652.BadArcBound
import ErdosProblems.Erdos652.TwoRichLineIncidences
import ErdosProblems.Erdos652.EndpointPairMultiplicitySimpleGraph
import Util.IncidenceGeometry.CrossingLemma
import Util.IncidenceGeometry.PolygonalReplacementForGeometricArcs

open Classical
open scoped BigOperators Real
noncomputable section

namespace Erdos652

private lemma crossing_numeric_contradiction
    {m n τ e ε : ℝ}
    (hm : 0 < m) (hn : 0 < n)
    (hτ0 : 0 ≤ τ)
    (hε40 : ε ≤ (1 : ℝ) / 40)
    (hsqrt_sq : (Real.sqrt (m * n)) ^ 2 = m * n)
    (hτ : τ < ε * Real.sqrt (m * n))
    (he : m * n / 2 ≤ e)
    (hcube : e ^ 3 ≤ 200 * n ^ 2 * m ^ 2 * τ ^ 2) : False := by
  have ht40 : τ < Real.sqrt (m * n) / 40 := by
    calc
      τ < ε * Real.sqrt (m * n) := hτ
      _ ≤ ((1 : ℝ) / 40) * Real.sqrt (m * n) :=
        mul_le_mul_of_nonneg_right hε40 (Real.sqrt_nonneg _)
      _ = Real.sqrt (m * n) / 40 := by ring
  have htSq : τ ^ 2 < (m * n) / 1600 := by
    have htNonneg : 0 ≤ τ := hτ0
    have hsNonneg : 0 ≤ Real.sqrt (m * n) / 40 := by positivity
    have hsquare := (sq_lt_sq₀ htNonneg hsNonneg).mpr ht40
    rw [div_pow, hsqrt_sq] at hsquare
    norm_num at hsquare ⊢
    exact hsquare
  have hecubeLower : (m * n / 2) ^ 3 ≤ e ^ 3 :=
    pow_le_pow_left₀ (by positivity) he 3
  have hstrict : 200 * n ^ 2 * m ^ 2 * τ ^ 2 < (m * n / 2) ^ 3 := by
    have hposfac : 0 < 200 * n ^ 2 * m ^ 2 := by positivity
    calc
      200 * n ^ 2 * m ^ 2 * τ ^ 2 <
          200 * n ^ 2 * m ^ 2 * ((m * n) / 1600) :=
        mul_lt_mul_of_pos_left htSq hposfac
      _ = (m * n / 2) ^ 3 := by ring
  exact (not_lt_of_ge (hecubeLower.trans hcube)) hstrict

/-- Mathialagan's pinned-distance estimate, in the uniform form used for
Erdős Problem 652.  The numerical constant is deliberately non-optimized. -/
theorem pinnedDistanceLowerBound :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (P Q : Finset Point) (t : ℕ), Disjoint P Q →
        8 ≤ P.card → P.card ^ 3 ≤ Q.card →
          (∀ p ∈ P, (distanceRadii p Q).card ≤ t) →
            ε * Real.sqrt ((P.card : ℝ) * (Q.card : ℝ)) ≤ t := by
  obtain ⟨C, hC, hlines⟩ := twoRichLineIncidences
  let ε : ℝ := 1 / (160 * (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hden : 0 < 160 * (C + 1) := mul_pos (by norm_num) hC1
  have hε : 0 < ε := by
    change 0 < 1 / (160 * (C + 1))
    exact one_div_pos.mpr hden
  have hε40 : ε ≤ (1 : ℝ) / 40 := by
    change 1 / (160 * (C + 1)) ≤ (1 : ℝ) / 40
    rw [div_le_iff₀ hden]
    nlinarith [hC]
  have hdeleteCoeff : (4 * C + 2) * ε ≤ (1 : ℝ) / 2 := by
    change (4 * C + 2) * (1 / (160 * (C + 1))) ≤ (1 : ℝ) / 2
    rw [show (4 * C + 2) * (1 / (160 * (C + 1))) =
      (4 * C + 2) / (160 * (C + 1)) by ring]
    rw [div_le_iff₀ hden]
    nlinarith [hC]
  refine ⟨ε, hε, ?_⟩
  intro P Q t hPQ hm8 hmq ht
  let m : ℝ := P.card
  let n : ℝ := Q.card
  have hmpos : 0 < m := by
    dsimp [m]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 8) hm8)
  have hmnonneg : 0 ≤ m := hmpos.le
  have hnpos_nat : 0 < Q.card := by
    have : 0 < P.card ^ 3 := pow_pos (lt_of_lt_of_le (by omega : 0 < 8) hm8) _
    omega
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast hnpos_nat
  have hnnonneg : 0 ≤ n := hnpos.le
  have hmqR : m ^ 3 ≤ n := by
    dsimp [m, n]
    exact_mod_cast hmq
  have hsqrt_sq : (Real.sqrt (m * n)) ^ 2 = m * n :=
    Real.sq_sqrt (mul_nonneg hmnonneg hnnonneg)
  have hsqrt_m_le_n : Real.sqrt (m * n) * m ≤ n := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hmnonneg) hnnonneg).mp
    rw [mul_pow, hsqrt_sq]
    have hmul := mul_le_mul_of_nonneg_right hmqR hnnonneg
    nlinarith
  have hsqrt_le_n : Real.sqrt (m * n) ≤ n := by
    have hm8R : (8 : ℝ) ≤ m := by
      dsimp [m]
      exact_mod_cast hm8
    have hm1 : (1 : ℝ) ≤ m := by linarith
    calc
      Real.sqrt (m * n) ≤ Real.sqrt (m * n) * m := by
        nlinarith [Real.sqrt_nonneg (m * n)]
      _ ≤ n := hsqrt_m_le_n
  by_contra hbound
  have htSmall : (t : ℝ) < ε * Real.sqrt (m * n) := lt_of_not_ge hbound
  obtain ⟨L, hLmem, hInc⟩ := hlines P (by omega)
  rcases retainedCircleArcFamily P Q t hPQ ht with
    ⟨ι, instF, instD, A, endpoint, center, arcStart, arcEnd,
      carrier, arcInterior, γ, hcount, h_nondiag, h_endpoint_eq,
      h_endpoints_distinct, h_endpoints_on_circle, h_arc_param,
      h_carrier_circle, h_no_vertex, h_same_disjoint, h_same_unique,
      h_radius⟩
  letI : Fintype ι := instF
  letI : DecidableEq ι := instD
  let B : Finset ι := A.filter (fun i =>
    2 ≤ (A.filter (fun j => endpoint j = endpoint i)).card)
  let Good : Finset ι := A \ B
  have hBsubset : B ⊆ A := Finset.filter_subset _ _
  have hB := repeatedEndpointArcCard_le P Q t A endpoint center arcStart arcEnd
    arcInterior γ ht h_endpoint_eq h_endpoints_distinct h_endpoints_on_circle
    (fun i hi => by
      rcases h_arc_param i hi with ⟨a, b, c, d, e, _, g⟩
      exact ⟨a, b, c, d, e, g⟩)
    h_same_disjoint h_same_unique L hLmem
  have hBreal : (B.card : ℝ) ≤ 2 * (t : ℝ) *
      (C * (m ^ 2 + m)) := by
    calc
      (B.card : ℝ) ≤ (2 * t * LineIncidences P L : ℕ) := by
        exact_mod_cast hB
      _ = 2 * (t : ℝ) * (LineIncidences P L : ℝ) := by norm_num
      _ ≤ 2 * (t : ℝ) * (C * (m ^ 2 + m)) := by
        gcongr
  have hm2m : m ^ 2 + m ≤ 2 * m ^ 2 := by
    have hm8R : (8 : ℝ) ≤ m := by
      dsimp [m]
      exact_mod_cast hm8
    have hm1 : (1 : ℝ) ≤ m := by linarith
    nlinarith [mul_nonneg hmnonneg (sub_nonneg.mpr hm1)]
  have hBhalf : (B.card : ℝ) ≤ 4 * C * ε * (m * n) := by
    calc
      (B.card : ℝ) ≤ 2 * (t : ℝ) * (C * (m ^ 2 + m)) := hBreal
      _ ≤ 2 * (ε * Real.sqrt (m * n)) * (C * (2 * m ^ 2)) := by
        gcongr
      _ = 4 * C * ε * (Real.sqrt (m * n) * m) * m := by ring
      _ ≤ 4 * C * ε * n * m := by
        gcongr
      _ = 4 * C * ε * (m * n) := by ring
  have hsmallFibres : (2 * P.card * t : ℕ) ≤
      (2 * ε * (m * n) : ℝ) := by
    norm_num
    calc
      2 * m * (t : ℝ) ≤ 2 * m * (ε * Real.sqrt (m * n)) := by
        gcongr
      _ ≤ 2 * m * (ε * n) := by
        gcongr
      _ = 2 * ε * (m * n) := by ring
  have hremoved : (B.card : ℝ) + (2 * P.card * t : ℕ) ≤
      (m * n) / 2 := by
    have hcoef : 4 * C * ε + 2 * ε ≤ (1 : ℝ) / 2 := by
      nlinarith [hdeleteCoeff]
    calc
      (B.card : ℝ) + (2 * P.card * t : ℕ) ≤
          4 * C * ε * (m * n) + 2 * ε * (m * n) :=
        add_le_add hBhalf hsmallFibres
      _ = (4 * C * ε + 2 * ε) * (m * n) := by ring
      _ ≤ ((1 : ℝ) / 2) * (m * n) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hmnonneg hnnonneg)
      _ = (m * n) / 2 := by ring
  have hAcard : A.card = Good.card + B.card := by
    have hcard := Finset.card_sdiff_add_card_eq_card hBsubset
    simpa [Good, Nat.add_comm] using hcard.symm
  have hGoodLower : (m * n) / 2 ≤ (Good.card : ℝ) := by
    have hcR : (m * n : ℝ) ≤ (A.card : ℝ) + (2 * P.card * t : ℕ) := by
      dsimp [m, n]
      exact_mod_cast hcount
    rw [hAcard] at hcR
    norm_num at hcR hremoved
    linarith
  have hGoodA : Good ⊆ A := Finset.sdiff_subset
  have hGoodMultiplicity : ∀ e ∈ Good.image endpoint,
      (Good.filter (fun i => endpoint i = e)).card ≤ 1 := by
    intro e he
    by_contra hle
    have htwo : 2 ≤ (Good.filter (fun i => endpoint i = e)).card := by omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 2) htwo)
    have hiGood := (Finset.mem_filter.mp hi).1
    have hiA := hGoodA hiGood
    have hAfiber : 2 ≤ (A.filter (fun j => endpoint j = endpoint i)).card := by
      have hsub : Good.filter (fun j => endpoint j = e) ⊆
          A.filter (fun j => endpoint j = endpoint i) := by
        intro j hj
        have hje := (Finset.mem_filter.mp hj).2
        have hie := (Finset.mem_filter.mp hi).2
        exact Finset.mem_filter.mpr ⟨hGoodA (Finset.mem_filter.mp hj).1,
          hje.trans hie.symm⟩
      exact htwo.trans (Finset.card_le_card hsub)
    have hiB : i ∈ B := Finset.mem_filter.mpr ⟨hiA, hAfiber⟩
    exact (Finset.mem_sdiff.mp hiGood).2 hiB
  have hGoodNondiag : ∀ i ∈ Good, ¬(endpoint i).IsDiag :=
    fun i hi => h_nondiag i (hGoodA hi)
  obtain ⟨G, hGfin, hGedgeLower, hGedge⟩ :=
    endpointPairMultiplicitySimpleGraph Good endpoint 1 (by omega)
      hGoodNondiag hGoodMultiplicity
  letI : Fintype G.edgeSet := hGfin
  have hEdgesGood : (Good.card : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
    simpa using hGedgeLower
  obtain ⟨D, hDlocal⟩ := circleRetainedArcDrawingAssembly Q (circleKeys P Q)
    Good endpoint center arcStart arcEnd carrier arcInterior γ
    (fun i hi => h_endpoint_eq i (hGoodA hi))
    (fun i hi => h_endpoints_distinct i (hGoodA hi))
    (fun i hi => h_endpoints_on_circle i (hGoodA hi))
    (fun i hi => h_arc_param i (hGoodA hi))
    (fun i hi => h_carrier_circle i (hGoodA hi))
    (fun i hi => h_radius i (hGoodA hi))
    (fun i hi => h_no_vertex i (hGoodA hi))
    (fun i hi j hj => h_same_disjoint i (hGoodA hi) j (hGoodA hj))
    G hGedge
  obtain ⟨_Dpoly, _hpoly, hcrossNat⟩ := PolygonalReplacementForGeometricArcs G D
  have hCircleCard := circleKeys_card_le P Q t ht
  have hcrossUpper : (CrossingNumber G : ℝ) ≤ 2 * (m * (t : ℝ)) ^ 2 := by
    calc
      (CrossingNumber G : ℝ) ≤ (D.localPairCount : ℝ) := by exact_mod_cast hcrossNat
      _ ≤ 2 * ((circleKeys P Q).card : ℝ) ^ 2 := hDlocal
      _ ≤ 2 * (m * (t : ℝ)) ^ 2 := by
        gcongr
        dsimp [m]
        exact_mod_cast hCircleCard
  have hedgeLarge : 4 * Q.card ≤ G.edgeFinset.card := by
    have hreal : (4 * Q.card : ℕ) ≤ (G.edgeFinset.card : ℝ) := by
      calc
        (4 * Q.card : ℕ) = 4 * n := by norm_num [n]
        _ ≤ (m * n) / 2 := by
          have : (8 : ℝ) ≤ m := by
            dsimp [m]
            exact_mod_cast hm8
          nlinarith
        _ ≤ (Good.card : ℝ) := hGoodLower
        _ ≤ (G.edgeFinset.card : ℝ) := hEdgesGood
    exact_mod_cast hreal
  have hnQ : 1 ≤ Fintype.card Q := by
    simpa only [Fintype.card_coe] using Nat.succ_le_iff.mpr hnpos_nat
  have heQ : 4 * Fintype.card Q ≤ G.edgeFinset.card := by
    simpa only [Fintype.card_coe] using hedgeLarge
  have hcrossLower0 := CrossingLemma G hnQ heQ
  have hcrossLower :
      (G.edgeFinset.card : ℝ) ^ 3 /
          (100 * (Q.card : ℝ) ^ 2) ≤ (CrossingNumber G : ℝ) := by
    simpa only [Fintype.card_coe] using hcrossLower0
  let e : ℝ := G.edgeFinset.card
  have heLower : (m * n) / 2 ≤ e := hGoodLower.trans hEdgesGood
  have hcube : e ^ 3 ≤ 200 * n ^ 2 * m ^ 2 * (t : ℝ) ^ 2 := by
    have hdenCross : 0 < 100 * n ^ 2 := by positivity
    have hcl : e ^ 3 / (100 * n ^ 2) ≤ (CrossingNumber G : ℝ) := by
      change (G.edgeFinset.card : ℝ) ^ 3 /
        (100 * (Q.card : ℝ) ^ 2) ≤ (CrossingNumber G : ℝ)
      exact hcrossLower
    have hboth : e ^ 3 / (100 * n ^ 2) ≤ 2 * (m * (t : ℝ)) ^ 2 :=
      hcl.trans hcrossUpper
    have hmul : e ^ 3 ≤ 2 * (m * (t : ℝ)) ^ 2 * (100 * n ^ 2) :=
      (div_le_iff₀ hdenCross).mp hboth
    calc
      e ^ 3 ≤ 2 * (m * (t : ℝ)) ^ 2 * (100 * n ^ 2) := hmul
      _ = 200 * n ^ 2 * m ^ 2 * (t : ℝ) ^ 2 := by ring
  exact crossing_numeric_contradiction hmpos hnpos (by positivity) hε40 hsqrt_sq
    htSmall heLower hcube

end Erdos652
