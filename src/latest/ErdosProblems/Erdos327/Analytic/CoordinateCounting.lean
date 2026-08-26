import ErdosProblems.Erdos327.Analytic.MixedEdges
import ErdosProblems.Erdos327.Analytic.SourceBadCoordinates

/-!
# Finite coordinate supersets for the analytic counts

This file turns the existential coordinates attached to a deleted source
vertex into an injective map to one explicit finite set of triples.  It is
the finite counting bridge needed before the residual and three-form
estimates can be summed.
-/

namespace Erdos327.Analytic

open Finset

/-- A source coordinate triple is `((u,v),d)`. -/
abbrev SourceTriple := (ℕ × ℕ) × ℕ

def sourceU (q : SourceTriple) : ℕ := q.1.1
def sourceV (q : SourceTriple) : ℕ := q.1.2
def sourceD (q : SourceTriple) : ℕ := q.2

/-- The source vertex reconstructed from `2b = u(u+v)d`. -/
def sourceVertex (q : SourceTriple) : ℕ :=
  sourceU q * (sourceU q + sourceV q) * sourceD q / 2

/-- Every divisor of twice a rough number is free of odd primes below the
roughness cutoff. -/
theorem oddRough_of_dvd_two_mul_rough
    {L b r : ℕ} (hr : r ∣ 2 * b) (hb : Rough L b) :
    OddRough L r := by
  intro p hpPrime hp2 hpL hpr
  have hpTwoB : p ∣ 2 * b := hpr.trans hr
  rcases hpPrime.dvd_mul.mp hpTwoB with hpTwo | hpB
  · have hpEq : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hpPrime Nat.prime_two).mp hpTwo
    omega
  · exact hb p hpPrime hpL hpB

/-- A nontrivial coordinate sum occurring in an exact representation of a
rough odd source vertex cannot lie below the roughness cutoff. -/
theorem sourceSum_ge_cutoff
    {L b u v d : ℕ} (hL : 3 ≤ L)
    (hu : 0 < u) (hv : 0 < v) (hpair : (u, v) ≠ (1, 1))
    (hexact : 2 * b = u * (u + v) * d)
    (hrough : Rough L b) :
    L ≤ u + v := by
  by_contra hnot
  have hsumL : u + v < L := Nat.lt_of_not_ge hnot
  have hsum2 : 2 < u + v := by
    have htwo : 2 ≤ u + v := by omega
    by_contra hnot2
    have hsumEq : u + v = 2 := by omega
    have huEq : u = 1 := by omega
    have hvEq : v = 1 := by omega
    exact hpair (by simp [huEq, hvEq])
  have hoddB : Odd b := odd_of_rough (by omega) hrough
  have hsumDvdProduct : u + v ∣ u * (u + v) * d :=
    ⟨u * d, by ring⟩
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hsum2 with
    hfour | ⟨p, hpPrime, hpSum, hpOdd⟩
  · have hfourProduct : 4 ∣ u * (u + v) * d :=
      hfour.trans hsumDvdProduct
    have hfourTwoB : 4 ∣ 2 * b := by
      rwa [← hexact] at hfourProduct
    rcases hfourTwoB with ⟨k, hk⟩
    rcases hoddB with ⟨r, hr⟩
    omega
  · have hpProduct : p ∣ u * (u + v) * d :=
      hpSum.trans hsumDvdProduct
    have hpTwoB : p ∣ 2 * b := by
      rwa [← hexact] at hpProduct
    rcases hpPrime.dvd_mul.mp hpTwoB with hpTwo | hpB
    · have hpEq : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hpPrime Nat.prime_two).mp hpTwo
      rcases hpOdd with ⟨r, hr⟩
      omega
    · have hpLe : p ≤ u + v :=
        Nat.le_of_dvd (by omega) hpSum
      exact hrough p hpPrime (hpLe.trans_lt hsumL) hpB

/-- The explicit finite superset of all triples selected by a bad source
vertex.  Conditions that can only reduce the later analytic sum are retained
here, including coprimality, score orientation, roughness, and centered
regularity. -/
noncomputable def sourceCoordinateSet
    (L N : ℕ) (A K : ℝ) : Finset SourceTriple :=
  (((Icc 1 N) ×ˢ (Icc 1 (3 * N))) ×ˢ (Icc 1 (2 * N))).filter fun q ↦
    Nat.Coprime (sourceU q) (sourceV q) ∧
      sourceV q ≤ 3 * sourceU q ∧
      ArithmeticFunction.cardFactors (sourceV q) ≤
        ArithmeticFunction.cardFactors (sourceU q) ∧
      (sourceU q, sourceV q) ≠ (1, 1) ∧
      2 * sourceVertex q =
        sourceU q * (sourceU q + sourceV q) * sourceD q ∧
      L ≤ sourceU q + sourceV q ∧
      N / 2 ≤ sourceVertex q ∧ sourceVertex q ≤ N ∧
      OddRough L (sourceU q) ∧
      OddRough L (sourceU q + sourceV q) ∧
      OddRough L (sourceD q) ∧
      Rough L (sourceVertex q) ∧
      CutoffRegular L A K (sourceVertex q)

theorem sourceCoordinate_of_rankBad
    {L N b : ℕ} {A K : ℝ} (hL : 3 ≤ L) (hN : 2 ≤ N)
    (hb : b ∈ Erdos327.rankBad (Erdos327.upto N)
      (regularSource L A K N)
      ArithmeticFunction.cardFactors) :
    ∃ q ∈ sourceCoordinateSet L N A K,
      sourceVertex q = b := by
  rcases Erdos327.sourceBad_coordinates hN hb with
    ⟨g, u, v, d, hg, hu, hv, hd, hcop, hbu, hproduct,
      huN, hv3u, _huv4u, hscore, hpair, hrough, hregular⟩
  have hbSource :=
    (Erdos327.mem_rankBad.mp hb).1
  have hbData := mem_regularSource.mp hbSource
  have hv3N : v ≤ 3 * N := by omega
  have hcoeff : 0 < u * (u + v) :=
    Nat.mul_pos hu (Nat.add_pos_left hu v)
  have hdProduct : d ≤ u * (u + v) * d := by
    exact Nat.le_mul_of_pos_left d hcoeff
  have hproductN : u * (u + v) * d ≤ 2 * N := by
    rw [← hproduct]
    omega
  have hd2N : d ≤ 2 * N := hdProduct.trans hproductN
  let q : SourceTriple := ((u, v), d)
  have hvertex : sourceVertex q = b := by
    dsimp [q, sourceVertex, sourceU, sourceV, sourceD]
    omega
  have hsumL : L ≤ u + v :=
    sourceSum_ge_cutoff hL hu hv hpair hproduct hrough
  have huDvd : u ∣ 2 * b := by
    rw [hproduct]
    exact ⟨(u + v) * d, by ring⟩
  have hsumDvd : u + v ∣ 2 * b := by
    rw [hproduct]
    exact ⟨u * d, by ring⟩
  have hdDvd : d ∣ 2 * b := by
    rw [hproduct]
    exact ⟨u * (u + v), by ring⟩
  have huOddRough := oddRough_of_dvd_two_mul_rough huDvd hrough
  have hsumOddRough := oddRough_of_dvd_two_mul_rough hsumDvd hrough
  have hdOddRough := oddRough_of_dvd_two_mul_rough hdDvd hrough
  refine ⟨q, ?_, hvertex⟩
  rw [sourceCoordinateSet, mem_filter]
  refine ⟨?_, ?_⟩
  · exact mem_product.mpr
      ⟨mem_product.mpr
        ⟨mem_Icc.mpr ⟨hu, huN⟩,
          mem_Icc.mpr ⟨hv, hv3N⟩⟩,
        mem_Icc.mpr ⟨hd, hd2N⟩⟩
  · dsimp [q, sourceU, sourceV]
    rw [hvertex]
    exact ⟨hcop, hv3u, hscore, hpair, hproduct, hsumL,
      hbData.1, hbData.2.1,
      huOddRough, hsumOddRough, hdOddRough, hrough, hregular⟩

/-- Every bad source vertex selects a coordinate triple, and equality of
selected triples forces equality of the reconstructed source vertices. -/
theorem card_rankBad_le_sourceCoordinateSet
    {L N : ℕ} {A K : ℝ} (hL : 3 ≤ L) (hN : 2 ≤ N) :
    (Erdos327.rankBad (Erdos327.upto N)
      (regularSource L A K N)
      ArithmeticFunction.cardFactors).card ≤
        (sourceCoordinateSet L N A K).card := by
  classical
  let bad :=
    Erdos327.rankBad (Erdos327.upto N)
      (regularSource L A K N)
      ArithmeticFunction.cardFactors
  let f : ℕ → SourceTriple := fun b ↦
    if hb : b ∈ bad then
      Classical.choose (sourceCoordinate_of_rankBad hL hN hb)
    else ((0, 0), 0)
  have hfData {b : ℕ} (hb : b ∈ bad) :
      f b ∈ sourceCoordinateSet L N A K ∧
        sourceVertex (f b) = b := by
    dsimp [f]
    rw [dif_pos hb]
    exact Classical.choose_spec (sourceCoordinate_of_rankBad hL hN hb)
  apply card_le_card_of_injOn f
  · intro b hb
    exact (hfData hb).1
  · intro b₁ hb₁ b₂ hb₂ heq
    have h₁ := (hfData hb₁).2
    have h₂ := (hfData hb₂).2
    rw [heq] at h₁
    exact h₁.symm.trans h₂

/-- A mixed-edge coordinate triple is `((t,u),w)`. -/
abbrev MixedTriple := (ℕ × ℕ) × ℕ

def mixedT (q : MixedTriple) : ℕ := q.1.1
def mixedU (q : MixedTriple) : ℕ := q.1.2
def mixedW (q : MixedTriple) : ℕ := q.2
def mixedLinear (q : MixedTriple) : ℕ := 2 * mixedU q + mixedW q

def mixedOddVertex (q : MixedTriple) : ℕ :=
  mixedT q * mixedW q * mixedLinear q

def mixedSourceVertex (q : MixedTriple) : ℕ :=
  mixedT q * mixedU q * mixedLinear q

/-- Explicit finite coordinate superset for mixed edges. -/
noncomputable def mixedCoordinateSet
    (L N : ℕ) (Ab Kb Ao Ko : ℝ) : Finset MixedTriple :=
  (((Icc 1 N) ×ˢ (Icc 1 N)) ×ˢ (Icc 1 (6 * N))).filter fun q ↦
    Nat.Coprime (mixedU q) (mixedW q) ∧
      mixedW q ≤ 6 * mixedU q ∧
      mixedLinear q ≤ 8 * mixedU q ∧
      mixedOddVertex q ∈ oddHost N ∧
      N / 2 ≤ mixedSourceVertex q ∧ mixedSourceVertex q ≤ N ∧
      Rough L (mixedT q) ∧ Rough L (mixedU q) ∧
      Rough L (mixedLinear q) ∧
      Odd (mixedT q) ∧ Odd (mixedU q) ∧ Odd (mixedW q) ∧
      Odd (mixedLinear q) ∧
      CutoffRegular L Ab Kb (mixedSourceVertex q) ∧
      CutoffRegular L Ao Ko (mixedOddVertex q)

theorem mixedCoordinate_of_edge
    {L N a b : ℕ} {Ab Kb Ao Ko : ℝ}
    (hL : 3 ≤ L) (hN : 2 ≤ N)
    (hedge :
      (a, b) ∈ Erdos327.mixedEdges
        (regularOddHost L Ao Ko N)
        (Erdos327.rankFilteredSource (Erdos327.upto N)
          (regularSource L Ab Kb N)
          ArithmeticFunction.cardFactors)) :
    ∃ q ∈ mixedCoordinateSet L N Ab Kb Ao Ko,
      mixedOddVertex q = a ∧ mixedSourceVertex q = b := by
  have hedgeData := Erdos327.mem_mixedEdges.mp hedge
  have hbRegular :
      b ∈ regularSource L Ab Kb N :=
    (Erdos327.mem_rankFilteredSource.mp hedgeData.2.1).1
  have hedgeRegular :
      (a, b) ∈ Erdos327.mixedEdges
        (regularOddHost L Ao Ko N)
        (regularSource L Ab Kb N) :=
    Erdos327.mem_mixedEdges.mpr
      ⟨hedgeData.1, hbRegular, hedgeData.2.2⟩
  rcases Erdos327.regularMixedEdge_coordinates hL hN hedgeRegular with
    ⟨t, u, w, ht, hu, hw, hcop, ha, hb, huN, hw6u, hx8u,
      htRough, huRough, hxRough, htOdd, huOdd, hwOdd, hxOdd,
      hbRegularity, haRegularity⟩
  have hbData := mem_regularSource.mp hbRegular
  have htB : t ≤ b := by
    rw [hb]
    have hcoeff : 0 < u * (2 * u + w) :=
      Nat.mul_pos hu (by omega)
    calc
      t ≤ t * (u * (2 * u + w)) :=
        Nat.le_mul_of_pos_right t hcoeff
      _ = t * u * (2 * u + w) := by ring
  have htN : t ≤ N := htB.trans hbData.2.1
  have hw6N : w ≤ 6 * N := by omega
  let q : MixedTriple := ((t, u), w)
  have hoddVertex : mixedOddVertex q = a := by
    dsimp [q, mixedOddVertex, mixedT, mixedW, mixedLinear, mixedU]
    exact ha.symm
  have hsourceVertex : mixedSourceVertex q = b := by
    dsimp [q, mixedSourceVertex, mixedT, mixedU, mixedLinear, mixedW]
    exact hb.symm
  refine ⟨q, ?_, hoddVertex, hsourceVertex⟩
  rw [mixedCoordinateSet, mem_filter]
  refine ⟨?_, ?_⟩
  · exact mem_product.mpr
      ⟨mem_product.mpr
        ⟨mem_Icc.mpr ⟨ht, htN⟩,
          mem_Icc.mpr ⟨hu, huN⟩⟩,
        mem_Icc.mpr ⟨hw, hw6N⟩⟩
  · dsimp [q, mixedU, mixedW, mixedLinear, mixedT]
    rw [hoddVertex, hsourceVertex]
    exact ⟨hcop, hw6u, hx8u,
      (mem_regularOddHost.mp hedgeData.1).1,
      hbData.1, hbData.2.1, htRough, huRough, hxRough,
      htOdd, huOdd, hwOdd, hxOdd, hbRegularity, haRegularity⟩

/-- Mixed edges inject into the explicit coordinate set because both
endpoints are recovered from the selected triple. -/
theorem card_mixedEdges_le_mixedCoordinateSet
    {L N : ℕ} {Ab Kb Ao Ko : ℝ}
    (hL : 3 ≤ L) (hN : 2 ≤ N) :
    (Erdos327.mixedEdges
      (regularOddHost L Ao Ko N)
      (Erdos327.rankFilteredSource (Erdos327.upto N)
        (regularSource L Ab Kb N)
        ArithmeticFunction.cardFactors)).card ≤
      (mixedCoordinateSet L N Ab Kb Ao Ko).card := by
  classical
  let edges :=
    Erdos327.mixedEdges
      (regularOddHost L Ao Ko N)
      (Erdos327.rankFilteredSource (Erdos327.upto N)
        (regularSource L Ab Kb N)
        ArithmeticFunction.cardFactors)
  let f : (ℕ × ℕ) → MixedTriple := fun e ↦
    if he : e ∈ edges then
      Classical.choose (mixedCoordinate_of_edge hL hN he)
    else ((0, 0), 0)
  have hfData {e : ℕ × ℕ} (he : e ∈ edges) :
      f e ∈ mixedCoordinateSet L N Ab Kb Ao Ko ∧
        mixedOddVertex (f e) = e.1 ∧
        mixedSourceVertex (f e) = e.2 := by
    dsimp [f]
    rw [dif_pos he]
    exact Classical.choose_spec (mixedCoordinate_of_edge hL hN he)
  apply card_le_card_of_injOn f
  · intro e he
    exact (hfData he).1
  · intro e₁ he₁ e₂ he₂ heq
    have h₁ := (hfData he₁).2
    have h₂ := (hfData he₂).2
    apply Prod.ext
    · rw [← h₁.1, ← h₂.1, heq]
    · rw [← h₁.2, ← h₂.2, heq]

end Erdos327.Analytic
