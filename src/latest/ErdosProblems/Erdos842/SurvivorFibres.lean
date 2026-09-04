import ErdosProblems.Erdos842.CycleBoundary
import ErdosProblems.Erdos842.GoodChords
import ErdosProblems.Erdos842.OrientedRestriction
import ErdosProblems.Erdos842.SurvivorChords

/-!
# Canonical survivor fibres for Erdős Problem 842

This file joins the cyclic-boundary construction to the canonical survivor
and chord APIs.  It proves that the chord key of every survivor is good and
that every good key has exactly the two complementary survivor orientations.
-/

open scoped BigOperators

namespace Erdos842.SurvivorFibres

open Erdos842.Parity
open Erdos842.Coefficient

/-- The selected Hamilton-cycle occurrences of a canonical occurrence set. -/
noncomputable def cycleRestriction {n : ℕ}
    (S : Finset (CanonicalOccurrence n)) : Finset (Fin (3 * n)) :=
  Finset.univ.filter fun v ↦ Sum.inl v ∈ S

@[simp] theorem mem_cycleRestriction {n : ℕ}
    (S : Finset (CanonicalOccurrence n)) (v : Fin (3 * n)) :
    v ∈ cycleRestriction S ↔ Sum.inl v ∈ S := by
  classical
  simp [cycleRestriction]

/-- The canonical cyclic successor is inverse to our canonical predecessor. -/
theorem finCyclicSucc_eq_iff_eq_finCyclePred {m : ℕ} (hm : 0 < m)
    (u v : Fin m) :
    finCyclicSucc m u = v ↔ u = CycleBoundary.finCyclePred hm v := by
  let : NeZero m := ⟨hm.ne'⟩
  simp only [finCyclicSucc_eq_finRotate, finRotate_apply,
    CycleBoundary.finCyclePred, Equiv.subRight_apply]
  constructor <;> intro h
  · rw [← h]
    abel
  · rw [h]
    abel

/-- Balance decomposes into the cyclic boundary and the local triangle
boundary. -/
theorem cycleBoundary_add_triangleBoundary_eq_zero
    {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S : Finset (CanonicalOccurrence n)}
    (hbal : (canonicalIndexedArcs n triangleCoord).Balanced S)
    (i : Fin n) (j : Fin 3) :
    cycleBoundary (CycleBoundary.finCyclePred (by omega : 0 < 3 * n))
        (cycleRestriction S) (canonicalTriangleVertices n triangleCoord i j) +
      triangleBoundary
        ((canonicalDirectedTriangle n triangleCoord i).restriction S) j = 0 := by
  classical
  let v := canonicalTriangleVertices n triangleCoord i j
  let p := CycleBoundary.finCyclePred (by omega : 0 < 3 * n) v
  have hvcoord : triangleCoord v = (i, j) := by
    simp [v, canonicalTriangleVertices]
  have hpcycle : finCyclicSucc (3 * n) p = v :=
    (finCyclicSucc_eq_iff_eq_finCyclePred (by omega : 0 < 3 * n) p v).2 rfl
  have hout :
      ((S.filter fun a ↦
        (canonicalIndexedArcs n triangleCoord).tail a = v).card) =
        (if Sum.inl v ∈ S then 1 else 0) +
          if Sum.inr (i, j) ∈ S then 1 else 0 := by
    have hset : S.filter (fun a ↦
        (canonicalIndexedArcs n triangleCoord).tail a = v) =
        (if Sum.inl v ∈ S then {Sum.inl v} else ∅) ∪
          if Sum.inr (i, j) ∈ S then {Sum.inr (i, j)} else ∅ := by
      ext a
      cases a with
      | inl u =>
          rw [Finset.mem_filter]
          change (Sum.inl u ∈ S ∧ u = v) ↔ _
          by_cases hmem : Sum.inl v ∈ S <;> simp [hmem] <;> aesop
      | inr q =>
          rw [Finset.mem_filter]
          change (Sum.inr q ∈ S ∧ triangleCoord.symm q = v) ↔ _
          have hq : triangleCoord.symm q = v ↔ q = (i, j) := by
            simp [Equiv.symm_apply_eq, hvcoord]
          rw [hq]
          by_cases hmem : Sum.inr (i, j) ∈ S <;>
            simp [hmem] <;> aesop
    rw [hset]
    by_cases hc : Sum.inl v ∈ S <;>
      by_cases ht : Sum.inr (i, j) ∈ S <;> simp [hc, ht]
  have hin :
      ((S.filter fun a ↦
        (canonicalIndexedArcs n triangleCoord).head a = v).card) =
        (if Sum.inl p ∈ S then 1 else 0) +
          if Sum.inr (i, triPred j) ∈ S then 1 else 0 := by
    have hset : S.filter (fun a ↦
        (canonicalIndexedArcs n triangleCoord).head a = v) =
        (if Sum.inl p ∈ S then {Sum.inl p} else ∅) ∪
          if Sum.inr (i, triPred j) ∈ S then {Sum.inr (i, triPred j)} else ∅ := by
      ext a
      cases a with
      | inl u =>
          rw [Finset.mem_filter]
          change (Sum.inl u ∈ S ∧ finCyclicSucc (3 * n) u = v) ↔ _
          have hu : finCyclicSucc (3 * n) u = v ↔ u = p := by
            exact finCyclicSucc_eq_iff_eq_finCyclePred (by omega : 0 < 3 * n) u v
          rw [hu]
          by_cases hmem : Sum.inl p ∈ S <;> simp [hmem] <;> aesop
      | inr q =>
          rw [Finset.mem_filter]
          change (Sum.inr q ∈ S ∧ triangleCoord.symm (q.1, q.2 + 1) = v) ↔ _
          have hq : triangleCoord.symm (q.1, q.2 + 1) = v ↔
              q = (i, triPred j) := by
            rw [Equiv.symm_apply_eq, hvcoord]
            rcases q with ⟨q1, q2⟩
            fin_cases q2 <;> fin_cases j <;> simp [triPred]
          rw [hq]
          by_cases hmem : Sum.inr (i, triPred j) ∈ S <;> simp [hmem] <;> aesop
    rw [hset]
    by_cases hc : Sum.inl p ∈ S <;>
      by_cases ht : Sum.inr (i, triPred j) ∈ S <;> simp [hc, ht]
  have hcard := hbal v
  change (S.filter fun a ↦
      (canonicalIndexedArcs n triangleCoord).head a = v).card =
    (S.filter fun a ↦
      (canonicalIndexedArcs n triangleCoord).tail a = v).card at hcard
  rw [hin, hout] at hcard
  simp only [cycleBoundary, triangleBoundary, mem_cycleRestriction,
    DirectedTriangle.mem_restriction, canonicalDirectedTriangle]
  change
    ((if Sum.inl p ∈ S then 1 else 0) - (if Sum.inl v ∈ S then 1 else 0)) +
      ((if Sum.inr (i, triPred j) ∈ S then 1 else 0) -
        (if Sum.inr (i, j) ∈ S then 1 else 0)) = 0
  split_ifs at hcard ⊢ <;> omega

/-- The inclusive prefix count of a member is one plus its rank in the
increasing enumeration of the finset. -/
theorem prefixCount_eq_orderRank_succ {m k : ℕ}
    (s : Finset (Fin m)) (hcard : s.card = k) {x : Fin m} (hx : x ∈ s) :
    CycleBoundary.prefixCount s x =
      ((s.orderIsoOfFin hcard).symm ⟨x, hx⟩).val + 1 := by
  classical
  let r := (s.orderIsoOfFin hcard).symm ⟨x, hx⟩
  change (s.filter fun y ↦ y ≤ x).card = r.val + 1
  rw [← Fin.card_Iic r]
  apply Finset.card_bij (fun y hy ↦
    (s.orderIsoOfFin hcard).symm
      ⟨y, (Finset.mem_filter.mp hy).1⟩)
  · intro y hy
    rw [Finset.mem_Iic]
    apply (s.orderIsoOfFin hcard).symm.le_iff_le.mpr
    exact (Finset.mem_filter.mp hy).2
  · intro a ha b hb hab
    exact congrArg Subtype.val ((s.orderIsoOfFin hcard).symm.injective hab)
  · intro q hq
    refine ⟨((s.orderIsoOfFin hcard) q).val, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨((s.orderIsoOfFin hcard) q).property, ?_⟩
      change (s.orderIsoOfFin hcard) q ≤ ⟨x, hx⟩
      rw [← (s.orderIsoOfFin hcard).apply_symm_apply ⟨x, hx⟩]
      apply (s.orderIsoOfFin hcard).le_iff_le.mpr
      exact Finset.mem_Iic.mp hq
    · convert (s.orderIsoOfFin hcard).symm_apply_apply q using 1

/-- For the selected chord endpoints, `prefixCount` is one plus the compressed
Hamiltonian rank used by `GoodChords.endpointCyclicOrder`. -/
theorem prefixCount_selectedEndpoint {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (p : ChordCrossing.Endpoint (Fin n)) :
    CycleBoundary.prefixCount (GoodChords.selectedVertices triangleCoord key)
        (GoodChords.selectedEndpoint triangleCoord key p) =
      (GoodChords.endpointCyclicOrder triangleCoord key p).val + 1 := by
  classical
  let used := GoodChords.selectedVertices triangleCoord key
  have hp : GoodChords.selectedEndpoint triangleCoord key p ∈ used :=
    (GoodChords.mem_selectedVertices triangleCoord key _).2 ⟨p, rfl⟩
  have h := prefixCount_eq_orderRank_succ used
    (GoodChords.card_selectedVertices triangleCoord key) hp
  calc
    CycleBoundary.prefixCount used
        (GoodChords.selectedEndpoint triangleCoord key p) =
        ((used.orderIsoOfFin
          (GoodChords.card_selectedVertices triangleCoord key)).symm
            ⟨GoodChords.selectedEndpoint triangleCoord key p, hp⟩).val + 1 := h
    _ = (GoodChords.endpointCyclicOrder triangleCoord key p).val + 1 := by
      congr 2

/-- The selected vertices are exactly those whose local coordinate is not the
vertex opposite the selected chord. -/
theorem mem_selectedVertices_iff_coord_ne_key {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (i : Fin n) (j : Fin 3) :
    GoodChords.triangleVertices triangleCoord i j ∈
        GoodChords.selectedVertices triangleCoord key ↔ j ≠ key i := by
  classical
  rw [GoodChords.mem_selectedVertices]
  constructor
  · rintro ⟨⟨q, e⟩, h⟩
    have hc := congrArg triangleCoord h
    rw [GoodChords.triangleCoord_selectedEndpoint] at hc
    simp only [GoodChords.triangleVertices, Equiv.apply_symm_apply,
      Prod.mk.injEq] at hc
    rcases hc with ⟨hqi, hcoord⟩
    intro hj
    have hcoord' : (if e = 0 then key i + 1 else key i + 2) = j := by
      simpa [hqi] using hcoord
    rw [hj] at hcoord'
    generalize hk : key i = k at hcoord'
    fin_cases e <;> fin_cases k <;> simp_all
  · intro hne
    rcases fin_three_cyclic_adj hne.symm with h | h
    · refine ⟨(i, 0), ?_⟩
      apply triangleCoord.injective
      rw [GoodChords.triangleCoord_selectedEndpoint]
      simp [GoodChords.triangleVertices, h]
    · refine ⟨(i, 1), ?_⟩
      have h2 : key i + 2 = j := by
        generalize hk : key i = k at h ⊢
        fin_cases k <;> fin_cases j <;> simp_all
      apply triangleCoord.injective
      rw [GoodChords.triangleCoord_selectedEndpoint]
      simp [GoodChords.triangleVertices, h2]

/-- In a nondegenerate directed triangle the two endpoints of the chord
opposite `triangleChordIndex` carry different boundary signs. -/
theorem triangleBoundary_chord_endpoints_ne
    (R : Finset (Fin 3)) (hne : R ≠ ∅) (hfull : R ≠ Finset.univ) :
    triangleBoundary R (triangleChordIndex R + 1) ≠
      triangleBoundary R (triangleChordIndex R + 2) := by
  revert R
  decide

/-- The cyclic boundary of a survivor is supported exactly at the two
endpoints retained from every triangle. -/
theorem survivor_cycleBoundary_support {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S : Finset (CanonicalOccurrence n)}
    (hS : S ∈ canonicalSurvivors n triangleCoord) (v : Fin (3 * n)) :
    cycleBoundary (CycleBoundary.finCyclePred (by omega : 0 < 3 * n))
        (cycleRestriction S) v ≠ 0 ↔
      v ∈ GoodChords.selectedVertices triangleCoord
        (canonicalChordKey n triangleCoord S) := by
  let i := (triangleCoord v).1
  let j := (triangleCoord v).2
  have hv : v = GoodChords.triangleVertices triangleCoord i j := by
    apply triangleCoord.injective
    simp [i, j, GoodChords.triangleVertices]
  have hv' : v = canonicalTriangleVertices n triangleCoord i j := by
    simpa [canonicalTriangleVertices, GoodChords.triangleVertices] using hv
  have hbal := (mem_canonicalSurvivors n triangleCoord S).mp hS |>.1
  have hdeg := (mem_canonicalSurvivors n triangleCoord S).mp hS |>.2
  have hnondeg :
      (canonicalDirectedTriangle n triangleCoord i).restriction S ≠ ∅ ∧
        (canonicalDirectedTriangle n triangleCoord i).restriction S ≠ Finset.univ := by
    have hi : i ∉ canonicalDegenerateIndices n triangleCoord S := by
      rw [hdeg]
      simp
    rw [mem_canonicalDegenerateIndices] at hi
    push_neg at hi
    exact ⟨hi.1.ne_empty, hi.2⟩
  have hsum := cycleBoundary_add_triangleBoundary_eq_zero hn triangleCoord hbal i j
  have hsum' :
      cycleBoundary (CycleBoundary.finCyclePred (by omega : 0 < 3 * n))
          (cycleRestriction S) (GoodChords.triangleVertices triangleCoord i j) +
        triangleBoundary ((canonicalDirectedTriangle n triangleCoord i).restriction S) j = 0 := by
    simpa [canonicalTriangleVertices, GoodChords.triangleVertices] using hsum
  rw [hv']
  rw [show canonicalTriangleVertices n triangleCoord i j =
    GoodChords.triangleVertices triangleCoord i j from rfl]
  rw [mem_selectedVertices_iff_coord_ne_key]
  have hzero := SurvivorChords.zero_boundary_iff_key
    ((canonicalDirectedTriangle n triangleCoord i).restriction S)
    hnondeg.1 hnondeg.2 j
  change triangleBoundary ((canonicalDirectedTriangle n triangleCoord i).restriction S) j = 0 ↔
    j = canonicalChordKey n triangleCoord S i at hzero
  constructor
  · intro hcycle hkey
    have htri : triangleBoundary
        ((canonicalDirectedTriangle n triangleCoord i).restriction S) j = 0 :=
      hzero.mpr hkey
    apply hcycle
    rw [htri] at hsum'
    simpa using hsum'
  · intro hkey hcycle
    have htri : triangleBoundary
        ((canonicalDirectedTriangle n triangleCoord i).restriction S) j = 0 := by
      rw [hcycle] at hsum'
      simpa using hsum'
    exact hkey (hzero.mp htri)

/-- A survivor's Hamilton-cycle restriction is one of the two prefix-parity
solutions for the support determined by its chord key. -/
theorem survivor_cycleRestriction_eq_selection {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S : Finset (CanonicalOccurrence n)}
    (hS : S ∈ canonicalSurvivors n triangleCoord) :
    ∃ base : Bool, cycleRestriction S =
      CycleBoundary.selection
        (GoodChords.selectedVertices triangleCoord
          (canonicalChordKey n triangleCoord S)) base := by
  classical
  let used := GoodChords.selectedVertices triangleCoord
    (canonicalChordKey n triangleCoord S)
  have heven : Even used.card := by
    rw [GoodChords.card_selectedVertices]
    exact even_two_mul _
  have hsupport : ∀ v,
      (cycleBoundary (CycleBoundary.finCyclePred (by omega : 0 < 3 * n))
          (cycleRestriction S) v ≠ 0 ↔
        cycleBoundary (CycleBoundary.finCyclePred (by omega : 0 < 3 * n))
          (CycleBoundary.selection used false) v ≠ 0) := by
    intro v
    rw [survivor_cycleBoundary_support hn triangleCoord hS v,
      CycleBoundary.cycleBoundary_selection
        (by omega : 0 < 3 * n) used false heven v]
    change (v ∈ used) ↔ CycleBoundary.alternatingBoundary used false v ≠ 0
    by_cases hv : v ∈ used
    · by_cases hp : CycleBoundary.prefixCount used v % 2 = 0 <;>
        simp [CycleBoundary.alternatingBoundary, hv, hp]
    · simp [CycleBoundary.alternatingBoundary, hv]
  rcases eq_or_compl_of_cycleBoundary_support_eq
      (CycleBoundary.finCyclePred (by omega : 0 < 3 * n))
      (CycleBoundary.finCyclePred_transitive (by omega : 0 < 3 * n))
      hsupport with h | h
  · exact ⟨false, h⟩
  · refine ⟨true, ?_⟩
    change cycleRestriction S = CycleBoundary.selection used true
    have hc := CycleBoundary.selection_not_base used false
    simp only [Bool.not_false] at hc
    rw [hc]
    exact h

/-- Different prefix-parity boundary signs at two selected endpoints force
different canonical alternating Boolean signs in the compressed endpoint
order. -/
theorem alternatingSign_ne_of_boundary_ne {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (base : Bool)
    (p q : ChordCrossing.Endpoint (Fin n))
    (hne : CycleBoundary.alternatingBoundary
        (GoodChords.selectedVertices triangleCoord key) base
          (GoodChords.selectedEndpoint triangleCoord key p) ≠
      CycleBoundary.alternatingBoundary
        (GoodChords.selectedVertices triangleCoord key) base
          (GoodChords.selectedEndpoint triangleCoord key q)) :
    ChordCrossing.alternatingSign
        (GoodChords.endpointCyclicOrder triangleCoord key) false p ≠
      ChordCrossing.alternatingSign
        (GoodChords.endpointCyclicOrder triangleCoord key) false q := by
  classical
  let used := GoodChords.selectedVertices triangleCoord key
  have hp : GoodChords.selectedEndpoint triangleCoord key p ∈ used :=
    (GoodChords.mem_selectedVertices triangleCoord key _).2 ⟨p, rfl⟩
  have hq : GoodChords.selectedEndpoint triangleCoord key q ∈ used :=
    (GoodChords.mem_selectedVertices triangleCoord key _).2 ⟨q, rfl⟩
  simp only [ne_eq] at hne
  rw [prefixCount_selectedEndpoint, prefixCount_selectedEndpoint] at hne
  unfold ChordCrossing.alternatingSign
  let rp := (GoodChords.endpointCyclicOrder triangleCoord key p).val
  let rq := (GoodChords.endpointCyclicOrder triangleCoord key q).val
  change (if rp % 2 = 0 then false else true) ≠
    (if rq % 2 = 0 then false else true)
  change (if (rp + 1) % 2 = CycleBoundary.boolNat base then (-1 : ℤ) else 1) ≠
    (if (rq + 1) % 2 = CycleBoundary.boolNat base then (-1 : ℤ) else 1) at hne
  cases base <;>
    by_cases hp0 : rp % 2 = 0 <;>
    by_cases hq0 : rq % 2 = 0 <;>
    simp [CycleBoundary.boolNat, hp0, hq0] at hne ⊢ <;> omega

/-- The chord key of every canonical survivor has even selected crossing
degree at every triangle, hence belongs to the canonical good-key finset. -/
theorem canonicalChordKey_mem_good {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S : Finset (CanonicalOccurrence n)}
    (hS : S ∈ canonicalSurvivors n triangleCoord) :
    canonicalChordKey n triangleCoord S ∈
      canonicalGoodChordKeys n triangleCoord := by
  classical
  let key := canonicalChordKey n triangleCoord S
  let used := GoodChords.selectedVertices triangleCoord key
  obtain ⟨base, hcycle⟩ :=
    survivor_cycleRestriction_eq_selection hn triangleCoord hS
  have hbal := (mem_canonicalSurvivors n triangleCoord S).mp hS |>.1
  have hnondeg : ∀ i : Fin n,
      (canonicalDirectedTriangle n triangleCoord i).restriction S ≠ ∅ ∧
        (canonicalDirectedTriangle n triangleCoord i).restriction S ≠ Finset.univ := by
    intro i
    have hdeg := (mem_canonicalSurvivors n triangleCoord S).mp hS |>.2
    have hi : i ∉ canonicalDegenerateIndices n triangleCoord S := by
      rw [hdeg]
      simp
    rw [mem_canonicalDegenerateIndices] at hi
    push_neg at hi
    exact ⟨hi.1.ne_empty, hi.2⟩
  have hcompat : ChordCrossing.CompatibleAlternatingBase
      (GoodChords.endpointCyclicOrder triangleCoord key) false := by
    intro i
    let p : ChordCrossing.Endpoint (Fin n) := (i, 0)
    let q : ChordCrossing.Endpoint (Fin n) := (i, 1)
    let vp := GoodChords.selectedEndpoint triangleCoord key p
    let vq := GoodChords.selectedEndpoint triangleCoord key q
    have hbp := cycleBoundary_add_triangleBoundary_eq_zero hn triangleCoord hbal
      i (key i + 1)
    have hbq := cycleBoundary_add_triangleBoundary_eq_zero hn triangleCoord hbal
      i (key i + 2)
    have hvp : canonicalTriangleVertices n triangleCoord i (key i + 1) = vp := by
      apply triangleCoord.injective
      simp [vp, p, canonicalTriangleVertices,
        GoodChords.triangleVertices, GoodChords.selectedEndpoint,
        ChordCrossing.triangleSide]
    have hvq : canonicalTriangleVertices n triangleCoord i (key i + 2) = vq := by
      apply triangleCoord.injective
      simp [vq, q, canonicalTriangleVertices,
        GoodChords.triangleVertices, GoodChords.selectedEndpoint,
        ChordCrossing.triangleSide]
    rw [hvp, hcycle,
      CycleBoundary.cycleBoundary_selection
        (by omega : 0 < 3 * n) used base
        (by rw [GoodChords.card_selectedVertices]; exact even_two_mul _) vp] at hbp
    rw [hvq, hcycle,
      CycleBoundary.cycleBoundary_selection
        (by omega : 0 < 3 * n) used base
        (by rw [GoodChords.card_selectedVertices]; exact even_two_mul _) vq] at hbq
    have htri := triangleBoundary_chord_endpoints_ne
      ((canonicalDirectedTriangle n triangleCoord i).restriction S)
      (hnondeg i).1 (hnondeg i).2
    change triangleBoundary ((canonicalDirectedTriangle n triangleCoord i).restriction S)
        (key i + 1) ≠
      triangleBoundary ((canonicalDirectedTriangle n triangleCoord i).restriction S)
        (key i + 2) at htri
    have halt : CycleBoundary.alternatingBoundary used base vp ≠
        CycleBoundary.alternatingBoundary used base vq := by
      intro heq
      apply htri
      linarith
    exact alternatingSign_ne_of_boundary_ne triangleCoord key base p q halt
  have hall : ChordCrossing.AllSelectedCrossingDegreesEven
      (GoodChords.endpointCyclicOrder triangleCoord key) :=
    (ChordCrossing.all_even_iff_compatibleAlternatingBase _ false).mpr hcompat
  have hgood : key ∈ GoodChords.goodSelections triangleCoord :=
    (GoodChords.mem_goodSelections_iff_allSelectedCrossingDegreesEven
      triangleCoord key).mpr hall
  rw [canonicalGoodChordKeys_eq_goodSelections]
  exact hgood

/-- Pointwise identification of the integer prefix boundary with the Boolean
alternating sign on the compressed endpoint order. -/
theorem alternatingBoundary_selectedEndpoint {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (base : Bool)
    (p : ChordCrossing.Endpoint (Fin n)) :
    CycleBoundary.alternatingBoundary
        (GoodChords.selectedVertices triangleCoord key) base
        (GoodChords.selectedEndpoint triangleCoord key p) =
      if ChordCrossing.alternatingSign
          (GoodChords.endpointCyclicOrder triangleCoord key) base p
        then -1 else 1 := by
  classical
  let used := GoodChords.selectedVertices triangleCoord key
  have hp : GoodChords.selectedEndpoint triangleCoord key p ∈ used :=
    (GoodChords.mem_selectedVertices triangleCoord key _).2 ⟨p, rfl⟩
  simp [CycleBoundary.alternatingBoundary, used, hp]
  rw [prefixCount_selectedEndpoint]
  unfold ChordCrossing.alternatingSign
  let r := (GoodChords.endpointCyclicOrder triangleCoord key p).val
  change (if (r + 1) % 2 = CycleBoundary.boolNat base then (-1 : ℤ) else 1) =
    if (if r % 2 = 0 then base else !base) then -1 else 1
  cases base <;> by_cases hr : r % 2 = 0 <;>
    simp [CycleBoundary.boolNat, hr] <;> omega

/-- Choose the local directed-triangle orientation that cancels the prescribed
cycle boundary at the successor endpoint. -/
noncomputable def localIsBase {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (base : Bool) (i : Fin n) : Bool :=
  decide (CycleBoundary.alternatingBoundary
    (GoodChords.selectedVertices triangleCoord key) base
    (GoodChords.selectedEndpoint triangleCoord key (i, 0)) = 1)

noncomputable def localRestriction {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (base : Bool) (i : Fin n) : Finset (Fin 3) :=
  OrientedRestriction.orientedRestriction (key i)
    (localIsBase triangleCoord key base i)

/-- If the key is good, each constructed local restriction has boundary the
negative of the prescribed alternating cycle boundary at all three vertices. -/
theorem localRestriction_boundary {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (base : Bool)
    (hall : ChordCrossing.AllSelectedCrossingDegreesEven
      (GoodChords.endpointCyclicOrder triangleCoord key))
    (i : Fin n) (j : Fin 3) :
    triangleBoundary (localRestriction triangleCoord key base i) j =
      -CycleBoundary.alternatingBoundary
        (GoodChords.selectedVertices triangleCoord key) base
        (GoodChords.triangleVertices triangleCoord i j) := by
  classical
  let ord := GoodChords.endpointCyclicOrder triangleCoord key
  let p : ChordCrossing.Endpoint (Fin n) := (i, 0)
  let q : ChordCrossing.Endpoint (Fin n) := (i, 1)
  have hcompat : ChordCrossing.CompatibleAlternatingBase ord base :=
    (ChordCrossing.all_even_iff_compatibleAlternatingBase ord base).mp hall
  have hpq := hcompat i
  have hp := alternatingBoundary_selectedEndpoint triangleCoord key base p
  have hq := alternatingBoundary_selectedEndpoint triangleCoord key base q
  have hvp : GoodChords.selectedEndpoint triangleCoord key p =
      GoodChords.triangleVertices triangleCoord i (triSucc (key i)) := by
    apply triangleCoord.injective
    simp only [p, GoodChords.triangleCoord_selectedEndpoint,
      GoodChords.triangleVertices, Equiv.apply_symm_apply, Prod.mk.injEq,
      true_and, Fin.isValue]
    rfl
  have hvq : GoodChords.selectedEndpoint triangleCoord key q =
      GoodChords.triangleVertices triangleCoord i (triPred (key i)) := by
    apply triangleCoord.injective
    simp only [q, GoodChords.triangleCoord_selectedEndpoint,
      GoodChords.triangleVertices, Equiv.apply_symm_apply, Prod.mk.injEq,
      true_and, Fin.isValue]
    rfl
  rw [hvp] at hp
  rw [hvq] at hq
  rcases SurvivorChords.fin3_eq_self_or_succ_or_pred (key i) j with h | h | h
  · subst j
    have hnot : GoodChords.triangleVertices triangleCoord i (key i) ∉
        GoodChords.selectedVertices triangleCoord key := by
      rw [mem_selectedVertices_iff_coord_ne_key]
      simp
    simp [localRestriction, CycleBoundary.alternatingBoundary, hnot]
  · subst j
    rw [localRestriction,
      OrientedRestriction.triangleBoundary_orientedRestriction_succ]
    rw [hp]
    unfold localIsBase
    cases hs : ChordCrossing.alternatingSign ord base p <;>
      simp_all [ord, p]
  · subst j
    rw [localRestriction,
      OrientedRestriction.triangleBoundary_orientedRestriction_pred]
    rw [hq]
    unfold localIsBase
    cases hs : ChordCrossing.alternatingSign ord base p <;>
      cases ht : ChordCrossing.alternatingSign ord base q <;>
      simp_all [ord, p, q]

/-- The coefficient layer and the prefix-parity layer use the same canonical
predecessor. -/
theorem canonicalCyclePred_eq_finCyclePred {n : ℕ} (hn : 0 < n) :
    canonicalCyclePred n =
      CycleBoundary.finCyclePred (by omega : 0 < 3 * n) := by
  ext v
  let : NeZero (3 * n) := ⟨by omega⟩
  simp [canonicalCyclePred, CycleBoundary.finCyclePred]

/-- Assemble a global occurrence selection from its prefix-parity cycle part
and the uniquely compatible local triangle orientations. -/
noncomputable def survivorFor {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (base : Bool) :
    Finset (CanonicalOccurrence n) := by
  classical
  exact Finset.univ.filter fun a ↦ match a with
      | .inl v => v ∈ CycleBoundary.selection
          (GoodChords.selectedVertices triangleCoord key) base
      | .inr ij => ij.2 ∈ localRestriction triangleCoord key base ij.1

@[simp] theorem mem_survivorFor_cycle {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (base : Bool) (v : Fin (3 * n)) :
    Sum.inl v ∈ survivorFor triangleCoord key base ↔
      v ∈ CycleBoundary.selection
        (GoodChords.selectedVertices triangleCoord key) base := by
  classical
  simp [survivorFor]

@[simp] theorem mem_survivorFor_triangle {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (base : Bool) (i : Fin n) (j : Fin 3) :
    Sum.inr (i, j) ∈ survivorFor triangleCoord key base ↔
      j ∈ localRestriction triangleCoord key base i := by
  classical
  simp [survivorFor]

@[simp] theorem cycleRestriction_survivorFor {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (base : Bool) :
    cycleRestriction (survivorFor triangleCoord key base) =
      CycleBoundary.selection
        (GoodChords.selectedVertices triangleCoord key) base := by
  classical
  ext v
  simp

@[simp] theorem canonicalCycleRestriction_survivorFor {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (base : Bool) :
    canonicalCycleRestriction n (survivorFor triangleCoord key base) =
      CycleBoundary.selection
        (GoodChords.selectedVertices triangleCoord key) base := by
  classical
  ext v
  simp

@[simp] theorem triangleRestriction_survivorFor {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (base : Bool) (i : Fin n) :
    (canonicalDirectedTriangle n triangleCoord i).restriction
        (survivorFor triangleCoord key base) =
      localRestriction triangleCoord key base i := by
  classical
  ext j
  simp [DirectedTriangle.mem_restriction, canonicalDirectedTriangle]

/-- The assembled occurrence set is balanced whenever the underlying chord
key has all selected crossing degrees even. -/
theorem survivorFor_balanced {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (base : Bool)
    (hall : ChordCrossing.AllSelectedCrossingDegreesEven
      (GoodChords.endpointCyclicOrder triangleCoord key)) :
    (canonicalIndexedArcs n triangleCoord).Balanced
      (survivorFor triangleCoord key base) := by
  apply canonical_balanced_of_boundary n triangleCoord
  intro v
  let i := (triangleCoord v).1
  let j := (triangleCoord v).2
  have hv : v = GoodChords.triangleVertices triangleCoord i j := by
    apply triangleCoord.injective
    simp [i, j, GoodChords.triangleVertices]
  rw [canonicalCyclePred_eq_finCyclePred hn,
    canonicalCycleRestriction_survivorFor,
    CycleBoundary.cycleBoundary_selection
      (by omega : 0 < 3 * n)
      (GoodChords.selectedVertices triangleCoord key) base
      (by rw [GoodChords.card_selectedVertices]; exact even_two_mul _),
    triangleRestriction_survivorFor]
  change CycleBoundary.alternatingBoundary
      (GoodChords.selectedVertices triangleCoord key) base v +
    triangleBoundary (localRestriction triangleCoord key base i) j = 0
  rw [hv, localRestriction_boundary triangleCoord key base hall i j]
  ring

/-- Every good chord key and either base bit produce a canonical survivor with
that exact chord key. -/
theorem survivorFor_mem_and_key {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {key : Fin n → Fin 3}
    (hkey : key ∈ canonicalGoodChordKeys n triangleCoord) (base : Bool) :
    survivorFor triangleCoord key base ∈ canonicalSurvivors n triangleCoord ∧
      canonicalChordKey n triangleCoord (survivorFor triangleCoord key base) = key := by
  classical
  have hall : ChordCrossing.AllSelectedCrossingDegreesEven
      (GoodChords.endpointCyclicOrder triangleCoord key) := by
    rw [canonicalGoodChordKeys_eq_goodSelections] at hkey
    exact (GoodChords.mem_goodSelections_iff_allSelectedCrossingDegreesEven
      triangleCoord key).mp hkey
  have hbal := survivorFor_balanced hn triangleCoord key base hall
  have hdeg : canonicalDegenerateIndices n triangleCoord
      (survivorFor triangleCoord key base) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i
    rw [mem_canonicalDegenerateIndices, triangleRestriction_survivorFor]
    push Not
    exact ⟨Finset.nonempty_iff_ne_empty.mpr
        (OrientedRestriction.orientedRestriction_ne_empty _ _),
      OrientedRestriction.orientedRestriction_ne_univ _ _⟩
  constructor
  · exact (mem_canonicalSurvivors n triangleCoord _).2 ⟨hbal, hdeg⟩
  · funext i
    change SurvivorChords.unorientedChordKey
      ((canonicalDirectedTriangle n triangleCoord i).restriction
        (survivorFor triangleCoord key base)) = key i
    rw [triangleRestriction_survivorFor]
    exact OrientedRestriction.unorientedChordKey_orientedRestriction _ _

/-- Every survivor in the fibre of a good key is one of the two explicitly
constructed base orientations. -/
theorem survivor_eq_survivorFor {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {key : Fin n → Fin 3}
    (hgood : key ∈ canonicalGoodChordKeys n triangleCoord)
    {S : Finset (CanonicalOccurrence n)}
    (hS : S ∈ canonicalSurvivors n triangleCoord)
    (hkey : canonicalChordKey n triangleCoord S = key) :
    ∃ base : Bool, S = survivorFor triangleCoord key base := by
  classical
  have hall : ChordCrossing.AllSelectedCrossingDegreesEven
      (GoodChords.endpointCyclicOrder triangleCoord key) := by
    have hg := hgood
    rw [canonicalGoodChordKeys_eq_goodSelections] at hg
    exact (GoodChords.mem_goodSelections_iff_allSelectedCrossingDegreesEven
      triangleCoord key).mp hg
  obtain ⟨base, hcycle0⟩ :=
    survivor_cycleRestriction_eq_selection hn triangleCoord hS
  have hcycle : cycleRestriction S = CycleBoundary.selection
      (GoodChords.selectedVertices triangleCoord key) base := by
    simpa [hkey] using hcycle0
  have hbal := (mem_canonicalSurvivors n triangleCoord S).mp hS |>.1
  have hnondeg : ∀ i : Fin n,
      (canonicalDirectedTriangle n triangleCoord i).restriction S ≠ ∅ ∧
        (canonicalDirectedTriangle n triangleCoord i).restriction S ≠ Finset.univ := by
    intro i
    have hdeg := (mem_canonicalSurvivors n triangleCoord S).mp hS |>.2
    have hi : i ∉ canonicalDegenerateIndices n triangleCoord S := by
      rw [hdeg]
      simp
    rw [mem_canonicalDegenerateIndices] at hi
    push_neg at hi
    exact ⟨hi.1.ne_empty, hi.2⟩
  have hrestr : ∀ i : Fin n,
      (canonicalDirectedTriangle n triangleCoord i).restriction S =
        localRestriction triangleCoord key base i := by
    intro i
    let R := (canonicalDirectedTriangle n triangleCoord i).restriction S
    have hRkey : SurvivorChords.unorientedChordKey R = key i := by
      change canonicalChordKey n triangleCoord S i = key i
      exact congrFun hkey i
    have hb := cycleBoundary_add_triangleBoundary_eq_zero hn triangleCoord hbal
      i (triSucc (key i))
    have hv : canonicalTriangleVertices n triangleCoord i (triSucc (key i)) =
        GoodChords.triangleVertices triangleCoord i (triSucc (key i)) := rfl
    rw [hv, hcycle,
      CycleBoundary.cycleBoundary_selection
        (by omega : 0 < 3 * n)
        (GoodChords.selectedVertices triangleCoord key) base
        (by rw [GoodChords.card_selectedVertices]; exact even_two_mul _)] at hb
    have hlocal := localRestriction_boundary triangleCoord key base hall
      i (triSucc (key i))
    rw [localRestriction,
      OrientedRestriction.triangleBoundary_orientedRestriction_succ] at hlocal
    apply OrientedRestriction.eq_orientedRestriction_of_key_of_boundary_succ
      R (key i) (localIsBase triangleCoord key base i)
      (hnondeg i).1 (hnondeg i).2 hRkey
    linarith
  refine ⟨base, ?_⟩
  ext a
  cases a with
  | inl v =>
      rw [← mem_cycleRestriction, hcycle]
      simp
  | inr ij =>
      rcases ij with ⟨i, j⟩
      change (canonicalDirectedTriangle n triangleCoord i).arc j ∈ S ↔ _
      rw [← (canonicalDirectedTriangle n triangleCoord i).mem_restriction,
        hrestr i]
      simp

/-- The two explicitly constructed global orientations are distinct when the
canonical cycle is nonempty. -/
theorem survivorFor_false_ne_true {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) :
    survivorFor triangleCoord key false ≠ survivorFor triangleCoord key true := by
  classical
  intro h
  let used := GoodChords.selectedVertices triangleCoord key
  have hc := congrArg cycleRestriction h
  have hsel : CycleBoundary.selection used false =
      CycleBoundary.selection used true := by
    simpa [used] using hc
  have hcomp := CycleBoundary.selection_not_base used false
  simp only [Bool.not_false] at hcomp
  rw [hcomp] at hsel
  let v : Fin (3 * n) := ⟨0, by omega⟩
  have hm := congrArg (fun C : Finset (Fin (3 * n)) ↦ v ∈ C) hsel
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hm
  tauto

/-- Every good chord key has exactly its two global alternating survivor
orientations. -/
theorem canonicalChordKey_fibre_card_eq_two {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3)
    (hgood : key ∈ canonicalGoodChordKeys n triangleCoord) :
    ((canonicalSurvivors n triangleCoord).filter fun S ↦
      canonicalChordKey n triangleCoord S = key).card = 2 := by
  classical
  have hfiber :
      (canonicalSurvivors n triangleCoord).filter (fun S ↦
          canonicalChordKey n triangleCoord S = key) =
        {survivorFor triangleCoord key false,
          survivorFor triangleCoord key true} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hS, hkey⟩
      obtain ⟨base, hbase⟩ :=
        survivor_eq_survivorFor hn triangleCoord hgood hS hkey
      cases base
      · exact Or.inl hbase
      · exact Or.inr hbase
    · rintro (rfl | rfl)
      · exact survivorFor_mem_and_key hn triangleCoord hgood false
      · exact survivorFor_mem_and_key hn triangleCoord hgood true
  rw [hfiber, Finset.card_pair (survivorFor_false_ne_true hn triangleCoord key)]

/-- The concrete canonical central coefficient is nonzero for every positive
number of triangles. -/
theorem canonicalCoeff_ne_zero_pos {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    MvPolynomial.coeff (canonicalIndexedArcs n triangleCoord).centralExponent
      (canonicalIndexedArcs n triangleCoord).polynomial ≠ 0 := by
  apply canonicalCoeff_ne_zero_of_goodChord_fibres hn triangleCoord
  · intro S hS
    exact canonicalChordKey_mem_good hn triangleCoord hS
  · intro key hkey
    exact canonicalChordKey_fibre_card_eq_two hn triangleCoord key hkey

/-- Final all-`n` canonical coefficient theorem, including the empty base
case. -/
theorem canonicalCoeff_ne_zero (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    MvPolynomial.coeff (canonicalIndexedArcs n triangleCoord).centralExponent
      (canonicalIndexedArcs n triangleCoord).polynomial ≠ 0 := by
  by_cases hn : n = 0
  · subst n
    exact canonicalCoeff_ne_zero_zero triangleCoord
  · exact canonicalCoeff_ne_zero_pos (Nat.pos_of_ne_zero hn) triangleCoord

end Erdos842.SurvivorFibres
