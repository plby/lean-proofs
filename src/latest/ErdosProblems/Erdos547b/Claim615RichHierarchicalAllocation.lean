/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615CoordinateSourceAllocation
import ErdosProblems.Erdos547b.RichClaim61Lemma611

/-!
# Concrete exceptional-edge allocation for Zhao Claim 6.15

This module starts the graph-side specialization of the exact all-vertex
Claim-6.15 hierarchy.  Its edges are literal edges of the rich Claim-6.7
matching.  It chooses the high-density endpoint in the unbalanced case and
proves the two raw endpoints are nonextreme in the second case.  These are
the orientation facts used by Lemma 5.8(2)/(3); no forest copy, containment,
or continuation datum occurs here.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichHierarchicalAllocation

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma615
open Erdos547b.ZhaoLemma612
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoRoundedScales
open Erdos547b.ZhaoSection6EventualParameters

universe u v

/-! ## Two-point orientation arithmetic -/

/-- The endpoint on which a two-entry row is largest. -/
def largerSide (d : Fin 2 → ℝ) : Fin 2 :=
  if d 1 ≤ d 0 then 0 else 1

/-- The other endpoint of a two-entry row. -/
def otherSide (c : Fin 2) : Fin 2 :=
  if c = 0 then 1 else 0

@[simp] theorem otherSide_zero : otherSide 0 = 1 := by
  simp [otherSide]

@[simp] theorem otherSide_one : otherSide 1 = 0 := by
  simp [otherSide]

theorem otherSide_ne (c : Fin 2) : otherSide c ≠ c := by
  fin_cases c <;> simp

theorem largerSide_sub_otherSide_eq_abs (d : Fin 2 → ℝ) :
    d (largerSide d) - d (otherSide (largerSide d)) = |d 0 - d 1| := by
  by_cases h : d 1 ≤ d 0
  · simp [largerSide, otherSide, h, abs_of_nonneg (sub_nonneg.mpr h)]
  · have h' : d 0 < d 1 := lt_of_not_ge h
    simp [largerSide, otherSide, h, abs_of_nonpos (sub_nonpos.mpr h'.le)]

theorem otherSide_largerSide_le (d : Fin 2 → ℝ) :
    d (otherSide (largerSide d)) ≤ d (largerSide d) := by
  by_cases h : d 1 ≤ d 0
  · simpa [largerSide, otherSide, h] using h
  · have h' : d 0 ≤ d 1 := (lt_of_not_ge h).le
    simpa [largerSide, otherSide, h] using h'

theorem density_largerSide_pos_of_abs_ge
    (d : Fin 2 → ℝ) {eta : ℝ}
    (heta : 0 < eta) (h0 : 0 ≤ d 0) (h1 : 0 ≤ d 1)
    (habs : eta ≤ |d 0 - d 1|) :
    0 < d (largerSide d) := by
  have hdiff : eta ≤
      d (largerSide d) - d (otherSide (largerSide d)) := by
    simpa [largerSide_sub_otherSide_eq_abs] using habs
  generalize hside : largerSide d = side
  fin_cases side <;> simp_all [otherSide] <;> nlinarith

/-- A positive two-endpoint total has positive density on its larger side. -/
theorem density_largerSide_pos_of_sum_pos
    (d : Fin 2 → ℝ) (hsum : 0 < d 0 + d 1) :
    0 < d (largerSide d) := by
  by_cases h : d 1 ≤ d 0
  · simp only [largerSide, if_pos h]
    linarith
  · have h' : d 0 < d 1 := lt_of_not_ge h
    simp only [largerSide, if_neg h]
    linarith

/-! ## Literal rich matching rows -/

section Rich

variable {Bv : Type u} {I : Type v}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable {Pcluster : ClusterAssignment Bv I}
variable {Gdegree : SimpleGraph Bv} [DecidableRel Gdegree.Adj]
variable {threshold quota : ℕ} {R0 : SimpleGraph I} [DecidableRel R0.Adj]
variable {miss : ℕ}
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
variable (density : EvenPadding I → EvenPadding I → ℝ)

/-- The raw endpoint-density row read from the rich selected `A` root. -/
def rawDensityA (e : MatchingEdge Q.claim67.M) (side : Fin 2) : ℝ :=
  density (Sum.inl Q.A) (matchingEdgeEndpoint e.1 side)

/-- The raw endpoint-density row read from the rich selected `B` root. -/
def rawDensityB (e : MatchingEdge Q.claim67.M) (side : Fin 2) : ℝ :=
  density (Sum.inl Q.B) (matchingEdgeEndpoint e.1 side)

/-- The canonical high-density raw side of an exceptional unbalanced edge. -/
def unbalancedRootSide (e : MatchingEdge Q.claim67.M) : Fin 2 :=
  largerSide (rawDensityA Q density e)

theorem abs_rawDensityA_sub_eq_abs_oriented
    (e : MatchingEdge Q.claim67.M) (L : Finset (EvenPadding I)) :
    |rawDensityA Q density e 0 - rawDensityA Q density e 1| =
      |density (Sum.inl Q.A) (orientedEndpoint Q.claim67.M L e 0) -
        density (Sum.inl Q.A) (orientedEndpoint Q.claim67.M L e 1)| := by
  by_cases hlarge : e.1.out.1 ∈ L
  · simp [rawDensityA, orientedEndpoint, rawEndpoint, matchingEdgeEndpoint,
      hlarge]
  · simp [rawDensityA, orientedEndpoint, rawEndpoint, matchingEdgeEndpoint,
      hlarge, abs_sub_comm]

/-- The high raw side of an unbalanced edge exceeds its other side by at
least the exceptional threshold. -/
theorem unbalancedRootSide_gap
    (L : Finset (EvenPadding I)) (eta : ℝ) (e : MatchingEdge Q.claim67.M)
    (he : e ∈ unbalancedEdges (allMatchingEdges Q.claim67.M)
      (fun f c ↦ density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M L f c)) eta) :
    eta ≤ rawDensityA Q density e (unbalancedRootSide Q density e) -
      rawDensityA Q density e
        (otherSide (unbalancedRootSide Q density e)) := by
  have habs := (mem_unbalancedEdges.mp he).2
  rw [← abs_rawDensityA_sub_eq_abs_oriented Q density e L] at habs
  simpa [unbalancedRootSide, largerSide_sub_otherSide_eq_abs] using habs

/-- Under the actual nonnegative rich row, the selected unbalanced side is
genuinely adjacent to `A`. -/
theorem unbalancedRootSide_density_pos
    (L : Finset (EvenPadding I)) (eta : ℝ) (heta : 0 < eta)
    (hrow : ∀ x, 0 ≤ density (Sum.inl Q.A) x)
    (e : MatchingEdge Q.claim67.M)
    (he : e ∈ unbalancedEdges (allMatchingEdges Q.claim67.M)
      (fun f c ↦ density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M L f c)) eta) :
    0 < density (Sum.inl Q.A)
      (matchingEdgeEndpoint e.1 (unbalancedRootSide Q density e)) := by
  apply density_largerSide_pos_of_abs_ge (rawDensityA Q density e) heta
    (hrow _) (hrow _)
  rw [abs_rawDensityA_sub_eq_abs_oriented Q density e L]
  exact (mem_unbalancedEdges.mp he).2

/-- The concrete reduced adjacency furnished by the rich `A`-row. -/
theorem unbalancedRootSide_adj_A
    (L : Finset (EvenPadding I)) (eta : ℝ) (heta : 0 < eta)
    (hrow : ∀ x, 0 ≤ density (Sum.inl Q.A) x)
    (hAdj : ∀ x, 0 < density (Sum.inl Q.A) x →
      (padGraph R0).Adj (Sum.inl Q.A) x)
    (e : MatchingEdge Q.claim67.M)
    (he : e ∈ unbalancedEdges (allMatchingEdges Q.claim67.M)
      (fun f c ↦ density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M L f c)) eta) :
    (padGraph R0).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint e.1 (unbalancedRootSide Q density e)) :=
  hAdj _ (unbalancedRootSide_density_pos Q density L eta heta hrow e he)

/-- Nonextremity is invariant under changing from the large-endpoint
orientation to the literal raw endpoints. -/
theorem rawDensityA_mem_interval_of_nonextreme
    (L : Finset (EvenPadding I)) (eta : ℝ) (e : MatchingEdge Q.claim67.M)
    (he : e ∈ nonextremeEdges (allMatchingEdges Q.claim67.M)
      (fun f c ↦ density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M L f c)) eta)
    (side : Fin 2) :
    eta ≤ rawDensityA Q density e side ∧
      rawDensityA Q density e side ≤ 1 - eta := by
  have hbounds := (mem_nonextremeEdges.mp he).2
  fin_cases side <;> by_cases hlarge : e.1.out.1 ∈ L <;>
    simp [rawDensityA, orientedEndpoint, rawEndpoint, matchingEdgeEndpoint,
      hlarge] at hbounds ⊢ <;> tauto

theorem nonextremeRawSide_adj_A
    (L : Finset (EvenPadding I)) (eta : ℝ) (heta : 0 < eta)
    (hAdj : ∀ x, 0 < density (Sum.inl Q.A) x →
      (padGraph R0).Adj (Sum.inl Q.A) x)
    (e : MatchingEdge Q.claim67.M)
    (he : e ∈ nonextremeEdges (allMatchingEdges Q.claim67.M)
      (fun f c ↦ density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M L f c)) eta)
    (side : Fin 2) :
    (padGraph R0).Adj (Sum.inl Q.A) (matchingEdgeEndpoint e.1 side) := by
  apply hAdj
  exact heta.trans_le
    (rawDensityA_mem_interval_of_nonextreme Q density L eta e he side).1

/-! ## Actual exceptional submatching selection -/

/-- The two alternatives in Claim 6.15. -/
inductive ExceptionalCase
  | unbalanced
  | nonextreme
  deriving DecidableEq

/-- Literal exceptional family for one of the two Claim-6.15 cases. -/
def exceptionalFamily
    (L : Finset (EvenPadding I)) (eta : ℝ) :
    ExceptionalCase → Finset (MatchingEdge Q.claim67.M)
  | .unbalanced =>
      unbalancedEdges (allMatchingEdges Q.claim67.M)
        (fun e c ↦ density (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e c)) eta
  | .nonextreme =>
      nonextremeEdges (allMatchingEdges Q.claim67.M)
        (fun e c ↦ density (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e c)) eta

/-- A genuine selected exceptional submatching, with its exact integral
size retained for the later finite packing. -/
structure SelectedExceptionalEdges
    (L : Finset (EvenPadding I)) (eta : ℝ)
    (which : ExceptionalCase) (count : ℕ) where
  selected : Finset (MatchingEdge Q.claim67.M)
  selected_subset : selected ⊆ exceptionalFamily Q density L eta which
  selected_card : selected.card = count

theorem exists_selectedExceptionalEdges
    (L : Finset (EvenPadding I)) (eta : ℝ)
    (which : ExceptionalCase) (count : ℕ)
    (henough : count ≤ #(exceptionalFamily Q density L eta which)) :
    Nonempty (SelectedExceptionalEdges Q density L eta which count) := by
  obtain ⟨selected, hsub, hcard⟩ := Finset.exists_subset_card_eq henough
  exact ⟨⟨selected, hsub, hcard⟩⟩

/-- A real lower bound on an exceptional family selects the exact
upward-rounded number of matching edges used by the integral packing.  This
is the ceiling step suppressed in the paper's asymptotic notation. -/
theorem exists_selectedExceptionalEdges_upperScale
    (L : Finset (EvenPadding I)) (eta : ℝ)
    (which : ExceptionalCase) (k : ℕ)
    (henough : eta * k ≤
      (#(exceptionalFamily Q density L eta which) : ℝ)) :
    Nonempty (SelectedExceptionalEdges Q density L eta which
      (upperScale (eta * k))) := by
  apply exists_selectedExceptionalEdges Q density L eta which
  change ⌈eta * k⌉₊ ≤ #(exceptionalFamily Q density L eta which)
  exact Nat.ceil_le.mpr henough

/-- Select an exceptional submatching while avoiding a previously reserved
edge family.  The coarse but source-convenient room hypothesis charges every
reserved edge, including those outside the exceptional family. -/
theorem exists_selectedExceptionalEdges_avoiding
    (L : Finset (EvenPadding I)) (eta : ℝ)
    (which : ExceptionalCase) (count : ℕ)
    (forbidden : Finset (MatchingEdge Q.claim67.M))
    (hroom : count + #forbidden ≤
      #(exceptionalFamily Q density L eta which)) :
    Nonempty {S : SelectedExceptionalEdges Q density L eta which count //
      Disjoint S.selected forbidden} := by
  let family := exceptionalFamily Q density L eta which
  change count + #forbidden ≤ #family at hroom
  have hinter : #(family ∩ forbidden) ≤ #forbidden :=
    Finset.card_le_card (Finset.inter_subset_right)
  have hsplit := Finset.card_sdiff_add_card_inter family forbidden
  have havailable : count ≤ #(family \ forbidden) := by omega
  obtain ⟨selected, hselected, hcard⟩ :=
    Finset.exists_subset_card_eq havailable
  have hfamily : selected ⊆ family :=
    hselected.trans (Finset.sdiff_subset : family \ forbidden ⊆ family)
  have hdisjoint : Disjoint selected forbidden := by
    rw [Finset.disjoint_left]
    intro e heSelected heForbidden
    exact (Finset.mem_sdiff.mp (hselected heSelected)).2 heForbidden
  exact ⟨⟨{
    selected := selected
    selected_subset := by simpa only [family] using hfamily
    selected_card := hcard
  }, hdisjoint⟩⟩

/-- Zhao's literal `M₀` selection after reserving `M_b`: if the exceptional
family has real size at least `x` and the already-reserved family has size at
most `x / 2`, then `⌈x / 2⌉` exceptional edges can be selected disjointly.
The strict unit ceiling error is absorbed by integrality of the family
cardinality. -/
theorem exists_halfSelectedExceptionalEdges_avoiding
    (L : Finset (EvenPadding I)) (eta : ℝ)
    (which : ExceptionalCase) (x : ℝ)
    (forbidden : Finset (MatchingEdge Q.claim67.M))
    (hx : 0 ≤ x)
    (hfamily : x ≤
      (#(exceptionalFamily Q density L eta which) : ℝ))
    (hforbidden : (#forbidden : ℝ) ≤ x / 2) :
    Nonempty {S : SelectedExceptionalEdges Q density L eta which
        (upperScale (x / 2)) //
      Disjoint S.selected forbidden} := by
  apply exists_selectedExceptionalEdges_avoiding Q density L eta which
  have hceil : (upperScale (x / 2) : ℝ) < x / 2 + 1 :=
    upperScale_cast_lt_add_one (div_nonneg hx (by norm_num))
  have hroomReal :
      ((upperScale (x / 2) + #forbidden : ℕ) : ℝ) <
        (#(exceptionalFamily Q density L eta which) : ℝ) + 1 := by
    push_cast
    linarith
  have hroomNat : upperScale (x / 2) + #forbidden <
      #(exceptionalFamily Q density L eta which) + 1 := by
    exact_mod_cast hroomReal
  omega

/-- Eventual-parameter specialization of the preceding selector.  The
reserved family may have the full Claim-6.17 size `q`; the explicit Section-6
hierarchy proves that this still occupies at most half of the Claim-6.15
exceptional threshold. -/
theorem exists_eventualHalfSelectedExceptionalEdges_avoiding
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {reducedK : ℕ} (hreducedK : section6K₀ β ≤ reducedK)
    (L : Finset (EvenPadding I)) (which : ExceptionalCase)
    (forbidden : Finset (MatchingEdge Q.claim67.M))
    (hfamily : (eta β : ℝ) * reducedK ≤
      (#(exceptionalFamily Q density L (eta β : ℝ) which) : ℝ))
    (hforbidden : #forbidden ≤ claim617Q β reducedK) :
    Nonempty {S : SelectedExceptionalEdges Q density L (eta β : ℝ) which
        (upperScale (((eta β : ℝ) * reducedK) / 2)) //
      Disjoint S.selected forbidden} := by
  apply exists_halfSelectedExceptionalEdges_avoiding Q density L
    (eta β : ℝ) which ((eta β : ℝ) * reducedK) forbidden
  · positivity [eta_pos hβ0]
  · exact hfamily
  · calc
      (#forbidden : ℝ) ≤ (claim617Q β reducedK : ℝ) := by
        exact_mod_cast hforbidden
      _ ≤ (eta β : ℝ) * reducedK / 2 :=
        claim617Q_cast_le_eta_half hβ0 hβ1 hreducedK

/-! ## Preliminary reserved matching, before Lemma 6.11 -/

/-- The independent `M_b` chosen by Lemma 6.12 before Claim 6.15 is used.
It is deliberately not tied to a later `MatchingDecomposition`: using that
decomposition here would be circular, since its construction already needs
the exceptional-family bounds obtained from Claim 6.15. -/
structure PreliminaryReservedEdges
    (L : Finset (EvenPadding I)) (N targetB cap : ℝ)
    (cardBound : ℕ) where
  selected : Finset (MatchingEdge Q.claim67.M)
  selected_subset : selected ⊆ allMatchingEdges Q.claim67.M
  degree_lower : targetB ≤ sourceDegree Q.claim67.M L density N
    (Sum.inl Q.B) selected
  degree_upper : sourceDegree Q.claim67.M L density N
    (Sum.inl Q.B) selected < targetB + cap
  card_le : selected.card ≤ cardBound
  singleton_pos : ∀ e ∈ selected,
    0 < N * (density (Sum.inl Q.B)
        (orientedEndpoint Q.claim67.M L e 0) +
      density (Sum.inl Q.B)
        (orientedEndpoint Q.claim67.M L e 1))

/-- Source-faithful Lemma-6.12 construction of the preliminary reserved
matching.  Every selected edge retains a positive `B` contribution, which
later supplies its literal `B`-facing root endpoint. -/
theorem exists_preliminaryReservedEdges
    (L : Finset (EvenPadding I)) (N targetB cap : ℝ)
    (cardBound : ℕ)
    (hnonneg : ∀ e ∈ allMatchingEdges Q.claim67.M,
      0 ≤ N * (density (Sum.inl Q.B)
          (orientedEndpoint Q.claim67.M L e 0) +
        density (Sum.inl Q.B)
          (orientedEndpoint Q.claim67.M L e 1)))
    (htarget : 0 ≤ targetB) (hcap : 0 < cap)
    (hedgecap : ∀ e ∈ allMatchingEdges Q.claim67.M,
      N * (density (Sum.inl Q.B)
          (orientedEndpoint Q.claim67.M L e 0) +
        density (Sum.inl Q.B)
          (orientedEndpoint Q.claim67.M L e 1)) ≤ cap)
    (htotal : targetB ≤ sourceDegree Q.claim67.M L density N
      (Sum.inl Q.B) (allMatchingEdges Q.claim67.M))
    (htotalpos : 0 < sourceDegree Q.claim67.M L density N
      (Sum.inl Q.B) (allMatchingEdges Q.claim67.M))
    (hcard : ((allMatchingEdges Q.claim67.M).card : ℝ) *
        (targetB + cap) ≤
      (cardBound : ℝ) * sourceDegree Q.claim67.M L density N
        (Sum.inl Q.B) (allMatchingEdges Q.claim67.M)) :
    Nonempty (PreliminaryReservedEdges Q density L N targetB cap
      cardBound) := by
  obtain ⟨Mb, hMb, hlower, hupper, hMbCard, hpositive⟩ :=
    exists_small_submatching_positive
      (allMatchingEdges Q.claim67.M)
      (fun e ↦ N * (density (Sum.inl Q.B)
          (orientedEndpoint Q.claim67.M L e 0) +
        density (Sum.inl Q.B)
          (orientedEndpoint Q.claim67.M L e 1)))
      targetB cap (cardBound : ℝ) hnonneg htarget hcap hedgecap
      (by simpa [sourceDegree, clusterMatchingDegree] using htotal)
      (by simpa [sourceDegree, clusterMatchingDegree] using htotalpos)
      (by simpa [sourceDegree, clusterMatchingDegree] using hcard)
  exact ⟨{
    selected := Mb
    selected_subset := hMb
    degree_lower := by
      simpa [sourceDegree, clusterMatchingDegree] using hlower
    degree_upper := by
      simpa [sourceDegree, clusterMatchingDegree] using hupper
    card_le := by exact_mod_cast hMbCard
    singleton_pos := hpositive
  }⟩

namespace PreliminaryReservedEdges

variable {L : Finset (EvenPadding I)} {N targetB cap : ℝ}
variable {cardBound : ℕ}

/-- A positive reserved target forces the preliminary edge family to be
nonempty; this supplies the finite-bin instance used by source packing. -/
theorem selected_nonempty
    (Mb : PreliminaryReservedEdges Q density L N targetB cap cardBound)
    (htargetB : 0 < targetB) : Mb.selected.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hlower := Mb.degree_lower
  rw [hempty] at hlower
  simp [sourceDegree, clusterMatchingDegree] at hlower
  linarith

/-- At the eventual Section-6 scales, a preliminary `M_b` can be fed
directly to the exact disjoint exceptional selector. -/
theorem exists_eventualHalfSelectedExceptionalEdges_avoiding_selected
    {β : ℚ} (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 4)
    {reducedK : ℕ} (hreducedK : section6K₀ β ≤ reducedK)
    {N targetB cap : ℝ}
    (Mb : PreliminaryReservedEdges Q density L N targetB cap
      (claim617Q β reducedK))
    (which : ExceptionalCase)
    (hfamily : (eta β : ℝ) * reducedK ≤
      (#(exceptionalFamily Q density L (eta β : ℝ) which) : ℝ)) :
    Nonempty {S : SelectedExceptionalEdges Q density L (eta β : ℝ) which
        (upperScale (((eta β : ℝ) * reducedK) / 2)) //
      Disjoint S.selected Mb.selected} :=
  exists_eventualHalfSelectedExceptionalEdges_avoiding Q density hβ0 hβ1
    hreducedK L which Mb.selected hfamily Mb.card_le

/-- Literal raw side on which one preliminary reserved edge has largest
`B`-density. -/
def rootSide
    (Mb : PreliminaryReservedEdges Q density L N targetB cap cardBound)
    (e : {e // e ∈ Mb.selected}) : Fin 2 :=
  largerSide (rawDensityB Q density e.1)

/-- Positivity of the selected singleton contribution yields positivity of
the chosen raw endpoint, independently of the large-endpoint orientation. -/
theorem rootSide_density_pos
    (Mb : PreliminaryReservedEdges Q density L N targetB cap cardBound)
    (hN : 0 < N) (e : {e // e ∈ Mb.selected}) :
    0 < density (Sum.inl Q.B)
      (matchingEdgeEndpoint e.1.1 (rootSide Q density Mb e)) := by
  have hproduct := Mb.singleton_pos e.1 e.2
  have hproductRaw : 0 < N * (rawDensityB Q density e.1 0 +
      rawDensityB Q density e.1 1) := by
    by_cases hlarge : e.1.1.out.1 ∈ L
    · simpa [rawDensityB, orientedEndpoint, rawEndpoint,
        matchingEdgeEndpoint, hlarge] using hproduct
    · simpa [rawDensityB, orientedEndpoint, rawEndpoint,
        matchingEdgeEndpoint, hlarge, add_comm] using hproduct
  have hsum : 0 < rawDensityB Q density e.1 0 +
      rawDensityB Q density e.1 1 := by
    nlinarith
  exact density_largerSide_pos_of_sum_pos (rawDensityB Q density e.1) hsum

/-- The preliminary reserved endpoint is literally adjacent to the selected
`B` cluster in the padded reduced graph. -/
theorem rootSide_adj_B
    (Mb : PreliminaryReservedEdges Q density L N targetB cap cardBound)
    (hN : 0 < N)
    (hAdj : ∀ x, 0 < density (Sum.inl Q.B) x →
      (padGraph R0).Adj (Sum.inl Q.B) x)
    (e : {e // e ∈ Mb.selected}) :
    (padGraph R0).Adj (Sum.inl Q.B)
      (matchingEdgeEndpoint e.1.1 (rootSide Q density Mb e)) :=
  hAdj _ (rootSide_density_pos Q density Mb hN e)

end PreliminaryReservedEdges

/-! ## Positive remaining `A`-edges -/

/-- The source-faithful `M₁`: after the exceptional and reserved edges have
been removed, discard precisely the edges with zero `A` contribution. -/
def positiveRemainingEdgesA
    (L : Finset (EvenPadding I)) (N : ℝ)
    (forbidden : Finset (MatchingEdge Q.claim67.M)) :
    Finset (MatchingEdge Q.claim67.M) :=
  (allMatchingEdges Q.claim67.M \ forbidden).filter fun e ↦
    0 < N * (density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M L e 0) +
      density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M L e 1))

theorem positiveRemainingEdgesA_subset
    (L : Finset (EvenPadding I)) (N : ℝ)
    (forbidden : Finset (MatchingEdge Q.claim67.M)) :
    positiveRemainingEdgesA Q density L N forbidden ⊆
      allMatchingEdges Q.claim67.M \ forbidden :=
  Finset.filter_subset _ _

/-- Removing zero-contribution edges does not change the total remaining
`A` source degree. -/
theorem sourceDegree_positiveRemainingEdgesA_eq
    (L : Finset (EvenPadding I)) (N : ℝ)
    (forbidden : Finset (MatchingEdge Q.claim67.M))
    (hnonneg : ∀ e ∈ allMatchingEdges Q.claim67.M,
      0 ≤ N * (density (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 0) +
        density (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 1))) :
    sourceDegree Q.claim67.M L density N (Sum.inl Q.A)
        (positiveRemainingEdgesA Q density L N forbidden) =
      sourceDegree Q.claim67.M L density N (Sum.inl Q.A)
        (allMatchingEdges Q.claim67.M \ forbidden) := by
  simp only [sourceDegree, clusterMatchingDegree]
  apply Finset.sum_subset (positiveRemainingEdgesA_subset Q density L N forbidden)
  intro e heRemaining heNotPositive
  have heAll : e ∈ allMatchingEdges Q.claim67.M :=
    (Finset.mem_sdiff.mp heRemaining).1
  have hnot : ¬ 0 < N * (density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M L e 0) +
      density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M L e 1)) := by
    intro hpos
    exact heNotPositive (Finset.mem_filter.mpr ⟨heRemaining, hpos⟩)
  exact le_antisymm (le_of_not_gt hnot) (hnonneg e heAll)

/-- A positive remaining total produces an actual nonempty `M₁`. -/
theorem positiveRemainingEdgesA_nonempty
    (L : Finset (EvenPadding I)) (N : ℝ)
    (forbidden : Finset (MatchingEdge Q.claim67.M))
    (hnonneg : ∀ e ∈ allMatchingEdges Q.claim67.M,
      0 ≤ N * (density (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 0) +
        density (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 1)))
    (hpos : 0 < sourceDegree Q.claim67.M L density N (Sum.inl Q.A)
      (allMatchingEdges Q.claim67.M \ forbidden)) :
    (positiveRemainingEdgesA Q density L N forbidden).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have heq := sourceDegree_positiveRemainingEdgesA_eq Q density L N forbidden
    hnonneg
  rw [hempty] at heq
  simp [sourceDegree, clusterMatchingDegree] at heq
  change 0 < ∑ e ∈ allMatchingEdges Q.claim67.M \ forbidden,
      N * (density (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 0) +
        density (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M L e 1)) at hpos
  rw [← heq] at hpos
  exact (lt_irrefl 0 hpos)

namespace PositiveRemainingEdgesA

variable {L : Finset (EvenPadding I)} {N : ℝ}
variable {forbidden : Finset (MatchingEdge Q.claim67.M)}

abbrev IndexedEdge :=
  {e : MatchingEdge Q.claim67.M //
    e ∈ positiveRemainingEdgesA Q density L N forbidden}

def edge (e : IndexedEdge (Q := Q) (density := density)
    (L := L) (N := N) (forbidden := forbidden)) :
    MatchingEdge Q.claim67.M := e.1

theorem edge_injective :
    Function.Injective (fun e : IndexedEdge (Q := Q) (density := density)
      (L := L) (N := N) (forbidden := forbidden) ↦ edge Q density e) := by
  intro e f hef
  exact Subtype.ext hef

theorem edge_not_mem_forbidden
    (e : IndexedEdge (Q := Q) (density := density)
      (L := L) (N := N) (forbidden := forbidden)) :
    edge Q density e ∉ forbidden :=
  (Finset.mem_sdiff.mp
    (positiveRemainingEdgesA_subset Q density L N forbidden e.2)).2

def rootSide (e : IndexedEdge (Q := Q) (density := density)
    (L := L) (N := N) (forbidden := forbidden)) : Fin 2 :=
  largerSide (rawDensityA Q density e.1)

theorem rootSide_density_pos
    (hN : 0 < N)
    (e : IndexedEdge (Q := Q) (density := density)
      (L := L) (N := N) (forbidden := forbidden)) :
    0 < density (Sum.inl Q.A)
      (matchingEdgeEndpoint e.1.1 (rootSide Q density e)) := by
  have hproduct := (Finset.mem_filter.mp e.2).2
  have hproductRaw : 0 < N * (rawDensityA Q density e.1 0 +
      rawDensityA Q density e.1 1) := by
    by_cases hlarge : e.1.1.out.1 ∈ L
    · simpa [rawDensityA, orientedEndpoint, rawEndpoint,
        matchingEdgeEndpoint, hlarge] using hproduct
    · simpa [rawDensityA, orientedEndpoint, rawEndpoint,
        matchingEdgeEndpoint, hlarge, add_comm] using hproduct
  have hsum : 0 < rawDensityA Q density e.1 0 +
      rawDensityA Q density e.1 1 := by
    nlinarith
  exact density_largerSide_pos_of_sum_pos (rawDensityA Q density e.1) hsum

theorem rootSide_adj_A
    (hN : 0 < N)
    (hAdj : ∀ x, 0 < density (Sum.inl Q.A) x →
      (padGraph R0).Adj (Sum.inl Q.A) x)
    (e : IndexedEdge (Q := Q) (density := density)
      (L := L) (N := N) (forbidden := forbidden)) :
    (padGraph R0).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint e.1.1 (rootSide Q density e)) :=
  hAdj _ (rootSide_density_pos Q density hN e)

end PositiveRemainingEdgesA

namespace SelectedExceptionalEdges

variable {L : Finset (EvenPadding I)} {eta : ℝ}
variable {which : ExceptionalCase} {count : ℕ}

/-- Canonical literal original matching edge represented by a selected
finite index. -/
abbrev IndexedEdge
    (S : SelectedExceptionalEdges Q density L eta which count) :=
  Fin S.selected.card

def edge (S : SelectedExceptionalEdges Q density L eta which count)
    (e : S.IndexedEdge) : MatchingEdge Q.claim67.M :=
  finsetValue S.selected e

theorem edge_mem (S : SelectedExceptionalEdges Q density L eta which count)
    (e : S.IndexedEdge) : edge Q density S e ∈ S.selected :=
  finsetValue_mem S.selected e

theorem edge_injective
    (S : SelectedExceptionalEdges Q density L eta which count) :
    Function.Injective (edge Q density S) :=
  finsetValue_injective S.selected

theorem edge_mem_family
    (S : SelectedExceptionalEdges Q density L eta which count)
    (e : S.IndexedEdge) :
    edge Q density S e ∈ exceptionalFamily Q density L eta which :=
  S.selected_subset (edge_mem Q density S e)

/-- Matching-side orientation used for the selected `F₀` forest. -/
def rootSide (S : SelectedExceptionalEdges Q density L eta which count)
    (e : S.IndexedEdge) : Fin 2 :=
  match which with
  | .unbalanced => unbalancedRootSide Q density (edge Q density S e)
  | .nonextreme => 0

theorem rootSide_adj_A
    (S : SelectedExceptionalEdges Q density L eta which count)
    (heta : 0 < eta)
    (hrow : ∀ x, 0 ≤ density (Sum.inl Q.A) x)
    (hAdj : ∀ x, 0 < density (Sum.inl Q.A) x →
      (padGraph R0).Adj (Sum.inl Q.A) x)
    (e : S.IndexedEdge) :
    (padGraph R0).Adj (Sum.inl Q.A)
      (matchingEdgeEndpoint (edge Q density S e).1
        (rootSide Q density S e)) := by
  cases which with
  | unbalanced =>
      exact unbalancedRootSide_adj_A Q density L eta heta hrow hAdj
        (edge Q density S e) (edge_mem_family Q density S e)
  | nonextreme =>
      exact nonextremeRawSide_adj_A Q density L eta heta hAdj
        (edge Q density S e) (edge_mem_family Q density S e) 0

theorem rootSide_gap_of_unbalanced
    (S : SelectedExceptionalEdges Q density L eta .unbalanced count)
    (e : S.IndexedEdge) :
    eta ≤ rawDensityA Q density (edge Q density S e)
        (rootSide Q density S e) -
      rawDensityA Q density (edge Q density S e)
        (otherSide (rootSide Q density S e)) := by
  exact unbalancedRootSide_gap Q density L eta (edge Q density S e)
    (edge_mem_family Q density S e)

theorem rawDensity_mem_interval_of_nonextreme
    (S : SelectedExceptionalEdges Q density L eta .nonextreme count)
    (e : S.IndexedEdge) (side : Fin 2) :
    eta ≤ rawDensityA Q density (edge Q density S e) side ∧
      rawDensityA Q density (edge Q density S e) side ≤ 1 - eta := by
  exact rawDensityA_mem_interval_of_nonextreme Q density L eta
    (edge Q density S e) (edge_mem_family Q density S e) side

end SelectedExceptionalEdges

end Rich

end Erdos547b.ZhaoClaim615RichHierarchicalAllocation

#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.unbalancedRootSide_gap
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.otherSide_largerSide_le
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.unbalancedRootSide_adj_A
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.nonextremeRawSide_adj_A
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.exists_selectedExceptionalEdges_upperScale
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.exists_selectedExceptionalEdges_avoiding
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.exists_halfSelectedExceptionalEdges_avoiding
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.exists_eventualHalfSelectedExceptionalEdges_avoiding
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.exists_preliminaryReservedEdges
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.PreliminaryReservedEdges.selected_nonempty
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.PreliminaryReservedEdges.exists_eventualHalfSelectedExceptionalEdges_avoiding_selected
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.PreliminaryReservedEdges.rootSide_adj_B
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.sourceDegree_positiveRemainingEdgesA_eq
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.positiveRemainingEdgesA_nonempty
#print axioms Erdos547b.ZhaoClaim615RichHierarchicalAllocation.PositiveRemainingEdgesA.rootSide_adj_A
