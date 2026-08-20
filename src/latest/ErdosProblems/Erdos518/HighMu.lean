/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.CaseArithmetic
import ErdosProblems.Erdos518.ExtensionObstruction
import ErdosProblems.Erdos518.Selection
import ErdosProblems.Erdos518.TripleFree

/-!
# The high-neighbourhood branch

This file contains the finite hypergraph and arithmetic part of the high-`mu` branch in the
Chen--Chen proof of Erdős Problem 518.  The graph-specific inputs are kept as hypotheses:

* an odd outside part has no blue triple;
* in the even case two disjoint blue triples are impossible;
* the clique-extension obstruction implies the triple-free estimate; and
* no blue triple contains every high vertex.

Those statements are proved by the path-construction modules.  Starting from precisely these
inputs, `highMu_structural_reduction` carries out all remaining parity, matching, deletion, and
cardinality deductions and produces the parameters `lambda = 2` or `lambda = 3` used by the
final greedy extension.  The last section packages that greedy distinct-representative step.
-/

namespace Erdos518

universe u v

variable {V : Type u}

namespace Configuration

variable [Fintype V] [DecidableEq V] (C : Configuration V)

/-- Adapter from the fully proved configuration-level triple-free estimate to the numerical
shape consumed by `highMu_structural_reduction`. -/
theorem tripleFree_estimate_highMu_form
    {Y' S : Finset V} {s e : V} {lo hi : Nat}
    (hY' : Y' ⊆ C.Y1) (hs : s ∈ Y') (hfree : C.TripleFreeOn Y')
    (hwit : C.HasUpperBoundaryWitness Y' s hi)
    (hM : (C.lowerBlueSet Y' s lo).card <= 1)
    (hSclique : C.G.IsClique (S : Set V)) (heS : e ∈ S) (hSX : S ⊆ C.X)
    (hScard : S.card = C.blueDegreeToX s + 1)
    (hbridge : ∀ y ∈ C.Y, C.G.Adj e y)
    (hhigh : C.IsHigh s)
    (hmu : C.blueDegreeToX s + 2 <= C.r)
    (hFempty : ¬ (C.middleOutsideSet Y' s lo).Nonempty ->
      C.r - C.blueDegreeToX s <= (C.tripleFreeF Y' S s lo hi).card)
    (hFnonempty : (C.middleOutsideSet Y' s lo).Nonempty ->
      C.blueDegreeToX s - 1 <= (C.tripleFreeF Y' S s lo hi).card) :
    C.a0 + max (Y'.card - 2) 0 < C.r - C.blueDegreeToX s := by
  simpa only [max_eq_left (Nat.zero_le (Y'.card - 2))] using
    C.tripleFree_estimate hY' hs hfree hwit hM hSclique heS hSX hScard hbridge
      hhigh hmu hFempty hFnonempty

/-- The exact list data which would trigger Chen--Chen's clique-extension obstruction. -/
def HasCliqueExtensionData (y : V) : Prop :=
  ∃ ys xs : List V,
    ys.length = C.extensionCount y ∧ xs.length = C.extensionCount y ∧
      ys.Nodup ∧ xs.Nodup ∧
      (∀ z ∈ ys, z ∈ C.Y) ∧
      (∀ x ∈ xs, x ∈ C.extensionReservoir y) ∧
      List.Forall₂ C.G.Adj ys xs ∧
      List.Forall₂ C.G.Adj xs.dropLast ys.tail

/-- Lemma 3.4 rules out the exact extension data above. -/
lemma not_hasCliqueExtensionData {y : V} (hy : y ∈ C.Y1)
    (hdeg : C.blueDegreeToX y < C.r) : ¬ C.HasCliqueExtensionData y := by
  rintro ⟨ys, xs, hysLen, hxsLen, hysN, hxsN, hysY, hxsW, hyx, hxy⟩
  exact C.clique_extension_obstruction_list hy hdeg hysLen hxsLen hysN hxsN
    hysY hxsW hyx hxy

end Configuration

/-! ## The auxiliary three-uniform hypergraph -/

/-- The high vertices for a degree function `degree` and remainder `r`. -/
def highVertices [DecidableEq V] (Y1 : Finset V) (degree : V -> Nat) (r : Nat) : Finset V :=
  Y1.filter fun y => r + 1 <= 2 * degree y

@[simp] lemma mem_highVertices [DecidableEq V] {Y1 : Finset V} {degree : V -> Nat}
    {r : Nat} {y : V} :
    y ∈ highVertices Y1 degree r ↔ y ∈ Y1 ∧ r + 1 <= 2 * degree y := by
  simp [highVertices]

/-- A finite family all of whose members are triples contained in `Y1`. -/
def IsThreeUniformOn (H : Finset (Finset V)) (Y1 : Finset V) : Prop :=
  ∀ T ∈ H, T ⊆ Y1 ∧ T.card = 3

/-- The induced hypergraph on `S` has no edge. -/
def IsTripleFreeIn (H : Finset (Finset V)) (S : Finset V) : Prop :=
  ∀ T ∈ H, ¬ T ⊆ S

/-- The hypergraph has matching number at most one.  Since every member is a triple, this is
equivalent to saying that every two edges meet. -/
def MatchingNumberAtMostOne (H : Finset (Finset V)) : Prop :=
  ∀ T ∈ H, ∀ U ∈ H, ¬ Disjoint T U

lemma tripleFreeIn_of_hypergraph_empty {H : Finset (Finset V)} (hH : H = ∅)
    (S : Finset V) : IsTripleFreeIn H S := by
  subst H
  simp [IsTripleFreeIn]

/-- Deleting one edge leaves a triple-free induced hypergraph when the matching number is at
most one. -/
lemma tripleFreeIn_sdiff_edge [DecidableEq V] {H : Finset (Finset V)} {Y1 T : Finset V}
    (hmatch : MatchingNumberAtMostOne H) (hT : T ∈ H) :
    IsTripleFreeIn H (Y1 \ T) := by
  intro U hU hsub
  apply hmatch T hT U hU
  rw [Finset.disjoint_left]
  intro x hxT hxU
  have hx : x ∈ Y1 \ T := hsub hxU
  exact (Finset.mem_sdiff.mp hx).2 hxT

/-- If no edge contains all high vertices, the complement of each edge contains a high
vertex. -/
lemma exists_high_mem_sdiff_edge [DecidableEq V] {H : Finset (Finset V)}
    {Y1 high T : Finset V} (hT : T ∈ H) (hHigh : high ⊆ Y1)
    (hno : ∀ U ∈ H, ¬ high ⊆ U) :
    ∃ s ∈ Y1 \ T, s ∈ high := by
  have hnsub : ¬ high ⊆ T := hno T hT
  obtain ⟨s, hsHigh, hsT⟩ := Finset.not_subset.mp hnsub
  exact ⟨s, Finset.mem_sdiff.mpr ⟨hHigh hsHigh, hsT⟩, hsHigh⟩

/-- Choose a maximum-degree member of a nonempty finite set. -/
lemma exists_max_degree {S : Finset V} {degree : V -> Nat} (hS : S.Nonempty) :
    ∃ s ∈ S, ∀ y ∈ S, degree y <= degree s :=
  Finset.exists_max_image S degree hS

/-- Claim 3 in interface form.  The path-theoretic proof supplies `hExtensionObstruction` by
constructing the forbidden clique extension whenever an edge contains all high vertices. -/
lemma no_hyperedge_contains_all_high_of_extension_obstruction [DecidableEq V]
    {H : Finset (Finset V)} {Y1 : Finset V} {degree : V -> Nat} {r : Nat}
    (hExtensionObstruction :
      ∀ T ∈ H, highVertices Y1 degree r ⊆ T -> False) :
    ∀ T ∈ H, ¬ highVertices Y1 degree r ⊆ T := by
  intro T hT hsub
  exact hExtensionObstruction T hT hsub

namespace Configuration

variable [Fintype V] [DecidableEq V] (C : Configuration V)

/-- Claim 3 with the actual Lemma 3.4 obstruction wired in.  Its sole constructive input says
that, from an edge containing all high vertices, the preceding cardinal/greedy argument builds
the two aligned lists required by `clique_extension_obstruction_list`. -/
theorem no_hyperedge_contains_all_high_of_extension_data
    {H : Finset (Finset V)}
    (hSelection : ∀ T ∈ H,
      highVertices C.Y1 C.blueDegreeToX C.r ⊆ T ->
        ∃ y ∈ C.Y1, C.blueDegreeToX y < C.r ∧ C.HasCliqueExtensionData y) :
    ∀ T ∈ H, ¬ highVertices C.Y1 C.blueDegreeToX C.r ⊆ T := by
  classical
  apply no_hyperedge_contains_all_high_of_extension_obstruction
  intro T hT hsub
  obtain ⟨y, hy, hdeg, hdata⟩ := hSelection T hT hsub
  exact C.not_hasCliqueExtensionData hy hdeg hdata

end Configuration

/-! ## Parity and matching reduction -/

/-- The exact data produced at the end of the hypergraph part of the high-`mu` branch. -/
def HighMuReductionData [DecidableEq V] (H : Finset (Finset V))
    (Y1 : Finset V) (degree : V -> Nat) (r a0 a1 c w : Nat) : Prop :=
  ∃ lam : Nat, (lam = 2 ∨ lam = 3) ∧ a1 = 2 * lam ∧ a0 + lam = c ∧
    w = c + lam ∧ ∃ edge ∈ H, ∃ vertex ∈ Y1 \ edge,
      r + 1 <= 2 * degree vertex ∧ IsTripleFreeIn H (Y1 \ edge) ∧
        ∀ y ∈ Y1 \ edge, degree y <= degree vertex

/-- The finite hypergraph core of the high-neighbourhood argument.

`hOddNoEdge` and `hEvenMatching` are the two consequences of the initial blue cover;
`hEstimate` is the triple-free estimate; and `hNoEdgeContainsHigh` is the clique-extension
consequence.  Every other conclusion, including the small list of possible values of `lambda`,
is derived here. -/
theorem highMu_structural_reduction [DecidableEq V]
    {H : Finset (Finset V)} {Y1 : Finset V} {degree : V -> Nat}
    {r a0 a1 c w mu : Nat}
    (hY1card : Y1.card = a1)
    (hUniform : IsThreeUniformOn H Y1)
    (hMax : ∃ z ∈ Y1, degree z = mu)
    (hr : r <= 2 * c)
    (hHighMu : r + 1 <= 2 * mu)
    (hKey : c = a0 + ceilHalf a1)
    (hW : w = a0 + a1)
    (hOddNoEdge : Odd a1 -> H = ∅)
    (hEvenMatching : Even a1 -> MatchingNumberAtMostOne H)
    (hEstimate : ∀ S, S ⊆ Y1 -> IsTripleFreeIn H S ->
      ∀ s ∈ S, r + 1 <= 2 * degree s ->
        a0 + max (S.card - 2) 0 < r - degree s)
    (hNoEdgeContainsHigh :
      ∀ T ∈ H, ¬ highVertices Y1 degree r ⊆ T) :
    HighMuReductionData H Y1 degree r a0 a1 c w := by
  obtain ⟨z, hzY1, hzdeg⟩ := hMax
  have hzHigh : r + 1 <= 2 * degree z := by simpa [hzdeg] using hHighMu
  have hHighNonempty : (highVertices Y1 degree r).Nonempty := by
    exact ⟨z, mem_highVertices.mpr ⟨hzY1, hzHigh⟩⟩
  have hHighSubset : highVertices Y1 degree r ⊆ Y1 := by
    intro y hy
    exact (mem_highVertices.mp hy).1
  have ha1pos : 1 <= a1 := by
    rw [← hY1card]
    exact Finset.one_le_card.mpr ⟨z, hzY1⟩

  have hEven : Even a1 := by
    rcases Nat.even_or_odd a1 with heven | hodd
    · exact heven
    · exfalso
      have hHem : H = ∅ := hOddNoEdge hodd
      have hfree : IsTripleFreeIn H Y1 := tripleFreeIn_of_hypergraph_empty hHem Y1
      have hest := hEstimate Y1 (by rfl) hfree z hzY1 hzHigh
      have hdeficit : r - degree z <= c - 1 := highMu_deficit_le_pred hr hzHigh
      have hceil := two_mul_ceilHalf_of_odd hodd
      have hlower : c - 1 <= a0 + max (Y1.card - 2) 0 := by
        rw [hY1card]
        simp only [max_eq_left (Nat.zero_le (a1 - 2))]
        omega
      omega

  have hEdgeNonempty : H.Nonempty := by
    by_contra hne
    have hHem : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hfree : IsTripleFreeIn H Y1 := tripleFreeIn_of_hypergraph_empty hHem Y1
    have hest := hEstimate Y1 (by rfl) hfree z hzY1 hzHigh
    have hdeficit : r - degree z <= c - 1 := highMu_deficit_le_pred hr hzHigh
    have hceil := two_mul_ceilHalf_of_even hEven
    have hlower : c - 1 <= a0 + max (Y1.card - 2) 0 := by
      rw [hY1card]
      simp only [max_eq_left (Nat.zero_le (a1 - 2))]
      omega
    omega

  obtain ⟨T, hTH⟩ := hEdgeNonempty
  have hmatch : MatchingNumberAtMostOne H := hEvenMatching hEven
  have hfreeComp : IsTripleFreeIn H (Y1 \ T) :=
    tripleFreeIn_sdiff_edge hmatch hTH
  obtain ⟨s0, hs0Comp, hs0HighMem⟩ :=
    exists_high_mem_sdiff_edge hTH hHighSubset hNoEdgeContainsHigh
  have hCompNonempty : (Y1 \ T).Nonempty := ⟨s0, hs0Comp⟩
  obtain ⟨s, hsComp, hsMax⟩ := exists_max_degree hCompNonempty
  have hs0le : degree s0 <= degree s := hsMax s0 hs0Comp
  have hs0High : r + 1 <= 2 * degree s0 := (mem_highVertices.mp hs0HighMem).2
  have hsHigh : r + 1 <= 2 * degree s := by omega

  have hTsub : T ⊆ Y1 := (hUniform T hTH).1
  have hTcard : T.card = 3 := (hUniform T hTH).2
  have hCompCard : (Y1 \ T).card = a1 - 3 := by
    rw [Finset.card_sdiff_of_subset hTsub, hY1card, hTcard]

  have ha1lt : a1 < 8 := by
    by_contra hnot
    have ha1ge : 8 <= a1 := by omega
    obtain ⟨lam, hlam⟩ := hEven
    have ha1eq : a1 = 2 * lam := by omega
    have hlam4 : 4 <= lam := by omega
    have hceilEq : ceilHalf a1 = lam := by
      rw [ceilHalf, ha1eq]
      omega
    have ha0lam : a0 + lam = c := by rw [hKey, hceilEq]
    have hlower0 : c - 1 <= a0 + ((2 * lam - 3) - 2) :=
      large_even_triple_free_lower hlam4 ha0lam
    have hlower : c - 1 <= a0 + max ((Y1 \ T).card - 2) 0 := by
      rw [hCompCard, ha1eq]
      simpa only [max_eq_left (Nat.zero_le ((2 * lam - 3) - 2))] using hlower0
    have hest := hEstimate (Y1 \ T) Finset.sdiff_subset
      hfreeComp s hsComp hsHigh
    have hdeficit : r - degree s <= c - 1 := highMu_deficit_le_pred hr hsHigh
    omega

  have ha1ge3 : 3 <= a1 := by
    rw [← hY1card, ← hTcard]
    exact Finset.card_le_card hTsub
  obtain ⟨lam, hlamCases, ha1eq⟩ := even_between_four_and_seven hEven ha1ge3 ha1lt
  have hceilEq : ceilHalf a1 = lam := by
    have hceil := two_mul_ceilHalf_of_even hEven
    omega
  have ha0lam : a0 + lam = c := by rw [hKey, hceilEq]
  have hwlam : w = c + lam := even_parameter_cardinalities ha1eq ha0lam hW
  exact ⟨lam, hlamCases, ha1eq, ha0lam, hwlam, T, hTH, s, hsComp, hsHigh,
    hfreeComp, hsMax⟩

/-- The final clique-extension obstruction closes the high-neighbourhood branch once the
structural reduction has produced `lambda = 2` or `lambda = 3`.  This theorem is deliberately
phrased with every item passed to the graph-specific obstruction, so using it cannot conceal a
weaker cardinality statement. -/
theorem highMu_final_extension_contradiction [DecidableEq V]
    {H : Finset (Finset V)} {Y1 : Finset V} {degree : V -> Nat}
    {r a0 a1 c w : Nat}
    (hred : HighMuReductionData H Y1 degree r a0 a1 c w)
    (hFinalExtensionObstruction :
      ∀ lam, (lam = 2 ∨ lam = 3) -> a1 = 2 * lam -> a0 + lam = c -> w = c + lam ->
        ∀ edge ∈ H, ∀ vertex ∈ Y1 \ edge,
          r + 1 <= 2 * degree vertex -> IsTripleFreeIn H (Y1 \ edge) ->
            (∀ y ∈ Y1 \ edge, degree y <= degree vertex) -> False) :
    False := by
  rcases hred with ⟨lam, hlam, ha1, ha0, hw, edge, hedge, vertex, hver, hhigh,
    hfree, hmax⟩
  exact hFinalExtensionObstruction lam hlam ha1 ha0 hw edge hedge vertex hver hhigh
    hfree hmax

namespace Configuration

variable [Fintype V] [DecidableEq V] (C : Configuration V)

/-- The final `lambda in {2,3}` contradiction, with Lemma 3.4 applied rather than retained as
an abstract falsehood.  The remaining hypothesis is exactly the finite greedy construction of
the aligned outside/reservoir lists. -/
theorem highMu_final_extension_contradiction_of_data
    {H : Finset (Finset V)}
    (hred : HighMuReductionData H C.Y1 C.blueDegreeToX C.r C.a0 C.a1 C.c C.w)
    (hSelection :
      ∀ lam, (lam = 2 ∨ lam = 3) -> C.a1 = 2 * lam -> C.a0 + lam = C.c ->
        C.w = C.c + lam -> ∀ edge ∈ H, ∀ vertex ∈ C.Y1 \ edge,
          C.r + 1 <= 2 * C.blueDegreeToX vertex ->
          IsTripleFreeIn H (C.Y1 \ edge) ->
          (∀ y ∈ C.Y1 \ edge, C.blueDegreeToX y <= C.blueDegreeToX vertex) ->
          C.blueDegreeToX vertex < C.r ∧ C.HasCliqueExtensionData vertex) :
    False := by
  classical
  apply highMu_final_extension_contradiction hred
  intro lam hlam ha1 ha0 hw edge hedge vertex hver hhigh hfree hmax
  obtain ⟨hdeg, hdata⟩ :=
    hSelection lam hlam ha1 ha0 hw edge hedge vertex hver hhigh hfree hmax
  exact C.not_hasCliqueExtensionData (Finset.mem_sdiff.mp hver).1 hdeg hdata

end Configuration

/-! ## The final `lambda in {2,3}` greedy step -/

/-- The final capacity inequality in natural-number form.  The equality for `Wcard` is the
cardinality identity `|W| + mu_s + 1 + c + lambda = c^2 + r`, while `b + mu_s = r`
is the definition `b = r - mu_s` together with `mu_s <= r`. -/
lemma highMu_final_capacity {c r lam muS b Wcard : Nat}
    (hc : 4 <= c) (hlam : lam <= 3) (hmu : muS <= 2 * c - 2)
    (hb : b + muS = r)
    (hWcard : Wcard + muS + 1 + c + lam = c ^ 2 + r) :
    muS + b <= Wcard := by
  have hsquare : 4 * c <= c ^ 2 := by
    have := Nat.mul_le_mul_left c hc
    nlinarith
  have hcap : c + lam + muS + 1 <= c ^ 2 := by omega
  omega

/-- Uniform red-neighbourhood bounds imply all distinct representatives needed for the final
alternating extension.  The list `ys` is the already chosen order of the `b` outside vertices;
`N y` is its red-neighbour set in `W`. -/
theorem highMu_final_greedy_representatives
    {A : Type u} {B : Type v} [DecidableEq A]
    (N : B -> Finset A) (ys : List B) (b : Nat)
    (hlen : ys.length = b)
    (hys : ys ≠ [])
    (hcommon : ∀ C ∈ sequentialCommonCandidates N ys, b <= C.card)
    (hendpoint : ∀ y, ys.getLast? = some y -> b <= (N y).card) :
    ∃ xs : List A, ∃ z : A,
      (xs ++ [z]).Nodup ∧
        IsRepresentativeList (sequentialCommonCandidates N ys) xs ∧
        ys.getLast?.elim False (fun y => z ∈ N y) := by
  let y := ys.getLast hys
  have hyLast : ys.getLast? = some y := List.getLast?_eq_some_getLast hys
  have hcommon' : ∀ C ∈ sequentialCommonCandidates N ys,
      (sequentialCommonCandidates N ys).length <= C.card := by
    intro C hC
    rw [length_sequentialCommonCandidates, hlen]
    exact (Nat.sub_le b 1).trans (hcommon C hC)
  have hendpoint' : (sequentialCommonCandidates N ys).length + 1 <= (N y).card := by
    rw [length_sequentialCommonCandidates, hlen]
    have hbpos : 1 <= b := by
      rw [← hlen]
      exact List.length_pos_iff.mpr hys
    have : b - 1 + 1 = b := by omega
    rw [this]
    exact hendpoint y hyLast
  obtain ⟨xs, z, hnodup, hrep, hz⟩ :=
    exists_nodup_sequential_common_and_endpoint N ys (N y) hcommon' hendpoint'
  refine ⟨xs, z, hnodup, hrep, ?_⟩
  simp [hyLast, hz]

/-- The form used after the displayed final capacity calculation.  All sequential common
neighbour sets and the last endpoint set lose at most `muS` vertices from `W`; the inequality
`muS + b <= Wcard` therefore supplies the uniform cardinality required by the greedy lemma. -/
theorem highMu_final_greedy_representatives_of_capacity
    {A : Type u} {B : Type v} [DecidableEq A]
    (N : B -> Finset A) (ys : List B) (b muS Wcard : Nat)
    (hlen : ys.length = b) (hys : ys ≠ [])
    (hcapacity : muS + b <= Wcard)
    (hcommon : ∀ C ∈ sequentialCommonCandidates N ys, Wcard - muS <= C.card)
    (hendpoint : ∀ y, ys.getLast? = some y -> Wcard - muS <= (N y).card) :
    ∃ xs : List A, ∃ z : A,
      (xs ++ [z]).Nodup ∧
        IsRepresentativeList (sequentialCommonCandidates N ys) xs ∧
        ys.getLast?.elim False (fun y => z ∈ N y) := by
  have hb : b <= Wcard - muS := by omega
  apply highMu_final_greedy_representatives N ys b hlen hys
  · intro C hC
    exact hb.trans (hcommon C hC)
  · intro y hy
    exact hb.trans (hendpoint y hy)

/-- Representatives of the consecutive intersections, followed by a representative for the
last endpoint, are exactly the aligned vertices of an alternating relation. -/
theorem representativeList_sequential_relations
    {A : Type u} {B : Type v} [DecidableEq A]
    (N : B -> Finset A) (R : B -> A -> Prop)
    (hmem : ∀ y x, x ∈ N y ↔ R y x)
    {ys : List B} {xs : List A} {z : A}
    (hrep : IsRepresentativeList (sequentialCommonCandidates N ys) xs)
    (hz : ys.getLast?.elim False (fun y => z ∈ N y)) :
    List.Forall₂ R ys (xs ++ [z]) ∧
      List.Forall₂ (fun x y => R y x) xs ys.tail := by
  induction ys generalizing xs with
  | nil => simp at hz
  | cons y ys ih =>
      cases ys with
      | nil =>
          have hxs : xs = [] := by
            have hlen := hrep.length_eq
            simp only [sequentialCommonCandidates_singleton, List.length_nil] at hlen
            exact List.eq_nil_of_length_eq_zero hlen.symm
          subst xs
          simp only [List.getLast?_singleton, Option.elim_some] at hz
          constructor
          · exact .cons (hmem y z |>.mp hz) .nil
          · exact .nil
      | cons y' ys =>
          cases xs with
          | nil =>
              have hlen := hrep.length_eq
              simp only [sequentialCommonCandidates_cons_cons, List.length_cons,
                List.length_nil] at hlen
              omega
          | cons x xs =>
              have hrep' := isRepresentativeList_cons.mp hrep
              have hx := Finset.mem_inter.mp hrep'.1
              have hz' : (y' :: ys).getLast?.elim False (fun q => z ∈ N q) := by
                simpa using hz
              obtain ⟨hfirst, hnext⟩ := ih hrep'.2 hz'
              constructor
              · exact .cons ((hmem y x).mp hx.1) hfirst
              · exact .cons ((hmem y' x).mp hx.2) hnext

namespace Configuration

variable [Fintype V] [DecidableEq V] (C : Configuration V)

/-- Red neighbours of `y` inside the extension reservoir belonging to the anchor `s`. -/
noncomputable def extensionRedNeighbors (s y : V) : Finset V := by
  classical
  exact (C.extensionReservoir s).filter fun x => C.G.Adj y x

@[simp] lemma mem_extensionRedNeighbors {s y x : V} :
    x ∈ C.extensionRedNeighbors s y ↔
      x ∈ C.extensionReservoir s ∧ C.G.Adj y x := by
  classical
  simp [extensionRedNeighbors]

/-- The final greedy argument in graph form.  Uniform cardinal bounds for the consecutive
common-neighbour sets and the last endpoint set produce the exact extension lists forbidden by
Lemma 3.4. -/
theorem highMu_greedy_extension_contradiction
    {s : V} (hs : s ∈ C.Y1) (hdeg : C.blueDegreeToX s < C.r)
    (ys : List V)
    (hysLen : ys.length = C.extensionCount s) (hys0 : ys ≠ []) (hysN : ys.Nodup)
    (hysY : ∀ y ∈ ys, y ∈ C.Y)
    (hcommon : ∀ D ∈ sequentialCommonCandidates (C.extensionRedNeighbors s) ys,
      C.extensionCount s <= D.card)
    (hendpoint : ∀ y, ys.getLast? = some y ->
      C.extensionCount s <= (C.extensionRedNeighbors s y).card) : False := by
  classical
  obtain ⟨xs0, z, hxsN, hrep, hz⟩ :=
    highMu_final_greedy_representatives (C.extensionRedNeighbors s) ys
      (C.extensionCount s) hysLen hys0 hcommon hendpoint
  let xs := xs0 ++ [z]
  have hrels := representativeList_sequential_relations
    (C.extensionRedNeighbors s)
    (fun y x => x ∈ C.extensionReservoir s ∧ C.G.Adj y x)
    (fun y x => C.mem_extensionRedNeighbors (s := s) (y := y) (x := x)) hrep hz
  have hxsLen : xs.length = C.extensionCount s := by
    have hrepLen := hrep.length_eq
    simp only [xs, List.length_append, List.length_singleton,
      length_sequentialCommonCandidates] at hrepLen ⊢
    rw [hysLen] at hrepLen
    have hcountPos : 0 < C.extensionCount s := by
      simp only [extensionCount]
      omega
    omega
  have hxsW : ∀ x ∈ xs, x ∈ C.extensionReservoir s := by
    intro x hx
    have hright : ∀ {as bs : List V},
        List.Forall₂ (fun _ q => q ∈ C.extensionReservoir s) as bs →
          ∀ q ∈ bs, q ∈ C.extensionReservoir s := by
      intro as bs hab
      induction hab with
      | nil => simp
      | cons hp _ ih =>
          intro q hq
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact hp
          · exact ih q hq
    exact hright (hrels.1.imp fun _ _ h => h.1) x hx
  have hyx : List.Forall₂ C.G.Adj ys xs :=
    hrels.1.imp fun _ _ h => h.2
  have hxy : List.Forall₂ C.G.Adj xs.dropLast ys.tail := by
    simpa [xs] using (hrels.2.imp fun _ _ h => h.2.symm)
  apply C.clique_extension_obstruction_list hs hdeg hysLen hxsLen hysN hxsN hysY hxsW
    hyx hxy

end Configuration

end Erdos518
