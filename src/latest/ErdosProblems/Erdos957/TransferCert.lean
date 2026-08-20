import ErdosProblems.Erdos957.Charge

/-!
# Transfer certificates for the charging argument in Erdős problem 957

This file packages the combinatorial content of Dumitrescu's transfer
argument.  The geometric part of the proof has to construct a certificate;
the theorem below then turns that certificate into the required edge bound.

All charges are doubled.  Thus a source sends two tokens, an ordinary hull
vertex has capacity six, every distinguished hull vertex has capacity four,
and a non-hull vertex has capacity twelve.  The emitting sources `B` are a
subset of the full distinguished set `Q`: vertices of `Q \ B` already have
degree at most two and therefore need not emit a token.
-/

namespace Erdos957

open scoped BigOperators

section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
A certificate for the finite transfer part of Dumitrescu's argument.

`H` is the set of hull vertices, `Q` is the full set of distinguished flat
diameter endpoints, and `B ⊆ Q` is the subset of degree-three emitters.
Every emitter sends exactly two doubled tokens, every other vertex emits
none, and transfers only land outside the hull.  The last field is the local
geometric assertion that each non-hull target can absorb all its incoming
tokens without exceeding doubled capacity twelve.
-/
structure TransferCert (H Q B : Finset V) where
  /-- The number of doubled tokens sent from one vertex to another. -/
  transfer : V → V → ℕ
  /-- Every emitter is one of the distinguished vertices. -/
  source_subset_distinguished : B ⊆ Q
  /-- Every distinguished vertex is a hull vertex. -/
  distinguished_subset_hull : Q ⊆ H
  /-- The shortest-distance degree of every hull vertex is at most three. -/
  hull_degree_le_three : ∀ v ∈ H, G.degree v ≤ 3
  /-- A distinguished vertex which does not emit has degree at most two. -/
  distinguished_nonsource_degree_le_two :
    ∀ v, v ∈ Q → v ∉ B → G.degree v ≤ 2
  /-- A source emits two doubled tokens and every non-source emits none. -/
  source_row_sum : ∀ u, ∑ v, transfer u v = if u ∈ B then 2 else 0
  /-- A transfer with positive weight always lands strictly inside the hull. -/
  target_not_hull : ∀ {u v}, 0 < transfer u v → v ∉ H
  /-- Every non-hull vertex remains within doubled capacity twelve. -/
  nonhull_target_capacity :
    ∀ v, v ∉ H → 2 * G.degree v + ∑ u, transfer u v ≤ 12

namespace TransferCert

variable {G} {H Q B : Finset V}

/-- No token in a transfer certificate lands on a hull vertex. -/
lemma transfer_eq_zero_of_mem_hull (C : TransferCert G H Q B)
    (u : V) {v : V} (hv : v ∈ H) : C.transfer u v = 0 := by
  by_contra hne
  have hpos : 0 < C.transfer u v := Nat.pos_of_ne_zero hne
  exact C.target_not_hull hpos hv

/-- A vertex outside the hull cannot be distinguished. -/
lemma not_mem_distinguished_of_not_mem_hull (C : TransferCert G H Q B)
    {v : V} (hv : v ∉ H) : v ∉ Q := by
  exact fun hvQ ↦ hv (C.distinguished_subset_hull hvQ)

/-- A vertex outside the distinguished set cannot be a source. -/
lemma not_mem_source_of_not_mem_distinguished (C : TransferCert G H Q B)
    {v : V} (hv : v ∉ Q) : v ∉ B := by
  exact fun hvB ↦ hv (C.source_subset_distinguished hvB)

/-- A vertex outside the hull cannot be a source. -/
lemma not_mem_source_of_not_mem_hull (C : TransferCert G H Q B)
    {v : V} (hv : v ∉ H) : v ∉ B := by
  exact C.not_mem_source_of_not_mem_distinguished
    (C.not_mem_distinguished_of_not_mem_hull hv)

/--
The local fields of a transfer certificate imply the pointwise final-capacity
inequality used by the global doubled-token calculation.
-/
theorem doubledFinalToken_le_doubledCapacity (C : TransferCert G H Q B) (v : V) :
    doubledFinalToken (fun w ↦ G.degree w) C.transfer v ≤ doubledCapacity H Q v := by
  by_cases hvH : v ∈ H
  · have hin : ∑ u, C.transfer u v = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      exact C.transfer_eq_zero_of_mem_hull u hvH
    have hinZ : ∑ u, (C.transfer u v : ℤ) = 0 := by
      exact_mod_cast hin
    have hdeg : G.degree v ≤ 3 := C.hull_degree_le_three v hvH
    have hdegZ : (G.degree v : ℤ) ≤ 3 := by exact_mod_cast hdeg
    by_cases hvQ : v ∈ Q
    · by_cases hvB : v ∈ B
      · have hout : ∑ w, C.transfer v w = 2 := by
          simpa [hvB] using C.source_row_sum v
        have houtZ : ∑ w, (C.transfer v w : ℤ) = 2 := by
          exact_mod_cast hout
        simp only [doubledFinalToken, doubledInitialToken, hinZ, houtZ,
          doubledCapacity, if_pos hvH, if_pos hvQ]
        omega
      · have hout : ∑ w, C.transfer v w = 0 := by
          simpa [hvB] using C.source_row_sum v
        have houtZ : ∑ w, (C.transfer v w : ℤ) = 0 := by
          exact_mod_cast hout
        have hdegTwo : G.degree v ≤ 2 :=
          C.distinguished_nonsource_degree_le_two v hvQ hvB
        have hdegTwoZ : (G.degree v : ℤ) ≤ 2 := by exact_mod_cast hdegTwo
        simp only [doubledFinalToken, doubledInitialToken, hinZ, houtZ,
          doubledCapacity, if_pos hvH, if_pos hvQ]
        omega
    · have hvB : v ∉ B := C.not_mem_source_of_not_mem_distinguished hvQ
      have hout : ∑ w, C.transfer v w = 0 := by
        simpa [hvB] using C.source_row_sum v
      have houtZ : ∑ w, (C.transfer v w : ℤ) = 0 := by
        exact_mod_cast hout
      simp only [doubledFinalToken, doubledInitialToken, hinZ, houtZ,
        doubledCapacity, if_pos hvH, if_neg hvQ]
      omega
  · have hvQ : v ∉ Q := C.not_mem_distinguished_of_not_mem_hull hvH
    have hvB : v ∉ B := C.not_mem_source_of_not_mem_distinguished hvQ
    have hout : ∑ w, C.transfer v w = 0 := by
      simpa [hvB] using C.source_row_sum v
    have houtZ : ∑ w, (C.transfer v w : ℤ) = 0 := by
      exact_mod_cast hout
    have hcap := C.nonhull_target_capacity v hvH
    have hcapZ :
        2 * (G.degree v : ℤ) + ∑ u, (C.transfer u v : ℤ) ≤ 12 := by
      exact_mod_cast hcap
    simp only [doubledFinalToken, doubledInitialToken, houtZ,
      doubledCapacity, if_neg hvH, if_neg hvQ]
    omega

/--
The exact global edge bound supplied by a transfer certificate.

This is the finite combinatorial conclusion of the charging argument.  It
uses no geometry beyond the certificate fields.  The result is stated in
`ℤ` so the two deficits can be subtracted without truncated-natural-number
side conditions.
-/
theorem edge_bound_of_transfer (C : TransferCert G H Q B) :
    (4 * G.edgeFinset.card : ℤ) ≤
      12 * (Fintype.card V : ℤ) - 6 * (H.card : ℤ) - 2 * (Q.card : ℤ) := by
  have hsum :
      ∑ v, doubledFinalToken (fun w ↦ G.degree w) C.transfer v ≤
        ∑ v, doubledCapacity H Q v :=
    Finset.sum_le_sum fun v _ ↦ C.doubledFinalToken_le_doubledCapacity v
  rw [sum_doubledFinalToken_eq_sum_doubledInitialToken,
    sum_doubledCapacity] at hsum
  have hhandshake :
      ∑ v, doubledInitialToken (fun w ↦ G.degree w) v =
        (4 * G.edgeFinset.card : ℤ) := by
    simp only [doubledInitialToken, ← Finset.mul_sum]
    have hdegree :
        ∑ v, (G.degree v : ℤ) = 2 * (G.edgeFinset.card : ℤ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    rw [hdegree]
    ring
  rwa [hhandshake] at hsum

end TransferCert

end

end Erdos957

