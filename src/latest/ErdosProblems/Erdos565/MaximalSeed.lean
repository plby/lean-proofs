import ErdosProblems.Erdos565.Rounding
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# The finite maximal-seed argument for Erdős problem 565

This file isolates the completely finite choice made in the proof of the key
lemma.  The graph- and Janson-specific assertion is represented by an arbitrary
predicate `Good i U R`.  Thus the selection argument can be used with the copy
hypergraphs once those have been constructed, but does not hide any
probabilistic or container theorem in an unproved declaration.

The important point for formalization is that radii are natural numbers.  A
candidate satisfies the literal equality

`U.card = seedThreshold r N + ∑ i, R i`.

This equality bounds every coordinate by `S.card`, so all candidates can be
enumerated by a finite type and one maximizing the sum of the radii can be
chosen.  Monotonicity of `Good` under enlarging the vertex set then turns
maximality into the required one-vertex extension failure.
-/

namespace Erdos565
namespace MaximalSeed

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The exact candidate predicate used in the maximal-seed construction. -/
def IsCandidate (r N : ℕ) (S : Finset α)
    (Good : Fin r → Finset α → ℕ → Prop) (U : Finset α) (R : Fin r → ℕ) : Prop :=
  U ⊆ S ∧
    U.card = seedThreshold r N + ∑ i, R i ∧
    ∀ i, Good i U (R i)

/-- The output of the finite maximization.  The `maximal` field quantifies over
all natural-valued radius vectors, not merely over the bounded encoding used in
the proof. -/
structure Result (r N : ℕ) (S : Finset α)
    (Good : Fin r → Finset α → ℕ → Prop) where
  U : Finset α
  R : Fin r → ℕ
  candidate : IsCandidate r N S Good U R
  maximal : ∀ (U' : Finset α) (R' : Fin r → ℕ),
    IsCandidate r N S Good U' R' → (∑ i, R' i) ≤ ∑ i, R i
  extensionFailure : ∀ v ∈ S \ U, ∀ i, ¬ Good i (insert v U) (R i + 1)

/-- A finite code for a candidate.  The radius bound is harmless: candidate
equality and `U ⊆ S` imply every radius is at most `S.card`. -/
private abbrev Code (r : ℕ) (S : Finset α) :=
  Finset α × (Fin r → Fin (S.card + 1))

private def codeMass {r : ℕ} {S : Finset α} (x : Code r S) : ℕ :=
  ∑ i, (x.2 i).val

private def codeCandidate (r N : ℕ) (S : Finset α)
    (Good : Fin r → Finset α → ℕ → Prop) (x : Code r S) : Prop :=
  IsCandidate r N S Good x.1 fun i ↦ (x.2 i).val

private lemma coordinate_le_sum {r : ℕ} (R : Fin r → ℕ) (i : Fin r) :
    R i ≤ ∑ j, R j := by
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

omit [Fintype α] [DecidableEq α] in
private lemma radius_le_ground_card {r N : ℕ} {S U : Finset α}
    {Good : Fin r → Finset α → ℕ → Prop} {R : Fin r → ℕ}
    (h : IsCandidate r N S Good U R) (i : Fin r) : R i ≤ S.card := by
  exact (coordinate_le_sum R i).trans <|
    calc
      ∑ j, R j ≤ seedThreshold r N + ∑ j, R j := Nat.le_add_left _ _
      _ = U.card := h.2.1.symm
      _ ≤ S.card := Finset.card_le_card h.1

/-- Exact finite maximal-seed selection.

The only semantic assumptions on `Good` are the two facts used in the paper:
radius zero is available on an initial `b_N`-set, and enlarging the vertex set
preserves `Good` at a fixed radius. -/
theorem exists_result (r N : ℕ) (S : Finset α)
    (Good : Fin r → Finset α → ℕ → Prop)
    (hseed : seedThreshold r N ≤ S.card)
    (hzero : ∀ U ⊆ S, U.card = seedThreshold r N → ∀ i, Good i U 0)
    (hmono : ∀ i U T R, U ⊆ T → Good i U R → Good i T R) :
    Nonempty (Result r N S Good) := by
  classical
  obtain ⟨U₀, hU₀S, hU₀card⟩ := S.exists_subset_card_eq hseed
  let R₀ : Fin r → Fin (S.card + 1) := fun _ ↦ ⟨0, Nat.succ_pos _⟩
  let x₀ : Code r S := (U₀, R₀)
  let candidates : Finset (Code r S) :=
    Finset.univ.filter (codeCandidate r N S Good)
  have hx₀ : x₀ ∈ candidates := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hU₀S, ?_, ?_⟩
    · simpa [x₀, R₀] using hU₀card
    · intro i
      simpa [x₀, R₀] using hzero U₀ hU₀S hU₀card i
  obtain ⟨x, hx, hmax⟩ :=
    Finset.exists_max_image candidates codeMass ⟨x₀, hx₀⟩
  have hxc : codeCandidate r N S Good x := (Finset.mem_filter.mp hx).2
  let U : Finset α := x.1
  let R : Fin r → ℕ := fun i ↦ (x.2 i).val
  have hcandidate : IsCandidate r N S Good U R := by
    simpa [codeCandidate, U, R] using hxc
  have hmaximal : ∀ (U' : Finset α) (R' : Fin r → ℕ),
      IsCandidate r N S Good U' R' → (∑ i, R' i) ≤ ∑ i, R i := by
    intro U' R' h'
    let boundedR : Fin r → Fin (S.card + 1) := fun i ↦
      ⟨R' i, Nat.lt_succ_iff.mpr (radius_le_ground_card h' i)⟩
    let x' : Code r S := (U', boundedR)
    have hx' : x' ∈ candidates := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [codeCandidate, x', boundedR] using h'
    have := hmax x' hx'
    simpa [codeMass, x', boundedR, R] using this
  have hext : ∀ v ∈ S \ U, ∀ i, ¬ Good i (insert v U) (R i + 1) := by
    intro v hv i hgood
    have hvS : v ∈ S := (Finset.mem_sdiff.mp hv).1
    have hvU : v ∉ U := (Finset.mem_sdiff.mp hv).2
    let R' : Fin r → ℕ := Function.update R i (R i + 1)
    have hsum : (∑ j, R' j) = (∑ j, R j) + 1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      rw [Finset.sdiff_singleton_eq_erase]
      omega
    have hinsSub : insert v U ⊆ S := Finset.insert_subset hvS hcandidate.1
    have hinsCard : (insert v U).card = U.card + 1 := Finset.card_insert_of_notMem hvU
    have hgood' : ∀ j, Good j (insert v U) (R' j) := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [R'] using hgood
      · have hj := hmono j U (insert v U) (R j) (Finset.subset_insert v U)
            (hcandidate.2.2 j)
        simpa [R', Function.update_of_ne hji] using hj
    have hcand' : IsCandidate r N S Good (insert v U) R' := by
      refine ⟨hinsSub, ?_, hgood'⟩
      rw [hinsCard, hcandidate.2.1, hsum]
      omega
    have hle := hmaximal (insert v U) R' hcand'
    rw [hsum] at hle
    omega
  exact ⟨⟨U, R, hcandidate, hmaximal, hext⟩⟩

/-! ## Pure arithmetic consequences -/

/-- Summing the source bound
`R_i ≤ p |U| / (2^9 r)` over the `r` colors and using `p ≤ 1` gives the
exact integral inequality `512 * ∑ R_i ≤ |U|`. -/
lemma aggregate_radius_bound {r u : ℕ} {p : ℝ} (R : Fin r → ℕ)
    (hr : 0 < r) (hp : p ≤ 1)
    (hR : ∀ i, (R i : ℝ) ≤ p * u / (512 * r)) :
    512 * (∑ i, R i) ≤ u := by
  have hsum : (∑ i, (R i : ℝ)) ≤ ∑ _i : Fin r, p * u / (512 * r) :=
    Finset.sum_le_sum fun i _ ↦ hR i
  have hu : (0 : ℝ) ≤ u := by positivity
  have hreal : (512 : ℝ) * (∑ i, (R i : ℝ)) ≤ u := by
    calc
      (512 : ℝ) * (∑ i, (R i : ℝ))
          ≤ 512 * (∑ _i : Fin r, p * u / (512 * r)) := by
            gcongr
      _ = p * u := by
        simp
        field_simp
      _ ≤ 1 * u := by gcongr
      _ = u := one_mul _
  exact_mod_cast hreal

/-- The exact rounded seed-size algebra.  Here `d` is `r^50`, `b` is
`ceil (N / d)`, `u = |U|`, and `t = ∑ R_i`.  The conclusions are the
cross-multiplied forms of

`N/d ≤ u ≤ (768/511) N/d < 2 N/d`.
-/
lemma rounded_seed_size {N d b u t : ℕ}
    (hd : 0 < d) (hb : b = N ⌈/⌉ d) (hscale : 2 * d ≤ N)
    (heq : u = b + t) (haggregate : 512 * t ≤ u) :
    N ≤ d * u ∧ 511 * d * u ≤ 768 * N ∧ d * u < 2 * N := by
  subst b
  have hbLower : N ≤ d * (N ⌈/⌉ d) := ceilDiv_lower N d hd
  have hbUpper : d * (N ⌈/⌉ d) ≤ N + d := by
    calc
      d * (N ⌈/⌉ d) ≤ d * (N / d + 1) :=
        Nat.mul_le_mul_left d (ceilDiv_upper N d hd)
      _ = d * (N / d) + d := by ring
      _ ≤ N + d := Nat.add_le_add_right (Nat.mul_div_le N d) d
  have htu : 511 * t ≤ N ⌈/⌉ d := by omega
  have h511 : 511 * u ≤ 512 * (N ⌈/⌉ d) := by omega
  have hlower : N ≤ d * u := by
    exact hbLower.trans (Nat.mul_le_mul_left d (by omega))
  have hmiddle : 511 * d * u ≤ 768 * N := by
    calc
      511 * d * u = d * (511 * u) := by ring
      _ ≤ d * (512 * (N ⌈/⌉ d)) := Nat.mul_le_mul_left d h511
      _ = 512 * (d * (N ⌈/⌉ d)) := by ring
      _ ≤ 512 * (N + d) := Nat.mul_le_mul_left 512 hbUpper
      _ ≤ 768 * N := by omega
  have hNpos : 0 < N := lt_of_lt_of_le (by omega : 0 < 2 * d) hscale
  have hstrict : d * u < 2 * N := by
    by_contra h
    have hge : 2 * N ≤ d * u := Nat.le_of_not_gt h
    have : 1022 * N ≤ 768 * N := by
      calc
        1022 * N = 511 * (2 * N) := by ring
        _ ≤ 511 * (d * u) := Nat.mul_le_mul_left 511 hge
        _ = 511 * d * u := by ring
        _ ≤ 768 * N := hmiddle
    omega
  exact ⟨hlower, hmiddle, hstrict⟩

/-- The exact natural-number derivation of `4|U| ≤ s_N`.  In the
application `a = r^34`, `d = r^50`, and `8a ≤ d`. -/
lemma four_mul_le_ceilDiv {N a d u : ℕ}
    (ha : 0 < a) (hratio : 8 * a ≤ d) (hu : d * u < 2 * N) :
    4 * u ≤ N ⌈/⌉ a := by
  have hmul : a * (4 * u) ≤ N := by
    have h₁ : 8 * a * u ≤ d * u := Nat.mul_le_mul_right u hratio
    have h₂ : 8 * a * u < 2 * N := h₁.trans_lt hu
    have htwice : 2 * (a * (4 * u)) < 2 * N := by
      calc
        2 * (a * (4 * u)) = 8 * a * u := by ring
        _ < 2 * N := h₂
    omega
  have hdiv : 4 * u ≤ N / a := by
    apply (Nat.le_div_iff_mul_le ha).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hfloorRaw : N ⌊/⌋ a ≤ N ⌈/⌉ a := floorDiv_le_ceilDiv
  have hfloor : N / a ≤ N ⌈/⌉ a := by
    simpa only [Nat.floorDiv_eq_div] using hfloorRaw
  exact hdiv.trans hfloor

omit [Fintype α] in
/-- The rounded size estimates in precisely the parameters used by the
maximal-seed argument: `d = r^50` and `a = r^34`. -/
lemma result_card_bounds {r N : ℕ} {S : Finset α}
    {Good : Fin r → Finset α → ℕ → Prop} (result : Result r N S Good)
    (hr : 2 ≤ r) (hscale : 2 * r ^ 50 ≤ N)
    (haggregate : 512 * (∑ i, result.R i) ≤ result.U.card)
    (hsample : sampleThreshold r N ≤ S.card) :
    N ≤ r ^ 50 * result.U.card ∧
      511 * r ^ 50 * result.U.card ≤ 768 * N ∧
      r ^ 50 * result.U.card < 2 * N ∧
      4 * result.U.card ≤ sampleThreshold r N ∧
      4 * result.U.card ≤ S.card := by
  have hd : 0 < r ^ 50 := Nat.pow_pos (by omega)
  have hsize := rounded_seed_size hd (rfl : seedThreshold r N = N ⌈/⌉ r ^ 50)
    hscale result.candidate.2.1 haggregate
  have hratio : 8 * r ^ 34 ≤ r ^ 50 := by
    calc
      8 * r ^ 34 ≤ r ^ 16 * r ^ 34 := Nat.mul_le_mul_right _ (eight_le_pow_sixteen hr)
      _ = r ^ 50 := by rw [← pow_add]
  have hfour : 4 * result.U.card ≤ sampleThreshold r N :=
    four_mul_le_ceilDiv (Nat.pow_pos (by omega)) hratio hsize.2.2
  exact ⟨hsize.1, hsize.2.1, hsize.2.2, hfour, hfour.trans hsample⟩

/-- Packaging of the exact candidate properties with the source's real-valued
radius estimate.  The estimate is a theorem parameter because its proof is the
copy-hypergraph/Janson contradiction, while every finite selection and
arithmetic consequence is proved here. -/
theorem exists_result_with_bounds (r N : ℕ) (S : Finset α)
    (Good : Fin r → Finset α → ℕ → Prop) (p : ℝ)
    (hr : 0 < r) (hp : p ≤ 1)
    (hseed : seedThreshold r N ≤ S.card)
    (hzero : ∀ U ⊆ S, U.card = seedThreshold r N → ∀ i, Good i U 0)
    (hmono : ∀ i U T R, U ⊆ T → Good i U R → Good i T R)
    (hradius : ∀ U R, IsCandidate r N S Good U R →
      ∀ i, (R i : ℝ) ≤ p * U.card / (512 * r)) :
    ∃ result : Result r N S Good,
      (∀ i, (result.R i : ℝ) ≤ p * result.U.card / (512 * r)) ∧
      512 * (∑ i, result.R i) ≤ result.U.card := by
  obtain ⟨result⟩ := exists_result r N S Good hseed hzero hmono
  refine ⟨result, hradius result.U result.R result.candidate, ?_⟩
  exact aggregate_radius_bound result.R hr hp
    (hradius result.U result.R result.candidate)

end MaximalSeed
end Erdos565
