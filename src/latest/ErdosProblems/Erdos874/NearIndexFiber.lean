/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.PopularPairs

/-!
# Fibers of the near-index pair-sum map

The gaps occurring among the pairs with one fixed sum differ by at least two.
Consequently such a fiber has at most `ceil (u / 2)` elements.  This is the
small counting fact used in the popular-pair-sums argument for Erdős problem
874.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The parameters of near-index pairs whose elements have sum `z`. -/
def nearIndexParameterFiber (B : Finset ℤ) (u : ℕ) (hu : u ≤ B.card)
    (z : ℤ) : Finset (NearIndex B u) :=
  Finset.univ.filter fun p ↦ (∑ x ∈ nearIndexPair B u hu p, x) = z

lemma mem_nearIndexParameterFiber {B : Finset ℤ} {u : ℕ}
    {hu : u ≤ B.card} {z : ℤ} {p : NearIndex B u} :
    p ∈ nearIndexParameterFiber B u hu z ↔
      (∑ x ∈ nearIndexPair B u hu p, x) = z := by
  simp [nearIndexParameterFiber]

private lemma nearIndexPair_sum (B : Finset ℤ) (u : ℕ)
    (hu : u ≤ B.card) (p : NearIndex B u) :
    (∑ x ∈ nearIndexPair B u hu p, x) =
      B.orderEmbOfFin rfl ⟨p.1, by omega⟩ +
        B.orderEmbOfFin rfl ⟨p.1 + p.2 + 1, by omega⟩ := by
  rw [nearIndexPair]
  rw [Finset.sum_pair]
  intro h
  have h' := (B.orderEmbOfFin rfl).injective h
  have hval := congrArg Fin.val h'
  change (p.1 : ℕ) = p.1 + p.2 + 1 at hval
  omega

/-- On one pair-sum fiber, the map sending a near-index pair to the half of
its zero-based gap parameter is injective.  Indeed, equal halves make the two
gap parameters differ by at most one, whereas two different representations
of the same sum force the index gaps to differ by at least two. -/
private lemma nearIndexParameterFiber_halfGap_injOn
    (B : Finset ℤ) (u : ℕ) (hu : u ≤ B.card) (z : ℤ) :
    Set.InjOn (fun p : NearIndex B u ↦ (p.2 : ℕ) / 2)
      (nearIndexParameterFiber B u hu z : Set (NearIndex B u)) := by
  intro p hp q hq hhalf
  have hpsum := mem_nearIndexParameterFiber.mp hp
  have hqsum := mem_nearIndexParameterFiber.mp hq
  rw [nearIndexPair_sum] at hpsum hqsum
  let e : Fin B.card ↪o ℤ := B.orderEmbOfFin rfl
  let pi : Fin B.card := ⟨p.1, by omega⟩
  let pj : Fin B.card := ⟨p.1 + p.2 + 1, by omega⟩
  let qi : Fin B.card := ⟨q.1, by omega⟩
  let qj : Fin B.card := ⟨q.1 + q.2 + 1, by omega⟩
  have hsum : e pi + e pj = e qi + e qj := by
    simpa [e, pi, pj, qi, qj] using hpsum.trans hqsum.symm
  change (p.2 : ℕ) / 2 = (q.2 : ℕ) / 2 at hhalf
  have hgap_close :
      (p.2 : ℕ) ≤ (q.2 : ℕ) + 1 ∧ (q.2 : ℕ) ≤ (p.2 : ℕ) + 1 := by
    have hpmod : (p.2 : ℕ) % 2 < 2 := Nat.mod_lt _ (by omega)
    have hqmod : (q.2 : ℕ) % 2 < 2 := Nat.mod_lt _ (by omega)
    have hpdecomp := Nat.mod_add_div (p.2 : ℕ) 2
    have hqdecomp := Nat.mod_add_div (q.2 : ℕ) 2
    omega
  have hi : pi = qi := by
    apply le_antisymm
    · by_contra hnle
      have hqi_lt_pi : qi < pi := lt_of_not_ge hnle
      have heqi_lt_epi : e qi < e pi := e.strictMono hqi_lt_pi
      have hpj_lt_eqj : e pj < e qj := by omega
      have hpj_lt_qj : pj < qj := (e.lt_iff_lt).mp hpj_lt_eqj
      have hpjval_lt_qjval : pj.val < qj.val := hpj_lt_qj
      dsimp [pi, pj, qi, qj] at hpjval_lt_qjval
      have hqiltpi : qi.val < pi.val := hqi_lt_pi
      dsimp [pi, qi] at hqiltpi
      omega
    · by_contra hnle
      have hpi_lt_qi : pi < qi := lt_of_not_ge hnle
      have hepi_lt_eqi : e pi < e qi := e.strictMono hpi_lt_qi
      have heqj_lt_epj : e qj < e pj := by omega
      have hqj_lt_pj : qj < pj := (e.lt_iff_lt).mp heqj_lt_epj
      have hqjval_lt_pjval : qj.val < pj.val := hqj_lt_pj
      dsimp [pi, pj, qi, qj] at hqjval_lt_pjval
      have hpiltqi : pi.val < qi.val := hpi_lt_qi
      dsimp [pi, qi] at hpiltqi
      omega
  have hj : pj = qj := by
    have hfirst : e pi = e qi := congrArg e hi
    have : e pj = e qj := by omega
    exact e.injective this
  apply Prod.ext
  · exact Fin.ext (by
      simpa [pi, qi] using congrArg Fin.val hi)
  · apply Fin.ext
    have hi' := congrArg Fin.val hi
    have hj' := congrArg Fin.val hj
    dsimp [pi, pj, qi, qj] at hi' hj'
    omega

/-- A fixed sum occurs among the `(L-u)u` near-index pairs at most
`ceil (u/2)` times, in the division-free form used in the counting argument. -/
theorem card_nearIndexParameterFiber_two_mul_le
    (B : Finset ℤ) (u : ℕ) (hu : u ≤ B.card) (z : ℤ) :
    2 * (nearIndexParameterFiber B u hu z).card ≤ u + 1 := by
  let F := nearIndexParameterFiber B u hu z
  let halfGap : NearIndex B u → ℕ := fun p ↦ (p.2 : ℕ) / 2
  have hinj : Set.InjOn halfGap (F : Set (NearIndex B u)) := by
    simpa [F, halfGap] using
      nearIndexParameterFiber_halfGap_injOn B u hu z
  have himage : F.image halfGap ⊆ Finset.range ((u + 1) / 2) := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    simp only [Finset.mem_range]
    have hp_lt : (p.2 : ℕ) < u := p.2.isLt
    dsimp [halfGap]
    omega
  have hcard := Finset.card_le_card himage
  rw [Finset.card_image_iff.mpr hinj, Finset.card_range] at hcard
  have hround : 2 * ((u + 1) / 2) ≤ u + 1 := Nat.mul_div_le (u + 1) 2
  dsimp [F] at hcard
  exact (Nat.mul_le_mul_left 2 hcard).trans hround

/-- The same fiber estimate for the concrete finset of unordered pairs. -/
theorem card_nearIndexPairs_sum_fiber_two_mul_le
    (B : Finset ℤ) (u : ℕ) (hu : u ≤ B.card) (z : ℤ) :
    2 * ((nearIndexPairs B u hu).filter
      (fun P ↦ (∑ x ∈ P, x) = z)).card ≤ u + 1 := by
  have hfilter :
      (nearIndexPairs B u hu).filter (fun P ↦ (∑ x ∈ P, x) = z) =
        (nearIndexParameterFiber B u hu z).image (nearIndexPair B u hu) := by
    ext P
    constructor
    · intro hP
      obtain ⟨hPnear, hPsum⟩ := Finset.mem_filter.mp hP
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hPnear
      exact Finset.mem_image.mpr
        ⟨p, mem_nearIndexParameterFiber.mpr hPsum, rfl⟩
    · intro hP
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩,
        mem_nearIndexParameterFiber.mp hp⟩
  rw [hfilter, Finset.card_image_of_injective _
    (nearIndexPair_injective B u hu)]
  exact card_nearIndexParameterFiber_two_mul_le B u hu z

/-- For even `u` the preceding estimate has the sharper right-hand side
`u`, equivalently every fiber has at most `u/2` elements. -/
theorem card_nearIndexPairs_sum_fiber_two_mul_le_of_even
    (B : Finset ℤ) (u : ℕ) (hu : u ≤ B.card) (z : ℤ)
    (hu_even : Even u) :
    2 * ((nearIndexPairs B u hu).filter
      (fun P ↦ (∑ x ∈ P, x) = z)).card ≤ u := by
  have h := card_nearIndexPairs_sum_fiber_two_mul_le B u hu z
  obtain ⟨v, rfl⟩ := hu_even
  omega

/-! ## The explicit DF95 popular-sum estimate -/

/-- Under the small fourth-layer hypothesis used by the DF95 engine, more
than `1.98 |B|` pair sums have the required representation reserve.  The
large absolute threshold is only used to make the floor estimates uniform. -/
theorem card_dfPopularPairSums_large_of_small_four
    {B : Finset ℤ} (hB : 100000000 ≤ B.card)
    (hfour : 5 * (restrictedSumset 4 B).card ≤ 29 * B.card) :
    99 * B.card < 50 * (dfPopularPairSums B).card := by
  let L := B.card
  let q := L / 500
  let u := 2 * q
  let h := L / 1000000
  let D := (restrictedSumset 2 B).card
  let S := (dfPopularPairSums B).card
  have hqLower : L < 500 * (q + 1) := by
    dsimp [q]
    omega
  have hqUpper : 500 * q ≤ L := by
    dsimp [q]
    omega
  have hh : 1000000 * h ≤ L := by
    dsimp [h]
    omega
  have hu : u ≤ B.card := by
    dsimp [u, q, L]
    omega
  have hD : 5 * D ≤ 44 * L := by
    have htwo := card_restrictedSumset_two_le_three_mul_add_four
      (B := B) (by omega)
    dsimp [D, L]
    omega
  have hfiber : ∀ z : ℤ,
      (pairSumFiber (nearIndexPairs B u hu) z).card ≤ q := by
    intro z
    change ((nearIndexPairs B u hu).filter
      (fun P ↦ (∑ x ∈ P, x) = z)).card ≤ q
    have hz := card_nearIndexPairs_sum_fiber_two_mul_le_of_even
      B u hu z (by simp [u])
    have huq : u = 2 * q := rfl
    omega
  have hcount₀ := card_pairFamily_le_popular_mul_add_twoLayer_mul
    (B := B) (T := nearIndexPairs B u hu)
    (v := dfPairMultiplicity B) (w := q)
    (fun P hP ↦ mem_nearIndexPairs_pairRepresentation hu hP) hfiber
  have hcount : (L - 2 * q) * (2 * q) ≤ S * q + D * (2 * h + 1) := by
    rw [card_nearIndexPairs] at hcount₀
    simpa [L, u, h, D, S, dfPopularPairSums, dfPairMultiplicity]
      using hcount₀
  exact dfPopular_numeric hB hqLower hqUpper hh hD hcount

end

end Erdos874
