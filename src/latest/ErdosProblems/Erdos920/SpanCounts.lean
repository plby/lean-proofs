import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import ErdosProblems.Erdos920.ProjectiveContainer

/-!
# Cardinality bounds for projective spans

This file supplies the two finite-geometric counting estimates used by the
poor/popular container argument.  A vector subspace of rank `r` contains
exactly `1 + q + ... + q^(r-1)` projective points.  Under the nondegenerate
standard dot product in ambient vector dimension `t + 1`, the points
orthogonal to such a subspace form a projective space of vector dimension
`t + 1 - r`.

All public estimates are stated for `Finset.univ.filter`, so that they can be
applied directly to the finite sets in `Container`.
-/

open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos920.SpanCounts

noncomputable section

open Erdos920.Projective
open Erdos920.ProjectiveContainer

attribute [local instance] Classical.propDecidable Classical.decEq

local instance pointFintype (q d : ℕ) [Fact q.Prime] :
    Fintype (Point (ZMod q) d) := Fintype.ofFinite _

variable {q d t r : ℕ} [Fact q.Prime]

/-! ## Points contained in a projective span -/

/-- Exact `Finset` count of the projective points contained in a span. -/
theorem card_filter_inClosure_eq_geomSum
    (S : Finset (Point (ZMod q) d)) :
    (Finset.univ.filter fun p ↦ InClosure p S).card =
      ∑ i ∈ Finset.range (Module.finrank (ZMod q) (pointSpan S)), q ^ i := by
  classical
  rw [card_filter_univ_eq_natCard_subtype]
  simpa [InClosure, Nat.card_zmod] using
    (natCard_pointsIn (pointSpan S))

/-- A rank-`r` span contains at most `2 q^(r-1)` projective points.  The
truncated exponent is harmless in rank zero; the left side is then zero. -/
theorem card_filter_inClosure_le_two_mul_pow_pred
    (S : Finset (Point (ZMod q) d))
    (hr : Module.finrank (ZMod q) (pointSpan S) = r) :
    (Finset.univ.filter fun p ↦ InClosure p S).card ≤ 2 * q ^ (r - 1) := by
  calc
    (Finset.univ.filter fun p ↦ InClosure p S).card =
        ∑ i ∈ Finset.range r, q ^ i := by
      simpa only [hr] using card_filter_inClosure_eq_geomSum S
    _ ≤ 2 * q ^ (r - 1) :=
      geomSum_le_two_mul_pow_pred q r (Fact.out : q.Prime).two_le

/-- A rank-zero span contains no projective points. -/
theorem card_filter_inClosure_eq_zero_of_rank_eq_zero
    (S : Finset (Point (ZMod q) d))
    (hr : Module.finrank (ZMod q) (pointSpan S) = 0) :
    (Finset.univ.filter fun p ↦ InClosure p S).card = 0 := by
  calc
    (Finset.univ.filter fun p ↦ InClosure p S).card =
        ∑ i ∈ Finset.range 0, q ^ i := by
      simpa only [hr] using card_filter_inClosure_eq_geomSum S
    _ = 0 := by simp

/-- The closure-count bound in the exact `Container.RankClosure` vocabulary. -/
theorem card_filter_rankClosure_cl_le_two_mul_pow_pred
    (S : Finset (Point (ZMod q) d))
    (hr : (rankClosure (F := ZMod q) (d := d)).rank S = r) :
    (Finset.univ.filter fun p ↦
        (rankClosure (F := ZMod q) (d := d)).Cl p S).card ≤
      2 * q ^ (r - 1) := by
  exact card_filter_inClosure_le_two_mul_pow_pred S hr

/-- The rank-zero closure is empty, in the `Container.RankClosure` vocabulary. -/
theorem card_filter_rankClosure_cl_eq_zero_of_rank_eq_zero
    (S : Finset (Point (ZMod q) d))
    (hr : (rankClosure (F := ZMod q) (d := d)).rank S = 0) :
    (Finset.univ.filter fun p ↦
        (rankClosure (F := ZMod q) (d := d)).Cl p S).card = 0 := by
  exact card_filter_inClosure_eq_zero_of_rank_eq_zero S hr

/-- Uniform closure fibre bound with the rank-zero edge case made exact. -/
theorem card_filter_rankClosure_cl_le_if
    (S : Finset (Point (ZMod q) d))
    (hr : (rankClosure (F := ZMod q) (d := d)).rank S = r) :
    (Finset.univ.filter fun p ↦
        (rankClosure (F := ZMod q) (d := d)).Cl p S).card ≤
      if r = 0 then 0 else 2 * q ^ (r - 1) := by
  split_ifs with hzero
  · exact (card_filter_rankClosure_cl_eq_zero_of_rank_eq_zero S
      (hr.trans hzero)).le
  · exact card_filter_rankClosure_cl_le_two_mul_pow_pred S hr

/-- The rank of a projective span is bounded by the ambient vector
dimension. -/
theorem finrank_pointSpan_le_ambient
    (S : Finset (Point (ZMod q) d)) :
    Module.finrank (ZMod q) (pointSpan S) ≤ d := by
  calc
    Module.finrank (ZMod q) (pointSpan S) ≤
        Module.finrank (ZMod q) (Fin d → ZMod q) := Submodule.finrank_le _
    _ = d := Module.finrank_fin_fun (ZMod q)

/-! ## Points orthogonal to a projective span -/

/-- Vector orthogonal complement of the span of a finite set of projective
points, with respect to the standard dot product. -/
def spanOrthSpace (S : Finset (Point (ZMod q) d)) :
    Submodule (ZMod q) (Fin d → ZMod q) :=
  LinearMap.BilinForm.orthogonal
    (dotProductBilin (ZMod q) (ZMod q) :
      LinearMap.BilinForm (ZMod q) (Fin d → ZMod q))
    (pointSpan S)

/-- The standard dot product is nondegenerate over every field. -/
theorem dotProductBilin_nondegenerate :
    (dotProductBilin (ZMod q) (ZMod q) :
      (Fin d → ZMod q) →ₗ[ZMod q] (Fin d → ZMod q) →ₗ[ZMod q] ZMod q).Nondegenerate := by
  constructor
  · intro x hx
    apply dotProduct_eq_zero x
    exact hx
  · intro y hy
    apply dotProduct_eq_zero y
    intro x
    rw [dotProduct_comm]
    exact hy x

/-- The orthogonal complement of a rank-`r` span has vector dimension
`d-r`. -/
theorem finrank_spanOrthSpace (S : Finset (Point (ZMod q) d)) :
    Module.finrank (ZMod q) (spanOrthSpace S) =
      d - Module.finrank (ZMod q) (pointSpan S) := by
  rw [spanOrthSpace,
    LinearMap.BilinForm.finrank_orthogonal dotProductBilin_nondegenerate,
    Module.finrank_fin_fun]

/-- A point lies in the projectivized orthogonal complement of the span iff
it is orthogonal to each generator of that span. -/
theorem submodule_le_spanOrthSpace_iff
    (a : Point (ZMod q) d) (S : Finset (Point (ZMod q) d)) :
    a.submodule ≤ spanOrthSpace S ↔
      ∀ p ∈ S, Orthogonal p a := by
  constructor
  · intro ha p hp
    rw [orthogonal_iff_submodule_le]
    intro v hv
    have hva : v ∈ spanOrthSpace S := ha hv
    exact hva p.rep (submodule_le_pointSpan_of_mem hp
      (by rw [Projectivization.submodule_eq]
          exact Submodule.mem_span_singleton_self p.rep))
  · intro ha
    rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
    intro v hv
    have hspan : pointSpan S ≤
        LinearMap.ker
          ((dotProductBilin (ZMod q) (ZMod q) :
            LinearMap.BilinForm (ZMod q) (Fin d → ZMod q)).flip a.rep) := by
      unfold pointSpan
      apply Finset.sup_le
      intro p hp
      rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
      change p.rep ⬝ᵥ a.rep = 0
      have hap := (orthogonal_iff_submodule_le p a).mp (ha p hp)
      exact hap (by
        rw [Projectivization.submodule_eq]
        exact Submodule.mem_span_singleton_self a.rep)
    exact hspan hv

/-- Exact count of projective points orthogonal to every point of `S`. -/
theorem card_filter_orthogonal_to_span_eq_geomSum
    (S : Finset (Point (ZMod q) d)) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal p a).card =
      ∑ i ∈ Finset.range
        (d - Module.finrank (ZMod q) (pointSpan S)), q ^ i := by
  classical
  rw [card_filter_univ_eq_natCard_subtype]
  have hequiv :
      {a : Point (ZMod q) d // ∀ p ∈ S, Orthogonal p a} ≃
        {a : Point (ZMod q) d // a.submodule ≤ spanOrthSpace S} :=
    Equiv.setCongr (Set.ext fun a ↦ (submodule_le_spanOrthSpace_iff a S).symm)
  calc
    Nat.card {a : Point (ZMod q) d // ∀ p ∈ S, Orthogonal p a} =
        Nat.card {a : Point (ZMod q) d // a.submodule ≤ spanOrthSpace S} :=
      Nat.card_congr hequiv
    _ = ∑ i ∈ Finset.range (Module.finrank (ZMod q) (spanOrthSpace S)), q ^ i := by
      simpa [Nat.card_zmod] using natCard_pointsIn (spanOrthSpace S)
    _ = ∑ i ∈ Finset.range
        (d - Module.finrank (ZMod q) (pointSpan S)), q ^ i := by
      rw [finrank_spanOrthSpace]

/-- Symmetric-orientation version of the exact orthogonal-to-span count. -/
theorem card_filter_left_orthogonal_to_span_eq_geomSum
    (S : Finset (Point (ZMod q) d)) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal a p).card =
      ∑ i ∈ Finset.range
        (d - Module.finrank (ZMod q) (pointSpan S)), q ^ i := by
  have heq :
      (Finset.univ.filter fun a : Point (ZMod q) d ↦
          ∀ p ∈ S, Orthogonal a p) =
        Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal p a := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h p hp
    · exact (orthogonal_comm p a).mpr (h p hp)
    · exact (orthogonal_comm a p).mpr (h p hp)
  rw [heq, card_filter_orthogonal_to_span_eq_geomSum]

/-- In ambient vector dimension `t+1`, the set of projective points
orthogonal to a rank-`r` span has size at most `2 q^(t-r)`. -/
theorem card_filter_orthogonal_to_span_le_two_mul_pow
    (S : Finset (Point (ZMod q) (t + 1)))
    (hr : Module.finrank (ZMod q) (pointSpan S) = r) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal p a).card ≤
      2 * q ^ (t - r) := by
  have hpred : t + 1 - r - 1 = t - r := by omega
  calc
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal p a).card =
        ∑ i ∈ Finset.range (t + 1 - r), q ^ i := by
      simpa only [hr] using card_filter_orthogonal_to_span_eq_geomSum S
    _ ≤ 2 * q ^ (t - r) := by
      simpa only [hpred] using geomSum_le_two_mul_pow_pred q (t + 1 - r)
        (Fact.out : q.Prime).two_le

/-- The orthogonal-to-span bound in the direct `RankClosure.rank` vocabulary. -/
theorem card_filter_orthogonal_to_rankClosure_le_two_mul_pow
    (S : Finset (Point (ZMod q) (t + 1)))
    (hr : (rankClosure (F := ZMod q) (d := t + 1)).rank S = r) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal p a).card ≤
      2 * q ^ (t - r) := by
  exact card_filter_orthogonal_to_span_le_two_mul_pow S hr

/-- Symmetric-orientation version of the orthogonal-to-span upper bound. -/
theorem card_filter_left_orthogonal_to_span_le_two_mul_pow
    (S : Finset (Point (ZMod q) (t + 1)))
    (hr : Module.finrank (ZMod q) (pointSpan S) = r) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal a p).card ≤
      2 * q ^ (t - r) := by
  rw [card_filter_left_orthogonal_to_span_eq_geomSum, hr]
  have hpred : t + 1 - r - 1 = t - r := by omega
  simpa only [hpred] using geomSum_le_two_mul_pow_pred q (t + 1 - r)
    (Fact.out : q.Prime).two_le

/-- If a span fills the ambient vector space, no projective point is
orthogonal to all of it. -/
theorem card_filter_left_orthogonal_to_span_eq_zero_of_full_rank
    (S : Finset (Point (ZMod q) (t + 1)))
    (hr : Module.finrank (ZMod q) (pointSpan S) = t + 1) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal a p).card = 0 := by
  rw [card_filter_left_orthogonal_to_span_eq_geomSum, hr]
  simp

/-- Uniform annihilator fibre bound, including the full-rank edge case. -/
theorem card_filter_left_orthogonal_to_span_le_if
    (S : Finset (Point (ZMod q) (t + 1)))
    (hr : Module.finrank (ZMod q) (pointSpan S) = r) :
    (Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal a p).card ≤
      if r = t + 1 then 0 else 2 * q ^ (t - r) := by
  split_ifs with hfull
  · exact (card_filter_left_orthogonal_to_span_eq_zero_of_full_rank S
      (hr.trans hfull)).le
  · exact card_filter_left_orthogonal_to_span_le_two_mul_pow S hr

/-! ## Direct container-history consequences -/

/-- A compatible extension has first coordinate orthogonal to every second
coordinate selected by the old history at its new second coordinate. -/
theorem canExtend_orthogonal_generators
    (a b : Point (ZMod q) d)
    (sigma : List (Point (ZMod q) d × Point (ZMod q) d))
    (h : Container.CanExtend Orthogonal (a, b) sigma) :
    ∀ g ∈ Container.generators Orthogonal sigma b, Orthogonal a g := by
  intro g hg
  rw [Container.generators] at hg
  rcases Finset.mem_image.mp hg with ⟨old, hold, rfl⟩
  have hold' := Finset.mem_filter.mp hold
  exact h.2 old (by simpa using hold'.1) hold'.2

/-- The possible first coordinates of a compatible extension over a fixed
second coordinate lie in the annihilator of the selected generator span. -/
theorem card_filter_canExtend_le_if
    (b : Point (ZMod q) (t + 1))
    (sigma : List
      (Point (ZMod q) (t + 1) × Point (ZMod q) (t + 1)))
    (hr : (rankClosure (F := ZMod q) (d := t + 1)).rank
      (Container.generators Orthogonal sigma b) = r) :
    (Finset.univ.filter fun a ↦
        Container.CanExtend Orthogonal (a, b) sigma).card ≤
      if r = t + 1 then 0 else 2 * q ^ (t - r) := by
  let S := Container.generators Orthogonal sigma b
  have hsubset :
      (Finset.univ.filter fun a : Point (ZMod q) (t + 1) ↦
          Container.CanExtend Orthogonal (a, b) sigma) ⊆
        Finset.univ.filter fun a ↦ ∀ p ∈ S, Orthogonal a p := by
    intro a ha
    have ha' := (Finset.mem_filter.mp ha).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, canExtend_orthogonal_generators a b sigma ha'⟩
  exact (Finset.card_le_card hsubset).trans
    (card_filter_left_orthogonal_to_span_le_if S hr)

/-- Closure fibre bound for the generator set selected by a history, stated
using `prefixRank` exactly as in the container argument. -/
theorem card_filter_cl_generators_le_if
    (b : Point (ZMod q) d)
    (sigma : List (Point (ZMod q) d × Point (ZMod q) d))
    (ell : ℕ)
    (hr : Container.prefixRank
      (rankClosure (F := ZMod q) (d := d)) Orthogonal sigma b = ell) :
    (Finset.univ.filter fun x ↦
        (rankClosure (F := ZMod q) (d := d)).Cl x
          (Container.generators Orthogonal sigma b)).card ≤
      if ell = 0 then 0 else 2 * q ^ (ell - 1) := by
  apply card_filter_rankClosure_cl_le_if
  exact hr

/-- Compatible-extension fibre bound stated directly with `prefixRank`. -/
theorem card_filter_canExtend_le_if_of_prefixRank
    (b : Point (ZMod q) (t + 1))
    (sigma : List
      (Point (ZMod q) (t + 1) × Point (ZMod q) (t + 1)))
    (hr : Container.prefixRank
      (rankClosure (F := ZMod q) (d := t + 1)) Orthogonal sigma b = r) :
    (Finset.univ.filter fun a ↦
        Container.CanExtend Orthogonal (a, b) sigma).card ≤
      if r = t + 1 then 0 else 2 * q ^ (t - r) := by
  apply card_filter_canExtend_le_if
  exact hr

end

end Erdos920.SpanCounts
