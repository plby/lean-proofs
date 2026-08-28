import Wikipedia.NoExoticSixSphere.LowCollaredHalf
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The square double of an actual nonnegative half

The zero set of `t(p) - u²` has a continuous projection to the original
nonnegative half and a continuous square-root section. The section is
not claimed smooth at the seam. Its two signed images cover the double.
For a connected half with a nonempty zero seam, the double is connected;
for compact ambient space, it is compact.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.SquareDouble

variable {M : Type} [TopologicalSpace M] (t : C(M, ℝ))

def equation : C(ℝ × M, ℝ) :=
  ⟨fun q ↦ t q.2 - q.1 ^ 2, (t.continuous.comp continuous_snd).sub (continuous_fst.pow 2)⟩

abbrev Space := {q : ℝ × M // equation t q = 0}

abbrev Half := {p : M // 0 ≤ t p}

theorem time_eq_square (q : Space t) : t q.val.2 = q.val.1 ^ 2 :=
  sub_eq_zero.mp q.property

def projection : C(Space t, Half t) where
  toFun q := ⟨q.val.2, (time_eq_square t q).symm ▸ sq_nonneg q.val.1⟩
  continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _

def sectionMap : C(Half t, Space t) where
  toFun p := ⟨(Real.sqrt (t p.val), p.val),
    sub_eq_zero.mpr (Real.sq_sqrt p.property).symm⟩
  continuous_toFun :=
    ((Real.continuous_sqrt.comp (t.continuous.comp continuous_subtype_val)).prodMk
      continuous_subtype_val).subtype_mk _

theorem projection_section (p : Half t) : projection t (sectionMap t p) = p :=
  Subtype.ext rfl

def flip : C(Space t, Space t) where
  toFun q := ⟨(-q.val.1, q.val.2),
    sub_eq_zero.mpr ((time_eq_square t q).trans (neg_sq q.val.1).symm)⟩
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).neg.prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

theorem flip_section_of_time_zero (p : Half t) (hp : t p.val = 0) :
    flip t (sectionMap t p) = sectionMap t p := by
  apply Subtype.ext
  apply Prod.ext
  · change -Real.sqrt (t p.val) = Real.sqrt (t p.val)
    simp only [hp, Real.sqrt_zero, neg_zero]
  · rfl

theorem section_or_flip (q : Space t) :
    q = sectionMap t (projection t q) ∨ q = flip t (sectionMap t (projection t q)) := by
  by_cases hq : 0 ≤ q.val.1
  · left
    apply Subtype.ext
    apply Prod.ext
    · change q.val.1 = Real.sqrt (t q.val.2)
      rw [time_eq_square t q, Real.sqrt_sq_eq_abs, abs_of_nonneg hq]
    · rfl
  · right
    apply Subtype.ext
    apply Prod.ext
    · change q.val.1 = -Real.sqrt (t q.val.2)
      rw [time_eq_square t q, Real.sqrt_sq_eq_abs, abs_of_nonpos (le_of_not_ge hq), neg_neg]
    · rfl

theorem pathConnected [PathConnectedSpace (Half t)] (p : Half t) (hp : t p.val = 0) :
    PathConnectedSpace (Space t) := by
  have hU : IsPathConnected (range (sectionMap t)) :=
    isPathConnected_range (sectionMap t).continuous
  have hV : IsPathConnected (range ((flip t).comp (sectionMap t))) :=
    isPathConnected_range ((flip t).comp (sectionMap t)).continuous
  have hi : (range (sectionMap t) ∩ range ((flip t).comp (sectionMap t))).Nonempty :=
    ⟨sectionMap t p, mem_range_self p, ⟨p, flip_section_of_time_zero t p hp⟩⟩
  have hc : range (sectionMap t) ∪ range ((flip t).comp (sectionMap t)) = univ := by
    apply eq_univ_of_forall
    intro q
    rcases section_or_flip t q with h | h
    · exact Or.inl ⟨projection t q, h.symm⟩
    · exact Or.inr ⟨projection t q, h.symm⟩
  exact pathConnectedSpace_iff_univ.mpr (hc ▸ hU.union hV hi)

theorem compact [CompactSpace M] : CompactSpace (Space t) := by
  let R : ℝ := ‖t‖ + 1
  have hclosed : IsClosed {q : ℝ × M | equation t q = 0} :=
    isClosed_eq (equation t).continuous continuous_const
  have hsub : {q : ℝ × M | equation t q = 0} ⊆ Icc (-R) R ×ˢ univ := by
    intro q hq
    have ht : t q.2 = q.1 ^ 2 := sub_eq_zero.mp hq
    have hb : t q.2 ≤ ‖t‖ := (le_abs_self _).trans (t.norm_coe_le_norm q.2)
    have hn := norm_nonneg t
    have hsq := sq_nonneg (q.1 - 1)
    have hsq' := sq_nonneg (q.1 + 1)
    constructor
    · constructor <;> dsimp [R] <;> nlinarith
    · trivial
  exact isCompact_iff_compactSpace.mp
    ((isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set M))).of_isClosed_subset
      hclosed hsub)

end NoExoticSixSphere.SquareDouble
