import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Algebra.Order.Field

/-!
# Gluing a homotopy using a supported time cutoff

A homotopy of an auxiliary family can be applied to an original family only
where the two initial maps agree. A continuous time cutoff supported in that
agreement region makes the gluing continuous, fixes the original family off
the support, and uses the full endpoint where the cutoff equals one.
-/

open Set Filter unitInterval
open scoped Topology

namespace NoExoticSixSphere.CutoffHomotopyGluing

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def clock (β : C(X, ℝ)) (hβ : ∀ x, β x ∈ I) (tx : I × X) : I :=
  ⟨(tx.1 : ℝ) * β tx.2, unitInterval.mul_mem tx.1.2 (hβ tx.2)⟩

theorem continuous_clock (β : C(X, ℝ)) (hβ : ∀ x, β x ∈ I) : Continuous (clock β hβ) :=
  ((continuous_subtype_val.comp continuous_fst).mul
    (β.continuous.comp continuous_snd)).subtype_mk _

theorem clock_zero (β : C(X, ℝ)) (hβ : ∀ x, β x ∈ I) (x : X) :
    clock β hβ (0, x) = 0 := by
  apply Subtype.ext
  simp [clock]

theorem clock_of_zero (β : C(X, ℝ)) (hβ : ∀ x, β x ∈ I) {x : X} (hx : β x = 0)
    (t : I) : clock β hβ (t, x) = 0 := by
  apply Subtype.ext
  simp [clock, hx]

theorem clock_one_of_one (β : C(X, ℝ)) (hβ : ∀ x, β x ∈ I) {x : X} (hx : β x = 1) :
    clock β hβ (1, x) = 1 := by
  apply Subtype.ext
  simp [clock, hx]

variable {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (p : C(X, Y))
  (β : C(X, ℝ)) (hβ : ∀ x, β x ∈ I) (hAgree : EqOn f p (tsupport β))

noncomputable def map : C(I × X, Y) := by
  classical
  refine ⟨fun tx ↦ if tx.2 ∈ tsupport β then H (clock β hβ tx, tx.2) else p tx.2, ?_⟩
  apply Continuous.if _
    (H.continuous.comp ((continuous_clock β hβ).prodMk continuous_snd))
    (p.continuous.comp continuous_snd)
  intro tx hx
  let A : Set (I × X) := {tx | tx.2 ∈ tsupport β}
  have hA : IsClosed A := (isClosed_tsupport β).preimage continuous_snd
  have htx : tx.2 ∈ tsupport β := hA.closure_subset (frontier_subset_closure hx)
  have hzero : β tx.2 = 0 := by
    by_contra hne
    have ho : IsOpen {tx : I × X | β tx.2 ≠ 0} :=
      isOpen_ne.preimage (β.continuous.comp continuous_snd)
    have hsub : {tx : I × X | β tx.2 ≠ 0} ⊆ A :=
      fun tx hh ↦ subset_tsupport β hh
    exact hx.2 ((ho.subset_interior_iff.mpr hsub) hne)
  change H (clock β hβ (tx.1, tx.2), tx.2) = p tx.2
  rw [clock_of_zero β hβ hzero, H.apply_zero]
  exact hAgree htx

theorem map_of_mem {x : X} (hx : x ∈ tsupport β) (t : I) :
    map H p β hβ hAgree (t, x) = H (clock β hβ (t, x), x) := by
  classical
  simp only [map, ContinuousMap.coe_mk, if_pos hx]

theorem map_of_notMem {x : X} (hx : x ∉ tsupport β) (t : I) :
    map H p β hβ hAgree (t, x) = p x := by
  classical
  simp only [map, ContinuousMap.coe_mk, if_neg hx]

theorem map_zero (x : X) : map H p β hβ hAgree (0, x) = p x := by
  by_cases hx : x ∈ tsupport β
  · rw [map_of_mem H p β hβ hAgree hx, clock_zero, H.apply_zero]
    exact hAgree hx
  · exact map_of_notMem H p β hβ hAgree hx 0

theorem map_one_of_one {x : X} (hx : β x = 1) : map H p β hβ hAgree (1, x) = g x := by
  have hmem : x ∈ tsupport β := subset_tsupport β (by simp [hx])
  rw [map_of_mem H p β hβ hAgree hmem, clock_one_of_one β hβ hx, H.apply_one]

noncomputable def endpoint : C(X, Y) :=
  (map H p β hβ hAgree).comp ⟨fun x ↦ (1, x), continuous_const.prodMk continuous_id⟩

variable {S : Set X}

noncomputable def homotopy (hFixed : ∀ t x, x ∈ S ∩ tsupport β → H (t, x) = f x) :
    ContinuousMap.HomotopyRel p (endpoint H p β hβ hAgree) S where
  toContinuousMap := map H p β hβ hAgree
  map_zero_left := map_zero H p β hβ hAgree
  map_one_left _ := rfl
  prop' t x hx := by
    change map H p β hβ hAgree (t, x) = p x
    by_cases hm : x ∈ tsupport β
    · rw [map_of_mem H p β hβ hAgree hm, hFixed _ x ⟨hx, hm⟩]
      exact hAgree hm
    · exact map_of_notMem H p β hβ hAgree hm t

end NoExoticSixSphere.CutoffHomotopyGluing
