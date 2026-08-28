import Wikipedia.NoExoticSixSphere.CircleCylinderCollarWindow
import Wikipedia.NoExoticSixSphere.CircleCylinderEndpointSum

/-!
# The explicit closed collar map retains both original endpoint fibers

Each height-coordinate branch is paired with its original endpoint fiber.
Their sum parametrizes precisely the native double's closed time band,
injectively and continuously, with the literal time coordinate retained.
-/

noncomputable section

open Function Set
open scoped Manifold

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def leftCollarMap : C(CollarInterval d × {x : Sphere m // d.leftMap x = b}, Fiber d) where
  toFun p := ⟨(collarBranch (collarWidth_lt_one d) true p.1, p.2.val),
    (map_left_collarBranch d p.1 p.2.val).trans p.2.property⟩
  continuous_toFun := (((continuous_collarBranch (collarWidth_lt_one d) true).comp
    continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def rightCollarMap : C(CollarInterval d × {x : Sphere m // d.rightMap x = b}, Fiber d) where
  toFun p := ⟨(collarBranch (collarWidth_lt_one d) false p.1, p.2.val),
    (map_right_collarBranch d p.1 p.2.val).trans p.2.property⟩
  continuous_toFun := (((continuous_collarBranch (collarWidth_lt_one d) false).comp
    continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def closedCollarMap : C(CollarInterval d × Endpoints d, Fiber d) :=
  (⟨Sum.elim (leftCollarMap d) (rightCollarMap d),
    (leftCollarMap d).continuous.sumElim (rightCollarMap d).continuous⟩ :
      C((CollarInterval d × {x : Sphere m // d.leftMap x = b}) ⊕
        (CollarInterval d × {x : Sphere m // d.rightMap x = b}), Fiber d)).comp
      ⟨Homeomorph.prodSumDistrib, Homeomorph.prodSumDistrib.continuous⟩

theorem closedCollarMap_inl (s : CollarInterval d) (x : {x : Sphere m // d.leftMap x = b}) :
    closedCollarMap d (s, Sum.inl x) = leftCollarMap d (s, x) := rfl

theorem closedCollarMap_inr (s : CollarInterval d) (x : {x : Sphere m // d.rightMap x = b}) :
    closedCollarMap d (s, Sum.inr x) = rightCollarMap d (s, x) := rfl

theorem time_closedCollarMap (p : CollarInterval d × Endpoints d) :
    time d (closedCollarMap d p) = p.1.val := by
  rcases p with ⟨s, x | x⟩ <;> rfl

theorem closedCollarMap_injective : Injective (closedCollarMap d) := by
  rintro ⟨s, x⟩ ⟨t, y⟩ h
  have hs : s = t := by
    apply Subtype.ext
    have he := congrArg (time d) h
    simpa only [time_closedCollarMap] using he
  apply Prod.ext hs
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      exact congrArg Sum.inl (Subtype.ext (congrArg (fun p : Fiber d ↦ p.val.2) h))
    | inr y =>
      exact (collarBranch_left_ne_right (collarWidth_lt_one d) s t
        (congrArg (fun p : Fiber d ↦ p.val.1) h)).elim
  | inr x =>
    cases y with
    | inl y =>
      exact (collarBranch_left_ne_right (collarWidth_lt_one d) t s
        (congrArg (fun p : Fiber d ↦ p.val.1) h).symm).elim
    | inr y =>
      exact congrArg Sum.inr (Subtype.ext (congrArg (fun p : Fiber d ↦ p.val.2) h))

theorem closedCollarMap_covers (p : Fiber d)
    (hp : time d p ∈ Icc (-collarWidth d) (collarWidth d)) :
    ∃ q : CollarInterval d × Endpoints d, closedCollarMap d q = p := by
  let s : CollarInterval d := ⟨time d p, hp⟩
  by_cases hh : 0 ≤ p.val.1.val 0
  · have hc : collarBranch (collarWidth_lt_one d) true s = p.val.1 :=
      collarBranch_left_inverse (collarWidth_lt_one d) p.val.1 hp hh
    have hx : d.leftMap p.val.2 = b := by
      rw [← map_left_collarBranch d s, hc]
      exact p.property
    refine ⟨(s, Sum.inl ⟨p.val.2, hx⟩), Subtype.ext (Prod.ext hc rfl)⟩
  · have hc : collarBranch (collarWidth_lt_one d) false s = p.val.1 :=
      collarBranch_right_inverse (collarWidth_lt_one d) p.val.1 hp (le_of_not_ge hh)
    have hx : d.rightMap p.val.2 = b := by
      rw [← map_right_collarBranch d s, hc]
      exact p.property
    refine ⟨(s, Sum.inr ⟨p.val.2, hx⟩), Subtype.ext (Prod.ext hc rfl)⟩

theorem closedCollarMap_zero (x : Endpoints d) :
    closedCollarMap d
      (⟨0, neg_nonpos.mpr (collarWidth_pos d).le, (collarWidth_pos d).le⟩, x) =
        endpointsMap d x := by
  cases x with
  | inl x =>
    apply Subtype.ext
    exact Prod.ext (collarBranch_zero (collarWidth_lt_one d) _ true) rfl
  | inr x =>
    apply Subtype.ext
    exact Prod.ext (collarBranch_zero (collarWidth_lt_one d) _ false) rfl

end NoExoticSixSphere.CircleCylinder
