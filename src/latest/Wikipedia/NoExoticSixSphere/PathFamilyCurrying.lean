import Mathlib.Topology.Path
import Mathlib.Topology.Homotopy.Basic

/-!
# Fixed-endpoint path families in the native compact-open path space

Currying and uncurrying preserve actual paths and relative homotopies.
No alternate topology is imposed on `Path a b`.
-/

open Set

namespace NoExoticSixSphere.PathFamilies

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {a b : Y}

noncomputable def uncurry (f : C(X, Path a b)) : C(unitInterval × X, Y) where
  toFun z := f z.2 z.1
  continuous_toFun := (Path.continuous_uncurry_iff.mpr f.continuous).comp continuous_swap

theorem uncurry_zero (f : C(X, Path a b)) (x : X) : uncurry f (0, x) = a := (f x).source

theorem uncurry_one (f : C(X, Path a b)) (x : X) : uncurry f (1, x) = b := (f x).target

noncomputable def curry (F : C(unitInterval × X, Y))
    (ha : ∀ x, F (0, x) = a) (hb : ∀ x, F (1, x) = b) : C(X, Path a b) where
  toFun x := {
    toContinuousMap := F.comp ⟨fun t ↦ (t, x), continuous_id.prodMk continuous_const⟩
    source' := ha x
    target' := hb x }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact F.continuous.comp continuous_swap

theorem uncurry_curry (F : C(unitInterval × X, Y))
    (ha : ∀ x, F (0, x) = a) (hb : ∀ x, F (1, x) = b) :
    uncurry (curry F ha hb) = F := by
  apply ContinuousMap.ext
  intro z
  rfl

theorem curry_uncurry (f : C(X, Path a b)) :
    curry (uncurry f) (uncurry_zero f) (uncurry_one f) = f := by
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  rfl

noncomputable def uncurryHomotopy {f g : C(X, Path a b)} {S : Set X}
    (F : f.HomotopyRel g S) :
    (uncurry f).HomotopyRel (uncurry g) {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S} where
  toContinuousMap := (uncurry F.toContinuousMap).comp {
    toFun z := (z.2.1, (z.1, z.2.2))
    continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)) }
  map_zero_left z := by
    change F (0, z.2) z.1 = f z.2 z.1
    rw [F.apply_zero]
  map_one_left z := by
    change F (1, z.2) z.1 = g z.2 z.1
    rw [F.apply_one]
  prop' r z hz := by
    rcases z with ⟨t, x⟩
    change F (r, x) t = f x t
    rcases hz with ht | ht | hx
    · change t = 0 at ht
      subst t
      rw [Path.source, Path.source]
    · change t = 1 at ht
      subst t
      rw [Path.target, Path.target]
    · rw [F.eq_fst r hx]

noncomputable def curryHomotopy {f g : C(X, Path a b)} {S : Set X}
    (F : (uncurry f).HomotopyRel (uncurry g) {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S}) :
    f.HomotopyRel g S := by
  let P : C(unitInterval × (unitInterval × X), Y) := F.toContinuousMap.comp {
    toFun z := (z.2.1, (z.1, z.2.2))
    continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)) }
  have hPa (z : unitInterval × X) : P (0, z) = a :=
    (F.eq_fst z.1 (Or.inl rfl)).trans (uncurry_zero f z.2)
  have hPb (z : unitInterval × X) : P (1, z) = b :=
    (F.eq_fst z.1 (Or.inr (Or.inl rfl))).trans (uncurry_one f z.2)
  exact {
    toContinuousMap := curry P hPa hPb
    map_zero_left := by
      intro x
      apply Path.ext
      funext t
      exact F.apply_zero (t, x)
    map_one_left := by
      intro x
      apply Path.ext
      funext t
      exact F.apply_one (t, x)
    prop' := by
      intro r x hx
      apply Path.ext
      funext t
      exact F.eq_fst r (Or.inr (Or.inr hx)) }

theorem homotopicRel_iff_uncurry (f g : C(X, Path a b)) (S : Set X) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty ((uncurry f).HomotopyRel (uncurry g) {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S}) :=
  ⟨fun ⟨F⟩ ↦ ⟨uncurryHomotopy F⟩, fun ⟨F⟩ ↦ ⟨curryHomotopy F⟩⟩

end NoExoticSixSphere.PathFamilies
