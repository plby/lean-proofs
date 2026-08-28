import Wikipedia.NoExoticSixSphere.OnePointProductMap
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Exact coordinate naturality and associativity of product compactification

These identities hold on the whole compactification, including infinity.
They compare actual descended product maps, not assigned homotopy classes.
-/

noncomputable section

open scoped OnePoint

namespace NoExoticSixSphere.OnePointProduct

section Pointwise

variable {E F G H K : Type*}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
  [TopologicalSpace H] [TopologicalSpace K]

theorem map_prodCongr (e : E ≃ₜ G) (f : F ≃ₜ H) (x : OnePoint E) (y : OnePoint F) :
    (e.prodCongr f).onePointCongr (map (x, y)) =
      map (e.onePointCongr x, f.onePointCongr y) := by
  induction x using OnePoint.rec with
  | infty =>
    rw [map_infty_left]
    change ∞ = map (∞, f.onePointCongr y)
    rw [map_infty_left]
  | coe x =>
    induction y using OnePoint.rec with
    | infty =>
      rw [map_infty_right]
      change ∞ = map (e.onePointCongr (↑x), ∞)
      rw [map_infty_right]
    | coe y =>
      rw [map_coe]
      change (↑(e x, f y) : OnePoint (G × H)) = map (↑(e x), ↑(f y))
      rw [map_coe]

theorem map_assoc (x : OnePoint E) (y : OnePoint F) (z : OnePoint K) :
    (Homeomorph.prodAssoc E F K).onePointCongr (map (map (x, y), z)) =
      map (x, map (y, z)) := by
  induction x using OnePoint.rec with
  | infty => simp only [map_infty_left]; rfl
  | coe x =>
    induction y using OnePoint.rec with
    | infty =>
      rw [map_infty_right, map_infty_left, map_infty_left, map_infty_right]
      rfl
    | coe y =>
      induction z using OnePoint.rec with
      | infty => rw [map_infty_right, map_infty_right, map_infty_right]; rfl
      | coe z => simp only [map_coe]; rfl

theorem onePoint_refl (x : OnePoint E) : (Homeomorph.refl E).onePointCongr x = x := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x => rfl

theorem onePoint_trans_apply (e : E ≃ₜ F) (f : F ≃ₜ G) (x : OnePoint E) :
    (e.trans f).onePointCongr x = f.onePointCongr (e.onePointCongr x) := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x => rfl

end Pointwise

section Products

variable {E F G H T U : Type*}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [TopologicalSpace T] [TopologicalSpace U]
  [T2Space E] [T2Space F] [T2Space G] [T2Space H] [T2Space T] [T2Space U]
  [LocallyCompactSpace E] [LocallyCompactSpace F]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [LocallyCompactSpace T] [LocallyCompactSpace U]

def addFactor (f : C(OnePoint E, OnePoint F)) (hf : f ∞ = ∞) (T : Type*)
    [TopologicalSpace T] [T2Space T] [LocallyCompactSpace T] :
    C(OnePoint (E × T), OnePoint (F × T)) :=
  productMap f (ContinuousMap.id (OnePoint T)) hf rfl

theorem addFactor_infty (f : C(OnePoint E, OnePoint F)) (hf : f ∞ = ∞) :
    addFactor f hf T ∞ = ∞ := productMap_infty _ _ _ _

theorem addFactor_map (f : C(OnePoint E, OnePoint F)) (hf : f ∞ = ∞)
    (x : OnePoint E) (t : OnePoint T) : addFactor f hf T (map (x, t)) = map (f x, t) :=
  productMap_apply _ _ _ _ (x, t)

theorem addFactor_left_coordinates (f : C(OnePoint E, OnePoint F)) (hf : f ∞ = ∞)
    (g : C(OnePoint G, OnePoint H)) (hg : g ∞ = ∞)
    (e : E ≃ₜ G) (d : F ≃ₜ H) (h : ∀ x, d.onePointCongr (f x) = g (e.onePointCongr x))
    (z : OnePoint (E × T)) :
    (d.prodCongr (Homeomorph.refl T)).onePointCongr (addFactor f hf T z) =
      addFactor g hg T ((e.prodCongr (Homeomorph.refl T)).onePointCongr z) := by
  obtain ⟨⟨x, t⟩, rfl⟩ := map_surjective z
  rw [addFactor_map, map_prodCongr, map_prodCongr, addFactor_map, h]

theorem addFactor_right_coordinates (f : C(OnePoint E, OnePoint F)) (hf : f ∞ = ∞)
    (e : T ≃ₜ U) (z : OnePoint (E × T)) :
    ((Homeomorph.refl F).prodCongr e).onePointCongr (addFactor f hf T z) =
      addFactor f hf U (((Homeomorph.refl E).prodCongr e).onePointCongr z) := by
  obtain ⟨⟨x, t⟩, rfl⟩ := map_surjective z
  rw [addFactor_map, map_prodCongr, map_prodCongr, addFactor_map]
  rw [onePoint_refl, onePoint_refl]

theorem addFactor_assoc (f : C(OnePoint E, OnePoint F)) (hf : f ∞ = ∞)
    (z : OnePoint ((E × T) × U)) :
    (Homeomorph.prodAssoc F T U).onePointCongr
        (addFactor (addFactor f hf T) (addFactor_infty f hf) U z) =
      addFactor f hf (T × U) ((Homeomorph.prodAssoc E T U).onePointCongr z) := by
  obtain ⟨⟨p, u⟩, rfl⟩ := map_surjective z
  obtain ⟨⟨x, t⟩, rfl⟩ := map_surjective p
  rw [addFactor_map, addFactor_map, map_assoc, map_assoc, addFactor_map]

theorem addFactor_unique [Unique T] (f : C(OnePoint E, OnePoint F)) (hf : f ∞ = ∞)
    (z : OnePoint (E × T)) :
    (Homeomorph.prodUnique F T).onePointCongr (addFactor f hf T z) =
      f ((Homeomorph.prodUnique E T).onePointCongr z) := by
  induction z using OnePoint.rec with
  | infty =>
    rw [addFactor_infty]
    change ∞ = f ∞
    exact hf.symm
  | coe p =>
    have hm := addFactor_map (T := T) f hf (↑p.1) (↑p.2)
    rw [map_coe] at hm
    change addFactor f hf T (↑p) = map (f ↑p.1, ↑p.2) at hm
    rw [hm]
    change (Homeomorph.prodUnique F T).onePointCongr (map (f ↑p.1, ↑p.2)) = f ↑p.1
    induction h : f (↑p.1) using OnePoint.rec with
    | infty => rw [map_infty_left]; rfl
    | coe v => rw [map_coe]; rfl

end Products

end NoExoticSixSphere.OnePointProduct
