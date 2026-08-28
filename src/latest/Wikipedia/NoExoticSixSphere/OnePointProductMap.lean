import Wikipedia.NoExoticSixSphere.OnePointProductQuotient
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Products of based maps on actual one-point compactifications

A pair of continuous maps preserving infinity descends through the product
compactification quotient. This constructs a genuine continuous map on the
one-point compactification of the product, with its exact finite formula.
In particular, taking one factor to be the identity adds a normal coordinate.
-/

noncomputable section

open Function Topology
open scoped OnePoint

namespace NoExoticSixSphere.OnePointProduct

variable {E F G H : Type*}

theorem mapped_infty (f : OnePoint E → OnePoint G) (g : OnePoint F → OnePoint H)
    (hf : f ∞ = ∞) (hg : g ∞ = ∞) (p : OnePoint E × OnePoint F) (hp : map p = ∞) :
    map (f p.1, g p.2) = ∞ := by
  rcases (map_eq_infty_iff p).mp hp with h | h
  · rw [h, hf, map_infty_left]
  · rw [h, hg, map_infty_right]

theorem respects_fibers (f : OnePoint E → OnePoint G) (g : OnePoint F → OnePoint H)
    (hf : f ∞ = ∞) (hg : g ∞ = ∞) (p q : OnePoint E × OnePoint F)
    (h : map p = map q) : map (f p.1, g p.2) = map (f q.1, g q.2) := by
  by_cases hp : map p = ∞
  · exact (mapped_infty f g hf hg p hp).trans
      (mapped_infty f g hf hg q (h.symm.trans hp)).symm
  · obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.mp hp
    obtain ⟨hp₁, hp₂⟩ := (map_eq_coe_iff p v).mp hv.symm
    obtain ⟨hq₁, hq₂⟩ := (map_eq_coe_iff q v).mp (h.symm.trans hv.symm)
    rw [hp₁, hp₂, hq₁, hq₂]

variable [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [T2Space E] [T2Space F] [T2Space G] [T2Space H]
  [LocallyCompactSpace E] [LocallyCompactSpace F]
  [LocallyCompactSpace G] [LocallyCompactSpace H]

def productMap (f : C(OnePoint E, OnePoint G)) (g : C(OnePoint F, OnePoint H))
    (hf : f ∞ = ∞) (hg : g ∞ = ∞) : C(OnePoint (E × F), OnePoint (G × H)) :=
  IsQuotientMap.lift (f := continuousMap (E := E) (F := F)) isQuotientMap_map
    ((continuousMap (E := G) (F := H)).comp (f.prodMap g))
    (respects_fibers f g hf hg)

theorem productMap_apply (f : C(OnePoint E, OnePoint G)) (g : C(OnePoint F, OnePoint H))
    (hf : f ∞ = ∞) (hg : g ∞ = ∞) (p : OnePoint E × OnePoint F) :
    productMap f g hf hg (map p) = map (f p.1, g p.2) := by
  have h := IsQuotientMap.lift_comp (f := continuousMap (E := E) (F := F))
    isQuotientMap_map ((continuousMap (E := G) (F := H)).comp (f.prodMap g))
    (respects_fibers f g hf hg)
  exact ContinuousMap.congr_fun h p

@[simp]
theorem productMap_coe
    (f : C(OnePoint E, OnePoint G)) (g : C(OnePoint F, OnePoint H))
    (hf : f ∞ = ∞) (hg : g ∞ = ∞) (x : E) (y : F) :
    productMap f g hf hg ((x, y) : OnePoint (E × F)) = map (f ↑x, g ↑y) := by
  simpa using productMap_apply f g hf hg (↑x, ↑y)

@[simp]
theorem productMap_infty
    (f : C(OnePoint E, OnePoint G)) (g : C(OnePoint F, OnePoint H))
    (hf : f ∞ = ∞) (hg : g ∞ = ∞) : productMap f g hf hg ∞ = ∞ := by
  simpa [hf, hg] using productMap_apply f g hf hg (∞, ∞)

theorem productMap_id :
    productMap (ContinuousMap.id (OnePoint E)) (ContinuousMap.id (OnePoint F)) rfl rfl =
      ContinuousMap.id (OnePoint (E × F)) := by
  ext z
  obtain ⟨p, rfl⟩ := map_surjective z
  exact productMap_apply _ _ rfl rfl p

omit [T2Space E] [T2Space F] [LocallyCompactSpace E] [LocallyCompactSpace F] in
theorem map_swap (p : OnePoint E × OnePoint F) :
    (Homeomorph.prodComm E F).onePointCongr (map p) = map (p.2, p.1) := by
  rcases p with ⟨x, y⟩
  induction x using OnePoint.rec with
  | infty =>
    rw [map_infty_left, map_infty_right]
    rfl
  | coe x =>
    induction y using OnePoint.rec with
    | infty =>
      rw [map_infty_right, map_infty_left]
      rfl
    | coe y =>
      rw [map_coe, map_coe]
      rfl

theorem productMap_swap
    (f : C(OnePoint E, OnePoint G)) (g : C(OnePoint F, OnePoint H))
    (hf : f ∞ = ∞) (hg : g ∞ = ∞) (z : OnePoint (E × F)) :
    productMap g f hg hf ((Homeomorph.prodComm E F).onePointCongr z) =
      (Homeomorph.prodComm G H).onePointCongr (productMap f g hf hg z) := by
  obtain ⟨p, rfl⟩ := map_surjective z
  rw [map_swap, productMap_apply, productMap_apply, map_swap]

end NoExoticSixSphere.OnePointProduct
