import Wikipedia.NoExoticSixSphere.OnePointProductMap
import Mathlib.Topology.Homotopy.Basic

/-!
# Product compactification preserves actual based homotopies

Joint continuity in time and position is proved by descent through the
actual compact product quotient, not by pointwise continuity of the slices.
The resulting homotopy retains the infinity basepoint throughout.
-/

noncomputable section

open Function Topology
open scoped OnePoint unitInterval

namespace NoExoticSixSphere.OnePointProduct

variable {E F G H : Type*}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [T2Space E] [T2Space F] [T2Space G] [T2Space H]
  [LocallyCompactSpace E] [LocallyCompactSpace F]
  [LocallyCompactSpace G] [LocallyCompactSpace H]

def timeQuotient : C(I × (OnePoint E × OnePoint F), I × OnePoint (E × F)) :=
  ⟨fun z ↦ (z.1, map z.2), continuous_fst.prodMk (continuous_map.comp continuous_snd)⟩

theorem isQuotientMap_timeQuotient :
    IsQuotientMap (timeQuotient (E := E) (F := F)) := by
  apply IsQuotientMap.of_surjective_continuous ?_ timeQuotient.continuous
  rintro ⟨t, z⟩
  obtain ⟨p, hp⟩ := map_surjective z
  exact ⟨(t, p), Prod.ext rfl hp⟩

variable {f₀ f₁ : C(OnePoint E, OnePoint G)} {g₀ g₁ : C(OnePoint F, OnePoint H)}
  (A : f₀.Homotopy f₁) (B : g₀.Homotopy g₁)
  (hA : ∀ t : I, A (t, ∞) = ∞) (hB : ∀ t : I, B (t, ∞) = ∞)

def rawHomotopyMap : C(I × (OnePoint E × OnePoint F), OnePoint (G × H)) :=
  ⟨fun z ↦ map (A (z.1, z.2.1), B (z.1, z.2.2)),
    continuous_map.comp
      ((A.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (B.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))⟩

include hA hB in
theorem rawHomotopyMap_respects (p q : I × (OnePoint E × OnePoint F))
    (h : timeQuotient p = timeQuotient q) : rawHomotopyMap A B p = rawHomotopyMap A B q := by
  rcases p with ⟨t, p⟩
  rcases q with ⟨s, q⟩
  have ht : t = s := congrArg Prod.fst h
  have hp : map p = map q := congrArg Prod.snd h
  subst s
  exact respects_fibers (fun x ↦ A (t, x)) (fun y ↦ B (t, y)) (hA t) (hB t) p q hp

def homotopyMap : C(I × OnePoint (E × F), OnePoint (G × H)) :=
  IsQuotientMap.lift (f := timeQuotient) isQuotientMap_timeQuotient (rawHomotopyMap A B)
    (rawHomotopyMap_respects A B hA hB)

theorem homotopyMap_apply (t : I) (p : OnePoint E × OnePoint F) :
    homotopyMap A B hA hB (t, map p) = map (A (t, p.1), B (t, p.2)) := by
  exact ContinuousMap.congr_fun
    (IsQuotientMap.lift_comp (f := timeQuotient) isQuotientMap_timeQuotient
      (rawHomotopyMap A B) (rawHomotopyMap_respects A B hA hB)) (t, p)

/-- The descended homotopy is a homotopy between the original endpoint product maps. -/
def productHomotopy :
    (productMap f₀ g₀ ((A.apply_zero ∞).symm.trans (hA 0))
      ((B.apply_zero ∞).symm.trans (hB 0))).Homotopy
    (productMap f₁ g₁ ((A.apply_one ∞).symm.trans (hA 1))
      ((B.apply_one ∞).symm.trans (hB 1))) where
  toContinuousMap := homotopyMap A B hA hB
  map_zero_left z := by
    obtain ⟨p, rfl⟩ := map_surjective z
    change homotopyMap A B hA hB (0, map p) = _
    rw [homotopyMap_apply, productMap_apply, A.apply_zero, B.apply_zero]
  map_one_left z := by
    obtain ⟨p, rfl⟩ := map_surjective z
    change homotopyMap A B hA hB (1, map p) = _
    rw [homotopyMap_apply, productMap_apply, A.apply_one, B.apply_one]

theorem productHomotopy_infty (t : I) : productHomotopy A B hA hB (t, ∞) = ∞ := by
  change homotopyMap A B hA hB (t, ∞) = ∞
  simpa [hA t, hB t] using homotopyMap_apply A B hA hB t (∞, ∞)

end NoExoticSixSphere.OnePointProduct
