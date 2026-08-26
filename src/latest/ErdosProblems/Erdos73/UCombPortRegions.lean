import ErdosProblems.Erdos73.UCombGeometry
import ErdosProblems.Erdos73.NoncrossingLeftRegions

/-! Pairwise disjoint two-sided port combs in cyclic boundary order. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Finset

variable {M c r L : ℕ} {U : Type*}

def twoSidePortRank (nails : Fin M → ElementaryWallVertex c r)
    (leftSide : Fin M → Bool) (L : ℕ) (i : Fin M) : ℕ :=
  if leftSide i then (nails i).val.1.val else 2 * uCombBase L M - (nails i).val.1.val

def sidePortRows (label : Fin M → U) (nails : Fin M → ElementaryWallVertex c r)
    (leftSide : Fin M → Bool) (side : Bool) (u : U) : Finset ℕ :=
  ((portWordFiber label u).filter (fun i => leftSide i = side)).image
    (fun i => (nails i).val.1.val)

def portWordUComb (label : Fin M → U) (hsurj : Function.Surjective label)
    (nails : Fin M → ElementaryWallVertex c r) (leftSide : Fin M → Bool) (L : ℕ) (u : U) :
    Finset (ElementaryWallVertex c r) :=
  rectangularUComb (sidePortRows label nails leftSide true u)
    (sidePortRows label nails leftSide false u) L M
    (twoSidePortRank nails leftSide L (portWordFirst label hsurj u))
    (twoSidePortRank nails leftSide L (portWordLast label hsurj u))
    (portWordSpine label hsurj u)

theorem twoSidePortRank_extreme (nails : Fin M → ElementaryWallVertex c r)
    (leftSide : Fin M → Bool) (hrows : ∀ i, (nails i).val.1.val ≤ L) (i : Fin M) :
    twoSidePortRank nails leftSide L i ≤ L ∨
      2 * uCombBase L M - L ≤ twoSidePortRank nails leftSide L i := by
  have hi := hrows i
  dsimp only [twoSidePortRank]
  split_ifs <;> omega

theorem sidePortRows_avoids_nested {label : Fin M → U} (hsurj : Function.Surjective label)
    (hNC : NoncrossingPortWord label) (nails : Fin M → ElementaryWallVertex c r)
    (leftSide : Fin M → Bool) (hmono : StrictMono (twoSidePortRank nails leftSide L))
    {u v : U} (huv : u ≠ v)
    (hlo : portWordFirst label hsurj u < portWordFirst label hsurj v)
    (side : Bool) : ∀ s ∈ sidePortRows label nails leftSide side u,
      ¬ (twoSidePortRank nails leftSide L (portWordFirst label hsurj v) ≤
          (if side then s else 2 * uCombBase L M - s) ∧
        (if side then s else 2 * uCombBase L M - s) ≤
          twoSidePortRank nails leftSide L (portWordLast label hsurj v)) := by
  intro s hs hb
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hs
  obtain ⟨hi, hside⟩ := mem_filter.mp hi
  have hrank : twoSidePortRank nails leftSide L i =
      (if side then (nails i).val.1.val else 2 * uCombBase L M - (nails i).val.1.val) := by
    rw [twoSidePortRank, hside]
  rw [← hrank] at hb
  exact hNC.outer_block_avoids_inner huv hlo (portWordFirst_label label hsurj u)
    (portWordFirst_label label hsurj v) (portWordLast_label label hsurj v)
    ((mem_portWordFiber label u i).mp hi)
    ⟨hmono.le_iff_le.mp hb.1, hmono.le_iff_le.mp hb.2⟩

theorem portWordUComb_disjoint {label : Fin M → U} (hsurj : Function.Surjective label)
    (hNC : NoncrossingPortWord label) (nails : Fin M → ElementaryWallVertex c r)
    (leftSide : Fin M → Bool) (hmono : StrictMono (twoSidePortRank nails leftSide L))
    (hrows : ∀ i, (nails i).val.1.val ≤ L) (hc : 2 * M + 3 ≤ c) :
    Pairwise (fun u v => Disjoint (portWordUComb label hsurj nails leftSide L u)
      (portWordUComb label hsurj nails leftSide L v)) := by
  intro u v huv
  have hcases := hNC.interval_cases huv (portWordFirst_le_last label hsurj u)
    (portWordFirst_le_last label hsurj v) (portWordFirst_label label hsurj u)
    (portWordLast_label label hsurj u) (portWordFirst_label label hsurj v)
    (portWordLast_label label hsurj v)
  have hj := portWordSpine_pos label hsurj
  have hjM := portWordSpine_le label hsurj
  have hext := twoSidePortRank_extreme nails leftSide hrows
  rcases hcases with hh | hh | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact rectangularUComb_disjoint_series hc (hj u) (hjM u) (hj v) (hjM v)
      (hext _) (hext _) (hext _) (hext _) (hmono hh)
  · exact (rectangularUComb_disjoint_series hc (hj v) (hjM v) (hj u) (hjM u)
      (hext _) (hext _) (hext _) (hext _) (hmono hh)).symm
  · apply rectangularUComb_disjoint_nested hc (hjM u) (hjM v)
      (portWordSpine_lt_of_nested label hsurj hlo hhi)
    · simpa using sidePortRows_avoids_nested hsurj hNC nails leftSide hmono huv hlo true
    · simpa using sidePortRows_avoids_nested hsurj hNC nails leftSide hmono huv hlo false
  · apply Disjoint.symm
    apply rectangularUComb_disjoint_nested hc (hjM v) (hjM u)
      (portWordSpine_lt_of_nested label hsurj hlo hhi)
    · simpa using sidePortRows_avoids_nested hsurj hNC nails leftSide hmono huv.symm hlo true
    · simpa using sidePortRows_avoids_nested hsurj hNC nails leftSide hmono huv.symm hlo false

theorem nail_mem_portWordUComb (label : Fin M → U) (hsurj : Function.Surjective label)
    (nails : Fin M → ElementaryWallVertex c r) (leftSide : Fin M → Bool)
    (hmono : StrictMono (twoSidePortRank nails leftSide L))
    (hrows : ∀ i, (nails i).val.1.val ≤ L)
    (hleft : ∀ i, leftSide i = true → (nails i).val.2.val ≤ 1)
    (hright : ∀ i, leftSide i = false → 2 * (c - 1) ≤ (nails i).val.2.val)
    (i : Fin M) : nails i ∈ portWordUComb label hsurj nails leftSide L (label i) := by
  have hib := portWord_bounds label hsurj (show label i = label i from rfl)
  have hmin := hmono.monotone hib.1
  have hmax := hmono.monotone hib.2
  have hmem (side : Bool) (hi : leftSide i = side) :
      (nails i).val.1.val ∈ sidePortRows label nails leftSide side (label i) :=
    mem_image.mpr ⟨i, mem_filter.mpr ⟨(mem_portWordFiber _ _ _).mpr rfl, hi⟩, rfl⟩
  change nails i ∈ rectangularUComb _ _ _ _ _ _ _
  rw [mem_rectangularUComb]
  cases hi : leftSide i
  · have hcol := hright i hi
    simp only [twoSidePortRank, hi, Bool.false_eq_true, if_false] at hmin hmax
    exact Or.inr (Or.inl ⟨hmem false hi, hrows i, hmin, hmax, by omega⟩)
  · have hcol := hleft i hi
    simp only [twoSidePortRank, hi, ite_true] at hmin hmax
    exact Or.inl ⟨hmem true hi, hrows i, hmin, hmax, by omega⟩

end
end Erdos73
