import Wikipedia.HopfProblem.CuspCentralHomologyEdgeBranches
import Wikipedia.HopfProblem.CuspCentralHomologyCornerOrbits

/-!
# No additional identifications between the three open edge cylinders

The two branch labels of an open edge determine its direction up to sign.
Of the first three hexagon rays none are negatives of one another. Thus
two projected open edge points can agree only along the same original
edge, using the zero lattice translation; their remaining phase is then
exactly the determinant character.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace ToricComponent CuspRetraction CuspCollapse

theorem hexagonRay_first_half_ne_neg (k l : Fin 6) (hk : k.val < 3) (hl : l.val < 3) :
    hexagonRay k ≠ -hexagonRay l := by
  have h : ∀ k l : Fin 6, k.val < 3 → l.val < 3 → hexagonRay k ≠ -hexagonRay l := by
    decide
  exact h k l hk hl

/-- The unordered branch pair on one of the three chosen edges admits
no nonzero translation to another chosen pair. -/
theorem hexagonPair_image_add_eq (k l : Fin 6) (hk : k.val < 3) (hl : l.val < 3)
    (d : Fin 2 → ℤ)
    (h : ({0, hexagonRay k} : Set (Fin 2 → ℤ)) =
      (fun w => w + d) '' {0, hexagonRay l}) : k = l ∧ d = 0 := by
  simp only [image_insert_eq, image_singleton, zero_add, pair_eq_pair_iff] at h
  rcases h with ⟨hd, hn⟩ | ⟨hd, hn⟩
  · subst d
    exact ⟨hexagonRay_injective (by simpa only [add_zero] using hn), rfl⟩
  · have hneg : hexagonRay k = -hexagonRay l := by
      funext i
      have hd' := congrFun hd i
      have hn' := congrFun hn i
      change (0 : ℤ) = hexagonRay l i + d i at hd'
      change hexagonRay k i = d i at hn'
      change hexagonRay k i = -hexagonRay l i
      omega
    exact (hexagonRay_first_half_ne_neg k l hk hl hneg).elim

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The original central quotient map on a single actual edge cylinder. -/
def projectedEdgeCylinder (k : Fin 6) (p : unitInterval × Circle) :
    QuotientCentralFibre C ε := centralProject C ε hε (edgeCylinder (C 0) k p)

theorem projectedEdgeCylinder_continuous (k : Fin 6) :
    Continuous (projectedEdgeCylinder C ε hε k) :=
  (centralProject_continuous C ε hε).comp (edgeCylinder_continuous (C 0) k)

/-- Equality of actual quotient points preserves the number of original branches. -/
theorem centralProject_branchCount_eq {x y : CentralFibre}
    (h : centralProject C ε hε x = centralProject C ε hε y) :
    branchCount (x : Space) = branchCount (y : Space) := by
  obtain ⟨v, hv⟩ := (centralProject_eq_iff C ε hε x y).mp h
  rw [← hv, branchCount_twistedTranslate]

theorem projectedEdgeCylinder_eq_iff_of_interior (k l : Fin 6)
    (hk : k.val < 3) (hl : l.val < 3) (s t : unitInterval)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (a b : Circle) :
    projectedEdgeCylinder C ε hε k (s, a) = projectedEdgeCylinder C ε hε l (t, b) ↔
      k = l ∧ s = t ∧ a = b := by
  constructor
  · intro he
    obtain ⟨v, hv⟩ := (centralProject_eq_iff C ε hε _ _).mp he
    have hb := congrArg branchVertices hv
    rw [branchVertices_twistedTranslate, edgeCylinder_branchVertices (C 0) l (t, b) ht0 ht1,
      edgeCylinder_branchVertices (C 0) k (s, a) hs0 hs1] at hb
    obtain ⟨hkl, hv0⟩ := hexagonPair_image_add_eq k l hk hl (cuspVector v) hb.symm
    have hzero : v = 0 := cuspVector_injective (hv0.trans cuspVector_zero.symm)
    subst v
    subst l
    rw [twistedTranslate_zero] at hv
    exact ⟨rfl, (edgeCylinder_eq_iff_of_interior (C 0) k s t hs0 hs1 a b).mp
      (Subtype.ext hv.symm)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- An open-edge point cannot become a triple point in the actual quotient. -/
theorem projectedEdgeCylinder_interior_ne_corner (k : Fin 6) (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (a : Circle) (j : Fin 6) :
    projectedEdgeCylinder C ε hε k (t, a) ≠ cornerPoint C ε hε j := by
  intro he
  have hb := centralProject_branchCount_eq C ε hε he
  rw [edgeCylinder_branchCount (C 0) k (t, a) ht0 ht1,
    cornerOrigin_coe, branchCount_inclusion, ToricCharts.zeroCount_zero] at hb
  omega

end Wikipedia.HopfProblem.CuspCentralHomology
