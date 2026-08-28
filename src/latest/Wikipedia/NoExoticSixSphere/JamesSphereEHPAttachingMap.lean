import Wikipedia.NoExoticSixSphere.JamesSphereCellQuotientRange

/-!
# The EHP connecting image is the original cell-attaching image

The original characteristic-cell quotient is now proved bijective in
the required range. With its actual boundary homeomorphism and cubical
suspension, it parametrizes every input of the EHP connecting map.
Thus the connecting image, and the kernel of the original suspension,
are exactly the image induced by the actual second-cell attaching map.
No numerical homotopy-group or Whitehead-product calculation is assumed.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.EHPCell

def attachingMap (n : ℕ) (hn : 0 < n) : C(Sphere (RoundCell.sphereDimension n), Sphere n) :=
  (CellBoundary.attaching n).comp (RoundCell.boundaryHomeomorph n hn : C(_, _))

theorem attachingMap_pole (n : ℕ) (hn : 0 < n) :
    attachingMap n hn (spherePole (RoundCell.sphereDimension n)) = spherePole n := by
  change CellBoundary.attaching n
    (RoundCell.boundaryHomeomorph n hn (spherePole (RoundCell.sphereDimension n))) = _
  rw [RoundCell.boundaryHomeomorph_pole, CellBoundary.attaching_corner]

def attachingHom (n : ℕ) (hn : 0 < n) (d : ℕ) [NeZero d] :=
  HigherHomotopy.mapMonoidHom (N := Fin d) (attachingMap n hn) (attachingMap_pole n hn)

theorem attachingHom_factor (n : ℕ) (hn : 0 < n) (d : ℕ) [NeZero d]
    (c : π_ d (Sphere (RoundCell.sphereDimension n)) (spherePole (RoundCell.sphereDimension n))) :
    HigherHomotopy.map (N := Fin d) (CellBoundary.attaching n) (CellBoundary.attaching_corner n hn)
      (RoundCell.boundaryPiEquiv n hn d c) = attachingHom n hn d c := by
  rw [RoundCell.boundaryPiEquiv_apply, HigherHomotopy.map_comp]
  rfl

def comparisonHom (n : ℕ) (hn : 0 < n) (d : ℕ) [NeZero d] :=
  (CubicalSphereSuspension.hom (d + 1) (n + n)).comp
    ((CellBoundary.quotientHom n hn d).comp (RoundCell.boundaryPiEquiv n hn d).toMonoidHom)

theorem comparisonHom_bijective (n d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n) :
    Function.Bijective (comparisonHom n (by omega) d) := by
  have hq := RoundCell.quotientHom_bijective n (by omega) d (by omega)
  have he := CubicalSphereSuspension.hom_bijective (m := d + 1) (n := n + n) (by omega)
  change Function.Bijective ((CubicalSphereSuspension.hom (d + 1) (n + n)) ∘
    ((CellBoundary.quotientHom n (by omega) d) ∘ RoundCell.boundaryPiEquiv n (by omega) d))
  exact he.comp (hq.comp (RoundCell.boundaryPiEquiv n (by omega) d).bijective)

theorem connecting_comparisonHom (n d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n)
    (c : π_ d (Sphere (RoundCell.sphereDimension n)) (spherePole (RoundCell.sphereDimension n))) :
    EHP.connectingHomMetastable n d hn hdn (comparisonHom n (by omega) d c) =
      attachingHom n (by omega) d c :=
  (CellBoundary.connecting_quotientHom n d hn hdn
    (RoundCell.boundaryPiEquiv n (by omega) d c)).trans (attachingHom_factor n (by omega) d c)

theorem connecting_image_iff (n d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n)
    (x : π_ d (Sphere n) (spherePole n)) :
    (∃ a : π_ (d + 1 + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1)),
      EHP.connectingHomMetastable n d hn hdn a = x) ↔
    ∃ c : π_ d (Sphere (RoundCell.sphereDimension n)) (spherePole (RoundCell.sphereDimension n)),
      attachingHom n (by omega) d c = x := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨c, rfl⟩ := (comparisonHom_bijective n d hn hdn).surjective a
    exact ⟨c, (connecting_comparisonHom n d hn hdn c).symm.trans ha⟩
  · rintro ⟨c, hc⟩
    exact ⟨comparisonHom n (by omega) d c, (connecting_comparisonHom n d hn hdn c).trans hc⟩

theorem suspension_eq_one_iff_attaching (n d : ℕ) [NeZero d]
    (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n) (x : π_ d (Sphere n) (spherePole n)) :
    CubicalSphereSuspension.hom d n x = 1 ↔
      ∃ c : π_ d (Sphere (RoundCell.sphereDimension n)) (spherePole (RoundCell.sphereDimension n)),
        attachingHom n (by omega) d c = x :=
  (EHP.suspension_eq_one_iff_metastable n d hn hdn x).trans (connecting_image_iff n d hn hdn x)

end NoExoticSixSphere.JamesSphere.EHPCell
