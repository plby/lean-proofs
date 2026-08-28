import Wikipedia.NoExoticSixSphere.CellExcisionHeight
import Wikipedia.NoExoticSixSphere.CellExcisionFiberSeparation

/-!
# Cell-point excision for a cylinder with smooth local coordinate maps

The actual target map need not take values in a manifold. It suffices
that its two cell-coordinate maps are smooth on the specified open
source regions and correctly describe the selected cell fibers.
The dimension bound chooses the cell points; compactness and the graph
construction then produce the original map's relative homotopy.

Producing these coordinate descriptions by local smoothing, and applying
punctured-cell retractions, are separate steps in homotopy excision.
-/

noncomputable section

open Set Module TopologicalSpace
open scoped unitInterval ContDiff

namespace NoExoticSixSphere.CellExcisionSmoothCylinder

open CellExcisionFiberSeparation

variable {P X E A B : Type}
  [TopologicalSpace P] [CompactSpace P] [T2Space P] [NormalSpace P]
  [TopologicalSpace X] [T1Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem exists_excision_homotopy
    (f : C(I × P, X)) (ι : P → E) (cA : A → X) (cB : B → X)
    (F : ℝ × E → A) (G : ℝ × E → B) (U V : Opens (ℝ × E))
    (hF : ContDiffOn ℝ 1 F U) (hG : ContDiffOn ℝ 1 G V)
    (hd : finrank ℝ E + 2 < finrank ℝ A + finrank ℝ B)
    (O : Set A) (W : Set B) (hO : IsOpen O) (hW : IsOpen W)
    (hneO : O.Nonempty) (hneW : W.Nonempty)
    (hFA : ∀ a ∈ O, ∀ z : I × P, f z = cA a →
      ((z.1 : ℝ), ι z.2) ∈ U ∧ F ((z.1 : ℝ), ι z.2) = a)
    (hGB : ∀ b ∈ W, ∀ z : I × P, f z = cB b →
      ((z.1 : ℝ), ι z.2) ∈ V ∧ G ((z.1 : ℝ), ι z.2) = b)
    (S : Set P) (hS : IsClosed S)
    (hside : ∀ b ∈ W, ∀ t p, p ∈ S → f (t, p) ≠ cB b)
    (htop : ∀ b ∈ W, ∀ p, f (1, p) ≠ cB b)
    (hbottom : ∀ a ∈ O, ∀ p, f (0, p) ≠ cA a) :
    ∃ a ∈ O, ∃ b ∈ W, ∃ g : C(I × P, X), ∃ H : f.Homotopy g,
      (∀ s p, H (s, (1, p)) = f (1, p)) ∧
      (∀ s t p, p ∈ S → H (s, (t, p)) = f (t, p)) ∧
      (∀ s p, H (s, (0, p)) ≠ cA a) ∧ ∀ z, g z ≠ cB b := by
  obtain ⟨a, ha, b, hb, hsep⟩ := exists_disjoint_projected_fibers
    F G U V hF hG hd O W hO hW hneO hneW
  have hA : IsCompact (f ⁻¹' {cA a}) := (isClosed_singleton.preimage f.continuous).isCompact
  have hB : IsCompact (f ⁻¹' {cB b}) := (isClosed_singleton.preimage f.continuous).isCompact
  have hBA : Disjoint (Prod.snd '' (f ⁻¹' {cB b})) (Prod.snd '' (f ⁻¹' {cA a})) := by
    apply Set.disjoint_left.mpr
    intro p hpB hpA
    obtain ⟨⟨t, q⟩, ht, hqp⟩ := hpB
    obtain ⟨⟨s, r⟩, hs, hrp⟩ := hpA
    change q = p at hqp
    change r = p at hrp
    subst q
    subst r
    have hsa := hFA a ha (s, p) hs
    have htb := hGB b hb (t, p) ht
    exact Set.disjoint_left.mp hsep
      ⟨((s : ℝ), ι p), hsa, rfl⟩ ⟨((t : ℝ), ι p), htb, rfl⟩
  have hBS : Disjoint (Prod.snd '' (f ⁻¹' {cB b})) S := by
    apply Set.disjoint_left.mpr
    intro p hp hps
    obtain ⟨⟨t, q⟩, ht, hqp⟩ := hp
    change q = p at hqp
    subst q
    exact hside b hb t p hps ht
  have htime : ∀ z : I × P, f z ∈ ({cB b} : Set X) → z.1 < 1 := by
    rintro ⟨t, p⟩ ht
    by_contra hn
    have he : t = 1 := le_antisymm t.property.2 (le_of_not_gt hn)
    subst t
    exact htop b hb p ht
  obtain ⟨g, H, hHtop, hHside, hHbottom, hg⟩ := CellExcisionGraph.exists_homotopy_avoiding
    f {cA a} {cB b} hA hB S hS hBA hBS htime (hbottom a ha)
  exact ⟨a, ha, b, hb, g, H, hHtop, hHside, hHbottom, hg⟩

end NoExoticSixSphere.CellExcisionSmoothCylinder
