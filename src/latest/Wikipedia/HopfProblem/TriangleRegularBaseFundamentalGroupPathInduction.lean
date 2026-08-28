import Wikipedia.HopfProblem.SimplyConnectedCover

/-!
# Path-class induction over an arbitrary open cover

A property of endpoint-preserving path homotopy classes holds globally
if it holds for constant paths, is closed under concatenation, and holds
for paths contained in each member of an open cover.  The proof uses
finite subdivision of the parameter interval and the actual homotopy
between consecutive concatenated subpaths and the combined subpath.
No simple-connectivity or connectedness assumption is needed.
-/

noncomputable section

open Set Path.Homotopic.Quotient
open scoped unitInterval

namespace Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroup

variable {X : Type*} [TopologicalSpace X]

/-- A property indexed by both endpoints transports along endpoint equalities. -/
theorem pathClass_property_cast
    (P : ∀ {x y : X}, Path.Homotopic.Quotient x y → Prop)
    {x y x' y' : X} (q : Path.Homotopic.Quotient x y)
    (hx : x' = x) (hy : y' = y) (hq : P q) : P (q.cast hx hy) := by
  cases hx
  cases hy
  simpa using hq

/-- Induction on path homotopy classes using an arbitrary open cover.
Only local paths, constant paths, and concatenation need to be checked. -/
theorem pathClass_induction_of_open_cover {ι : Type*} (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    (P : ∀ {x y : X}, Path.Homotopic.Quotient x y → Prop)
    (h_refl : ∀ x, P (refl x))
    (h_trans : ∀ {x y z : X} {p : Path.Homotopic.Quotient x y}
      {q : Path.Homotopic.Quotient y z}, P p → P q → P (p.trans q))
    (h_local : ∀ i {x y : X} (p : Path x y), range p ⊆ U i → P (mk p)) :
    ∀ {x y : X} (q : Path.Homotopic.Quotient x y), P q := by
  intro x y q
  obtain ⟨p⟩ := q
  have hpre : univ ⊆ ⋃ i, p ⁻¹' U i := by
    rw [← preimage_iUnion, hcover, preimage_univ]
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => (hopen i).preimage p.continuous) hpre
  have hwalk : ∀ k : ℕ, P (mk (p.subpath 0 (t k))) := by
    intro k
    induction k with
    | zero =>
      rw [ht0, Path.subpath_self, mk_refl]
      exact h_refl (p 0)
    | succ k ih =>
      obtain ⟨i, hi⟩ := hsub k
      have hmem : range (p.subpath (t k) (t (k + 1))) ⊆ U i := by
        rw [p.range_subpath_of_le _ _ (hmono (Nat.le_succ k))]
        exact image_subset_iff.mpr hi
      have hconcat : trans (mk (p.subpath 0 (t k)))
          (mk (p.subpath (t k) (t (k + 1)))) = mk (p.subpath 0 (t (k + 1))) := by
        rw [← mk_trans, eq]
        exact ⟨Path.Homotopy.subpathTransSubpath p 0 (t k) (t (k + 1))⟩
      rw [← hconcat]
      exact h_trans ih (h_local i _ hmem)
  have hfull := hwalk n
  rw [hn n le_rfl] at hfull
  have hp : (mk (p.subpath 0 1)).cast p.source.symm p.target.symm = mk p := by
    rw [← mk_cast, Path.subpath_zero_one]
    rfl
  have htransport := pathClass_property_cast P _ p.source.symm p.target.symm hfull
  rwa [hp] at htransport

end Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroup
