import Wikipedia.SchoenfliesTheorem.FaceCyclesLand

open Metric Set Schoenflies unitInterval

namespace PlaneFace

/-- A finite decomposition into the open connected regions that are used as graph faces. -/
structure Decomposition (S : Set Plane) where
  cells : Finset (Set Plane)
  nonempty : ∀ U ∈ cells, U.Nonempty
  isOpen : ∀ U ∈ cells, IsOpen U
  isPreconnected : ∀ U ∈ cells, IsPreconnected U
  pairwise_disjoint : (cells : Set (Set Plane)).Pairwise Disjoint
  cover : S = ⋃₀ (cells : Set (Set Plane))

namespace Decomposition

variable {S P Ω U V : Set Plane}

theorem mem_cover (D : Decomposition S) {x : Plane} :
    x ∈ S ↔ ∃ W ∈ D.cells, x ∈ W := by
  have heq : (x ∈ S) = (x ∈ ⋃₀ (D.cells : Set (Set Plane))) :=
    congrArg (fun T : Set Plane => x ∈ T) D.cover
  rw [heq]
  simp

/-- The cells of a finite open connected partition are exactly the connected components of
their union.  This turns a finite face token back into the usual graph-theoretic `face`. -/
theorem cell_eq_connectedComponentIn (D : Decomposition S) {W : Set Plane}
    (hW : W ∈ D.cells) {x : Plane} (hx : x ∈ W) :
    W = connectedComponentIn S x := by
  classical
  let R : Set Plane := ⋃₀ ((D.cells.erase W : Finset (Set Plane)) : Set (Set Plane))
  have hWsub : W ⊆ S := by
    intro y hy
    exact D.mem_cover.mpr ⟨W, hW, hy⟩
  have hWcomp : W ⊆ connectedComponentIn S x :=
    (D.isPreconnected W hW).subset_connectedComponentIn hx hWsub
  have hRopen : IsOpen R := by
    apply isOpen_sUnion
    intro T hT
    exact D.isOpen T (Finset.mem_of_mem_erase hT)
  have hWR : Disjoint W R := by
    rw [Set.disjoint_left]
    intro y hyW hyR
    obtain ⟨T, hT, hyT⟩ := hyR
    have hTD : T ∈ D.cells := Finset.mem_of_mem_erase hT
    have hTne : T ≠ W := Finset.ne_of_mem_erase hT
    exact Set.disjoint_left.1
      (D.pairwise_disjoint (by simpa using hW) (by simpa using hTD) hTne.symm) hyW hyT
  have hSR : S ⊆ W ∪ R := by
    intro y hy
    obtain ⟨T, hTD, hyT⟩ := D.mem_cover.mp hy
    by_cases hTW : T = W
    · exact Or.inl (hTW ▸ hyT)
    · exact Or.inr ⟨T, Finset.mem_erase.mpr ⟨hTW, hTD⟩, hyT⟩
  have hxcomp : x ∈ connectedComponentIn S x :=
    mem_connectedComponentIn (hWsub hx)
  have hcompW : (connectedComponentIn S x ∩ W).Nonempty := ⟨x, hxcomp, hx⟩
  apply Set.Subset.antisymm hWcomp
  exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
    (D.isOpen W hW) hRopen hWR
    ((connectedComponentIn_subset S x).trans hSR) hcompW

/-- Replacing one face by the two regions cut out by a crosscut preserves a finite face
decomposition. This is the bookkeeping layer omitted by pointwise `HasFaceCycles`. -/
noncomputable def split (D : Decomposition S) (hΩ : Ω ∈ D.cells)
    (hPS : P ∩ S ⊆ Ω) (hUV : Ω \ P = U ∪ V)
    (hU : U.Nonempty) (hV : V.Nonempty)
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hUconn : IsPreconnected U) (hVconn : IsPreconnected V)
    (hdis : Disjoint U V) : Decomposition (S \ P) := by
  classical
  let cells' := insert U (insert V (D.cells.erase Ω))
  have hUsub : U ⊆ Ω := by
    intro x hx
    have hx' : x ∈ Ω \ P := by rw [hUV]; exact Or.inl hx
    exact hx'.1
  have hVsub : V ⊆ Ω := by
    intro x hx
    have hx' : x ∈ Ω \ P := by rw [hUV]; exact Or.inr hx
    exact hx'.1
  have hUneV : U ≠ V := by
    intro heq
    obtain ⟨x, hx⟩ := hU
    exact Set.disjoint_left.1 hdis hx (heq ▸ hx)
  have hU_notmem : U ∉ D.cells.erase Ω := by
    intro hmem
    have hUD : U ∈ D.cells := Finset.mem_of_mem_erase hmem
    have hUneΩ : U ≠ Ω := Finset.ne_of_mem_erase hmem
    have hd := D.pairwise_disjoint (by simpa using hUD) (by simpa using hΩ) hUneΩ
    obtain ⟨x, hx⟩ := hU
    exact Set.disjoint_left.1 hd hx (hUsub hx)
  have hV_notmem : V ∉ D.cells.erase Ω := by
    intro hmem
    have hVD : V ∈ D.cells := Finset.mem_of_mem_erase hmem
    have hVneΩ : V ≠ Ω := Finset.ne_of_mem_erase hmem
    have hd := D.pairwise_disjoint (by simpa using hVD) (by simpa using hΩ) hVneΩ
    obtain ⟨x, hx⟩ := hV
    exact Set.disjoint_left.1 hd hx (hVsub hx)
  have hold_disjoint_U : ∀ W ∈ D.cells.erase Ω, Disjoint U W := by
    intro W hW
    have hWD : W ∈ D.cells := Finset.mem_of_mem_erase hW
    have hWne : W ≠ Ω := Finset.ne_of_mem_erase hW
    exact (D.pairwise_disjoint (by simpa using hΩ) (by simpa using hWD) hWne.symm).mono
      hUsub (Subset.refl _)
  have hold_disjoint_V : ∀ W ∈ D.cells.erase Ω, Disjoint V W := by
    intro W hW
    have hWD : W ∈ D.cells := Finset.mem_of_mem_erase hW
    have hWne : W ≠ Ω := Finset.ne_of_mem_erase hW
    exact (D.pairwise_disjoint (by simpa using hΩ) (by simpa using hWD) hWne.symm).mono
      hVsub (Subset.refl _)
  have herase_pairwise :
      ((D.cells.erase Ω : Finset (Set Plane)) : Set (Set Plane)).Pairwise Disjoint := by
    intro A hA B hB hAB
    exact D.pairwise_disjoint (by simpa using Finset.mem_of_mem_erase hA)
      (by simpa using Finset.mem_of_mem_erase hB) hAB
  refine ⟨cells', ?_, ?_, ?_, ?_, ?_⟩
  · intro W hW
    simp only [cells', Finset.mem_insert] at hW
    rcases hW with rfl | rfl | hW
    · exact hU
    · exact hV
    · exact D.nonempty W (Finset.mem_of_mem_erase hW)
  · intro W hW
    simp only [cells', Finset.mem_insert] at hW
    rcases hW with rfl | rfl | hW
    · exact hUopen
    · exact hVopen
    · exact D.isOpen W (Finset.mem_of_mem_erase hW)
  · intro W hW
    simp only [cells', Finset.mem_insert] at hW
    rcases hW with rfl | rfl | hW
    · exact hUconn
    · exact hVconn
    · exact D.isPreconnected W (Finset.mem_of_mem_erase hW)
  · intro A hA B hB hAB
    simp only [cells', Finset.mem_coe, Finset.mem_insert] at hA hB
    rcases hA with rfl | rfl | hA <;> rcases hB with rfl | rfl | hB
    · exact (hAB rfl).elim
    · exact hdis
    · exact hold_disjoint_U B hB
    · exact hdis.symm
    · exact (hAB rfl).elim
    · exact hold_disjoint_V B hB
    · exact (hold_disjoint_U A hA).symm
    · exact (hold_disjoint_V A hA).symm
    · exact herase_pairwise hA hB hAB
  · ext x
    constructor
    · intro hx
      have hxS : x ∈ S := hx.1
      obtain ⟨W, hWD, hxW⟩ := D.mem_cover.mp hxS
      by_cases hWΩ : W = Ω
      · subst W
        have hxUV : x ∈ U ∪ V := by rw [← hUV]; exact ⟨hxW, hx.2⟩
        rcases hxUV with hxU | hxV
        · simp only [Set.mem_sUnion, Finset.mem_coe]
          exact ⟨U, by simp [cells'], hxU⟩
        · simp only [Set.mem_sUnion, Finset.mem_coe]
          exact ⟨V, by simp [cells'], hxV⟩
      · simp only [Set.mem_sUnion, Finset.mem_coe]
        exact ⟨W, by simp [cells', hWD, hWΩ], hxW⟩
    · intro hx
      simp only [Set.mem_sUnion, Finset.mem_coe] at hx
      obtain ⟨W, hW, hxW⟩ := hx
      simp only [cells', Finset.mem_insert] at hW
      rcases hW with rfl | rfl | hW
      · have hxΩP : x ∈ Ω \ P := by rw [hUV]; exact Or.inl hxW
        exact ⟨D.mem_cover.mpr ⟨Ω, hΩ, hUsub hxW⟩, hxΩP.2⟩
      · have hxΩP : x ∈ Ω \ P := by rw [hUV]; exact Or.inr hxW
        exact ⟨D.mem_cover.mpr ⟨Ω, hΩ, hVsub hxW⟩, hxΩP.2⟩
      · have hWD : W ∈ D.cells := Finset.mem_of_mem_erase hW
        have hWne : W ≠ Ω := Finset.ne_of_mem_erase hW
        refine ⟨D.mem_cover.mpr ⟨W, hWD, hxW⟩, ?_⟩
        intro hxP
        have hxΩ : x ∈ Ω := hPS ⟨hxP, D.mem_cover.mpr ⟨W, hWD, hxW⟩⟩
        exact Set.disjoint_left.1
          (D.pairwise_disjoint (by simpa using hWD) (by simpa using hΩ) hWne) hxW hxΩ

#print axioms PlaneFace.Decomposition.split

/-- One connected plane component together with the two global count identities needed for
Euler's inequality. The weights are boundary-walk lengths. -/
structure WeightedDecomposition (S : Set Plane) (vertices edges : ℕ)
    extends Decomposition S where
  perimeter : Set Plane → ℕ
  euler : vertices + cells.card = edges + 2
  sum_perimeters : cells.sum perimeter = 2 * edges

namespace WeightedDecomposition

variable {vertices edges a b : ℕ}

/-- The two faces of one separating Jordan cycle, both with the cycle perimeter. This is the
base object for an ear decomposition. -/
noncomputable def ofSeparatingCycle (C : Set Plane) (k : ℕ) (hC : IsSeparating C) :
    WeightedDecomposition Cᶜ k k := by
  classical
  let Inn := inside C
  let Out := outside C
  have hInn : Inn.Nonempty := hC.isConnected_inside.nonempty
  have hOut : Out.Nonempty := hC.isConnected_outside.nonempty
  have hInnOut : Inn ≠ Out := by
    intro heq
    obtain ⟨x, hx⟩ := hInn
    have hxOut : x ∈ Out := by rw [← heq]; exact hx
    exact Set.disjoint_left.1 disjoint_inside_outside hx hxOut
  let cells : Finset (Set Plane) := {Inn, Out}
  let perim : Set Plane → ℕ := fun W => if W = Inn then k else if W = Out then k else 0
  refine ⟨{
    cells := cells
    nonempty := ?_
    isOpen := ?_
    isPreconnected := ?_
    pairwise_disjoint := ?_
    cover := ?_ }, perim, ?_, ?_⟩
  · intro W hW
    simp only [cells, Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl
    · exact hInn
    · exact hOut
  · intro W hW
    simp only [cells, Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl
    · exact hC.isOpen_inside
    · exact hC.isOpen_outside
  · intro W hW
    simp only [cells, Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl
    · exact hC.isConnected_inside.isPreconnected
    · exact hC.isConnected_outside.isPreconnected
  · intro A hA B hB hAB
    simp only [cells, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hAB rfl).elim
    · exact disjoint_inside_outside
    · exact disjoint_inside_outside.symm
    · exact (hAB rfl).elim
  · ext x
    simp only [Set.mem_compl_iff, Set.mem_sUnion, Finset.mem_coe]
    constructor
    · intro hx
      have hx' : x ∈ inside C ∪ outside C := by
        rw [inside_union_outside]
        exact hx
      rcases hx' with hxI | hxO
      · exact ⟨Inn, by simp [cells], hxI⟩
      · exact ⟨Out, by simp [cells], hxO⟩
    · rintro ⟨W, hW, hxW⟩
      simp only [cells, Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl
      · exact inside_subset_compl hxW
      · exact outside_subset_compl hxW
  · simp [cells, hInnOut]
  · simp [cells, perim, hInnOut]
    omega

#print axioms PlaneFace.Decomposition.WeightedDecomposition.ofSeparatingCycle

/-- The exact `chord` update: one face of perimeter `a+b` is replaced by faces of perimeter
`a+1` and `b+1`. Both Euler and the dart double-count are preserved. -/
noncomputable def split (D : WeightedDecomposition S vertices edges)
    (hΩ : Ω ∈ D.cells) (hPS : P ∩ S ⊆ Ω) (hUV : Ω \ P = U ∪ V)
    (hU : U.Nonempty) (hV : V.Nonempty)
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hUconn : IsPreconnected U) (hVconn : IsPreconnected V)
    (hdis : Disjoint U V) (hperim : D.perimeter Ω = a + b) :
    WeightedDecomposition (S \ P) vertices (edges + 1) := by
  classical
  let base := D.toDecomposition.split hΩ hPS hUV hU hV hUopen hVopen hUconn hVconn hdis
  let perimeter' : Set Plane → ℕ := fun W =>
    if W = U then a + 1 else if W = V then b + 1 else D.perimeter W
  have hUsub : U ⊆ Ω := by
    intro x hx
    have hx' : x ∈ Ω \ P := by rw [hUV]; exact Or.inl hx
    exact hx'.1
  have hVsub : V ⊆ Ω := by
    intro x hx
    have hx' : x ∈ Ω \ P := by rw [hUV]; exact Or.inr hx
    exact hx'.1
  have hUneV : U ≠ V := by
    intro heq
    obtain ⟨x, hx⟩ := hU
    exact Set.disjoint_left.1 hdis hx (heq ▸ hx)
  have hU_notmem : U ∉ D.cells.erase Ω := by
    intro hmem
    have hUD : U ∈ D.cells := Finset.mem_of_mem_erase hmem
    have hUneΩ : U ≠ Ω := Finset.ne_of_mem_erase hmem
    have hd := D.pairwise_disjoint (by simpa using hUD) (by simpa using hΩ) hUneΩ
    obtain ⟨x, hx⟩ := hU
    exact Set.disjoint_left.1 hd hx (hUsub hx)
  have hV_notmem : V ∉ D.cells.erase Ω := by
    intro hmem
    have hVD : V ∈ D.cells := Finset.mem_of_mem_erase hmem
    have hVneΩ : V ≠ Ω := Finset.ne_of_mem_erase hmem
    have hd := D.pairwise_disjoint (by simpa using hVD) (by simpa using hΩ) hVneΩ
    obtain ⟨x, hx⟩ := hV
    exact Set.disjoint_left.1 hd hx (hVsub hx)
  have hcard : base.cells.card = D.cells.card + 1 := by
    have hpos : 0 < D.cells.card := Finset.card_pos.mpr ⟨Ω, hΩ⟩
    simp [base, Decomposition.split, hUneV, hU_notmem, hV_notmem, hΩ]
    omega
  have hsumErase : (D.cells.erase Ω).sum D.perimeter + D.perimeter Ω =
      D.cells.sum D.perimeter := by
    rw [Finset.sum_erase_add _ _ hΩ]
  have hsum : base.cells.sum perimeter' = 2 * (edges + 1) := by
    simp only [base, Decomposition.split]
    have hU_notmemInsert : U ∉ insert V (D.cells.erase Ω) := by
      simp [hUneV, hU_notmem]
    rw [Finset.sum_insert hU_notmemInsert, Finset.sum_insert hV_notmem]
    simp only [perimeter', if_pos, hUneV.symm, if_false]
    have hrest : (D.cells.erase Ω).sum perimeter' =
        (D.cells.erase Ω).sum D.perimeter := by
      apply Finset.sum_congr rfl
      intro W hW
      have hWU : W ≠ U := fun h => hU_notmem (h ▸ hW)
      have hWV : W ≠ V := fun h => hV_notmem (h ▸ hW)
      simp [perimeter', hWU, hWV]
    rw [hrest]
    have hp := hperim
    have he := hsumErase
    have hsumOld := D.sum_perimeters
    omega
  refine ⟨base, perimeter', ?_, hsum⟩
  have heulerOld := D.euler
  omega

#print axioms PlaneFace.Decomposition.WeightedDecomposition.split

/-- Increasing the lengths of two distinct face boundaries by `t` advances both the vertex
and edge counts by `t`, while preserving Euler and the perimeter double-count.  This is the
pure bookkeeping operation that turns a one-edge chord split into a multi-edge ear split. -/
noncomputable def inflateTwoFaces (D : WeightedDecomposition S vertices edges)
    {U V : Set Plane} (hU : U ∈ D.cells) (hV : V ∈ D.cells) (hUV : U ≠ V) (t : ℕ) :
    WeightedDecomposition S (vertices + t) (edges + t) := by
  classical
  let perimeter' : Set Plane → ℕ := fun W =>
    D.perimeter W + (if W = U then t else 0) + (if W = V then t else 0)
  refine ⟨D.toDecomposition, perimeter', ?_, ?_⟩
  · have he := D.euler
    omega
  · simp only [perimeter', Finset.sum_add_distrib]
    have hsumU : ∑ W ∈ D.cells, (if W = U then t else 0) = t := by
      simp [hU]
    have hsumV : ∑ W ∈ D.cells, (if W = V then t else 0) = t := by
      simp [hV]
    rw [hsumU, hsumV, D.sum_perimeters]
    omega

#print axioms PlaneFace.Decomposition.WeightedDecomposition.inflateTwoFaces

/-- A path of `t+1` edges inserted as one geometric crosscut has `t` new internal vertices.
It replaces one face of boundary lengths `a+b` by two boundaries of lengths
`a+(t+1)` and `b+(t+1)`, and preserves both global count identities. -/
noncomputable def splitEar (D : WeightedDecomposition S vertices edges)
    (hΩ : Ω ∈ D.cells) (hPS : P ∩ S ⊆ Ω) (hUV : Ω \ P = U ∪ V)
    (hU : U.Nonempty) (hV : V.Nonempty)
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hUconn : IsPreconnected U) (hVconn : IsPreconnected V)
    (hdis : Disjoint U V) (hperim : D.perimeter Ω = a + b) (t : ℕ) :
    WeightedDecomposition (S \ P) (vertices + t) ((edges + 1) + t) := by
  let chord := D.split hΩ hPS hUV hU hV hUopen hVopen hUconn hVconn hdis hperim
  have hUmem : U ∈ chord.cells := by
    simp [chord, WeightedDecomposition.split, Decomposition.split]
  have hVmem : V ∈ chord.cells := by
    simp [chord, WeightedDecomposition.split, Decomposition.split]
  have hUneV : U ≠ V := by
    intro heq
    obtain ⟨x, hx⟩ := hU
    exact Set.disjoint_left.1 hdis hx (heq ▸ hx)
  exact chord.inflateTwoFaces hUmem hVmem hUneV t

#print axioms PlaneFace.Decomposition.WeightedDecomposition.splitEar

theorem edge_add_four_le_two_vertices
    (D : WeightedDecomposition S vertices edges) (hcells : D.cells.Nonempty)
    (hface : ∀ W ∈ D.cells, 4 ≤ D.perimeter W) :
    edges + 4 ≤ 2 * vertices := by
  have hfour : 4 * D.cells.card ≤ D.cells.sum D.perimeter := by
    calc
      4 * D.cells.card = ∑ _W ∈ D.cells, 4 := by simp [mul_comm]
      _ ≤ ∑ W ∈ D.cells, D.perimeter W := Finset.sum_le_sum hface
  have hcard : 0 < D.cells.card := Finset.card_pos.mpr hcells
  have heuler := D.euler
  have hsum := D.sum_perimeters
  omega

#print axioms PlaneFace.Decomposition.WeightedDecomposition.edge_add_four_le_two_vertices

end WeightedDecomposition

end Decomposition
end PlaneFace
