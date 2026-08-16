import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedGoodAtoms
import Wikipedia.SzemeredisTheorem.Hypergraph.BoundaryBernoulli
import Wikipedia.SzemeredisTheorem.Hypergraph.BundleCountingRecurrence
import Wikipedia.SzemeredisTheorem.Hypergraph.FullOrderedRegularity
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedEnergy

/-!
# Positive counts for good closed ordered configurations

This file turns the local good-atom estimates into a direct positive-count
recurrence.  The edge index contains every positive-rank ordered face of an
ordered partition complex.  On downward-closed face families, the count is
the normalized mean of the selected atom indicators.  On other families we
use the exact product of the coarse densities; this total extension lets us
apply the finite abstract recurrence without asking localized estimates on
families which omit their boundary.

At a maximum-rank face, the remaining product contains every proper
boundary factor.  Thus it is supported on the canonical coarse boundary
atom.  The identity

```text
1_A = p + (E_fine 1_A - p) + (1_A - E_fine 1_A)
```

then gives the recurrence.  The uniform term is tested against a bounded
boundary product after freezing the outside variables.  The defect term is
bounded by localized Cauchy--Schwarz; the boundary support and unit bounds
make its square at most the good-atom defect threshold.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Positive-rank faces and immediate downward closure -/

/-- A positive-rank ordered face of a complex with ranks `0, ..., r`.
`lowerRank = j` represents an actual face of rank `j + 1`. -/
structure PositiveOrderedFace (k r : ℕ) where
  lowerRank : Fin r
  face : OrderedFace k (lowerRank.1 + 1)
deriving DecidableEq

namespace PositiveOrderedFace

/-- Positive ordered faces are the dependent sum of their rank index and
their increasing face. -/
def equivSigma (k r : ℕ) :
    PositiveOrderedFace k r ≃
      Σ j : Fin r, OrderedFace k (j.1 + 1) where
  toFun e := ⟨e.lowerRank, e.face⟩
  invFun e := ⟨e.1, e.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

noncomputable instance instFintype (k r : ℕ) :
    Fintype (PositiveOrderedFace k r) :=
  Fintype.ofEquiv
    (Σ j : Fin r, OrderedFace k (j.1 + 1))
    (equivSigma k r).symm

/-- Actual cardinality/rank of a positive ordered face. -/
def rank {k r : ℕ} (e : PositiveOrderedFace k r) : ℕ :=
  e.lowerRank.1 + 1

@[simp]
theorem rank_pos {k r : ℕ} (e : PositiveOrderedFace k r) :
    0 < e.rank := by
  simp [rank]

/-- A positive immediate boundary face, obtained by erasing one coordinate.
The positivity hypothesis says that the original face has rank at least
two. -/
noncomputable def boundary
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    PositiveOrderedFace k r := by
  let j : Fin r :=
    ⟨e.lowerRank.1 - 1,
      lt_of_le_of_lt (Nat.sub_le _ _) e.lowerRank.2⟩
  refine ⟨j, ?_⟩
  have hj : j.1 + 1 = e.lowerRank.1 := by
    simp only [j]
    omega
  exact hj ▸ eraseBoundaryFace e.face i

@[simp]
theorem boundary_lowerRank
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    (e.boundary hpos i).lowerRank.1 =
      e.lowerRank.1 - 1 := by
  rfl

theorem boundary_rank_lt
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    (e.boundary hpos i).rank < e.rank := by
  simp only [rank, boundary_lowerRank]
  omega

/-- Restriction to the canonical positive boundary face is coordinate
erasure, up to the definitional rank normalization in `boundary`. -/
theorem orderedFaceTuple_boundary
    {G : Type*} {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1))
    (x : Fin k → G) :
    orderedFaceTuple (e.boundary hpos i).face x =
      (by
        have hj :
            (e.boundary hpos i).lowerRank.1 + 1 =
              e.lowerRank.1 := by
          simp only [boundary_lowerRank]
          omega
        exact hj ▸
          eraseBoundaryCoordinate i
            (orderedFaceTuple e.face x)) := by
  rcases e with ⟨⟨n, hn⟩, face⟩
  cases n with
  | zero => simp at hpos
  | succ n =>
      rfl

end PositiveOrderedFace

/-- A positive face family contains every positive immediate boundary face
of each of its members. -/
def IsDownwardClosedPositiveFaces
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r)) : Prop :=
  ∀ (e : PositiveOrderedFace k r), e ∈ s →
    ∀ (hpos : 0 < e.lowerRank.1)
      (i : Fin (e.lowerRank.1 + 1)),
      e.boundary hpos i ∈ s

theorem downwardClosed_empty
    {k r : ℕ} :
    IsDownwardClosedPositiveFaces
      (∅ : Finset (PositiveOrderedFace k r)) := by
  intro e he
  simp at he

/-- The full family of positive ordered faces is downward closed. -/
theorem downwardClosed_univ
    {k r : ℕ} :
    IsDownwardClosedPositiveFaces
      (Finset.univ : Finset (PositiveOrderedFace k r)) := by
  intro e _ hpos i
  exact Finset.mem_univ _

/-- Every nonempty finite positive-face family has a face of maximum rank. -/
theorem exists_maxRank_mem
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r))
    (hs : s.Nonempty) :
    ∃ e ∈ s, ∀ f ∈ s, f.rank ≤ e.rank := by
  classical
  induction s using Finset.induction with
  | empty =>
      exact (Finset.not_nonempty_empty hs).elim
  | @insert a s ha ih =>
      by_cases hs0 : s.Nonempty
      · obtain ⟨e, he, hmax⟩ := ih hs0
        by_cases hae : a.rank ≤ e.rank
        · refine ⟨e, Finset.mem_insert_of_mem he, ?_⟩
          intro f hf
          rw [Finset.mem_insert] at hf
          rcases hf with rfl | hf
          · exact hae
          · exact hmax f hf
        · refine ⟨a, by simp, ?_⟩
          intro f hf
          rw [Finset.mem_insert] at hf
          rcases hf with rfl | hf
          · exact le_rfl
          · exact le_trans (hmax f hf) (Nat.le_of_not_ge hae)
      · have hsEmpty : s = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hs0
        subst s
        refine ⟨a, by simp, ?_⟩
        intro f hf
        have hfa : f = a := by simpa using hf
        subst f
        exact le_rfl

/-- Erasing a maximum-rank face preserves immediate downward closure. -/
theorem IsDownwardClosedPositiveFaces.erase_maxRank
    {k r : ℕ}
    {s : Finset (PositiveOrderedFace k r)}
    (hclosed : IsDownwardClosedPositiveFaces s)
    {e : PositiveOrderedFace k r} (he : e ∈ s)
    (hmax : ∀ f ∈ s, f.rank ≤ e.rank) :
    IsDownwardClosedPositiveFaces (s.erase e) := by
  intro f hf hpos i
  have hfS : f ∈ s := Finset.mem_of_mem_erase hf
  have hbS := hclosed f hfS hpos i
  apply Finset.mem_erase.mpr
  refine ⟨?_, hbS⟩
  intro hbe
  have hranklt := f.boundary_rank_lt hpos i
  have hfle := hmax f hfS
  subst e
  omega

/-! ## Missing coordinates for lower-or-equal rank faces -/

/-- If `f` has rank at most `e` but is not `e`, then `f` omits a vertex
coordinate of `e`. -/
theorem exists_positiveFace_coordinate_not_mem_range
    {k r : ℕ}
    (e f : PositiveOrderedFace k r)
    (hle : f.rank ≤ e.rank) (hne : f ≠ e) :
    ∃ i : Fin (e.lowerRank.1 + 1),
      e.face i ∉ Set.range f.face := by
  classical
  rcases e with ⟨ej, ef⟩
  rcases f with ⟨fj, ff⟩
  by_contra hnone
  push Not at hnone
  have hsubset :
      Finset.univ.map ef.toEmbedding ⊆
        Finset.univ.map ff.toEmbedding := by
    intro v hv
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨j, hj⟩ := hnone i
    exact Finset.mem_map.mpr
      ⟨j, Finset.mem_univ _, hj⟩
  have hreverseRank : ej.1 + 1 ≤ fj.1 + 1 := by
    have hc :=
      Finset.card_le_card hsubset
    simpa [PositiveOrderedFace.rank] using hc
  have hforwardRank : fj.1 + 1 ≤ ej.1 + 1 := by
    simpa [PositiveOrderedFace.rank] using hle
  have hlowerVal : ej.1 = fj.1 := by
    omega
  have hlower : ej = fj := Fin.ext hlowerVal
  subst fj
  have hsets :
      Finset.univ.map ef.toEmbedding =
        Finset.univ.map ff.toEmbedding := by
    apply Finset.eq_of_subset_of_card_le hsubset
    simp
  have hrange : Set.range ef = Set.range ff := by
    ext v
    have hv := Finset.ext_iff.mp hsets v
    simpa using hv
  apply hne
  congr
  exact OrderEmbedding.range_inj.mp hrange.symm

/-- Canonical missing coordinate for a distinct lower-or-equal rank face. -/
noncomputable def positiveFaceMissingCoordinate
    {k r : ℕ}
    (e f : PositiveOrderedFace k r)
    (hle : f.rank ≤ e.rank) (hne : f ≠ e) :
    Fin (e.lowerRank.1 + 1) :=
  Classical.choose
    (exists_positiveFace_coordinate_not_mem_range
      e f hle hne)

theorem positiveFaceMissingCoordinate_not_mem_range
    {k r : ℕ}
    (e f : PositiveOrderedFace k r)
    (hle : f.rank ≤ e.rank) (hne : f ≠ e) :
    e.face (positiveFaceMissingCoordinate e f hle hne) ∉
      Set.range f.face :=
  Classical.choose_spec
    (exists_positiveFace_coordinate_not_mem_range
      e f hle hne)

/-- Updating a coordinate of `e` does not change the tuple seen by any
possibly lower-rank face `f` which omits that vertex. -/
theorem orderedFaceTuple_split_update_eq_of_missing
    {G : Type*} {k n m : ℕ}
    (e : OrderedFace k n) (f : OrderedFace k m)
    (i : Fin n)
    (hmissing : e i ∉ Set.range f)
    (a : G) (y : Fin n → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm
          (Function.update y i a, z)) =
      orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm (y, z)) := by
  funext t
  by_cases hfe : f t ∈ Set.range e
  · obtain ⟨q, hq⟩ := hfe
    have hqi : q ≠ i := by
      intro h
      apply hmissing
      exact ⟨t, (h ▸ hq).symm⟩
    have hleft :=
      congrFun
        (orderedFaceTuple_splitOrderedFaceEquiv_symm
          e (Function.update y i a) z) q
    have hright :=
      congrFun
        (orderedFaceTuple_splitOrderedFaceEquiv_symm
          e y z) q
    change
      ((splitOrderedFaceEquiv e).symm
          (Function.update y i a, z)) (e q) =
        Function.update y i a q at hleft
    change
      ((splitOrderedFaceEquiv e).symm (y, z)) (e q) =
        y q at hright
    change
      ((splitOrderedFaceEquiv e).symm
          (Function.update y i a, z)) (f t) =
        ((splitOrderedFaceEquiv e).symm (y, z)) (f t)
    rw [← hq, hleft, hright]
    simp [hqi]
  · let v : OrderedFaceComplement e := ⟨f t, hfe⟩
    have hleft :=
      congrFun
        (orderedFaceComplementTuple_splitOrderedFaceEquiv_symm
          e (Function.update y i a) z) v
    have hright :=
      congrFun
        (orderedFaceComplementTuple_splitOrderedFaceEquiv_symm
          e y z) v
    exact hleft.trans hright.symm

/-- Erasing and reinserting a missing coordinate does not change a face
which omits that coordinate. -/
theorem orderedFaceTuple_split_insertErased_eq_of_missing
    {G : Type*} [DecidableEq G] {k j m : ℕ}
    (e : OrderedFace k (j + 1)) (f : OrderedFace k m)
    (i : Fin (j + 1))
    (hmissing : e i ∉ Set.range f)
    (a : G) (y : Fin (j + 1) → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm
          (Fin.insertNth i a
            (eraseBoundaryCoordinate i y), z)) =
      orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm (y, z)) := by
  have hinsert :
      Fin.insertNth i a (eraseBoundaryCoordinate i y) =
        Function.update y i a := by
    exact Fin.insertNth_removeNth i a y
  rw [hinsert]
  exact orderedFaceTuple_split_update_eq_of_missing
    e f i hmissing a y z

/-! ## Selected atom weights and counts -/

/-- Indicator of the atom selected by a closed configuration at one
positive-rank face. -/
def configurationFaceWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (C.partition e.lowerRank.succ e.face)
    (A.atom e.lowerRank.succ e.face) y

theorem configurationFaceWeight_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    0 ≤ configurationFaceWeight A e y :=
  partitionAtomIndicator_nonneg _ _ _

theorem configurationFaceWeight_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    configurationFaceWeight A e y ≤ 1 :=
  partitionAtomIndicator_le_one _ _ _

/-- Product of the selected atom indicators over a partial positive-face
family. -/
noncomputable def partialConfigurationWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (x : Fin k → G) : ℝ :=
  ∏ e ∈ s,
    configurationFaceWeight A e
      (orderedFaceTuple e.face x)

/-- Normalized count of one partial closed atom configuration. -/
noncomputable def partialConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r)) : ℝ :=
  mean (partialConfigurationWeight A s)

/-- Full normalized count of the selected positive-rank atoms. -/
noncomputable def fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) : ℝ :=
  partialConfigurationCount A Finset.univ

@[simp]
theorem partialConfigurationWeight_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (x : Fin k → G) :
    partialConfigurationWeight A ∅ x = 1 := by
  simp [partialConfigurationWeight]

@[simp]
theorem partialConfigurationCount_empty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    partialConfigurationCount A ∅ = 1 := by
  change mean (fun _x : Fin k → G => (1 : ℝ)) = 1
  exact mean_const 1

theorem partialConfigurationWeight_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (x : Fin k → G) :
    0 ≤ partialConfigurationWeight A s x := by
  unfold partialConfigurationWeight
  exact Finset.prod_nonneg fun e he =>
    configurationFaceWeight_nonneg A e _

theorem partialConfigurationWeight_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (x : Fin k → G) :
    partialConfigurationWeight A s x ≤ 1 := by
  unfold partialConfigurationWeight
  apply Finset.prod_le_one
  · intro e he
    exact configurationFaceWeight_nonneg A e _
  · intro e he
    exact configurationFaceWeight_le_one A e _

/-! ## Freezing and grouping a maximum-rank remainder -/

/-- Reconstructing an erased coordinate leaves a lower-or-equal rank face
unchanged when that face omits the reconstructed vertex. -/
theorem orderedFaceTuple_split_insertNth_erase_eq_of_missing
    {G : Type*} [DecidableEq G] {k j m : ℕ}
    (e : OrderedFace k (j + 1)) (f : OrderedFace k m)
    (i : Fin (j + 1))
    (hmissing : e i ∉ Set.range f)
    (a : G) (y : Fin (j + 1) → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm
          (Fin.insertNth i a (eraseCoordinate i y), z)) =
      orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm (y, z)) := by
  rw [insertNth_eraseCoordinate_eq_update]
  exact orderedFaceTuple_split_update_eq_of_missing
    e f i hmissing a y z

/-- Totalized canonical missing coordinate for the grouped remainder.
Only its value on members of `s.erase e` is used. -/
noncomputable def configurationMissingCoordinate
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax : ∀ f ∈ s.erase e, f.rank ≤ e.rank)
    (f : PositiveOrderedFace k r) :
    Fin (e.lowerRank.1 + 1) := by
  classical
  by_cases hf : f ∈ s.erase e
  · exact positiveFaceMissingCoordinate e f
      (hmax f hf) (Finset.mem_erase.mp hf).1
  · exact 0

theorem configurationMissingCoordinate_not_mem_range
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax : ∀ f ∈ s.erase e, f.rank ≤ e.rank)
    {f : PositiveOrderedFace k r}
    (hf : f ∈ s.erase e) :
    e.face
        (configurationMissingCoordinate s e hmax f) ∉
      Set.range f.face := by
  rw [configurationMissingCoordinate]
  simp only [dif_pos hf]
  exact positiveFaceMissingCoordinate_not_mem_range
    e f (hmax f hf) (Finset.mem_erase.mp hf).1

/-- Group the factors remaining after a maximum-rank face under canonical
missing coordinates.  Once the outside variables are frozen this is a
bounded boundary cut test on the selected face tuple. -/
noncomputable def configurationRemainderCutTest
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax : ∀ f ∈ s.erase e, f.rank ≤ e.rank)
    (a : G)
    (z : OrderedFaceComplement e.face → G) :
    CutTestFamily G (e.lowerRank.1 + 1) :=
  fun i y =>
    ∏ f ∈ s.erase e,
      if _hcoord :
          configurationMissingCoordinate s e hmax f = i
      then
        configurationFaceWeight A f
          (orderedFaceTuple f.face
            ((splitOrderedFaceEquiv e.face).symm
              (Fin.insertNth i a y, z)))
      else 1

/-- The grouped remainder cut test takes values in `[0,1]`. -/
theorem configurationRemainderCutTest_bounded
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax : ∀ f ∈ s.erase e, f.rank ≤ e.rank)
    (a : G)
    (z : OrderedFaceComplement e.face → G) :
    IsBoundedCutTest
      (configurationRemainderCutTest A s e hmax a z) := by
  constructor
  · intro i y
    unfold configurationRemainderCutTest
    apply Finset.prod_nonneg
    intro f hf
    split_ifs
    · exact configurationFaceWeight_nonneg A f _
    · positivity
  · intro i y
    unfold configurationRemainderCutTest
    apply Finset.prod_le_one
    · intro f hf
      split_ifs
      · exact configurationFaceWeight_nonneg A f _
      · positivity
    · intro f hf
      split_ifs
      · exact configurationFaceWeight_le_one A f _
      · exact le_rfl

/-- Evaluating the grouped cut product recovers the complete product of the
remaining selected atom factors. -/
theorem cutTestProduct_configurationRemainderCutTest
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax : ∀ f ∈ s.erase e, f.rank ≤ e.rank)
    (a : G)
    (y : Fin (e.lowerRank.1 + 1) → G)
    (z : OrderedFaceComplement e.face → G) :
    cutTestProduct
        (configurationRemainderCutTest A s e hmax a z) y =
      partialConfigurationWeight A (s.erase e)
        ((splitOrderedFaceEquiv e.face).symm (y, z)) := by
  classical
  unfold cutTestProduct configurationRemainderCutTest
  rw [Finset.prod_comm]
  unfold partialConfigurationWeight
  apply Finset.prod_congr rfl
  intro f hf
  let i :=
    configurationMissingCoordinate s e hmax f
  have hmissing :
      e.face i ∉ Set.range f.face :=
    configurationMissingCoordinate_not_mem_range
      s e hmax hf
  calc
    (∏ q : Fin (e.lowerRank.1 + 1),
        if hcoord :
            configurationMissingCoordinate s e hmax f = q
        then
          configurationFaceWeight A f
            (orderedFaceTuple f.face
              ((splitOrderedFaceEquiv e.face).symm
                (Fin.insertNth q a
                  (eraseCoordinate q y), z)))
        else 1) =
        (if hcoord :
            configurationMissingCoordinate s e hmax f = i
        then
          configurationFaceWeight A f
            (orderedFaceTuple f.face
              ((splitOrderedFaceEquiv e.face).symm
                (Fin.insertNth i a
                  (eraseCoordinate i y), z)))
        else 1) := by
      apply Fintype.prod_eq_single i
      intro q hqi
      have hne :
          configurationMissingCoordinate s e hmax f ≠ q := by
        intro h
        exact hqi h.symm
      simp [hne]
    _ =
        configurationFaceWeight A f
          (orderedFaceTuple f.face
            ((splitOrderedFaceEquiv e.face).symm
              (Fin.insertNth i a
                (eraseCoordinate i y), z))) := by
      simp [i]
    _ =
        configurationFaceWeight A f
          (orderedFaceTuple f.face
            ((splitOrderedFaceEquiv e.face).symm (y, z))) := by
      rw [orderedFaceTuple_split_insertNth_erase_eq_of_missing
        e.face f.face i hmissing a y z]

/-! ## Coarse densities, defects, and boundary support -/

/-- Rank-normalized lower layer attached to a positive face. -/
def positiveFaceLowerLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    OrderedFacePartitionSystem G k e.lowerRank.1 :=
  C.partition e.lowerRank.castSucc

/-- Coarse conditional density of the selected fine atom at one face. -/
noncomputable def configurationCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.coarse e)
    e.face
    (partitionAtomIndicator
      (P.fine.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    (orderedFaceTuple e.face A.witness)

/-- Fine conditional density of the selected atom. -/
noncomputable def configurationFineDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.fine e)
    e.face
    (partitionAtomIndicator
      (P.fine.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    y

/-- Fine conditional density minus the constant coarse density selected by
the closed configuration. -/
noncomputable def configurationDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  configurationFineDensity P A e y -
    configurationCoarseDensity P A e

/-- Residual of the selected atom after conditioning on the fine boundary. -/
noncomputable def configurationUniform
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  configurationFaceWeight A e y -
    configurationFineDensity P A e y

/-- Indicator of the canonical coarse boundary atom determined by the
configuration witness. -/
noncomputable def configurationBoundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face)
    (orderedBoundaryAtomAt
      (positiveFaceLowerLayer P.coarse e) e.face
      (orderedFaceTuple e.face A.witness))
    y

theorem configurationCoarseDensity_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r) :
    0 ≤ configurationCoarseDensity P A e := by
  exact conditionalMean_nonneg _
    (partitionAtomIndicator_nonneg _ _) _

theorem configurationCoarseDensity_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r) :
    configurationCoarseDensity P A e ≤ 1 := by
  exact conditionalMean_le_one _
    (partitionAtomIndicator_le_one _ _) _

theorem configurationBoundaryIndicator_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    0 ≤ configurationBoundaryIndicator P A e y :=
  partitionAtomIndicator_nonneg _ _ _

theorem configurationBoundaryIndicator_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    configurationBoundaryIndicator P A e y ≤ 1 :=
  partitionAtomIndicator_le_one _ _ _

/-- Exact selected-edge decomposition with a constant coarse main term. -/
theorem configurationFaceWeight_decompose
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    configurationFaceWeight A e y =
      configurationCoarseDensity P A e +
        configurationDefect P A e y +
        configurationUniform P A e y := by
  unfold configurationDefect configurationUniform
  ring

/-- A nonzero selected factor on an immediate positive boundary face puts
the erased tuple in the corresponding coarse boundary atom. -/
theorem coarse_boundary_mem_of_boundary_weight_ne_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1))
    (x : Fin k → G)
    (hweight :
      configurationFaceWeight A (e.boundary hpos i)
          (orderedFaceTuple (e.boundary hpos i).face x) ≠
        0) :
    eraseBoundaryCoordinate i (orderedFaceTuple e.face x) ∈
      (positiveFaceLowerLayer P.coarse e
        (eraseBoundaryFace e.face i)).part
        (eraseBoundaryCoordinate i
          (orderedFaceTuple e.face A.witness)) := by
  rcases e with ⟨⟨n, hn⟩, eface⟩
  cases n with
  | zero =>
      simp at hpos
  | succ n =>
      let f :=
        (⟨⟨n, by omega⟩,
            eraseBoundaryFace eface i⟩ :
          PositiveOrderedFace k r)
      have hfine :
          orderedFaceTuple f.face x ∈
            (A.atom f.lowerRank.succ f.face).1 := by
        by_contra hnot
        exact hweight
          (partitionAtomIndicator_of_not_mem
            (P.fine.partition f.lowerRank.succ f.face)
            (A.atom f.lowerRank.succ f.face) hnot)
      have hcanonical :
          (A.atom f.lowerRank.succ f.face).1 =
            (P.fine.partition f.lowerRank.succ f.face).part
              (orderedFaceTuple f.face A.witness) := by
        exact congrArg Subtype.val
          (A.atom_eq_partitionAtomAt
            f.lowerRank.succ f.face)
      rw [hcanonical] at hfine
      have hcoarse :
          orderedFaceTuple f.face x ∈
            (P.coarse.partition f.lowerRank.succ f.face).part
              (orderedFaceTuple f.face A.witness) :=
        FacePartition.part_subset_of_le
          (P.refines f.lowerRank.succ f.face)
          (orderedFaceTuple f.face A.witness) hfine
      let j : Fin (r + 1) :=
        ⟨n + 1, Nat.lt_succ_of_lt hn⟩
      have hfj : f.lowerRank.succ = j := by
        apply Fin.ext
        rfl
      have hcoarse' :
          orderedFaceTuple f.face x ∈
            (P.coarse.partition j f.face).part
              (orderedFaceTuple f.face A.witness) := by
        subst j
        exact hcoarse
      simpa [f, j, positiveFaceLowerLayer,
        OrderedPartitionComplex.layer] using hcoarse'

/-- On a downward-closed family, the remainder after removing a
maximum-rank face is supported on that face's canonical coarse boundary
atom. -/
theorem configurationBoundaryIndicator_mul_remainder
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s)
    (x : Fin k → G) :
    configurationBoundaryIndicator P A e
          (orderedFaceTuple e.face x) *
        partialConfigurationWeight A (s.erase e) x =
      partialConfigurationWeight A (s.erase e) x := by
  by_cases hrem :
      partialConfigurationWeight A (s.erase e) x = 0
  · rw [hrem, mul_zero]
  · have hbaseMem :
        orderedFaceTuple e.face x ∈
          (orderedBoundaryAtomAt
            (positiveFaceLowerLayer P.coarse e)
            e.face
            (orderedFaceTuple e.face A.witness)).1 := by
      rw [mem_orderedBoundaryAtomAt_iff]
      intro i
      by_cases hzero : e.lowerRank.1 = 0
      · have heq :
            eraseBoundaryCoordinate i
                (orderedFaceTuple e.face x) =
              eraseBoundaryCoordinate i
                (orderedFaceTuple e.face A.witness) := by
          funext q
          have hq : q.1 < 0 := by
            simpa [hzero] using q.2
          omega
        rw [heq]
        exact
          (positiveFaceLowerLayer P.coarse e
            (eraseBoundaryFace e.face i)).mem_part
            (Finset.mem_univ _)
      · have hpos : 0 < e.lowerRank.1 :=
          Nat.pos_of_ne_zero hzero
        let f := e.boundary hpos i
        have hfS : f ∈ s :=
          hclosed e he hpos i
        have hfe : f ≠ e := by
          intro h
          have hlt := e.boundary_rank_lt hpos i
          change e.boundary hpos i = e at h
          rw [h] at hlt
          exact (Nat.lt_irrefl _ hlt)
        have hfErase : f ∈ s.erase e :=
          Finset.mem_erase.mpr ⟨hfe, hfS⟩
        have hfactor :
            configurationFaceWeight A f
                (orderedFaceTuple f.face x) ≠ 0 := by
          have hprod :
              (∏ g ∈ s.erase e,
                configurationFaceWeight A g
                  (orderedFaceTuple g.face x)) ≠ 0 := by
            simpa [partialConfigurationWeight] using hrem
          exact Finset.prod_ne_zero_iff.mp hprod f hfErase
        exact coarse_boundary_mem_of_boundary_weight_ne_zero
          P A e hpos i x hfactor
    rw [configurationBoundaryIndicator,
      partitionAtomIndicator_of_mem _ _ hbaseMem,
      one_mul]

/-! ## Selected-face contributions and exact decomposition -/

/-- The contribution of a function on one selected face against all
remaining configuration factors. -/
noncomputable def configurationContribution
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (q : (Fin (e.lowerRank.1 + 1) → G) → ℝ) : ℝ :=
  mean fun x : Fin k → G =>
    q (orderedFaceTuple e.face x) *
      partialConfigurationWeight A (s.erase e) x

/-- Pulling out a selected factor leaves precisely the erased-family
weight. -/
theorem partialConfigurationWeight_eq_face_mul_erase
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r) (he : e ∈ s)
    (x : Fin k → G) :
    partialConfigurationWeight A s x =
      configurationFaceWeight A e
          (orderedFaceTuple e.face x) *
        partialConfigurationWeight A (s.erase e) x := by
  unfold partialConfigurationWeight
  exact
    (Finset.mul_prod_erase s
      (fun f =>
        configurationFaceWeight A f
          (orderedFaceTuple f.face x)) he).symm

/-- The exact coarse/defect/uniform decomposition after selecting one
face. -/
theorem partialConfigurationCount_decompose
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r) (he : e ∈ s) :
    partialConfigurationCount A s =
      configurationCoarseDensity P A e *
          partialConfigurationCount A (s.erase e) +
        configurationContribution A s e
          (configurationDefect P A e) +
        configurationContribution A s e
          (configurationUniform P A e) := by
  rw [partialConfigurationCount, partialConfigurationCount]
  have hpoint :
      partialConfigurationWeight A s =
        fun x =>
          configurationCoarseDensity P A e *
              partialConfigurationWeight A (s.erase e) x +
            configurationDefect P A e
                (orderedFaceTuple e.face x) *
              partialConfigurationWeight A (s.erase e) x +
            configurationUniform P A e
                (orderedFaceTuple e.face x) *
              partialConfigurationWeight A (s.erase e) x := by
    funext x
    rw [partialConfigurationWeight_eq_face_mul_erase
      A s e he x,
      configurationFaceWeight_decompose P A e]
    ring
  rw [hpoint, mean_add, mean_add, mean_smul]
  rfl

/-- Full regularity at every rank specializes to the fine-boundary
regularity state attached to a positive face and the selected fine atom. -/
theorem configurationFace_isFaceCutRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (ε : OrderedRegularityTolerance r)
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    (e : PositiveOrderedFace k r) :
    (⟨orderedBoundaryPartition
        (positiveFaceLowerLayer P.fine e) e.face⟩ :
      FaceRegularityState
        (Fin (e.lowerRank.1 + 1) → G)).IsFaceCutRegular
      (partitionAtomIndicator
        (P.fine.partition e.lowerRank.succ e.face)
        (A.atom e.lowerRank.succ e.face))
      (ε e.lowerRank) := by
  rw [positiveFaceLowerLayer]
  exact
    (hregular e.lowerRank).toBounded
      e.face
      (A.atom e.lowerRank.succ e.face)

/-- Rank-scheduled configuration goodness specializes to any positive
ordered face. -/
theorem ClosedOrderedAtomConfiguration.IsGood.atPositiveFace
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (α β : ℕ → ℝ)
    (hgood : A.IsGood P.fine P.coarse α β)
    (e : PositiveOrderedFace k r) :
    OrderedAtomIsGoodAtBoundary
      (positiveFaceLowerLayer P.fine e)
      (positiveFaceLowerLayer P.coarse e)
      e.face
      (P.fine.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face)
      (orderedFaceTuple e.face A.witness)
      (α e.rank) (β e.rank) := by
  rcases e with ⟨⟨j, hj⟩, e⟩
  exact hgood j hj e

/-! ## Uniform contribution -/

/-- After freezing the coordinates outside the selected face, the uniform
contribution is exactly a fine-boundary cut correlation. -/
theorem configurationContribution_uniform_eq_mean_faceCutCorrelation
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax :
      ∀ f ∈ s.erase e, f.rank ≤ e.rank)
    (a : G) :
    configurationContribution A s e
        (configurationUniform P A e) =
      mean fun z : OrderedFaceComplement e.face → G =>
        (⟨orderedBoundaryPartition
            (positiveFaceLowerLayer P.fine e) e.face⟩ :
          FaceRegularityState
            (Fin (e.lowerRank.1 + 1) → G)).faceCutCorrelation
          (partitionAtomIndicator
            (P.fine.partition e.lowerRank.succ e.face)
            (A.atom e.lowerRank.succ e.face))
          (configurationRemainderCutTest
            A s e hmax a z) := by
  unfold configurationContribution
  rw [mean_splitOrderedFace e.face, mean₂_comm]
  unfold mean₂
  apply congrArg mean
  funext z
  unfold FaceRegularityState.faceCutCorrelation
  apply congrArg mean
  funext y
  rw [cutTestProduct_configurationRemainderCutTest
    A s e hmax a y z]
  simp only [orderedFaceTuple_splitOrderedFaceEquiv_symm]
  rfl

/-- Full preliminary regularity controls the uniform term in the
selected-face recurrence. -/
theorem abs_configurationContribution_uniform_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (ε : OrderedRegularityTolerance r)
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax :
      ∀ f ∈ s.erase e, f.rank ≤ e.rank) :
    |configurationContribution A s e
        (configurationUniform P A e)| ≤
      ε e.lowerRank := by
  rw [configurationContribution_uniform_eq_mean_faceCutCorrelation
    P A s e hmax (Classical.choice inferInstance)]
  let S :
      FaceRegularityState
        (Fin (e.lowerRank.1 + 1) → G) :=
    ⟨orderedBoundaryPartition
      (positiveFaceLowerLayer P.fine e) e.face⟩
  let f :
      (Fin (e.lowerRank.1 + 1) → G) → ℝ :=
    partitionAtomIndicator
      (P.fine.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face)
  calc
    |mean fun z : OrderedFaceComplement e.face → G =>
        S.faceCutCorrelation f
          (configurationRemainderCutTest A s e hmax
            (Classical.choice inferInstance) z)| ≤
        mean fun z : OrderedFaceComplement e.face → G =>
          |S.faceCutCorrelation f
            (configurationRemainderCutTest A s e hmax
              (Classical.choice inferInstance) z)| :=
      Finset.abs_expect_le Finset.univ _
    _ ≤
        mean fun _z : OrderedFaceComplement e.face → G =>
          ε e.lowerRank := by
      apply mean_mono
      intro z
      exact
        configurationFace_isFaceCutRegular
          P A ε hregular e
          (configurationRemainderCutTest A s e hmax
            (Classical.choice inferInstance) z)
          (configurationRemainderCutTest_bounded
            A s e hmax (Classical.choice inferInstance) z)
    _ = ε e.lowerRank := mean_const _

/-! ## Localized defect contribution -/

/-- On the canonical coarse boundary atom, the defect with the frozen
coarse density is the usual pointwise fine-minus-coarse boundary defect. -/
theorem configurationDefect_mul_boundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    configurationDefect P A e y *
        configurationBoundaryIndicator P A e y =
      orderedAtomBoundaryDefect
          (positiveFaceLowerLayer P.fine e)
          (positiveFaceLowerLayer P.coarse e)
          e.face
          (P.fine.partition e.lowerRank.succ e.face)
          (A.atom e.lowerRank.succ e.face) y *
        configurationBoundaryIndicator P A e y := by
  let Q :=
    orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face
  let b : Q.parts :=
    orderedBoundaryAtomAt
      (positiveFaceLowerLayer P.coarse e) e.face
      (orderedFaceTuple e.face A.witness)
  let f :
      (Fin (e.lowerRank.1 + 1) → G) → ℝ :=
    partitionAtomIndicator
      (P.fine.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face)
  by_cases hy : y ∈ b.1
  · have hcoarse :
        conditionalMean Q f y =
          conditionalMean Q f
            (orderedFaceTuple e.face A.witness) := by
      exact conditionalMean_eq_of_mem_part Q f hy
    rw [configurationBoundaryIndicator,
      partitionAtomIndicator_of_mem _ _ hy,
      mul_one, mul_one]
    change
      conditionalMean
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.fine e) e.face)
            f y -
          conditionalMean Q f
            (orderedFaceTuple e.face A.witness) =
        conditionalMean
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.fine e) e.face)
            f y -
          conditionalMean Q f y
    rw [hcoarse]
  · rw [configurationBoundaryIndicator,
      partitionAtomIndicator_of_not_mem _ _ hy,
      mul_zero, mul_zero]

/-- Squared localized configuration defect is the library's canonical
localized atom-defect mass. -/
theorem mean_sq_configurationDefect_mul_boundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r) :
    mean (fun y =>
      (configurationDefect P A e y *
        configurationBoundaryIndicator P A e y) ^ 2) =
      orderedLocalizedAtomDefectSq
        (positiveFaceLowerLayer P.fine e)
        (positiveFaceLowerLayer P.coarse e)
        e.face
        (P.fine.partition e.lowerRank.succ e.face)
        (A.atom e.lowerRank.succ e.face)
        (orderedBoundaryAtomAt
          (positiveFaceLowerLayer P.coarse e)
          e.face
          (orderedFaceTuple e.face A.witness)) := by
  unfold orderedLocalizedAtomDefectSq
  apply congrArg mean
  funext y
  rw [configurationDefect_mul_boundaryIndicator P A e y,
    mul_pow]
  rw [show
    configurationBoundaryIndicator P A e y ^ 2 =
      configurationBoundaryIndicator P A e y by
        exact partitionAtomIndicator_sq _ _ _]
  rfl

/-- A boundary atom indicator has normalized mass at most one. -/
theorem orderedBoundaryAtomMass_le_one
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (coarse : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (b : (orderedBoundaryPartition coarse e).parts) :
    orderedBoundaryAtomMass coarse e b ≤ 1 := by
  unfold orderedBoundaryAtomMass
  exact mean_le_of_le_const fun y =>
    partitionAtomIndicator_le_one _ _ y

/-- The squared remainder has normalized mean at most one. -/
theorem mean_sq_partialConfigurationWeight_le_one
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r)) :
    mean (fun x : Fin k → G =>
      partialConfigurationWeight A s x ^ 2) ≤ 1 := by
  apply mean_le_of_le_const
  intro x
  have h0 := partialConfigurationWeight_nonneg A s x
  have h1 := partialConfigurationWeight_le_one A s x
  nlinarith

/-- Boundary support inserts the canonical atom indicator into the defect
contribution without changing it. -/
theorem configurationContribution_defect_eq_localized
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s) :
    configurationContribution A s e
        (configurationDefect P A e) =
      mean fun x : Fin k → G =>
        (configurationDefect P A e
            (orderedFaceTuple e.face x) *
          configurationBoundaryIndicator P A e
            (orderedFaceTuple e.face x)) *
        partialConfigurationWeight A (s.erase e) x := by
  unfold configurationContribution
  apply congrArg mean
  funext x
  rw [mul_assoc,
    configurationBoundaryIndicator_mul_remainder
      P A s hclosed e he x]

/-- Goodness bounds the square of the selected defect contribution by its
rank-dependent defect threshold. -/
theorem configurationContribution_defect_sq_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (α β : ℕ → ℝ)
    (hgood : A.IsGood P.fine P.coarse α β)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s)
    (hβ : 0 ≤ β e.rank) :
    configurationContribution A s e
        (configurationDefect P A e) ^ 2 ≤
      β e.rank := by
  let u : (Fin k → G) → ℝ :=
    fun x =>
      configurationDefect P A e
          (orderedFaceTuple e.face x) *
        configurationBoundaryIndicator P A e
          (orderedFaceTuple e.face x)
  let v : (Fin k → G) → ℝ :=
    partialConfigurationWeight A (s.erase e)
  have hlocal :
      mean (fun x : Fin k → G => u x ^ 2) ≤
        β e.rank := by
    have hgoodLocal :=
      (hgood.atPositiveFace P A α β e).localized_defect
        (positiveFaceLowerLayer P.fine e)
        (positiveFaceLowerLayer P.coarse e)
        e.face
        (P.fine.partition e.lowerRank.succ e.face)
        (A.atom e.lowerRank.succ e.face)
        (orderedFaceTuple e.face A.witness)
        (α e.rank) (β e.rank)
    have hmass :
        orderedBoundaryAtomMass
            (positiveFaceLowerLayer P.coarse e)
            e.face
            (orderedBoundaryAtomAt
              (positiveFaceLowerLayer P.coarse e)
              e.face
              (orderedFaceTuple e.face A.witness)) ≤
          1 :=
      orderedBoundaryAtomMass_le_one _ _ _
    calc
      mean (fun x : Fin k → G => u x ^ 2) =
          mean (fun y =>
            (configurationDefect P A e y *
              configurationBoundaryIndicator P A e y) ^ 2) := by
        exact mean_comp_orderedFaceTuple e.face
          (fun y =>
            (configurationDefect P A e y *
              configurationBoundaryIndicator P A e y) ^ 2)
      _ =
          orderedLocalizedAtomDefectSq
            (positiveFaceLowerLayer P.fine e)
            (positiveFaceLowerLayer P.coarse e)
            e.face
            (P.fine.partition e.lowerRank.succ e.face)
            (A.atom e.lowerRank.succ e.face)
            (orderedBoundaryAtomAt
              (positiveFaceLowerLayer P.coarse e)
              e.face
              (orderedFaceTuple e.face A.witness)) :=
        mean_sq_configurationDefect_mul_boundaryIndicator
          P A e
      _ ≤
          β e.rank *
            orderedBoundaryAtomMass
              (positiveFaceLowerLayer P.coarse e)
              e.face
              (orderedBoundaryAtomAt
                (positiveFaceLowerLayer P.coarse e)
                e.face
                (orderedFaceTuple e.face A.witness)) :=
        hgoodLocal
      _ ≤ β e.rank := by
        exact mul_le_of_le_one_right hβ hmass
  have hv0 :
      0 ≤ mean (fun x : Fin k → G => v x ^ 2) :=
    mean_nonneg fun x => sq_nonneg _
  have hv1 :
      mean (fun x : Fin k → G => v x ^ 2) ≤ 1 :=
    mean_sq_partialConfigurationWeight_le_one
      A (s.erase e)
  calc
    configurationContribution A s e
        (configurationDefect P A e) ^ 2 =
        mean (fun x : Fin k → G => u x * v x) ^ 2 := by
      rw [configurationContribution_defect_eq_localized
        P A s hclosed e he]
    _ ≤
        mean (fun x : Fin k → G => u x ^ 2) *
          mean (fun x : Fin k → G => v x ^ 2) :=
      mean_mul_sq_le_product u v
    _ ≤
        β e.rank *
          mean (fun x : Fin k → G => v x ^ 2) :=
      mul_le_mul_of_nonneg_right hlocal hv0
    _ ≤ β e.rank :=
      mul_le_of_le_one_right hβ hv1

/-- If the scheduled defect threshold is below `δ²`, the absolute defect
contribution is at most `δ`. -/
theorem abs_configurationContribution_defect_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (α β : ℕ → ℝ)
    (hgood : A.IsGood P.fine P.coarse α β)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s)
    (hβ0 : 0 ≤ β e.rank)
    (hβδ : β e.rank ≤ δ ^ 2) :
    |configurationContribution A s e
        (configurationDefect P A e)| ≤ δ := by
  have hsquare :
      |configurationContribution A s e
          (configurationDefect P A e)| ^ 2 ≤
        δ ^ 2 := by
    rw [sq_abs]
    exact le_trans
      (configurationContribution_defect_sq_le
        P A α β hgood s hclosed e he hβ0)
      hβδ
  exact
    (sq_le_sq₀
      (abs_nonneg
        (configurationContribution A s e
          (configurationDefect P A e)))
      hδ).mp hsquare

/-! ## The one-face recurrence -/

/-- At a maximum-rank face of a downward-closed family, the partial count
satisfies the expected multiplicative recurrence, with one defect and one
uniform error. -/
theorem abs_partialConfigurationCount_sub_coarseDensity_mul_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (α β : ℕ → ℝ)
    (hgood : A.IsGood P.fine P.coarse α β)
    (ε : OrderedRegularityTolerance r)
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s)
    (hmax :
      ∀ f ∈ s.erase e, f.rank ≤ e.rank)
    (hβ0 : 0 ≤ β e.rank)
    (hβδ : β e.rank ≤ δ ^ 2) :
    |partialConfigurationCount A s -
        configurationCoarseDensity P A e *
          partialConfigurationCount A (s.erase e)| ≤
      δ + ε e.lowerRank := by
  have hdefect :
      |configurationContribution A s e
        (configurationDefect P A e)| ≤ δ :=
    abs_configurationContribution_defect_le
      P A α β hgood hδ s hclosed e he hβ0 hβδ
  have huniform :
      |configurationContribution A s e
        (configurationUniform P A e)| ≤
          ε e.lowerRank :=
    abs_configurationContribution_uniform_le
      P A ε hregular s e hmax
  rw [partialConfigurationCount_decompose
    P A s e he]
  calc
    |configurationCoarseDensity P A e *
            partialConfigurationCount A (s.erase e) +
          configurationContribution A s e
            (configurationDefect P A e) +
          configurationContribution A s e
            (configurationUniform P A e) -
        configurationCoarseDensity P A e *
          partialConfigurationCount A (s.erase e)| =
        |configurationContribution A s e
            (configurationDefect P A e) +
          configurationContribution A s e
            (configurationUniform P A e)| := by
      congr 1
      ring
    _ ≤
        |configurationContribution A s e
            (configurationDefect P A e)| +
          |configurationContribution A s e
            (configurationUniform P A e)| :=
      abs_add_le _ _
    _ ≤ δ + ε e.lowerRank :=
      add_le_add hdefect huniform

/-- Extend the genuine partial configuration count to all positive-face
families.  Non-closed families use the exact product of coarse densities;
this is only an induction device, and agrees with the genuine count on the
full downward-closed family. -/
noncomputable def extendedConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (s : Finset (PositiveOrderedFace k r)) : ℝ := by
  classical
  exact
    if IsDownwardClosedPositiveFaces s then
      partialConfigurationCount A s
    else
      ∏ e ∈ s, configurationCoarseDensity P A e

@[simp]
theorem extendedConfigurationCount_empty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine) :
    extendedConfigurationCount P A ∅ = 1 := by
  rw [extendedConfigurationCount,
    if_pos downwardClosed_empty,
    partialConfigurationCount_empty]

/-- On the full positive-face family, the extended count is the actual
configuration count. -/
theorem extendedConfigurationCount_univ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine) :
    extendedConfigurationCount P A Finset.univ =
      fullConfigurationCount A := by
  rw [extendedConfigurationCount,
    if_pos downwardClosed_univ]
  rfl

/-- Goodness gives the required lower bound for every coarse main
density. -/
theorem configurationCoarseDensity_lower
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (α β : ℕ → ℝ)
    (hgood : A.IsGood P.fine P.coarse α β)
    (e : PositiveOrderedFace k r) :
    α e.rank ≤ configurationCoarseDensity P A e :=
  (hgood.atPositiveFace P A α β e).1

/-- The totalized count satisfies a uniform recurrence on every nonempty
face family.  Closed families use a maximum-rank analytic step; non-closed
families use an exact coarse-product step. -/
theorem extendedConfigurationCount_step
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (α β : ℕ → ℝ)
    (hgood : A.IsGood P.fine P.coarse α β)
    (ε : OrderedRegularityTolerance r)
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hε : ∀ j, ε j ≤ η)
    (hβ0 : ∀ n, 0 ≤ β n)
    (hβδ : ∀ n, β n ≤ δ ^ 2)
    (s : Finset (PositiveOrderedFace k r))
    (hs : s.Nonempty) :
    ∃ e ∈ s,
      |extendedConfigurationCount P A s -
          configurationCoarseDensity P A e *
            extendedConfigurationCount P A (s.erase e)| ≤
        η + δ := by
  classical
  by_cases hclosed : IsDownwardClosedPositiveFaces s
  · obtain ⟨e, he, hmax⟩ :=
      exists_maxRank_mem s hs
    have hclosedErase :
        IsDownwardClosedPositiveFaces (s.erase e) :=
      hclosed.erase_maxRank he hmax
    refine ⟨e, he, ?_⟩
    rw [extendedConfigurationCount,
      if_pos hclosed,
      extendedConfigurationCount,
      if_pos hclosedErase]
    have hrec :=
      abs_partialConfigurationCount_sub_coarseDensity_mul_le
        P A α β hgood ε hregular hδ
        s hclosed e he
        (fun f hf => hmax f (Finset.mem_of_mem_erase hf))
        (hβ0 e.rank) (hβδ e.rank)
    have heps := hε e.lowerRank
    linarith
  · unfold IsDownwardClosedPositiveFaces at hclosed
    push Not at hclosed
    obtain ⟨f, hf, hpos, i, hboundary⟩ := hclosed
    by_cases hrest : s.erase f = ∅
    · have hsEq : s = {f} := by
        rcases (Finset.erase_eq_empty_iff s f).mp hrest with
          hsEmpty | hsSingleton
        · exact (hs.ne_empty hsEmpty).elim
        · exact hsSingleton
      refine ⟨f, hf, ?_⟩
      have hcountS :
          extendedConfigurationCount P A s =
            configurationCoarseDensity P A f := by
        rw [extendedConfigurationCount, if_neg]
        · simp [hsEq]
        · intro h
          exact hboundary (h f hf hpos i)
      have hcountErase :
          extendedConfigurationCount P A (s.erase f) = 1 := by
        rw [hrest, extendedConfigurationCount_empty]
      rw [hcountS, hcountErase, mul_one, sub_self, abs_zero]
      exact add_nonneg hη hδ
    · obtain ⟨e, heRest⟩ :
          (s.erase f).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hrest
      have heS : e ∈ s :=
        Finset.mem_of_mem_erase heRest
      have hef : e ≠ f :=
        (Finset.mem_erase.mp heRest).1
      have hfEraseE : f ∈ s.erase e :=
        Finset.mem_erase.mpr ⟨hef.symm, hf⟩
      have hclosedErase :
          ¬IsDownwardClosedPositiveFaces (s.erase e) := by
        intro h
        have hb := h f hfEraseE hpos i
        exact hboundary (Finset.mem_of_mem_erase hb)
      refine ⟨e, heS, ?_⟩
      have hcountS :
          extendedConfigurationCount P A s =
            ∏ g ∈ s,
              configurationCoarseDensity P A g := by
        rw [extendedConfigurationCount, if_neg]
        intro h
        exact hboundary (h f hf hpos i)
      have hcountErase :
          extendedConfigurationCount P A (s.erase e) =
            ∏ g ∈ s.erase e,
              configurationCoarseDensity P A g := by
        rw [extendedConfigurationCount,
          if_neg hclosedErase]
      rw [hcountS, hcountErase]
      have hprod :
          configurationCoarseDensity P A e *
              (∏ g ∈ s.erase e,
                configurationCoarseDensity P A g) =
            ∏ g ∈ s,
              configurationCoarseDensity P A g :=
        Finset.mul_prod_erase s
          (configurationCoarseDensity P A) heS
      rw [hprod, sub_self, abs_zero]
      exact add_nonneg hη hδ

/-! ## Quantitative full-count lower bound and positivity -/

/-- A good closed fine-atom configuration has full count at least the
product-density floor minus one uniform-plus-defect error per positive
ordered face. -/
theorem fullConfigurationCount_lower_bound
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (α β : ℕ → ℝ)
    (hgood : A.IsGood P.fine P.coarse α β)
    (ε : OrderedRegularityTolerance r)
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    {ρ η δ : ℝ}
    (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hα : ∀ n, ρ ≤ α n)
    (hε : ∀ j, ε j ≤ η)
    (hβ0 : ∀ n, 0 ≤ β n)
    (hβδ : ∀ n, β n ≤ δ ^ 2) :
    ρ ^ Fintype.card (PositiveOrderedFace k r) -
        (Fintype.card (PositiveOrderedFace k r) : ℝ) *
          (η + δ) ≤
      fullConfigurationCount A := by
  let count :
      Finset (PositiveOrderedFace k r) → ℝ :=
    extendedConfigurationCount P A
  let p : PositiveOrderedFace k r → ℝ :=
    configurationCoarseDensity P A
  have hempty : count ∅ = 1 :=
    extendedConfigurationCount_empty P A
  have hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1 := by
    intro e
    exact
      ⟨configurationCoarseDensity_nonneg P A e,
        configurationCoarseDensity_le_one P A e⟩
  have hpLower : ∀ e, ρ ≤ p e := by
    intro e
    exact le_trans
      (hα e.rank)
      (configurationCoarseDensity_lower
        P A α β hgood e)
  have hstep :
      ∀ s : Finset (PositiveOrderedFace k r), s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤
            η + δ := by
    intro s hs
    exact extendedConfigurationCount_step
      P A α β hgood ε hregular
      hη hδ hε hβ0 hβδ s hs
  have hbound :=
    pow_sub_card_mul_le_finiteCount
      count p hρ (add_nonneg hη hδ)
      hempty hp hpLower hstep
      (Finset.univ :
        Finset (PositiveOrderedFace k r))
  rw [show count
      (Finset.univ :
        Finset (PositiveOrderedFace k r)) =
        fullConfigurationCount A by
      exact extendedConfigurationCount_univ P A] at hbound
  simpa using hbound

/-- **Positive configuration count.**  If the density floor to the number
of positive ordered faces dominates the accumulated regularity and defect
errors, then a good closed fine-atom configuration is realized by a
positive proportion of full tuples. -/
theorem fullConfigurationCount_pos
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (α β : ℕ → ℝ)
    (hgood : A.IsGood P.fine P.coarse α β)
    (ε : OrderedRegularityTolerance r)
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    {ρ η δ : ℝ}
    (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hα : ∀ n, ρ ≤ α n)
    (hε : ∀ j, ε j ≤ η)
    (hβ0 : ∀ n, 0 ≤ β n)
    (hβδ : ∀ n, β n ≤ δ ^ 2)
    (hsmall :
      (Fintype.card (PositiveOrderedFace k r) : ℝ) *
          (η + δ) <
        ρ ^ Fintype.card (PositiveOrderedFace k r)) :
    0 < fullConfigurationCount A := by
  let count :
      Finset (PositiveOrderedFace k r) → ℝ :=
    extendedConfigurationCount P A
  let p : PositiveOrderedFace k r → ℝ :=
    configurationCoarseDensity P A
  have hempty : count ∅ = 1 :=
    extendedConfigurationCount_empty P A
  have hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1 := by
    intro e
    exact
      ⟨configurationCoarseDensity_nonneg P A e,
        configurationCoarseDensity_le_one P A e⟩
  have hpLower : ∀ e, ρ ≤ p e := by
    intro e
    exact le_trans
      (hα e.rank)
      (configurationCoarseDensity_lower
        P A α β hgood e)
  have hstep :
      ∀ s : Finset (PositiveOrderedFace k r), s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤
            η + δ := by
    intro s hs
    exact extendedConfigurationCount_step
      P A α β hgood ε hregular
      hη hδ hε hβ0 hβδ s hs
  have hpositive :=
    finiteCount_pos_of_card_mul_lt_pow
      count p hρ (add_nonneg hη hδ)
      hempty hp hpLower hstep
      (Finset.univ :
        Finset (PositiveOrderedFace k r))
      (by simpa using hsmall)
  rw [show count
      (Finset.univ :
        Finset (PositiveOrderedFace k r)) =
        fullConfigurationCount A by
      exact extendedConfigurationCount_univ P A] at hpositive
  exact hpositive

end Wikipedia.SzemeredisTheorem
