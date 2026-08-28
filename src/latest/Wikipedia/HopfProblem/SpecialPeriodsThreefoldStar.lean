import Wikipedia.HopfProblem.ThreefoldGluing

/-!
# Gluing a regular piece to disjoint filling pieces

Only the identifications of individual filling pieces with the regular
piece are inputs.  All other transitions, their full source descriptions,
and the cocycle are constructed here.  Distinct filling patches are
disjoint, so their transition maps have empty source.  Composing the
given partial homeomorphisms still defines those maps without choosing
points or requiring any of the pieces to be inhabited.
-/

noncomputable section

open Set Topology TopologicalSpace

universe u

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Star

/-- Local star-shaped input, with no global space or cocycle as a field.
The index `none` denotes the regular piece. -/
structure Input (B : Type u) [TopologicalSpace B] (I : Type u) where
  patch : Option I → Opens B
  cover : IsOpenCover patch
  disjoint : Pairwise (fun i j : I =>
    Disjoint (patch (some i) : Set B) (patch (some j) : Set B))
  piece : Option I → TopCat.{u}
  toBase : ∀ i, C(piece i, B)
  toBase_mem : ∀ i x, toBase i x ∈ patch i
  overlap : ∀ i, OpenPartialHomeomorph (piece (some i)) (piece none)
  source_eq : ∀ i, (overlap i).source = toBase (some i) ⁻¹' (patch none : Set B)
  target_eq : ∀ i, (overlap i).target = toBase none ⁻¹' (patch (some i) : Set B)
  preserves_base : ∀ i x, x ∈ (overlap i).source →
    toBase none (overlap i x) = toBase (some i) x

namespace Input

variable {B I : Type u} [TopologicalSpace B] (D : Input B I)

/-- Literal identity on a piece, the given map on a filling-to-regular
overlap, its inverse in the other direction, and composition between
different fillings. -/
def transition : ∀ i j : Option I, OpenPartialHomeomorph (D.piece i) (D.piece j)
  | none, none => OpenPartialHomeomorph.refl _
  | none, some j => (D.overlap j).symm
  | some i, none => D.overlap i
  | some i, some j => by
      classical
      exact if h : i = j then by
        subst j
        exact OpenPartialHomeomorph.refl _
      else (D.overlap i).trans (D.overlap j).symm

@[simp] theorem transition_none_none :
    D.transition none none = OpenPartialHomeomorph.refl (D.piece none) := rfl

@[simp] theorem transition_none_some (i : I) :
    D.transition none (some i) = (D.overlap i).symm := rfl

@[simp] theorem transition_some_none (i : I) :
    D.transition (some i) none = D.overlap i := rfl

@[simp] theorem transition_some_self (i : I) :
    D.transition (some i) (some i) = OpenPartialHomeomorph.refl (D.piece (some i)) := by
  simp [transition]

theorem transition_some_some_of_ne {i j : I} (h : i ≠ j) :
    D.transition (some i) (some j) = (D.overlap i).trans (D.overlap j).symm := by
  simp [transition, h]

@[simp] theorem transition_self (i : Option I) :
    D.transition i i = OpenPartialHomeomorph.refl (D.piece i) := by
  cases i <;> simp

theorem transition_symm (i j : Option I) :
    (D.transition i j).symm = D.transition j i := by
  cases i with
  | none => cases j <;> simp
  | some i =>
      cases j with
      | none => simp
      | some j =>
          by_cases h : i = j
          · subst j
            simp
          · rw [D.transition_some_some_of_ne h, D.transition_some_some_of_ne (Ne.symm h)]
            simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
              OpenPartialHomeomorph.symm_symm]

theorem overlap_symm_preserves_base (i : I) (x : D.piece none)
    (hx : x ∈ (D.overlap i).target) :
    D.toBase (some i) ((D.overlap i).symm x) = D.toBase none x := by
  have h := D.preserves_base i ((D.overlap i).symm x) ((D.overlap i).map_target hx)
  rw [(D.overlap i).right_inv hx] at h
  exact h.symm

@[simp] theorem toBase_preimage_own (i : Option I) :
    D.toBase i ⁻¹' (D.patch i : Set B) = univ :=
  eq_univ_of_forall (D.toBase_mem i)

theorem filling_preimage_eq_empty {i j : I} (h : i ≠ j) :
    D.toBase (some i) ⁻¹' (D.patch (some j) : Set B) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact Set.disjoint_left.mp (D.disjoint h) (D.toBase_mem (some i) x) hx

/-- Composing the actual overlaps supplies a map even when its source is
empty; there is no arbitrary-point assumption for any piece. -/
theorem transition_some_some_source_eq_empty {i j : I} (h : i ≠ j) :
    (D.transition (some i) (some j)).source = ∅ := by
  rw [D.transition_some_some_of_ne h, OpenPartialHomeomorph.trans_source]
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hy⟩
  have hb : D.toBase none (D.overlap i x) ∈ D.patch (some j) := by
    simpa only [OpenPartialHomeomorph.symm_source, D.target_eq j, mem_preimage,
      SetLike.mem_coe] using hy
  rw [D.preserves_base i x hx] at hb
  exact Set.disjoint_left.mp (D.disjoint h) (D.toBase_mem (some i) x) hb

/-- Every transition is defined on the full inverse image of the other
base patch, including the empty intersections of distinct fillings. -/
theorem transition_source_eq (i j : Option I) :
    (D.transition i j).source = D.toBase i ⁻¹' (D.patch j : Set B) := by
  cases i with
  | none =>
      cases j with
      | none => simp
      | some j => simpa using D.target_eq j
  | some i =>
      cases j with
      | none => exact D.source_eq i
      | some j =>
          by_cases h : i = j
          · subst j
            simp
          · rw [D.transition_some_some_source_eq_empty h, D.filling_preimage_eq_empty h]

theorem transition_preserves_base (i j : Option I) (x : D.piece i)
    (hx : x ∈ (D.transition i j).source) :
    D.toBase j (D.transition i j x) = D.toBase i x := by
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some j => exact D.overlap_symm_preserves_base j x hx
  | some i =>
      cases j with
      | none => exact D.preserves_base i x hx
      | some j =>
          by_cases h : i = j
          · subst j
            simp
          · rw [D.transition_some_some_source_eq_empty h] at hx
            exact hx.elim

/-- Three patches with a common base point contain a repeated index:
two distinct filling patches cannot contain that point. -/
theorem eq_or_eq_or_eq_of_common_base (i j k : Option I) {b : B}
    (hi : b ∈ D.patch i) (hj : b ∈ D.patch j) (hk : b ∈ D.patch k) :
    i = j ∨ j = k ∨ i = k := by
  have he : ∀ a c : I, b ∈ D.patch (some a) → b ∈ D.patch (some c) → a = c := by
    intro a c ha hc
    by_contra h
    exact Set.disjoint_left.mp (D.disjoint h) ha hc
  cases i with
  | none =>
      cases j with
      | none => exact Or.inl rfl
      | some j =>
          cases k with
          | none => exact Or.inr (Or.inr rfl)
          | some k => exact Or.inr (Or.inl (congrArg some (he j k hj hk)))
  | some i =>
      cases j with
      | none =>
          cases k with
          | none => exact Or.inr (Or.inl rfl)
          | some k => exact Or.inr (Or.inr (congrArg some (he i k hi hk)))
      | some j => exact Or.inl (congrArg some (he i j hi hj))

/-- The cocycle follows from inverse identities and disjointness; it is
not a compatibility hypothesis on the star input. -/
theorem transition_cocycle (i j k : Option I) (x : D.piece i)
    (hx : x ∈ (D.transition i j).source)
    (hy : D.transition i j x ∈ (D.transition j k).source) :
    D.transition j k (D.transition i j x) = D.transition i k x := by
  have hj : D.toBase i x ∈ D.patch j := by
    simpa only [D.transition_source_eq i j, mem_preimage, SetLike.mem_coe] using hx
  have hk : D.toBase i x ∈ D.patch k := by
    have h : D.toBase j (D.transition i j x) ∈ D.patch k := by
      simpa only [D.transition_source_eq j k, mem_preimage, SetLike.mem_coe] using hy
    rwa [D.transition_preserves_base i j x hx] at h
  rcases D.eq_or_eq_or_eq_of_common_base i j k (D.toBase_mem i x) hj hk with
    hij | hjk | hik
  · subst j
    simp
  · subst k
    simp
  · subst k
    rw [← D.transition_symm i j, D.transition_self]
    exact (D.transition i j).left_inv hx

/-- Full actual gluing data generated by the individual filling overlaps. -/
abbrev toData : ThreefoldGluing.Data B where
  J := Option I
  patch := D.patch
  cover := D.cover
  piece := D.piece
  toBase := D.toBase
  toBase_mem := D.toBase_mem
  transition := D.transition
  source_eq := D.transition_source_eq
  self_eq := D.transition_self
  symm_eq := D.transition_symm
  preserves_base := D.transition_preserves_base
  cocycle := D.transition_cocycle

@[simp] theorem toData_transition (i j : Option I) :
    D.toData.transition i j = D.transition i j := rfl

end Input
end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Star
