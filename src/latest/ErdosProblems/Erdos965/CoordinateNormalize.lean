import ErdosProblems.Erdos965.Countability
import ErdosProblems.Erdos965.UniformPrefix

open Function Set

universe u

namespace Erdos965
namespace FiniteColoring

variable {ι : Type u}

/-! ## Simultaneous normalization of finitely many coordinates -/

/-- A coordinate is normalized on `J` if it is constant there, or if it is
injective and every one of its strict initial segments (for the fixed
well-order) is countable. -/
def CoordinateNormalized (p : ι → HamelIndex) (J : Set ι) : Prop :=
  (∃ b, ∀ x ∈ J, p x = b) ∨
    InjOn p J ∧ ∀ x ∈ J, {y ∈ J | WellOrderingRel (p y) (p x)}.Countable

namespace CoordinateNormalized

/-- Coordinate normalization is preserved when the index set is thinned. -/
theorem mono {p : ι → HamelIndex} {J K : Set ι}
    (h : CoordinateNormalized p J) (hKJ : K ⊆ J) :
    CoordinateNormalized p K := by
  rcases h with hconst | ⟨hinj, hlower⟩
  · exact Or.inl ⟨hconst.choose, fun x hx ↦ hconst.choose_spec x (hKJ hx)⟩
  · refine Or.inr ⟨hinj.mono hKJ, ?_⟩
    intro x hx
    refine (hlower x (hKJ hx)).mono ?_
    intro y hy
    exact ⟨hKJ hy.1, hy.2⟩

end CoordinateNormalized

/-- Simultaneous coordinate normalization on an uncountable thinning of an
initial index set. -/
structure CoordinateNormalization {n : ℕ} (p : Fin n → ι → HamelIndex)
    (I J : Set ι) : Prop where
  subset : J ⊆ I
  uncountable : ¬ J.Countable
  normalized : ∀ j, CoordinateNormalized (p j) J

namespace CoordinateNormalization

/-- A simultaneous normalization remains valid after any further
uncountable thinning. -/
theorem mono {n : ℕ} {p : Fin n → ι → HamelIndex} {I J K : Set ι}
    (h : CoordinateNormalization p I J) (hKJ : K ⊆ J)
    (hKunc : ¬ K.Countable) : CoordinateNormalization p I K where
  subset := hKJ.trans h.subset
  uncountable := hKunc
  normalized j := (h.normalized j).mono hKJ

end CoordinateNormalization

/-- Normalize the coordinates in a prescribed finite set.  This is the
inductive engine used for all coordinates below. -/
private theorem exists_normalized_on_finset {n : ℕ}
    (p : Fin n → ι → HamelIndex) (s : Finset (Fin n))
    (I : Set ι) (hI : ¬ I.Countable) :
    ∃ J ⊆ I, ¬ J.Countable ∧
      ∀ j ∈ s, CoordinateNormalized (p j) J := by
  classical
  induction s using Finset.induction_on generalizing I with
  | empty =>
      exact ⟨I, Set.Subset.rfl, hI, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨J, hJI, hJunc, hJnorm⟩ := ih I hI
      obtain ⟨K, hKJ, hKunc, hKcase⟩ :=
        uncountable_constant_or_injective (p a) hJunc
      rcases hKcase with hconst | hinj
      · refine ⟨K, hKJ.trans hJI, hKunc, ?_⟩
        intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact Or.inl hconst
        · exact (hJnorm j hj).mono hKJ
      · obtain ⟨L, hLK, hLunc, hlower⟩ :=
          uncountable_lowerNormalized (r := WellOrderingRel) (p a) hKunc hinj
        refine ⟨L, hLK.trans (hKJ.trans hJI), hLunc, ?_⟩
        intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact Or.inr ⟨hinj.mono hLK, hlower⟩
        · exact (hJnorm j hj).mono (hLK.trans hKJ)

/-- Any finite family of Hamel-index-valued coordinate maps can be
simultaneously normalized on an uncountable subset. -/
theorem exists_coordinateNormalization {n : ℕ}
    (p : Fin n → ι → HamelIndex) {I : Set ι} (hI : ¬ I.Countable) :
    ∃ J, CoordinateNormalization p I J := by
  obtain ⟨J, hJI, hJunc, hnorm⟩ :=
    exists_normalized_on_finset p Finset.univ I hI
  exact ⟨J, hJI, hJunc, fun j ↦ hnorm j (Finset.mem_univ j)⟩

/-! ## Ordered coordinates of a uniform finite-set family -/

/-- The `j`th member, in ordinary increasing order, of a uniformly
`n`-element family of finite sets. -/
noncomputable def coordinate {n : ℕ} (F : ι → Finset HamelIndex)
    (hcard : ∀ i, (F i).card = n) (j : Fin n) (i : ι) : HamelIndex :=
  finsetCoord F hcard i j

theorem coordinate_mem {n : ℕ} (F : ι → Finset HamelIndex)
    (hcard : ∀ i, (F i).card = n) (j : Fin n) (i : ι) :
    coordinate F hcard j i ∈ F i := by
  exact finsetCoord_mem F hcard i j

theorem coordinate_strictMono {n : ℕ} (F : ι → Finset HamelIndex)
    (hcard : ∀ i, (F i).card = n) (i : ι) :
    StrictMono (fun j : Fin n ↦ coordinate F hcard j i) := by
  exact finsetCoord_strictMono F hcard i

/-- The ordered coordinate of a family whose cardinality is known only on
`I`.  Its value outside `I` is irrelevant; all normalization conclusions are
on subsets of `I`. -/
noncomputable def coordinateWithin {n : ℕ} (F : ι → Finset HamelIndex)
    (I : Set ι) (hcard : ∀ i ∈ I, (F i).card = n)
    (j : Fin n) (i : ι) : HamelIndex := by
  classical
  exact if hi : i ∈ I then (F i).orderEmbOfFin (hcard i hi) j
    else hamelBasis.index_nonempty.some

theorem coordinateWithin_of_mem {n : ℕ} (F : ι → Finset HamelIndex)
    (I : Set ι) (hcard : ∀ i ∈ I, (F i).card = n)
    (j : Fin n) {i : ι} (hi : i ∈ I) :
    coordinateWithin F I hcard j i = (F i).orderEmbOfFin (hcard i hi) j := by
  simp only [coordinateWithin, dif_pos hi]

theorem coordinateWithin_mem {n : ℕ} (F : ι → Finset HamelIndex)
    (I : Set ι) (hcard : ∀ i ∈ I, (F i).card = n)
    (j : Fin n) {i : ι} (hi : i ∈ I) :
    coordinateWithin F I hcard j i ∈ F i := by
  rw [coordinateWithin_of_mem F I hcard j hi]
  exact Finset.orderEmbOfFin_mem (F i) (hcard i hi) j

/-- A uniform finite-set family admits an uncountable thinning on which
each ordered coordinate is constant or injective and lower-normalized in
`WellOrderingRel`.  This is the main interface for the finite-set colouring
argument. -/
theorem exists_coordinateNormalization_of_uniformCard {n : ℕ}
    (F : ι → Finset HamelIndex) (hcard : ∀ i, (F i).card = n)
    {I : Set ι} (hI : ¬ I.Countable) :
    ∃ J, CoordinateNormalization
      (fun j i ↦ finsetCoord F hcard i j) I J :=
  exists_coordinateNormalization (fun j i ↦ finsetCoord F hcard i j) hI

/-- Relative-cardinality version of
`exists_coordinateNormalization_of_uniformCard`. -/
theorem exists_coordinateNormalization_of_uniformCardOn {n : ℕ}
    (F : ι → Finset HamelIndex) {I : Set ι}
    (hcard : ∀ i ∈ I, (F i).card = n) (hI : ¬ I.Countable) :
    ∃ J, CoordinateNormalization
      (fun j ↦ coordinateWithin F I hcard j) I J :=
  exists_coordinateNormalization (fun j ↦ coordinateWithin F I hcard j) hI

/-- Normalize all ordered coordinates of a uniform-prefix witness while
remaining inside its carrier.  Thus every prefix identity furnished by `W`
is preserved automatically. -/
theorem exists_coordinateNormalization_of_uniformPrefixWitness {n : ℕ}
    (F : ι → Finset HamelIndex) (hcard : ∀ i, (F i).card = n)
    (W : UniformPrefixWitness F hcard) :
    ∃ J, CoordinateNormalization
      (fun j i ↦ finsetCoord F hcard i j) W.carrier J :=
  Erdos965.FiniteColoring.exists_coordinateNormalization
    (fun (j : Fin n) (i : ι) ↦ finsetCoord F hcard i j) W.uncountable

end FiniteColoring
end Erdos965
