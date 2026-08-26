import ErdosProblems.Erdos633.CommonRefinement

/-!
# Congruent triangle tilings of intermediate regions

Exceptional triangle constructions contain parallelogram regions. This local
interface permits tiling such regions and gluing them back into a triangle;
coverage and disjoint interiors are always part of the data.
-/

namespace Erdos633

/-- A triangle is a one-piece congruent tiling of itself. -/
def Triangle.oneTiling (P : Triangle) : CongruentTiling P P 1 where
  tile _ := P
  congruent _ := ⟨IsometryEquiv.refl ℂ, Set.image_id _⟩
  covers := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact hi
    · intro hz
      exact Set.mem_iUnion.mpr ⟨0, hz⟩
  disjoint := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

structure RegionTiling (S : Set ℂ) (R : Triangle) (ι : Type*) where
  tile : ι → Triangle
  congruent : ∀ i, ∃ e : ℂ ≃ᵢ ℂ, e '' R.carrier = (tile i).carrier
  covers : (⋃ i, (tile i).carrier) = S
  disjoint : Pairwise fun i j =>
    Disjoint (interior (tile i).carrier) (interior (tile j).carrier)

theorem RegionTiling.tile_subset {S : Set ℂ} {R : Triangle} {ι : Type*}
    (T : RegionTiling S R ι) (i : ι) : (T.tile i).carrier ⊆ S := by
  intro z hz
  rw [← T.covers]
  exact Set.mem_iUnion.mpr ⟨i, hz⟩

def CongruentTiling.toRegionTiling {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) : RegionTiling P.carrier R (Fin N) where
  tile := T.tile
  congruent := T.congruent
  covers := T.covers
  disjoint := T.disjoint

noncomputable def RegionTiling.toCongruentTiling {S : Set ℂ} {R : Triangle}
    {ι : Type*} [Fintype ι] (T : RegionTiling S R ι) (P : Triangle) (h : S = P.carrier) :
    CongruentTiling P R (Fintype.card ι) :=
  CongruentTiling.ofIndexed T.tile T.congruent (T.covers.trans h) T.disjoint

def RegionTiling.of_region_eq {S U : Set ℂ} {R : Triangle} {ι : Type*}
    (T : RegionTiling S R ι) (h : S = U) : RegionTiling U R ι :=
  { T with covers := T.covers.trans h }

def RegionTiling.changeTile {S : Set ℂ} {R Q : Triangle} {ι : Type*}
    (T : RegionTiling S R ι) (e : ℂ ≃ᵢ ℂ) (he : e '' Q.carrier = R.carrier) :
    RegionTiling S Q ι where
  tile := T.tile
  covers := T.covers
  disjoint := T.disjoint
  congruent := by
    intro i
    obtain ⟨f, hf⟩ := T.congruent i
    refine ⟨e.trans f, ?_⟩
    change (fun z : ℂ => f (e z)) '' Q.carrier = (T.tile i).carrier
    rw [← Set.image_image f e Q.carrier, he, hf]

/-- Moving a tiled region by an isometry preserves the reference tile. -/
noncomputable def RegionTiling.mapIsometry {S : Set ℂ} {R : Triangle} {ι : Type*}
    (T : RegionTiling S R ι) (e : ℂ ≃ᵢ ℂ) : RegionTiling (e '' S) R ι where
  tile i := (T.tile i).mapIsometry e
  congruent := by
    intro i
    obtain ⟨f, hf⟩ := T.congruent i
    refine ⟨f.trans e, ?_⟩
    rw [Triangle.mapIsometry_carrier, ← hf]
    exact (Set.image_image e f R.carrier).symm
  covers := by
    simp only [Triangle.mapIsometry_carrier]
    rw [← Set.image_iUnion, T.covers]
  disjoint := by
    intro i j hij
    simp only [Triangle.mapIsometry_carrier]
    have hi := e.toHomeomorph.image_interior (T.tile i).carrier
    have hj := e.toHomeomorph.image_interior (T.tile j).carrier
    change e '' interior (T.tile i).carrier = interior (e '' (T.tile i).carrier) at hi
    change e '' interior (T.tile j).carrier = interior (e '' (T.tile j).carrier) at hj
    rw [← hi, ← hj]
    exact Set.disjoint_image_of_injective e.injective (T.disjoint hij)

/-- Glue an indexed family; different regions may have different tile counts. -/
def RegionTiling.indexedUnion {κ : Type*} {S : κ → Set ℂ} {R : Triangle}
    {ι : κ → Type*} (T : ∀ k, RegionTiling (S k) R (ι k))
    (h : Pairwise fun k l => Disjoint (interior (S k)) (interior (S l))) :
    RegionTiling (⋃ k, S k) R (Sigma ι) where
  tile i := (T i.1).tile i.2
  congruent i := (T i.1).congruent i.2
  covers := by
    ext z
    simp only [Set.mem_iUnion, Sigma.exists]
    constructor
    · rintro ⟨k, i, hi⟩
      exact ⟨k, (T k).tile_subset i hi⟩
    · rintro ⟨k, hk⟩
      rw [← (T k).covers] at hk
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hk
      exact ⟨k, i, hi⟩
  disjoint := by
    rintro ⟨k, i⟩ ⟨l, j⟩ hij
    by_cases hkl : k = l
    · subst l
      exact (T k).disjoint (fun heq => hij (congrArg (Sigma.mk k) heq))
    · exact (h hkl).mono (interior_mono ((T k).tile_subset i))
        (interior_mono ((T l).tile_subset j))

/-- Glue two tilings with pairwise disjoint interiors across the two families. -/
def RegionTiling.unionOfDisjointTiles {S U : Set ℂ} {R : Triangle} {ι κ : Type*}
    (T : RegionTiling S R ι) (V : RegionTiling U R κ)
    (h : ∀ i j, Disjoint (interior (T.tile i).carrier) (interior (V.tile j).carrier)) :
    RegionTiling (S ∪ U) R (ι ⊕ κ) where
  tile := Sum.elim T.tile V.tile
  congruent := by
    intro i
    cases i with
    | inl i => exact T.congruent i
    | inr j => exact V.congruent j
  covers := by
    calc
      (⋃ i, (Sum.elim T.tile V.tile i).carrier) =
          (⋃ i, (T.tile i).carrier) ∪ (⋃ j, (V.tile j).carrier) := by
        ext z
        simp only [Set.mem_iUnion, Set.mem_union]
        constructor
        · rintro ⟨i, hi⟩
          cases i with
          | inl i => exact Or.inl ⟨i, hi⟩
          | inr j => exact Or.inr ⟨j, hi⟩
        · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
          · exact ⟨Sum.inl i, hi⟩
          · exact ⟨Sum.inr j, hj⟩
      _ = S ∪ U := congrArg₂ (· ∪ ·) T.covers V.covers
  disjoint := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact T.disjoint (fun heq => hij (congrArg Sum.inl heq))
      | inr j => exact h i j
    | inr i =>
      cases j with
      | inl j => exact (h j i).symm
      | inr j => exact V.disjoint (fun heq => hij (congrArg Sum.inr heq))

def RegionTiling.union {S U : Set ℂ} {R : Triangle} {ι κ : Type*}
    (T : RegionTiling S R ι) (V : RegionTiling U R κ)
    (h : Disjoint (interior S) (interior U)) : RegionTiling (S ∪ U) R (ι ⊕ κ) :=
  T.unionOfDisjointTiles V fun i j =>
    h.mono (interior_mono (T.tile_subset i)) (interior_mono (V.tile_subset j))

/-- Glue three regions without assuming that interiors commute with union. -/
def RegionTiling.unionThree {S₁ S₂ S₃ : Set ℂ} {R : Triangle} {ι₁ ι₂ ι₃ : Type*}
    (T₁ : RegionTiling S₁ R ι₁) (T₂ : RegionTiling S₂ R ι₂)
    (T₃ : RegionTiling S₃ R ι₃)
    (h₁₂ : Disjoint (interior S₁) (interior S₂))
    (h₁₃ : Disjoint (interior S₁) (interior S₃))
    (h₂₃ : Disjoint (interior S₂) (interior S₃)) :
    RegionTiling ((S₁ ∪ S₂) ∪ S₃) R ((ι₁ ⊕ ι₂) ⊕ ι₃) := by
  apply (T₁.union T₂ h₁₂).unionOfDisjointTiles T₃
  intro i j
  cases i with
  | inl i =>
    exact h₁₃.mono (interior_mono (T₁.tile_subset i))
      (interior_mono (T₃.tile_subset j))
  | inr i =>
    exact h₂₃.mono (interior_mono (T₂.tile_subset i))
      (interior_mono (T₃.tile_subset j))

/-- Glue four regions using their six pairwise interior-disjointness facts.
No claim about the interior of a union is needed. -/
def RegionTiling.unionFour {S₁ S₂ S₃ S₄ : Set ℂ} {R : Triangle}
    {ι₁ ι₂ ι₃ ι₄ : Type*}
    (T₁ : RegionTiling S₁ R ι₁) (T₂ : RegionTiling S₂ R ι₂)
    (T₃ : RegionTiling S₃ R ι₃) (T₄ : RegionTiling S₄ R ι₄)
    (h₁₂ : Disjoint (interior S₁) (interior S₂))
    (h₁₃ : Disjoint (interior S₁) (interior S₃))
    (h₁₄ : Disjoint (interior S₁) (interior S₄))
    (h₂₃ : Disjoint (interior S₂) (interior S₃))
    (h₂₄ : Disjoint (interior S₂) (interior S₄))
    (h₃₄ : Disjoint (interior S₃) (interior S₄)) :
    RegionTiling (((S₁ ∪ S₂) ∪ S₃) ∪ S₄) R (((ι₁ ⊕ ι₂) ⊕ ι₃) ⊕ ι₄) := by
  let T₁₂ := T₁.union T₂ h₁₂
  have h₁₂₃ : ∀ i j, Disjoint (interior (T₁₂.tile i).carrier)
      (interior (T₃.tile j).carrier) := by
    intro i j
    cases i with
    | inl i =>
      exact h₁₃.mono (interior_mono (T₁.tile_subset i))
        (interior_mono (T₃.tile_subset j))
    | inr i =>
      exact h₂₃.mono (interior_mono (T₂.tile_subset i))
        (interior_mono (T₃.tile_subset j))
  let T₁₂₃ := T₁₂.unionOfDisjointTiles T₃ h₁₂₃
  apply T₁₂₃.unionOfDisjointTiles T₄
  intro i j
  cases i with
  | inl i =>
    cases i with
    | inl i =>
      exact h₁₄.mono (interior_mono (T₁.tile_subset i))
        (interior_mono (T₄.tile_subset j))
    | inr i =>
      exact h₂₄.mono (interior_mono (T₂.tile_subset i))
        (interior_mono (T₄.tile_subset j))
  | inr i =>
    exact h₃₄.mono (interior_mono (T₃.tile_subset i))
      (interior_mono (T₄.tile_subset j))

end Erdos633
