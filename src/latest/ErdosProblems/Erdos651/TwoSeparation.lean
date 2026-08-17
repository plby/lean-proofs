/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.Definitions
import ErdosProblems.Erdos651.HamSandwich
import ErdosProblems.Erdos651.Kirchberger

/-!
# Two-separated families of point clusters

This file contains the separation notions used in Propositions 2.5 and 2.7
of Pohoata--Zakharov.  All hulls below are actual convex hulls in `ℝ³`.
-/

namespace Erdos651

open Set

noncomputable section

private def vsubMatrix (a b c d : Point 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ![b - a, c - a, d - a] j i

private def orientedVolume (a b c d : Point 3) : ℝ :=
  (vsubMatrix a b c d).det

private lemma orientedVolume_eq (a b c d : Point 3) :
    orientedVolume a b c d =
      (b 0 - a 0) * ((c 1 - a 1) * (d 2 - a 2) - (c 2 - a 2) * (d 1 - a 1)) -
      (b 1 - a 1) * ((c 0 - a 0) * (d 2 - a 2) - (c 2 - a 2) * (d 0 - a 0)) +
      (b 2 - a 2) * ((c 0 - a 0) * (d 1 - a 1) - (c 1 - a 1) * (d 0 - a 0)) := by
  simp [orientedVolume, vsubMatrix, Matrix.det_fin_three]
  ring

private def orientedVolumeLinear (a b c : Point 3) : Point 3 →ₗ[ℝ] ℝ where
  toFun p := orientedVolume a b c p - orientedVolume a b c 0
  map_add' p q := by
    rw [orientedVolume_eq, orientedVolume_eq, orientedVolume_eq, orientedVolume_eq]
    change _ = _
    have hadd (i : Fin 3) : (p + q) i = p i + q i := rfl
    have hzero (i : Fin 3) : (0 : Point 3) i = 0 := rfl
    simp only [hadd, hzero]
    ring
  map_smul' r p := by
    rw [orientedVolume_eq, orientedVolume_eq, orientedVolume_eq]
    change _ = _
    have hsmul (i : Fin 3) : (r • p) i = r * p i := rfl
    have hzero (i : Fin 3) : (0 : Point 3) i = 0 := rfl
    simp only [hsmul, hzero, RingHom.id_apply]
    ring

private def orientedVolumeAffine (a b c : Point 3) : Point 3 →ᵃ[ℝ] ℝ :=
  (orientedVolumeLinear a b c).toAffineMap +
    AffineMap.const ℝ (Point 3) (orientedVolume a b c 0)

@[simp] private lemma orientedVolumeAffine_apply (a b c p : Point 3) :
    orientedVolumeAffine a b c p = orientedVolume a b c p := by
  simp [orientedVolumeAffine, orientedVolumeLinear]

private lemma orientedVolume_ne_zero_of_affineIndependent {a b c d : Point 3}
    (h : AffineIndependent ℝ ![a, b, c, d]) : orientedVolume a b c d ≠ 0 := by
  have hv : LinearIndependent ℝ ![b - a, c - a, d - a] := by
    apply (linearIndependent_equiv' (finSuccAboveEquiv (0 : Fin 4)) ?_).mpr
      ((affineIndependent_iff_linearIndependent_vsub ℝ ![a, b, c, d] 0).mp h)
    funext i
    fin_cases i <;> rfl
  have hcols : LinearIndependent ℝ (vsubMatrix a b c d).col := by
    have hmapped := hv.map' (EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot_of_injective (EuclideanSpace.equiv (Fin 3) ℝ).injective)
    have hfun :
        (fun j => (EuclideanSpace.equiv (Fin 3) ℝ) (![b - a, c - a, d - a] j)) =
          (vsubMatrix a b c d).col := by
      funext j i
      rfl
    change LinearIndependent ℝ
      (fun j => (EuclideanSpace.equiv (Fin 3) ℝ) (![b - a, c - a, d - a] j)) at hmapped
    rw [hfun] at hmapped
    exact hmapped
  exact ((Matrix.isUnit_iff_isUnit_det (vsubMatrix a b c d)).mp
    ((Matrix.linearIndependent_cols_iff_isUnit).mp hcols)).ne_zero

/-- The union of the clusters with indices in `I`. -/
def clusterUnion {k : ℕ} (X : Fin k → Finset (Point 3))
    (I : Finset (Fin k)) : Finset (Point 3) :=
  I.biUnion X

@[simp] theorem clusterUnion_empty {k : ℕ}
    (X : Fin k → Finset (Point 3)) :
    clusterUnion X ∅ = ∅ := by
  simp [clusterUnion]

@[simp] theorem clusterUnion_singleton {k : ℕ}
    (X : Fin k → Finset (Point 3)) (i : Fin k) :
    clusterUnion X {i} = X i := by
  simp [clusterUnion]

theorem clusterUnion_mono {k : ℕ} {X Y : Fin k → Finset (Point 3)}
    (hXY : ∀ i, X i ⊆ Y i) (I : Finset (Fin k)) :
    clusterUnion X I ⊆ clusterUnion Y I := by
  classical
  intro x hx
  simp only [clusterUnion, Finset.mem_biUnion] at hx ⊢
  obtain ⟨i, hi, hxi⟩ := hx
  exact ⟨i, hi, hXY i hxi⟩

theorem clusterUnion_index_mono {k : ℕ} (X : Fin k → Finset (Point 3))
    {I J : Finset (Fin k)} (hIJ : I ⊆ J) :
    clusterUnion X I ⊆ clusterUnion X J := by
  classical
  intro x hx
  simp only [clusterUnion, Finset.mem_biUnion] at hx ⊢
  obtain ⟨i, hi, hxi⟩ := hx
  exact ⟨i, hIJ hi, hxi⟩

/-- The point set obtained by taking every cluster. -/
def allClusters {k : ℕ} (X : Fin k → Finset (Point 3)) :
    Finset (Point 3) :=
  clusterUnion X Finset.univ

theorem mem_allClusters_iff {k : ℕ} {X : Fin k → Finset (Point 3)}
    {x : Point 3} :
    x ∈ allClusters X ↔ ∃ i, x ∈ X i := by
  classical
  simp [allClusters, clusterUnion]

/-- The clusters are pairwise disjoint as finite point sets. -/
def PairwiseDisjointClusters {k : ℕ}
    (X : Fin k → Finset (Point 3)) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → Disjoint (X i) (X j)

/-- Pohoata--Zakharov's `2`-separation condition.  Convex hulls belonging
to two disjoint pairs of cluster indices do not meet. -/
def TwoSeparatedClusters {k : ℕ}
    (X : Fin k → Finset (Point 3)) : Prop :=
  ∀ ⦃i j i' j' : Fin k⦄,
    i ≠ j → i' ≠ j' →
    Disjoint ({i, j} : Finset (Fin k)) {i', j'} →
    Disjoint
      (convexHull ℝ ((X i ∪ X j : Finset (Point 3)) : Set (Point 3)))
      (convexHull ℝ ((X i' ∪ X j' : Finset (Point 3)) : Set (Point 3)))

/-- The strong convex-position hypothesis for a family of clusters: the
convex hull of any one cluster misses the hull of all the other clusters. -/
def StrongConvexPositionClusters {k : ℕ}
    (X : Fin k → Finset (Point 3)) : Prop :=
  ∀ i,
    Disjoint
      (convexHull ℝ ((X i : Finset (Point 3)) : Set (Point 3)))
      (convexHull ℝ
        ((clusterUnion X (Finset.univ.erase i) : Finset (Point 3)) : Set (Point 3)))

theorem PairwiseDisjointClusters.mono {k : ℕ}
    {X Y : Fin k → Finset (Point 3)}
    (hX : PairwiseDisjointClusters X) (hYX : ∀ i, Y i ⊆ X i) :
    PairwiseDisjointClusters Y := by
  intro i j hij
  exact (hX hij).mono (hYX i) (hYX j)

theorem TwoSeparatedClusters.mono {k : ℕ}
    {X Y : Fin k → Finset (Point 3)}
    (hX : TwoSeparatedClusters X) (hYX : ∀ i, Y i ⊆ X i) :
    TwoSeparatedClusters Y := by
  intro i j i' j' hij hi'j' hpairs
  apply (hX hij hi'j' hpairs).mono
  · exact convexHull_mono (by
      intro x hx
      simp only [Finset.coe_union, mem_union, Finset.mem_coe] at hx ⊢
      exact hx.elim (fun hxi => Or.inl (hYX i hxi))
        (fun hxj => Or.inr (hYX j hxj)))
  · exact convexHull_mono (by
      intro x hx
      simp only [Finset.coe_union, mem_union, Finset.mem_coe] at hx ⊢
      exact hx.elim (fun hxi => Or.inl (hYX i' hxi))
        (fun hxj => Or.inr (hYX j' hxj)))

theorem StrongConvexPositionClusters.mono {k : ℕ}
    {X Y : Fin k → Finset (Point 3)}
    (hX : StrongConvexPositionClusters X) (hYX : ∀ i, Y i ⊆ X i) :
    StrongConvexPositionClusters Y := by
  intro i
  apply (hX i).mono
  · exact convexHull_mono (by
      intro x hx
      exact hYX i hx)
  · exact convexHull_mono (clusterUnion_mono hYX _)

/-- Strong convex position in particular forces distinct clusters to be
disjoint.  This is useful when assigning a Kirchberger witness point to its
unique cluster. -/
theorem StrongConvexPositionClusters.pairwiseDisjoint {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (hX : StrongConvexPositionClusters X) :
    PairwiseDisjointClusters X := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro y hyi hyj
  have hyHullI : y ∈ convexHull ℝ ((X i : Finset (Point 3)) : Set (Point 3)) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr hyi)
  have hj : j ∈ (Finset.univ.erase i : Finset (Fin k)) := by
    simp [hij.symm]
  have hyOthers : y ∈ clusterUnion X (Finset.univ.erase i) := by
    simp only [clusterUnion, Finset.mem_biUnion]
    exact ⟨j, hj, hyj⟩
  have hyHullOthers :
      y ∈ convexHull ℝ
        ((clusterUnion X (Finset.univ.erase i) : Finset (Point 3)) :
          Set (Point 3)) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr hyOthers)
  exact Set.disjoint_left.1 (hX i) hyHullI hyHullOthers

/-! ### The iterative two-separation selection -/

/-- One of the three unordered pairings of four different cluster indices.
The inequalities order each pair, and put first the pair containing the
least of the four indices.  Thus every pairing is represented exactly once. -/
@[ext] structure SeparationCut (k : ℕ) where
  p₁ : Fin k
  p₂ : Fin k
  n₁ : Fin k
  n₂ : Fin k
  hp : p₁ < p₂
  hn : n₁ < n₂
  hfirst : p₁ < n₁
  hdisj : Disjoint ({p₁, p₂} : Finset (Fin k)) {n₁, n₂}
  deriving DecidableEq, Fintype

namespace SeparationCut

def Contains {k : ℕ} (c : SeparationCut k) (i : Fin k) : Prop :=
  i = c.p₁ ∨ i = c.p₂ ∨ i = c.n₁ ∨ i = c.n₂

instance {k : ℕ} (c : SeparationCut k) (i : Fin k) : Decidable (c.Contains i) := by
  unfold Contains
  infer_instance

@[simp] theorem contains_p₁ {k : ℕ} (c : SeparationCut k) : c.Contains c.p₁ :=
  Or.inl rfl

@[simp] theorem contains_p₂ {k : ℕ} (c : SeparationCut k) : c.Contains c.p₂ :=
  Or.inr (Or.inl rfl)

@[simp] theorem contains_n₁ {k : ℕ} (c : SeparationCut k) : c.Contains c.n₁ :=
  Or.inr (Or.inr (Or.inl rfl))

@[simp] theorem contains_n₂ {k : ℕ} (c : SeparationCut k) : c.Contains c.n₂ :=
  Or.inr (Or.inr (Or.inr rfl))

theorem pair_ne {k : ℕ} (c : SeparationCut k) : c.p₁ ≠ c.p₂ := ne_of_lt c.hp

theorem neg_ne {k : ℕ} (c : SeparationCut k) : c.n₁ ≠ c.n₂ := ne_of_lt c.hn

theorem cross_ne {k : ℕ} (c : SeparationCut k) :
    c.p₁ ≠ c.n₁ ∧ c.p₁ ≠ c.n₂ ∧
      c.p₂ ≠ c.n₁ ∧ c.p₂ ≠ c.n₂ := by
  have hd := Finset.disjoint_left.mp c.hdisj
  constructor
  · intro h
    exact hd (a := c.p₁) (by simp) (by simp [h])
  constructor
  · intro h
    exact hd (a := c.p₁) (by simp) (by simp [h])
  constructor
  · intro h
    exact hd (a := c.p₂) (by simp) (by simp [h])
  · intro h
    exact hd (a := c.p₂) (by simp) (by simp [h])

/-- For a fixed participating index, a cut is determined by its partner and
the ordered endpoints of the other pair. -/
private def codeAt {k : ℕ} (i : Fin k) (c : SeparationCut k) :
    Fin k × Fin k × Fin k :=
  if i = c.p₁ then (c.p₂, c.n₁, c.n₂)
  else if i = c.p₂ then (c.p₁, c.n₁, c.n₂)
  else if i = c.n₁ then (c.n₂, c.p₁, c.p₂)
  else (c.n₁, c.p₁, c.p₂)

private theorem codeAt_p₁ {k : ℕ} (c : SeparationCut k) :
    codeAt c.p₁ c = (c.p₂, c.n₁, c.n₂) := by
  simp [codeAt]

private theorem codeAt_p₂ {k : ℕ} (c : SeparationCut k) :
    codeAt c.p₂ c = (c.p₁, c.n₁, c.n₂) := by
  simp [codeAt, c.pair_ne.symm]

private theorem codeAt_n₁ {k : ℕ} (c : SeparationCut k) :
    codeAt c.n₁ c = (c.n₂, c.p₁, c.p₂) := by
  obtain ⟨hp₁n₁, _, hp₂n₁, _⟩ := c.cross_ne
  simp [codeAt, hp₁n₁.symm, hp₂n₁.symm]

private theorem codeAt_n₂ {k : ℕ} (c : SeparationCut k) :
    codeAt c.n₂ c = (c.n₁, c.p₁, c.p₂) := by
  obtain ⟨_, hp₁n₂, _, hp₂n₂⟩ := c.cross_ne
  simp [codeAt, hp₁n₂.symm, hp₂n₂.symm, c.neg_ne.symm]

private theorem codeAt_injective {k : ℕ} (i : Fin k) :
    Set.InjOn (codeAt i) {c : SeparationCut k | c.Contains i} := by
  intro c hc d hd hcode
  change c.Contains i at hc
  change d.Contains i at hd
  have chp := c.hp
  have chn := c.hn
  have chfirst := c.hfirst
  have dhp := d.hp
  have dhn := d.hn
  have dhfirst := d.hfirst
  have codeP₁ (e : SeparationCut k) (h : i = e.p₁) :
      codeAt i e = (e.p₂, e.n₁, e.n₂) := by
    rw [h]
    exact codeAt_p₁ e
  have codeP₂ (e : SeparationCut k) (h : i = e.p₂) :
      codeAt i e = (e.p₁, e.n₁, e.n₂) := by
    rw [h]
    exact codeAt_p₂ e
  have codeN₁ (e : SeparationCut k) (h : i = e.n₁) :
      codeAt i e = (e.n₂, e.p₁, e.p₂) := by
    rw [h]
    exact codeAt_n₁ e
  have codeN₂ (e : SeparationCut k) (h : i = e.n₂) :
      codeAt i e = (e.n₁, e.p₁, e.p₂) := by
    rw [h]
    exact codeAt_n₂ e
  rcases hc with hc | hc | hc | hc <;>
    rcases hd with hd | hd | hd | hd
  all_goals first
    | rw [codeP₁ c hc, codeP₁ d hd] at hcode
    | rw [codeP₁ c hc, codeP₂ d hd] at hcode
    | rw [codeP₁ c hc, codeN₁ d hd] at hcode
    | rw [codeP₁ c hc, codeN₂ d hd] at hcode
    | rw [codeP₂ c hc, codeP₁ d hd] at hcode
    | rw [codeP₂ c hc, codeP₂ d hd] at hcode
    | rw [codeP₂ c hc, codeN₁ d hd] at hcode
    | rw [codeP₂ c hc, codeN₂ d hd] at hcode
    | rw [codeN₁ c hc, codeP₁ d hd] at hcode
    | rw [codeN₁ c hc, codeP₂ d hd] at hcode
    | rw [codeN₁ c hc, codeN₁ d hd] at hcode
    | rw [codeN₁ c hc, codeN₂ d hd] at hcode
    | rw [codeN₂ c hc, codeP₁ d hd] at hcode
    | rw [codeN₂ c hc, codeP₂ d hd] at hcode
    | rw [codeN₂ c hc, codeN₁ d hd] at hcode
    | rw [codeN₂ c hc, codeN₂ d hd] at hcode
  all_goals simp only [Prod.mk.injEq] at hcode
  all_goals apply SeparationCut.ext <;> omega

theorem number_containing_le_cube {k : ℕ} (i : Fin k) :
    ((Finset.univ : Finset (SeparationCut k)).filter fun c ↦ c.Contains i).card ≤ k ^ 3 := by
  classical
  let C := (Finset.univ : Finset (SeparationCut k)).filter fun c ↦ c.Contains i
  have hinj : Set.InjOn (codeAt i) (C : Set (SeparationCut k)) := by
    intro c hc d hd
    apply codeAt_injective i
    · exact (Finset.mem_filter.mp hc).2
    · exact (Finset.mem_filter.mp hd).2
  have himage : (C.image (codeAt i)).card = C.card :=
    Finset.card_image_iff.mpr hinj
  have hsub : C.image (codeAt i) ⊆ Finset.univ := Finset.subset_univ _
  calc
    C.card = (C.image (codeAt i)).card := himage.symm
    _ ≤ (Finset.univ : Finset (Fin k × Fin k × Fin k)).card := Finset.card_le_card hsub
    _ = k ^ 3 := by simp [pow_succ, mul_assoc]

/-- Replace the four participating clusters by the four selected halves. -/
private noncomputable def selectedFamily {k : ℕ}
    (Y : Fin k → Finset (Point 3)) (c : SeparationCut k)
    (S : OrientedHalfSelection (Y c.p₁) (Y c.p₂) (Y c.n₁) (Y c.n₂)) :
    Fin k → Finset (Point 3) := fun i ↦
  if i = c.p₁ then S.Y₁
  else if i = c.p₂ then S.Y₂
  else if i = c.n₁ then S.Y₃
  else if i = c.n₂ then S.Y₄
  else Y i

private theorem selectedFamily_subset {k : ℕ}
    {Y : Fin k → Finset (Point 3)} (c : SeparationCut k)
    (S : OrientedHalfSelection (Y c.p₁) (Y c.p₂) (Y c.n₁) (Y c.n₂)) :
    ∀ i, selectedFamily Y c S i ⊆ Y i := by
  intro i
  obtain ⟨hp₁n₁, hp₁n₂, hp₂n₁, hp₂n₂⟩ := c.cross_ne
  by_cases h₁ : i = c.p₁
  · subst i
    simpa [selectedFamily, c.pair_ne, hp₁n₁, hp₁n₂] using S.half₁.1
  by_cases h₂ : i = c.p₂
  · subst i
    simpa [selectedFamily, c.pair_ne.symm, hp₂n₁, hp₂n₂] using S.half₂.1
  by_cases h₃ : i = c.n₁
  · subst i
    simpa [selectedFamily, h₁, h₂, c.neg_ne, hp₁n₁.symm,
      hp₂n₁.symm] using S.half₃.1
  by_cases h₄ : i = c.n₂
  · subst i
    simpa [selectedFamily, h₁, h₂, h₃, c.neg_ne.symm,
      hp₁n₂.symm, hp₂n₂.symm] using S.half₄.1
  · simp [selectedFamily, h₁, h₂, h₃, h₄]

private theorem selectedFamily_half {k : ℕ}
    {Y : Fin k → Finset (Point 3)} (c : SeparationCut k)
    (S : OrientedHalfSelection (Y c.p₁) (Y c.p₂) (Y c.n₁) (Y c.n₂))
    (i : Fin k) :
    (Y i).card ≤ 2 ^ (if c.Contains i then 1 else 0) *
      (selectedFamily Y c S i).card := by
  obtain ⟨hp₁n₁, hp₁n₂, hp₂n₁, hp₂n₂⟩ := c.cross_ne
  by_cases h₁ : i = c.p₁
  · subst i
    simpa [selectedFamily, c.pair_ne, hp₁n₁, hp₁n₂] using S.half₁.2
  by_cases h₂ : i = c.p₂
  · subst i
    simpa [selectedFamily, c.pair_ne.symm, hp₂n₁, hp₂n₂] using S.half₂.2
  by_cases h₃ : i = c.n₁
  · subst i
    simpa [selectedFamily, h₁, h₂, c.neg_ne, hp₁n₁.symm,
      hp₂n₁.symm, Contains] using S.half₃.2
  by_cases h₄ : i = c.n₂
  · subst i
    simpa [selectedFamily, h₁, h₂, h₃, c.neg_ne.symm,
      hp₁n₂.symm, hp₂n₂.symm, Contains] using S.half₄.2
  · have hnot : ¬ c.Contains i := by
      simp only [Contains, not_or]
      exact ⟨h₁, h₂, h₃, h₄⟩
    simp [selectedFamily, h₁, h₂, h₃, h₄, hnot]

private theorem selectedFamily_separates {k : ℕ}
    {Y : Fin k → Finset (Point 3)} (c : SeparationCut k)
    (S : OrientedHalfSelection (Y c.p₁) (Y c.p₂) (Y c.n₁) (Y c.n₂)) :
    Disjoint
      (convexHull ℝ
        (((selectedFamily Y c S c.p₁) ∪ (selectedFamily Y c S c.p₂) :
          Finset (Point 3)) : Set (Point 3)))
      (convexHull ℝ
        (((selectedFamily Y c S c.n₁) ∪ (selectedFamily Y c S c.n₂) :
          Finset (Point 3)) : Set (Point 3))) := by
  obtain ⟨hp₁n₁, hp₁n₂, hp₂n₁, hp₂n₂⟩ := c.cross_ne
  have e₁ : selectedFamily Y c S c.p₁ = S.Y₁ := by
    simp [selectedFamily]
  have e₂ : selectedFamily Y c S c.p₂ = S.Y₂ := by
    simp [selectedFamily, c.pair_ne.symm]
  have e₃ : selectedFamily Y c S c.n₁ = S.Y₃ := by
    simp [selectedFamily, hp₁n₁.symm, hp₂n₁.symm]
  have e₄ : selectedFamily Y c S c.n₂ = S.Y₄ := by
    simp [selectedFamily, hp₁n₂.symm, hp₂n₂.symm, c.neg_ne.symm]
  simpa only [e₁, e₂, e₃, e₄] using S.convexHulls_disjoint

end SeparationCut

/-- A current family together with the fact that it was obtained by shrinking
the original clusters. -/
private structure ClusterSubfamily {k : ℕ}
    (X : Fin k → Finset (Point 3)) where
  family : Fin k → Finset (Point 3)
  subset : ∀ i, family i ⊆ X i

private theorem allClusters_card_ge_four_of_cut {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (c : SeparationCut k) : 4 ≤ (allClusters X).card := by
  classical
  have hne (i : Fin k) : (X i).Nonempty := by
    apply Finset.card_pos.mp
    have := hcard i
    have : 0 < 2 ^ (k ^ 3) := pow_pos (by omega : 0 < (2 : ℕ)) _
    omega
  choose xp hxp using fun i ↦ hne i
  let W : Finset (Point 3) := {xp c.p₁, xp c.p₂, xp c.n₁, xp c.n₂}
  have hxp_ne {i j : Fin k} (hij : i ≠ j) : xp i ≠ xp j := by
    intro heq
    have hd := hdisj hij
    rw [Finset.disjoint_left] at hd
    have hxj : xp i ∈ X j := by simpa [heq] using hxp j
    exact hd (hxp i) hxj
  have hWcard : W.card = 4 := by
    obtain ⟨hp₁n₁, hp₁n₂, hp₂n₁, hp₂n₂⟩ := c.cross_ne
    simp [W, hxp_ne c.pair_ne, hxp_ne c.neg_ne, hxp_ne hp₁n₁,
      hxp_ne hp₁n₂, hxp_ne hp₂n₁, hxp_ne hp₂n₂]
  have hWU : W ⊆ allClusters X := by
    intro y hy
    simp only [W, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    all_goals rw [mem_allClusters_iff]; exact ⟨_, hxp _⟩
  rw [← hWcard]
  exact Finset.card_le_card hWU

private theorem cut_pair_disjoint {k : ℕ}
    {Y : Fin k → Finset (Point 3)}
    (hY : PairwiseDisjointClusters Y) (c : SeparationCut k) :
    Disjoint (Y c.p₁ ∪ Y c.p₂) (Y c.n₁ ∪ Y c.n₂) := by
  rw [Finset.disjoint_left]
  intro y hyp hyn
  rcases Finset.mem_union.mp hyp with hyp | hyp <;>
    rcases Finset.mem_union.mp hyn with hyn | hyn
  · exact Finset.disjoint_left.mp (hY c.cross_ne.1) hyp hyn
  · exact Finset.disjoint_left.mp (hY c.cross_ne.2.1) hyp hyn
  · exact Finset.disjoint_left.mp (hY c.cross_ne.2.2.1) hyp hyn
  · exact Finset.disjoint_left.mp (hY c.cross_ne.2.2.2) hyp hyn

/-- Perform one of the finitely many strict ham-sandwich cuts. -/
private noncomputable def applySeparationCut {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (c : SeparationCut k) (Y : ClusterSubfamily X) : ClusterSubfamily X := by
  let U := allClusters X
  have hYU (i : Fin k) : Y.family i ⊆ U := by
    intro y hy
    rw [mem_allClusters_iff]
    exact ⟨i, Y.subset i hy⟩
  let S := Classical.choice (exists_orientedHalfSelection_of_subset_ambient
    U (Y.family c.p₁) (Y.family c.p₂) (Y.family c.n₁) (Y.family c.n₂)
    (hYU c.p₁) (hYU c.p₂) (hYU c.n₁) (hYU c.n₂)
    (cut_pair_disjoint (hdisj.mono Y.subset) c)
    (allClusters_card_ge_four_of_cut hdisj hcard c) hgp)
  exact
    { family := SeparationCut.selectedFamily Y.family c S
      subset := fun i ↦ (SeparationCut.selectedFamily_subset c S i).trans (Y.subset i) }

private theorem applySeparationCut_subset {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (c : SeparationCut k) (Y : ClusterSubfamily X) :
    ∀ i, (applySeparationCut X hdisj hcard hgp c Y).family i ⊆ Y.family i := by
  intro i
  exact SeparationCut.selectedFamily_subset _ _ _

private theorem applySeparationCut_half {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (c : SeparationCut k) (Y : ClusterSubfamily X) (i : Fin k) :
    (Y.family i).card ≤ 2 ^ (if c.Contains i then 1 else 0) *
      ((applySeparationCut X hdisj hcard hgp c Y).family i).card := by
  exact SeparationCut.selectedFamily_half _ _ _

private theorem applySeparationCut_separates {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (c : SeparationCut k) (Y : ClusterSubfamily X) :
    Disjoint
      (convexHull ℝ
        ((((applySeparationCut X hdisj hcard hgp c Y).family c.p₁) ∪
          ((applySeparationCut X hdisj hcard hgp c Y).family c.p₂) :
          Finset (Point 3)) : Set (Point 3)))
      (convexHull ℝ
        ((((applySeparationCut X hdisj hcard hgp c Y).family c.n₁) ∪
          ((applySeparationCut X hdisj hcard hgp c Y).family c.n₂) :
          Finset (Point 3)) : Set (Point 3))) := by
  exact SeparationCut.selectedFamily_separates _ _

private noncomputable def runSeparationCuts {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X)) :
    List (SeparationCut k) → ClusterSubfamily X → ClusterSubfamily X
  | [], Y => Y
  | c :: cs, Y => runSeparationCuts X hdisj hcard hgp cs
      (applySeparationCut X hdisj hcard hgp c Y)

private theorem runSeparationCuts_subset {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (cs : List (SeparationCut k)) (Y : ClusterSubfamily X) :
    ∀ i, (runSeparationCuts X hdisj hcard hgp cs Y).family i ⊆ Y.family i := by
  induction cs generalizing Y with
  | nil => exact fun i ↦ Finset.Subset.rfl
  | cons c cs ih =>
      intro i
      exact (ih _ i).trans (applySeparationCut_subset X hdisj hcard hgp c Y i)

private theorem runSeparationCuts_loss {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (cs : List (SeparationCut k)) (Y : ClusterSubfamily X) (i : Fin k) :
    (Y.family i).card ≤
      2 ^ (cs.countP fun c ↦ c.Contains i) *
        ((runSeparationCuts X hdisj hcard hgp cs Y).family i).card := by
  induction cs generalizing Y with
  | nil => simp [runSeparationCuts]
  | cons c cs ih =>
      let Z := applySeparationCut X hdisj hcard hgp c Y
      have hstep := applySeparationCut_half X hdisj hcard hgp c Y i
      have htail := ih Z
      calc
        (Y.family i).card ≤ 2 ^ (if c.Contains i then 1 else 0) * (Z.family i).card := hstep
        _ ≤ 2 ^ (if c.Contains i then 1 else 0) *
              (2 ^ (cs.countP fun d ↦ d.Contains i) *
                ((runSeparationCuts X hdisj hcard hgp cs Z).family i).card) :=
          Nat.mul_le_mul_left _ htail
        _ = 2 ^ ((c :: cs).countP fun d ↦ d.Contains i) *
              ((runSeparationCuts X hdisj hcard hgp (c :: cs) Y).family i).card := by
          simp only [List.countP_cons, runSeparationCuts]
          split <;> simp_all [pow_succ, Z] <;> ring

private theorem runSeparationCuts_separates {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X))
    (cs : List (SeparationCut k)) (Y : ClusterSubfamily X)
    {c : SeparationCut k} (hc : c ∈ cs) :
    Disjoint
      (convexHull ℝ
        (((runSeparationCuts X hdisj hcard hgp cs Y).family c.p₁ ∪
          (runSeparationCuts X hdisj hcard hgp cs Y).family c.p₂ :
          Finset (Point 3)) : Set (Point 3)))
      (convexHull ℝ
        (((runSeparationCuts X hdisj hcard hgp cs Y).family c.n₁ ∪
          (runSeparationCuts X hdisj hcard hgp cs Y).family c.n₂ :
          Finset (Point 3)) : Set (Point 3))) := by
  induction cs generalizing Y with
  | nil => simp at hc
  | cons d ds ih =>
      rw [List.mem_cons] at hc
      let Z := applySeparationCut X hdisj hcard hgp d Y
      rcases hc with hcd | hc
      · subst c
        apply (applySeparationCut_separates X hdisj hcard hgp d Y).mono
        all_goals
          apply convexHull_mono
          intro y hy
          simp only [Finset.coe_union, mem_union, Finset.mem_coe] at hy ⊢
          exact hy.elim
            (fun h ↦ Or.inl (runSeparationCuts_subset X hdisj hcard hgp ds Z _ h))
            (fun h ↦ Or.inr (runSeparationCuts_subset X hdisj hcard hgp ds Z _ h))
      · exact ih Z hc

private theorem pair_disjoint_of_cross_ne {α : Type*} [DecidableEq α]
    {a b c d : α} (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    Disjoint ({a, b} : Finset α) {c, d} := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂
  rcases hx₁ with hxa | hxb <;> rcases hx₂ with hxc | hxd
  · exact hac (hxa.symm.trans hxc)
  · exact had (hxa.symm.trans hxd)
  · exact hbc (hxb.symm.trans hxc)
  · exact hbd (hxb.symm.trans hxd)

private theorem vector4_injective_of_pairwise {α : Type*}
    (a b c d : α) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective ![a, b, c, d] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem exists_separationCut_of_ordered_pairs {k : ℕ}
    {a b c d : Fin k} (hab : a < b) (hcd : c < d)
    (hdisj : Disjoint ({a, b} : Finset (Fin k)) {c, d}) :
    ∃ q : SeparationCut k,
      (q.p₁ = a ∧ q.p₂ = b ∧ q.n₁ = c ∧ q.n₂ = d) ∨
      (q.p₁ = c ∧ q.p₂ = d ∧ q.n₁ = a ∧ q.n₂ = b) := by
  have hac : a ≠ c := by
    intro h
    subst c
    have hd := Finset.disjoint_left.mp hdisj
    exact hd (a := a) (by simp) (by simp)
  rcases lt_or_gt_of_ne hac with hac | hca
  · exact ⟨⟨a, b, c, d, hab, hcd, hac, hdisj⟩, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  · exact ⟨⟨c, d, a, b, hcd, hab, hca, hdisj.symm⟩,
      Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩

private theorem exists_separationCut_of_pairs {k : ℕ}
    {i j i' j' : Fin k} (hij : i ≠ j) (hi'j' : i' ≠ j')
    (hdisj : Disjoint ({i, j} : Finset (Fin k)) {i', j'}) :
    ∃ q : SeparationCut k,
      (((q.p₁ = i ∧ q.p₂ = j) ∨ (q.p₁ = j ∧ q.p₂ = i)) ∧
        ((q.n₁ = i' ∧ q.n₂ = j') ∨ (q.n₁ = j' ∧ q.n₂ = i'))) ∨
      (((q.p₁ = i' ∧ q.p₂ = j') ∨ (q.p₁ = j' ∧ q.p₂ = i')) ∧
        ((q.n₁ = i ∧ q.n₂ = j) ∨ (q.n₁ = j ∧ q.n₂ = i))) := by
  rcases lt_or_gt_of_ne hij with hij | hji <;>
    rcases lt_or_gt_of_ne hi'j' with hi'j' | hj'i'
  · obtain ⟨q, hq | hq⟩ := exists_separationCut_of_ordered_pairs hij hi'j' hdisj
    · exact ⟨q, Or.inl ⟨Or.inl ⟨hq.1, hq.2.1⟩, Or.inl ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
    · exact ⟨q, Or.inr ⟨Or.inl ⟨hq.1, hq.2.1⟩, Or.inl ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
  · have hd : Disjoint ({i, j} : Finset (Fin k)) {j', i'} := by
      simpa [Finset.pair_comm] using hdisj
    obtain ⟨q, hq | hq⟩ := exists_separationCut_of_ordered_pairs hij hj'i' hd
    · exact ⟨q, Or.inl ⟨Or.inl ⟨hq.1, hq.2.1⟩, Or.inr ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
    · exact ⟨q, Or.inr ⟨Or.inr ⟨hq.1, hq.2.1⟩, Or.inl ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
  · have hd : Disjoint ({j, i} : Finset (Fin k)) {i', j'} := by
      simpa [Finset.pair_comm] using hdisj
    obtain ⟨q, hq | hq⟩ := exists_separationCut_of_ordered_pairs hji hi'j' hd
    · exact ⟨q, Or.inl ⟨Or.inr ⟨hq.1, hq.2.1⟩, Or.inl ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
    · exact ⟨q, Or.inr ⟨Or.inl ⟨hq.1, hq.2.1⟩, Or.inr ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
  · have hd : Disjoint ({j, i} : Finset (Fin k)) {j', i'} := by
      simpa [Finset.pair_comm] using hdisj
    obtain ⟨q, hq | hq⟩ := exists_separationCut_of_ordered_pairs hji hj'i' hd
    · exact ⟨q, Or.inl ⟨Or.inr ⟨hq.1, hq.2.1⟩, Or.inr ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩
    · exact ⟨q, Or.inr ⟨Or.inr ⟨hq.1, hq.2.1⟩, Or.inr ⟨hq.2.2.1, hq.2.2.2⟩⟩⟩

/-- Pohoata--Zakharov Proposition 2.5.  Processing the three pairings of
every four indices loses at most a factor `2^(k^3)` from each cluster. -/
theorem exists_twoSeparated_subclusters {k : ℕ}
    (X : Fin k → Finset (Point 3))
    (hdisj : PairwiseDisjointClusters X)
    (hcard : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition 3 (allClusters X)) :
    ∃ Y : Fin k → Finset (Point 3),
      (∀ i, Y i ⊆ X i) ∧ TwoSeparatedClusters Y ∧
        ∀ i, (X i).card ≤ 2 ^ (k ^ 3) * (Y i).card := by
  classical
  let initial : ClusterSubfamily X := ⟨X, fun _ ↦ Finset.Subset.rfl⟩
  let cuts : List (SeparationCut k) := (Finset.univ : Finset (SeparationCut k)).toList
  let final := runSeparationCuts X hdisj hcard hgp cuts initial
  refine ⟨final.family, final.subset, ?_, ?_⟩
  · intro i j i' j' hij hi'j' hpairs
    obtain ⟨q, hq | hq⟩ := exists_separationCut_of_pairs hij hi'j' hpairs
    · obtain ⟨hp, hn⟩ := hq
      have hsep := runSeparationCuts_separates X hdisj hcard hgp cuts initial
        (c := q) (by simp [cuts])
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals simpa only [Finset.union_comm] using hsep
    · obtain ⟨hp, hn⟩ := hq
      have hsep := runSeparationCuts_separates X hdisj hcard hgp cuts initial
        (c := q) (by simp [cuts])
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals simpa only [Finset.union_comm] using hsep.symm
  · intro i
    have hloss := runSeparationCuts_loss X hdisj hcard hgp cuts initial i
    have hcount : (cuts.countP fun c ↦ c.Contains i) ≤ k ^ 3 := by
      rw [← (Finset.univ : Finset (SeparationCut k)).nodup_toList.card_eq_countP]
      simpa [cuts] using SeparationCut.number_containing_le_cube i
    calc
      (X i).card ≤ 2 ^ (cuts.countP fun c ↦ c.Contains i) * (final.family i).card := hloss
      _ ≤ 2 ^ (k ^ 3) * (final.family i).card := by
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hcount)

/-! ### The oriented-matroid core of pattern lifting -/

private theorem convexHull_image_subset_clusterHull {k n : ℕ}
    {X : Fin k → Finset (Point 3)} {idx : Fin n → Fin k}
    {p : Fin n → Point 3}
    (hp : ∀ t, p t ∈ convexHull ℝ ((X (idx t) : Finset (Point 3)) : Set (Point 3)))
    (S : Finset (Fin n)) :
    convexHull ℝ (p '' (S : Set (Fin n))) ⊆
      convexHull ℝ
        ((clusterUnion X (S.image idx) : Finset (Point 3)) : Set (Point 3)) := by
  apply convexHull_min
  · rintro y ⟨t, ht, rfl⟩
    apply convexHull_mono (s := ((X (idx t) : Finset (Point 3)) : Set (Point 3)))
      (t := ((clusterUnion X (S.image idx) : Finset (Point 3)) : Set (Point 3))) ?_ (hp t)
    intro y hy
    simp only [clusterUnion, Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨idx t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, hy⟩
  · exact convex_convexHull ℝ _

/-- Four points chosen from the four cluster hulls are affinely independent.
The `1+3` Radon partitions are excluded by strong convex position, and the
`2+2` partitions by two-separation. -/
private theorem affineIndependent_four_clusterHull_points {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {idx : Fin 4 → Fin k} (hidx : Function.Injective idx)
    {p : Fin 4 → Point 3}
    (hp : ∀ t, p t ∈ convexHull ℝ ((X (idx t) : Finset (Point 3)) : Set (Point 3))) :
    AffineIndependent ℝ p := by
  classical
  by_contra hdep
  obtain ⟨I, z, hzI, hzIc⟩ := Convex.radon_partition hdep
  let S : Finset (Fin 4) := I.toFinite.toFinset
  let T : Finset (Fin 4) := Finset.univ \ S
  have hScoe : (S : Set (Fin 4)) = I := I.toFinite.coe_toFinset
  have hTcoe : (T : Set (Fin 4)) = Iᶜ := by
    ext t
    simp [T, hScoe]
  have hzS : z ∈ convexHull ℝ
      ((clusterUnion X (S.image idx) : Finset (Point 3)) : Set (Point 3)) :=
    convexHull_image_subset_clusterHull hp S (by simpa [hScoe] using hzI)
  have hzT : z ∈ convexHull ℝ
      ((clusterUnion X (T.image idx) : Finset (Point 3)) : Set (Point 3)) :=
    convexHull_image_subset_clusterHull hp T (by simpa [hTcoe] using hzIc)
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hzS
    simpa only [Finset.image_empty, clusterUnion_empty, Finset.coe_empty,
      convexHull_empty, Set.mem_empty_iff_false] using hzS
  have hTne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hzT
    simpa only [Finset.image_empty, clusterUnion_empty, Finset.coe_empty,
      convexHull_empty, Set.mem_empty_iff_false] using hzT
  have hSTcard : S.card + T.card = 4 := by
    change S.card + (Finset.univ \ S).card = 4
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    have hle := Finset.card_le_card (Finset.subset_univ S)
    simp only [Finset.card_univ, Fintype.card_fin] at hle ⊢
    omega
  by_cases hSone : S.card = 1
  · obtain ⟨s, hS⟩ := Finset.card_eq_one.mp hSone
    have hTim : ({s} : Finset (Fin 4)).image idx = {idx s} := by simp
    have hother : T.image idx ⊆ (Finset.univ.erase (idx s) : Finset (Fin k)) := by
      intro j hj
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
      have hts : t ≠ s := by
        intro h
        subst t
        simp [T, hS] at ht
      simp [hidx.ne hts]
    have hzOthers : z ∈ convexHull ℝ
        ((clusterUnion X (Finset.univ.erase (idx s)) : Finset (Point 3)) : Set (Point 3)) :=
      convexHull_mono (clusterUnion_index_mono X hother) hzT
    have hzOne : z ∈ convexHull ℝ ((X (idx s) : Finset (Point 3)) : Set (Point 3)) := by
      simpa [hS, hTim] using hzS
    exact Set.disjoint_left.mp (hstrong (idx s)) hzOne hzOthers
  by_cases hTone : T.card = 1
  · obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hTone
    have hSim : ({t} : Finset (Fin 4)).image idx = {idx t} := by simp
    have hother : S.image idx ⊆ (Finset.univ.erase (idx t) : Finset (Fin k)) := by
      intro j hj
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
      have hst : s ≠ t := by
        intro h
        subst s
        have : t ∈ T := by simpa [ht]
        simp [T, hs] at this
      simp [hidx.ne hst]
    have hzOthers : z ∈ convexHull ℝ
        ((clusterUnion X (Finset.univ.erase (idx t)) : Finset (Point 3)) : Set (Point 3)) :=
      convexHull_mono (clusterUnion_index_mono X hother) hzS
    have hzOne : z ∈ convexHull ℝ ((X (idx t) : Finset (Point 3)) : Set (Point 3)) := by
      rw [ht] at hzT
      simpa [hSim] using hzT
    exact Set.disjoint_left.mp (hstrong (idx t)) hzOne hzOthers
  · have hScard : S.card = 2 := by
      have := Finset.card_pos.mpr hSne
      have := Finset.card_pos.mpr hTne
      omega
    have hTcard : T.card = 2 := by omega
    obtain ⟨s₁, s₂, hsne, hS⟩ := Finset.card_eq_two.mp hScard
    obtain ⟨t₁, t₂, htne, ht⟩ := Finset.card_eq_two.mp hTcard
    have hcross₁₁ : s₁ ≠ t₁ := by
      intro h
      subst t₁
      have : s₁ ∈ T := by simp [ht]
      simp [T, hS] at this
    have hcross₁₂ : s₁ ≠ t₂ := by
      intro h
      subst t₂
      have : s₁ ∈ T := by simp [ht]
      simp [T, hS] at this
    have hcross₂₁ : s₂ ≠ t₁ := by
      intro h
      subst t₁
      have : s₂ ∈ T := by simp [ht]
      simp [T, hS] at this
    have hcross₂₂ : s₂ ≠ t₂ := by
      intro h
      subst t₂
      have : s₂ ∈ T := by simp [ht]
      simp [T, hS] at this
    have hpairs : Disjoint ({idx s₁, idx s₂} : Finset (Fin k)) {idx t₁, idx t₂} := by
      exact pair_disjoint_of_cross_ne (hidx.ne hcross₁₁) (hidx.ne hcross₁₂)
        (hidx.ne hcross₂₁) (hidx.ne hcross₂₂)
    have hsep := htwo (hidx.ne hsne) (hidx.ne htne) hpairs
    apply Set.disjoint_left.mp hsep
    · simpa [hS, clusterUnion] using hzS
    · rw [ht] at hzT
      simpa [clusterUnion] using hzT

private theorem affineMap_same_sign_on_convex {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (φ : E →ᵃ[ℝ] ℝ) {C : Set E} (hC : Convex ℝ C)
    {p q : E} (hp : p ∈ C) (hq : q ∈ C)
    (hnone : ∀ r ∈ C, φ r ≠ 0) : 0 < φ p * φ q := by
  have hp0 := hnone p hp
  have hq0 := hnone q hq
  rcases hp0.lt_or_gt with hpneg | hppos
  · rcases hq0.lt_or_gt with hqneg | hqpos
    · exact mul_pos_of_neg_of_neg hpneg hqneg
    · let t : ℝ := -φ p / (φ q - φ p)
      have hden : 0 < φ q - φ p := sub_pos.mpr (hpneg.trans hqpos)
      have ht0 : 0 < t := div_pos (neg_pos.mpr hpneg) hden
      have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
      have hr := hC.lineMap_mem hp hq ⟨ht0.le, ht1.le⟩
      have hz : φ (AffineMap.lineMap p q t) = 0 := by
        rw [φ.apply_lineMap, AffineMap.lineMap_apply_ring]
        dsimp [t]
        field_simp
        ring
      exact False.elim (hnone _ hr hz)
  · rcases hq0.lt_or_gt with hqneg | hqpos
    · let t : ℝ := -φ q / (φ p - φ q)
      have hden : 0 < φ p - φ q := sub_pos.mpr (hqneg.trans hppos)
      have ht0 : 0 < t := div_pos (neg_pos.mpr hqneg) hden
      have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
      have hr := hC.lineMap_mem hq hp ⟨ht0.le, ht1.le⟩
      have hz : φ (AffineMap.lineMap q p t) = 0 := by
        rw [φ.apply_lineMap, AffineMap.lineMap_apply_ring]
        dsimp [t]
        field_simp
        ring
      exact False.elim (hnone _ hr hz)
    · exact mul_pos hppos hqpos

private lemma orientedVolume_rotate' (a b c d : Point 3) :
    orientedVolume b c d a = -orientedVolume a b c d := by
  simp [orientedVolume, vsubMatrix, Matrix.det_fin_three]
  ring

private lemma orientedVolume_cycle_last' (a b c d : Point 3) :
    orientedVolume a c d b = orientedVolume a b c d := by
  simp [orientedVolume, vsubMatrix, Matrix.det_fin_three]
  ring

private lemma orientedVolume_swap_last' (a b c d : Point 3) :
    orientedVolume a b d c = -orientedVolume a b c d := by
  simp [orientedVolume, vsubMatrix, Matrix.det_fin_three]
  ring

private theorem orientedVolume_last_same_sign {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {idx : Fin 4 → Fin k} (hidx : Function.Injective idx)
    {p : Fin 4 → Point 3}
    (hp : ∀ t, p t ∈ convexHull ℝ ((X (idx t) : Finset (Point 3)) : Set (Point 3)))
    {q : Point 3}
    (hq : q ∈ convexHull ℝ ((X (idx 3) : Finset (Point 3)) : Set (Point 3))) :
    0 < orientedVolume (p 0) (p 1) (p 2) (p 3) *
      orientedVolume (p 0) (p 1) (p 2) q := by
  let φ := orientedVolumeAffine (p 0) (p 1) (p 2)
  have hnone : ∀ r ∈ convexHull ℝ ((X (idx 3) : Finset (Point 3)) : Set (Point 3)),
      φ r ≠ 0 := by
    intro r hr hzero
    have hai : AffineIndependent ℝ ![p 0, p 1, p 2, r] :=
      affineIndependent_four_clusterHull_points htwo hstrong hidx (by
        intro t
        fin_cases t
        · simpa using hp 0
        · simpa using hp 1
        · simpa using hp 2
        · simpa using hr)
    exact orientedVolume_ne_zero_of_affineIndependent hai (by simpa [φ] using hzero)
  simpa [φ] using affineMap_same_sign_on_convex φ (convex_convexHull ℝ _)
    (hp 3) hq hnone

private theorem orientedVolumes_same_sign_in_clusterHulls {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {idx : Fin 4 → Fin k} (hidx : Function.Injective idx)
    {p q : Fin 4 → Point 3}
    (hp : ∀ t, p t ∈ convexHull ℝ ((X (idx t) : Finset (Point 3)) : Set (Point 3)))
    (hq : ∀ t, q t ∈ convexHull ℝ ((X (idx t) : Finset (Point 3)) : Set (Point 3))) :
    0 < orientedVolume (p 0) (p 1) (p 2) (p 3) *
      orientedVolume (q 0) (q 1) (q 2) (q 3) := by
  let r₁ : Fin 4 → Point 3 := ![q 0, p 1, p 2, p 3]
  let r₂ : Fin 4 → Point 3 := ![q 0, q 1, p 2, p 3]
  let r₃ : Fin 4 → Point 3 := ![q 0, q 1, q 2, p 3]
  have hr₁ : ∀ t, r₁ t ∈ convexHull ℝ
      ((X (idx t) : Finset (Point 3)) : Set (Point 3)) := by
    intro t; fin_cases t <;> simp [r₁, hp, hq]
  have hr₂ : ∀ t, r₂ t ∈ convexHull ℝ
      ((X (idx t) : Finset (Point 3)) : Set (Point 3)) := by
    intro t; fin_cases t <;> simp [r₂, hp, hq]
  have hr₃ : ∀ t, r₃ t ∈ convexHull ℝ
      ((X (idx t) : Finset (Point 3)) : Set (Point 3)) := by
    intro t; fin_cases t <;> simp [r₃, hp, hq]
  have h₁last := orientedVolume_last_same_sign htwo hstrong
    (idx := ![idx 1, idx 2, idx 3, idx 0])
    (p := ![p 1, p 2, p 3, p 0]) (q := q 0) (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [hidx.eq_iff]) (by
      intro t; fin_cases t <;> simp [hp]) (by simpa using hq 0)
  have h₁ : 0 < orientedVolume (p 0) (p 1) (p 2) (p 3) *
      orientedVolume (q 0) (p 1) (p 2) (p 3) := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h₁last
    simpa only [orientedVolume_rotate' (p 0) (p 1) (p 2) (p 3),
      orientedVolume_rotate' (q 0) (p 1) (p 2) (p 3), neg_mul_neg] using h₁last
  have h₂last := orientedVolume_last_same_sign htwo hstrong
    (idx := ![idx 0, idx 2, idx 3, idx 1])
    (p := ![q 0, p 2, p 3, p 1]) (q := q 1) (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [hidx.eq_iff]) (by
      intro t; fin_cases t <;> simp [hp, hq]) (by simpa using hq 1)
  have h₂ : 0 < orientedVolume (q 0) (p 1) (p 2) (p 3) *
      orientedVolume (q 0) (q 1) (p 2) (p 3) := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h₂last
    simpa only [orientedVolume_cycle_last' (q 0) (p 1) (p 2) (p 3),
      orientedVolume_cycle_last' (q 0) (q 1) (p 2) (p 3)] using h₂last
  have h₃last := orientedVolume_last_same_sign htwo hstrong
    (idx := ![idx 0, idx 1, idx 3, idx 2])
    (p := ![q 0, q 1, p 3, p 2]) (q := q 2) (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [hidx.eq_iff]) (by
      intro t; fin_cases t <;> simp [hp, hq]) (by simpa using hq 2)
  have h₃ : 0 < orientedVolume (q 0) (q 1) (p 2) (p 3) *
      orientedVolume (q 0) (q 1) (q 2) (p 3) := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h₃last
    simpa only [orientedVolume_swap_last' (q 0) (q 1) (p 2) (p 3),
      orientedVolume_swap_last' (q 0) (q 1) (q 2) (p 3), neg_mul_neg] using h₃last
  have h₄ := orientedVolume_last_same_sign htwo hstrong hidx hr₃ (hq 3)
  have h12 : 0 < orientedVolume (p 0) (p 1) (p 2) (p 3) *
      orientedVolume (q 0) (q 1) (p 2) (p 3) := by
    rcases (mul_pos_iff.mp h₂) with hpos | hneg
    · exact mul_pos (pos_of_mul_pos_left h₁ hpos.1.le) hpos.2
    · exact mul_pos_of_neg_of_neg (neg_of_mul_pos_left h₁ hneg.1.le) hneg.2
  have h123 : 0 < orientedVolume (p 0) (p 1) (p 2) (p 3) *
      orientedVolume (q 0) (q 1) (q 2) (p 3) := by
    rcases (mul_pos_iff.mp h₃) with hpos | hneg
    · exact mul_pos (pos_of_mul_pos_left h12 hpos.1.le) hpos.2
    · exact mul_pos_of_neg_of_neg (neg_of_mul_pos_left h12 hneg.1.le) hneg.2
  rcases (mul_pos_iff.mp h₄) with hpos | hneg
  · exact mul_pos (pos_of_mul_pos_left h123 hpos.1.le) hpos.2
  · exact mul_pos_of_neg_of_neg (neg_of_mul_pos_left h123 hneg.1.le) hneg.2

private def fivePoints (a b c d e : Point 3) : Fin 5 → Point 3 := ![a, b, c, d, e]

private def fiveCofactors (a b c d e : Point 3) : Fin 5 → ℝ :=
  ![orientedVolume b c d e, -orientedVolume a c d e,
    orientedVolume a b d e, -orientedVolume a b c e,
    orientedVolume a b c d]

private theorem fiveCofactors_sum (a b c d e : Point 3) :
    ∑ i, fiveCofactors a b c d e i = 0 := by
  simp [fiveCofactors, Fin.sum_univ_succ, orientedVolume, vsubMatrix,
    Matrix.det_fin_three]
  ring

private theorem fiveCofactors_point_sum (a b c d e : Point 3) :
    ∑ i, fiveCofactors a b c d e i • fivePoints a b c d e i = 0 := by
  ext j
  fin_cases j <;>
    simp [fiveCofactors, fivePoints, Fin.sum_univ_succ, orientedVolume,
      vsubMatrix, Matrix.det_fin_three] <;> ring

private theorem affineRelation_eq_zero_of_last_zero
    {a b c d e : Point 3} (hai : AffineIndependent ℝ ![a, b, c, d])
    {u : Fin 5 → ℝ} (hsum : ∑ i, u i = 0)
    (hpoint : ∑ i, u i • fivePoints a b c d e i = 0) (hu4 : u 4 = 0) :
    u = 0 := by
  let u₄ : Fin 4 → ℝ := ![u 0, u 1, u 2, u 3]
  have hsum₄ : ∑ i, u₄ i = ∑ i, (0 : Fin 4 → ℝ) i := by
    simpa [u₄, Fin.sum_univ_succ, hu4] using hsum
  have hpoint₄ : ∑ i, u₄ i • ![a, b, c, d] i =
      ∑ i, (0 : Fin 4 → ℝ) i • ![a, b, c, d] i := by
    simpa [u₄, fivePoints, Fin.sum_univ_succ, hu4] using hpoint
  have hu := hai.eq_of_sum_eq_sum (s := Finset.univ) hsum₄ hpoint₄
  funext i
  fin_cases i
  · simpa [u₄] using hu 0 (by simp)
  · simpa [u₄] using hu 1 (by simp)
  · simpa [u₄] using hu 2 (by simp)
  · simpa [u₄] using hu 3 (by simp)
  · simpa [hu4]

private theorem fiveCofactors_proportional
    {a b c d e : Point 3} (hai : AffineIndependent ℝ ![a, b, c, d])
    {u : Fin 5 → ℝ} (hsum : ∑ i, u i = 0)
    (hpoint : ∑ i, u i • fivePoints a b c d e i = 0) (hu4 : u 4 ≠ 0) :
    fiveCofactors a b c d e =
      fun i ↦ (fiveCofactors a b c d e 4 / u 4) * u i := by
  let r := fiveCofactors a b c d e 4 / u 4
  let v : Fin 5 → ℝ := fun i ↦ fiveCofactors a b c d e i - r * u i
  have hvsum : ∑ i, v i = 0 := by
    simp only [v, Finset.sum_sub_distrib, ← Finset.mul_sum, fiveCofactors_sum, hsum,
      mul_zero, sub_zero]
  have hvpoint : ∑ i, v i • fivePoints a b c d e i = 0 := by
    rw [show (∑ i, v i • fivePoints a b c d e i) =
        (∑ i, fiveCofactors a b c d e i • fivePoints a b c d e i) -
          r • ∑ i, u i • fivePoints a b c d e i by
      simp only [v, sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]]
    rw [fiveCofactors_point_sum, hpoint, smul_zero, sub_zero]
  have hv4 : v 4 = 0 := by
    dsimp [v, r]
    rw [div_mul_cancel₀ _ hu4, sub_self]
  have hv := affineRelation_eq_zero_of_last_zero hai hvsum hvpoint hv4
  funext i
  have := congr_fun hv i
  simp only [v, Pi.zero_apply, sub_eq_zero] at this
  exact this

/-- A strict oriented affine-hyperplane sign function, written as
`normal x - offset`.  Positivity and negativity are the two open
half-spaces. -/
def planeValue (normal : Point 3 →L[ℝ] ℝ) (offset : ℝ)
    (x : Point 3) : ℝ :=
  normal x - offset

/-- A representative `x i` is chosen from every cluster. -/
def IsClusterTransversal {k : ℕ} (X : Fin k → Finset (Point 3))
    (x : Fin k → Point 3) : Prop :=
  ∀ i, x i ∈ X i

/-- The sign pattern of a strict plane on a transversal. -/
def HasRepresentativePlanePattern {k : ℕ}
    (x : Fin k → Point 3) (normal : Point 3 →L[ℝ] ℝ) (offset : ℝ) : Prop :=
  normal ≠ 0 ∧ ∀ i, planeValue normal offset (x i) ≠ 0

/-- A plane on the full clusters realizes exactly the signs induced on the
chosen representatives by another plane. -/
def LiftsRepresentativePlanePattern {k : ℕ}
    (X : Fin k → Finset (Point 3)) (x : Fin k → Point 3)
    (normal : Point 3 →L[ℝ] ℝ) (offset : ℝ) : Prop :=
  ∃ (liftNormal : Point 3 →L[ℝ] ℝ) (liftOffset : ℝ),
    liftNormal ≠ 0 ∧
    ∀ i y, y ∈ X i →
      (0 < planeValue normal offset (x i) →
        0 < planeValue liftNormal liftOffset y) ∧
      (planeValue normal offset (x i) < 0 →
        planeValue liftNormal liftOffset y < 0)

/-- Indices whose representatives lie in the positive open half-space. -/
def positiveClusterIndices {k : ℕ} (x : Fin k → Point 3)
    (normal : Point 3 →L[ℝ] ℝ) (offset : ℝ) : Finset (Fin k) :=
  Finset.univ.filter fun i => 0 < planeValue normal offset (x i)

/-- Indices whose representatives lie in the negative open half-space. -/
def negativeClusterIndices {k : ℕ} (x : Fin k → Point 3)
    (normal : Point 3 →L[ℝ] ℝ) (offset : ℝ) : Finset (Fin k) :=
  Finset.univ.filter fun i => planeValue normal offset (x i) < 0

/-- The geometric conclusion needed before invoking strict hyperplane
separation: the hulls of the unions of the negative and positive clusters
are disjoint. -/
def RepresentativePatternHullsSeparated {k : ℕ}
    (X : Fin k → Finset (Point 3)) (x : Fin k → Point 3)
    (normal : Point 3 →L[ℝ] ℝ) (offset : ℝ) : Prop :=
  Disjoint
    (convexHull ℝ
      ((clusterUnion X (negativeClusterIndices x normal offset) :
        Finset (Point 3)) : Set (Point 3)))
    (convexHull ℝ
      ((clusterUnion X (positiveClusterIndices x normal offset) :
        Finset (Point 3)) : Set (Point 3)))

private theorem fiveCluster_segment_triangle_pattern_impossible {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {ia ib ic id ie : Fin k}
    (hindices : Function.Injective ![ia, ib, ic, id, ie])
    {a b c d e : Point 3}
    (ha : a ∈ X ia) (hb : b ∈ X ib) (hc : c ∈ X ic)
    (hd : d ∈ X id) (he : e ∈ X ie)
    {x : Fin k → Point 3} (hx : IsClusterTransversal X x)
    {normal : Point 3 →L[ℝ] ℝ} {offset : ℝ}
    (hacneg : planeValue normal offset (x ia) < 0 ∧
      planeValue normal offset (x ic) < 0)
    (hbdeposit : 0 < planeValue normal offset (x ib) ∧
      0 < planeValue normal offset (x id) ∧
      0 < planeValue normal offset (x ie))
    (hinter : (convexHull ℝ (({a, c} : Finset (Point 3)) : Set (Point 3)) ∩
      convexHull ℝ (({b, d, e} : Finset (Point 3)) : Set (Point 3))).Nonempty) : False := by
  classical
  have hidx4 (v : Fin 4 → Fin 5) (hv : Function.Injective v) :
      Function.Injective fun t ↦ ![ia, ib, ic, id, ie] (v t) := hindices.comp hv
  have hinj0 : Function.Injective ![ib, ic, id, ie] := by
    exact vector4_injective_of_pairwise ib ic id ie
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 2 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (2 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (2 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (3 : Fin 5) ≠ 4 by decide))
  have hinj1 : Function.Injective ![ia, ic, id, ie] := by
    exact vector4_injective_of_pairwise ia ic id ie
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 2 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (2 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (2 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (3 : Fin 5) ≠ 4 by decide))
  have hinj2 : Function.Injective ![ia, ib, id, ie] := by
    exact vector4_injective_of_pairwise ia ib id ie
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 1 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (3 : Fin 5) ≠ 4 by decide))
  have hinj3 : Function.Injective ![ia, ib, ic, ie] := by
    exact vector4_injective_of_pairwise ia ib ic ie
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 1 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 2 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 2 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 4 by decide))
      (by simpa using hindices.ne (show (2 : Fin 5) ≠ 4 by decide))
  have hinj4 : Function.Injective ![ia, ib, ic, id] := by
    exact vector4_injective_of_pairwise ia ib ic id
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 1 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 2 by decide))
      (by simpa using hindices.ne (show (0 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 2 by decide))
      (by simpa using hindices.ne (show (1 : Fin 5) ≠ 3 by decide))
      (by simpa using hindices.ne (show (2 : Fin 5) ≠ 3 by decide))
  have hpHull (i : Fin k) {y : Point 3} (hy : y ∈ X i) :
      y ∈ convexHull ℝ ((X i : Finset (Point 3)) : Set (Point 3)) :=
    subset_convexHull ℝ _ hy
  have hvol0 := orientedVolumes_same_sign_in_clusterHulls htwo hstrong
    (idx := ![ib, ic, id, ie]) (p := ![b, c, d, e])
    (q := ![x ib, x ic, x id, x ie])
    hinj0 (by
      intro t; fin_cases t
      · exact hpHull ib hb
      · exact hpHull ic hc
      · exact hpHull id hd
      · exact hpHull ie he) (by
      intro t; fin_cases t <;> exact hpHull _ (hx _))
  have hvol1 := orientedVolumes_same_sign_in_clusterHulls htwo hstrong
    (idx := ![ia, ic, id, ie]) (p := ![a, c, d, e])
    (q := ![x ia, x ic, x id, x ie])
    hinj1 (by
      intro t; fin_cases t
      · exact hpHull ia ha
      · exact hpHull ic hc
      · exact hpHull id hd
      · exact hpHull ie he) (by
      intro t; fin_cases t <;> exact hpHull _ (hx _))
  have hvol2 := orientedVolumes_same_sign_in_clusterHulls htwo hstrong
    (idx := ![ia, ib, id, ie]) (p := ![a, b, d, e])
    (q := ![x ia, x ib, x id, x ie])
    hinj2 (by
      intro t; fin_cases t
      · exact hpHull ia ha
      · exact hpHull ib hb
      · exact hpHull id hd
      · exact hpHull ie he) (by
      intro t; fin_cases t <;> exact hpHull _ (hx _))
  have hvol3 := orientedVolumes_same_sign_in_clusterHulls htwo hstrong
    (idx := ![ia, ib, ic, ie]) (p := ![a, b, c, e])
    (q := ![x ia, x ib, x ic, x ie])
    hinj3 (by
      intro t; fin_cases t
      · exact hpHull ia ha
      · exact hpHull ib hb
      · exact hpHull ic hc
      · exact hpHull ie he) (by
      intro t; fin_cases t <;> exact hpHull _ (hx _))
  have hvol4 := orientedVolumes_same_sign_in_clusterHulls htwo hstrong
    (idx := ![ia, ib, ic, id]) (p := ![a, b, c, d])
    (q := ![x ia, x ib, x ic, x id])
    hinj4 (by
      intro t; fin_cases t
      · exact hpHull ia ha
      · exact hpHull ib hb
      · exact hpHull ic hc
      · exact hpHull id hd) (by
      intro t; fin_cases t <;> exact hpHull _ (hx _))
  obtain ⟨z, hzac, hzbde⟩ := hinter
  obtain ⟨w, hw, hwsum, hwpoint⟩ := Finset.mem_convexHull'.mp hzac
  obtain ⟨v, hv, hvsum, hvpoint⟩ := Finset.mem_convexHull'.mp hzbde
  have hac : a ≠ c := by
    intro h
    subst c
    exact Finset.disjoint_left.mp
      (hstrong.pairwiseDisjoint (hindices.ne (by decide : (0 : Fin 5) ≠ 2))) ha hc
  have hbd : b ≠ d := by
    intro h
    subst d
    exact Finset.disjoint_left.mp
      (hstrong.pairwiseDisjoint (hindices.ne (by decide : (1 : Fin 5) ≠ 3))) hb hd
  have hbe : b ≠ e := by
    intro h
    subst e
    exact Finset.disjoint_left.mp
      (hstrong.pairwiseDisjoint (hindices.ne (by decide : (1 : Fin 5) ≠ 4))) hb he
  have hde : d ≠ e := by
    intro h
    subst e
    exact Finset.disjoint_left.mp
      (hstrong.pairwiseDisjoint (hindices.ne (by decide : (3 : Fin 5) ≠ 4))) hd he
  have hwsum' : w a + w c = 1 := by simpa [hac] using hwsum
  have hvsum' : v b + v d + v e = 1 := by simpa [hbd, hbe, hde, add_assoc] using hvsum
  have hwpoint' : w a • a + w c • c = z := by simpa [hac] using hwpoint
  have hvpoint' : v b • b + v d • d + v e • e = z := by
    simpa [hbd, hbe, hde, add_assoc] using hvpoint
  let u : Fin 5 → ℝ := ![w a, -v b, w c, -v d, -v e]
  have husum : ∑ i, u i = 0 := by
    simp [u, Fin.sum_univ_succ]
    linarith
  have hupoint : ∑ i, u i • fivePoints a b c d e i = 0 := by
    calc
      ∑ i, u i • fivePoints a b c d e i =
          (w a • a + w c • c) - (v b • b + v d • d + v e • e) := by
            simp [u, fivePoints, Fin.sum_univ_succ]
            module
      _ = z - z := by rw [hwpoint', hvpoint']
      _ = 0 := sub_self z
  have hu4 : u 4 ≠ 0 := by
    intro hu
    have hve0 : v e = 0 := by simpa [u] using hu
    have hzbd : z ∈ convexHull ℝ (({b, d} : Finset (Point 3)) : Set (Point 3)) := by
      rw [Finset.mem_convexHull']
      refine ⟨v, ?_, ?_, ?_⟩
      · intro y hy
        exact hv y (by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          exact hy.elim Or.inl (fun h ↦ Or.inr (Or.inl h)))
      · simpa [hbd, hbe, hde, hve0, add_assoc] using hvsum
      · simpa [hbd, hbe, hde, hve0, add_assoc] using hvpoint
    have hiaib : ia ≠ ib := by
      simpa using hindices.ne (show (0 : Fin 5) ≠ 1 by decide)
    have hiaid : ia ≠ id := by
      simpa using hindices.ne (show (0 : Fin 5) ≠ 3 by decide)
    have hicib : ic ≠ ib := by
      simpa using hindices.ne (show (2 : Fin 5) ≠ 1 by decide)
    have hicid : ic ≠ id := by
      simpa using hindices.ne (show (2 : Fin 5) ≠ 3 by decide)
    have hiac : ia ≠ ic := by
      simpa using hindices.ne (show (0 : Fin 5) ≠ 2 by decide)
    have hibd : ib ≠ id := by
      simpa using hindices.ne (show (1 : Fin 5) ≠ 3 by decide)
    have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, id} := by
      exact pair_disjoint_of_cross_ne hiaib hiaid hicib hicid
    have hsep := htwo hiac hibd hpairs
    apply Set.disjoint_left.mp hsep
    · apply convexHull_mono (s := (({a, c} : Finset (Point 3)) : Set (Point 3)))
        (t := (((X ia ∪ X ic : Finset (Point 3))) : Set (Point 3))) ?_ hzac
      intro y hy
      simp only [Finset.mem_coe, Finset.mem_union]
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Or.inl ha
      · exact Or.inr hc
    · apply convexHull_mono (s := (({b, d} : Finset (Point 3)) : Set (Point 3)))
        (t := (((X ib ∪ X id : Finset (Point 3))) : Set (Point 3))) ?_ hzbd
      intro y hy
      simp only [Finset.mem_coe, Finset.mem_union]
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Or.inl hb
      · exact Or.inr hd
  have hai : AffineIndependent ℝ ![a, b, c, d] :=
    affineIndependent_four_clusterHull_points htwo hstrong
      hinj4 (by
        intro t; fin_cases t
        · exact hpHull ia ha
        · exact hpHull ib hb
        · exact hpHull ic hc
        · exact hpHull id hd)
  have hprop := fiveCofactors_proportional hai husum hupoint hu4
  let r := fiveCofactors a b c d e 4 / u 4
  have hr : r ≠ 0 := by
    have hV : fiveCofactors a b c d e 4 ≠ 0 := by
      simpa [fiveCofactors] using orientedVolume_ne_zero_of_affineIndependent hai
    exact div_ne_zero hV hu4
  have hupos : 0 < u 0 ∧ u 2 > 0 := by
    have hC0 : fiveCofactors a b c d e 0 ≠ 0 := by
      have hi := affineIndependent_four_clusterHull_points htwo hstrong
        (idx := ![ib, ic, id, ie]) (p := ![b, c, d, e])
        hinj0 (by
          intro t; fin_cases t
          · exact hpHull ib hb
          · exact hpHull ic hc
          · exact hpHull id hd
          · exact hpHull ie he)
      simpa [fiveCofactors] using orientedVolume_ne_zero_of_affineIndependent hi
    have hC2 : fiveCofactors a b c d e 2 ≠ 0 := by
      have hi := affineIndependent_four_clusterHull_points htwo hstrong
        (idx := ![ia, ib, id, ie]) (p := ![a, b, d, e])
        hinj2 (by
          intro t; fin_cases t
          · exact hpHull ia ha
          · exact hpHull ib hb
          · exact hpHull id hd
          · exact hpHull ie he)
      simpa [fiveCofactors] using orientedVolume_ne_zero_of_affineIndependent hi
    have hu0 : u 0 ≠ 0 := by
      intro h
      have := congr_fun hprop 0
      simp [r, h, hC0] at this
    have hu2 : u 2 ≠ 0 := by
      intro h
      have := congr_fun hprop 2
      simp [r, h, hC2] at this
    exact ⟨lt_of_le_of_ne (hw a (by simp)) (Ne.symm (by simpa [u] using hu0)),
      lt_of_le_of_ne (hw c (by simp)) (Ne.symm (by simpa [u] using hu2))⟩
  have huneg : u 1 < 0 ∧ u 3 < 0 ∧ u 4 < 0 := by
    have getneg (j : Fin 5) (hj : j = 1 ∨ j = 3 ∨ j = 4) : u j < 0 := by
      have hC : fiveCofactors a b c d e j ≠ 0 := by
        rcases hj with rfl | rfl | rfl
        · have hi := affineIndependent_four_clusterHull_points htwo hstrong
            (idx := ![ia, ic, id, ie]) (p := ![a, c, d, e])
            hinj1 (by
              intro t; fin_cases t
              · exact hpHull ia ha
              · exact hpHull ic hc
              · exact hpHull id hd
              · exact hpHull ie he)
          simpa [fiveCofactors] using orientedVolume_ne_zero_of_affineIndependent hi
        · have hi := affineIndependent_four_clusterHull_points htwo hstrong
            (idx := ![ia, ib, ic, ie]) (p := ![a, b, c, e])
            hinj3 (by
              intro t; fin_cases t
              · exact hpHull ia ha
              · exact hpHull ib hb
              · exact hpHull ic hc
              · exact hpHull ie he)
          simpa [fiveCofactors] using orientedVolume_ne_zero_of_affineIndependent hi
        · simpa [fiveCofactors] using orientedVolume_ne_zero_of_affineIndependent hai
      have hu : u j ≠ 0 := by
        intro h
        have := congr_fun hprop j
        simp [r, h, hC] at this
      rcases hj with rfl | rfl | rfl
      · exact neg_neg_of_pos (lt_of_le_of_ne (hv b (by simp))
          (Ne.symm (by simpa [u] using hu)))
      · exact neg_neg_of_pos (lt_of_le_of_ne (hv d (by simp))
          (Ne.symm (by simpa [u] using hu)))
      · exact neg_neg_of_pos (lt_of_le_of_ne (hv e (by simp))
          (Ne.symm (by simpa [u] using hu)))
    exact ⟨getneg 1 (Or.inl rfl), getneg 3 (Or.inr (Or.inl rfl)),
      getneg 4 (Or.inr (Or.inr rfl))⟩
  let q : Fin 5 → Point 3 := ![x ia, x ib, x ic, x id, x ie]
  let D := fiveCofactors (q 0) (q 1) (q 2) (q 3) (q 4)
  have hsame : ∀ j, 0 < fiveCofactors a b c d e j * D j := by
    intro j
    fin_cases j
    · simpa [D, q, fiveCofactors] using hvol0
    · simpa [D, q, fiveCofactors] using hvol1
    · simpa [D, q, fiveCofactors] using hvol2
    · simpa [D, q, fiveCofactors] using hvol3
    · simpa [D, q, fiveCofactors] using hvol4
  have hDsum : ∑ j, D j = 0 := by simpa [D, q] using fiveCofactors_sum (q 0) (q 1) (q 2) (q 3) (q 4)
  have hDpoint : ∑ j, D j • q j = 0 := by
    simpa [D, q, fivePoints] using fiveCofactors_point_sum (q 0) (q 1) (q 2) (q 3) (q 4)
  have hplane : ∑ j, D j * planeValue normal offset (q j) = 0 := by
    have hn := congrArg normal hDpoint
    change normal (∑ j, D j • q j) = normal 0 at hn
    simp only [map_sum, ContinuousLinearMap.map_smul_of_tower, map_zero] at hn
    simp only [planeValue, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hDsum,
      zero_mul, sub_zero]
    simpa [smul_eq_mul] using hn
  rcases hr.lt_or_gt with hrneg | hrpos
  · have hDsign : D 0 < 0 ∧ 0 < D 1 ∧ D 2 < 0 ∧ 0 < D 3 ∧ 0 < D 4 := by
      have hc (j : Fin 5) : fiveCofactors a b c d e j = r * u j := by
        simpa [r] using congr_fun hprop j
      constructor
      · have : fiveCofactors a b c d e 0 < 0 := by rw [hc]; exact mul_neg_of_neg_of_pos hrneg hupos.1
        exact neg_of_mul_pos_right (hsame 0) this.le
      constructor
      · have : 0 < fiveCofactors a b c d e 1 := by rw [hc]; exact mul_pos_of_neg_of_neg hrneg huneg.1
        exact pos_of_mul_pos_right (hsame 1) this.le
      constructor
      · have : fiveCofactors a b c d e 2 < 0 := by rw [hc]; exact mul_neg_of_neg_of_pos hrneg hupos.2
        exact neg_of_mul_pos_right (hsame 2) this.le
      constructor
      · have : 0 < fiveCofactors a b c d e 3 := by rw [hc]; exact mul_pos_of_neg_of_neg hrneg huneg.2.1
        exact pos_of_mul_pos_right (hsame 3) this.le
      · have : 0 < fiveCofactors a b c d e 4 := by rw [hc]; exact mul_pos_of_neg_of_neg hrneg huneg.2.2
        exact pos_of_mul_pos_right (hsame 4) this.le
    have := hplane
    simp [Fin.sum_univ_succ, q] at this
    linarith [mul_pos_of_neg_of_neg hDsign.1 hacneg.1,
      mul_pos hDsign.2.1 hbdeposit.1,
      mul_pos_of_neg_of_neg hDsign.2.2.1 hacneg.2,
      mul_pos hDsign.2.2.2.1 hbdeposit.2.1,
      mul_pos hDsign.2.2.2.2 hbdeposit.2.2]
  · have hDsign : 0 < D 0 ∧ D 1 < 0 ∧ 0 < D 2 ∧ D 3 < 0 ∧ D 4 < 0 := by
      have hc (j : Fin 5) : fiveCofactors a b c d e j = r * u j := by
        simpa [r] using congr_fun hprop j
      constructor
      · have : 0 < fiveCofactors a b c d e 0 := by rw [hc]; exact mul_pos hrpos hupos.1
        exact pos_of_mul_pos_right (hsame 0) this.le
      constructor
      · have : fiveCofactors a b c d e 1 < 0 := by rw [hc]; exact mul_neg_of_pos_of_neg hrpos huneg.1
        exact neg_of_mul_pos_right (hsame 1) this.le
      constructor
      · have : 0 < fiveCofactors a b c d e 2 := by rw [hc]; exact mul_pos hrpos hupos.2
        exact pos_of_mul_pos_right (hsame 2) this.le
      constructor
      · have : fiveCofactors a b c d e 3 < 0 := by rw [hc]; exact mul_neg_of_pos_of_neg hrpos huneg.2.1
        exact neg_of_mul_pos_right (hsame 3) this.le
      · have : fiveCofactors a b c d e 4 < 0 := by rw [hc]; exact mul_neg_of_pos_of_neg hrpos huneg.2.2
        exact neg_of_mul_pos_right (hsame 4) this.le
    have := hplane
    simp [Fin.sum_univ_succ, q] at this
    linarith [mul_neg_of_pos_of_neg hDsign.1 hacneg.1,
      mul_neg_of_neg_of_pos hDsign.2.1 hbdeposit.1,
      mul_neg_of_pos_of_neg hDsign.2.2.1 hacneg.2,
      mul_neg_of_neg_of_pos hDsign.2.2.2.1 hbdeposit.2.1,
      mul_neg_of_neg_of_pos hDsign.2.2.2.2 hbdeposit.2.2]

private theorem hulls_disjoint_of_one_cluster {k : ℕ}
    {X : Fin k → Finset (Point 3)} (hstrong : StrongConvexPositionClusters X)
    {i : Fin k} {J : Finset (Fin k)} (hiJ : i ∉ J)
    {A B : Finset (Point 3)} (hA : A ⊆ X i)
    (hB : B ⊆ clusterUnion X J) :
    Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3))) := by
  apply (hstrong i).mono
  · exact convexHull_mono hA
  · apply convexHull_mono
    exact hB.trans (clusterUnion_index_mono X (by
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_univ]
      exact ⟨fun hji ↦ hiJ (hji ▸ hj), trivial⟩))

private theorem hulls_disjoint_of_two_pairs {k : ℕ}
    {X : Fin k → Finset (Point 3)} (htwo : TwoSeparatedClusters X)
    {i j i' j' : Fin k} (hij : i ≠ j) (hi'j' : i' ≠ j')
    (hpairs : Disjoint ({i, j} : Finset (Fin k)) {i', j'})
    {A B : Finset (Point 3)} (hA : A ⊆ X i ∪ X j)
    (hB : B ⊆ X i' ∪ X j') :
    Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3))) :=
  (htwo hij hi'j' hpairs).mono (convexHull_mono hA) (convexHull_mono hB)

private theorem pair_disjoint_of_mem {α : Type*} [DecidableEq α]
    {S T : Finset α} (hST : Disjoint S T)
    {a b c d : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ T) (hd : d ∈ T) :
    Disjoint ({a, b} : Finset α) {c, d} := by
  rw [Finset.disjoint_left]
  intro x hxS hxT
  have hxS' : x ∈ S := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxS
    rcases hxS with rfl | rfl
    · exact ha
    · exact hb
  have hxT' : x ∈ T := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
    rcases hxT with rfl | rfl
    · exact hc
    · exact hd
  exact Finset.disjoint_left.mp hST hxS' hxT'

private theorem vector5_injective_of_pairwise {α : Type*}
    (a b c d e : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Function.Injective ![a, b, c, d, e] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Kirchberger plus the `1+4` and `2+2` exclusions leaves exactly a
five-cluster `2+3` Radon witness. -/
private theorem fiveCluster_witness_of_hulls_intersect {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {N P : Finset (Fin k)} (hNP : Disjoint N P)
    (hinter : (convexHull ℝ ((clusterUnion X N : Finset (Point 3)) : Set (Point 3)) ∩
      convexHull ℝ ((clusterUnion X P : Finset (Point 3)) : Set (Point 3))).Nonempty) :
    (∃ ia ib ic id ie a b c d e,
      Function.Injective ![ia, ib, ic, id, ie] ∧
      ia ∈ N ∧ ic ∈ N ∧ ib ∈ P ∧ id ∈ P ∧ ie ∈ P ∧
      a ∈ X ia ∧ b ∈ X ib ∧ c ∈ X ic ∧ d ∈ X id ∧ e ∈ X ie ∧
      (convexHull ℝ (({a, c} : Finset (Point 3)) : Set (Point 3)) ∩
        convexHull ℝ (({b, d, e} : Finset (Point 3)) : Set (Point 3))).Nonempty) ∨
    (∃ ia ib ic id ie a b c d e,
      Function.Injective ![ia, ib, ic, id, ie] ∧
      ia ∈ P ∧ ic ∈ P ∧ ib ∈ N ∧ id ∈ N ∧ ie ∈ N ∧
      a ∈ X ia ∧ b ∈ X ib ∧ c ∈ X ic ∧ d ∈ X id ∧ e ∈ X ie ∧
      (convexHull ℝ (({a, c} : Finset (Point 3)) : Set (Point 3)) ∩
        convexHull ℝ (({b, d, e} : Finset (Point 3)) : Set (Point 3))).Nonempty) := by
  classical
  obtain ⟨A, B, hAN, hBP, hcard, z, hzA, hzB⟩ :=
    finite_kirchberger_point3 (clusterUnion X N) (clusterUnion X P) hinter
  have hAne : A.Nonempty := by
    by_contra h
    have : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst A
    simp at hzA
  have hBne : B.Nonempty := by
    by_contra h
    have : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst B
    simp at hzB
  have indexN {y : Point 3} (hy : y ∈ A) : ∃ i ∈ N, y ∈ X i := by
    exact Finset.mem_biUnion.mp (hAN hy)
  have indexP {y : Point 3} (hy : y ∈ B) : ∃ i ∈ P, y ∈ X i := by
    exact Finset.mem_biUnion.mp (hBP hy)
  by_cases hAone : A.card = 1
  · obtain ⟨a, hA⟩ := Finset.card_eq_one.mp hAone
    rw [hA] at hAN hzA indexN
    obtain ⟨ia, hiaN, ha⟩ := indexN (y := a) (by simp)
    have hBP' : B ⊆ clusterUnion X P := hBP
    exact False.elim (Set.disjoint_left.mp
      (hulls_disjoint_of_one_cluster hstrong (i := ia) (J := P)
        (A := {a}) (B := B)
        (fun h ↦ Finset.disjoint_left.mp hNP hiaN h) (by simpa using ha) hBP')
      (by simpa using hzA) hzB)
  by_cases hBone : B.card = 1
  · obtain ⟨b, hB⟩ := Finset.card_eq_one.mp hBone
    rw [hB] at hBP hzB indexP
    obtain ⟨ib, hibP, hb⟩ := indexP (y := b) (by simp)
    exact False.elim (Set.disjoint_left.mp
      (hulls_disjoint_of_one_cluster hstrong (i := ib) (J := N)
        (A := {b}) (B := A)
        (fun h ↦ Finset.disjoint_left.mp hNP h hibP) (by simpa using hb) hAN).symm
      hzA (by simpa using hzB))
  have hApos : 0 < A.card := Finset.card_pos.mpr hAne
  have hBpos : 0 < B.card := Finset.card_pos.mpr hBne
  have hA2 : 2 ≤ A.card := by omega
  have hB2 : 2 ≤ B.card := by omega
  have hsizes : (A.card = 2 ∧ B.card = 2) ∨
      (A.card = 2 ∧ B.card = 3) ∨ (A.card = 3 ∧ B.card = 2) := by omega
  rcases hsizes with h22 | h23 | h32
  · obtain ⟨a, c, hac, hA⟩ := Finset.card_eq_two.mp h22.1
    obtain ⟨b, d, hbd, hB⟩ := Finset.card_eq_two.mp h22.2
    subst A; subst B
    obtain ⟨ia, hiaN, ha⟩ := indexN (y := a) (by simp)
    obtain ⟨ic, hicN, hc⟩ := indexN (y := c) (by simp)
    obtain ⟨ib, hibP, hb⟩ := indexP (y := b) (by simp)
    obtain ⟨id, hidP, hd⟩ := indexP (y := d) (by simp)
    by_cases hiac : ia = ic
    · subst ic
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_one_cluster hstrong (i := ia) (J := P)
          (fun h ↦ Finset.disjoint_left.mp hNP hiaN h)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl <;> assumption) hBP) hzA hzB)
    by_cases hibd : ib = id
    · subst id
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_one_cluster hstrong (i := ib) (J := N)
          (fun h ↦ Finset.disjoint_left.mp hNP h hibP)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl <;> assumption) hAN).symm hzA hzB)
    have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, id} := by
      exact pair_disjoint_of_mem hNP hiaN hicN hibP hidP
    exact False.elim (Set.disjoint_left.mp
      (hulls_disjoint_of_two_pairs htwo hiac hibd hpairs
        (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact Finset.mem_union_left _ ha
          · exact Finset.mem_union_right _ hc)
        (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact Finset.mem_union_left _ hb
          · exact Finset.mem_union_right _ hd)) hzA hzB)
  · obtain ⟨a, c, hac, hA⟩ := Finset.card_eq_two.mp h23.1
    obtain ⟨b, d, e, hbd, hbe, hde, hB⟩ := Finset.card_eq_three.mp h23.2
    subst A; subst B
    obtain ⟨ia, hiaN, ha⟩ := indexN (y := a) (by simp)
    obtain ⟨ic, hicN, hc⟩ := indexN (y := c) (by simp)
    obtain ⟨ib, hibP, hb⟩ := indexP (y := b) (by simp)
    obtain ⟨id, hidP, hd⟩ := indexP (y := d) (by simp)
    obtain ⟨ie, hieP, he⟩ := indexP (y := e) (by simp)
    by_cases hiac : ia = ic
    · subst ic
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_one_cluster hstrong (i := ia) (J := P)
          (fun h ↦ Finset.disjoint_left.mp hNP hiaN h)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl <;> assumption) hBP) hzA hzB)
    have cross {i j : Fin k} (hi : i ∈ N) (hj : j ∈ P) : i ≠ j := by
      intro h
      exact Finset.disjoint_left.mp hNP hi (h ▸ hj)
    by_cases hibd : ib = id
    · subst id
      by_cases hibie : ib = ie
      · subst ie
        exact False.elim (Set.disjoint_left.mp
          (hulls_disjoint_of_one_cluster hstrong (i := ib) (J := N)
            (fun h ↦ Finset.disjoint_left.mp hNP h hibP)
            (by
              intro y hy
              simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with rfl | rfl | rfl <;> assumption) hAN).symm hzA hzB)
      have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, ie} := by
        exact pair_disjoint_of_mem hNP hiaN hicN hibP hieP
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_two_pairs htwo hiac hibie hpairs
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_union_left _ ha
            · exact Finset.mem_union_right _ hc)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_union_left _ hb
            · exact Finset.mem_union_left _ hd
            · exact Finset.mem_union_right _ he)) hzA hzB)
    by_cases hibe : ib = ie
    · subst ie
      have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, id} := by
        exact pair_disjoint_of_mem hNP hiaN hicN hibP hidP
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_two_pairs htwo hiac hibd hpairs
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_union_left _ ha
            · exact Finset.mem_union_right _ hc)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_union_left _ hb
            · exact Finset.mem_union_right _ hd
            · exact Finset.mem_union_left _ he)) hzA hzB)
    by_cases hide : id = ie
    · subst ie
      have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, id} := by
        exact pair_disjoint_of_mem hNP hiaN hicN hibP hidP
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_two_pairs htwo hiac hibd hpairs
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_union_left _ ha
            · exact Finset.mem_union_right _ hc)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_union_left _ hb
            · exact Finset.mem_union_right _ hd
            · exact Finset.mem_union_right _ he)) hzA hzB)
    left
    refine ⟨ia, ib, ic, id, ie, a, b, c, d, e, ?_, hiaN, hicN, hibP, hidP, hieP,
      ha, hb, hc, hd, he, ?_⟩
    · exact vector5_injective_of_pairwise ia ib ic id ie
        (cross hiaN hibP) hiac (cross hiaN hidP) (cross hiaN hieP)
        (cross hicN hibP).symm hibd hibe (cross hicN hidP)
        (cross hicN hieP) hide
    · exact ⟨z, hzA, hzB⟩
  · obtain ⟨b, d, e, hbd, hbe, hde, hA⟩ := Finset.card_eq_three.mp h32.1
    obtain ⟨a, c, hac, hB⟩ := Finset.card_eq_two.mp h32.2
    subst A; subst B
    obtain ⟨ib, hibN, hb⟩ := indexN (y := b) (by simp)
    obtain ⟨id, hidN, hd⟩ := indexN (y := d) (by simp)
    obtain ⟨ie, hieN, he⟩ := indexN (y := e) (by simp)
    obtain ⟨ia, hiaP, ha⟩ := indexP (y := a) (by simp)
    obtain ⟨ic, hicP, hc⟩ := indexP (y := c) (by simp)
    by_cases hiac : ia = ic
    · subst ic
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_one_cluster hstrong (i := ia) (J := N)
          (fun h ↦ Finset.disjoint_left.mp hNP h hiaP)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl <;> assumption) hAN).symm hzA hzB)
    have cross {i j : Fin k} (hi : i ∈ P) (hj : j ∈ N) : i ≠ j := by
      intro h
      exact Finset.disjoint_left.mp hNP hj (h ▸ hi)
    by_cases hibd : ib = id
    · subst id
      by_cases hibie : ib = ie
      · subst ie
        exact False.elim (Set.disjoint_left.mp
          (hulls_disjoint_of_one_cluster hstrong (i := ib) (J := P)
            (fun h ↦ Finset.disjoint_left.mp hNP hibN h)
            (by
              intro y hy
              simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with rfl | rfl | rfl <;> assumption) hBP) hzA hzB)
      have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, ie} := by
        exact pair_disjoint_of_mem hNP.symm hiaP hicP hibN hieN
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_two_pairs htwo hiac hibie hpairs
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_union_left _ ha
            · exact Finset.mem_union_right _ hc)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_union_left _ hb
            · exact Finset.mem_union_left _ hd
            · exact Finset.mem_union_right _ he)) hzB hzA)
    by_cases hibe : ib = ie
    · subst ie
      have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, id} := by
        exact pair_disjoint_of_mem hNP.symm hiaP hicP hibN hidN
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_two_pairs htwo hiac (by exact fun h ↦ hibd h) hpairs
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_union_left _ ha
            · exact Finset.mem_union_right _ hc)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_union_left _ hb
            · exact Finset.mem_union_right _ hd
            · exact Finset.mem_union_left _ he)) hzB hzA)
    by_cases hide : id = ie
    · subst ie
      have hpairs : Disjoint ({ia, ic} : Finset (Fin k)) {ib, id} := by
        exact pair_disjoint_of_mem hNP.symm hiaP hicP hibN hidN
      exact False.elim (Set.disjoint_left.mp
        (hulls_disjoint_of_two_pairs htwo hiac hibd hpairs
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact Finset.mem_union_left _ ha
            · exact Finset.mem_union_right _ hc)
          (by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact Finset.mem_union_left _ hb
            · exact Finset.mem_union_right _ hd
            · exact Finset.mem_union_right _ he)) hzB hzA)
    right
    refine ⟨ia, ib, ic, id, ie, a, b, c, d, e, ?_, hiaP, hicP, hibN, hidN, hieN,
      ha, hb, hc, hd, he, ?_⟩
    · exact vector5_injective_of_pairwise ia ib ic id ie
        (cross hiaP hibN) hiac (cross hiaP hidN) (cross hiaP hieN)
        (cross hicP hibN).symm hibd hibe (cross hicP hidN)
        (cross hicP hieN) hide
    · exact ⟨z, hzB, hzA⟩

/-- The exact geometric core of Pohoata--Zakharov Proposition 2.7. -/
theorem representativePatternHullsSeparated_of_twoSeparated_of_strong {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {x : Fin k → Point 3} (hx : IsClusterTransversal X x)
    {normal : Point 3 →L[ℝ] ℝ} {offset : ℝ}
    (hpattern : HasRepresentativePlanePattern x normal offset) :
    RepresentativePatternHullsSeparated X x normal offset := by
  classical
  let N := negativeClusterIndices x normal offset
  let P := positiveClusterIndices x normal offset
  have hNP : Disjoint N P := by
    rw [Finset.disjoint_left]
    intro i hiN hiP
    have hn : planeValue normal offset (x i) < 0 := by
      simpa [N, negativeClusterIndices] using hiN
    have hp : 0 < planeValue normal offset (x i) := by
      simpa [P, positiveClusterIndices] using hiP
    linarith
  rw [RepresentativePatternHullsSeparated, Set.disjoint_left]
  intro z hzN hzP
  have hinter : (convexHull ℝ
        ((clusterUnion X N : Finset (Point 3)) : Set (Point 3)) ∩
      convexHull ℝ
        ((clusterUnion X P : Finset (Point 3)) : Set (Point 3))).Nonempty :=
    ⟨z, hzN, hzP⟩
  obtain hfive | hfive := fiveCluster_witness_of_hulls_intersect htwo hstrong hNP hinter
  · obtain ⟨ia, ib, ic, id, ie, a, b, c, d, e, hindices,
      hiaN, hicN, hibP, hidP, hieP, ha, hb, hc, hd, he, hwit⟩ := hfive
    apply fiveCluster_segment_triangle_pattern_impossible htwo hstrong hindices
      ha hb hc hd he hx
    · constructor <;> simpa [N, negativeClusterIndices] using ‹_ ∈ N›
    · constructor
      · simpa [P, positiveClusterIndices] using hibP
      constructor <;> simpa [P, positiveClusterIndices] using ‹_ ∈ P›
    · exact hwit
  · obtain ⟨ia, ib, ic, id, ie, a, b, c, d, e, hindices,
      hiaP, hicP, hibN, hidN, hieN, ha, hb, hc, hd, he, hwit⟩ := hfive
    apply fiveCluster_segment_triangle_pattern_impossible htwo hstrong hindices
      ha hb hc hd he hx (normal := -normal) (offset := -offset)
    · constructor
      · have hp : 0 < planeValue normal offset (x ia) := by
          simpa [P, positiveClusterIndices] using hiaP
        simpa [planeValue] using neg_neg_of_pos hp
      · have hp : 0 < planeValue normal offset (x ic) := by
          simpa [P, positiveClusterIndices] using hicP
        simpa [planeValue] using neg_neg_of_pos hp
    · constructor
      · have hn : planeValue normal offset (x ib) < 0 := by
          simpa [N, negativeClusterIndices] using hibN
        simpa [planeValue] using neg_pos.mpr hn
      constructor
      · have hn : planeValue normal offset (x id) < 0 := by
          simpa [N, negativeClusterIndices] using hidN
        simpa [planeValue] using neg_pos.mpr hn
      · have hn : planeValue normal offset (x ie) < 0 := by
          simpa [N, negativeClusterIndices] using hieN
        simpa [planeValue] using neg_pos.mpr hn
    · exact hwit

private theorem abs_le_sum_abs_of_mem {S : Finset (Point 3)}
    (normal : Point 3 →L[ℝ] ℝ) {y : Point 3} (hy : y ∈ S) :
    |normal y| ≤ ∑ z ∈ S, |normal z| := by
  exact Finset.single_le_sum (fun z _ => abs_nonneg (normal z)) hy

/-- Once the two union hulls are known to be disjoint, finite-dimensional
strict separation produces a plane realizing the representative pattern on
every point of every cluster.  The two one-sided cases are handled by
translating the original nonzero normal beyond the finite point family. -/
theorem liftsRepresentativePlanePattern_of_hullsSeparated {k : ℕ}
    {X : Fin k → Finset (Point 3)} {x : Fin k → Point 3}
    {normal : Point 3 →L[ℝ] ℝ} {offset : ℝ}
    (hx : IsClusterTransversal X x)
    (hpattern : HasRepresentativePlanePattern x normal offset)
    (hsep : RepresentativePatternHullsSeparated X x normal offset) :
    LiftsRepresentativePlanePattern X x normal offset := by
  classical
  let P := positiveClusterIndices x normal offset
  let N := negativeClusterIndices x normal offset
  let U := allClusters X
  let M : ℝ := (∑ z ∈ U, |normal z|) + 1
  by_cases hP : P.Nonempty
  · by_cases hN : N.Nonempty
    · obtain ⟨f, u, hNlt, hPlt⟩ :=
        finite_convexHulls_strictly_separated_point3
          (clusterUnion X N) (clusterUnion X P)
          (by simpa [RepresentativePatternHullsSeparated, P, N] using hsep)
      have hf : f ≠ 0 := by
        intro hf
        obtain ⟨i, hiN⟩ := hN
        obtain ⟨j, hjP⟩ := hP
        have hxiN : x i ∈ clusterUnion X N := by
          simp only [clusterUnion, Finset.mem_biUnion]
          exact ⟨i, hiN, hx i⟩
        have hxjP : x j ∈ clusterUnion X P := by
          simp only [clusterUnion, Finset.mem_biUnion]
          exact ⟨j, hjP, hx j⟩
        have hi := hNlt (x i)
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr hxiN))
        have hj := hPlt (x j)
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr hxjP))
        simp only [hf, zero_apply] at hi hj
        linarith
      refine ⟨f, u, hf, ?_⟩
      intro i y hy
      constructor
      · intro hi
        have hiP : i ∈ P := by
          simpa [P, positiveClusterIndices] using hi
        have hyP : y ∈ clusterUnion X P := by
          simp only [clusterUnion, Finset.mem_biUnion]
          exact ⟨i, hiP, hy⟩
        have := hPlt y
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr hyP))
        dsimp [planeValue]
        linarith
      · intro hi
        have hiN : i ∈ N := by
          simpa [N, negativeClusterIndices] using hi
        have hyN : y ∈ clusterUnion X N := by
          simp only [clusterUnion, Finset.mem_biUnion]
          exact ⟨i, hiN, hy⟩
        have := hNlt y
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr hyN))
        dsimp [planeValue]
        linarith
    · refine ⟨normal, -M, hpattern.1, ?_⟩
      intro i y hy
      have hyU : y ∈ U := by
        rw [mem_allClusters_iff]
        exact ⟨i, hy⟩
      have habs : |normal y| ≤ ∑ z ∈ U, |normal z| :=
        abs_le_sum_abs_of_mem normal hyU
      have hallpos : 0 < planeValue normal (-M) y := by
        have hnegabs : -|normal y| ≤ normal y := neg_abs_le (normal y)
        dsimp [planeValue, M]
        linarith
      constructor
      · exact fun _ => hallpos
      · intro hi
        have hiN : i ∈ N := by
          simpa [N, negativeClusterIndices] using hi
        exact False.elim (hN ⟨i, hiN⟩)
  · refine ⟨normal, M, hpattern.1, ?_⟩
    intro i y hy
    have hyU : y ∈ U := by
      rw [mem_allClusters_iff]
      exact ⟨i, hy⟩
    have habs : |normal y| ≤ ∑ z ∈ U, |normal z| :=
      abs_le_sum_abs_of_mem normal hyU
    have hallneg : planeValue normal M y < 0 := by
      have hleabs : normal y ≤ |normal y| := le_abs_self (normal y)
      dsimp [planeValue, M]
      linarith
    constructor
    · intro hi
      have hiP : i ∈ P := by
        simpa [P, positiveClusterIndices] using hi
      exact False.elim (hP ⟨i, hiP⟩)
    · exact fun _ => hallneg

/-- Pohoata--Zakharov Proposition 2.7: every strict representative-plane
pattern lifts to a strict plane on the full clusters. -/
theorem liftsRepresentativePlanePattern_of_twoSeparated_of_strong {k : ℕ}
    {X : Fin k → Finset (Point 3)}
    (htwo : TwoSeparatedClusters X) (hstrong : StrongConvexPositionClusters X)
    {x : Fin k → Point 3} (hx : IsClusterTransversal X x)
    {normal : Point 3 →L[ℝ] ℝ} {offset : ℝ}
    (hpattern : HasRepresentativePlanePattern x normal offset) :
    LiftsRepresentativePlanePattern X x normal offset :=
  liftsRepresentativePlanePattern_of_hullsSeparated hx hpattern
    (representativePatternHullsSeparated_of_twoSeparated_of_strong
      htwo hstrong hx hpattern)

end

end Erdos651
