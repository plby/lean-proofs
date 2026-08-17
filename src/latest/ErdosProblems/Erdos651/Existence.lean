/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.FiniteRamsey

/-!
Finite Ramsey and convex-geometric existence lemmas for Erdős Problem 651.
-/

namespace Erdos651

open Set Function

noncomputable section

section Ramsey

variable {α : Type*} [DecidableEq α]

/-- A Boolean coloring is constant on all `k`-subsets of `Y`. -/
def BoolHomogeneous (k : ℕ) (color : Finset α → Bool) (Y : Finset α) : Prop :=
  ∃ b, ∀ A : Finset α, A ⊆ Y → A.card = k → color A = b

/-- The ordered sequence used in the elementary induction proof of finite Ramsey's theorem.
The color of a `k+1`-set is determined by its least sequence index. -/
def CanonicalSequence (k t : ℕ) (color : Finset α → Bool) (X R : Finset α) : Prop :=
  ∃ p : Fin t → α, Injective p ∧
    (∀ i, p i ∈ X) ∧ R ⊆ X ∧ Disjoint (Finset.univ.image p) R ∧
    ∃ b : Fin t → Bool, ∀ i (A : Finset α),
      A ⊆ (Finset.univ.filter (i < ·)).image p ∪ R → A.card = k →
        color (insert (p i) A) = b i

/-- Canonical-sequence extraction, assuming finite Ramsey for `k`-sets. -/
lemma canonicalSequence_exists
    (k : ℕ)
    (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ (X : Finset α) (color : Finset α → Bool),
      N ≤ X.card → ∃ Y : Finset α, Y ⊆ X ∧ Y.card = m ∧ BoolHomogeneous k color Y) :
    ∀ t r : ℕ, ∃ N : ℕ, ∀ (X : Finset α) (color : Finset α → Bool),
      N ≤ X.card → ∃ R : Finset α, R.card = r ∧ CanonicalSequence k t color X R := by
  intro t
  induction t with
  | zero =>
      intro r
      refine ⟨r, fun X color hcard ↦ ?_⟩
      obtain ⟨R, hRX, hRcard⟩ := Finset.exists_subset_card_eq hcard
      refine ⟨R, hRcard, ?_⟩
      refine ⟨Fin.elim0, ?_, ?_, hRX, ?_, ?_⟩
      · exact fun i ↦ Fin.elim0 i
      · exact fun i ↦ Fin.elim0 i
      · simp
      · exact ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
  | succ t iht =>
      intro r
      obtain ⟨Nt, hNt⟩ := iht r
      obtain ⟨Nk, hNk⟩ := hr Nt
      refine ⟨Nk + 1, fun X color hcard ↦ ?_⟩
      have hX : X.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        subst X
        simp at hcard
      obtain ⟨x, hxX⟩ := hX
      have hErase : Nk ≤ (X.erase x).card := by
        rw [Finset.card_erase_of_mem hxX]
        omega
      let derived : Finset α → Bool := fun A ↦ color (insert x A)
      obtain ⟨H, hHX, hHcard, hHhom⟩ := hNk (X.erase x) derived hErase
      obtain ⟨R, hRcard, q, hqinj, hqH, hRH, hqR, b, hb⟩ := hNt H color (by omega)
      have hxH : x ∉ H := by
        intro hx
        exact Finset.notMem_erase x X (hHX hx)
      let p : Fin (t + 1) → α := Fin.cases x q
      have hpinj : Injective p := by
        intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => rfl
            | succ j =>
                simp only [p, Fin.cases_zero, Fin.cases_succ] at hij
                exact False.elim (hxH (by simpa [← hij] using hqH j))
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                simp only [p, Fin.cases_zero, Fin.cases_succ] at hij
                exact False.elim (hxH (by simpa [hij] using hqH i))
            | succ j =>
                simp only [p, Fin.cases_succ] at hij
                exact congrArg Fin.succ (hqinj hij)
      refine ⟨R, hRcard, p, hpinj, ?_,
        hRH.trans (hHX.trans (Finset.erase_subset _ _)), ?_, ?_⟩
      · intro i
        refine Fin.cases hxX (fun j ↦ Finset.erase_subset x X (hHX (hqH j))) i
      · refine Finset.disjoint_left.2 ?_
        intro y hy hRy
        rw [Finset.mem_image] at hy
        obtain ⟨i, -, rfl⟩ := hy
        cases i using Fin.cases with
        | zero =>
            simp only [p, Fin.cases_zero] at hRy
            exact Finset.notMem_erase x X (hHX (hRH hRy))
        | succ j =>
            simp only [p, Fin.cases_succ] at hRy
            exact Finset.disjoint_left.1 hqR
              (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩) hRy
      · refine ⟨Fin.cases hHhom.choose b, ?_⟩
        intro i A hA hAcard
        cases i using Fin.cases with
        | zero =>
          simp only [p, Fin.cases_zero] at hA ⊢
          apply hHhom.choose_spec A
          · intro y hy
            have hy' := hA hy
            rw [Finset.mem_union] at hy'
            rcases hy' with hy' | hy'
            · rw [Finset.mem_image] at hy'
              obtain ⟨u, hu, rfl⟩ := hy'
              have hu0 : (0 : Fin (t + 1)) < u := (Finset.mem_filter.1 hu).2
              cases u using Fin.cases with
              | zero => exact False.elim (lt_irrefl 0 hu0)
              | succ v => simpa [p] using hqH v
            · exact hRH hy'
          · exact hAcard
        | succ j =>
          simp only [p, Fin.cases_succ] at hA ⊢
          apply hb j A
          · intro y hy
            have hy' := hA hy
            rw [Finset.mem_union] at hy' ⊢
            rcases hy' with hy' | hy'
            · left
              rw [Finset.mem_image] at hy' ⊢
              obtain ⟨u, hu, rfl⟩ := hy'
              have hju : Fin.succ j < u := (Finset.mem_filter.1 hu).2
              cases u using Fin.cases with
              | zero => exact False.elim (not_lt_of_ge (Fin.zero_le _) hju)
              | succ v =>
                refine ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
                simpa using hju
            · exact Or.inr hy'
          · exact hAcard

/-- Finite Ramsey's theorem for Boolean colorings of uniform finite subsets. -/
theorem finiteRamsey_bool (k m : ℕ) :
    ∃ N : ℕ, ∀ (X : Finset α) (color : Finset α → Bool), N ≤ X.card →
      ∃ Y : Finset α, Y ⊆ X ∧ Y.card = m ∧ BoolHomogeneous k color Y := by
  induction k generalizing m with
  | zero =>
      refine ⟨m, fun X color hcard ↦ ?_⟩
      obtain ⟨Y, hYX, hYcard⟩ := Finset.exists_subset_card_eq hcard
      refine ⟨Y, hYX, hYcard, color ∅, ?_⟩
      intro A hAY hAcard
      have hA : A = ∅ := Finset.card_eq_zero.mp hAcard
      subst A
      rfl
  | succ k ih =>
      have hr : ∀ q : ℕ, ∃ N : ℕ, ∀ (X : Finset α) (color : Finset α → Bool),
          N ≤ X.card → ∃ Y : Finset α, Y ⊆ X ∧ Y.card = q ∧
            BoolHomogeneous k color Y := fun q ↦ ih q
      obtain ⟨N, hN⟩ := canonicalSequence_exists k hr (2 * m) 0
      refine ⟨N, fun X color hcard ↦ ?_⟩
      obtain ⟨R, hRcard, p, hpinj, hpX, hRX, hpR, b, hb⟩ := hN X color hcard
      let T : Finset (Fin (2 * m)) := Finset.univ.filter (b · = true)
      let F : Finset (Fin (2 * m)) := Finset.univ.filter (b · = false)
      have hTF : T.card + F.card = 2 * m := by
        rw [show F = Finset.univ.filter (fun i ↦ ¬ b i = true) by
          ext i
          cases h : b i <;> simp [F, h]]
        simpa [T] using Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin (2 * m)))) (fun i ↦ b i = true)
      have hlarge : m ≤ T.card ∨ m ≤ F.card := by omega
      obtain ⟨I, hITF, hIcard, c, hc⟩ :
          ∃ I : Finset (Fin (2 * m)), (I ⊆ T ∨ I ⊆ F) ∧ I.card = m ∧
            ∃ c : Bool, ∀ i ∈ I, b i = c := by
        rcases hlarge with hT | hF
        · obtain ⟨I, hIT, hIcard⟩ := Finset.exists_subset_card_eq hT
          exact ⟨I, Or.inl hIT, hIcard, true, fun i hi ↦
            (Finset.mem_filter.1 (hIT hi)).2⟩
        · obtain ⟨I, hIF, hIcard⟩ := Finset.exists_subset_card_eq hF
          exact ⟨I, Or.inr hIF, hIcard, false, fun i hi ↦
            (Finset.mem_filter.1 (hIF hi)).2⟩
      let Y := I.image p
      have hYcard : Y.card = m := by
        change (I.image p).card = m
        rw [Finset.card_image_iff.mpr hpinj.injOn, hIcard]
      refine ⟨Y, ?_, hYcard, c, ?_⟩
      · intro y hy
        change y ∈ I.image p at hy
        rw [Finset.mem_image] at hy
        obtain ⟨i, hi, rfl⟩ := hy
        exact hpX i
      · intro A hAY hAcard
        have hAne : A.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          subst A
          simp at hAcard
        let J : Finset (Fin (2 * m)) := A.preimage p (Set.injOn_of_injective hpinj)
        have hJimage : J.image p = A := by
          apply Finset.Subset.antisymm
          · intro y hy
            rw [Finset.mem_image] at hy
            obtain ⟨i, hi, rfl⟩ := hy
            exact Finset.mem_preimage.1 hi
          · intro y hy
            have hyY := hAY hy
            change y ∈ I.image p at hyY
            rw [Finset.mem_image] at hyY
            obtain ⟨i, hi, rfl⟩ := hyY
            exact Finset.mem_image.2 ⟨i, Finset.mem_preimage.2 hy, rfl⟩
        have hJcard : J.card = k + 1 := by
          rw [← hAcard, ← hJimage, Finset.card_image_iff.mpr hpinj.injOn]
        have hJne : J.Nonempty := by simpa [Finset.card_pos] using show 0 < J.card by omega
        let i := J.min' hJne
        have hiJ : i ∈ J := J.min'_mem hJne
        have hiI : i ∈ I := by
          have hpA : p i ∈ A := by
            rw [← hJimage]
            exact Finset.mem_image.2 ⟨i, hiJ, rfl⟩
          have := hAY hpA
          change p i ∈ I.image p at this
          rw [Finset.mem_image] at this
          obtain ⟨j, hjI, hpji⟩ := this
          exact hpinj hpji ▸ hjI
        let B := (J.erase i).image p
        have hBcard : B.card = k := by
          change ((J.erase i).image p).card = k
          rw [Finset.card_image_iff.mpr hpinj.injOn, Finset.card_erase_of_mem hiJ, hJcard]
          omega
        have hBtail : B ⊆ (Finset.univ.filter (i < ·)).image p ∪ R := by
          intro y hy
          apply Finset.mem_union_left
          change y ∈ (J.erase i).image p at hy
          rw [Finset.mem_image] at hy ⊢
          obtain ⟨j, hj, rfl⟩ := hy
          refine ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
          exact lt_of_le_of_ne (J.min'_le j (Finset.mem_of_mem_erase hj))
            (Ne.symm (Finset.ne_of_mem_erase hj))
        have hAB : insert (p i) B = A := by
          change insert (p i) ((J.erase i).image p) = A
          rw [← Finset.image_insert, Finset.insert_erase hiJ, hJimage]
        rw [← hAB, hb i B hBtail hBcard, hc i hiI]

end Ramsey

section Infimum

/-- Exact least-threshold specification of the natural-number infimum. -/
theorem erdosSzekeresNumber_eq_iff {d n N : ℕ} (h : HasErdosSzekeresNumber d n) :
    erdosSzekeresNumber d n = N ↔
      ForcesConvexSubset d n N ∧ ∀ M, ForcesConvexSubset d n M → N ≤ M := by
  constructor
  · intro heq
    subst N
    exact ⟨erdosSzekeresNumber_forces h, fun M hM ↦ erdosSzekeresNumber_le hM⟩
  · rintro ⟨hN, hleast⟩
    exact Nat.le_antisymm (erdosSzekeresNumber_le hN)
      (hleast _ (erdosSzekeresNumber_forces h))

/-- Above the exact infimum, and only there, the convex-subset property is forced. -/
theorem forcesConvexSubset_iff_erdosSzekeresNumber_le {d n N : ℕ}
    (h : HasErdosSzekeresNumber d n) :
    ForcesConvexSubset d n N ↔ erdosSzekeresNumber d n ≤ N := by
  constructor
  · exact erdosSzekeresNumber_le
  · intro hle
    exact (erdosSzekeresNumber_forces h).mono hle

end Infimum

section SmallConfigurations

/-- A subset of at most four points of a 3-dimensional general-position set is in convex
position, provided the ambient set has at least four points. -/
lemma inConvexPosition_of_card_le_four {X Y : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hYX : Y ⊆ X) (hYcard : Y.card ≤ 4)
    (hXcard : 4 ≤ X.card) : InConvexPosition Y := by
  obtain ⟨S, hYS, hSX, hScard⟩ :=
    Finset.exists_subsuperset_card_eq hYX hYcard hXcard
  have hAI : AffineIndependent ℝ (fun p : ↥S ↦ (p : Point 3)) := by
    apply hgp S hSX
    norm_num at hScard ⊢
    exact hScard
  intro x hxY hx
  have hx' : x ∈ convexHull ℝ ({x} : Set (Point 3)) ∩
      convexHull ℝ (↑(Y.erase x) : Set (Point 3)) := ⟨by simp, hx⟩
  have hinter := hAI.convexHull_inter
    (show ({x} : Finset (Point 3)) ⊆ S by simpa using hYS hxY)
    (Finset.erase_subset x Y |>.trans hYS)
  have hx'' : x ∈ convexHull ℝ
      ((↑({x} : Finset (Point 3)) : Set (Point 3)) ∩
        (↑(Y.erase x) : Set (Point 3))) := by
    rw [hinter]
    simpa using hx'
  have hempty : ((↑({x} : Finset (Point 3)) : Set (Point 3)) ∩
      (↑(Y.erase x) : Set (Point 3))) = ∅ := by
    ext y
    simp
  rw [hempty, convexHull_empty] at hx''
  exact hx''

/-- The elementary range of Erdős--Szekeres numbers in dimension three. -/
theorem hasErdosSzekeresNumber_three_of_le_four {n : ℕ} (hn : n ≤ 4) :
    HasErdosSzekeresNumber 3 n := by
  refine ⟨4, ?_⟩
  intro X hXcard hgp
  obtain ⟨Y, hYX, hYcard⟩ := Finset.exists_subset_card_eq (hn.trans hXcard)
  exact ⟨Y, hYX, hYcard,
    inConvexPosition_of_card_le_four hgp hYX (by omega) hXcard⟩

end SmallConfigurations

section RamseyAssembly

/-- Convex position is inherited by subsets. -/
lemma inConvexPosition_mono {d : ℕ} {X Y : Finset (Point d)}
    (hX : InConvexPosition X) (hYX : Y ⊆ X) : InConvexPosition Y := by
  intro x hxY hxHull
  apply hX x (hYX hxY)
  apply convexHull_mono ?_ hxHull
  intro y hy
  exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hy).1,
    hYX (Finset.mem_of_mem_erase hy)⟩

/-- An affine functional which is negative at one point and nonnegative on a finite set
separates that point from the set's convex hull. -/
lemma not_mem_convexHull_of_affine_lt_zero {d : ℕ} {x : Point d}
    {S : Finset (Point d)} (f : Point d →ᵃ[ℝ] ℝ) (hx : f x < 0)
    (hS : ∀ y ∈ S, 0 ≤ f y) : x ∉ convexHull ℝ (↑S : Set (Point d)) := by
  intro hxHull
  have hxNonneg : 0 ≤ f x := by
    apply convexHull_min (s := (↑S : Set (Point d)))
        (t := f ⁻¹' Set.Ici 0) ?_ (convex_Ici 0 |>.affine_preimage f) hxHull
    intro y hy
    exact hS y hy
  exact (not_le_of_gt hx) hxNonneg

/-- Dually, a functional which is strictly less than one on a finite set separates a point
where it takes the value one. -/
lemma not_mem_convexHull_of_affine_eq_one {d : ℕ} {x : Point d}
    {S : Finset (Point d)} (f : Point d →ᵃ[ℝ] ℝ) (hx : f x = 1)
    (hS : ∀ y ∈ S, f y < 1) : x ∉ convexHull ℝ (↑S : Set (Point d)) := by
  intro hxHull
  have hxLt : f x < 1 := by
    apply convexHull_min (s := (↑S : Set (Point d)))
        (t := f ⁻¹' Set.Iio 1) ?_ (convex_Iio 1 |>.affine_preimage f) hxHull
    intro y hy
    exact hS y hy
  linarith

/-- The vertices of the convex hull of a finite set form a convex-position subset with the
same convex hull. -/
lemma exists_hull_vertex_finset {d : ℕ} (X : Finset (Point d)) :
    ∃ V : Finset (Point d), V ⊆ X ∧ InConvexPosition V ∧
      convexHull ℝ (↑V : Set (Point d)) = convexHull ℝ (↑X : Set (Point d)) := by
  classical
  let K : Set (Point d) := convexHull ℝ (↑X : Set (Point d))
  let V : Finset (Point d) := X.filter fun x ↦ x ∈ K.extremePoints ℝ
  have hVK : (↑V : Set (Point d)) = K.extremePoints ℝ := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.1 hx).2
    · intro hx
      exact Finset.mem_filter.2 ⟨by
        exact extremePoints_convexHull_subset hx, hx⟩
  have hVconvex : InConvexPosition V := by
    intro x hxV hxHull
    have hxExtreme : x ∈ K.extremePoints ℝ := hVK ▸ hxV
    have hxCharacterization :=
      (convex_convexHull ℝ (↑X : Set (Point d))).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.1
        hxExtreme
    apply hxCharacterization.2
    apply convexHull_mono ?_ hxHull
    intro y hy
    refine ⟨?_, ?_⟩
    · apply subset_convexHull ℝ
      exact Finset.mem_of_mem_erase hy |> Finset.mem_filter.1 |>.1
    · simpa using (Finset.mem_erase.1 hy).1
  have hKcompact : IsCompact K := by
    exact (Set.toFinite (↑X : Set (Point d))).isCompact_convexHull ℝ
  have hVclosed : IsClosed (convexHull ℝ (↑V : Set (Point d))) := by
    exact (Set.toFinite (↑V : Set (Point d))).isCompact_convexHull ℝ |>.isClosed
  have hKM := closure_convexHull_extremePoints hKcompact (convex_convexHull ℝ
    (↑X : Set (Point d)))
  refine ⟨V, fun x hx ↦ (Finset.mem_filter.1 hx).1, hVconvex, ?_⟩
  calc
    convexHull ℝ (↑V : Set (Point d)) =
        closure (convexHull ℝ (↑V : Set (Point d))) := hVclosed.closure_eq.symm
    _ = closure (convexHull ℝ (K.extremePoints ℝ)) := by rw [hVK]
    _ = K := hKM
    _ = convexHull ℝ (↑X : Set (Point d)) := rfl

/-- A six-point general-position set in three-space has at least four convex-hull vertices. -/
lemma four_le_card_of_same_hull {X V : Finset (Point 3)} (hXcard : X.card = 6)
    (hgp : InGeneralPosition 3 X) (hVX : V ⊆ X)
    (hHull : convexHull ℝ (↑V : Set (Point 3)) =
      convexHull ℝ (↑X : Set (Point 3))) :
    4 ≤ V.card := by
  classical
  obtain ⟨S, hSX, hScard⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ X.card by omega)
  have hAI : AffineIndependent ℝ (fun p : ↥S ↦ (p : Point 3)) := by
    apply hgp S hSX
    norm_num at hScard ⊢
    exact hScard
  have hSspan : affineSpan ℝ (↑S : Set (Point 3)) = ⊤ := by
    have := hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 (by
      simpa [Point] using hScard)
    simpa using this
  have hSVspan : affineSpan ℝ (↑S : Set (Point 3)) ≤
      affineSpan ℝ (↑V : Set (Point 3)) := by
    apply affineSpan_le_of_subset_coe
    intro x hxS
    have hxHullX : x ∈ convexHull ℝ (↑X : Set (Point 3)) :=
      subset_convexHull ℝ _ (hSX hxS)
    rw [← hHull] at hxHullX
    exact (convexHull_subset_affineSpan (𝕜 := ℝ) (↑V : Set (Point 3))) hxHullX
  have hVspan : affineSpan ℝ (↑V : Set (Point 3)) = ⊤ := by
    apply top_unique
    simpa [hSspan] using hSVspan
  have hVne : V.Nonempty := by
    simpa using AffineSubspace.nonempty_of_affineSpan_eq_top ℝ (Point 3) (Point 3) hVspan
  letI : Nonempty ↥V := Fintype.card_pos_iff.mp (by simpa using V.card_pos.mpr hVne)
  have hVvector : vectorSpan ℝ (Set.range (fun p : ↥V ↦ (p : Point 3))) = ⊤ := by
    apply AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ (Point 3) (Point 3)
    simpa using hVspan
  have hdim := finrank_vectorSpan_range_add_one_le ℝ
    (fun p : ↥V ↦ (p : Point 3))
  rw [hVvector] at hdim
  simpa [Point] using hdim

/-- A point of a general-position set which is not a vertex of a tetrahedral affine basis
cannot lie on one of the basis coordinate hyperplanes. -/
lemma affineBasis_coord_pos_of_gp {X V : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hVX : V ⊆ X) (hVcard : V.card = 4)
    (b : AffineBasis ↥V ℝ (Point 3))
    (hb : (b : ↥V → Point 3) = fun v ↦ (v : Point 3))
    {p : Point 3} (hpX : p ∈ X) (hpV : p ∉ V) (i : ↥V)
    (hcoord : 0 ≤ b.coord i p) : 0 < b.coord i p := by
  classical
  have hne : b.coord i p ≠ 0 := by
    intro hzero
    let S : Finset (Point 3) := insert p (V.erase (b i))
    have hbi : b i = (i : Point 3) := by simpa only [hb]
    have hSsubset : S ⊆ X := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hpX
      · exact hVX (Finset.mem_of_mem_erase hx)
    have hpErase : p ∉ V.erase (b i) := fun hp ↦ hpV (Finset.mem_of_mem_erase hp)
    have hScard : S.card = 4 := by
      simp only [S, Finset.card_insert_of_notMem hpErase,
        Finset.card_erase_of_mem (hbi ▸ i.property), hVcard]
    have hAI : AffineIndependent ℝ (fun x : ↥S ↦ (x : Point 3)) := by
      apply hgp S hSsubset
      norm_num at hScard ⊢
      exact hScard
    have hSspan : affineSpan ℝ (↑S : Set (Point 3)) = ⊤ := by
      have := hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 (by
        simpa [Point] using hScard)
      simpa using this
    have hagree : (↑S : Set (Point 3)).EqOn (b.coord i) 0 := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · simpa using hzero
      · have hxV : x ∈ V := Finset.mem_of_mem_erase hx
        let j : ↥V := ⟨x, hxV⟩
        have hji : j ≠ i := by
          intro hji
          have : x = b i := by simpa [j, hb] using congrArg Subtype.val hji
          exact (Finset.mem_erase.1 hx).1 this
        simpa [j] using b.coord_apply_ne hji.symm
    have heq : b.coord i = 0 := AffineMap.ext_on hSspan hagree
    have := congrArg (fun f : Point 3 →ᵃ[ℝ] ℝ ↦ f (b i)) heq
    simpa using this
  exact lt_of_le_of_ne hcoord (Ne.symm hne)

/-- The coordinate ratios of two nonvertex points relative to a tetrahedral affine basis are
pairwise distinct in general position. -/
lemma affineBasis_coord_ratio_injective_of_gp {X V : Finset (Point 3)}
    (hgp : InGeneralPosition 3 X) (hVX : V ⊆ X) (hVcard : V.card = 4)
    (b : AffineBasis ↥V ℝ (Point 3))
    (hb : (b : ↥V → Point 3) = fun v ↦ (v : Point 3))
    {p q : Point 3} (hpX : p ∈ X) (hqX : q ∈ X) (hpV : p ∉ V) (hqV : q ∉ V)
    (hpq : p ≠ q) (hpcoord : ∀ i, 0 < b.coord i p)
    (hqcoord : ∀ i, 0 < b.coord i q) :
    Function.Injective (fun i : ↥V ↦ b.coord i p / b.coord i q) := by
  classical
  intro i j hratio
  by_contra hij
  have hbij : b i ≠ b j := b.ind.injective hij
  let W : Finset (Point 3) := (V.erase (b i)).erase (b j)
  let S : Finset (Point 3) := insert p (insert q W)
  have hbiV : b i ∈ V := by simpa [hb] using i.property
  have hbjErase : b j ∈ V.erase (b i) :=
    Finset.mem_erase.2 ⟨hbij.symm, by simpa [hb] using j.property⟩
  have hqW : q ∉ W := fun hq ↦ hqV
    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq))
  have hpInsert : p ∉ insert q W := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hpq, fun hp ↦ hpV
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp))⟩
  have hScard : S.card = 4 := by
    simp only [S, Finset.card_insert_of_notMem hpInsert,
      Finset.card_insert_of_notMem hqW, W,
      Finset.card_erase_of_mem hbjErase, Finset.card_erase_of_mem hbiV, hVcard]
  have hSsubset : S ⊆ X := by
    intro x hx
    simp only [S, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hpX
    · exact hqX
    · exact hVX (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
  have hAI : AffineIndependent ℝ (fun x : ↥S ↦ (x : Point 3)) := by
    apply hgp S hSsubset
    norm_num at hScard ⊢
    exact hScard
  have hSspan : affineSpan ℝ (↑S : Set (Point 3)) = ⊤ := by
    have := hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 (by
      simpa [Point] using hScard)
    simpa using this
  let f : Point 3 →ᵃ[ℝ] ℝ :=
    (b.coord j q) • b.coord i - (b.coord i q) • b.coord j
  have hfp : f p = 0 := by
    have hcross : b.coord i p * b.coord j q = b.coord j p * b.coord i q :=
      (div_eq_div_iff (hqcoord i).ne' (hqcoord j).ne').mp hratio
    dsimp only [f]
    simp only [AffineMap.smul_apply, AffineMap.sub_apply]
    linarith
  have hfq : f q = 0 := by
    simp [f]
  have hagree : (↑S : Set (Point 3)).EqOn f 0 := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · simpa using hfp
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · simpa using hfq
    have hxV : x ∈ V := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
    let k : ↥V := ⟨x, hxV⟩
    have hki : k ≠ i := by
      intro hki
      have : x = b i := by simpa [k, hb] using congrArg Subtype.val hki
      exact (Finset.mem_erase.1 (Finset.mem_of_mem_erase hx)).1 this
    have hkj : k ≠ j := by
      intro hkj
      have : x = b j := by simpa [k, hb] using congrArg Subtype.val hkj
      exact (Finset.mem_erase.1 hx).1 this
    have hxk : b k = x := by simp [k, hb]
    rw [← hxk]
    simp [f, b.coord_apply_ne hki.symm, b.coord_apply_ne hkj.symm]
  have heq : f = 0 := AffineMap.ext_on hSspan hagree
  have heval := congrArg (fun g : Point 3 →ᵃ[ℝ] ℝ ↦ g (b i)) heq
  have hpositive : 0 < f (b i) := by
    simp [f, b.coord_apply_ne hij]
    exact hqcoord j
  have : f (b i) = 0 := by simpa using heval
  linarith

/-- Among four distinct real values, one is strictly between two others. -/
lemma exists_strictly_between_of_card_four {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 4) (r : ι → ℝ) (hr : Function.Injective r) :
    ∃ i j k : ι, r j < r i ∧ r i < r k := by
  classical
  let R : Finset ℝ := Finset.univ.image r
  have hRcard : R.card = 4 := by
    simp only [R, Finset.card_image_iff.mpr hr.injOn, Finset.card_univ, hcard]
  have hRne : R.Nonempty := by simpa [Finset.card_pos, hRcard]
  let lo : ℝ := R.min' hRne
  let hi : ℝ := R.max' hRne
  have hnot : ¬R ⊆ {lo, hi} := by
    intro hsub
    have := Finset.card_le_card hsub
    have hp : ({lo, hi} : Finset ℝ).card ≤ 2 := Finset.card_pair_le _ _
    omega
  obtain ⟨x, hxR, hxpair⟩ := Finset.not_subset.mp hnot
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hxR
  have hloMem : lo ∈ R := by exact R.min'_mem hRne
  have hhiMem : hi ∈ R := by exact R.max'_mem hRne
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hloMem
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hhiMem
  refine ⟨i, j, k, ?_, ?_⟩
  · rw [hj]
    exact lt_of_le_of_ne (R.min'_le _ _ hxR) (by simpa using hxpair)
  · rw [hk]
    exact lt_of_le_of_ne (R.le_max' _ _ hxR) (by simpa [eq_comm] using hxpair)

/-- If every barycentric coordinate is positive and there is another basis vertex, then each
individual coordinate is strictly less than one. -/
lemma AffineBasis.coord_lt_one_of_pos {ι : Type*} [Fintype ι] [Nontrivial ι]
    (b : AffineBasis ι ℝ (Point 3)) {p : Point 3} (hpos : ∀ i, 0 < b.coord i p)
    (i : ι) : b.coord i p < 1 := by
  classical
  obtain ⟨j, hji⟩ := exists_ne i
  have hj : j ∈ (Finset.univ.erase i : Finset ι) :=
    Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩
  have hrest : 0 < ∑ j ∈ Finset.univ.erase i, b.coord j p :=
    Finset.sum_pos' (fun j _ ↦ (hpos j).le) ⟨j, hj, hpos j⟩
  have hsum := b.sum_coord_apply_eq_one p
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
  linarith

/-- Deleting a non-extremal ratio vertex from a tetrahedral basis and inserting two strictly
interior points produces five points in convex position. -/
lemma inConvexPosition_face_insert_two {V : Finset (Point 3)}
    (b : AffineBasis ↥V ℝ (Point 3))
    (hb : (b : ↥V → Point 3) = fun v ↦ (v : Point 3))
    {p q : Point 3} (hpV : p ∉ V) (hqV : q ∉ V) (hpq : p ≠ q)
    (hpcoord : ∀ i, 0 < b.coord i p) (hqcoord : ∀ i, 0 < b.coord i q)
    {i j k : ↥V}
    (hji : b.coord j p / b.coord j q < b.coord i p / b.coord i q)
    (hik : b.coord i p / b.coord i q < b.coord k p / b.coord k q) :
    InConvexPosition (insert p (insert q (V.erase (b i)))) := by
  classical
  have hji_ne : j ≠ i := by
    intro h
    subst j
    exact (lt_irrefl _ hji)
  letI : Nontrivial ↥V := ⟨⟨j, i, hji_ne⟩⟩
  let Y : Finset (Point 3) := insert p (insert q (V.erase (b i)))
  intro x hxY
  simp only [Y, Finset.mem_insert] at hxY
  rcases hxY with rfl | rfl | hxFace
  · let f : Point 3 →ᵃ[ℝ] ℝ :=
      (b.coord i q) • b.coord j - (b.coord j q) • b.coord i
    have hcross : b.coord j p * b.coord i q < b.coord i p * b.coord j q :=
      (div_lt_div_iff₀ (hqcoord j) (hqcoord i)).mp hji
    have hfp : f p < 0 := by
      simp only [f, AffineMap.smul_apply, AffineMap.sub_apply]
      linarith
    apply not_mem_convexHull_of_affine_lt_zero f hfp
    intro y hy
    have hyY := Finset.mem_of_mem_erase hy
    have hyp : y ≠ p := (Finset.mem_erase.1 hy).1
    simp only [Y, Finset.mem_insert] at hyY
    rcases hyY with rfl | rfl | hyFace
    · exact False.elim (hyp rfl)
    · simp [f]
    · have hyV : y ∈ V := Finset.mem_of_mem_erase hyFace
      let l : ↥V := ⟨y, hyV⟩
      have hil : i ≠ l := by
        intro hil
        have : y = b i := by simpa [l, hb] using congrArg Subtype.val hil.symm
        exact (Finset.mem_erase.1 hyFace).1 this
      have hyl : b l = y := by simp [l, hb]
      rw [← hyl]
      by_cases hlj : l = j
      · subst l
        simp [f, b.coord_apply_ne hji_ne.symm]
        exact (hqcoord i).le
      · simp [f, b.coord_apply_ne hil, b.coord_apply_ne hlj.symm]
  · let f : Point 3 →ᵃ[ℝ] ℝ :=
      (b.coord i p) • b.coord k - (b.coord k p) • b.coord i
    have hcross : b.coord i p * b.coord k q < b.coord k p * b.coord i q :=
      (div_lt_div_iff₀ (hqcoord i) (hqcoord k)).mp hik
    have hfq : f q < 0 := by
      simp only [f, AffineMap.smul_apply, AffineMap.sub_apply]
      linarith
    apply not_mem_convexHull_of_affine_lt_zero f hfq
    intro y hy
    have hyY := Finset.mem_of_mem_erase hy
    have hyq : y ≠ q := (Finset.mem_erase.1 hy).1
    simp only [Y, Finset.mem_insert] at hyY
    rcases hyY with rfl | rfl | hyFace
    · simp [f]
    · exact False.elim (hyq rfl)
    · have hyV : y ∈ V := Finset.mem_of_mem_erase hyFace
      let l : ↥V := ⟨y, hyV⟩
      have hil : i ≠ l := by
        intro hil
        have : y = b i := by simpa [l, hb] using congrArg Subtype.val hil.symm
        exact (Finset.mem_erase.1 hyFace).1 this
      have hyl : b l = y := by simp [l, hb]
      rw [← hyl]
      by_cases hlk : l = k
      · subst l
        have hki : k ≠ i := by
          intro h
          subst k
          exact lt_irrefl _ hik
        simp [f, b.coord_apply_ne hki.symm]
        exact (hpcoord i).le
      · simp [f, b.coord_apply_ne hil, b.coord_apply_ne hlk.symm]
  · have hxV : x ∈ V := Finset.mem_of_mem_erase hxFace
    let l : ↥V := ⟨x, hxV⟩
    have hxl : b l = x := by simp [l, hb]
    apply not_mem_convexHull_of_affine_eq_one (b.coord l)
    · rw [← hxl]
      exact b.coord_apply_eq l
    · intro y hy
      have hyY := Finset.mem_of_mem_erase hy
      have hyx : y ≠ x := (Finset.mem_erase.1 hy).1
      simp only [Y, Finset.mem_insert] at hyY
      rcases hyY with rfl | rfl | hyFace'
      · exact b.coord_lt_one_of_pos hpcoord l
      · exact b.coord_lt_one_of_pos hqcoord l
      · have hyV : y ∈ V := Finset.mem_of_mem_erase hyFace'
        let m : ↥V := ⟨y, hyV⟩
        have hym : b m = y := by simp [m, hb]
        have hlm : l ≠ m := by
          intro hlm
          apply hyx
          rw [← hxl, ← hym, hlm]
        rw [← hym]
        simpa [b.coord_apply_ne hlm] using (show (0 : ℝ) < 1 by norm_num)

/-- Every six points in general position in three-space contain five points in convex position. -/
theorem six_points_contain_convex_five {X : Finset (Point 3)}
    (hXcard : X.card = 6) (hgp : InGeneralPosition 3 X) :
    ∃ Y : Finset (Point 3), Y ⊆ X ∧ Y.card = 5 ∧ InConvexPosition Y := by
  classical
  obtain ⟨V, hVX, hVconvex, hHull⟩ := exists_hull_vertex_finset X
  have hVfour : 4 ≤ V.card := four_le_card_of_same_hull hXcard hgp hVX hHull
  by_cases hVfive : 5 ≤ V.card
  · obtain ⟨Y, hYV, hYcard⟩ := Finset.exists_subset_card_eq hVfive
    exact ⟨Y, hYV.trans hVX, hYcard, inConvexPosition_mono hVconvex hYV⟩
  have hVcard : V.card = 4 := by omega
  have hAIV : AffineIndependent ℝ (fun v : ↥V ↦ (v : Point 3)) := by
    apply hgp V hVX
    norm_num at hVcard ⊢
    exact hVcard
  have hVspan : affineSpan ℝ (Set.range (fun v : ↥V ↦ (v : Point 3))) = ⊤ :=
    hAIV.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 (by
      simpa [Point] using hVcard)
  let b : AffineBasis ↥V ℝ (Point 3) := ⟨fun v ↦ (v : Point 3), hAIV, hVspan⟩
  have hb : (b : ↥V → Point 3) = fun v ↦ (v : Point 3) := rfl
  have hDiffCard : (X \ V).card = 2 := by
    rw [Finset.card_sdiff hVX, hXcard, hVcard]
  obtain ⟨p, q, hpq, hDiff⟩ := Finset.card_eq_two.mp hDiffCard
  have hpDiff : p ∈ X \ V := by rw [hDiff]; simp
  have hqDiff : q ∈ X \ V := by rw [hDiff]; simp
  have hpX : p ∈ X := (Finset.mem_sdiff.1 hpDiff).1
  have hqX : q ∈ X := (Finset.mem_sdiff.1 hqDiff).1
  have hpV : p ∉ V := (Finset.mem_sdiff.1 hpDiff).2
  have hqV : q ∉ V := (Finset.mem_sdiff.1 hqDiff).2
  have hpHullV : p ∈ convexHull ℝ (↑V : Set (Point 3)) := by
    rw [hHull]
    exact subset_convexHull ℝ _ hpX
  have hqHullV : q ∈ convexHull ℝ (↑V : Set (Point 3)) := by
    rw [hHull]
    exact subset_convexHull ℝ _ hqX
  have hpcoordNonneg : ∀ i, 0 ≤ b.coord i p := by
    have hpRange : p ∈ convexHull ℝ (Set.range b) := by simpa [b] using hpHullV
    rw [b.convexHull_eq_nonneg_coord] at hpRange
    exact hpRange
  have hqcoordNonneg : ∀ i, 0 ≤ b.coord i q := by
    have hqRange : q ∈ convexHull ℝ (Set.range b) := by simpa [b] using hqHullV
    rw [b.convexHull_eq_nonneg_coord] at hqRange
    exact hqRange
  have hpcoord : ∀ i, 0 < b.coord i p := fun i ↦
    affineBasis_coord_pos_of_gp hgp hVX hVcard b hb hpX hpV i (hpcoordNonneg i)
  have hqcoord : ∀ i, 0 < b.coord i q := fun i ↦
    affineBasis_coord_pos_of_gp hgp hVX hVcard b hb hqX hqV i (hqcoordNonneg i)
  have hratio : Function.Injective (fun i : ↥V ↦ b.coord i p / b.coord i q) :=
    affineBasis_coord_ratio_injective_of_gp hgp hVX hVcard b hb hpX hqX hpV hqV hpq
      hpcoord hqcoord
  obtain ⟨i, j, k, hji, hik⟩ := exists_strictly_between_of_card_four
    (by simpa using hVcard) (fun i : ↥V ↦ b.coord i p / b.coord i q) hratio
  let Y : Finset (Point 3) := insert p (insert q (V.erase (b i)))
  have hYsubset : Y ⊆ X := by
    intro x hx
    simp only [Y, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hpX
    · exact hqX
    · exact hVX (Finset.mem_of_mem_erase hx)
  have hbiV : b i ∈ V := by simpa [hb] using i.property
  have hqErase : q ∉ V.erase (b i) := fun hq ↦ hqV (Finset.mem_of_mem_erase hq)
  have hpInsert : p ∉ insert q (V.erase (b i)) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hpq, fun hp ↦ hpV (Finset.mem_of_mem_erase hp)⟩
  have hYcard : Y.card = 5 := by
    simp only [Y, Finset.card_insert_of_notMem hpInsert,
      Finset.card_insert_of_notMem hqErase, Finset.card_erase_of_mem hbiV, hVcard]
  exact ⟨Y, hYsubset, hYcard,
    inConvexPosition_face_insert_two b hb hpV hqV hpq hpcoord hqcoord hji hik⟩

/-- In dimension three it suffices to test convex position on five-point subsets. -/
theorem inConvexPosition_of_five_subsets {X : Finset (Point 3)} (hXcard : 5 ≤ X.card)
    (hfive : ∀ Y : Finset (Point 3), Y ⊆ X → Y.card = 5 → InConvexPosition Y) :
    InConvexPosition X := by
  intro x hxX hxHull
  let T : Finset (Point 3) := Caratheodory.minCardFinsetOfMemConvexHull hxHull
  have hTXerase : (↑T : Set (Point 3)) ⊆ (↑(X.erase x) : Set (Point 3)) :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hxHull
  have hxT : x ∈ convexHull ℝ (↑T : Set (Point 3)) :=
    Caratheodory.mem_minCardFinsetOfMemConvexHull hxHull
  have hTcard : T.card ≤ 4 := by
    have hAI := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hxHull
    have hcard := hAI.card_le_finrank_succ
    let V := vectorSpan ℝ (Set.range
      (fun p : ↥(Caratheodory.minCardFinsetOfMemConvexHull hxHull) ↦ (p : Point 3)))
    have hcard' : Fintype.card ↥T ≤ Module.finrank ℝ V + 1 := by
      dsimp only [T, V]
      exact hcard
    have hle : Fintype.card ↥T ≤ Module.finrank ℝ (Point 3) + 1 :=
      hcard'.trans (Nat.add_le_add_right (Submodule.finrank_le V) 1)
    rw [Fintype.card_coe] at hle
    simpa [Point] using hle
  have hTX : T ⊆ X := by
    intro y hy
    exact Finset.mem_of_mem_erase (hTXerase hy)
  have hZcard : (insert x T).card ≤ 5 := by
    exact (Finset.card_insert_le x T).trans (by omega)
  have hZX : insert x T ⊆ X := by
    simpa [Finset.insert_subset_iff, hxX] using hTX
  obtain ⟨Y, hZY, hYX, hYcard⟩ :=
    Finset.exists_subsuperset_card_eq hZX hZcard hXcard
  apply hfive Y hYX hYcard x (hZY (Finset.mem_insert_self x T))
  apply convexHull_mono ?_ hxT
  intro y hy
  have hyY : y ∈ Y := hZY (Finset.mem_insert_of_mem hy)
  have hyne : y ≠ x := by
    intro hyx
    subst y
    exact Finset.notMem_erase x X (hTXerase hy)
  exact Finset.mem_erase.2 ⟨hyne, hyY⟩

/-- The explicit five-uniform Ramsey bound forces an `n`-point convex-position subset in
three-space. -/
theorem uniformRamseyBound_five_forcesConvexSubset_three (n : ℕ) :
    ForcesConvexSubset 3 n (uniformRamseyBound 5 (max 6 n)) := by
  classical
  intro X hXcard hgp
  let color : Finset (Point 3) → Bool := fun A ↦ decide (InConvexPosition A)
  obtain ⟨H, hHX, hHcard, hHmono⟩ :=
    uniformRamseyBound_spec 5 (max 6 n) X hXcard color
  have hgpH : InGeneralPosition 3 H := by
    intro S hSH hScard
    exact hgp S (hSH.trans hHX) hScard
  have hHsix : 6 ≤ H.card := by omega
  obtain ⟨S, hSH, hScard⟩ := Finset.exists_subset_card_eq hHsix
  have hgpS : InGeneralPosition 3 S := by
    intro T hTS hTcard
    exact hgpH T (hTS.trans hSH) hTcard
  obtain ⟨Y, hYS, hYcard, hYconvex⟩ :=
    six_points_contain_convex_five hScard hgpS
  rcases hHmono with ⟨c, hc⟩
  have hcolorY : color Y = c := hc Y (hYS.trans hSH) hYcard
  have hcolorYtrue : color Y = true := by simp [color, hYconvex]
  have hcTrue : c = true := hcolorY.symm.trans hcolorYtrue
  have hfive : ∀ A : Finset (Point 3), A ⊆ H → A.card = 5 → InConvexPosition A := by
    intro A hAH hAcard
    have hcolorA : color A = c := hc A hAH hAcard
    have hdecide : decide (InConvexPosition A) = true := by
      simpa [color] using hcolorA.trans hcTrue
    exact of_decide_eq_true hdecide
  have hHconvex : InConvexPosition H :=
    inConvexPosition_of_five_subsets (by omega) hfive
  obtain ⟨Z, hZH, hZcard⟩ := Finset.exists_subset_card_eq
    (show n ≤ H.card by omega)
  exact ⟨Z, hZH.trans hHX, hZcard, inConvexPosition_mono hHconvex hZH⟩

/-- Erdős--Szekeres thresholds exist in dimension three for every target cardinality. -/
theorem hasErdosSzekeresNumber_three (n : ℕ) : HasErdosSzekeresNumber 3 n :=
  ⟨uniformRamseyBound 5 (max 6 n), uniformRamseyBound_five_forcesConvexSubset_three n⟩

/-- A four-uniform Boolean coloring whose monochromatic general-position sets are convex gives
the required finite Erdős--Szekeres threshold in dimension three. -/
theorem hasErdosSzekeresNumber_three_of_monochromatic_certificate (n : ℕ)
    (color : Finset (Point 3) → Bool)
    (hcert : ∀ Y : Finset (Point 3), InGeneralPosition 3 Y →
      MonochromaticOn 4 color Y → InConvexPosition Y) :
    HasErdosSzekeresNumber 3 n := by
  refine ⟨uniformRamseyBound 4 n, ?_⟩
  intro X hXcard hgp
  obtain ⟨Y, hYX, hYcard, hYmono⟩ :=
    uniformRamseyBound_spec 4 n X hXcard color
  have hgpY : InGeneralPosition 3 Y := by
    intro S hSY hScard
    exact hgp S (hSY.trans hYX) hScard
  exact ⟨Y, hYX, hYcard, hcert Y hgpY hYmono⟩

end RamseyAssembly

end

end Erdos651
