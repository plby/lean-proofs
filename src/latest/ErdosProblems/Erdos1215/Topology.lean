import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import ErdosProblems.Erdos1215.Geometry

/-!
# Topology of the alternating-wall labyrinth

This file proves the two topological facts needed by the polynomial separator construction:
the finite wall set is compact, and its union with the origin has preconnected complement.
-/

open Set Metric
open scoped Topology

noncomputable section

namespace Erdos1215

lemma alternatingWall_isClosed (r : ℕ → ℝ) (j : ℕ) :
    IsClosed (alternatingWall r j) := by
  unfold alternatingWall
  apply (isClosed_eq continuous_norm continuous_const).and
  split_ifs
  · exact isClosed_le Complex.continuous_re continuous_const
  · exact isClosed_le continuous_const Complex.continuous_re

lemma alternatingWall_isCompact (r : ℕ → ℝ) (j : ℕ) :
    IsCompact (alternatingWall r j) := by
  refine (isCompact_sphere (0 : ℂ) (r j)).of_isClosed_subset
    (alternatingWall_isClosed r j) ?_
  rintro z ⟨hz, _⟩
  simpa [mem_sphere] using hz

theorem alternatingWalls_isCompact (r : ℕ → ℝ) (m : ℕ) :
    IsCompact (alternatingWalls r m) := by
  unfold alternatingWalls
  exact (finite_Iic m).isCompact_biUnion fun j _hj ↦ alternatingWall_isCompact r j

theorem standardAlternatingWalls_isCompact (m : ℕ) :
    IsCompact (alternatingWalls (standardWallRadius m) m) :=
  alternatingWalls_isCompact _ _

/-! ## Radial chambers -/

/-- The union of all circles whose radii lie in `I`. -/
def radialSet (I : Set ℝ) : Set ℂ :=
  {z | ‖z‖ ∈ I}

private def radialMap (p : ℝ × ℂ) : ℂ :=
  p.1 • p.2

private lemma continuous_radialMap : Continuous radialMap := by
  exact continuous_fst.smul continuous_snd

lemma radialSet_eq_image {I : Set ℝ} (hI : I ⊆ Ioi 0) :
    radialSet I = radialMap '' (I ×ˢ sphere (0 : ℂ) 1) := by
  ext z
  constructor
  · intro hz
    have hr : 0 < ‖z‖ := hI hz
    refine ⟨(‖z‖, ‖z‖⁻¹ • z), ⟨hz, ?_⟩, ?_⟩
    · simp [hr.ne']
    · simp [radialMap, hr.ne']
  · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
    have hrpos : 0 < r := hI hr
    have hunorm : ‖u‖ = 1 := by simpa [mem_sphere] using hu
    change ‖r • u‖ ∈ I
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hunorm] using hr

lemma radialSet_isPreconnected {I : Set ℝ} (hI : I ⊆ Ioi 0)
    (hIconn : IsPreconnected I) : IsPreconnected (radialSet I) := by
  rw [radialSet_eq_image hI]
  exact (hIconn.prod (isPreconnected_sphere
    (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) (0 : ℂ) 1)).image _
      continuous_radialMap.continuousOn

lemma openAnnulus_isPreconnected {a b : ℝ} (ha : 0 ≤ a) :
    IsPreconnected {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b} := by
  change IsPreconnected (radialSet (Ioo a b))
  exact radialSet_isPreconnected (fun _ hz ↦ ha.trans_lt hz.1) isPreconnected_Ioo

lemma exterior_isPreconnected {a : ℝ} (ha : 0 ≤ a) :
    IsPreconnected {z : ℂ | a < ‖z‖} := by
  change IsPreconnected (radialSet (Ioi a))
  exact radialSet_isPreconnected (fun _ hz ↦ ha.trans_lt hz) isPreconnected_Ioi

lemma mem_closure_radialSet {I : Set ℝ} (hI : I ⊆ Ioi 0) {z : ℂ}
    (hz : ‖z‖ ∈ closure I) (hz0 : z ≠ 0) : z ∈ closure (radialSet I) := by
  let f : ℝ → ℂ := fun t ↦ (t / ‖z‖) • z
  have hmap : MapsTo f I (radialSet I) := by
    intro t ht
    have ht0 : 0 < t := hI ht
    have hn0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
    change ‖(t / ‖z‖) • z‖ ∈ I
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, abs_of_pos hn0,
      div_mul_cancel₀ _ hn0.ne'] using ht
  have hcont : Continuous f := continuous_id.div_const _ |>.smul continuous_const
  have h := map_mem_closure hcont hz hmap
  have hfz : f ‖z‖ = z := by
    simp [f, hz0]
  rwa [hfz] at h

lemma closedAnnulus_subset_closure_openAnnulus {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b ∧ z ≠ 0} ⊆
      closure {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b} := by
  intro z hz
  apply mem_closure_radialSet (I := Ioo a b) (fun _ ht ↦ ha.trans_lt ht.1) _ hz.2.2
  rw [closure_Ioo hab.ne]
  exact ⟨hz.1, hz.2.1⟩

lemma exteriorBoundary_subset_closure_exterior {a : ℝ} (ha : 0 ≤ a) :
    {z : ℂ | a ≤ ‖z‖ ∧ z ≠ 0} ⊆ closure {z : ℂ | a < ‖z‖} := by
  intro z hz
  apply mem_closure_radialSet (I := Ioi a) (fun _ ht ↦ ha.trans_lt ht) _ hz.2
  rw [closure_Ioi]
  exact hz.1

/-! ## Shell pieces in the complement -/

def standardWallComplement (m : ℕ) : Set ℂ :=
  (insert 0 (alternatingWalls (standardWallRadius m) m))ᶜ

def innerChamber (m : ℕ) : Set ℂ :=
  {z | 0 < ‖z‖ ∧ ‖z‖ < standardWallRadius m 0}

def middleChamber (m j : ℕ) : Set ℂ :=
  {z | standardWallRadius m j < ‖z‖ ∧ ‖z‖ < standardWallRadius m (j + 1)}

def outerChamber (m : ℕ) : Set ℂ :=
  {z | standardWallRadius m m < ‖z‖}

def innerPiece (m : ℕ) : Set ℂ :=
  standardWallComplement m ∩ {z | ‖z‖ ≤ standardWallRadius m 0}

def middlePiece (m j : ℕ) : Set ℂ :=
  standardWallComplement m ∩
    {z | standardWallRadius m j ≤ ‖z‖ ∧ ‖z‖ ≤ standardWallRadius m (j + 1)}

def outerPiece (m : ℕ) : Set ℂ :=
  standardWallComplement m ∩ {z | standardWallRadius m m ≤ ‖z‖}

private lemma standardRadius_mono {m i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) (hij : i ≤ j) :
    standardWallRadius m i ≤ standardWallRadius m j :=
  (standardWallRadius_strictMonoOn m).monotoneOn hi hj hij

lemma innerChamber_subset_complement (m : ℕ) :
    innerChamber m ⊆ standardWallComplement m := by
  intro z hz
  rw [standardWallComplement, mem_compl_iff]
  rintro (rfl | hwalls)
  · simpa [innerChamber] using hz.1
  · rcases mem_iUnion₂.1 hwalls with ⟨j, hj, hjwall⟩
    have hrle : standardWallRadius m 0 ≤ standardWallRadius m j :=
      standardRadius_mono (Nat.zero_le m) hj (Nat.zero_le j)
    have hnorm : ‖z‖ = standardWallRadius m j := hjwall.1
    exact (not_lt_of_ge hrle) (hnorm ▸ hz.2)

lemma middleChamber_subset_complement {m j : ℕ} (hj : j < m) :
    middleChamber m j ⊆ standardWallComplement m := by
  intro z hz
  rw [standardWallComplement, mem_compl_iff]
  rintro (rfl | hwalls)
  · have hpos := (half_lt_standardWallRadius m j)
    simp [middleChamber] at hz
    linarith
  · rcases mem_iUnion₂.1 hwalls with ⟨k, hk, hkwall⟩
    have hnorm : ‖z‖ = standardWallRadius m k := hkwall.1
    rcases le_or_gt k j with hkj | hjk
    · have hle : standardWallRadius m k ≤ standardWallRadius m j :=
        standardRadius_mono hk hj.le hkj
      exact (not_lt_of_ge hle) (hnorm ▸ hz.1)
    · have hle : standardWallRadius m (j + 1) ≤ standardWallRadius m k :=
        standardRadius_mono hj hk (by omega)
      exact (not_lt_of_ge hle) (hnorm ▸ hz.2)

lemma outerChamber_subset_complement (m : ℕ) :
    outerChamber m ⊆ standardWallComplement m := by
  intro z hz
  rw [standardWallComplement, mem_compl_iff]
  rintro (rfl | hwalls)
  · have hpos := half_lt_standardWallRadius m m
    simp [outerChamber] at hz
    linarith
  · rcases mem_iUnion₂.1 hwalls with ⟨j, hj, hjwall⟩
    have hle : standardWallRadius m j ≤ standardWallRadius m m :=
      standardRadius_mono hj (le_refl m) hj
    have hnorm : ‖z‖ = standardWallRadius m j := hjwall.1
    exact (not_lt_of_ge hle) (hnorm ▸ hz)

lemma innerPiece_isPreconnected (m : ℕ) : IsPreconnected (innerPiece m) := by
  have hch : IsPreconnected (innerChamber m) := by
    exact openAnnulus_isPreconnected (a := 0) (b := standardWallRadius m 0) (le_refl 0)
  apply hch.subset_closure
  · intro z hz
    exact ⟨innerChamber_subset_complement m hz, hz.2.le⟩
  · intro z hz
    apply closedAnnulus_subset_closure_openAnnulus (a := 0)
      (b := standardWallRadius m 0) (le_refl 0)
      (half_lt_standardWallRadius m 0 |>.trans' (by norm_num))
    exact ⟨norm_nonneg z, hz.2, by
      exact fun hzero ↦ hz.1 (mem_insert_iff.2 (Or.inl hzero))⟩

lemma middlePiece_isPreconnected {m j : ℕ} (hj : j < m) :
    IsPreconnected (middlePiece m j) := by
  have ha : 0 ≤ standardWallRadius m j := by
    linarith [half_lt_standardWallRadius m j]
  have hch : IsPreconnected (middleChamber m j) :=
    openAnnulus_isPreconnected ha
  apply hch.subset_closure
  · intro z hz
    exact ⟨middleChamber_subset_complement hj hz, hz.1.le, hz.2.le⟩
  · intro z hz
    apply closedAnnulus_subset_closure_openAnnulus
      ha
      ((standardWallRadius_strictMonoOn m) hj.le hj (by omega))
    exact ⟨hz.2.1, hz.2.2, by
      exact fun hzero ↦ hz.1 (mem_insert_iff.2 (Or.inl hzero))⟩

lemma outerPiece_isPreconnected (m : ℕ) : IsPreconnected (outerPiece m) := by
  have ha : 0 ≤ standardWallRadius m m := by
    linarith [half_lt_standardWallRadius m m]
  have hch : IsPreconnected (outerChamber m) :=
    exterior_isPreconnected ha
  apply hch.subset_closure
  · intro z hz
    refine ⟨outerChamber_subset_complement m hz, ?_⟩
    change standardWallRadius m m ≤ ‖z‖
    exact hz.le
  · intro z hz
    apply exteriorBoundary_subset_closure_exterior
      ha
    exact ⟨hz.2, by
      exact fun hzero ↦ hz.1 (mem_insert_iff.2 (Or.inl hzero))⟩

/-! ## Gate points and the finite chain of shell pieces -/

/-- A point in the open gate of wall `j`: on the positive real axis for an even wall and
on the negative real axis for an odd wall. -/
def wallGate (m j : ℕ) : ℂ :=
  if Even j then (standardWallRadius m j : ℂ) else -(standardWallRadius m j : ℂ)

@[simp] lemma norm_wallGate (m j : ℕ) :
    ‖wallGate m j‖ = standardWallRadius m j := by
  have hp : 0 < standardWallRadius m j := by
    linarith [half_lt_standardWallRadius m j]
  by_cases hj : Even j <;> simp [wallGate, hj, abs_of_pos hp]

lemma wallGate_mem_complement {m j : ℕ} (hj : j ≤ m) :
    wallGate m j ∈ standardWallComplement m := by
  rw [standardWallComplement, mem_compl_iff]
  rintro (hzero | hwalls)
  · have hp : 0 < standardWallRadius m j := by
      linarith [half_lt_standardWallRadius m j]
    have := norm_wallGate m j
    rw [hzero, norm_zero] at this
    linarith
  · rcases mem_iUnion₂.1 hwalls with ⟨k, hk, hkwall⟩
    have hrEq : standardWallRadius m k = standardWallRadius m j := by
      rw [← hkwall.1, norm_wallGate]
    have hkj : k = j :=
      (standardWallRadius_strictMonoOn m).injOn hk hj hrEq
    subst k
    have hp : 0 < standardWallRadius m j := by
      linarith [half_lt_standardWallRadius m j]
    have hineq := hkwall.2
    by_cases heven : Even j
    · simp [wallGate, heven] at hineq
      linarith
    · simp [wallGate, heven] at hineq
      linarith

lemma wallGate_mem_innerPiece (m : ℕ) : wallGate m 0 ∈ innerPiece m := by
  exact ⟨wallGate_mem_complement (Nat.zero_le m), (norm_wallGate m 0).le⟩

lemma wallGate_mem_middlePiece_left {m j : ℕ} (hj : j < m) :
    wallGate m j ∈ middlePiece m j := by
  exact ⟨wallGate_mem_complement hj.le, (norm_wallGate m j).ge,
    (norm_wallGate m j).symm ▸
      ((standardWallRadius_strictMonoOn m) hj.le hj (by omega)).le⟩

lemma wallGate_mem_middlePiece_right {m j : ℕ} (hj : j + 1 ≤ m) :
    wallGate m (j + 1) ∈ middlePiece m j := by
  have hmono := standardWallRadius_strictMonoOn m
  have hlt := hmono (show j ≤ m by omega) hj (show j < j + 1 by omega)
  exact ⟨wallGate_mem_complement hj, hlt.le.trans_eq (norm_wallGate m (j + 1)).symm,
    (norm_wallGate m (j + 1)).le⟩

lemma wallGate_mem_outerPiece (m : ℕ) : wallGate m m ∈ outerPiece m := by
  exact ⟨wallGate_mem_complement (le_refl m), (norm_wallGate m m).ge⟩

/-- The inner piece followed by the first `n` closed shell pieces. -/
def boundedPieceUnion (m : ℕ) : ℕ → Set ℂ
  | 0 => innerPiece m
  | n + 1 => boundedPieceUnion m n ∪ middlePiece m n

lemma wallGate_mem_boundedPieceUnion {m n : ℕ} (hn : n ≤ m) :
    wallGate m n ∈ boundedPieceUnion m n := by
  cases n with
  | zero => exact wallGate_mem_innerPiece m
  | succ n =>
      exact mem_union_right _ (wallGate_mem_middlePiece_right hn)

lemma boundedPieceUnion_isPreconnected {m n : ℕ} (hn : n ≤ m) :
    IsPreconnected (boundedPieceUnion m n) := by
  induction n with
  | zero => exact innerPiece_isPreconnected m
  | succ n ih =>
      rw [boundedPieceUnion]
      apply (ih (by omega)).union'
      · exact ⟨wallGate m n, wallGate_mem_boundedPieceUnion (by omega),
          wallGate_mem_middlePiece_left (by omega)⟩
      · exact middlePiece_isPreconnected (by omega)

lemma boundedPieceUnion_eq {m n : ℕ} (hn : n ≤ m) :
    boundedPieceUnion m n =
      standardWallComplement m ∩ {z | ‖z‖ ≤ standardWallRadius m n} := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [boundedPieceUnion, ih (by omega)]
      change
        (standardWallComplement m ∩ {z | ‖z‖ ≤ standardWallRadius m n}) ∪
          (standardWallComplement m ∩
            {z | standardWallRadius m n ≤ ‖z‖ ∧
              ‖z‖ ≤ standardWallRadius m (n + 1)}) =
        standardWallComplement m ∩ {z | ‖z‖ ≤ standardWallRadius m (n + 1)}
      have hmono : standardWallRadius m n ≤ standardWallRadius m (n + 1) := by
        have hs := standardWallRadius_strictMonoOn m
        exact (hs (show n ≤ m by omega) hn (show n < n + 1 by omega)).le
      ext z
      simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro (⟨hzS, hzn⟩ | ⟨hzS, _hlo, hzup⟩)
        · exact ⟨hzS, hzn.trans hmono⟩
        · exact ⟨hzS, hzup⟩
      · intro hz
        by_cases hzn : ‖z‖ ≤ standardWallRadius m n
        · exact Or.inl ⟨hz.1, hzn⟩
        · exact Or.inr ⟨hz.1, (lt_of_not_ge hzn).le, hz.2⟩

lemma standardWallComplement_eq_chain (m : ℕ) :
    standardWallComplement m = boundedPieceUnion m m ∪ outerPiece m := by
  rw [boundedPieceUnion_eq (le_refl m)]
  change standardWallComplement m =
    (standardWallComplement m ∩ {z | ‖z‖ ≤ standardWallRadius m m}) ∪
      (standardWallComplement m ∩ {z | standardWallRadius m m ≤ ‖z‖})
  ext z
  simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
  constructor
  · intro hz
    rcases le_total ‖z‖ (standardWallRadius m m) with hle | hge
    · exact Or.inl ⟨hz, hle⟩
    · exact Or.inr ⟨hz, hge⟩
  · rintro (hz | hz) <;> exact hz.1

theorem standardWallComplement_isPreconnected (m : ℕ) :
    IsPreconnected (standardWallComplement m) := by
  rw [standardWallComplement_eq_chain]
  apply (boundedPieceUnion_isPreconnected (le_refl m)).union'
  · exact ⟨wallGate m m, wallGate_mem_boundedPieceUnion (le_refl m),
      wallGate_mem_outerPiece m⟩
  · exact outerPiece_isPreconnected m

/-- The compact alternating labyrinth, together with the origin, does not disconnect the plane. -/
theorem standardAlternatingWalls_compl_isPreconnected (m : ℕ) :
    IsPreconnected (insert 0 (alternatingWalls (standardWallRadius m) m))ᶜ :=
  standardWallComplement_isPreconnected m

end Erdos1215
