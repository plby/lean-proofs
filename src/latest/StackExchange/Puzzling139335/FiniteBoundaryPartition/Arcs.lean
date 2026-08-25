import StackExchange.Puzzling139335.FiniteBoundaryPartition
import StackExchange.Puzzling139335.FiniteBoundaryPartition.IntervalCover
import Wikipedia.SchoenfliesTheorem.ModelCurve
import Wikipedia.SchoenfliesTheorem.Subarc

/-!
# The arcs of a finite Jordan boundary partition

The midpoint breakpoint prevents any one interval from identifying the two
ends of a Jordan-loop parametrization.  Its closed image is therefore a
proper arc with the prescribed endpoints.
-/

open Set

namespace Puzzling139335

/-- An interval between consecutive breakpoints cannot contain both `0` and
`1` when the midpoint is itself a breakpoint. -/
theorem partition_interval_not_contains_endpoints {n : ℕ} {t : Fin (n + 1) → ℝ}
    (ht : StrictMono t) (hhalf : (1 / 2 : ℝ) ∈ range t) (k : Fin n) :
    ¬ (0 ∈ Icc (t k.castSucc) (t k.succ) ∧
      1 ∈ Icc (t k.castSucc) (t k.succ)) := by
  rintro ⟨hzero, hone⟩
  have hgap : (1 / 2 : ℝ) ∈ Ioo (t k.castSucc) (t k.succ) :=
    ⟨lt_of_le_of_lt hzero.1 (by norm_num), lt_of_lt_of_le (by norm_num) hone.2⟩
  exact Set.disjoint_left.mp (strictMono_consecutive_range_disjoint ht k) hgap hhalf

/-- The images of consecutive partition intervals cover the whole path. -/
theorem iUnion_partition_interval_images {X : Type*} (f : ℝ → X)
    {n : ℕ} (hn : 0 < n) {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1) :
    (⋃ k : Fin n, f '' Icc (t k.castSucc) (t k.succ)) = f '' Icc 0 1 := by
  rw [← image_iUnion, iUnion_consecutive_Icc hn ht.monotone, ht0, ht1]

end Puzzling139335

namespace Schoenflies

/-- The loop parametrization is injective on each consecutive partition interval. -/
theorem IsLoop.injOn_partition_interval {f : ℝ → Plane} (hf : IsLoop f)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1)
    (hhalf : (1 / 2 : ℝ) ∈ range t) (k : Fin n) :
    InjOn f (Icc (t k.castSucc) (t k.succ)) := by
  have ha := Puzzling139335.partition_mem_unitInterval ht ht0 ht1 k.castSucc
  have hb := Puzzling139335.partition_mem_unitInterval ht ht0 ht1 k.succ
  have hI : Icc (t k.castSucc) (t k.succ) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc ha.1 hb.2
  intro s hs u hu heq
  rcases hf.param_eq_or (hI hs) (hI hu) heq with heq | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact heq
  · exact False.elim
      (Puzzling139335.partition_interval_not_contains_endpoints ht hhalf k ⟨hs, hu⟩)
  · exact False.elim
      (Puzzling139335.partition_interval_not_contains_endpoints ht hhalf k ⟨hu, hs⟩)

/-- Each consecutive closed interval in a midpoint-containing Jordan-loop
partition is an arc between its two endpoint images. -/
theorem IsLoop.isArcBetween_partition_interval {f : ℝ → Plane} (hf : IsLoop f)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1)
    (hhalf : (1 / 2 : ℝ) ∈ range t) (k : Fin n) :
    IsArcBetween (f '' Icc (t k.castSucc) (t k.succ))
      (f (t k.castSucc)) (f (t k.succ)) := by
  have ha := Puzzling139335.partition_mem_unitInterval ht ht0 ht1 k.castSucc
  have hb := Puzzling139335.partition_mem_unitInterval ht ht0 ht1 k.succ
  have hab : t k.castSucc < t k.succ := ht k.castSucc_lt_succ
  have hinj := hf.injOn_partition_interval ht ht0 ht1 hhalf k
  have hu : uIcc (t k.castSucc) (t k.succ) = Icc (t k.castSucc) (t k.succ) :=
    uIcc_of_le hab.le
  have h := isArcBetween_subarc hf.continuousOn (hu.symm ▸ hinj) ha hb hab.ne
  simpa only [hu] using h

/-- Removing the endpoints of a partition arc gives exactly the image of the
corresponding open parameter interval. -/
theorem IsLoop.partition_interval_diff_endpoints {f : ℝ → Plane} (hf : IsLoop f)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1)
    (hhalf : (1 / 2 : ℝ) ∈ range t) (k : Fin n) :
    (f '' Icc (t k.castSucc) (t k.succ)) \ {f (t k.castSucc), f (t k.succ)} =
      f '' Ioo (t k.castSucc) (t k.succ) := by
  have hab : t k.castSucc < t k.succ := ht k.castSucc_lt_succ
  have hinj := hf.injOn_partition_interval ht ht0 ht1 hhalf k
  have hu : uIcc (t k.castSucc) (t k.succ) = Icc (t k.castSucc) (t k.succ) :=
    uIcc_of_le hab.le
  have hsubinj := injOn_subarc (hu.symm ▸ hinj) hab.ne
  calc
    (f '' Icc (t k.castSucc) (t k.succ)) \ {f (t k.castSucc), f (t k.succ)} =
        openArc (subarc f (t k.castSucc) (t k.succ)) := by
          rw [openArc_eq_diff hsubinj, subarc_image, subarc_zero, subarc_one, hu]
    _ = f '' Ioo (t k.castSucc) (t k.succ) := by
      rw [openArc_subarc hab.ne, uIoo_of_le hab.le]

/-- Distinct partition arcs can meet only at endpoints of both arcs, including
the identified first and last point of the loop. -/
theorem IsLoop.partition_interval_images_inter_subset_endpoints {f : ℝ → Plane}
    (hf : IsLoop f) {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1) {i j : Fin n} (hij : i ≠ j) :
    (f '' Icc (t i.castSucc) (t i.succ)) ∩ (f '' Icc (t j.castSucc) (t j.succ)) ⊆
      ({f (t i.castSucc), f (t i.succ)} : Set Plane) ∩
        {f (t j.castSucc), f (t j.succ)} := by
  have hmem (k : Fin (n + 1)) := Puzzling139335.partition_mem_unitInterval ht ht0 ht1 k
  have hiI : Icc (t i.castSucc) (t i.succ) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc (hmem i.castSucc).1 (hmem i.succ).2
  have hjI : Icc (t j.castSucc) (t j.succ) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc (hmem j.castSucc).1 (hmem j.succ).2
  have mem_image_pair {a b u : ℝ} (hu : u ∈ ({a, b} : Set ℝ)) :
      f u ∈ ({f a, f b} : Set Plane) := by
    simpa only [image_pair] using mem_image_of_mem f hu
  rintro x ⟨⟨s, hs, rfl⟩, ⟨u, hu, hfu⟩⟩
  rcases hf.param_eq_or (hiI hs) (hjI hu) hfu.symm with
    rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hend := Puzzling139335.consecutive_Icc_inter_subset_endpoints
      ht.monotone hij ⟨hs, hu⟩
    exact ⟨mem_image_pair hend.1, mem_image_pair hend.2⟩
  · have hai : t i.castSucc = 0 := le_antisymm hs.1 (hmem i.castSucc).1
    have hbj : t j.succ = 1 := le_antisymm (hmem j.succ).2 hu.2
    constructor
    · exact Or.inl (congrArg f hai.symm)
    · exact Or.inr (hf.closes.trans (congrArg f hbj.symm))
  · have hbi : t i.succ = 1 := le_antisymm (hmem i.succ).2 hs.2
    have haj : t j.castSucc = 0 := le_antisymm hu.1 (hmem j.castSucc).1
    constructor
    · exact Or.inr (congrArg f hbi.symm)
    · exact Or.inl (hf.closes.symm.trans (congrArg f haj.symm))

end Schoenflies
