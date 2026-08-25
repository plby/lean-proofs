import StackExchange.Puzzling139335.FiniteBoundaryPartition.Arcs
import StackExchange.Puzzling139335.FiniteBoundaryPartition.AnchoredLoop

/-!
# Partitions with exactly the prescribed boundary vertices

When the base point and midpoint of a Jordan-loop parametrization are already
exceptional points, the partition introduces no auxiliary vertices.  Every
vertex belongs to the exceptional set and every open arc avoids that set.
Two distinct exceptional points on a Jordan curve provide the required anchors.
-/

open Set

namespace Puzzling139335

/-- A nondegenerate closed interval image belongs to one member of a finite
closed cover when distinct cover members do not meet on its open image. -/
theorem continuousOn_Icc_subset_of_finite_closed_cover
    {X ι : Type*} [TopologicalSpace X] [Finite ι] {f : ℝ → X} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b)) (T : ι → Set X)
    (hclosed : ∀ i, IsClosed (T i)) (hcover : f '' Ioo a b ⊆ ⋃ i, T i)
    (hdis : Pairwise fun i j => Disjoint ((f '' Ioo a b) ∩ T i)
      ((f '' Ioo a b) ∩ T j)) :
    ∃ j, f '' Icc a b ⊆ T j := by
  have hconn := (isConnected_Ioo hab).image f (hf.mono Ioo_subset_Icc_self)
  obtain ⟨j, hj⟩ := exists_subset_of_finite_closed_cover hconn hclosed hcover hdis
  refine ⟨j, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxcl : x ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
  have hfxcl : f x ∈ closure (f '' Ioo a b) :=
    ((hf x hx).mono Ioo_subset_Icc_self).mem_closure_image hxcl
  exact closure_minimal hj (hclosed j) hfxcl

end Puzzling139335

namespace Schoenflies

/-- An anchored loop admits a finite partition whose vertices are all in the
prescribed exceptional set and whose arc interiors avoid that set.  The arcs
have single closed-cover labels and cover the whole curve. -/
theorem IsLoop.exists_exact_finite_closed_cover_partition {ι : Type*} [Finite ι]
    {f : ℝ → Plane} (hf : IsLoop f) (T : ι → Set Plane)
    (hclosed : ∀ i, IsClosed (T i)) (hcover : f '' Icc 0 1 ⊆ ⋃ i, T i)
    (E : Set Plane) (hE : E.Finite)
    (hoverlap : ∀ i j, i ≠ j → (f '' Icc 0 1) ∩ T i ∩ T j ⊆ E)
    (hbase : f 0 ∈ E) (hmid : f (1 / 2) ∈ E) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → ℝ,
      StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      (1 / 2 : ℝ) ∈ range t ∧
      (∀ v, f (t v) ∈ E) ∧
      (∀ k : Fin n, Disjoint (f '' Ioo (t k.castSucc) (t k.succ)) E) ∧
      (∀ k : Fin n, Disjoint
        ((f '' Icc (t k.castSucc) (t k.succ)) \ {f (t k.castSucc), f (t k.succ)}) E) ∧
      (∀ k : Fin n, ∃ j, f '' Icc (t k.castSucc) (t k.succ) ⊆ T j) ∧
      (∀ k : Fin n, IsArcBetween (f '' Icc (t k.castSucc) (t k.succ))
        (f (t k.castSucc)) (f (t k.succ))) ∧
      (⋃ k : Fin n, f '' Icc (t k.castSucc) (t k.succ)) = f '' Icc 0 1 ∧
      ∀ i j : Fin n, i ≠ j →
        (f '' Icc (t i.castSucc) (t i.succ)) ∩ (f '' Icc (t j.castSucc) (t j.succ)) ⊆
          ({f (t i.castSucc), f (t i.succ)} : Set Plane) ∩
            {f (t j.castSucc), f (t j.succ)} := by
  have hzero : (0 : ℝ) ∈ Icc 0 1 ∩ f ⁻¹' E := ⟨zero_mem_I, hbase⟩
  have hone : (1 : ℝ) ∈ Icc 0 1 ∩ f ⁻¹' E :=
    ⟨one_mem_I, show f 1 ∈ E from hf.closes ▸ hbase⟩
  have hhalf : (1 / 2 : ℝ) ∈ Icc 0 1 ∩ f ⁻¹' E := ⟨by norm_num, hmid⟩
  obtain ⟨n, hn, t, ht, ht0, ht1, hthalf, hrange⟩ :=
    Puzzling139335.exists_partition_with_exact_range
      (hf.finite_preimage_inter_unitInterval hE) inter_subset_left hzero hhalf hone
  have hvertices (v : Fin (n + 1)) : f (t v) ∈ E :=
    (show t v ∈ Icc 0 1 ∩ f ⁻¹' E from hrange ▸ mem_range_self v).2
  have hopen (k : Fin n) : Disjoint (f '' Ioo (t k.castSucc) (t k.succ)) E := by
    have hgap := Puzzling139335.strictMono_consecutive_range_disjoint ht k
    rw [hrange] at hgap
    have ha := Puzzling139335.partition_mem_unitInterval ht ht0 ht1 k.castSucc
    have hb := Puzzling139335.partition_mem_unitInterval ht ht0 ht1 k.succ
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hfx
    have hxI : x ∈ Icc (0 : ℝ) 1 :=
      ⟨ha.1.trans hx.1.le, hx.2.le.trans hb.2⟩
    exact Set.disjoint_left.mp hgap hx ⟨hxI, hfx⟩
  refine ⟨n, hn, t, ht, ht0, ht1, hthalf, hvertices, hopen, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [hf.partition_interval_diff_endpoints ht ht0 ht1 hthalf k]
    exact hopen k
  · intro k
    have ha := Puzzling139335.partition_mem_unitInterval ht ht0 ht1 k.castSucc
    have hb := Puzzling139335.partition_mem_unitInterval ht ht0 ht1 k.succ
    have hab : t k.castSucc < t k.succ := ht k.castSucc_lt_succ
    have hI : Icc (t k.castSucc) (t k.succ) ⊆ Icc (0 : ℝ) 1 :=
      Icc_subset_Icc ha.1 hb.2
    have him : f '' Ioo (t k.castSucc) (t k.succ) ⊆ f '' Icc 0 1 :=
      image_mono (Ioo_subset_Icc_self.trans hI)
    apply Puzzling139335.continuousOn_Icc_subset_of_finite_closed_cover hab
      (hf.continuousOn.mono hI) T hclosed (him.trans hcover)
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp (hopen k) hxi.1
      (hoverlap i j hij ⟨⟨him hxi.1, hxi.2⟩, hxj.2⟩)
  · exact hf.isArcBetween_partition_interval ht ht0 ht1 hthalf
  · exact Puzzling139335.iUnion_partition_interval_images f hn ht ht0 ht1
  · intro i j hij
    exact hf.partition_interval_images_inter_subset_endpoints ht ht0 ht1 hij

/-- Two distinct exceptional points on a Jordan curve suffice for a partition
with no auxiliary vertices.  Its arc interiors avoid the exceptional set. -/
theorem IsJordanCurve.exists_exact_finite_closed_cover_partition {ι : Type*} [Finite ι]
    {C : Set Plane} (hC : IsJordanCurve C) (T : ι → Set Plane)
    (hclosed : ∀ i, IsClosed (T i)) (hcover : C ⊆ ⋃ i, T i)
    (E : Set Plane) (hE : E.Finite)
    (hoverlap : ∀ i j, i ≠ j → C ∩ T i ∩ T j ⊆ E)
    (hpoints : (C ∩ E).Nontrivial) :
    ∃ f : ℝ → Plane, IsLoop f ∧ f '' Icc 0 1 = C ∧
      ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → ℝ,
        StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
        (1 / 2 : ℝ) ∈ range t ∧
        (∀ v, f (t v) ∈ E) ∧
        (∀ k : Fin n, Disjoint (f '' Ioo (t k.castSucc) (t k.succ)) E) ∧
        (∀ k : Fin n, Disjoint
          ((f '' Icc (t k.castSucc) (t k.succ)) \ {f (t k.castSucc), f (t k.succ)}) E) ∧
        (∀ k : Fin n, ∃ j, f '' Icc (t k.castSucc) (t k.succ) ⊆ T j) ∧
        (∀ k : Fin n, IsArcBetween (f '' Icc (t k.castSucc) (t k.succ))
          (f (t k.castSucc)) (f (t k.succ))) ∧
        (⋃ k : Fin n, f '' Icc (t k.castSucc) (t k.succ)) = C ∧
        ∀ i j : Fin n, i ≠ j →
          (f '' Icc (t i.castSucc) (t i.succ)) ∩ (f '' Icc (t j.castSucc) (t j.succ)) ⊆
            ({f (t i.castSucc), f (t i.succ)} : Set Plane) ∩
              {f (t j.castSucc), f (t j.succ)} := by
  obtain ⟨p, hp, q, hq, hpq⟩ := hpoints
  obtain ⟨f, hf, hfC, hf0, hfhalf⟩ :=
    Puzzling139335.jordanCurve_exists_anchored_loop hC hp.1 hq.1 hpq
  have hcover' : f '' Icc 0 1 ⊆ ⋃ i, T i := by rwa [hfC]
  have hoverlap' : ∀ i j, i ≠ j → (f '' Icc 0 1) ∩ T i ∩ T j ⊆ E := by rwa [hfC]
  have hbase : f 0 ∈ E := by simpa only [hf0] using hp.2
  have hmid : f (1 / 2) ∈ E := by simpa only [hfhalf] using hq.2
  refine ⟨f, hf, hfC, ?_⟩
  simpa only [hfC] using
    hf.exists_exact_finite_closed_cover_partition T hclosed hcover' E hE hoverlap' hbase hmid

end Schoenflies
