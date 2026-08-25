import StackExchange.Puzzling139335.FiniteBoundaryPartition.Arcs
import Mathlib.Data.Set.Card

/-!
# Two partition intervals meet at each Jordan-loop vertex

The left endpoint map and the right endpoint map are separately injective.
Each lists every partition vertex exactly once, with the closing endpoint
identified with the initial one.  The midpoint breakpoint ensures that the
two incidences at a vertex belong to different intervals.
-/

open Set

namespace Puzzling139335

/-- For a closed loop, the left endpoint images list all partition vertices. -/
theorem image_range_partition_eq_range_left {X : Type*} (f : ℝ → X)
    {n : ℕ} (hn : 0 < n) {t : Fin (n + 1) → ℝ}
    (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1) (hclose : f 0 = f 1) :
    f '' range t = range (fun k : Fin n => f (t k.castSucc)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · exact ⟨k, rfl⟩
    · refine ⟨⟨0, hn⟩, ?_⟩
      change f (t 0) = f (t (Fin.last n))
      rw [ht0, ht1]
      exact hclose
  · rintro ⟨k, rfl⟩
    exact ⟨t k.castSucc, ⟨k.castSucc, rfl⟩, rfl⟩

/-- For a closed loop, the right endpoint images list all partition vertices. -/
theorem image_range_partition_eq_range_right {X : Type*} (f : ℝ → X)
    {n : ℕ} (hn : 0 < n) {t : Fin (n + 1) → ℝ}
    (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1) (hclose : f 0 = f 1) :
    f '' range t = range (fun k : Fin n => f (t k.succ)) := by
  have hlast : (Fin.last n : Fin (n + 1)) ≠ 0 :=
    fun h => (Nat.ne_of_gt hn) (congrArg Fin.val h)
  obtain ⟨last, hlast⟩ := Fin.exists_succ_eq_of_ne_zero hlast
  ext x
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    rcases eq_or_ne j 0 with rfl | hj
    · refine ⟨last, ?_⟩
      change f (t last.succ) = f (t 0)
      rw [hlast, ht1, ht0]
      exact hclose.symm
    · obtain ⟨k, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
      exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨t k.succ, ⟨k.succ, rfl⟩, rfl⟩

private theorem endpoint_incidence_encard_eq_two {ι X : Type*}
    {a b : ι → X} (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i, a i ≠ b i) {v : X} (hva : v ∈ range a) (hvb : v ∈ range b) :
    {i : ι | v = a i ∨ v = b i}.encard = 2 := by
  obtain ⟨i, hi⟩ := hva
  obtain ⟨j, hj⟩ := hvb
  have hij : i ≠ j := by
    intro h
    subst j
    exact hab i (hi.trans hj.symm)
  have heq : {k : ι | v = a k ∨ v = b k} = {i, j} := by
    ext k
    constructor
    · rintro (hka | hkb)
      · exact Or.inl (ha (hka.symm.trans hi.symm))
      · exact Or.inr (hb (hkb.symm.trans hj.symm))
    · rintro (rfl | rfl)
      · exact Or.inl hi.symm
      · exact Or.inr hj.symm
  rw [heq]
  exact encard_pair hij

end Puzzling139335

namespace Schoenflies

/-- Distinct consecutive intervals have distinct left endpoint images. -/
theorem IsLoop.injective_partition_left_endpoints {f : ℝ → Plane} (hf : IsLoop f)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1) :
    Function.Injective (fun k : Fin n => f (t k.castSucc)) := by
  have hmem (k : Fin n) : t k.castSucc ∈ Ico (0 : ℝ) 1 := by
    refine ⟨(Puzzling139335.partition_mem_unitInterval ht ht0 ht1 k.castSucc).1, ?_⟩
    simpa only [ht1] using ht k.castSucc_lt_last
  intro i j hij
  exact Fin.castSucc_injective n (ht.injective (hf.injOn (hmem i) (hmem j) hij))

/-- Distinct consecutive intervals have distinct right endpoint images. -/
theorem IsLoop.injective_partition_right_endpoints {f : ℝ → Plane} (hf : IsLoop f)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1) :
    Function.Injective (fun k : Fin n => f (t k.succ)) := by
  have hmem (k : Fin n) := Puzzling139335.partition_mem_unitInterval ht ht0 ht1 k.succ
  have hpos (k : Fin n) : 0 < t k.succ := by
    rw [← ht0]
    exact ht (show (0 : Fin (n + 1)) < k.succ from Nat.succ_pos _)
  intro i j hij
  rcases hf.param_eq_or (hmem i) (hmem j) hij with heq | ⟨hi0, _⟩ | ⟨_, hj0⟩
  · exact Fin.succ_injective n (ht.injective heq)
  · exact False.elim ((ne_of_gt (hpos i)) hi0)
  · exact False.elim ((ne_of_gt (hpos j)) hj0)

/-- The midpoint breakpoint prevents the two endpoint images of one
partition interval from coinciding. -/
theorem IsLoop.partition_endpoints_ne {f : ℝ → Plane} (hf : IsLoop f)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1)
    (hhalf : (1 / 2 : ℝ) ∈ range t) (k : Fin n) :
    f (t k.castSucc) ≠ f (t k.succ) := by
  intro heq
  have hlt := ht k.castSucc_lt_succ
  exact hlt.ne (hf.injOn_partition_interval ht ht0 ht1 hhalf k
    ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ heq)

/-- Exactly two consecutive partition intervals have a given partition
vertex as an endpoint, including the identified initial/final vertex. -/
theorem IsLoop.partition_vertex_incidence_encard {f : ℝ → Plane} (hf : IsLoop f)
    {n : ℕ} (hn : 0 < n) {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1)
    (hhalf : (1 / 2 : ℝ) ∈ range t) {v : Plane} (hv : v ∈ f '' range t) :
    {k : Fin n | v = f (t k.castSucc) ∨ v = f (t k.succ)}.encard = 2 := by
  apply Puzzling139335.endpoint_incidence_encard_eq_two
    (hf.injective_partition_left_endpoints ht ht0 ht1)
    (hf.injective_partition_right_endpoints ht ht0 ht1)
    (hf.partition_endpoints_ne ht ht0 ht1 hhalf)
  · rwa [← Puzzling139335.image_range_partition_eq_range_left f hn ht0 ht1 hf.closes]
  · rwa [← Puzzling139335.image_range_partition_eq_range_right f hn ht0 ht1 hf.closes]

end Schoenflies
