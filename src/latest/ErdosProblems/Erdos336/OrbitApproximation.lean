import Mathlib
import ErdosProblems.Erdos336.CompactProjection

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite initial orbit nets with a later near-return
-/

namespace Erdos336

/-- A dense cyclic orbit in a compact metric abelian group has a finite initial
`ε`-net, followed arbitrarily far out by an `ε`-return to zero.  This is the
compact approximation input needed to replace the orbit by a long finite
cycle. -/
theorem exists_initial_orbit_net_and_return
    {K : Type*} [MetricSpace K] [AddCommGroup K]
    [IsTopologicalAddGroup K] [CompactSpace K]
    (φ : ℤ →+ K) (hdense : DenseRange φ)
    {ε : ℝ} (hε : 0 < ε) (L : ℕ) :
    ∃ N : ℕ,
      L < N ∧
      dist (φ (N : ℤ)) 0 < ε ∧
      ∀ y : K, ∃ r : ℕ, r < N ∧ dist (φ (r : ℤ)) y < ε := by
  have hdenseNat : Dense (φ '' {z : ℤ | 0 ≤ z}) :=
    dense_image_int_tail φ hdense 0
  let V : ℕ → Set K := fun r => Metric.ball (φ (r : ℤ)) ε
  have hVopen : ∀ r : ℕ, IsOpen (V r) := fun r => Metric.isOpen_ball
  have hcover : (Set.univ : Set K) ⊆ ⋃ r : ℕ, V r := by
    intro y hy
    have hballOpen : IsOpen (Metric.ball y ε) := Metric.isOpen_ball
    have hballNe : (Metric.ball y ε).Nonempty :=
      ⟨y, Metric.mem_ball_self hε⟩
    obtain ⟨x, hximage, hxy⟩ :=
      hdenseNat.exists_mem_open hballOpen hballNe
    obtain ⟨z, hznonneg, rfl⟩ := hximage
    let r := z.toNat
    have hzr : (r : ℤ) = z := by
      dsimp [r]
      rw [Int.toNat_of_nonneg hznonneg]
    apply Set.mem_iUnion.mpr
    refine ⟨r, ?_⟩
    dsimp [V]
    rw [hzr]
    simpa [dist_comm] using hxy
  obtain ⟨T, hTcover⟩ :=
    CompactSpace.isCompact_univ.elim_finite_subcover V hVopen hcover
  let B : ℕ := max L (T.sum (fun x : ℕ => x) + 1)
  have hdenseTail : Dense (φ '' {z : ℤ | ((B + 1 : ℕ) : ℤ) ≤ z}) :=
    dense_image_int_tail φ hdense ((B + 1 : ℕ) : ℤ)
  have hzeroBallOpen : IsOpen (Metric.ball (0 : K) ε) := Metric.isOpen_ball
  have hzeroBallNe : (Metric.ball (0 : K) ε).Nonempty :=
    ⟨0, Metric.mem_ball_self hε⟩
  obtain ⟨x, hximage, hxball⟩ :=
    hdenseTail.exists_mem_open hzeroBallOpen hzeroBallNe
  obtain ⟨z, hzlarge, rfl⟩ := hximage
  have hznonneg : 0 ≤ z := by
    have hbase : (0 : ℤ) ≤ ((B + 1 : ℕ) : ℤ) := Int.ofNat_zero_le _
    exact hbase.trans hzlarge
  let N := z.toNat
  have hNz : (N : ℤ) = z := by
    dsimp [N]
    rw [Int.toNat_of_nonneg hznonneg]
  refine ⟨N, ?_, ?_, ?_⟩
  · have hBL : L ≤ B := Nat.le_max_left _ _
    have hBN : B < N := by
      have hle : B + 1 ≤ N := by
        rw [← Int.ofNat_le]
        rw [hNz]
        exact hzlarge
      omega
    omega
  · rw [hNz]
    exact hxball
  · intro y
    have hymem : y ∈ (Set.univ : Set K) := Set.mem_univ y
    have hycover := hTcover hymem
    simp only [Set.mem_iUnion] at hycover
    obtain ⟨r, hrT, hry⟩ := hycover
    refine ⟨r, ?_, ?_⟩
    · have hrle : r ≤ T.sum (fun x : ℕ => x) :=
        Finset.single_le_sum_of_canonicallyOrdered
          (f := fun x : ℕ => x) hrT
      have hrB : r < B := by
        have : T.sum (fun x : ℕ => x) + 1 ≤ B := Nat.le_max_right _ _
        omega
      have hBN : B < N := by
        have hle : B + 1 ≤ N := by
          rw [← Int.ofNat_le]
          rw [hNz]
          exact hzlarge
        omega
      omega
    · simpa [V, dist_comm] using hry

end Erdos336
