import ErdosProblems.Erdos421.LatticeCount

/-!
# Counting a finite increasing convex point set

The sorting and uniqueness arguments here turn the chain estimate into a
bound for an unordered set of positive integral solutions.
-/

namespace Erdos421

theorem finite_point_set_bound (S : Finset (ℕ × ℕ)) (T B : ℕ)
    (hbound : ∀ p ∈ S, p.1 ≤ B ∧ p.2 ≤ B)
    (hxin : Set.InjOn Prod.fst (↑S : Set (ℕ × ℕ)))
    (hmono : ∀ p ∈ S, ∀ q ∈ S, p.1 < q.1 → p.2 < q.2)
    (htrip : ∀ p ∈ S, ∀ q ∈ S, ∀ v ∈ S, p.1 < q.1 → q.1 < v.1 →
      ((q.2 : ℝ) - p.2) / ((q.1 : ℝ) - p.1) <
        ((v.2 : ℝ) - q.2) / ((v.1 : ℝ) - q.1)) :
    T * S.card ≤ T ^ 3 + 2 * B + T := by
  classical
  cases hcard : S.card with
  | zero => simp
  | succ n =>
    let X := S.image Prod.fst
    have hXcard : X.card = n + 1 := (Finset.card_image_iff.mpr hxin).trans hcard
    let e := X.orderEmbOfFin hXcard
    have hp : ∀ i : Fin (n + 1), ∃ p ∈ S, p.1 = e i := by
      intro i
      exact Finset.mem_image.mp (X.orderEmbOfFin_mem hXcard i)
    choose p hpS hpX using hp
    let point : ℕ → ℕ × ℕ := fun i ↦ p ⟨min i n, Nat.lt_succ_of_le (min_le_right i n)⟩
    let x : ℕ → ℕ := fun i ↦ (point i).1
    let y : ℕ → ℕ := fun i ↦ (point i).2
    have hpoint : ∀ i, point i ∈ S := fun i ↦ hpS _
    have hx : ∀ i < n, x i < x (i + 1) := by
      intro i hi
      change (p _).1 < (p _).1
      rw [hpX, hpX]
      apply e.strictMono
      change min i n < min (i + 1) n
      omega
    have hy : ∀ i < n, y i < y (i + 1) := by
      intro i hi
      exact hmono (point i) (hpoint i) (point (i + 1)) (hpoint (i + 1)) (hx i hi)
    have hslopes : StrictMono (fun i : Fin n ↦
        ((y (i + 1) - y i : ℕ) : ℝ) / ((x (i + 1) - x i : ℕ) : ℝ)) := by
      cases n with
      | zero => intro i; exact Fin.elim0 i
      | succ m =>
        apply Fin.strictMono_iff_lt_succ.mpr
        intro i
        have hi : (i : ℕ) < m + 1 := by omega
        have hi1 : (i : ℕ) + 1 < m + 1 := by omega
        have h := htrip (point i) (hpoint i) (point (i + 1)) (hpoint (i + 1))
          (point (i + 1 + 1)) (hpoint (i + 1 + 1)) (hx i hi) (hx (i + 1) hi1)
        change ((y (i + 1) : ℝ) - y i) / ((x (i + 1) : ℝ) - x i) <
          ((y (i + 1 + 1) : ℝ) - y (i + 1)) / ((x (i + 1 + 1) : ℝ) - x (i + 1)) at h
        simpa only [Fin.val_castSucc, Fin.val_succ,
          Nat.cast_sub (hy i hi).le, Nat.cast_sub (hx i hi).le,
          Nat.cast_sub (hy (i + 1) hi1).le, Nat.cast_sub (hx (i + 1) hi1).le] using h
    have h := increasing_slope_chain_bound x y n T B hx hy
      (hbound (point n) (hpoint n)).1 (hbound (point n) (hpoint n)).2 hslopes
    nlinarith

end Erdos421
