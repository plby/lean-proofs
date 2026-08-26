import ErdosProblems.Erdos19.OutsidePairBudget
import ErdosProblems.Erdos19.ProjectivePairCompression

/-! # Coverage bounds for the near-projective coloring

If every edge is short, disjoint-pair compression bounds each class's coverage.
If an edge is long, the outside-pair budget bounds the entire edge count by `n`,
so every edge may instead receive a different color.
-/

namespace Erdos19

theorem projective_outside_budget_saving_arithmetic (n k t : ℕ)
    (ht : 1024 ≤ t) (hk : 64 * t ≤ k)
    (hlow : (k - 1) * (k - 1) + (k - 1) + 2 ≤ n)
    (hup : n ≤ k * k + k + 1) :
    (n - 8 * (n / t)) * (n - 8 * (n / t) - 1) <
      (n - n / t) * ((k - k / t - 1) * (k - k / t - 2)) := by
  let u := k / t
  let r := k - u
  let p := (r - 1) * (r - 2)
  let R := 8 * (n / t)
  have htpos : 0 < t := by omega
  have hu : t * u ≤ k := Nat.mul_div_le k t
  have hu4 : 4 * u ≤ k := (Nat.mul_le_mul_right u (by omega : 4 ≤ t)).trans hu
  have hku : r + u = k := by dsimp only [r]; omega
  have hr : 3 ≤ r := by omega
  have hkpred : k - 1 + 1 = k := by omega
  have hnlow : k ^ 2 + 2 ≤ n + k := by nlinarith only [hlow, hkpred]
  have hp : 0 < p := Nat.mul_pos (by omega) (by omega)
  have hn : 0 < n := by nlinarith only [hnlow, hk, ht]
  have hpoly : n ≤ p + (2 * k * u + 4 * k) := by
    have hr1 : r - 1 + 1 = r := by omega
    have hr2 : r - 2 + 2 = r := by omega
    dsimp only [p]
    nlinarith only [hup, hku, hr1, hr2, Nat.zero_le (u * u)]
  have hterm : t * (2 * k * u + 4 * k) ≤ 3 * k ^ 2 := by
    have hfirst := Nat.mul_le_mul_left (2 * k) hu
    have hsecond := Nat.mul_le_mul_left k (show 4 * t ≤ k by omega)
    nlinarith only [hfirst, hsecond]
  have hscaled : t * n ≤ t * p + 3 * k ^ 2 := by
    have h := Nat.mul_le_mul_left t hpoly
    nlinarith only [h, hterm]
  have hlarge : 4 * k ^ 2 + 8 * t ≤ 8 * n := by
    have htk : t ≤ k := by omega
    have hk4 : 4 ≤ k := by omega
    nlinarith only [hnlow, htk, hk4]
  have hfloor := Nat.lt_mul_div_succ n htpos
  have hR : 4 * k ^ 2 < t * R := by
    dsimp only [R]
    nlinarith only [hfloor, hlarge]
  have hsmall : n < p + R := by
    have hineq : t * n < t * (p + R) := by nlinarith only [hscaled, hR]
    exact Nat.lt_of_mul_lt_mul_left hineq
  have hpred : n - R - 1 < p := by omega
  have hRn : n / t ≤ R := by dsimp only [R]; omega
  have hn' : 0 < n - n / t := by
    have h := Nat.div_lt_self hn (by omega : 1 < t)
    omega
  have hbound :
      (n - R) * (n - R - 1) ≤ (n - n / t) * (n - R - 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le_sub_left hRn n)
  exact hbound.trans_lt (Nat.mul_lt_mul_of_pos_left hpred hn')

theorem projective_outside_budget_arithmetic (n k t : ℕ)
    (ht : 1024 ≤ t) (hk : 64 * t ≤ k)
    (hlow : (k - 1) * (k - 1) + (k - 1) + 2 ≤ n)
    (hup : n ≤ k * k + k + 1) :
    (n - 8 * (n / t)) * (n - 8 * (n / t) - 1) <
      n * ((k - k / t - 1) * (k - k / t - 2)) :=
  (projective_outside_budget_saving_arithmetic n k t ht hk hlow hup).trans_le
    (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

namespace SetHypergraph

variable {X : Type*} [Fintype X]

theorem exists_cover_bounded_projective_coloring_of_budget
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n r R : ℕ)
    (hvertices : Fintype.card X = n)
    (hk : 65536 ≤ projectiveScale n)
    (hr : projectiveScale n - projectiveScale n / 1024 ≤ r)
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hbudget : (n - R) * (n - R - 1) < n * ((r - 1) * (r - 2))) :
    ∃ color : H.EdgeColoring (Fin n), H.IsCoverBoundedColoring color (2 * R) := by
  classical
  by_cases hex : ∃ e : H, R ≤ e.1.ncard
  · obtain ⟨e, he⟩ := hex
    have hc := H.card_le_of_large_edge hlinear n r R hvertices hmin hbudget e he
    obtain ⟨color, hsingle⟩ := H.exists_singleton_coloring_of_card_le hc
    exact ⟨color, fun c ↦ Or.inl (hsingle c)⟩
  · have hmax (e : H) : e.1.ncard ≤ R := by
      have h := not_exists.mp hex e
      omega
    have hp := H.pairCompressible_of_fixedFraction_projectiveScale_edges hlinear n
      hvertices hk (fun e ↦ hr.trans (hmin e))
    exact hp.exists_cover_bounded_coloring R hmax

/-- With an arbitrarily small relative gap below the projective scale, the
coloring can have an arbitrarily small linear coverage bound, allowing singleton
classes for edges which exceed that bound. -/
theorem exists_cover_bounded_projective_coloring
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n t : ℕ)
    (hvertices : Fintype.card X = n)
    (ht : 1024 ≤ t) (hk : 65536 ≤ projectiveScale n)
    (hkt : 64 * t ≤ projectiveScale n)
    (hmin : ∀ e : H, projectiveScale n - projectiveScale n / t ≤ e.1.ncard) :
    ∃ color : H.EdgeColoring (Fin n),
      H.IsCoverBoundedColoring color (16 * (n / t)) := by
  have hn : 2 ≤ n := by
    by_contra hnot
    have hscale : projectiveScale n ≤ 1 :=
      Nat.find_min' (exists_projectiveScale n) (by omega)
    omega
  have hbudget := projective_outside_budget_arithmetic n (projectiveScale n) t ht hkt
    (projectiveScale_pred_sq_add_le hn) (le_projectiveScale_sq_add n)
  have hr : projectiveScale n - projectiveScale n / 1024 ≤
      projectiveScale n - projectiveScale n / t :=
    Nat.sub_le_sub_left (Nat.div_le_div_left ht (by norm_num)) _
  obtain ⟨color, hc⟩ := H.exists_cover_bounded_projective_coloring_of_budget hlinear n
    (projectiveScale n - projectiveScale n / t) (8 * (n / t)) hvertices hk hr hmin hbudget
  exact ⟨color, by simpa only [← Nat.mul_assoc] using hc⟩

end SetHypergraph

#print axioms SetHypergraph.exists_cover_bounded_projective_coloring

end Erdos19
