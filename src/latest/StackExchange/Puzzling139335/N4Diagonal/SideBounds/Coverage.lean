import StackExchange.Puzzling139335.N4Diagonal.Defs

/-!
# Actual side coverage outside finitely many contacts

The source of a continuous side parametrization belongs to the closed
prototype at the interval endpoints once the other repeated pieces are
excluded from its open part and the remaining piece has finite contact.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ReflectionSeparation

private theorem source_interval_of_coverage
    {P C Q R L : Set Plane} {side source : ℝ → Plane}
    (hP : IsClosed P) (hsource : Continuous source) (hinj : Function.Injective side)
    (hside : ∀ t, side t ∈ L) (hR : (R ∩ L).Finite)
    {b : ℝ} (hb : 0 < b)
    (hcover : ∀ t ∈ Ioo (0 : ℝ) b,
      side t ∈ P ∨ side t ∈ C ∨ side t ∈ Q ∨ side t ∈ R)
    (hPnot : ∀ t ∈ Ioo (0 : ℝ) b, side t ∉ P)
    (hCnot : ∀ t ∈ Ioo (0 : ℝ) b, side t ∉ C)
    (hQ : ∀ t, side t ∈ Q → source t ∈ P) :
    MapsTo source (Icc (0 : ℝ) b) P := by
  have hfinite : (side ⁻¹' (R ∩ L)).Finite := hR.preimage hinj.injOn
  have hbad : (side ⁻¹' R).Finite := hfinite.subset fun t ht => ⟨ht, hside t⟩
  apply N4Midline.mapsTo_Icc_of_finite_exceptions hsource hP hb hbad
  intro t ht htgood
  rcases hcover t ht with hp | hc | hq | hr
  · exact (hPnot t ht hp).elim
  · exact (hCnot t ht hc).elim
  · exact hQ t hq
  · exact (htgood hr).elim

namespace Model

private theorem top_not_mem (m : Model) {t : ℝ} (ht : 0 < t) :
    (!₂[t, 1] : Plane) ∉ m.P := by
  intro hp
  have hsum := (m.triangle hp).2.2
  change t + 1 ≤ 1 at hsum
  linarith

private theorem right_not_mem (m : Model) {t : ℝ} (ht : 0 < t) :
    (!₂[1, t] : Plane) ∉ m.P := by
  intro hp
  have hsum := (m.triangle hp).2.2
  change 1 + t ≤ 1 at hsum
  linarith

private theorem bottom_not_mem_reflected (m : Model) {t : ℝ} (ht : 0 < t) :
    (!₂[1 - t, 0] : Plane) ∉ antiDiagonal '' m.P := by
  rintro ⟨x, hx, heq⟩
  have hzero := congrArg (fun x : Plane => x 0) heq
  have hone := congrArg (fun x : Plane => x 1) heq
  simp only [antiDiagonal_apply_zero, antiDiagonal_apply_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hzero hone
  have hsum := (m.triangle hx).2.2
  linarith

private theorem left_not_mem_reflected (m : Model) {t : ℝ} (ht : 0 < t) :
    (!₂[0, 1 - t] : Plane) ∉ antiDiagonal '' m.P := by
  rintro ⟨x, hx, heq⟩
  have hzero := congrArg (fun x : Plane => x 0) heq
  have hone := congrArg (fun x : Plane => x 1) heq
  simp only [antiDiagonal_apply_zero, antiDiagonal_apply_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hzero hone
  have hsum := (m.triangle hx).2.2
  linarith

/-- Top coverage forces the entire corresponding source interval into the
prototype, including its endpoint; finite contacts do not leave a gap. -/
theorem top_source_interval (m : Model) {Q R : Set Plane} {source : ℝ → Plane}
    (hsource : Continuous source)
    (hcover : ∀ x ∈ unitSquare,
      x ∈ m.P ∨ x ∈ antiDiagonal '' m.P ∨ x ∈ Q ∨ x ∈ R)
    (hQ : ∀ t, (!₂[t, 1] : Plane) ∈ Q → source t ∈ m.P)
    (hR : (R ∩ {x : Plane | x 1 = 1}).Finite)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Ico (0 : ℝ) 1)
    (hmax : ∀ x ∈ m.P, x 0 = 0 → x 1 ≤ y₀) :
    MapsTo source (Icc (0 : ℝ) (1 - y₀)) m.P := by
  apply source_interval_of_coverage (C := antiDiagonal '' m.P) m.jordan.isClosed hsource
    (side := fun t => !₂[t, 1]) ?_ (fun _ => rfl) hR (by linarith [hy₀.2]) ?_ ?_ ?_ hQ
  · intro t u htu
    exact congrArg (fun x : Plane => x 0) htu
  · intro t ht
    apply hcover
    change t ∈ Icc (0 : ℝ) 1 ∧ (1 : ℝ) ∈ Icc (0 : ℝ) 1
    exact ⟨⟨ht.1.le, by linarith [ht.2, hy₀.1]⟩, by norm_num⟩
  · intro t ht
    exact m.top_not_mem ht.1
  · intro t ht
    rintro ⟨x, hx, heq⟩
    have hzero := congrArg (fun x : Plane => x 0) heq
    have hone := congrArg (fun x : Plane => x 1) heq
    simp only [antiDiagonal_apply_zero, antiDiagonal_apply_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hzero hone
    have hxzero : x 0 = 0 := by linarith
    have hxmax := hmax x hx hxzero
    linarith [ht.2]

/-- Right-side coverage gives a closed source interval up to one minus
the maximal bottom contact of the prototype. -/
theorem right_source_interval (m : Model) {Q R : Set Plane} {source : ℝ → Plane}
    (hsource : Continuous source)
    (hcover : ∀ x ∈ unitSquare,
      x ∈ m.P ∨ x ∈ antiDiagonal '' m.P ∨ x ∈ Q ∨ x ∈ R)
    (hQ : ∀ t, (!₂[1, t] : Plane) ∈ Q → source t ∈ m.P)
    (hR : (R ∩ {x : Plane | x 0 = 1}).Finite)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ico (0 : ℝ) 1)
    (hmax : ∀ x ∈ m.P, x 1 = 0 → x 0 ≤ x₀) :
    MapsTo source (Icc (0 : ℝ) (1 - x₀)) m.P := by
  apply source_interval_of_coverage (C := antiDiagonal '' m.P) m.jordan.isClosed hsource
    (side := fun t => !₂[1, t]) ?_ (fun _ => rfl) hR (by linarith [hx₀.2]) ?_ ?_ ?_ hQ
  · intro t u htu
    exact congrArg (fun x : Plane => x 1) htu
  · intro t ht
    apply hcover
    change (1 : ℝ) ∈ Icc (0 : ℝ) 1 ∧ t ∈ Icc (0 : ℝ) 1
    exact ⟨by norm_num, ⟨ht.1.le, by linarith [ht.2, hx₀.1]⟩⟩
  · intro t ht
    exact m.right_not_mem ht.1
  · intro t ht
    rintro ⟨x, hx, heq⟩
    have hzero := congrArg (fun x : Plane => x 0) heq
    have hone := congrArg (fun x : Plane => x 1) heq
    simp only [antiDiagonal_apply_zero, antiDiagonal_apply_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hzero hone
    have hxone : x 1 = 0 := by linarith
    have hxmax := hmax x hx hxone
    linarith [ht.2]

/-- Bottom coverage measured from the right corner forces a source
interval of length one minus the maximal bottom contact. -/
theorem bottom_source_interval (m : Model) {Q R : Set Plane} {source : ℝ → Plane}
    (hsource : Continuous source)
    (hcover : ∀ x ∈ unitSquare,
      x ∈ m.P ∨ x ∈ antiDiagonal '' m.P ∨ x ∈ Q ∨ x ∈ R)
    (hQ : ∀ t, (!₂[1 - t, 0] : Plane) ∈ Q → source t ∈ m.P)
    (hR : (R ∩ {x : Plane | x 1 = 0}).Finite)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ico (0 : ℝ) 1)
    (hmax : ∀ x ∈ m.P, x 1 = 0 → x 0 ≤ x₀) :
    MapsTo source (Icc (0 : ℝ) (1 - x₀)) m.P := by
  apply source_interval_of_coverage (C := antiDiagonal '' m.P) m.jordan.isClosed hsource
    (side := fun t => !₂[1 - t, 0]) ?_ (fun _ => rfl) hR
    (by linarith [hx₀.2]) ?_ ?_ ?_ hQ
  · intro t u htu
    have hzero := congrArg (fun x : Plane => x 0) htu
    change 1 - t = 1 - u at hzero
    linarith
  · intro t ht
    apply hcover
    change 1 - t ∈ Icc (0 : ℝ) 1 ∧ (0 : ℝ) ∈ Icc (0 : ℝ) 1
    exact ⟨⟨by linarith [ht.2, hx₀.1], by linarith [ht.1]⟩, by norm_num⟩
  · intro t ht hp
    have hxmax := hmax (!₂[1 - t, 0]) hp rfl
    change 1 - t ≤ x₀ at hxmax
    linarith [ht.2]
  · intro t ht
    exact m.bottom_not_mem_reflected ht.1

/-- Left coverage measured from the top corner forces the corresponding
closed source interval. -/
theorem left_source_interval (m : Model) {Q R : Set Plane} {source : ℝ → Plane}
    (hsource : Continuous source)
    (hcover : ∀ x ∈ unitSquare,
      x ∈ m.P ∨ x ∈ antiDiagonal '' m.P ∨ x ∈ Q ∨ x ∈ R)
    (hQ : ∀ t, (!₂[0, 1 - t] : Plane) ∈ Q → source t ∈ m.P)
    (hR : (R ∩ {x : Plane | x 0 = 0}).Finite)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Ico (0 : ℝ) 1)
    (hmax : ∀ x ∈ m.P, x 0 = 0 → x 1 ≤ y₀) :
    MapsTo source (Icc (0 : ℝ) (1 - y₀)) m.P := by
  apply source_interval_of_coverage (C := antiDiagonal '' m.P) m.jordan.isClosed hsource
    (side := fun t => !₂[0, 1 - t]) ?_ (fun _ => rfl) hR
    (by linarith [hy₀.2]) ?_ ?_ ?_ hQ
  · intro t u htu
    have hone := congrArg (fun x : Plane => x 1) htu
    change 1 - t = 1 - u at hone
    linarith
  · intro t ht
    apply hcover
    change (0 : ℝ) ∈ Icc (0 : ℝ) 1 ∧ 1 - t ∈ Icc (0 : ℝ) 1
    exact ⟨by norm_num, ⟨by linarith [ht.2, hy₀.1], by linarith [ht.1]⟩⟩
  · intro t ht hp
    have hxmax := hmax (!₂[0, 1 - t]) hp rfl
    change 1 - t ≤ y₀ at hxmax
    linarith [ht.2]
  · intro t ht
    exact m.left_not_mem_reflected ht.1

end Model

end Puzzling139335.N4Diagonal
