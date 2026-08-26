import Mathlib
import ErdosProblems.Erdos336.Basic

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Listwise approximation of compact sum representations by cyclic orbit points
-/

namespace Erdos336

/-- Residues whose canonical orbit points lie within `δ` of a set `E`. -/
def CyclicApproxSet
    {K : Type*} [SeminormedAddCommGroup K]
    (φ : ℤ →+ K) (N : ℕ) (E : Set K) (δ : ℝ) : Set (ZMod N) :=
  {a | ∃ e ∈ E, ‖φ (a.val : ℤ) - e‖ < δ}

private lemma approximate_list
    {K : Type*} [SeminormedAddCommGroup K]
    (φ : ℤ →+ K) {N : ℕ} {F : Set K} {A : Set (ZMod N)} {η : ℝ}
    (hη : 0 ≤ η)
    (happrox : ∀ y ∈ F, ∃ a ∈ A, ‖φ (a.val : ℤ) - y‖ ≤ η)
    (ys : List K) (hys : ∀ y ∈ ys, y ∈ F) :
    ∃ xs : List (ZMod N),
      xs.length = ys.length ∧
      (∀ a ∈ xs, a ∈ A) ∧
      ‖(xs.map (fun a => φ (a.val : ℤ))).sum - ys.sum‖ ≤
        (ys.length : ℝ) * η := by
  induction ys with
  | nil => exact ⟨[], by simp, by simp, by simp [hη]⟩
  | cons y ys ih =>
      obtain ⟨a, haA, hay⟩ := happrox y (hys y (by simp))
      have htail : ∀ z ∈ ys, z ∈ F := by
        intro z hz
        exact hys z (by simp [hz])
      obtain ⟨xs, hlen, hxmem, hxerr⟩ := ih htail
      refine ⟨a :: xs, by simp [hlen], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact haA
        · exact hxmem z hz
      · simp only [List.map_cons, List.sum_cons, List.length_cons]
        have hrearrange :
            φ (a.val : ℤ) + (xs.map (fun z => φ (z.val : ℤ))).sum -
                (y + ys.sum) =
              (φ (a.val : ℤ) - y) +
                ((xs.map (fun z => φ (z.val : ℤ))).sum - ys.sum) := by abel
        rw [hrearrange]
        calc
          ‖(φ (a.val : ℤ) - y) +
              ((xs.map (fun z => φ (z.val : ℤ))).sum - ys.sum)‖ ≤
              ‖φ (a.val : ℤ) - y‖ +
                ‖(xs.map (fun z => φ (z.val : ℤ))).sum - ys.sum‖ :=
            norm_add_le _ _
          _ ≤ η + (ys.length : ℝ) * η := add_le_add hay hxerr
          _ = (Nat.succ ys.length : ℝ) * η := by
            push_cast
            ring

/-- An exact compact-group representation can be approximated term by term
by residues, with total norm error at most length times the pointwise error. -/
theorem approximate_group_rep_by_residues
    {K : Type*} [SeminormedAddCommGroup K]
    (φ : ℤ →+ K) {N : ℕ} {F : Set K} {A : Set (ZMod N)}
    {η : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ y ∈ F, ∃ a ∈ A, ‖φ (a.val : ℤ) - y‖ ≤ η)
    {l : ℕ} {y : K} (hrep : GroupRepExactly F l y) :
    ∃ xs : List (ZMod N),
      xs.length = l ∧
      (∀ a ∈ xs, a ∈ A) ∧
      ‖(xs.map (fun a => φ (a.val : ℤ))).sum - y‖ ≤ (l : ℝ) * η := by
  obtain ⟨ys, hlen, hymem, hysum⟩ := hrep
  obtain ⟨xs, hxslen, hxmem, hxerr⟩ :=
    approximate_list φ hη happrox ys hymem
  refine ⟨xs, by simpa [hlen] using hxslen, hxmem, ?_⟩
  simpa [hlen, hysum] using hxerr

/-- Conversely, a residue representation whose individual orbit points lie
near `E` gives an exact-length list from `E` with controlled sum error. -/
theorem approximate_residue_rep_by_group
    {K : Type*} [SeminormedAddCommGroup K]
    (φ : ℤ →+ K) {N : ℕ} {A : Set (ZMod N)} {E : Set K}
    {η : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ a ∈ A, ∃ e ∈ E, ‖φ (a.val : ℤ) - e‖ ≤ η)
    {l : ℕ} {r : ZMod N} (hrep : GroupRepExactly A l r) :
    ∃ xs : List (ZMod N), ∃ es : List K,
      xs.length = l ∧
      (∀ a ∈ xs, a ∈ A) ∧
      xs.sum = r ∧
      es.length = l ∧
      (∀ e ∈ es, e ∈ E) ∧
      ‖(xs.map (fun a => φ (a.val : ℤ))).sum - es.sum‖ ≤
        (l : ℝ) * η := by
  obtain ⟨xs, hlen, hxmem, hxsum⟩ := hrep
  have hrecursive : ∀ (xs : List (ZMod N)),
      (∀ a ∈ xs, a ∈ A) →
      ∃ es : List K,
        es.length = xs.length ∧
        (∀ e ∈ es, e ∈ E) ∧
        ‖(xs.map (fun a => φ (a.val : ℤ))).sum - es.sum‖ ≤
          (xs.length : ℝ) * η := by
    intro zs hzmem
    induction zs with
    | nil => exact ⟨[], by simp, by simp, by simp [hη]⟩
    | cons a zs ih =>
        obtain ⟨e, heE, hae⟩ := happrox a (hzmem a (by simp))
        have htail : ∀ z ∈ zs, z ∈ A := by
          intro z hz
          exact hzmem z (by simp [hz])
        obtain ⟨es, hlen', hemem, herr⟩ := ih htail
        refine ⟨e :: es, by simp [hlen'], ?_, ?_⟩
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact heE
          · exact hemem z hz
        · simp only [List.map_cons, List.sum_cons, List.length_cons]
          have hrearrange :
              φ (a.val : ℤ) + (zs.map (fun z => φ (z.val : ℤ))).sum -
                  (e + es.sum) =
                (φ (a.val : ℤ) - e) +
                  ((zs.map (fun z => φ (z.val : ℤ))).sum - es.sum) := by abel
          rw [hrearrange]
          calc
            ‖(φ (a.val : ℤ) - e) +
                ((zs.map (fun z => φ (z.val : ℤ))).sum - es.sum)‖ ≤
                ‖φ (a.val : ℤ) - e‖ +
                  ‖(zs.map (fun z => φ (z.val : ℤ))).sum - es.sum‖ :=
              norm_add_le _ _
            _ ≤ η + (zs.length : ℝ) * η := add_le_add hae herr
            _ = (Nat.succ zs.length : ℝ) * η := by push_cast; ring
  obtain ⟨es, heslen, hemem, herr⟩ := hrecursive xs hxmem
  refine ⟨xs, es, hlen, hxmem, hxsum, by simpa [hlen] using heslen,
    hemem, ?_⟩
  simpa [hlen] using herr

end Erdos336
