import Mathlib
import ErdosProblems.Erdos336.ThickAbsorption

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Smoothing a represented core interval with cheap endpoint summands

The key finite-cyclic fibre-filling observation: a core interval already
representable with `t` original summands can be widened at unit cost per step
using two endpoint elements of the original set.
-/

namespace Erdos336

lemma ZRepExactly.add
    {A : Set ℤ} {k l : ℕ} {x y : ℤ}
    (hx : ZRepExactly A k x) (hy : ZRepExactly A l y) :
    ZRepExactly A (k + l) (x + y) := by
  obtain ⟨xs, hxslen, hxsmem, hxssum⟩ := hx
  obtain ⟨ys, hyslen, hysmem, hyssum⟩ := hy
  refine ⟨xs ++ ys, by simp [hxslen, hyslen], ?_, by simp [hxssum, hyssum]⟩
  intro z hz
  simp only [List.mem_append] at hz
  exact hz.elim (hxsmem z) (hysmem z)

lemma zRepExactly_replicate
    {A : Set ℤ} {x : ℤ} (hx : x ∈ A) (k : ℕ) :
    ZRepExactly A k ((k : ℤ) * x) := by
  refine ⟨List.replicate k x, by simp, ?_, ?_⟩
  · intro z hz
    simpa using (List.mem_replicate.mp hz).2 ▸ hx
  · simp [nsmul_eq_mul]

/-- Adding `r` independently represented copies of an interval gives the
whole `r`-fold dilate of that interval, with representation cost `r*t`. -/
theorem represented_core_iterate
    {A : Set ℤ} {a : ℤ} {M t r u : ℕ}
    (hcore : ∀ s : ℕ, s ≤ M → ZRepExactly A t (a + (s : ℤ)))
    (hu : u ≤ r * M) :
    ZRepExactly A (r * t) ((r : ℤ) * a + (u : ℤ)) := by
  induction r generalizing u with
  | zero =>
      have hu0 : u = 0 := by omega
      subst u
      exact ⟨[], by simp, by simp, by simp⟩
  | succ r ih =>
      by_cases huM : u ≤ M
      · have hleft := ih (u := 0) (by simp)
        have hright := hcore u huM
        have hadd := hleft.add hright
        convert hadd using 1
        · simp [Nat.succ_mul]
        · push_cast
          ring
      · have hMu : M ≤ u := Nat.le_of_lt (Nat.lt_of_not_ge huM)
        have hrem : u - M ≤ r * M := by
          rw [Nat.sub_le_iff_le_add]
          simpa [Nat.succ_mul, add_comm] using hu
        have hleft := ih hrem
        have hright := hcore M le_rfl
        have hadd := hleft.add hright
        convert hadd using 1
        · simp [Nat.succ_mul]
        · push_cast
          rw [Nat.cast_sub hMu]
          ring

/-- A bounded integer `u ≤ kL+M` splits as `jL+s`, where `j≤k` and `s≤M`,
provided one endpoint step is no wider than the core. -/
lemma exists_endpoint_core_decomposition
    {k L M u : ℕ} (hLM : L ≤ M) (hu : u ≤ k * L + M) :
    ∃ j s : ℕ, j ≤ k ∧ s ≤ M ∧ u = j * L + s := by
  induction k generalizing u with
  | zero =>
      exact ⟨0, u, by simp, by simpa using hu, by simp⟩
  | succ k ih =>
      by_cases huM : u ≤ M
      · exact ⟨0, u, by simp, huM, by simp⟩
      · have hLu : L ≤ u := by omega
        have hsub : u - L ≤ k * L + M := by
          rw [Nat.succ_mul] at hu
          omega
        obtain ⟨j, s, hj, hs, heq⟩ := ih hsub
        refine ⟨j + 1, s, by omega, hs, ?_⟩
        calc
          u = (u - L) + L := (Nat.sub_add_cancel hLu).symm
          _ = (j * L + s) + L := by rw [heq]
          _ = (j + 1) * L + s := by ring

/-- Suppose every point of `[a,a+M]` is representable by exactly `t` members
of `A`, and `p,p+L∈A`.  After taking `r` core blocks and `k` endpoint terms,
every point of the full interval of width `rM+kL` is representable using
exactly `rt+k` original summands.  In particular, endpoint widening costs one
summand per step, not `t` summands per step. -/
theorem endpoint_core_smoothing
    {A : Set ℤ} {a p : ℤ} {M L t r k u : ℕ}
    (hp : p ∈ A) (hq : p + (L : ℤ) ∈ A)
    (hcore : ∀ s : ℕ, s ≤ M → ZRepExactly A t (a + (s : ℤ)))
    (hLM : L ≤ r * M) (hu : u ≤ k * L + r * M) :
    ZRepExactly A (r * t + k)
      ((r : ℤ) * a + (k : ℤ) * p + (u : ℤ)) := by
  obtain ⟨j, s, hjk, hsrM, hujs⟩ :=
    exists_endpoint_core_decomposition hLM (by simpa [add_comm] using hu)
  have hcoreRep := represented_core_iterate (r := r) hcore hsrM
  have hpRep := zRepExactly_replicate hp (k - j)
  have hqRep := zRepExactly_replicate hq j
  have hsum := (hcoreRep.add hpRep).add hqRep
  convert hsum using 1
  · omega
  · push_cast at *
    rw [hujs]
    push_cast
    have hkj : (j : ℤ) ≤ (k : ℤ) := by exact_mod_cast hjk
    rw [Int.natCast_sub hjk]
    ring

end Erdos336
