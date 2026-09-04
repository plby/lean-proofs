import Mathlib
import ErdosProblems.Erdos336.Basic
import ErdosProblems.Erdos336.EndpointCoreSmoothing

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Full-fibre endpoint smoothing over a finite cyclic quotient
-/

namespace Erdos336

lemma GroupRepExactly.add
    {G : Type*} [AddCommGroup G] {A : Set G} {k l : ℕ} {x y : G}
    (hx : GroupRepExactly A k x) (hy : GroupRepExactly A l y) :
    GroupRepExactly A (k + l) (x + y) := by
  obtain ⟨xs, hxslen, hxsmem, hxssum⟩ := hx
  obtain ⟨ys, hyslen, hysmem, hyssum⟩ := hy
  refine ⟨xs ++ ys, by simp [hxslen, hyslen], ?_, by simp [hxssum, hyssum]⟩
  intro z hz
  simp only [List.mem_append] at hz
  exact hz.elim (hxsmem z) (hysmem z)

lemma groupRepExactly_replicate
    {G : Type*} [AddCommGroup G] {A : Set G} {x : G}
    (hx : x ∈ A) (k : ℕ) : GroupRepExactly A k (k • x) := by
  refine ⟨List.replicate k x, by simp, ?_, by simp⟩
  intro z hz
  have hzx : z = x := (List.mem_replicate.mp hz).2
  simpa [hzx] using hx

/-- If one exact power contains every fibre above a cyclic interval of width
`M`, and the original set contains two elements whose quotient coordinates
differ by `L≤M`, then `k` endpoint summands widen the full-fibre interval by
`kL`.  Once its width is at least `m-1`, the resulting exact power is the
whole group. -/
theorem cyclic_full_fiber_endpoint_smoothing
    {G : Type*} [AddCommGroup G] {m : ℕ} (hm : 0 < m)
    (π : G →+ ZMod m) {A : Set G} {β : ZMod m}
    {p q : G} {M L t k : ℕ}
    (hp : p ∈ A) (hq : q ∈ A)
    (hstep : π q = π p + (L : ZMod m))
    (hcore : ∀ s : ℕ, s ≤ M → ∀ y : G,
      π y = β + (s : ZMod m) → GroupRepExactly A t y)
    (hwidth : m - 1 ≤ k * L + M) (hLM : L ≤ M) :
    ∀ y : G, GroupRepExactly A (t + k) y := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  intro y
  let z : ZMod m := π y - β - k • π p
  let u : ℕ := z.val
  have hu_lt : u < m := ZMod.val_lt z
  have hu_width : u ≤ k * L + M := by omega
  obtain ⟨j, s, hjk, hsM, hujs⟩ :=
    exists_endpoint_core_decomposition hLM hu_width
  let endpoint : G := (k - j) • p + j • q
  have hcastu : (u : ZMod m) = z := ZMod.natCast_zmod_val z
  have hu_cast : (u : ZMod m) = j • (L : ZMod m) + (s : ZMod m) := by
    rw [hujs]
    push_cast
    simp [add_nsmul, mul_nsmul]
  have hπendpoint : π endpoint = k • π p + j • (L : ZMod m) := by
    dsimp [endpoint]
    simp only [map_add, map_nsmul, hstep]
    rw [nsmul_add]
    have hsub : (k - j) + j = k := Nat.sub_add_cancel hjk
    rw [← add_assoc, ← add_nsmul, hsub]
  have hzEq : j • (L : ZMod m) + (s : ZMod m) =
      π y - β - k • π p := by
    rw [← hu_cast, hcastu]
  have hyEq : π y = β + k • π p +
      (j • (L : ZMod m) + (s : ZMod m)) := by
    rw [hzEq]
    abel
  have hresidue : π (y - endpoint) = β + (s : ZMod m) := by
    rw [map_sub, hπendpoint, hyEq]
    abel
  have hcoreRep := hcore s hsM (y - endpoint) hresidue
  have hpRep := groupRepExactly_replicate hp (k - j)
  have hqRep := groupRepExactly_replicate hq j
  have hendpointRep : GroupRepExactly A k endpoint := by
    have hadd := hpRep.add hqRep
    simpa [endpoint, Nat.sub_add_cancel hjk] using hadd
  have htotal := hcoreRep.add hendpointRep
  simpa using htotal

end Erdos336
