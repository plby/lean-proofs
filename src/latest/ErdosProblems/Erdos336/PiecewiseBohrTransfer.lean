import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A finite compact cover turns a piecewise patch into a thick sumset

This file isolates the elementary combinatorial part of a proposed
piecewise-Bohr transference argument for Erdős Problem 336.  No topology is
needed in the lemma: all topological input has already been compressed into a
finite family of shifts covering every image point.
-/

namespace Erdos336.PiecewiseBohrTransfer

/-- A subset of `ℤ` is thick if it contains a translate of every finite
pattern. -/
def ThickZ (T : Set ℤ) : Prop :=
  ∀ F : Finset ℤ, ∃ a : ℤ, ∀ x ∈ F, a + x ∈ T

/-- Add a set of integers to a finite set of shifts. -/
def AddFinite (P : Set ℤ) (S : Finset ℤ) : Set ℤ :=
  {n | ∃ p ∈ P, ∃ s ∈ S, n = p + s}

/-- If `P` contains the part of a thick set `T` lying over a patch `U`, and
finitely many shifts make the inverse image of `U` cover every integer, then
`P` plus those shifts is thick.  The map `φ` need not be a homomorphism for
this purely combinatorial step. -/
theorem thick_addFinite_of_patch_cover
    {K : Type*} {φ : ℤ → K} {U : Set K} {T P : Set ℤ} {S : Finset ℤ}
    (hT : ThickZ T)
    (hpatch : ∀ n : ℤ, φ n ∈ U → n ∈ T → n ∈ P)
    (hcover : ∀ n : ℤ, ∃ s ∈ S, φ (n - s) ∈ U) :
    ThickZ (AddFinite P S) := by
  intro F
  let Q : Finset ℤ := (F ×ˢ S).image (fun z : ℤ × ℤ => z.1 - z.2)
  obtain ⟨a, ha⟩ := hT Q
  refine ⟨a, ?_⟩
  intro x hx
  obtain ⟨s, hs, hU⟩ := hcover (a + x)
  have hxs : x - s ∈ Q := by
    apply Finset.mem_image.mpr
    exact ⟨(x, s), Finset.mem_product.mpr ⟨hx, hs⟩, rfl⟩
  have hmemT : (a + x) - s ∈ T := by
    convert ha (x - s) hxs using 1 <;> ring
  have hmemP : (a + x) - s ∈ P := hpatch ((a + x) - s) hU hmemT
  exact ⟨(a + x) - s, hmemP, s, hs, by ring⟩

/-- Exact-length additive representation in `ℤ`, repeated here so this
artifact is standalone. -/
def Rep (D : Set ℤ) (k : ℕ) (n : ℤ) : Prop :=
  ∃ xs : List ℤ,
    xs.length = k ∧ (∀ x ∈ xs, x ∈ D) ∧ xs.sum = n

/-- The exact `k`-fold sumset is thick. -/
def RepThick (D : Set ℤ) (k : ℕ) : Prop :=
  ∀ F : Finset ℤ, ∃ a : ℤ, ∀ x ∈ F, Rep D k (a + x)

/-- The preceding set-theoretic transfer preserves exact representation
lengths: if the patch `P` is contained in `qD` and every finite covering shift
is in `kD`, then `(q+k)D` is thick. -/
theorem repThick_of_patch_cover
    {K : Type*} {φ : ℤ → K} {U : Set K} {T P D : Set ℤ}
    {S : Finset ℤ} {q k : ℕ}
    (hT : ThickZ T)
    (hpatch : ∀ n : ℤ, φ n ∈ U → n ∈ T → n ∈ P)
    (hcover : ∀ n : ℤ, ∃ s ∈ S, φ (n - s) ∈ U)
    (hPrep : ∀ p ∈ P, Rep D q p)
    (hSrep : ∀ s ∈ S, Rep D k s) :
    RepThick D (q + k) := by
  have hsumThick : ThickZ (AddFinite P S) :=
    thick_addFinite_of_patch_cover hT hpatch hcover
  intro F
  obtain ⟨a, ha⟩ := hsumThick F
  refine ⟨a, ?_⟩
  intro x hx
  obtain ⟨p, hp, s, hs, hpx⟩ := ha x hx
  obtain ⟨ps, hpslen, hpsmem, hpsum⟩ := hPrep p hp
  obtain ⟨ss, hsslen, hssmem, hssum⟩ := hSrep s hs
  refine ⟨ps ++ ss, ?_, ?_, ?_⟩
  · simp [hpslen, hsslen]
  · intro y hy
    simp only [List.mem_append] at hy
    exact hy.elim (hpsmem y) (hssmem y)
  · simp [hpsum, hssum, hpx]

end Erdos336.PiecewiseBohrTransfer
