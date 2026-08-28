import Wikipedia.NoExoticSixSphere.CircleCylinderZeroDiffeomorph
import Wikipedia.NoExoticSixSphere.DiffeomorphSumClopen

/-!
# Both actual circle seams as native clopen submanifolds

The original endpoint-sum diffeomorphism identifies each original
endpoint fiber with a clopen piece of the native time-zero manifold.
These pieces inherit the time-zero atlas. The complement of the left
piece is genuinely homeomorphic to the original right endpoint fiber.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (k : ℕ) (hd : m = n + k)

def leftZeroOpen : Opens (TimeZero d) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := timeZeroAtlas d k hd
  exact DiffeomorphSumClopen.leftImage (endpointsDiffeomorph d k hd)

def rightZeroOpen : Opens (TimeZero d) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := timeZeroAtlas d k hd
  exact DiffeomorphSumClopen.rightImage (endpointsDiffeomorph d k hd)

theorem leftZeroOpen_closed : IsClosed (leftZeroOpen d k hd : Set (TimeZero d)) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := timeZeroAtlas d k hd
  exact DiffeomorphSumClopen.leftImage_closed (endpointsDiffeomorph d k hd)

theorem rightZeroOpen_closed : IsClosed (rightZeroOpen d k hd : Set (TimeZero d)) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := timeZeroAtlas d k hd
  exact DiffeomorphSumClopen.rightImage_closed (endpointsDiffeomorph d k hd)

def leftZeroDiffeomorph :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    letI := timeZeroAtlas d k hd;
    {x : Sphere m // d.leftMap x = b} ≃ₘ⟮𝓡 k, 𝓡 k⟯ leftZeroOpen d k hd := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := timeZeroAtlas d k hd
  exact DiffeomorphSumClopen.leftImageDiffeomorph (endpointsDiffeomorph d k hd)

def rightZeroDiffeomorph :
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    letI := timeZeroAtlas d k hd;
    {x : Sphere m // d.rightMap x = b} ≃ₘ⟮𝓡 k, 𝓡 k⟯ rightZeroOpen d k hd := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := timeZeroAtlas d k hd
  exact DiffeomorphSumClopen.rightImageDiffeomorph (endpointsDiffeomorph d k hd)

theorem leftZeroDiffeomorph_val (x : {x : Sphere m // d.leftMap x = b}) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    letI := timeZeroAtlas d k hd;
    (leftZeroDiffeomorph d k hd x).val = endpointsDiffeomorph d k hd (Sum.inl x) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := timeZeroAtlas d k hd
  exact DiffeomorphSumClopen.leftImageDiffeomorph_val (endpointsDiffeomorph d k hd) x

theorem rightZeroDiffeomorph_val (x : {x : Sphere m // d.rightMap x = b}) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    letI := timeZeroAtlas d k hd;
    (rightZeroDiffeomorph d k hd x).val = endpointsDiffeomorph d k hd (Sum.inr x) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := timeZeroAtlas d k hd
  exact DiffeomorphSumClopen.rightImageDiffeomorph_val (endpointsDiffeomorph d k hd) x

theorem leftZeroOpen_compl : (leftZeroOpen d k hd : Set (TimeZero d))ᶜ = rightZeroOpen d k hd := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := timeZeroAtlas d k hd
  exact DiffeomorphSumClopen.leftImage_compl (endpointsDiffeomorph d k hd)

def leftZeroComplementHomeomorph : ↥((leftZeroOpen d k hd : Set (TimeZero d))ᶜ) ≃ₜ
    {x : Sphere m // d.rightMap x = b} := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := timeZeroAtlas d k hd
  exact DiffeomorphSumClopen.leftComplementHomeomorph (endpointsDiffeomorph d k hd)

end NoExoticSixSphere.CircleCylinder
