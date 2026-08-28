import Wikipedia.HopfProblem.SheafLerayCurveDegrees
import Wikipedia.HopfProblem.SheafLerayCurveRepresentatives
import Wikipedia.HopfProblem.SheafLerayCurveScalars

/-!
# Genuine curve-type Leray edges in degrees two and three

For an actual continuous map `f : X ⟶ Y` and an abelian sheaf `F`, the
proved native short exact sequences have terms

`0 → H¹(Y,R¹f_*F) → H²(X,F) → H⁰(Y,R²f_*F) → 0`,

`0 → H¹(Y,R²f_*F) → H³(X,F) → H⁰(Y,R³f_*F) → 0`.

The degree-two theorem takes the explicit actual vanishings
`H²(R⁰)=H³(R⁰)=H²(R¹)=0`. The degree-three theorem takes
`H²(R⁰)=H³(R⁰)=H⁴(R⁰)=H²(R¹)=H³(R¹)=H²(R²)=0`.
The shared proof works in degree `n+2` under the finite condition
`Hᵖ(Y,Rᑫf_*F)=0` for `p≥2` and `p+q≤n+3`.

The proof uses the actual pushed injective resolution and the genuine
short exact sequences of its cycles and boundaries. The required cycle
and boundary Ext vanishings are proved from the displayed homology-object
vanishings; no spectral sequence, exactness, or resolution-term acyclicity
is assumed. The exact native representative formula and coefficient
naturality are retained. Original sheaf scalar endomorphisms make the
same maps complex linear, using the genuinely derived scalar actions.

These are generic conditional-vanishing results. They neither assert that
all abelian sheaves on the sphere have cohomological dimension one nor
identify any particular higher direct image. Applying them to the original
threefold requires separately proved concrete higher-direct-image data.
-/
