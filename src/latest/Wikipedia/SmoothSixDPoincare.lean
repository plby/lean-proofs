import Wikipedia.SmoothSixDPoincare.TheoremA
import Wikipedia.SmoothSixDPoincare.Diffeomorphism
import Wikipedia.SmoothSixDPoincare.PuncturedRecognition
import Wikipedia.SmoothSixDPoincare.SmoothChartDisk
import Wikipedia.SmoothSixDPoincare.DiskCutout
import Wikipedia.SmoothSixDPoincare.LocalizedMorsePerturbation

/-!
# The smooth six-dimensional Poincaré theorem

Every closed smooth six-manifold homotopy equivalent to the standard six-sphere
is homeomorphic and diffeomorphic to it. The smooth conclusion concerns the
manifold's originally supplied atlas, not an atlas transported from the sphere.

`homeomorphic_sixSphere_of_homotopySixSphere` is the dimension-six specialization
of Smale's Theorem A. `diffeomorphic_sixSphere_of_homotopySixSphere` combines it
with `Wikipedia.NoExoticSixSphere` to obtain the stronger smooth conclusion.

The supporting development also retains general two-critical-point, disk-gluing,
punctured-manifold, and coordinate-disk recognition results.
-/
