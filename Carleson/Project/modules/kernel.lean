import Carleson.Project.modules.Haar
import Carleson.Project.modules.BinaryRepresentationSet

open Haar BinaryRepresentationSet

noncomputable section

/- ## Kernel-/
namespace Kernel

/--
Kernel function defined using Haar functions and binary representation sets.
-/
def kernel (N : ℕ) (x y : ℝ) : ℝ :=
    1 + ∑ m ∈ binaryRepresentationSet N,
      ∑ n ∈ Finset.range (2 ^ m), (haarFunctionScaled (-m) n x) * (haarFunctionScaled (-m) n y)


/--
The kernel function at `N = 0` is constant 1.
-/
theorem kernel_zero (x y : ℝ) : kernel 0 x y = 1 := by
  simp only [kernel, add_eq_left, binaryRepresentationSet_zero]
  exact rfl


/--
Kernel function for binary powers `N = 2^m`.
-/
theorem kernel_two_pow (N : ℕ) (x y : ℝ) : kernel (2^N) x y = 1 + ∑ n ∈ Finset.range (2 ^ N),
  (haarFunctionScaled (-N) n x) * (haarFunctionScaled (-N) n y) := by
  simp only [kernel, binaryforpower, Finset.sum_singleton]



end Kernel
