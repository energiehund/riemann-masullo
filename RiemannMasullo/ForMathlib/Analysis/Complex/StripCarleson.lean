module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv

/-! # Carleson's formula on a vertical strip: the Laplacian of `‖h‖²`

For a holomorphic function `h`, the second derivatives of `‖h‖²` along a horizontal and a
vertical line add up to `4 ‖h'‖²`. This is the identity `Δ ‖h‖² = 4 ‖h'‖²`, written with
one-variable derivatives, in the form used for Carleson's formula on a vertical strip.
-/

public section

open Complex Set Filter
open scoped Topology

namespace RiemannMasullo

variable {h : ℂ → ℂ} {U : Set ℂ}

/-- Along a horizontal line, `x ↦ h (z + x)` has the complex derivative of `h`. -/
private theorem hasDerivAt_horizontal (hh : DifferentiableOn ℂ h U) (hU : IsOpen U) (z : ℂ)
    {x : ℝ} (hx : z + x ∈ U) :
    HasDerivAt (fun y : ℝ ↦ h (z + y)) (deriv h (z + x)) x :=
  ((hh.differentiableAt (hU.mem_nhds hx)).hasDerivAt.comp_const_add z (x : ℂ)).comp_ofReal

/-- Along a vertical line, `y ↦ h (z + y I)` has derivative `h' · I`. -/
private theorem hasDerivAt_vertical (hh : DifferentiableOn ℂ h U) (hU : IsOpen U) (z : ℂ)
    {y : ℝ} (hy : z + y * I ∈ U) :
    HasDerivAt (fun t : ℝ ↦ h (z + t * I)) (deriv h (z + y * I) * I) y := by
  have hl : HasDerivAt (fun t : ℝ ↦ z + (t : ℂ) * I) I y := by
    simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).comp_ofReal.const_add z
  exact (hh.differentiableAt (hU.mem_nhds hy)).hasDerivAt.comp y hl

/-- The first derivative of `‖h‖²` along a horizontal line. -/
private theorem hasDerivAt_normSq_horizontal (hh : DifferentiableOn ℂ h U) (hU : IsOpen U)
    (z : ℂ) {x : ℝ} (hx : z + x ∈ U) :
    HasDerivAt (fun y : ℝ ↦ ‖h (z + y)‖ ^ 2)
      (2 * inner ℝ (h (z + x)) (deriv h (z + x))) x :=
  (hasDerivAt_horizontal hh hU z hx).norm_sq

/-- The first derivative of `‖h‖²` along a vertical line. -/
private theorem hasDerivAt_normSq_vertical (hh : DifferentiableOn ℂ h U) (hU : IsOpen U)
    (z : ℂ) {y : ℝ} (hy : z + y * I ∈ U) :
    HasDerivAt (fun t : ℝ ↦ ‖h (z + t * I)‖ ^ 2)
      (2 * inner ℝ (h (z + y * I)) (deriv h (z + y * I) * I)) y :=
  (hasDerivAt_vertical hh hU z hy).norm_sq

/-- **The Laplacian of `‖h‖²` in coordinates.** For `h` holomorphic on an open set containing
`z`, the second derivatives of `‖h‖²` along the horizontal and the vertical line through `z`
add up to `4 ‖h' (z)‖²`. -/
theorem deriv_deriv_normSq_horizontal_add_vertical (hh : DifferentiableOn ℂ h U) (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U) :
    deriv (deriv fun x : ℝ ↦ ‖h (z + x)‖ ^ 2) 0 + deriv (deriv fun y : ℝ ↦ ‖h (z + y * I)‖ ^ 2) 0 =
      4 * ‖deriv h z‖ ^ 2 := by
  have hh' : DifferentiableOn ℂ (deriv h) U := hh.deriv hU
  -- the preimages of `U` along the two lines are open and contain `0`
  have hU₁ : IsOpen {x : ℝ | z + x ∈ U} :=
    hU.preimage (continuous_const.add Complex.continuous_ofReal)
  have hU₂ : IsOpen {y : ℝ | z + y * I ∈ U} :=
    hU.preimage (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have h0₁ : (0 : ℝ) ∈ {x : ℝ | z + x ∈ U} := by simpa using hz
  have h0₂ : (0 : ℝ) ∈ {y : ℝ | z + y * I ∈ U} := by simpa using hz
  -- first derivatives near `0`
  have hd₁ : deriv (fun x : ℝ ↦ ‖h (z + x)‖ ^ 2) =ᶠ[𝓝 0]
      fun x : ℝ ↦ 2 * inner ℝ (h (z + x)) (deriv h (z + x)) := by
    filter_upwards [hU₁.mem_nhds h0₁] with x hx
    exact (hasDerivAt_normSq_horizontal hh hU z hx).deriv
  have hd₂ : deriv (fun y : ℝ ↦ ‖h (z + y * I)‖ ^ 2) =ᶠ[𝓝 0]
      fun y : ℝ ↦ 2 * inner ℝ (h (z + y * I)) (deriv h (z + y * I) * I) := by
    filter_upwards [hU₂.mem_nhds h0₂] with y hy
    exact (hasDerivAt_normSq_vertical hh hU z hy).deriv
  -- second derivatives at `0`
  have hz₁ : z + ((0 : ℝ) : ℂ) ∈ U := by simpa using hz
  have hz₂ : z + ((0 : ℝ) : ℂ) * I ∈ U := by simpa using hz
  have hs₁ := ((hasDerivAt_horizontal hh hU z hz₁).inner ℝ
    (hasDerivAt_horizontal hh' hU z hz₁)).const_mul 2
  have hs₂ := ((hasDerivAt_vertical hh hU z hz₂).inner ℝ
    ((hasDerivAt_vertical hh' hU z hz₂).mul_const I)).const_mul 2
  rw [hd₁.deriv_eq, hd₂.deriv_eq, hs₁.deriv, hs₂.deriv]
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  have hII : deriv (deriv h) z * I * I = -deriv (deriv h) z := by
    rw [mul_assoc, I_mul_I, mul_neg_one]
  rw [hII, inner_neg_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_mul,
    norm_I, mul_one]
  ring

end RiemannMasullo
