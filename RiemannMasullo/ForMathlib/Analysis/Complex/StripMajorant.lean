module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # A holomorphic majorant on a vertical strip

This file contains the estimates of point 3 of the argument posted on #7405 (Theorem 10.4.2.1,
p. 459), which replace Step D there.

* `re_strip_integrand_ge`: if `‖ψ'‖ ≤ Re ψ`, the integrand
  `ψ a ā + (ψ' a + ψ b) b̄` of `⟨Ψκ, κ⟩` in the area inner product
  `∬ (κ λ̄ + κ' λ̄') w` has real part at least `½ Re ψ (‖a‖² + ‖b‖²)`.
* `norm_sq_mul_add_le`: `‖φ a‖² + ‖φ' a + φ b‖² ≤ 2 (‖φ‖² + ‖φ'‖²)(‖a‖² + ‖b‖²)`.
* `stripMajorant`: the function `1 / ((α + 1)² − z²)`. On the closed strip `|Re z| ≤ α` it
  satisfies `‖Ψ'‖ ≤ Re Ψ`, `Re Ψ ≥ ((1 + α²)(α + 1)²(1 + t²))⁻¹` and `‖Ψ‖ ≤ (1 + t²)⁻¹`,
  with `t = Im z`.

Integrating the two pointwise inequalities against `w dA` gives `X ≤ 2 Re ⟨Ψκ, κ⟩` and
`‖Φκ‖² ≤ 2X` for `X = ∬ Re Ψ (|κ|² + |κ'|²) w`, once a multiple of `stripMajorant` dominates
`|Φ|² + |Φ'|²`. The exponent `M = 1` and `L = α + 1` are enough: the derivative bound holds
with `ε = 1`, and `(1 + t²)⁻¹` is summable over the zeros by the zero count.
-/

public section

open Complex

namespace RiemannMasullo

/-! ### Two pointwise inequalities -/

/-- If `‖ψ'‖ ≤ Re ψ`, then `Re (ψ a ā + (ψ' a + ψ b) b̄) ≥ ½ Re ψ (‖a‖² + ‖b‖²)`. -/
theorem re_strip_integrand_ge (ψ ψ' a b : ℂ) (h : ‖ψ'‖ ≤ ψ.re) :
    ψ.re * (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 ≤
      (ψ * a * (starRingEnd ℂ) a + (ψ' * a + ψ * b) * (starRingEnd ℂ) b).re := by
  have e1 : (ψ * a * (starRingEnd ℂ) a).re = ψ.re * ‖a‖ ^ 2 := by
    rw [mul_assoc, Complex.mul_conj, Complex.re_mul_ofReal, Complex.normSq_eq_norm_sq]
  have e2 : (ψ * b * (starRingEnd ℂ) b).re = ψ.re * ‖b‖ ^ 2 := by
    rw [mul_assoc, Complex.mul_conj, Complex.re_mul_ofReal, Complex.normSq_eq_norm_sq]
  have e3 : -(‖ψ'‖ * (‖a‖ * ‖b‖)) ≤ (ψ' * a * (starRingEnd ℂ) b).re := by
    have := Complex.abs_re_le_norm (ψ' * a * (starRingEnd ℂ) b)
    rw [norm_mul, norm_mul, Complex.norm_conj] at this
    have := neg_abs_le (ψ' * a * (starRingEnd ℂ) b).re
    nlinarith
  have hsplit : (ψ * a * (starRingEnd ℂ) a + (ψ' * a + ψ * b) * (starRingEnd ℂ) b).re =
      (ψ * a * (starRingEnd ℂ) a).re + (ψ' * a * (starRingEnd ℂ) b).re +
        (ψ * b * (starRingEnd ℂ) b).re := by
    rw [add_mul, ← add_assoc, Complex.add_re, Complex.add_re]
  rw [hsplit, e1, e2]
  have hab : ‖a‖ * ‖b‖ ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have hψ0 : 0 ≤ ψ.re := (norm_nonneg _).trans h
  have := mul_le_mul h hab (by positivity) hψ0
  nlinarith

/-- `‖φ a‖² + ‖φ' a + φ b‖² ≤ 2 (‖φ‖² + ‖φ'‖²)(‖a‖² + ‖b‖²)`. -/
theorem norm_sq_mul_add_le (φ φ' a b : ℂ) :
    ‖φ * a‖ ^ 2 + ‖φ' * a + φ * b‖ ^ 2 ≤ 2 * (‖φ‖ ^ 2 + ‖φ'‖ ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h1 : ‖φ' * a + φ * b‖ ≤ ‖φ'‖ * ‖a‖ + ‖φ‖ * ‖b‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
  have h2 : ‖φ' * a + φ * b‖ ^ 2 ≤ (‖φ'‖ * ‖a‖ + ‖φ‖ * ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [norm_mul]
  nlinarith [sq_nonneg (‖φ'‖ * ‖a‖ - ‖φ‖ * ‖b‖), sq_nonneg ‖φ‖, sq_nonneg ‖φ'‖, sq_nonneg ‖a‖,
    sq_nonneg ‖b‖, mul_nonneg (sq_nonneg ‖φ‖) (sq_nonneg ‖a‖),
    mul_nonneg (sq_nonneg ‖φ'‖) (sq_nonneg ‖b‖)]

/-! ### The majorant `1 / ((α + 1)² − z²)` -/

/-- The holomorphic majorant of the strip `|Re z| ≤ α`. -/
noncomputable def stripMajorant (α : ℝ) (z : ℂ) : ℂ := 1 / (((α + 1 : ℝ) : ℂ) ^ 2 - z ^ 2)

/-- The real and imaginary parts of `q = (α + 1)² − z²`. -/
theorem stripMajorant_q_re_im (α : ℝ) (z : ℂ) :
    ((((α + 1 : ℝ) : ℂ) ^ 2 - z ^ 2)).re = (α + 1) ^ 2 - z.re ^ 2 + z.im ^ 2 ∧
      ((((α + 1 : ℝ) : ℂ) ^ 2 - z ^ 2)).im = -(2 * z.re * z.im) := by
  constructor <;> simp [sq, Complex.mul_re, Complex.mul_im] <;> ring

/-- On the closed strip, `Re q ≥ 1 + t²`. -/
theorem stripMajorant_q_re_ge {α : ℝ} (hα : 0 ≤ α) {z : ℂ} (hz : |z.re| ≤ α) :
    1 + z.im ^ 2 ≤ ((((α + 1 : ℝ) : ℂ) ^ 2 - z ^ 2)).re := by
  rw [(stripMajorant_q_re_im α z).1]
  have : z.re ^ 2 ≤ α ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  nlinarith

/-- `q` does not vanish on the closed strip. -/
theorem stripMajorant_q_ne_zero {α : ℝ} (hα : 0 ≤ α) {z : ℂ} (hz : |z.re| ≤ α) :
    (((α + 1 : ℝ) : ℂ) ^ 2 - z ^ 2) ≠ 0 := by
  intro h
  have := stripMajorant_q_re_ge hα hz
  rw [h, Complex.zero_re] at this
  nlinarith [sq_nonneg z.im]

/-- The derivative of the majorant: `Ψ' = 2z / q²`. -/
theorem hasDerivAt_stripMajorant {α : ℝ} (hα : 0 ≤ α) {z : ℂ} (hz : |z.re| ≤ α) :
    HasDerivAt (stripMajorant α)
      (2 * z / (((α + 1 : ℝ) : ℂ) ^ 2 - z ^ 2) ^ 2) z := by
  have hq := stripMajorant_q_ne_zero hα hz
  have hp : HasDerivAt (fun y : ℂ ↦ y ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have hc : HasDerivAt (fun y : ℂ ↦ ((α + 1 : ℝ) : ℂ) ^ 2 - y ^ 2) (-(2 * z)) z :=
    _root_.HasDerivAt.const_sub _ hp
  have h := _root_.HasDerivAt.inv hc hq
  unfold stripMajorant
  simp only [one_div]
  convert h using 1
  simp

/-- **The three estimates for the majorant on the closed strip `|Re z| ≤ α`:**
`‖Ψ'‖ ≤ Re Ψ`, `Re Ψ ≥ ((1 + α²)(α + 1)²(1 + t²))⁻¹` and `‖Ψ‖ ≤ (1 + t²)⁻¹`. -/
theorem stripMajorant_bounds {α : ℝ} (hα : 0 ≤ α) {z : ℂ} (hz : |z.re| ≤ α) :
    ‖2 * z / (((α + 1 : ℝ) : ℂ) ^ 2 - z ^ 2) ^ 2‖ ≤ (stripMajorant α z).re ∧
      ((1 + α ^ 2) * (α + 1) ^ 2 * (1 + z.im ^ 2))⁻¹ ≤ (stripMajorant α z).re ∧
      ‖stripMajorant α z‖ ≤ (1 + z.im ^ 2)⁻¹ := by
  set q : ℂ := ((α + 1 : ℝ) : ℂ) ^ 2 - z ^ 2 with hq
  obtain ⟨hre, him⟩ := stripMajorant_q_re_im α z
  rw [← hq] at hre him
  have hq0 : q ≠ 0 := stripMajorant_q_ne_zero hα hz
  have hge := stripMajorant_q_re_ge hα hz
  rw [← hq] at hge
  have hnq : 0 < Complex.normSq q := Complex.normSq_pos.mpr hq0
  have hreΨ : (stripMajorant α z).re = q.re / Complex.normSq q := by
    unfold stripMajorant
    rw [← hq, one_div, Complex.inv_re]
  have hsq : Complex.normSq q = q.re ^ 2 + q.im ^ 2 := by rw [Complex.normSq_apply]; ring
  have hy : |z.im| ≤ (1 + z.im ^ 2) / 2 := by nlinarith [sq_nonneg (|z.im| - 1), sq_abs z.im]
  have hzre : |z.re| * |z.im| ≤ α * |z.im| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
  have hzre2 : z.re ^ 2 ≤ α ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  have hge2 : 2 * α + 1 + z.im ^ 2 ≤ q.re := by rw [hre]; nlinarith
  refine ⟨?_, ?_, ?_⟩
  · -- `‖2z/q²‖ = 2|z|/|q|² ≤ Re q / |q|²` since `2|z| ≤ Re q`
    rw [hreΨ, norm_div, norm_mul, Complex.norm_two, norm_pow, ← Complex.normSq_eq_norm_sq]
    rw [div_le_div_iff_of_pos_right hnq]
    have hz1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    linarith
  · -- `Re Ψ = Re q / |q|² ≥ 1 / ((1 + α²) Re q)`
    rw [hreΨ]
    have hqre : 0 < q.re := by nlinarith [sq_nonneg z.im]
    have himb : |q.im| ≤ α * q.re := by
      rw [him, abs_neg, abs_mul, abs_mul, abs_two]
      nlinarith [abs_nonneg z.re, abs_nonneg z.im]
    have hnorm : Complex.normSq q ≤ (1 + α ^ 2) * q.re ^ 2 := by
      rw [hsq]
      have : q.im ^ 2 ≤ (α * q.re) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) himb 2
      nlinarith
    have hreup : q.re ≤ (α + 1) ^ 2 * (1 + z.im ^ 2) := by
      rw [hre]; nlinarith [sq_nonneg z.re, sq_nonneg z.im, sq_nonneg (α + 1)]
    have h1 : Complex.normSq q ≤ (1 + α ^ 2) * q.re * ((α + 1) ^ 2 * (1 + z.im ^ 2)) := by
      calc Complex.normSq q ≤ (1 + α ^ 2) * q.re ^ 2 := hnorm
        _ = (1 + α ^ 2) * q.re * q.re := by ring
        _ ≤ (1 + α ^ 2) * q.re * ((α + 1) ^ 2 * (1 + z.im ^ 2)) := by gcongr
    calc ((1 + α ^ 2) * (α + 1) ^ 2 * (1 + z.im ^ 2))⁻¹
        = q.re / ((1 + α ^ 2) * q.re * ((α + 1) ^ 2 * (1 + z.im ^ 2))) := by
          field_simp
      _ ≤ q.re / Complex.normSq q := div_le_div_of_nonneg_left hqre.le hnq h1
  · -- `‖Ψ‖ = 1/|q| ≤ 1/Re q ≤ 1/(1 + t²)`
    unfold stripMajorant
    rw [← hq, norm_div, norm_one, one_div]
    apply inv_anti₀ (by positivity)
    exact hge.trans (Complex.re_le_norm q)

/-- **The majorant for a given test.** If `‖Φ‖² + ‖Φ'‖² ≤ K (1 + t²)⁻¹` on the closed strip, then
`Ψ = c · stripMajorant α` with `c = K (1 + α²)(α + 1)²` satisfies, on the closed strip,
`‖Φ‖² + ‖Φ'‖² ≤ Re Ψ`, `‖Ψ'‖ ≤ Re Ψ` and `‖Ψ‖ ≤ c (1 + t²)⁻¹`. -/
theorem stripMajorant_dominates {α K : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K) {Φ Φ' : ℂ → ℂ}
    (hΦ : ∀ z : ℂ, |z.re| ≤ α → ‖Φ z‖ ^ 2 + ‖Φ' z‖ ^ 2 ≤ K * (1 + z.im ^ 2)⁻¹) {z : ℂ}
    (hz : |z.re| ≤ α) :
    HasDerivAt (fun w ↦ ((K * (1 + α ^ 2) * (α + 1) ^ 2 : ℝ) : ℂ) * stripMajorant α w)
        (((K * (1 + α ^ 2) * (α + 1) ^ 2 : ℝ) : ℂ) *
          (2 * z / (((α + 1 : ℝ) : ℂ) ^ 2 - z ^ 2) ^ 2)) z ∧
      ‖Φ z‖ ^ 2 + ‖Φ' z‖ ^ 2 ≤ (((K * (1 + α ^ 2) * (α + 1) ^ 2 : ℝ) : ℂ) * stripMajorant α z).re ∧
      ‖((K * (1 + α ^ 2) * (α + 1) ^ 2 : ℝ) : ℂ) *
          (2 * z / (((α + 1 : ℝ) : ℂ) ^ 2 - z ^ 2) ^ 2)‖ ≤
        (((K * (1 + α ^ 2) * (α + 1) ^ 2 : ℝ) : ℂ) * stripMajorant α z).re ∧
      ‖((K * (1 + α ^ 2) * (α + 1) ^ 2 : ℝ) : ℂ) * stripMajorant α z‖ ≤
        K * (1 + α ^ 2) * (α + 1) ^ 2 * (1 + z.im ^ 2)⁻¹ := by
  set c : ℝ := K * (1 + α ^ 2) * (α + 1) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  obtain ⟨b1, b2, b3⟩ := stripMajorant_bounds hα hz
  have hre : ((c : ℂ) * stripMajorant α z).re = c * (stripMajorant α z).re := Complex.re_ofReal_mul _ _
  refine ⟨(hasDerivAt_stripMajorant hα hz).const_mul _, ?_, ?_, ?_⟩
  · rw [hre]
    have hpos : 0 < (1 + α ^ 2) * (α + 1) ^ 2 * (1 + z.im ^ 2) := by positivity
    calc ‖Φ z‖ ^ 2 + ‖Φ' z‖ ^ 2 ≤ K * (1 + z.im ^ 2)⁻¹ := hΦ z hz
      _ = c * ((1 + α ^ 2) * (α + 1) ^ 2 * (1 + z.im ^ 2))⁻¹ := by
          rw [hc]; field_simp
      _ ≤ c * (stripMajorant α z).re := mul_le_mul_of_nonneg_left b2 hc0
  · rw [hre, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left b1 hc0
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left b3 hc0

/-! ### The integrated estimates -/

section Integrated

open MeasureTheory

variable {μ : Measure ℂ} {Ψ Ψ' Φ Φ' κ κ' : ℂ → ℂ}

/-- **`X ≤ 2 Re ⟨Ψκ, κ⟩`.** With `μ` the weighted area measure, `X = ∫ Re Ψ (‖κ‖² + ‖κ'‖²) dμ` and
`⟨Ψκ, κ⟩ = ∫ (Ψ κ κ̄ + (Ψ' κ + Ψ κ') κ̄') dμ`, the bound `‖Ψ'‖ ≤ Re Ψ` gives `X ≤ 2 Re ⟨Ψκ, κ⟩`. -/
theorem integral_re_mul_le_two_re_integral (hb : ∀ᵐ z ∂μ, ‖Ψ' z‖ ≤ (Ψ z).re)
    (hX : Integrable (fun z ↦ (Ψ z).re * (‖κ z‖ ^ 2 + ‖κ' z‖ ^ 2)) μ)
    (hI : Integrable (fun z ↦ Ψ z * κ z * (starRingEnd ℂ) (κ z) +
      (Ψ' z * κ z + Ψ z * κ' z) * (starRingEnd ℂ) (κ' z)) μ) :
    ∫ z, (Ψ z).re * (‖κ z‖ ^ 2 + ‖κ' z‖ ^ 2) ∂μ ≤
      2 * (∫ z, (Ψ z * κ z * (starRingEnd ℂ) (κ z) +
        (Ψ' z * κ z + Ψ z * κ' z) * (starRingEnd ℂ) (κ' z)) ∂μ).re := by
  have h := Complex.reCLM.integral_comp_comm hI
  simp only [Complex.reCLM_apply] at h
  rw [← h, ← integral_const_mul]
  refine integral_mono_ae hX (hI.re.const_mul 2) ?_
  filter_upwards [hb] with z hz
  have := re_strip_integrand_ge (Ψ z) (Ψ' z) (κ z) (κ' z) hz
  linarith

/-- **`‖Φκ‖² ≤ 2X`.** If `‖Φ‖² + ‖Φ'‖² ≤ Re Ψ`, then
`∫ (‖Φκ‖² + ‖(Φκ)'‖²) dμ ≤ 2 ∫ Re Ψ (‖κ‖² + ‖κ'‖²) dμ`, with `(Φκ)' = Φ'κ + Φκ'`. -/
theorem integral_norm_sq_mul_le_two_integral (hd : ∀ᵐ z ∂μ, ‖Φ z‖ ^ 2 + ‖Φ' z‖ ^ 2 ≤ (Ψ z).re)
    (hX : Integrable (fun z ↦ (Ψ z).re * (‖κ z‖ ^ 2 + ‖κ' z‖ ^ 2)) μ)
    (hY : Integrable (fun z ↦ ‖Φ z * κ z‖ ^ 2 + ‖Φ' z * κ z + Φ z * κ' z‖ ^ 2) μ) :
    ∫ z, (‖Φ z * κ z‖ ^ 2 + ‖Φ' z * κ z + Φ z * κ' z‖ ^ 2) ∂μ ≤
      2 * ∫ z, (Ψ z).re * (‖κ z‖ ^ 2 + ‖κ' z‖ ^ 2) ∂μ := by
  rw [← integral_const_mul]
  refine integral_mono_ae hY (hX.const_mul 2) ?_
  filter_upwards [hd] with z hz
  have h1 := norm_sq_mul_add_le (Φ z) (Φ' z) (κ z) (κ' z)
  have h2 : 0 ≤ ‖κ z‖ ^ 2 + ‖κ' z‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hz h2]

end Integrated

end RiemannMasullo
