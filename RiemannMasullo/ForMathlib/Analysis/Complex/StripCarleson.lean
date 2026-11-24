module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.RealDeriv
public import RiemannMasullo.ForMathlib.Analysis.Complex.Blaschke

/-! # Carleson's formula on a vertical strip: the Laplacian of `‖h‖²`

For a holomorphic function `h`, the second derivatives of `‖h‖²` along a horizontal and a
vertical line add up to `4 ‖h'‖²`. This is the identity `Δ ‖h‖² = 4 ‖h'‖²`, written with
one-variable derivatives, in the form used for Carleson's formula on a vertical strip.
-/

public section

open Complex Set Filter Metric
open scoped Topology Real Interval

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

/-! ### The conformal coordinate of the strip near its boundary -/

/-- The real and imaginary parts of the exponent in `stripBlaschkeToDisk 0 k`. -/
private theorem stripExponent_re_im (k σ t : ℝ) :
    ((k : ℂ) * (I * ((σ : ℂ) + t * I - 0))).re = -(k * t) ∧
      ((k : ℂ) * (I * ((σ : ℂ) + t * I - 0))).im = k * σ := by
  constructor <;> simp [mul_comm]

/-- **The defect of the strip coordinate.** For `w = σ + t I` and `u = exp(k I w)`,
`1 − ‖T w‖² = 4 e^{−kt} cos(kσ) / (e^{−2kt} + 2 e^{−kt} cos(kσ) + 1)`. -/
theorem one_sub_sq_norm_stripBlaschkeToDisk (k σ t : ℝ)
    (hden : Real.exp (-(k * t)) ^ 2 + 2 * Real.exp (-(k * t)) * Real.cos (k * σ) + 1 ≠ 0) :
    1 - ‖stripBlaschkeToDisk 0 k ((σ : ℂ) + t * I)‖ ^ 2 =
      4 * Real.exp (-(k * t)) * Real.cos (k * σ) /
        (Real.exp (-(k * t)) ^ 2 + 2 * Real.exp (-(k * t)) * Real.cos (k * σ) + 1) := by
  obtain ⟨hre, him⟩ := stripExponent_re_im k σ t
  set z : ℂ := (k : ℂ) * (I * ((σ : ℂ) + t * I - 0)) with hz
  set A := Real.exp (-(k * t))
  set c := Real.cos (k * σ)
  set d := Real.sin (k * σ)
  have hu_re : (Complex.exp z).re = A * c := by rw [Complex.exp_re, hre, him]
  have hu_im : (Complex.exp z).im = A * d := by rw [Complex.exp_im, hre, him]
  have hcd : c ^ 2 + d ^ 2 = 1 := Real.cos_sq_add_sin_sq (k * σ)
  have hp : Complex.normSq (Complex.exp z + 1) = A ^ 2 + 2 * A * c + 1 := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, hu_re, hu_im]
    linear_combination A ^ 2 * hcd
  have hm : Complex.normSq (Complex.exp z - 1) = A ^ 2 - 2 * A * c + 1 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hu_re, hu_im]
    linear_combination A ^ 2 * hcd
  have hT : ‖stripBlaschkeToDisk 0 k ((σ : ℂ) + t * I)‖ ^ 2 =
      Complex.normSq (Complex.exp z - 1) / Complex.normSq (Complex.exp z + 1) := by
    unfold stripBlaschkeToDisk
    rw [← hz, norm_div, div_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  rw [hT, hp, hm, eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]
  ring

/-- On the closed strip (`cos(kσ) ≥ 0`), the defect `1 − ‖T w‖²` is nonnegative and at most
`2 cos(kσ) / cosh(kt)`: it vanishes on the boundary lines and decays exponentially at both
ends. -/
theorem stripBlaschkeToDisk_defect_bounds {k σ t : ℝ} (hc : 0 ≤ Real.cos (k * σ)) :
    0 ≤ 1 - ‖stripBlaschkeToDisk 0 k ((σ : ℂ) + t * I)‖ ^ 2 ∧
      1 - ‖stripBlaschkeToDisk 0 k ((σ : ℂ) + t * I)‖ ^ 2 ≤
        2 * Real.cos (k * σ) / Real.cosh (k * t) := by
  set A := Real.exp (-(k * t)) with hA
  have hA0 : 0 < A := Real.exp_pos _
  have hden₀ : 0 < A ^ 2 + 1 := by positivity
  have hden : 0 < A ^ 2 + 2 * A * Real.cos (k * σ) + 1 := by nlinarith [mul_nonneg hA0.le hc]
  rw [one_sub_sq_norm_stripBlaschkeToDisk k σ t hden.ne']
  have hcosh : Real.cosh (k * t) = (A ^ 2 + 1) / (2 * A) := by
    rw [Real.cosh_eq, hA, Real.exp_neg]
    field_simp
    ring
  refine ⟨by positivity, ?_⟩
  rw [hcosh, div_div_eq_mul_div]
  rw [div_le_div_iff₀ hden hden₀]
  nlinarith [mul_nonneg (mul_nonneg hA0.le hc) (mul_nonneg hA0.le hc), mul_nonneg hA0.le hc]

/-- On a boundary line (`cos(kσ) = 0`) the strip coordinate has modulus one. -/
theorem norm_stripBlaschkeToDisk_eq_one {k σ t : ℝ} (hc : Real.cos (k * σ) = 0) :
    ‖stripBlaschkeToDisk 0 k ((σ : ℂ) + t * I)‖ = 1 := by
  have h := (stripBlaschkeToDisk_defect_bounds (k := k) (σ := σ) (t := t) hc.ge)
  rw [hc, mul_zero, zero_div] at h
  have h2 : ‖stripBlaschkeToDisk 0 k ((σ : ℂ) + t * I)‖ ^ 2 = 1 := by linarith [h.1, h.2]
  have h0 := norm_nonneg (stripBlaschkeToDisk 0 k ((σ : ℂ) + t * I))
  nlinarith [h2]

/-- For the half-width `α` and `k = π/(2α)`, the factor `cos(kσ)` lies between `0` and
`k (α − |σ|)` on the closed strip, so the defect is at most a constant times the distance to
the boundary. -/
theorem stripCos_bounds {α σ : ℝ} (hα : 0 < α) (hσ : |σ| ≤ α) :
    0 ≤ Real.cos (π / (2 * α) * σ) ∧
      Real.cos (π / (2 * α) * σ) ≤ π / (2 * α) * (α - |σ|) := by
  have hk : 0 < π / (2 * α) := by positivity
  have habs : Real.cos (π / (2 * α) * σ) = Real.cos (π / (2 * α) * |σ|) := by
    rcases abs_choice σ with h | h <;> rw [h]
    rw [mul_neg, Real.cos_neg]
  have hle : π / (2 * α) * |σ| ≤ π / 2 := by
    calc π / (2 * α) * |σ| ≤ π / (2 * α) * α := by gcongr
      _ = π / 2 := by field_simp
  have hshift : Real.cos (π / (2 * α) * |σ|) = Real.sin (π / (2 * α) * (α - |σ|)) := by
    rw [← Real.cos_pi_div_two_sub]
    congr 1
    field_simp
    ring
  rw [habs, hshift]
  have hx : 0 ≤ π / (2 * α) * (α - |σ|) := by
    have := sub_nonneg.mpr hσ
    positivity
  refine ⟨Real.sin_nonneg_of_nonneg_of_le_pi hx ?_, Real.sin_le hx⟩
  have : π / (2 * α) * (α - |σ|) ≤ π / (2 * α) * α := by
    gcongr
    linarith [abs_nonneg σ]
  calc π / (2 * α) * (α - |σ|) ≤ π / (2 * α) * α := this
    _ = π / 2 := by field_simp
    _ ≤ π := by linarith [Real.pi_pos]

/-! ### Möbius factors of the disk and Blaschke factors of the strip -/

/-- The Möbius factor of the unit disk with zero at `a`. -/
noncomputable def diskMobius (a z : ℂ) : ℂ := (z - a) / (1 - (starRingEnd ℂ) a * z)

/-- The defect identity `|1 − ā z|² − |z − a|² = (1 − |a|²)(1 − |z|²)`. -/
theorem normSq_one_sub_conj_mul_sub_normSq_sub (a z : ℂ) :
    Complex.normSq (1 - (starRingEnd ℂ) a * z) - Complex.normSq (z - a) =
      (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- The denominator of a Möbius factor does not vanish on the closed disk. -/
theorem one_sub_conj_mul_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - (starRingEnd ℂ) a * z ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * z = 1 := (sub_eq_zero.mp h).symm
  have h2 := congrArg norm h1
  rw [norm_mul, Complex.norm_conj, norm_one] at h2
  nlinarith [norm_nonneg a, norm_nonneg z, mul_le_mul_of_nonneg_left hz (norm_nonneg a)]

/-- **The defect of a Möbius factor.** On the closed disk,
`1 − |φ_a(z)|² = (1 − |a|²)(1 − |z|²)/|1 − ā z|²`. -/
theorem one_sub_sq_norm_diskMobius {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - ‖diskMobius a z‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by
  have hd := one_sub_conj_mul_ne_zero ha hz
  have hd' : Complex.normSq (1 - (starRingEnd ℂ) a * z) ≠ 0 := (Complex.normSq_pos.mpr hd).ne'
  have hid := normSq_one_sub_conj_mul_sub_normSq_sub a z
  unfold diskMobius
  rw [norm_div, div_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  rw [eq_div_iff hd', sub_mul, div_mul_cancel₀ _ hd', one_mul]
  linarith

/-- On the closed disk a Möbius factor has modulus at most one, with defect at most
`(1 + |a|)/(1 − |a|)` times that of `z`; on the circle it has modulus one. -/
theorem diskMobius_defect_bounds {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    0 ≤ 1 - ‖diskMobius a z‖ ^ 2 ∧
      1 - ‖diskMobius a z‖ ^ 2 ≤ (1 + ‖a‖) / (1 - ‖a‖) * (1 - ‖z‖ ^ 2) := by
  have hd := one_sub_conj_mul_ne_zero ha hz
  have hdpos : 0 < ‖1 - (starRingEnd ℂ) a * z‖ := norm_pos_iff.mpr hd
  have hlow : 1 - ‖a‖ ≤ ‖1 - (starRingEnd ℂ) a * z‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((starRingEnd ℂ) a * z)
    rw [norm_one, norm_mul, Complex.norm_conj] at this
    nlinarith [norm_nonneg a, norm_nonneg z, mul_le_mul_of_nonneg_left hz (norm_nonneg a)]
  have ha0 : 0 < 1 - ‖a‖ := by linarith
  have hz2 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have ha2 : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  rw [one_sub_sq_norm_diskMobius ha hz]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have hsq : (1 - ‖a‖) ^ 2 ≤ ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by
    exact pow_le_pow_left₀ ha0.le hlow 2
  have key : (1 - ‖a‖ ^ 2) = (1 + ‖a‖) / (1 - ‖a‖) * (1 - ‖a‖) ^ 2 := by
    field_simp
    ring
  rw [key]
  have hc : 0 ≤ (1 + ‖a‖) / (1 - ‖a‖) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hc hz2)]

/-- For numbers in `[0, 1]`, `1 − ∏ x_j ≤ ∑ (1 − x_j)`. -/
theorem one_sub_prod_le_sum_one_sub {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h0 : ∀ j ∈ s, 0 ≤ x j) (h1 : ∀ j ∈ s, x j ≤ 1) :
    1 - ∏ j ∈ s, x j ≤ ∑ j ∈ s, (1 - x j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    have hxj0 := h0 j (Finset.mem_insert_self j s)
    have hxj1 := h1 j (Finset.mem_insert_self j s)
    have ih' := ih (fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi))
    have hP0 : 0 ≤ ∏ i ∈ s, x i := Finset.prod_nonneg fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
    have hP1 : ∏ i ∈ s, x i ≤ 1 := Finset.prod_le_one₀ (fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi))
    nlinarith

/-- The finite Blaschke product of the strip `{|Re w| < α}` with zeros `ρ j` (repeated by
multiplicity), through the coordinate `stripBlaschkeToDisk 0 (π/(2α))`. -/
noncomputable def stripBlaschke (α : ℝ) {n : ℕ} (ρ : Fin n → ℂ) (w : ℂ) : ℂ :=
  ∏ j, diskMobius (stripBlaschkeToDisk 0 (π / (2 * α)) (ρ j)) (stripBlaschkeToDisk 0 (π / (2 * α)) w)

/-- **Boundary behaviour of a finite strip Blaschke product.** Let the zeros lie in the open
strip. On the closed strip, `0 ≤ 1 − |B(σ + t I)|² ≤ C (α − |σ|) / cosh(π t/(2α))` with `C`
depending only on the zeros; in particular `|B| = 1` on the two boundary lines. -/
theorem stripBlaschke_defect_bounds {α : ℝ} (hα : 0 < α) {n : ℕ} (ρ : Fin n → ℂ)
    (hρ : ∀ j, |(ρ j).re| < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, |σ| ≤ α →
      0 ≤ 1 - ‖stripBlaschke α ρ ((σ : ℂ) + t * I)‖ ^ 2 ∧
        1 - ‖stripBlaschke α ρ ((σ : ℂ) + t * I)‖ ^ 2 ≤
          C * (α - |σ|) / Real.cosh (π / (2 * α) * t) := by
  set k := π / (2 * α) with hk
  have hk0 : 0 < k := by positivity
  let T := stripBlaschkeToDisk 0 k
  have ha (j : Fin n) : ‖T (ρ j)‖ < 1 := by
    have h := stripBlaschkeToDisk_mem (w₀ := 0) (w := ρ j) hk0 (by
      rw [Complex.zero_re, sub_zero, hk]
      have : (π / 2) / (π / (2 * α)) = α := by field_simp
      rw [this]; exact hρ j)
    simpa [Metric.mem_ball, dist_zero_right] using h
  let c (j : Fin n) := (1 + ‖T (ρ j)‖) / (1 - ‖T (ρ j)‖)
  have hc0 (j : Fin n) : 0 ≤ c j := by
    have := ha j
    exact div_nonneg (by positivity) (by linarith)
  refine ⟨∑ j, c j * (2 * k), Finset.sum_nonneg fun j _ ↦ mul_nonneg (hc0 j) (by positivity), ?_⟩
  intro σ t hσ
  obtain ⟨hcos0, hcosle⟩ := stripCos_bounds hα hσ
  rw [← hk] at hcos0 hcosle
  obtain ⟨hT0, hT1⟩ := stripBlaschkeToDisk_defect_bounds (k := k) (σ := σ) (t := t) hcos0
  set z := T ((σ : ℂ) + t * I)
  have hz : ‖z‖ ≤ 1 := by nlinarith [norm_nonneg z]
  have hcosh : 0 < Real.cosh (k * t) := Real.cosh_pos _
  have hfac (j : Fin n) := diskMobius_defect_bounds (ha j) hz
  set x : Fin n → ℝ := fun j ↦ ‖diskMobius (T (ρ j)) z‖ ^ 2
  have hx0 (j) : 0 ≤ x j := by positivity
  have hx1 (j) : x j ≤ 1 := by linarith [(hfac j).1]
  have hprod : ‖stripBlaschke α ρ ((σ : ℂ) + t * I)‖ ^ 2 = ∏ j, x j := by
    unfold stripBlaschke
    rw [norm_prod, ← Finset.prod_pow]
  rw [hprod]
  refine ⟨by linarith [Finset.prod_le_one₀ (s := Finset.univ) (f := x) (fun j _ ↦ hx0 j) (fun j _ ↦ hx1 j)], ?_⟩
  calc 1 - ∏ j, x j ≤ ∑ j, (1 - x j) :=
        one_sub_prod_le_sum_one_sub _ x (fun j _ ↦ hx0 j) (fun j _ ↦ hx1 j)
    _ ≤ ∑ j, c j * (2 * Real.cos (k * σ) / Real.cosh (k * t)) := by
        apply Finset.sum_le_sum
        intro j _
        exact (hfac j).2.trans (mul_le_mul_of_nonneg_left hT1 (hc0 j))
    _ ≤ ∑ j, c j * (2 * k) * (α - |σ|) / Real.cosh (k * t) := by
        apply Finset.sum_le_sum
        intro j _
        have h2 : 2 * Real.cos (k * σ) / Real.cosh (k * t) ≤ 2 * k * (α - |σ|) / Real.cosh (k * t) :=
          div_le_div_of_nonneg_right (by linarith) hcosh.le
        calc c j * (2 * Real.cos (k * σ) / Real.cosh (k * t))
            ≤ c j * (2 * k * (α - |σ|) / Real.cosh (k * t)) := mul_le_mul_of_nonneg_left h2 (hc0 j)
          _ = c j * (2 * k) * (α - |σ|) / Real.cosh (k * t) := by ring
    _ = (∑ j, c j * (2 * k)) * (α - |σ|) / Real.cosh (k * t) := by
        rw [← Finset.sum_div, ← Finset.sum_mul]

/-! ### Derivatives -/

/-- The strip coordinate is holomorphic where `exp(k I w) ≠ −1`, with derivative
`2 k I u / (u + 1)²`, `u = exp(k I w)`. -/
theorem hasDerivAt_stripBlaschkeToDisk (k : ℝ) {w : ℂ}
    (hw : Complex.exp ((k : ℂ) * (I * (w - 0))) + 1 ≠ 0) :
    HasDerivAt (stripBlaschkeToDisk 0 k)
      (2 * ((k : ℂ) * I) * Complex.exp ((k : ℂ) * (I * (w - 0))) /
        (Complex.exp ((k : ℂ) * (I * (w - 0))) + 1) ^ 2) w := by
  have hu : HasDerivAt (fun w : ℂ ↦ Complex.exp ((k : ℂ) * (I * (w - 0))))
      (Complex.exp ((k : ℂ) * (I * (w - 0))) * ((k : ℂ) * I)) w := by
    have hl : HasDerivAt (fun w : ℂ ↦ (k : ℂ) * (I * (w - 0))) ((k : ℂ) * I) w := by
      simpa [mul_comm, mul_assoc] using ((hasDerivAt_id w).sub_const 0).const_mul I |>.const_mul (k : ℂ)
    exact hl.cexp
  have h := (hu.sub_const 1).div (hu.add_const 1) hw
  unfold stripBlaschkeToDisk
  convert h using 1
  field_simp
  ring

/-- On the closed strip (`Re u ≥ 0`), `‖2 k I u / (u + 1)²‖ ≤ k`. -/
theorem norm_deriv_stripBlaschkeToDisk_le {k : ℝ} (hk : 0 ≤ k) {u : ℂ} (hu : 0 ≤ u.re) :
    ‖2 * ((k : ℂ) * I) * u / (u + 1) ^ 2‖ ≤ k := by
  have hsq : 1 + ‖u‖ ^ 2 ≤ ‖u + 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, add_zero]
    nlinarith
  have hpos : 0 < ‖u + 1‖ ^ 2 := lt_of_lt_of_le (by positivity) hsq
  rw [norm_div, norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_real, norm_I, mul_one,
    Complex.norm_two, Real.norm_of_nonneg hk, div_le_iff₀ hpos]
  nlinarith [sq_nonneg (‖u‖ - 1), norm_nonneg u]

/-- The derivative of a Möbius factor: `φ_a' (z) = (1 − |a|²)/(1 − ā z)²`. -/
theorem hasDerivAt_diskMobius {a z : ℂ} (hz : 1 - (starRingEnd ℂ) a * z ≠ 0) :
    HasDerivAt (diskMobius a) ((1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) ^ 2) z := by
  have h1 : HasDerivAt (fun x : ℂ ↦ x - a) 1 z := (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun x : ℂ ↦ 1 - (starRingEnd ℂ) a * x) (-(starRingEnd ℂ) a) z := by
    simpa using ((hasDerivAt_id z).const_mul ((starRingEnd ℂ) a)).const_sub 1
  have h := h1.div h2 hz
  unfold diskMobius
  convert h using 1
  congr 1
  ring

/-- On the closed disk, `‖φ_a'‖ ≤ (1 + |a|)/(1 − |a|)`, and `‖φ_a‖ ≤ 1`. -/
theorem diskMobius_norm_bounds {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖diskMobius a z‖ ≤ 1 ∧
      ‖(1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) ^ 2‖ ≤ (1 + ‖a‖) / (1 - ‖a‖) := by
  have h0 := (diskMobius_defect_bounds ha hz).1
  refine ⟨by nlinarith [norm_nonneg (diskMobius a z)], ?_⟩
  have hlow : 1 - ‖a‖ ≤ ‖1 - (starRingEnd ℂ) a * z‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((starRingEnd ℂ) a * z)
    rw [norm_one, norm_mul, Complex.norm_conj] at this
    nlinarith [norm_nonneg a, norm_nonneg z, mul_le_mul_of_nonneg_left hz (norm_nonneg a)]
  have ha0 : 0 < 1 - ‖a‖ := by linarith
  have hnum : ‖1 - (starRingEnd ℂ) a * a‖ = 1 - ‖a‖ ^ 2 := by
    rw [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_of_nonneg (by nlinarith [norm_nonneg a])]
  rw [norm_div, norm_pow, hnum]
  have hsq : (1 - ‖a‖) ^ 2 ≤ ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := pow_le_pow_left₀ ha0.le hlow 2
  calc (1 - ‖a‖ ^ 2) / ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 ≤ (1 - ‖a‖ ^ 2) / (1 - ‖a‖) ^ 2 :=
        div_le_div_of_nonneg_left (by nlinarith [norm_nonneg a]) (by positivity) hsq
    _ = (1 + ‖a‖) / (1 - ‖a‖) := by field_simp; ring

/-- On the open strip `|Re w| < α`, `u = exp(k I w)` with `k = π/(2α)` has positive real part. -/
theorem stripExp_re_pos {α : ℝ} (hα : 0 < α) {w : ℂ} (hw : |w.re| < α) :
    0 < (Complex.exp (((π / (2 * α) : ℝ) : ℂ) * (I * (w - 0)))).re := by
  rw [Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have him : (((π / (2 * α) : ℝ) : ℂ) * (I * (w - 0))).im = π / (2 * α) * w.re := by
    rw [sub_zero, Complex.im_ofReal_mul, Complex.I_mul_im]
  rw [him]
  have hk : 0 < π / (2 * α) := by positivity
  have h1 : π / (2 * α) * |w.re| < π / 2 := by
    calc π / (2 * α) * |w.re| < π / (2 * α) * α := by gcongr
      _ = π / 2 := by field_simp
  constructor
  · nlinarith [neg_abs_le w.re, mul_le_mul_of_nonneg_left (neg_abs_le w.re) hk.le]
  · nlinarith [le_abs_self w.re, mul_le_mul_of_nonneg_left (le_abs_self w.re) hk.le]

/-- **A finite strip Blaschke product is holomorphic on the open strip, with bounded
derivative.** -/
theorem stripBlaschke_deriv_bound {α : ℝ} (hα : 0 < α) {n : ℕ} (ρ : Fin n → ℂ)
    (hρ : ∀ j, |(ρ j).re| < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, |w.re| < α →
      DifferentiableAt ℂ (stripBlaschke α ρ) w ∧ ‖deriv (stripBlaschke α ρ) w‖ ≤ C := by
  set k := π / (2 * α) with hk
  have hk0 : 0 < k := by positivity
  let T := stripBlaschkeToDisk 0 k
  have hmem {v : ℂ} (hv : |v.re| < α) : ‖T v‖ < 1 := by
    have h := stripBlaschkeToDisk_mem (w₀ := 0) (w := v) hk0 (by
      rw [Complex.zero_re, sub_zero, hk]
      have : (π / 2) / (π / (2 * α)) = α := by field_simp
      rw [this]; exact hv)
    simpa [Metric.mem_ball, dist_zero_right] using h
  let a (j : Fin n) := T (ρ j)
  let c (j : Fin n) := (1 + ‖a j‖) / (1 - ‖a j‖)
  have hc0 (j : Fin n) : 0 ≤ c j := div_nonneg (by positivity) (by linarith [hmem (hρ j)])
  refine ⟨∑ j, c j * k, Finset.sum_nonneg fun j _ ↦ mul_nonneg (hc0 j) hk0.le, ?_⟩
  intro w hw
  set u := Complex.exp ((k : ℂ) * (I * (w - 0)))
  have hu : 0 < u.re := stripExp_re_pos hα hw
  have hu1 : u + 1 ≠ 0 := fun h ↦ by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hTw : ‖T w‖ ≤ 1 := (hmem hw).le
  have hden (j : Fin n) : 1 - (starRingEnd ℂ) (a j) * T w ≠ 0 :=
    one_sub_conj_mul_ne_zero (hmem (hρ j)) hTw
  have hT := hasDerivAt_stripBlaschkeToDisk k hu1
  have hf (j : Fin n) := (hasDerivAt_diskMobius (hden j)).comp w hT
  have hB := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun j _ ↦ hf j)
  have heq : (fun w ↦ ∏ j ∈ Finset.univ, (diskMobius (a j) ∘ T) w) = stripBlaschke α ρ := by
    funext v; rfl
  rw [heq] at hB
  refine ⟨hB.differentiableAt, ?_⟩
  rw [hB.deriv]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [norm_smul]
  have hprod : ‖∏ j ∈ Finset.univ.erase i, (diskMobius (a j) ∘ T) w‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
      (fun j _ ↦ (diskMobius_norm_bounds (hmem (hρ j)) hTw).1)
  have hderiv : ‖(1 - (starRingEnd ℂ) (a i) * a i) / (1 - (starRingEnd ℂ) (a i) * T w) ^ 2 *
      (2 * ((k : ℂ) * I) * u / (u + 1) ^ 2)‖ ≤ c i * k := by
    rw [norm_mul]
    exact mul_le_mul (diskMobius_norm_bounds (hmem (hρ i)) hTw).2
      (norm_deriv_stripBlaschkeToDisk_le hk0.le hu.le) (norm_nonneg _) (hc0 i)
  calc ‖∏ j ∈ Finset.univ.erase i, (diskMobius (a j) ∘ T) w‖ * ‖_‖ ≤ 1 * (c i * k) :=
        mul_le_mul hprod hderiv (norm_nonneg _) zero_le_one
    _ = c i * k := one_mul _

/-! ### Integration by parts against the weight `(α − σ)^{1−s}` -/

/-- The weight `(α − x)^{1−s}` has derivative `−(1 − s)(α − x)^{−s}` for `x < α`. -/
theorem hasDerivAt_stripWeight {α s x : ℝ} (hx : x < α) :
    HasDerivAt (fun y : ℝ ↦ (α - y) ^ (1 - s)) (-((1 - s) * (α - x) ^ (-s))) x := by
  have h := ((hasDerivAt_id' x).const_sub α).rpow_const (p := 1 - s) (Or.inl (by linarith))
  convert h using 1
  rw [show (1 - s - 1) = -s by ring]
  ring

/-- The derivative `−(1 − s)(α − x)^{−s}` has derivative `−s(1 − s)(α − x)^{−s−1}` for `x < α`. -/
theorem hasDerivAt_stripWeight' {α s x : ℝ} (hx : x < α) :
    HasDerivAt (fun y : ℝ ↦ -((1 - s) * (α - y) ^ (-s))) (-(s * (1 - s) * (α - x) ^ (-s - 1))) x := by
  have h := (((hasDerivAt_id' x).const_sub α).rpow_const (p := -s)
    (Or.inl (by linarith))).const_mul (-(1 - s))
  convert h using 1
  · funext y
    ring
  · ring

/-- **Integration by parts twice on `[0, b]`, `b < α`.** -/
theorem stripWeight_ibp_finite {α s b : ℝ} (hb0 : 0 ≤ b) (hbα : b < α) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc 0 b, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Icc 0 b, HasDerivAt f' (f'' x) x)
    (hc'' : ContinuousOn f'' (Icc 0 b)) :
    ∫ x in (0 : ℝ)..b, f'' x * (α - x) ^ (1 - s) =
      f' b * (α - b) ^ (1 - s) - f' 0 * α ^ (1 - s)
        - (f b * (-((1 - s) * (α - b) ^ (-s))) - f 0 * (-((1 - s) * α ^ (-s))))
        + ∫ x in (0 : ℝ)..b, f x * (-(s * (1 - s) * (α - x) ^ (-s - 1))) := by
  have hlt (x : ℝ) (hx : x ∈ Icc 0 b) : x < α := lt_of_le_of_lt hx.2 hbα
  have huIcc : [[(0 : ℝ), b]] = Icc 0 b := uIcc_of_le hb0
  -- continuity of everything on `[0, b]`
  have hcW : ContinuousOn (fun y : ℝ ↦ (α - y) ^ (1 - s)) (Icc 0 b) := fun x hx ↦
    (hasDerivAt_stripWeight (s := s) (hlt x hx)).continuousAt.continuousWithinAt
  have hcW' : ContinuousOn (fun y : ℝ ↦ -((1 - s) * (α - y) ^ (-s))) (Icc 0 b) := fun x hx ↦
    (hasDerivAt_stripWeight' (s := s) (hlt x hx)).continuousAt.continuousWithinAt
  have hcW'' : ContinuousOn (fun y : ℝ ↦ -(s * (1 - s) * (α - y) ^ (-s - 1))) (Icc 0 b) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have : α - x ≠ 0 := by linarith [hlt x hx]
    exact (((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl this)).const_mul
      (s * (1 - s))).neg
  have hcf : ContinuousOn f (Icc 0 b) := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hcf' : ContinuousOn f' (Icc 0 b) := fun x hx ↦ (hf' x hx).continuousAt.continuousWithinAt
  have hIoo {g g' : ℝ → ℝ} (h : ∀ x ∈ Icc 0 b, HasDerivAt g (g' x) x) :
      ∀ x ∈ Ioo (min 0 b) (max 0 b), HasDerivAt g (g' x) x := fun x hx ↦
    h x (by rw [min_eq_left hb0, max_eq_right hb0] at hx; exact Ioo_subset_Icc_self hx)
  -- first integration by parts: `∫ W f'' = [W f'] − ∫ W' f'`
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun y : ℝ ↦ (α - y) ^ (1 - s)) (v := f')
    (u' := fun y ↦ -((1 - s) * (α - y) ^ (-s))) (v' := f'')
    (by rw [huIcc]; exact hcW) (by rw [huIcc]; exact hcf')
    (hIoo fun x hx ↦ hasDerivAt_stripWeight (hlt x hx)) (hIoo hf')
    (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb0]; exact hcW'.integrableOn_Icc)
    (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb0]; exact hc''.integrableOn_Icc)
  -- second integration by parts: `∫ W' f' = [W' f] − ∫ W'' f`
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun y : ℝ ↦ -((1 - s) * (α - y) ^ (-s))) (v := f)
    (u' := fun y ↦ -(s * (1 - s) * (α - y) ^ (-s - 1))) (v' := f')
    (by rw [huIcc]; exact hcW') (by rw [huIcc]; exact hcf)
    (hIoo fun x hx ↦ hasDerivAt_stripWeight' (hlt x hx)) (hIoo hf)
    (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb0]; exact hcW''.integrableOn_Icc)
    (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb0]; exact hcf'.integrableOn_Icc)
  have e1 : ∫ x in (0 : ℝ)..b, f'' x * (α - x) ^ (1 - s) =
      ∫ x in (0 : ℝ)..b, (α - x) ^ (1 - s) * f'' x :=
    intervalIntegral.integral_congr fun x _ ↦ mul_comm _ _
  have e2 : ∫ x in (0 : ℝ)..b, -((1 - s) * (α - x) ^ (-s)) * f' x =
      ∫ x in (0 : ℝ)..b, f' x * -((1 - s) * (α - x) ^ (-s)) :=
    intervalIntegral.integral_congr fun x _ ↦ mul_comm _ _
  have e3 : ∫ x in (0 : ℝ)..b, -(s * (1 - s) * (α - x) ^ (-s - 1)) * f x =
      ∫ x in (0 : ℝ)..b, f x * -(s * (1 - s) * (α - x) ^ (-s - 1)) :=
    intervalIntegral.integral_congr fun x _ ↦ mul_comm _ _
  rw [e1, h1, h2, e3]
  simp only [sub_zero]
  ring

/-- `(α − x)^{−s}` is integrable on `[0, α]` for `s < 1`. -/
theorem intervalIntegrable_stripWeight_neg {α s : ℝ} (hs1 : s < 1) :
    IntervalIntegrable (fun x : ℝ ↦ (α - x) ^ (-s)) MeasureTheory.volume 0 α := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := α) (r := -s)
    (by linarith)).comp_sub_left α
  simpa [sub_self, sub_zero] using h.symm

/-- `(α − b)^{p} → 0` as `b → α⁻`, for `p > 0`. -/
theorem tendsto_stripWeight_zero {α p : ℝ} (hp : 0 < p) :
    Tendsto (fun b : ℝ ↦ (α - b) ^ p) (𝓝[<] α) (𝓝 0) := by
  have h : Tendsto (fun b : ℝ ↦ α - b) (𝓝[<] α) (𝓝 0) := by
    have h0 : Tendsto (fun b : ℝ ↦ α - b) (𝓝 α) (𝓝 (α - α)) := tendsto_const_nhds.sub tendsto_id
    rw [sub_self] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  simpa [Real.zero_rpow hp.ne'] using h.rpow_const (Or.inr hp.le)

/-- `f w''` is integrable on `[0, α]` when `f` is continuous on `[0, α)` and vanishes like `α − x`
at `α`: it is dominated by `C s (1 − s)(α − x)^{−s}`. -/
theorem intervalIntegrable_mul_stripWeight'' {α s : ℝ} (hα : 0 < α) (hs0 : 0 ≤ s) (hs1 : s < 1)
    {f : ℝ → ℝ} (hcf : ContinuousOn f (Ico 0 α)) {C : ℝ}
    (hfC : ∀ x ∈ Ico 0 α, |f x| ≤ C * (α - x)) :
    IntervalIntegrable (fun x ↦ f x * (-(s * (1 - s) * (α - x) ^ (-s - 1))))
      MeasureTheory.volume 0 α := by
  have hs1' : 0 < 1 - s := by linarith
  have hg := (intervalIntegrable_stripWeight_neg (α := α) hs1).const_mul (C * (s * (1 - s)))
  refine hg.mono_fun' ?_ ?_
  · rw [uIoc_of_le hα.le, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    intro x hx
    have hx' : α - x ≠ 0 := by linarith [hx.2]
    have hfx : ContinuousWithinAt f (Ioo 0 α) x := hcf.mono Ioo_subset_Ico_self x hx
    exact hfx.mul ((((continuousAt_const.sub continuousAt_id).rpow_const
      (Or.inl hx')).const_mul (s * (1 - s))).neg).continuousWithinAt
  · rw [uIoc_of_le hα.le, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm]
    refine (MeasureTheory.ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦ ?_
    have hpos : 0 < α - x := by linarith [hx.2]
    have hss : 0 ≤ s * (1 - s) := mul_nonneg hs0 hs1'.le
    have hsplit : (α - x) ^ (-s) = (α - x) * (α - x) ^ (-s - 1) := by
      have h := Real.rpow_add hpos 1 (-s - 1)
      rw [Real.rpow_one, show (1 : ℝ) + (-s - 1) = -s by ring] at h
      exact h
    have hfx := hfC x ⟨hx.1.le, hx.2⟩
    dsimp only
    rw [norm_mul, Real.norm_eq_abs, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hss (Real.rpow_nonneg hpos.le _)), hsplit]
    have hw : 0 ≤ (α - x) ^ (-s - 1) := Real.rpow_nonneg hpos.le _
    calc |f x| * (s * (1 - s) * (α - x) ^ (-s - 1)) ≤ C * (α - x) * (s * (1 - s) * (α - x) ^ (-s - 1)) :=
          mul_le_mul_of_nonneg_right hfx (mul_nonneg hss hw)
      _ = C * (s * (1 - s)) * ((α - x) * (α - x) ^ (-s - 1)) := by ring

/-- **Integration by parts twice against `(α − x)^{1−s}` on `(0, α)`.** For `0 ≤ s < 1` and a
function `f` that is `C²` on `[0, α)`, vanishes like `α − x` at `α`, and has bounded
derivative:
`∫₀^α f'' w = −f'(0) α^{1−s} − f(0)(1 − s)α^{−s} + ∫₀^α f w''`, with
`w'' = −s(1 − s)(α − x)^{−s−1}`. -/
theorem stripWeight_ibp {α s : ℝ} (hα : 0 < α) (hs0 : 0 ≤ s) (hs1 : s < 1) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x ∈ Ico 0 α, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Ico 0 α, HasDerivAt f' (f'' x) x)
    (hc'' : ContinuousOn f'' (Ico 0 α)) {C : ℝ}
    (hfC : ∀ x ∈ Ico 0 α, |f x| ≤ C * (α - x)) (hf'C : ∀ x ∈ Ico 0 α, |f' x| ≤ C)
    (hint : IntervalIntegrable (fun x ↦ f'' x * (α - x) ^ (1 - s)) MeasureTheory.volume 0 α) :
    ∫ x in (0 : ℝ)..α, f'' x * (α - x) ^ (1 - s) =
      -(f' 0 * α ^ (1 - s)) - f 0 * ((1 - s) * α ^ (-s)) +
        ∫ x in (0 : ℝ)..α, f x * (-(s * (1 - s) * (α - x) ^ (-s - 1))) := by
  have hs1' : 0 < 1 - s := by linarith
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf'C 0 ⟨le_rfl, hα⟩)
  -- integrability of `f w''`, dominated by `C s (1 − s) (α − x)^{−s}`
  have hint2 := intervalIntegrable_mul_stripWeight'' hα hs0 hs1
    (fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt) hfC
  -- the finite identity for `b ∈ [0, α)`
  have hfin : ∀ b ∈ Ico 0 α, ∫ x in (0 : ℝ)..b, f'' x * (α - x) ^ (1 - s) =
      f' b * (α - b) ^ (1 - s) - f' 0 * α ^ (1 - s)
        - (f b * (-((1 - s) * (α - b) ^ (-s))) - f 0 * (-((1 - s) * α ^ (-s))))
        + ∫ x in (0 : ℝ)..b, f x * (-(s * (1 - s) * (α - x) ^ (-s - 1))) := by
    intro b hb
    have sub : Icc 0 b ⊆ Ico 0 α := fun x hx ↦ ⟨hx.1, lt_of_le_of_lt hx.2 hb.2⟩
    exact stripWeight_ibp_finite hb.1 hb.2 (fun x hx ↦ hf x (sub hx)) (fun x hx ↦ hf' x (sub hx))
      (hc''.mono sub)
  -- limits as `b → α⁻`
  have hprim {F : ℝ → ℝ} (hF : IntervalIntegrable F MeasureTheory.volume 0 α) :
      Tendsto (fun b ↦ ∫ x in (0 : ℝ)..b, F x) (𝓝[<] α) (𝓝 (∫ x in (0 : ℝ)..α, F x)) := by
    have hc := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
      (a := 0) (b := α) (f := F) (by
        rw [uIcc_of_le hα.le]
        exact (intervalIntegrable_iff_integrableOn_Icc_of_le hα.le).mp hF)
    have hα' : α ∈ uIcc 0 α := right_mem_uIcc
    have := (hc α hα').tendsto
    rw [← nhdsWithin_Ioo_eq_nhdsLT hα]
    refine this.mono_left (nhdsWithin_mono _ ?_)
    rw [uIcc_of_le hα.le]
    exact Ioo_subset_Icc_self
  have hev : ∀ᶠ b in 𝓝[<] α, b ∈ Ico 0 α :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hα) Ioo_subset_Ico_self
  have hevpos : ∀ᶠ b in 𝓝[<] α, b ∈ Ioo 0 α := Ioo_mem_nhdsLT hα
  have hw0 := tendsto_stripWeight_zero (α := α) hs1'
  have hlim1 : Tendsto (fun b ↦ f' b * (α - b) ^ (1 - s)) (𝓝[<] α) (𝓝 0) := by
    have hb : Tendsto (fun b ↦ C * (α - b) ^ (1 - s)) (𝓝[<] α) (𝓝 0) := by
      simpa using hw0.const_mul C
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hevpos] with b hb'
    have hpos : 0 < α - b := by linarith [hb'.2]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
    exact mul_le_mul_of_nonneg_right (hf'C b ⟨hb'.1.le, hb'.2⟩) (Real.rpow_nonneg hpos.le _)
  have hlim2 : Tendsto (fun b ↦ f b * (-((1 - s) * (α - b) ^ (-s)))) (𝓝[<] α) (𝓝 0) := by
    have hb : Tendsto (fun b ↦ C * (1 - s) * (α - b) ^ (1 - s)) (𝓝[<] α) (𝓝 0) := by
      simpa using hw0.const_mul (C * (1 - s))
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hevpos] with b hb'
    have hpos : 0 < α - b := by linarith [hb'.2]
    have hsplit : (α - b) ^ (1 - s) = (α - b) * (α - b) ^ (-s) := by
      have h := Real.rpow_add hpos 1 (-s)
      rw [Real.rpow_one, show (1 : ℝ) + -s = 1 - s by ring] at h
      exact h
    rw [norm_mul, Real.norm_eq_abs, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hs1'.le (Real.rpow_nonneg hpos.le _)), hsplit]
    calc |f b| * ((1 - s) * (α - b) ^ (-s)) ≤ C * (α - b) * ((1 - s) * (α - b) ^ (-s)) :=
          mul_le_mul_of_nonneg_right (hfC b ⟨hb'.1.le, hb'.2⟩)
            (mul_nonneg hs1'.le (Real.rpow_nonneg hpos.le _))
      _ = C * (1 - s) * ((α - b) * (α - b) ^ (-s)) := by ring
  have hR : Tendsto (fun b ↦ f' b * (α - b) ^ (1 - s) - f' 0 * α ^ (1 - s)
        - (f b * (-((1 - s) * (α - b) ^ (-s))) - f 0 * (-((1 - s) * α ^ (-s))))
        + ∫ x in (0 : ℝ)..b, f x * (-(s * (1 - s) * (α - x) ^ (-s - 1)))) (𝓝[<] α)
      (𝓝 (0 - f' 0 * α ^ (1 - s) - (0 - f 0 * (-((1 - s) * α ^ (-s))))
        + ∫ x in (0 : ℝ)..α, f x * (-(s * (1 - s) * (α - x) ^ (-s - 1))))) :=
    (((hlim1.sub_const _).sub (hlim2.sub_const _)).add (hprim hint2))
  have hL := hprim hint
  have heq := tendsto_nhds_unique (hL.congr' (Filter.eventuallyEq_of_mem hev hfin)) hR
  rw [heq]
  ring

/-- Reflection of interval integrability: from `F` on `[−α, 0]` to `x ↦ F(−x)` on `[0, α]`. -/
private theorem intervalIntegrable_reflect {F : ℝ → ℝ} {α : ℝ}
    (hF : IntervalIntegrable F MeasureTheory.volume (-α) 0) :
    IntervalIntegrable (fun x ↦ F (-x)) MeasureTheory.volume 0 α := by
  have h := hF.comp_mul_left (c := -1)
  simp only [neg_mul, one_mul, div_neg, div_one, neg_neg, neg_zero] at h
  exact h.symm

/-- **Integration by parts twice against `(α − |x|)^{1−s}` on `(−α, α)`.** The two halves give
the boundary-free identity with a kink term at `0`:
`∫_{−α}^{α} f'' w = −2 f(0)(1 − s)α^{−s} + ∫_{−α}^{α} f w''`, `w'' = −s(1 − s)(α − |x|)^{−s−1}`. -/
theorem stripWeight_ibp_symm {α s : ℝ} (hα : 0 < α) (hs0 : 0 ≤ s) (hs1 : s < 1) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x ∈ Ioo (-α) α, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Ioo (-α) α, HasDerivAt f' (f'' x) x)
    (hc'' : ContinuousOn f'' (Ioo (-α) α)) {C : ℝ}
    (hfC : ∀ x ∈ Ioo (-α) α, |f x| ≤ C * (α - |x|)) (hf'C : ∀ x ∈ Ioo (-α) α, |f' x| ≤ C)
    (hint : IntervalIntegrable (fun x ↦ f'' x * (α - |x|) ^ (1 - s)) MeasureTheory.volume (-α) α) :
    ∫ x in (-α)..α, f'' x * (α - |x|) ^ (1 - s) =
      -(2 * f 0 * ((1 - s) * α ^ (-s))) +
        ∫ x in (-α)..α, f x * (-(s * (1 - s) * (α - |x|) ^ (-s - 1))) := by
  have hαn : -α < 0 := by linarith
  have hIco : Ico 0 α ⊆ Ioo (-α) α := fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
  have hIcoN (x : ℝ) (hx : x ∈ Ico 0 α) : -x ∈ Ioo (-α) α := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  -- the right half
  have hintR : IntervalIntegrable (fun x ↦ f'' x * (α - x) ^ (1 - s)) MeasureTheory.volume 0 α := by
    have h : IntervalIntegrable (fun x ↦ f'' x * (α - |x|) ^ (1 - s)) MeasureTheory.volume 0 α :=
      hint.mono_set (by rw [uIcc_of_le hα.le, uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) le_rfl)
    refine h.congr ?_
    rw [uIoc_of_le hα.le]
    intro x (hx : x ∈ Ioc 0 α)
    simp only [abs_of_pos hx.1]
  have hR := stripWeight_ibp hα hs0 hs1 (fun x hx ↦ hf x (hIco hx)) (fun x hx ↦ hf' x (hIco hx))
    (hc''.mono hIco) (C := C)
    (fun x (hx : x ∈ Ico 0 α) ↦ by simpa [abs_of_nonneg hx.1] using hfC x (hIco hx))
    (fun x hx ↦ hf'C x (hIco hx)) hintR
  -- the left half, by reflection
  have hg : ∀ x ∈ Ico 0 α, HasDerivAt (fun y ↦ f (-y)) (-f' (-x)) x := fun x hx ↦ by
    convert (hf (-x) (hIcoN x hx)).comp x (hasDerivAt_neg x) using 1 <;> first | rfl | ring
  have hg' : ∀ x ∈ Ico 0 α, HasDerivAt (fun y ↦ -f' (-y)) (f'' (-x)) x := fun x hx ↦ by
    convert ((hf' (-x) (hIcoN x hx)).comp x (hasDerivAt_neg x)).neg using 1 <;> first | rfl | ring
  have hcg : ContinuousOn (fun x ↦ f'' (-x)) (Ico 0 α) :=
    hc''.comp continuous_neg.continuousOn (fun x hx ↦ hIcoN x hx)
  have hintL : IntervalIntegrable (fun x ↦ f'' (-x) * (α - x) ^ (1 - s)) MeasureTheory.volume 0 α := by
    have h : IntervalIntegrable (fun x ↦ f'' x * (α - |x|) ^ (1 - s)) MeasureTheory.volume (-α) 0 :=
      hint.mono_set (by rw [uIcc_of_le hαn.le, uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith))
    refine (intervalIntegrable_reflect h).congr ?_
    rw [uIoc_of_le hα.le]
    intro x (hx : x ∈ Ioc 0 α)
    simp only [abs_neg, abs_of_pos hx.1]
  have hL := stripWeight_ibp hα hs0 hs1 hg hg' hcg (C := C)
    (fun x (hx : x ∈ Ico 0 α) ↦ by simpa [abs_neg, abs_of_nonneg hx.1] using hfC (-x) (hIcoN x hx))
    (fun x hx ↦ by simpa [abs_neg] using hf'C (-x) (hIcoN x hx)) hintL
  -- change variables back and add the halves
  have cF : ∫ x in (-α)..0, f'' x * (α - |x|) ^ (1 - s) =
      ∫ x in (0 : ℝ)..α, f'' (-x) * (α - x) ^ (1 - s) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := α)
      (fun x ↦ f'' x * (α - |x|) ^ (1 - s))
    simp only [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hα.le] at hx
    simp only [abs_neg, abs_of_nonneg hx.1]
  have cG : ∫ x in (-α)..0, f x * (-(s * (1 - s) * (α - |x|) ^ (-s - 1))) =
      ∫ x in (0 : ℝ)..α, f (-x) * (-(s * (1 - s) * (α - x) ^ (-s - 1))) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := α)
      (fun x ↦ f x * (-(s * (1 - s) * (α - |x|) ^ (-s - 1))))
    simp only [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hα.le] at hx
    simp only [abs_neg, abs_of_nonneg hx.1]
  have rF : ∫ x in (0 : ℝ)..α, f'' x * (α - |x|) ^ (1 - s) =
      ∫ x in (0 : ℝ)..α, f'' x * (α - x) ^ (1 - s) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hα.le] at hx
    simp only [abs_of_nonneg hx.1]
  have rG : ∫ x in (0 : ℝ)..α, f x * (-(s * (1 - s) * (α - |x|) ^ (-s - 1))) =
      ∫ x in (0 : ℝ)..α, f x * (-(s * (1 - s) * (α - x) ^ (-s - 1))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hα.le] at hx
    simp only [abs_of_nonneg hx.1]
  -- integrability of the four pieces
  have iF_L : IntervalIntegrable (fun x ↦ f'' x * (α - |x|) ^ (1 - s)) MeasureTheory.volume (-α) 0 :=
    hint.mono_set (by rw [uIcc_of_le hαn.le, uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith))
  have iF_R : IntervalIntegrable (fun x ↦ f'' x * (α - |x|) ^ (1 - s)) MeasureTheory.volume 0 α :=
    hint.mono_set (by rw [uIcc_of_le hα.le, uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) le_rfl)
  have iG_R0 := intervalIntegrable_mul_stripWeight'' hα hs0 hs1
    (fun x hx ↦ (hf x (hIco hx)).continuousAt.continuousWithinAt)
    (C := C) (fun x (hx : x ∈ Ico 0 α) ↦ by simpa [abs_of_nonneg hx.1] using hfC x (hIco hx))
  have iG_L0 := intervalIntegrable_mul_stripWeight'' hα hs0 hs1 (f := fun y ↦ f (-y))
    (fun x hx ↦ ((hg x hx).continuousAt).continuousWithinAt)
    (C := C) (fun x (hx : x ∈ Ico 0 α) ↦ by simpa [abs_neg, abs_of_nonneg hx.1] using hfC (-x) (hIcoN x hx))
  have iG_R : IntervalIntegrable (fun x ↦ f x * (-(s * (1 - s) * (α - |x|) ^ (-s - 1))))
      MeasureTheory.volume 0 α := by
    refine iG_R0.congr ?_
    rw [uIoc_of_le hα.le]
    intro x (hx : x ∈ Ioc 0 α)
    simp only [abs_of_pos hx.1]
  have iG_L : IntervalIntegrable (fun x ↦ f x * (-(s * (1 - s) * (α - |x|) ^ (-s - 1))))
      MeasureTheory.volume (-α) 0 := by
    have h := iG_L0.comp_mul_left (c := -1)
    simp only [neg_mul, one_mul, neg_neg, div_neg, div_one, neg_zero] at h
    refine h.symm.congr ?_
    rw [uIoc_of_le hαn.le]
    intro x (hx : x ∈ Ioc (-α) 0)
    simp only [abs_of_nonpos hx.2]
  rw [← intervalIntegral.integral_add_adjacent_intervals iF_L iF_R,
    ← intervalIntegral.integral_add_adjacent_intervals iG_L iG_R, cF, cG, rF, rG, hR, hL]
  simp only [neg_zero]
  ring

/-- The open strip `{|Re w| < α}` is open. -/
theorem isOpen_strip (α : ℝ) : IsOpen {w : ℂ | |w.re| < α} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const

/-- **A Cauchy estimate for the second derivative.** On the open strip,
`‖B''(w)‖ ≤ C / (α − |Re w|)`. -/
theorem stripBlaschke_deriv2_bound {α : ℝ} (hα : 0 < α) {n : ℕ} (ρ : Fin n → ℂ)
    (hρ : ∀ j, |(ρ j).re| < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, |w.re| < α →
      ‖deriv (deriv (stripBlaschke α ρ)) w‖ ≤ C / (α - |w.re|) := by
  obtain ⟨C, hC0, hC⟩ := stripBlaschke_deriv_bound hα ρ hρ
  have hd : DifferentiableOn ℂ (stripBlaschke α ρ) {w : ℂ | |w.re| < α} := fun w hw ↦
    (hC w hw).1.differentiableWithinAt
  have hd' : DifferentiableOn ℂ (deriv (stripBlaschke α ρ)) {w : ℂ | |w.re| < α} :=
    hd.deriv (isOpen_strip α)
  refine ⟨2 * C, by positivity, fun w hw ↦ ?_⟩
  set r := (α - |w.re|) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hball : closedBall w r ⊆ {w : ℂ | |w.re| < α} := by
    intro z hz
    have h1 : |z.re - w.re| ≤ r := by
      calc |z.re - w.re| = |(z - w).re| := by rw [Complex.sub_re]
        _ ≤ ‖z - w‖ := Complex.abs_re_le_norm _
        _ ≤ r := by simpa [dist_eq_norm] using hz
    have h2 : |z.re| ≤ |w.re| + r := by
      have := abs_sub_abs_le_abs_sub z.re w.re
      linarith
    show |z.re| < α
    linarith
  have hcl : DiffContOnCl ℂ (deriv (stripBlaschke α ρ)) (ball w r) :=
    (hd'.mono ((closure_ball w hr0.ne').subset.trans hball)).diffContOnCl
  have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 hcl
    (fun z hz ↦ (hC z (hball (sphere_subset_closedBall hz))).2)
  calc ‖deriv (deriv (stripBlaschke α ρ)) w‖ ≤ C / r := hest
    _ = 2 * C / (α - |w.re|) := by rw [hr]; field_simp

/-! ### Second derivatives of `‖h‖²` along the coordinate lines -/

section Lines

variable {h : ℂ → ℂ} {U : Set ℂ}

/-- Along the horizontal line through `σ + t I`, `x ↦ h(x + t I)` has derivative `h'`. -/
theorem hasDerivAt_re_line (hh : DifferentiableOn ℂ h U) (hU : IsOpen U) {σ t : ℝ}
    (hz : (σ : ℂ) + t * I ∈ U) :
    HasDerivAt (fun x : ℝ ↦ h (x + t * I)) (deriv h (σ + t * I)) σ := by
  have hd := (hh.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hl : HasDerivAt (fun x : ℝ ↦ (x : ℂ) + t * I) 1 σ := by
    simpa using (hasDerivAt_id (σ : ℂ)).comp_ofReal.add_const ((t : ℂ) * I)
  have h' := hd.comp σ hl
  rwa [mul_one] at h'

/-- Along the vertical line through `σ + t I`, `y ↦ h(σ + y I)` has derivative `h' · I`. -/
theorem hasDerivAt_im_line (hh : DifferentiableOn ℂ h U) (hU : IsOpen U) {σ t : ℝ}
    (hz : (σ : ℂ) + t * I ∈ U) :
    HasDerivAt (fun y : ℝ ↦ h (σ + y * I)) (deriv h (σ + t * I) * I) t := by
  have hd := (hh.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hl : HasDerivAt (fun y : ℝ ↦ (σ : ℂ) + y * I) I t := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).comp_ofReal.const_add (σ : ℂ)
  exact hd.comp t hl

/-- The horizontal second derivative of `‖h‖²`: `P = 2‖h'‖² + 2⟪h, h''⟫`. -/
theorem hasDerivAt_re_line_normSq (hh : DifferentiableOn ℂ h U) (hU : IsOpen U) {σ t : ℝ}
    (hz : (σ : ℂ) + t * I ∈ U) :
    HasDerivAt (fun x : ℝ ↦ ‖h (x + t * I)‖ ^ 2)
        (2 * inner ℝ (h (σ + t * I)) (deriv h (σ + t * I))) σ ∧
      HasDerivAt (fun x : ℝ ↦ 2 * inner ℝ (h (x + t * I)) (deriv h (x + t * I)))
        (2 * ‖deriv h (σ + t * I)‖ ^ 2 + 2 * inner ℝ (h (σ + t * I)) (deriv (deriv h) (σ + t * I))) σ := by
  have h1 := hasDerivAt_re_line hh hU hz
  have h2 := hasDerivAt_re_line (hh.deriv hU) hU hz
  refine ⟨h1.norm_sq, ?_⟩
  have := (h1.inner ℝ h2).const_mul 2
  convert this using 1
  rw [real_inner_self_eq_norm_sq]
  ring

/-- The vertical second derivative of `‖h‖²`: `Q = 2‖h'‖² − 2⟪h, h''⟫`. -/
theorem hasDerivAt_im_line_normSq (hh : DifferentiableOn ℂ h U) (hU : IsOpen U) {σ t : ℝ}
    (hz : (σ : ℂ) + t * I ∈ U) :
    HasDerivAt (fun y : ℝ ↦ ‖h (σ + y * I)‖ ^ 2)
        (2 * inner ℝ (h (σ + t * I)) (deriv h (σ + t * I) * I)) t ∧
      HasDerivAt (fun y : ℝ ↦ 2 * inner ℝ (h (σ + y * I)) (deriv h (σ + y * I) * I))
        (2 * ‖deriv h (σ + t * I)‖ ^ 2 - 2 * inner ℝ (h (σ + t * I)) (deriv (deriv h) (σ + t * I))) t := by
  have h1 := hasDerivAt_im_line hh hU hz
  have h2 := (hasDerivAt_im_line (hh.deriv hU) hU hz).mul_const I
  refine ⟨h1.norm_sq, ?_⟩
  have := (h1.inner ℝ h2).const_mul 2
  convert this using 1
  have hII : deriv (deriv h) (σ + t * I) * I * I = -deriv (deriv h) (σ + t * I) := by
    rw [mul_assoc, I_mul_I, mul_neg_one]
  rw [hII, inner_neg_right, real_inner_self_eq_norm_sq, norm_mul, norm_I, mul_one]
  ring

end Lines

/-! ### Carleson's formula on the strip -/

section Carleson

variable {h : ℂ → ℂ} {U : Set ℂ}

/-- **The vertical term integrates to zero.** If the first vertical derivative of `‖h‖²` tends to
`0` at both ends of a vertical line and the second is integrable, the second integrates to `0`. -/
theorem integral_im_line_secondDeriv_eq_zero (hh : DifferentiableOn ℂ h U) (hU : IsOpen U) {σ : ℝ}
    (hline : ∀ t : ℝ, (σ : ℂ) + t * I ∈ U)
    (hint : MeasureTheory.Integrable fun t : ℝ ↦
      2 * ‖deriv h (σ + t * I)‖ ^ 2 - 2 * inner ℝ (h (σ + t * I)) (deriv (deriv h) (σ + t * I)))
    (hbot : Tendsto (fun t : ℝ ↦ 2 * inner ℝ (h (σ + t * I)) (deriv h (σ + t * I) * I)) atBot (𝓝 0))
    (htop : Tendsto (fun t : ℝ ↦ 2 * inner ℝ (h (σ + t * I)) (deriv h (σ + t * I) * I)) atTop (𝓝 0)) :
    ∫ t : ℝ, (2 * ‖deriv h (σ + t * I)‖ ^ 2 -
      2 * inner ℝ (h (σ + t * I)) (deriv (deriv h) (σ + t * I))) = 0 := by
  have := MeasureTheory.integral_of_hasDerivAt_of_tendsto
    (fun t ↦ (hasDerivAt_im_line_normSq hh hU (hline t)).2) hint hbot htop
  simpa using this

end Carleson

/-! ### Bounds for the product `B g` on the strip -/

section ProductBounds

variable {α : ℝ} {B g : ℂ → ℂ}

/-- The derivative of the product on the open strip. -/
theorem deriv_mul_strip (hB : DifferentiableOn ℂ B {z : ℂ | |z.re| < α})
    (hg : DifferentiableOn ℂ g {z : ℂ | |z.re| < α}) {z : ℂ} (hz : |z.re| < α) :
    HasDerivAt (fun z ↦ B z * g z) (deriv B z * g z + B z * deriv g z) z := by
  have hn := (isOpen_strip α).mem_nhds hz
  exact ((hB.differentiableAt hn).hasDerivAt).mul ((hg.differentiableAt hn).hasDerivAt)

/-- The second derivative of the product on the open strip:
`(Bg)'' = B'' g + 2 B' g' + B g''`. -/
theorem deriv_deriv_mul_strip (hB : DifferentiableOn ℂ B {z : ℂ | |z.re| < α})
    (hg : DifferentiableOn ℂ g {z : ℂ | |z.re| < α}) {z : ℂ} (hz : |z.re| < α) :
    deriv (deriv fun z ↦ B z * g z) z =
      deriv (deriv B) z * g z + 2 * (deriv B z * deriv g z) + B z * deriv (deriv g) z := by
  have hU := isOpen_strip α
  have hn := hU.mem_nhds hz
  have heq : deriv (fun z ↦ B z * g z) =ᶠ[𝓝 z] fun z ↦ deriv B z * g z + B z * deriv g z := by
    filter_upwards [hn] with y hy
    exact (deriv_mul_strip hB hg hy).deriv
  rw [heq.deriv_eq]
  have hB' := ((hB.deriv hU).differentiableAt hn).hasDerivAt
  have hg' := ((hg.deriv hU).differentiableAt hn).hasDerivAt
  have hB0 := (hB.differentiableAt hn).hasDerivAt
  have hg0 := (hg.differentiableAt hn).hasDerivAt
  rw [((hB'.fun_mul hg0).fun_add (hB0.fun_mul hg')).deriv]
  ring

variable {C M : ℝ}

/-- Bounds for `B g` and its first two derivatives. -/
theorem norm_mul_strip_bounds (hB : DifferentiableOn ℂ B {z : ℂ | |z.re| < α})
    (hg : DifferentiableOn ℂ g {z : ℂ | |z.re| < α})
    (hB0 : ∀ z : ℂ, |z.re| < α → ‖B z‖ ≤ 1)
    (hB1 : ∀ z : ℂ, |z.re| < α → ‖deriv B z‖ ≤ C)
    (hB2 : ∀ z : ℂ, |z.re| < α → ‖deriv (deriv B) z‖ ≤ C / (α - |z.re|))
    (hg0 : ∀ z : ℂ, |z.re| < α → ‖g z‖ ≤ M / (1 + z.im ^ 2))
    (hg1 : ∀ z : ℂ, |z.re| < α → ‖deriv g z‖ ≤ M / (1 + z.im ^ 2))
    (hg2 : ∀ z : ℂ, |z.re| < α → ‖deriv (deriv g) z‖ ≤ M / (1 + z.im ^ 2))
    {z : ℂ} (hz : |z.re| < α) :
    ‖B z * g z‖ ≤ M / (1 + z.im ^ 2) ∧
      ‖deriv (fun z ↦ B z * g z) z‖ ≤ (C + 1) * (M / (1 + z.im ^ 2)) ∧
      ‖deriv (deriv fun z ↦ B z * g z) z‖ ≤
        (C / (α - |z.re|) + 2 * C + 1) * (M / (1 + z.im ^ 2)) := by
  have hb := hB0 z hz
  have hgz := hg0 z hz
  have hg1z := hg1 z hz
  have hg2z := hg2 z hz
  have hb1 := hB1 z hz
  have hb2 := hB2 z hz
  have hD : 0 ≤ M / (1 + z.im ^ 2) := (norm_nonneg _).trans hgz
  have hC : 0 ≤ C := (norm_nonneg _).trans hb1
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul]
    calc ‖B z‖ * ‖g z‖ ≤ 1 * (M / (1 + z.im ^ 2)) := mul_le_mul hb hgz (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [(deriv_mul_strip hB hg hz).deriv]
    calc ‖deriv B z * g z + B z * deriv g z‖ ≤ ‖deriv B z‖ * ‖g z‖ + ‖B z‖ * ‖deriv g z‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ C * (M / (1 + z.im ^ 2)) + 1 * (M / (1 + z.im ^ 2)) := by
          gcongr
      _ = (C + 1) * (M / (1 + z.im ^ 2)) := by ring
  · rw [deriv_deriv_mul_strip hB hg hz]
    have hd : 0 < α - |z.re| := by linarith
    calc ‖deriv (deriv B) z * g z + 2 * (deriv B z * deriv g z) + B z * deriv (deriv g) z‖
        ≤ ‖deriv (deriv B) z‖ * ‖g z‖ + 2 * (‖deriv B z‖ * ‖deriv g z‖) +
            ‖B z‖ * ‖deriv (deriv g) z‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)
          · rw [norm_mul, norm_mul, norm_mul, Complex.norm_two]
          · rw [norm_mul]
      _ ≤ C / (α - |z.re|) * (M / (1 + z.im ^ 2)) + 2 * (C * (M / (1 + z.im ^ 2))) +
            1 * (M / (1 + z.im ^ 2)) := by
          gcongr
      _ = (C / (α - |z.re|) + 2 * C + 1) * (M / (1 + z.im ^ 2)) := by ring

end ProductBounds

/-! ### Continuity along lines, and the bound for `P` and `Q` -/

/-- A function continuous on the open strip is continuous along every vertical line in it. -/
theorem continuous_im_line {α σ : ℝ} {E : Type*} [TopologicalSpace E] {f : ℂ → E}
    (hf : ContinuousOn f {z : ℂ | |z.re| < α}) (hσ : |σ| < α) :
    Continuous fun t : ℝ ↦ f (σ + t * I) := by
  refine hf.comp_continuous (by fun_prop) fun t ↦ ?_
  show |((σ : ℂ) + t * I).re| < α
  simpa using hσ

/-- A function continuous on the open strip is continuous along horizontal lines, on `(−α, α)`. -/
theorem continuousOn_re_line {α t : ℝ} {E : Type*} [TopologicalSpace E] {f : ℂ → E}
    (hf : ContinuousOn f {z : ℂ | |z.re| < α}) :
    ContinuousOn (fun σ : ℝ ↦ f (σ + t * I)) (Ioo (-α) α) := by
  refine hf.comp (by fun_prop) fun σ hσ ↦ ?_
  show |((σ : ℂ) + t * I).re| < α
  simpa [abs_lt] using hσ

/-- A function continuous on the open strip is continuous on `(−α, α) × ℝ` in coordinates. -/
theorem continuousOn_strip_coords {α : ℝ} {E : Type*} [TopologicalSpace E] {f : ℂ → E}
    (hf : ContinuousOn f {z : ℂ | |z.re| < α}) :
    ContinuousOn (fun p : ℝ × ℝ ↦ f (p.1 + p.2 * I)) (Ioo (-α) α ×ˢ univ) := by
  refine hf.comp (by fun_prop) fun p hp ↦ ?_
  show |((p.1 : ℂ) + p.2 * I).re| < α
  simpa [abs_lt] using hp.1

/-- `|2‖b‖² ± 2⟪a, c⟫| ≤ 2‖b‖² + 2‖a‖‖c‖`. -/
theorem abs_two_sq_add_two_inner_le (a b c : ℂ) :
    |2 * ‖b‖ ^ 2 + 2 * inner ℝ a c| ≤ 2 * ‖b‖ ^ 2 + 2 * (‖a‖ * ‖c‖) ∧
      |2 * ‖b‖ ^ 2 - 2 * inner ℝ a c| ≤ 2 * ‖b‖ ^ 2 + 2 * (‖a‖ * ‖c‖) := by
  have hi := abs_real_inner_le_norm a c
  have hb : 0 ≤ ‖b‖ ^ 2 := by positivity
  constructor <;> (rw [abs_le]; constructor <;> nlinarith [abs_le.mp hi])

/-- `(1 + t²)⁻¹ → 0` at both ends of the real line. -/
theorem tendsto_inv_one_add_sq_atTop :
    Tendsto (fun t : ℝ ↦ (1 + t ^ 2)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun t ↦ by linarith) (tendsto_pow_atTop two_ne_zero))

theorem tendsto_inv_one_add_sq_atBot :
    Tendsto (fun t : ℝ ↦ (1 + t ^ 2)⁻¹) atBot (𝓝 0) := by
  have h := tendsto_inv_one_add_sq_atTop.comp tendsto_neg_atBot_atTop
  refine h.congr fun t ↦ ?_
  simp [Function.comp]

/-- `M/(1 + t²)` squared is at most `M² (1 + t²)⁻¹`. -/
theorem sq_div_one_add_sq_le {M t : ℝ} : (M / (1 + t ^ 2)) ^ 2 ≤ M ^ 2 * (1 + t ^ 2)⁻¹ := by
  have h1 : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  rw [div_pow]
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  nlinarith

/-- `(α − |σ|)^{−s}` is integrable on `[−α, α]` for `s < 1`. -/
theorem intervalIntegrable_stripWeight_abs_neg {α s : ℝ} (hα : 0 < α) (hs1 : s < 1) :
    IntervalIntegrable (fun σ : ℝ ↦ (α - |σ|) ^ (-s)) MeasureTheory.volume (-α) α := by
  have hR : IntervalIntegrable (fun σ : ℝ ↦ (α - |σ|) ^ (-s)) MeasureTheory.volume 0 α := by
    refine (intervalIntegrable_stripWeight_neg (α := α) hs1).congr ?_
    rw [uIoc_of_le hα.le]
    intro x (hx : x ∈ Ioc 0 α)
    simp only [abs_of_pos hx.1]
  have hL : IntervalIntegrable (fun σ : ℝ ↦ (α - |σ|) ^ (-s)) MeasureTheory.volume (-α) 0 := by
    have h := hR.comp_mul_left (c := -1)
    simp only [neg_mul, one_mul, abs_neg, div_neg, div_one, neg_zero] at h
    exact h.symm
  exact hL.trans hR

/-- **Fubini on the strip.** If `F` is continuous on `(−α, α) × ℝ` and
`|F σ t| ≤ G σ (1 + t²)⁻¹` with `G` integrable on `[−α, α]`, the iterated integrals agree, and
`t ↦ ∫ F σ t dσ` is integrable. -/
theorem stripFubini {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ ↦ F p.1 p.2) (Ioo (-α) α ×ˢ univ)) {G : ℝ → ℝ}
    (hG : IntervalIntegrable G MeasureTheory.volume (-α) α)
    (hb : ∀ σ ∈ Ioo (-α) α, ∀ t : ℝ, |F σ t| ≤ G σ * (1 + t ^ 2)⁻¹) :
    (∫ σ in (-α)..α, ∫ t : ℝ, F σ t) = (∫ t : ℝ, ∫ σ in (-α)..α, F σ t) ∧
      MeasureTheory.Integrable fun t : ℝ ↦ ∫ σ in (-α)..α, F σ t := by
  have hαα : -α ≤ α := by linarith
  set μ := MeasureTheory.volume.restrict (Ioo (-α) α) with hμ
  have hG' : MeasureTheory.Integrable G μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hαα).mp hG
  have hprod : μ.prod (MeasureTheory.volume : MeasureTheory.Measure ℝ) =
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)).restrict (Ioo (-α) α ×ˢ univ) := by
    rw [hμ, ← MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_univ]
  have hmeas : MeasurableSet (Ioo (-α) α ×ˢ (univ : Set ℝ)) := measurableSet_Ioo.prod MeasurableSet.univ
  have hint : MeasureTheory.Integrable (Function.uncurry F)
      (μ.prod (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    refine (hG'.mul_prod integrable_inv_one_add_sq).mono' ?_ ?_
    · rw [hprod]
      exact hF.aestronglyMeasurable hmeas
    · rw [hprod]
      refine (MeasureTheory.ae_restrict_mem hmeas).mono fun p hp ↦ ?_
      rw [Real.norm_eq_abs]
      exact hb p.1 hp.1 p.2
  have hI (f : ℝ → ℝ) : ∫ σ in (-α)..α, f σ = ∫ σ, f σ ∂μ := by
    rw [intervalIntegral.integral_of_le hαα, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  constructor
  · rw [hI]
    simp_rw [hI]
    exact MeasureTheory.integral_integral_swap hint
  · simp_rw [hI]
    exact hint.integral_prod_right

/-! ### Carleson's formula on the strip, assembled -/

/-- **Carleson's formula on the strip, with the weight `(α − |σ|)^{1−s}`.** Let `B` be bounded by
one on the open strip `S = {|Re z| < α}`, with defect `1 − ‖B‖² ≤ C (α − |Re z|)`, `‖B'‖ ≤ C` and
`‖B''‖ ≤ C/(α − |Re z|)`, and let `g`, `g'`, `g''` decay like `1/(1 + t²)`. Then
`∬ (‖(Bg)'‖² − ‖g'‖²) w = ½(1 − s)α^{−s} ∫ (1 − ‖B(it)‖²)‖g(it)‖² dt
  + ¼ s(1 − s) ∬ (1 − ‖B‖²)‖g‖² (α − |σ|)^{−s−1}`. -/
theorem stripCarleson {α s : ℝ} (hα : 0 < α) (hs0 : 0 ≤ s) (hs1 : s < 1) {B g : ℂ → ℂ}
    (hB : DifferentiableOn ℂ B {z : ℂ | |z.re| < α}) (hg : DifferentiableOn ℂ g {z : ℂ | |z.re| < α})
    {C M : ℝ}
    (hB0 : ∀ z : ℂ, |z.re| < α → ‖B z‖ ≤ 1)
    (hBd : ∀ z : ℂ, |z.re| < α → 1 - ‖B z‖ ^ 2 ≤ C * (α - |z.re|))
    (hB1 : ∀ z : ℂ, |z.re| < α → ‖deriv B z‖ ≤ C)
    (hB2 : ∀ z : ℂ, |z.re| < α → ‖deriv (deriv B) z‖ ≤ C / (α - |z.re|))
    (hg0 : ∀ z : ℂ, |z.re| < α → ‖g z‖ ≤ M / (1 + z.im ^ 2))
    (hg1 : ∀ z : ℂ, |z.re| < α → ‖deriv g z‖ ≤ M / (1 + z.im ^ 2))
    (hg2 : ∀ z : ℂ, |z.re| < α → ‖deriv (deriv g) z‖ ≤ M / (1 + z.im ^ 2)) :
    ∫ σ in (-α)..α, (∫ t : ℝ, (‖deriv (fun z ↦ B z * g z) (σ + t * I)‖ ^ 2 -
        ‖deriv g (σ + t * I)‖ ^ 2)) * (α - |σ|) ^ (1 - s) =
      (1 - s) / 2 * α ^ (-s) * (∫ t : ℝ, (1 - ‖B (t * I)‖ ^ 2) * ‖g (t * I)‖ ^ 2) +
        s * (1 - s) / 4 * ∫ σ in (-α)..α,
          (∫ t : ℝ, (1 - ‖B (σ + t * I)‖ ^ 2) * ‖g (σ + t * I)‖ ^ 2) * (α - |σ|) ^ (-s - 1) := by
  set H : ℂ → ℂ := fun z ↦ B z * g z with hH
  -- the pointwise quantities on the line through `σ + t I`
  let Ph (h : ℂ → ℂ) (σ t : ℝ) : ℝ := 2 * ‖deriv h (σ + t * I)‖ ^ 2 +
    2 * inner ℝ (h (σ + t * I)) (deriv (deriv h) (σ + t * I))
  let Qh (h : ℂ → ℂ) (σ t : ℝ) : ℝ := 2 * ‖deriv h (σ + t * I)‖ ^ 2 -
    2 * inner ℝ (h (σ + t * I)) (deriv (deriv h) (σ + t * I))
  let P (σ t : ℝ) : ℝ := Ph H σ t - Ph g σ t
  let Q (σ t : ℝ) : ℝ := Qh H σ t - Qh g σ t
  let E (σ t : ℝ) : ℝ := ‖deriv H (σ + t * I)‖ ^ 2 - ‖deriv g (σ + t * I)‖ ^ 2
  let u (σ t : ℝ) : ℝ := ‖H (σ + t * I)‖ ^ 2 - ‖g (σ + t * I)‖ ^ 2
  let w (σ : ℝ) : ℝ := (α - |σ|) ^ (1 - s)
  let w₂ (σ : ℝ) : ℝ := -(s * (1 - s) * (α - |σ|) ^ (-s - 1))
  have hE (σ t : ℝ) : E σ t = (P σ t + Q σ t) / 4 := by
    simp only [E, P, Q, Ph, Qh]
    ring
  have hu (σ t : ℝ) : u σ t = -((1 - ‖B (σ + t * I)‖ ^ 2) * ‖g (σ + t * I)‖ ^ 2) := by
    simp only [u, hH, norm_mul, mul_pow]
    ring
  -- common facts
  have hU := isOpen_strip α
  have hHd : DifferentiableOn ℂ H {z : ℂ | |z.re| < α} := hB.mul hg
  have hmem {σ t : ℝ} (hσ : σ ∈ Ioo (-α) α) : |((σ : ℂ) + t * I).re| < α := by
    simpa [abs_lt] using hσ
  have him (σ t : ℝ) : ((σ : ℂ) + t * I).im = t := by simp
  have hre (σ t : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp
  have cont3 {h : ℂ → ℂ} (hd : DifferentiableOn ℂ h {z : ℂ | |z.re| < α}) :
      ContinuousOn h {z : ℂ | |z.re| < α} ∧ ContinuousOn (deriv h) {z : ℂ | |z.re| < α} ∧
        ContinuousOn (deriv (deriv h)) {z : ℂ | |z.re| < α} :=
    ⟨hd.continuousOn, (hd.deriv hU).continuousOn, ((hd.deriv hU).deriv hU).continuousOn⟩
  have hM : 0 ≤ M := by
    have := hg0 0 (by simpa using hα)
    simpa using (norm_nonneg _).trans this
  have hC : 0 ≤ C := (norm_nonneg _).trans (hB1 0 (by simpa using hα))
  -- pointwise bounds on the line `σ + t I`
  have bH {σ t : ℝ} (hσ : σ ∈ Ioo (-α) α) :=
    norm_mul_strip_bounds hB hg hB0 hB1 hB2 hg0 hg1 hg2 (hmem (t := t) hσ)
  let A (σ : ℝ) : ℝ := M ^ 2 * (2 * (C + 1) ^ 2 + 2 * (C / (α - |σ|) + 2 * C + 1) + 4)
  have hPhH : ∀ σ ∈ Ioo (-α) α, ∀ t : ℝ,
      |Ph H σ t| ≤ M ^ 2 * (2 * (C + 1) ^ 2 + 2 * (C / (α - |σ|) + 2 * C + 1)) * (1 + t ^ 2)⁻¹ ∧
      |Qh H σ t| ≤ M ^ 2 * (2 * (C + 1) ^ 2 + 2 * (C / (α - |σ|) + 2 * C + 1)) * (1 + t ^ 2)⁻¹ := by
    intro σ hσ t
    obtain ⟨b0, b1, b2⟩ := bH (t := t) hσ
    simp only [him, hre] at b0 b1 b2
    have hd : 0 < α - |σ| := by have := abs_lt.mpr hσ; linarith
    have hc1 : 0 ≤ C / (α - |σ|) + 2 * C + 1 := by positivity
    have hD : 0 ≤ M / (1 + t ^ 2) := by positivity
    have key : 2 * ‖deriv H (σ + t * I)‖ ^ 2 + 2 * (‖H (σ + t * I)‖ * ‖deriv (deriv H) (σ + t * I)‖) ≤
        (2 * (C + 1) ^ 2 + 2 * (C / (α - |σ|) + 2 * C + 1)) * (M / (1 + t ^ 2)) ^ 2 := by
      have e1 : ‖deriv H (σ + t * I)‖ ^ 2 ≤ ((C + 1) * (M / (1 + t ^ 2))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) b1 2
      have e2 : ‖H (σ + t * I)‖ * ‖deriv (deriv H) (σ + t * I)‖ ≤
          (M / (1 + t ^ 2)) * ((C / (α - |σ|) + 2 * C + 1) * (M / (1 + t ^ 2))) :=
        mul_le_mul b0 b2 (norm_nonneg _) hD
      nlinarith
    have hsq := sq_div_one_add_sq_le (M := M) (t := t)
    have hcoef : 0 ≤ 2 * (C + 1) ^ 2 + 2 * (C / (α - |σ|) + 2 * C + 1) := by positivity
    have final : (2 * (C + 1) ^ 2 + 2 * (C / (α - |σ|) + 2 * C + 1)) * (M / (1 + t ^ 2)) ^ 2 ≤
        M ^ 2 * (2 * (C + 1) ^ 2 + 2 * (C / (α - |σ|) + 2 * C + 1)) * (1 + t ^ 2)⁻¹ := by
      nlinarith [mul_le_mul_of_nonneg_left hsq hcoef]
    obtain ⟨i1, i2⟩ := abs_two_sq_add_two_inner_le (H (σ + t * I)) (deriv H (σ + t * I))
      (deriv (deriv H) (σ + t * I))
    exact ⟨i1.trans (key.trans final), i2.trans (key.trans final)⟩
  have hPhg : ∀ σ ∈ Ioo (-α) α, ∀ t : ℝ,
      |Ph g σ t| ≤ M ^ 2 * 4 * (1 + t ^ 2)⁻¹ ∧ |Qh g σ t| ≤ M ^ 2 * 4 * (1 + t ^ 2)⁻¹ := by
    intro σ hσ t
    have b0 := hg0 _ (hmem (t := t) hσ)
    have b1 := hg1 _ (hmem (t := t) hσ)
    have b2 := hg2 _ (hmem (t := t) hσ)
    rw [him] at b0 b1 b2
    have hD : 0 ≤ M / (1 + t ^ 2) := by positivity
    have key : 2 * ‖deriv g (σ + t * I)‖ ^ 2 + 2 * (‖g (σ + t * I)‖ * ‖deriv (deriv g) (σ + t * I)‖) ≤
        4 * (M / (1 + t ^ 2)) ^ 2 := by
      have e1 : ‖deriv g (σ + t * I)‖ ^ 2 ≤ (M / (1 + t ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) b1 2
      have e2 := mul_le_mul b0 b2 (norm_nonneg _) hD
      nlinarith
    have hsq := sq_div_one_add_sq_le (M := M) (t := t)
    obtain ⟨i1, i2⟩ := abs_two_sq_add_two_inner_le (g (σ + t * I)) (deriv g (σ + t * I))
      (deriv (deriv g) (σ + t * I))
    exact ⟨i1.trans (key.trans (by nlinarith)), i2.trans (key.trans (by nlinarith))⟩
  have hPQb : ∀ σ ∈ Ioo (-α) α, ∀ t : ℝ, |P σ t| ≤ A σ * (1 + t ^ 2)⁻¹ ∧ |Q σ t| ≤ A σ * (1 + t ^ 2)⁻¹ := by
    intro σ hσ t
    obtain ⟨a1, a2⟩ := hPhH σ hσ t
    obtain ⟨c1, c2⟩ := hPhg σ hσ t
    constructor
    · calc |P σ t| ≤ |Ph H σ t| + |Ph g σ t| := abs_sub _ _
        _ ≤ A σ * (1 + t ^ 2)⁻¹ := by simp only [A]; nlinarith
    · calc |Q σ t| ≤ |Qh H σ t| + |Qh g σ t| := abs_sub _ _
        _ ≤ A σ * (1 + t ^ 2)⁻¹ := by simp only [A]; nlinarith
  -- continuity along vertical lines
  have contV {h : ℂ → ℂ} (hd : DifferentiableOn ℂ h {z : ℂ | |z.re| < α}) {σ : ℝ} (hσ : σ ∈ Ioo (-α) α) :
      Continuous (Ph h σ) ∧ Continuous (Qh h σ) := by
    obtain ⟨c0, c1, c2⟩ := cont3 hd
    have hσ' : |σ| < α := abs_lt.mpr hσ
    have k0 := continuous_im_line c0 hσ'
    have k1 := continuous_im_line c1 hσ'
    have k2 := continuous_im_line c2 hσ'
    exact ⟨(continuous_const.mul (k1.norm.pow 2)).add (continuous_const.mul (k0.inner k2)),
      (continuous_const.mul (k1.norm.pow 2)).sub (continuous_const.mul (k0.inner k2))⟩
  have hint_of_bound {F : ℝ → ℝ} (hF : Continuous F) {K : ℝ} (hb : ∀ t, |F t| ≤ K * (1 + t ^ 2)⁻¹) :
      MeasureTheory.Integrable F :=
    (integrable_inv_one_add_sq.const_mul K).mono' hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t ↦ by rw [Real.norm_eq_abs]; exact hb t)
  -- integrability in `t` of `P` and `Q` on every vertical line
  have hPi : ∀ σ ∈ Ioo (-α) α, MeasureTheory.Integrable (P σ) := fun σ hσ ↦
    hint_of_bound (((contV hHd hσ).1).sub ((contV hg hσ).1)) fun t ↦ (hPQb σ hσ t).1
  have hQi : ∀ σ ∈ Ioo (-α) α, MeasureTheory.Integrable (Q σ) := fun σ hσ ↦
    hint_of_bound (((contV hHd hσ).2).sub ((contV hg hσ).2)) fun t ↦ (hPQb σ hσ t).2
  -- (a) on every vertical line the second vertical derivative integrates to zero
  have hQ : ∀ σ ∈ Ioo (-α) α, ∫ t : ℝ, Q σ t = 0 := by
    intro σ hσ
    have hline (t : ℝ) : (σ : ℂ) + t * I ∈ {z : ℂ | |z.re| < α} := hmem hσ
    have lim {h : ℂ → ℂ} {K : ℝ} (hb : ∀ t : ℝ, ‖h (σ + t * I)‖ * ‖deriv h (σ + t * I)‖ ≤ K * (1 + t ^ 2)⁻¹) :
        Tendsto (fun t : ℝ ↦ 2 * inner ℝ (h (σ + t * I)) (deriv h (σ + t * I) * I)) atBot (𝓝 0) ∧
        Tendsto (fun t : ℝ ↦ 2 * inner ℝ (h (σ + t * I)) (deriv h (σ + t * I) * I)) atTop (𝓝 0) := by
      have bd (t : ℝ) : ‖2 * inner ℝ (h (σ + t * I)) (deriv h (σ + t * I) * I)‖ ≤ 2 * K * (1 + t ^ 2)⁻¹ := by
        rw [Real.norm_eq_abs, abs_mul, abs_two]
        have := abs_real_inner_le_norm (h (σ + t * I)) (deriv h (σ + t * I) * I)
        rw [norm_mul, norm_I, mul_one] at this
        nlinarith [hb t]
      constructor
      · exact squeeze_zero_norm bd (by simpa using tendsto_inv_one_add_sq_atBot.const_mul (2 * K))
      · exact squeeze_zero_norm bd (by simpa using tendsto_inv_one_add_sq_atTop.const_mul (2 * K))
    have bHH (t : ℝ) : ‖H (σ + t * I)‖ * ‖deriv H (σ + t * I)‖ ≤ (C + 1) * M ^ 2 * (1 + t ^ 2)⁻¹ := by
      obtain ⟨b0, b1, -⟩ := bH (t := t) hσ
      rw [him] at b0 b1
      have := mul_le_mul b0 b1 (norm_nonneg _) (by positivity)
      have hsq := sq_div_one_add_sq_le (M := M) (t := t)
      nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ C + 1)]
    have bgg (t : ℝ) : ‖g (σ + t * I)‖ * ‖deriv g (σ + t * I)‖ ≤ M ^ 2 * (1 + t ^ 2)⁻¹ := by
      have b0 := hg0 _ (hmem (t := t) hσ)
      have b1 := hg1 _ (hmem (t := t) hσ)
      rw [him] at b0 b1
      have := mul_le_mul b0 b1 (norm_nonneg _) (by positivity)
      have hsq := sq_div_one_add_sq_le (M := M) (t := t)
      nlinarith
    have hH0 := integral_im_line_secondDeriv_eq_zero hHd hU hline
      (hint_of_bound (contV hHd hσ).2 fun t ↦ (hPhH σ hσ t).2) (lim bHH).1 (lim bHH).2
    have hg0' := integral_im_line_secondDeriv_eq_zero hg hU hline
      (hint_of_bound (contV hg hσ).2 fun t ↦ (hPhg σ hσ t).2) (lim bgg).1 (lim bgg).2
    show ∫ t : ℝ, (Qh H σ t - Qh g σ t) = 0
    rw [MeasureTheory.integral_sub (hint_of_bound (contV hHd hσ).2 fun t ↦ (hPhH σ hσ t).2)
      (hint_of_bound (contV hg hσ).2 fun t ↦ (hPhg σ hσ t).2)]
    simp only [Qh]
    rw [hH0, hg0', sub_zero]
  -- (b) hence `∫ E = ¼ ∫ P` on every vertical line
  have hEP : ∀ σ ∈ Ioo (-α) α, ∫ t : ℝ, E σ t = (∫ t : ℝ, P σ t) / 4 := by
    intro σ hσ
    simp_rw [hE]
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add (hPi σ hσ) (hQi σ hσ), hQ σ hσ,
      add_zero]
  -- (c) integration by parts in `σ` on every horizontal line
  have hIBP : ∀ t : ℝ, ∫ σ in (-α)..α, P σ t * w σ =
      -(2 * u 0 t * ((1 - s) * α ^ (-s))) + ∫ σ in (-α)..α, u σ t * w₂ σ := by
    intro t
    -- continuity along the horizontal line
    have cH (h : ℂ → ℂ) (hd : DifferentiableOn ℂ h {z : ℂ | |z.re| < α}) :
        ContinuousOn (fun σ : ℝ ↦ Ph h σ t) (Ioo (-α) α) := by
      obtain ⟨c0, c1, c2⟩ := cont3 hd
      have k0 := continuousOn_re_line (t := t) c0
      have k1 := continuousOn_re_line (t := t) c1
      have k2 := continuousOn_re_line (t := t) c2
      exact (continuousOn_const.mul (k1.norm.pow 2)).add (continuousOn_const.mul (k0.inner k2))
    have hPc : ContinuousOn (fun σ : ℝ ↦ P σ t) (Ioo (-α) α) := (cH H hHd).sub (cH g hg)
    have hwc : ContinuousOn w (Ioo (-α) α) := by
      intro σ hσ
      have : α - |σ| ≠ 0 := by have := abs_lt.mpr hσ; linarith
      exact ((continuousAt_const.sub continuous_abs.continuousAt).rpow_const
        (Or.inl this)).continuousWithinAt
    -- the constant for the hypotheses on `u` and its first derivative
    set C₀ := C * M ^ 2 + 2 * (C + 1) * M ^ 2 + 2 * M ^ 2 with hC₀
    have hDle : M / (1 + t ^ 2) ≤ M := div_le_self hM (by nlinarith [sq_nonneg t])
    refine stripWeight_ibp_symm hα hs0 hs1 (f := fun σ ↦ u σ t)
      (f' := fun σ ↦ 2 * inner ℝ (H (σ + t * I)) (deriv H (σ + t * I)) -
        2 * inner ℝ (g (σ + t * I)) (deriv g (σ + t * I)))
      (f'' := fun σ ↦ P σ t)
      (fun x hx ↦ ((hasDerivAt_re_line_normSq hHd hU (hmem hx)).1).sub
        ((hasDerivAt_re_line_normSq hg hU (hmem hx)).1))
      (fun x hx ↦ ((hasDerivAt_re_line_normSq hHd hU (hmem hx)).2).sub
        ((hasDerivAt_re_line_normSq hg hU (hmem hx)).2))
      hPc (C := C₀) ?_ ?_ ?_
    · -- `|u| ≤ C₀ (α − |σ|)`
      intro x hx
      have hz := hmem (t := t) hx
      have hd : 0 ≤ α - |x| := by have := abs_lt.mpr hx; linarith
      have c0 := hg0 _ hz
      simp only [him] at c0
      have hgM : ‖g (x + t * I)‖ ≤ M := c0.trans hDle
      have hdef := hBd _ hz
      simp only [hre] at hdef
      have hB1' : 0 ≤ 1 - ‖B (x + t * I)‖ ^ 2 := by
        nlinarith [hB0 _ hz, norm_nonneg (B (x + t * I))]
      rw [show u x t = -((1 - ‖B (x + t * I)‖ ^ 2) * ‖g (x + t * I)‖ ^ 2) from hu x t, abs_neg,
        abs_of_nonneg (mul_nonneg hB1' (sq_nonneg _))]
      have hg2 : ‖g (x + t * I)‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgM 2
      calc (1 - ‖B (x + t * I)‖ ^ 2) * ‖g (x + t * I)‖ ^ 2 ≤ (C * (α - |x|)) * M ^ 2 :=
            mul_le_mul hdef hg2 (sq_nonneg _) (by positivity)
        _ ≤ C₀ * (α - |x|) := by
            rw [hC₀]
            nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * (C + 1) + 2) (sq_nonneg M)) hd]
    · -- `|f'| ≤ C₀`
      intro x hx
      obtain ⟨b0, b1, -⟩ := bH (t := t) hx
      have c0 := hg0 _ (hmem (t := t) hx)
      have c1 := hg1 _ (hmem (t := t) hx)
      simp only [him] at b0 b1 c0 c1
      have i1 := abs_real_inner_le_norm (H (x + t * I)) (deriv H (x + t * I))
      have i2 := abs_real_inner_le_norm (g (x + t * I)) (deriv g (x + t * I))
      have p1 : ‖H (x + t * I)‖ * ‖deriv H (x + t * I)‖ ≤ M * ((C + 1) * M) :=
        mul_le_mul (b0.trans hDle) (b1.trans (by nlinarith)) (norm_nonneg _) hM
      have p2 : ‖g (x + t * I)‖ * ‖deriv g (x + t * I)‖ ≤ M * M :=
        mul_le_mul (c0.trans hDle) (c1.trans hDle) (norm_nonneg _) hM
      rw [abs_le]
      constructor <;> nlinarith [abs_le.mp i1, abs_le.mp i2, mul_nonneg hC (sq_nonneg M)]
    · -- integrability of `P · w` on `(−α, α)`
      set K := (1 + t ^ 2)⁻¹ with hK
      have hK0 : 0 ≤ K := by positivity
      have hg := ((intervalIntegrable_stripWeight_abs_neg hα hs1).const_mul (K * (2 * M ^ 2 * C))).add
        (intervalIntegrable_const (c := K * (M ^ 2 * (2 * (C + 1) ^ 2 + 4 * C + 6) * α ^ (1 - s))))
      refine hg.mono_fun' ?_ ?_
      · rw [uIoc_of_le (by linarith), MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm]
        exact (hPc.mul hwc).aestronglyMeasurable measurableSet_Ioo
      · rw [uIoc_of_le (by linarith), MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc.symm]
        refine (MeasureTheory.ae_restrict_mem measurableSet_Ioo).mono fun σ hσ ↦ ?_
        have hd : 0 < α - |σ| := by have := abs_lt.mpr hσ; linarith
        have hb := (hPQb σ hσ t).1
        have hw0 : 0 ≤ w σ := Real.rpow_nonneg hd.le _
        have hwα : w σ ≤ α ^ (1 - s) :=
          Real.rpow_le_rpow hd.le (by linarith [abs_nonneg σ]) (by linarith)
        have hwd : w σ / (α - |σ|) = (α - |σ|) ^ (-s) := by
          simp only [w]
          rw [div_eq_iff hd.ne', ← Real.rpow_add_one hd.ne']
          ring_nf
        dsimp only
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw0]
        have hA : A σ * w σ = M ^ 2 * (2 * (C + 1) ^ 2 + 4 * C + 6) * w σ +
            2 * M ^ 2 * C * (w σ / (α - |σ|)) := by
          simp only [A]
          field_simp
          ring
        calc |P σ t| * w σ ≤ A σ * K * w σ := mul_le_mul_of_nonneg_right hb hw0
          _ = K * (A σ * w σ) := by ring
          _ = K * (M ^ 2 * (2 * (C + 1) ^ 2 + 4 * C + 6) * w σ) +
                K * (2 * M ^ 2 * C) * (α - |σ|) ^ (-s) := by rw [hA, hwd]; ring
          _ ≤ K * (M ^ 2 * (2 * (C + 1) ^ 2 + 4 * C + 6) * α ^ (1 - s)) +
                K * (2 * M ^ 2 * C) * (α - |σ|) ^ (-s) := by
              gcongr
          _ = _ := by ring
  -- (d), (e) Fubini
  have hd_of {σ : ℝ} (hσ : σ ∈ Ioo (-α) α) : 0 < α - |σ| := by have := abs_lt.mpr hσ; linarith
  have hwc : ContinuousOn w (Ioo (-α) α) := by
    intro σ hσ
    exact ((continuousAt_const.sub continuous_abs.continuousAt).rpow_const
      (Or.inl (hd_of hσ).ne')).continuousWithinAt
  have hw₂c : ContinuousOn w₂ (Ioo (-α) α) := by
    intro σ hσ
    exact ((((continuousAt_const.sub continuous_abs.continuousAt).rpow_const
      (Or.inl (hd_of hσ).ne')).const_mul (s * (1 - s))).neg).continuousWithinAt
  have hfst {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo (-α) α)) :
      ContinuousOn (fun p : ℝ × ℝ ↦ f p.1) (Ioo (-α) α ×ˢ univ) :=
    hf.comp continuousOn_fst fun p hp ↦ hp.1
  have cS (h : ℂ → ℂ) (hd : DifferentiableOn ℂ h {z : ℂ | |z.re| < α}) :
      ContinuousOn (fun p : ℝ × ℝ ↦ Ph h p.1 p.2) (Ioo (-α) α ×ˢ univ) ∧
        ContinuousOn (fun p : ℝ × ℝ ↦ ‖h (p.1 + p.2 * I)‖ ^ 2) (Ioo (-α) α ×ˢ univ) := by
    obtain ⟨c0, c1, c2⟩ := cont3 hd
    have k0 := continuousOn_strip_coords c0
    have k1 := continuousOn_strip_coords c1
    have k2 := continuousOn_strip_coords c2
    exact ⟨(continuousOn_const.mul (k1.norm.pow 2)).add (continuousOn_const.mul (k0.inner k2)),
      k0.norm.pow 2⟩
  -- the bound for `P w`
  set c₁ := M ^ 2 * (2 * (C + 1) ^ 2 + 4 * C + 6) * α ^ (1 - s) with hc₁
  have hPw : ∀ σ ∈ Ioo (-α) α, ∀ t : ℝ,
      |P σ t * w σ| ≤ (c₁ + 2 * M ^ 2 * C * (α - |σ|) ^ (-s)) * (1 + t ^ 2)⁻¹ := by
    intro σ hσ t
    have hd := hd_of hσ
    have hb := (hPQb σ hσ t).1
    have hw0 : 0 ≤ w σ := Real.rpow_nonneg hd.le _
    have hwα : w σ ≤ α ^ (1 - s) :=
      Real.rpow_le_rpow hd.le (by linarith [abs_nonneg σ]) (by linarith)
    have hwd : w σ / (α - |σ|) = (α - |σ|) ^ (-s) := by
      simp only [w]
      rw [div_eq_iff hd.ne', ← Real.rpow_add_one hd.ne']
      ring_nf
    have hK0 : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    have hA : A σ * w σ = M ^ 2 * (2 * (C + 1) ^ 2 + 4 * C + 6) * w σ +
        2 * M ^ 2 * C * (w σ / (α - |σ|)) := by
      simp only [A]
      field_simp
      ring
    rw [abs_mul, abs_of_nonneg hw0]
    calc |P σ t| * w σ ≤ A σ * (1 + t ^ 2)⁻¹ * w σ := mul_le_mul_of_nonneg_right hb hw0
      _ = (M ^ 2 * (2 * (C + 1) ^ 2 + 4 * C + 6) * w σ +
            2 * M ^ 2 * C * (α - |σ|) ^ (-s)) * (1 + t ^ 2)⁻¹ := by rw [mul_right_comm, hA, hwd]
      _ ≤ (c₁ + 2 * M ^ 2 * C * (α - |σ|) ^ (-s)) * (1 + t ^ 2)⁻¹ := by
          gcongr
          rw [hc₁]
          exact mul_le_mul_of_nonneg_left hwα (by positivity)
  have hG₁ : IntervalIntegrable (fun σ : ℝ ↦ c₁ + 2 * M ^ 2 * C * (α - |σ|) ^ (-s))
      MeasureTheory.volume (-α) α :=
    intervalIntegrable_const.add ((intervalIntegrable_stripWeight_abs_neg hα hs1).const_mul _)
  have FubP := stripFubini hα (F := fun σ t ↦ P σ t * w σ)
    ((((cS H hHd).1).sub ((cS g hg).1)).mul (hfst hwc)) hG₁ hPw
  -- the bound for `u w₂`
  have huw : ∀ σ ∈ Ioo (-α) α, ∀ t : ℝ,
      |u σ t * w₂ σ| ≤ (C * M ^ 2 * (s * (1 - s)) * (α - |σ|) ^ (-s)) * (1 + t ^ 2)⁻¹ := by
    intro σ hσ t
    have hd := hd_of hσ
    have hz := hmem (t := t) hσ
    have c0 := hg0 _ hz
    simp only [him] at c0
    have hdef := hBd _ hz
    simp only [hre] at hdef
    have hB1' : 0 ≤ 1 - ‖B (σ + t * I)‖ ^ 2 := by nlinarith [hB0 _ hz, norm_nonneg (B (σ + t * I))]
    have hg2 : ‖g (σ + t * I)‖ ^ 2 ≤ M ^ 2 * (1 + t ^ 2)⁻¹ :=
      (pow_le_pow_left₀ (norm_nonneg _) c0 2).trans sq_div_one_add_sq_le
    have hss : 0 ≤ s * (1 - s) := mul_nonneg hs0 (by linarith)
    have hw₂ : |w₂ σ| = s * (1 - s) * (α - |σ|) ^ (-s - 1) := by
      simp only [w₂, abs_neg]
      exact abs_of_nonneg (mul_nonneg hss (Real.rpow_nonneg hd.le _))
    have hsplit : (α - |σ|) * (α - |σ|) ^ (-s - 1) = (α - |σ|) ^ (-s) := by
      have h := Real.rpow_add hd 1 (-s - 1)
      rw [Real.rpow_one, show (1 : ℝ) + (-s - 1) = -s by ring] at h
      exact h.symm
    rw [abs_mul, hw₂, hu, abs_neg, abs_of_nonneg (mul_nonneg hB1' (sq_nonneg _))]
    have hK0 : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    calc (1 - ‖B (σ + t * I)‖ ^ 2) * ‖g (σ + t * I)‖ ^ 2 * (s * (1 - s) * (α - |σ|) ^ (-s - 1))
        ≤ (C * (α - |σ|)) * (M ^ 2 * (1 + t ^ 2)⁻¹) * (s * (1 - s) * (α - |σ|) ^ (-s - 1)) := by
          gcongr
      _ = C * M ^ 2 * (s * (1 - s)) * ((α - |σ|) * (α - |σ|) ^ (-s - 1)) * (1 + t ^ 2)⁻¹ := by ring
      _ = _ := by rw [hsplit]
  have hG₂ : IntervalIntegrable (fun σ : ℝ ↦ C * M ^ 2 * (s * (1 - s)) * (α - |σ|) ^ (-s))
      MeasureTheory.volume (-α) α :=
    (intervalIntegrable_stripWeight_abs_neg hα hs1).const_mul _
  have Fubu := stripFubini hα (F := fun σ t ↦ u σ t * w₂ σ)
    ((((cS H hHd).2).sub ((cS g hg).2)).mul (hfst hw₂c)) hG₂ huw
  have hF1 : ∫ σ in (-α)..α, (∫ t : ℝ, P σ t) * w σ = ∫ t : ℝ, ∫ σ in (-α)..α, P σ t * w σ := by
    rw [← FubP.1]
    apply intervalIntegral.integral_congr
    intro σ _
    exact (MeasureTheory.integral_mul_const _ _).symm
  have hF2 : ∫ t : ℝ, ∫ σ in (-α)..α, u σ t * w₂ σ = ∫ σ in (-α)..α, (∫ t : ℝ, u σ t) * w₂ σ := by
    rw [← Fubu.1]
    apply intervalIntegral.integral_congr
    intro σ _
    exact MeasureTheory.integral_mul_const _ _
  -- (f) integrability in `t` of the two terms on the right
  -- bounds and continuity for `u`
  have hub : ∀ σ ∈ Ioo (-α) α, ∀ t : ℝ, |u σ t| ≤ 2 * M ^ 2 * (1 + t ^ 2)⁻¹ := by
    intro σ hσ t
    obtain ⟨b0, -, -⟩ := bH (t := t) hσ
    have c0 := hg0 _ (hmem (t := t) hσ)
    simp only [him] at b0 c0
    have e1 := pow_le_pow_left₀ (norm_nonneg _) b0 2
    have e2 := pow_le_pow_left₀ (norm_nonneg _) c0 2
    have hsq := sq_div_one_add_sq_le (M := M) (t := t)
    have : |u σ t| ≤ ‖H (σ + t * I)‖ ^ 2 + ‖g (σ + t * I)‖ ^ 2 := by
      simp only [u]
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg ‖H (σ + t * I)‖, sq_nonneg ‖g (σ + t * I)‖]
    linarith
  have hu_contV {σ : ℝ} (hσ : σ ∈ Ioo (-α) α) : Continuous (u σ) :=
    ((continuous_im_line (cont3 hHd).1 (abs_lt.mpr hσ)).norm.pow 2).sub
      ((continuous_im_line (cont3 hg).1 (abs_lt.mpr hσ)).norm.pow 2)
  have h0 : (0 : ℝ) ∈ Ioo (-α) α := ⟨by linarith, hα⟩
  have hK : MeasureTheory.Integrable fun t : ℝ ↦ -(2 * u 0 t * ((1 - s) * α ^ (-s))) := by
    refine hint_of_bound (K := 4 * M ^ 2 * |(1 - s) * α ^ (-s)|)
      (((continuous_const.mul (hu_contV h0)).mul continuous_const).neg) fun t ↦ ?_
    rw [abs_neg, abs_mul, abs_mul, abs_two]
    have := hub 0 h0 t
    have hk := abs_nonneg ((1 - s) * α ^ (-s))
    nlinarith [mul_le_mul_of_nonneg_right this hk]
  have hU : MeasureTheory.Integrable fun t : ℝ ↦ ∫ σ in (-α)..α, u σ t * w₂ σ := Fubu.2
  -- assembly
  have hL : ∫ σ in (-α)..α, (∫ t : ℝ, E σ t) * w σ = ∫ σ in (-α)..α, (∫ t : ℝ, P σ t) * w σ / 4 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(Set.countable_singleton α).ae_notMem MeasureTheory.volume] with σ hσα hσ
    rw [uIoc_of_le (by linarith)] at hσ
    have hσ' : σ ∈ Ioo (-α) α := ⟨hσ.1, lt_of_le_of_ne hσ.2 (by simpa using hσα)⟩
    rw [hEP σ hσ']
    ring
  have hstep : ∫ σ in (-α)..α, (∫ t : ℝ, E σ t) * w σ =
      (2 * ((1 - s) * α ^ (-s)) * (∫ t : ℝ, (1 - ‖B (t * I)‖ ^ 2) * ‖g (t * I)‖ ^ 2) +
        s * (1 - s) * ∫ σ in (-α)..α,
          (∫ t : ℝ, (1 - ‖B (σ + t * I)‖ ^ 2) * ‖g (σ + t * I)‖ ^ 2) * (α - |σ|) ^ (-s - 1)) / 4 := by
    have h1 : ∫ t : ℝ, -(2 * u 0 t * ((1 - s) * α ^ (-s))) =
        2 * ((1 - s) * α ^ (-s)) * ∫ t : ℝ, (1 - ‖B (t * I)‖ ^ 2) * ‖g (t * I)‖ ^ 2 := by
      have : (fun t : ℝ ↦ -(2 * u 0 t * ((1 - s) * α ^ (-s)))) =
          fun t : ℝ ↦ 2 * ((1 - s) * α ^ (-s)) * ((1 - ‖B (t * I)‖ ^ 2) * ‖g (t * I)‖ ^ 2) := by
        funext t
        rw [hu]
        simp only [Complex.ofReal_zero, zero_add]
        ring
      rw [this, MeasureTheory.integral_const_mul]
    have h2 : ∫ σ in (-α)..α, (∫ t : ℝ, u σ t) * w₂ σ = s * (1 - s) * ∫ σ in (-α)..α,
        (∫ t : ℝ, (1 - ‖B (σ + t * I)‖ ^ 2) * ‖g (σ + t * I)‖ ^ 2) * (α - |σ|) ^ (-s - 1) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro σ _
      have : ∫ t : ℝ, u σ t = -∫ t : ℝ, (1 - ‖B (σ + t * I)‖ ^ 2) * ‖g (σ + t * I)‖ ^ 2 := by
        simp_rw [hu]
        exact MeasureTheory.integral_neg _
      simp only [w₂]
      rw [this]
      ring
    rw [hL, intervalIntegral.integral_div, hF1,
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hIBP),
      MeasureTheory.integral_add hK hU, hF2, h1, h2]
  have hfin := hstep
  simp only [E, w] at hfin
  rw [hfin]
  ring

/-- **Carleson's formula for a finite strip Blaschke product** (Step A of the argument on #7405).
For zeros `ρ j` in the open strip, `B = stripBlaschke α ρ` and `g` with `g, g', g''` decaying
like `1/(1 + t²)` on the open strip, the weighted Dirichlet integrals satisfy
`∬ (‖(Bg)'‖² − ‖g'‖²) w = ∫ |g|² dν_B` with the positive measure
`ν_B = ½(1 − s)α^{−s}(1 − |B|²) dt` on `Re = 0` plus `¼ s(1 − s)(1 − |B|²)(α − |σ|)^{−s−1} dσ dt`. -/
theorem stripBlaschke_carleson {α s : ℝ} (hα : 0 < α) (hs0 : 0 ≤ s) (hs1 : s < 1) {n : ℕ}
    (ρ : Fin n → ℂ) (hρ : ∀ j, |(ρ j).re| < α) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g {z : ℂ | |z.re| < α}) {M : ℝ}
    (hg0 : ∀ z : ℂ, |z.re| < α → ‖g z‖ ≤ M / (1 + z.im ^ 2))
    (hg1 : ∀ z : ℂ, |z.re| < α → ‖deriv g z‖ ≤ M / (1 + z.im ^ 2))
    (hg2 : ∀ z : ℂ, |z.re| < α → ‖deriv (deriv g) z‖ ≤ M / (1 + z.im ^ 2)) :
    ∫ σ in (-α)..α, (∫ t : ℝ, (‖deriv (fun z ↦ stripBlaschke α ρ z * g z) (σ + t * I)‖ ^ 2 -
        ‖deriv g (σ + t * I)‖ ^ 2)) * (α - |σ|) ^ (1 - s) =
      (1 - s) / 2 * α ^ (-s) * (∫ t : ℝ, (1 - ‖stripBlaschke α ρ (t * I)‖ ^ 2) * ‖g (t * I)‖ ^ 2) +
        s * (1 - s) / 4 * ∫ σ in (-α)..α,
          (∫ t : ℝ, (1 - ‖stripBlaschke α ρ (σ + t * I)‖ ^ 2) * ‖g (σ + t * I)‖ ^ 2) *
            (α - |σ|) ^ (-s - 1) := by
  obtain ⟨C₀, hC₀, hdef⟩ := stripBlaschke_defect_bounds hα ρ hρ
  obtain ⟨C₁, hC₁, hd1⟩ := stripBlaschke_deriv_bound hα ρ hρ
  obtain ⟨C₂, hC₂, hd2⟩ := stripBlaschke_deriv2_bound hα ρ hρ
  set C := max C₀ (max C₁ C₂)
  have hz (z : ℂ) : z = (z.re : ℂ) + z.im * I := (Complex.re_add_im z).symm
  have hdz (z : ℂ) (hz' : |z.re| < α) := by
    have h := hdef z.re z.im hz'.le
    rw [← hz z] at h
    exact h
  refine stripCarleson hα hs0 hs1 (C := C) (M := M)
    (fun z hz' ↦ (hd1 z hz').1.differentiableWithinAt) hg ?_ ?_ ?_ ?_ hg0 hg1 hg2
  · intro z hz'
    have := (hdz z hz').1
    nlinarith [norm_nonneg (stripBlaschke α ρ z)]
  · intro z hz'
    have h2 := (hdz z hz').2
    have hcosh : 1 ≤ Real.cosh (π / (2 * α) * z.im) := Real.one_le_cosh _
    have hd : 0 ≤ α - |z.re| := by linarith
    calc 1 - ‖stripBlaschke α ρ z‖ ^ 2 ≤ C₀ * (α - |z.re|) / Real.cosh (π / (2 * α) * z.im) := h2
      _ ≤ C₀ * (α - |z.re|) := div_le_self (by positivity) hcosh
      _ ≤ C * (α - |z.re|) := by gcongr; exact le_max_left _ _
  · intro z hz'
    exact (hd1 z hz').2.trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro z hz'
    have hd : 0 < α - |z.re| := by linarith
    exact (hd2 z hz').trans (by gcongr; exact (le_max_right _ _).trans (le_max_right _ _))

end RiemannMasullo
