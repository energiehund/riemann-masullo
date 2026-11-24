module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
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

end RiemannMasullo
