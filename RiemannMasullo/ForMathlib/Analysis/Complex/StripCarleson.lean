module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
public import RiemannMasullo.ForMathlib.Analysis.Complex.Blaschke

/-! # Carleson's formula on a vertical strip: the Laplacian of `‖h‖²`

For a holomorphic function `h`, the second derivatives of `‖h‖²` along a horizontal and a
vertical line add up to `4 ‖h'‖²`. This is the identity `Δ ‖h‖² = 4 ‖h'‖²`, written with
one-variable derivatives, in the form used for Carleson's formula on a vertical strip.
-/

public section

open Complex Set Filter
open scoped Topology Real

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

end RiemannMasullo
