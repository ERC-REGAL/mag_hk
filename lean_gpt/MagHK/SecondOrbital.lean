import MagHK.Noninteracting

/-! Literal second-orbital differential equations from actual derivatives. -/
noncomputable section
namespace MagHK.SecondOrbital
open MagHK.Noninteracting
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def growthPrime (r : ℝ) : ℝ :=
  Real.exp (Real.sqrt (1 + r ^ 2) - 1) * (1 + r * profileH r)
def growthSecond (r : ℝ) : ℝ :=
  Real.exp (Real.sqrt (1 + r ^ 2) - 1) *
    (2 * profileH r + r * profileH r ^ 2 + r * profileHPrime r)

theorem growthPrime_hasDerivAt (r : ℝ) :
    HasDerivAt growthPrime (growthSecond r) r := by
  have hE : HasDerivAt (fun u : ℝ => Real.exp (Real.sqrt (1 + u ^ 2) - 1))
      (Real.exp (Real.sqrt (1 + r ^ 2) - 1) * profileH r) r :=
    HasDerivAt.exp ((radiusSqrt_hasDerivAt r).sub_const 1)
  have hD : HasDerivAt (fun u : ℝ => 1 + u * profileH u)
      (profileH r + r * profileHPrime r) r := by
    apply (((hasDerivAt_id r).mul (profileH_hasDerivAt r)).const_add 1).congr_deriv
    simp
  apply (hE.mul hD).congr_deriv
  unfold growthSecond
  ring

def boundedProduct (t r : ℝ) : ℝ := profileR r * profileF t r
def boundedProductPrime (t r : ℝ) : ℝ :=
  growthPrime r * profileF t r - profileR r * profileU t r * profileF t r
def boundedProductSecond (t r : ℝ) : ℝ :=
  (growthSecond r - 2 * growthPrime r * profileU t r +
    profileR r * (profileU t r ^ 2 - deriv (profileU t) r)) * profileF t r

theorem boundedProduct_hasDerivAt (t r : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (boundedProduct t) (boundedProductPrime t r) r := by
  have h := (profileR_hasDerivAt_regular r).mul (profileF_hasDerivAt t r ht)
  apply h.congr_deriv
  unfold boundedProductPrime growthPrime
  ring

theorem boundedProductPrime_hasDerivAt (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    HasDerivAt (boundedProductPrime t) (boundedProductSecond t r) r := by
  have hf := profileF_hasDerivAt t r (le_of_lt ht)
  have h := ((growthPrime_hasDerivAt r).mul hf).sub
    (((profileR_hasDerivAt_regular r).mul (profileU_hasDerivAt t r ht hr)).mul hf)
  apply h.congr_deriv
  unfold boundedProductSecond growthPrime
  rw [(profileU_hasDerivAt t r ht hr).deriv]
  simp only [Pi.mul_apply]
  ring

theorem boundedProduct_deriv (t : ℝ) (ht : 0 ≤ t) :
    deriv (boundedProduct t) = boundedProductPrime t :=
  funext (fun r => (boundedProduct_hasDerivAt t r ht).deriv)

/-- The exact bounded equation L_{-1}(R f_t) = 20 R f_t. -/
theorem bounded_eigen_equation (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    -deriv (deriv (boundedProduct t)) r - deriv (boundedProduct t) r / r +
      ((-1 / r + profileA t r) ^ 2 + profileV t r) * boundedProduct t r =
        20 * boundedProduct t r := by
  rw [boundedProduct_deriv t (le_of_lt ht), (boundedProductPrime_hasDerivAt t r ht hr).deriv]
  have hd : 1 + r * profileH r ≠ 0 := ne_of_gt (by have := profileH_mul_nonneg r; positivity)
  unfold boundedProductSecond boundedProductPrime boundedProduct growthPrime growthSecond
  unfold profileR profileV profileU boundedU
  field_simp
  <;> ring

/-- Scaling a twice differentiable radial eigenfunction preserves its equation. -/
theorem radial_equation_scale (f : ℝ → ℝ) (k r a v energy : ℝ)
    (hf : Differentiable ℝ f) (hfp : DifferentiableAt ℝ (deriv f) r)
    (heq : -deriv (deriv f) r - deriv f r / r + ((-1 / r + a) ^ 2 + v) * f r = energy * f r) :
    -deriv (deriv (fun u => k * f u)) r - deriv (fun u => k * f u) r / r +
      ((-1 / r + a) ^ 2 + v) * (k * f r) = energy * (k * f r) := by
  have hd : deriv (fun u => k * f u) = fun u => k * deriv f u :=
    funext (fun u => ((hf u).hasDerivAt.const_mul k).deriv)
  rw [hd, (hfp.hasDerivAt.const_mul k).deriv]
  calc
    -(k * deriv (deriv f) r) - k * deriv f r / r + ((-1 / r + a) ^ 2 + v) * (k * f r) =
        k * (-deriv (deriv f) r - deriv f r / r + ((-1 / r + a) ^ 2 + v) * f r) := by ring
    _ = energy * (k * f r) := by rw [heq]; ring

/-- The literal q_t f_t orbital, with q_t = sqrt(t) R. -/
theorem bounded_qf_eigen_equation (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    -deriv (deriv (fun u => Real.sqrt t * profileR u * profileF t u)) r -
      deriv (fun u => Real.sqrt t * profileR u * profileF t u) r / r +
      ((-1 / r + profileA t r) ^ 2 + profileV t r) * (Real.sqrt t * profileR r * profileF t r) =
        20 * (Real.sqrt t * profileR r * profileF t r) := by
  have hf : Differentiable ℝ (boundedProduct t) :=
    fun u => (boundedProduct_hasDerivAt t u (le_of_lt ht)).differentiableAt
  have hfp : DifferentiableAt ℝ (deriv (boundedProduct t)) r := by
    rw [boundedProduct_deriv t (le_of_lt ht)]
    exact (boundedProductPrime_hasDerivAt t r ht hr).differentiableAt
  have h := radial_equation_scale (boundedProduct t) (Real.sqrt t) r (profileA t r)
    (profileV t r) 20 hf hfp (bounded_eigen_equation t r ht hr)
  simpa only [boundedProduct, mul_assoc] using h

def gaussianProduct (t r : ℝ) : ℝ := r * gaussianF t r
def gaussianProductPrime (t r : ℝ) : ℝ := (1 - r * (r + gaussianA t r)) * gaussianF t r
def gaussianProductSecond (t r : ℝ) : ℝ :=
  (-2 * (r + gaussianA t r) + r * ((r + gaussianA t r) ^ 2 - (1 + gaussianAPrime t r))) * gaussianF t r

theorem gaussianProduct_hasDerivAt (t r : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (gaussianProduct t) (gaussianProductPrime t r) r := by
  have h := (hasDerivAt_id r).mul (gaussianF_hasDerivAt t r ht)
  apply h.congr_deriv
  unfold gaussianProductPrime
  simp only [one_mul, id_eq]
  ring

theorem gaussianProductPrime_hasDerivAt (t r : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (gaussianProductPrime t) (gaussianProductSecond t r) r := by
  have hU := (hasDerivAt_id r).add (gaussianA_hasDerivAt t r ht)
  have hC := (hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).mul hU)
  have h := hC.mul (gaussianF_hasDerivAt t r ht)
  apply h.congr_deriv
  unfold gaussianProductSecond
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, id_eq, one_mul]
  ring

theorem gaussianProduct_deriv (t : ℝ) (ht : 0 ≤ t) :
    deriv (gaussianProduct t) = gaussianProductPrime t :=
  funext (fun r => (gaussianProduct_hasDerivAt t r ht).deriv)

/-- The exact explicit equation L_{-1}(r f) = 2 r f. -/
theorem gaussian_eigen_equation (t r : ℝ) (ht : 0 ≤ t) (hr : r ≠ 0) :
    -deriv (deriv (gaussianProduct t)) r - deriv (gaussianProduct t) r / r +
      ((-1 / r + gaussianA t r) ^ 2 +
        (r ^ 2 - 2 / (1 + t * r ^ 2) - 2 * t / (1 + t * r ^ 2) ^ 2)) * gaussianProduct t r =
          2 * gaussianProduct t r := by
  rw [gaussianProduct_deriv t ht, (gaussianProductPrime_hasDerivAt t r ht).deriv,
    gaussian_scalar_factorization t r ht hr]
  unfold gaussianProductSecond gaussianProductPrime gaussianProduct
  field_simp
  <;> ring

theorem gaussian_qf_eigen_equation (t r : ℝ) (ht : 0 ≤ t) (hr : r ≠ 0) :
    -deriv (deriv (fun u => Real.sqrt t * u * gaussianF t u)) r -
      deriv (fun u => Real.sqrt t * u * gaussianF t u) r / r +
      ((-1 / r + gaussianA t r) ^ 2 +
        (r ^ 2 - 2 / (1 + t * r ^ 2) - 2 * t / (1 + t * r ^ 2) ^ 2)) *
          (Real.sqrt t * r * gaussianF t r) = 2 * (Real.sqrt t * r * gaussianF t r) := by
  have hf : Differentiable ℝ (gaussianProduct t) :=
    fun u => (gaussianProduct_hasDerivAt t u ht).differentiableAt
  have hfp : DifferentiableAt ℝ (deriv (gaussianProduct t)) r := by
    rw [gaussianProduct_deriv t ht]
    exact (gaussianProductPrime_hasDerivAt t r ht).differentiableAt
  have h := radial_equation_scale (gaussianProduct t) (Real.sqrt t) r (gaussianA t r)
    (r ^ 2 - 2 / (1 + t * r ^ 2) - 2 * t / (1 + t * r ^ 2) ^ 2) 2 hf hfp
    (gaussian_eigen_equation t r ht hr)
  simpa only [gaussianProduct, mul_assoc] using h

end MagHK.SecondOrbital
