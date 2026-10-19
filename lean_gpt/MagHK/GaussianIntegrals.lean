import MagHK.GaussianNormalization
import MagHK.Noninteracting
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Literal radial and axial integrals for the Gaussian orbitals. -/

noncomputable section
namespace MagHK.GaussianIntegrals

open MeasureTheory Set
open MagHK.Noninteracting MagHK.GaussianNormalization

theorem gaussianF_squared (t r : ℝ) (ht : 0 ≤ t) :
    gaussianF t r ^ 2 = Real.exp (-r ^ 2) / (1 + t * r ^ 2) := by
  have hd : 0 ≤ 1 + t * r ^ 2 := by positivity
  unfold gaussianF
  rw [div_pow, Real.sq_sqrt hd, pow_two, ← Real.exp_add]
  congr 2
  ring

theorem gaussian_radial_squared_integrable (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun r => gaussianF t r ^ 2 * r) (Ioi (0 : ℝ)) := by
  have hdom : IntegrableOn (fun r : ℝ => r * Real.exp (-r ^ 2)) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul, one_mul] using
      (integrable_mul_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)).integrableOn
  have hf : Continuous (gaussianF t) :=
    continuous_iff_continuousAt.2 fun r => (gaussianF_hasDerivAt t r ht).continuousAt
  apply hdom.mono' ((hf.pow 2).mul continuous_id).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 ≤ r := hr.le
  change ‖gaussianF t r ^ 2 * r‖ ≤ r * Real.exp (-r ^ 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), gaussianF_squared t r ht]
  calc
    Real.exp (-r ^ 2) / (1 + t * r ^ 2) * r ≤ Real.exp (-r ^ 2) * r :=
      mul_le_mul_of_nonneg_right
        (div_le_self (Real.exp_pos _).le (by nlinarith [mul_nonneg ht (sq_nonneg r)])) hr0
    _ = _ := mul_comm _ _

theorem gaussian_second_squared_integrable (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun r => t * r ^ 2 * gaussianF t r ^ 2 * r) (Ioi (0 : ℝ)) := by
  have hdom : IntegrableOn (fun r : ℝ => r * Real.exp (-r ^ 2)) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul, one_mul] using
      (integrable_mul_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)).integrableOn
  have hf : Continuous (gaussianF t) :=
    continuous_iff_continuousAt.2 fun r => (gaussianF_hasDerivAt t r ht).continuousAt
  apply hdom.mono'
    (((continuous_const.mul (continuous_id.pow 2)).mul (hf.pow 2)).mul
      continuous_id).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 ≤ r := hr.le
  have htr : 0 ≤ t * r ^ 2 := by positivity
  have hfrac : t * r ^ 2 / (1 + t * r ^ 2) ≤ 1 :=
    (div_le_one (by positivity)).2 (by linarith)
  change ‖t * r ^ 2 * gaussianF t r ^ 2 * r‖ ≤ r * Real.exp (-r ^ 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), gaussianF_squared t r ht]
  calc
    _ = (t * r ^ 2 / (1 + t * r ^ 2)) * (r * Real.exp (-r ^ 2)) := by ring
    _ ≤ 1 * (r * Real.exp (-r ^ 2)) :=
      mul_le_mul_of_nonneg_right hfrac (by positivity)
    _ = _ := one_mul _

theorem gaussian_radial_squared_integral (t : ℝ) (ht : 0 ≤ t) :
    (∫ r in Ioi (0 : ℝ), gaussianF t r ^ 2 * r) = normIntegral t / 2 := by
  have h := integral_comp_rpow_Ioi_of_pos
    (g := fun s : ℝ => Real.exp (-s) / (1 + t * s)) (by norm_num : (0 : ℝ) < 2)
  simp only [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num,
    Real.rpow_one, smul_eq_mul] at h
  have hfun : (fun r : ℝ => 2 * r * (Real.exp (-r ^ 2) / (1 + t * r ^ 2))) =
      (fun r => 2 * (gaussianF t r ^ 2 * r)) := by
    funext r
    rw [gaussianF_squared t r ht]
    ring
  rw [hfun, integral_const_mul, ← normIntegral_eq_literal t ht] at h
  linarith

theorem gaussian_second_squared_integral (t : ℝ) (ht : 0 ≤ t) :
    (∫ r in Ioi (0 : ℝ), t * r ^ 2 * gaussianF t r ^ 2 * r) =
      (1 - normIntegral t) / 2 := by
  have h := integral_comp_rpow_Ioi_of_pos
    (g := fun s : ℝ => t * s * Real.exp (-s) / (1 + t * s))
    (by norm_num : (0 : ℝ) < 2)
  simp only [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num,
    Real.rpow_one, smul_eq_mul] at h
  have hfun : (fun r : ℝ => 2 * r * (t * r ^ 2 * Real.exp (-r ^ 2) / (1 + t * r ^ 2))) =
      (fun r => 2 * (t * r ^ 2 * gaussianF t r ^ 2 * r)) := by
    funext r
    rw [gaussianF_squared t r ht]
    ring
  rw [hfun, integral_const_mul, complementary_integral t ht] at h
  linarith

def axialChi (c z : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (c / Real.pi)) * Real.exp (-c * z ^ 2 / 2)

theorem axialChi_eq_literal (c z : ℝ) (hc : 0 ≤ c) :
    axialChi c z = (c / Real.pi) ^ ((1 : ℝ) / 4) * Real.exp (-c * z ^ 2 / 2) := by
  unfold axialChi
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  norm_num

theorem axialChi_positive (c z : ℝ) (hc : 0 < c) : 0 < axialChi c z := by
  unfold axialChi
  positivity

theorem axialChi_hasDerivAt (c z : ℝ) :
    HasDerivAt (axialChi c) (-c * z * axialChi c z) z := by
  have h := (((((hasDerivAt_id z).pow 2).const_mul (-c)).div_const 2).exp).const_mul
    (Real.sqrt (Real.sqrt (c / Real.pi)))
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply, axialChi]
  ring

theorem axialChiPrime_hasDerivAt (c z : ℝ) :
    HasDerivAt (fun u => -c * u * axialChi c u)
      ((c ^ 2 * z ^ 2 - c) * axialChi c z) z := by
  have h := ((hasDerivAt_id z).const_mul (-c)).mul (axialChi_hasDerivAt c z)
  apply h.congr_deriv
  simp only [id_eq]
  ring

theorem axialChi_eigen_equation (c z : ℝ) :
    -deriv (deriv (axialChi c)) z + (c ^ 2 * z ^ 2 - c) * axialChi c z = 0 := by
  have hfun : deriv (axialChi c) = fun u => -c * u * axialChi c u :=
    funext (fun u => (axialChi_hasDerivAt c u).deriv)
  rw [hfun, (axialChiPrime_hasDerivAt c z).deriv]
  ring

theorem axialChi_squared (c z : ℝ) :
    axialChi c z ^ 2 = Real.sqrt (c / Real.pi) * Real.exp (-c * z ^ 2) := by
  unfold axialChi
  rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _), pow_two, ← Real.exp_add]
  congr 2
  ring

theorem axialChi_squared_integrable (c : ℝ) (hc : 0 < c) :
    Integrable (fun z => axialChi c z ^ 2) := by
  simp_rw [axialChi_squared]
  exact (integrable_exp_neg_mul_sq hc).const_mul _

theorem axialChi_normalized (c : ℝ) (hc : 0 < c) :
    (∫ z : ℝ, axialChi c z ^ 2) = 1 := by
  simp_rw [axialChi_squared]
  rw [integral_const_mul, integral_gaussian, ← Real.sqrt_mul (by positivity)]
  have heq : c / Real.pi * (Real.pi / c) = 1 := by
    field_simp [ne_of_gt hc, ne_of_gt Real.pi_pos]
  rw [heq, Real.sqrt_one]

theorem exists_gaussian_equal_norms : ∃ t : ℝ, 0 < t ∧
    (∫ r in Ioi (0 : ℝ), gaussianF t r ^ 2 * r) = 1 / 4 ∧
    (∫ r in Ioi (0 : ℝ), t * r ^ 2 * gaussianF t r ^ 2 * r) = 1 / 4 := by
  obtain ⟨t, ht, heq⟩ := exists_parameter
  have hnorm : normIntegral t = 1 / 2 := (normIntegral_eq_literal t ht.le).trans heq
  refine ⟨t, ht, ?_, ?_⟩
  · rw [gaussian_radial_squared_integral t ht.le, hnorm]
    norm_num
  · rw [gaussian_second_squared_integral t ht.le, hnorm]
    norm_num

end MagHK.GaussianIntegrals
