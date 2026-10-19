import MagHK.GaussianIntegrals
import MagHK.PartnerAsymptotics
import MagHK.SecondOrbital
import MagHK.CylindricalOrbitals

/-! Explicit Gaussian moments and finite radial energy for both orbitals. -/
noncomputable section
namespace MagHK.GaussianDomains
open MeasureTheory Set
open MagHK.Noninteracting MagHK.SecondOrbital MagHK.GaussianIntegrals
open MagHK.RadialEndpoints MagHK.PartnerAsymptotics MagHK.CylindricalOrbitals
open scoped ContDiff
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def scalar (t r : ℝ) : ℝ :=
  r ^ 2 - 2 / (1 + t * r ^ 2) - 2 * t / (1 + t * r ^ 2) ^ 2

theorem scalar_contDiff (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ⊤ (scalar t) := by
  have hd : ContDiff ℝ ⊤ (fun r : ℝ => 1 + t * r ^ 2) :=
    contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))
  exact ((contDiff_id.pow 2).sub (contDiff_const.div hd
    (fun r => ne_of_gt (by positivity : 0 < 1 + t * r ^ 2)))).sub
      (contDiff_const.div (hd.pow 2)
        (fun r => ne_of_gt (by positivity : 0 < (1 + t * r ^ 2) ^ 2)))

theorem scalar_abs_bound (t r : ℝ) (ht : 0 ≤ t) :
    |scalar t r| ≤ r ^ 2 + 2 + 2 * t := by
  have hlo := gaussianScalar_quadratic_lower_bound t r ht
  have h1 : 0 ≤ 2 / (1 + t * r ^ 2) := by positivity
  have h2 : 0 ≤ 2 * t / (1 + t * r ^ 2) ^ 2 := by positivity
  unfold scalar
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg r]

theorem gaussianF_contDiff (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ∞ (gaussianF t) := by
  have hd : ContDiff ℝ ∞ (fun r : ℝ => Real.sqrt (1 + t * r ^ 2)) :=
    (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))).sqrt
      (fun r => ne_of_gt (by positivity : 0 < 1 + t * r ^ 2))
  exact (((contDiff_id.pow 2).neg.div_const 2).exp).div hd
    (fun r => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

theorem gaussianProduct_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (gaussianProduct t) := contDiff_id.mul (gaussianF_contDiff t ht)

theorem gaussianF_contDiffOn_two (t : ℝ) (ht : 0 ≤ t) :
    ContDiffOn ℝ 2 (gaussianF t) (Ioi 0) :=
  ((gaussianF_contDiff t ht).of_le (by simp)).contDiffOn

theorem gaussianProduct_contDiffOn_two (t : ℝ) (ht : 0 ≤ t) :
    ContDiffOn ℝ 2 (gaussianProduct t) (Ioi 0) :=
  ((gaussianProduct_contDiff t ht).of_le (by simp)).contDiffOn

theorem gaussianF_square_bound (t r : ℝ) (ht : 0 ≤ t) :
    gaussianF t r ^ 2 ≤ Real.exp (-r ^ 2) := by
  rw [gaussianF_squared t r ht]
  exact div_le_self (Real.exp_pos _).le (by nlinarith [mul_nonneg ht (sq_nonneg r)])

def moment (t : ℝ) (n : ℕ) (r : ℝ) : ℝ := r ^ n * gaussianF t r ^ 2 * r

theorem moment_integrable (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    IntegrableOn (moment t n) (Ioi (0 : ℝ)) := by
  have hdom : IntegrableOn (fun r : ℝ => r ^ (n + 1) * Real.exp (-r ^ 2)) (Ioi 0) := by
    simpa only [Real.rpow_natCast, neg_mul, one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
        (s := ((n + 1 : ℕ) : ℝ))
        (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _)))
  have hm : Continuous (moment t n) :=
    ((continuous_id.pow n).mul ((gaussianF_contDiff t ht).continuous.pow 2)).mul continuous_id
  apply hdom.mono' hm.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  change ‖r ^ n * gaussianF t r ^ 2 * r‖ ≤ r ^ (n + 1) * Real.exp (-r ^ 2)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (pow_nonneg hr.le _) (sq_nonneg _)) hr.le)]
  calc
    _ ≤ r ^ n * Real.exp (-r ^ 2) * r :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (gaussianF_square_bound t r ht) (pow_nonneg hr.le _)) hr.le
    _ = _ := by rw [pow_succ]; ring

theorem gaussianU_square_upper (t r : ℝ) (ht : 0 ≤ t) :
    gaussianU t r ^ 2 ≤ 2 * r ^ 2 + 2 * t := by
  have ha := gaussianA_square_le t r ht
  unfold gaussianU
  nlinarith [sq_nonneg (r - gaussianA t r)]

theorem gaussianF_deriv_energy_bound (t r : ℝ) (ht : 0 ≤ t) :
    deriv (gaussianF t) r ^ 2 ≤ (2 * r ^ 2 + 2 * t) * gaussianF t r ^ 2 := by
  rw [(gaussianF_hasDerivAt t r ht).deriv]
  have h := mul_le_mul_of_nonneg_right (gaussianU_square_upper t r ht) (sq_nonneg (gaussianF t r))
  simpa only [gaussianU, mul_pow, neg_sq] using h

theorem gaussianProduct_deriv_energy_bound (t r : ℝ) (ht : 0 ≤ t) :
    deriv (gaussianProduct t) r ^ 2 ≤
      (2 + 4 * r ^ 4 + 4 * t * r ^ 2) * gaussianF t r ^ 2 := by
  rw [(gaussianProduct_hasDerivAt t r ht).deriv]
  have hU := mul_le_mul_of_nonneg_left (gaussianU_square_upper t r ht) (sq_nonneg r)
  have hs : (1 - r * gaussianU t r) ^ 2 ≤ 2 + 4 * r ^ 4 + 4 * t * r ^ 2 := by
    nlinarith [sq_nonneg (1 + r * gaussianU t r)]
  have h := mul_le_mul_of_nonneg_right hs (sq_nonneg (gaussianF t r))
  simpa only [gaussianProductPrime, gaussianU, mul_pow] using h

theorem gaussianProduct_magnetic_energy_bound (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    (-1 / r + gaussianA t r) ^ 2 * gaussianProduct t r ^ 2 ≤ gaussianF t r ^ 2 := by
  have ha := gaussian_angular_bounds t r ht hr
  have hs : (1 - r * gaussianA t r) ^ 2 ≤ 1 := by nlinarith
  calc
    _ = (1 - r * gaussianA t r) ^ 2 * gaussianF t r ^ 2 := by
      unfold gaussianProduct
      field_simp
      <;> ring
    _ ≤ 1 * gaussianF t r ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = _ := one_mul _

theorem gaussianF_energy_bound (t r : ℝ) (ht : 0 ≤ t) :
    deriv (gaussianF t) r ^ 2 + (gaussianA t r ^ 2 + |scalar t r|) * gaussianF t r ^ 2 ≤
      (3 * r ^ 2 + 2 + 5 * t) * gaussianF t r ^ 2 := by
  have hd := gaussianF_deriv_energy_bound t r ht
  have ha := mul_le_mul_of_nonneg_right (gaussianA_square_le t r ht) (sq_nonneg (gaussianF t r))
  have hv := mul_le_mul_of_nonneg_right (scalar_abs_bound t r ht) (sq_nonneg (gaussianF t r))
  nlinarith

theorem gaussianProduct_energy_bound (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    deriv (gaussianProduct t) r ^ 2 +
      ((-1 / r + gaussianA t r) ^ 2 + |scalar t r|) * gaussianProduct t r ^ 2 ≤
        (3 + 5 * r ^ 4 + (2 + 6 * t) * r ^ 2) * gaussianF t r ^ 2 := by
  have hd := gaussianProduct_deriv_energy_bound t r ht.le
  have ha := gaussianProduct_magnetic_energy_bound t r ht hr
  have hv := mul_le_mul_of_nonneg_right (scalar_abs_bound t r ht.le) (sq_nonneg (gaussianProduct t r))
  unfold gaussianProduct at *
  nlinarith

theorem gaussianF_form_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun r => deriv (gaussianF t) r ^ 2 +
      ((0 / r + gaussianA t r) ^ 2 + |scalar t r|) * gaussianF t r ^ 2) radialMeasure := by
  rw [radial_integrable_iff]
  have hi := ((moment_integrable t ht.le 2).const_mul 3).add
    ((moment_integrable t ht.le 0).const_mul (2 + 5 * t))
  have hm : Measurable (fun r : ℝ => r * (deriv (gaussianF t) r ^ 2 +
      ((0 / r + gaussianA t r) ^ 2 + |scalar t r|) * gaussianF t r ^ 2)) := by
    have hf := (gaussianF_contDiff t ht.le).continuous.measurable
    have hd := ((gaussianF_contDiff t ht.le).continuous_deriv (by simp)).measurable
    have ha := (gaussianA_contDiff t ht.le).continuous.measurable
    have hv := (scalar_contDiff t ht.le).continuous.measurable
    fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr.le (by positivity))]
  simp only [zero_div, zero_add, Pi.add_apply]
  have h := mul_le_mul_of_nonneg_left (gaussianF_energy_bound t r ht.le) hr.le
  unfold moment
  nlinarith

theorem gaussianProduct_form_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun r => deriv (gaussianProduct t) r ^ 2 +
      ((-1 / r + gaussianA t r) ^ 2 + |scalar t r|) * gaussianProduct t r ^ 2) radialMeasure := by
  rw [radial_integrable_iff]
  have hi := (((moment_integrable t ht.le 0).const_mul 3).add
    ((moment_integrable t ht.le 4).const_mul 5)).add
      ((moment_integrable t ht.le 2).const_mul (2 + 6 * t))
  have hm : Measurable (fun r : ℝ => r * (deriv (gaussianProduct t) r ^ 2 +
      ((-1 / r + gaussianA t r) ^ 2 + |scalar t r|) * gaussianProduct t r ^ 2)) := by
    have hf := (gaussianProduct_contDiff t ht.le).continuous.measurable
    have hd := ((gaussianProduct_contDiff t ht.le).continuous_deriv (by simp)).measurable
    have ha := (gaussianA_contDiff t ht.le).continuous.measurable
    have hv := (scalar_contDiff t ht.le).continuous.measurable
    fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr.le (by positivity))]
  simp only [Pi.add_apply]
  have h := mul_le_mul_of_nonneg_left (gaussianProduct_energy_bound t r ht hr) hr.le
  unfold moment
  nlinarith

theorem gaussianF_le_one (t r : ℝ) (ht : 0 ≤ t) : gaussianF t r ≤ 1 := by
  have h := gaussianF_square_bound t r ht
  have he : Real.exp (-r ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
  nlinarith [gaussianF_pos t r ht]

theorem gaussianF_bounded_near_zero (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ r, 0 < r → r ≤ 1 → |gaussianF t r| ≤ C :=
  ⟨1, fun r _ _ => by rw [abs_of_pos (gaussianF_pos t r ht)]; exact gaussianF_le_one t r ht⟩

theorem gaussianProduct_positive (t r : ℝ) (ht : 0 ≤ t) (hr : 0 < r) :
    0 < gaussianProduct t r := mul_pos hr (gaussianF_pos t r ht)

theorem gaussianProduct_bounded_near_zero (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ r, 0 < r → r ≤ 1 → |gaussianProduct t r| ≤ C := by
  refine ⟨1, fun r hr hr1 => ?_⟩
  rw [abs_of_pos (gaussianProduct_positive t r ht hr)]
  exact (mul_le_mul_of_nonneg_left (gaussianF_le_one t r ht) hr.le).trans (by simpa using hr1)

theorem gaussianF_mass_integrable (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun r => gaussianF t r ^ 2) radialMeasure := by
  rw [radial_integrable_iff]
  simpa only [mul_comm] using gaussian_radial_squared_integrable t ht

theorem gaussianProduct_mass_integrable (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun r => gaussianProduct t r ^ 2) radialMeasure := by
  rw [radial_integrable_iff]
  have hi := moment_integrable t ht 2
  apply hi.congr
  exact ae_of_all _ (fun r => by simp only [moment, gaussianProduct]; ring)

theorem gaussianF_mass_positive (t : ℝ) (ht : 0 ≤ t) :
    0 < ∫ r, gaussianF t r ^ 2 ∂radialMeasure := by
  rw [radial_integral]
  have hi := (radial_integrable_iff _).mp (gaussianF_mass_integrable t ht)
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ hi).2
  · have he : Function.support (fun r => r * gaussianF t r ^ 2) ∩ Ioi (0 : ℝ) = Ioi 0 := by
      apply inter_eq_right.2
      intro r hr
      change r * gaussianF t r ^ 2 ≠ 0
      exact ne_of_gt (mul_pos hr (sq_pos_of_pos (gaussianF_pos t r ht)))
    rw [he, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact mul_nonneg hr.le (sq_nonneg _)

theorem gaussianProduct_mass_positive (t : ℝ) (ht : 0 ≤ t) :
    0 < ∫ r, gaussianProduct t r ^ 2 ∂radialMeasure := by
  rw [radial_integral]
  have hi := (radial_integrable_iff _).mp (gaussianProduct_mass_integrable t ht)
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ hi).2
  · have he : Function.support (fun r => r * gaussianProduct t r ^ 2) ∩ Ioi (0 : ℝ) = Ioi 0 := by
      apply inter_eq_right.2
      intro r hr
      change r * gaussianProduct t r ^ 2 ≠ 0
      exact ne_of_gt (mul_pos hr (sq_pos_of_pos (gaussianProduct_positive t r ht hr)))
    rw [he, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact mul_nonneg hr.le (sq_nonneg _)

end MagHK.GaussianDomains
