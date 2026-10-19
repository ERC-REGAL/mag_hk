import MagHK.NormContinuity
import MagHK.Axial
import MagHK.Slater
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Concrete bounded orbitals with the cylindrical volume element r dr dθ dz.
The final result uses the proved parameter existence and does not assume orbital
normalization or orthogonality. The Cartesian change of variables is separate. -/
noncomputable section
namespace MagHK.CylindricalOrbitals
open MeasureTheory Set
open MagHK.Noninteracting MagHK.Axial
open scoped ComplexConjugate ENNReal NNReal
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def radialMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun r => (Real.toNNReal r : ℝ≥0∞))

def angularMeasure : Measure ℝ := volume.restrict (Ioc (-Real.pi) Real.pi)

def cylindricalMeasure : Measure (ℝ × (ℝ × ℝ)) :=
  radialMeasure.prod (angularMeasure.prod volume)

instance : SFinite radialMeasure := by unfold radialMeasure; infer_instance
instance : IsFiniteMeasure angularMeasure := by unfold angularMeasure; infer_instance

/-- The radial Jacobian is included in the measure. -/
theorem radial_integral (f : ℝ → ℝ) :
    (∫ r, f r ∂radialMeasure) = ∫ r in Ioi (0 : ℝ), r * f r := by
  rw [radialMeasure, integral_withDensity_eq_integral_smul
    measurable_real_toNNReal]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  change (Real.toNNReal r : ℝ) * f r = r * f r
  rw [Real.coe_toNNReal r hr.le]

theorem radial_integrable_iff (f : ℝ → ℝ) :
    Integrable f radialMeasure ↔ IntegrableOn (fun r => r * f r) (Ioi (0 : ℝ)) := by
  rw [radialMeasure, integrable_withDensity_iff_integrable_smul
    measurable_real_toNNReal]
  apply integrable_congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  change (Real.toNNReal r : ℝ) * f r = r * f r
  rw [Real.coe_toNNReal r hr.le]

def radialZero (t r : ℝ) : ℝ := profileF t r

def radialMinus (t r : ℝ) : ℝ := Real.sqrt t * profileR r * profileF t r

theorem radialZero_sq_integrable (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun r => radialZero t r ^ 2) radialMeasure := by
  rw [radial_integrable_iff]
  have h : IntegrableOn (fun r => profileF t r ^ 2 * r) (Ioi (0 : ℝ)) :=
    radialDensityF_integrable t ht
  simpa only [radialZero, mul_comm] using h

theorem radialMinus_sq_integrable (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun r => radialMinus t r ^ 2) radialMeasure := by
  rw [radial_integrable_iff]
  simpa only [radialMinus, mul_pow, Real.sq_sqrt ht, mul_comm, mul_left_comm, mul_assoc]
    using radialNormG_integrable t ht

theorem radialZero_sq_integral (t : ℝ) :
    (∫ r, radialZero t r ^ 2 ∂radialMeasure) = radialNormF t := by
  rw [radial_integral]
  simp only [radialNormF, radialDensityF, radialZero, mul_comm]

theorem radialMinus_sq_integral (t : ℝ) (ht : 0 ≤ t) :
    (∫ r, radialMinus t r ^ 2 ∂radialMeasure) = radialNormG t := by
  rw [radial_integral]
  simp only [radialNormG, radialMinus, mul_pow, Real.sq_sqrt ht,
    mul_comm, mul_left_comm, mul_assoc]

theorem radial_cross_integrable (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun r => radialZero t r * radialMinus t r) radialMeasure := by
  apply ((radialZero_sq_integrable t ht).add (radialMinus_sq_integrable t ht)).mono'
  · exact ((profileF_continuous t ht).mul
      ((continuous_const.mul profileR_continuous).mul
        (profileF_continuous t ht))).aestronglyMeasurable
  · apply ae_of_all
    intro r
    simp only [Real.norm_eq_abs, Pi.add_apply]
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg (radialZero t r + radialMinus t r),
        sq_nonneg (radialZero t r), sq_nonneg (radialMinus t r)]
    · nlinarith [sq_nonneg (radialZero t r - radialMinus t r),
        sq_nonneg (radialZero t r), sq_nonneg (radialMinus t r)]

def phase (θ : ℝ) : ℂ := conj (Complex.exp ((θ : ℂ) * Complex.I))

theorem phase_eq_negative_exp (θ : ℝ) :
    phase θ = Complex.exp (-(θ : ℂ) * Complex.I) := by
  simp only [phase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, mul_neg, neg_mul]

theorem phase_continuous : Continuous phase := by
  exact Complex.continuous_conj.comp
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))

theorem phase_norm (θ : ℝ) : ‖phase θ‖ = 1 := by
  simp only [phase, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I]

theorem phase_pairing (θ : ℝ) : star (phase θ) * phase θ = 1 := by
  rw [Complex.star_def, Complex.conj_mul', phase_norm]
  norm_num

theorem phase_integrable : Integrable phase angularMeasure := by
  exact (phase_continuous.intervalIntegrable (-Real.pi) Real.pi).1

theorem phase_integral : (∫ θ, phase θ ∂angularMeasure) = 0 := by
  change (∫ θ in Ioc (-Real.pi) Real.pi, conj (Complex.exp ((θ : ℂ) * Complex.I))) = 0
  rw [integral_conj]
  have h := integral_exp_mul_I_eq_sin Real.pi
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])] at h
  simpa using congrArg conj h

theorem angular_one_integrable : Integrable (fun _ : ℝ => (1 : ℂ)) angularMeasure :=
  integrable_const 1

theorem angular_one_integral : (∫ _ : ℝ, (1 : ℂ) ∂angularMeasure) = (2 * Real.pi : ℝ) := by
  rw [angularMeasure, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  simp only [intervalIntegral.integral_const, sub_neg_eq_add, Complex.real_smul]
  push_cast
  ring

def normalization (t : ℝ) : ℝ := (Real.sqrt (2 * Real.pi * radialNormF t))⁻¹

def orbitalZero (t c : ℝ) (x : ℝ × (ℝ × ℝ)) : ℂ :=
  ((normalization t * radialZero t x.1 * chi c x.2.2 : ℝ) : ℂ)

def orbitalMinus (t c : ℝ) (x : ℝ × (ℝ × ℝ)) : ℂ :=
  ((normalization t * radialMinus t x.1 * chi c x.2.2 : ℝ) : ℂ) * phase x.2.1

/-- Fubini factorization with the actual axial square. -/
def separated (h : ℝ → ℝ) (p : ℝ → ℂ) (c : ℝ)
    (x : ℝ × (ℝ × ℝ)) : ℂ :=
  (h x.1 : ℂ) * (p x.2.1 * (chi c x.2.2 ^ 2 : ℝ))

theorem separated_integrable (h : ℝ → ℝ) (p : ℝ → ℂ) (c : ℝ)
    (hh : Integrable h radialMeasure) (hp : Integrable p angularMeasure) (hc : 0 < c) :
    Integrable (separated h p c) cylindricalMeasure := by
  exact hh.ofReal.mul_prod (hp.mul_prod (chi_squared_integrable c hc).ofReal)

theorem separated_integral (h : ℝ → ℝ) (p : ℝ → ℂ) (c : ℝ) (hc : 0 < c) :
    (∫ x, separated h p c x ∂cylindricalMeasure) =
      (∫ r, h r ∂radialMeasure : ℝ) * (∫ θ, p θ ∂angularMeasure) := by
  unfold separated cylindricalMeasure
  rw [integral_prod_mul (fun r => (h r : ℂ))
    (fun y : ℝ × ℝ => p y.1 * ((chi c y.2 ^ 2 : ℝ) : ℂ))]
  rw [integral_prod_mul p (fun z => ((chi c z ^ 2 : ℝ) : ℂ))]
  simp only [integral_complex_ofReal, chi_normalization c hc, Complex.ofReal_one, mul_one]

theorem star_phase_integrable : Integrable (fun θ => star (phase θ)) angularMeasure := by
  exact ((Complex.continuous_conj.comp phase_continuous).intervalIntegrable (-Real.pi) Real.pi).1

theorem star_phase_integral : (∫ θ, star (phase θ) ∂angularMeasure) = 0 := by
  simp only [Complex.star_def, integral_conj, phase_integral, map_zero]

theorem zero_pairing (t c : ℝ) (x : ℝ × (ℝ × ℝ)) :
    star (orbitalZero t c x) * orbitalZero t c x =
      (normalization t ^ 2 : ℝ) * separated (fun r => radialZero t r ^ 2) (fun _ => 1) c x := by
  simp only [orbitalZero, separated, Complex.star_def, Complex.conj_ofReal, one_mul]
  push_cast
  ring

theorem minus_pairing (t c : ℝ) (x : ℝ × (ℝ × ℝ)) :
    star (orbitalMinus t c x) * orbitalMinus t c x =
      (normalization t ^ 2 : ℝ) * separated (fun r => radialMinus t r ^ 2) (fun _ => 1) c x := by
  calc
    _ = ((normalization t ^ 2 * radialMinus t x.1 ^ 2 * chi c x.2.2 ^ 2 : ℝ) : ℂ) *
        (star (phase x.2.1) * phase x.2.1) := by
      simp only [orbitalMinus, star_mul, Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    _ = _ := by
      rw [phase_pairing]
      simp only [separated, one_mul, mul_one]
      push_cast
      ring

theorem cross_pairing (t c : ℝ) (x : ℝ × (ℝ × ℝ)) :
    star (orbitalZero t c x) * orbitalMinus t c x =
      (normalization t ^ 2 : ℝ) *
        separated (fun r => radialZero t r * radialMinus t r) phase c x := by
  simp only [orbitalZero, orbitalMinus, separated, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem reverse_pairing (t c : ℝ) (x : ℝ × (ℝ × ℝ)) :
    star (orbitalMinus t c x) * orbitalZero t c x =
      (normalization t ^ 2 : ℝ) *
        separated (fun r => radialZero t r * radialMinus t r) (fun θ => star (phase θ)) c x := by
  simp only [orbitalZero, orbitalMinus, separated, star_mul,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem normalization_identity (t : ℝ) (hn : 0 < radialNormF t) :
    normalization t ^ 2 * (2 * Real.pi) * radialNormF t = 1 := by
  have hp : 0 < 2 * Real.pi * radialNormF t := by positivity
  unfold normalization
  rw [inv_pow, Real.sq_sqrt hp.le]
  field_simp

/-- The normalized concrete orbitals form an orthonormal pair whenever the
radial norms agree. The following existence theorem supplies this parameter. -/
theorem bounded_orthonormal (t c : ℝ) (ht : 0 < t) (hc : 0 < c)
    (heq : radialNormF t = radialNormG t) :
    MagHK.Slater.OrthonormalPair cylindricalMeasure (orbitalZero t c) (orbitalMinus t c) := by
  have hnorm := congrArg (fun a : ℝ => (a : ℂ))
    (normalization_identity t (radialNormF_pos t ht.le))
  push_cast at hnorm
  constructor
  · simp_rw [zero_pairing]
    exact (separated_integrable _ _ c (radialZero_sq_integrable t ht.le)
      angular_one_integrable hc).const_mul _
  · simp_rw [minus_pairing]
    exact (separated_integrable _ _ c (radialMinus_sq_integrable t ht.le)
      angular_one_integrable hc).const_mul _
  · simp_rw [cross_pairing]
    exact (separated_integrable _ _ c (radial_cross_integrable t ht.le)
      phase_integrable hc).const_mul _
  · simp_rw [reverse_pairing]
    exact (separated_integrable _ _ c (radial_cross_integrable t ht.le)
      star_phase_integrable hc).const_mul _
  · simp_rw [zero_pairing]
    rw [integral_const_mul, separated_integral _ _ c hc,
      radialZero_sq_integral, angular_one_integral]
    push_cast
    convert hnorm using 1 <;> ring
  · simp_rw [minus_pairing]
    rw [integral_const_mul, separated_integral _ _ c hc,
      radialMinus_sq_integral t ht.le, angular_one_integral, ← heq]
    push_cast
    convert hnorm using 1 <;> ring
  · simp_rw [cross_pairing]
    rw [integral_const_mul, separated_integral _ _ c hc, phase_integral, mul_zero, mul_zero]
  · simp_rw [reverse_pairing]
    rw [integral_const_mul, separated_integral _ _ c hc, star_phase_integral, mul_zero, mul_zero]

/-- No normalization, integrability, or orthogonality assumptions are required. -/
theorem exists_bounded_orthonormal (c : ℝ) (hc : 0 < c) :
    ∃ t : ℝ, 0 < t ∧
      MagHK.Slater.OrthonormalPair cylindricalMeasure (orbitalZero t c) (orbitalMinus t c) := by
  obtain ⟨t, ht, heq, _⟩ := exists_bounded_parameter
  exact ⟨t, ht, bounded_orthonormal t c ht hc heq⟩

end MagHK.CylindricalOrbitals
