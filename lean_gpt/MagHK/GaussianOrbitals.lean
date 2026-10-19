import MagHK.GaussianDomains
import MagHK.CartesianOrbitals

/-! Concrete normalized Gaussian orbitals and Cartesian orthogonality. -/
noncomputable section
namespace MagHK.GaussianOrbitals
open MeasureTheory Set
open MagHK.Noninteracting MagHK.SecondOrbital MagHK.GaussianIntegrals MagHK.GaussianDomains
open MagHK.CylindricalOrbitals
open scoped ComplexConjugate
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def normalization : ℝ := Real.sqrt (2 / Real.pi)

def radialSecond (t r : ℝ) : ℝ := Real.sqrt t * gaussianProduct t r

def cylindricalZero (t c : ℝ) (x : ℝ × (ℝ × ℝ)) : ℂ :=
  ((normalization * gaussianF t x.1 * axialChi c x.2.2 : ℝ) : ℂ)

def cylindricalMinus (t c : ℝ) (x : ℝ × (ℝ × ℝ)) : ℂ :=
  ((normalization * radialSecond t x.1 * axialChi c x.2.2 : ℝ) : ℂ) * phase x.2.1

def orbitalZero (t c : ℝ) (x : ℂ × ℝ) : ℂ :=
  ((normalization * gaussianF t ‖x.1‖ * axialChi c x.2 : ℝ) : ℂ)

def orbitalMinus (t c : ℝ) (x : ℂ × ℝ) : ℂ :=
  ((normalization * Real.sqrt t * gaussianF t ‖x.1‖ * axialChi c x.2 : ℝ) : ℂ) * conj x.1

theorem axialChi_continuous (c : ℝ) : Continuous (axialChi c) :=
  continuous_iff_continuousAt.mpr (fun z => (axialChi_hasDerivAt c z).continuousAt)

theorem orbitalZero_continuous (t c : ℝ) (ht : 0 ≤ t) : Continuous (orbitalZero t c) := by
  exact Complex.continuous_ofReal.comp
    ((continuous_const.mul ((gaussianF_contDiff t ht).continuous.comp continuous_fst.norm)).mul
      ((axialChi_continuous c).comp continuous_snd))

theorem orbitalMinus_continuous (t c : ℝ) (ht : 0 ≤ t) : Continuous (orbitalMinus t c) := by
  unfold orbitalMinus
  have hf : Continuous (fun x : ℂ × ℝ => gaussianF t ‖x.1‖) :=
    (gaussianF_contDiff t ht).continuous.comp continuous_fst.norm
  have hc : Continuous (fun x : ℂ × ℝ => axialChi c x.2) :=
    (axialChi_continuous c).comp continuous_snd
  fun_prop

theorem first_squared_integral (t : ℝ) :
    (∫ r, gaussianF t r ^ 2 ∂radialMeasure) = ∫ r in Ioi (0 : ℝ), gaussianF t r ^ 2 * r := by
  rw [radial_integral]
  simp only [mul_comm]

theorem second_squared_integrable (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun r => radialSecond t r ^ 2) radialMeasure := by
  have hi := (gaussianProduct_mass_integrable t ht).const_mul t
  apply hi.congr
  exact ae_of_all _ (fun r => by simp only [radialSecond, mul_pow, Real.sq_sqrt ht])

theorem second_squared_integral (t : ℝ) (ht : 0 ≤ t) :
    (∫ r, radialSecond t r ^ 2 ∂radialMeasure) =
      ∫ r in Ioi (0 : ℝ), t * r ^ 2 * gaussianF t r ^ 2 * r := by
  rw [radial_integral]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by
    simp only [radialSecond, gaussianProduct, mul_pow, Real.sq_sqrt ht]
    ring)

theorem cross_integrable (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun r => gaussianF t r * radialSecond t r) radialMeasure := by
  apply ((gaussianF_mass_integrable t ht).add (second_squared_integrable t ht)).mono'
  · exact ((gaussianF_contDiff t ht).continuous.mul
      (continuous_const.mul (gaussianProduct_contDiff t ht).continuous)).aestronglyMeasurable
  · apply ae_of_all
    intro r
    change |gaussianF t r * radialSecond t r| ≤ gaussianF t r ^ 2 + radialSecond t r ^ 2
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg (gaussianF t r + radialSecond t r),
        sq_nonneg (gaussianF t r), sq_nonneg (radialSecond t r)]
    · nlinarith [sq_nonneg (gaussianF t r - radialSecond t r),
        sq_nonneg (gaussianF t r), sq_nonneg (radialSecond t r)]

def separated (h : ℝ → ℝ) (p : ℝ → ℂ) (c : ℝ) (x : ℝ × (ℝ × ℝ)) : ℂ :=
  (h x.1 : ℂ) * (p x.2.1 * (axialChi c x.2.2 ^ 2 : ℝ))

theorem separated_integrable (h : ℝ → ℝ) (p : ℝ → ℂ) (c : ℝ)
    (hh : Integrable h radialMeasure) (hp : Integrable p angularMeasure) (hc : 0 < c) :
    Integrable (separated h p c) cylindricalMeasure :=
  hh.ofReal.mul_prod (hp.mul_prod (axialChi_squared_integrable c hc).ofReal)

theorem separated_integral (h : ℝ → ℝ) (p : ℝ → ℂ) (c : ℝ) (hc : 0 < c) :
    (∫ x, separated h p c x ∂cylindricalMeasure) =
      (∫ r, h r ∂radialMeasure : ℝ) * (∫ θ, p θ ∂angularMeasure) := by
  unfold separated cylindricalMeasure
  rw [integral_prod_mul (fun r => (h r : ℂ))
    (fun y : ℝ × ℝ => p y.1 * ((axialChi c y.2 ^ 2 : ℝ) : ℂ))]
  rw [integral_prod_mul p (fun z => ((axialChi c z ^ 2 : ℝ) : ℂ))]
  simp only [integral_complex_ofReal, axialChi_normalized c hc, Complex.ofReal_one, mul_one]

theorem zero_pairing (t c : ℝ) (x : ℝ × (ℝ × ℝ)) :
    star (cylindricalZero t c x) * cylindricalZero t c x =
      (normalization ^ 2 : ℝ) * separated (fun r => gaussianF t r ^ 2) (fun _ => 1) c x := by
  simp only [cylindricalZero, separated, Complex.star_def, Complex.conj_ofReal, one_mul]
  push_cast
  ring

theorem minus_pairing (t c : ℝ) (x : ℝ × (ℝ × ℝ)) :
    star (cylindricalMinus t c x) * cylindricalMinus t c x =
      (normalization ^ 2 : ℝ) * separated (fun r => radialSecond t r ^ 2) (fun _ => 1) c x := by
  calc
    _ = ((normalization ^ 2 * radialSecond t x.1 ^ 2 * axialChi c x.2.2 ^ 2 : ℝ) : ℂ) *
        (star (phase x.2.1) * phase x.2.1) := by
      simp only [cylindricalMinus, star_mul, Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    _ = _ := by
      rw [phase_pairing]
      simp only [separated, one_mul, mul_one]
      push_cast
      ring

theorem cross_pairing (t c : ℝ) (x : ℝ × (ℝ × ℝ)) :
    star (cylindricalZero t c x) * cylindricalMinus t c x =
      (normalization ^ 2 : ℝ) *
        separated (fun r => gaussianF t r * radialSecond t r) phase c x := by
  simp only [cylindricalZero, cylindricalMinus, separated, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem reverse_pairing (t c : ℝ) (x : ℝ × (ℝ × ℝ)) :
    star (cylindricalMinus t c x) * cylindricalZero t c x =
      (normalization ^ 2 : ℝ) *
        separated (fun r => gaussianF t r * radialSecond t r) (fun θ => star (phase θ)) c x := by
  simp only [cylindricalZero, cylindricalMinus, separated, star_mul,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring


theorem normalization_identity : normalization ^ 2 * (2 * Real.pi) * (1 / 4) = 1 := by
  rw [normalization, Real.sq_sqrt (by positivity)]
  field_simp [ne_of_gt Real.pi_pos]
  norm_num

/-- The radial equalities below are supplied by exists_gaussian_equal_norms
in the final theorem. All pairing integrability and angular integrals are proved. -/
theorem cylindrical_orthonormal (t c : ℝ) (ht : 0 < t) (hc : 0 < c)
    (hzero : (∫ r in Ioi (0 : ℝ), gaussianF t r ^ 2 * r) = 1 / 4)
    (hminus : (∫ r in Ioi (0 : ℝ), t * r ^ 2 * gaussianF t r ^ 2 * r) = 1 / 4) :
    MagHK.Slater.OrthonormalPair cylindricalMeasure (cylindricalZero t c) (cylindricalMinus t c) := by
  have hn := congrArg (fun a : ℝ => (a : ℂ)) normalization_identity
  push_cast at hn
  constructor
  · simp_rw [zero_pairing]
    exact (separated_integrable _ _ c (gaussianF_mass_integrable t ht.le)
      angular_one_integrable hc).const_mul _
  · simp_rw [minus_pairing]
    exact (separated_integrable _ _ c (second_squared_integrable t ht.le)
      angular_one_integrable hc).const_mul _
  · simp_rw [cross_pairing]
    exact (separated_integrable _ _ c (cross_integrable t ht.le) phase_integrable hc).const_mul _
  · simp_rw [reverse_pairing]
    exact (separated_integrable _ _ c (cross_integrable t ht.le) star_phase_integrable hc).const_mul _
  · simp_rw [zero_pairing]
    rw [integral_const_mul, separated_integral _ _ c hc,
      first_squared_integral, hzero, angular_one_integral]
    push_cast
    convert hn using 1 <;> ring
  · simp_rw [minus_pairing]
    rw [integral_const_mul, separated_integral _ _ c hc,
      second_squared_integral t ht.le, hminus, angular_one_integral]
    push_cast
    convert hn using 1 <;> ring
  · simp_rw [cross_pairing]
    rw [integral_const_mul, separated_integral _ _ c hc, phase_integral, mul_zero, mul_zero]
  · simp_rw [reverse_pairing]
    rw [integral_const_mul, separated_integral _ _ c hc, star_phase_integral, mul_zero, mul_zero]

theorem orbitalZero_pullback (t c : ℝ) (x : ℝ × (ℝ × ℝ)) (hr : 0 ≤ x.1) :
    orbitalZero t c (CartesianOrbitals.toCartesian x) = cylindricalZero t c x := by
  simp only [orbitalZero, CartesianOrbitals.toCartesian, Complex.norm_polarCoord_symm,
    abs_of_nonneg hr, cylindricalZero]

theorem orbitalMinus_pullback (t c : ℝ) (x : ℝ × (ℝ × ℝ)) (hr : 0 ≤ x.1) :
    orbitalMinus t c (CartesianOrbitals.toCartesian x) = cylindricalMinus t c x := by
  simp only [orbitalMinus, CartesianOrbitals.toCartesian, Complex.norm_polarCoord_symm, abs_of_nonneg hr]
  simp only [Complex.polarCoord_symm_apply, map_mul, Complex.conj_ofReal,
    cylindricalMinus, radialSecond, gaussianProduct, phase, Complex.exp_mul_I]
  push_cast
  ring

theorem gaussian_orthonormal (t c : ℝ) (ht : 0 < t) (hc : 0 < c)
    (hzero : (∫ r in Ioi (0 : ℝ), gaussianF t r ^ 2 * r) = 1 / 4)
    (hminus : (∫ r in Ioi (0 : ℝ), t * r ^ 2 * gaussianF t r ^ 2 * r) = 1 / 4) :
    MagHK.Slater.OrthonormalPair volume (orbitalZero t c) (orbitalMinus t c) := by
  have h := cylindrical_orthonormal t c ht hc hzero hminus
  have hz : (fun x => orbitalZero t c (CartesianOrbitals.toCartesian x)) =ᵐ[cylindricalMeasure]
      cylindricalZero t c := by
    filter_upwards [CartesianOrbitals.cylindrical_positive_ae] with x hx
    exact orbitalZero_pullback t c x hx.le
  have hg : (fun x => orbitalMinus t c (CartesianOrbitals.toCartesian x)) =ᵐ[cylindricalMeasure]
      cylindricalMinus t c := by
    filter_upwards [CartesianOrbitals.cylindrical_positive_ae] with x hx
    exact orbitalMinus_pullback t c x hx.le
  have hff : (fun x => star (orbitalZero t c (CartesianOrbitals.toCartesian x)) * orbitalZero t c (CartesianOrbitals.toCartesian x))
      =ᵐ[cylindricalMeasure]
      (fun x => star (cylindricalZero t c x) *
        cylindricalZero t c x) := by
    filter_upwards [hz] with x hx
    rw [hx]
  have hgg : (fun x => star (orbitalMinus t c (CartesianOrbitals.toCartesian x)) * orbitalMinus t c (CartesianOrbitals.toCartesian x))
      =ᵐ[cylindricalMeasure]
      (fun x => star (cylindricalMinus t c x) *
        cylindricalMinus t c x) := by
    filter_upwards [hg] with x hx
    rw [hx]
  have hfg : (fun x => star (orbitalZero t c (CartesianOrbitals.toCartesian x)) * orbitalMinus t c (CartesianOrbitals.toCartesian x))
      =ᵐ[cylindricalMeasure]
      (fun x => star (cylindricalZero t c x) *
        cylindricalMinus t c x) := by
    filter_upwards [hz, hg] with x hx hy
    rw [hx, hy]
  have hgf : (fun x => star (orbitalMinus t c (CartesianOrbitals.toCartesian x)) * orbitalZero t c (CartesianOrbitals.toCartesian x))
      =ᵐ[cylindricalMeasure]
      (fun x => star (cylindricalMinus t c x) *
        cylindricalZero t c x) := by
    filter_upwards [hz, hg] with x hx hy
    rw [hx, hy]
  have hzc := orbitalZero_continuous t c ht.le
  have hgc := orbitalMinus_continuous t c ht.le
  have hffc : Continuous (fun x => star (orbitalZero t c x) * orbitalZero t c x) :=
    (Complex.continuous_conj.comp hzc).mul hzc
  have hggc : Continuous (fun x => star (orbitalMinus t c x) * orbitalMinus t c x) :=
    (Complex.continuous_conj.comp hgc).mul hgc
  have hfgc : Continuous (fun x => star (orbitalZero t c x) * orbitalMinus t c x) :=
    (Complex.continuous_conj.comp hzc).mul hgc
  have hgfc : Continuous (fun x => star (orbitalMinus t c x) * orbitalZero t c x) :=
    (Complex.continuous_conj.comp hgc).mul hzc
  constructor
  · exact (CartesianOrbitals.toCartesian_measure_preserving.integrable_comp hffc.aestronglyMeasurable).mp
      (h.integrable_ff.congr hff.symm)
  · exact (CartesianOrbitals.toCartesian_measure_preserving.integrable_comp hggc.aestronglyMeasurable).mp
      (h.integrable_gg.congr hgg.symm)
  · exact (CartesianOrbitals.toCartesian_measure_preserving.integrable_comp hfgc.aestronglyMeasurable).mp
      (h.integrable_fg.congr hfg.symm)
  · exact (CartesianOrbitals.toCartesian_measure_preserving.integrable_comp hgfc.aestronglyMeasurable).mp
      (h.integrable_gf.congr hgf.symm)
  · rw [CartesianOrbitals.cartesian_integral _ hffc, integral_congr_ae hff]
    exact h.norm_f
  · rw [CartesianOrbitals.cartesian_integral _ hggc, integral_congr_ae hgg]
    exact h.norm_g
  · rw [CartesianOrbitals.cartesian_integral _ hfgc, integral_congr_ae hfg]
    exact h.orthogonal_fg
  · rw [CartesianOrbitals.cartesian_integral _ hgfc, integral_congr_ae hgf]
    exact h.orthogonal_gf


theorem exists_gaussian_orthonormal (c : ℝ) (hc : 0 < c) :
    ∃ t : ℝ, 0 < t ∧
      MagHK.Slater.OrthonormalPair volume (orbitalZero t c) (orbitalMinus t c) := by
  obtain ⟨t, ht, hzero, hminus⟩ := exists_gaussian_equal_norms
  exact ⟨t, ht, gaussian_orthonormal t c ht hc hzero hminus⟩

end MagHK.GaussianOrbitals
