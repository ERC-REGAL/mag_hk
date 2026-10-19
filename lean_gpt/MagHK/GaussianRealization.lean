import MagHK.GaussianDomains
import MagHK.BoundedRealization

/-! The actual Gaussian radial construction in the universal realization
interface, with its ordered simple levels zero and two. -/
noncomputable section
namespace MagHK.GaussianRealization
open MeasureTheory Set
open MagHK.Noninteracting MagHK.RadialEndpoints MagHK.PartnerAsymptotics
open MagHK.SecondOrbital MagHK.GaussianDomains MagHK.GaussianIntegrals
open MagHK.RadialRealization MagHK.Ordering MagHK.BoundedRealization

theorem gaussian_coefficients (t : ℝ) (ht : 0 < t) :
    CoefficientConditions (gaussianA t) (scalar t) (gaussianU t) := by
  refine ⟨(gaussianA_contDiff t ht.le).of_le le_top, (scalar_contDiff t ht.le).of_le le_top,
    (gaussianU_contDiff t ht.le).of_le le_top, ?_, gaussianU_at_zero t, ?_, ?_, ?_, ?_⟩
  · simp [gaussianA]
  · intro r hr
    rw [(gaussianU_hasDerivAt t r ht.le).deriv]
    exact gaussian_scalar_factorization t r ht.le (ne_of_gt hr)
  · refine ⟨1, 2 + 2 * t, le_rfl, fun r _ => ?_⟩
    have h := gaussianScalar_quadratic_lower_bound t r ht.le
    unfold scalar
    nlinarith [sq_nonneg r]
  · obtain ⟨C, hC⟩ := gaussianPartner_near_origin t ht.le
    refine ⟨C, fun r hr hr1 => ?_⟩
    have hratio : gaussianU t r / r = gaussianUCoefficient t r := by
      rw [gaussianU_eq_mul_coefficient]
      field_simp
    simpa only [gaussianPartnerCoefficient, add_sub_cancel_left,
      gaussianPartnerRemainder, hratio] using hC r hr hr1
  · refine ⟨1, 2 * t, le_rfl, fun r hr => ?_⟩
    have hr0 : 0 < r := by linarith
    rw [← gaussianPartnerCoefficient_eq t r (ne_of_gt hr0)]
    nlinarith [gaussianPartner_quadratic_lower_bound t r ht.le, sq_nonneg r]

private theorem real_memLp (u : ℝ → ℝ) (hu : Continuous u)
    (hi : Integrable (fun r => u r ^ 2) radialMeasure) :
    MemLp (fun r => (u r : ℂ)) 2 radialMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (Complex.continuous_ofReal.comp hu).aestronglyMeasurable).mpr
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Function.comp_apply] using hi

theorem zero_memLp (t : ℝ) (ht : 0 ≤ t) :
    MemLp (fun r => (gaussianF t r : ℂ)) 2 radialMeasure :=
  real_memLp _ (gaussianF_contDiff t ht).continuous (gaussianF_mass_integrable t ht)

theorem minus_memLp (t : ℝ) (ht : 0 ≤ t) :
    MemLp (fun r => (gaussianProduct t r : ℂ)) 2 radialMeasure :=
  real_memLp _ (gaussianProduct_contDiff t ht).continuous (gaussianProduct_mass_integrable t ht)

def zeroState (t : ℝ) (ht : 0 ≤ t) : State :=
  (zero_memLp t ht).toLp (fun r => (gaussianF t r : ℂ))

def minusState (t : ℝ) (ht : 0 ≤ t) : State :=
  (minus_memLp t ht).toLp (fun r => (gaussianProduct t r : ℂ))

theorem gaussian_zero_solution (t : ℝ) (ht : 0 < t) :
    RegularSolution (gaussianA t) (scalar t) 0 0
      (gaussianF t) (zeroState t ht.le) := by
  refine ⟨gaussianF_contDiffOn_two t ht.le, fun r _ => gaussianF_pos t r ht.le,
    gaussianF_bounded_near_zero t ht.le, ?_, ?_,
    (zero_memLp t ht.le).coeFn_toLp, gaussianF_mass_positive t ht.le⟩
  · simpa only [Int.cast_zero] using gaussianF_form_integrable t ht
  · intro r hr
    simpa only [radialExpression, scalar, Int.cast_zero, zero_div, zero_add, zero_mul]
      using gaussian_zero_eigen_equation t r ht.le (ne_of_gt hr)

theorem gaussian_minus_solution (t : ℝ) (ht : 0 < t) :
    RegularSolution (gaussianA t) (scalar t) (-1) 2
      (gaussianProduct t) (minusState t ht.le) := by
  refine ⟨gaussianProduct_contDiffOn_two t ht.le,
    fun r hr => gaussianProduct_positive t r ht.le hr,
    gaussianProduct_bounded_near_zero t ht.le, ?_, ?_,
    (minus_memLp t ht.le).coeFn_toLp, gaussianProduct_mass_positive t ht.le⟩
  · simpa only [Int.cast_neg, Int.cast_one] using gaussianProduct_form_integrable t ht
  · intro r hr
    simpa only [radialExpression, scalar, Int.cast_neg, Int.cast_one]
      using gaussian_eigen_equation t r ht.le (ne_of_gt hr)

theorem gaussian_ordering (t : ℝ) (ht : 0 < t) (S : RadialSystem)
    (A : StandardRadialFacts S (gaussianA t) (scalar t) (gaussianU t)) :
    RadialOrderingData (Eigen S) 2 := by
  apply orderingData S (gaussianA t) (scalar t) (gaussianU t)
    (gaussianF t) (gaussianProduct t) 2 A (gaussian_coefficients t ht)
    (zeroState t ht.le) (minusState t ht.le)
    (gaussian_zero_solution t ht) (gaussian_minus_solution t ht) (by norm_num)
  · exact fun r hr => gaussian_angular_bounds t r ht hr
  · intro r hr
    exact lt_trans (by norm_num) (gaussian_partner_correction_gt_one t r ht hr)

/-- The threshold can be any number above two. For the confining Gaussian
potential the general compact-resolvent theorem supplies these facts. -/
theorem gaussian_planar_levels (t : ℝ) (ht : 0 < t) (S : RadialSystem)
    (A : StandardRadialFacts S (gaussianA t) (scalar t) (gaussianU t))
    (spectrum : Set ℝ) (multiplicity : ℝ → ℕ) (threshold : ℝ) (hthreshold : 2 < threshold)
    (hs : PlanarSpectralFacts S spectrum multiplicity threshold) :
    (∀ E, E ∈ spectrum ∧ E ≤ 2 ↔ E = 0 ∨ E = 2) ∧
      multiplicity 0 = 1 ∧ multiplicity 2 = 1 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ E, 2 < E → E < 2 + ε → E ∉ spectrum := by
  have ho := gaussian_ordering t ht S A
  refine ⟨planar_spectrum_below_second ho hs.discrete hthreshold, ?_, ?_,
    planar_strict_gap ho hs.discrete hthreshold⟩
  · exact hs.dimension_of_single_eigenline 0 0
      (fun n hn => unique_sector_at_zero ho hn)
      (simple_radial_eigenline S _ _ _ A 0 0 ho.zero_state)
  · exact hs.dimension_of_single_eigenline 2 (-1)
      (fun n hn => unique_sector_at_lambda ho hn)
      (simple_radial_eigenline S _ _ _ A (-1) 2 ho.minus_one_state)

theorem gaussian_realization (library : StandardRadialLibrary) (t : ℝ) (ht : 0 < t) :
    ∃ S : RadialSystem,
      StandardRadialFacts S (gaussianA t) (scalar t) (gaussianU t) ∧
      RadialOrderingData (Eigen S) 2 ∧
      ∀ spectrum multiplicity threshold, 2 < threshold →
        PlanarSpectralFacts S spectrum multiplicity threshold →
        (∀ E, E ∈ spectrum ∧ E ≤ 2 ↔ E = 0 ∨ E = 2) ∧
        multiplicity 0 = 1 ∧ multiplicity 2 = 1 ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ E, 2 < E → E < 2 + ε → E ∉ spectrum := by
  obtain ⟨S, A⟩ := library (gaussianA t) (scalar t) (gaussianU t) (gaussian_coefficients t ht)
  exact ⟨S, A, gaussian_ordering t ht S A, fun spectrum multiplicity threshold hthreshold hs =>
    gaussian_planar_levels t ht S A spectrum multiplicity threshold hthreshold hs⟩

theorem exists_balanced_gaussian_realization (library : StandardRadialLibrary) :
    ∃ t : ℝ, 0 < t ∧
      (∫ r in Ioi (0 : ℝ), gaussianF t r ^ 2 * r) = 1 / 4 ∧
      (∫ r in Ioi (0 : ℝ), t * r ^ 2 * gaussianF t r ^ 2 * r) = 1 / 4 ∧
      ∃ S : RadialSystem,
        StandardRadialFacts S (gaussianA t) (scalar t) (gaussianU t) ∧
        RadialOrderingData (Eigen S) 2 := by
  obtain ⟨t, ht, hzero, hminus⟩ := exists_gaussian_equal_norms
  obtain ⟨S, hS, ho, _⟩ := gaussian_realization library t ht
  exact ⟨t, ht, hzero, hminus, S, hS, ho⟩

end MagHK.GaussianRealization
