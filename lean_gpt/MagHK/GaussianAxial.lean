import MagHK.AxialRealization
import MagHK.GaussianIntegrals

/-! The harmonic axial factor. Only the universal harmonic-oscillator
spectral theorem is external. The Gaussian state, its normalization,
finite energy, differential equation, and its realization are checked. -/
noncomputable section
namespace MagHK.GaussianAxial
open MeasureTheory Set
open MagHK.GaussianIntegrals
open scoped ContDiff InnerProductSpace

def superpotential (c z : ℝ) : ℝ := c * z
def potential (c z : ℝ) : ℝ := c ^ 2 * z ^ 2 - c

/-- The standard full-line oscillator theorem for every positive frequency,
with the actual differential and spectral definitions of AxialRealization.
No chosen Gaussian state or three-dimensional level is an input. -/
def StandardOscillatorLibrary : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Z : AxialRealization.System,
    AxialRealization.Facts Z (superpotential c) (potential c) ∧
    Z.spectrum = Set.range (fun n : ℕ => 2 * c * (n : ℝ))

theorem potential_smooth (c : ℝ) : ContDiff ℝ ∞ (potential c) :=
  (contDiff_const.mul (contDiff_id.pow 2)).sub contDiff_const

theorem chi_smooth (c : ℝ) : ContDiff ℝ ∞ (axialChi c) :=
  contDiff_const.mul ((contDiff_const.mul (contDiff_id.pow 2)).div_const 2).exp

theorem chi_second_moment (c : ℝ) (hc : 0 < c) :
    Integrable (fun z => z ^ 2 * axialChi c z ^ 2) := by
  have hi : Integrable (fun z : ℝ => z ^ 2 * Real.exp (-c * z ^ 2)) := by
    simpa using (integrable_rpow_mul_exp_neg_mul_sq hc (s := (2 : ℕ)) (by norm_num))
  apply (hi.const_mul (Real.sqrt (c / Real.pi))).congr
  exact ae_of_all _ (fun z => by
    change Real.sqrt (c / Real.pi) * (z ^ 2 * Real.exp (-c * z ^ 2)) =
      z ^ 2 * axialChi c z ^ 2
    rw [axialChi_squared]
    ring)

theorem chi_finite_energy (c : ℝ) (hc : 0 < c) :
    Integrable (fun z => deriv (axialChi c) z ^ 2 + |potential c z| * axialChi c z ^ 2) := by
  have hi := ((chi_second_moment c hc).const_mul (2 * c ^ 2)).add
    ((axialChi_squared_integrable c hc).const_mul c)
  have hder : Continuous (deriv (axialChi c)) := by
    have heq : deriv (axialChi c) = fun z => -c * z * axialChi c z :=
      funext (fun z => (axialChi_hasDerivAt c z).deriv)
    rw [heq]
    exact (continuous_const.mul continuous_id).mul (chi_smooth c).continuous
  apply hi.mono' ((hder.pow 2).add
    ((potential_smooth c).continuous.abs.mul ((chi_smooth c).continuous.pow 2))).aestronglyMeasurable
  filter_upwards [] with z
  change ‖deriv (axialChi c) z ^ 2 + |potential c z| * axialChi c z ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), (axialChi_hasDerivAt c z).deriv]
  have hv : |potential c z| ≤ c ^ 2 * z ^ 2 + c := by
    unfold potential
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg (by positivity), abs_of_pos hc])
  have hm := mul_le_mul_of_nonneg_right hv (sq_nonneg (axialChi c z))
  change (-c * z * axialChi c z) ^ 2 + |potential c z| * axialChi c z ^ 2 ≤
    2 * c ^ 2 * (z ^ 2 * axialChi c z ^ 2) + c * axialChi c z ^ 2
  nlinarith only [hm]

theorem chi_memLp (c : ℝ) (hc : 0 < c) : MemLp (fun z => (axialChi c z : ℂ)) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (Complex.continuous_ofReal.comp (chi_smooth c).continuous).aestronglyMeasurable).mpr
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    axialChi_squared_integrable c hc

def chiState (c : ℝ) (hc : 0 < c) : AxialRealization.State :=
  (chi_memLp c hc).toLp (fun z => (axialChi c z : ℂ))

theorem chiState_mass (c : ℝ) (hc : 0 < c) : ‖chiState c hc‖ ^ 2 = 1 := by
  calc
    ‖chiState c hc‖ ^ 2 = inner ℝ (chiState c hc) (chiState c hc) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ z, inner ℝ ((chiState c hc) z) ((chiState c hc) z) := rfl
    _ = ∫ z, axialChi c z ^ 2 := by
      apply integral_congr_ae
      filter_upwards [(chi_memLp c hc).coeFn_toLp] with z hz
      change (chiState c hc) z = (axialChi c z : ℂ) at hz
      rw [hz, real_inner_self_eq_norm_sq]
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = 1 := axialChi_normalized c hc

theorem chiState_nonzero (c : ℝ) (hc : 0 < c) : chiState c hc ≠ 0 := by
  intro hz
  have h := chiState_mass c hc
  rw [hz, norm_zero] at h
  norm_num at h

theorem chi_regular_solution (c : ℝ) (hc : 0 < c) :
    AxialRealization.RegularSolution (potential c) (axialChi c) 0 (chiState c hc) := by
  refine ⟨(chi_smooth c).of_le (by norm_num), (chi_memLp c hc).coeFn_toLp,
    chi_finite_energy c hc, ?_⟩
  intro z
  simpa only [potential, zero_mul] using axialChi_eigen_equation c z

theorem gaussian_axial_realization (library : StandardOscillatorLibrary) (c : ℝ) (hc : 0 < c) :
    ∃ Z : AxialRealization.System,
      AxialRealization.Facts Z (superpotential c) (potential c) ∧
      AxialRealization.Eigen Z 0 (chiState c hc) ∧
      0 ∈ Z.spectrum ∧ Z.multiplicity 0 = 1 ∧
      (∀ E ∈ Z.spectrum, E = 0 ∨ 2 * c ≤ E) := by
  obtain ⟨Z, hZ, hs⟩ := library c hc
  have he := hZ.regular_solution 0 (axialChi c) (chiState c hc)
    (chi_regular_solution c hc) (chiState_nonzero c hc)
  refine ⟨Z, hZ, he, hZ.eigen_in_spectrum 0 _ he,
    hZ.dimension 0 ⟨chiState c hc, he, fun φ hφ => hZ.sturm_simplicity 0 _ φ he hφ⟩, ?_⟩
  intro E hE
  rw [hs] at hE
  obtain ⟨n, rfl⟩ := hE
  by_cases hn : n = 0
  · left
    simp [hn]
  · right
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    nlinarith

end MagHK.GaussianAxial
