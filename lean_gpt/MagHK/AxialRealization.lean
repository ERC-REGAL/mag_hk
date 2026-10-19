import MagHK.Axial
import MagHK.Ordering
import MagHK.OperatorSpectrum
import Mathlib.MeasureTheory.Function.L2Space

/-!
The bounded axial Hamiltonian relative to standard full-line operator theory.
All analytic coefficients, orbital normalization and finite-energy inputs are
literal functions and integrals. The library premise contains only general
realization, Sturm simplicity, factorization and spectral correspondence laws.
The manuscript's axial gap is proved from these laws and the constant partner.
-/

noncomputable section
namespace MagHK.AxialRealization

open MeasureTheory Set
open MagHK.Axial MagHK.Ordering
open scoped ContDiff InnerProductSpace

abbrev State := Lp ℂ 2 (volume : Measure ℝ)

structure Coefficients (U V : ℝ → ℝ) : Prop where
  U_smooth : ContDiff ℝ ∞ U
  V_smooth : ContDiff ℝ ∞ V
  U_bounded : ∃ C : ℝ, ∀ z, |U z| ≤ C
  V_bounded : ∃ C : ℝ, ∀ z, |V z| ≤ C
  riccati : ∀ z, U z ^ 2 - deriv U z = V z

structure RegularSolution (V u : ℝ → ℝ) (E : ℝ) (ψ : State) : Prop where
  smooth : ContDiff ℝ 2 u
  represented : ∀ᵐ z, ψ z = (u z : ℂ)
  finite_energy : Integrable (fun z => deriv u z ^ 2 + |V z| * u z ^ 2)
  equation : ∀ z, -deriv (deriv u) z + V z * u z = E * u z

structure System where
  H : DomainOperator State
  partner : DomainOperator State
  spectrum : Set ℝ
  partnerSpectrum : Set ℝ
  multiplicity : ℝ → ℕ

def Eigen (S : System) (E : ℝ) (ψ : State) : Prop :=
  ∃ hψ : ψ ∈ S.H.domain, ψ ≠ 0 ∧ S.H.map ⟨ψ, hψ⟩ = E • ψ

def SimpleEigenline (S : System) (E : ℝ) : Prop :=
  ∃ ψ : State, Eigen S E ψ ∧ ∀ φ, Eigen S E φ → ∃ a : ℂ, φ = a • ψ

/-- Standard results for the Friedrichs full-line realization of
-d²/dz²+V and the supersymmetric partner -d²/dz²+U²+U'. The test-function
law ties the operator to the literal differential expression. Nonzero
spectral correspondence refers to the whole spectrum, not just eigenvalues.
-/
structure Facts (S : System) (U V : ℝ → ℝ) : Prop where
  selfadjoint : OperatorModel.SelfAdjoint S.H
  partner_selfadjoint : OperatorModel.SelfAdjoint S.partner
  spectrum_identification : S.spectrum = OperatorModel.spectrum S.H
  partner_spectrum_identification : S.partnerSpectrum = OperatorModel.spectrum S.partner
  multiplicity_identification : S.multiplicity = OperatorModel.multiplicity S.H
  weak_equation : ∀ ψ (hψ : ψ ∈ S.H.domain) (η : ℝ → ℝ),
    ContDiff ℝ ∞ η → HasCompactSupport η →
      -(∫ z, ψ z * ((deriv (deriv η) z : ℝ) : ℂ)) +
        (∫ z, (V z : ℂ) * ψ z * (η z : ℂ)) =
          ∫ z, (S.H.map ⟨ψ, hψ⟩) z * (η z : ℂ)
  regular_solution : ∀ E u ψ, RegularSolution V u E ψ → ψ ≠ 0 → Eigen S E ψ
  sturm_simplicity : ∀ E ψ φ, Eigen S E ψ → Eigen S E φ → ∃ a : ℂ, φ = a • ψ
  eigen_in_spectrum : ∀ E ψ, Eigen S E ψ → E ∈ S.spectrum
  dimension : ∀ E, SimpleEigenline S E → S.multiplicity E = 1
  nonnegative : ∀ E ∈ S.spectrum, 0 ≤ E
  nonzero_spectrum : ∀ E, E ≠ 0 → (E ∈ S.spectrum ↔ E ∈ S.partnerSpectrum)
  constant_partner : ∀ k : ℝ, (∀ z, U z ^ 2 + deriv U z = k) →
    S.partnerSpectrum = Ici k

/-- This premise is general operator theory, independent of the chosen
sech orbital or the manuscript's numerical parameters. No instance is
postulated as an axiom. -/
def StandardAxialLibrary : Prop :=
  ∀ U V : ℝ → ℝ, Coefficients U V → ∃ S : System, Facts S U V

theorem superpotential_smooth (c : ℝ) : ContDiff ℝ ∞ (superpotential c) := by
  have ht : ContDiff ℝ ∞ Real.tanh := by
    have heq : Real.tanh = fun z => Real.sinh z / Real.cosh z :=
      funext Real.tanh_eq_sinh_div_cosh
    rw [heq]
    exact Real.contDiff_sinh.div Real.contDiff_cosh (fun z => ne_of_gt (Real.cosh_pos z))
  exact contDiff_const.mul (ht.comp (contDiff_const.mul contDiff_id))

theorem superpotential_sq_bound (c z : ℝ) : superpotential c z ^ 2 ≤ c ^ 2 := by
  have hid := congrArg (fun x : ℝ => c ^ 2 * x) (hyperbolic_identity (c * z))
  have hp : 0 ≤ c ^ 2 * sech (c * z) ^ 2 := by positivity
  unfold superpotential
  nlinarith only [hid, hp]

theorem bounded_coefficients (c : ℝ) :
    Coefficients (superpotential c) (potential c) := by
  refine ⟨superpotential_smooth c, potential_smooth c, ?_,
    ⟨c ^ 2, potential_bounded c⟩, fun z => (factorization c z).1⟩
  refine ⟨|c|, fun z => ?_⟩
  exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp (by
    simpa only [sq_abs] using superpotential_sq_bound c z)

theorem chi_finite_energy (c : ℝ) (hc : 0 < c) :
    Integrable (fun z => deriv (chi c) z ^ 2 + |potential c z| * chi c z ^ 2) := by
  have hi := (chi_squared_integrable c hc).const_mul (2 * c ^ 2)
  have hder : Continuous (deriv (chi c)) := by
    have hfun : deriv (chi c) = fun z => -superpotential c z * chi c z :=
      funext (fun z => (chi_hasDerivAt c z).deriv)
    rw [hfun]
    exact (superpotential_smooth c).continuous.neg.mul (chi_smooth c).continuous
  apply hi.mono' ((hder.pow 2).add
    ((potential_smooth c).continuous.abs.mul ((chi_smooth c).continuous.pow 2))).aestronglyMeasurable
  filter_upwards [] with z
  change ‖deriv (chi c) z ^ 2 + |potential c z| * chi c z ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), (chi_hasDerivAt c z).deriv]
  have h1 := mul_le_mul_of_nonneg_right (superpotential_sq_bound c z) (sq_nonneg (chi c z))
  have h2 := mul_le_mul_of_nonneg_right (potential_bounded c z) (sq_nonneg (chi c z))
  nlinarith only [h1, h2]

theorem chi_memLp (c : ℝ) (hc : 0 < c) : MemLp (fun z => (chi c z : ℂ)) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (Complex.continuous_ofReal.comp (chi_smooth c).continuous).aestronglyMeasurable).mpr
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    chi_squared_integrable c hc

def chiState (c : ℝ) (hc : 0 < c) : State :=
  (chi_memLp c hc).toLp (fun z => (chi c z : ℂ))

theorem chiState_mass (c : ℝ) (hc : 0 < c) : ‖chiState c hc‖ ^ 2 = 1 := by
  calc
    ‖chiState c hc‖ ^ 2 = inner ℝ (chiState c hc) (chiState c hc) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ z, inner ℝ ((chiState c hc) z) ((chiState c hc) z) := rfl
    _ = ∫ z, chi c z ^ 2 := by
      apply integral_congr_ae
      filter_upwards [(chi_memLp c hc).coeFn_toLp] with z hz
      change (chiState c hc) z = (chi c z : ℂ) at hz
      rw [hz, real_inner_self_eq_norm_sq]
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = 1 := chi_normalization c hc

theorem chiState_nonzero (c : ℝ) (hc : 0 < c) : chiState c hc ≠ 0 := by
  intro hz
  have h := chiState_mass c hc
  rw [hz, norm_zero] at h
  norm_num at h

theorem chi_regular_solution (c : ℝ) (hc : 0 < c) :
    RegularSolution (potential c) (chi c) 0 (chiState c hc) := by
  refine ⟨(chi_smooth c).of_le (by norm_num), (chi_memLp c hc).coeFn_toLp,
    chi_finite_energy c hc, ?_⟩
  intro z
  simpa only [zero_mul] using zero_eigen_equation c z

/-- The complete bounded axial spectral gap, including possible continuous
spectrum, follows from the exact constant partner and general operator theory. -/
theorem bounded_axial_levels (c : ℝ) (hc : 0 < c) (S : System)
    (hS : Facts S (superpotential c) (potential c)) :
    Eigen S 0 (chiState c hc) ∧ 0 ∈ S.spectrum ∧ S.multiplicity 0 = 1 ∧
      (∀ E ∈ S.spectrum, E = 0 ∨ c ^ 2 ≤ E) := by
  have he := hS.regular_solution 0 (chi c) (chiState c hc)
    (chi_regular_solution c hc) (chiState_nonzero c hc)
  refine ⟨he, hS.eigen_in_spectrum 0 _ he,
    hS.dimension 0 ⟨chiState c hc, he, fun φ hφ => hS.sturm_simplicity 0 _ φ he hφ⟩, ?_⟩
  intro E hE
  by_cases hz : E = 0
  · exact Or.inl hz
  · right
    have hp := (hS.nonzero_spectrum E hz).mp hE
    rw [hS.constant_partner (c ^ 2) (fun z => (factorization c z).2)] at hp
    exact hp

theorem bounded_axial_realization (library : StandardAxialLibrary) (c : ℝ) (hc : 0 < c) :
    ∃ S : System, Facts S (superpotential c) (potential c) ∧
      Eigen S 0 (chiState c hc) ∧ 0 ∈ S.spectrum ∧ S.multiplicity 0 = 1 ∧
      (∀ E ∈ S.spectrum, E = 0 ∨ c ^ 2 ≤ E) := by
  obtain ⟨S, hS⟩ := library (superpotential c) (potential c) (bounded_coefficients c)
  exact ⟨S, hS, bounded_axial_levels c hc S hS⟩

end MagHK.AxialRealization
